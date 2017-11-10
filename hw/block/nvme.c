/*
 * QEMU NVM Express Controller
 *
 * Copyright (c) 2012, Intel Corporation
 *
 * Written by Keith Busch <keith.busch@intel.com>
 *
 * This code is licensed under the GNU GPL v2 or later.
 */

/**
 * Reference Specs: http://www.nvmexpress.org, 1.2, 1.1, 1.0e
 *
 *  http://www.nvmexpress.org/resources/
 */

/**
 * Usage: add options:
 *      -drive file=<file>,if=none,id=<drive_id>
 *      -device nvme,drive=<drive_id>,serial=<serial>,id=<id[optional]>, \
 *              cmb_size_mb=<cmb_size_mb[optional]>
 *
 * Note cmb_size_mb denotes size of CMB in MB. CMB is assumed to be at
 * offset 0 in BAR2 and supports only WDS, RDS and SQS for now.
 */

#include "qemu/osdep.h"
#include "hw/block/block.h"
#include "hw/hw.h"
#include "hw/pci/msix.h"
#include "hw/pci/pci.h"
#include "sysemu/sysemu.h"
#include "qapi/error.h"
#include "qapi/visitor.h"
#include "sysemu/block-backend.h"
#include "hw/pci/pcie_sriov.h"

#include "nvme.h"

#define NVME_CTRL_LIST_MAX_ENTRIES  2047
#define NVME_MAX_NUM_NAMESPACES     256

/*?? this is a terrible idea */
NvmeCtrl *prim_ctrl = NULL;

static void nvme_process_sq(void *opaque);
static void nvme_write_bar(NvmeCtrl *n, hwaddr offset, uint64_t data,
    unsigned size);

static void nvme_addr_read(NvmeCtrl *n, hwaddr addr, void *buf, int size)
{
    if (n->cmbsz && addr >= n->ctrl_mem.addr &&
                addr < (n->ctrl_mem.addr + int128_get64(n->ctrl_mem.size))) {
        memcpy(buf, (void *)&n->cmbuf[addr - n->ctrl_mem.addr], size);
    } else {
        pci_dma_read(&n->parent_obj, addr, buf, size);
    }
}

static int nvme_check_sqid(NvmeCtrl *n, uint16_t sqid)
{
    return sqid < n->num_queues && n->sq[sqid] != NULL ? 0 : -1;
}

static int nvme_check_cqid(NvmeCtrl *n, uint16_t cqid)
{
    return cqid < n->num_queues && n->cq[cqid] != NULL ? 0 : -1;
}

static void nvme_inc_cq_tail(NvmeCQueue *cq)
{
    cq->tail++;
    if (cq->tail >= cq->size) {
        cq->tail = 0;
        cq->phase = !cq->phase;
    }
}

static void nvme_inc_sq_head(NvmeSQueue *sq)
{
    sq->head = (sq->head + 1) % sq->size;
}

static uint8_t nvme_cq_full(NvmeCQueue *cq)
{
    return (cq->tail + 1) % cq->size == cq->head;
}

static uint8_t nvme_sq_empty(NvmeSQueue *sq)
{
    return sq->head == sq->tail;
}

static void nvme_isr_notify(NvmeCtrl *n, NvmeCQueue *cq)
{
    if (cq->irq_enabled) {
        if (msix_enabled(&(n->parent_obj))) {
            msix_notify(&(n->parent_obj), cq->vector);
        } else {
            pci_irq_pulse(&n->parent_obj);
        }
    }
}

static uint16_t nvme_map_prp(QEMUSGList *qsg, QEMUIOVector *iov, uint64_t prp1,
                             uint64_t prp2, uint32_t len, NvmeCtrl *n)
{
    hwaddr trans_len = n->page_size - (prp1 % n->page_size);
    trans_len = MIN(len, trans_len);
    int num_prps = (len >> n->page_bits) + 1;

    if (!prp1) {
        return NVME_INVALID_FIELD | NVME_DNR;
    } else if (n->cmbsz && prp1 >= n->ctrl_mem.addr &&
               prp1 < n->ctrl_mem.addr + int128_get64(n->ctrl_mem.size)) {
        qsg->nsg = 0;
        qemu_iovec_init(iov, num_prps);
        qemu_iovec_add(iov, (void *)&n->cmbuf[prp1 - n->ctrl_mem.addr], trans_len);
    } else {
        pci_dma_sglist_init(qsg, &n->parent_obj, num_prps);
        qemu_sglist_add(qsg, prp1, trans_len);
    }
    len -= trans_len;
    if (len) {
        if (!prp2) {
            goto unmap;
        }
        if (len > n->page_size) {
            uint64_t prp_list[n->max_prp_ents];
            uint32_t nents, prp_trans;
            int i = 0;

            nents = (len + n->page_size - 1) >> n->page_bits;
            prp_trans = MIN(n->max_prp_ents, nents) * sizeof(uint64_t);
            nvme_addr_read(n, prp2, (void *)prp_list, prp_trans);
            while (len != 0) {
                uint64_t prp_ent = le64_to_cpu(prp_list[i]);

                if (i == n->max_prp_ents - 1 && len > n->page_size) {
                    if (!prp_ent || prp_ent & (n->page_size - 1)) {
                        goto unmap;
                    }

                    i = 0;
                    nents = (len + n->page_size - 1) >> n->page_bits;
                    prp_trans = MIN(n->max_prp_ents, nents) * sizeof(uint64_t);
                    nvme_addr_read(n, prp_ent, (void *)prp_list,
                        prp_trans);
                    prp_ent = le64_to_cpu(prp_list[i]);
                }

                if (!prp_ent || prp_ent & (n->page_size - 1)) {
                    goto unmap;
                }

                trans_len = MIN(len, n->page_size);
                if (qsg->nsg){
                    qemu_sglist_add(qsg, prp_ent, trans_len);
                } else {
                    qemu_iovec_add(iov, (void *)&n->cmbuf[prp_ent - n->ctrl_mem.addr], trans_len);
                }
                len -= trans_len;
                i++;
            }
        } else {
            if (prp2 & (n->page_size - 1)) {
                goto unmap;
            }
            if (qsg->nsg) {
                qemu_sglist_add(qsg, prp2, len);
            } else {
                qemu_iovec_add(iov, (void *)&n->cmbuf[prp2 - n->ctrl_mem.addr], trans_len);
            }
        }
    }
    return NVME_SUCCESS;

 unmap:
    qemu_sglist_destroy(qsg);
    return NVME_INVALID_FIELD | NVME_DNR;
}

static uint16_t nvme_dma_read_prp(NvmeCtrl *n, uint8_t *ptr, uint32_t len,
    uint64_t prp1, uint64_t prp2)
{
    QEMUSGList qsg;
    QEMUIOVector iov;
    uint16_t status = NVME_SUCCESS;

    if (nvme_map_prp(&qsg, &iov, prp1, prp2, len, n)) {
        return NVME_INVALID_FIELD | NVME_DNR;
    }
    if (qsg.nsg > 0) {
        if (dma_buf_read(ptr, len, &qsg)) {
            status = NVME_INVALID_FIELD | NVME_DNR;
        }
        qemu_sglist_destroy(&qsg);
    } else {
        if (qemu_iovec_to_buf(&iov, 0, ptr, len) != len) {
            status = NVME_INVALID_FIELD | NVME_DNR;
        }
        qemu_iovec_destroy(&iov);
    }
    return status;
}

static uint16_t nvme_dma_write_prp(NvmeCtrl *n, uint8_t *ptr, uint32_t len,
    uint64_t prp1, uint64_t prp2)
{
    QEMUSGList qsg;
    QEMUIOVector iov;

    if (nvme_map_prp(&qsg, &iov, prp1, prp2, len, n)) {
        return NVME_INVALID_FIELD | NVME_DNR;
    }

    if (dma_buf_write(ptr, len, &qsg)) {
        qemu_sglist_destroy(&qsg);
        return NVME_INVALID_FIELD | NVME_DNR;
    }
    qemu_sglist_destroy(&qsg);
    return NVME_SUCCESS;
}

static void nvme_post_cqes(void *opaque)
{
    NvmeCQueue *cq = opaque;
    NvmeCtrl *n = cq->ctrl;
    NvmeRequest *req, *next;

    QTAILQ_FOREACH_SAFE(req, &cq->req_list, entry, next) {
        NvmeSQueue *sq;
        hwaddr addr;

        if (nvme_cq_full(cq)) {
            break;
        }

        QTAILQ_REMOVE(&cq->req_list, req, entry);
        sq = req->sq;
        req->cqe.status = cpu_to_le16((req->status << 1) | cq->phase);
        req->cqe.sq_id = cpu_to_le16(sq->sqid);
        req->cqe.sq_head = cpu_to_le16(sq->head);
        addr = cq->dma_addr + cq->tail * n->cqe_size;
        nvme_inc_cq_tail(cq);
        pci_dma_write(&n->parent_obj, addr, (void *)&req->cqe,
            sizeof(req->cqe));
        QTAILQ_INSERT_TAIL(&sq->req_list, req, entry);
    }
    nvme_isr_notify(n, cq);
}

static void nvme_enqueue_req_completion(NvmeCQueue *cq, NvmeRequest *req)
{
    assert(cq->cqid == req->sq->cqid);
    QTAILQ_REMOVE(&req->sq->out_req_list, req, entry);
    QTAILQ_INSERT_TAIL(&cq->req_list, req, entry);
    timer_mod(cq->timer, qemu_clock_get_ns(QEMU_CLOCK_VIRTUAL) + 500);
}

static void nvme_rw_cb(void *opaque, int ret)
{
    NvmeRequest *req = opaque;
    NvmeSQueue *sq = req->sq;
    NvmeCtrl *n = sq->ctrl;
    NvmeCQueue *cq = n->cq[sq->cqid];

    if (!ret) {
        block_acct_done(blk_get_stats(n->conf.blk), &req->acct);
        req->status = NVME_SUCCESS;
    } else {
        block_acct_failed(blk_get_stats(n->conf.blk), &req->acct);
        req->status = NVME_INTERNAL_DEV_ERROR;
    }
    if (req->has_sg) {
        qemu_sglist_destroy(&req->qsg);
    }
    nvme_enqueue_req_completion(cq, req);
}

static uint16_t nvme_flush(NvmeCtrl *n, NvmeNamespace *ns, NvmeCmd *cmd,
    NvmeRequest *req)
{
    req->has_sg = false;
    block_acct_start(blk_get_stats(n->conf.blk), &req->acct, 0,
         BLOCK_ACCT_FLUSH);
    req->aiocb = blk_aio_flush(n->conf.blk, nvme_rw_cb, req);

    return NVME_NO_COMPLETE;
}

static uint16_t nvme_write_zeros(NvmeCtrl *n, NvmeNamespace *ns, NvmeCmd *cmd,
    NvmeRequest *req)
{
    NvmeRwCmd *rw = (NvmeRwCmd *)cmd;
    const uint8_t lba_index = NVME_ID_NS_FLBAS_INDEX(ns->id_ns.flbas);
    const uint8_t data_shift = ns->id_ns.lbaf[lba_index].ds;
    uint64_t slba = le64_to_cpu(rw->slba);
    uint32_t nlb  = le16_to_cpu(rw->nlb) + 1;
    uint64_t aio_slba = slba << (data_shift - BDRV_SECTOR_BITS);
    uint32_t aio_nlb = nlb << (data_shift - BDRV_SECTOR_BITS);

    if (slba + nlb > ns->id_ns.nsze) {
        return NVME_LBA_RANGE | NVME_DNR;
    }

    req->has_sg = false;
    block_acct_start(blk_get_stats(n->conf.blk), &req->acct, 0,
                     BLOCK_ACCT_WRITE);
    req->aiocb = blk_aio_pwrite_zeroes(n->conf.blk, aio_slba, aio_nlb,
                                        BDRV_REQ_MAY_UNMAP, nvme_rw_cb, req);
    return NVME_NO_COMPLETE;
}

static uint16_t nvme_rw(NvmeCtrl *n, NvmeNamespace *ns, NvmeCmd *cmd,
    NvmeRequest *req)
{
    NvmeRwCmd *rw = (NvmeRwCmd *)cmd;
    uint32_t nlb  = le32_to_cpu(rw->nlb) + 1;
    uint64_t slba = le64_to_cpu(rw->slba);
    uint64_t prp1 = le64_to_cpu(rw->prp1);
    uint64_t prp2 = le64_to_cpu(rw->prp2);

    uint8_t lba_index  = NVME_ID_NS_FLBAS_INDEX(ns->id_ns.flbas);
    uint8_t data_shift = ns->id_ns.lbaf[lba_index].ds;
    uint64_t data_size = (uint64_t)nlb << data_shift;
    uint64_t data_offset = ns->start_byte_index + (slba << (data_shift - BDRV_SECTOR_BITS));
    int is_write = rw->opcode == NVME_CMD_WRITE ? 1 : 0;
    enum BlockAcctType acct = is_write ? BLOCK_ACCT_WRITE : BLOCK_ACCT_READ;

    if (!ns->ctrl) {
        return NVME_INVALID_FIELD | NVME_DNR;
    }

    if ((slba + nlb) > ns->id_ns.nsze) {
        block_acct_invalid(blk_get_stats(n->conf.blk), acct);
        return NVME_LBA_RANGE | NVME_DNR;
    }

    if (nvme_map_prp(&req->qsg, &req->iov, prp1, prp2, data_size, n)) {
        block_acct_invalid(blk_get_stats(n->conf.blk), acct);
        return NVME_INVALID_FIELD | NVME_DNR;
    }

    assert((nlb << data_shift) == req->qsg.size);

    req->has_sg = true;
    req->ns = ns;
    req->status = NVME_SUCCESS;

    dma_acct_start(n->conf.blk, &req->acct, &req->qsg, acct);
    if (req->qsg.nsg > 0) {
        req->has_sg = true;
        req->aiocb = is_write ?
            dma_blk_write(n->conf.blk, &req->qsg, data_offset, BDRV_SECTOR_SIZE,
                          nvme_rw_cb, req) :
            dma_blk_read(n->conf.blk, &req->qsg, data_offset, BDRV_SECTOR_SIZE,
                         nvme_rw_cb, req);
    } else {
        req->has_sg = false;
        req->aiocb = is_write ?
            blk_aio_pwritev(n->conf.blk, data_offset, &req->iov, 0, nvme_rw_cb,
                            req) :
            blk_aio_preadv(n->conf.blk, data_offset, &req->iov, 0, nvme_rw_cb,
                           req);
    }

    return NVME_NO_COMPLETE;
}

static uint16_t nvme_io_cmd(NvmeCtrl *n, NvmeCmd *cmd, NvmeRequest *req)
{
    NvmeNamespace *ns;
    uint32_t nsid = le32_to_cpu(cmd->nsid);

    if (nsid == 0 || nsid > n->num_namespaces) {
        return NVME_INVALID_NSID | NVME_DNR;
    }

    ns = &n->namespaces[nsid - 1];
    switch (cmd->opcode) {
    case NVME_CMD_FLUSH:
        return nvme_flush(n, ns, cmd, req);
    case NVME_CMD_WRITE_ZEROS:
        return nvme_write_zeros(n, ns, cmd, req);
    case NVME_CMD_WRITE:
    case NVME_CMD_READ:
        return nvme_rw(n, ns, cmd, req);
    default:
        return NVME_INVALID_OPCODE | NVME_DNR;
    }
}

static void nvme_free_sq(NvmeSQueue *sq, NvmeCtrl *n)
{
    n->sq[sq->sqid] = NULL;
    timer_del(sq->timer);
    timer_free(sq->timer);
    g_free(sq->io_req);
    if (sq->sqid) {
        g_free(sq);
    }
}

static uint16_t nvme_del_sq(NvmeCtrl *n, NvmeCmd *cmd)
{
    NvmeDeleteQ *c = (NvmeDeleteQ *)cmd;
    NvmeRequest *req, *next;
    NvmeSQueue *sq;
    NvmeCQueue *cq;
    uint16_t qid = le16_to_cpu(c->qid);

    if (!qid || nvme_check_sqid(n, qid)) {
        return NVME_INVALID_QID | NVME_DNR;
    }

    sq = n->sq[qid];
    while (!QTAILQ_EMPTY(&sq->out_req_list)) {
        req = QTAILQ_FIRST(&sq->out_req_list);
        assert(req->aiocb);
        blk_aio_cancel(req->aiocb);
    }
    if (!nvme_check_cqid(n, sq->cqid)) {
        cq = n->cq[sq->cqid];
        QTAILQ_REMOVE(&cq->sq_list, sq, entry);

        nvme_post_cqes(cq);
        QTAILQ_FOREACH_SAFE(req, &cq->req_list, entry, next) {
            if (req->sq == sq) {
                QTAILQ_REMOVE(&cq->req_list, req, entry);
                QTAILQ_INSERT_TAIL(&sq->req_list, req, entry);
            }
        }
    }

    nvme_free_sq(sq, n);
    return NVME_SUCCESS;
}

static void nvme_init_sq(NvmeSQueue *sq, NvmeCtrl *n, uint64_t dma_addr,
    uint16_t sqid, uint16_t cqid, uint16_t size)
{
    int i;
    NvmeCQueue *cq;

    sq->ctrl = n;
    sq->dma_addr = dma_addr;
    sq->sqid = sqid;
    sq->size = size;
    sq->cqid = cqid;
    sq->head = sq->tail = 0;
    sq->io_req = g_new(NvmeRequest, sq->size);

    QTAILQ_INIT(&sq->req_list);
    QTAILQ_INIT(&sq->out_req_list);
    for (i = 0; i < sq->size; i++) {
        sq->io_req[i].sq = sq;
        QTAILQ_INSERT_TAIL(&(sq->req_list), &sq->io_req[i], entry);
    }
    sq->timer = timer_new_ns(QEMU_CLOCK_VIRTUAL, nvme_process_sq, sq);

    assert(n->cq[cqid]);
    cq = n->cq[cqid];
    QTAILQ_INSERT_TAIL(&(cq->sq_list), sq, entry);
    n->sq[sqid] = sq;
}

static uint16_t nvme_create_sq(NvmeCtrl *n, NvmeCmd *cmd)
{
    NvmeSQueue *sq;
    NvmeCreateSq *c = (NvmeCreateSq *)cmd;

    uint16_t cqid = le16_to_cpu(c->cqid);
    uint16_t sqid = le16_to_cpu(c->sqid);
    uint16_t qsize = le16_to_cpu(c->qsize);
    uint16_t qflags = le16_to_cpu(c->sq_flags);
    uint64_t prp1 = le64_to_cpu(c->prp1);

    if (!cqid || nvme_check_cqid(n, cqid)) {
        return NVME_INVALID_CQID | NVME_DNR;
    }
    if (!sqid || !nvme_check_sqid(n, sqid)) {
        return NVME_INVALID_QID | NVME_DNR;
    }
    if (!qsize || qsize > NVME_CAP_MQES(n->bar.cap)) {
        return NVME_MAX_QSIZE_EXCEEDED | NVME_DNR;
    }
    if (!prp1 || prp1 & (n->page_size - 1)) {
        return NVME_INVALID_FIELD | NVME_DNR;
    }
    if (!(NVME_SQ_FLAGS_PC(qflags))) {
        return NVME_INVALID_FIELD | NVME_DNR;
    }
    sq = g_malloc0(sizeof(*sq));
    nvme_init_sq(sq, n, prp1, sqid, cqid, qsize + 1);
    return NVME_SUCCESS;
}

static void nvme_free_cq(NvmeCQueue *cq, NvmeCtrl *n)
{
    n->cq[cq->cqid] = NULL;
    timer_del(cq->timer);
    timer_free(cq->timer);
    msix_vector_unuse(&n->parent_obj, cq->vector);
    if (cq->cqid) {
        g_free(cq);
    }
}

static uint16_t nvme_del_cq(NvmeCtrl *n, NvmeCmd *cmd)
{
    NvmeDeleteQ *c = (NvmeDeleteQ *)cmd;
    NvmeCQueue *cq;
    uint16_t qid = le16_to_cpu(c->qid);

    if (!qid || nvme_check_cqid(n, qid)) {
        return NVME_INVALID_CQID | NVME_DNR;
    }

    cq = n->cq[qid];
    if (!QTAILQ_EMPTY(&cq->sq_list)) {
        return NVME_INVALID_QUEUE_DEL;
    }
    nvme_free_cq(cq, n);
    return NVME_SUCCESS;
}

static void nvme_init_cq(NvmeCQueue *cq, NvmeCtrl *n, uint64_t dma_addr,
    uint16_t cqid, uint16_t vector, uint16_t size, uint16_t irq_enabled)
{
    cq->ctrl = n;
    cq->cqid = cqid;
    cq->size = size;
    cq->dma_addr = dma_addr;
    cq->phase = 1;
    cq->irq_enabled = irq_enabled;
    cq->vector = vector;
    cq->head = cq->tail = 0;
    QTAILQ_INIT(&cq->req_list);
    QTAILQ_INIT(&cq->sq_list);
    msix_vector_use(&n->parent_obj, cq->vector);
    n->cq[cqid] = cq;
    cq->timer = timer_new_ns(QEMU_CLOCK_VIRTUAL, nvme_post_cqes, cq);
}

static uint16_t nvme_create_cq(NvmeCtrl *n, NvmeCmd *cmd)
{
    NvmeCQueue *cq;
    NvmeCreateCq *c = (NvmeCreateCq *)cmd;
    uint16_t cqid = le16_to_cpu(c->cqid);
    uint16_t vector = le16_to_cpu(c->irq_vector);
    uint16_t qsize = le16_to_cpu(c->qsize);
    uint16_t qflags = le16_to_cpu(c->cq_flags);
    uint64_t prp1 = le64_to_cpu(c->prp1);

    if (!cqid || !nvme_check_cqid(n, cqid)) {
        return NVME_INVALID_CQID | NVME_DNR;
    }
    if (!qsize || qsize > NVME_CAP_MQES(n->bar.cap)) {
        return NVME_MAX_QSIZE_EXCEEDED | NVME_DNR;
    }
    if (!prp1) {
        return NVME_INVALID_FIELD | NVME_DNR;
    }
    if (vector > n->num_queues) {
        return NVME_INVALID_IRQ_VECTOR | NVME_DNR;
    }
    if (!(NVME_CQ_FLAGS_PC(qflags))) {
        return NVME_INVALID_FIELD | NVME_DNR;
    }

    cq = g_malloc0(sizeof(*cq));
    nvme_init_cq(cq, n, prp1, cqid, vector, qsize + 1,
        NVME_CQ_FLAGS_IEN(qflags));
    return NVME_SUCCESS;
}

static uint16_t nvme_identify_ctrl(NvmeCtrl *n, NvmeIdentify *c)
{
    uint64_t prp1 = le64_to_cpu(c->prp1);
    uint64_t prp2 = le64_to_cpu(c->prp2);

    return nvme_dma_read_prp(n, (uint8_t *)&n->id_ctrl, sizeof(n->id_ctrl),
        prp1, prp2);
}

static uint16_t nvme_identify_ns(NvmeCtrl *n, NvmeIdentify *c)
{
    NvmeNamespace *ns;
    uint32_t nsid = le32_to_cpu(c->nsid);
    uint64_t prp1 = le64_to_cpu(c->prp1);
    uint64_t prp2 = le64_to_cpu(c->prp2);

    if (nsid == 0 || nsid > n->num_namespaces) {
        return NVME_INVALID_NSID | NVME_DNR;
    }

    ns = &n->namespaces[nsid - 1];
    return nvme_dma_read_prp(n, (uint8_t *)&ns->id_ns, sizeof(ns->id_ns),
        prp1, prp2);
}

static uint16_t nvme_identify_ns_allocated(NvmeCtrl *n, NvmeIdentify *c)
{
    NvmeNamespace *ns;
    uint32_t nsid = le32_to_cpu(c->nsid);
    uint64_t prp1 = le64_to_cpu(c->prp1);
    uint64_t prp2 = le64_to_cpu(c->prp2);

    if (nsid == 0 || nsid > n->num_namespaces) {
        return NVME_INVALID_NSID | NVME_DNR;
    }

    ns = &n->namespaces[nsid - 1];
    if (nsid == 0xffffffff || nsid > NVME_MAX_NUM_NAMESPACES) {
        return NVME_INVALID_NSID | NVME_DNR;
    }
    if (!ns->created) {
        return NVME_SUCCESS;
    }
    return nvme_dma_read_prp(n, (uint8_t *)&ns->id_ns, sizeof(ns->id_ns),
        prp1, prp2);
}

static uint16_t nvme_identify_nslist(NvmeCtrl *n, NvmeIdentify *c)
{
    static const int data_len = 4096;
    uint32_t min_nsid = le32_to_cpu(c->nsid);
    uint64_t prp1 = le64_to_cpu(c->prp1);
    uint64_t prp2 = le64_to_cpu(c->prp2);
    uint32_t *list;
    uint16_t ret;
    int i, j = 0;

    list = g_malloc0(data_len);
    for (i = 0; i < NVME_MAX_NUM_NAMESPACES; i++) {
        if (i < min_nsid) {
            continue;
        }
        if (n->namespaces[i].created) {
            list[j++] = cpu_to_le32(i + 1);
            if (j == data_len / sizeof(uint32_t)) {
                break;
            }
        }
    }
    ret = nvme_dma_read_prp(n, (uint8_t *)list, data_len, prp1, prp2);
    g_free(list);
    return ret;
}

static uint16_t nvme_identify_sec_ctrl_list(NvmeCtrl *n, NvmeIdentify *c)
{
    static const int data_len = 4096;
    uint64_t prp1 = le64_to_cpu(c->prp1);
    uint64_t prp2 = le64_to_cpu(c->prp2);
    NvmeSecondaryControllerEntry *list;
    uint16_t ret;
    int i;
    NvmeCtrl *sec_n;

    list = g_malloc0(data_len);
    list[0].scid = prim_ctrl->num_vfs;


    for (i = 1; i <= prim_ctrl->num_vfs; i++)
    {
        sec_n = prim_ctrl->secondary_ctrl_list[i-1];
        list[i].scid = sec_n->id_ctrl.cntlid;
        list[i].pcid = prim_ctrl->id_ctrl.cntlid;
        list[i].scs = sec_n->bar.csts;
        list[i].vfn = sec_n->id_ctrl.cntlid;
//        list[i].vfn = pci_get_bdf(&sec_n->parent_obj) & 0xF;
        list[i].nvq = sec_n->nvq;
        list[i].nvi = sec_n->nvi;
//        list[i+1] = cpu_to_le32(prim_nrl->secondary_ctrl_list[i]->id_ctrl.cntlid);
    }

    ret = nvme_dma_read_prp(n, (uint8_t *)list, data_len, prp1, prp2);
    g_free(list);
    return ret;
}

static uint16_t nvme_identify_prim_ctrl_cap(NvmeCtrl *n, NvmeIdentify *c)
{
    uint64_t prp1 = le64_to_cpu(c->prp1);
    uint64_t prp2 = le64_to_cpu(c->prp2);

    /* TODO: needs moved to init */
    n->id_prim_ctrl.cntlid = n->id_ctrl.cntlid;
    n->id_prim_ctrl.portid = 0;  //wrong
    n->id_prim_ctrl.crt = 0x3; //both supported
    n->id_prim_ctrl.vqfrt = 0x2; //flexible resources total
    n->id_prim_ctrl.vqfrsm = 0x2;
    n->id_prim_ctrl.vifrt = 0x2;
    n->id_prim_ctrl.vifrsm = 0x2;
    n->id_prim_ctrl.viprt = 0x02;

    return nvme_dma_read_prp(n, (uint8_t *)&n->id_prim_ctrl, sizeof(n->id_prim_ctrl),
        prp1, prp2);
}

static uint16_t nvme_identify(NvmeCtrl *n, NvmeCmd *cmd)
{
    NvmeIdentify *c = (NvmeIdentify *)cmd;

    switch (le32_to_cpu(c->cns)) {
    case NVME_ADM_CNS_ID_NS:
        return nvme_identify_ns(n, c);
    case NVME_ADM_CNS_ID_CTRL:
        return nvme_identify_ctrl(n, c);
    case NVME_ADM_CNS_ID_NS_LIST:
        return nvme_identify_nslist(n, c);
    case NVME_ADM_CNS_ID_NS_LIST_ALLOC:
        return nvme_identify_ns_allocated(n, c);
    case NVME_ADM_CNS_PRIM_CTRL_CAP:
        return nvme_identify_prim_ctrl_cap(n, c);
    case NVME_ADM_CNS_SEC_CTRL_LIST:
        return nvme_identify_sec_ctrl_list(n, c);

    default:
        return NVME_INVALID_FIELD | NVME_DNR;
    }
}

static uint16_t nvme_namespace_controller_attach(NvmeCtrl *n, NvmeCmd *cmd)
{
    int i;
    uint64_t prp1 = le64_to_cpu(cmd->prp1);
    uint64_t prp2 = le64_to_cpu(cmd->prp2);
    NvmeNamespace *ns = &n->namespaces[cmd->nsid - 1];

    uint16_t ctrl_list[2048];
    uint16_t ctrl_list_size;

    if (nvme_dma_write_prp(n, (uint8_t *)ctrl_list, sizeof(ctrl_list), prp1, prp2)) {
        return NVME_INVALID_FIELD;
    }

    ctrl_list_size = ctrl_list[0];

    if (!ctrl_list_size || ctrl_list_size > NVME_CTRL_LIST_MAX_ENTRIES) {
        return NVME_CTRL_LIST_INVALID;
    }

    if (ns->ctrl == n) {
        return NVME_NS_ALREADY_ATTACHED;
    }
    if (!ns->created) {
        return NVME_INVALID_NSID;
    }

    /*  TODO: update NvmeNamespace to link multiple controllers */
    for ( i = 1; i <= ctrl_list_size; i++) {
        if (n->id_ctrl.cntlid == ctrl_list[i]) {
            ns->ctrl = n;
            return NVME_SUCCESS;
        }
    }
    return NVME_CTRL_LIST_INVALID;
}

static uint16_t nvme_namespace_controller_detach(NvmeCtrl *n, NvmeCmd *cmd)
{
    int i;
    uint64_t prp1 = le64_to_cpu(cmd->prp1);
    uint64_t prp2 = le64_to_cpu(cmd->prp2);
    NvmeNamespace *ns = &n->namespaces[cmd->nsid - 1];

    uint16_t ctrl_list[2048];
    uint16_t ctrl_list_size;

    if (nvme_dma_write_prp(n, (uint8_t *)ctrl_list, sizeof(ctrl_list), prp1, prp2)) {
        return NVME_INVALID_FIELD;
    }

    ctrl_list_size = ctrl_list[0];

    if (!ctrl_list_size || ctrl_list_size > NVME_CTRL_LIST_MAX_ENTRIES) {
        return NVME_CTRL_LIST_INVALID;
    }
    /* TODO: semaphore to lock NS on detach for scenario with detach during IO */
    if (!ns->ctrl || (ns->ctrl != n) ) {
        return NVME_NS_NOT_ATTACHED;
    }
    if (!ns->created) {
        return NVME_INVALID_NSID;
    }

    /*  TODO: update NvmeNamespace to link multiple controllers */
    for ( i = 1; i <= ctrl_list_size; i++) {
        if (n->id_ctrl.cntlid == ctrl_list[i]) {
            ns->ctrl = NULL;
            return NVME_SUCCESS;
        }
    }
    return NVME_CTRL_LIST_INVALID;
}

static uint16_t nvme_namespace_attachment(NvmeCtrl *n, NvmeCmd *cmd)
{
    uint32_t dw10 = le32_to_cpu(cmd->cdw10);

    if ( (!cmd->nsid || cmd->nsid > NVME_MAX_NUM_NAMESPACES)
            && (cmd->nsid != 0xFFFFFFFF)) {
        return NVME_INVALID_FIELD;
    }

    switch (dw10) {
    case NVME_NS_CONTROLLER_ATTACH:
        return nvme_namespace_controller_attach(n, cmd);
    case NVME_NS_CONTROLLER_DETACH:
        return nvme_namespace_controller_detach(n, cmd);
    default:
        return NVME_INVALID_FIELD;
    }
}

static int nvme_set_start_index(NvmeCtrl *n, uint64_t *ns_start_index, uint64_t requested_ns_size)
{
    int i;
    int lba_index;
    uint64_t start_index = 0;
    uint64_t end_index, ns_bytes;
    bool adjusted;

    if (requested_ns_size > n->nvm_capacity) {
        return -1;
    }
    do {
        adjusted = false;
        end_index = start_index + requested_ns_size;
        if (end_index > n->nvm_capacity) {
            return -1;
        }

        for (i = 0; i < NVME_MAX_NUM_NAMESPACES; i++) {
            NvmeNamespace *ns = &n->namespaces[i];
            NvmeIdNs *id_ns = &ns->id_ns;
            if (ns->created) {

                lba_index = NVME_ID_NS_FLBAS_INDEX(ns->id_ns.flbas);
                ns_bytes = id_ns->nsze * ((1 << id_ns->lbaf[lba_index].ds));

                if ((start_index >= ns->start_byte_index &&
                       start_index < (ns->start_byte_index + ns_bytes)) ||
                       (end_index >= ns->start_byte_index &&
                        end_index < (ns->start_byte_index + ns_bytes))) {
                   start_index = ns->start_byte_index + ns_bytes;
                   adjusted = true;
                }
            }
        }
    } while (adjusted);

    *ns_start_index = start_index;
    return 0;
}

static uint16_t nvme_namespace_create(NvmeCtrl *n, NvmeCmd *cmd, NvmeRequest *req)
{
    int i;
    uint64_t prp1 = le64_to_cpu(cmd->prp1);
    uint64_t prp2 = le64_to_cpu(cmd->prp2);
    NvmeIdNs id_ns_host;


    if (nvme_dma_write_prp(n, (uint8_t*)&id_ns_host, sizeof(id_ns_host), prp1, prp2)) {
            return NVME_INVALID_FIELD;
    }

    for (i = 0; i < NVME_MAX_NUM_NAMESPACES; i++) {
        uint64_t ns_size;
        int lba_index;
        NvmeNamespace *ns = &n->namespaces[i];
        NvmeIdNs *id_ns = &ns->id_ns;

        if (id_ns_host.flbas || id_ns_host.mc || id_ns_host.dps) {
            return NVME_INVALID_FIELD | NVME_DNR;
        }

        if (!ns->created) { /* take the first available NS */

            id_ns->flbas = id_ns_host.flbas;
            id_ns->mc = id_ns_host.mc;
            id_ns->dps = id_ns_host.dps;

            id_ns->nuse = id_ns_host.nsze;
            id_ns->ncap = id_ns_host.ncap;
            id_ns->nsze = id_ns_host.nsze;

            lba_index = NVME_ID_NS_FLBAS_INDEX(id_ns->flbas);
            id_ns->lbaf[lba_index].ds = BDRV_SECTOR_BITS;
            ns_size = id_ns->nsze * (1 << id_ns->lbaf[lba_index].ds);
            id_ns->nvmcap = ns_size;

            ns->id = i + 1;

            if (nvme_set_start_index(n, &ns->start_byte_index, ns_size)) {
                return NVME_NS_INSUFF_CAP;
            }
            ns->created = true;
            n->id_ctrl.unvmcap -= id_ns->nvmcap;

            ns->ctrl = NULL; /* not attached */

            n->num_namespaces++;
            n->id_ctrl.nn++;

            req->cqe.result = ns->id;
            return NVME_SUCCESS;
        }
    }

    return NVME_NS_INSUFF_CAP;
}

static uint16_t nvme_namespace_delete(NvmeCtrl *n, NvmeCmd *cmd, NvmeRequest *req)
{
    NvmeNamespace *ns = &n->namespaces[cmd->nsid - 1];
    if (ns->created) {
        ns->created = false;
        ns->ctrl = NULL;
        n->num_namespaces--;
        n->id_ctrl.nn--;
        n->id_ctrl.unvmcap += ns->id_ns.nvmcap;
        return NVME_SUCCESS;
    }
    return NVME_INVALID_NSID;
}

static uint16_t nvme_namespace_management(NvmeCtrl *n, NvmeCmd *cmd, NvmeRequest *req)
{
    uint32_t dw10 = le32_to_cpu(cmd->cdw10);

    if ( (cmd->nsid > NVME_MAX_NUM_NAMESPACES)
            && (cmd->nsid != 0xFFFFFFFF)) {
        return NVME_INVALID_FIELD;
    }

    switch (dw10) {
        case NVME_NS_CREATE:
            return nvme_namespace_create(n, cmd, req);
        case NVME_NS_DELETE:
            if ( cmd->nsid == 0xFFFFFFFF ) {
                uint32_t i;
                uint16_t ret = NVME_SUCCESS;

                for (i = 1; i < NVME_MAX_NUM_NAMESPACES; i++) {
                    cmd->nsid = i;
                    if ( &n->namespaces[cmd->nsid - 1].created) {
                        ret = nvme_namespace_delete(n, cmd, req);
                    }
                    if (ret != NVME_SUCCESS) {
                        return ret;
                    }
                }
                return ret;
            }
            return nvme_namespace_delete(n, cmd, req);
        default:
            return NVME_INVALID_FIELD;
    }
}

static uint16_t nvme_virtualization_management(NvmeCtrl *n, NvmeCmd *cmd, NvmeRequest *req)
{
    uint32_t dw10 = le32_to_cpu(cmd->cdw10);
    uint32_t dw11 = le32_to_cpu(cmd->cdw11);
    uint8_t  act    = dw10 & 0x000F;
    uint8_t  rt     = (dw10 & 0x0070) >> 8;
    uint16_t cntlid = (dw10 >> 16);
    uint16_t nr     = dw11 & 0x00FF;
    uint32_t nrm = 0;
    int i;
    NvmeCtrl *sec_n;

    switch(act) {
    case NVME_VIRT_MGMT_PRIM_CTRL_FLEX_ALLOC:
        if (cntlid != n->id_ctrl.cntlid)
        {
            return NVME_INVALID_CTRL_ID;
        }
        switch (rt) {
        case 0x0:
            if (nr <= (n->id_prim_ctrl.vqfrt - n->id_prim_ctrl.vqrfa))
            {
                n->id_prim_ctrl.vqrfap = nr;
                nrm += nr;
            }
            break;
        case 0x1:
            if (nr <= (n->id_prim_ctrl.vifrt - n->id_prim_ctrl.virfa))
            {
                n->id_prim_ctrl.virfap = nr;
                nrm += nr;
            }
            break;
        default:
            return NVME_INVALID_FIELD;
            break;
        }
        break;
    case NVME_VIRT_MGMT_SEC_CTRL_OFFLINE:
        /*?? need to handle individual cases as well*/
        for(i = 0; i < prim_ctrl->num_vfs; i++)
        {
//            sec_n = prim_ctrl->secondary_ctrl_list[i];
//            nvme_write_bar(sec_n, 0x14, NVME_CC_EN(0), 0);
            nrm++;
        }
        break;
    case NVME_VIRT_MGMT_SEC_CTRL_ASSIGN_RES:
        if (cntlid == prim_ctrl->id_ctrl.cntlid) {
            return NVME_INVALID_CTRL_ID;
        }
        sec_n = prim_ctrl->secondary_ctrl_list[cntlid -1];
        switch (rt) {
            case 0x0:
                sec_n->nvq = nr;
                nrm += nr;
                break;
            case 0x1:
                sec_n->nvi = nr;
                nrm += nr;
                break;
            default:
                return NVME_INVALID_FIELD;
                break;
        }
        break;
    case NVME_VIRT_MGMT_SEC_CTRL_ONLINE:
        /*?? need to handle individual cases as well*/
        for(i = 0; i < prim_ctrl->num_vfs; i++)
        {
//            sec_n = prim_ctrl->secondary_ctrl_list[i];
//            nvme_write_bar(sec_n, 0x14, NVME_CC_EN(1), 0);
            nrm++;
        }
        break;
    default:
        return NVME_INVALID_RES_ID;

    }


    req->cqe.result = nrm;
    return NVME_SUCCESS;
}

static uint16_t nvme_get_host_mem_buff(NvmeCtrl *n, NvmeCmd *cmd, NvmeRequest *req)
{
    static const int data_len = 4096;
        uint64_t prp1 = le64_to_cpu(cmd->prp1);
        uint64_t prp2 = le64_to_cpu(cmd->prp2);
        uint32_t *list;
        uint16_t ret;

        list = g_malloc0(data_len);
        list[0] = n->hsize;
        list[1] = n->hmdlal;
        list[2] = n->hmdlua;
        list[3] = n->hmdlec;

        ret = nvme_dma_read_prp(n, (uint8_t *)list, data_len, prp1, prp2);
        g_free(list);
        return ret;
}

static uint16_t nvme_get_feature(NvmeCtrl *n, NvmeCmd *cmd, NvmeRequest *req)
{
    uint32_t dw10 = le32_to_cpu(cmd->cdw10);
    uint32_t result;



    switch (dw10) {
    case NVME_VOLATILE_WRITE_CACHE:
        result = blk_enable_write_cache(n->conf.blk);
        break;
    case NVME_NUMBER_OF_QUEUES:
        result = cpu_to_le32((n->num_queues - 2) | ((n->num_queues - 2) << 16));
        break;
    case NVME_HOST_MEM_BUF:
        result = nvme_get_host_mem_buff(n, cmd, req);
        break;
    default:
        return NVME_INVALID_FIELD | NVME_DNR;
    }

    req->cqe.result = result;
    return NVME_SUCCESS;
}

static uint16_t nvme_set_feature(NvmeCtrl *n, NvmeCmd *cmd, NvmeRequest *req)
{
    uint32_t dw10 = le32_to_cpu(cmd->cdw10);
    uint32_t dw11 = le32_to_cpu(cmd->cdw11);
    uint32_t dw12 = le32_to_cpu(cmd->cdw12);
    uint32_t dw13 = le32_to_cpu(cmd->cdw13);
    uint32_t dw14 = le32_to_cpu(cmd->cdw14);
    uint32_t dw15 = le32_to_cpu(cmd->cdw15);

    switch (dw10) {
    case NVME_VOLATILE_WRITE_CACHE:
        blk_set_enable_write_cache(n->conf.blk, dw11 & 1);
        break;
    case NVME_NUMBER_OF_QUEUES:
        req->cqe.result =
            cpu_to_le32((n->num_queues - 2) | ((n->num_queues - 2) << 16));
        break;
    case NVME_HOST_MEM_BUF:
        n->ehm = dw11 & 0x1;
        n->hsize = dw12;
        n->hmdlal = dw13 & 0xFFFFFFFF0;
        n->hmdlua = dw14;
        n->hmdlec = dw15;
        break;
    default:
        return NVME_INVALID_FIELD | NVME_DNR;
    }
    return NVME_SUCCESS;
}

static uint16_t nvme_admin_cmd(NvmeCtrl *n, NvmeCmd *cmd, NvmeRequest *req)
{
    switch (cmd->opcode) {
    case NVME_ADM_CMD_DELETE_SQ:
        return nvme_del_sq(n, cmd);
    case NVME_ADM_CMD_CREATE_SQ:
        return nvme_create_sq(n, cmd);
    case NVME_ADM_CMD_DELETE_CQ:
        return nvme_del_cq(n, cmd);
    case NVME_ADM_CMD_CREATE_CQ:
        return nvme_create_cq(n, cmd);
    case NVME_ADM_CMD_IDENTIFY:
        return nvme_identify(n, cmd);
    case NVME_ADM_CMD_SET_FEATURES:
        return nvme_set_feature(n, cmd, req);
    case NVME_ADM_CMD_GET_FEATURES:
        return nvme_get_feature(n, cmd, req);
    case NVME_ADM_CMD_NS_MANAGEMENT:
        return nvme_namespace_management(n, cmd, req);
    case NVME_ADM_CMD_NS_ATTACH:
        return nvme_namespace_attachment(n, cmd);
    case NVME_ADM_VIRT_MANAGEMENT:
        return nvme_virtualization_management(n, cmd, req);
    default:
        return NVME_INVALID_OPCODE | NVME_DNR;
    }
}

static void nvme_process_sq(void *opaque)
{
    NvmeSQueue *sq = opaque;
    NvmeCtrl *n = sq->ctrl;
    NvmeCQueue *cq = n->cq[sq->cqid];

    uint16_t status;
    hwaddr addr;
    NvmeCmd cmd;
    NvmeRequest *req;

    while (!(nvme_sq_empty(sq) || QTAILQ_EMPTY(&sq->req_list))) {
        addr = sq->dma_addr + sq->head * n->sqe_size;
        nvme_addr_read(n, addr, (void *)&cmd, sizeof(cmd));
        nvme_inc_sq_head(sq);

        req = QTAILQ_FIRST(&sq->req_list);
        QTAILQ_REMOVE(&sq->req_list, req, entry);
        QTAILQ_INSERT_TAIL(&sq->out_req_list, req, entry);
        memset(&req->cqe, 0, sizeof(req->cqe));
        req->cqe.cid = cmd.cid;

        status = sq->sqid ? nvme_io_cmd(n, &cmd, req) :
            nvme_admin_cmd(n, &cmd, req);
        if (status != NVME_NO_COMPLETE) {
            req->status = status;
            nvme_enqueue_req_completion(cq, req);
        }
    }
}

static void nvme_clear_ctrl(NvmeCtrl *n)
{
    int i;

    for (i = 0; i < n->num_queues; i++) {
        if (n->sq[i] != NULL) {
            nvme_free_sq(n->sq[i], n);
        }
    }
    for (i = 0; i < n->num_queues; i++) {
        if (n->cq[i] != NULL) {
            nvme_free_cq(n->cq[i], n);
        }
    }

    if(!pci_is_vf(&n->parent_obj))
    {
        blk_flush(n->conf.blk);
    }
    n->bar.cc = 0;
}

static int nvme_start_ctrl(NvmeCtrl *n)
{
    uint32_t page_bits = NVME_CC_MPS(n->bar.cc) + 12;
    uint32_t page_size = 1 << page_bits;

    if (n->cq[0] || n->sq[0] || !n->bar.asq || !n->bar.acq ||
            n->bar.asq & (page_size - 1) || n->bar.acq & (page_size - 1) ||
            NVME_CC_MPS(n->bar.cc) < NVME_CAP_MPSMIN(n->bar.cap) ||
            NVME_CC_MPS(n->bar.cc) > NVME_CAP_MPSMAX(n->bar.cap) ||
            NVME_CC_IOCQES(n->bar.cc) < NVME_CTRL_CQES_MIN(n->id_ctrl.cqes) ||
            NVME_CC_IOCQES(n->bar.cc) > NVME_CTRL_CQES_MAX(n->id_ctrl.cqes) ||
            NVME_CC_IOSQES(n->bar.cc) < NVME_CTRL_SQES_MIN(n->id_ctrl.sqes) ||
            NVME_CC_IOSQES(n->bar.cc) > NVME_CTRL_SQES_MAX(n->id_ctrl.sqes) ||
            !NVME_AQA_ASQS(n->bar.aqa) || !NVME_AQA_ACQS(n->bar.aqa)) {
        return -1;
    }

    n->page_bits = page_bits;
    n->page_size = page_size;
    n->max_prp_ents = n->page_size / sizeof(uint64_t);
    n->cqe_size = 1 << NVME_CC_IOCQES(n->bar.cc);
    n->sqe_size = 1 << NVME_CC_IOSQES(n->bar.cc);
    nvme_init_cq(&n->admin_cq, n, n->bar.acq, 0, 0,
        NVME_AQA_ACQS(n->bar.aqa) + 1, 1);
    nvme_init_sq(&n->admin_sq, n, n->bar.asq, 0, 0,
        NVME_AQA_ASQS(n->bar.aqa) + 1);

    return 0;
}

static void nvme_write_bar(NvmeCtrl *n, hwaddr offset, uint64_t data,
    unsigned size)
{
    switch (offset) {
    case 0xc:
        n->bar.intms |= data & 0xffffffff;
        n->bar.intmc = n->bar.intms;
        break;
    case 0x10:
        n->bar.intms &= ~(data & 0xffffffff);
        n->bar.intmc = n->bar.intms;
        break;
    case 0x14:
        /* Windows first sends data, then sends enable bit */
        if (!NVME_CC_EN(data) && !NVME_CC_EN(n->bar.cc) &&
            !NVME_CC_SHN(data) && !NVME_CC_SHN(n->bar.cc))
        {
            n->bar.cc = data;
        }

        if (NVME_CC_EN(data) && !NVME_CC_EN(n->bar.cc)) {
            n->bar.cc = data;
            if (nvme_start_ctrl(n)) {
                n->bar.csts = NVME_CSTS_FAILED;
            } else {
                n->bar.csts = NVME_CSTS_READY;
            }
        } else if (!NVME_CC_EN(data) && NVME_CC_EN(n->bar.cc)) {
            nvme_clear_ctrl(n);
            n->bar.csts &= ~NVME_CSTS_READY;
        }
        if (NVME_CC_SHN(data) && !(NVME_CC_SHN(n->bar.cc))) {
                nvme_clear_ctrl(n);
                n->bar.cc = data;
                n->bar.csts |= NVME_CSTS_SHST_COMPLETE;
        } else if (!NVME_CC_SHN(data) && NVME_CC_SHN(n->bar.cc)) {
                n->bar.csts &= ~NVME_CSTS_SHST_COMPLETE;
                n->bar.cc = data;
        }
        break;
    case 0x24:
        n->bar.aqa = data & 0xffffffff;
        break;
    case 0x28:
        n->bar.asq = data;
        break;
    case 0x2c:
        n->bar.asq |= data << 32;
        break;
    case 0x30:
        n->bar.acq = data;
        break;
    case 0x34:
        n->bar.acq |= data << 32;
        break;
    default:
        break;
    }
}

static uint64_t nvme_mmio_read(void *opaque, hwaddr addr, unsigned size)
{
    NvmeCtrl *n = (NvmeCtrl *)opaque;
    uint8_t *ptr = (uint8_t *)&n->bar;
    uint64_t val = 0;

    if (addr < sizeof(n->bar)) {
        memcpy(&val, ptr + addr, size);
    }
    return val;
}

static void nvme_process_db(NvmeCtrl *n, hwaddr addr, int val)
{
    uint32_t qid;

    if (addr & ((1 << 2) - 1)) {
        return;
    }

    if (((addr - 0x1000) >> 2) & 1) {
        uint16_t new_head = val & 0xffff;
        int start_sqs;
        NvmeCQueue *cq;

        qid = (addr - (0x1000 + (1 << 2))) >> 3;
        if (nvme_check_cqid(n, qid)) {
            return;
        }

        cq = n->cq[qid];
        if (new_head >= cq->size) {
            return;
        }

        start_sqs = nvme_cq_full(cq) ? 1 : 0;
        cq->head = new_head;
        if (start_sqs) {
            NvmeSQueue *sq;
            QTAILQ_FOREACH(sq, &cq->sq_list, entry) {
                timer_mod(sq->timer, qemu_clock_get_ns(QEMU_CLOCK_VIRTUAL) + 500);
            }
            timer_mod(cq->timer, qemu_clock_get_ns(QEMU_CLOCK_VIRTUAL) + 500);
        }

        if (cq->tail != cq->head) {
            nvme_isr_notify(n, cq);
        }
    } else {
        uint16_t new_tail = val & 0xffff;
        NvmeSQueue *sq;

        qid = (addr - 0x1000) >> 3;
        if (nvme_check_sqid(n, qid)) {
            return;
        }

        sq = n->sq[qid];
        if (new_tail >= sq->size) {
            return;
        }

        sq->tail = new_tail;
        timer_mod(sq->timer, qemu_clock_get_ns(QEMU_CLOCK_VIRTUAL) + 500);
    }
}

static void nvme_mmio_write(void *opaque, hwaddr addr, uint64_t data,
    unsigned size)
{
    NvmeCtrl *n = (NvmeCtrl *)opaque;
    if (addr < sizeof(n->bar)) {
        nvme_write_bar(n, addr, data, size);
    } else if (addr >= 0x1000) {
        nvme_process_db(n, addr, data);
    }
}

static const MemoryRegionOps nvme_mmio_ops = {
    .read = nvme_mmio_read,
    .write = nvme_mmio_write,
    .endianness = DEVICE_LITTLE_ENDIAN,
    .impl = {
        .min_access_size = 2,
        .max_access_size = 8,
    },
};

static void nvme_cmb_write(void *opaque, hwaddr addr, uint64_t data,
    unsigned size)
{
    NvmeCtrl *n = (NvmeCtrl *)opaque;
    memcpy(&n->cmbuf[addr], &data, size);
}

static uint64_t nvme_cmb_read(void *opaque, hwaddr addr, unsigned size)
{
    uint64_t val;
    NvmeCtrl *n = (NvmeCtrl *)opaque; cpu_to_le32((n->num_queues - 2) | ((n->num_queues - 2) << 16));

    memcpy(&val, &n->cmbuf[addr], size);
    return val;
}

static const MemoryRegionOps nvme_cmb_ops = {
    .read = nvme_cmb_read,
    .write = nvme_cmb_write,
    .endianness = DEVICE_LITTLE_ENDIAN,
    .impl = {
        .min_access_size = 2,
        .max_access_size = 8,
    },
};


static void nvme_init_ctrl(NvmeCtrl *n)
{
    NvmeIdCtrl *id = &n->id_ctrl;
    uint8_t *pci_conf = n->parent_obj.config;

    id->vid = cpu_to_le16(pci_get_word(pci_conf + PCI_VENDOR_ID));
    id->ssvid = cpu_to_le16(pci_get_word(pci_conf + PCI_SUBSYSTEM_VENDOR_ID));
    strpadcpy((char *)id->mn, sizeof(id->mn), "QEMU NVMe Ctrl", ' ');
    strpadcpy((char *)id->fr, sizeof(id->fr), "1.0", ' ');
    strpadcpy((char *)id->sn, sizeof(id->sn), "bada55", ' ');
    id->rab = 6;
    id->ieee[0] = 0x00;
    id->ieee[1] = 0x02;
    id->ieee[2] = 0xb3;
    id->oacs = cpu_to_le16(0);
    id->oacs |= BIT(7);
    id->frmw = 7 << 1;
    id->lpa = 1 << 0;
    id->sqes = (0x6 << 4) | 0x6;
    id->cqes = (0x4 << 4) | 0x4;
    id->nn = cpu_to_le32(n->num_namespaces);
    id->oncs = cpu_to_le16(NVME_ONCS_WRITE_ZEROS);
    id->psd[0].mp = cpu_to_le16(0x9c4);
    id->psd[0].enlat = cpu_to_le32(0x10);
    id->psd[0].exlat = cpu_to_le32(0x4);
    id->tnvmcap = n->nvm_capacity;
    id->unvmcap = 0;
    id->hmpre = n->hmpre;
    id->hmmin = n->hmmin;

    if (!pci_is_vf(&n->parent_obj))
    {
        if (blk_enable_write_cache(n->conf.blk)) {
            id->vwc = 1;
        }
    }

    n->bar.cap = 0;
    NVME_CAP_SET_MQES(n->bar.cap, 0x7ff);
    NVME_CAP_SET_CQR(n->bar.cap, 1);
    NVME_CAP_SET_AMS(n->bar.cap, 1);
    NVME_CAP_SET_TO(n->bar.cap, 0xf);
    NVME_CAP_SET_CSS(n->bar.cap, 1);
    NVME_CAP_SET_MPSMIN(n->bar.cap, 0);
    NVME_CAP_SET_MPSMAX(n->bar.cap, 4);

    n->bar.intmc = n->bar.intms = 0;
    n->bar.vs = 0x00010300;

}

static void nvme_init_pci(NvmeCtrl *n)
{
    uint8_t *pci_conf = n->parent_obj.config;

    pci_conf[PCI_INTERRUPT_PIN] = 1;
    pci_config_set_prog_interface(pci_conf, 0x2);
    pci_config_set_class(pci_conf, PCI_CLASS_STORAGE_EXPRESS);

    if (pci_is_vf(&n->parent_obj)) {
        pcie_endpoint_cap_init(&n->parent_obj, 0x80);
    } else {
        pci_config_set_device_id(pci_conf, 0x5845);
        pcie_endpoint_cap_init(&n->parent_obj, 0x80);
    }

    memory_region_init_io(&n->iomem, OBJECT(n), &nvme_mmio_ops, n, "nvme",
        n->reg_size);

    if (pci_is_vf(&n->parent_obj)) {
        pcie_sriov_vf_register_bar(&n->parent_obj, 0, &n->iomem);

    } else {
        pci_register_bar(&n->parent_obj, 0,
            PCI_BASE_ADDRESS_SPACE_MEMORY | PCI_BASE_ADDRESS_MEM_TYPE_64,
            &n->iomem);
        if(n->sriov_total_vfs) {
//            pcie_ari_init(&n->parent_obj, 0x100, 2);
            pcie_sriov_pf_init(&n->parent_obj, 0x100, "nvme", 0x5845,
                    n->sriov_total_vfs, n->sriov_total_vfs, 0x1, 0x1);
            pcie_sriov_pf_init_vf_bar(&n->parent_obj, 0x0, PCI_BASE_ADDRESS_MEM_TYPE_64, 0x4000);

        }
    }

    msix_init_exclusive_bar(&n->parent_obj, n->num_queues, 4, NULL);
//    msi_init(&n->parent_obj, 0x50, 32, true, false, NULL);

    /*broken with sriov*/
    if (!pci_is_vf(&n->parent_obj)) {

        if (n->cmb_size_mb) {

            NVME_CMBLOC_SET_BIR(n->bar.cmbloc, 2);
            NVME_CMBLOC_SET_OFST(n->bar.cmbloc, 0);

            NVME_CMBSZ_SET_SQS(n->bar.cmbsz, 1);
            NVME_CMBSZ_SET_CQS(n->bar.cmbsz, 1);
            NVME_CMBSZ_SET_LISTS(n->bar.cmbsz, 0);
            NVME_CMBSZ_SET_RDS(n->bar.cmbsz, 1);
            NVME_CMBSZ_SET_WDS(n->bar.cmbsz, 1);
            NVME_CMBSZ_SET_SZU(n->bar.cmbsz, 2); /* MBs */
            NVME_CMBSZ_SET_SZ(n->bar.cmbsz, n->cmb_size_mb);

            n->cmbloc = n->bar.cmbloc;
            n->cmbsz = n->bar.cmbsz;

            n->cmbuf = g_malloc0(NVME_CMBSZ_GETSIZE(n->bar.cmbsz));
            memory_region_init_io(&n->ctrl_mem, OBJECT(n), &nvme_cmb_ops, n,
                                  "nvme-cmb", NVME_CMBSZ_GETSIZE(n->bar.cmbsz));
            pci_register_bar(&n->parent_obj, NVME_CMBLOC_BIR(n->bar.cmbloc),
                PCI_BASE_ADDRESS_SPACE_MEMORY | PCI_BASE_ADDRESS_MEM_TYPE_64 |
                PCI_BASE_ADDRESS_MEM_PREFETCH, &n->ctrl_mem);
        }
    }

}

static void nvme_init_namespaces(NvmeCtrl *n)
{
    int i;

    for (i = 0; i < n->num_namespaces; i++) {
        uint64_t blks;
        int lba_index;
        NvmeNamespace *ns = &n->namespaces[i];
        NvmeIdNs *id_ns = &ns->id_ns;

        id_ns->nsfeat = 0;
        id_ns->nlbaf = 0;
        id_ns->flbas = 0;
        id_ns->mc = 0;
        id_ns->dpc = 0;
        id_ns->dps = 0;
        id_ns->lbaf[0].ds = BDRV_SECTOR_BITS;

        lba_index = NVME_ID_NS_FLBAS_INDEX(ns->id_ns.flbas);
        blks = n->nvm_capacity / (1 << id_ns->lbaf[lba_index].ds);
        id_ns->nuse = id_ns->ncap = id_ns->nsze = cpu_to_le64(blks);
        id_ns->nvmcap = id_ns->nsze * (1 << id_ns->lbaf[lba_index].ds);

        ns->id = i + 1;
        ns->start_byte_index = i * n->nvm_capacity >> BDRV_SECTOR_BITS;
        ns->created = true;
        ns->ctrl = n; /* attached */

    }
}

static int nvme_init(PCIDevice *pci_dev)
{
    NvmeCtrl *n = NVME(pci_dev);

    int64_t bs_size;
    Error *local_err = NULL;

    if (!pci_is_vf(pci_dev))
    {
        prim_ctrl = n;
        prim_ctrl->secondary_ctrl_list = g_new0(NvmeCtrl *, n->sriov_total_vfs);

        if (!n->conf.blk) {
            return -1;
        }

        bs_size = blk_getlength(n->conf.blk);
        if (bs_size < 0) {
            return -1;
        }

        blkconf_serial(&n->conf, &n->serial);
        if (!n->serial) {
            return -1;
        }
        blkconf_blocksizes(&n->conf);
        blkconf_apply_backend_options(&n->conf, blk_is_read_only(n->conf.blk),
                                      false, &local_err);
    }
    if (local_err) {
        error_report_err(local_err);
        return -1;
    }
    if (pci_is_vf(pci_dev))
    {
        /* link the block device to the secondary controller */
        n->conf.blk = prim_ctrl->conf.blk;
        /* add secondary controllers to the primary controller list */
        prim_ctrl->secondary_ctrl_list[prim_ctrl->num_vfs] = n;
        prim_ctrl->num_vfs++;
        n->id_ctrl.cntlid = prim_ctrl->num_vfs;
    }

    n->num_queues = 64;

    n->reg_size = pow2ceil(0x1004 + 2 * (n->num_queues + 1) * 4);
    n->nvm_capacity = bs_size / (uint64_t)n->num_namespaces;

    n->sq = g_new0(NvmeSQueue *, n->num_queues);
    n->cq = g_new0(NvmeCQueue *, n->num_queues);
    n->namespaces = g_new0(NvmeNamespace, NVME_MAX_NUM_NAMESPACES);

    nvme_init_pci(n);
    nvme_init_ctrl(n);
    nvme_init_namespaces(n);

    return 0;
}

static void nvme_exit(PCIDevice *pci_dev)
{
    NvmeCtrl *n = NVME(pci_dev);

    if (pci_is_vf(&n->parent_obj))
    {
        prim_ctrl->num_vfs--;
    }
    nvme_clear_ctrl(n);
    g_free(n->namespaces);
    g_free(n->cq);
    g_free(n->sq);
    if (n->cmbsz) {
        memory_region_unref(&n->ctrl_mem);
    }

    msix_uninit_exclusive_bar(pci_dev);
}

static Property nvme_props[] = {
    DEFINE_BLOCK_PROPERTIES(NvmeCtrl, conf),
    DEFINE_PROP_STRING("serial", NvmeCtrl, serial),
    DEFINE_PROP_UINT32("namespaces", NvmeCtrl, num_namespaces, 1),
    DEFINE_PROP_UINT32("cmb_size_mb", NvmeCtrl, cmb_size_mb, 0),
    DEFINE_PROP_UINT32("sriov_total_vfs", NvmeCtrl, sriov_total_vfs, 2),
    DEFINE_PROP_UINT32("hmpre", NvmeCtrl, hmpre, 0),
    DEFINE_PROP_UINT32("hmmin", NvmeCtrl, hmmin, 0),

    DEFINE_PROP_END_OF_LIST(),
};

static const VMStateDescription nvme_vmstate = {
    .name = "nvme",
    .unmigratable = 1,
};

static void nvme_pci_reset(DeviceState *dev)
{

}

static void nvme_class_init(ObjectClass *oc, void *data)
{
    DeviceClass *dc = DEVICE_CLASS(oc);
    PCIDeviceClass *pc = PCI_DEVICE_CLASS(oc);

    pc->init = nvme_init;
    pc->exit = nvme_exit;
    pc->class_id = PCI_CLASS_STORAGE_EXPRESS;
    pc->vendor_id = PCI_VENDOR_ID_INTEL;
    pc->device_id = 0x5845;
    pc->revision = 2;
    pc->is_express = 1;

    set_bit(DEVICE_CATEGORY_STORAGE, dc->categories);
    dc->desc = "Non-Volatile Memory Express";
    dc->props = nvme_props;
    dc->vmsd = &nvme_vmstate;
    dc->reset = nvme_pci_reset;
}

static void nvme_instance_init(Object *obj)
{
    NvmeCtrl *s = NVME(obj);

    device_add_bootindex_property(obj, &s->conf.bootindex,
                                  "bootindex", "/namespace@1,0",
                                  DEVICE(obj), &error_abort);
}

static const TypeInfo nvme_info = {
    .name          = "nvme",
    .parent        = TYPE_PCI_DEVICE,
    .instance_size = sizeof(NvmeCtrl),
    .class_init    = nvme_class_init,
    .instance_init = nvme_instance_init,
};


static void nvme_register_types(void)
{
    type_register_static(&nvme_info);
}

type_init(nvme_register_types)

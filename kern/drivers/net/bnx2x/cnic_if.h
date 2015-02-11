/* cnic_if.h: QLogic CNIC core network driver.
 *
 * Copyright (c) 2006-2014 Broadcom Corporation
 * Copyright (c) 2014 QLogic Corporation
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation.
 *
 */


#ifndef CNIC_IF_H
#define CNIC_IF_H

#include "bnx2x_mfw_req.h"

#define CNIC_MODULE_VERSION	"2.5.20"
#define CNIC_MODULE_RELDATE	"March 14, 2014"

#define CNIC_ULP_RDMA		0
#define CNIC_ULP_ISCSI		1
#define CNIC_ULP_FCOE		2
#define CNIC_ULP_L4		3
#define MAX_CNIC_ULP_TYPE_EXT	3
#define MAX_CNIC_ULP_TYPE	4

/* Use CPU native page size up to 16K for cnic ring sizes.  */
#if (PAGE_SHIFT > 14)
#define CNIC_PAGE_BITS	14
#else
#define CNIC_PAGE_BITS	PAGE_SHIFT
#endif
#define CNIC_PAGE_SIZE	(1 << (CNIC_PAGE_BITS))
#define CNIC_PAGE_ALIGN(addr) ALIGN(addr, CNIC_PAGE_SIZE)
#define CNIC_PAGE_MASK	(~((CNIC_PAGE_SIZE) - 1))

struct kwqe {
	uint32_t kwqe_op_flag;

#define KWQE_QID_SHIFT		8
#define KWQE_OPCODE_MASK	0x00ff0000
#define KWQE_OPCODE_SHIFT	16
#define KWQE_OPCODE(x)		((x & KWQE_OPCODE_MASK) >> KWQE_OPCODE_SHIFT)
#define KWQE_LAYER_MASK			0x70000000
#define KWQE_LAYER_SHIFT		28
#define KWQE_FLAGS_LAYER_MASK_L2	(2<<28)
#define KWQE_FLAGS_LAYER_MASK_L3	(3<<28)
#define KWQE_FLAGS_LAYER_MASK_L4	(4<<28)
#define KWQE_FLAGS_LAYER_MASK_L5_RDMA	(5<<28)
#define KWQE_FLAGS_LAYER_MASK_L5_ISCSI	(6<<28)
#define KWQE_FLAGS_LAYER_MASK_L5_FCOE	(7<<28)

	uint32_t kwqe_info0;
	uint32_t kwqe_info1;
	uint32_t kwqe_info2;
	uint32_t kwqe_info3;
	uint32_t kwqe_info4;
	uint32_t kwqe_info5;
	uint32_t kwqe_info6;
};

struct kwqe_16 {
	uint32_t kwqe_info0;
	uint32_t kwqe_info1;
	uint32_t kwqe_info2;
	uint32_t kwqe_info3;
};

struct kcqe {
	uint32_t kcqe_info0;
	uint32_t kcqe_info1;
	uint32_t kcqe_info2;
	uint32_t kcqe_info3;
	uint32_t kcqe_info4;
	uint32_t kcqe_info5;
	uint32_t kcqe_info6;
	uint32_t kcqe_op_flag;
		#define KCQE_RAMROD_COMPLETION		(0x1<<27) /* Everest */
		#define KCQE_FLAGS_LAYER_MASK		(0x7<<28)
		#define KCQE_FLAGS_LAYER_MASK_MISC	(0<<28)
		#define KCQE_FLAGS_LAYER_MASK_L2	(2<<28)
		#define KCQE_FLAGS_LAYER_MASK_L3	(3<<28)
		#define KCQE_FLAGS_LAYER_MASK_L4	(4<<28)
		#define KCQE_FLAGS_LAYER_MASK_L5_RDMA	(5<<28)
		#define KCQE_FLAGS_LAYER_MASK_L5_ISCSI	(6<<28)
		#define KCQE_FLAGS_LAYER_MASK_L5_FCOE	(7<<28)
		#define KCQE_FLAGS_NEXT 		(1<<31)
		#define KCQE_FLAGS_OPCODE_MASK		(0xff<<16)
		#define KCQE_FLAGS_OPCODE_SHIFT		(16)
		#define KCQE_OPCODE(op)			\
		(((op) & KCQE_FLAGS_OPCODE_MASK) >> KCQE_FLAGS_OPCODE_SHIFT)
};

#define MAX_CNIC_CTL_DATA	64
#define MAX_DRV_CTL_DATA	64

#define CNIC_CTL_STOP_CMD		1
#define CNIC_CTL_START_CMD		2
#define CNIC_CTL_COMPLETION_CMD		3
#define CNIC_CTL_STOP_ISCSI_CMD		4
#define CNIC_CTL_FCOE_STATS_GET_CMD	5
#define CNIC_CTL_ISCSI_STATS_GET_CMD	6

#define DRV_CTL_IO_WR_CMD		0x101
#define DRV_CTL_IO_RD_CMD		0x102
#define DRV_CTL_CTX_WR_CMD		0x103
#define DRV_CTL_CTXTBL_WR_CMD		0x104
#define DRV_CTL_RET_L5_SPQ_CREDIT_CMD	0x105
#define DRV_CTL_START_L2_CMD		0x106
#define DRV_CTL_STOP_L2_CMD		0x107
#define DRV_CTL_RET_L2_SPQ_CREDIT_CMD	0x10c
#define DRV_CTL_ISCSI_STOPPED_CMD	0x10d
#define DRV_CTL_ULP_REGISTER_CMD	0x10e
#define DRV_CTL_ULP_UNREGISTER_CMD	0x10f

struct cnic_ctl_completion {
	uint32_t	cid;
	uint8_t	opcode;
	uint8_t	error;
};

struct cnic_ctl_info {
	int	cmd;
	union {
		struct cnic_ctl_completion comp;
		char bytes[MAX_CNIC_CTL_DATA];
	} data;
};

struct drv_ctl_spq_credit {
	uint32_t	credit_count;
};

struct drv_ctl_io {
	uint32_t		cid_addr;
	uint32_t		offset;
	uint32_t		data;
	dma_addr_t	dma_addr;
};

struct drv_ctl_l2_ring {
	uint32_t		client_id;
	uint32_t		cid;
};

struct drv_ctl_register_data {
	int ulp_type;
	struct fcoe_capabilities fcoe_features;
};

struct drv_ctl_info {
	int	cmd;
	union {
		struct drv_ctl_spq_credit credit;
		struct drv_ctl_io io;
		struct drv_ctl_l2_ring ring;
		int ulp_type;
		struct drv_ctl_register_data register_data;
		char bytes[MAX_DRV_CTL_DATA];
	} data;
};

struct cnic_ops {
	struct module	*cnic_owner;
	/* Calls to these functions are protected by RCU.  When
	 * unregistering, we wait for any calls to complete before
	 * continuing.
	 */
	int		(*cnic_handler)(void *, void *);
	int		(*cnic_ctl)(void *, struct cnic_ctl_info *);
};

#define MAX_CNIC_VEC	8

struct cnic_irq {
	unsigned int	vector;
	void		*status_blk;
	uint32_t		status_blk_num;
	uint32_t		status_blk_num2;
	uint32_t		irq_flags;
#define CNIC_IRQ_FL_MSIX		0x00000001
};

struct cnic_eth_dev {
	struct module	*drv_owner;
	uint32_t		drv_state;
#define CNIC_DRV_STATE_REGD		0x00000001
#define CNIC_DRV_STATE_USING_MSIX	0x00000002
#define CNIC_DRV_STATE_NO_ISCSI_OOO	0x00000004
#define CNIC_DRV_STATE_NO_ISCSI		0x00000008
#define CNIC_DRV_STATE_NO_FCOE		0x00000010
#define CNIC_DRV_STATE_HANDLES_IRQ	0x00000020
	uint32_t		chip_id;
	uint32_t		max_kwqe_pending;
	struct pci_device	*pdev;
	void __iomem	*io_base;
	void __iomem	*io_base2;
	const void	*iro_arr;

	uint32_t		ctx_tbl_offset;
	uint32_t		ctx_tbl_len;
	int		ctx_blk_size;
	uint32_t		starting_cid;
	uint32_t		max_iscsi_conn;
	uint32_t		max_fcoe_conn;
	uint32_t		max_rdma_conn;
	uint32_t		fcoe_init_cid;
	uint32_t		max_fcoe_exchanges;
	uint32_t		fcoe_wwn_port_name_hi;
	uint32_t		fcoe_wwn_port_name_lo;
	uint32_t		fcoe_wwn_node_name_hi;
	uint32_t		fcoe_wwn_node_name_lo;

	uint16_t		iscsi_l2_client_id;
	uint16_t		iscsi_l2_cid;
	uint8_t		iscsi_mac[Eaddrlen];

	int		num_irq;
	struct cnic_irq	irq_arr[MAX_CNIC_VEC];
	int		(*drv_register_cnic)(struct ether *,
					     struct cnic_ops *, void *);
	int		(*drv_unregister_cnic)(struct ether *);
	int		(*drv_submit_kwqes_32)(struct ether *,
					       struct kwqe *[], uint32_t);
	int		(*drv_submit_kwqes_16)(struct ether *,
					       struct kwqe_16 *[], uint32_t);
	int		(*drv_ctl)(struct ether *, struct drv_ctl_info *);
	unsigned long	reserved1[2];
	union drv_info_to_mcp	*addr_drv_info_to_mcp;
};

struct cnic_sockaddr {
	union {
		struct sockaddr_in	v4;
		struct sockaddr_in6	v6;
	} local;
	union {
		struct sockaddr_in	v4;
		struct sockaddr_in6	v6;
	} remote;
};

struct cnic_sock {
	struct cnic_dev *dev;
	void	*context;
	uint32_t	src_ip[4];
	uint32_t	dst_ip[4];
	uint16_t	src_port;
	uint16_t	dst_port;
	uint16_t	vlan_id;
	unsigned char old_ha[Eaddrlen];
	unsigned char ha[Eaddrlen];
	uint32_t	mtu;
	uint32_t	cid;
	uint32_t	l5_cid;
	uint32_t	pg_cid;
	int	ulp_type;

	uint32_t	ka_timeout;
	uint32_t	ka_interval;
	uint8_t	ka_max_probe_count;
	uint8_t	tos;
	uint8_t	ttl;
	uint8_t	snd_seq_scale;
	uint32_t	rcv_buf;
	uint32_t	snd_buf;
	uint32_t	seed;

	unsigned long	tcp_flags;
#define SK_TCP_NO_DELAY_ACK	0x1
#define SK_TCP_KEEP_ALIVE	0x2
#define SK_TCP_NAGLE		0x4
#define SK_TCP_TIMESTAMP	0x8
#define SK_TCP_SACK		0x10
#define SK_TCP_SEG_SCALING	0x20
	unsigned long	flags;
#define SK_F_INUSE		0
#define SK_F_OFFLD_COMPLETE	1
#define SK_F_OFFLD_SCHED	2
#define SK_F_PG_OFFLD_COMPLETE	3
#define SK_F_CONNECT_START	4
#define SK_F_IPV6		5
#define SK_F_CLOSING		7
#define SK_F_HW_ERR		8

	atomic_t ref_count;
	uint32_t state;
	struct kwqe kwqe1;
	struct kwqe kwqe2;
	struct kwqe kwqe3;
};

struct cnic_dev {
	struct ether	*netdev;
	struct pci_device		*pcidev;
	void __iomem		*regview;
	struct list_head	list;

	int (*register_device)(struct cnic_dev *dev, int ulp_type,
			       void *ulp_ctx);
	int (*unregister_device)(struct cnic_dev *dev, int ulp_type);
	int (*submit_kwqes)(struct cnic_dev *dev, struct kwqe *wqes[],
				uint32_t num_wqes);
	int (*submit_kwqes_16)(struct cnic_dev *dev, struct kwqe_16 *wqes[],
				uint32_t num_wqes);

	int (*cm_create)(struct cnic_dev *, int, uint32_t, uint32_t, struct cnic_sock **,
			 void *);
	int (*cm_destroy)(struct cnic_sock *);
	int (*cm_connect)(struct cnic_sock *, struct cnic_sockaddr *);
	int (*cm_abort)(struct cnic_sock *);
	int (*cm_close)(struct cnic_sock *);
	struct cnic_dev *(*cm_select_dev)(struct sockaddr_in *, int ulp_type);
	int (*iscsi_nl_msg_recv)(struct cnic_dev *dev, uint32_t msg_type,
				 char *data, uint16_t data_size);
	unsigned long	flags;
#define CNIC_F_CNIC_UP		1
#define CNIC_F_BNX2_CLASS	3
#define CNIC_F_BNX2X_CLASS	4
	atomic_t	ref_count;
	uint8_t		mac_addr[Eaddrlen];

	int		max_iscsi_conn;
	int		max_fcoe_conn;
	int		max_rdma_conn;

	int		max_fcoe_exchanges;

	union drv_info_to_mcp	*stats_addr;
	struct fcoe_capabilities	*fcoe_cap;

	void		*cnic_priv;
};

#define CNIC_WR(dev, off, val)		write32(val, dev->regview + off)
#define CNIC_WR16(dev, off, val)	write16(val, dev->regview + off)
#define CNIC_WR8(dev, off, val)		write8(val, dev->regview + off)
#define CNIC_RD(dev, off)		read32(dev->regview + off)
#define CNIC_RD16(dev, off)		read16(dev->regview + off)

struct cnic_ulp_ops {
	/* Calls to these functions are protected by RCU.  When
	 * unregistering, we wait for any calls to complete before
	 * continuing.
	 */

	void (*cnic_init)(struct cnic_dev *dev);
	void (*cnic_exit)(struct cnic_dev *dev);
	void (*cnic_start)(void *ulp_ctx);
	void (*cnic_stop)(void *ulp_ctx);
	void (*indicate_kcqes)(void *ulp_ctx, struct kcqe *cqes[],
				uint32_t num_cqes);
	void (*indicate_netevent)(void *ulp_ctx, unsigned long event,
				  uint16_t vid);
	void (*cm_connect_complete)(struct cnic_sock *);
	void (*cm_close_complete)(struct cnic_sock *);
	void (*cm_abort_complete)(struct cnic_sock *);
	void (*cm_remote_close)(struct cnic_sock *);
	void (*cm_remote_abort)(struct cnic_sock *);
	int (*iscsi_nl_send_msg)(void *ulp_ctx, uint32_t msg_type,
				  char *data, uint16_t data_size);
	int (*cnic_get_stats)(void *ulp_ctx);
	struct module *owner;
	atomic_t ref_count;
};

int cnic_register_driver(int ulp_type, struct cnic_ulp_ops *ulp_ops);

int cnic_unregister_driver(int ulp_type);

#endif

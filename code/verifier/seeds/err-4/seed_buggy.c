/* QLM seed slice: drivers/usb/gadget/legacy/multi.c @ c021e0235770^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define __ref
#define __init
#define __exit
#define unlikely(x) (x)
#define likely(x) (x)

#define EINVAL 22
#define ENOMEM 12
#define MAX_ERRNO 4095

#define USB_GADGET_PRODUCT_IDX 2
#define DRIVER_DESC "Multi Gadget"

/* container_of */
#define container_of(ptr, type, member) \
    ((type *)((char *)(ptr) - offsetof(type, member)))

/* ERR_PTR / IS_ERR / PTR_ERR */
#define IS_ERR(ptr)  ((unsigned long)(void *)(ptr) >= (unsigned long)-MAX_ERRNO)
#define PTR_ERR(ptr) ((long)(ptr))

/* printk-ish */
#define pr_info(fmt, ...)       ((void)0)
#define dev_err(dev, fmt, ...)  ((void)0)
#define dev_info(dev, fmt, ...) ((void)0)

/* forward structs */
struct device;
struct net_device;
struct usb_gadget;
struct usb_configuration;
struct usb_function_instance;
struct usb_descriptor_header;
struct fsg_common;
struct fsg_module_parameters;

struct device {
    int unused;
};

struct usb_gadget {
    struct device dev;
    const char *name;
};

struct usb_composite_dev {
    struct usb_gadget *gadget;
};

struct usb_composite_overwrite {
    int unused;
};

struct usb_function_instance {
    int unused;
};

struct f_ecm_opts {
    struct usb_function_instance func_inst;
    struct net_device *net;
    bool bound;
};

struct f_rndis_opts {
    struct usb_function_instance func_inst;
    struct net_device *net;
};

struct fsg_opts {
    bool no_configfs;
    struct fsg_common *common;
};

struct fsg_config {
    char can_stall;
    const char *vendor_name;
    const char *product_name;
};

struct usb_descriptor_header {
    unsigned char bLength;
    unsigned char bDescriptorType;
};

struct usb_string_id {
    unsigned char id;
};

struct usb_device_descriptor {
    unsigned char iProduct;
};

/* globals used by the function */
extern struct usb_function_instance *fi_ecm;
extern struct usb_function_instance *fi_rndis;
extern struct usb_function_instance *fi_acm;
extern struct usb_function_instance *fi_msg;

extern unsigned int qmult;
extern char host_addr[];
extern char dev_addr[];

extern struct fsg_module_parameters fsg_mod_data;
extern unsigned int fsg_num_buffers;

extern struct usb_string_id strings_dev[];
extern struct usb_device_descriptor device_desc;
extern struct usb_descriptor_header *otg_desc[2];
extern struct usb_composite_overwrite coverwrite;

/* function prototypes */
extern void kfree(const void *p);

extern bool can_support_ecm(struct usb_gadget *gadget);

extern struct usb_function_instance *usb_get_function_instance(const char *name);
extern void usb_put_function_instance(struct usb_function_instance *fi);

extern void gether_set_qmult(struct net_device *net, unsigned int qmult);
extern int gether_set_host_addr(struct net_device *net, const char *host_addr);
extern int gether_set_dev_addr(struct net_device *net, const char *dev_addr);
extern void gether_set_gadget(struct net_device *net, struct usb_gadget *g);
extern int gether_register_netdev(struct net_device *net);

extern void rndis_borrow_net(struct usb_function_instance *fi, struct net_device *net);

extern void fsg_config_from_params(struct fsg_config *cfg,
                                   const struct fsg_module_parameters *params,
                                   unsigned int fsg_num_buffers);
extern struct fsg_opts *fsg_opts_from_func_inst(const struct usb_function_instance *fi);

extern int fsg_common_set_num_buffers(struct fsg_common *common, unsigned int n);
extern int fsg_common_set_cdev(struct fsg_common *common,
                               struct usb_composite_dev *cdev, int can_stall);
extern void fsg_common_set_sysfs(struct fsg_common *common, bool sysfs);
extern int fsg_common_create_luns(struct fsg_common *common, struct fsg_config *cfg);
extern void fsg_common_set_inquiry_string(struct fsg_common *common,
                                          const char *vendor, const char *product);
extern void fsg_common_remove_luns(struct fsg_common *common);
extern void fsg_common_free_buffers(struct fsg_common *common);

extern int usb_string_ids_tab(struct usb_composite_dev *cdev, struct usb_string_id *str);
extern void usb_composite_overwrite_options(struct usb_composite_dev *cdev,
                                            struct usb_composite_overwrite *covr);

extern bool gadget_is_otg(struct usb_gadget *g);
extern struct usb_descriptor_header *usb_otg_descriptor_alloc(struct usb_gadget *gadget);
extern void usb_otg_descriptor_init(struct usb_gadget *gadget, void *desc);

extern int rndis_config_register(struct usb_composite_dev *cdev);
extern int cdc_config_register(struct usb_composite_dev *cdev);
#undef CONFIG_USB_G_MULTI_CDC
#define CONFIG_USB_G_MULTI_CDC 1

/* ---- verbatim kernel code ---- */
static int __ref multi_bind(struct usb_composite_dev *cdev)
{
	struct usb_gadget *gadget = cdev->gadget;
#ifdef CONFIG_USB_G_MULTI_CDC
	struct f_ecm_opts *ecm_opts;
#endif
#ifdef USB_ETH_RNDIS
	struct f_rndis_opts *rndis_opts;
#endif
	struct fsg_opts *fsg_opts;
	struct fsg_config config;
	int status;

	if (!can_support_ecm(cdev->gadget)) {
		dev_err(&gadget->dev, "controller '%s' not usable\n",
			gadget->name);
		return -EINVAL;
	}

#ifdef CONFIG_USB_G_MULTI_CDC
	fi_ecm = usb_get_function_instance("ecm");
	if (IS_ERR(fi_ecm))
		return PTR_ERR(fi_ecm);

	ecm_opts = container_of(fi_ecm, struct f_ecm_opts, func_inst);

	gether_set_qmult(ecm_opts->net, qmult);
	if (!gether_set_host_addr(ecm_opts->net, host_addr))
		pr_info("using host ethernet address: %s", host_addr);
	if (!gether_set_dev_addr(ecm_opts->net, dev_addr))
		pr_info("using self ethernet address: %s", dev_addr);
#endif

#ifdef USB_ETH_RNDIS
	fi_rndis = usb_get_function_instance("rndis");
	if (IS_ERR(fi_rndis)) {
		status = PTR_ERR(fi_rndis);
		goto fail;
	}

	rndis_opts = container_of(fi_rndis, struct f_rndis_opts, func_inst);

	gether_set_qmult(rndis_opts->net, qmult);
	if (!gether_set_host_addr(rndis_opts->net, host_addr))
		pr_info("using host ethernet address: %s", host_addr);
	if (!gether_set_dev_addr(rndis_opts->net, dev_addr))
		pr_info("using self ethernet address: %s", dev_addr);
#endif

#if (defined CONFIG_USB_G_MULTI_CDC && defined USB_ETH_RNDIS)
	/*
	 * If both ecm and rndis are selected then:
	 *	1) rndis borrows the net interface from ecm
	 *	2) since the interface is shared it must not be bound
	 *	twice - in ecm's _and_ rndis' binds, so do it here.
	 */
	gether_set_gadget(ecm_opts->net, cdev->gadget);
	status = gether_register_netdev(ecm_opts->net);
	if (status)
		goto fail0;

	rndis_borrow_net(fi_rndis, ecm_opts->net);
	ecm_opts->bound = true;
#endif

	/* set up serial link layer */
	fi_acm = usb_get_function_instance("acm");
	if (IS_ERR(fi_acm)) {
		status = PTR_ERR(fi_acm);
		goto fail0;
	}

	/* set up mass storage function */
	fi_msg = usb_get_function_instance("mass_storage");
	if (IS_ERR(fi_msg)) {
		status = PTR_ERR(fi_msg);
		goto fail1;
	}
	fsg_config_from_params(&config, &fsg_mod_data, fsg_num_buffers);
	fsg_opts = fsg_opts_from_func_inst(fi_msg);

	fsg_opts->no_configfs = true;
	status = fsg_common_set_num_buffers(fsg_opts->common, fsg_num_buffers);
	if (status)
		goto fail2;

	status = fsg_common_set_cdev(fsg_opts->common, cdev, config.can_stall);
	if (status)
		goto fail_set_cdev;

	fsg_common_set_sysfs(fsg_opts->common, true);
	status = fsg_common_create_luns(fsg_opts->common, &config);
	if (status)
		goto fail_set_cdev;

	fsg_common_set_inquiry_string(fsg_opts->common, config.vendor_name,
				      config.product_name);

	/* allocate string IDs */
	status = usb_string_ids_tab(cdev, strings_dev);
	if (unlikely(status < 0))
		goto fail_string_ids;
	device_desc.iProduct = strings_dev[USB_GADGET_PRODUCT_IDX].id;

	if (gadget_is_otg(gadget) && !otg_desc[0]) {
		struct usb_descriptor_header *usb_desc;

		usb_desc = usb_otg_descriptor_alloc(gadget);
		if (!usb_desc)
			goto fail_string_ids;
		usb_otg_descriptor_init(gadget, usb_desc);
		otg_desc[0] = usb_desc;
		otg_desc[1] = NULL;
	}

	/* register configurations */
	status = rndis_config_register(cdev);
	if (unlikely(status < 0))
		goto fail_otg_desc;

	status = cdc_config_register(cdev);
	if (unlikely(status < 0))
		goto fail_otg_desc;
	usb_composite_overwrite_options(cdev, &coverwrite);

	/* we're done */
	dev_info(&gadget->dev, DRIVER_DESC "\n");
	return 0;


	/* error recovery */
fail_otg_desc:
	kfree(otg_desc[0]);
	otg_desc[0] = NULL;
fail_string_ids:
	fsg_common_remove_luns(fsg_opts->common);
fail_set_cdev:
	fsg_common_free_buffers(fsg_opts->common);
fail2:
	usb_put_function_instance(fi_msg);
fail1:
	usb_put_function_instance(fi_acm);
fail0:
#ifdef USB_ETH_RNDIS
	usb_put_function_instance(fi_rndis);
fail:
#endif
#ifdef CONFIG_USB_G_MULTI_CDC
	usb_put_function_instance(fi_ecm);
#endif
	return status;
}

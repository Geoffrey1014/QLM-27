/* QLM seed slice: drivers/media/usb/em28xx/em28xx-core.c @ 2453e60702e1 (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define GFP_ATOMIC 0
#define GFP_KERNEL 0

struct em28xx;
struct urb {
    unsigned int pipe;
};

struct usb_interface;
struct usb_device;
struct device;

enum em28xx_mode {
    EM28XX_SUSPEND = -1,
    EM28XX_UNUSED = 0,
    EM28XX_ANALOG_MODE = 1,
    EM28XX_DIGITAL_MODE = 2,
};

struct em28xx_dmaqueue {
    void *wq;
};

struct em28xx_usb_bufs {
    int num_bufs;
    struct urb **urb;
};

struct em28xx_usb_ctl {
    int (*urb_data_copy)(struct em28xx *dev, struct urb *urb);
    struct em28xx_usb_bufs digital_bufs;
    struct em28xx_usb_bufs analog_bufs;
};

struct intf_dev_wrap {
    struct device *dev_ptr;
};

struct device_stub { int _unused; };

struct usb_interface {
    struct device_stub dev;
};

struct em28xx {
    struct em28xx_dmaqueue vidq;
    struct em28xx_dmaqueue vbiq;
    struct usb_interface *intf;
    struct em28xx_usb_ctl usb_ctl;
};

#define em28xx_isocdbg(fmt, ...) do {} while (0)
#define dev_err(dev, fmt, ...) do {} while (0)
#define init_waitqueue_head(wq) do { (void)(wq); } while (0)

extern struct usb_device *interface_to_usbdev(struct usb_interface *intf);
extern int usb_clear_halt(struct usb_device *dev, unsigned int pipe);
extern int usb_submit_urb(struct urb *urb, int mem_flags);
extern int em28xx_alloc_urbs(struct em28xx *dev, enum em28xx_mode mode,
                             int xfer_bulk, int num_bufs,
                             int max_pkt_size, int packet_multiplier);
extern void em28xx_uninit_usb_xfer(struct em28xx *dev, enum em28xx_mode mode);
extern void em28xx_capture_start(struct em28xx *dev, int start);

/* ---- verbatim kernel code ---- */
int em28xx_init_usb_xfer(struct em28xx *dev, enum em28xx_mode mode,
			 int xfer_bulk, int num_bufs, int max_pkt_size,
		    int packet_multiplier,
		    int (*urb_data_copy)(struct em28xx *dev, struct urb *urb))
{
	struct em28xx_dmaqueue *dma_q = &dev->vidq;
	struct em28xx_dmaqueue *vbi_dma_q = &dev->vbiq;
	struct em28xx_usb_bufs *usb_bufs;
	struct usb_device *udev = interface_to_usbdev(dev->intf);
	int i;
	int rc;
	int alloc;

	em28xx_isocdbg("em28xx: called %s in mode %d\n", __func__, mode);

	dev->usb_ctl.urb_data_copy = urb_data_copy;

	if (mode == EM28XX_DIGITAL_MODE) {
		usb_bufs = &dev->usb_ctl.digital_bufs;
		/* no need to free/alloc usb buffers in digital mode */
		alloc = 0;
	} else {
		usb_bufs = &dev->usb_ctl.analog_bufs;
		alloc = 1;
	}

	if (alloc) {
		rc = em28xx_alloc_urbs(dev, mode, xfer_bulk, num_bufs,
				       max_pkt_size, packet_multiplier);
		if (rc)
			return rc;
	}

	if (xfer_bulk) {
		rc = usb_clear_halt(udev, usb_bufs->urb[0]->pipe);
		if (rc < 0) {
			dev_err(&dev->intf->dev,
				"failed to clear USB bulk endpoint stall/halt condition (error=%i)\n",
			       rc);
			em28xx_uninit_usb_xfer(dev, mode);
			return rc;
		}
	}

	init_waitqueue_head(&dma_q->wq);
	init_waitqueue_head(&vbi_dma_q->wq);

	em28xx_capture_start(dev, 1);

	/* submit urbs and enables IRQ */
	for (i = 0; i < usb_bufs->num_bufs; i++) {
		rc = usb_submit_urb(usb_bufs->urb[i], GFP_KERNEL);
		if (rc) {
			dev_err(&dev->intf->dev,
				"submit of urb %i failed (error=%i)\n", i, rc);
			em28xx_uninit_usb_xfer(dev, mode);
			return rc;
		}
	}

	return 0;
}

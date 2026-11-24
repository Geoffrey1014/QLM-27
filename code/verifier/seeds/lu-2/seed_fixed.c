/* QLM seed slice: drivers/media/usb/dvb-usb/af9005.c @ 2289adbfa559 (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;

struct usb_device;
struct dvb_usb_device_properties;
struct dvb_usb_device_description;

#define GFP_KERNEL 0
#define ENOMEM 12
#define EIO 5

#define FW_BULKOUT_SIZE 250
#define FW_CONFIG 0x11

#define deb_info(fmt, ...) do { } while (0)

extern void *kmalloc(size_t size, unsigned int flags);
extern void kfree(const void *ptr);
extern int af9005_boot_packet(struct usb_device *udev, int type, u8 *reply,
                              u8 *buf, int size);

/* ---- verbatim kernel code ---- */
static int af9005_identify_state(struct usb_device *udev,
				 struct dvb_usb_device_properties *props,
				 struct dvb_usb_device_description **desc,
				 int *cold)
{
	int ret;
	u8 reply, *buf;

	buf = kmalloc(FW_BULKOUT_SIZE + 2, GFP_KERNEL);
	if (!buf)
		return -ENOMEM;

	ret = af9005_boot_packet(udev, FW_CONFIG, &reply,
				 buf, FW_BULKOUT_SIZE + 2);
	if (ret)
		goto err;
	deb_info("result of FW_CONFIG in identify state %d\n", reply);
	if (reply == 0x01)
		*cold = 1;
	else if (reply == 0x02)
		*cold = 0;
	else
		ret = -EIO;
	if (!ret)
		deb_info("Identify state cold = %d\n", *cold);

err:
	kfree(buf);
	return ret;
}

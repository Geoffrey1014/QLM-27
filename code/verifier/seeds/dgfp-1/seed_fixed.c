/* QLM seed slice: drivers/input/touchscreen/wdt87xx_i2c.c @ e58650b57ee0 (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define __maybe_unused __attribute__((unused))

struct device {
    int _opaque;
};

struct i2c_client {
    int irq;
    struct device dev;
};

#define VND_CMD_START 0

extern struct i2c_client *to_i2c_client(struct device *dev);
extern void mdelay(unsigned long msecs);
extern void msleep(unsigned int msecs);
extern int wdt87xx_send_command(struct i2c_client *client, int cmd, int arg);
extern void enable_irq(unsigned int irq);
extern int dev_err(struct device *dev, const char *fmt, ...);

/* ---- verbatim kernel code ---- */
static int __maybe_unused wdt87xx_resume(struct device *dev)
{
	struct i2c_client *client = to_i2c_client(dev);
	int error;

	/*
	 * The chip may have been reset while system is resuming,
	 * give it some time to settle.
	 */
	msleep(100);

	error = wdt87xx_send_command(client, VND_CMD_START, 0);
	if (error)
		dev_err(&client->dev,
			"failed to start device when resuming: %d\n",
			error);

	enable_irq(client->irq);

	return 0;
}

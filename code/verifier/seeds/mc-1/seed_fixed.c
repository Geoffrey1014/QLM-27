/* QLM seed slice: drivers/input/touchscreen/ad7879.c @ e85bb0beb649 (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef unsigned int irqreturn_t;
#define IRQ_HANDLED ((irqreturn_t)1)

#define AD7879_REG_XPLUS 0x08
#define AD7879_NR_SENSE 4
#define TS_PEN_UP_TIMEOUT 50

struct regmap;
struct device;

struct timer_list {
    unsigned long expires;
    void (*function)(struct timer_list *);
    unsigned long data;
    unsigned int flags;
};

struct ad7879 {
    struct regmap *regmap;
    struct device *dev;
    struct timer_list timer;
    unsigned short conversion_data[AD7879_NR_SENSE];
};

extern unsigned long volatile jiffies;

extern int regmap_bulk_read(struct regmap *map, unsigned int reg, void *val, size_t val_count);
extern bool ad7879_report(struct ad7879 *ts);
extern int mod_timer(struct timer_list *timer, unsigned long expires);

#define dev_err_ratelimited(dev, fmt, ...) ((void)0)

/* ---- verbatim kernel code ---- */
static irqreturn_t ad7879_irq(int irq, void *handle)
{
	struct ad7879 *ts = handle;
	int error;

	error = regmap_bulk_read(ts->regmap, AD7879_REG_XPLUS,
				 ts->conversion_data, AD7879_NR_SENSE);
	if (error)
		dev_err_ratelimited(ts->dev, "failed to read %#02x: %d\n",
				    AD7879_REG_XPLUS, error);
	else if (!ad7879_report(ts))
		mod_timer(&ts->timer, jiffies + TS_PEN_UP_TIMEOUT);

	return IRQ_HANDLED;
}

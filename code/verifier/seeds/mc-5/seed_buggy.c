/* QLM seed slice: drivers/pinctrl/intel/pinctrl-baytrail.c @ d6cb77228e3a^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define GFP_KERNEL     ((unsigned int)0x400u)
#define ENOMEM         12
#define IORESOURCE_IRQ 0x00000400
#define IRQ_TYPE_NONE  0
#define CONFIG_PM_SLEEP 1

typedef unsigned int gfp_t;
typedef unsigned long resource_size_t;

struct device {
    void *driver_data;
    struct device *parent;
};

struct irq_desc;

struct resource {
    resource_size_t start;
    resource_size_t end;
    const char *name;
    unsigned long flags;
};

typedef void (*irq_flow_handler_t)(struct irq_desc *desc);

struct irq_chip {
    const char *name;
};

struct gpio_irq_chip {
    bool need_valid_mask;
};

struct gpio_chip {
    const char *label;
    int base;
    bool can_sleep;
    struct device *parent;
    unsigned int ngpio;
    struct gpio_irq_chip irq;
};

struct platform_device {
    struct device dev;
};

struct byt_context {
    unsigned int conf0;
    unsigned int val;
};

struct intel_pinctrl_soc_data {
    int npins;
};

struct byt_gpio {
    struct platform_device *pdev;
    struct gpio_chip chip;
    const struct intel_pinctrl_soc_data *soc_data;
    struct byt_context *saved_context;
};

extern struct gpio_chip byt_gpio_chip;
extern struct irq_chip byt_irqchip;

extern const char *dev_name(const struct device *dev);
extern void *devm_kcalloc(struct device *dev, size_t n, size_t size, gfp_t flags);
extern int devm_gpiochip_add_data(struct device *dev, struct gpio_chip *gc, void *data);
extern void dev_err(const struct device *dev, const char *fmt, ...);
extern int gpiochip_add_pin_range(struct gpio_chip *gc, const char *pinctl_name,
                                  unsigned int gpio_offset, unsigned int pin_offset,
                                  unsigned int npins);
extern struct resource *platform_get_resource(struct platform_device *pdev,
                                              unsigned int type, unsigned int num);
extern void byt_gpio_irq_init_hw(struct byt_gpio *vg);
extern int gpiochip_irqchip_add(struct gpio_chip *gc, struct irq_chip *irqchip,
                                unsigned int first_irq,
                                irq_flow_handler_t handler,
                                unsigned int type);
extern void gpiochip_set_chained_irqchip(struct gpio_chip *gc,
                                         struct irq_chip *irqchip,
                                         unsigned int parent_irq,
                                         irq_flow_handler_t parent_handler);
extern void handle_bad_irq(struct irq_desc *desc);
extern void byt_gpio_irq_handler(struct irq_desc *desc);
#undef CONFIG_PM_SLEEP
#define CONFIG_PM_SLEEP 1

/* ---- verbatim kernel code ---- */
static int byt_gpio_probe(struct byt_gpio *vg)
{
	struct gpio_chip *gc;
	struct resource *irq_rc;
	int ret;

	/* Set up gpio chip */
	vg->chip	= byt_gpio_chip;
	gc		= &vg->chip;
	gc->label	= dev_name(&vg->pdev->dev);
	gc->base	= -1;
	gc->can_sleep	= false;
	gc->parent	= &vg->pdev->dev;
	gc->ngpio	= vg->soc_data->npins;
	gc->irq.need_valid_mask	= true;

#ifdef CONFIG_PM_SLEEP
	vg->saved_context = devm_kcalloc(&vg->pdev->dev, gc->ngpio,
				       sizeof(*vg->saved_context), GFP_KERNEL);
#endif
	ret = devm_gpiochip_add_data(&vg->pdev->dev, gc, vg);
	if (ret) {
		dev_err(&vg->pdev->dev, "failed adding byt-gpio chip\n");
		return ret;
	}

	ret = gpiochip_add_pin_range(&vg->chip, dev_name(&vg->pdev->dev),
				     0, 0, vg->soc_data->npins);
	if (ret) {
		dev_err(&vg->pdev->dev, "failed to add GPIO pin range\n");
		return ret;
	}

	/* set up interrupts  */
	irq_rc = platform_get_resource(vg->pdev, IORESOURCE_IRQ, 0);
	if (irq_rc && irq_rc->start) {
		byt_gpio_irq_init_hw(vg);
		ret = gpiochip_irqchip_add(gc, &byt_irqchip, 0,
					   handle_bad_irq, IRQ_TYPE_NONE);
		if (ret) {
			dev_err(&vg->pdev->dev, "failed to add irqchip\n");
			return ret;
		}

		gpiochip_set_chained_irqchip(gc, &byt_irqchip,
					     (unsigned)irq_rc->start,
					     byt_gpio_irq_handler);
	}

	return ret;
}

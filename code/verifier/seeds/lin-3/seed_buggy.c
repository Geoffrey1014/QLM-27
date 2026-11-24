/* QLM seed slice: sound/soc/samsung/aries_wm8994.c @ bf4a9b2467b7^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define GFP_KERNEL 0
#define EINVAL 22
#define ENOMEM 12
#define GPIOD_OUT_LOW 0
#define GPIOD_IN 1
#define IIO_VOLTAGE 2
#define ARRAY_SIZE(a) (sizeof(a) / sizeof((a)[0]))

struct device_node;

struct device {
    struct device_node *of_node;
};

struct platform_device {
    struct device dev;
};

struct regulator;
struct gpio_desc;
struct extcon_dev;

struct iio_chan_spec {
    int type;
};

struct iio_channel {
    const struct iio_chan_spec *channel;
};

struct snd_soc_dai_link_component {
    struct device_node *of_node;
    const char *dai_name;
    const char *name;
};

struct snd_soc_dai_link {
    struct snd_soc_dai_link_component *cpus;
    struct snd_soc_dai_link_component *codecs;
    struct snd_soc_dai_link_component *platforms;
    unsigned int dai_fmt;
    const char *name;
};

struct snd_soc_card {
    struct device *dev;
    int num_dapm_widgets;
    struct snd_soc_dai_link *dai_link;
    int num_links;
};

struct of_device_id {
    char name[32];
    char type[32];
    char compatible[128];
    const void *data;
};

struct aries_variant {
    int has_fm_radio;
    unsigned int modem_dai_fmt;
};

struct aries_wm8994_data {
    const struct aries_variant *variant;
    struct regulator *reg_main_micbias;
    struct regulator *reg_headset_micbias;
    struct gpio_desc *gpio_earpath_sel;
    struct extcon_dev *usb_extcon;
    struct iio_channel *adc;
    struct gpio_desc *gpio_headset_key;
    struct gpio_desc *gpio_headset_detect;
};

struct snd_soc_component_driver {
    const char *name;
};

struct snd_soc_dai_driver {
    const char *name;
};

extern struct snd_soc_card aries_card;
extern struct snd_soc_dai_link aries_dai[3];
extern const struct of_device_id samsung_wm8994_of_match[];
extern const struct snd_soc_component_driver aries_component;
extern struct snd_soc_dai_driver aries_ext_dai[2];

extern void *devm_kzalloc(struct device *dev, size_t size, unsigned int gfp);
extern void snd_soc_card_set_drvdata(struct snd_soc_card *card, void *data);
extern const struct of_device_id *of_match_node(const struct of_device_id *matches,
                                                const struct device_node *node);
extern struct regulator *devm_regulator_get(struct device *dev, const char *id);
extern long IS_ERR(const void *ptr);
extern long PTR_ERR(const void *ptr);
extern int dev_err(const struct device *dev, const char *fmt, ...);
extern struct gpio_desc *devm_gpiod_get(struct device *dev, const char *con_id, int flags);
extern struct device_node *of_parse_phandle(const struct device_node *np,
                                            const char *phandle_name, int index);
extern struct extcon_dev *extcon_find_edev_by_node(struct device_node *node);
extern int dev_err_probe(const struct device *dev, int err, const char *fmt, ...);
extern void of_node_put(struct device_node *node);
extern struct iio_channel *devm_iio_channel_get(struct device *dev, const char *name);
extern int snd_soc_of_parse_card_name(struct snd_soc_card *card, const char *propname);
extern int snd_soc_of_parse_audio_routing(struct snd_soc_card *card, const char *propname);
extern struct device_node *of_get_child_by_name(const struct device_node *node,
                                                const char *name);
extern int devm_snd_soc_register_component(struct device *dev,
                                           const struct snd_soc_component_driver *driver,
                                           struct snd_soc_dai_driver *dai_drv,
                                           int num_dai);
extern int devm_snd_soc_register_card(struct device *dev, struct snd_soc_card *card);

#define for_each_card_prelinks(card, i, link)                              \
    for ((i) = 0, (link) = (card)->dai_link;                               \
         (i) < (card)->num_links;                                          \
         (i)++, (link)++)

/* ---- verbatim kernel code ---- */
static int aries_audio_probe(struct platform_device *pdev)
{
	struct device_node *np = pdev->dev.of_node;
	struct device_node *cpu, *codec, *extcon_np;
	struct device *dev = &pdev->dev;
	struct snd_soc_card *card = &aries_card;
	struct aries_wm8994_data *priv;
	struct snd_soc_dai_link *dai_link;
	const struct of_device_id *match;
	int ret, i;

	if (!np)
		return -EINVAL;

	card->dev = dev;

	priv = devm_kzalloc(dev, sizeof(*priv), GFP_KERNEL);
	if (!priv)
		return -ENOMEM;

	snd_soc_card_set_drvdata(card, priv);

	match = of_match_node(samsung_wm8994_of_match, np);
	priv->variant = match->data;

	/* Remove FM widget if not present */
	if (!priv->variant->has_fm_radio)
		card->num_dapm_widgets--;

	priv->reg_main_micbias = devm_regulator_get(dev, "main-micbias");
	if (IS_ERR(priv->reg_main_micbias)) {
		dev_err(dev, "Failed to get main micbias regulator\n");
		return PTR_ERR(priv->reg_main_micbias);
	}

	priv->reg_headset_micbias = devm_regulator_get(dev, "headset-micbias");
	if (IS_ERR(priv->reg_headset_micbias)) {
		dev_err(dev, "Failed to get headset micbias regulator\n");
		return PTR_ERR(priv->reg_headset_micbias);
	}

	priv->gpio_earpath_sel = devm_gpiod_get(dev, "earpath-sel",
			GPIOD_OUT_LOW);
	if (IS_ERR(priv->gpio_earpath_sel)) {
		dev_err(dev, "Failed to get earpath selector gpio");
		return PTR_ERR(priv->gpio_earpath_sel);
	}

	extcon_np = of_parse_phandle(np, "extcon", 0);
	priv->usb_extcon = extcon_find_edev_by_node(extcon_np);
	if (IS_ERR(priv->usb_extcon))
		return dev_err_probe(dev, PTR_ERR(priv->usb_extcon),
				     "Failed to get extcon device");
	of_node_put(extcon_np);

	priv->adc = devm_iio_channel_get(dev, "headset-detect");
	if (IS_ERR(priv->adc))
		return dev_err_probe(dev, PTR_ERR(priv->adc),
				     "Failed to get ADC channel");

	if (priv->adc->channel->type != IIO_VOLTAGE)
		return -EINVAL;

	priv->gpio_headset_key = devm_gpiod_get(dev, "headset-key",
			GPIOD_IN);
	if (IS_ERR(priv->gpio_headset_key)) {
		dev_err(dev, "Failed to get headset key gpio");
		return PTR_ERR(priv->gpio_headset_key);
	}

	priv->gpio_headset_detect = devm_gpiod_get(dev,
			"headset-detect", GPIOD_IN);
	if (IS_ERR(priv->gpio_headset_detect)) {
		dev_err(dev, "Failed to get headset detect gpio");
		return PTR_ERR(priv->gpio_headset_detect);
	}

	/* Update card-name if provided through DT, else use default name */
	snd_soc_of_parse_card_name(card, "model");

	ret = snd_soc_of_parse_audio_routing(card, "samsung,audio-routing");
	if (ret < 0) {
		dev_err(dev, "Audio routing invalid/unspecified\n");
		return ret;
	}

	aries_dai[1].dai_fmt = priv->variant->modem_dai_fmt;

	cpu = of_get_child_by_name(dev->of_node, "cpu");
	if (!cpu)
		return -EINVAL;

	codec = of_get_child_by_name(dev->of_node, "codec");
	if (!codec)
		return -EINVAL;

	for_each_card_prelinks(card, i, dai_link) {
		dai_link->codecs->of_node = of_parse_phandle(codec,
				"sound-dai", 0);
		if (!dai_link->codecs->of_node) {
			ret = -EINVAL;
			goto out;
		}
	}

	/* Set CPU and platform of_node for main DAI */
	aries_dai[0].cpus->of_node = of_parse_phandle(cpu,
			"sound-dai", 0);
	if (!aries_dai[0].cpus->of_node) {
		ret = -EINVAL;
		goto out;
	}

	aries_dai[0].platforms->of_node = aries_dai[0].cpus->of_node;

	/* Set CPU of_node for BT DAI */
	aries_dai[2].cpus->of_node = of_parse_phandle(cpu,
			"sound-dai", 1);
	if (!aries_dai[2].cpus->of_node) {
		ret = -EINVAL;
		goto out;
	}

	ret = devm_snd_soc_register_component(dev, &aries_component,
				aries_ext_dai, ARRAY_SIZE(aries_ext_dai));
	if (ret < 0) {
		dev_err(dev, "Failed to register component: %d\n", ret);
		goto out;
	}

	ret = devm_snd_soc_register_card(dev, card);
	if (ret)
		dev_err(dev, "snd_soc_register_card() failed:%d\n", ret);

out:
	of_node_put(cpu);
	of_node_put(codec);

	return ret;
}

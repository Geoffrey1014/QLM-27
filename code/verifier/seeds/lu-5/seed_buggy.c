/* QLM seed slice: fs/affs/super.c @ 450c3d416683^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define GFP_KERNEL 0
#define ENOMEM 12
#define EINVAL 22
#define SB_RDONLY 1
#define SB_NODIRATIME 2048

#define pr_debug(fmt, ...) do {} while (0)

typedef struct { unsigned int val; } kuid_t;
typedef struct { unsigned int val; } kgid_t;
typedef struct { int _lock; } spinlock_t;

struct delayed_work { int _dw_pad; };

struct super_block;

struct affs_sb_info {
    unsigned long   s_flags;
    int             s_mode;
    kuid_t          s_uid;
    kgid_t          s_gid;
    char            s_volume[32];
    char           *s_prefix;
    spinlock_t      symlink_lock;
    struct delayed_work sb_work;
};

#define AFFS_SB(sb) ((struct affs_sb_info *)(sb))

extern char *kstrdup(const char *s, int gfp);
extern void kfree(const void *p);
extern void *memcpy(void *dst, const void *src, unsigned long n);

extern int sync_filesystem(struct super_block *sb);
extern bool sb_rdonly(const struct super_block *sb);

extern void spin_lock(spinlock_t *lock);
extern void spin_unlock(spinlock_t *lock);

extern bool flush_delayed_work(struct delayed_work *dwork);

extern int parse_options(char *options, kuid_t *uid, kgid_t *gid,
                         int *mode, int *reserved, int *root,
                         int *blocksize, char **prefix,
                         char *volume, unsigned long *mount_opts);

extern void affs_free_bitmap(struct super_block *sb);
extern int  affs_init_bitmap(struct super_block *sb, int *flags);

/* ---- verbatim kernel code ---- */
static int
affs_remount(struct super_block *sb, int *flags, char *data)
{
	struct affs_sb_info	*sbi = AFFS_SB(sb);
	int			 blocksize;
	kuid_t			 uid;
	kgid_t			 gid;
	int			 mode;
	int			 reserved;
	int			 root_block;
	unsigned long		 mount_flags;
	int			 res = 0;
	char			*new_opts;
	char			 volume[32];
	char			*prefix = NULL;

	new_opts = kstrdup(data, GFP_KERNEL);
	if (data && !new_opts)
		return -ENOMEM;

	pr_debug("%s(flags=0x%x,opts=\"%s\")\n", __func__, *flags, data);

	sync_filesystem(sb);
	*flags |= SB_NODIRATIME;

	memcpy(volume, sbi->s_volume, 32);
	if (!parse_options(data, &uid, &gid, &mode, &reserved, &root_block,
			   &blocksize, &prefix, volume,
			   &mount_flags)) {
		kfree(prefix);
		kfree(new_opts);
		return -EINVAL;
	}

	flush_delayed_work(&sbi->sb_work);

	sbi->s_flags = mount_flags;
	sbi->s_mode  = mode;
	sbi->s_uid   = uid;
	sbi->s_gid   = gid;
	/* protect against readers */
	spin_lock(&sbi->symlink_lock);
	if (prefix) {
		kfree(sbi->s_prefix);
		sbi->s_prefix = prefix;
	}
	memcpy(sbi->s_volume, volume, 32);
	spin_unlock(&sbi->symlink_lock);

	if ((bool)(*flags & SB_RDONLY) == sb_rdonly(sb))
		return 0;

	if (*flags & SB_RDONLY)
		affs_free_bitmap(sb);
	else
		res = affs_init_bitmap(sb, flags);

	return res;
}

/* QLM seed slice: net/sctp/sm_statefuns.c @ b6631c6031c7^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef unsigned short __u16;
typedef unsigned int __u32;
typedef unsigned short __be16;
typedef unsigned int __be32;
typedef unsigned int gfp_t;

#define GFP_ATOMIC 0x20u

#define SCTP_IERROR_NOMEM 1
#define SCTP_IERROR_STALE_COOKIE 2
#define SCTP_IERROR_BAD_SIG 3

enum sctp_disposition {
    SCTP_DISPOSITION_DISCARD,
    SCTP_DISPOSITION_CONSUME,
    SCTP_DISPOSITION_NOMEM,
    SCTP_DISPOSITION_DELETE_TCB,
    SCTP_DISPOSITION_ABORT,
    SCTP_DISPOSITION_VIOLATION,
    SCTP_DISPOSITION_NOT_IMPL,
    SCTP_DISPOSITION_ERROR,
    SCTP_DISPOSITION_BUG,
};

enum sctp_verb {
    SCTP_CMD_NOP,
    SCTP_CMD_SET_ASOC,
    SCTP_CMD_DELETE_TCB,
};

struct net;
struct sctp_endpoint;
struct sctp_association;
struct sctp_cmd_seq;
struct sctp_signed_cookie;

union sctp_subtype {
    int chunk;
    int event;
    int other;
};

struct sctp_chunkhdr {
    __u16 type;
    __u16 flags;
    __be16 length;
};

struct sk_buff {
    unsigned char *data;
    unsigned int len;
};

struct sctp_chunk {
    struct sk_buff *skb;
    struct sctp_chunkhdr *chunk_hdr;
    union {
        struct sctp_signed_cookie *cookie_hdr;
        void *v;
    } subh;
};

struct sctp_association {
    int temp;
};

union sctp_arg {
    void *ptr;
    struct sctp_association *asoc;
    int i32;
};

#define SCTP_ASOC(a)  ((union sctp_arg){ .asoc = (struct sctp_association *)(a) })
#define SCTP_NULL()   ((union sctp_arg){ .ptr = NULL })

extern __u16 ntohs(__be16);

extern int sctp_chunk_length_valid(struct sctp_chunk *chunk, size_t required);
extern enum sctp_disposition sctp_sf_violation_chunklen(
    struct net *net, const struct sctp_endpoint *ep,
    const struct sctp_association *asoc, const union sctp_subtype type,
    void *arg, struct sctp_cmd_seq *commands);
extern int pskb_pull(struct sk_buff *skb, unsigned int len);
extern struct sctp_association *sctp_unpack_cookie(
    const struct sctp_endpoint *ep, const struct sctp_association *asoc,
    struct sctp_chunk *chunk, gfp_t gfp, int *error,
    struct sctp_chunk **err_chk_p);
extern void sctp_send_stale_cookie_err(
    struct net *net, const struct sctp_endpoint *ep,
    const struct sctp_association *asoc, const struct sctp_chunk *chunk,
    struct sctp_cmd_seq *commands, struct sctp_chunk *err_chk_p);
extern enum sctp_disposition sctp_sf_pdiscard(
    struct net *net, const struct sctp_endpoint *ep,
    const struct sctp_association *asoc, const union sctp_subtype type,
    void *arg, struct sctp_cmd_seq *commands);
extern int security_sctp_assoc_request(struct sctp_endpoint *ep,
                                       struct sk_buff *skb);
extern void sctp_association_free(struct sctp_association *asoc);
extern char sctp_tietags_compare(struct sctp_association *new_asoc,
                                 const struct sctp_association *asoc);
extern enum sctp_disposition sctp_sf_do_dupcook_a(
    struct net *net, const struct sctp_endpoint *ep,
    const struct sctp_association *asoc, struct sctp_chunk *chunk,
    struct sctp_cmd_seq *commands, struct sctp_association *new_asoc);
extern enum sctp_disposition sctp_sf_do_dupcook_b(
    struct net *net, const struct sctp_endpoint *ep,
    const struct sctp_association *asoc, struct sctp_chunk *chunk,
    struct sctp_cmd_seq *commands, struct sctp_association *new_asoc);
extern enum sctp_disposition sctp_sf_do_dupcook_c(
    struct net *net, const struct sctp_endpoint *ep,
    const struct sctp_association *asoc, struct sctp_chunk *chunk,
    struct sctp_cmd_seq *commands, struct sctp_association *new_asoc);
extern enum sctp_disposition sctp_sf_do_dupcook_d(
    struct net *net, const struct sctp_endpoint *ep,
    const struct sctp_association *asoc, struct sctp_chunk *chunk,
    struct sctp_cmd_seq *commands, struct sctp_association *new_asoc);
extern void sctp_add_cmd_sf(struct sctp_cmd_seq *commands,
                            enum sctp_verb verb, union sctp_arg obj);

/* ---- verbatim kernel code ---- */
enum sctp_disposition sctp_sf_do_5_2_4_dupcook(
					struct net *net,
					const struct sctp_endpoint *ep,
					const struct sctp_association *asoc,
					const union sctp_subtype type,
					void *arg,
					struct sctp_cmd_seq *commands)
{
	struct sctp_association *new_asoc;
	struct sctp_chunk *chunk = arg;
	enum sctp_disposition retval;
	struct sctp_chunk *err_chk_p;
	int error = 0;
	char action;

	/* Make sure that the chunk has a valid length from the protocol
	 * perspective.  In this case check to make sure we have at least
	 * enough for the chunk header.  Cookie length verification is
	 * done later.
	 */
	if (!sctp_chunk_length_valid(chunk, sizeof(struct sctp_chunkhdr)))
		return sctp_sf_violation_chunklen(net, ep, asoc, type, arg,
						  commands);

	/* "Decode" the chunk.  We have no optional parameters so we
	 * are in good shape.
	 */
	chunk->subh.cookie_hdr = (struct sctp_signed_cookie *)chunk->skb->data;
	if (!pskb_pull(chunk->skb, ntohs(chunk->chunk_hdr->length) -
					sizeof(struct sctp_chunkhdr)))
		goto nomem;

	/* In RFC 2960 5.2.4 3, if both Verification Tags in the State Cookie
	 * of a duplicate COOKIE ECHO match the Verification Tags of the
	 * current association, consider the State Cookie valid even if
	 * the lifespan is exceeded.
	 */
	new_asoc = sctp_unpack_cookie(ep, asoc, chunk, GFP_ATOMIC, &error,
				      &err_chk_p);

	/* FIXME:
	 * If the re-build failed, what is the proper error path
	 * from here?
	 *
	 * [We should abort the association. --piggy]
	 */
	if (!new_asoc) {
		/* FIXME: Several errors are possible.  A bad cookie should
		 * be silently discarded, but think about logging it too.
		 */
		switch (error) {
		case -SCTP_IERROR_NOMEM:
			goto nomem;

		case -SCTP_IERROR_STALE_COOKIE:
			sctp_send_stale_cookie_err(net, ep, asoc, chunk, commands,
						   err_chk_p);
			return sctp_sf_pdiscard(net, ep, asoc, type, arg, commands);
		case -SCTP_IERROR_BAD_SIG:
		default:
			return sctp_sf_pdiscard(net, ep, asoc, type, arg, commands);
		}
	}

	/* Update socket peer label if first association. */
	if (security_sctp_assoc_request((struct sctp_endpoint *)ep,
					chunk->skb))
		return sctp_sf_pdiscard(net, ep, asoc, type, arg, commands);

	/* Set temp so that it won't be added into hashtable */
	new_asoc->temp = 1;

	/* Compare the tie_tag in cookie with the verification tag of
	 * current association.
	 */
	action = sctp_tietags_compare(new_asoc, asoc);

	switch (action) {
	case 'A': /* Association restart. */
		retval = sctp_sf_do_dupcook_a(net, ep, asoc, chunk, commands,
					      new_asoc);
		break;

	case 'B': /* Collision case B. */
		retval = sctp_sf_do_dupcook_b(net, ep, asoc, chunk, commands,
					      new_asoc);
		break;

	case 'C': /* Collision case C. */
		retval = sctp_sf_do_dupcook_c(net, ep, asoc, chunk, commands,
					      new_asoc);
		break;

	case 'D': /* Collision case D. */
		retval = sctp_sf_do_dupcook_d(net, ep, asoc, chunk, commands,
					      new_asoc);
		break;

	default: /* Discard packet for all others. */
		retval = sctp_sf_pdiscard(net, ep, asoc, type, arg, commands);
		break;
	}

	/* Delete the tempory new association. */
	sctp_add_cmd_sf(commands, SCTP_CMD_SET_ASOC, SCTP_ASOC(new_asoc));
	sctp_add_cmd_sf(commands, SCTP_CMD_DELETE_TCB, SCTP_NULL());

	/* Restore association pointer to provide SCTP command interpeter
	 * with a valid context in case it needs to manipulate
	 * the queues */
	sctp_add_cmd_sf(commands, SCTP_CMD_SET_ASOC,
			 SCTP_ASOC((struct sctp_association *)asoc));

	return retval;

nomem:
	return SCTP_DISPOSITION_NOMEM;
}

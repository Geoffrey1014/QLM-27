/*
 * POC for Linux commit c42458fcf54b3d0bc2ac06667c98dceb43831889
 * Bug: Memory leak in realloc pattern when realloc fails
 *
 * This POC demonstrates the memory leak pattern where ptr = realloc(ptr, size)
 * overwrites the original pointer. If realloc() fails and returns NULL,
 * the original buffer becomes unreachable, causing a memory leak.
 *
 * CWE-401: Missing Release of Memory after Effective Lifetime (Memory Leak)
 */

#include <stddef.h>
#include <stdlib.h>

/* Kernel-style type definitions */
typedef unsigned int gfp_t;
#define GFP_KERNEL 0

/* Stub declarations for kernel functions */
extern void *kvrealloc(void *p, size_t size, gfp_t flags);
extern void kvfree(void *p);
extern void *krealloc(void *p, size_t size, gfp_t flags);
extern void kfree(void *p);

/*
 * BUGGY FUNCTION - Memory leak when kvrealloc fails
 * Pattern from module_frob_arch_sections()
 */
int process_data_buggy(int *data, size_t count)
{
    void *scratch = NULL;
    size_t scratch_size = 0;
    size_t i;

    for (i = 0; i < count; i++) {
        size_t needed_size = (i + 1) * sizeof(int) * 100;

        if (needed_size > scratch_size) {
            scratch_size = needed_size;
            /* BUG: If kvrealloc fails, original scratch is leaked */
            scratch = kvrealloc(scratch, scratch_size, GFP_KERNEL);
            if (!scratch)
                return -1;  /* Memory leak! Original buffer is lost */
        }

        /* Use scratch buffer... */
    }

    if (scratch)
        kvfree(scratch);

    return 0;
}

/*
 * FIXED FUNCTION - Properly handles realloc failure
 */
int process_data_fixed(int *data, size_t count)
{
    void *scratch = NULL;
    void *new_scratch;
    size_t scratch_size = 0;
    size_t i;

    for (i = 0; i < count; i++) {
        size_t needed_size = (i + 1) * sizeof(int) * 100;

        if (needed_size > scratch_size) {
            scratch_size = needed_size;
            /* FIXED: Use temporary variable */
            new_scratch = kvrealloc(scratch, scratch_size, GFP_KERNEL);
            if (!new_scratch) {
                kvfree(scratch);  /* Free original buffer on failure */
                return -1;
            }
            scratch = new_scratch;
        }

        /* Use scratch buffer... */
    }

    if (scratch)
        kvfree(scratch);

    return 0;
}

/*
 * Another buggy example using krealloc
 */
int resize_buffer_buggy(size_t initial_size, size_t final_size)
{
    char *buffer = NULL;
    size_t current_size = initial_size;

    buffer = krealloc(NULL, current_size, GFP_KERNEL);
    if (!buffer)
        return -1;

    /* Grow the buffer - BUG: memory leak if krealloc fails */
    current_size = final_size;
    buffer = krealloc(buffer, current_size, GFP_KERNEL);
    if (!buffer)
        return -1;  /* Original buffer leaked! */

    kfree(buffer);
    return 0;
}

/*
 * Fixed version using temporary variable
 */
int resize_buffer_fixed(size_t initial_size, size_t final_size)
{
    char *buffer = NULL;
    char *new_buffer;
    size_t current_size = initial_size;

    buffer = krealloc(NULL, current_size, GFP_KERNEL);
    if (!buffer)
        return -1;

    /* Grow the buffer - FIXED: use temporary */
    current_size = final_size;
    new_buffer = krealloc(buffer, current_size, GFP_KERNEL);
    if (!new_buffer) {
        kfree(buffer);  /* Free original on failure */
        return -1;
    }
    buffer = new_buffer;

    kfree(buffer);
    return 0;
}

/*
 * Buggy example with standard realloc (for completeness)
 */
int grow_array_buggy(int **arr, size_t *size, size_t new_size)
{
    /* BUG: Direct assignment loses original pointer on failure */
    *arr = realloc(*arr, new_size * sizeof(int));
    if (!*arr)
        return -1;  /* Memory leak if realloc failed */

    *size = new_size;
    return 0;
}

/*
 * Fixed version
 */
int grow_array_fixed(int **arr, size_t *size, size_t new_size)
{
    int *new_arr = realloc(*arr, new_size * sizeof(int));
    if (!new_arr) {
        /* Original *arr still valid, caller can free it */
        return -1;
    }
    *arr = new_arr;
    *size = new_size;
    return 0;
}

/* Main function for compilation test */
int main(void)
{
    int data[10] = {0};

    process_data_buggy(data, 10);   /* Will trigger CodeQL alert */
    process_data_fixed(data, 10);   /* Should NOT trigger alert */

    resize_buffer_buggy(100, 1000); /* Will trigger CodeQL alert */
    resize_buffer_fixed(100, 1000); /* Should NOT trigger alert */

    int *arr = NULL;
    size_t size = 0;
    grow_array_buggy(&arr, &size, 100);  /* Will trigger CodeQL alert */
    grow_array_fixed(&arr, &size, 100);  /* Should NOT trigger alert */

    return 0;
}

#include <stdint.h>

static uint64_t __count = 0;

// External linkage: exercises `accesses` handling in the test wrapper
// generated for externally-linked functions.
uint64_t count()
/*@ accesses __count;
    requires
        __count < 100u64;
  @*/
{
  return __count++;
}

// `static` so that this exercises the test wrapper generated for internal
// linkage as well as `accesses`.
static uint64_t count_alt()
/*@ accesses __count;
    requires
        __count < 100u64;
  @*/
{
  return __count++;
}

/* CN's exporter names a static test through the same externally-visible
 * wrapper spelling Fulminate generates. AustenTest compiles the original C
 * target, so expose that wrapper only for its target build. */
#ifdef __AUSTEN_TEST
uint64_t static_counterpass_count_alt(void)
{
  return count_alt();
}
#endif

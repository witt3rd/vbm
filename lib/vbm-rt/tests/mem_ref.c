/* The byte-for-byte test of the runtime's mem* (scripts/rt/runtime/rt.c, native part): every size 0..300, every source and destination alignment 0..63, overlaps both ways for memmove, against libc.
 * The runtime's functions are compiled under other names (tests/test_mem.sh); libc's are the oracle. Exit 0 only when every case is byte-identical. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
void *rt_memcpy(void *, const void *, size_t);
void *rt_memmove(void *, const void *, size_t);
void *rt_memset(void *, int, size_t);
int rt_memcmp(const void *, const void *, size_t);
#define N 4096
static unsigned char src[N + 128], a[N + 128], b[N + 128];
static long cases;
static void bad(const char *what, size_t n, size_t so, size_t dof) { fprintf(stderr, "MISMATCH %s n=%zu src_off=%zu dst_off=%zu\n", what, n, so, dof); exit(1); }
int main(void) {
  unsigned s = 12345; for (size_t i = 0; i < sizeof src; i++) { s = s * 1103515245u + 12345u; src[i] = (unsigned char)(s >> 16); }
  for (size_t n = 0; n <= 300; n++) for (size_t so = 0; so < 64; so++) for (size_t d = 0; d < 64; d++) {
    memcpy(a, src, sizeof a); memcpy(b, src, sizeof b);
    memcpy(a + 200 + d, src + 700 + so, n); rt_memcpy(b + 200 + d, src + 700 + so, n); if (memcmp(a, b, sizeof a)) bad("memcpy", n, so, d); cases++;
    memset(a + d, (int)(n * 7 + so), n); rt_memset(b + d, (int)(n * 7 + so), n); if (memcmp(a, b, sizeof a)) bad("memset", n, so, d); cases++;
  }
  /* memmove: overlapping, the destination below and above the source, by every distance 0..80 */
  for (size_t n = 0; n <= 300; n++) for (int dist = -80; dist <= 80; dist++) {
    memcpy(a, src, sizeof a); memcpy(b, src, sizeof b);
    memmove(a + 400 + dist, a + 400, n); rt_memmove(b + 400 + dist, b + 400, n); if (memcmp(a, b, sizeof a)) bad("memmove", n, 400, (size_t)(400 + dist)); cases++;
  }
  /* memcmp: equal, and differing at every position, both signs */
  for (size_t n = 0; n <= 100; n++) for (size_t pos = 0; pos <= n; pos++) {
    memcpy(a, src, 128); memcpy(b, src, 128); if (pos < n) b[pos] ^= 0x80;
    int x = memcmp(a, b, n), y = rt_memcmp(a, b, n); if ((x > 0) - (x < 0) != (y > 0) - (y < 0)) bad("memcmp", n, pos, 0); cases++;
    int x2 = memcmp(b, a, n), y2 = rt_memcmp(b, a, n); if ((x2 > 0) - (x2 < 0) != (y2 > 0) - (y2 < 0)) bad("memcmp rev", n, pos, 0); cases++;
  }
  printf("ran: mem_ref: %ld cases\n", cases);
  return 0;
}

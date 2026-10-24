// The practical speed ceiling: the same input sets as sorted, deduplicated
// arrays, and union, intersection and difference as linear merges. One
// thread, unverified. Prints the same lines as spec/ALGORITHM.md asks.
//   cc -O3 -o arrays arrays.c && ./arrays 22
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static uint32_t hash32(uint32_t x) {
  x ^= x >> 16;
  x *= 0x7feb352du;
  x ^= x >> 15;
  x *= 0x846ca68bu;
  x ^= x >> 16;
  return x;
}

static uint64_t gen(uint32_t seed, unsigned bits, uint32_t i) {
  uint64_t h = hash32(2u * i + seed);
  return bits >= 32 ? h : h & ((1ull << bits) - 1);
}

// LSD radix sort on 32-bit keys, then drop duplicates; returns the new length
static size_t sorted_set(uint32_t *a, size_t n) {
  uint32_t *tmp = malloc(n * sizeof *a);
  for (int shift = 0; shift < 32; shift += 8) {
    size_t count[257] = {0};
    for (size_t i = 0; i < n; i++) count[((a[i] >> shift) & 255) + 1]++;
    for (int b = 0; b < 256; b++) count[b + 1] += count[b];
    for (size_t i = 0; i < n; i++) tmp[count[(a[i] >> shift) & 255]++] = a[i];
    memcpy(a, tmp, n * sizeof *a);
  }
  free(tmp);
  size_t m = 0;
  for (size_t i = 0; i < n; i++)
    if (m == 0 || a[m - 1] != a[i]) a[m++] = a[i];
  return m;
}

// op 0: union, 1: intersection, 2: difference; returns the result length
static size_t merge(int op, const uint32_t *a, size_t na, const uint32_t *b, size_t nb, uint32_t *out) {
  size_t i = 0, j = 0, m = 0;
  while (i < na && j < nb) {
    if (a[i] < b[j]) {
      if (op != 1) out[m++] = a[i];
      i++;
    } else if (a[i] > b[j]) {
      if (op == 0) out[m++] = b[j];
      j++;
    } else {
      if (op != 2) out[m++] = a[i];
      i++, j++;
    }
  }
  if (op != 1)
    while (i < na) out[m++] = a[i++];
  if (op == 0)
    while (j < nb) out[m++] = b[j++];
  return m;
}

static double ms(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e3 + t.tv_nsec / 1e6;
}

static uint64_t sum(const uint32_t *a, size_t n) {
  uint64_t s = 0;
  for (size_t i = 0; i < n; i++) s += a[i];
  return s;
}

int main(int argc, char **argv) {
  unsigned D = argc > 1 ? (unsigned)atoi(argv[1]) : 22;
  size_t n = (size_t)1 << D;
  uint32_t *A = malloc(n * 4), *B = malloc(n * 4), *R = malloc(2 * n * 4);
  double t0 = ms();
  for (size_t i = 0; i < n; i++) A[i] = (uint32_t)gen(0, D + 1, (uint32_t)i), B[i] = (uint32_t)gen(1, D + 1, (uint32_t)i);
  size_t na = sorted_set(A, n), nb = sorted_set(B, n);
  double t1 = ms();
  printf("D %u\nbuild_ms %.1f sizes %zu %zu\n", D, t1 - t0, na, nb);
  const char *names[3] = {"union", "inter", "diff"};
  for (int op = 0; op < 3; op++) {
    double s = ms();
    size_t m = merge(op, A, na, B, nb, R);
    double e = ms();
    printf("%s_ms %.1f size %zu sum %llu\n", names[op], e - s, m, (unsigned long long)sum(R, m));
  }
  return 0;
}

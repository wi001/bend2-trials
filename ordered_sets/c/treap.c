// The algorithm of spec/ALGORITHM.md in C: unverified, one thread.
// Trees are persistent, as in the Bend and Lean versions (A and B are reused
// by all three operations), so split and join copy paths instead of mutating.
// Nodes come from an arena and are never freed.
//   cc -O3 -o treap treap.c && ./treap 22
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef struct Node {
  struct Node *l, *r;
  uint64_t k;
  uint32_t p;
} Node;

#define CHUNK (1u << 20)
static Node *chunk;
static size_t used = CHUNK;

static Node *mk(Node *l, uint64_t k, uint32_t p, Node *r) {
  if (used == CHUNK) {
    chunk = malloc(sizeof(Node) * CHUNK);
    used = 0;
  }
  Node *n = &chunk[used++];
  n->l = l, n->k = k, n->p = p, n->r = r;
  return n;
}

static uint32_t hash32(uint32_t x) {
  x ^= x >> 16;
  x *= 0x7feb352du;
  x ^= x >> 15;
  x *= 0x846ca68bu;
  x ^= x >> 16;
  return x;
}

static uint32_t prio(uint64_t k) { return hash32((uint32_t)k); }

// node a above node b
static int above(uint32_t pa, uint64_t ka, uint32_t pb, uint64_t kb) {
  return pa > pb || (pa == pb && ka > kb);
}

static Node *join(Node *l, uint64_t k, Node *r) {
  uint32_t pk = prio(k);
  int top = 0;  // 0: k, 1: l's root, 2: r's root
  uint32_t tp = pk;
  uint64_t tk = k;
  if (l && above(l->p, l->k, tp, tk)) top = 1, tp = l->p, tk = l->k;
  if (r && above(r->p, r->k, tp, tk)) top = 2;
  if (top == 0) return mk(l, k, pk, r);
  if (top == 1) return mk(l->l, l->k, l->p, join(l->r, k, r));
  return mk(join(l, k, r->l), r->k, r->p, r->r);
}

static Node *join2(Node *l, Node *r) {
  if (!l) return r;
  if (!r) return l;
  if (above(l->p, l->k, r->p, r->k)) return mk(l->l, l->k, l->p, join2(l->r, r));
  return mk(join2(l, r->l), r->k, r->p, r->r);
}

static void split(uint64_t k, Node *t, Node **lo, int *found, Node **hi) {
  if (!t) {
    *lo = *hi = NULL;
    *found = 0;
  } else if (k < t->k) {
    Node *h;
    split(k, t->l, lo, found, &h);
    *hi = mk(h, t->k, t->p, t->r);
  } else if (k > t->k) {
    Node *l;
    split(k, t->r, &l, found, hi);
    *lo = mk(t->l, t->k, t->p, l);
  } else {
    *lo = t->l, *hi = t->r, *found = 1;
  }
}

static Node *uni(Node *a, Node *b) {
  if (!a) return b;
  if (!b) return a;
  Node *l2, *r2;
  int f;
  split(a->k, b, &l2, &f, &r2);
  Node *L = uni(a->l, l2), *R = uni(a->r, r2);
  return join(L, a->k, R);
}

static Node *inter(Node *a, Node *b) {
  if (!a || !b) return NULL;
  Node *l2, *r2;
  int f;
  split(a->k, b, &l2, &f, &r2);
  Node *L = inter(a->l, l2), *R = inter(a->r, r2);
  return f ? join(L, a->k, R) : join2(L, R);
}

static Node *diff(Node *a, Node *b) {
  if (!a) return NULL;
  if (!b) return a;
  Node *l2, *r2;
  int f;
  split(a->k, b, &l2, &f, &r2);
  Node *L = diff(a->l, l2), *R = diff(a->r, r2);
  return f ? join2(L, R) : join(L, a->k, R);
}

static uint64_t gen(uint32_t seed, unsigned bits, uint32_t i) {
  uint64_t h = hash32(2u * i + seed);
  return bits >= 32 ? h : h & ((1ull << bits) - 1);
}

static Node *build(uint32_t seed, unsigned bits, unsigned d, uint32_t lo) {
  if (d == 0) {
    uint64_t g = gen(seed, bits, lo);
    return mk(NULL, g, prio(g), NULL);
  }
  Node *L = build(seed, bits, d - 1, lo), *R = build(seed, bits, d - 1, lo + (1u << (d - 1)));
  return uni(L, R);
}

static void measure(Node *t, uint64_t *size, uint64_t *sum) {
  if (!t) return;
  *size += 1, *sum += t->k;
  measure(t->l, size, sum);
  measure(t->r, size, sum);
}

static double ms(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e3 + t.tv_nsec / 1e6;
}

int main(int argc, char **argv) {
  unsigned D = argc > 1 ? (unsigned)atoi(argv[1]) : 22;
  double t0 = ms();
  Node *A = build(0, D + 1, D, 0), *B = build(1, D + 1, D, 0);
  double t1 = ms();
  uint64_t sa = 0, ka = 0, sb = 0, kb = 0;
  measure(A, &sa, &ka), measure(B, &sb, &kb);
  printf("D %u\nbuild_ms %.1f sizes %llu %llu\n", D, t1 - t0, (unsigned long long)sa, (unsigned long long)sb);
  const char *names[3] = {"union", "inter", "diff"};
  for (int op = 0; op < 3; op++) {
    double s = ms();
    Node *R = op == 0 ? uni(A, B) : op == 1 ? inter(A, B) : diff(A, B);
    double e = ms();
    uint64_t size = 0, sum = 0;
    measure(R, &size, &sum);
    printf("%s_ms %.1f size %llu sum %llu\n", names[op], e - s, (unsigned long long)size, (unsigned long long)sum);
  }
  return 0;
}

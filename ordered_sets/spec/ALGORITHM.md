# The shared algorithm and benchmark

Every implementation (Bend, Lean, C) computes exactly these trees, so their
outputs can be compared number for number.

## Trees

A tree is a leaf or a node `(left, key, prio, right)`. Keys are natural
numbers below 2^32; `prio` is a 32-bit unsigned priority. The trees are
treaps: shape follows priorities, but correctness never depends on shape.

## Hash and priority

`hash32(x)` on a 32-bit unsigned `x`, all arithmetic modulo 2^32
("lowbias32"):

    x = x xor (x >> 16)
    x = x * 0x7feb352d
    x = x xor (x >> 15)
    x = x * 0x846ca68b
    x = x xor (x >> 16)

`prio(k) = hash32(k mod 2^32)`. `node(l, k, r)` is the node
`(l, k, prio(k), r)`.

Node a is **above** node b when `prio(a) > prio(b)`, or the priorities are
equal and `key(a) > key(b)`.

## Operations

`join(l, k, r)`, for trees whose keys satisfy l < k < r. The top is whichever
of these is highest under "above": the middle key k (with priority prio(k)),
the root of l if l is a node, the root of r if r is a node.

    top is k:          (l, k, prio(k), r)
    top is l's root:   (l.left, l.key, l.prio, join(l.right, k, r))
    top is r's root:   (join(l, k, r.left), r.key, r.prio, r.right)

`join2(l, r)`, for trees whose keys satisfy l < r:

    l is a leaf:                 r
    r is a leaf:                 l
    l's root above r's root:     (l.left, l.key, l.prio, join2(l.right, r))
    otherwise:                   (join2(l, r.left), r.key, r.prio, r.right)

`split(k, t)` returns `(lower, found, upper)`:

    t is a leaf:                 (leaf, false, leaf)
    t = (l, k', p, r), k < k':   (L, f, R) = split(k, l);  (L, f, (R, k', p, r))
    t = (l, k', p, r), k > k':   (L, f, R) = split(k, r);  ((l, k', p, L), f, R)
    t = (l, k', p, r), k = k':   (l, true, r)

`union(a, b)`:

    a is a leaf:  b
    b is a leaf:  a
    a = (l1, k1, p1, r1):  (l2, f, r2) = split(k1, b)
                           L, R = union(l1, l2), union(r1, r2)   -- in parallel
                           join(L, k1, R)

`inter(a, b)`:

    a or b is a leaf:      leaf
    a = (l1, k1, p1, r1):  (l2, f, r2) = split(k1, b)
                           L, R = inter(l1, l2), inter(r1, r2)   -- in parallel
                           f ? join(L, k1, R) : join2(L, R)

`diff(a, b)` (keys of a not in b):

    a is a leaf:           leaf
    b is a leaf:           a
    a = (l1, k1, p1, r1):  (l2, f, r2) = split(k1, b)
                           L, R = diff(l1, l2), diff(r1, r2)     -- in parallel
                           f ? join2(L, R) : join(L, k1, R)

## Building the input sets

`gen(seed, bits, i) = hash32((2 * i + seed) mod 2^32) mod 2^bits`.

`build(seed, bits, d, lo)` builds the set of the 2^d keys
`gen(seed, bits, lo), ..., gen(seed, bits, lo + 2^d - 1)` (indices mod 2^32):

    d = 0:      node(leaf, gen(seed, bits, lo), leaf)
    d = e + 1:  L, R = build(seed, bits, e, lo), build(seed, bits, e, lo + 2^e)   -- in parallel
                union(L, R)

## Benchmark

Parameter D (default 22, from the first command-line argument). Then

    A = build(0, D + 1, D, 0)
    B = build(1, D + 1, D, 0)
    U = union(A, B);  I = inter(A, B);  X = diff(A, B)

Time the building of A and B together, then each operation separately, each
with a monotonic clock in milliseconds. A tree's `size` is its number of nodes
and its `sum` the sum of its keys (exact; it fits in 64 bits). Size and sum are
computed outside the timed sections. Print exactly:

    D <D>
    build_ms <ms> sizes <size A> <size B>
    union_ms <ms> size <size U> sum <sum U>
    inter_ms <ms> size <size I> sum <sum I>
    diff_ms <ms> size <size X> sum <sum X>

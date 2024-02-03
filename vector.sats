#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"

absview malloced_ptr
vtypedef Boxed(a: t@ype, l: addr) = (malloced_ptr, a? @ l | ptr l)

fn {a: t@ype} array_malloc {n: nat} (n: int n): [l: agz] (Boxed(@[a?][n], l))

fn ty_free {a: t@ype} {l: addr} (Boxed(a, l)): void = "mac#free"

dataview disjunct_array_v(a: t@ype, l: addr, n: int, m: int) =
  | disjunct_array_nil (a, l, 0, 0)

  | {n: nat} {m: nat}
    disjunct_array_inited (a, l, n + 1, m) of 
    (a @ l, disjunct_array_v(a, l + sizeof(a), n, m))

  | {m: nat}
    disjunct_array_uninited (a, l, 0, m + 1) of 
    (a? @ l, disjunct_array_v(a, l + sizeof(a), 0, m))

vtypedef DynArray(a: t@ype, l: addr, n: int, m: int) = 
    (malloced_ptr, disjunct_array_v (a, l, n, m) | ptr l)

vtypedef Vector(a: t@ype, l: addr, n: int, m: int) = 
    @{ detail=DynArray(a, l, n, m - n), size=size_t n, capacity=size_t m }

fun {a: t@ype} vector_make (): [l: agz][m: pos] (Vector(a, l, 0, m))

fun {a: t@ype} vector_pop {l: agz}{m: pos}{n: pos | n <= m}
    (vec: &(Vector(a, l, n, m)) >> Vector(a, l, n - 1, m)): a

fun {a: t@ype} vector_push {l: agz}{m: pos}{n: nat | n <= m}
    (vec: &(Vector(a, l, n, m)) >> Vector(a, l2, n + 1, k), elem: a):
    #[k: pos | k >= n + 1] #[l2: agz] void

fn {a: t@ype} vector_expand {l: agz}{m: pos}{n: nat | n <= m}
   (vec: &(Vector(a, l, n, m)) >> Vector(a, l2, n, k)): 
   #[k: pos | k == 2 * m] #[l2: agz] void

fn {a: t@ype} vector_push_one {l: agz}{m: pos}{n: nat | n < m}
   (vec: &(Vector(a, l, n, m)) >> Vector(a, l, n + 1, m), elem: a): void

fn {a: t@ype} vector_get {l: agz}{m: pos}{n, i: nat | n < m | i < n}
   (vec: !(Vector(a, l, n, m)), i: int i): a

fun vector_dealloc {a:t@ype}{l: agz}{n, m: nat | n <= m} (vec: Vector(a, l, n, m)): void

fn dynarray_dealloc {a: t@ype}{l: agz}{n, m: nat} (darray: DynArray(a, l, n, m)): void

prfun disjunct_array_uninit {a: t@ype}{l: addr}{n, m: nat}
      (a1: !disjunct_array_v(a, l, n, m) >> disjunct_array_v(a, l, 0, m + n)): void

prfun disjunct_to_array_v {a: t@ype}{l: addr}{n: nat}
      (v: !disjunct_array_v(a, l, 0, n) >> array_v(a?, l, n)): void

praxi commutative_add_mul {l: addr} {n, m: int} (): [l + m * n == l + n * m] void

prfn disjunct_array_split {a: t@ype}{l: addr}{n, m: nat}
      (v: disjunct_array_v(a, l, n, m)): (array_v(a, l, n), array_v(a?, l + sizeof(a) * n, m))

prfun disjunct_array_unsplit {a: t@ype}{l: addr}{n, m: nat}
      (a1: array_v(a, l, n), a2: array_v(a?, l + sizeof(a) * n, m)): (disjunct_array_v(a, l, n, m))

prfun array_v_to_disjunct {a: t@ype}{l: addr}{n: nat}
      (v: !array_v (a?, l, n) >> disjunct_array_v(a, l, 0, n)): void

fn {a: t@ype} dynarray_copy {l1, l2: addr} {n1, n2, m1, m2: nat | n2 + m2 >= n1}
   (a1: !DynArray(a, l1, n1, m1),
    a2: !DynArray(a, l2, n2, m2) >> DynArray(a, l2, n1, m2 + n2 - n1),
    to_copy: size_t n1): void

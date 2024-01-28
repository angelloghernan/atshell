#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"

absview malloced_ptr
vtypedef Boxed(a: t@ype, l: addr) = (malloced_ptr, a? @ l | ptr l)

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

fun {a: t@ype} vector_push {l: agz}{m: pos}{n: nat | n <= m}
    (vec: &(Vector(a, l, n, m)) >> Vector(a, l2, n + 1, k), elem: a):
    #[k: pos | k >= n + 1] #[l2: agz] void

fun {a: t@ype} vector_pop {l: agz}{m: pos}{n: pos | n <= m}
    (vec: &(Vector(a, l, n, m)) >> Vector(a, l, n - 1, m)): a

fun vector_dealloc {a:t@ype}{l: agz}{n, m: nat | n <= m} (vec: Vector(a, l, n, m)): void

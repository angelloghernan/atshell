#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"
#define ATS_DYNLOADFLAG 0

absview malloced_ptr

vtypedef Boxed(a: t@ype, l: addr) = (malloced_ptr, a? @ l | ptr l)

fn {a: t@ype} ty_malloc (): [l: agz] (Boxed(a, l)) =
    $extfcall([l: agz] (Boxed(a, l)), "malloc", sizeof<a>)

fn {a: t@ype} array_malloc {n: nat} (n: int n): [l: agz] (Boxed(@[a?][n], l)) =
    $extfcall([l: agz] (Boxed(@[a?][n], l)), "malloc", sizeof<a> * n)

extern fn ty_free {a: t@ype} {l: addr} (Boxed(a, l)): void = "mac#free"


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

prfun array_v_to_disjunct {a: t@ype}{l: addr}{n: nat} .<n>.
      (v: !array_v (a?, l, n) >> disjunct_array_v(a, l, 0, n)): void =
      sif n == 0 then let
          prval () = array_v_unnil (v)
          prval () = v := disjunct_array_nil ()
      in end
      else let 
          prval (pf, cons) = array_v_uncons (v)
          prval () = array_v_to_disjunct (cons)
          prval () = v := disjunct_array_uninited (pf, cons)
      in end

prfun disjunct_to_array_v {a: t@ype}{l: addr}{n: nat} .<n>.
      (v: !disjunct_array_v(a, l, 0, n) >> array_v(a?, l, n)): void =
      case+ v of
      | disjunct_array_nil () => let prval () = v := array_v_nil () in end
      | disjunct_array_inited (pf, cons) =>
        let
            prval () = disjunct_to_array_v (cons)
            prval () = v := array_v_cons (pf, cons)
        in end
      | disjunct_array_uninited (pf, cons) =>
        let
            prval () = disjunct_to_array_v (cons)
            prval () = v := array_v_cons (pf, cons)
        in end

prfun disjunct_extract {a: t@ype}{l: addr}{n, m: nat} .<n>.
      (v: !disjunct_array_v(a, l, n, m) >> disjunct_array_v(a, l + sizeof(a) * n, 0, m)): (array_v(a, l, n)) =
      case+ v of
      | disjunct_array_nil () =>
        let
            prval () = v := disjunct_array_nil ()
        in 
            array_v_nil () 
        end
      | disjunct_array_uninited (pf, cons) => 
        let 
            prval () = v := disjunct_array_uninited (pf, cons)
        in
            array_v_nil ()
        end
      | disjunct_array_inited (pf, cons) => 
        let
            prval rest = disjunct_extract (cons)
            prval () = v := cons
        in
            array_v_cons (pf, rest)
        end

/*
prfn disjunct_array_split {a: t@ype}{l: addr}{n, m: nat}
      (v: disjunct_array_v(a, l, n, m)): (array_v(a, l, n), array_v(a?, l + sizeof(a) * n, m)) =


        
 
fun {a: t@ype} vector_make (): [l: agz][m: nat] (Vector(a, l, 0, m)) =
    let
        val box = array_malloc (1)
        prval () = array_v_to_disjunct (box.1)
    in
        @{ detail=box, size=i2sz(0), capacity=i2sz(1)}
end

fun {a: t@ype} vector_back_ptr {l: agz}{n, m: nat | n > 0} (vec: !Vector(a, l, n, m)): (ptr (l + (n - 1) * sizeof(a))) =
        ptr_add<a>(vec.detail.2, vec.size - 1)


fun {a: t@ype} vector_push {l: agz}{l2: agz}{n, m, k: nat} 
    (vec: !Vector(a, l, n, m) >> Vector(a, l2, n + 1, k), elem: a): void =
    if vec.size < vec.capacity then let
        val p = ptr_add<a>(vec.detail.2, vec.size)
        val () = !p := elem
        val () = vec.size := vec.size + 1
    in end
    else let
    in end
*/

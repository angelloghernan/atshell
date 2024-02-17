#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"
staload "vector.sats"

fn {a: t@ype} ty_malloc (): [l: agz] (Boxed(a, l)) =
    $extfcall([l: agz] (Boxed(a, l)), "malloc", sizeof<a>)

implement {a} array_malloc {n} (n: size_t n): [l: agz] (Boxed(@[a?][n], l)) =
    $extfcall([l: agz] (Boxed(@[a?][n], l)), "malloc", sizeof<a> * n)

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

prfn disjunct_array_split {a: t@ype}{l: addr}{n, m: nat}
      (v: disjunct_array_v(a, l, n, m)): (array_v(a, l, n), array_v(a?, l + sizeof(a) * n, m)) =
      let
          prval inited = disjunct_extract (v)
          prval () = disjunct_to_array_v (v)
      in
          (inited, v)
end

prfun disjunct_array_unsplit {a: t@ype}{l: addr}{n, m: nat} .<n>.
      (a1: array_v(a, l, n), a2: array_v(a?, l + sizeof(a) * n, m)): (disjunct_array_v(a, l, n, m)) =
      sif n == 0 then let
          prval () = array_v_unnil (a1)
          prval EQINT () = eqint_make {n, 0} ()
          prval () = array_v_to_disjunct (a2)
      in
          a2
      end
      else let
          prval (pf, cons) = array_v_uncons (a1)
          prval rest = disjunct_array_unsplit (cons, a2)
      in
          disjunct_array_inited (pf, rest)
      end

prfun disjunct_array_uninit {a: t@ype}{l: addr}{n, m: nat} .<n>.
      (a1: !disjunct_array_v(a, l, n, m) >> disjunct_array_v(a, l, 0, m + n)): void =
      sif n == 0 then ()
      else let
          prval disjunct_array_inited (pf, cons) = a1
          prval () = disjunct_array_uninit (cons)
          prval () = a1 := disjunct_array_uninited (pf, cons)
      in
end

prfun disjunct_array_uninit_one {a: t@ype}{l: addr}{n: pos}{m: nat} .<n - 1>.
     (a1: !disjunct_array_v(a, l, n, m) >> disjunct_array_v(a, l, n - 1, m + 1)): void =
     sif n == 1 then let
        prval disjunct_array_inited (pf, cons) = a1
     in
        a1 := disjunct_array_uninited (pf, cons)
     end
     else let
        prval disjunct_array_inited (pf, cons) = a1
        prval () = disjunct_array_uninit_one (cons)
     in
        a1 := disjunct_array_inited (pf, cons)
     end

fn {a: t@ype} dynarray_copy {l1, l2: addr} {n1, n2, m1, m2: nat | n2 + m2 >= n1}
   (a1: !DynArray(a, l1, n1, m1),
    a2: !DynArray(a, l2, n2, m2) >> DynArray(a, l2, n1, m2 + n2 - n1),
    to_copy: size_t n1): void =
    let
        fun {a: t@ype} loop {l1, l2: addr} {n, m1, m2: nat | m2 >= n} .<n>.
            (a1: !disjunct_array_v(a, l1, n, m1), 
             a2: !disjunct_array_v(a, l2, 0, m2) >> disjunct_array_v(a, l2, n, m2 - n),
             to_copy: size_t n, p1: ptr l1, p2: ptr l2): void =
            if to_copy = 0 then ()
            else let
                prval disjunct_array_inited (pf1, cons1) = a1
                prval disjunct_array_uninited (pf2, cons2) = a2
                val () = !p2 := !p1
                val () = loop (cons1, cons2, to_copy - 1, ptr_succ<a>(p1), ptr_succ<a>(p2))
                prval () = a1 := disjunct_array_inited (pf1, cons1)
                prval () = a2 := disjunct_array_inited (pf2, cons2)
            in
            end

        prval () = disjunct_array_uninit (a2.1)
    in
        loop<a>(a1.1, a2.1, to_copy, a1.2, a2.2)
end

implement {a: t@ype} vector_make (): [l: agz] (Vector(a, l, 0, 1)) =
    let
        val box = array_malloc (i2sz(1))
        prval () = array_v_to_disjunct (box.1)
    in
        @{ detail=box, size=i2sz(0), capacity=i2sz(1) }
end

implement {a} vector_push_one {l}{m}{n} (vec, elem): void =
    let
        prval () = commutative_add_mul {l} {n, sizeof(a)} ()
        prval (l, r) = disjunct_array_split (vec.detail.1)
        val p: ptr(l + n * sizeof(a)) = ptr_add<a>(vec.detail.2, vec.size)
        prval (pf, r) = array_v_uncons (r)
        val () = ptr_set<a> (pf | p, elem)
        prval () = l := array_v_extend(l, pf)
        prval () = vec.detail.1 := disjunct_array_unsplit (l, r)
        val () = vec.size := vec.size + 1
    in
end

implement {a} vector_expand {l}{m}{n} (vec): void =
    let
        val new_capacity: size_t(m * 2) = vec.capacity * 2
        val box = array_malloc (new_capacity)
        prval () = array_v_to_disjunct (box.1)
        val () = dynarray_copy(vec.detail, box, vec.size)
        prval () = disjunct_array_uninit (vec.detail.1)
        prval () = disjunct_to_array_v (vec.detail.1)
        val () = ty_free (vec.detail)
        val () = vec.detail := box
        val () = vec.capacity := new_capacity
    in
end


implement {a} vector_get (vec, i): a = elem where {
    prval (l, r) = disjunct_array_split (vec.detail.1)
    val p = vec.detail.2
    val elem = array_get_at(!p, i)
    prval () = vec.detail.1 := disjunct_array_unsplit (l, r)
}
    

(* implement {a} vector_push {l}{m}{j} (vec, elem): void = *)
(*     if vec.size < vec.capacity then vector_push_one (vec, elem) *)
(*     else let *)
(*         val () = vector_expand<a>(vec) *)
(*     in *)
(*         vector_push_one (vec, elem) *)
(*     end *)

fun {a: t@ype} vector_back_ptr {l: agz}{n, m: nat | n > 0} (vec: !Vector(a, l, n, m)): (ptr (l + (n - 1) * sizeof(a))) =
        ptr_add<a>(vec.detail.2, vec.size - 1)

implement {a} vector_pop {l: addr}{m: int}{n: int} (vec): a =
    let
        prval (l, r) = disjunct_array_split (vec.detail.1)
        val p = vec.detail.2
        val elem = array_get_at(!p, vec.size - 1)
        prval () = vec.detail.1 := disjunct_array_unsplit (l, r)
        val sz: size_t(n - 1) = vec.size - 1
        val () = vec.size := sz
        prval () = disjunct_array_uninit_one (vec.detail.1)
    in
        elem
end


implement dynarray_dealloc (darray): void = ty_free (darray) where {
    prval () = disjunct_array_uninit (darray.1)
    prval () = disjunct_to_array_v (darray.1)
}

implement vector_dealloc {a:t@ype}{l: addr}{n, m: int} (vec: Vector(a, l, n, m)): void =
    let
        prval () = disjunct_array_uninit (vec.detail.1)
        prval () = disjunct_to_array_v (vec.detail.1)
    in
        ty_free (vec.detail)
end


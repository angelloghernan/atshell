#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"
staload "vector.sats"
staload "split_string.sats"
staload "exec.sats"

macdef NULL = $extval(ptr(0), "0")

fn {a: t@ype} malloc_array {n: nat} (n: size_t n): [l: agz] (BoxedArray(a, l, n)) =
    $extfcall([l: agz] (Boxed(@[a?][n], l)), "malloc", sizeof<a> * n)

implement make_terminated {l}{n}{m}
    (split_str, p): [l2: agz] TerminatedArray(l2, m) =
    let
        fun loop {l1, l2: addr}{n, m: nat}{k: pos | k == m + 1}
            (v: !split_string_v(l1, n, m),
             arr: !array_v(ptr?, l2, k) >> terminated_array_v(l2, k - 1) |
             size: size_t n,
             p1: ptr l1, p2: ptr l2): void =
            if size = 0 then let
                prval () = split_string_v_is_end (v)
                prval (l, r) = array_v_uncons (arr)
                prval () = array_v_unnil (r)
                val () = ptr_set<ptr(0)>(l | p2, NULL)
                prval () = arr := terminated_array_nil (l)
            in end
            else let
                prval () = split_string_v_is_not_end (v)
                prval (al, ar) = array_v_uncons (arr)
                prval (vl, vr) = split_string_get_first (v)
                val c = ptr_get(vl | p1)
            in
                if c = '\0' then let
                    val _ = $showtype c
                    val () = ptr_set<ptr>(al | p2, ptr_succ<ptr>(p1))
                    val () = loop (vr, ar | size - 1, ptr_succ<ptr>(p1), ptr_succ<ptr>(p2))
                    prval () = v := split_string_nil (vl, vr)
                    prval () = arr := terminated_array_cons (al, ar)
                in
                end
                else if c = '\x1a' then let
                    val () = loop (vr, ar | size - 1, ptr_succ<ptr>(p1), p2)
                    prval () = v := split_string_replace (vl, vr)
                    prval () = arr := terminated_array_cons (al, ar)
                in
                end
                else let
                    val () = loop (vr, ar | size - 1, ptr_succ<ptr>(p1), p2)
                    prval () = v := split_string_cons (vl, vr)
                    prval () = arr := terminated_array_cons (al, ar)
                in
                end
            end
        // box.0: malloc pf (mpf), box.1: at-view, box.2: ptr l
        val box = malloc_array<ptr>(split_str.num_strings + 1)

        prval pf = box.0
        prval av = box.1

        val () = loop (split_str.str_view, av | split_str.size, p, box.2)
    in
        @{ mpf=pf, tpf=av, size=split_str.size }
end

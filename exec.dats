#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"
staload "vector.sats"
staload "split_string.sats"
staload "exec.sats"

staload UN = "prelude/SATS/unsafe.sats"

%{^
    #include <unistd.h>
%}

macdef NULL = $extval(ptr(0), "0")

fn {a: t@ype} malloc_array {n: nat} (n: size_t n): [l: agz] (BoxedArray(a, l, n)) =
    $extfcall([l: agz] (Boxed(@[a?][n], l)), "malloc", sizeof<a> * n)

implement exec_variable_params {l}{m} (ta) =
    let
        prval (ptr_pf, f) = terminated_array_v_fst (ta.tpf)
        val name_p = ptr_get<ptr>(ptr_pf | ta.p)
        prval () = ta.tpf := f (ptr_pf)
    in
        $extfcall(int, "execvp", name_p, ta.p)
end

implement make_terminated {l}{n}{m}
    (split_str, p): [l2: agz] TerminatedArray(l2, m) =
    let
        fun loop {l1, l2: addr}{n: nat}{m: pos}{p: nat | p == m}
            (v: !split_string_v(l1, n, m),
             arr: !array_v(ptr?, l2, p) >> terminated_array_v(l2, p - 1) |
             num_strings: size_t m,
             p1: ptr l1, p2: ptr l2): void =
            if num_strings = 1 then let
                prval (l, r) = array_v_uncons (arr)
                prval () = array_v_unnil (r)
                val () = ptr_set<ptr(0)>(l | p2, NULL)
                prval () = arr := terminated_array_nil (l)
            in end
            else let
                prval () = split_string_v_m_is_not_end (v)
                prval (vl, vr) = split_string_get_first (v)
                val c = !p1
            in
                if c = '\0' then let
                    prval (al, ar) = array_v_uncons (arr)
                    val () = !p2 := ptr_succ<char>(p1)
                    val () = loop (vr, ar | num_strings - 1, ptr_succ<char>(p1), ptr_succ<ptr>(p2))
                    prval () = v := split_string_nil (vl, vr)
                    prval () = arr := terminated_array_cons (al, ar)
                in end
                else if c = '\x1a' then let
                    val () = loop (vr, arr | num_strings, ptr_succ<char>(p1), p2)
                    prval () = v := split_string_replace (vl, vr)
                in end
                else let
                    val () = print c
                    val () = loop (vr, arr | num_strings, ptr_succ<char>(p1), p2)
                    prval () = v := split_string_cons (vl, vr)
                in end
            end
        // box.0: malloc pf (mpf), box.1: at-view, box.2: ptr l
        val box = malloc_array<ptr>(split_str.num_strings + 1)

        prval pf = box.0
        prval av = box.1

        prval (avl, avr) = array_v_uncons (av)

        val p2 = box.2

    in
        if split_str.num_strings = 0 then let
            prval () = array_v_unnil (avr)
            val () = ptr_set<ptr(0)>(avl | p2, NULL)
            prval () = av := terminated_array_nil (avl)
        in 
            @{ mpf=pf, tpf=av, size=split_str.num_strings, p=box.2 }
        end
        else let
            val () = print "Printing now\n"
            val () = ptr_set<ptr>(avl | p2, p)

            val () = loop (split_str.str_view, avr | split_str.num_strings, p, ptr_succ<ptr>(box.2))
            
            prval () = av := terminated_array_cons (avl, avr)
            val () = print "\nPrinting done\n"
        in 
            @{ mpf=pf, tpf=av, size=split_str.num_strings, p=box.2 }
        end
end

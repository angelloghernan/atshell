#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"
staload "split_string.sats"

// stadef REPLACEMENT_CHAR = 26

implement array_to_split_string {l} {n}
   (buf_view: BufferView(asciiChar, l, n), p: ptr l, size: size_t n, delimiter: asciiChar): [m: nat] SplitString(l, n, m) =
   let
      fun loop {l: addr}{n: pos}
         (str_v: (@[asciiChar][n] @ l) | p: ptr l, sz: size_t n, delimiter: asciiChar, prev_null: bool):
         [m: nat] (split_string_v(l, n, m) | size_t m) =
         let
            prval (pf1, pf2) = array_v_uncons(str_v)
            val c: asciiChar = ptr_get<asciiChar>(pf1 | p)
         in
            if sz = 1 then let 
               prval () = array_v_unnil (pf2)
               val () = ptr_set<char(0)>(pf1 | p, '\0')
            in
               (split_string_nil(pf1, split_string_end ()) | i2sz(1))
            end
            else if c = delimiter && prev_null = false then let
               val () = ptr_set<char(0)>(pf1 | p, '\0')
               val (rpf | sz2) = loop (pf2 | ptr_succ<char>(p), sz - 1, delimiter, true)
            in
               (split_string_nil (pf1, rpf) | sz2 + 1)
            end
            else if c = delimiter && prev_null = true then let
               val () = ptr_set<char(26)>(pf1 | p, '\x1a')
               val (rpf | sz2) = loop (pf2 | ptr_succ<char>(p), sz - 1, delimiter, true)
            in
               (split_string_replace (pf1, rpf) | sz2)
            end
            else let
               val (rpf | sz2) = loop (pf2 | ptr_succ<char>(p), sz - 1, delimiter, false)
            in
               (split_string_cons (pf1, rpf) | sz2)
            end
         end
      
      prval (malloc_pf, arr_pf) = buf_view
      val (ssv | num_strings) = loop (arr_pf | p, size, delimiter, false)
   in
      @{ size=size, num_strings=num_strings, str_view=ssv, pf=malloc_pf }
end

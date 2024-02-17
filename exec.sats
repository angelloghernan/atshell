#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"
staload "split_string.sats"
staload "vector.sats"

dataview terminated_array_v(l: addr, int) =
  | terminated_array_nil (l, 0) of (ptr(0) @ l)

  | {n: nat}
    terminated_array_cons (l, n + 1) of (ptr @ l, terminated_array_v(l + sizeof(ptr), n))

vtypedef TerminatedArray(l: addr, n: int) =
  @{ mpf=malloced_ptr(l), tpf=terminated_array_v(l, n), size=size_t n  }


fn make_terminated {l: addr}{n: pos}{m: nat}
    (split_str: !SplitString(l, n, m), p: ptr l): [l2: agz] TerminatedArray(l2, m)


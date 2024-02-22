#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"
staload "split_string.sats"
staload "vector.sats"

dataview terminated_array_v(l: addr, int) =
  | terminated_array_nil (l, 0) of (ptr(0) @ l)

  | {n: nat}
    terminated_array_cons (l, n + 1) of (ptr @ l, terminated_array_v(l + sizeof(ptr), n))

vtypedef TerminatedArray(l: addr, n: int) =
  @{ mpf=malloced_ptr(l), tpf=terminated_array_v(l, n), size=size_t n, p=ptr l }

fn make_terminated {l: addr}{n: pos}{m: nat}
    (split_str: !SplitString(l, n, m), p: ptr l): [l2: agz] TerminatedArray(l2, m)

fn exec_variable_params {l: addr}{m: nat} (ta: !TerminatedArray(l, m)): int

praxi terminated_array_v_to_array_v {l: addr}{m: nat} 
      (terminated_array_v(l, m)): array_v(ptr, l, m + 1)

praxi terminated_array_v_fst {l: addr}{m: nat}
      (terminated_array_v(l, m)): (ptr @ l, ptr @ l -<lin,prf> terminated_array_v (l, m))

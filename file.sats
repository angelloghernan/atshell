#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"

typedef file_t = $extype"FILE"

fun file_open_raw: (string, string) -> [l: agz](file_t @ l | ptr l) = "mac#fopen"
fun file_close_raw: {l: agz}(file_t @ l | ptr l) -> int = "mac#fclose"
fun file_write_raw: {l: agz}(!(file_t @ l) | string, size_t, size_t) -> size_t = "mac#fwrite"

fun file_read_raw {m, n: nat | m <= n}{l: agz}{l2: agz}
           (b0ytes n @ l, !(file_t @ l2) | ptr l, size_t 1, size_t m, ptr l2): 
           [o: nat | o <= m]
           (b0ytes n @ l | size_t o) = 
           "mac#fread"

viewdef File(l: addr) = file_t @ l

fun file_read1 {m, n: nat | m <= n}{l: agz}{l2: agz}
    (pf: b0ytes n @ l, fpf: !File(l2) | p: ptr l, sz: size_t m, fptr: ptr l2): 
    (b0ytes n @ l | size_t)

fun file_read_raw1 {m, n: nat | m <= n}{l: agz}{l2: agz}
           (array_v (char?, l, n), !File(l2) | ptr l, size_t 1, size_t m, f: ptr l2): 
           [o: nat | o <= m]
           (@[char][o] @ l, @[char?][n - o] @ (l + o * sizeof(char)) | size_t o) = 
           "mac#fread"

fn file_read {m, n: nat | m <= n}{l: agz}{l2: agz}
          (pf: array_v (char?, l, n), fpf: !File(l2) | p: ptr l, sz: size_t m, f: ptr l2):
          [o: nat | o <= m]
          (@[char][o] @ l, @[char?][n - o] @ (l + o * sizeof(char)) | size_t o)


fn file_write {m, n: nat | m <= n}{l: agz}
          (fpf: !File(l) | A: &(@[char][n]), sz: size_t m, f: ptr l):
          [o: nat | o <= m] (size_t o)


fn file_open {l: addr} (file_name: string, mode: string): 
          [l: addr] (option_v(File(l), l > null) | ptr l)

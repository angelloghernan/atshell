#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"
staload "file.sats"
staload "vector.sats"
staload "./vector.dats"
staload "prelude/basics_dyn.sats"

macdef NULL = $extval(ptr(0), "0")

vtypedef Buffer(a: t@ype, l: addr, n: int) = ((@[a][n]) @ l | ptr l)

extern fn get_line_raw: (&ptr(0) >> ptr l, &size_t? >> size_t n, file_t) ->
                       #[l: agz]#[n: nat]((@[char][n]) @ l | ssize_t) = "mac#getline"

extern fn put_buf {l: addr}{n: int}{a: t@ype} (Buffer(a, l, n)): void = "mac#free"

macdef stdin_raw = $extval(file_t, "stdin")

vtypedef Array(a: t@ype, l: addr, n: int) = @{ size=size_t n, buffer=Buffer(a, l, n) }

typedef Command(n: int) = [m, k: nat | m <= k | k <= n] @{ str_start=size_t m, str_end=size_t k }

fn get_line (): [l: agz][n: nat](Array(char, l, n)) = array where {
    var p: ptr = NULL
    var bufsize: size_t
    val (pf | _) = get_line_raw (p, bufsize, stdin_raw)
    val array = @{ size=bufsize, buffer=(pf | p) }
}


fn array_iter_over {l: addr}{n, i, j: nat | i <= j | j <= n}
                   (array: !Array(char, l, n), i: size_t i, j: size_t j, f: char -> void): void =
    let
        fun loop {l: addr}{n, i, j: nat | i <= j | j <= n} .<j - i>.
            (buf: !Buffer(char, l, n), i: size_t i, j: size_t j, f: char -> void): void =
            if i = j then ()
            else let
                val c = array_get_at(!(buf.1), i)
                val () = f (c)
            in loop (buf, i + 1, j, f)
        end
    in
        loop (array.buffer, i, j, f)
end 

fn array_iter {l: addr}{n: nat} (array: !Array(char, l, n), f: char -> void): void =
    array_iter_over (array, i2sz(0), array.size, f)


fn find_cmd {l: addr}{n: nat}
            (array: !Array(char, l, n), res: &Command(n)? >> opt(Command(n), b)): #[b:bool] bool(b) =
    let
        fun loop {l: addr}{n, i: nat | i <= n} .<n - i>.
            (array: !Array(char, l, n), i: size_t i): [j: nat | j <= n | j >= i] size_t j =
            if i = array.size then i
            else if array_get_at(!(array.buffer.1), i) = ' ' then i + 1
            else loop (array, i + 1)
        
        val start = loop (array, i2sz(0))
    in
        if start = array.size then false where {
            prval () = opt_none(res)
        }
        else true where {
            // I have no idea why, but I have to explicitly annotate this type
            val str_end: [p: nat | p <= n] size_t(p) = loop(array, start + 1)
            val () = res := @{ str_start=start, str_end=str_end }
            prval () = opt_some(res)
        }
end

fn make_empty_cmd {l: addr}{n: nat} (array: !Array(char, l, n)): (Command(n)?) =
    res where { var res: Command(n) }

fn print_cmd {l: addr}{n: nat}{b: bool}
             (array: !Array(char, l, n), maybe_cmd: !opt(Command(n), b), b: bool b): void =
    if b then let
        prval () = opt_unsome (maybe_cmd)
        val () = array_iter_over (array, maybe_cmd.str_start, maybe_cmd.str_end, lam c => print (c))
        prval () = opt_some (maybe_cmd)
    in end
    else ()

implement main0 (argv, argc) = 
    let
        val () = print ("> ")

        val array = get_line ()

        var cmd = make_empty_cmd (array)

        val b = find_cmd (array, cmd)

        val () = print_cmd (array, cmd, b)


        val () = if b then let prval () = opt_unsome (cmd) in end
                 else let prval () = opt_unnone (cmd) in end

        val () = array_iter (array, lam c => print (c))

        val () = put_buf (array.buffer)

        var vec = vector_make<int> ()

        val () = vector_dealloc (vec)
    in
end

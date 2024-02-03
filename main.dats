#include "share/atspre_staload.hats"
#include "share/atspre_staload_libats_ML.hats"
staload "file.sats"
staload "prelude/basics_dyn.sats"
staload "./vector.sats"
staload _ = "./vector.dats"

macdef NULL = $extval(ptr(0), "0")

vtypedef Buffer(a: t@ype, l: addr, n: int) = ((@[a][n]) @ l | ptr l)

extern fn get_line_raw: (&ptr(0) >> ptr l, &size_t? >> size_t n, file_t) ->
                       #[l: agz]#[n: nat]((@[char][n]) @ l | ssize_t) = "mac#getline"

extern fn put_buf {l: addr}{n: int}{a: t@ype} (Buffer(a, l, n)): void = "mac#free"

macdef stdin_raw = $extval(file_t, "stdin")

vtypedef Array(a: t@ype, l: addr, n: int) = @{ size=size_t n, buffer=Buffer(a, l, n) }

typedef Command(n: int) = [m, k: nat | m <= k | k <= n] @{ str_start=size_t m, str_end=size_t k }

fun {a: t@ype} vector_push {l: agz}{m: pos}{n: nat | n <= m}
    (vec: &(Vector(a, l, n, m)) >> Vector(a, l2, n + 1, k), elem: a):
    #[k: pos | k >= n + 1] #[l2: agz] void = 
    if vec.size < vec.capacity then vector_push_one (vec, elem)
    else let
        val () = vector_expand<a>(vec)
    in
        vector_push_one (vec, elem)
    end

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


fn find_cmd {l: addr}{n: nat}{i: nat | i <= n}
            (array: !Array(char, l, n), res: &Command(n)? >> opt(Command(n), b), i: size_t i): #[b:bool] bool(b) =
    let
        fun loop {l: addr}{n, i: nat | i <= n} .<n - i>.
            (array: !Array(char, l, n), i: size_t i): [j: nat | j <= n | j >= i] size_t j =
            if i = array.size then i
            else if array_get_at(!(array.buffer.1), i) = ' ' then i + 1
            else loop (array, i + 1)
        
        val start = i
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

fn make_cmd_vec {l: addr}{n: nat} (array: !Array(char, l, n)): [l2: agz](Vector(Command(n), l2, 0, 1)) =
    res where { var res = vector_make<Command(n)> () }

fn print_maybe_cmd {l: addr}{n: nat}{b: bool}
             (array: !Array(char, l, n), maybe_cmd: !opt(Command(n), b), b: bool b): void =
    if b then let
        prval () = opt_unsome (maybe_cmd)
        val () = array_iter_over (array, maybe_cmd.str_start, maybe_cmd.str_end, lam c => print (c))
        prval () = opt_some (maybe_cmd)
    in end
    else ()

fn print_cmd {l: addr}{n: nat}{b: bool}
             (array: !Array(char, l, n), cmd: Command(n)): void = () where {
    val () = array_iter_over (array, cmd.str_start, cmd.str_end, lam c => print (c))
}

fn print_cmds {l: addr}{n: nat}{l2: agz}{k: pos}{m: nat | m <= k}
    (array: !Array(char, l, n), cmds: !Vector(Command(n), l2, m, k)): void = () where {

    fun loop{l: addr}{n: nat}{l2: agz}{k: pos}{m: nat | m <= k}{i: nat | i <= m}
        (array: !Array(char, l, n), cmds: !Vector(Command(n), l2, m, k), i: int i): void =
        if i2sz(i) = cmds.size then ()
        else let
            val cmd = vector_get (cmds, i)
            val () = print_cmd (array, cmd)
        in
            loop (array, cmds, i + 1)
        end

    val () = loop (array, cmds, 0)
}


fn parse_cmds {l: addr}{n: nat}{l2: agz}
              (array: !Array(char, l, n), vec: &Vector(Command(n), l2, 0, 1) >> Vector(Command(n), l3, m, k)): 
              #[l3: agz]#[k: pos]#[m: nat | m <= k] void =
    let
        fun loop {l: addr}{l2: agz}{k: pos}{n, m, i: nat | i <= n | m <= k} 
                 (array: !Array(char, l, n), 
                  vec: &Vector(Command(n), l2, m, k) >> Vector(Command(n), l3, m2, k2), 
                  i: size_t i): #[l3: agz] #[k2: pos] #[m2: nat | m2 <= k2] void =
            if i = array.size then ()
            else let
                var maybe_cmd = make_empty_cmd (array)
                val b = find_cmd (array, maybe_cmd, i)
            in
                if b then let
                    prval () = opt_unsome (maybe_cmd)
                    val () = vector_push<Command(n)>(vec, maybe_cmd)
                in 
                    loop(array, vec, maybe_cmd.str_end)
                end
                else let 
                    prval () = opt_unnone (maybe_cmd)
                in end
            end
    in
        loop (array, vec, i2sz(0))
    end
    

implement main0 (argv, argc) = 
    let
        val () = print ("> ")

        val array = get_line ()

        var cmds = make_cmd_vec (array)
        
        val () = parse_cmds (array, cmds)

        val () = print (cmds.size)

        val () = print_cmds (array, cmds)

        val () = dynarray_dealloc (cmds.detail)

        val () = put_buf (array.buffer)

        // prval () = disjunct_array_uninit (vec.detail.1)
        // prval () = disjunct_to_array_v (vec.detail.1)
        // val () = ty_free (vec.detail)

        // val () = vector_dealloc (vec)
    in
end

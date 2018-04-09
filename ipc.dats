staload "prelude/SATS/arrayptr.sats"
staload "prelude/DATS/arrayptr.dats"
staload "prelude/SATS/filebas.sats"
staload "prelude/DATS/filebas.dats"
staload "prelude/SATS/integer.sats"
staload "prelude/DATS/integer.dats"
staload "prelude/SATS/integer_size.sats"
staload "prelude/DATS/integer_size.dats"
staload "prelude/SATS/pointer.sats"
staload "prelude/DATS/pointer.dats"

staload UN = "prelude/SATS/unsafe.sats"
staload "prelude/DATS/unsafe.dats"

staload "ipc.sats"
#include "ipc.hats"

typedef vo_uint = $extype "volatile unsigned int"

typedef padding = $extype "padding"

typedef header = @{
    nodes = uint,
    rings = uint,
    size = uint,
    msg_size = size_t
}

typedef ring = @{
    size = uint,
    msg_size = uint,
    offset = uint,
    pad1 = padding,
    head = vo_uint,
    pad2 = padding,
    tail = vo_uint
}

typedef msg_t(msg:t0ype) = @{
    size = size_t,
    msg = msg
}

vtypedef ipc_v(msg:t0ype, nodes:int, size:int) = '{
    fname = string,
    header = ptr,
    rings = arrayptr(ring, nodes*(nodes-1)),
    data = arrayptr(msg, size*(nodes*(nodes-1)))
}

assume ipc(msg,nodes,size) = ipc_v(msg,nodes,size)

implement {a} ipc_create{n}{m}(fname, nodes, size, msg_size) =
  let
    // open a file in preparation for mmap
    val flags = $extval(int, "O_RDWR|O_CREAT|O_EXCL")
    val perms = $extval(int, "S_IRUSR|S_IWUSR")
    val fd = open(fname, flags, perms)
  in
    // check the file is successfully opened
    case+ 0 of
      | _ when fd = ~1 => $raise AssertExn()
      | _ =>
        let
          // compute sizes of portions of mmap'd buffer
          val real_size = po2(size)
          val n_rings = nodes*(nodes-1u)
          val file_size = sizeof<header>
                        + $UN.cast{size_t}(n_rings)*sizeof<ring>
                        + $UN.cast{size_t}(n_rings*real_size)*msg_size
        in
          // check that file has been appropriately resized
          case+ 0 of
            | _ when ftruncate(fd, file_size) = ~1 => $raise AssertExn()
            | _ =>
              let
                // mmap ipc buffer
                val rwflags = $extval(int, "PROT_READ|PROT_WRITE")
                val mapflags = $extval(int, "MAP_SHARED")
                val p = mmap(the_null_ptr, file_size, rwflags, mapflags, fd, 0)
              in
                // check that buffer was mmap'd successfully
                case+ 0 of
                  | _ when p = the_null_ptr => $raise AssertExn()
                  | _ =>
                    let
                      // zero out buffer
                      val _ = memset(p, 0, file_size)
                      // cast buffer to ipc data structure
                      val r = ptr_add<header>(p, 1)
                      val d = ptr_add<ring>(r, $UN.cast{size_t}(n_rings))
                      val x = $UN.castvwtp0{ipc_v(a, n, m)}
                          (
                            '{
                              fname = fname,
                              header = p,
                              rings = r,
                              data = d
                             }
                          )
                      // function that initializes rings with values for
                      // templated data structure in main function
                      fun init_rings
                      {n:int|n>1}
                      {m:nat}
                      {i:int|i >= 0 && i < n*(n-1)}
                      (
                        i:uint(i),
                        rs:uint, // real size of ipc_v (in nodes)
                        ms:uint, // size of single message
                        ipc: !ipc(a, n, m)
                      ): void =
                        let
                          // get pointer to i'th ring
                          val p = ptrcast(ipc.rings)
                          val q = ptr1_add_guint<ring>(p, i)
                          val (pf,pfn|r) = $UN.ptr0_vtake{ring}(q)
                          // set appropriate size info
                          val () = begin
                            r->size := rs-1u;
                            r->msg_size := ms;
                            r->offset := i*rs;
                          end
                          prval () = pfn(pf);
                        in
                          if i > 0 then
                            init_rings{n}{m}(i-1u, rs, ms, ipc)
                          else ()
                        end
                      // ok since n >= 2
                      extern praxi __assert():<> [n*(n-1)-1 >= 1] unit_p
                      prval pf = __assert()
                      val seed = n_rings-1u
                      val () = init_rings{n}{m}
                          (seed, real_size, $UN.cast{uint}(msg_size), x)
                      // setup header
                      val (pf,pfn|head) = $UN.ptr0_vtake{header}(x.header)
                      val () = begin
                        head->nodes := nodes;
                        head->rings := n_rings;
                        head->size := real_size;
                        head->msg_size := msg_size;
                      end
                      prval () = pfn(pf)
                    in
                      x
                    end
              end
        end
  end

implement {a} ipc_open {n}{m}
(
  fname, nodes, size, msg_size
) =
  let
    var buf : statbuf
    val flags = $extval(int, "O_RDWR")
    val perms = $extval(int, "S_IRUSR|S_IWUSR")
    val fd = open(fname, flags, perms)
  in
    // check if file already exists
    case+ 0 of
      // if it doesn't, create it
      | _ when fd = ~1 => ipc_create(fname, nodes, size, msg_size)
      // otherwise, open it
      | _ =>
        let
          val stat = fstat(fd, addr@buf)
        in
          case+ 0 of
            // bail if fstat has an error
            | _ when stat = ~1 => $raise AssertExn()
            // otherwise truncate to its current size
            // (not sure why; but leaving it just in case)
            | _ =>
              let
                val file_size = buf.st_size
                val ft = ftruncate(fd, $UN.cast{size_t}(file_size))
              in
                case+ 0 of
                  // bail if error
                  | _ when ft = ~1 => $raise AssertExn()
                  // otherwise mmap buffer
                  | _ =>
                    let
                      val rwflags = $extval(int, "PROT_READ|PROT_WRITE")
                      val mapflags = $extval(int, "MAP_SHARED")
                      val p = mmap(the_null_ptr, $UN.cast{size_t}(file_size),
                                   rwflags, mapflags, fd, 0)
                    in
                      if p = the_null_ptr then
                        // mmap failed, bail out
                        $raise AssertExn()
                      else
                        // mmap succeeded, initialize ipc structure
                        let
                          val n_rings = nodes*(nodes-1u)
                          val r = ptr_add<header>(p, 1)
                          val d = ptr_add<ring>(r, $UN.cast{size_t}(n_rings))
                          val x = $UN.castvwtp0{ipc(a, n, m)}
                              (
                                '{
                                  fname = fname,
                                  header = p,
                                  rings = r,
                                  data = d
                                }
                              )
                        in
                          x
                        end
                    end
              end
        end
  end

implement {a} ipc_free {n}{m}(ipc) =
  let
    extern fun munmap(ptr, uint): int = "mac#"
    extern fun free(ptr): void = "mac#"
    val (pf,pfn|p) = $UN.ptr0_vtake{header}(ipc.header)
    val i = munmap(p, p->size)
    prval () = pfn(pf)
    var pp = $UN.castvwtp0{ptr}(ipc)
  in
    free(pp)
  end

fn
{a:t0ype}{tk:tk}
arrayptr_get_ptr_at_uint
{n:nat}
{i:int|i >= 0 && i < n}
(
  A: !arrayptr(INV(a), n),
  i: g1uint(tk, i)
):<> [l:addr] (a@l, a@l -<prf,lin> void | ptr(l)) =
  let
    val p = ptrcast(A)
    val q = ptr1_add_guint<a>(p, i)
  in
    $UN.ptr0_vtake(q)
  end

fn
{a:t0ype}
ipc_ring_from_to
{n:int|n>1}
{j:int|j >= 0 && j < n}
{k:int|k >= 0 && k < n && j != k}
(
  from:uint(j),
  to:uint(k),
  n:uint(n)
):<> [i:int | i >= 0 && i < n*(n-1)] uint(i) =
  if from > to then
    let
      extern praxi __assert1():<> [k*(n-1)+j-1 >= 0] unit_p
      extern praxi __assert2():<> [k*(n-1)+j-1 < n*(n-1)] unit_p
      prval pffoo = __assert1()
      prval pfbar = __assert2()
    in
      to*(n-1u)+from-1u
    end
  else
    let
      extern praxi __assert1():<> [k*(n-1)+j >= 0] unit_p
      extern praxi __assert2():<> [k*(n-1)+j < n*(n-1)] unit_p
      prval pffoo = __assert1()
      prval pfbar = __assert2()
    in
      to*(n-1u)+from
    end

fn
{a:t0ype}
ipc_recv_internal
{n:int|n>1}
{m:nat}
{k:int| k >= 0 && k < n*(n-1)}
{l:addr}
(
  pf: !INV(a)@l |
  ipc: !ipc(a, n, m),
  ring: uint(k),
  msg: ptr(l)
): bool =
  let
    val (pf_ring,pfn_ring|r) = arrayptr_get_ptr_at_uint<ring>(ipc.rings, ring)
    val t = r->tail
    val h = r->head
  in
    case+ 0 of
      // safe since h and t are volatile uints
      | _ when $UN.cast{uint}(h) = $UN.cast{uint}(t) =>
          let
            prval () = pfn_ring(pf_ring)
          in
            false
          end
      | _ =>
        let
          val p = ptrcast(ipc.data)
          val d = ptr_add<a>(p, $UN.cast{uint}(h))
          // safe since moves modded by size of buffer
          val (pf_d, pfn_d | d) = $UN.ptr0_vtake(d)
          val () = begin
            !msg := ptr_get<a>(pf_d | d);
            // barrier needed to make sure we finish reading msg
            // before moving the head (prevent read tearing)
            ipc_comp_barrier();
            // safe since h and head are volatile uints
            r->head := $UN.cast{vo_uint}
            (bitwise_and_uint($UN.cast{uint}(h)+1u, r->size))
          end
          prval () = pfn_d(pf_d)
          prval () = pfn_ring(pf_ring)
        in
          true
        end
  end

implement {a} ipc_recv {n}{m}{j}{k}
(
  pf |
  ipc, to, from, nodes, msg
) =
  let
    // loop is a busy wait using the cpu's pause instruction
    fun {a:t0ype} loop
    {n:int|n>1}
    {m:nat}
    {x:int|x>=0 && x < n*(n-1)}
    {l:addr}
    (
      pf: !INV(a)@l |
      ipc: !ipc(a, n, m),
      r:uint(x),
      msg: ptr(l)
    ): bool =
      if ~ipc_recv_internal{n}{m}{x}(pf | ipc, r, msg) then (
        ipc_relax();
        loop{n}{m}{x}(pf | ipc, r, msg)
      ) else true
  in
    loop{n}{m}(pf | ipc, ipc_ring_from_to(from, to, nodes), msg)
  end

fn
{a:t0ype}
ipc_send_internal
{n:int|n>1}
{m:nat}
{j:int| j >= 0 && j < n}
{k:int| k >= 0 && k < n && j != k}
{l:addr}
(
  pf: !INV(a)@l |
  ipc: !ipc(a, n, m),
  to: uint(j),
  from: uint(k),
  nodes: uint(n),
  msg: ptr(l)
): bool =
  let
    val ring = ipc_ring_from_to(from, to, nodes)
    val (pf_ring,pfn_ring|r) = arrayptr_get_ptr_at_uint<ring>(ipc.rings, ring)
    // safe since head/tail are volatile uint
    val h = bitwise_and_uint($UN.cast{uint}(r->head)-1u, r->size)
    val t = $UN.cast{uint}(r->tail)
  in
    case+ 0 of
      | _ when t = h =>
          let
            prval () = pfn_ring(pf_ring)
          in
            false
          end
      | _ =>
        let
          val p = ptrcast(ipc.data)
          val d = ptr_add<a>(p, $UN.cast{uint}(t))
          // safe since moves modded by size of buffer
          val (pf_d, pfn_d | d) = $UN.ptr0_vtake(d)
          val () = ptr_set<a>(pf_d | d, !msg)
          // barrier is needed to make sure item is updated before it's made
          // available to concurrent reader
          val () = ipc_write_barrier()
          val () = r->tail := $UN.cast{vo_uint}(bitwise_and_uint(t+1u, r->size))
          prval () = pfn_d(pf_d)
          prval () = pfn_ring(pf_ring)
        in
          true
        end
  end

implement {a} ipc_send{n}{m}{j}{k}
(
  pf |
  ipc, to, from, nodes, msg
) =
  let
    fun {a:t0ype} loop
    {n:int|n>1}
    {m:nat}
    {j:int| j >= 0 && j < n}
    {k:int| k >= 0 && k < n && j != k}
    {l:addr}
    (
      pf: !INV(a)@l |
      ipc: !ipc(a, n, m),
      to: uint(j),
      from: uint(k),
      nodes: uint(n),
      msg: ptr(l)
    ): bool =
      if ~ipc_send_internal{n}{m}{j}{k}(pf | ipc, to, from, nodes, msg) then (
        ipc_relax();
        loop{n}{m}{j}(pf | ipc, to, from, nodes, msg)
      ) else true
  in
    loop{n}{m}(pf | ipc, to, from, nodes, msg)
  end

absviewtype ipc(msg:t0ype, nodes:int, size:int)

/// Create an ipc bridge for some processes.
///
/// *** Parameters
/// - =fname= name of file for ipc storage
/// - =nodes= number of different processes that will communicate over ipc
/// - =size= number of slots in each ring buffer
/// - =msg_size= size of data type that will be passed over ipc
///
/// *** Returns
/// An ipc bridge or throws an assert exception if something goes wrong.
fn
{a:t0ype}
ipc_create
{n:int|n>1}
{m:nat}
(
  fname:string,
  nodes:uint(n),
  size:uint(m),
  msg_size:size_t(sizeof(INV(a)))
): ipc(a, n, m)

/// Opens an ipc bridge or creates it if it does not exist.
///
/// *** Parameters
/// - =fname= name of file for ipc storage
/// - =nodes= number of different processes that will communicate over ipc
/// - =size= number of slots in each ring buffer
/// - =msg_size= size of data type that will be passed over ipc
///
/// *** Returns
/// An ipc bridge or throws an assert exception if something goes wrong.
fn
{a:t0ype}
ipc_open
{n:int|n>1}
{m:nat}
(
  fname:string,
  nodes:uint(n),
  size:uint(m),
  msg_size:size_t(sizeof(INV(a)))
): ipc(a, n, m)

/// Destroys an ipc bridge, munmaping the memory.
///
/// *** Parameters
/// - =ipc= an ipc bridge
///
/// *** Returns
/// void
fn
{a:t0ype}
ipc_free
{n:int|n>1}
{m:nat}
(
  ipc: ipc(INV(a), n, m)
): void

/// Receives a message over ipc. Blocks via spin lock until message is received.
///
/// *** Parameters
/// - =pf= a proof a msg is at l
/// - =ipc= an ipc bridge
/// - =to= process id of receiving node (i.e. this one)
/// - =from= process id to receive message from
/// - =nodes= number of nodes in process group
/// - =msg= pointer to message, which is filled when process returns
///
/// *** Returns
/// true
fn
{a:t0ype}
ipc_recv
{n:int|n>1}
{m:nat}
{j:int| j >= 0 && j < n}
{k:int| k >= 0 && k < n && j != k}
{l:addr}
(
  pf: !a@l |
  ipc: !ipc(INV(a), n, m),
  to: uint(j),
  from: uint(k),
  nodes: uint(n),
  msg: ptr(l)
): bool

/// Sends a message over ipc.
///
/// *** Parameters
/// - =pf= a proof a msg is at l
/// - =ipc= an ipc bridge
/// - =to= process id of receiving node
/// - =from= process id to send message from (i.e. this one)
/// - =nodes= number of nodes in process group
/// - =msg= pointer to message, which is filled when process returns
///
/// *** Returns
/// true
fn
{a:t0ype}
ipc_send
{n:int|n>1}
{m:nat}
{j:int| j >= 0 && j < n}
{k:int| k >= 0 && k < n && j != k}
{l:addr}
(
  pf: !a@l |
  ipc: !ipc(INV(a), n, m),
  to: uint(j),
  from: uint(k),
  nodes: uint(n),
  msg: ptr(l)
): bool

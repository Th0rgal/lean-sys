/-
  LeanSys: Zero-Wrapper Verified Systems Layer for Lean 4 (`0 import Lean`, `0 sorryAx`)
-/
import LeanSys.Contracts.MetaGate
import LeanSys.Contracts.SpeculativeGate
import LeanSys.Gate
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash
import LeanSys.Codec
import LeanSys.Store
import LeanSys.Mmap
import LeanSys.Lsm
import LeanSys.Table
import LeanSys.Auth
import LeanSys.ProcLog
import LeanSys.JsonRpc
import LeanSys.Http
import LeanSys.Reactor
import LeanSys.Sandbox
import LeanSys.Par

namespace LeanSys

/-! ## Zero-lock multi-threaded chunk, slice, and DAG wave scheduler (`LeanSys.Par`) -/
namespace Par
  abbrev verifyParChunk := LeanSys.Spec.verifyParChunk
  abbrev verifyArenaDisjoint := LeanSys.Spec.verifyArenaDisjoint
  abbrev verifyDagWaveStep := LeanSys.Spec.verifyDagWaveStep
end Par

/-! ## Core pure zero-copy slices, hashes, codecs, and C-ABI verification gates (`LeanSys.Core`) -/
namespace Core
  abbrev ByteSlice := LeanSys.Posix.ByteSlice
  abbrev Errno := LeanSys.Posix.Errno
  abbrev SysResult := LeanSys.Posix.SysResult
  abbrev JsonTape := LeanSys.Codec.JsonTape
  abbrev xxh64Slice := LeanSys.Hash.xxh64Slice
  abbrev xxh64String := LeanSys.Hash.xxh64String
  abbrev bloomInsert := LeanSys.Hash.bloomInsert
  abbrev bloomContains := LeanSys.Hash.bloomContains
  abbrev verifySliceBounds := LeanSys.Spec.verifySliceBounds
  abbrev verifyCounterexampleTriage := LeanSys.Spec.verifyCounterexampleTriage
  abbrev checkCounterexampleTriage := LeanSys.Contracts.checkCounterexampleTriage
  abbrev CounterexampleTriageInput := LeanSys.Contracts.CounterexampleTriageInput
  abbrev mix64Word := LeanSys.Spec.mix64Word
end Core

/-! ## OS file-descriptor, shared-memory SPSC ring, process log, and sandbox primitives (`LeanSys.Os`) -/
namespace Os
  abbrev Fd := LeanSys.Posix.Fd
  abbrev withFd {α : Type} := @LeanSys.Posix.withFd α
  abbrev preadByteArray := LeanSys.Posix.preadByteArray
  abbrev writeAll := LeanSys.Posix.writeAll
  abbrev atomicRename := LeanSys.Posix.atomicRename
  abbrev ShmRing := LeanSys.Mmap.ShmRing
  abbrev LogChunk := LeanSys.ProcLog.LogChunk
  abbrev readLogChunk := LeanSys.ProcLog.readLogChunk
  abbrev SandboxQuota := LeanSys.Sandbox.SandboxQuota
  abbrev SandboxResult := LeanSys.Sandbox.SandboxResult
  abbrev runSandboxedGroup := LeanSys.Sandbox.runSandboxedGroup
end Os

/-! ## Crash-atomic WAL/CAS store, LSM SST tables, and snapshot-isolated composite-key range scans (`LeanSys.Db`) -/
namespace Db
  abbrev StoreHandle := LeanSys.Store.Handle
  abbrev openStore := LeanSys.Store.openStore
  abbrev put := LeanSys.Store.put
  abbrev putString := LeanSys.Store.putString
  abbrev putBatch := LeanSys.Store.putBatch
  abbrev get? := LeanSys.Store.get?
  abbrev getString? := LeanSys.Store.getString?
  abbrev compact := LeanSys.Store.compact
  abbrev casPut := LeanSys.Store.casPut
  abbrev casMaterialize := LeanSys.Store.casMaterialize
  abbrev SstTable := LeanSys.Lsm.SstTable
  abbrev flushStore := LeanSys.Lsm.SstTable.flushStore
  abbrev flushAndCompactStore := LeanSys.Lsm.SstTable.flushAndCompactStore
  abbrev openSst := LeanSys.Lsm.SstTable.openSst
  abbrev CompositeKey := LeanSys.Table.CompositeKey
  abbrev tombstoneMarker := LeanSys.Table.tombstoneMarker
  abbrev isTombstoneSlice := LeanSys.Table.isTombstoneSlice
  abbrev putComposite := LeanSys.Table.putComposite
  abbrev deleteComposite := LeanSys.Table.deleteComposite
  abbrev getComposite? := LeanSys.Table.getComposite?
  abbrev rangeScan := LeanSys.Table.rangeScan
  abbrev rangeScanUpTo := LeanSys.Table.rangeScanUpTo
  abbrev rangeScanSnapshot := LeanSys.Table.rangeScanSnapshot
end Db

/-! ## Bounded zero-copy HTTP/1.1 server/router, JSON-RPC 2.0 framing, and constant-time bearer auth (`LeanSys.Web`) -/
namespace Web
  abbrev HttpRequest := LeanSys.Http.HttpRequest
  abbrev HttpResponse := LeanSys.Http.HttpResponse
  abbrev RouteEntry := LeanSys.Http.RouteEntry
  abbrev dispatchRoutes := LeanSys.Http.dispatchRoutes
  abbrev parseHttpRequest := LeanSys.Http.parseRequest
  abbrev serveLoop := LeanSys.Http.serveLoop
  abbrev httpClientRequest := LeanSys.Http.httpClientRequest
  abbrev RpcRequest := LeanSys.JsonRpc.RpcRequest
  abbrev parseRpcRequest? := LeanSys.JsonRpc.parseRequest?
  abbrev formatRpcSuccess := LeanSys.JsonRpc.formatSuccess
  abbrev verifyRotatedBearer := LeanSys.Auth.verifyRotatedBearer
  abbrev mintLease := LeanSys.Auth.mintLease
  abbrev validateLease := LeanSys.Auth.validateLease
end Web

end LeanSys

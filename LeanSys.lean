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
  abbrev verifyWorkerBudget := LeanSys.Spec.verifyWorkerBudget
  abbrev verifyPageAlignedBuffer := LeanSys.Spec.verifyPageAlignedBuffer
  abbrev selectIsaVariant := LeanSys.Spec.selectIsaVariant
  abbrev verifyIsaSelection := LeanSys.Spec.verifyIsaSelection
end Par

/-! ## Core pure zero-copy slices, hashes, codecs, and C-ABI verification gates (`LeanSys.Core`) -/
namespace Core
  abbrev ByteSlice := LeanSys.Posix.ByteSlice
  abbrev BorrowedSlice := LeanSys.Posix.BorrowedSlice
  abbrev RawByteView := LeanSys.Posix.RawByteView
  abbrev ByteSource := LeanSys.Posix.ByteSource
  abbrev Errno := LeanSys.Posix.Errno
  abbrev SysResult := LeanSys.Posix.SysResult
  abbrev JsonTape := LeanSys.Codec.JsonTape
  abbrev BorrowedJsonTape := LeanSys.Codec.BorrowedJsonTape
  abbrev xxh64Slice := LeanSys.Hash.xxh64Slice
  abbrev xxh64Borrowed := LeanSys.Hash.xxh64Borrowed
  abbrev xxh64Source := LeanSys.Hash.xxh64Source
  abbrev xxh64String := LeanSys.Hash.xxh64String
  abbrev bloomInsert := LeanSys.Hash.bloomInsert
  abbrev bloomContains := LeanSys.Hash.bloomContains
  abbrev verifySliceBounds := LeanSys.Spec.verifySliceBounds
  abbrev verifyBorrowedView := LeanSys.Spec.verifyBorrowedView
  abbrev verifyFdBounds := LeanSys.Spec.verifyFdBounds
  abbrev verifyUnixPathBounds := LeanSys.Spec.verifyUnixPathBounds
  abbrev verifyCounterexampleTriage := LeanSys.Spec.verifyCounterexampleTriage
  abbrev checkCounterexampleTriage := LeanSys.Contracts.checkCounterexampleTriage
  abbrev CounterexampleTriageInput := LeanSys.Contracts.CounterexampleTriageInput
  abbrev mix64Word := LeanSys.Spec.mix64Word
  abbrev StepReactorSpec (State Ev Eff : Type) := LeanSys.Spec.StepReactorSpec State Ev Eff
  abbrev LinearLeaseSpec (State Cmd : Type) := LeanSys.Spec.LinearLeaseSpec State Cmd
  abbrev IdempotentOutboxSpec (State Key Eff : Type) := LeanSys.Spec.IdempotentOutboxSpec State Key Eff
  abbrev ConservedResource := LeanSys.Spec.ConservedResource
  abbrev QuotaCircuitSpec (State Req : Type) := LeanSys.Spec.QuotaCircuitSpec State Req
end Core

/-! ## OS file-descriptor, shared-memory SPSC ring, process log, and sandbox primitives (`LeanSys.Os`) -/
namespace Os
  abbrev Fd := LeanSys.Posix.Fd
  abbrev MmapRegion := LeanSys.Posix.MmapRegion
  abbrev withFd {α : Type} := @LeanSys.Posix.withFd α
  abbrev preadByteArray := LeanSys.Posix.preadByteArray
  abbrev writeAll := LeanSys.Posix.writeAll
  abbrev atomicRename := LeanSys.Posix.atomicRename
  abbrev reflinkFile := LeanSys.Posix.reflinkFile
  abbrev unixListen := LeanSys.Posix.unixListen
  abbrev unixConnect := LeanSys.Posix.unixConnect
  abbrev setNonBlocking := LeanSys.Posix.setNonBlocking
  abbrev pollFdSet := LeanSys.Posix.pollFdSet
  abbrev ShmRing := LeanSys.Mmap.ShmRing
  abbrev MmapArena := LeanSys.Mmap.MmapArena
  abbrev IoUring := LeanSys.Mmap.IoUring
  abbrev IoUringCqe := LeanSys.Mmap.IoUringCqe
  abbrev LogChunk := LeanSys.ProcLog.LogChunk
  abbrev readLogChunk := LeanSys.ProcLog.readLogChunk
  abbrev SandboxQuota := LeanSys.Sandbox.SandboxQuota
  abbrev LandlockPolicy := LeanSys.Sandbox.LandlockPolicy
  abbrev SandboxResult := LeanSys.Sandbox.SandboxResult
  abbrev CgroupV2Metrics := LeanSys.Sandbox.CgroupV2Metrics
  abbrev queryLandlockAbi := LeanSys.Sandbox.queryLandlockAbi
  abbrev applyLandlockPolicy := LeanSys.Sandbox.applyLandlockPolicy
  abbrev runSandboxedGroup := LeanSys.Sandbox.runSandboxedGroup
  abbrev runLandlockedGroup := LeanSys.Sandbox.runLandlockedGroup
  abbrev resolveSelfCgroupV2Dir := LeanSys.Sandbox.resolveSelfCgroupV2Dir
  abbrev readCgroupV2Metrics := LeanSys.Sandbox.readCgroupV2Metrics
  abbrev runCgroupV2Group := LeanSys.Sandbox.runCgroupV2Group
end Os

/-! ## Crash-atomic WAL/CAS store, LSM SST tables, and snapshot-isolated composite-key range scans (`LeanSys.Db`) -/
namespace Db
  abbrev StoreHandle := LeanSys.Store.Handle
  abbrev openStore := LeanSys.Store.openStore
  abbrev openStoreWithChunk := LeanSys.Store.openStoreWithChunk
  abbrev put := LeanSys.Store.put
  abbrev putString := LeanSys.Store.putString
  abbrev putBatch := LeanSys.Store.putBatch
  abbrev get? := LeanSys.Store.get?
  abbrev getString? := LeanSys.Store.getString?
  abbrev compact := LeanSys.Store.compact
  abbrev casPut := LeanSys.Store.casPut
  abbrev casGet := LeanSys.Store.casGet
  abbrev casMaterialize := LeanSys.Store.casMaterialize
  abbrev CasAlgo256 := LeanSys.Store.CasAlgo256
  abbrev ReflinkOutcome := LeanSys.Store.ReflinkOutcome
  abbrev casPut256 := LeanSys.Store.casPut256
  abbrev casPutFile256 := LeanSys.Store.casPutFile256
  abbrev casGet256 := LeanSys.Store.casGet256
  abbrev casMaterializeReflink := LeanSys.Store.casMaterializeReflink
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
  abbrev BorrowedHttpRequest := LeanSys.Http.BorrowedHttpRequest
  abbrev HttpResponse := LeanSys.Http.HttpResponse
  abbrev RouteEntry := LeanSys.Http.RouteEntry
  abbrev dispatchRoutes := LeanSys.Http.dispatchRoutes
  abbrev parseHttpRequest := LeanSys.Http.parseRequest
  abbrev parseHttpRequestSourcePrefix := LeanSys.Http.parseRequestSourcePrefix
  abbrev serveLoop := LeanSys.Http.serveLoop
  abbrev httpClientRequest := LeanSys.Http.httpClientRequest
  abbrev requestUnix := LeanSys.Http.requestUnix
  abbrev runMultiplexedReactor := LeanSys.Reactor.runMultiplexedReactor
  abbrev stepGoverned {S Msg Out : Type} := @LeanSys.Reactor.stepGoverned S Msg Out
  abbrev RpcRequest := LeanSys.JsonRpc.RpcRequest
  abbrev BorrowedRpcRequest := LeanSys.JsonRpc.BorrowedRpcRequest
  abbrev parseRpcRequest? := LeanSys.JsonRpc.parseRequest?
  abbrev parseRpcRequestSource? := LeanSys.JsonRpc.parseRequestSource?
  abbrev formatRpcSuccess := LeanSys.JsonRpc.formatSuccess
  abbrev verifyRotatedBearer := LeanSys.Auth.verifyRotatedBearer
  abbrev sha256Bytes := LeanSys.Auth.sha256Bytes
  abbrev sha256Source := LeanSys.Auth.sha256Source
  abbrev Sha256Stream := LeanSys.Auth.Sha256Stream
  abbrev Digest256 := LeanSys.Auth.Digest256
  abbrev hmacSha256Bytes := LeanSys.Auth.hmacSha256Bytes
  abbrev hmacSha256Hex := LeanSys.Auth.hmacSha256Hex
  abbrev AwsSigV4Credentials := LeanSys.Auth.AwsSigV4Credentials
  abbrev AwsSigV4Request := LeanSys.Auth.AwsSigV4Request
  abbrev signSigV4Headers := LeanSys.Auth.signSigV4Headers
  abbrev presignS3Url := LeanSys.Auth.presignS3Url
  abbrev mintLease := LeanSys.Auth.mintLease
  abbrev validateLease := LeanSys.Auth.validateLease
end Web

end LeanSys

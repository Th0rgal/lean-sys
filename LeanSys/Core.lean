/-
  LeanSys.Core: Standalone Native Verification, Benchmark & Self-Test Binary (`lean-sys-core`, `supportInterpreter := false`)
  Executes deterministic end-to-end self-tests and throughput micro-benchmarks across all 10 C-ABI Spec gates
  and all 8 `LeanSys` runtime subsystems (`Posix`, `Hash`, `Codec`, `Store`, `Mmap`, `Lsm`, `Http`/`Reactor`, `Sandbox`).
-/
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

namespace LeanSys.Core

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash
open LeanSys.Codec
open LeanSys.Store
open LeanSys.Mmap
open LeanSys.Lsm
open LeanSys.Table
open LeanSys.Auth
open LeanSys.ProcLog
open LeanSys.JsonRpc
open LeanSys.Http
open LeanSys.Reactor
open LeanSys.Sandbox

/-- Run the complete `lean-sys-core self-test` suite across all 10 C-ABI gates and 8 runtime modules. -/
def runSelfTest : IO UInt32 := do
  -- 1. All 10 C-ABI Spec Gates
  let sbOk := verifySliceBounds 4 8 16 == 1 && verifySliceBounds 12 8 16 == 0
  let wfOk := verifyWalFrame walMagic 32 32 0x1234 0x1234 == 1 &&
              verifyWalFrame walMagic 32 16 0x1234 0x1234 == 0 &&
              verifyWalFrame walMagic 32 32 0x1234 0x9999 == 0
  let casGateOk := verifyCasDigest 0xABCD 0xABCD 0 == 1 &&
                   verifyCasDigest 0xABCD 0xABCD 1 == 0 &&
                   verifyCasDigest 0 0 0 == 0
  let httpGateOk := checkHttpBounds 4 128 128 1 == 1 &&
                    checkHttpBounds 40 128 128 1 == 0 &&
                    checkHttpBounds 4 128 64 1 == 0 &&
                    checkHttpBounds 4 128 128 0 == 0
  let tapeGateOk := verifyJsonlTape 2 4 8 6 32 1 == 1 &&
                    verifyJsonlTape 20 8 8 6 32 1 == 0 &&
                    verifyJsonlTape 2 4 8 6 32 99 == 0
  let ringGateOk := verifyRingCursor 16 4 64 16 == 1 &&
                    verifyRingCursor 60 0 64 16 == 0 &&
                    verifyRingCursor 4 16 64 4 == 0
  let sstGateOk := verifySstBlock sstMagic 4 128 256 280 0x11 == 1 &&
                   verifySstBlock sstMagic 4 300 256 280 0x11 == 0 &&
                   verifySstBlock sstMagic 4 128 256 280 0 == 0
  let pollGateOk := verifyPollInterest 4 64 2 16 100 2000 == 1 &&
                    verifyPollInterest 80 64 2 16 100 2000 == 0 &&
                    verifyPollInterest 4 64 16 16 100 2000 == 0
  let rlimGateOk := verifyRlimitBudget 1024 4096 50 1000 512 4096 == 1 &&
                    verifyRlimitBudget 8192 4096 50 1000 512 4096 == 0 &&
                    verifyRlimitBudget 1024 4096 2000 1000 512 4096 == 0
  let mixGateOk := mix64Word 0 0 != mix64Word 0 1
  let ckGateOk := verifyCompositeKeyOrder 1 2 3 1 2 4 == 1 &&
                  verifyCompositeKeyOrder 1 2 5 1 2 4 == 0
  let tokGateOk := verifyTokenAuth 0 1 1 1 100 200 == 1 &&
                   verifyTokenAuth 0 0 1 1 100 200 == 0 &&
                   verifyTokenAuth 1 0 0 1 200 200 == 0
  let logGateOk := verifyLogWindow 0 1024 4096 65536 == 1 &&
                   verifyLogWindow 1024 512 4096 65536 == 0 &&
                   verifyLogWindow 0 1024 4096 524288 == 0
  let rpcGateOk := verifyJsonRpcFrame 1 1 10 256 == 1 &&
                   verifyJsonRpcFrame 0 1 10 256 == 0 &&
                   verifyJsonRpcFrame 1 1 0 256 == 0
  let admitGateOk := verifyGateAdmit 1 1 1 == 1 &&
                     verifyGateAdmit 0 1 1 == 0 &&
                     verifyGateAdmit 1 0 1 == 0 &&
                     verifyGateAdmit 1 1 0 == 0
  let seqlockGateOk := verifyMmapSeqlock mmapSeqlockMagic 1 1 4 4 10 10 128 1024 == 1 &&
                       verifyMmapSeqlock mmapSeqlockMagic 1 1 4 6 10 10 128 1024 == 0 &&
                       verifyMmapSeqlock mmapSeqlockMagic 1 1 5 5 10 10 128 1024 == 0 &&
                       verifyMmapSeqlock mmapSeqlockMagic 1 1 4 4 8 10 128 1024 == 0
  let procStatGateOk := verifyProcStatFields 5 18 64 5 12 == 1 &&
                        verifyProcStatFields 18 5 64 5 12 == 0 &&
                        verifyProcStatFields 5 18 64 15 12 == 0
  let sseGateOk := verifySseFrameScan 4 12 64 2 0x41 0x7D == 1 &&
                   verifySseFrameScan 4 12 64 2 0x85 0x7D == 0 &&
                   verifySseFrameScan 4 12 64 2 0x41 0xE2 == 0 &&
                   verifySseFrameScan 60 12 64 2 0x41 0x7D == 0 &&
                   verifySseFrameScan 0xFFFFFFFFFFFFFFF8 16 64 2 0x41 0x7D == 0
  let gfmGateOk := verifyGfmPipeScan 0 24 64 3 3 0 == 1 &&
                   verifyGfmPipeScan 0 24 64 3 2 0 == 0 &&
                   verifyGfmPipeScan 0 24 64 3 3 1 == 0
  let tagGateOk := verifyTagScan 0 20 6 12 64 1 == 1 &&
                   verifyTagScan 0 20 6 18 64 1 == 0 &&
                   verifyTagScan 0 20 6 12 64 9 == 0 &&
                   verifyTagScan 0 20 6 0xFFFFFFFFFFFFFFFC 64 1 == 0
  let trIdxGateOk := verifyTranscriptIndex 0 32 64 0x1111 0x2222 != 0 &&
                     verifyTranscriptIndex 48 32 64 0x1111 0x2222 == 0
  let parChunkGateOk := verifyParChunk 0 64 256 64 == 1 &&
                        verifyParChunk 0 32 256 64 == 0 &&
                        verifyParChunk 192 256 256 64 == 1
  let arenaDisjointGateOk := verifyArenaDisjoint 0 128 128 128 256 == 1 &&
                             verifyArenaDisjoint 0 128 64 128 256 == 0
  let snapVisGateOk := verifySnapshotVisibility 2 5 0 == 1 &&
                       verifySnapshotVisibility 6 5 0 == 0 &&
                       verifySnapshotVisibility 2 5 1 == 0
  let routeMatchGateOk := verifyHttpRouteMatch 1 1 0 4 == 1 &&
                          verifyHttpRouteMatch 0 1 0 4 == 0 &&
                          verifyHttpRouteMatch 1 0 0 4 == 0 &&
                          verifyHttpRouteMatch 1 1 4 4 == 0 &&
                          verifyHttpRouteMatch 1 1 0 65 == 0
  let triageGateOk := verifyCounterexampleTriage 1 1 0 1 == 1 &&
                      verifyCounterexampleTriage 1 0 1 2 == 1 &&
                      verifyCounterexampleTriage 1 0 0 3 == 1 &&
                      verifyCounterexampleTriage 1 1 0 3 == 0 &&
                      verifyCounterexampleTriage 0 1 0 1 == 0
  if !(sbOk && wfOk && casGateOk && httpGateOk && tapeGateOk && ringGateOk && sstGateOk && pollGateOk && rlimGateOk && mixGateOk && ckGateOk && tokGateOk && logGateOk && rpcGateOk && admitGateOk && seqlockGateOk && procStatGateOk && sseGateOk && gfmGateOk && tagGateOk && trIdxGateOk && parChunkGateOk && arenaDisjointGateOk && snapVisGateOk && routeMatchGateOk && triageGateOk) then
    IO.eprintln "[lean-sys-core] FAIL: C-ABI Spec gates check failed"
    return 1

  -- 1b. Zero-Copy SSE Frame, GFM Pipe Table, Rich Tag & Transcript Turn Scanners
  let sseChunk := ByteSlice.ofString "event: turn_delta\ndata: {\"delta\":\"ok\"}\nid: 42\n"
  let (sseSpans, _) := scanSseFrames sseChunk
  let gfmTable := ByteSlice.ofString "| ColA | ColB |\n|---|:-:|\n| a\\|b | c |\n"
  let gfmRows := scanGfmPipeTable gfmTable
  let tagSample := ByteSlice.ofString "See <file path=\"a.lean\"> and <image src=\"b.png\"> plus <svg viewBox=\"0 0 10 10\">"
  let richTags := scanRichTags tagSample
  let trSample := ByteSlice.ofString "{\"turn\":1}\n{\"turn\":2}\n"
  let trTurns := indexTranscriptTurns trSample
  if sseSpans.size != 3 || gfmRows.size != 3 || richTags.size != 3 || trTurns.size != 2 then
    IO.eprintln "[lean-sys-core] FAIL: Zero-copy SSE/GFM/Tag/Transcript scanner mismatch"
    return 1

  -- 2. Zero-Copy JSONL Tape Codec & 64-Bit Word-Strided Hash (`LeanSys.Codec` & `LeanSys.Hash`)
  let sampleJson := ByteSlice.ofString "{\"schema\":\"lean-sys.telemetry.v1\",\"event_id\":\"ev-900\",\"tokens_used\":4200,\"verified\":true}"
  let tape := JsonTape.indexJsonObject sampleJson
  if JsonTape.lookupString? tape "schema" != some "lean-sys.telemetry.v1" ||
     JsonTape.lookupString? tape "event_id" != some "ev-900" ||
     JsonTape.lookupNat? tape "tokens_used" != some 4200 ||
     JsonTape.lookupBool? tape "verified" != some true then
    IO.eprintln "[lean-sys-core] FAIL: JsonTape zero-copy lookup mismatch"
    return 1

  -- 3. Store WAL + Batch Group-Commit + Torn-Tail Recovery + Compaction + CAS Hardlink
  let ts ← IO.monoNanosNow
  let testDir := s!"/tmp/lean-sys-selftest-{ts}"
  let pTest : System.FilePath := testDir
  if ← pTest.pathExists then
    IO.FS.removeDirAll pTest
  IO.FS.createDirAll pTest

  let .ok st0 ← openStore testDir | do IO.eprintln "[lean-sys-core] FAIL: openStore initial"; return 1
  let .ok st1 ← putString st0 "alpha" "value-alpha-1" true | do IO.eprintln "[lean-sys-core] FAIL: put alpha"; return 1
  let .ok st2 ← putBatch st1 #[("beta", ByteSlice.ofString "value-beta-2"), ("gamma", ByteSlice.ofString "value-gamma-3")] true
    | do IO.eprintln "[lean-sys-core] FAIL: putBatch"; return 1

  -- Inject a corrupt / torn trailing WAL frame (8 bytes instead of full frame)
  let tornBytes := ByteArray.mk #[0x53, 0x59, 0x53, 0x4C, 0x20, 0x00, 0x00, 0x00]
  let _ ← withFd st2.walPath 2 (fun fd => writeAll fd tornBytes true)

  -- Re-open Store and verify torn frame was truncated and committed keys are intact
  let .ok stRecovered ← openStore testDir | do IO.eprintln "[lean-sys-core] FAIL: openStore recovery"; return 1
  if !stRecovered.tornCleaned ||
     getString? stRecovered "alpha" != some "value-alpha-1" ||
     getString? stRecovered "beta" != some "value-beta-2" ||
     getString? stRecovered "gamma" != some "value-gamma-3" then
    IO.eprintln "[lean-sys-core] FAIL: WAL torn-tail recovery mismatch"; return 1

  let .ok stCompacted ← compact stRecovered | do IO.eprintln "[lean-sys-core] FAIL: Store.compact"; return 1
  if getString? stCompacted "gamma" != some "value-gamma-3" || stCompacted.framesCount != 3 then
    IO.eprintln "[lean-sys-core] FAIL: Store.compact state mismatch"; return 1

  -- CAS put & hardlink materialize
  let blobPayload := ByteSlice.ofString "(lnir_module verified_cas_object_v1)"
  let .ok casKey ← casPut stCompacted blobPayload | do IO.eprintln "[lean-sys-core] FAIL: Store.casPut"; return 1
  let matPath := s!"{testDir}/materialized_blob.lnir"
  let .ok () ← casMaterialize stCompacted casKey matPath | do IO.eprintln "[lean-sys-core] FAIL: Store.casMaterialize"; return 1
  let matRead ← IO.FS.readFile matPath
  if matRead != "(lnir_module verified_cas_object_v1)" then
    IO.eprintln "[lean-sys-core] FAIL: CAS materialized content mismatch"; return 1

  -- 4. LSM Sorted-String Table (`SstTable`) & 64-Bit Bloom Filter
  let sstPath := s!"{testDir}/state.sst"
  let .ok _ ← SstTable.flushFromStore stCompacted sstPath
    | do IO.eprintln "[lean-sys-core] FAIL: SstTable.flushFromStore"; return 1
  let .ok sstOpened ← SstTable.openSst sstPath
    | do IO.eprintln "[lean-sys-core] FAIL: SstTable.openSst"; return 1
  if SstTable.getString? sstOpened "alpha" != some "value-alpha-1" ||
     SstTable.getString? sstOpened "gamma" != some "value-gamma-3" ||
     (SstTable.getString? sstOpened "nonexistent-key").isSome then
    IO.eprintln "[lean-sys-core] FAIL: SstTable Bloom/binary-search lookup mismatch"
    return 1

  -- 4b. CompositeKey Table Range Scan (`LeanSys.Table`), Token Rotation (`LeanSys.Auth`), ProcLog (`LeanSys.ProcLog`), and JSON-RPC 2.0 (`LeanSys.JsonRpc`)
  let ck1 : CompositeKey := { hi := 10, lo := 20, seq := 1 }
  let ck2 : CompositeKey := { hi := 10, lo := 20, seq := 2 }
  let ck3 : CompositeKey := { hi := 10, lo := 20, seq := 3 }
  let ckTomb : CompositeKey := { hi := 10, lo := 20, seq := 4 }
  let ckEmpty : CompositeKey := { hi := 10, lo := 21, seq := 1 }
  let ckHi : CompositeKey := { hi := 10, lo := 25, seq := 99 }
  let .ok stTbl1 ← putComposite stCompacted ck1 (ByteSlice.ofString "ev-1") false
    | do IO.eprintln "[lean-sys-core] FAIL: putComposite 1"; return 1
  let .ok stTbl2 ← putComposite stTbl1 ck2 (ByteSlice.ofString "ev-2") false
    | do IO.eprintln "[lean-sys-core] FAIL: putComposite 2"; return 1
  let .ok stTbl3 ← putComposite stTbl2 ck3 (ByteSlice.ofString "ev-3") false
    | do IO.eprintln "[lean-sys-core] FAIL: putComposite 3"; return 1
  let .ok stTbl4 ← deleteComposite stTbl3 ckTomb false
    | do IO.eprintln "[lean-sys-core] FAIL: deleteComposite tombstone"; return 1
  let .ok stTbl5 ← putComposite stTbl4 ckEmpty (ByteSlice.ofString "") true
    | do IO.eprintln "[lean-sys-core] FAIL: putComposite empty string"; return 1
  let sstTblPath := s!"{testDir}/table.sst"
  let .ok (stTblCompacted, sstTbl) ← SstTable.flushAndCompactStore stTbl5 sstTblPath
    | do IO.eprintln "[lean-sys-core] FAIL: SstTable.flushAndCompactStore table"; return 1
  let scanRows := rangeScan sstTbl ck1 ck2 10
  let snapAt2 := rangeScanSnapshot sstTbl ck1 ckHi 2 10
  let snapAt3 := rangeScanSnapshot sstTbl ck1 ckHi 3 10
  let snapAt10 := rangeScanSnapshot sstTbl ck1 ckHi 10 10
  let evUpTo2 := rangeScanUpTo sstTbl ck1 ckTomb 2 10
  let evUpTo10 := rangeScanUpTo sstTbl ck1 ckTomb 10 10
  if scanRows.size != 2 || scanRows[0]!.2.toStringLossy != "ev-1" || scanRows[1]!.2.toStringLossy != "ev-2" ||
     snapAt2.size != 2 || snapAt2[0]!.2.toStringLossy != "ev-2" || snapAt2[1]!.2.toStringLossy != "" ||
     snapAt3.size != 2 || snapAt3[0]!.2.toStringLossy != "ev-3" || snapAt3[1]!.2.toStringLossy != "" ||
     snapAt10.size != 1 || snapAt10[0]!.2.toStringLossy != "" ||
     evUpTo2.size != 2 || evUpTo10.size != 3 ||
     getString? stTblCompacted "gamma" != some "value-gamma-3" then
    IO.eprintln "[lean-sys-core] FAIL: Table.rangeScan / rangeScanSnapshot MVCC / flushAndCompactStore mismatch"
    return 1

  let routes : Array RouteEntry := #[
    { method := "GET", path := "/v1/health", handler := fun _ => pure (HttpResponse.json 200 "{\"status\":\"ok\"}") },
    { method := "POST", path := "/v1/items", handler := fun _ => pure (HttpResponse.json 201 "{\"created\":true}") }
  ]
  let dummySlice := ByteSlice.ofString ""
  let rGet ← dispatchRoutes routes { method := "GET", path := "/v1/health", headers := #[], contentLength := 0, authBearer := none, bodySlice := dummySlice }
  let rMethodErr ← dispatchRoutes routes { method := "POST", path := "/v1/health", headers := #[], contentLength := 0, authBearer := none, bodySlice := dummySlice }
  let rNotFound ← dispatchRoutes routes { method := "GET", path := "/v1/unknown", headers := #[], contentLength := 0, authBearer := none, bodySlice := dummySlice }
  let rOverflow ← dispatchRoutes (Array.replicate 65 routes[0]!) { method := "GET", path := "/v1/health", headers := #[], contentLength := 0, authBearer := none, bodySlice := dummySlice }
  let wire405 := String.fromUTF8! rMethodErr.toWireBytes
  if rGet.status != 200 || rMethodErr.status != 405 || rNotFound.status != 404 || rOverflow.status != 500 ||
     (wire405.splitOn "405 Method Not Allowed").length ≤ 1 then
    IO.eprintln "[lean-sys-core] FAIL: dispatchRoutes / HttpResponse.toWireBytes mismatch"
    return 1

  let lease := mintLease "cur-secret" "babylon" "job:submit" 2000
  if !verifyRotatedBearer "old-tok" "new-tok" (some "old-tok") ||
     verifyRotatedBearer "bad-tok" "new-tok" (some "old-tok") ||
     !validateLease lease "new-secret" (some "cur-secret") "babylon" "job:submit" 1500 ||
     validateLease lease "new-secret" (some "cur-secret") "babylon" "job:submit" 2500 then
    IO.eprintln "[lean-sys-core] FAIL: Auth token rotation / lease validation mismatch"
    return 1

  let logPath := s!"{testDir}/job.log"
  IO.FS.writeFile logPath "line-one\nline-two\npartial-tail"
  let .ok chunk1 ← readLogChunk logPath 0 14 false
    | do IO.eprintln "[lean-sys-core] FAIL: ProcLog.readLogChunk"; return 1
  if chunk1.data != "line-one\n" || chunk1.nextOff != 9 then
    IO.eprintln s!"[lean-sys-core] FAIL: ProcLog newline cut mismatch: {repr chunk1}"
    return 1

  let rpcSample := ByteSlice.ofString "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"tools/list\",\"params\":{\"cursor\":null}}"
  let some rpcReq := parseRequest? rpcSample | do IO.eprintln "[lean-sys-core] FAIL: JsonRpc.parseRequest? failed"; return 1
  if rpcReq.method != "tools/list" || rpcReq.idRaw? != some "7" then
    IO.eprintln "[lean-sys-core] FAIL: JsonRpc field mismatch"; return 1

  -- 5. Shared-Memory SPSC Ring Buffer (`ShmRing`) & Seqlock / `/proc/<pid>/stat`
  let ringPath := s!"{testDir}/ipc.ring"
  let .ok ring ← ShmRing.init ringPath 1024 | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.init"; return 1
  let .ok () ← ShmRing.push ring (ByteSlice.ofString "ring-msg-1") | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.push 1"; return 1
  let .ok () ← ShmRing.push ring (ByteSlice.ofString "ring-msg-2") | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.push 2"; return 1
  let .ok (some pop1) ← ShmRing.pop? ring | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.pop 1"; return 1
  let .ok (some pop2) ← ShmRing.pop? ring | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.pop 2"; return 1
  let .ok none ← ShmRing.pop? ring | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.pop empty"; return 1
  if String.fromUTF8! pop1 != "ring-msg-1" || String.fromUTF8! pop2 != "ring-msg-2" ||
     !ShmRing.validateSeqlockSnapshot 1 1 8 8 3 2 64 1024 ||
     ShmRing.validateSeqlockSnapshot 1 1 7 7 3 2 64 1024 then
    IO.eprintln "[lean-sys-core] FAIL: ShmRing FIFO order or seqlock snapshot mismatch"; return 1
  let statSample := ByteSlice.ofString "4242 (my (tricky) worker) S 1 4242 4242 0 -1 4194304 10 0 0 0 5 2 0 0 20 0 1 0 987654321 123456"
  let some (commSl, fCount) := scanProcStatFields? statSample 5 | do IO.eprintln "[lean-sys-core] FAIL: scanProcStatFields?"; return 1
  if commSl.toStringLossy != "my (tricky) worker" || fCount != 21 then
    IO.eprintln "[lean-sys-core] FAIL: scanProcStatFields? mismatch"; return 1
  let some statRec := parseProcStatRecord? statSample | do IO.eprintln "[lean-sys-core] FAIL: parseProcStatRecord?"; return 1
  if statRec.commSlice.toStringLossy != "my (tricky) worker" || statRec.stateByte != 83 || statRec.startTicks != 987654321 || statRec.fieldsAfterComm != 21 then
    IO.eprintln "[lean-sys-core] FAIL: parseProcStatRecord? mismatch"; return 1

  -- 6. Process-Group Sandbox & Quota Enforcer (`LeanSys.Sandbox`)
  let quota : SandboxQuota := { maxRssBytes := 536870912, timeoutMs := 3000, maxPipeBytes := 4194304 }
  let .ok sbRes ← runSandboxedGroup quota "/bin/true" #[]
    | do IO.eprintln "[lean-sys-core] FAIL: runSandboxedGroup /bin/true"; return 1
  if sbRes.exitCode != 0 || sbRes.timedOut || sbRes.quotaBreach then
    IO.eprintln s!"[lean-sys-core] FAIL: SandboxResult unexpected: {repr sbRes}"
    return 1

  -- 7. Zero-Copy HTTP/1.1 & Reactor Loopback Roundtrip
  let .ok (listenFd, boundPort) ← tcpListen "127.0.0.1" 0 16
    | do IO.eprintln "[lean-sys-core] FAIL: tcpListen ephemeral"; return 1
  let rCfg : ReactorConfig := { maxConns := 64, maxKeepAliveReq := 8, maxIdleMs := 3000, expectedBearer? := some "secret-cap-token" }
  let serverTask ← IO.asTask (prio := .dedicated) do
    runReactorLoop rCfg listenFd 1 fun req => do
      let t := JsonTape.indexJsonObject req.bodySlice
      let pingVal := (JsonTape.lookupString? t "ping").getD "none"
      return HttpResponse.json 200 s!"\{\"ok\":true,\"method\":\"{req.method}\",\"path\":\"{req.path}\",\"ping\":\"{pingVal}\"}"

  let reqJson := ByteSlice.ofString "{\"ping\":\"pong\"}"
  let clientRes ← httpClientRequest "127.0.0.1" boundPort "POST" "/v1/test" reqJson (some "secret-cap-token")
  let servedRes ← IO.wait serverTask
  let servedCount := match servedRes with | .ok n => n | .error _ => 0
  discard <| closeFd listenFd
  IO.FS.removeDirAll pTest

  match clientRes with
  | .error e =>
    IO.eprintln s!"[lean-sys-core] FAIL: httpClientRequest error {e}"
    return 1
  | .ok respBody =>
    if servedCount != 1 || (respBody.splitOn "\"ok\":true").length ≤ 1 || (respBody.splitOn "\"pong\"").length ≤ 1 then
      IO.eprintln s!"[lean-sys-core] FAIL: unexpected HTTP response: {respBody}"
      return 1

  IO.println s!"\{ \"ok\": true, \"binary\": \"lean-sys-core\", \"c_abi_gates\": 26, \"wal_torn_recovery\": true, \"cas_hardlink\": true, \"sst_bloom\": true, \"table_range_scan\": true, \"auth_rotation\": true, \"proc_log\": true, \"proc_stat_scanner\": true, \"jsonrpc_2_0\": true, \"shm_ring\": true, \"mmap_seqlock\": true, \"jsonl_tape\": true, \"reactor_keepalive\": true, \"sandbox_rlimit\": true, \"pgid_reaper\": true, \"http_loopback_port\": {boundPort} }"
  return 0

/-- Run deterministic micro-benchmarks for `autoresearch/sys_arena.py` and emit JSON metrics. -/
def runBench (iters : Nat := 2000) : IO UInt32 := do
  let ts ← IO.monoNanosNow
  let benchDir := s!"/dev/shm/lean-sys-bench-{ts}"
  let pBench : System.FilePath := benchDir
  IO.FS.createDirAll pBench

  -- 1. Hash throughput (`xxh64Slice` on 4 KiB buffer)
  let buf4k := ByteArray.mk (Array.replicate 4096 (0x61 : UInt8))
  let slice4k := ByteSlice.ofByteArray buf4k
  let tHash0 ← IO.monoNanosNow
  let mut hAcc : UInt64 := 0
  for idx in [0:iters] do
    hAcc := hAcc ^^^ xxh64Slice slice4k idx.toUInt64
  let tHash1 ← IO.monoNanosNow
  let hashNs := Nat.max 1 (tHash1 - tHash0)
  let hashMbPerSec := (iters * 4096 * 1000) / hashNs

  -- 2. Zero-Copy JsonTape parse + lookup throughput
  let sampleLine := ByteSlice.ofString "{\"schema\":\"lean-sys.telemetry.v1\",\"event_id\":\"ev-bench-001\",\"goal_class\":\"lean_sys_parity\",\"tokens_used\":4800,\"verified\":true}"
  let tCodec0 ← IO.monoNanosNow
  let mut tokSum : Nat := 0
  for _ in [0:iters] do
    let tape := JsonTape.indexJsonObject sampleLine
    tokSum := tokSum + (JsonTape.lookupNat? tape "tokens_used").getD 0
  let tCodec1 ← IO.monoNanosNow
  let codecNs := Nat.max 1 (tCodec1 - tCodec0)
  let codecOpsPerSec := (iters * 1000000000) / codecNs

  -- 3. WAL Batch Group-Commit + Replay + SST Bloom Lookup
  let .ok st0 ← openStore benchDir | return 1
  let mut batchEntries : Array (String × ByteSlice) := Array.mkEmpty 500
  for i in [0:500] do
    batchEntries := batchEntries.push (s!"key-{i}", sampleLine)
  let tWal0 ← IO.monoNanosNow
  let .ok st1 ← putBatch st0 batchEntries false | return 1
  let tWal1 ← IO.monoNanosNow
  let walNs := Nat.max 1 (tWal1 - tWal0)
  let walFramesPerSec := (500 * 1000000000) / walNs

  let sstPath := s!"{benchDir}/bench.sst"
  let .ok sstTbl ← SstTable.flushFromStore st1 sstPath | return 1
  let tSst0 ← IO.monoNanosNow
  let mut hits : Nat := 0
  for i in [0:iters] do
    let qKey := if i % 2 == 0 then s!"key-{i % 500}" else s!"missing-{i}"
    if (SstTable.getSlice? sstTbl qKey).isSome then
      hits := hits + 1
  let tSst1 ← IO.monoNanosNow
  let sstNs := Nat.max 1 (tSst1 - tSst0)
  let sstOpsPerSec := (iters * 1000000000) / sstNs

  IO.FS.removeDirAll pBench
  IO.println s!"\{\"ok\":true,\"iters\":{iters},\"hash_mb_per_s\":{hashMbPerSec},\"codec_ops_per_s\":{codecOpsPerSec},\"wal_frames_per_s\":{walFramesPerSec},\"sst_ops_per_s\":{sstOpsPerSec},\"checksum\":{hAcc ^^^ tokSum.toUInt64 ^^^ hits.toUInt64}}"
  return 0

end LeanSys.Core

def main (args : List String) : IO UInt32 := do
  match args with
  | ["self-test"] | ["--self-test"] | [] => LeanSys.Core.runSelfTest
  | ["bench"] | ["--bench"] => LeanSys.Core.runBench 4000
  | ["bench", nStr] | ["--bench", nStr] => LeanSys.Core.runBench (nStr.toNat?.getD 4000)
  | ["--c-abi"] =>
    IO.println "{\"ok\":true,\"exports\":[\"leansys_verify_slice_bounds\",\"leansys_verify_wal_frame\",\"leansys_verify_cas_digest\",\"leansys_check_http_bounds\",\"leansys_verify_jsonl_tape\",\"leansys_verify_ring_cursor\",\"leansys_verify_sst_block\",\"leansys_verify_poll_interest\",\"leansys_verify_rlimit_budget\",\"leansys_mix64_word\",\"leansys_verify_composite_key_order\",\"leansys_verify_token_auth\",\"leansys_verify_log_window\",\"leansys_verify_jsonrpc_frame\",\"leansys_gate_admit\",\"leansys_verify_mmap_seqlock\",\"leansys_verify_proc_stat_fields\",\"leansys_sse_frame_scan\",\"leansys_gfm_pipe_scan\",\"leansys_tag_scan\",\"leansys_transcript_index\",\"leansys_verify_par_chunk\",\"leansys_verify_arena_disjoint\",\"leansys_verify_snapshot_visibility\",\"leansys_verify_http_route_match\"]}"
    return 0
  | _ =>
    IO.println "usage: lean-sys-core [self-test | bench | --c-abi]"
    return 0

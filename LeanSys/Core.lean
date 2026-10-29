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
import LeanSys.Par

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
open LeanSys.Par

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
  let dagWaveGateOk := verifyDagWaveStep 0 4 8 16 4 4 == 1 &&
                       verifyDagWaveStep 1 4 8 16 4 4 == 0 &&
                       verifyDagWaveStep 0 0 8 16 4 4 == 0 &&
                       verifyDagWaveStep 0 12 8 16 4 4 == 0 &&
                       verifyDagWaveStep 0 4 8 16 6 4 == 0
  let jetsamGateOk := verifyIosJetsamBudget 4194304 65536 134217728 16383 0 == 1 &&
                      verifyIosJetsamBudget 4194304 65536 25165824 16383 1 == 1 &&
                      verifyIosJetsamBudget 4194304 65536 33554432 16383 1 == 0 &&
                      verifyIosJetsamBudget 4194304 65536 134217728 4095 0 == 0 &&
                      verifyIosJetsamBudget 134217728 65536 134217728 16383 0 == 0
  let workerGateOk := verifyWorkerBudget 4 6 24 4096 1 == 1 &&
                      verifyWorkerBudget 4 8 24 4096 1 == 0 &&
                      verifyWorkerBudget 6 9 54 4096 2 == 1 &&
                      verifyWorkerBudget 6 10 54 4096 2 == 0 &&
                      verifyWorkerBudget 4 8 24 4096 0 == 1 &&
                      verifyWorkerBudget 0 6 24 4096 1 == 0
  let pageBufGateOk := verifyPageAlignedBuffer 0x10000 4096 16384 1048576 134217728 16383 == 1 &&
                       verifyPageAlignedBuffer 0x11000 4096 4096 1048576 134217728 4095 == 1 &&
                       verifyPageAlignedBuffer 0x11000 4096 16384 1048576 134217728 16383 == 0 &&
                       verifyPageAlignedBuffer 0 4096 16384 1048576 134217728 16383 == 0 &&
                       verifyPageAlignedBuffer 0x10000 4096 16384 1048576 134217728 8191 == 0
  let isaGateOk := selectIsaVariant IsaLevel.tensorG3.hwcapMask IsaLevel.tensorG3.hwcapMask 3 3 == 3 &&
                   selectIsaVariant IsaLevel.appleA15.hwcapMask IsaLevel.tensorG3.hwcapMask 3 3 == 0 &&
                   selectIsaVariant IsaLevel.tensorG3.hwcapMask 0 3 3 == 0 &&
                   verifyIsaSelection IsaLevel.tensorG3.hwcapMask IsaLevel.tensorG3.hwcapMask 3 3 == 1 &&
                   verifyIsaSelection IsaLevel.appleA15.hwcapMask IsaLevel.tensorG3.hwcapMask 3 3 == 0 &&
                   verifyIsaSelection IsaLevel.tensorG3.hwcapMask 0 3 3 == 0 &&
                   verifyIsaSelection IsaLevel.tensorG3.hwcapMask IsaLevel.arm64Baseline.hwcapMask 3 3 == 0 &&
                   IsaLevel.arm64Baseline.le IsaLevel.appleA15 &&
                   IsaLevel.appleA15.le IsaLevel.appleA16_A17 &&
                   IsaLevel.appleA16_A17.le IsaLevel.tensorG3 &&
                   (IsaLevel.ofLinuxHwcap 0x120502 0x6012).wellFormed &&
                   (IsaLevel.ofLinuxHwcap 0x120502 0x6012).hwcapMask == IsaLevel.tensorG3.hwcapMask &&
                   (WorkerBudget.ofTopology (CoreTopology.uniformSmp 4)).microChunkFactor == 2 &&
                   !(WorkerBudget.ofTopology (CoreTopology.uniformSmp 4)).isMobileHetero &&
                   (WorkerBudget.ofTopology CoreTopology.appleA15).microChunkFactor == 4 &&
                   (WorkerBudget.ofTopology CoreTopology.appleA15).isMobileHetero &&
                   (WorkerBudget.ofTopology CoreTopology.tensorG3).microChunkFactor == 6 &&
                   (WorkerBudget.ofTopology CoreTopology.tensorG3).isMobileHetero
  let fdGateOk := verifyFdBounds 70000 70000 == 1 &&
                  verifyFdBounds 0x7FFFFFFF 0x7FFFFFFF == 1 &&
                  verifyFdBounds 0x80000000 0x80000000 == 0 &&
                  verifyFdBounds 70000 4464 == 0 &&
                  verifyFdBounds 0xFFFFFFFFFFFFFFFF 0xFFFFFFFF == 0
  if !(sbOk && wfOk && casGateOk && httpGateOk && tapeGateOk && ringGateOk && sstGateOk && pollGateOk && rlimGateOk && mixGateOk && ckGateOk && tokGateOk && logGateOk && rpcGateOk && admitGateOk && seqlockGateOk && procStatGateOk && sseGateOk && gfmGateOk && tagGateOk && trIdxGateOk && parChunkGateOk && arenaDisjointGateOk && snapVisGateOk && routeMatchGateOk && triageGateOk && dagWaveGateOk && jetsamGateOk && workerGateOk && pageBufGateOk && isaGateOk && fdGateOk) then
    IO.eprintln "[lean-sys-core] FAIL: C-ABI Spec gates check failed"
    return 1

  -- 1a. Certified Multi-Threaded Chunk, Slice, Micro-Chunk & DAG Wave Scheduler (`LeanSys.Par`)
  let parBuf := ByteArray.mk (Array.replicate 4096 (0x5A : UInt8))
  let parXor := parReduceSlices parBuf 1024 4 (0 : UInt64) (· ^^^ ·) (fun sl => xxh64Slice sl sl.off.toUInt64)
  let seqChunks := partitionRange 4096 1024 4
  let seqXor := seqChunks.foldl (fun acc c =>
    acc ^^^ xxh64Slice { ba := parBuf, off := c.startIdx, len := c.endIdx - c.startIdx } c.startIdx.toUInt64) (0 : UInt64)
  let waveOut ← parMapWave 4 #[10, 20, 30, 40, 50] (fun x => pure (x * 2))
  let microOut ← parMapMicroChunks 4096 (WorkerBudget.ofTopology CoreTopology.appleA15 256)
    (fun c => pure (c.endIdx - c.startIdx))
  let microSum := microOut.foldl (· + ·) 0
  let tensorOut ← parMapMicroChunks 4096 (WorkerBudget.ofTopology CoreTopology.tensorG3 256)
    (fun c => pure (c.endIdx - c.startIdx))
  let tensorSum := tensorOut.foldl (· + ·) 0
  if parXor == 0 || parXor != seqXor || seqChunks.size != 4 || waveOut != #[20, 40, 60, 80, 100] || microSum != 4096 || tensorSum != 4096 then
    IO.eprintln "[lean-sys-core] FAIL: LeanSys.Par multi-threaded reduction or wave order mismatch"
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

  -- 3. Store WAL + Batch Group-Commit + Torn-Tail Recovery + Mid-Log Corruption Fail-Closed + >64 MiB Replay + CAS Immutability
  let ts ← IO.monoNanosNow
  let tmpBase ← match ← IO.getEnv "TMPDIR" with
    | some d => pure (if d.isEmpty then "/tmp" else d)
    | none => pure "/tmp"
  let testDir := s!"{tmpBase}/lean-sys-selftest-{ts}"
  let pTest : System.FilePath := testDir
  if ← pTest.pathExists then
    IO.FS.removeDirAll pTest
  IO.FS.createDirAll pTest

  -- 3a. 32-Bit High File Descriptor (`F_DUPFD_CLOEXEC >= 65536`) I/O & `closeFd` Roundtrip
  let hiFdPath := s!"{testDir}/high_fd_probe.bin"
  let .ok baseFd ← openFd hiFdPath 4 | do IO.eprintln "[lean-sys-core] FAIL: openFd high_fd_probe"; return 1
  let .ok highFd ← dupFdAbove64k baseFd 1 | do
    discard <| closeFd baseFd
    IO.eprintln "[lean-sys-core] FAIL: dupFdAbove64k (>= 65536)"
    return 1
  let .ok () ← closeFd baseFd | do IO.eprintln "[lean-sys-core] FAIL: closeFd baseFd"; return 1
  if highFd.raw < 65536 then
    discard <| closeFd highFd
    IO.eprintln s!"[lean-sys-core] FAIL: highFd < 65536 ({highFd.raw})"
    return 1
  let .ok writtenHi ← writeAll highFd "high-fd-32bit-ok".toUTF8 true
    | do discard <| closeFd highFd; IO.eprintln "[lean-sys-core] FAIL: writeAll on highFd"; return 1
  let readHi ← preadByteArray highFd 0 64
  let .ok () ← closeFd highFd | do IO.eprintln "[lean-sys-core] FAIL: closeFd highFd"; return 1
  -- Verify `highFd` was genuinely closed (`fstatSize` on closed 32-bit FD returns `EBADF`)
  match ← fstatSize highFd with
  | .error .ebadf => pure ()
  | other =>
    IO.eprintln s!"[lean-sys-core] FAIL: closeFd did not close 32-bit highFd ({highFd.raw}), fstat={repr other}"
    return 1
  if writtenHi != 16 || String.fromUTF8! readHi != "high-fd-32bit-ok" then
    IO.eprintln "[lean-sys-core] FAIL: highFd 32-bit read/write payload mismatch"
    return 1

  let .ok st0 ← openStore testDir | do IO.eprintln "[lean-sys-core] FAIL: openStore initial"; return 1
  let .ok st1 ← putString st0 "alpha" "value-alpha-1" true | do IO.eprintln "[lean-sys-core] FAIL: put alpha"; return 1
  let .ok st2 ← putBatch st1 #[("beta", ByteSlice.ofString "value-beta-2"), ("gamma", ByteSlice.ofString "value-gamma-3")] true
    | do IO.eprintln "[lean-sys-core] FAIL: putBatch"; return 1

  -- Inject a partial / torn trailing WAL frame at EOF (8 bytes of valid LSYS magic + payloadLen)
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

  -- 3b. Fail-closed mid-log WAL corruption detection
  let corruptDir := s!"{testDir}/corrupt_wal"
  IO.FS.createDirAll corruptDir
  let .ok stCor0 ← openStore corruptDir | do IO.eprintln "[lean-sys-core] FAIL: openStore corruptDir"; return 1
  let .ok stCor1 ← putString stCor0 "k1" "val-one-valid" false | do return 1
  let .ok stCor2 ← putString stCor1 "k2" "val-two-to-corrupt" false | do return 1
  let .ok stCor3 ← putString stCor2 "k3" "val-three-valid" true | do return 1
  -- Flip a payload byte inside the middle frame (`k2`) without updating checksum
  let walRaw ← IO.FS.readBinFile stCor3.walPath
  let flipIdx := 34
  let corruptedWal := walRaw.set! flipIdx (walRaw.get! flipIdx ^^^ 0xFF)
  IO.FS.writeBinFile stCor3.walPath corruptedWal
  match ← openStore corruptDir with
  | .error .eio => pure ()
  | .ok _ =>
    IO.eprintln "[lean-sys-core] FAIL: openStore accepted mid-log corrupted WAL instead of failing closed"
    return 1
  | .error e =>
    IO.eprintln s!"[lean-sys-core] FAIL: unexpected error on mid-log corrupt WAL: {e}"
    return 1

  -- 3c. Fail-closed premature empty read before `fileSize` (must NEVER misclassify I/O error as EOF torn tail)
  let validWalImage := encodeWalKVFrame "f1" (ByteSlice.ofString "committed-one") ++
    encodeWalKVFrame "f2" (ByteSlice.ofString "committed-two-must-survive")
  let f1Len := (encodeWalKVFrame "f1" (ByteSlice.ofString "committed-one")).size
  let cutInF2 := f1Len + 10
  let prematureRes ← replayWalReader validWalImage.size.toUInt64 (fun off _ => do
    if off == 0 then
      pure (validWalImage.extract 0 cutInF2)
    else
      pure ByteArray.empty) 65536
  match prematureRes with
  | .error .eio => pure ()
  | _ =>
    IO.eprintln "[lean-sys-core] FAIL: replayWalReader did not return EIO on premature empty read before fileSize"
    return 1

  -- 3d. Streaming WAL replay across > 64 MiB log in portable temp dir (`testDir/bigwal`), cleaned up immediately
  let bigWalDir := s!"{testDir}/bigwal"
  IO.FS.createDirAll bigWalDir
  let .ok stBig0 ← openStore bigWalDir | do IO.eprintln "[lean-sys-core] FAIL: openStore bigWalDir"; return 1
  let chunk4m := ByteArray.mk (Array.replicate 4194304 (0x42 : UInt8))
  let mut stBigCur := stBig0
  for idx in [0:17] do
    match ← put stBigCur s!"big-{idx}" (ByteSlice.ofByteArray chunk4m) false with
    | .ok next => stBigCur := next
    | .error e =>
      IO.FS.removeDirAll bigWalDir
      IO.eprintln s!"[lean-sys-core] FAIL: big WAL put {idx}: {e}"
      return 1
  let .ok stBigLast ← putString stBigCur "big-sentinel" "after-68mib-ok" false
    | do IO.FS.removeDirAll bigWalDir; return 1
  let .ok bigWalSz ← statFileSize stBigLast.walPath
    | do IO.FS.removeDirAll bigWalDir; return 1
  let .ok stBigReopened ← openStoreWithChunk bigWalDir 2097152
    | do IO.FS.removeDirAll bigWalDir; IO.eprintln "[lean-sys-core] FAIL: >64 MiB WAL replay failed"; return 1
  IO.FS.removeDirAll bigWalDir
  if bigWalSz ≤ 67108864 || stBigReopened.framesCount != 18 ||
     getString? stBigReopened "big-sentinel" != some "after-68mib-ok" ||
     (get? stBigReopened "big-16").map ByteArray.size != some 4194304 then
    IO.eprintln "[lean-sys-core] FAIL: >64 MiB streaming WAL replay state mismatch"
    return 1

  -- 3e. CAS `0444` immutability & copy-on-materialize isolation
  let blobPayload := ByteSlice.ofString "(lnir_module verified_cas_object_v1)"
  let .ok casKey ← casPut stCompacted blobPayload | do IO.eprintln "[lean-sys-core] FAIL: Store.casPut"; return 1
  let casBlobPath := s!"{stCompacted.casDir}/{casKey}"
  -- Direct write open on sealed CAS blob must be rejected (`EACCES` / `EPERM`) unless running as root (`uid == 0`),
  -- and mutating a materialized target must NEVER mutate the stored CAS blob.
  let matPath := s!"{testDir}/materialized_blob.lnir"
  let .ok () ← casMaterialize stCompacted casKey matPath | do IO.eprintln "[lean-sys-core] FAIL: Store.casMaterialize"; return 1
  let matRead ← IO.FS.readFile matPath
  if matRead != "(lnir_module verified_cas_object_v1)" then
    IO.eprintln "[lean-sys-core] FAIL: CAS materialized content mismatch"; return 1
  -- Mutate the materialized copy in place and verify CAS blob + subsequent `casGet`/`casMaterialize` remain untouched
  IO.FS.writeFile matPath "TAMPERED_BY_CALLER_AFTER_MATERIALIZE"
  let .ok casBytesAfter ← casGet stCompacted casKey
    | do IO.eprintln "[lean-sys-core] FAIL: CAS corrupted when materialized file was modified!"; return 1
  let matPath2 := s!"{testDir}/materialized_blob_clean.lnir"
  let .ok () ← casMaterialize stCompacted casKey matPath2
    | do IO.eprintln "[lean-sys-core] FAIL: second casMaterialize after caller mutation failed"; return 1
  let matRead2 ← IO.FS.readFile matPath2
  let casRawOnDisk ← IO.FS.readFile casBlobPath
  if String.fromUTF8! casBytesAfter != "(lnir_module verified_cas_object_v1)" ||
     matRead2 != "(lnir_module verified_cas_object_v1)" ||
     casRawOnDisk != "(lnir_module verified_cas_object_v1)" then
    IO.eprintln "[lean-sys-core] FAIL: CAS immutability / isolation invariant violated"; return 1

  -- 4. LSM Sorted-String Table (`SstTable`) & 64-Bit Bloom Filter
  let sstPath := s!"{testDir}/state.sst"
  let .ok _ ← SstTable.flushFromStore stCompacted sstPath
    | do IO.eprintln "[lean-sys-core] FAIL: SstTable.flushFromStore"; return 1
  let .ok sstOpened ← SstTable.openSst sstPath
    | do IO.eprintln "[lean-sys-core] FAIL: SstTable.openSst"; return 1
  let .ok sstLazy ← SstTable.openSstLazy sstPath
    | do IO.eprintln "[lean-sys-core] FAIL: SstTable.openSstLazy"; return 1
  let lazyAlpha ← SstTable.getLazyIO? sstLazy "alpha"
  let lazyGamma ← SstTable.getLazyIO? sstLazy "gamma"
  let lazyMiss ← SstTable.getLazyIO? sstLazy "nonexistent-key"
  if SstTable.getString? sstOpened "alpha" != some "value-alpha-1" ||
     SstTable.getString? sstOpened "gamma" != some "value-gamma-3" ||
     lazyAlpha.map String.fromUTF8! != some "value-alpha-1" ||
     lazyGamma.map String.fromUTF8! != some "value-gamma-3" ||
     lazyMiss.isSome ||
     sstLazy.rawBuf.size != 0 ||
     sstLazy.entries != sstOpened.entries ||
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
  let forgedLease := { lease with macHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  if !verifyRfc4231Vectors ||
     !verifyRotatedBearer "old-tok" "new-tok" (some "old-tok") ||
     verifyRotatedBearer "bad-tok" "new-tok" (some "old-tok") ||
     !validateLease lease "new-secret" (some "cur-secret") "babylon" "job:submit" 1500 ||
     validateLease forgedLease "cur-secret" none "babylon" "job:submit" 1500 ||
     validateLease lease "wrong-secret" none "babylon" "job:submit" 1500 ||
     validateLease lease "new-secret" (some "cur-secret") "babylon" "job:submit" 2500 then
    IO.eprintln "[lean-sys-core] FAIL: Auth RFC 4231 HMAC-SHA256 / token rotation / lease validation mismatch"
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

  -- 5. Shared-Memory `MAP_SHARED` Circular Ring (`ShmRing.init` + non-truncating `ShmRing.open`) & Seqlock / `/proc/<pid>/stat`
  -- Verify empty (0-byte), undersized header (12-byte), and truncated payload (32-byte for cap=128) backing files return `.error .einval` without raising `SIGBUS`
  let emptyRingPath := s!"{testDir}/empty_ipc.ring"
  IO.FS.writeBinFile emptyRingPath ByteArray.empty
  let shortRingPath := s!"{testDir}/short_ipc.ring"
  IO.FS.writeBinFile shortRingPath (ByteArray.mk (Array.replicate 12 0))
  let truncPayloadRingPath := s!"{testDir}/trunc_payload_ipc.ring"
  let .ok truncRing ← ShmRing.init truncPayloadRingPath 128 | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.init trunc_payload"; return 1
  let .ok () ← ShmRing.push truncRing (ByteSlice.ofString "before-truncate") | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.push trunc_payload"; return 1
  -- Truncate file to 32 bytes (24-byte valid LRNG header + only 8 bytes of the 128-byte payload arena)
  let .ok () ← withFd truncPayloadRingPath 5 (fun fd => ftruncateFd fd 32)
    | do IO.eprintln "[lean-sys-core] FAIL: ftruncate trunc_payload"; return 1
  let emptyOpenRes ← ShmRing.openExisting emptyRingPath
  let emptyReadHdrRes ← ShmRing.readHeader { path := emptyRingPath, lockPath := emptyRingPath ++ ".lock", cap := 64 }
  let shortOpenRes ← ShmRing.openExisting shortRingPath
  let truncOpenRes ← ShmRing.openExisting truncPayloadRingPath
  let truncPopRes ← ShmRing.pop? truncRing
  let truncPushRes ← ShmRing.push truncRing (ByteSlice.ofString "after-truncate")
  match emptyOpenRes, emptyReadHdrRes, shortOpenRes, truncOpenRes, truncPopRes, truncPushRes with
  | .error .einval, .error .einval, .error .einval, .error .einval, .error .einval, .error .einval => pure ()
  | _, _, _, _, _, _ =>
    IO.eprintln "[lean-sys-core] FAIL: ShmRing empty/short/truncated backing file did not fail closed with EINVAL"
    return 1
  let ringPath := s!"{testDir}/ipc.ring"
  let .ok ring ← ShmRing.init ringPath 128 | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.init"; return 1
  let .ok () ← ShmRing.push ring (ByteSlice.ofString "ring-msg-1") | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.push 1"; return 1
  -- Attach a second independent handle via non-truncating `ShmRing.open` and verify unread messages survive!
  let .ok ring2 ← ShmRing.open ringPath | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.open existing"; return 1
  let .ok () ← ShmRing.push ring2 (ByteSlice.ofString "ring-msg-2-from-handle2") | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.push 2"; return 1
  let .ok (some pop1) ← ShmRing.pop? ring2 | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.pop 1"; return 1
  let .ok (some pop2) ← ShmRing.pop? ring | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.pop 2"; return 1
  -- Exercise circular wrap-around past `cap = 128` via `MAP_SHARED` `mmap` without resizing file
  let mut wrapOk := true
  for wi in [0:12] do
    let msgStr := s!"wrap-payload-{wi}-0123456789abcdef"
    match ← ShmRing.push ring (ByteSlice.ofString msgStr) with
    | .error _ => wrapOk := false
    | .ok () =>
      match ← ShmRing.pop? ring2 with
      | .ok (some popped) =>
        if String.fromUTF8! popped != msgStr then wrapOk := false
      | _ => wrapOk := false
  let .ok ringFileSz ← statFileSize ringPath | do return 1
  let .ok none ← ShmRing.pop? ring | do IO.eprintln "[lean-sys-core] FAIL: ShmRing.pop empty"; return 1
  if !wrapOk || ringFileSz != (24 + 128) ||
     String.fromUTF8! pop1 != "ring-msg-1" || String.fromUTF8! pop2 != "ring-msg-2-from-handle2" ||
     !ShmRing.validateSeqlockSnapshot 1 1 8 8 3 2 64 1024 ||
     ShmRing.validateSeqlockSnapshot 1 1 7 7 3 2 64 1024 then
    IO.eprintln "[lean-sys-core] FAIL: ShmRing MAP_SHARED open/wrap/FIFO order or seqlock snapshot mismatch"; return 1
  let statSample := ByteSlice.ofString "4242 (my (tricky) worker) S 1 4242 4242 0 -1 4194304 10 0 0 0 5 2 0 0 20 0 1 0 987654321 123456"
  let some (commSl, fCount) := scanProcStatFields? statSample 5 | do IO.eprintln "[lean-sys-core] FAIL: scanProcStatFields?"; return 1
  if commSl.toStringLossy != "my (tricky) worker" || fCount != 21 then
    IO.eprintln "[lean-sys-core] FAIL: scanProcStatFields? mismatch"; return 1
  let some statRec := parseProcStatRecord? statSample | do IO.eprintln "[lean-sys-core] FAIL: parseProcStatRecord?"; return 1
  if statRec.commSlice.toStringLossy != "my (tricky) worker" || statRec.stateByte != 83 || statRec.startTicks != 987654321 || statRec.fieldsAfterComm != 21 then
    IO.eprintln "[lean-sys-core] FAIL: parseProcStatRecord? mismatch"; return 1

  -- 6. Process-Group Sandbox & Honest Linux Landlock Confinement (`LeanSys.Sandbox`)
  let quota : SandboxQuota := { maxRssBytes := 536870912, timeoutMs := 3000, maxPipeBytes := 4194304 }
  let .ok sbRes ← runSandboxedGroup quota "/bin/true" #[]
    | do IO.eprintln "[lean-sys-core] FAIL: runSandboxedGroup /bin/true"; return 1
  if sbRes.exitCode != 0 || sbRes.timedOut || sbRes.quotaBreach || sbRes.landlockEnforced then
    IO.eprintln s!"[lean-sys-core] FAIL: SandboxResult unexpected: {repr sbRes}"
    return 1
  -- Verify ordinary argv starting with ASCII 31 (`0x1F`) is passed verbatim to `execve` without C-shim stripping
  let unitSepArg := String.fromUTF8! (ByteArray.mk #[31] ++ "verbatim-arg0".toUTF8)
  let argvCheckOut := s!"{testDir}/argv_byte31.txt"
  let .ok sbArgvRes ← runSandboxedGroup quota "/bin/sh" #[
      "-c", s!"printf '%s|%s' \"$0\" \"$1\" > {argvCheckOut}", unitSepArg, "second-arg"
    ]
    | do IO.eprintln "[lean-sys-core] FAIL: runSandboxedGroup byte-31 argv check"; return 1
  let argvRecorded ← IO.FS.readFile argvCheckOut
  if sbArgvRes.exitCode != 0 || argvRecorded != s!"{unitSepArg}|second-arg" then
    IO.eprintln s!"[lean-sys-core] FAIL: byte-31 argv was altered or stripped: {repr argvRecorded}"
    return 1
  let llRoDir := s!"{testDir}/ll_ro"
  let llRwDir := s!"{testDir}/ll_rw"
  let llDeniedDir := s!"{testDir}/ll_denied"
  IO.FS.createDirAll llRoDir
  IO.FS.createDirAll llRwDir
  IO.FS.createDirAll llDeniedDir
  IO.FS.writeFile s!"{llRoDir}/in.txt" "landlock-ro-ok"
  IO.FS.writeFile s!"{llDeniedDir}/secret.txt" "forbidden"
  let llPolicy : LandlockPolicy := { readOnlyPath := llRoDir, readWritePath := llRwDir }
  let landlockHonestOk ← match ← queryLandlockAbi with
    | .error .eopnotsupp =>
      -- On non-Landlock kernels/OSes, `runLandlockedGroup` MUST fail closed with `.error .eopnotsupp`
      match ← runLandlockedGroup quota llPolicy "/bin/true" #[] with
      | .error .eopnotsupp => pure true
      | _ => pure false
    | .error _ => pure false
    | .ok abiVer =>
      if abiVer < 1 then pure false
      else
        -- 1) Allowed: read from `llRoDir` and write to `llRwDir`
        let allowedCmd := s!"cat {llRoDir}/in.txt > {llRwDir}/out.txt"
        let rAllow ← runLandlockedGroup quota llPolicy "/bin/sh" #["-c", allowedCmd]
        -- 2) Blocked by kernel Landlock: reading `llDeniedDir/secret.txt` must fail (`exitCode != 0`)
        let rDenyRead ← runLandlockedGroup quota llPolicy "/bin/sh" #["-c", s!"exec 2>{llRwDir}/err1.log; cat {llDeniedDir}/secret.txt >{llRwDir}/leak.txt"]
        -- 3) Blocked by kernel Landlock: writing into `llRoDir` must fail (`exitCode != 0`)
        let rDenyWrite ← runLandlockedGroup quota llPolicy "/bin/sh" #["-c", s!"exec 2>{llRwDir}/err2.log; echo pwn > {llRoDir}/pwn.txt"]
        match rAllow, rDenyRead, rDenyWrite with
        | .ok resA, .ok resDR, .ok resDW =>
          let copied ← IO.FS.readFile s!"{llRwDir}/out.txt"
          let pwnExists ← (System.FilePath.mk s!"{llRoDir}/pwn.txt").pathExists
          pure (resA.exitCode == 0 && resA.landlockEnforced && copied == "landlock-ro-ok" &&
                resDR.exitCode != 0 && resDW.exitCode != 0 && !pwnExists)
        | _, _, _ => pure false
  if !landlockHonestOk then
    IO.eprintln "[lean-sys-core] FAIL: Linux Landlock kernel enforcement / fail-closed check failed"
    return 1

  -- 7. Smuggling-Safe HTTP/1.1 Parser, Fragmented Socket Reads & Pipelined Keep-Alive Reactor Roundtrip
  let smuggleTe := "POST /v1/test HTTP/1.1\r\nHost: localhost\r\nContent-Length: 4\r\nTransfer-Encoding: chunked\r\n\r\ntest".toUTF8
  let smuggleDupCl := "POST /v1/test HTTP/1.1\r\nHost: localhost\r\nContent-Length: 4\r\nContent-Length: 8\r\n\r\ntest".toUTF8
  let smuggleNegCl := "POST /v1/test HTTP/1.1\r\nHost: localhost\r\nContent-Length: -1\r\n\r\n".toUTF8
  if (parseRequest smuggleTe).isOk || (parseRequest smuggleDupCl).isOk || (parseRequest smuggleNegCl).isOk then
    IO.eprintln "[lean-sys-core] FAIL: HTTP smuggling / conflicting or negative Content-Length was not rejected"
    return 1

  let .ok (listenFd, boundPort) ← tcpListen "127.0.0.1" 0 16
    | do IO.eprintln "[lean-sys-core] FAIL: tcpListen ephemeral"; return 1
  let rCfg : ReactorConfig := { maxConns := 64, maxKeepAliveReq := 8, maxIdleMs := 3000, expectedBearer? := some "secret-cap-token" }
  let serverTask ← IO.asTask (prio := .dedicated) do
    runReactorLoop rCfg listenFd 2 fun req => do
      let t := JsonTape.indexJsonObject req.bodySlice
      let pingVal := (JsonTape.lookupString? t "ping").getD "none"
      return HttpResponse.json 200 s!"\{\"ok\":true,\"method\":\"{req.method}\",\"path\":\"{req.path}\",\"ping\":\"{pingVal}\"}"

  -- Session 1: Standard `httpClientRequest` (`Connection: close`)
  let reqJson := ByteSlice.ofString "{\"ping\":\"pong\"}"
  let clientRes ← httpClientRequest "127.0.0.1" boundPort "POST" "/v1/test" reqJson (some "secret-cap-token")

  -- Session 2: Fragmented header/body writes + pipelined second request on the same keep-alive TCP socket
  let .ok fragFd ← tcpConnect "127.0.0.1" boundPort
    | do IO.eprintln "[lean-sys-core] FAIL: tcpConnect fragmented session"; return 1
  let body1 := "{\"ping\":\"frag1\"}"
  let body2 := "{\"ping\":\"pipe2\"}"
  let rawReq1PartA := "POST /v1/frag HTTP/1.1\r\nHost: 127.0.0.1\r\nAuthorization: Bea".toUTF8
  let rawReq1PartB := (s!"rer secret-cap-token\r\nContent-Length: {body1.utf8ByteSize}\r\nConnection: keep-alive\r\n\r\n" ++ "{\"ping\":").toUTF8
  let rawReq1TailAndReq2 :=
    ("\"frag1\"}" ++ s!"POST /v1/pipe HTTP/1.1\r\nHost: 127.0.0.1\r\nAuthorization: Bearer secret-cap-token\r\nContent-Length: {body2.utf8ByteSize}\r\nConnection: close\r\n\r\n{body2}").toUTF8
  discard <| writeAll fragFd rawReq1PartA false
  IO.sleep 5
  discard <| writeAll fragFd rawReq1PartB false
  IO.sleep 5
  discard <| writeAll fragFd rawReq1TailAndReq2 false
  let mut pipeResp := ByteArray.empty
  for _ in [0:32] do
    match ← pollReadable fragFd 1000 with
    | .error _ => break
    | .ok () =>
      let ch ← readStreamChunk fragFd 16384
      if ch.isEmpty then break
      pipeResp := pipeResp ++ ch
  discard <| closeFd fragFd
  let pipeRespStr := String.fromUTF8! pipeResp

  let servedRes ← IO.wait serverTask
  let servedCount := match servedRes with | .ok n => n | .error _ => 0
  discard <| closeFd listenFd

  -- 7b. `httpClientRequest` fail-closed deadline & truncated-response checks (no silent `.ok ""` or partial body)
  let .ok (slowListenFd, slowPort) ← tcpListen "127.0.0.1" 0 16
    | do IO.eprintln "[lean-sys-core] FAIL: tcpListen slow/truncated server"; return 1
  let slowServerTask ← IO.asTask (prio := .dedicated) do
    -- Case 1: Client connects, server accepts and stalls past client deadline without sending headers
    if let .ok c1 ← tcpAcceptPoll slowListenFd 2000 then
      discard <| pollReadable c1 50
      discard <| readStreamChunk c1 4096
      IO.sleep 140
      discard <| closeFd c1
    -- Case 2: Server sends `Content-Length: 32` header + only 6 bytes of body, then stalls past deadline
    if let .ok c2 ← tcpAcceptPoll slowListenFd 2000 then
      discard <| pollReadable c2 50
      discard <| readStreamChunk c2 4096
      let partialResp := "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 32\r\nConnection: close\r\n\r\n{\"par"
      discard <| writeAll c2 partialResp.toUTF8 false
      IO.sleep 140
      discard <| closeFd c2
    -- Case 3: Server sends `Content-Length: 32` header + 6 bytes of body, then closes socket immediately (premature EOF)
    if let .ok c3 ← tcpAcceptPoll slowListenFd 2000 then
      discard <| pollReadable c3 50
      discard <| readStreamChunk c3 4096
      let eofPartialResp := "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 32\r\nConnection: close\r\n\r\n{\"eof"
      discard <| writeAll c3 eofPartialResp.toUTF8 false
      discard <| closeFd c3
  let emptyTimeoutRes ← httpClientRequest "127.0.0.1" slowPort "GET" "/stall" (ByteSlice.ofString "") none 60
  let partialTimeoutRes ← httpClientRequest "127.0.0.1" slowPort "GET" "/partial-stall" (ByteSlice.ofString "") none 60
  let prematureEofRes ← httpClientRequest "127.0.0.1" slowPort "GET" "/partial-eof" (ByteSlice.ofString "") none 500
  discard <| IO.wait slowServerTask
  discard <| closeFd slowListenFd
  IO.FS.removeDirAll pTest

  match emptyTimeoutRes, partialTimeoutRes, prematureEofRes with
  | .error .eagain, .error .eagain, .error .eio => pure ()
  | _, _, _ =>
    IO.eprintln s!"[lean-sys-core] FAIL: httpClientRequest did not fail closed on timeout/premature-EOF: {repr emptyTimeoutRes} / {repr partialTimeoutRes} / {repr prematureEofRes}"
    return 1

  match clientRes with
  | .error e =>
    IO.eprintln s!"[lean-sys-core] FAIL: httpClientRequest error {e}"
    return 1
  | .ok respBody =>
    if servedCount != 3 ||
       (respBody.splitOn "\"ok\":true").length ≤ 1 ||
       (respBody.splitOn "\"pong\"").length ≤ 1 ||
       (pipeRespStr.splitOn "\"frag1\"").length ≤ 1 ||
       (pipeRespStr.splitOn "\"pipe2\"").length ≤ 1 then
      IO.eprintln s!"[lean-sys-core] FAIL: unexpected HTTP/pipelined response (served={servedCount}): {respBody} / {pipeRespStr}"
      return 1

  IO.println s!"\{ \"ok\": true, \"binary\": \"lean-sys-core\", \"c_abi_gates\": 33, \"fd_32bit_high\": true, \"hmac_sha256_rfc4231\": true, \"par_scheduler\": true, \"wal_torn_recovery\": true, \"wal_68mib_streaming\": true, \"cas_immutable\": true, \"sst_bloom\": true, \"table_range_scan\": true, \"auth_rotation\": true, \"proc_log\": true, \"proc_stat_scanner\": true, \"jsonrpc_2_0\": true, \"shm_ring_mmap\": true, \"mmap_seqlock\": true, \"jsonl_tape\": true, \"reactor_keepalive\": true, \"sandbox_landlock\": true, \"pgid_reaper\": true, \"http_loopback_port\": {boundPort} }"
  return 0

/-- Run deterministic micro-benchmarks for `lean-sys-core bench` and emit JSON metrics. -/
def runBench (iters : Nat := 2000) : IO UInt32 := do
  let ts ← IO.monoNanosNow
  let tmpBase ← match ← IO.getEnv "TMPDIR" with
    | some d => pure (if d.isEmpty then "/tmp" else d)
    | none => pure "/tmp"
  let benchRoot := if ← (System.FilePath.mk "/dev/shm").pathExists then "/dev/shm" else tmpBase
  let benchDir := s!"{benchRoot}/lean-sys-bench-{ts}"
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
    IO.println "{\"ok\":true,\"exports\":[\"leansys_verify_slice_bounds\",\"leansys_verify_wal_frame\",\"leansys_verify_cas_digest\",\"leansys_check_http_bounds\",\"leansys_verify_jsonl_tape\",\"leansys_verify_ring_cursor\",\"leansys_verify_sst_block\",\"leansys_verify_poll_interest\",\"leansys_verify_rlimit_budget\",\"leansys_mix64_word\",\"leansys_verify_composite_key_order\",\"leansys_verify_token_auth\",\"leansys_verify_log_window\",\"leansys_verify_jsonrpc_frame\",\"leansys_gate_admit\",\"leansys_verify_mmap_seqlock\",\"leansys_verify_proc_stat_fields\",\"leansys_sse_frame_scan\",\"leansys_gfm_pipe_scan\",\"leansys_tag_scan\",\"leansys_transcript_index\",\"leansys_verify_par_chunk\",\"leansys_verify_arena_disjoint\",\"leansys_verify_snapshot_visibility\",\"leansys_verify_http_route_match\",\"leansys_verify_counterexample_triage\",\"leansys_verify_dag_wave_step\",\"leansys_verify_ios_jetsam_budget\",\"leansys_verify_worker_budget\",\"leansys_verify_page_aligned_buffer\",\"leansys_select_isa\",\"leansys_verify_isa_selection\",\"leansys_verify_fd_bounds\"]}"
    return 0
  | _ =>
    IO.println "usage: lean-sys-core [self-test | bench | --c-abi]"
    return 0

/-
  LeanSys.Core: Standalone Native Verification & Self-Test Binary (`lean-sys-core`, `supportInterpreter := false`)
  Executes deterministic end-to-end self-tests across:
  1. `LeanSys.Spec` C-ABI gates (`leansys_verify_slice_bounds`, `leansys_verify_wal_frame`,
     `leansys_verify_cas_digest`, `leansys_check_http_bounds`)
  2. `LeanSys.Store` WAL `put`, torn-tail fault injection & truncation recovery, atomic `compact`,
     and `casPut` / `casMaterialize` zero-copy hardlinking
  3. `LeanSys.Posix` `spawnProcessGroup` + `waitOrKillGroup` (`-pgid` reaper)
  4. `LeanSys.Http` zero-copy HTTP/1.1 parser, ephemeral loopback `tcpListen`/`serveLoop` + `httpClientRequest` roundtrip
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Store
import LeanSys.Http

namespace LeanSys.Core

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Store
open LeanSys.Http

/-- Run the complete `lean-sys-core self-test` suite. -/
def runSelfTest : IO UInt32 := do
  -- 1. C-ABI Spec Gates
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
  if !(sbOk && wfOk && casGateOk && httpGateOk) then
    IO.eprintln "[lean-sys-core] FAIL: C-ABI Spec gates check failed"
    return 1

  -- 2. Store WAL + Torn-Tail Recovery + Compaction + CAS Hardlink
  let ts ← IO.monoNanosNow
  let testDir := s!"/tmp/lean-sys-selftest-{ts}"
  let pTest : System.FilePath := testDir
  if ← pTest.pathExists then
    IO.FS.removeDirAll pTest
  IO.FS.createDirAll pTest

  let .ok st0 ← openStore testDir
    | do IO.eprintln "[lean-sys-core] FAIL: openStore initial"; return 1
  let .ok st1 ← putString st0 "alpha" "value-alpha-1" true
    | do IO.eprintln "[lean-sys-core] FAIL: put alpha"; return 1
  let .ok st2 ← putString st1 "beta" "value-beta-2" true
    | do IO.eprintln "[lean-sys-core] FAIL: put beta"; return 1

  -- Inject a corrupt / torn trailing WAL frame (8 bytes instead of full frame)
  let tornBytes := ByteArray.mk #[0x53, 0x59, 0x53, 0x4C, 0x20, 0x00, 0x00, 0x00]
  let _ ← withFd st2.walPath 2 (fun fd => writeAll fd tornBytes true)

  -- Re-open Store and verify torn frame was truncated and committed keys are intact
  let .ok stRecovered ← openStore testDir
    | do IO.eprintln "[lean-sys-core] FAIL: openStore recovery"; return 1
  if !stRecovered.tornCleaned ||
     getString? stRecovered "alpha" != some "value-alpha-1" ||
     getString? stRecovered "beta" != some "value-beta-2" then
    IO.eprintln "[lean-sys-core] FAIL: WAL torn-tail recovery mismatch"
    return 1

  let .ok stCompacted ← compact stRecovered
    | do IO.eprintln "[lean-sys-core] FAIL: Store.compact"; return 1
  if getString? stCompacted "alpha" != some "value-alpha-1" || stCompacted.framesCount != 2 then
    IO.eprintln "[lean-sys-core] FAIL: Store.compact state mismatch"
    return 1

  -- CAS put & hardlink materialize
  let blobPayload := ByteSlice.ofString "(lnir_module verified_cas_object_v1)"
  let .ok casKey ← casPut stCompacted blobPayload
    | do IO.eprintln "[lean-sys-core] FAIL: Store.casPut"; return 1
  let matPath := s!"{testDir}/materialized_blob.lnir"
  let .ok () ← casMaterialize stCompacted casKey matPath
    | do IO.eprintln "[lean-sys-core] FAIL: Store.casMaterialize"; return 1
  let matRead ← IO.FS.readFile matPath
  if matRead != "(lnir_module verified_cas_object_v1)" then
    IO.eprintln "[lean-sys-core] FAIL: CAS materialized content mismatch"
    return 1

  -- 3. Process-Group Spawn & Reaper (`setpgid` + `waitpid`)
  let .ok cg ← spawnProcessGroup "/bin/true" #[]
    | do IO.eprintln "[lean-sys-core] FAIL: spawnProcessGroup /bin/true"; return 1
  let .ok (some exitCode) ← waitOrKillGroup cg 0 false
    | do IO.eprintln "[lean-sys-core] FAIL: waitOrKillGroup /bin/true"; return 1
  if exitCode != 0 then
    IO.eprintln s!"[lean-sys-core] FAIL: /bin/true exit code {exitCode}"
    return 1

  -- 4. Zero-Copy HTTP/1.1 Loopback Server & Client Roundtrip
  let .ok (listenFd, boundPort) ← tcpListen "127.0.0.1" 0 16
    | do IO.eprintln "[lean-sys-core] FAIL: tcpListen ephemeral"; return 1
  let serverTask ← IO.asTask (prio := .dedicated) do
    serveLoop listenFd 1 3000 (some "secret-cap-token") fun req => do
      let bodyStr := req.bodySlice.toStringLossy
      return HttpResponse.json 200 s!"\{\"ok\":true,\"method\":\"{req.method}\",\"path\":\"{req.path}\",\"echo\":{bodyStr}}"

  let reqJson := ByteSlice.ofString "{\"ping\":\"pong\"}"
  let clientRes ← httpClientRequest "127.0.0.1" boundPort "POST" "/v1/test" reqJson (some "secret-cap-token")
  let _ ← IO.wait serverTask
  discard <| closeFd listenFd
  IO.FS.removeDirAll pTest

  match clientRes with
  | .error e =>
    IO.eprintln s!"[lean-sys-core] FAIL: httpClientRequest error {e}"
    return 1
  | .ok respBody =>
    if (respBody.splitOn "\"ok\":true").length ≤ 1 || (respBody.splitOn "\"pong\"").length ≤ 1 then
      IO.eprintln s!"[lean-sys-core] FAIL: unexpected HTTP response: {respBody}"
      return 1

  IO.println s!"\{ \"ok\": true, \"binary\": \"lean-sys-core\", \"c_abi_gates\": 4, \"wal_torn_recovery\": true, \"cas_hardlink\": true, \"pgid_reaper\": true, \"http_loopback_port\": {boundPort} }"
  return 0

end LeanSys.Core

def main (args : List String) : IO UInt32 := do
  match args with
  | ["self-test"] | ["--self-test"] | [] => LeanSys.Core.runSelfTest
  | ["--c-abi"] =>
    IO.println "{\"ok\":true,\"exports\":[\"leansys_verify_slice_bounds\",\"leansys_verify_wal_frame\",\"leansys_verify_cas_digest\",\"leansys_check_http_bounds\"]}"
    return 0
  | _ =>
    IO.println "usage: lean-sys-core [self-test | --c-abi]"
    return 0

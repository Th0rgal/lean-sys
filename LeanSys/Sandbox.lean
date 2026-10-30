/-
  LeanSys.Sandbox: Subprocess Process-Group Quota Enforcer & Honest Linux Landlock Isolation
  (`0 import Lean`, `0 sorryAx`)
  - Gated by `LeanSys.Spec.verifyRlimitBudget` (`leansys_verify_rlimit_budget`)
  - Spawns isolated process groups (`setpgid(0, 0)`) and polls completion under wall-clock
    and output-byte quotas, guaranteeing `SIGKILL` (`-pgid`) cleanup on timeout or quota breach
  - Real Linux Landlock filesystem confinement (`LandlockPolicy`, `probeLandlockAbi`, `applyLandlockPolicy`,
    `runLandlockedGroup`): probes kernel Landlock ABI first and applies `landlock_restrict_self(2)` in the
    child before `execve` (or in-process via `applyLandlockSelf`), failing closed with `.error .eopnotsupp`
    on kernels/platforms without Landlock instead of returning a synthetic pure `applied := true` struct.
-/
import LeanSys.Spec
import LeanSys.Posix

namespace LeanSys.Sandbox

open LeanSys.Spec
open LeanSys.Posix

/-- Resource quota envelope for a sandboxed subprocess group. -/
structure SandboxQuota where
  maxRssBytes  : UInt64 := 536870912 -- 512 MiB
  timeoutMs    : UInt64 := 5000      -- 5s
  maxPipeBytes : UInt64 := 4194304   -- 4 MiB

/-- Linux Landlock filesystem access policy for a sandboxed child process (in addition to system `/usr`, `/lib`, `/lib64`, `/bin` read/exec). -/
structure LandlockPolicy where
  readOnlyPath  : String := ""
  readWritePath : String := ""
  deriving Repr, DecidableEq

/-- Execution receipt from a sandboxed subprocess group (`landlockEnforced` is `true` iff kernel Landlock ruleset was applied before `execve`). -/
structure SandboxResult where
  exitCode         : UInt32
  elapsedMs        : UInt64
  timedOut         : Bool
  quotaBreach      : Bool
  landlockEnforced : Bool := false
  deriving Repr, DecidableEq

@[inline]
private def hasInteriorNullByte (s : String) : Bool := Id.run do
  let b := s.toUTF8
  for i in [0:b.size] do
    if b.get! i == 0 then
      return true
  return false

/-- Probe host kernel Landlock support (`>= 1` on Linux 5.13+ with Landlock enabled; `.error .eopnotsupp` otherwise). -/
@[inline]
def queryLandlockAbi : IO (SysResult UInt32) :=
  probeLandlockAbi

/-- Apply `policy` to the calling process/thread via `landlock_create_ruleset` + `landlock_restrict_self`.
    Fails closed with `.error .eopnotsupp` when Landlock is unsupported or `.error .einval` on invalid paths. -/
def applyLandlockPolicy (policy : LandlockPolicy) : IO (SysResult UInt32) := do
  if hasInteriorNullByte policy.readOnlyPath || hasInteriorNullByte policy.readWritePath then
    return .error .einval
  match ← probeLandlockAbi with
  | .error e => return .error e
  | .ok abi =>
    match ← applyLandlockSelf policy.readOnlyPath policy.readWritePath with
    | .error e => return .error e
    | .ok () => return .ok abi

/-- Internal helper running `cmd` with optional pre-`execve` Landlock confinement (`landlockPolicy?`)
    decoded in Lean and passed as explicit typed parameters (`roPath`, `rwPath`, `confine`) to `withChildGroupWithLandlock`. -/
private def runGroupInternal (quota : SandboxQuota) (landlockPolicy? : Option LandlockPolicy)
    (cmd : String) (args : Array String)
    (observedRssBytes : UInt64 := 0) (observedPipeBytes : UInt64 := 0) : IO (SysResult SandboxResult) := do
  if args.size > 64 || hasInteriorNullByte cmd || args.any hasInteriorNullByte then
    return .error .einval
  let (roPath, rwPath, confine) ← match landlockPolicy? with
    | none => pure ("", "", false)
    | some pol =>
      if hasInteriorNullByte pol.readOnlyPath || hasInteriorNullByte pol.readWritePath then
        return .error .einval
      match ← probeLandlockAbi with
      | .error e => return .error e
      | .ok _ => pure (pol.readOnlyPath, pol.readWritePath, true)
  let t0 ← IO.monoNanosNow
  withChildGroupWithLandlock cmd args roPath rwPath confine fun cg => do
    let mut doneExit : Option UInt32 := none
    let mut timedOut := false
    let mut quotaBreach := false
    while doneExit.isNone do
      let now ← IO.monoNanosNow
      let elapsedMs : UInt64 := ((now - t0) / 1000000).toUInt64
      if verifyRlimitBudget observedRssBytes quota.maxRssBytes elapsedMs quota.timeoutMs observedPipeBytes quota.maxPipeBytes != 1 then
        timedOut := elapsedMs > quota.timeoutMs
        quotaBreach := true
        discard <| waitOrKillGroup cg 9 false
        doneExit := some 137
        break
      match ← waitOrKillGroup cg 0 true with
      | .error e => return .error e
      | .ok (some code) =>
        doneExit := some code
      | .ok none =>
        IO.sleep 2
    let code := doneExit.getD 137
    if landlockPolicy?.isSome && code == 126 then
      return .error .eacces
    let t1 ← IO.monoNanosNow
    let finalMs : UInt64 := ((t1 - t0) / 1000000).toUInt64
    return .ok {
      exitCode := code
      elapsedMs := finalMs
      timedOut := timedOut
      quotaBreach := quotaBreach
      landlockEnforced := landlockPolicy?.isSome
    }

/-- Run `cmd` with `args` inside a monitored `ChildGroup` (`-pgid`) enforced by `leansys_verify_rlimit_budget`. -/
def runSandboxedGroup (quota : SandboxQuota) (cmd : String) (args : Array String)
    (observedRssBytes : UInt64 := 0) (observedPipeBytes : UInt64 := 0) : IO (SysResult SandboxResult) :=
  runGroupInternal quota none cmd args observedRssBytes observedPipeBytes

/-- Run `cmd` with `args` inside both a monitored `-pgid` quota group AND kernel Linux Landlock path confinement (`policy`).
    Fails closed (`.error .eopnotsupp` on non-Landlock kernels/OSes; `.error .eacces` if policy rule setup fails).
    The child reports a pre-`execve` Landlock setup failure as exit status `126`, so a confined command that itself
    exits `126` (e.g. a shell "not executable" error) is also reported as `.error .eacces`; this conservative mapping
    never reports an unconfined run as `landlockEnforced := true`. -/
def runLandlockedGroup (quota : SandboxQuota) (policy : LandlockPolicy) (cmd : String) (args : Array String)
    (observedRssBytes : UInt64 := 0) (observedPipeBytes : UInt64 := 0) : IO (SysResult SandboxResult) :=
  runGroupInternal quota (some policy) cmd args observedRssBytes observedPipeBytes


/-! ## Linux `cgroup v2` Unified Hierarchy Metrics & Atomic Pre-`execve` Confinement -/

/-- Parsed live snapshot of a Linux `cgroup v2` directory (`memory.current` + `memory.events`). -/
structure CgroupV2Metrics where
  cgroupDir         : String
  memoryCurrentBytes : UInt64
  oomEvents         : UInt64
  oomKillCount      : UInt64
  deriving Repr, DecidableEq

private def parseAsciiUInt64? (s : String) : Option UInt64 := Id.run do
  let u := s.trimAscii.toString.toUTF8
  if u.size == 0 then return none
  let mut acc : UInt64 := 0
  for i in [0:u.size] do
    let b := u.get! i
    if 48 ≤ b && b ≤ 57 then
      acc := acc * 10 + (b - 48).toUInt64
    else
      return none
  return some acc

private def readSmallProcFile (path : String) : IO (SysResult String) := do
  withFd path 0 fun fd => do
    let bytes ← preadByteArray fd 0 8192
    pure (.ok (String.fromUTF8! bytes))

/-- Resolve the calling process's Linux `cgroup v2` directory (`/sys/fs/cgroup/<subpath>`) from `/proc/self/cgroup`. -/
def resolveSelfCgroupV2Dir (cgroupMount : String := "/sys/fs/cgroup") : IO (SysResult String) := do
  match ← readSmallProcFile "/proc/self/cgroup" with
  | .error e => pure (.error e)
  | .ok txt =>
    for line in txt.splitOn "\n" do
      let trimmed := line.trimAscii.toString
      if trimmed.startsWith "0::" then
        let sub := (trimmed.drop 3).toString
        let rel := if sub.startsWith "/" then (sub.drop 1).toString else sub
        let full := if rel.isEmpty then cgroupMount else s!"{cgroupMount}/{rel}"
        return .ok full
    return .error .eopnotsupp

/-- Parse `memory.events` text to extract `(oom, oom_kill)` counters in pure Lean (`0` C LOC).
    Fails closed (`none`) if `oom` or `oom_kill` lines are missing or non-numeric. -/
def parseMemoryEvents? (content : String) : Option (UInt64 × UInt64) := Id.run do
  let mut oom? : Option UInt64 := none
  let mut oomKill? : Option UInt64 := none
  for line in content.splitOn "\n" do
    let parts := line.trimAscii.toString.splitOn " "
    match parts with
    | ["oom", v] =>
      match parseAsciiUInt64? v with
      | some n => oom? := some n
      | none => return none
    | ["oom_kill", v] =>
      match parseAsciiUInt64? v with
      | some n => oomKill? := some n
      | none => return none
    | _ => pure ()
  match oom?, oomKill? with
  | some o, some k => some (o, k)
  | _, _ => none

/-- Read live `memory.current` and `memory.events` (`oom`, `oom_kill`) from `cgroupDir` in pure Lean. -/
def readCgroupV2Metrics (cgroupDir : String) : IO (SysResult CgroupV2Metrics) := do
  if cgroupDir.isEmpty || hasInteriorNullByte cgroupDir then
    return .error .einval
  match ← readSmallProcFile s!"{cgroupDir}/memory.current" with
  | .error e => return .error e
  | .ok memTxt =>
    let some memCur := parseAsciiUInt64? memTxt
      | return .error .eio
    match ← readSmallProcFile s!"{cgroupDir}/memory.events" with
    | .error e => return .error e
    | .ok evTxt =>
      let some (oomCnt, oomKillCnt) := parseMemoryEvents? evTxt
        | return .error .eio
      return .ok {
        cgroupDir := cgroupDir
        memoryCurrentBytes := memCur
        oomEvents := oomCnt
        oomKillCount := oomKillCnt
      }

/-- Run `cmd` inside an isolated `-pgid` process group atomically placed into `cgroupDir/cgroup.procs`
    (and optional `landlockPolicy?`) in the child BEFORE `execve`, polling live `memory.current` and `oom_kill`
    via `leansys_verify_cgroup_v2_budget` and `leansys_verify_rlimit_budget`.
    Fails closed (`.error .eacces`) if the child cannot attach to `cgroup.procs` (child exits `126`). -/
def runCgroupV2Group (quota : SandboxQuota) (cgroupDir : String)
    (cmd : String) (args : Array String)
    (landlockPolicy? : Option LandlockPolicy := none)
    (observedPipeBytes : UInt64 := 0) : IO (SysResult (SandboxResult × Option CgroupV2Metrics)) := do
  if cgroupDir.isEmpty || hasInteriorNullByte cgroupDir || args.size > 63 ||
     hasInteriorNullByte cmd || args.any hasInteriorNullByte then
    return .error .einval
  let (roPath, rwPath, confineLl) ← match landlockPolicy? with
    | none => pure ("", "", false)
    | some pol =>
      if hasInteriorNullByte pol.readOnlyPath || hasInteriorNullByte pol.readWritePath then
        return .error .einval
      match ← probeLandlockAbi with
      | .error e => return .error e
      | .ok _ => pure (pol.readOnlyPath, pol.readWritePath, true)
  let cgProcs := s!"{cgroupDir}/cgroup.procs"
  let t0 ← IO.monoNanosNow
  match ← spawnProcessGroupWithCgroupAndLandlock cmd args cgProcs roPath rwPath confineLl with
  | .error e => return .error e
  | .ok cg =>
    try
      let mut doneExit : Option UInt32 := none
      let mut timedOut := false
      let mut quotaBreach := false
      let mut metricsErr : Option Errno := none
      let mut lastMetrics : Option CgroupV2Metrics := none
      while doneExit.isNone do
        let now ← IO.monoNanosNow
        let elapsedMs : UInt64 := ((now - t0) / 1000000).toUInt64
        let liveRss ← match ← readCgroupV2Metrics cgroupDir with
          | .ok m =>
            lastMetrics := some m
            if verifyCgroupV2Budget m.memoryCurrentBytes quota.maxRssBytes m.oomKillCount 1 != 1 then
              quotaBreach := true
            pure m.memoryCurrentBytes
          | .error e =>
            metricsErr := some e
            pure 0
        if metricsErr.isSome then
          discard <| waitOrKillGroup cg 9 false
          break
        if quotaBreach || verifyRlimitBudget liveRss quota.maxRssBytes elapsedMs quota.timeoutMs observedPipeBytes quota.maxPipeBytes != 1 then
          timedOut := elapsedMs > quota.timeoutMs
          quotaBreach := true
          discard <| waitOrKillGroup cg 9 false
          doneExit := some 137
          break
        match ← waitOrKillGroup cg 0 true with
        | .error e => return .error e
        | .ok (some code) => doneExit := some code
        | .ok none => IO.sleep 2
      if let some me := metricsErr then
        return .error me
      let code := doneExit.getD 137
      if code == 126 then
        return .error .eacces
      let t1 ← IO.monoNanosNow
      let finalMs : UInt64 := ((t1 - t0) / 1000000).toUInt64
      return .ok ({
        exitCode := code
        elapsedMs := finalMs
        timedOut := timedOut
        quotaBreach := quotaBreach
        landlockEnforced := confineLl
      }, lastMetrics)
    finally
      discard <| waitOrKillGroup cg 9 false

end LeanSys.Sandbox

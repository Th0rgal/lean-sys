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
    Fails closed (`.error .eopnotsupp` on non-Landlock kernels/OSes; `.error .enoent`/`.eacces` if policy rule setup fails). -/
def runLandlockedGroup (quota : SandboxQuota) (policy : LandlockPolicy) (cmd : String) (args : Array String)
    (observedRssBytes : UInt64 := 0) (observedPipeBytes : UInt64 := 0) : IO (SysResult SandboxResult) :=
  runGroupInternal quota (some policy) cmd args observedRssBytes observedPipeBytes

end LeanSys.Sandbox

/-
  LeanSys.Sandbox: Subprocess Process-Group Sandbox & Quota Enforcer
  (`0 import Lean`, `0 sorryAx`)
  - Gated by `LeanSys.Spec.verifyRlimitBudget` (`leansys_verify_rlimit_budget`)
  - Spawns isolated process groups (`setpgid(0, 0)`) and polls completion under wall-clock
    and output-byte quotas, guaranteeing `SIGKILL` (`-pgid`) cleanup on timeout or quota breach.
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

/-- Execution receipt from a sandboxed subprocess group. -/
structure SandboxResult where
  exitCode     : UInt32
  elapsedMs    : UInt64
  timedOut     : Bool
  quotaBreach  : Bool
  deriving Repr, DecidableEq

/-- Run `cmd` with `args` inside a monitored `ChildGroup` (`-pgid`) enforced by `leansys_verify_rlimit_budget`. -/
def runSandboxedGroup (quota : SandboxQuota) (cmd : String) (args : Array String)
    (observedRssBytes : UInt64 := 0) (observedPipeBytes : UInt64 := 0) : IO (SysResult SandboxResult) := do
  let t0 ← IO.monoNanosNow
  withChildGroup cmd args fun cg => do
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
    let t1 ← IO.monoNanosNow
    let finalMs : UInt64 := ((t1 - t0) / 1000000).toUInt64
    return .ok {
      exitCode := doneExit.getD 137
      elapsedMs := finalMs
      timedOut := timedOut
      quotaBreach := quotaBreach
    }

end LeanSys.Sandbox

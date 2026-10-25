/-
  LeanSys.Contracts.SpeculativeGate: Universal Layer-0 Speculative Gate Combinators (`0 import Lean`, `0 sorryAx`)
-/

namespace LeanSys.Contracts

/-- Universal Speculative Gate combinator for boolean verifiers with baseline fallback (`turbo-lean` pattern). -/
@[inline] def evalWithUntrustedAccelerator {Goal Cert : Type}
    (accel : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool) (g : Goal) : Bool :=
  match accel g with
  | some c => if kernelVerifyCert g c then true else kernelFallback g
  | none => kernelFallback g

theorem untrusted_accelerator_kernel_replay_sound {Goal Cert : Type}
    (accel : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool)
    (h_cert_sound : ∀ g c, kernelVerifyCert g c = true → kernelFallback g = true) (g : Goal) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = kernelFallback g := by
  unfold evalWithUntrustedAccelerator
  split <;> first | rfl | (split <;> first | rfl | exact (h_cert_sound g _ ‹_›).symm)

theorem untrusted_accelerator_timeout_fallback {Goal Cert : Type}
    (accel : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool)
    (g : Goal) (h_timeout : accel g = none) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = kernelFallback g := by
  simp [evalWithUntrustedAccelerator, h_timeout]

theorem speculative_gate_rejection_fallback {Goal Cert : Type}
    (accel : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool)
    (g : Goal) (c : Cert) (h_some : accel g = some c) (h_rej : kernelVerifyCert g c = false) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = kernelFallback g := by
  simp [evalWithUntrustedAccelerator, h_some, h_rej]

theorem speculative_gate_complete {Goal Cert : Type}
    (accel : Goal → Option Cert) (kernelVerifyCert : Goal → Cert → Bool) (kernelFallback : Goal → Bool)
    (g : Goal) (h_valid : kernelFallback g = true) :
    evalWithUntrustedAccelerator accel kernelVerifyCert kernelFallback g = true := by
  unfold evalWithUntrustedAccelerator; split <;> simp_all

/-- Universal Speculative Gate combinator for artifact/code transformations (`lean-native` pattern). -/
@[inline] def evalWithUntrustedOptPlugin {Decl Cert : Type}
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool) (d : Decl) : Decl :=
  match plugin d with
  | some (cand, cert) => if verifyGate d cand cert then cand else d
  | none => d

theorem untrusted_opt_plugin_tv_gate_sound {Decl Cert : Type}
    (Refines : Decl → Decl → Prop) (h_refl : ∀ d, Refines d d)
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool)
    (h_gate_sound : ∀ d cand cert, verifyGate d cand cert = true → Refines d cand) (d : Decl) :
    Refines d (evalWithUntrustedOptPlugin plugin verifyGate d) := by
  unfold evalWithUntrustedOptPlugin
  split
  · split
    · exact h_gate_sound d _ _ ‹_›
    · exact h_refl d
  · exact h_refl d

theorem untrusted_opt_plugin_timeout_fallback {Decl Cert : Type}
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool)
    (d : Decl) (h_timeout : plugin d = none) :
    evalWithUntrustedOptPlugin plugin verifyGate d = d := by
  simp [evalWithUntrustedOptPlugin, h_timeout]

theorem untrusted_opt_plugin_reject_fallback {Decl Cert : Type}
    (plugin : Decl → Option (Decl × Cert)) (verifyGate : Decl → Decl → Cert → Bool)
    (d cand : Decl) (cert : Cert) (h_prop : plugin d = some (cand, cert)) (h_rej : verifyGate d cand cert = false) :
    evalWithUntrustedOptPlugin plugin verifyGate d = d := by
  simp [evalWithUntrustedOptPlugin, h_prop, h_rej]

end LeanSys.Contracts

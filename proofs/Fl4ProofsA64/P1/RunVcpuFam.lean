/-
P1 (AArch64 only): per-family frame lemmas for [J] `RunVcpuInv` (`RUN_VCPU t ≠ 0 → STATE t = TS_RUNNING_VM`),
in the style of `vcpu.check.rv` / `RvW` / `RvSt`, for use from P3 (the entry composites of P1 are vacuous,
p1g EntryVacuous, so the discharge is per family, not over `EntryHyps0A`).

* `RunVcpuInv.keepT`: a step that changes, among the `STATE` / `RUN_VCPU` words, only thread `t`'s `STATE`
  (`KeepT t`, the frame of `set_thread_state` and of the caller's restart) keeps it when `t`'s new state is
  `TS_RUNNING_VM` or `t` runs no VCPU. `RunVcpuInv.restart` (QueueInvoke) is the second case.
* `sched.set_thread_state.rvi`: **the invocation paths that write a thread's `STATE`** (blocking the caller
  on send / receive / reply / call, the restart, suspend's `INACTIVE`, resume): `set_thread_state t v` keeps
  `RunVcpuInv` if `v = TS_RUNNING_VM` or `t`'s `RUN_VCPU` is 0 (for the caller of a syscall: it is not
  `TS_RUNNING_VM`, `P3Place.recvOK`'s A64 conjunct, so `RunVcpuInv.zero`).
* `sched.set_thread_state.rvi_vm`: the `TS_RUNNING_VM` instance (no `RUN_VCPU` hypothesis).
* `RunVcpuInv.wr_vm` and `vcpu.run_tail.rvi`: **`ARMVCPURun` establishes it** (`vcpu::decode_run`'s tail,
  crates/fl4-core/src/arch/aarch64/vcpu.rs): it writes the caller's `RUN_VCPU := vc` and then
  `set_thread_state ct TS_RUNNING_VM`. The write alone breaks `RunVcpuInv` for `ct` (still `TS_RESTART`),
  so the lemma is stated over the pair: from `RunVcpuInv s`, after both steps it holds, with
  `STATE ct = TS_RUNNING_VM` and `RUN_VCPU ct = vc`. The VCPU-word writes before (`OWNER_CPU`, `RUN_CALLER`,
  `RUN_OFFSET`, `RUN_OUT_MASK`, the frame copy) are outside the TCBs: `RvSt.wr_out` (RunVcpuKeep).
* `RunVcpuInv.wr_field`: a write of a TCB field other than `STATE` / `RUN_VCPU` (`RvSt.wr_field`).

No named premises (the lemmas take `RunVcpuInv` at the start, the [J] being discharged, and the
`set_thread_state` / queue facts at the step).
-/
import Fl4ProofsA64.P1.QueueInvoke
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- A `KeepT t` step keeps [J] `RunVcpuInv` when `t`'s new state is `TS_RUNNING_VM` or `t` runs no VCPU. -/
theorem RunVcpuInv.keepT {s s1 : S} {t : U64} (hRV : RunVcpuInv st T s) (k : KeepT st T Cs Rp Scs Nt t s s1)
    (h : L.mem s1 (stA t) = sched.TS_RUNNING_VM ∨ L.mem s (runVcpuA t) = 0#u64) : RunVcpuInv st T s1 := by
  intro y hy hne
  have ef : L.mem s1 (runVcpuA y) = L.mem s (runVcpuA y) :=
    k.fld y hy 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  by_cases e : y = t
  · subst e
    rcases h with h | h
    · exact h
    · exact absurd (ef.trans h) hne
  · rw [k.stf hy e]; exact hRV y hy (by rw [← ef]; exact hne)

/-- **`set_thread_state t v` keeps [J] `RunVcpuInv`** when `v` is `TS_RUNNING_VM` or `t` runs no VCPU. -/
theorem sched.set_thread_state.rvi {X : Set U64} (s : S) (t : obj.Tcb) (v : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hRV : RunVcpuInv st T s)
    (hv : v = sched.TS_RUNNING_VM ∨ L.mem s (runVcpuA t) = 0#u64) :
    sched.set_thread_state st s t v ⦃ s' => L.mem s' (stA t) = v ∧ RunVcpuInv st T s' ⦄ :=
  WP.spec_mono (sched.set_thread_state.state s t v Q R h ht hO hsub) fun s' ⟨est, k⟩ =>
    ⟨est, hRV.keepT k (hv.imp (fun e => est.trans e) id)⟩

/-- `set_thread_state t TS_RUNNING_VM` keeps [J] `RunVcpuInv`. -/
theorem sched.set_thread_state.rvi_vm {X : Set U64} (s : S) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hRV : RunVcpuInv st T s) :
    sched.set_thread_state st s t sched.TS_RUNNING_VM ⦃ s' => L.mem s' (stA t) = sched.TS_RUNNING_VM ∧
      RunVcpuInv st T s' ⦄ :=
  sched.set_thread_state.rvi s t _ Q R h ht hO hsub hRV (Or.inl rfl)

/-- A write of a TCB field other than `STATE` / `RUN_VCPU` keeps [J] `RunVcpuInv`. -/
theorem RunVcpuInv.wr_field {s : S} {t K v : U64} (hRV : RunVcpuInv st T s) (hT : TcbPlaced T) (ht : t ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (h1 : K.val ≠ 3328) (h2 : K.val ≠ 3672) :
    RunVcpuInv st T (L.wr s (core.num.U64.wrapping_add t K) v) :=
  hRV.rvSt (RvSt.wr_field hT ht hK hK8 h1 h2)

/-- The `RUN_VCPU := vc` write of `ARMVCPURun` keeps every other thread's `STATE` and `RUN_VCPU` words. -/
theorem runVcpu_wr_other {s : S} {t y vc : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hy : y ∈ T) :
    L.mem (L.wr s (runVcpuA t) vc) (stA y) = L.mem s (stA y) ∧
      (y ≠ t → L.mem (L.wr s (runVcpuA t) vc) (runVcpuA y) = L.mem s (runVcpuA y)) := by
  have ha : Aligned (core.num.U64.wrapping_add t 3672#u64) := field_aligned (hT t ht) (by simp) (by simp)
  refine ⟨?_, fun hne => ?_⟩
  · rw [stA_eq]
    exact L.mem_wr_ne ha (field_aligned (K := 3328#u64) (hT y hy) (by simp) (by simp))
      (fun e => field_ne (K2 := 3328#u64) (hT t ht) (hT y hy) (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e))
  · exact L.mem_wr_ne ha (field_aligned (K := 3672#u64) (hT y hy) (by simp) (by simp))
      (fun e => field_ne (K2 := 3672#u64) (hT t ht) (hT y hy) (by simp) (by simp) (fun e' => absurd e'.symm hne)
        (UScalar.eq_of_val_eq e))

/-- **`ARMVCPURun` establishes [J] `RunVcpuInv`** (`vcpu::decode_run`'s tail): from `RunVcpuInv s`, the write
`RUN_VCPU ct := vc` followed by `set_thread_state ct TS_RUNNING_VM` ends in a `RunVcpuInv` state, with
`ct` in `TS_RUNNING_VM` running `vc`. The queue / object facts are those at the state after the write
(the caller's, as for any `set_thread_state`). -/
theorem vcpu.run_tail.rvi {X : Set U64} (s : S) (t vc : U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hRV : RunVcpuInv st T s) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h1 : SchedQueuesInvX st T Cs Ω H X (L.wr s (runVcpuA t) vc) Q R)
    (hO1 : ObjsOK st Ω Sg Rp Scs Nt Z (L.wr s (runVcpuA t) vc)) (hsub : ∀ b ∈ Sg, b ∈ Ω) :
    sched.set_thread_state st (L.wr s (runVcpuA t) vc) t sched.TS_RUNNING_VM ⦃ s' =>
      L.mem s' (stA t) = sched.TS_RUNNING_VM ∧ L.mem s' (runVcpuA t) = vc ∧ RunVcpuInv st T s' ⦄ := by
  refine WP.spec_mono (sched.set_thread_state.state _ t _ Q R h1 ht hO1 hsub) fun s' ⟨est, k⟩ => ?_
  have ha : Aligned (runVcpuA t) := field_aligned (K := 3672#u64) (hT t ht) (by simp) (by simp)
  have kr : ∀ y ∈ T, L.mem s' (runVcpuA y) = L.mem (L.wr s (runVcpuA t) vc) (runVcpuA y) := fun y hy =>
    k.fld y hy 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  refine ⟨est, (kr t ht).trans (L.mem_wr_same ha), fun y hy hne => ?_⟩
  by_cases e : y = t
  · subst e; exact est
  · obtain ⟨e1, e2⟩ := runVcpu_wr_other (st := st) (s := s) (vc := vc) hT ht hy
    rw [k.stf hy e, e1]
    exact hRV y hy (by rw [← e2 e, ← kr y hy]; exact hne)

end

end Fl4ProofsA64.P1

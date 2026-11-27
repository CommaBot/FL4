/-
# P2 (line p3mc, gen 34): P3's spec boot lemmas at the relocated boot state `σB`

Every P3 lemma about l4v's dummy initial state `initASt` (the 80 names whose statement or proof mentions
`initASt` / `initKheap` / `initIoc` / `initIrqNodePtr`, in 53 P3 modules: `boot_*`, `init_*`, `initKheap_*`,
`domListOK_init`), re-proved at `σB` (`P2/BootSpec`: `initASt` with the IRQ node at `kbB + 1248`). Each copy keeps
its original's namespace, name + `_B`, statement and proof with `initASt ↦ σB`, `initKheap ↦ kheapB`,
`initIoc ↦ iocB`, `initIrqNodePtr ↦ irqNodeB` and every family name `n ↦ n_B` (generated mechanically by
`proofs/scratch/p3mc/port34.py`; hand fixes, if any, are noted at the declaration).

The facts the P3 start bundle reads: **`boot_sinvX_B`** (`SInvX σB`), **`boot_ioi_B`** (`SInvIP`'s I/O parts),
**`boot_gpmOut_B`**, **`boot_idleVtS_B`**, **`boot_yieldBlock'_B`**, **`boot_yieldScope'_B`**, **`boot_bsa_B`**,
**`boot_offReady_B`**, **`init_capAt_B`** (every cap of `σB` null).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootSpec
import Fl4Proofs.P3.SpecInvUt
import Fl4Proofs.P3.SpecInvUtC
import Fl4Proofs.P3.SpecInvValidMachineTime
import Fl4Proofs.P3.SpecInvOffReady
import Fl4Proofs.P3.SpecInvRdA
import Fl4Proofs.P3.SpecInvFaultTcbs
import Fl4Proofs.P3.SpecInvFaultTcbsH4
import Fl4Proofs.P3.SpecInvFaultTcbsH10
import Fl4Proofs.P3.SpecInvNtfnQ
import Fl4Proofs.P3.SpecInvEqA
import Fl4Proofs.P3.SpecInvCqK
import Fl4Proofs.P3.SpecInvCqR
import Fl4Proofs.P3.SpecInvCtNQR
import Fl4Proofs.P3.SpecInvCqS
import Fl4Proofs.P3.SpecInvUtN
import Fl4Proofs.P3.SpecInvRdY
import Fl4Proofs.P3.SpecInvUtN8
import Fl4Proofs.P3.SpecInvSgE
import Fl4Proofs.P3.SpecInvCqY
import Fl4Proofs.P3.SpecInvRdK
import Fl4Proofs.P3.SpecInvVfhAll
import Fl4Proofs.P3.SpecInvSbE
import Fl4Proofs.P3.SpecInvDom
import Fl4Proofs.P3.SpecInvQDom
import Fl4Proofs.P3.SpecInvSlT
import Fl4Proofs.P3.SpecInvValidIrqMasks
import Fl4Proofs.P3.SpecInvValidIrqHandlers
import Fl4Proofs.P3.SpecInvVfhK
import Fl4Proofs.P3.SpecInvNativeScope
import Fl4Proofs.P3.SpecInvFoS
import Fl4Proofs.P3.SpecInvSlKT
import Fl4Proofs.P3.SpecInvAll
import Fl4Proofs.P3.SpecInvAllC
import Fl4Proofs.P3.SpecInvAllB
import Fl4Proofs.P3.SpecInvCqP3
import Fl4Proofs.P3.SpecInvAllQ
import Fl4Proofs.P3.SpecInvAllR
import Fl4Proofs.P3.SpecInvRd8eC
import Fl4Proofs.P3.SpecInvRd8nC
import Fl4Proofs.P3.SpecInvRd8lD
import Fl4Proofs.P3.SpecInvRd8vC
import Fl4Proofs.P3.SpecInvRd8wB
import Fl4Proofs.P3.XTopJointKEntry35
import Fl4Proofs.P3.SpecInvIoPortsS
import Fl4Proofs.P3.XTopJointKEntry37E
import Fl4Proofs.P3.SpecInvGpm
import Fl4Proofs.P3.SpecInvSiE
import Fl4Proofs.P3.SpecInvNativeScopeBridge
import Fl4Proofs.P3.SpecInvYieldScopeT
import Fl4Proofs.P3.SpecInvYieldScopeH
import Fl4Proofs.P3.JYieldScope
import Fl4Proofs.P3.SpecInvYieldBlockT
import Fl4Proofs.P3.JYieldBlock
open Aeneas Aeneas.Std Result
open Fl4Proofs.P2.BootSt

/-! ## from Fl4Proofs.P3.SpecInvUt -/
section
open Classical
namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem init_cv_B {p : ObjRef} {o : KernelObject} (hp : kheapB p = some o) {i : CnodeIndex} {c : Cap}
    (h : capView o i = some c) : c = .nullCap := by
  simp only [kheapB, Function.update_apply] at hp
  split_ifs at hp <;> (try cases hp)
  all_goals first
    | (cases h; done)
    | (simp only [capView, tcbCnodeMap, Function.update_apply] at h; split_ifs at h <;> (cases h; first | rfl | done))
    | (rw [capView_cnode] at h; split_ifs at h <;> (try simp only [emptyCnode] at h) <;> (try split_ifs at h) <;>
        (cases h; first | rfl | done))
end
end Fl4Proofs.P3.SInvU
end

section
open Classical
namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
/-- The initial state holds only null caps. -/
theorem init_capAt_B {sl : CslotPtr} {c : Cap} (h : capAt (σB (Z := Unit)) sl = some c) : c = .nullCap := by
  obtain ⟨p, i⟩ := sl
  unfold capAt at h
  split at h
  · rename_i o ho; exact init_cv_B ho h
  · cases h
end
end Fl4Proofs.P3.SInvU
end

section
open Classical
namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
/-- **(d) boot**: the untyped invariant holds in the initial state (vacuously:
it has no untyped cap). -/
theorem boot_utInv_B : UtInv (σB (Z := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sl _ _ _ _ hc; cases init_capAt_B hc
  · intro sl _ _ _ _ hc; cases init_capAt_B hc
  · intro s1 _ _ _ _ _ _ _ _ _ _ hc; cases init_capAt_B hc
  · intro s1 _ _ _ _ _ _ _ _ _ _ hc; cases init_capAt_B hc
  · intro sl _ _ _ _ hc; cases init_capAt_B hc
end
end Fl4Proofs.P3.SInvU
end

/-! ## from Fl4Proofs.P3.SpecInvUtC -/
section
open Classical
namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
/-- **(d) boot.** -/
theorem boot_utInv'_B : UtInv' (σB (Z := Unit)) := by
  refine ⟨boot_utInv_B, fun c p h => ?_, fun x hx => ?_⟩
  · exact absurd h (by simp [uV, σB, initCdt])
  · obtain ⟨c, hc⟩ := tg_first hx
    exact absurd hc (by simp [uV, σB, initCdt])
end
end Fl4Proofs.P3.SInvU
end

/-! ## from Fl4Proofs.P3.SpecInvValidMachineTime -/
section
open Classical
namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3.Vs
section
/-- **`ValidMachineTime` at boot** (`σB`: both times 0). -/
theorem boot_vmt_B : ValidMachineTime (σB (Z := Unit)) :=
  ⟨BitVec.le_refl _, by show (0 : Nat) ≤ _; exact Nat.zero_le _⟩
end
end Fl4Proofs.P3.SInvV
end

/-! ## from Fl4Proofs.P3.SpecInvOffReady -/
section
open Classical
namespace Fl4Proofs.P3.SInvV
open Fl4Spec
section
theorem initKheap_idleSc_B : kheapB idleScPtr = some (.schedContext
      { defaultSchedContext with
        scTcb := some idleThreadPtr,
        scRefills := [{ rTime := 0, rAmount := MAX_PERIOD }, { rTime := MAX_PERIOD, rAmount := 0 }],
        scBudget := MAX_PERIOD,
        scRefillMax := MIN_REFILLS } 0) := by
  unfold kheapB
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_self]
end
end Fl4Proofs.P3.SInvV
end

section
open Classical
namespace Fl4Proofs.P3.SInvV
open Fl4Spec
section
/-- **`OffReady` at boot.** -/
theorem boot_offReady_B : Sched.OffReady (σB (Z := Unit)) := by
  intro y n hy
  have h : kheapB idleScPtr = some (.schedContext y n) := hy
  rw [initKheap_idleSc_B] at h
  cases h
  show (0 : Nat) + 0 ≤ 0
  rfl
end
end Fl4Proofs.P3.SInvV
end

/-! ## from Fl4Proofs.P3.SpecInvRdA -/
section
open Classical
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.SInvR
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
section
set_option maxHeartbeats 1000000
section
open Fl4Spec
theorem init_tcbSt_B {u : ObjRef} {x : Tcb} (h : kheapB u = some (.tcb x)) : x.tcbState = .idleThreadState := by
  by_cases e : u = idleThreadPtr
  · subst e
    unfold kheapB at h
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self] at h
    cases h; rfl
  · exfalso
    unfold kheapB at h
    simp only [Function.update_apply, e, if_false] at h
    split_ifs at h <;> cases h
end
end
end Fl4Proofs.P3.SInvR
end

section
open Classical
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.SInvR
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
section
set_option maxHeartbeats 1000000
section
open Fl4Spec
theorem boot_rdy_B : Rdy (σB (Z := Unit)) := by
  refine ⟨fun d p t h => by simp [σB] at h, fun t h => by simp [σB] at h, fun t x c hx hb _ => ?_,
    fun p y n hy _ => ?_, fun t h => by simp [σB] at h, fun y n hy => ?_⟩
  · exfalso
    have e := init_tcbSt_B (u := t) hx
    rcases hb with ⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩ <;> rw [e] at h <;> cases h
  · have hy' : kheapB p = some (.schedContext y n) := hy
    by_cases e : p = idleScPtr
    · subst e
      rw [SInvV.initKheap_idleSc_B] at hy'
      cases hy'
      refine ⟨le_refl _, minBudget_le_maxPeriod, ?_, fun _ => by simp⟩
      have := MAX_PERIOD.isLt
      simp [rsum]; omega
    · exfalso
      unfold kheapB at hy'
      simp only [Function.update_apply, e, if_false] at hy'
      split_ifs at hy' <;> cases hy'
  · have h : kheapB idleScPtr = some (.schedContext y n) := hy
    rw [SInvV.initKheap_idleSc_B] at h
    cases h
    exact ⟨by simp, by show (0 : Nat) ≤ _; exact Nat.zero_le _⟩
end
end
end Fl4Proofs.P3.SInvR
end

/-! ## from Fl4Proofs.P3.SpecInvFaultTcbs -/
section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
/-- **FaultTcbsS at boot** (invA (d)). -/
theorem boot_faultTcbsS_B : FaultTcbsS (σB (Z := Unit)) := by
  intro p x hp
  simp only [σB, kheapB, Function.update_apply] at hp
  split_ifs at hp <;> (try cases hp) <;> (try (intro hf; exact absurd rfl hf))
  all_goals (split_ifs at hp <;> cases hp)
end
end Fl4Proofs.P3.SInv
end

section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
/-- **FaultTcbs at boot** (invA (d)). -/
theorem boot_faultTcbs_B : FaultTcbs (σB (Z := Unit)) := boot_faultTcbsS_B.weak
end
end Fl4Proofs.P3.SInv
end

/-! ## from Fl4Proofs.P3.SpecInvFaultTcbsH4 -/
section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
set_option maxHeartbeats 1000000
variable {L E K : List ObjRef} {C : ObjRef → Prop}
/-- **NQB at boot**: the initial heap has no notification. -/
theorem boot_nqb_B : NQB (σB (Z := Unit)) := by
  rintro t ⟨n, x, hn, -⟩
  simp only [σB, kheapB, Function.update_apply] at hn
  split_ifs at hn <;> (try cases hn)
  all_goals (split_ifs at hn <;> cases hn)
end
end Fl4Proofs.P3.SInv
end

section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
set_option maxHeartbeats 1000000
variable {L E K : List ObjRef} {C : ObjRef → Prop}
/-- **The bundle at boot.** -/
theorem boot_B_B : B [] [] [] (fun _ => True) (σB (Z := Unit)) :=
  (b_nil_iff _).2 ⟨boot_faultTcbsS_B, boot_nqb_B⟩
end
end Fl4Proofs.P3.SInv
end

/-! ## from Fl4Proofs.P3.SpecInvFaultTcbsH10 -/
section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
set_option maxHeartbeats 1000000
/-- The carried pair at boot. -/
theorem boot_faultTcbsS_nqb_B : FaultTcbsS (σB (Z := Unit)) ∧ NQB (σB (Z := Unit)) :=
  ⟨boot_faultTcbsS_B, boot_nqb_B⟩
end
end Fl4Proofs.P3.SInv
end

/-! ## from Fl4Proofs.P3.SpecInvNtfnQ -/
section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
set_option maxHeartbeats 1000000
/-- **NtfnQB at boot** (no notification exists). -/
theorem boot_ntfnQB_B : NtfnQB (σB (Z := Unit)) := by
  intro n x t hn _
  simp only [σB, kheapB, Function.update_apply] at hn
  split_ifs at hn <;> (try cases hn)
  all_goals (split_ifs at hn <;> cases hn)
end
end Fl4Proofs.P3.SInv
end

section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
set_option maxHeartbeats 1000000
/-- **EpQB at boot** (no endpoint exists). -/
theorem boot_epQB_B : EpQB (σB (Z := Unit)) := by
  intro n x t hn _
  simp only [σB, kheapB, Function.update_apply] at hn
  split_ifs at hn <;> (try cases hn)
  all_goals (split_ifs at hn <;> cases hn)
end
end Fl4Proofs.P3.SInv
end

/-! ## from Fl4Proofs.P3.SpecInvEqA -/
section
open Classical
namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvB
section
theorem boot_rpos_B : RPos (σB (Z := Unit)) := by
  intro p y n hy ha hp
  have hy' : kheapB p = some (.schedContext y n) := hy
  by_cases e : p = idleScPtr
  · subst e
    rw [SInvV.initKheap_idleSc_B] at hy'
    cases hy'
    exact absurd rfl hp
  · exfalso
    unfold kheapB at hy'
    simp only [Function.update_apply, e, if_false] at hy'
    split_ifs at hy' <;> cases hy'
end
end Fl4Proofs.P3.SInvE
end

/-! ## from Fl4Proofs.P3.SpecInvCqK -/
section
open Classical
namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
/-- **T1 at boot** (empty queues). -/
theorem boot_t1_B : T1 (σB (Z := Unit)) := fun _ _ _ h => (List.not_mem_nil h).elim
end
end Fl4Proofs.P3.SInvQ
end

/-! ## from Fl4Proofs.P3.SpecInvCqR -/
section
open Classical
namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
/-- **TQ at boot** (empty queues). -/
theorem boot_tq_B : TQ (σB (Z := Unit)) := ⟨fun _ _ _ h => (List.not_mem_nil h).elim, trivial⟩
end
end Fl4Proofs.P3.SInvQ
end

/-! ## from Fl4Proofs.P3.SpecInvCtNQR -/
section
open Classical
namespace Fl4Proofs.P3.SInvV
open Fl4Spec
section
/-- **`CtNQR` at boot.** -/
theorem boot_ctNQR_B : CtNQR (σB (Z := Unit)) := fun _ _ _ h => List.not_mem_nil h
end
end Fl4Proofs.P3.SInvV
end

/-! ## from Fl4Proofs.P3.SpecInvCqS -/
section
open Classical
namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv
open Fl4Proofs.P3.SInvV (CtNQR boot_ctNQR_B)
section
set_option maxHeartbeats 1000000
theorem boot_sa_B : SA (σB (Z := Unit)) :=
  ⟨fun _ h => by simp [σB] at h, fun _ h => by simp [σB] at h, boot_ctNQR_B⟩
end
end Fl4Proofs.P3.SInvQ
end

section
open Classical
namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv
open Fl4Proofs.P3.SInvV (CtNQR boot_ctNQR_B)
section
set_option maxHeartbeats 1000000
theorem boot_schedQ_B : SchedQ (σB (Z := Unit)) := ⟨boot_tq_B, boot_sa_B⟩
end
end Fl4Proofs.P3.SInvQ
end

/-! ## from Fl4Proofs.P3.SpecInvUtN -/
section
open Classical
namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem boot_utNV_B : UtNV (uV (σB (Z := Unit))) := by
  have h0 : ∀ sl c, (uV (σB (Z := Unit))).2.1 sl = some c → c = .nullCap := fun _ _ h => init_capAt_B h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u dev b n fi hu; cases h0 _ _ hu
  · intro p c hp hne; exact absurd (h0 _ _ hp) hne
  · intro u dev b n fi hu; cases h0 _ _ hu
  · intro s c s' c' r _ hs' _ hr'; rw [h0 _ _ hs'] at hr'; simp [sRefs] at hr'
  · intro s c r hs hr; rw [h0 _ _ hs] at hr; simp [sRefs] at hr
  · intro s r b n hs; cases h0 _ _ hs
  · intro s c hs b hb; rw [h0 _ _ hs] at hb; simp [shp] at hb
end
end Fl4Proofs.P3.SInvU
end

section
open Classical
namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
/-- **(boot)** `UtInv''` holds at `σB` (a non-vacuity check; G4 starts from any `UtInv''` state). -/
theorem boot_utInv''_B : UtInv'' (σB (Z := Unit)) := ⟨boot_utInv'_B, boot_utNV_B⟩
end
end Fl4Proofs.P3.SInvU
end

/-! ## from Fl4Proofs.P3.SpecInvRdY -/
section
open Classical
namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ
section
set_option maxHeartbeats 1000000
/-- `IdleHd` (defined in SpecInvRdA since rd5, `Rdy`'s sixth conjunct) at boot (non-vacuity). -/
theorem boot_idleHd_B : IdleHd (σB (Z := Unit)) := boot_rdy_B.2.2.2.2.2
end
end Fl4Proofs.P3.SInvR
end

/-! ## from Fl4Proofs.P3.SpecInvUtN8 -/
section
open Classical
namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem boot_irqOut_B (N : Irq → ObjRef) : IrqOutV N (uV (σB (Z := Unit))) := by
  intro irq s c hs
  rw [init_capAt_B hs, covR_null]; exact fun h => h
end
end Fl4Proofs.P3.SInvU
end

section
open Classical
namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem boot_utInv3_B : UtInv3 (σB (Z := Unit)) := ⟨boot_utInv''_B, boot_irqOut_B _⟩
end
end Fl4Proofs.P3.SInvU
end

/-! ## from Fl4Proofs.P3.SpecInvSgE -/
section
open Classical
namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU
section
set_option maxHeartbeats 1000000
variable {N M : Irq → ObjRef}
/-- Boot (non-vacuity only: the initial state holds null caps). -/
theorem boot_specGlob_B : SpecGlobS (σB (Z := Unit)) ∧ IdleOutV (σB (Z := Unit)) := by
  refine ⟨⟨fun irq a ha => Or.inl (init_capAt_B ha), fun p cref a ha _ irq => ?_, fun p cref a ha _ => ?_⟩,
    boot_irqOut_B _⟩
  · rw [init_capAt_B ha]; simp [objRefs]
  · rw [init_capAt_B ha]; simp [objRefs]
end
end Fl4Proofs.P3.SInvG
end

/-! ## from Fl4Proofs.P3.SpecInvCqY -/
section
open Classical
namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem boot_rb_B (k : Bool) : RBk k (σB (Z := Unit)) := by
  refine ⟨⟨⟨fun _ _ _ h => by simp [σB] at h, fun _ h => by simp [σB] at h⟩,
    fun _ => ⟨fun _ _ h => by simp [σB] at h, ⟨fun h => by simp [σB] at h,
      fun h => by simp [σB] at h⟩⟩, fun _ h => by simp [σB] at h⟩, fun _ => Or.inr ?_⟩
  simp [σB]
end
end Fl4Proofs.P3.SInvQ
end

/-! ## from Fl4Proofs.P3.SpecInvRdK -/
section
open Classical
namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
section
set_option maxHeartbeats 1000000
theorem boot_cAx_B : CAx (σB (Z := Unit)) := fun h => absurd rfl h
end
end Fl4Proofs.P3.SInvR
end

/-! ## from Fl4Proofs.P3.SpecInvVfhAll -/
section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
/-- **VfhAll at boot** (invA (d)): the initial state `σB`. -/
theorem boot_vfhAll_B : VfhAll (σB (Z := Unit)) := by
  intro p x hp
  simp only [σB, kheapB, Function.update_apply] at hp
  split_ifs at hp <;> (try cases hp) <;> (try (unfold vfhQ validFaultHandler; exact Or.inr rfl))
  all_goals (split_ifs at hp <;> cases hp)
end
end Fl4Proofs.P3.SInv
end

/-! ## from Fl4Proofs.P3.SpecInvSbE -/
section
open Classical
namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem initKheap_idleThread_B : ∃ x, kheapB idleThreadPtr = some (.tcb x) ∧ x.tcbSchedContext = some idleScPtr := by
  unfold kheapB
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self]
  exact ⟨_, rfl, rfl⟩
end
end Fl4Proofs.P3.SInvB
end

section
open Classical
namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem init_tcb_B {u : ObjRef} {x : Tcb} (h : kheapB u = some (.tcb x)) :
    u = idleThreadPtr ∧ x.tcbSchedContext = some idleScPtr := by
  by_cases e : u = idleThreadPtr
  · subst e
    obtain ⟨x0, h0, hs⟩ := initKheap_idleThread_B
    rw [h0] at h; cases h; exact ⟨rfl, hs⟩
  · exfalso
    unfold kheapB at h
    simp only [Function.update_apply, e, if_false] at h
    split_ifs at h <;> cases h
end
end Fl4Proofs.P3.SInvB
end

section
open Classical
namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem init_sc_B {p : ObjRef} {y : SchedContext} {n : Nat} (h : kheapB p = some (.schedContext y n)) :
    p = idleScPtr ∧ y.scTcb = some idleThreadPtr ∧ rneQ y := by
  by_cases e : p = idleScPtr
  · subst e
    rw [SInvV.initKheap_idleSc_B] at h
    simp only [Option.some.injEq, KernelObject.schedContext.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl, fun _ => List.cons_ne_nil _ _⟩
  · exfalso
    unfold kheapB at h
    simp only [Function.update_apply, e, if_false] at h
    split_ifs at h <;> cases h
end
end Fl4Proofs.P3.SInvB
end

section
open Classical
namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
/-- **Boot**: the initial state's only binding is the idle thread with the idle SC. -/
theorem boot_scInv_B : ScInv (σB (Z := Unit)) := by
  rw [scInv_iff]
  refine ⟨⟨fun u c h => ?_, fun p u h => ?_⟩, fun p y n hp => (init_sc_B hp).2.2⟩
  · obtain ⟨x, hx, hc⟩ := bv_t.1 h
    obtain ⟨rfl, h2⟩ := init_tcb_B hx
    rw [h2] at hc; cases hc
    exact bv_s.2 ⟨_, 0, SInvV.initKheap_idleSc_B, rfl⟩
  · obtain ⟨y, n, hy, hu⟩ := bv_s.1 h
    obtain ⟨rfl, h2, -⟩ := init_sc_B hy
    rw [h2] at hu; cases hu
    obtain ⟨x0, h0, hs⟩ := initKheap_idleThread_B
    exact bv_t.2 ⟨x0, h0, hs⟩
end
end Fl4Proofs.P3.SInvB
end

section
open Classical
namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem boot_scSym_B : ScSym (σB (Z := Unit)) := boot_scInv_B.1
end
end Fl4Proofs.P3.SInvB
end

section
open Classical
namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
/-- `ScLive` at boot (the idle pair is bound and no cap covers anything: the initial
state holds only null caps). -/
theorem boot_scLive_B : ScLive (σB (Z := Unit)) := by
  intro p _
  refine Or.inr fun s c h => ?_
  rw [SInvU.init_capAt_B h]
  simp [SInvU.covR, SInvU.capRng, objRefs]
end
end Fl4Proofs.P3.SInvB
end

section
open Classical
namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem boot_entryOK_B : EntryOK (σB (Z := Unit)) :=
  ⟨boot_scInv_B, SInvU.boot_utInv3_B, boot_vfhAll_B, boot_scLive_B⟩
end
end Fl4Proofs.P3.SInvB
end

/-! ## from Fl4Proofs.P3.SpecInvDom -/
section
open Classical
namespace Fl4Proofs.P3.SInvDom
open Fl4Spec Fl4Proofs.P3.Vs
section
/-- **(d) `DomListOK` at Fl4Spec's initial state** (`σB`: the list
`[(0, -1), (0, 0)]`, start and index 0). -/
theorem domListOK_init_B : DomListOK (σB (Z := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [σB]
  · intro e he _; simp only [σB, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  · simp [σB]
  · simp only [σB, domainEndMarker]; decide
  · simp only [σB, domainEndMarker]; decide
  · simp [σB]
  · intro e he; simp only [σB, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
end
end Fl4Proofs.P3.SInvDom
end

/-! ## from Fl4Proofs.P3.SpecInvQDom -/
section
open Classical
namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvDom Fl4Proofs.P3.Vs
section
set_option maxHeartbeats 1000000
/-- **(d) T4 at boot** (`σB`). -/
theorem boot_t4_B : T4 (σB (Z := Unit)) := by
  refine ⟨dlok_of domListOK_init_B, rfl, ?_⟩
  intro p x hp
  simp only [σB, kheapB, Function.update_apply] at hp
  split_ifs at hp <;> first | (cases hp; done) | (cases hp; simp [dom0, defaultDomain]) | simp_all [dom0]
end
end Fl4Proofs.P3.SInvQ
end

/-! ## from Fl4Proofs.P3.SpecInvSlT -/
section
open Classical
namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem boot_scLiveT_B : ScLiveT (idleP (σB (Z := Unit))) (σB (Z := Unit)) := by
  intro p o hp hl h1 h2
  exfalso
  simp only [idleP, σB] at hp h1 h2
  unfold kheapB at hp
  simp only [Function.update_apply] at hp
  split_ifs at hp <;> first
    | (exact h1 (by assumption))
    | (exact h2 (by assumption))
    | (cases hp; exact hl)
    | (cases hp)
end
end Fl4Proofs.P3.SInvL
end

section
open Classical
namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv
section
set_option maxHeartbeats 1000000
theorem boot_idleScOutV_B : IdleScOutV (σB (Z := Unit)) := by
  intro _ s c h
  rw [SInvU.init_capAt_B h]
  simp [SInvU.covR, SInvU.capRng, objRefs]
end
end Fl4Proofs.P3.SInvL
end

/-! ## from Fl4Proofs.P3.SpecInvValidIrqMasks -/
section
open Classical
namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3.Vs
section
/-- **`ValidIrqMasks` at boot** (`initIrqMasks`: every line masked). -/
theorem boot_vim_B : ValidIrqMasks (σB (Z := Unit)) := fun _ _ => rfl
end
end Fl4Proofs.P3.SInvV
end

/-! ## from Fl4Proofs.P3.SpecInvValidIrqHandlers -/
section
open Classical
namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3
section
/-- **`ValidIrqHandlers` at boot**: `kheapB` holds no handler cap (the IRQ node's
empty CNodes and the idle thread's null slots). -/
theorem boot_vih_B : ValidIrqHandlers (σB (Z := Unit)) := by
  intro p cref irq hc
  exfalso
  simp only [σB, kheapB, Function.update_apply] at hc
  split_ifs at hc <;>
    first
    | (simp [capOpt] at hc; done)
    | (simp only [capOpt] at hc; done)
    | (simp only [capOpt, emptyCnode] at hc; split_ifs at hc <;> simp_all; done)
    | (simp only [capOpt, tcbCnodeMap, Function.update_apply] at hc; split_ifs at hc <;> simp_all; done)
end
end Fl4Proofs.P3.SInvV
end

/-! ## from Fl4Proofs.P3.SpecInvVfhK -/
section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvV
section
set_option maxHeartbeats 1000000
/-- **CnDom at boot**: every cap of `σB` is null. -/
theorem boot_cnDom_B : CnDom (σB (Z := Unit)) := by
  intro sl c hc p r g e
  subst e
  exfalso
  obtain ⟨o, l⟩ := sl
  dsimp only at hc
  simp only [σB, kheapB, Function.update_apply] at hc
  split_ifs at hc <;>
    first
    | (simp [capOpt] at hc; done)
    | (simp only [capOpt] at hc; done)
    | (simp only [capOpt, emptyCnode] at hc; split_ifs at hc <;> simp_all; done)
    | (simp only [capOpt, tcbCnodeMap, Function.update_apply] at hc; split_ifs at hc <;> simp_all; done)
end
end Fl4Proofs.P3.SInv
end

/-! ## from Fl4Proofs.P3.SpecInvNativeScope -/
section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
set_option maxHeartbeats 1000000
set_option maxErrors 2000
/-- **NativeScope at boot** (invA (d)): the initial state `σB`. -/
theorem boot_nativeScope_B : NativeScopeS (σB (Z := Unit)) := by
  intro p x hp
  simp only [σB, kheapB, Function.update_apply] at hp
  split_ifs at hp <;> first | (cases hp; done) | (cases hp; simp [nsQ]) | simp_all [nsQ]
end
end Fl4Proofs.P3.SInv
end

/-! ## from Fl4Proofs.P3.SpecInvFoS -/
section
open Classical
namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU
section
set_option maxHeartbeats 2000000
set_option maxErrors 2000
/-- Boot (non-vacuity only, per the 2026-11-20 lead decision): no FPU owner. -/
theorem boot_ft_B : FT (σB (Z := Unit)) := fun t ht => by
  simp [σB, initArchState] at ht
end
end Fl4Proofs.P3.SInvF
end

/-! ## from Fl4Proofs.P3.SpecInvSlKT -/
section
open Classical
namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU
section
set_option maxHeartbeats 2000000
/-- **ScKindR at boot**: every cap of `σB` is null. -/
theorem boot_scKindR_B : ScKindR (σB (Z := Unit)) := by
  intro s r b s' c' h1 _ _
  exfalso
  have hc : capOpt ((σB (Z := Unit)).kheap s.1) s.2 = some (.schedContextCap r b) := by
    rw [← vfh_capAt]; exact h1
  obtain ⟨o, l⟩ := s
  dsimp only at hc
  simp only [σB, kheapB, Function.update_apply] at hc
  split_ifs at hc <;>
    first
    | (simp [capOpt] at hc; done)
    | (simp only [capOpt] at hc; done)
    | (simp only [capOpt, emptyCnode] at hc; split_ifs at hc <;> simp_all; done)
    | (simp only [capOpt, tcbCnodeMap, Function.update_apply] at hc; split_ifs at hc <;> simp_all; done)
end
end Fl4Proofs.P3.SInvL
end

/-! ## from Fl4Proofs.P3.SpecInvAll -/
section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec
section
set_option maxHeartbeats 1000000
/-- **valid_idle at boot**: the idle TCB / SC of `kheapB`. -/
theorem boot_validIdle_B : SInvI.ValidIdle (σB (Z := Unit)) := by
  obtain ⟨x0, h0, -⟩ := SInvB.initKheap_idleThread_B
  unfold SInvI.ValidIdle SInvI.VI SInvI.VIT
  refine ⟨rfl, rfl, fun e => absurd e Bool.false_ne_true, ⟨x0, h0⟩, ⟨_, 0, SInvV.initKheap_idleSc_B⟩, ?_⟩
  intro p o hp
  change kheapB p = some o at hp
  change SInvI.ObjOK idleThreadPtr idleScPtr idleThreadPtr p o
  cases o with
  | tcb x =>
    obtain ⟨rfl, -⟩ := SInvB.init_tcb_B hp
    unfold kheapB at hp
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self] at hp
    cases hp
    exact ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun e => absurd rfl e, fun _ => Option.some_ne_none _⟩
  | schedContext sc n =>
    obtain ⟨rfl, -, -⟩ := SInvB.init_sc_B hp
    rw [SInvV.initKheap_idleSc_B] at hp
    cases hp
    exact ⟨fun _ => ⟨rfl, rfl, by unfold validSchedContextSize minSchedContextBits untypedMaxBits; omega⟩,
      fun e => absurd rfl e⟩
  | endpoint ep =>
    exfalso
    unfold kheapB at hp
    simp only [Function.update_apply] at hp
    split_ifs at hp <;> cases hp
  | notification nt =>
    exfalso
    unfold kheapB at hp
    simp only [Function.update_apply] at hp
    split_ifs at hp <;> cases hp
  | _ => trivial
end
end Fl4Proofs.P3.SInvAll
end

section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec
section
set_option maxHeartbeats 1000000
/-- **IfLiveT at boot**: the only TCB is the idle thread, which is not live. -/
theorem boot_ifLiveT_B : SInv.IfLiveT (σB (Z := Unit)) := by
  intro t y ht hl
  change kheapB t = some (.tcb y) at ht
  obtain ⟨rfl, -⟩ := SInvB.init_tcb_B ht
  unfold kheapB at ht
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self] at ht
  cases ht
  exact False.elim hl
end
end Fl4Proofs.P3.SInvAll
end

section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec
section
set_option maxHeartbeats 1000000
/-- **NtfnScB at boot** (no notification exists). -/
theorem boot_ntfnScB_B : SInvL.NtfnScB (σB (Z := Unit)) := by
  intro n ntf c hn _
  exfalso
  change kheapB n = some (.notification ntf) at hn
  unfold kheapB at hn
  simp only [Function.update_apply] at hn
  split_ifs at hn <;> cases hn
end
end Fl4Proofs.P3.SInvAll
end

section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec
section
set_option maxHeartbeats 1000000
/-- **CurScT at boot**: the idle thread is bound to the idle SC, `cur_sc`. -/
theorem boot_curScT_B : SInvQ.CurScT (σB (Z := Unit)) := by
  intro x hx
  change kheapB idleThreadPtr = some (.tcb x) at hx
  exact (SInvB.init_tcb_B hx).2
end
end Fl4Proofs.P3.SInvAll
end

section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec
section
set_option maxHeartbeats 1000000
/-- **`SInvA` at Fl4Spec's initial state** (non-vacuity of the bundle only). -/
theorem boot_sinvA_B : SInvA (σB (Z := Unit)) where
  vfh := SInv.boot_vfhAll_B
  cnDom := SInv.boot_cnDom_B
  fts := SInv.boot_faultTcbsS_B
  nqb := SInv.boot_nqb_B
  ns := SInv.boot_nativeScope_B
  sg := SInvG.boot_specGlob_B.1
  idleOut := SInvG.boot_specGlob_B.2
  dom := SInvDom.domListOK_init_B
  vim := SInvV.boot_vim_B
  vih := SInvV.boot_vih_B
  vmt := SInvV.boot_vmt_B
  ut := SInvU.boot_utInv3_B
  nq := SInv.boot_ntfnQB_B
  epq := SInv.boot_epQB_B
  live := boot_ifLiveT_B
  vi := boot_validIdle_B
  ft := SInvF.boot_ft_B
  sl := ⟨⟨SInvL.boot_scLiveT_B, SInvL.boot_idleScOutV_B, boot_ntfnScB_B, SInvB.boot_scInv_B⟩, SInvL.boot_scKindR_B⟩
  cs := boot_curScT_B
end
end Fl4Proofs.P3.SInvAll
end

/-! ## from Fl4Proofs.P3.SpecInvAllC -/
section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec
section
set_option maxHeartbeats 1000000
theorem boot_ctExit_B : CtExit (σB (Z := Unit)) := by
  obtain ⟨x0, h0, -⟩ := SInvB.initKheap_idleThread_B
  refine ⟨x0, h0, Or.inr ?_⟩
  have h1 := h0
  unfold kheapB at h1
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self] at h1
  cases h1
  rfl
end
end Fl4Proofs.P3.SInvAll
end

section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec
section
set_option maxHeartbeats 1000000
theorem boot_onlyIdle_B : OnlyIdle (σB (Z := Unit)) := by
  intro t x ht _
  change kheapB t = some (.tcb x) at ht
  exact (SInvB.init_tcb_B ht).1
end
end Fl4Proofs.P3.SInvAll
end

section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec
section
set_option maxHeartbeats 1000000
theorem boot_sinvA'_B : SInvA' (σB (Z := Unit)) := ⟨boot_sinvA_B, boot_ctExit_B⟩
end
end Fl4Proofs.P3.SInvAll
end

/-! ## from Fl4Proofs.P3.SpecInvAllB -/
section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec
section
/-- **`SInvB` at boot** (non-vacuity). -/
theorem boot_sinvB_B : SInvB (σB (Z := Unit)) := ⟨boot_sinvA'_B, boot_onlyIdle_B⟩
end
end Fl4Proofs.P3.SInvAll
end

/-! ## from Fl4Proofs.P3.SpecInvCqP3 -/
section
open Classical
namespace Fl4Proofs.P3.SInvQ.P19
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL
section
/-- CurScT at boot: the idle thread is bound to the idle SC, `cur_sc`. -/
theorem boot_curScT'_B : CurScT (σB (Z := Unit)) := by
  intro x hx
  change kheapB idleThreadPtr = some (.tcb x) at hx
  exact (SInvB.init_tcb_B hx).2
end
end Fl4Proofs.P3.SInvQ.P19
end

section
open Classical
namespace Fl4Proofs.P3.SInvQ.P19
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL
section
/-- **ctq5's `EX` at boot.** -/
theorem boot_ex_B : EX (σB (Z := Unit)) :=
  ⟨boot_schedQ_B, ⟨fun _ _ h => by simp [σB] at h, ⟨fun _ h => by simp [σB] at h, boot_curScT'_B⟩⟩⟩
end
end Fl4Proofs.P3.SInvQ.P19
end

section
open Classical
namespace Fl4Proofs.P3.SInvQ.P19
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL
section
/-- **The ready-queue bundle at boot**: `EX`, `RB` and `T4`. -/
theorem boot_tq_B : EX (σB (Z := Unit)) ∧ RB (σB (Z := Unit)) ∧ T4 (σB (Z := Unit)) :=
  ⟨boot_ex_B, boot_rb_B true, boot_t4_B⟩
end
end Fl4Proofs.P3.SInvQ.P19
end

/-! ## from Fl4Proofs.P3.SpecInvAllQ -/
section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec Fl4Proofs.P3.SInvQ
section
/-- **`SInvCQ` at boot.** -/
theorem boot_sinvCQ_B : SInvCQ (σB (Z := Unit)) := ⟨boot_sinvB_B, P19.boot_tq_B⟩
end
end Fl4Proofs.P3.SInvAll
end

section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec Fl4Proofs.P3.SInvQ
section
/-- **`SInvC` at boot** (`boot_rpos_B`). -/
theorem boot_sinvC_B : SInvC (σB (Z := Unit)) := ⟨boot_sinvCQ_B, SInvE.boot_rpos_B⟩
end
end Fl4Proofs.P3.SInvAll
end

/-! ## from Fl4Proofs.P3.SpecInvAllR -/
section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec
section
/-- **`RS` at boot** (`σB`'s action is `resumeCurThread`). -/
theorem boot_rs_B : SInvQ.RS (σB (Z := Unit)) := rfl
end
end Fl4Proofs.P3.SInvAll
end

section
open Classical
namespace Fl4Proofs.P3.SInvAll
open Fl4Spec
section
/-- **`SInvCR` at boot.** -/
theorem boot_sinvCR_B : SInvCR (σB (Z := Unit)) := ⟨boot_sinvCQ_B, boot_rs_B⟩
end
end Fl4Proofs.P3.SInvAll
end

/-! ## from Fl4Proofs.P3.SpecInvRd8eC -/
section
open Classical
namespace Fl4Proofs.P3.SInvR.B8e
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d
section
set_option maxHeartbeats 1000000
/-- **`BlockedScActive` at boot** (non-vacuity of the entry hypothesis): the
idle thread is the only TCB (state `IdleThreadState`, not ipc-queued) and the
idle SC the only SC (empty reply stack). -/
theorem boot_bsa_B : Sched.BlockedScActive (σB (Z := Unit)) := by
  refine ⟨fun p y n t x hp hyt hx hq => ?_, fun p y n hp hr => ?_⟩
  · have hx' : kheapB t = some (.tcb x) := hx
    rw [init_tcbSt_B hx'] at hq
    cases hq
  · have hy' : kheapB p = some (.schedContext y n) := hp
    by_cases e : p = idleScPtr
    · subst e
      rw [SInvV.initKheap_idleSc_B] at hy'
      cases hy'
      exact absurd rfl hr
    · exfalso
      unfold kheapB at hy'
      simp only [Function.update_apply, e, if_false] at hy'
      split_ifs at hy' <;> cases hy'
end
end Fl4Proofs.P3.SInvR.B8e
end

/-! ## from Fl4Proofs.P3.SpecInvRd8nC -/
section
open Classical
namespace Fl4Proofs.P3.SInvR.B8n
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8j Fl4Proofs.P3.SInvR.A12b
section
set_option maxHeartbeats 1000000
/-- **`VB` at boot**: no TCB is runnable. -/
theorem boot_vb_B : VB (σB (Z := Unit)) := by
  intro t hs _ _
  obtain ⟨x, -, -, -, hx, -, hr, -, -, -⟩ := Sched.schedulable_inv hs
  have e := init_tcbSt_B (u := t) hx
  rw [e] at hr; simp [runnable] at hr
end
end Fl4Proofs.P3.SInvR.B8n
end

/-! ## from Fl4Proofs.P3.SpecInvRd8lD -/
section
open Classical
namespace Fl4Proofs.P3.SInvR.B8l
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif
  Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g Fl4Proofs.P3.SInvR.B8i Fl4Proofs.P3.SInvR.B8k
section
set_option maxHeartbeats 4000000
/-- **`SInvCRB` at boot** (non-vacuity). -/
theorem boot_sinvCRB_B : SInvCRB (σB (Z := Unit)) := ⟨SInvAll.boot_sinvCR_B, B8e.boot_bsa_B⟩
end
end Fl4Proofs.P3.SInvR.B8l
end

/-! ## from Fl4Proofs.P3.SpecInvRd8vC -/
section
open Classical
namespace Fl4Proofs.P3.SInvR.B8v
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8q Fl4Proofs.P3.SInvR.B8s
section
set_option maxHeartbeats 1000000
variable {E : ObjRef → Prop}
/-- **`SInvCRBV` at boot** (non-vacuity). -/
theorem boot_sinvCRBV_B : SInvCRBV (σB (Z := Unit)) := ⟨B8l.boot_sinvCRB_B, B8n.boot_vb_B⟩
end
end Fl4Proofs.P3.SInvR.B8v
end

/-! ## from Fl4Proofs.P3.SpecInvRd8wB -/
section
open Classical
namespace Fl4Proofs.P3.SInvR.B8w
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif
open Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19
section
set_option maxHeartbeats 1000000
/-- **`SInvW` at boot** (non-vacuity only). -/
theorem boot_sinvW_B : SInvW (σB (Z := Unit)) :=
  ⟨B8v.boot_sinvCRBV_B, boot_rdy_B, SInvV.boot_offReady_B, boot_cAx_B⟩
end
end Fl4Proofs.P3.SInvR.B8w
end

/-! ## from Fl4Proofs.P3.XTopJointKEntry35 -/
section
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.SInvR.G4
open Fl4Spec Fl4Proofs.P3.SInvR.B8w
section
/-- `SInvX` at boot (non-vacuity only; G4 starts from any `SInvX` state). -/
theorem boot_sinvX_B : SInvX (σB (Z := Unit)) := ⟨boot_sinvW_B, SInvE.boot_rpos_B⟩
end
end Fl4Proofs.P3.SInvR.G4
end

/-! ## from Fl4Proofs.P3.SpecInvIoPortsS -/
section
open Classical
namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom
section
set_option maxHeartbeats 1000000
theorem boot_noIo_B (f l : IoPort) : ¬ Has (σB (Z := Unit)) f l := by
  rintro ⟨p, cref, hc⟩
  simp only [σB, kheapB, Function.update_apply] at hc
  split_ifs at hc <;>
    first
    | (simp [capOpt] at hc; done)
    | (simp only [capOpt] at hc; done)
    | (simp only [capOpt, emptyCnode] at hc; split_ifs at hc <;> simp_all; done)
    | (simp only [capOpt, tcbCnodeMap, Function.update_apply] at hc; split_ifs at hc <;> simp_all; done)
end
end Fl4Proofs.P3.SInvIo
end

section
open Classical
namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom
section
set_option maxHeartbeats 1000000
theorem boot_IOI_B : IOI (σB (Z := Unit)) :=
  ⟨fun f l hh => absurd hh (boot_noIo_B f l), fun f l _ _ hh => absurd hh (boot_noIo_B f l)⟩
end
end Fl4Proofs.P3.SInvIo
end

/-! ## from Fl4Proofs.P3.XTopJointKEntry37E -/
section
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3
/-- The spec's initial state holds no IO-port cap (non-vacuity check, INV-PLAN lead decision). -/
theorem boot_ioi_B : SInvR.G5.SpecIoP (σB (Z := Unit)) ∧ IoNoOverlap (σB (Z := Unit)) :=
  ioi_iff.1 ⟨fun f l hh => absurd hh (boot_noIo_B f l), fun f l _ _ hh => absurd hh (boot_noIo_B f l)⟩
end Fl4Proofs.P3.SInvIo
end

/-! ## from Fl4Proofs.P3.SpecInvGpm -/
section
open Classical
namespace Fl4Proofs.P3.SInvGp
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvG
section
theorem boot_gpmOut_B : GpmOutV (σB (Z := Unit)) := boot_irqOut_B _
end
end Fl4Proofs.P3.SInvGp
end

/-! ## from Fl4Proofs.P3.SpecInvSiE -/
section
open Classical
namespace Fl4Proofs.P3.SInvIV
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvG
section
set_option maxHeartbeats 1000000
variable {N : Irq → ObjRef} {t : ObjRef}
/-- Boot (non-vacuity only: the initial state holds null caps). -/
theorem boot_idleVtS_B : IdleVtS (σB (Z := Unit)) := fun _ ha => init_capAt_B (sl := ((σB (Z := Unit)).idleThread, tcbCnodeIndex 1)) ha
end
end Fl4Proofs.P3.SInvIV
end

/-! ## from Fl4Proofs.P3.SpecInvNativeScopeBridge -/
section
open Classical
namespace Fl4Proofs.P3.SInv
/-- NativeScope at boot, in IpcLeaves' form. -/
theorem boot_nativeScope'_B : Fl4Proofs.P3.Endp.NativeScope (σB (Z := Unit)) := boot_nativeScope_B
end Fl4Proofs.P3.SInv
end

/-! ## from Fl4Proofs.P3.SpecInvYieldScopeT -/
section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
set_option maxHeartbeats 1000000
set_option maxErrors 2000
variable {L : List ObjRef}
/-- **YieldScope at boot**: the initial state `σB`. -/
theorem boot_yieldScope_B : YieldScopeS (σB (Z := Unit)) := by
  intro p x hp
  simp only [σB, kheapB, Function.update_apply] at hp
  split_ifs at hp <;> first | (cases hp; done) | (cases hp; simp [ysQ, notRecvSt]) | simp_all [ysQ, notRecvSt]
end
end Fl4Proofs.P3.SInv
end

/-! ## from Fl4Proofs.P3.SpecInvYieldScopeH -/
section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
set_option maxHeartbeats 1000000
set_option maxErrors 2000
variable {L : List ObjRef}
/-- **The entry half at boot**: the initial state's current thread does not yield. -/
theorem boot_curYieldNone_B : CurYieldNone (σB (Z := Unit)) := by
  intro x hp
  simp only [σB, kheapB, Function.update_apply] at hp
  split_ifs at hp <;> first | (cases hp; done) | (cases hp; rfl)
end
end Fl4Proofs.P3.SInv
end

/-! ## from Fl4Proofs.P3.JYieldScope -/
section
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
section
/-- The pair at boot. -/
theorem boot_yieldScope'_B : SInv.YieldScopeS (σB (Z := Unit)) ∧
    SInv.CurYieldNone (σB (Z := Unit)) :=
  ⟨SInv.boot_yieldScope_B, SInv.boot_curYieldNone_B⟩
end
end Fl4Proofs.P3.SInvR.G5
end

/-! ## from Fl4Proofs.P3.SpecInvYieldBlockT -/
section
open Classical
namespace Fl4Proofs.P3.SInv
open Fl4Spec
section
set_option maxHeartbeats 1000000
set_option maxErrors 2000
variable {L : List ObjRef}
/-- **YieldBlock at boot**: the initial state `σB`. -/
theorem boot_yieldBlock_B : YieldBlockS (σB (Z := Unit)) := by
  intro p x hp
  simp only [σB, kheapB, Function.update_apply] at hp
  split_ifs at hp <;> first | (cases hp; done) | (cases hp; simp [ybQ, notBlkSt]) | simp_all [ybQ, notBlkSt]
end
end Fl4Proofs.P3.SInv
end

/-! ## from Fl4Proofs.P3.JYieldBlock -/
section
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4
section
theorem boot_yieldBlock'_B : SInv.YieldBlockS (σB (Z := Unit)) ∧
    SInv.CurYieldNone (σB (Z := Unit)) :=
  ⟨SInv.boot_yieldBlock_B, SInv.boot_curYieldNone_B⟩
end
end Fl4Proofs.P3.SInvR.G5
end


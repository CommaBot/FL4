/-
P3x for virtualization, spec side (line virt, gen 3; proofs/VIRT-PLAN.md §10 "Remaining (R7)" (b)):
**`recDelV = recDel` and `capRevokeV = capRevoke` on states without virtualization caps or VCPU objects**.

Spec: `Fl4Spec/Ext/VirtFinalise` (`finaliseCapV`, `recDelFV` / `recDelV`, `capDeleteV`, `capRevokeFV` /
`capRevokeV`: l4v `CSpace_A.rec_del` / `cap_delete` / `cap_revoke` with FL4's finalisation hooks) against the
ported `Fl4Spec/CSpace` (`recDelF` / `recDel`, `capDelete`, `capRevokeF` / `capRevoke`). Nothing of the port
changes.

* `NV σ := NVC σ ∧ NVV σ`: no slot holds a virtualization cap (VirtNvCaps) and no object is a VCPU (`NVV`: the
  object-type family of VirtTyK1..K3 at "type ≠ VCPU"). `nv_of_noVirt`: `NoVirtCaps ∧ NoVirtObjects` gives it.
* Kept by the ported deletion (the preservation half of R7 (b)): `nv_recDel`, `nv_capDelete`, `nv_capRevoke`, and
  every step `rec_del` and `cap_revoke` take (`nvc_*` / `ty_*` frames: `get_cap`, `is_final_cap`,
  `finalise_cap`, `set_cap` of a remainder, `preemption_point`, `cap_swap_for_delete`, `empty_slot`,
  `select_ext`, the recursive calls).
* `finaliseCapV_agree`: on an `NVV` state `finaliseCapV` of a non-virtualization cap is `finaliseCap` (a thread
  cap's `vcpuDetach` finds no VCPU; `ioPortRevoke` is the owner adapter's no-op; the other hooked caps are
  virtualization caps).
* Generic least-fixed-point agreement `lfp_agree`: two monotone functionals (`NDMono`) whose steps agree from
  every `I` state, given arguments that agree on `I` states and keep `I`, have least fixed points that agree on
  `I` states, as soon as the first one's keeps `I`. (`lfp_prefixed`: a monotone functional's `NonDet.lfp` is a
  prefixed point.) Monotonicity: `recDelF_mono`, `recDelFV_mono`, `capRevokeF_mono`, `capRevokeFV_mono`.
* **`recDelV_eq`**, `capDeleteV_eq`, **`capRevokeV_eq`**: at every `NV` state the extended operation has the
  ported one's outcomes and failure flag.

No premises beyond the state fact `NV` (or `NoVirtCaps ∧ NoVirtObjects`, `nv_of_noVirt`). No [J]/[P]/[W]; new
file only.
-/
import Fl4Proofs.P3.VirtR7d
import Fl4Proofs.P3.VirtTyK3
import Fl4Proofs.P3.VirtNvCaps
open Classical

namespace Fl4Proofs.P3.VirtR7b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvTY
open Fl4Proofs.P3.SInvV (hv_preemptionPoint hv_getCap hv_selectExt hv_isFinalCap vih_mem_getCap)
open Fl4Proofs.P3.VirtR7d (nd_bind_congr_on nd_bind_eq_of)

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Generic: least fixed points that agree on an invariant -/

section Gen
variable {σ α ι : Type}

/-- Every outcome of `m` from an `I` state is an `I` state. -/
def Pres (I : σ → Prop) {β : Type} (m : NonDet σ β) : Prop := ∀ s, I s → ∀ x ∈ (m s).1, I x.2

/-- A functional monotone in its argument. -/
def NDMono (F : (ι → NonDet σ α) → ι → NonDet σ α) : Prop :=
  ∀ f g : ι → NonDet σ α, (∀ i s, f i s ≤ g i s) → ∀ i s, F f i s ≤ F g i s

/-- A monotone functional's `lfp` is a prefixed point. -/
theorem lfp_prefixed (F : (ι → NonDet σ α) → ι → NonDet σ α) (hm : NDMono F) (i : ι) (s : σ) :
    F (NonDet.lfp F) i s ≤ NonDet.lfp F i s := by
  let S := {f : ι → σ → Set (α × σ) × Prop | ∀ k t, F f k t ≤ f k t}
  have h := @le_sInf (ι → σ → Set (α × σ) × Prop) _ S (F (NonDet.lfp F))
    (fun f hf k t => (hm _ _ (fun i s => ik_lfp_le F f hf i s) k t).trans (hf k t))
  exact h i s

/-- **Least fixed points agreeing on an invariant** (module docstring). -/
theorem lfp_agree (I : σ → Prop) (F G : (ι → NonDet σ α) → ι → NonDet σ α) (hmF : NDMono F) (hmG : NDMono G)
    (hPF : ∀ i, Pres I (NonDet.lfp F i))
    (hag : ∀ f g : ι → NonDet σ α, (∀ i, Pres I (f i)) → (∀ i, Pres I (g i)) → (∀ i s, I s → f i s = g i s) →
      ∀ i s, I s → F f i s = G g i s) (i : ι) (s : σ) (hs : I s) :
    NonDet.lfp G i s = NonDet.lfp F i s := by
  -- `lfp G ≤ lfp F` on `I` states
  have hA : ∀ i s, I s → NonDet.lfp G i s ≤ NonDet.lfp F i s := by
    intro i s hs
    let g : ι → NonDet σ α := fun k t => if I t then NonDet.lfp F k t else ⊤
    have hgI : ∀ k t, I t → g k t = NonDet.lfp F k t := fun k t ht => by simp only [g, if_pos ht]
    have hgp : ∀ k, Pres I (g k) := fun k t ht x hx => by
      rw [hgI k t ht] at hx; exact hPF k t ht x hx
    have hg : ∀ k t, G g k t ≤ g k t := by
      intro k t
      by_cases ht : I t
      · rw [← hag (NonDet.lfp F) g hPF hgp (fun k t ht => (hgI k t ht).symm) k t ht, hgI k t ht]
        exact lfp_prefixed F hmF k t
      · simp only [g, if_neg ht]; exact le_top
    have h := ik_lfp_le G g hg i s
    rwa [hgI i s hs] at h
  have hPG : ∀ i, Pres I (NonDet.lfp G i) := fun i t ht x hx => hPF i t ht x ((hA i t ht).1 hx)
  -- `lfp F ≤ lfp G` on `I` states
  have hB : NonDet.lfp F i s ≤ NonDet.lfp G i s := by
    let f : ι → NonDet σ α := fun k t => if I t then NonDet.lfp G k t else ⊤
    have hfI : ∀ k t, I t → f k t = NonDet.lfp G k t := fun k t ht => by simp only [f, if_pos ht]
    have hfp : ∀ k, Pres I (f k) := fun k t ht x hx => by
      rw [hfI k t ht] at hx; exact hPG k t ht x hx
    have hf : ∀ k t, F f k t ≤ f k t := by
      intro k t
      by_cases ht : I t
      · rw [hag f (NonDet.lfp G) hfp hPG (fun k t ht => hfI k t ht) k t ht, hfI k t ht]
        exact lfp_prefixed G hmG k t
      · simp only [f, if_neg ht]; exact le_top
    have h := ik_lfp_le F f hf i s
    rwa [hfI i s hs] at h
  exact le_antisymm (hA i s hs) hB

/-! ### Monotonicity and congruence of binds -/

theorem nd_le_bind {β γ : Type} {m1 m2 : NonDet σ β} {k1 k2 : β → NonDet σ γ} (hm : ∀ s, m1 s ≤ m2 s)
    (hk : ∀ a s, k1 a s ≤ k2 a s) (s : σ) : (m1 >>= k1) s ≤ (m2 >>= k2) s := by
  rw [nd_bind_apply, nd_bind_apply]
  obtain ⟨h1, h2⟩ := hm s
  refine ⟨fun r ⟨x, hx, hr⟩ => ⟨x, h1 hx, (hk x.1 x.2).1 hr⟩, ?_⟩
  rintro (h | ⟨x, hx, h⟩)
  · exact Or.inl (h2 h)
  · exact Or.inr ⟨x, h1 hx, (hk x.1 x.2).2 h⟩

theorem nde_le_bind {ε β γ : Type} {m1 m2 : NonDetE σ ε β} {k1 k2 : β → NonDetE σ ε γ}
    (hm : ∀ s, ExceptT.run m1 s ≤ ExceptT.run m2 s) (hk : ∀ a s, ExceptT.run (k1 a) s ≤ ExceptT.run (k2 a) s)
    (s : σ) : ExceptT.run (m1 >>= k1) s ≤ ExceptT.run (m2 >>= k2) s := by
  rw [ExceptT.run_bind, ExceptT.run_bind]
  refine nd_le_bind hm (fun e t => ?_) s
  cases e with
  | error e => exact le_rfl
  | ok a => exact hk a t

theorem nde_le_ite {ε β : Type} (p : Prop) [Decidable p] {a1 a2 b1 b2 : NonDetE σ ε β}
    (ha : ∀ s, ExceptT.run a1 s ≤ ExceptT.run a2 s) (hb : ∀ s, ExceptT.run b1 s ≤ ExceptT.run b2 s) (s : σ) :
    ExceptT.run (if p then a1 else b1) s ≤ ExceptT.run (if p then a2 else b2) s := by
  by_cases h : p
  · rw [if_pos h, if_pos h]; exact ha s
  · rw [if_neg h, if_neg h]; exact hb s

/-- Binds agree at `s` when their heads do and their continuations agree at every outcome of the head. -/
theorem nde_bind_congr {ε β γ : Type} {m1 m2 : NonDetE σ ε β} {k1 k2 : β → NonDetE σ ε γ} {s : σ}
    (hm : ExceptT.run m1 s = ExceptT.run m2 s)
    (hk : ∀ a t, ((Except.ok a : Except ε β), t) ∈ (ExceptT.run m1 s).1 →
      ExceptT.run (k1 a) t = ExceptT.run (k2 a) t) :
    ExceptT.run (m1 >>= k1) s = ExceptT.run (m2 >>= k2) s := by
  rw [ExceptT.run_bind, ExceptT.run_bind]
  refine (nd_bind_congr_on _ _ _ s fun x hx => ?_).trans (nd_bind_eq_of hm _)
  obtain ⟨e, t⟩ := x
  cases e with
  | error e => rfl
  | ok a => exact hk a t hx

theorem run_liftE_congr {ε β : Type} {m1 m2 : NonDet σ β} {s : σ} (h : m1 s = m2 s) :
    ExceptT.run (NonDetE.liftE (ε := ε) m1) s = ExceptT.run (NonDetE.liftE m2) s := by
  unfold NonDetE.liftE
  rw [ExceptT.run_lift, ExceptT.run_lift]
  exact nd_bind_eq_of h _

theorem mem_run_liftE' {ε β : Type} {m : NonDet σ β} {s : σ} {a : β} {t : σ}
    (h : ((Except.ok a : Except ε β), t) ∈ (ExceptT.run (NonDetE.liftE m) s).1) : (a, t) ∈ (m s).1 := by
  unfold NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  obtain ⟨⟨x1, x2⟩, hx, hz⟩ := h
  simp only [Set.mem_singleton_iff, Prod.mk.injEq, Except.ok.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  exact hx

end Gen

syntax "nd_mono" term : tactic
macro_rules
  | `(tactic| nd_mono $h) => `(tactic| repeat' (first
      | exact le_rfl
      | exact $h _ _
      | (refine nde_le_bind (fun _ => le_rfl) (fun _ _ => ?_) _)
      | (refine nde_le_bind (fun _ => $h _ _) (fun _ _ => ?_) _)
      | (refine nde_le_ite _ (fun _ => ?_) (fun _ => ?_) _)
      | (unfold NonDetE.whenE)
      | split))

/-! ## The invariant -/

/-- Object types other than the VCPU. -/
abbrev NVT : TySet := fun _ t => t ≠ .aArch .aVcpu

/-- No object is a VCPU. -/
abbrev NVV (σ : State Unit) : Prop := TIn NVT σ

/-- **No virtualization cap in a slot, no VCPU object.** -/
def NV (σ : State Unit) : Prop := NVC σ ∧ NVV σ

theorem nvv_of_noVirtObjects {σ : State Unit} (h : NoVirtObjects σ) : NVV σ := by
  intro o ko hk ht
  cases ko with
  | archObj ao =>
    cases ao with
    | vcpu st => exact (h o _ hk).1 st rfl
    | dataPage dev sz => simp only [aType, aaType] at ht; split at ht <;> cases ht
    | _ => simp [aType, aaType] at ht
  | cnode sz cs => simp only [aType] at ht; split at ht <;> cases ht
  | schedContext sc n => simp only [aType] at ht; split at ht <;> cases ht
  | _ => simp [aType] at ht

theorem nv_of_noVirt {σ : State Unit} (hc : NoVirtCaps σ) (ho : NoVirtObjects σ) : NV σ :=
  ⟨nvc_of_noVirtCaps hc, nvv_of_noVirtObjects ho⟩

theorem nv_step {ε β : Type} {m : NonDetE (State Unit) ε β} (h1 : IKE NVC m) (h2 : IKE (TIn NVT) m)
    {s t : State Unit} {a : β} (hs : NV s) (hx : ((Except.ok a : Except ε β), t) ∈ (ExceptT.run m s).1) : NV t :=
  ⟨h1 s hs.1 _ hx, h2 s hs.2 _ hx⟩

theorem nv_recDel (k : RecDelCall) : Pres NV (ExceptT.run (recDel (Z := Unit) k)) :=
  fun s hs x hx => ⟨nvc_recDel k s hs.1 x hx, ty_recDel k s hs.2 x hx⟩

theorem nv_capDelete (sl : CslotPtr) : Pres NV (ExceptT.run (capDelete (Z := Unit) sl)) :=
  fun s hs x hx => ⟨nvc_capDelete sl s hs.1 x hx, ty_capDelete sl s hs.2 x hx⟩

theorem nv_capRevoke (sl : CslotPtr) : Pres NV (ExceptT.run (capRevoke (Z := Unit) sl)) :=
  fun s hs x hx => ⟨nvc_capRevoke sl s hs.1 x hx, ty_capRevoke sl s hs.2 x hx⟩

/-! ## Finalisation -/

theorem vcpuAt_nvv {σ : State Unit} (hv : NVV σ) (v : ObjRef) : vcpuAt σ v = none := by
  unfold vcpuAt
  split
  · rename_i st h; exact absurd rfl (hv v _ h)
  · rfl

theorem vcpuDetach_nvv {σ : State Unit} (hv : NVV σ) (t : ObjRef) :
    vcpuDetach (Z := Unit) t σ = ({((), σ)}, False) := by
  have ht : tcbVcpuOf σ t = none := tcbVcpuOf_none.2 fun v st h => by rw [vcpuAt_nvv hv v] at h; cases h
  unfold vcpuDetach
  rw [nd_bind_det _ _ σ none (by simp only [getTcbVcpu, NonDet.gets]; rw [ht])]
  rfl

/-- **`finaliseCapV` of a non-virtualization cap on an `NVV` state is `finaliseCap`.** -/
theorem finaliseCapV_agree {σ : State Unit} {c : Cap} (hc : ¬ IsVirtCap c) (hv : NVV σ) (fin : Bool) :
    finaliseCapV (Z := Unit) c fin σ = finaliseCap c fin σ := by
  by_cases hh : FinaliseHooked c
  · cases c with
    | threadCap t =>
      show (NonDet.when fin (vcpuDetach t) >>= fun _ => finaliseCap (.threadCap t) fin) σ = _
      refine nd_bind_det _ _ σ () ?_
      cases fin with
      | false => rfl
      | true => exact vcpuDetach_nvv hv t
    | archObjectCap a =>
      cases a with
      | ioPortCap f l =>
        show (ioPortRevoke (.ioPortCap f l) >>= fun _ => finaliseCap (.archObjectCap (.ioPortCap f l)) fin) σ = _
        rw [ioPortRevoke_eq]
        exact nd_bind_det _ _ σ () rfl
      | vcpuCap _ => exact absurd trivial hc
      | eptCap _ _ m => exact absurd trivial hc
      | pageCap _ _ _ mt _ m => cases mt <;> first | exact absurd trivial hc | cases hh
      | _ => cases hh
    | _ => cases hh
  · rw [finaliseCapV_eq c fin hh]

/-! ## `rec_del` -/

theorem recDelF_mono :
    NDMono (fun (r : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))) c => recDelF (Z := Unit) r c) := by
  intro f g hfg k s
  show ExceptT.run (recDelF (Z := Unit) f k) s ≤ ExceptT.run (recDelF (Z := Unit) g k) s
  cases k with
  | cTEDeleteCall sl e => unfold recDelF; nd_mono hfg
  | finaliseSlotCall sl e => unfold recDelF; nd_mono hfg
  | reduceZombieCall c sl e =>
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => exact le_rfl
      | succ n => cases e <;> (unfold recDelF; nd_mono hfg)
    | _ => exact le_rfl

theorem recDelFV_mono :
    NDMono (fun (r : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))) c => recDelFV (Z := Unit) r c) := by
  intro f g hfg k s
  show ExceptT.run (recDelFV (Z := Unit) f k) s ≤ ExceptT.run (recDelFV (Z := Unit) g k) s
  cases k with
  | cTEDeleteCall sl e => unfold recDelFV; nd_mono hfg
  | finaliseSlotCall sl e => unfold recDelFV; nd_mono hfg
  | reduceZombieCall c sl e =>
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => exact le_rfl
      | succ n => cases e <;> (unfold recDelFV; nd_mono hfg)
    | _ => exact le_rfl

/-- One step of `rec_del` and of the extended `rec_del` agree from an `NV` state. -/
theorem recDel_agree (f g : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hpf : ∀ i, Pres NV (f i)) (hfg : ∀ i s, NV s → f i s = g i s) (k : RecDelCall) (s : State Unit)
    (hs : NV s) : recDelF (Z := Unit) f k s = recDelFV (Z := Unit) g k s := by
  show ExceptT.run (recDelF (Z := Unit) f k) s = ExceptT.run (recDelFV (Z := Unit) g k) s
  cases k with
  | cTEDeleteCall sl e =>
    unfold recDelF recDelFV
    exact nde_bind_congr (hfg _ s hs) fun _ _ _ => rfl
  | finaliseSlotCall sl e =>
    obtain ⟨o, r⟩ := sl
    unfold recDelF recDelFV
    refine nde_bind_congr rfl fun cap t hmem => ?_
    obtain ⟨rfl, hcap⟩ := vih_mem_getCap (mem_run_liftE' hmem)
    by_cases hn : cap = .nullCap
    · rw [if_pos hn, if_pos hn]
    rw [if_neg hn, if_neg hn]
    refine nde_bind_congr rfl fun fin t2 hmem2 => ?_
    have ht2 : t2 = t := by
      have h := mem_run_liftE' hmem2
      exact (Prod.mk.inj (Set.mem_singleton_iff.1 (h : (fin, t2) ∈ ({(decide (isFinalCap' cap t), t)} : Set _)))).2
    subst ht2
    have hv : ¬ IsVirtCap cap := hs.1 (o, r) cap hcap
    refine nde_bind_congr (run_liftE_congr (finaliseCapV_agree hv hs.2 fin).symm) fun p t3 hmem3 => ?_
    have hI3 : NV t3 := nv_step (ike_liftE (nvc_finaliseCap cap fin)) (ike_liftE (ty_finaliseCap cap fin)) hs hmem3
    have hr : ¬ IsVirtCap p.1 := nv_finaliseCap_rem cap fin t2 _ (mem_run_liftE' hmem3) hv
    obtain ⟨rem, ci⟩ := p
    dsimp only at hr ⊢
    by_cases h1 : capRemoveable rem (o, r)
    · rw [if_pos h1, if_pos h1]
    rw [if_neg h1, if_neg h1]
    by_cases h2 : capCyclicZombie rem (o, r) ∧ ¬ e = true
    · rw [if_pos h2, if_pos h2]
    rw [if_neg h2, if_neg h2]
    refine nde_bind_congr rfl fun _ t4 hmem4 => ?_
    have hI4 : NV t4 := nv_step (ike_liftE (nvc_setCap _ hr)) (ike_liftE (ty_setCap _ _)) hI3 hmem4
    refine nde_bind_congr (hfg _ t4 hI4) fun _ t5 hmem5 => ?_
    have hI5 : NV t5 := hpf _ t4 hI4 _ hmem5
    refine nde_bind_congr rfl fun _ t6 hmem6 => ?_
    have hI6 : NV t6 := nv_step (hv_preemptionPoint (P := NVC)) (ty_preemptionPoint (OS := NVT)) hI5 hmem6
    exact hfg _ t6 hI6
  | reduceZombieCall c sl e =>
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases e with
        | false => rfl
        | true =>
          unfold recDelF recDelFV
          refine nde_bind_congr rfl fun _ t1 hmem1 => ?_
          have ht1 : t1 = s := (Prod.mk.inj (Set.mem_singleton_iff.1 hmem1)).2
          subst ht1
          exact nde_bind_congr (hfg _ t1 hs) fun _ _ _ => rfl
    | _ => rfl

/-- **R7 (b), `rec_del`**: on an `NV` state the extended `rec_del` is the ported one. -/
theorem recDelV_eq (k : RecDelCall) {s : State Unit} (hs : NV s) : recDelV (Z := Unit) k s = recDel k s := by
  unfold recDelV recDel
  exact lfp_agree NV _ _ recDelF_mono recDelFV_mono (fun k => nv_recDel k)
    (fun f g hf _ hfg k s hs => recDel_agree f g hf hfg k s hs) k s hs

/-- **R7 (b), `cap_delete`.** -/
theorem capDeleteV_eq (sl : CslotPtr) {s : State Unit} (hs : NV s) : capDeleteV (Z := Unit) sl s = capDelete sl s := by
  show ExceptT.run (capDeleteV (Z := Unit) sl) s = ExceptT.run (capDelete (Z := Unit) sl) s
  unfold capDeleteV capDelete
  exact nde_bind_congr (recDelV_eq _ hs) fun _ _ _ => rfl

/-! ## `cap_revoke` -/

theorem capRevokeF_mono :
    NDMono (fun (r : CslotPtr → NonDet (State Unit) (Except Unit Unit)) c => capRevokeF (Z := Unit) r c) := by
  intro f g hfg k s
  show ExceptT.run (capRevokeF (Z := Unit) f k) s ≤ ExceptT.run (capRevokeF (Z := Unit) g k) s
  unfold capRevokeF; nd_mono hfg

theorem capRevokeFV_mono :
    NDMono (fun (r : CslotPtr → NonDet (State Unit) (Except Unit Unit)) c => capRevokeFV (Z := Unit) r c) := by
  intro f g hfg k s
  show ExceptT.run (capRevokeFV (Z := Unit) f k) s ≤ ExceptT.run (capRevokeFV (Z := Unit) g k) s
  unfold capRevokeFV; nd_mono hfg

/-- One step of `cap_revoke` and of the extended `cap_revoke` agree from an `NV` state. -/
theorem capRevoke_agree (f g : CslotPtr → NonDet (State Unit) (Except Unit Unit))
    (_hpf : ∀ i, Pres NV (f i)) (hfg : ∀ i s, NV s → f i s = g i s) (sl : CslotPtr) (s : State Unit)
    (hs : NV s) : capRevokeF (Z := Unit) f sl s = capRevokeFV (Z := Unit) g sl s := by
  show ExceptT.run (capRevokeF (Z := Unit) f sl) s = ExceptT.run (capRevokeFV (Z := Unit) g sl) s
  unfold capRevokeF capRevokeFV withoutPreemption
  refine nde_bind_congr rfl fun cap t1 hmem1 => ?_
  have hI1 : NV t1 := nv_step (ike_liftE (hv_getCap (P := NVC) _)) (ike_liftE (ty_getCap _)) hs hmem1
  refine nde_bind_congr rfl fun cdt t2 hmem2 => ?_
  have hI2 : NV t2 := nv_step (ike_liftE (ik_gets _)) (ike_liftE (ik_gets _)) hI1 hmem2
  refine nde_bind_congr rfl fun d t3 hmem3 => ?_
  have hI3 : NV t3 := nv_step (ike_returnOk _) (ike_returnOk _) hI2 hmem3
  unfold NonDetE.whenE
  by_cases hc : cap ≠ .nullCap ∧ d ≠ ∅
  · rw [if_pos hc, if_pos hc]
    refine nde_bind_congr rfl fun child t4 hmem4 => ?_
    have hI4 : NV t4 := nv_step (ike_liftE (hv_selectExt (P := NVC) _ _)) (ike_liftE (ty_selectExt _ _)) hI3 hmem4
    refine nde_bind_congr rfl fun cap' t5 hmem5 => ?_
    have hI5 : NV t5 := nv_step (ike_liftE (hv_getCap (P := NVC) _)) (ike_liftE (ty_getCap _)) hI4 hmem5
    refine nde_bind_congr rfl fun _ t6 hmem6 => ?_
    have hI6 : NV t6 := nv_step (ike_assertE _) (ike_assertE _) hI5 hmem6
    refine nde_bind_congr (capDeleteV_eq child hI6).symm fun _ t7 hmem7 => ?_
    have hI7 : NV t7 := nv_capDelete child t6 hI6 _ hmem7
    refine nde_bind_congr rfl fun _ t8 hmem8 => ?_
    have hI8 : NV t8 := nv_step (hv_preemptionPoint (P := NVC)) (ty_preemptionPoint (OS := NVT)) hI7 hmem8
    exact hfg _ t8 hI8
  · rw [if_neg hc, if_neg hc]

/-- **R7 (b), `cap_revoke`**: on an `NV` state the extended `cap_revoke` is the ported one. -/
theorem capRevokeV_eq (sl : CslotPtr) {s : State Unit} (hs : NV s) : capRevokeV (Z := Unit) sl s = capRevoke sl s := by
  unfold capRevokeV capRevoke
  exact lfp_agree NV _ _ capRevokeF_mono capRevokeFV_mono (fun k => nv_capRevoke k)
    (fun f g hf _ hfg k s hs => capRevoke_agree f g hf hfg k s hs) sl s hs

end

end Fl4Proofs.P3.VirtR7b

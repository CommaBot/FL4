/-
# P2 (line hpzg, generation 7): `hSC` of the frame-cap invocation path discharged (`InvSC`)

`inv_pathsKDG2` (`P2/InvLPG.lean`) left one premise of the program family, [J] `hSC : InvSlotCNK`: at the path's
`Pre`, the plan's slot `p.slot` is a capability slot of the layout holding a CNode cap. Both halves come from what
`localinv.plan` decided at the entry:

* the CNode cap: `InvQ`'s plan (`InvPlanD`: `plan_with` of the current label on `p.slot`) at the label `InvQ`'s arm
  fixes (`InvArm`: `CNodeDelete`), and `plan_with`'s Delete branch returns a plan only for a CNode cap
  (`planDel_cnode`);
* `p.slot ∈ K.slots`: `p.slot` is the slot `localinv.plan`'s lookup of the caller's `CAP` register found (the plan's
  lookup, `hlk` below: exactly stpost gen 13's `InvLk`), and `IoPre.fin` places that lookup's slot in `K.slots`.

So for every `Q` giving `InvQ` and the plan's lookup (stpost gen 13's `InvQF := InvQ ∧ InvLk` gives it by `id`):

* `planDel_cnode`, `invQ_cnode`, **`invQ_slotCN`**, **`invSlotCNK_of`** (`InvSlotCNK` from `hQ`);
* **`inv_pathsKDG3`** / **`inv_pathsKDG3_startAt`**: `inv_pathsKDG2` with `hSC` (and `hPE`, which `InvQ`'s
  `IoPre` gives) discharged. Premises: `hA`, `hm` [P], `Q`, `hQ` (`Q` gives `InvQ` and the plan's lookup: by `id` for
  `InvQF`), `hacc` [W], `hSeen` [J], `hmv` [W], `huf` [J].

No statement of an existing declaration changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvLPG
import Fl4Proofs.P3.StPostInvAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **`plan_with` at `CNodeDelete` returns a plan only for a CNode cap** at the slot it is given. -/
theorem planDel_cnode {s : S} {t : obj.Tcb} {sl : obj.Slot} {ex : Array obj.Slot 3#usize} {p : localinv.Plan}
    (h : localinv.plan_with st s t fl4_abi.label.CNodeDelete sl ex = ok (some p)) :
    ∃ x y z w, obj.Slot.cap st sl s = ok (.CNode x y z w) := by
  unfold localinv.plan_with at h
  obtain ⟨q, -, h⟩ := bind_eq_ok h
  obtain ⟨cap, hc, h⟩ := bind_eq_ok h
  rw [if_neg lbl_del_ne_copy, if_neg lbl_del_ne_mint, if_pos rfl] at h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · rw [if_neg Bool.false_ne_true] at h
    cases ok_inj_ff h
  · cases cap <;> first
      | exact ⟨_, _, _, _, hc⟩
      | (cases ok_inj_ff eb)

variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The CNode cap at the plan's slot, from `InvQ`. -/
theorem invQ_cnode {p : localinv.Plan} {K : KLayout} {m : U64 → U64} {s : S}
    (hq : InvQ st Cs Ω Sg Ac Locks p K m s) :
    ∃ x y z w, obj.Slot.cap st p.slot s = ok (.CNode x y z w) := by
  obtain ⟨-, ⟨t, info, ex, ht, hi, hpw⟩, harm, -⟩ := hq
  rw [(harm t info ht hi).1] at hpw
  exact planDel_cnode hpw

/-- **`InvSlotCN` at a state of `InvQ` with the plan's lookup** (`hlk`: the lookup of the caller's `CAP` register
found `p.slot`). -/
theorem invQ_slotCN {p : localinv.Plan} {K : KLayout} {m : U64 → U64} {s : S}
    (hq : InvQ st Cs Ω Sg Ac Locks p K m s)
    (hlk : ∃ x, cspace.lookup_slot st s (L.curW s) (L.mem s (regA (L.curW s) layout.reg.CAP)) = ok (.Ok x) ∧
      x.slot = p.slot) :
    p.slot ∈ K.slots ∧ ∃ x y z w, obj.Slot.cap st p.slot s = ok (.CNode x y z w) := by
  obtain ⟨x, hx, e⟩ := hlk
  refine ⟨?_, invQ_cnode hq⟩
  rw [← e]
  exact (hq.1.1.fin x hx).1

/-- **`InvSlotCNK` discharged** for every `Q` giving `InvQ` and the plan's lookup (`hQ`; by `id` for stpost gen 13's
`InvQF`). -/
theorem invSlotCNK_of {p : localinv.Plan} {Q : KLayout → (U64 → U64) → S → Prop}
    (hQ : ∀ K m s, SlJAt (L := L) K s → Q K m s → InvQ st Cs Ω Sg Ac Locks p K m s ∧
      ∃ x, cspace.lookup_slot st s (L.curW s) (L.mem s (regA (L.curW s) layout.reg.CAP)) = ok (.Ok x) ∧
        x.slot = p.slot) :
    InvSlotCNK st p Q :=
  fun K m s h => invQ_slotCN (hQ K m s h.1 h.2).1 (hQ K m s h.1 h.2).2

variable {A : Type}

/-- (hpzg gen 7) **`inv_pathsKDG2` with `hSC` discharged** (and `hPE`, from `InvQ`'s `IoPre`). Premises: `hA`,
`hm` [P], `Q`, `hQ` (`Q` gives `InvQ` and the plan's lookup), `hacc` [W], `hSeen` [J], `hmv` [W], `huf` [J]. -/
noncomputable def inv_pathsKDG3 (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hQ : ∀ K m s, SlJAt (L := L) K s → Q K m s → InvQ st Cs Ω Sg Ac Locks p K m s ∧
      ∃ x, cspace.lookup_slot st s (L.curW s) (L.mem s (regA (L.curW s) layout.reg.CAP)) = ok (.Ok x) ∧
        x.slot = p.slot)
    (hacc : ∀ K m, InvAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hSeen : InvSeenRS st Locks p Q)
    (hmv : ∀ K m, InvMoveW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    E2E.Paths Unit :=
  inv_pathsKDG2 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) ar hA number p hm Q
    (fun K m s hJ hq => (hQ K m s hJ hq).1.1.1) hacc hSeen hmv huf (invSlotCNK_of hQ)

/-- (hpzg gen 7) **`StartAt` of `inv_pathsKDG3` at a chain state** (as `inv_pathsKD_startAt`). -/
theorem inv_pathsKDG3_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hQ : ∀ K m s, SlJAt (L := L) K s → Q K m s → InvQ st Cs Ω Sg Ac Locks p K m s ∧
      ∃ x, cspace.lookup_slot st s (L.curW s) (L.mem s (regA (L.curW s) layout.reg.CAP)) = ok (.Ok x) ∧
        x.slot = p.slot)
    (hacc : ∀ K m, InvAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hSeen : InvSeenRS st Locks p Q)
    (hmv : ∀ K m, InvMoveW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {A3 : Type} {Rc : S → A3 → Fl4Spec.State Unit → Prop}
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), Rc σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : Rc σ a3 τ) (a : A) (hq : Q K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (inv_pathsKDG3 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) ar hA number p hm Q hQ hacc hSeen hmv huf
      () K m hK hU) c hs μ
      ((inv_pathsKDG3 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) ar hA number p hm Q hQ hacc hSeen hmv huf
        () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨h7 σ a3 τ hR, hq⟩, hc, hl, hμ, rfl⟩

end

end Fl4Proofs.P2.PathObl

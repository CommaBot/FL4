/-
# P2 (line stpost, generation 14): a stale mapped frame cap's `unmap_page` writes nothing

`InvMapJ` (gen 13) is false at P3 states: deleting a VSpace root clears the ASID pool entry while mapped frame caps
keep their `mapped` / `asid` / `vaddr` fields (l4v's stale mapped caps), so `small_page_entry` can be `none` for a
mapped frame with a non-zero ASID. `plan_with` then takes no PTE lock, and the decode's `finalise_cap` runs
`unmap_page`, which re-walks the same ASID table / page tables. This module shows that this re-walk finds nothing
and writes nothing, given that the walk reads only gate-owned kernel words (`VsW`), unchanged between the plan and
the decode:

* `VsW K a` (aligned, `region K a = .none`, not a user word); `VsW.ioRS` (such a word is in `IoRS`), `IoPre.vs_notPreW`,
  `IoPre.vs_notIoTW` (the prefix and the caller's register / `STATE` writes miss it);
* `rdG`, `readT`: a read the store guarded to `V` answered is answered alike by any store agreeing on `V`;
* transfer of the walk from `guard st V W` at `s` to any `m'` at `x'` agreeing on `V`: `obj.ks_get.trV`,
  `vspace.asid_table.trV`, `vspace.find_asid.trV`, `vspace.find_vspace_for_asid.trV`, `vspace.entry.trV`,
  `vspace.lookup_pdpt_slot.trV`, `vspace.lookup_pd_slot.trV`, `vspace.lookup_pt_slot.trV`;
* [J] `VsRd` (the walk at `s` reads only `VsW` words: it runs alike on `guard st (VsW K) ⊥`), [J] **`InvVsJ`** (for a
  mapped small RAM frame cap with a non-zero ASID in a capability slot: `vaddr ≤ USER_TOP`, `small_page_entry` is not
  `some 0`, and `VsRd`) — replaces `InvMapJ`;
* **`unmap_nop`**: from `small_page_entry st s asid va = ok none`, `va ≤ USER_TOP` and `VsRd`, `unmap_page` on any
  store agreeing with `st` at `s` on `VsW` words returns its state and arch state unchanged;
* `FrNo m ar x mp asid va fp` (the frame finalisation makes no access: unmapped, ASID 0, or `unmap_page` a no-op).

No existing statement changes.
-/
import Fl4Proofs.P2.InvAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField)

section vs
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- A gate-owned kernel word outside every typed region: what the ASID / page-table walk reads. -/
def VsW (K : KLayout) (a : U64) : Prop := Aligned a ∧ region K a = .none ∧ a ∉ K.user

variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}
variable {Locks : S → U64 → Prop}

theorem VsW.ioRS {a : U64} (h : VsW K a) : IoRS (st := st) K Locks s a :=
  ⟨h.1, h.2.2, Or.inr (own_none h.2.1)⟩

theorem IoPre.vs_notPreW (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {a : U64} (h : VsW K a) :
    ¬ PreW (L := L) s (L.curW s) a := by
  rintro (⟨k, hk, e⟩ | e | e)
  · have ht := P.lay.tcbw _ (P.hT _ P.cT) k (by omega) (by omega)
    unfold fld at ht
    rw [← e, h.2.1] at ht
    cases ht
  · have hn := P.lay.node _ _ (P.inNode layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]))
    have hn' : region K a = OwnMap.Region.node (L.cpu s) := by rw [e]; exact hn
    rw [h.2.1] at hn'; cases hn'
  · have hn := P.lay.node _ _ (P.inNode layout.node.CONSUMED (by simp [layout.node.CONSUMED]))
    have hn' : region K a = OwnMap.Region.node (L.cpu s) := by rw [e]; exact hn
    rw [h.2.1] at hn'; cases hn'

theorem IoPre.vs_notIoTW (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {a : U64} (h : VsW K a) :
    ¬ IoTW (L.curW s) a := by
  rintro (⟨r, hr, e⟩ | e)
  · obtain ⟨k, hk, ek⟩ := regA_eq P.tA hr
    have ht := P.lay.tcbw _ (P.hT _ P.cT) k (by omega) (by omega)
    unfold fld at ht
    rw [← ek, ← e, h.2.1] at ht
    cases ht
  · have ht := P.lay.tcbw _ (P.hT _ P.cT) layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)
    unfold fld at ht
    have ht' : region K a = OwnMap.Region.tcb (L.curW s) := by rw [e]; exact ht
    rw [h.2.1] at ht'; cases ht'

end vs

section tr
variable {S : Type} {st : machine.Store S} {V W : U64 → Prop} {m' : machine.Store S} {x' s : S}

theorem rdG {a v : U64} (h : (PathObl.guard st V W).read s a = ok v) : V a ∧ st.read s a = ok v := by
  by_cases hV : V a
  · exact ⟨hV, by rw [guard_read hV] at h; exact h⟩
  · exfalso
    have e : (PathObl.guard st V W).read s a = fail .panic := by
      simp only [PathObl.guard, hV, ↓reduceIte]
    rw [e] at h
    simp at h

variable (hr : ∀ a, V a → m'.read x' a = st.read s a) (hk : m'.ks_base x' = st.ks_base s)
include hr

theorem readT {a v : U64} (h : (PathObl.guard st V W).read s a = ok v) : m'.read x' a = ok v := by
  obtain ⟨hV, e⟩ := rdG h
  rw [hr a hV, e]

theorem vspace.entry.trV {t i r : U64} (h : vspace.entry (PathObl.guard st V W) s t i = ok r) :
    vspace.entry m' x' t i = ok r := by
  unfold vspace.entry at h ⊢
  simp only [lift, bind_ok] at h ⊢
  exact readT hr h

include hk

theorem obj.ks_get.trV {o r : U64} (h : obj.ks_get (PathObl.guard st V W) s o = ok r) : obj.ks_get m' x' o = ok r := by
  unfold obj.ks_get at h ⊢
  revert h
  refine tr_bind (fun v hv _ => by rw [hk]; exact hv) (fun v _ => ?_)
  simp only [lift, bind_ok]
  exact readT hr

theorem vspace.asid_table.trV {i r : U64} (h : vspace.asid_table (PathObl.guard st V W) s i = ok r) :
    vspace.asid_table m' x' i = ok r := by
  unfold vspace.asid_table at h ⊢
  revert h
  refine tr_bind_same (fun _ _ => ?_)
  simp only [lift, bind_ok]
  refine tr_bind_same (fun _ _ => ?_)
  exact obj.ks_get.trV hr hk

theorem vspace.find_asid.trV {asid : U64} {r : core.result.Result U64 error.LookupFault}
    (h : vspace.find_asid (PathObl.guard st V W) s asid = ok r) : vspace.find_asid m' x' asid = ok r := by
  unfold vspace.find_asid at h ⊢
  revert h
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_bind (fun v hv _ => vspace.asid_table.trV hr hk hv) (fun pool _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  simp only [lift, bind_ok]
  refine tr_bind (fun v hv _ => readT hr hv) (fun _ _ h => h)

theorem vspace.find_vspace_for_asid.trV {asid : U64} {r : core.result.Result U64 error.LookupFault}
    (h : vspace.find_vspace_for_asid (PathObl.guard st V W) s asid = ok r) : vspace.find_vspace_for_asid m' x' asid = ok r := by
  unfold vspace.find_vspace_for_asid at h ⊢
  revert h
  exact tr_bind (fun v hv _ => vspace.find_asid.trV hr hk hv) (fun _ _ h => h)

omit hk in
theorem vspace.lookup_pdpt_slot.trV {pml4 va : U64} {r : core.result.Result U64 error.LookupFault}
    (h : vspace.lookup_pdpt_slot (PathObl.guard st V W) s pml4 va = ok r) : vspace.lookup_pdpt_slot m' x' pml4 va = ok r := by
  unfold vspace.lookup_pdpt_slot at h ⊢
  revert h
  refine tr_bind_same (fun _ _ => ?_)
  exact tr_bind (fun v hv _ => vspace.entry.trV hr hv) (fun _ _ h => h)

omit hk in
theorem vspace.lookup_pd_slot.trV {pml4 va : U64} {r : core.result.Result U64 error.LookupFault}
    (h : vspace.lookup_pd_slot (PathObl.guard st V W) s pml4 va = ok r) : vspace.lookup_pd_slot m' x' pml4 va = ok r := by
  unfold vspace.lookup_pd_slot at h ⊢
  revert h
  refine tr_bind (fun v hv _ => vspace.lookup_pdpt_slot.trV hr hv) (fun r0 _ => ?_)
  refine tr_bind_same (fun cf _ => ?_)
  cases cf with
  | Continue val => exact tr_bind (fun v hv _ => readT hr hv) (fun _ _ h => h)
  | Break _ => exact id

omit hk in
theorem vspace.lookup_pt_slot.trV {pml4 va : U64} {r : core.result.Result U64 error.LookupFault}
    (h : vspace.lookup_pt_slot (PathObl.guard st V W) s pml4 va = ok r) : vspace.lookup_pt_slot m' x' pml4 va = ok r := by
  unfold vspace.lookup_pt_slot at h ⊢
  revert h
  refine tr_bind (fun v hv _ => vspace.lookup_pd_slot.trV hr hv) (fun r0 _ => ?_)
  refine tr_bind_same (fun cf _ => ?_)
  cases cf with
  | Continue val => exact tr_bind (fun v hv _ => readT hr hv) (fun _ _ h => h)
  | Break _ => exact id

end tr

section nop
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- [J] **The ASID / page-table walk at `s` reads only gate-owned kernel words** (`VsW`): `find_vspace_for_asid`,
and `lookup_pt_slot` from the root it finds, run alike on the store guarded to `VsW K`. -/
def VsRd (K : KLayout) (s : S) (asid va : U64) : Prop :=
  vspace.find_vspace_for_asid (PathObl.guard st (VsW K) (fun _ => False)) s asid = vspace.find_vspace_for_asid st s asid ∧
    ∀ root, vspace.find_vspace_for_asid st s asid = ok (.Ok root) →
      vspace.lookup_pt_slot (PathObl.guard st (VsW K) (fun _ => False)) s root va = vspace.lookup_pt_slot st s root va

variable (st) in
/-- [J] (stpost gen 14) **A mapped small RAM frame cap with a non-zero ASID, at a state of `P`** (replaces the false
`InvMapJ`; holds for stale caps too): its `vaddr` is a user address, `small_page_entry` never names the PTE address 0,
and the walk reads only `VsW` words (`VsRd`). -/
def InvVsJ (K : KLayout) (P : S → Prop) : Prop :=
  ∀ s sl fp rt asid va, P s → sl ∈ K.slots →
    obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
    va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧ VsRd st K s asid va

/-- The frame finalisation makes no access: the cap is unmapped, has ASID 0, or its `unmap_page` is a no-op. -/
def FrNo (m : machine.Store S) {A : Type} (ar : machine.Arch A) (x : S) (mp : Bool) (asid va fp : U64) : Prop :=
  mp = false ∨ asid = 0#u64 ∨ ∀ a : A, vspace.unmap_page m ar x a .Small asid va fp = ok (x, a)

/-- (stpost gen 14) **A stale mapped frame cap's `unmap_page` is a no-op**: `small_page_entry` found nothing at `s`
(`vaddr ≤ USER_TOP`, so the walk failed), and `m'` at `x'` reads the walk's words as `st` at `s`. -/
theorem unmap_nop {A : Type} (ar : machine.Arch A) {K : KLayout} {m' : machine.Store S} {x' s : S}
    {asid va fp : U64} (hr : ∀ a, VsW K a → m'.read x' a = st.read s a) (hk : m'.ks_base x' = st.ks_base s)
    (hV : VsRd st K s asid va) (hva : va ≤ fl4_abi.consts.USER_TOP)
    (hn : localinv.small_page_entry st s asid va = ok none) (a : A) :
    vspace.unmap_page m' ar x' a .Small asid va fp = ok (x', a) := by
  unfold localinv.small_page_entry at hn
  obtain ⟨r, er, hn⟩ := bind_eq_ok hn
  have er' : vspace.find_vspace_for_asid m' x' asid = ok r :=
    vspace.find_vspace_for_asid.trV hr hk (by rw [hV.1]; exact er)
  unfold vspace.unmap_page
  rw [er']
  simp only [bind_ok]
  cases r with
  | Err e => rfl
  | Ok root =>
    simp only [core.result.Result.ok, bind_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch] at hn
    unfold localinv.page_entry at hn
    have hnt : ¬ va > fl4_abi.consts.USER_TOP := by
      intro hg; exact absurd hva (not_le.mpr hg)
    rw [if_neg hnt] at hn
    unfold vspace.small_page_entry at hn
    obtain ⟨r2, er2, hn⟩ := bind_eq_ok hn
    cases r2 with
    | Ok x => simp [core.result.Result.ok] at hn
    | Err e =>
      have er2' : vspace.lookup_pt_slot m' x' root va = ok (.Err e) :=
        vspace.lookup_pt_slot.trV hr (by rw [hV.2 root er]; exact er2)
      simp only [layout.paddr, bind_ok, er2']

/-- `FrNo` from the arm's disjunct at the entry `s` and the [J] facts, for a store `m'` at `x3` reading the walk's
words as `st` at `s`. -/
theorem frNo_of {A : Type} (ar : machine.Arch A) {K : KLayout} {m' : machine.Store S} {x3 s : S}
    {mp : Bool} {asid va fp : U64}
    (hm : mp = false ∨ asid = 0#u64 ∨ localinv.small_page_entry st s asid va = ok none)
    (hvs : mp = true → asid ≠ 0#u64 → va ≤ fl4_abi.consts.USER_TOP ∧ VsRd st K s asid va)
    (hr : ∀ b, VsW K b → m'.read x3 b = st.read s b) (hk : m'.ks_base x3 = st.ks_base s) :
    FrNo m' ar x3 mp asid va fp := by
  rcases hm with h0 | h0 | hn
  · exact Or.inl h0
  · exact Or.inr (Or.inl h0)
  · cases mp with
    | false => exact Or.inl rfl
    | true =>
      by_cases hA : asid = 0#u64
      · exact Or.inr (Or.inl hA)
      · obtain ⟨hva, hV⟩ := hvs rfl hA
        exact Or.inr (Or.inr (fun a' => unmap_nop ar hr hk hV hva hn a'))

end nop

end Fl4Proofs.P2.PathObl

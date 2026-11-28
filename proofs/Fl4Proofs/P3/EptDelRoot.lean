/-
P3 (line mmuAD, gen 42b3): **the delete of a slot holding a mapped EPT root cap at `VmEptState`** — FL4's
`cdt::delete(slot, true)` (cdt.rs l. 309-316: `finalise_slot_immediate`'s loop, l. 271-297, then `empty_slot`) of a
slot holding `Ept p 0 true asid va` against the spec's `capDeleteVF` (Ext/VirtKernelF: `recDelVF (CTEDeleteCall slot
True)`, `finaliseCapVF` of a level-0 `eptCap` is the ported `finaliseCap`). This is TCBSetEPTRoot's delete of the
old `SLOT_EPT` cap (tcb.rs l. 416: only a mapped level-0 `Ept` cap is ever installed there, l. 413) and the CNode
delete of such a cap.

* FL4's loop runs one round: the cap is not null, `finalise_cap` (objects.rs l. 266: `if fin { ept::finalise }`,
  remainder and cleanup `Null`), `cap_removable(Null)` (**`finalise_imm_rm`**, **`delete_rm`**).
* The spec's `rec_del` likewise (`rdvf_of_F`, **`rdvf_fin_removable`**, **`rdvf_cte_ok`**, **`capDeleteVF_ok`**: the
  `recDelFVF` analogues of P3/DelSpec's `rd_*` lemmas for `recDelF`; `finaliseCapVF_eptRoot`: a level-0 `eptCap`'s
  `finaliseCapVF` is `finaliseCap`; `ept_finRoot_null` / `ept_finRoot_false`: its outcomes return `(nullCap,
  nullCap)`, and do nothing when not final).
* The finalisation: **final** by P3/EptFinRoot's `VmEptState.finEptRoot`; **not final** a no-op on both sides
  (FL4 `fin = false`, `arch_finalise_cap _ False`) — `VmEptState.finEptRootAny`.
* The emptying: P3/XTopJointWJLEmpty's **`JAtZB.emptyL`** (gen 42b3: `emptyHypJL`'s step generalised in place to
  `JAtZB`) inside P3/DelEmpty's `empty_stepWR'`, the slot ready (`rdLO_noRefB`: an `Ept` cap names no container;
  `EmptyReady` / `TcbReady` from `JAtZB.ept_obj`; `VsPend.of_nokey`: an `Ept` cap has no VSpace key);
  **`VcpuCore.ofEmpty`** (the slot words miss every VCPU, the TCBs' VCPU / state words and the VCPU list head;
  `RngOne` by `mdbStep_rngOne`; the spec step `CnK`: VCPU objects, TCB states kept) and **`EptCore.ofEmpty`** (the
  slot words miss the tables of `X`: a slot lies in its CNode / TCB, a spec object apart from the tables,
  `EptCore.sep`; the emptied cap was an `Ept` cap, now null).
* **`VmEptState.delEptRoot`**: from `VmEptState V X XL` and a slot holding `Ept p 0 true asid va`: FL4's delete
  ends in `Ok ()` with an outcome of `capDeleteVF`, `VmEptState V X XL` at the new ghost, the slot null and every
  other slot's cap kept. Premise: `ArchRefines` [P] only (as `VmEptState.finEptRoot`). No named premise added.

`X` keeps `p` (its table outlives its last cap: an orphan, as the Architect's note on `UnmappedEmpty` allows).

(gen 42b4) `VcpuCore.ofEmpty` generalised in place to **`VcpuCore.ofSet`** (the slot null or an `Ept` cap after; the
original a corollary, statement unchanged); `EptCore.ofEmpty`'s apartness factored out as **`JAtZB.slotWd_ept`**.

(gen 42b10) `EptCore.ofEmpty` takes `hxl` (the emptied slot's cap, if an `Ept` cap, is a level-0 one: outside
`EptNamed`'s witnesses) and proves `EptCore.named`.

(gen 42b19, the Architect's goal 2) **`EptCore.ofEmpty`'s `hxl` generalised** (statement change, this module's own):
the emptied slot's cap, if a mapped non-root `Ept p lv true a v` cap, has its table `p` reached by no path at a nonzero
level (a final delete after `ept::finalise`) or another slot `y ≠ x` holds an `Ept` cap to `p` (a non-final delete);
the old premise (an `Ept` cap is level 0) implies it. `EptNamed` after by `EptNamed.keepW`: a path's witness that was
the emptied slot is replaced by the other slot's cap (`EptNamed.all` at the path: mapped, same ASID bits and address
bits; `EptCore.capL`: same level). **`VmEptState.delEptStep`**: `delEptRoot`'s body for any `Ept p l m asid va` cap,
the finalisation given as hypotheses (FL4 `ok ((Null, Null), s1, a1)`, the spec outcome of `finaliseCapVF`,
`VmEptState` after, slots and `ksb` kept, `hxl` at the finalised state); `delEptRoot` is `finEptRootAny` +
`delEptStep` (statement unchanged). The combined delete of every `Ept` cap is P3/EptFinAll's `VmEptState.delEpt`.
-/
import Fl4Proofs.P3.EptFinRoot
import Fl4Proofs.P3.XTopJointWJLEmpty
import Fl4Proofs.P3.DelSpec
import Fl4Spec.Ext.VirtKernelF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## The spec's `rec_del` with `finaliseCapVF` -/

section
open Fl4Spec Classical

/-- An outcome of a `recDelVF` call. -/
abbrev RDVF (c : RecDelCall) (σ : State Unit) (x : Except Unit (Bool × Cap) × State Unit) : Prop :=
  x ∈ ((recDelVF (Z := Unit) c).run σ).1

abbrev RDFVF := fun (r : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))) (c : RecDelCall) =>
  recDelFVF (Z := Unit) r c

/-- An outcome of `recDelFVF f` for every pre-fixed point `f` is one of `recDelVF` (`rd_of_F`'s analogue). -/
theorem rdvf_of_F {c : RecDelCall} {σ : State Unit} {x : Except Unit (Bool × Cap) × State Unit}
    (h : ∀ f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)),
      (∀ k t, RDFVF f k t ≤ f k t) → (∀ c' σ' y, RDVF c' σ' y → y ∈ (f c' σ').1) →
      x ∈ ((recDelFVF (Z := Unit) f c).run σ).1) : RDVF c σ x := by
  show x ∈ (NonDet.lfp RDFVF c σ).1
  exact lfp_mem _ fun f hf => h f hf fun c' σ' y hy => (lfp_le_prefixed _ f hf c' σ').1 hy

/-- `FinaliseSlotCall` on a cap whose `finaliseCapVF` remainder is removable (`rd_fin_removable`'s analogue). -/
theorem rdvf_fin_removable {sl : CslotPtr} {e : Bool} {σ σ1 : State Unit} {c rem cl : Cap}
    (hg : getCap (Z := Unit) sl σ = ({(c, σ)}, False)) (hc : c ≠ .nullCap)
    (hfc : ((rem, cl), σ1) ∈ (finaliseCapVF (Z := Unit) c (decide (isFinalCap' c σ)) σ).1)
    (hr : capRemoveable rem sl) :
    RDVF (.finaliseSlotCall sl e) σ (.ok (true, cl), σ1) := by
  refine rdvf_of_F fun f _ _ => ?_
  unfold recDelFVF withoutPreemption
  refine mem_bindE_ok (mem_of_run (run_liftE hg)) ?_
  simp only [hc, ↓reduceIte]
  refine mem_bindE_ok (mem_of_run (run_liftE (m := isFinalCap (Z := Unit) c) rfl)) ?_
  refine mem_bindE_ok (a := (rem, cl)) (s' := σ1) ?_ ?_
  · rw [liftE_run]; exact mem_bind_nd hfc rfl
  · rw [if_pos hr]
    exact mem_of_run (run_returnOk _ σ1)

/-- `CTEDeleteCall` after a successful `FinaliseSlotCall` (`rd_cte_ok`'s analogue). -/
theorem rdvf_cte_ok {sl : CslotPtr} {e : Bool} {σ σ1 σ2 : State Unit} {succ : Bool} {cl : Cap}
    (hf : RDVF (.finaliseSlotCall sl e) σ (.ok (succ, cl), σ1))
    (he : ((), σ2) ∈ ((NonDet.when (e = true ∨ succ = true) (emptySlot (Z := Unit) sl cl)) σ1).1) :
    ∃ v, RDVF (.cTEDeleteCall sl e) σ (.ok v, σ2) := by
  refine ⟨undefined, rdvf_of_F fun f _ hl => ?_⟩
  unfold recDelFVF withoutPreemption
  refine mem_bindE_ok (hl _ _ _ hf) ?_
  show (Except.ok undefined, σ2) ∈ ((NonDetE.liftE _ >>= fun _ => NonDetE.returnOk undefined).run σ1).1
  refine mem_bindE_ok (s' := σ2) (a := ()) ?_ (mem_of_run (run_returnOk _ σ2))
  rw [liftE_run]
  exact mem_bind_nd he rfl

/-- `capDeleteVF` from `CTEDeleteCall slot True` (`capDelete_ok`'s analogue). -/
theorem capDeleteVF_ok {sl : CslotPtr} {σ σ' : State Unit} {v : Bool × Cap}
    (h : RDVF (.cTEDeleteCall sl true) σ (.ok v, σ')) :
    (.ok (), σ') ∈ ((capDeleteVF (Z := Unit) sl).run σ).1 := by
  unfold capDeleteVF
  exact mem_bindE_ok h (mem_of_run (run_returnOk _ σ'))

/-- A level-0 `eptCap`'s `finaliseCapVF` is the ported `finaliseCap`. -/
theorem finaliseCapVF_eptRoot (p asid va : U64) (b : Bool) :
    finaliseCapVF (Z := Unit) (absCap (.Ept p 0#u64 true asid va)) b =
      finaliseCap (absCap (.Ept p 0#u64 true asid va)) b := by
  have h0 : (0#u64 : U64).val = 0 := rfl
  show (if b = true ∧ (0#u64 : U64).val ≠ 0 then _ else _) = _
  rw [if_neg (by rw [h0]; simp)]

/-- **A final mapped EPT root's `finaliseCap` returns `(nullCap, nullCap)`.** -/
theorem ept_finRoot_null {p asid va : U64} {σ : State Unit} {x : (Cap × Cap) × State Unit}
    (hx : x ∈ (finaliseCap (Z := Unit) (absCap (.Ept p 0#u64 true asid va)) true σ).1) :
    x.1 = (.nullCap, .nullCap) := by
  obtain ⟨y, -, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx]

/-- **A non-final mapped EPT root's `finaliseCap` does nothing.** -/
theorem ept_finRoot_false (p asid va : U64) (σ : State Unit) :
    finaliseCap (Z := Unit) (absCap (.Ept p 0#u64 true asid va)) false σ = ({((.nullCap, .nullCap), σ)}, False) :=
  rfl

end

/-! ## FL4's loop: one round -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **One round of `finalise_slot_immediate` on a cap whose finalisation leaves no remainder.** -/
theorem finalise_imm_rm {s : S} {a : A} {slot : obj.Slot} {c : capability.Cap} {fin : Bool} {s1 : S} {a1 : A}
    {cl : capability.Cap} (hc : capAt (L.mem s) slot = ok c) (hcn : c ≠ .Null)
    (hfin : cdt.is_final_capability st s slot = ok fin)
    (hf : objects.finalise_cap st arI s a c fin false = ok ((.Null, cl), s1, a1)) :
    cdt.finalise_slot_immediate st arI s a slot = ok (.Ok { success := true, cleanup := cl }, s1, a1) := by
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  rw [loop]
  have hf0 : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨v, hv, -⟩ := spec_exists (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64) (by simp [layout.WALK_FUEL, U64.rMax]))
  unfold cdt.finalise_slot_immediate_loop.body
  simp only [hf0, ↓reduceIte, hv, bind_ok, slot_cap_eq, hc]
  rw [cap_is_null_ne hcn]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  rw [is_final_with_cap_eq _ _ _ hc]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, hfin, hf, uncurry_apply_pair, cdt.cap_removable]

/-- **`delete(slot, true)` of such a cap**: the round, then `empty_slot` with its cleanup. -/
theorem delete_rm {s : S} {a : A} {slot : obj.Slot} {c : capability.Cap} {fin : Bool} {s1 : S} {a1 : A}
    {cl : capability.Cap} {Q : core.result.Result Unit error.Exc × S × A → Prop} (hc : capAt (L.mem s) slot = ok c)
    (hcn : c ≠ .Null) (hfin : cdt.is_final_capability st s slot = ok fin)
    (hf : objects.finalise_cap st arI s a c fin false = ok ((.Null, cl), s1, a1))
    (he : cdt.empty_slot st arI s1 a1 slot cl ⦃ q => Q (.Ok (), q) ⦄) :
    cdt.delete st arI s a slot true ⦃ r => Q r ⦄ := by
  obtain ⟨⟨s2, a2⟩, he2, hP⟩ := spec_exists he
  unfold cdt.delete
  simp only [↓reduceIte]
  rw [finalise_imm_rm arI hc hcn hfin hf]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
  rw [he2]
  simp only [bind_ok, uncurry_apply_pair]
  rw [WP.spec_ok]
  exact hP

end

/-! ## The spec's `CnK` steps keep the arch objects -/

section
open Fl4Spec

theorem cnK_arch {σ σ' : State Unit} (h : Ipc.CnK σ σ') {p : ObjRef} {ao : ArchKernelObj} :
    σ'.kheap p = some (.archObj ao) ↔ σ.kheap p = some (.archObj ao) := by
  rcases h.2 p with e | ⟨r, cs, cs', e1, e2⟩ | ⟨x, y, e1, e2, -⟩
  · rw [e]
  · rw [e1, e2]; simp
  · rw [e1, e2]; simp

theorem cnK_asid {σ σ' : State Unit} (h : Ipc.CnK σ σ') :
    σ'.archState.x64AsidTable = σ.archState.x64AsidTable := by
  have e := congrArg AbstractState.archState h.1
  exact congrArg ArchState.x64AsidTable e

theorem cnK_size {σ σ' : State Unit} (h : Ipc.CnK σ σ') :
    ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ objBits ko' = objBits ko := by
  intro o ko' hk
  rcases h.2 o with e | ⟨r, cs, cs', e1, e2⟩ | ⟨x, y, e1, e2, -⟩
  · exact ⟨ko', by rw [← e]; exact hk, rfl⟩
  · rw [e2] at hk; cases hk; exact ⟨_, e1, rfl⟩
  · rw [e2] at hk; cases hk; exact ⟨_, e1, rfl⟩

theorem cnK_rv {σ σ' : State Unit} (h : Ipc.CnK σ σ') :
    ∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM := by
  intro o x' hk hx
  rcases h.2 o with e | ⟨r, cs, cs', e1, e2⟩ | ⟨x, y, e1, e2, hxy⟩
  · exact ⟨x', by rw [← e]; exact hk, hx⟩
  · rw [e2] at hk; cases hk
  · rw [e2] at hk; cases hk; exact ⟨x, e1, by rw [← hxy.1]; exact hx⟩

theorem cnK_entry {σ σ' : State Unit} (h : Ipc.CnK σ σ') : ∀ e, GuestEntry σ' e → GuestEntry σ e := by
  rintro e ⟨hi, q, f, lo, h1, h2, h3⟩
  exact ⟨hi, q, f, lo, by rw [← cnK_asid h]; exact h1, (cnK_arch h).1 h2, h3⟩

end

/-! ## The VCPU and EPT records across `empty_slot` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- A slot word misses every VCPU of `V` (`JVLay.vap`: the slot lies in its object). -/
theorem JAtZB.slotWd_vcpu (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ)
    {b : U64} (hb : SlotWd Z.th b) : ∀ u ∈ V, b.val < u.val ∨ u.val + 32768 ≤ b.val := by
  intro u hu
  have hP := B.xtop.rel.1
  obtain ⟨y, hy, h1, h2⟩ := slotWd_range hP hb
  obtain ⟨p, k, hk, g1, g2, -⟩ := slot_in_object hP hy
  rcases (B.jvLay Jv).vap u hu p k hk with h | h <;> omega

/-- A slot word is not the VCPU list head (`TopPlaced.disj`: the head is an `OObj` kernel-global word, a slot word a
`VObj` word). -/
theorem JAtZB.slotWd_head (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : SlotWd Z.th b) :
    b ≠ P1.vHeadA st s := by
  intro e
  have hP := B.xtop.fin.1.2
  obtain ⟨y, hy, h1, h2⟩ := slotWd_range B.xtop.rel.1 hb
  have hv : VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b := vobj_of_slot B.xtop.rel.1 _ _ _ _ _ _ hy h1 h2
  have hh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
  have hO : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b := by
    refine Or.inr (Or.inl ⟨?_, ?_, Or.inl ?_⟩) <;> rw [e, hh] <;> omega
  exact hP.disj b hO hv

/-- A slot word misses the TCB words at offsets `[256, 4096)` (`SlotsApart`). -/
theorem JAtZB.slotWd_tcb (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : SlotWd Z.th b)
    {t : U64} (ht : Z.th t = some .tcb) {w : U64} (h1 : t.val + 256 ≤ w.val) (h2 : w.val + 8 ≤ t.val + 4096) :
    b ≠ w := by
  intro e
  obtain ⟨y, hy, g1, g2⟩ := slotWd_range B.xtop.rel.1 hb
  have hb8 : b.val % 8 = 0 := by
    obtain ⟨y', hy', k, hk, rfl⟩ := hb
    exact slot_word_aligned B.xtop.rel.1 hy' hk
  rcases (B.apart y hy).1 t (B.thT t ht) with h | h <;> subst e <;> omega

set_option maxHeartbeats 4000000 in
/-- **`VcpuCore` across a write of one slot `x`** (gen 42b4: `empty_slot`, or `cdt::insert` of an `Ept` cap): the
slot words written, every other slot's cap kept, `x` null or an `Ept` cap after. -/
theorem VcpuCore.ofSet (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost} {x : U64}
    (hw : P1.WritesIn st s s' (SlotWd Z.th))
    (hcp : ∀ y, IsSlot Z.th y → y ≠ x → capV (L.mem s') y = capV (L.mem s) y) (hx0 : capV (L.mem s') x = .Null ∨ ∃ p l mm a v, capV (L.mem s') x = .Ept p l mm a v)
    (hmS : MdbStep (L.mem s) Z.G (L.mem s') G') (hcn : Ipc.CnK σ σ') :
    VcpuCore (L := L) V (Z.mv G' Z.vs) H s' σ' := by
  have Ly := B.jvLay C.vm
  have Pw := B.jwPl C.vm
  have nV : ∀ u ∈ V, ∀ b, SlotWd Z.th b → b.val < u.val ∨ u.val + 32768 ≤ b.val :=
    fun u hu b hb => B.slotWd_vcpu C.vm hb u hu
  have hTc := B.ip.e.tcb
  have kTV : ∀ t, Z.th t = some .tcb → L.mem s' (tVcpuA t) = L.mem s (tVcpuA t) := fun t ht =>
    hw.mem_eq (Pw.jw _ (Or.inr (Or.inl ⟨t, ht, rfl⟩))) fun hb => B.slotWd_tcb hb ht
      (by rw [Sched.tVcpuA_val hTc (B.thT t ht)]; omega) (by rw [Sched.tVcpuA_val hTc (B.thT t ht)]; omega) rfl
  have kVT : ∀ v ∈ V, L.mem s' (vTcbA v) = L.mem s (vTcbA v) := fun v hv =>
    hw.mem_eq (Pw.jw _ (Or.inr (Or.inr ⟨v, hv, rfl⟩))) fun hb => by
      have e := lay_vTcb_val (Ly.vfit v hv).2
      rcases nV v hv _ hb with h | h <;> omega
  have kSt : ∀ t, Z.th t = some .tcb → L.mem s' (P1.stA t) = L.mem s (P1.stA t) := fun t ht =>
    hw.mem_eq (Pw.sw _ ⟨t, ht, rfl⟩) fun hb => B.slotWd_tcb hb ht
      (by rw [Sched.stA_tStA, Sched.tStA_val' (hTc t (B.thT t ht))]; omega)
      (by rw [Sched.stA_tStA, Sched.tStA_val' (hTc t (B.thT t ht))]; omega) rfl
  have hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv := fun u hu => by
    obtain ⟨vs, hvs⟩ := C.vm.spec u hu
    rw [hvs]; exact (cnK_arch hcn).2 hvs
  have hnv : ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs)) := fun p vs hp => (cnK_arch hcn).1 hp
  have E0 := C.extv
  have E' : JExtVcpu (L := L) V Z.th s' :=
    { cap := fun y hy => by
        by_cases e : y = x
        · rw [e]
          rcases hx0 with h | ⟨_, _, _, _, _, h⟩ <;> rw [h] <;> trivial
        · rw [hcp y hy e]; exact E0.cap y hy
      bnd := fun t ht => by
        rcases E0.bnd t ht with h | ⟨h1, h2⟩
        · left; rw [kTV t ht]; exact h
        · right; rw [kTV t ht]; exact ⟨h1, by rw [kVT _ h1]; exact h2⟩
      back := fun v hv => by
        rcases E0.back v hv with h | ⟨h1, h2⟩
        · left; rw [kVT v hv]; exact h
        · right; rw [kVT v hv]; exact ⟨h1, by rw [kTV _ h1]; exact h2⟩
      nz := E0.nz }
  have R' : RunVmB (L := L) Z.th s' := fun t ht h8' => by
    rw [kTV t ht]; exact C.rvm t ht (by rw [← kSt t ht]; exact h8')
  have Jv' : JVm (L := L) V H s' σ' :=
    C.vm.step (fun _ h => h) (fun _ _ => rfl) hw.1 (fun u hu => by rw [hvk u hu]; exact C.vm.spec u hu)
      (fun o ko' ho => Or.inl (cnK_size hcn o ko' ho))
  have Vl' : VList st V Z.th s' := C.vl.writes hw fun b hb => by
    refine ⟨C.vl.lw_al Ly.vfit hb, fun hWb => ?_⟩
    rcases hb with rfl | ⟨u, hu, rfl | rfl⟩
    · exact B.slotWd_head hWb rfl
    · have := lay_next_val (Ly.vfit u hu).2
      rcases nV u hu _ hWb with h | h <;> omega
    · have := lay_prev_val (Ly.vfit u hu).2
      rcases nV u hu _ hWb with h | h <;> omega
  exact ⟨E', C.vo.frame hnv,
    C.vr.frame (fun u _ vs hu => hnv _ vs hu) (v3_agreeW (L := L) hw (fun u hu => (Ly.vfit u hu).2) nV),
    fun y hy f l o hc => by
      by_cases e : y = x
      · rw [e] at hc
        rcases hx0 with h | ⟨_, _, _, _, _, h⟩ <;> rw [h] at hc <;> cases hc
      · rw [hcp y (isSlot_thTcb hy) e] at hc; exact C.noIoTcb y hy f l o hc,
    (VirtRngOne.mdbStep_rngOne hmS B.ut C.rngOne).2, R', Jv', Vl', C.vb.ofV hvk kVT⟩

/-- **`VcpuCore` across `empty_slot`** (module docstring). -/
theorem VcpuCore.ofEmpty (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost} {x : U64}
    (hw : P1.WritesIn st s s' (SlotWd Z.th))
    (hcp : ∀ y, IsSlot Z.th y → y ≠ x → capV (L.mem s') y = capV (L.mem s) y) (hx0 : capV (L.mem s') x = .Null)
    (hmS : MdbStep (L.mem s) Z.G (L.mem s') G') (hcn : Ipc.CnK σ σ') :
    VcpuCore (L := L) V (Z.mv G' Z.vs) H s' σ' :=
  C.ofSet B hw hcp (Or.inl hx0) hmS hcn

set_option maxHeartbeats 4000000 in
/-- A slot word misses every table of `X` (the slot lies in its CNode / TCB, a spec object apart from the tables:
`EptCore.sep`; gen 42b4, from `EptCore.ofEmpty`). -/
theorem JAtZB.slotWd_ept (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ) :
    ∀ b, SlotWd Z.th b → ∀ t ∈ X, b.val < t.val ∨ t.val + 4096 ≤ b.val := by
  have hP := B.xtop.rel.1
  have hR := B.xtop.rel.2.1.1
  intro b hb t ht
  obtain ⟨y, hy, h1, h2⟩ := slotWd_range hP hb
  obtain ⟨p, k, hk, g1, g2, g3⟩ := slot_in_object hP hy
  obtain ⟨es, hxe, -⟩ := C.rel.obj t ht
  have hpv : p.bv.toNat = p.val := rfl
  rcases B.thk p k hk with rfl | ⟨r, rfl⟩
  · obtain ⟨tcb, hkp, -⟩ := hR.tcb p hk
    have hne : p.bv ≠ t.bv := fun e => by rw [e, hxe] at hkp; cases hkp
    have := C.sep t ht _ _ hkp hne
    unfold EptApart at this
    have h11 : (2 : Nat) ^ Fl4Spec.objBits (.tcb tcb) = 2048 := by
      simp [Fl4Spec.objBits, Fl4Spec.tcbBits]
    rw [h11, hpv] at this
    have g3' := g3 rfl
    simp only [tcbSlots] at g3'
    omega
  · obtain ⟨cs, hkp, -⟩ := hR.cnode p r hk
    have hne : p.bv ≠ t.bv := fun e => by rw [e, hxe] at hkp; cases hkp
    have := C.sep t ht _ _ hkp hne
    unfold EptApart at this
    have h5 : (2 : Nat) ^ Fl4Spec.objBits (.cnode r cs) = objSize (.cnode r) := by
      simp only [Fl4Spec.objBits, objSize, Fl4Spec.cteLevelBits]
      ring_nf
    rw [h5, hpv] at this
    omega

set_option maxHeartbeats 4000000 in
/-- **`EptCore` across `empty_slot`** (module docstring; gen 42b19: `hxl` generalised). The emptied slot's cap, if a
mapped non-root `Ept p lv true a v` cap, names a table that is reached by no path at a nonzero level (a final delete
after `ept::finalise`: P3/EptUnmapCore's `EptCore.unmapUnreach`) or that another slot's `Ept` cap names (a non-final
delete: `ept_nonfinal_twin`); `EptNamed.all` and `EptCore.capL` make that cap the path's witness. A level-0, unmapped
or non-`Ept` cap needs nothing. -/
theorem EptCore.ofEmpty (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {s' : S} {σ' : Fl4Spec.State Unit} {x : U64}
    (hw : P1.WritesIn st s s' (SlotWd Z.th))
    (hcp : ∀ y, IsSlot Z.th y → y ≠ x → capV (L.mem s') y = capV (L.mem s) y) (hx0 : capV (L.mem s') x = .Null)
    (hcn : Ipc.CnK σ σ')
    (hxl : ∀ p lv a v, capV (L.mem s) x = .Ept p lv true a v → lv.val ≠ 0 →
      (∀ hi lo gpa l, gpa.toNat < 2 ^ 47 → l ≠ 0 → ¬ GPath σ hi lo gpa l p.bv) ∨
      ∃ y, IsSlot Z.th y ∧ y ≠ x ∧ ∃ (lv' : U64) (mm : Bool) (a' v' : U64), capV (L.mem s) y = .Ept p lv' mm a' v') :
    EptCore (L := L) X XL Z.th s' σ' := by
  have hW := B.slotWd_ept C
  have hpool : ∀ hi lo e, PoolAt σ' hi lo e → e &&& 1 = 1 → PoolAt σ hi lo e :=
    fun _ _ _ ⟨q, f, h1, h2, h3⟩ _ => ⟨q, f, by rw [← cnK_asid hcn]; exact h1, (cnK_arch hcn).1 h2, h3⟩
  refine C.frame hw hW (fun y hy p l a v mm hc => ?_) ⟨fun y hy => ?_, ⟨fun y hy p l a v hc => ?_,
    fun y hy p sz r d a v hc => ?_⟩, fun y hy p l a v hc => ?_⟩
    (fun t ht => ?_)
    (fun r l es hk => ⟨l, es, (cnK_arch hcn).1 hk⟩) (cnK_entry hcn) (cnK_size hcn) (EptSlotStep.ofOne hcp (Or.inl hx0))
    (C.named.keepW (GPath.mono' (fun hi lo e h1 h2 => Or.inl (hpool hi lo e h1 h2))
        (fun r l es hk => Or.inl ((cnK_arch hcn).1 hk)))
      (C.named.inj.mono (cnK_asid hcn) hpool) (fun hi lo gpa l u hg hp hl => ?_)
      (fun y p lv mm a v hy hc => Or.inl ?_))
  · by_cases e : y = x
    · rw [e, hx0] at hc; cases hc
    · exact ⟨hy, by rw [← hcp y hy e]; exact hc⟩
  · by_cases e : y = x
    · rw [e, hx0]; trivial
    · rw [hcp y hy e]; exact C.exte.cap y hy
  · by_cases e : y = x
    · rw [e, hx0] at hc; cases hc
    · rw [hcp y hy e] at hc; exact C.exte.vtop.1 y hy p l a v hc
  · by_cases e : y = x
    · rw [e, hx0] at hc; cases hc
    · rw [hcp y hy e] at hc; exact C.exte.vtop.2 y hy p sz r d a v hc
  · by_cases e : y = x
    · rw [e, hx0] at hc; cases hc
    · rw [hcp y hy e] at hc; exact C.exte.anz y hy p l a v hc
  · obtain ⟨es, hxe, -⟩ := C.rel.obj t ht
    rw [hxe]; exact (cnK_arch hcn).2 hxe
  · obtain ⟨y, p, lv, a', v, hy, hpu, hlv, h1, h2, h3, hc⟩ := C.named.ex hi lo gpa l u hg hp hl
    by_cases e : y = x
    · subst e
      rcases hxl p lv a' v hc (by rw [hlv]; exact hl) with hun | ⟨y', hy', hne, lv', mm, a2, v2, hc'⟩
      · exact (hun hi lo gpa l hg hl (by rw [hpu]; exact hp)).elim
      · obtain ⟨rfl, g1, g2, g3⟩ := C.named.all hi lo gpa l u hg hp hl y' p lv' mm a2 v2 hy' hpu hc'
        have e1 := C.capL y' hy' p lv' a2 v2 true hc'
        have e2 := C.capL y hy p lv a' v true hc
        exact ⟨y', p, lv', a2, v2, hy', hpu, by rw [e1, ← e2, hlv], g1, g2, g3, by rw [hcp y' hy' hne]; exact hc'⟩
    · exact ⟨y, p, lv, a', v, hy, hpu, hlv, h1, h2, h3, by rw [hcp y hy e]; exact hc⟩
  · by_cases e : y = x
    · rw [e, hx0] at hc; cases hc
    · exact ⟨y, hy, by rw [← hcp y hy e]; exact hc⟩

end

/-! ## The finalisation, final or not -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **A mapped EPT root cap's finalisation at `VmEptState`, final or not**: FL4's `finalise_cap … fin false`
returns `(Null, Null)` at a state `s1` related to an outcome `σ1` of the spec's `finaliseCapVF` at FL4's finality
(`finalHyp_full`), `VmEptState` there, the slots kept. -/
theorem VmEptState.finEptRootAny [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR)
    (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {sl : Fl4Spec.CslotPtr} {p asid va : U64} (hAs : AbsSlot Z.th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Ept p 0#u64 true asid va)) :
    ∃ fin s1 a1 σ1, cdt.is_final_capability st s (cslotAddr sl) = ok fin ∧
      objects.finalise_cap st arI s a (.Ept p 0#u64 true asid va) fin false = ok ((.Null, .Null), s1, a1) ∧
      ((.nullCap, .nullCap), σ1) ∈ (Fl4Spec.finaliseCapVF (Z := Unit) (absCap (.Ept p 0#u64 true asid va))
        (decide (Fl4Spec.isFinalCap' (absCap (.Ept p 0#u64 true asid va)) σ)) σ).1 ∧
      VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s1 a1 σ1 ∧
      SlotsSame Z.th (L.mem s) (L.mem s1) ∧ L.ksb s1 = L.ksb s := by
  have B := J.1.1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨B.xtop.rel.2.1, B.del, B.xtop.rel.2.2.1⟩
  obtain ⟨fin, hfin, hNF, -⟩ := finalHyp_full Z.th B.xtop.rel.1 s σ Z.G sl _ hDS hAs hc (fun h => by cases h)
  have hfe : fin = decide (Fl4Spec.isFinalCap' (absCap (.Ept p 0#u64 true asid va)) σ) :=
    hNF (Or.inl ⟨trivial, rfl⟩)
  rw [finaliseCapVF_eptRoot]
  cases fin with
  | true =>
    rw [← hfe]
    obtain ⟨⟨⟨rem, cl⟩, s1, a1⟩, hr, h1, h2, h3, σ1, hm, J1, hSS, hks⟩ := spec_exists (J.finEptRoot hA hDS hAs hc)
    simp only at h1 h2 h3 hm J1 hSS hks
    have hn := ept_finRoot_null hm
    simp only [Prod.mk.injEq] at hn
    have hcl : cl = .Null := (absCap_eq_null h3).1 hn.2
    have hrm : rem = .Null := h1
    subst hcl hrm
    rw [show ((.nullCap, .nullCap) : Fl4Spec.Cap × Fl4Spec.Cap) = (absCap .Null, absCap .Null) from rfl]
    exact ⟨true, s1, a1, σ1, hfin, hr, hm, J1, hSS, hks⟩
  | false =>
    rw [← hfe]
    refine ⟨false, s, a, σ, hfin, ?_, ?_, J, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    · simp [objects.finalise_cap, objects.finalise_cap_object]
    · rw [ept_finRoot_false]; exact Set.mem_singleton _

end

/-! ## The delete -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

set_option maxHeartbeats 4000000 in
/-- **The delete of a slot holding an `Ept` cap at `VmEptState`, from its finalisation** (gen 42b19: the body of
`delEptRoot`, generalised to any `Ept p l m asid va` cap): given FL4's finality `fin`, a finalisation `finalise_cap
… fin false = ok ((Null, Null), s1, a1)` whose spec outcome `σ1` is one of `finaliseCapVF` at the spec's finality,
`VmEptState` at `s1` / `σ1` with the slots and `ksb` kept, and, for a mapped non-root cap, `EptCore.ofEmpty`'s
`hxl` at `s1` / `σ1` (the table unreachable, or another slot's `Ept` cap to it), FL4's delete ends as `delEptRoot`
says. The emptying is `delEptRoot`'s (no cap kind is read but `Ept`'s object apartness and missing VSpace key). -/
theorem VmEptState.delEptStep [Fl4Proofs.P1.PlainStore st]
    {sl : Fl4Spec.CslotPtr} {p l asid va : U64} {m : Bool} (hAs : AbsSlot Z.th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Ept p l m asid va))
    (hR : StateRel Z.th (L.mem s) σ)
    {fin : Bool} {s1 : S} {a1 : A} {σ1 : Fl4Spec.State Unit}
    (hfin : cdt.is_final_capability st s (cslotAddr sl) = ok fin)
    (hf : objects.finalise_cap st arI s a (.Ept p l m asid va) fin false = ok ((.Null, .Null), s1, a1))
    (hfc : ((.nullCap, .nullCap), σ1) ∈ (Fl4Spec.finaliseCapVF (Z := Unit) (absCap (.Ept p l m asid va))
      (decide (Fl4Spec.isFinalCap' (absCap (.Ept p l m asid va)) σ)) σ).1)
    (J1 : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s1 a1 σ1)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s1)) (hks1 : L.ksb s1 = L.ksb s)
    (hxl : m = true → l.val ≠ 0 →
      (∀ hi lo gpa l', gpa.toNat < 2 ^ 47 → l' ≠ 0 → ¬ GPath σ1 hi lo gpa l' p.bv) ∨
      ∃ y, IsSlot Z.th y ∧ y ≠ cslotAddr sl ∧ ∃ (lv' : U64) (mm : Bool) (a' v' : U64), capV (L.mem s1) y = .Ept p lv' mm a' v') :
    cdt.delete st arI s a (cslotAddr sl) true ⦃ r => r.1 = .Ok () ∧
      ∃ (σ' : Fl4Spec.State Unit) (G' : MdbGhost) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        (.ok (), σ') ∈ ((Fl4Spec.capDeleteVF (Z := Unit) sl).run σ).1 ∧
        VmEptState (L := L) arI V X XL AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' r.2.1 r.2.2 σ' ∧
        capV (L.mem r.2.1) (cslotAddr sl) = .Null ∧
        (∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y) ∧
        L.ksb r.2.1 = L.ksb s ⦄ := by
  obtain ⟨⟨B1, Cv1⟩, C1⟩ := J1
  have hP := B1.xtop.rel.1
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Ept p l m asid va := by
    rw [hSS.capV hAs.isSlot]; exact capV_of_capAt hc
  have hDS1 : DState (L := L) Z.th s1 σ1 Z.G := ⟨B1.xtop.rel.2.1, B1.del, B1.xtop.rel.2.2.1⟩
  -- the slot is ready
  have hap0 := B1.ept_obj hAs.isSlot hcv1
  have hn : ∀ q, ¬ RefsObj q (capV (L.mem s1) (cslotAddr sl)) := fun q h => by rw [hcv1] at h; exact h
  have hRd : RdLX (L := L) (A := A) Z.th H Z.vx s1 a1 σ1 Z.G (cslotAddr sl) :=
    ⟨rdLO_noRefB arI (Z := Z) (G := Z.G) (V := Z.vs) B1 B1.live.1
      (EmptyReady.of_apartO (by rw [hcv1]; exact hap0)) hn (TcbReady.of_apartO (by rw [hcv1]; exact hap0)),
      fun h => VsPend.of_nokey (B1.carry.vsNamed h) (by rw [hcv1]; rfl)⟩
  -- the emptying, at `JAtZB` (`JAtZB.emptyL`)
  let W : S → A → Fl4Spec.State Unit → MdbGhost → Prop := fun s2 a2 σ2 G2 =>
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZB (L := L) arI AR (Z.mv G2 Z.vs) H Cs Ac' Lst' D' s2 a2 σ2 ∧ L.ksb s2 = L.ksb s1 ∧
      P1.WritesIn st s1 s2 (SlotWd Z.th) ∧ Ipc.CnK σ1 σ2
  let Wx : S → A → Fl4Spec.State Unit → MdbGhost → Prop := fun s2 a2 σ2 G2 =>
    s2 = s1 ∧ a2 = a1 ∧ σ2 = σ1 ∧ G2 = Z.G
  have hE : EmptyHypWR (L := L) W Wx (RdLX (L := L) (A := A) Z.th H Z.vx) Z.th := by
    intro s2 s3 a2 σ2 σ3 G2 G3 sl3 hWx hRd3 hD2 hD3 hF hes hA3 hxn hx0 hoth hmS
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hWx
    obtain ⟨Ac', Lst', D', B', hks, -, -, -, -⟩ :=
      JAtZB.emptyL arI (E0 := Z.vx) (V := Z.vs) B1 B1.live.1 B1.live.2.1 B1.live.2.2 hRd3 hD2 hD3 hF hes hA3 hxn
        hx0 hoth hmS
    exact ⟨Ac', Lst', D', B', hks, SlotFrame2.writesIn hF, emptySlot_null_nkn _ _ _ hes⟩
  have hEmp := empty_stepWR' arI W Wx (RdLX (L := L) (A := A) Z.th H Z.vx) Z.th hP (cl := .Null)
    (fun h => absurd rfl h) hE s1 a1 σ1 Z.G hDS1 ⟨rfl, rfl, rfl, rfl⟩
    (fun h => by rw [hcv1] at h; cases h) hAs (fun _ => hRd) trivial trivial
  apply delete_rm arI hc (by intro h; cases h) hfin hf
  refine WP.spec_mono hEmp ?_
  rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, hDS2, hnull, hoth, -, -, -, hmS, Ac', Lst', D', B2, hks2, hw2, hcn2⟩
  simp only at hes hDS2 hnull hoth hmS B2 hks2 hw2 hcn2 ⊢
  -- the spec's delete
  obtain ⟨c0, ac, hc0, hca, hg⟩ := hR.abs_cap hAs
  rw [hc] at hc0
  obtain rfl : (.Ept p l m asid va : capability.Cap) = c0 := eq_of_ok_eq hc0
  rw [hca.abs] at hg
  have hfr := rdvf_fin_removable (e := true) hg (by cases m <;> simp [absCap]) hfc (by simp [Fl4Spec.capRemoveable])
  obtain ⟨v, hv⟩ := rdvf_cte_ok hfr (σ2 := σ2) (by
    simp only [Fl4Spec.NonDet.when, true_or, ↓reduceIte]; exact hes)
  have hoth' : ∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem s2) y = capV (L.mem s) y := fun y hy hne => by
    exact (hoth y hy hne).trans (hSS.capV hy)
  exact ⟨by first | trivial | rfl, σ2, G2, Ac', Lst', D', capDeleteVF_ok hv,
    ⟨⟨B2, Cv1.ofEmpty B1 hw2 (fun y hy hne => hoth y hy hne) hnull hmS hcn2⟩,
      C1.ofEmpty B1 hw2 (fun y hy hne => hoth y hy hne) hnull hcn2
        (fun p' lv a' v' h hl => by
          rw [hcv1] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := capability.Cap.Ept.inj h
          exact hxl rfl hl)⟩,
    hnull, hoth', hks2.trans hks1⟩

set_option maxHeartbeats 4000000 in
/-- **The delete of a slot holding a mapped EPT root cap at `VmEptState`** (module docstring). From
`ArchRefines` [P]. Gen 42b19: `delEptStep` after `finEptRootAny`. -/
theorem VmEptState.delEptRoot [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR)
    (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {sl : Fl4Spec.CslotPtr} {p asid va : U64} (hAs : AbsSlot Z.th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Ept p 0#u64 true asid va)) :
    cdt.delete st arI s a (cslotAddr sl) true ⦃ r => r.1 = .Ok () ∧
      ∃ (σ' : Fl4Spec.State Unit) (G' : MdbGhost) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        (.ok (), σ') ∈ ((Fl4Spec.capDeleteVF (Z := Unit) sl).run σ).1 ∧
        VmEptState (L := L) arI V X XL AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' r.2.1 r.2.2 σ' ∧
        capV (L.mem r.2.1) (cslotAddr sl) = .Null ∧
        (∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y) ∧
        L.ksb r.2.1 = L.ksb s ⦄ := by
  obtain ⟨fin, s1, a1, σ1, hfin, hf, hfc, J1, hSS, hks1⟩ := J.finEptRootAny hA hAs hc
  exact VmEptState.delEptStep arI hAs hc J.1.1.xtop.rel.2.1.1 hfin hf hfc J1 hSS hks1
    (fun _ hl => (hl rfl).elim)
end

end

end Fl4Proofs.P3

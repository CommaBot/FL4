/-
# P2 (line hpzg, generation 6): the frame-cap invocation body pruned to its CNode decode (`InvPrune`)

`IsProg` of `syscall.handle_invocation_local` with a `NoZero` tree is false (`P2/InvProgSrc.lean`): on an
arbitrary store the cap read at the plan's slot `p.slot` can be any cap, and `decode_invocation` reaches untyped
reset, `vspace.decode`, `ept.decode`. The bridge needs the program premise only on stores narrowing the path's
lawful store and from the entry states and their alternatives (`IsProgOn`, `AltOf`). There the cap at `p.slot` is
the entry's CNode cap, so the body is `invBodyG` (the decode cut to `decCNG`, the CNode arm), as `io_prune`
(`P2/IoPrune.lean`) does for the I/O port path:

* `invTail_eq_G`, `hil_eq_G`: on any store, the body is `invBodyG` when every cap read at `p.slot` after the
  prefix (`FAULT_IP` write, `update_timestamp`) is a CNode cap;
* `slot_cap_nar`: on a store narrowing `st`, a slot's cap reads as on `st` or fails;
* **`inv_prune`**: on every store narrowing `st`, from every entry state and every alternative of one, the body
  is `invBodyG` (the prefix writes no slot word: `prefix_slot`; the CNode cap words at `p.slot` are the gate's,
  so in `IoRS` at the entry (`IoPre.slot`) and equal at the alternative);
* **`inv_isProgOn`**: a tree of the pruned body `invBodyP` gives the relativised program premise.

Premises: `hA` (Arch totality), `hPE` (`Pre` gives `IoPre`), and
[J] **`hSC`** (`InvSlotCN`): at a `Pre` state the plan's slot is a capability slot of the layout holding a CNode
cap. (For the canonical `InvQ`, the cap part is `InvPlanD`'s `plan_with` on the Delete label, which returns a plan
only for a CNode cap; `p.slot ∈ K.slots` is the CSpace walk's result, fl4-sync's `localinv::plan` input.)
No statement of an existing declaration changes.
-/
import Fl4Proofs.P2.InvDec
import Fl4Proofs.P2.InvProgSrc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own region RegionOK InW TcbSlot NullOrFrame)

section eqs
variable {S : Type}

/-- **`invTail` is `invTailG`** when every cap read at the plan's slot after the prefix is a CNode cap. -/
theorem invTail_eq_G {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (info : msginfo.MessageInfo) (p : localinv.Plan)
    (hcap : ∀ i2 s1 s2 a1 c, obj.Tcb.set_reg m t s layout.reg.FAULT_IP i2 = ok s1 →
      sched.update_timestamp m ar s1 a = ok (s2, a1) → obj.Slot.cap m p.slot s2 = ok c →
      ∃ x y z w, c = .CNode x y z w) :
    invTail m ar s a t info p = invTailG m ar s a t info p := by
  unfold invTail invTailG
  refine bind_guard_congr rfl fun b _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  refine bind_guard_congr rfl fun next _ => ?_
  refine bind_guard_congr rfl fun i2 _ => ?_
  refine bind_guard_congr rfl fun s1 hs1 => ?_
  refine bind_guard_congr rfl fun ⟨s2, a1⟩ hu => ?_
  refine bind_guard_congr rfl fun csc _ => ?_
  refine bind_guard_congr rfl fun i3 _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  refine bind_guard_congr rfl fun i4 _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  refine bind_guard_congr rfl fun i5 _ => ?_
  refine bind_guard_congr rfl fun b1 _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  refine bind_guard_congr rfl fun b2 _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  refine bind_guard_congr rfl fun b3 _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  refine bind_guard_congr rfl fun buf _ => ?_
  refine bind_guard_congr rfl fun len _ => ?_
  refine bind_guard_congr rfl fun cap hc => ?_
  obtain ⟨x, y, z, w, rfl⟩ := hcap i2 s1 s2 a1 cap hs1 hu hc
  rw [decInv_eq_CN]
  rfl

/-- **The body is `invBodyG`** when every cap read at the plan's slot after the prefix is a CNode cap. -/
theorem hil_eq_G {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (number : I64)
    (p : localinv.Plan)
    (hcap : ∀ t i2 s1 s2 a1 c, sched.cur_thread m s = ok t →
      obj.Tcb.set_reg m t s layout.reg.FAULT_IP i2 = ok s1 →
      sched.update_timestamp m ar s1 a = ok (s2, a1) → obj.Slot.cap m p.slot s2 = ok c →
      ∃ x y z w, c = .CNode x y z w) :
    syscall.handle_invocation_local m ar s a number p = invBodyG m ar s a number p := by
  rw [handle_invocation_local_eq]
  unfold invBodyG
  refine bind_guard_congr rfl fun t ht => ?_
  refine bind_guard_congr rfl fun info _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  refine bind_guard_congr rfl fun i _ => ?_
  refine bind_guard_congr rfl fun i1 _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  exact invTail_eq_G m ar s a t info p (hcap t · · · · · ht)

end eqs

section nar
variable {S : Type} {st m : machine.Store S}

/-- On a store narrowing `st`, a slot's cap reads as on `st` or fails. -/
theorem slot_cap_nar (N : Narrow st m) (sl : U64) (s : S) :
    Nar (obj.Slot.cap m sl s) (obj.Slot.cap st sl s) := by
  unfold obj.Slot.cap
  exact Nar.bind (N.read_pair _ _) (fun _ _ => Nar.refl _)

end nar

section prune
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

variable (st) in
/-- [J] **The plan's slot holds a CNode cap** at the `Pre` states: it is a capability slot of the layout
(`K.slots`) and its cap is a CNode cap. -/
def InvSlotCN (K : KLayout) (p : localinv.Plan) (P : S → Prop) : Prop :=
  ∀ s, P s → p.slot ∈ K.slots ∧ ∃ x y z w, obj.Slot.cap st p.slot s = ok (.CNode x y z w)

set_option maxHeartbeats 1000000 in
/-- **The frame-cap invocation body is `invBodyG`** on every store narrowing `st`, from every entry state and
every alternative of one (`hSC` [J]). -/
theorem inv_prune (hA : P0.ArchTotal ar) {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {p : localinv.Plan}
    (hSC : InvSlotCN st K p P) {m : machine.Store S} (N : Narrow st m)
    {s' : S} (hG : AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s')
    (a : A) (number : I64) :
    syscall.handle_invocation_local m ar s' a number p = invBodyG m ar s' a number p := by
  obtain ⟨s, hE, Al⟩ := hG
  have P := hPE s hE
  obtain ⟨hsl, x1, x2, x3, x4, hcs⟩ := hSC s hE
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hN' : NodePlaced st T s' (L.cpu s') := by rw [Al.cpu]; exact P.np.ksb Al.ksb
  have hcT' : L.curW s' ∈ T := by rw [hcur]; exact P.cT
  -- the cap at `p.slot` at the alternative is the entry's CNode cap
  have hnf := cap_not_nof hcs (Or.inl ⟨x1, x2, x3, x4, rfl⟩)
  obtain ⟨r0, r8⟩ := P.slot (Locks := Locks) hsl (Or.inr hnf)
  have hcs' : obj.Slot.cap st p.slot s' = ok (.CNode x1 x2 x3 x4) := by
    rw [← hcs]
    unfold obj.Slot.cap
    rw [L.read_pair_eq, L.read_pair_eq, Al.read _ r0, Al.read _ r8]
  obtain ⟨h8, hf⟩ := P.lay.slot8 _ hsl
  have hv : (core.num.U64.wrapping_add p.slot 8#u64).val = p.slot.val + 8 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine hil_eq_G m ar s' a number p fun t i2 s1 s2 a1 c ht hs1 hu hc => ?_
  have et : t = L.curW s' := by
    have := (cur_thread_nar N s').ok_eq ht
    rw [cur_thread_ok] at this
    exact (ok_inj_ff this).symm
  subst et
  have es1 := (set_reg_nar N _ s' _ i2).ok_eq hs1
  have eu := (update_timestamp_nar N ar s1 a).ok_eq hu
  have ec := (slot_cap_nar N _ s2).ok_eq hc
  have w := prefix_writes ar hA P.tp hN' hcT' es1 eu
  have np : ∀ b, InW p.slot 32 b → Aligned b → L.mem s2 b = L.mem s' b := by
    intro b hb ha
    obtain ⟨p1, p2, p3⟩ := prefix_slot P hsl hb
    refine w.2.2 _ ha ?_
    rintro (⟨K', hK', e⟩ | e | e)
    · obtain ⟨k, hk, e2⟩ := regA_eq P.tA (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
      have ek : K' = k := UScalar.eq_of_val_eq (by rw [hK', hk]; simp [layout.reg.FAULT_IP])
      exact p1 (by rw [e2, e, hcur, ek])
    · exact p2 (e.trans (G.node _))
    · exact p3 (e.trans (G.node _))
  have sk : obj.Slot.cap st p.slot s2 = obj.Slot.cap st p.slot s' := by
    unfold obj.Slot.cap
    rw [L.read_pair_eq, L.read_pair_eq, np p.slot ⟨le_refl _, by omega⟩ h8,
      np _ ⟨by omega, by omega⟩ (by unfold Aligned; omega)]
  rw [sk, hcs'] at ec
  exact ⟨x1, x2, x3, x4, (ok_inj_ff ec).symm⟩

/-- **The relativised program premise of the frame-cap invocation path** from a tree of the pruned body
(`hSC` [J]). -/
theorem inv_isProgOn (hA : P0.ArchTotal ar) {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {number : I64} {p : localinv.Plan}
    (hSC : InvSlotCN st K p P) {q : SProg Bool} (hp : IsProg (invBodyP S number p) q) :
    IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q :=
  fun m N s' hG a => by
    show syscall.handle_invocation_local m ar s' a number p = _
    exact (inv_prune (Locks := Locks) hA hPE hSC N hG a number).trans (congrFun (congrFun (hp A ar m) s') a)

end prune

end Fl4Proofs.P2.PathObl

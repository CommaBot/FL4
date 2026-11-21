/-
P3 (DESIGN.md §9), CSpace: **an insert into an empty TCB slot keeps
`LiveDN`** (XTopJointWJLRestart's `LiveJ ∧ DbgWF ∧ NullOrig`), for the TCB
cap installs at `WJL` (XTopJointTcbInstall's `install_tcb_capJ`,
`install_bufferJ`; l4v `cap_insert` keeps `if_unsafe_then_cap`,
`if_live_then_nonz_cap`, `zombies_final` and `valid_nullcaps`).

* `LiveDN.insT`: `cdt::insert` of a cap alike an existing one (its shape)
  into the empty slot `n` of a TCB `t` that a thread cap names:
  - the new cap is no zombie: a zombie's shape is itself, so its source
    would hold the same zombie, against `zombies_final` after
    (`FinInv.zombie_alone`);
  - `slots`: the new slot's container `t` is named by the thread cap (kept,
    and in the MDB after); a slot in use after but that one was in use
    before (the caps and original bits elsewhere kept, `capInsert_orig`),
    its naming cap kept;
  - `dbg`: the debug words kept (the insert writes slot words only,
    `JAtZ.inSlot_notDbg`), the thread caps kept;
  - `zslots`: a zombie after is one before; the new slot is no zombie's slot
    from its count on: a zombie to `t` would name `t`, which the thread cap
    names too (`FinInv.zombie_alone`);
  - `zdead`: the dead stay dead (`JAtZ.deadP_slot`);
  - `DbgWF` by `JAtZ.dbgWF_keep`; `NullOrig`: the new slot is not null, the
    other slots' caps and bits kept.
-/
import Fl4Proofs.P3.XTopJointWJLRestart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- **An insert into an empty TCB slot keeps `LiveDN`** (module docstring; `LiveDN.insTX` at `J'`). -/
theorem LiveDN.insT {G : MdbGhost} {V : XVs} {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hDS : DState (L := L) Z.th s σ G)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ)
    {G' : MdbGhost} {V' : XVs} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S}
    {σ' : Fl4Spec.State Unit}
    (J' : JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a σ') (hDS' : DState (L := L) Z.th s' σ' G')
    {t : U64} (ht : Z.th t = some .tcb) {n : Nat} (hn : n < tcbSlots) {c : Fl4Spec.Cap} {src : Fl4Spec.CslotPtr}
    (hci : Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({((), σ')}, False))
    (hwS : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    (hnull : capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
      capV (L.mem s') y = capV (L.mem s) y)
    (hnn : capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) ≠ .Null)
    (hsh : ∃ y0, IsSlot Z.th y0 ∧
      shape (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) = shape (capV (L.mem s) y0))
    (hlive : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .Thread t) :
    LiveDN (L := L) Z.th H Cs G' s' σ' :=
  LiveDN.insTX J hDS hLv J'.xtop hDS' ht hn hci hwS hnull hcap hnn hsh hlive

end

end

end Fl4Proofs.P3

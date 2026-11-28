/-
P3 (line mmuAD, gen 42b4): **TCBSetEPTRoot at `VmEptState`** — FL4's perform half of `tcb::decode` at label 88
(tcb.rs l. 410-420: `cdt::delete` of the target's `SLOT_EPT`, `cdt::insert` of the derived cap from the source slot,
the caller's restart) against the extension spec's `invokeSetEptRootF` (Ext/VirtKernelF: `capDeleteVF` of
`(target, tcbCnodeIndex 5)`, then `capInsert`), at the VM-epoch invariant with guest tables.

* **The install half.** `insert_eptRoot`: FL4's `cdt::insert` of a mapped level-0 `Ept` cap, read from a CNode slot,
  into an empty TCB slot refines the spec's `capInsert` of its abstract cap (P3/TcbCaps' `insert_full_abs_fin`,
  `insert_delinv`, `insert_caps_nofull`; `Vs.insert_frame2`: slot words only), the ghost stepping by `MdbStep`.
  **`VmEptState.insEptRoot`**: that insert at `VmEptState` — the base by P3/XTopJointTcbInstall's **`JAtZB.insTJ`**
  (gen 42b4: `JAtZ.insTJ` generalised in place to `JAtZB`; an `Ept` cap has no VSpace key, is native-free, the copy
  of the source slot's cap for every VSpace slot fact), **`VcpuCore.ofSet`** (P3/EptDelRoot, gen 42b4: `ofEmpty`
  generalised in place to a slot written null or with an `Ept` cap) and **`EptCore.frameI`** (P3/EptCore, gen 42b4:
  `EptCore.frame` generalised in place to slot `Ept` caps that are old caps, possibly copied to a new slot when
  mapped; `UnmappedEmpty.keepI`): the new cap is the source's mapped cap, so `capL`, `exte` and `UnmappedEmpty` hold
  (the source slot names its table, so no unmapped cap does), the slot words miss the tables (`JAtZB.slotWd_ept`).
* **The delete half** is P3/EptDelRoot's `VmEptState.delEptRoot` (old cap a mapped level-0 `Ept` cap) or a no-op on
  both sides (old slot empty: `delete_null_eq`, **`capDeleteVF_null`** via **`rdvf_fin_null`**).
* **`VmEptState.restart`**: the caller's restart (`tcb::restart_caller` / `sched::set_thread_state(ct, Restart)`)
  against the spec's `setThreadState curThread Restart` at `VmEptState`, on an `Entered` spec state (the base by
  P3/JAtZV3HiRun's `JAtZB.restartJB`, the records by `VmEptState.ofBS`).
* **`VmEptState.setEptRoot`** (SetEPTRoot whole after its checks): from `VmEptState V X XL` with the target's
  `SLOT_EPT` empty or holding a mapped level-0 `Ept` cap (gen 42b6: `EptCore.eslot`; before, the premise `hold`), the source CNode slot holding the mapped level-0
  `Ept q 0 true asid va` (what P3/VirtSetEptDec's `setEptRoot_decode_ok` reaches), a thread cap to the target in
  some slot (`hlive`): FL4's `setEptRootF` ends in `Ok ()`; there is an outcome `σ3` of `invokeSetEptRootF` with
  `VmEptState V X XL` at the state after the insert and `σ3`, FL4's last step is the restart of `curW`, and when
  `σ3` is `Entered` the restart is the spec's `setThreadState` with `VmEptState` after it.
  **`setEptRoot_decode_vmEpt`**: with P3/VirtSetEptDec's `setEptRoot_decode_ok`, the extended decoder's single
  outcome is the `setEptRoot` invocation whose perform is the above.

Premises: `ArchRefines` [P] (as P3/EptFinRoot / EptDelRoot), `hstall` [J] (`setEptRoot_decode_vmEpt` only, the
target's `remote_tcb_stall` a no-op, as P3/VirtSetEptDec's `setEptRoot_decode_ok`). Gen 42b6: the former premise
`hold` [J] (the target's `SLOT_EPT` holds null or a mapped level-0 `Ept` cap) is gone — it is the new `EptCore` field
`eslot : EptSlotOK` (P3/EptCore), established here by `VmEptState.insEptRoot`. Everything else is a hypothesis of the step (the source slot,
the target, `hlive`). No `sorry`; only the three standard axioms.
-/
import Fl4Proofs.P3.EptDelRoot
import Fl4Proofs.P3.XTopJointTcbInstall
import Fl4Proofs.P3.VirtSetEptDec
import Fl4Proofs.P3.JAtZV3HiRun
import Fl4Proofs.P3.JAtZV3HiFault
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## The spec's delete of an empty slot -/

section
open Fl4Spec Classical

/-- `FinaliseSlotCall` on an empty slot (`recDelFVF`'s first branch). -/
theorem rdvf_fin_null {sl : CslotPtr} {e : Bool} {σ : State Unit}
    (hg : getCap (Z := Unit) sl σ = ({(.nullCap, σ)}, False)) :
    RDVF (.finaliseSlotCall sl e) σ (.ok (true, .nullCap), σ) := by
  refine rdvf_of_F fun f _ _ => ?_
  unfold recDelFVF withoutPreemption
  refine mem_bindE_ok (mem_of_run (run_liftE hg)) ?_
  simp only [↓reduceIte]
  exact mem_of_run (run_returnOk _ σ)

/-- `capDeleteVF` of an empty slot returns with the state unchanged. -/
theorem capDeleteVF_null {sl : CslotPtr} {σ : State Unit}
    (hg : getCap (Z := Unit) sl σ = ({(.nullCap, σ)}, False)) :
    (.ok (), σ) ∈ ((capDeleteVF (Z := Unit) sl).run σ).1 := by
  have he : emptySlot (Z := Unit) sl .nullCap σ = ({((), σ)}, False) := by
    unfold emptySlot
    rw [nd_bind_single hg]; simp
  obtain ⟨v, hv⟩ := rdvf_cte_ok (rdvf_fin_null (e := true) hg) (σ2 := σ) (by
    simp only [NonDet.when, true_or, ↓reduceIte]; rw [he]; exact Set.mem_singleton _)
  exact capDeleteVF_ok hv

end

/-! ## FL4's insert of a mapped EPT root cap -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

open Classical Fl4Proofs.P3.Vs

set_option maxHeartbeats 4000000 in
/-- **`cdt::insert` of a mapped level-0 `Ept` cap from a CNode slot into an empty TCB slot** (module docstring). -/
theorem insert_eptRoot (th : TypedHeap) (hP : Placed th) (s1 : S) (σ1 : Fl4Spec.State Unit) (G1 : MdbGhost)
    (hDS1 : DState (L := L) th s1 σ1 G1) {t : U64} (ht : th t = some .tcb) {n : Nat} (hn : n < tcbSlots)
    (hroot : capV (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null)
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    {c : capability.Cap} {q asid va : U64} (hcE : c = .Ept q 0#u64 true asid va)
    (hsrc : capV (L.mem s1) (cslotAddr (ps.bv, idxs)) = c) :
    cdt.insert st s1 c (cslotAddr (ps.bv, idxs)) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) ⦃ s2 =>
      ∃ σ' G', Fl4Spec.capInsert (Z := Unit) (absCap c) (ps.bv, idxs) (t.bv, Fl4Spec.tcbCnodeIndex n) σ1 =
          ({((), σ')}, False) ∧ DState (L := L) th s2 σ' G' ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) → capV (L.mem s2) y = capV (L.mem s1) y) ∧
        MdbStep (L.mem s1) G1 (L.mem s2) G' ∧
        capV (L.mem s2) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = c ∧ SlotFrame2 (L := L) th s1 s2 ⦄ := by
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ := hDS1
  have hAt : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  have hAsrc : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hcs : capAt (L.mem s1) (cslotAddr (ps.bv, idxs)) = ok c := by rw [capAt_capV, hsrc]
  have hsnn : c ≠ .Null := by rw [hcE]; exact fun h => by cases h
  have hnut : isUt c = false := by rw [hcE]; rfl
  have hzb : isZb c = false := by rw [hcE]; rfl
  have hwf : CapWf c := by rw [hcE]; trivial
  have hcv : CapValid th c := by rw [hcE]; trivial
  have he : EncWf c := by
    have h := hcs
    rw [capAt_words] at h; exact decode_encWf h
  have hdst : capAt (L.mem s1) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = ok .Null := by
    rw [capAt_capV, hroot]
  have hsrcm := (hM.members _).2 ⟨hAsrc.isSlot, c, hcs, hsnn⟩
  have hdestm : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) ∉ G1.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn0⟩ := (hM.members _).1 h
    rw [hdst] at h0
    exact hn0 (by simpa using h0.symm)
  have hfull := fullF_none_of (a := c) hnut
  obtain ⟨s2, h2s, σ', G', hins, hR', hV', hM', hC', hI', hFI', hSti⟩ := spec_exists
    (insert_full_abs_fin th s1 σ1 G1 hR hV hP hM hC hI hFI hps hls hAt hcs hsnn hdst c (absCap c)
      ⟨hwf, rfl⟩ hcv he hsnn rfl (Or.inl rfl) (fun h => by rw [hnut] at h; cases h) hzb rfl
      (fun _ _ _ _ _ h => h))
  have hSt := hSti (fun _ => rfl)
  obtain ⟨s3, h3s, hD'⟩ := spec_exists
    (insert_delinv hP s1 G1 hM hD hsrcm hAt.isSlot hdestm hcs c he hfull hsnn hzb)
  obtain ⟨s4, h4s, hcap⟩ := spec_exists
    (insert_caps_nofull hP s1 G1 hM hsrcm hAt.isSlot hdestm hcs c he hfull)
  obtain ⟨s5, h5s, hF⟩ := spec_exists
    (Vs.insert_frame2 hP s1 c _ _ hAsrc.isSlot hAt.isSlot c hcs (nb_of hP hM hD hAsrc.isSlot).2)
  rw [h2s] at h3s h4s h5s
  cases eq_of_ok_eq h3s; cases eq_of_ok_eq h4s; cases eq_of_ok_eq h5s
  rw [h2s, WP.spec_ok]
  exact ⟨σ', G', hins, ⟨⟨hR', hV', hM', hC', hI'⟩, hD', hFI'⟩, fun y hy hyx => by rw [hcap y hy, if_neg hyx],
    hSt, by rw [hcap _ hAt.isSlot, if_pos rfl], hF⟩

end

/-! ## The insert at `VmEptState` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

set_option maxHeartbeats 4000000 in
/-- **The insert of a mapped level-0 `Ept` cap into an empty TCB slot at `VmEptState`** (module docstring): the
spec's `capInsert` has one outcome, `VmEptState V X XL` there at the stepped ghost, the slot holds the cap, every other
slot's cap is kept. -/
theorem VmEptState.insEptRoot (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : Z.th t = some .tcb) {n : Nat} (hn : n < tcbSlots) (hn2 : n ≠ 2) (hn3 : n ≠ 3)
    (hroot : capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null)
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    {q asid va : U64} (hsrc : capV (L.mem s) (cslotAddr (ps.bv, idxs)) = .Ept q 0#u64 true asid va)
    (hlive : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .Thread t) :
    cdt.insert st s (.Ept q 0#u64 true asid va) (cslotAddr (ps.bv, idxs)) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))
      ⦃ s' => ∃ (σ' : Fl4Spec.State Unit) (G' : MdbGhost) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        Fl4Spec.capInsert (Z := Unit) (absCap (.Ept q 0#u64 true asid va)) (ps.bv, idxs)
          (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({((), σ')}, False) ∧
        VmEptState (L := L) arI V X XL AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' s' a σ' ∧
        capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Ept q 0#u64 true asid va ∧
        (∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) → capV (L.mem s') y = capV (L.mem s) y) ∧
        L.ksb s' = L.ksb s ⦄ := by
  obtain ⟨⟨B, Cv⟩, C⟩ := J
  have hP := B.xtop.rel.1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨B.xtop.rel.2.1, B.del, B.xtop.rel.2.2.1⟩
  have hAsrc : AbsSlot Z.th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  refine WP.spec_mono (insert_eptRoot Z.th hP s σ Z.G hDS ht hn hroot hps hls rfl hsrc) ?_
  rintro s' ⟨σ', G', hci, hDS', hcap, hSt, hdst, hF⟩
  have hwS := SlotFrame2.writesIn hF
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) (absCap (.Ept q 0#u64 true asid va)) (ps.bv, idxs)
      (t.bv, Fl4Spec.tcbCnodeIndex n) σ).1 := by rw [hci]; rfl
  have hcn := capInsert_nkn _ _ _ σ _ hmem
  obtain ⟨Ac', Lst', D', B'⟩ := B.insTJ (fun e => absurd e hn2) ht hn hci hDS' hSt hwS hroot hcap
    (by rw [hdst]; rfl) (by rw [hdst]; exact fun h => by cases h) ⟨_, hAsrc.isSlot, by rw [hdst, hsrc]⟩
    (fun e => absurd e hn3) (fun e => absurd e hn2) hlive
    (fun P L4 L3 L2 L1 h => by rw [hdst, ← hsrc]; exact h _ hAsrc.isSlot)
    (fun U h => by rw [hdst, ← hsrc]; exact h _ hAsrc.isSlot)
    (fun h => by rw [hdst, ← hsrc]; exact h _ hAsrc.isSlot)
    (fun R h => by rw [hdst, ← hsrc]; exact h _ hAsrc.isSlot)
    (fun hk => by rw [hdst] at hk; exact absurd rfl hk)
  have hqX : q ∈ X := by have h := C.exte.cap _ hAsrc.isSlot; rw [hsrc] at h; exact h
  have Cv' := Cv.ofSet B hwS hcap (Or.inr ⟨_, _, _, _, _, hdst⟩) hSt hcn
  have C' : EptCore (L := L) X XL Z.th s' σ' := by
    refine C.frameI hwS (B.slotWd_ept C) (fun y hy p l a' v mm hc => ?_) ⟨fun y hy => ?_, ⟨fun y hy p l a' v hc => ?_,
      fun y hy p sz r d a' v hc => ?_⟩, fun y hy p l a' v hc => ?_⟩ (fun t' ht' => ?_)
      (fun r l es hk => ⟨l, es, (cnK_arch hcn).1 hk⟩) (cnK_entry hcn) (cnK_size hcn)
      (EptSlotStep.ofOne hcap (Or.inr ⟨_, _, _, hdst⟩))
      (C.named.frameA (cnK_asid hcn)
        (fun _ _ _ ⟨q', f, h1, h2, h3⟩ _ => ⟨q', f, by rw [← cnK_asid hcn]; exact h1, (cnK_arch hcn).1 h2, h3⟩)
        (fun r l es hk => (cnK_arch hcn).1 hk) (fun y p l a' v hy hc _ => ?_) (fun y p l mm a' v hy hc => ?_))
    · by_cases e : y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
      · rw [e, hdst] at hc
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := capability.Cap.Ept.inj hc
        exact ⟨_, hAsrc.isSlot, hsrc, fun h => by cases h⟩
      · exact ⟨y, hy, by rw [← hcap y hy e]; exact hc, fun _ => rfl⟩
    · by_cases e : y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
      · rw [e, hdst]; exact hqX
      · rw [hcap y hy e]; exact C.exte.cap y hy
    · by_cases e : y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
      · rw [e, hdst, ← hsrc] at hc; exact C.exte.vtop.1 _ hAsrc.isSlot p l a' v hc
      · rw [hcap y hy e] at hc; exact C.exte.vtop.1 y hy p l a' v hc
    · by_cases e : y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
      · rw [e, hdst, ← hsrc] at hc; exact C.exte.vtop.2 _ hAsrc.isSlot p sz r d a' v hc
      · rw [hcap y hy e] at hc; exact C.exte.vtop.2 y hy p sz r d a' v hc
    · by_cases e : y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
      · rw [e, hdst, ← hsrc] at hc; exact C.exte.anz _ hAsrc.isSlot p l a' v hc
      · rw [hcap y hy e] at hc; exact C.exte.anz y hy p l a' v hc
    · obtain ⟨es, hxe, -⟩ := C.rel.obj t' ht'
      rw [hxe]; exact (cnK_arch hcn).2 hxe
    · by_cases e : y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
      · rw [e, hroot] at hc; cases hc
      · exact ⟨y, hy, by rw [hcap y hy e]; exact hc⟩
    · by_cases e : y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
      · rw [e, hdst] at hc
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := capability.Cap.Ept.inj hc
        exact ⟨_, hAsrc.isSlot, hsrc⟩
      · exact ⟨y, hy, by rw [← hcap y hy e]; exact hc⟩
  exact ⟨σ', G', Ac', Lst', D', hci, ⟨⟨B', Cv'⟩, C'⟩, hdst, hcap, hwS.1⟩

/-- FL4's `set_thread_state(curW, Restart)` succeeds at `VmEptState` (the current thread a TCB of the typed heap). -/
theorem VmEptState.sts_ok (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) :
    ∃ s1, sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s1 := by
  have B := J.1.1
  obtain ⟨hcur, -⟩ := B.curEq (P1.cur_thread_ok s)
  have htcb := (B.xtop.curTcb hcur).1
  obtain ⟨s1, h1, -⟩ := spec_exists (set_thread_state_slots Z.th B.xtop.rel.1 s _ sched.TS_RESTART htcb B.kern.act)
  exact ⟨s1, h1⟩

set_option maxHeartbeats 4000000 in
/-- **The caller's restart at `VmEptState`** (module docstring): on an `Entered` spec state, FL4's
`set_thread_state(curW, Restart)` against the spec's `setThreadState curThread Restart`. -/
theorem VmEptState.restart (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) :
    ∃ (s1 : S) (σ1 : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s1 ∧
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst' D s1 a σ1 := by
  have B := J.1.1
  have C := J.2
  have hS := B.xtop.fin.1.1.1
  have hct := P1.cur_thread_ok (L := L) s
  obtain ⟨hcur, x, hk, hrun⟩ := B.curRunnable hni hct
  have htcb : Z.th (L.curW s) = some .tcb := (B.xtop.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨B.xtop.rel.2.1, B.del, B.xtop.rel.2.2.1⟩
  obtain ⟨s1, σ1, -, hs1, hst1, -, -, -, -, -⟩ :=
    restart_dstate Z.th B.xtop.rel.1 s σ Z.G hDS _ hct hcur htcb B.kern.act
  have e : σ1 = stsAct (updK σ (L.curW s).bv (.tcb { x with tcbState := .restart })) (L.curW s).bv := by
    have hst := hst1
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst e
  obtain ⟨Lst', B', hW⟩ := B.restartJB hcur hk htcb hrun hs1
  refine ⟨s1, _, Lst', hs1, hst1, ?_⟩
  have hk7 : (stsAct (updK σ (L.curW s).bv (.tcb { x with tcbState := .restart })) (L.curW s).bv).kheap (L.curW s).bv =
      some (.tcb { x with tcbState := .restart }) := by rw [stsAct_kheap]; simp [updK]
  have hkp7 : ∀ p, p ≠ (L.curW s).bv →
      (stsAct (updK σ (L.curW s).bv (.tcb { x with tcbState := .restart })) (L.curW s).bv).kheap p = σ.kheap p := by
    intro p hp; rw [stsAct_kheap]; simp [updK, hp]
  have har : (stsAct (updK σ (L.curW s).bv (.tcb { x with tcbState := .restart })) (L.curW s).bv).archState =
      σ.archState := by unfold stsAct; split <;> rfl
  refine J.ofBS B' hW (fun b hb => tfoot_oobj hS hb) (fun b hb => B.tfoot_nh hb) (VKeep.of_tfoot hS B.thT hW)
    (fun u hu => ?_) (fun o ko' ho => ?_) (fun o x' ho hx => ?_) (fun o vs ho => ?_) (fun t ht => ?_)
    (fun r l es ho => ?_) ?_
    (J.2.named.ofSS (B.xtop.slotsSame_of hW (fun b hb => tfoot_oobj hS hb)) (by rw [har]) (fun o ao ho => ?_))
  · obtain ⟨vu, hvu⟩ := J.1.2.vm.spec u hu
    refine hkp7 _ fun e => ?_
    rw [e, hk] at hvu; cases hvu
  · by_cases e : o = (L.curW s).bv
    · subst e
      rw [hk7] at ho; cases ho
      exact ⟨_, hk, rfl⟩
    · rw [hkp7 _ e] at ho; exact ⟨ko', ho, rfl⟩
  · by_cases e : o = (L.curW s).bv
    · subst e
      rw [hk7] at ho; cases ho
      cases hx
    · rw [hkp7 _ e] at ho; exact ⟨x', ho, hx⟩
  · by_cases e : o = (L.curW s).bv
    · subst e
      rw [hk7] at ho; cases ho
    · rw [hkp7 _ e] at ho; exact ho
  · obtain ⟨es, hxe, -⟩ := C.rel.obj t ht
    refine hkp7 _ fun e => ?_
    rw [e, hk] at hxe; cases hxe
  · by_cases e : r = (L.curW s).bv
    · subst e
      rw [hk7] at ho; cases ho
    · rw [hkp7 _ e] at ho; exact ⟨l, es, ho⟩
  · rintro e ⟨hi, p, f, lo, h1, h2, h3⟩
    refine ⟨hi, p, f, lo, by rw [← har]; exact h1, ?_, h3⟩
    by_cases e' : p = (L.curW s).bv
    · subst e'
      rw [hk7] at h2; cases h2
    · rw [hkp7 _ e'] at h2; exact h2
  · by_cases e : o = (L.curW s).bv
    · subst e
      rw [hk7] at ho; cases ho
    · rw [hkp7 _ e] at ho; exact ho

end

/-! ## SetEPTRoot -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- The post of `VmEptState.setEptRoot`: the spec's perform has the outcome `σ3`, `VmEptState` at FL4's state `s5`
after the insert (the target's `SLOT_EPT` holding the new cap), FL4's result the restart of `curW` at `s5`, and on an
`Entered` `σ3` the spec's restart with `VmEptState` after it. -/
def SetEptPost (V X : Set U64) (XL : U64 → Nat) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (σ : Fl4Spec.State Unit) (t ps : U64) (idxs : List Bool) (c : capability.Cap)
    (r : core.result.Result Unit error.Exc × S × A) : Prop :=
  r.1 = .Ok () ∧
  ∃ (σ3 : Fl4Spec.State Unit) (G' : MdbGhost) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s5 : S),
    (.ok (), σ3) ∈ ((Fl4Spec.invokeSetEptRootF (Z := Unit) ⟨t.bv, absCap c, (ps.bv, idxs)⟩).run σ).1 ∧
    VmEptState (L := L) arI V X XL AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' s5 r.2.2 σ3 ∧
    capV (L.mem s5) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = c ∧
    sched.set_thread_state st s5 (L.curW s5) sched.TS_RESTART = ok r.2.1 ∧
    (Entered σ3 → ∃ (σ4 : Fl4Spec.State Unit) (Lst'' : U64 → List U64),
      Fl4Spec.setThreadState (Z := Unit) σ3.curThread .restart σ3 = ({((), σ4)}, False) ∧
      VmEptState (L := L) arI V X XL AR (Z.mv G' Z.vs) H Cs Ac' Lst'' D' r.2.1 r.2.2 σ4)

/-- The insert-and-restart tail of `setEptRootF` at `VmEptState`, from the state after the delete. -/
theorem setEpt_tail {t : U64} {s4 : S} {a2 : A} {σ1 : Fl4Spec.State Unit} {G1 : MdbGhost} {Ac1 : Set U64}
    {Lst1 : U64 → List U64} {D1 : Set U64}
    (J1 : VmEptState (L := L) arI V X XL AR (Z.mv G1 Z.vs) H Cs Ac1 Lst1 D1 s4 a2 σ1)
    (hdel : (.ok (), σ1) ∈ ((Fl4Spec.capDeleteVF (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex 5)).run σ).1)
    (ht : Z.th t = some .tcb)
    (hroot : capV (L.mem s4) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = .Null)
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    {q asid va : U64} (hsrc : capV (L.mem s4) (cslotAddr (ps.bv, idxs)) = .Ept q 0#u64 true asid va)
    (hlive : ∃ y, IsSlot Z.th y ∧ capV (L.mem s4) y = .Thread t) :
    (do
      let s5 ← cdt.insert st s4 (.Ept q 0#u64 true asid va) (cslotAddr (ps.bv, idxs))
        (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5))
      let ct ← sched.cur_thread st s5
      let s6 ← sched.set_thread_state st s5 ct sched.TS_RESTART
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a2)) ⦃ r =>
      SetEptPost (L := L) arI V X XL AR Z H Cs σ t ps idxs (.Ept q 0#u64 true asid va) r ⦄ := by
  refine WP.spec_bind (VmEptState.insEptRoot (Z := Z.mv G1 Z.vs) J1 ht (n := 5) (by decide) (by decide) (by decide)
    hroot hps hls hsrc hlive) ?_
  rintro s5 ⟨σ3, G', Ac', Lst', D', hci, J3, hdst, -, -⟩
  obtain ⟨s6, h6⟩ := J3.sts_ok
  rw [P1.cur_thread_ok]
  simp only [bind_ok]
  rw [h6]
  simp only [bind_ok, WP.spec_ok]
  refine ⟨rfl, σ3, G', Ac', Lst', D', s5, ?_, J3, hdst, h6, fun hni => ?_⟩
  · unfold Fl4Spec.invokeSetEptRootF
    exact mem_bindE_ok hdel (mem_of_run (run_liftE' hci))
  · obtain ⟨s1, σ4, Lst'', h1, hst, J4⟩ := J3.restart hni
    rw [h6] at h1
    cases eq_of_ok_eq h1
    exact ⟨σ4, Lst'', hst, J4⟩

set_option maxHeartbeats 4000000 in
/-- **SetEPTRoot after its checks at `VmEptState`** (module docstring). Premise: `ArchRefines` [P] (gen 42b6: `hold` is `EptCore.eslot`). -/
theorem VmEptState.setEptRoot [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR)
    (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb)
    {ps : U64} {rs : Nat} (hps : Z.th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    {q asid va : U64} (hsrc : capV (L.mem s) (cslotAddr (ps.bv, idxs)) = .Ept q 0#u64 true asid va)
    (hlive : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .Thread t) :
    setEptRootF (st := st) arI s a t (cslotAddr (ps.bv, idxs)) (.Ept q 0#u64 true asid va) ⦃ r =>
      SetEptPost (L := L) arI V X XL AR Z H Cs σ t ps idxs (.Ept q 0#u64 true asid va) r ⦄ := by
  have B := J.1.1
  have hP := B.xtop.rel.1
  have hR := B.xtop.rel.2.1.1
  have hAd : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex 5) := ⟨t, rfl, Or.inr ⟨ht, 5, by decide, rfl⟩⟩
  have hAsrc : AbsSlot Z.th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hsrcT := cnode_slot_ne_tcb hP hps hls ht 5 (by decide)
  obtain ⟨y, hy, hyc⟩ := hlive
  unfold setEptRootF
  rw [spec_eq_ok (tcb_slot_spec t _), tcb_root_eq t _ (n := 5) (by decide) (by simp [layout.tcb.SLOT_EPT])]
  simp only [bind_ok]
  rcases J.2.eslot t ht with h0 | ⟨p, asid', va', h0⟩
  · have hc0 : capAt (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = ok .Null := by rw [capAt_capV, h0]
    rw [delete_null_eq arI s a _ hc0 σ]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
    obtain ⟨c0, a0, hc0', hca, hg⟩ := hR.abs_cap hAd
    rw [hc0] at hc0'
    obtain rfl : (.Null : capability.Cap) = c0 := eq_of_ok_eq hc0'
    rw [hca.abs] at hg
    exact setEpt_tail arI (G1 := Z.G) J (capDeleteVF_null hg) ht h0 hps hls hsrc ⟨y, hy, hyc⟩
  · have hc0 : capAt (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5)) = ok (.Ept p 0#u64 true asid' va') := by
      rw [capAt_capV, h0]
    have hyd : y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 5) := fun e => by rw [e, h0] at hyc; cases hyc
    obtain ⟨⟨r1, s4, a2⟩, hdeq, hr1, σ1, G1, Ac1, Lst1, D1, hdel, J1, hnull, hoth, -⟩ :=
      spec_exists (J.delEptRoot arI hA hAd hc0)
    simp only at hr1 hdel J1 hnull hoth
    subst hr1
    rw [hdeq]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
    exact setEpt_tail arI J1 hdel ht hnull hps hls (by rw [hoth _ hAsrc.isSlot hsrcT]; exact hsrc)
      ⟨y, hy, by rw [hoth y hy hyd]; exact hyc⟩

set_option maxHeartbeats 4000000 in
/-- **SetEPTRoot whole at `VmEptState`** (module docstring): P3/VirtSetEptDec's `setEptRoot_decode_ok` (the extended
decoder's single outcome, FL4's decode is `setEptRootF`) with `VmEptState.setEptRoot` for the perform. Premises:
`ArchRefines` [P], `hstall` [J] (as `setEptRoot_decode_ok`). -/
theorem setEptRoot_decode_vmEpt [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR)
    (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) (p : U64) (c : tcb.Ctx)
    (hstall : smp.remote_tcb_stall st arI s a p = ok (s, a)) (x0 : U64)
    (hx0 : Aeneas.Std.Array.index_usize c.extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel Z.th (L.mem s) x0 cps)
    {q asid va : U64} (hx0n : x0 ≠ 0#u64) (hc : capV (L.mem s) x0 = .Ept q 0#u64 true asid va)
    (slbl : Fl4Spec.Data) (hl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4SetEptRootLabel) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef)
    (ht : Z.th p = some .tcb)
    (hlive : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .Thread p) :
    ∃ (ps : U64) (idxs : Fl4Spec.CnodeIndex) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
      cps = (absCap (.Ept q 0#u64 true asid va), (ps.bv, idxs)) :: rest ∧
      (specDecV false slbl args ci sl (.Thread p) cps buffer).run σ =
        ({(.ok (.setEptRoot ⟨p.bv, absCap (.Ept q 0#u64 true asid va), (ps.bv, idxs)⟩), σ)}, False) ∧
      ∀ rs, Z.th ps = some (.cnode rs) → idxs.length = rs →
        tcb.decode st arI s a fl4_abi.label.TCBSetEPTRoot p c ⦃ r =>
          SetEptPost (L := L) arI V X XL AR Z H Cs σ p ps idxs (.Ept q 0#u64 true asid va) r ⦄ := by
  obtain ⟨ps, idxs, rest, hxe, hcps, hrun, hdec⟩ :=
    setEptRoot_decode_ok arI s a σ p c hstall Z.th x0 hx0 cps hex hx0n hc slbl hl args ci sl buffer
  refine ⟨ps, idxs, rest, hcps, hrun, fun rs hps hls => ?_⟩
  rw [hdec, hxe]
  rw [hxe] at hc
  exact J.setEptRoot arI hA ht hps hls hc hlive

end

end

end Fl4Proofs.P3

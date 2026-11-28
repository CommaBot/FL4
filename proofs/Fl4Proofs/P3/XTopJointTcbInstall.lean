/-
P3 (DESIGN.md §9), TCB: **a cap installed into a TCB slot at `J`**
(FL4 `tcb::install_tcb_cap`, l4v `install_tcb_cap`: `cap_delete` of the
TCB slot, `check_cap_at` twice, `cap_insert`), and the Thread cap labels
built on it.

* `SpecGlob.insTcb`: that insert keeps the deletion loop's `SpecGlob` (the
  new cap names the objects of its source cap, `absCap_shape_refs`; only it
  is written, `nik_capInsert`; a TCB slot is no IRQ node slot).
* `JAtZ.insTJ`: `cdt::insert` of a non-untyped cap into an empty TCB slot
  keeps `JAtZ` (no premise). The spec changes the TCB's caps only
  (`KeepCT`, `XTopAt.slotStepT`); the covers kept (the slot was empty);
  the untyped caps' facts by `ins_utcG` with the TCB live: the invoked
  thread cap, still in its slot (`still_valid`), covers the TCB, so the
  new MDB slot misses every childless untyped region (`live_slotT`); the
  fault-handler slot holds an endpoint cap or nothing (`JPlaced.fh`,
  `jowes_slotDF`).
* `InstPostWP`: `InstPostW` (TcbCaps) with `W` after an Ok install and `Wp`
  after a preempted one; `inst_seqWP`, `inst_skipWP`, `inst_doneWP`.
* `InsWJ arI AR Z H Cs kb W`: an invariant `W` of the installs: `WJR`, kept
  by an insert into an empty TCB slot (given `WJR` after it), with
  `BufHypW` at it (`insWJ_wjr` at `WJR` itself; at `WJL`:
  XTopJointTcbInsL's `insWJ_wjl`). `TcbInsW`: `InsWJ` and the deletion
  loop's steps (`DelHypsWRZ`) at every kernel-state base.
* `install_tcb_capJ`, `install_okJ`: the install at an `InsWJ` invariant `W`
  (`WJP` when preempted): the delete by DelFull's `delete_fullWRZ` with the
  loop's steps at `W` (`DelHypsWRZ`), the checks and insert by TcbCaps'
  `install_after`, then `insTJ`, `PPR0` and `NoSwitch` kept by the insert
  (`CnK`), `W` by `InsWJ.ins`.
* `JAtZ.bufWrJ`: a TCB's IPC-buffer word written at `J` with the spec's
  `tcb_ipc_buffer` (as XTopJointTcbSched's `JAtZ.mcpWrJ`; `QKM` now lets the
  IPC buffer change; `BufWordRel` by XTopBuf's `bufWordRel_setIpc`).
* `bufHypW_J`: TcbCaps' `BufHypW` at `WJR` (the word by `bufWrJ`, the tail's
  `reschedule_required` by XTopJointCopyRegs' `JAtZ.schedJ`; `SpecGlob`/`PPR0`/`NoSwitch` kept),
  with `ActReady` from the state's `JAtZ` (`Sched.Inv.actReady`).
* `install_bufferJ`: `tcb::install_buffer` at `W`/`WJP`, as TcbCaps'
  `install_buffer_refinesW` (the insert by `check_insert`'s case split and
  `insTJ`).
* `thread_control_capsJ`: ThreadControl's cap installs at `W`/`WJP`, as
  TcbCaps' `thread_control_caps_refinesW` (`install_okJ`, `install_bufferJ`).
* `JAtZ.restartJ`: the caller's restart at `J` (moved from XTopJointTcb).
* `JAtZ.restartW`: the restart at `TcbInsW`'s `W` (`RestartWJ`, from the
  caller: XTopJointWJLRestart's `WJL.restart`).
* `top_of_instJ`: an install run's outcome at `W`/`WJP` is a
  `TopPostDMXP` outcome at `JAt`/`JAtPre`.
* Labels: SetTimeoutEndpoint (`tcb_set_timeoutJ`), SetSpace (`tcb_set_spaceJ`),
  SetIPCBuffer (`tcb_set_ipcJ`), Configure (`tcb_configureJ`);
  `xcapP_of_tcb` lifts a label's `TcbOKXP` to the Thread cap's `XCapP`.

(mmuAD gen 42b4) Stated over `JAtZ`'s `ext`-free part `JAtZB` (P3/JointAt), none reading `JAtZ.ext`:
`LiveDN.insTX` (as `LiveDN.insTXB`) and `insTJ` (`JAtZB.insTJ`; `JAtZ.insTJ` rebuilds `ext` by `JExt.step`), with
their statements unchanged.
-/
import Fl4Proofs.P3.XTopJointCnDel
import Fl4Proofs.P3.XTopJointTcbSched
import Fl4Proofs.P3.XTopJointCopyRegs
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **An insert into an empty TCB slot keeps `LiveDN`** (XTopJointWJLIns's `LiveDN.insT` with the `XTopAt` after in place of a `JAtZ` after;
KENTRY-PLAN g2i). -/
theorem LiveDN.insTXB {G : MdbGhost} {V : XVs} {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hDS : DState (L := L) Z.th s σ G)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ)
    {G' : MdbGhost} {V' : XVs} {s' : S}
    {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a σ') (hDS' : DState (L := L) Z.th s' σ' G')
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
    LiveDN (L := L) Z.th H Cs G' s' σ' := by
  obtain ⟨hL, ⟨lst, hDW⟩, hN⟩ := hLv
  have hP : Placed Z.th := J.xtop.rel.1
  set x := cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) with hx
  have hAd : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  have hxS : IsSlot Z.th x := hAd.isSlot
  have htn : IsSlotAt Z.th t n := Or.inr ⟨ht, hn⟩
  have hxe : x = slotOf t n := by
    show slotAddr t.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, tcbCnodeIndex_blVal n hn]
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ).1 := by
    rw [hci]; rfl
  have hcn := capInsert_nkn c _ _ σ _ hmem
  have hkc : KeepCT σ σ' := KeepCT.of_cnK hcn
  have hw : P1.WritesIn st s s' (InSlot Z.th) := hwS.mono fun b hb => slotWd_range hP hb
  have horig : ∀ sl, sl ≠ (t.bv, Fl4Spec.tcbCnodeIndex n) → σ'.isOriginalCap sl = σ.isOriginalCap sl :=
    fun sl e => capInsert_orig c _ _ σ ((), σ') hmem sl e
  have hM := hDS.1.2.2.1
  have hM' := hDS'.1.2.2.1
  -- a non-null cap before, away from `x`: in the MDB after, kept
  have hkeep : ∀ y, IsSlot Z.th y → capV (L.mem s) y ≠ .Null →
      y ∈ G'.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y := fun y hy h => by
    have hyx : y ≠ x := fun e => h (by rw [e, hnull])
    have e := hcap y hy hyx
    exact ⟨(hM'.members y).2 ⟨hy, _, capAt_capV _ _, by rw [e]; exact h⟩, e⟩
  have hmemS : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hM.members y).1 hy).1
  have hmemN : ∀ y ∈ G.chains.flatten, capV (L.mem s) y ≠ .Null := fun y hy => by
    obtain ⟨-, c0, h0, hn0⟩ := (hM.members y).1 hy
    rw [capV_of_capAt h0]; exact hn0
  -- the new cap is no zombie
  have hnz : ∀ p zt k, capV (L.mem s') x ≠ .Zombie p zt k := by
    intro p zt k hz
    obtain ⟨y0, hy0, hsh0⟩ := hsh
    have e0 : capV (L.mem s) y0 = capV (L.mem s') x := zombie_of_shape hsh0 hz
    have hy0x : y0 ≠ x := fun e => by rw [e, hnull, hz] at e0; cases e0
    have h1 := FinInv.zombie_alone hDS'.2.2 hM' hxS hz y0 hy0 hy0x
    rw [hcap y0 hy0 hy0x, e0, hz] at h1
    exact h1 (by simp [absCap, Fl4Spec.objRefs])
  -- the thread cap naming `t`
  obtain ⟨yT, hyT, hTc⟩ := hlive
  obtain ⟨hyTG, hyTc⟩ := hkeep yT hyT (by rw [hTc]; exact fun h => by cases h)
  -- a slot in use after, away from `x`, was in use before
  have hU : ∀ y, IsSlot Z.th y → y ≠ x → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := fun y hy hyx hu => by
    unfold InUse at hu ⊢
    rw [hcap y hy hyx] at hu
    rcases hu with hu | ⟨x', hx', ho⟩
    · exact Or.inl hu
    · refine Or.inr ⟨x', hx', ?_⟩
      have hne : x' ≠ (t.bv, Fl4Spec.tcbCnodeIndex n) := fun e => hyx (by rw [← hx', e])
      rw [← horig x' hne]; exact ho
  -- the debug words
  have hdk : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
    dbgKeep_of_writes J.blk hwS fun _ hb => J.inSlot_notDbg (slotWd_range hP hb)
  have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s := ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
  have hc0 : 0#u64 ∈ Cs := J.kern.cs0
  have hhd : dbgHead (L := L) s' = dbgHead (L := L) s := by
    unfold dbgHead
    rw [P1.nodeAt_of_ksb hdk.1]
    exact hdk.2 _ (Or.inr ⟨0#u64, hc0, rfl⟩)
  have hNt : ∀ k, dbgNth (L.mem s') k (dbgHead (L := L) s') = dbgNth (L.mem s) k (dbgHead (L := L) s) :=
    fun k => by
      rw [hhd]
      exact dbgNth_keep (fun y hy => hdk.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (fun y hy => hTz.dn y hy) k _
        (hTz.dh _ hc0)
  -- no zombie names `t`
  have hzt : ∀ y, IsSlot Z.th y → ∀ zt k, capV (L.mem s) y ≠ .Zombie t zt k := fun y hy zt k hz => by
    have hne : yT ≠ y := fun e => by rw [e, hz] at hTc; cases hTc
    have h1 := FinInv.zombie_alone hDS.2.2 hM hy hz yT hyT hne
    rw [hTc] at h1
    exact h1 (by simp [absCap, Fl4Spec.objRefs])
  have hL' : LiveJ (L := L) Z.th H G' s' σ' := by
    refine ⟨fun q i hqi hu => ?_, fun k hk hki => ?_, fun y hy p zt k hz i hpi hki hu => ?_,
      fun y hy p zt k hz hzt' => ?_⟩
    · by_cases hqx : slotOf q i = x
      · obtain ⟨rfl, -⟩ := slotOf_inj hP hqi htn (hqx.trans hxe)
        exact Or.inl ⟨yT, hyTG, by rw [hyTc, hTc]; rfl⟩
      · rcases hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hqx hu) with ⟨y, hy, hr⟩ | hb
        · obtain ⟨hyG, hyc⟩ := hkeep y (hmemS y hy) (hmemN y hy)
          exact Or.inl ⟨y, hyG, by rw [hyc]; exact hr⟩
        · exact Or.inr (by rw [hdk.1]; exact hb)
    · rw [hNt] at hk hki ⊢
      obtain ⟨y, hy, hr⟩ := hL.dbg k hk (by rw [← hcn.idle]; exact hki)
      obtain ⟨hyG, hyc⟩ := hkeep y (hmemS y hy) (hmemN y hy)
      exact ⟨y, hyG, by rw [hyc]; exact hr⟩
    · have hyx : y ≠ x := fun e => hnz p zt k (by rw [← e]; exact hz)
      have hz0 : capV (L.mem s) y = .Zombie p zt k := by rw [← hcap y hy hyx]; exact hz
      by_cases hpx : slotOf p i = x
      · obtain ⟨rfl, -⟩ := slotOf_inj hP hpi htn (hpx.trans hxe)
        exact hzt y hy zt k hz0
      · exact hL.zslots y hy p zt k hz0 i hpi hki (hU _ ⟨p, i, hpi, rfl⟩ hpx hu)
    · have hyx : y ≠ x := fun e => hnz p zt k (by rw [← e]; exact hz)
      have hz0 : capV (L.mem s) y = .Zombie p zt k := by rw [← hcap y hy hyx]; exact hz
      exact J.deadP_slot hX' hcn hkc hw (hL.zdead y hy p zt k hz0 hzt')
  refine ⟨hL', ⟨lst, dbgWFL_step J.xtop hX' rfl rfl J.tcbs_eq.1 hDW hdk⟩, fun sl hA h => ?_⟩
  have hsx : cslotAddr sl ≠ x := fun e => hnn (by rw [← e]; exact h)
  have hne : sl ≠ (t.bv, Fl4Spec.tcbCnodeIndex n) := fun e => hsx (by rw [e])
  rw [horig sl hne]
  exact hN sl hA (by rw [← hcap _ hA.isSlot hsx]; exact h)

/-- `LiveDN.insTXB` at `JAtZ` (via `JAtZ.toB`). -/
theorem LiveDN.insTX {G : MdbGhost} {V : XVs} {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hDS : DState (L := L) Z.th s σ G)
    (hLv : LiveDN (L := L) Z.th H Cs G s σ)
    {G' : MdbGhost} {V' : XVs} {s' : S}
    {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a σ') (hDS' : DState (L := L) Z.th s' σ' G')
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
  LiveDN.insTXB J.toB hDS hLv hX' hDS' ht hn hci hwS hnull hcap hnn hsh hlive


set_option maxHeartbeats 4000000 in
/-- **An insertion into an empty TCB slot keeps `JAtZ`** (module
docstring). -/
theorem JAtZB.insTJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : Nat} {σ' : Fl4Spec.State Unit}
    (hok : n = 2 → Endp.IpcBufCapOK σ') {t : U64} (ht : Z.th t = some .tcb)
    (hn : n < tcbSlots) {c : Fl4Spec.Cap} {src : Fl4Spec.CslotPtr} {s' : S}
    {G' : MdbGhost}
    (hci : Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({((), σ')}, False))
    (hDS' : DState (L := L) Z.th s' σ' G') (hSt : MdbStep (L.mem s) Z.G (L.mem s') G')
    (hwS : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    (hnull : capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
      capV (L.mem s') y = capV (L.mem s) y)
    (hnu : isUt (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) = false)
    (hnn : capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) ≠ .Null)
    (hsh : ∃ y0, IsSlot Z.th y0 ∧
      shape (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) = shape (capV (L.mem s) y0))
    (hfh : n = 3 → capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Endpoint ep b0 b1 b2 b3 b4)
    (hbs : n = 2 → Sched.BufSlotOK (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (hlive : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .Thread t)
    (hvt : ∀ P L4 L3 L2 L1 : Set U64, Vs.VsSlotsW Z.th P L4 L3 L2 L1 (L.mem s) →
      Vs.VCapW P L4 L3 L2 L1 (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (hft : ∀ U : Nat → Prop, Vs.FrSlots Z.th U (L.mem s) →
      Vs.FrIn U (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (hnt : Vs.VsNat Z.th (L.mem s) → Vs.NativeCap (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (htt : ∀ R, Vs.TabSlots Z.th R (L.mem s) → Vs.TabR R (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (hkr : Vs.VKey (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) ≠ none →
      (∃ y0, IsSlot Z.th y0 ∧ y0 ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) ∧
        capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = capV (L.mem s) y0) ∧
      ¬ Vs.TabUn (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)))) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZB (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' s' a σ' := by
  have hX := J.xtop
  have hP := hX.rel.1
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ).1 := by
    rw [hci]; rfl
  have hcn := capInsert_nkn c _ _ σ _ hmem
  have hkc : KeepCT σ σ' := KeepCT.of_cnK hcn
  have hkz : KSz σ σ' := capInsert_nkz c _ _ σ _ hmem
  have hw : P1.WritesIn st s s' (InSlot Z.th) := hwS.mono fun b hb => slotWd_range hP hb
  have hAd : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  obtain ⟨hCR', hDl', hFI'⟩ := hDS'
  have hM' := hCR'.2.2.1
  have hMO : MdbOKV (L.ksb s) (L.mem s') G' := hSt.okv hX.rel.2.2.2.2.1
  have hct : σ'.curThread = σ.curThread := by
    have e := congrArg Fl4Spec.AbstractState.curThread hcn.1; exact e
  have hCO := CurOK.of_inv' hX.fin.2.2.2.2 hct hM' hMO.2.2
  have hX1 : XTopAt (L := L) AR (Z.mv G' Z.vs) s' a σ' := XTopAt.slotStepT hX hwS hcn hCR' hFI' hMO hCO
  have hnull' : capAt (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = ok .Null := by
    rw [capAt_capV, hnull]
  have hnu' : ∀ p sb fi d, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) ≠ .Untyped p sb fi d :=
    fun p sb fi d e => by rw [e] at hnu; simp [isUt] at hnu
  -- the slots' caps after
  have hTK : TypedKept Z.th (L.mem s) (L.mem s') := fun x hx => by
    by_cases e : x = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
    · subst e; obtain ⟨y0, hy0, h0⟩ := hsh; exact Or.inr ⟨y0, hy0, h0⟩
    · exact Or.inr ⟨x, hx, by rw [hcap x hx e]⟩
  have hUK : UtKept Z.th (L.mem s) (L.mem s') := fun x hx p sb fi d h => by
    have e : x ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) := fun e => hnu' p sb fi d (e ▸ h)
    exact ⟨x, hx, fi, by rw [← hcap x hx e]; exact h, Or.inl le_rfl⟩
  have hCK : CoverKept Z.th (L.mem s) (L.mem s') := fun y hy hp hu => by
    have hyd : y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) := fun e => by
      rw [e, hnull, physF_null] at hp; cases hp
    have e := hcap y hy hyd
    exact ⟨y, hy, by rw [e]; exact hp, by rw [e]; exact hu, by rw [e], by rw [e]⟩
  have hfh' : ∀ u, Z.th u = some .tcb → capV (L.mem s') (cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 3)) =
        .Endpoint ep b0 b1 b2 b3 b4 := by
    intro u hu
    have hAu : AbsSlot Z.th (u.bv, Fl4Spec.tcbCnodeIndex 3) := ⟨u, rfl, Or.inr ⟨hu, 3, by decide, rfl⟩⟩
    by_cases e : cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 3) = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
    · have e' := cslotAddr_inj hP hAu hAd e
      have h3 : 3 = n := tcbCnodeIndex_inj (by decide) hn (congrArg Prod.snd e')
      rw [e]; exact hfh h3.symm
    · rw [hcap _ hAu.isSlot e]
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      exact hJ.fh u hu
  have hbs' : ∀ u, Z.th u = some .tcb →
      Sched.BufSlotOK (capV (L.mem s') (cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 2))) := by
    intro u hu
    have hAu : AbsSlot Z.th (u.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨u, rfl, Or.inr ⟨hu, 2, by decide, rfl⟩⟩
    by_cases e : cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 2) = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
    · have e' := cslotAddr_inj hP hAu hAd e
      have h2 : 2 = n := tcbCnodeIndex_inj (by decide) hn (congrArg Prod.snd e')
      rw [e]; exact hbs h2.symm
    · rw [hcap _ hAu.isSlot e]
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      exact hJ.bfs u hu
  have horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl := by
    intro sl h
    by_cases e : sl = (t.bv, Fl4Spec.tcbCnodeIndex n)
    · right; rw [e]; exact hAd
    · left; rw [← capInsert_orig c _ _ σ ((), σ') hmem sl e]; exact h
  have hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn.1; exact e
  have hutc := J.ins_utcG arI hAd hcap hnull' hnu' hw (capInsert_cdt c _ _ σ _ hmem)
    (fun sl e => capInsert_orig c _ _ σ ((), σ') hmem sl e) hgp hM'
    fun _ _ _ _ _ hsl hcv _ hnc => J.live_slotT arI hsl hcv hnc ht hn hlive
  have hjc := J.jcov_cover hw.1 hM' hCK hUK (fun q hq => J.deadP_slot hX1 hcn hkc hw (J.jcov.dead q hq))
    (J.idleW_keep hX1.fin.1.1.1 (CnStep.of_cnK hcn).idle (CnStep.of_cnK hcn).isc)
    (DXKeep.of_dbg (dbgKeep_of_writes J.blk hw fun _ hb => J.inSlot_notDbg hb) (J.tdkeep_slot hw))
  obtain ⟨hJC, R⟩ := jowes_slotDFB J hX1 hcn hkc hw hFI' hMO hkz hTK hfh' hbs' hDl' hUK hjc horig hutc
  have hpgb : ∀ q vms, σ'.kheap q = some (.archObj (.dataPage false vms)) →
      σ.kheap q = some (.archObj (.dataPage false vms)) := fun q vms h => by
    rcases hkc q with e | ⟨_, _, _, _, h1⟩ | ⟨_, _, _, h1, _⟩
    · rw [← e]; exact h
    · rw [h] at h1; cases h1
    · rw [h] at h1; cases h1
  have hvT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s') :=
    Vs.VsSlotsT.of_some (· = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) (fun y hy hn => hcap y hy hn)
      (fun y _ e => by subst e; exact hvt) (fun y _ e => by subst e; exact hft) (fun y _ e => by subst e; exact hnt)
      fun y _ e => by subst e; exact htt
  have hbf : JBuf (L := L) Z s' σ' := by
    have hpgf : ∀ q vms, σ.kheap q = some (.archObj (.dataPage false vms)) →
        σ'.kheap q = some (.archObj (.dataPage false vms)) := fun q vms h => by
      rcases hkc q with e | ⟨_, _, _, h1, _⟩ | ⟨_, _, h1, _, _⟩
      · rw [e]; exact h
      · rw [h] at h1; cases h1
      · rw [h] at h1; cases h1
    refine ⟨?_, J.fcov.keep subset_rfl hpgb, J.fcap.keepU hvT hpgf⟩
    by_cases e2 : n = 2
    · exact hok e2
    · refine J.bok.keep (J.slot2Fr hkc hX1.rel.2.1.1 fun q hq => Or.inl ?_)
      have hAq : AbsSlot Z.th (q.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨q, rfl, Or.inr ⟨hq, 2, by decide, rfl⟩⟩
      have hne : cslotAddr (q.bv, Fl4Spec.tcbCnodeIndex 2) ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) := fun e => by
        have e' := cslotAddr_inj hP hAq hAd e
        exact e2 (tcbCnodeIndex_inj (by decide) hn (congrArg Prod.snd e')).symm
      have he2 : cslotAddr (q.bv, Fl4Spec.tcbCnodeIndex 2) = slotOf q 2 := by
        show slotAddr q.bv (Fl4Spec.ofBl _) = _
        rw [slotAddr_ofBl, tcbCnodeIndex_blVal 2 (by decide)]
      rw [← he2, capAt_capV, capAt_capV, hcap _ hAq.isSlot hne]
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  have hLv' := LiveDN.insTXB (G := Z.G) (V := Z.vs) J hDS J.live hX1 ⟨hCR', hDl', hFI'⟩ ht hn hci hwS hnull hcap hnn hsh hlive
  have hzD : ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D := fun p hp => J.zD p (ZTcb.of_zombies (fun y hy p zt k hz => by
    by_cases e : y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)
    · obtain ⟨y0, hy0, hsh0⟩ := hsh
      subst e
      exact ⟨y0, hy0, (zombie_of_shape hsh0 hz).trans hz⟩
    · exact ⟨y, hy, by rw [← hcap y hy e]; exact hz⟩) hp)
  exact ⟨Ac, Lst, D, J.cs_frameV (hvn := J.vsShr hX1 hw.1
      (Vs.vsKeep_copy hcap (by rw [hnull]; rfl) (fun hk => (hkr hk).1) (fun hu => (hkr (Vs.tabUn_key hu)).2 hu))
      (Vs.ArchShr.of_objCn hcn.2 (by have e := congrArg Fl4Spec.AbstractState.archState hcn.1; exact e))) hw.1 hX1 (KBack.of_keepCT hkc) hbf hJC R (J.vsc.step hvT)
    hLv' hzD (J.carry.of_objCn hkc) (devFrom_kept J.xtop.rel.2.1.2.2.1 hM' J.ut hUK) (J.carry.vsStep rfl hvT subset_rfl subset_rfl subset_rfl subset_rfl rfl hw.1 (ArchFwd.of_objCn hkc)) (ArchFwd.of_objCn hkc)⟩

/-- `JAtZB.insTJ` at `JAtZ` (via `JAtZ.toB`; `JExt` after by `JExt.step`). -/
theorem JAtZ.insTJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : Nat} {σ' : Fl4Spec.State Unit}
    (hok : n = 2 → Endp.IpcBufCapOK σ') {t : U64} (ht : Z.th t = some .tcb)
    (hn : n < tcbSlots) {c : Fl4Spec.Cap} {src : Fl4Spec.CslotPtr} {s' : S}
    {G' : MdbGhost}
    (hci : Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({((), σ')}, False))
    (hDS' : DState (L := L) Z.th s' σ' G') (hSt : MdbStep (L.mem s) Z.G (L.mem s') G')
    (hwS : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    (hnull : capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) →
      capV (L.mem s') y = capV (L.mem s) y)
    (hnu : isUt (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) = false)
    (hnn : capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) ≠ .Null)
    (hsh : ∃ y0, IsSlot Z.th y0 ∧
      shape (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) = shape (capV (L.mem s) y0))
    (hfh : n = 3 → capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Endpoint ep b0 b1 b2 b3 b4)
    (hbs : n = 2 → Sched.BufSlotOK (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (hlive : ∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .Thread t)
    (hvt : ∀ P L4 L3 L2 L1 : Set U64, Vs.VsSlotsW Z.th P L4 L3 L2 L1 (L.mem s) →
      Vs.VCapW P L4 L3 L2 L1 (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (hft : ∀ U : Nat → Prop, Vs.FrSlots Z.th U (L.mem s) →
      Vs.FrIn U (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (hnt : Vs.VsNat Z.th (L.mem s) → Vs.NativeCap (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (htt : ∀ R, Vs.TabSlots Z.th R (L.mem s) → Vs.TabR R (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))))
    (hkr : Vs.VKey (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) ≠ none →
      (∃ y0, IsSlot Z.th y0 ∧ y0 ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) ∧
        capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = capV (L.mem s) y0) ∧
      ¬ Vs.TabUn (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)))) :
    ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
      JAtZ (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' s' a σ' := by
  obtain ⟨Ac', Lst', D', B'⟩ := J.toB.insTJ hok ht hn hci hDS' hSt hwS hnull hcap hnu hnn hsh hfh hbs hlive hvt hft
    hnt htt hkr
  have hw : P1.WritesIn st s s' (InSlot Z.th) := hwS.mono fun b hb => slotWd_range J.xtop.rel.1 hb
  have hvT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s') :=
    Vs.VsSlotsT.of_some (· = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) (fun y hy hn => hcap y hy hn)
      (fun y _ e => by subst e; exact hvt) (fun y _ e => by subst e; exact hft) (fun y _ e => by subst e; exact hnt)
      fun y _ e => by subst e; exact htt
  exact ⟨Ac', Lst', D', B'.toJAtZ (J.ext.step hvT (J.vkeep_slot hw))⟩

set_option maxHeartbeats 8000000 in
/-- **`IpcBufCapOK` after SetIPCBuffer/Configure's frame insert** (decision 2
of gl11): the new IPC-frame cap of TCB `t` a non-device frame at a nonzero
pointer (`hc`, `hq0`) with the range of the source slot's cap (`hk`, so its
bytes in user frames by `JAtZ.fcap`), aligned (`hcv`), the buffer address
aligned (`hbuf`); the other TCBs' IPC frames kept. -/
theorem JAtZ.bokInstall {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb)
    {c : capability.Cap} {src : Fl4Spec.CslotPtr} {σ' : Fl4Spec.State Unit} {s' : S}
    (hci : Fl4Spec.capInsert (Z := Unit) (absCap c) src (t.bv, Fl4Spec.tcbCnodeIndex 2) σ = ({((), σ')}, False))
    (hR' : StateRel Z.th (L.mem s') σ')
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2) → capV (L.mem s') y = capV (L.mem s) y)
    (hdst : capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) = c)
    {q : U64} {sz : capability.FrameSize} {rr aa va : U64} {m : Bool} (hc : c = .Frame q sz rr false m false aa va)
    (hq0 : q ≠ 0#u64) (hcv : CapValid Z.th c) {y0 : U64} (hy0 : IsSlot Z.th y0)
    (hk : okey c = okey (capV (L.mem s) y0))
    (hbuf : ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbIpcBuffer.toNat % 1024 = 0) :
    Endp.IpcBufCapOK σ' := by
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) (absCap c) src (t.bv, Fl4Spec.tcbCnodeIndex 2) σ).1 := by
    rw [hci]; rfl
  have hkc : KeepCT σ σ' := KeepCT.of_cnK (capInsert_nkn _ _ _ σ _ hmem)
  have hpg : ∀ p vms, σ.kheap p = some (.archObj (.dataPage false vms)) →
      σ'.kheap p = some (.archObj (.dataPage false vms)) := fun p vms h => by
    rcases hkc p with e | ⟨_, _, _, h1, _⟩ | ⟨_, _, h1, _, _⟩
    · rw [e]; exact h
    · rw [h] at h1; cases h1
    · rw [h] at h1; cases h1
  intro t' x hx dev pb R mt vms md he hR
  -- the TCB before
  obtain ⟨x0, hx0, hbx⟩ : ∃ x0, σ.kheap t' = some (.tcb x0) ∧ x.tcbIpcBuffer = x0.tcbIpcBuffer := by
    rcases hkc t' with e | ⟨_, _, _, -, h2⟩ | ⟨x1, y, h1, h2, hco⟩
    · rw [e] at hx; exact ⟨x, hx, rfl⟩
    · rw [hx] at h2; cases h2
    · rw [hx] at h2; cases h2; exact ⟨x1, h1, hco.2.1⟩
  obtain ⟨u, rfl, hu⟩ := J.thOfTcb hx0
  obtain ⟨x', c', hkx, hcap', hcr⟩ := hR'.bufCap hu
  rw [hx] at hkx; cases hkx
  have he2 : cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 2) = slotOf u 2 := by
    show slotAddr u.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, tcbCnodeIndex_blVal 2 (by decide)]
  have hAu : AbsSlot Z.th (u.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨u, rfl, Or.inr ⟨hu, 2, by decide, rfl⟩⟩
  have hAt : AbsSlot Z.th (t.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨t, rfl, Or.inr ⟨ht, 2, by decide, rfl⟩⟩
  by_cases e : u = t
  · subst e
    have hc'e : c' = c := by
      rw [← he2, capAt_capV, hdst] at hcap'; exact (eq_of_ok_eq hcap').symm
    rw [he, hc'e, hc] at hcr
    obtain ⟨-, h2⟩ := hcr
    simp only [absCap] at h2
    injection h2 with h2
    injection h2 with hd hp0 _ _ hsz _
    subst hd
    have hpv : q.val = pb.toNat := by rw [← hp0]; rfl
    have hbits : (fbitsF sz).val = Fl4Spec.pageBitsForSize vms := by rw [fbitsF_val, hsz]
    have hal : pb.toNat % 2 ^ Fl4Spec.pageBitsForSize vms = 0 := by
      rw [hc] at hcv
      have h1 : q.val % 2 ^ frameBitsN sz = 0 := hcv
      have h2 : frameBitsN sz = (fbitsF sz).val := by
        rw [fbitsF_val]; cases sz <;> rfl
      rw [← hpv, ← hbits, ← h2]; exact h1
    have hba : x.tcbIpcBuffer.toNat % 1024 = 0 := by rw [hbx]; exact hbuf x0 hx0
    have hF : Vs.FrIn (UFr σ) c := Vs.FrIn.of_okey hk (J.fcap y0 hy0)
    rw [hc] at hF
    refine ⟨rfl, fun h0 => hq0 (P1.eq_of_bv (by rw [← hp0] at h0; exact h0)), fun k hk128 => ?_, hba, hal⟩
    obtain ⟨r1, r2, -⟩ := buf_frame_rng vms pb x.tcbIpcBuffer k hk128 hal hba
    have hU := hF rfl (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k).toNat
      (by rw [hpv]; exact r1) (by rw [hpv, hbits]; omega)
    have hU' : Fl4Spec.inUserFrame (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& Fl4Spec.mask
        (Fl4Spec.pageBitsForSize vms))) k) σ := by
      unfold UFr at hU; rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hU
    exact inUserFrame_keep hpg hU'
  · have hne : cslotAddr (u.bv, Fl4Spec.tcbCnodeIndex 2) ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2) := fun e' =>
      e (P1.eq_of_bv (congrArg Prod.fst (cslotAddr_inj J.xtop.rel.1 hAu hAt e')))
    obtain ⟨x2, c2, hkx2, hcap2, hcr2⟩ := J.xtop.rel.2.1.1.bufCap hu
    rw [hx0] at hkx2; cases hkx2
    have hcc : c' = c2 := by
      rw [← he2, capAt_capV, hcap _ hAu.isSlot hne] at hcap'
      rw [← he2, capAt_capV] at hcap2
      exact eq_of_ok_eq (hcap'.symm.trans hcap2)
    have hfr : x0.tcbIpcframe = x.tcbIpcframe := by rw [← hcr2.2, ← hcr.2, hcc]
    obtain ⟨h1, h2, h3, h4, h5⟩ := J.bok u.bv x0 hx0 dev pb R mt vms md (by rw [hfr]; exact he) hR
    rw [hbx]
    exact ⟨h1, h2, fun k hk => inUserFrame_keep hpg (h3 k hk), h4, h5⟩

end

/-! ## `SpecGlob` across the insert into a TCB slot -/

section
open Fl4Spec

/-- Every cap of `σ'` is `σ`'s in the same slot, or `c` at `dest`. -/
def InsK (c : Cap) (dest : CslotPtr) (σ σ' : State Unit) : Prop :=
  ∀ p cref a, capOpt (σ'.kheap p) cref = some a → ((p, cref) = dest ∧ a = c) ∨ capOpt (σ.kheap p) cref = some a

/-- Every outcome of `m` is `InsK`-related to its start. -/
def NIK (c : Cap) (dest : CslotPtr) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → InsK c dest σ x.2

theorem nik_bind {c : Cap} {dest : CslotPtr} {α β : Type} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : NIK c dest m) (hg : ∀ a, NIK c dest (g a)) : NIK c dest (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩ p cref a ha
  rcases hg y.1 y.2 x hx p cref a ha with h | h
  · exact Or.inl h
  · exact hm σ y hy p cref a h

theorem nik_of_kh {c : Cap} {dest : CslotPtr} {α : Type} {m : NonDet (State Unit) α} (h : KhK m) :
    NIK c dest m := fun σ x hx p cref a ha => Or.inr (by have e : x.2.kheap = σ.kheap := h σ x hx; rw [← e]; exact ha)

theorem nik_setCap (c : Cap) (dest : CslotPtr) : NIK c dest (setCap (Z := Unit) c dest) := by
  obtain ⟨o, r⟩ := dest
  intro σ x hx p cref a ha
  rcases setCap_capOpt hx p cref a ha with ⟨e1, e2, e3⟩ | ⟨-, h⟩
  · exact Or.inl ⟨by rw [e1, e2], e3⟩
  · exact Or.inr h

/-- **`cap_insert` of a non-untyped cap writes only the cap at its
destination** (`set_untyped_cap_as_full` then does nothing). -/
theorem nik_capInsert {c : Cap} (hnu : ¬ isUntypedCap c = true) (src dest : CslotPtr) :
    NIK c dest (capInsert (Z := Unit) c src dest) := by
  have hg : ∀ sl : CslotPtr, KhK (getCap (Z := Unit) sl) := fun sl => by
    obtain ⟨o, r⟩ := sl; unfold getCap; kh_auto
  unfold capInsert
  refine nik_bind (nik_of_kh (hg _)) (fun srcCap => ?_)
  refine nik_bind (nik_of_kh (dk_pure _)) (fun _ => ?_)
  refine nik_bind (nik_of_kh (hg _)) (fun _ => ?_)
  refine nik_bind (nik_of_kh (dk_assert _)) (fun _ => ?_)
  refine nik_bind ?_ (fun _ => ?_)
  · unfold setUntypedCapAsFull
    rw [if_neg (fun h => hnu h.2.1)]
    exact nik_of_kh (dk_pure _)
  refine nik_bind (nik_setCap _ _) (fun _ => ?_)
  exact nik_of_kh (by unfold updateCdt setCdt setOriginal; kh_auto)

/-- **`SpecGlob` across an `InsK` step** writing, off the IRQ node, a cap
naming no more objects than a non-frame cap of `σ` (or a frame cap). -/
theorem SpecGlob.ins {c : Cap} {dest : CslotPtr} {σ σ' : State Unit} (h : SpecGlob σ) (hk : InsK c dest σ σ')
    (hn : σ'.interruptIrqNode = σ.interruptIrqNode) (hi : σ'.idleThread = σ.idleThread)
    (hd : ∀ irq, dest ≠ (σ.interruptIrqNode irq, []))
    (hc : ¬ IsPageCap c → ∃ p0 cref0 a0, capOpt (σ.kheap p0) cref0 = some a0 ∧ ¬ IsPageCap a0 ∧
      objRefs c ⊆ objRefs a0) : SpecGlob σ' := by
  refine ⟨fun irq a ha => ?_, fun p cref a ha hpa => ?_, fun p cref a ha hpa => ?_⟩
  · rw [hn] at ha
    rcases hk _ _ _ ha with ⟨e, -⟩ | h'
    · exact absurd e.symm (hd irq)
    · exact h.irq irq a h'
  · intro irq
    rw [hn]
    rcases hk _ _ _ ha with ⟨-, rfl⟩ | h'
    · obtain ⟨p0, cref0, a0, h0, hp0, hsub⟩ := hc hpa
      exact fun hm => h.ref p0 cref0 a0 h0 hp0 irq (hsub hm)
    · exact h.ref p cref a h' hpa irq
  · rw [hi]
    rcases hk _ _ _ ha with ⟨-, rfl⟩ | h'
    · obtain ⟨p0, cref0, a0, h0, hp0, hsub⟩ := hc hpa
      exact fun hm => h.idle p0 cref0 a0 h0 hp0 (hsub hm)
    · exact h.idle p cref a h' hpa

end

/-- `shape` keeps the objects a cap names and whether it is a frame cap. -/
theorem absCap_shape_refs (c : capability.Cap) :
    Fl4Spec.objRefs (absCap (shape c)) = Fl4Spec.objRefs (absCap c) ∧
      (IsPageCap (absCap (shape c)) ↔ IsPageCap (absCap c)) := by
  cases c <;> simp [shape, absCap, Fl4Spec.objRefs, IsPageCap, Fl4Spec.aobjRef]

/-- **`SpecGlob` across the insert into a TCB slot** of a non-untyped cap
with the shape of a cap of `σ` (`nik_capInsert`, `SpecGlob.ins`; a TCB slot
is no IRQ node slot). -/
theorem SpecGlob.insTcb {σ σ' : Fl4Spec.State Unit} (h : SpecGlob σ) {nc c0 : capability.Cap}
    {src : Fl4Spec.CslotPtr} {t : U64} {n : Nat}
    (hins : Fl4Spec.capInsert (Z := Unit) (absCap nc) src (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({((), σ')}, False))
    (hnut : isUt nc = false) (hsh : shape nc = shape c0)
    (hsrc : capOpt (σ.kheap src.1) src.2 = some (absCap c0)) : SpecGlob σ' := by
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) (absCap nc) src (t.bv, Fl4Spec.tcbCnodeIndex n) σ).1 := by
    rw [hins]; rfl
  have hnu : ¬ Fl4Spec.isUntypedCap (absCap nc) = true := by
    cases nc <;> simp_all [isUt, absCap, Fl4Spec.isUntypedCap]
  have hk := nik_capInsert hnu src _ σ _ hmem
  have hgk := gk_capInsert (absCap nc) src (t.bv, Fl4Spec.tcbCnodeIndex n) σ _ hmem
  have hr := absCap_shape_refs nc
  have hr0 := absCap_shape_refs c0
  rw [hsh] at hr
  refine h.ins hk (congrArg Prod.fst hgk) (congrArg Prod.snd hgk) (fun irq e => ?_)
    (fun hp => ⟨src.1, src.2, absCap c0, hsrc, fun h0 => hp (hr.2.1 (hr0.2.2 h0)), fun x hx => ?_⟩)
  · have h2 := congrArg Prod.snd e
    simp [Fl4Spec.tcbCnodeIndex, Fl4Spec.toBl] at h2
  · rw [← hr.1, hr0.1] at hx; exact hx

/-! ## An install's outcome with an invariant after Ok and one after a preemption -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- `InstPostW` (TcbCaps) with `W` after an Ok install and `Wp` after a
preempted one. -/
def InstPostWP (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (t : U64)
    (m : Fl4Spec.PMonad Unit Unit) (s : S) (σ : Fl4Spec.State Unit)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ' G', ((res.1 = .Ok () ∧ (.ok (), σ') ∈ (m.run σ).1 ∧ InstFr th t (L.mem s) (L.mem res.2.1) ∧
        W res.2.1 res.2.2 σ' G') ∨
      (res.1 = .Err .Preempted ∧ (.error (), σ') ∈ (m.run σ).1 ∧ Wp res.2.1 res.2.2 σ' G')) ∧
    DState (L := L) th res.2.1 σ' G'

theorem inst_seqWP {W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap} {t : U64} {s0 : S}
    {σ : Fl4Spec.State Unit} {m1 m2 : Fl4Spec.PMonad Unit Unit}
    {P : Result (core.result.Result Unit error.Exc × S × A)}
    {K : S → A → Result (core.result.Result Unit error.Exc × S × A)}
    (h1 : P ⦃ res => InstPostWP (L := L) W Wp th t m1 s0 σ res ⦄)
    (h2 : ∀ s1 a1 σ1 G1, DState (L := L) th s1 σ1 G1 → (.ok (), σ1) ∈ (m1.run σ).1 →
      InstFr th t (L.mem s0) (L.mem s1) → W s1 a1 σ1 G1 →
      K s1 a1 ⦃ res => InstPostWP (L := L) W Wp th t m2 s0 σ1 res ⦄) :
    (do
      let (r, s1, a1) ← P
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ => K s1 a1
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame error.Exc) residual
        ok (r1, s1, a1)) ⦃ res => InstPostWP (L := L) W Wp th t (m1 >>= fun _ => m2) s0 σ res ⦄ := by
  apply WP.spec_bind h1
  rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hcase, hDS1⟩
  rcases hcase with ⟨hr, hmem, hcz, hW1⟩ | ⟨hr, hmem, hW1⟩
  · simp only at hr; subst hr
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_mono (h2 s1 a1 σ1 G1 hDS1 hmem hcz hW1) ?_
    rintro res ⟨σ2, G2, hc2, hDS2⟩
    refine ⟨σ2, G2, ?_, hDS2⟩
    rcases hc2 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, mem_bindE_ok hmem h2, h3, h4⟩
    · exact Or.inr ⟨h1, mem_bindE_ok hmem h2, h3⟩
  · simp only at hr; subst hr
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok, bind_tc_ok]
    rw [WP.spec_ok]
    exact ⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem, hW1⟩, hDS1⟩

theorem inst_skipWP {W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap} {t : U64} {s0 : S}
    {σ : Fl4Spec.State Unit} {m2 : Fl4Spec.PMonad Unit Unit}
    {P : Result (core.result.Result Unit error.Exc × S × A)}
    (h : P ⦃ res => InstPostWP (L := L) W Wp th t m2 s0 σ res ⦄) :
    P ⦃ res => InstPostWP (L := L) W Wp th t (Fl4Spec.NonDetE.returnOk () >>= fun _ => m2) s0 σ res ⦄ := by
  have e : ∀ x, x ∈ ((Fl4Spec.NonDetE.returnOk () >>= fun _ => m2 : Fl4Spec.PMonad Unit Unit).run σ).1 ↔
      x ∈ (m2.run σ).1 := by
    intro x; rw [run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.PMonad Unit Unit)) rfl]
  refine WP.spec_mono h ?_
  rintro res ⟨σ', G', hc, hDS⟩
  refine ⟨σ', G', ?_, hDS⟩
  rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1, (e _).2 h2, h3, h4⟩
  · exact Or.inr ⟨h1, (e _).2 h2, h3⟩

theorem inst_doneWP {W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap} {t : U64} {s0 s : S}
    {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hDS : DState (L := L) th s σ G) (hW : W s a σ G) (hcz : InstFr th t (L.mem s0) (L.mem s)) :
    (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s, a) :
      Result (core.result.Result Unit error.Exc × S × A)) ⦃ res =>
      InstPostWP (L := L) W Wp th t (Fl4Spec.NonDetE.returnOk ()) s0 σ res ⦄ := by
  rw [WP.spec_ok]
  exact ⟨σ, G, Or.inl ⟨rfl, rfl, hcz, hW⟩, hDS⟩

end

/-! ## The IPC buffer's word, and a scheduler step, at `J` -/

/-- A scheduler step (`SchedK`) keeps what `PPR0` reads. -/
theorem PPK.of_schedK {σ σ' : Fl4Spec.State Unit} (h : SchedK σ σ')
    (hns : ∀ u, σ'.schedulerAction ≠ .switchThread u) (hq : σ'.readyQueues = σ.readyQueues) : PPK σ σ' :=
  ⟨h.cons, h.ctime, h.csc, fun u hu => by rw [h.rel] at hu; exact hu,
    fun p y n hp => by rw [h.kh] at hp; exact hp, fun p y hp => ⟨y, by rw [h.kh] at hp; exact hp, rfl, id⟩, h.ct, h.idle,
    fun _ => hns, fun p x y hx hp hi => by rw [h.kh, hx] at hp; cases hp; exact Or.inl hi,
    fun h0 => by unfold CtNQ; rw [hq, h.ct]; exact h0⟩

/-- `reschedule_required` without a pending switch keeps the ready queues
(kp16). -/
theorem rq_of_resched {σ σ' : Fl4Spec.State Unit} (hn : ∀ t, σ.schedulerAction ≠ .switchThread t)
    (h : Fl4Spec.rescheduleRequired (Z := Unit) σ = ({((), σ')}, False)) : σ'.readyQueues = σ.readyQueues := by
  rw [Sched.rescheduleRequired_noswitch hn] at h
  have e := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h))).2
  rw [← e]

/-- An update of one TCB keeping its SC keeps what `PPR0` reads. -/
theorem PPK.updTcbSc {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x y : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hy : y.tcbSchedContext = x.tcbSchedContext)
    (hb : NotBlk x.tcbState → NotBlk y.tcbState := by first | exact id | (intro _; exact ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ _ h => by cases h⟩))
    (hi : x.tcbState = .inactive → y.tcbState = .inactive ∨ t = σ.curThread := by exact fun h => Or.inl h) :
    PPK σ (Notif.updK σ t (.tcb y)) := by
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun p z n hp => ?_, fun p z hp => ?_, rfl, rfl, fun h => h,
    fun p x' z hx hp hi' => ?_, fun h => h⟩
  rotate_right
  · by_cases e : p = t
    · subst e; rw [hk] at hx; cases hx; simp [Notif.updK] at hp; subst hp; exact hi hi'
    · simp [Notif.updK, e, hx] at hp; subst hp; exact Or.inl hi'
  · by_cases e : p = t
    · subst e; simp [Notif.updK] at hp
    · simpa [Notif.updK, e] using hp
  · by_cases e : p = t
    · subst e; simp [Notif.updK] at hp; subst hp; exact ⟨x, hk, hy.symm, hb⟩
    · exact ⟨z, by simpa [Notif.updK, e] using hp, rfl, id⟩

/-- The IPC-buffer update of one TCB empties and writes no cap. -/
theorem SlotK.ipcBuf {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (b : Fl4Spec.VSpaceRef) :
    SlotK σ (Notif.updK σ t (.tcb { x with tcbIpcBuffer := b })) := by
  intro p cref a ha
  right
  by_cases e : p = t
  · subst e
    rw [hk]
    simp only [Notif.updK, Function.update_self] at ha
    have e2 : capOpt (some (.tcb { x with tcbIpcBuffer := b })) cref =
        capOpt (some (.tcb x)) cref := rfl
    rw [e2] at ha; exact ha
  · simpa [Notif.updK, e] using ha

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

open Fl4Proofs.P1 Fl4Proofs.P3.Sched in
set_option maxHeartbeats 8000000 in
/-- **A TCB's IPC-buffer word at `J`** (as XTopJointTcbSched's
`JAtZ.mcpWrJ`): FL4's word (offset 3512; P1's `BlkOK` by `plainW_all`),
the spec's `tcb_ipc_buffer` (`XTopAt.bufSpec`, a `QKM` step), `BufWordRel`
by XTopBuf's `bufWordRel_setIpc`; the other fields as `JAtZ.mcpWrJ`. -/
theorem JAtZ.bufWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (v : U64) (hnf : x.tcbIpcframe = .nullCap) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s (tIpcBufA t) v) a
      (Notif.updK σ t.bv (.tcb { x with tcbIpcBuffer := v.bv })) := by
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hta := hT t ht
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hKt : (tIpcBufA t).val = t.val + 3512 := tIpcBufA_val hta
  have hwa : P1.Aligned (tIpcBufA t) := tIpcBufA_aligned hta
  set s' := L.wr s (tIpcBufA t) v with hs'
  set σ' := Notif.updK σ t.bv (.tcb { x with tcbIpcBuffer := v.bv }) with hσ'
  have hw : P1.WritesIn st s s' (· = tIpcBufA t) := P1.writesIn_wr hwa
  obtain ⟨hblk, hfoot0, -⟩ := P1.plainW_all (K := 3512#u64) (v := v) J.blk htH (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hfoot : P1.WritesIn st s (L.wr s (tIpcBufA t) v) (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s) := hfoot0
  have hA : QKM σ σ' := QKM.ipcBuf hk v.bv
  have hX' : XTopAt (L := L) AR Z s' a σ' := (J.xtop.bufWr ht v).bufSpec (tcbBufStep_upd hk v.bv)
  have hks : L.ksb s' = L.ksb s := hw.1
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hwW : P1.WritesIn st s s' (WideW (st := st) Z.T Z.N Z.C Z.c s σ) :=
    hw.mono fun b hb => Or.inl ⟨t, ht, by rw [hb, hKt]; omega, by rw [hb, hKt]; omega⟩
  -- the words other than `t`'s IPC-buffer word kept
  have keep : ∀ b, P1.Aligned b → b ≠ tIpcBufA t → L.mem s' b = L.mem s b := fun b hb hne =>
    hw.mem_eq hb hne
  have hBW : BufWordRel Z.T (L.mem s') σ' := bufWordRel_setIpc J.xtop ht hk v J.buf
  have hI3 := hX'.irelK (by rw [hks]; exact J.ks) hBW
  have hI := J.xtop.irelK J.ks J.buf
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw fun b hb =>
    Or.inr (Or.inr (Or.inl ⟨t, ht, by rw [hb, hKt]; omega, by rw [hb, hKt]; omega⟩))
  have hck : Fl4Proofs.P3.CKeep σ σ' := hA.ckeepP
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 hAR hF.1 hck.cdt hck.orig hck.ks hF.2
  -- the MCP, yield, SC-reply and reply-link words: not `t`'s IPC-buffer word
  have k1 : ∀ u ∈ Z.T, L.mem s' (mcpA u) = L.mem s (mcpA u) ∧ L.mem s' (flagsA u) = L.mem s (flagsA u) := fun u hu =>
    ⟨keep _ (mcpA_aligned hT hu) fun e => by
      have h1 := mcpA_val hT hu
      rw [e, hKt] at h1
      have a1 := (hT t ht).align; have a2 := (hT u hu).align
      by_cases eu : u = t
      · subst eu; omega
      · have := val_ne_of_ne eu; omega,
    keep _ (flagsA_aligned hT hu) fun e => by
      have h1 := flagsA_val hT hu
      rw [e, hKt] at h1
      have a1 := (hT t ht).align; have a2 := (hT u hu).align
      by_cases eu : u = t
      · subst eu; omega
      · have := val_ne_of_ne eu; omega⟩
  have k2 : ∀ u ∈ Z.T, L.mem s' (yieldA u) = L.mem s (yieldA u) := fun u hu =>
    keep _ (yieldA_aligned hT hu) fun e => by
      have h1 := yieldA_val hT hu
      rw [e, hKt] at h1
      have a1 := (hT t ht).align; have a2 := (hT u hu).align
      by_cases eu : u = t
      · subst eu; omega
      · have := val_ne_of_ne eu; omega
  have k3 : ∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q) := fun q hq =>
    keep _ (sc_reply_word hS hq).1 fun e => by
      obtain ⟨y, n, hky, -⟩ := hs.scs q hq
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hHq := (hJ.sc q y n (J.c0 q hq) hky).2
      have hz := J.kern.heap.scmin q _ hHq
      have h128 : 2 ^ 7 ≤ 2 ^ (n + Fl4Spec.minSchedContextBits) := Nat.pow_le_pow_right (by norm_num) hz
      have hv := (sc_reply_word hS hq).2.1
      rw [e, hKt] at hv
      have hne : q ≠ t := fun e' => by rw [e', J.zH.1 t ht] at hHq; cases hHq
      have := J.kern.heap.disj q _ t _ hHq (J.zH.1 t ht) hne
      simp only [P1.HKind.bits] at this
      omega
  have k4 : ∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r) := by
    intro r hr
    have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
      keep _ (J.rp.aligned hr ha) fun e => by
        have := J.rp.tcb r hr t ht; rw [e, hKt] at ha; omega
    exact ⟨k _ (Or.inl h8), k _ (Or.inr h16)⟩
  have ck := hA.callKeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hA.khrb
  have hDbg := J.kw_dbg (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hKd := J.kw_dbgKeep (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hI3.2.2.1
  have hAI3 : ActIdle σ' := hA.actIdle J.act
  have hyk : YKeep σ σ' := by
    refine ⟨fun q y hq => ?_, fun q y n hq => ?_, fun q y n hq => ?_⟩
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq; exact ⟨{ x with tcbIpcBuffer := v.bv }, by simp [hσ', Notif.updK], rfl⟩
      · exact ⟨y, by simp [hσ', Notif.updK, e, hq], rfl⟩
    · by_cases e : q = t.bv
      · subst e; rw [hk] at hq; cases hq
      · exact ⟨y, by simp [hσ', Notif.updK, e, hq], rfl⟩
    · by_cases e : q = t.bv
      · subst e; simp [hσ', Notif.updK] at hq
      · exact ⟨y, by simpa [hσ', Notif.updK, e] using hq, rfl⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_qm hA hS3 hI3.1 hwW k3 hAI3.1 (J.yld.frame k2 hyk) hyk
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hA.szKeep q.bv y n hq) hks (J.wideW_irq hwW)
      (J.idleW_keep hS3 hA.idle hA.isc).2⟩
  have hkern := J.kern_keep hks hwW.2.1 hS3 hA.ct hA.csc (fun sl h => Or.inl (by rw [← hA.orig]; exact h))
    (by rw [hA.arch])
    (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 hyk, J.mcp.frame k1 (mcpKeep_buf hk v.bv), hBW, hRP',
      J.apart.sc_frame hks hA.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 hA.idle hA.isc)
        (DXKeep.of_dbg hKd (J.tdkeep_of hw fun b hb u hu e => Ipc.tw_ne (a := b) hT ht hu (K0 := 3512) (K := 3528)
          (by rw [hb, hKt]) (by omega) (by omega) (by omega) (by rw [e]; exact J.tdA_val' hu))), hkern,
      J.wideW_utc hwW hF.1 hA.cdt hA.orig hA.arch hDbg, hA.nsc J.nsc, J.inv.updSame hk rfl rfl (Or.inl rfl), hA.cur J.cur,
      hA.own J.own, hA.off J.off, hAI3, hA.bsa J.bsa, hA.isorted J.isorted, hA.curRunM J.curRun, hblk⟩
  have hC0 := JCs.same J hF.1 hA.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameIS hks hX3 hw (fun b hb => WideW.oobj (st := st) (T := Z.T) (N := Z.N) (C := Z.C) (c := Z.c) (σ := σ)
      (Or.inl ⟨t, ht, by rw [hb, hKt]; omega, by rw [hb, hKt]; omega⟩))
      (fun b hb u hu => Sched.tVcpuA_ne (K := 3512) hT ht hu (by rw [hb, hKt]) (by omega) (by omega)) hA.arch (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hA.szKeep hF.1 hA.kback (J.bfK (IpcFrKeep.of_nullFrame hk hnf) (Vs.VsSlotsT.of_eq fun y hy => hF.1.capV hy)) hC R
      (dbgKeep_of_writes J.blk hw fun b hb => J.tcbw_notDbg ht (K := 3512) (by rw [hb, hKt]) (by omega)) hA.orig
      (XTopAt.idleW_eqS J.xtop hX3 hA.idle) J.zD⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

set_option maxHeartbeats 8000000 in
/-- **TcbCaps' `BufHypW` at the deletion loop's invariant `WJR`**: the
IPC-buffer word and `thread_set` by `JAtZ.bufWrJ` (the scheduler action and
`PPR0` kept: `PPK.updTcbSc`); the tail's `reschedule_required` of the
current thread as a scheduler step (`JAtZ.schedJ`; after it the action is
`choose_new_thread`), with the spec's `ActReady` at the state's `JAtZ`
(`Sched.Inv.actReady`). -/
theorem bufHypW_J {t : U64} (ht : Z.th t = some .tcb) (kb addr : U64) :
    BufHypW (L := L) (WJR (L := L) arI AR Z H Cs kb) Z.th t addr addr.bv := by
  refine ⟨fun s a σ G hDS hW hnull => ?_, fun s a σ G _ hW => ?_⟩
  · obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩ := hW
    have hX := J.xtop
    have htT : t ∈ Z.T := J.thT t ht
    obtain ⟨Q, R0, hc, hs⟩ := hX.fin.1.1.1.lists
    obtain ⟨x, hk, -⟩ := hs.tcb t htT
    have hta := hc.tcbs t htT
    have hwa : P1.Aligned (tIpcBufA t) := tIpcBufA_aligned hta
    refine WP.spec_mono (set_ipc_buffer_wr s t addr) ?_
    rintro s' rfl
    have hstep := tcbBufStep_upd hk addr.bv
    obtain ⟨V', J'⟩ := J.bufWrJ htT hk addr (ipcframe_null_of hX.rel.2.1.1 ht hk hnull)
    refine ⟨hX.slotsSame_of (P1.writesIn_wr hwa) (fun b hb => by subst hb; exact tcb_oobj htT hta (by decide) (by decide)),
      _, ?_, J'.xtop.rel.2.1, hstep.ksub, V', Ac, Lst, D, J', by rw [L.ksb_wr]; exact hkb, fun u e => hns u e,
      hsg.of_slotK (SlotK.ipcBuf hk addr.bv) rfl rfl, hp0.of_ppk (PPK.updTcbSc hk rfl)⟩
    rw [Notif.threadSet_eq _ hk]; rfl
  · obtain ⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩ := hW
    have hX := J.xtop
    have hS := hX.fin.1.1.1
    obtain ⟨Q, R0, hc, hs⟩ := hS.lists
    have hcur : σ.curThread = (L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)).bv := by
      rw [hs.curThread, hc.cur]; rfl
    rw [cur_thread_eq]
    simp only [bind_ok, tcb_eq_ct]
    by_cases e : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    · simp only [e, decide_true, ↓reduceIte]
      have hA1 : Notif.ActReady σ := J.inv.actReady
      obtain ⟨σ', hres, hK', hdl', hds'⟩ := rescheduleRequired_k hA1
      have hN := hX.fin.1.1.2.2.1
      refine WP.spec_bind (WP.spec_and (WP.spec_and (Sched.reschedule_required_refines s _ hN hS hA1)
        (Sched.reschedule_required_sfootI hS)) (spec_self (Sched.reschedule_required_sfootI hS))) ?_
      rintro s5 ⟨⟨⟨σ3, he3, -, -, -, -⟩, hw⟩, hrun5⟩
      rw [hres] at he3
      have e3 : σ3 = σ' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he3))).2.symm
      subst σ3
      obtain ⟨Ac5, Lst5, D5, J5⟩ := J.schedJ (schedStep_resched hA1 hrun5 hres hK' hdl' hds')
      have hact5 := Sched.rescheduleRequired_action hA1 hres
      have hgk := gk_rescheduleRequired' σ ((), σ') (by rw [hres]; rfl)
      rw [WP.spec_ok]
      refine ⟨rfl, rfl, hX.slotsSame_of hw (fun b hb => sfootI_oobj hc.tcbs hb), σ', ?_, J5.xtop.rel.2.1,
        KSub.of_kheap hK'.kh, V, Ac5, Lst5, D5, J5, by rw [hw.1]; exact hkb,
        (fun u e' => by rw [hact5] at e'; cases e'), hsg.of_eq hK'.kh (congrArg Prod.fst hgk) (congrArg Prod.snd hgk),
        hp0.of_ppk (PPK.of_schedK hK' (fun u e' => by rw [hact5] at e'; cases e') (rq_of_resched hns hres))⟩
      refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE_ok (x := (σ.curThread, σ)) rfl) ?_
      have hb : t.bv = σ.curThread := by rw [hcur, e]
      simp only [Fl4Spec.NonDet.when, hb, ↓reduceIte]
      exact mem_liftE_ok (x := ((), σ')) (by rw [hres]; rfl)
    · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨trivial, trivial, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, σ, ?_, hX.rel.2.1, KSub.refl σ, V, Ac, Lst, D, J, hkb,
        hns, hsg, hp0⟩
      refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE_ok (x := (σ.curThread, σ)) rfl) ?_
      have hb : ¬ t.bv = σ.curThread := fun h => e (P1.eq_of_bv (h.trans hcur))
      simp only [Fl4Spec.NonDet.when, hb, ↓reduceIte]
      exact mem_liftE_ok (x := ((), σ)) rfl

end

/-! ## The install at `J` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

/-- **An invariant of the TCB installs at `J`** (module docstring): `WJR`
at the base sets, kept by an insert into an empty TCB slot of a cap alike an
existing one (`WJR` after it given), with TcbCaps' `BufHypW` at it. -/
structure InsWJ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) : Prop where
  wjr : ∀ s a σ G, W s a σ G → WJR (L := L) arI AR Z H Cs kb s a σ G
  ins : ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G G' : MdbGhost) (t : U64) (n : Nat)
      (c : Fl4Spec.Cap) (src : Fl4Spec.CslotPtr),
    DState (L := L) Z.th s σ G → W s a σ G → DState (L := L) Z.th s' σ' G' →
    WJR (L := L) arI AR Z H Cs kb s' a σ' G' → Z.th t = some .tcb → n < tcbSlots →
    Fl4Spec.capInsert (Z := Unit) c src (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({((), σ')}, False) →
    P1.WritesIn st s s' (Sched.SlotWd Z.th) →
    capV (L.mem s) (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null →
    (∀ y, IsSlot Z.th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) → capV (L.mem s') y = capV (L.mem s) y) →
    capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) ≠ .Null →
    (∃ y0, IsSlot Z.th y0 ∧
      shape (capV (L.mem s') (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n))) = shape (capV (L.mem s) y0)) →
    (∃ y, IsSlot Z.th y ∧ capV (L.mem s) y = .Thread t) →
    W s' a σ' G'
  buf : ∀ t, Z.th t = some .tcb → ∀ addr : U64, BufHypW (L := L) W Z.th t addr addr.bv

/-- **`InsWJ` at `WJR`** (every insert's `WJR` after given; `bufHypW_J`). -/
theorem insWJ_wjr (kb : U64) : InsWJ (L := L) arI AR Z H Cs kb (WJR (L := L) arI AR Z H Cs kb) :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ _ _ _ _ _ => h,
    fun _ ht addr => bufHypW_J arI ht kb addr⟩

end

/-! ## The caller's restart, and the Thread cap's labels at `J` with a preemption -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}
  {s : S} {ar : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **The caller's restart at `J`** (`tcb::restart_caller`): FL4's and the
spec's (`restart_dstate`), `XTopAt` after (`XTopAt.restart`), the rest by
`jowes_restart`; no switch pending after (`Entered`), the idle thread kept. -/
theorem JAtZ.restartJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∃ s1 σ1 x, tcb.restart_caller st s = ok s1 ∧
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      σ.kheap ct.bv = some (.tcb x) ∧ σ.curThread = ct.bv ∧
      σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv ∧
      (∀ u, σ1.schedulerAction = .switchThread u → False) ∧ σ1.idleThread = σ.idleThread ∧
      σ1.curThread = σ.curThread ∧ sched.set_thread_state st s ct sched.TS_RESTART = ok s1 ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s1 ar σ1 := by
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨J.xtop.rel.2.1, J.del, J.xtop.rel.2.2.1⟩
  obtain ⟨s1, σ1, hrc1, hs1, hst1, -, -, -, -, -⟩ :=
    restart_dstate Z.th J.xtop.rel.1 s σ Z.G hDS ct hct hcur htcb J.kern.act
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    have hst := hst1
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  have h := XTopAt.restart J.xtop hcur hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨hX1, hSS, hk1⟩ := h
  obtain ⟨hkb, hkz⟩ := kback_ksz_upd (σ' := Notif.stsAct (Notif.updK σ ct.bv
    (.tcb { x with tcbState := .restart })) ct.bv) hk (by rw [stsAct_kheap]; rfl)
  obtain ⟨Ac', Lst', J1⟩ := J.restartSJ (jStepHyps arI) hcur hk htcb hrun hs1
  refine ⟨s1, σ1, x, hrc1, hst1, hk, hcur, e, ?_, ?_, ?_, hs1, Ac', Lst', D, ?_⟩
  · subst e
    intro u e
    unfold Notif.stsAct at e
    split_ifs at e
    all_goals first
      | (have e2 : σ.schedulerAction = .switchThread u := e
         rw [hni.2] at e2; cases e2)
      | cases e
  · subst e; unfold Notif.stsAct; split_ifs <;> rfl
  · subst e; exact (stsAct_fields _ _).2.1
  · subst e; exact J1


end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `tcb::decode` at one label keeping `X`, `XP` after a preemption
(`TopPostDMXP`). -/
abbrev TcbOKXP (X XP : S → A → Fl4Spec.State Unit → Prop) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl : U64)
    (p : U64) (c : tcb.Ctx) (blk call don : Bool) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) : Prop :=
  tcb.decode st arI s ar lbl p c ⦃ res =>
    TopPostDMXP (L := L) X XP σ blk call don (specDec false slbl args ci sl (.Thread p) excaps buffer) s res ⦄

/-- **A Thread cap label's `XCapP` from its `TcbOKXP`** (as
`decode_invocation_threadX` for one label; the fast-path flag's decode
error at the start's `X`). -/
theorem xcapP_of_tcb {X XP : S → A → Fl4Spec.State Unit → Prop} (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (hX0 : X s ar σ) (lbl length slot p : U64) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (h : TcbOKXP (L := L) arI X XP s ar σ lbl p ⟨length, buf, call, slot, extra⟩ blk call don slbl args ci sl
      excaps buffer) :
    XCapP (L := L) arI X XP s ar σ lbl length slot (.Thread p) blk call don fp buf extra slbl args ci sl excaps buffer
      ct := by
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    refine Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ?_⟩
    show if _ = _ then _ else _
    rw [if_neg (by simp)]
    exact hX0

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The caller's restart at the deletion loop's invariant**: `JAtZ.restartJ`,
with `NoSwitch` after (`Entered`), `SpecGlob` (`SpecGlob.sts`) and `PPR0` kept
(`PPK.restart`). -/
theorem JAtZ.restartWJR {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    ∃ s1 σ1, tcb.restart_caller st s = ok s1 ∧
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      DState (L := L) Z.th s1 σ1 Z.G ∧ WJR (L := L) arI AR Z H Cs (L.ksb s1) s1 ar σ1 Z.G ∧
      SlotsSame Z.th (L.mem s) (L.mem s1) := by
  obtain ⟨s1, σ1, x1, hrc, hst1, hk, hcur, e1, hns1, -, -, -, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨s1', σ1', hrc', -, -, hS1, -⟩ := restart_dstate Z.th J.xtop.rel.1 s σ Z.G J.dstate ct hct hcur htcb J.kern.act
  rw [hrc] at hrc'
  cases eq_of_ok_eq hrc'
  have hp1 : PPR0 σ1 := by rw [e1]; exact hP0.of_ppk (PPK.restart hk .restart (Or.inl hcur.symm))
  exact ⟨s1, σ1, hrc, hst1, J1.dstate, ⟨Z.vs, Ac1, Lst1, D1, J1, rfl, hns1, SpecGlob.sts (mem_of_single hst1) hsg,
    hp1⟩, hS1⟩

/-- The caller's restart from `s` establishes `W` (for `JAtZ.restartW`). -/
abbrev RestartWJ (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) : Prop :=
  ∀ ct, sched.cur_thread st s = ok ct → ∀ s1 σ1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) → W s1 ar σ1 Z.G

end

end

end Fl4Proofs.P3

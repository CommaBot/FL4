/-
# P2 (line pte, generation 15): `mv` discharged — the PageMap slot with `PmObl6` (no `blk`, no `mv`)

* `stepOKV_ofOwnPm` (invj's `stepOKV_of_own`, InvDelPteMoveP, verbatim but renamed): with no VCPU, `StepOK` for
  `own` is `StepOK` for `ownV`;
* **`pm_mvG`**: gen 11's [W] `PmMoveW` at `PmPreG` under `RegionOKP K`, `UserOKP K` (invj's `invMovePP` route): the
  accepted run on `gd st (PmRSU s) (PWs …)` by `inv_acc_gen2` with the block from `pmAccG2` (`STATE` per value by
  `OwnMap.gds_write_state`, the slot's `CAP0` by `OwnMap.gds_write_cap0`, `CAP1` / PTE / user words as `PW`
  non-decision words) and `pmFinG`, then the program tree (`pm_isProgOn`, `inv_hp`), `OwnMap.run_gds_mguard` (the
  start memory's `AFFINITY` agreement is `IoQ`'s, inside `PmPreG` — no ∀-Pre premise) and `interp_mguard_mono`
  (`stepOKP_of_stepOKV ∘ stepOKV_ofOwnPm`, `K.vcpus = ∅` from `GateEp`);
* `PmObl6` = [W] `roA`, [P] `cs`, [P] `lk`; `pmPathsJ`, `StartPmJ`, `pm_hSFQJ`, **`serializable_fl4_localW11PRIPmJ`**.

Premises of `serializable_fl4_localW11PRIPmJ` beyond `serializable_fl4_localW11PR`'s (`B : PmObl6`): [W] `roA`,
[P] `cs`, [P] `lk`. (Not named `…Pm3`: [W] `roA` remains.)

No new named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmMvB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame fld)

noncomputable section

section mv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- At a layout with no VCPU, `StepOK` for `own` is `StepOK` for `ownV` (invj's `stepOKV_of_own`). -/
theorem stepOKV_ofOwnPm {K : KLayoutP} (nv : K.vcpus = ∅) {m m' : U64 → U64}
    {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop} {c : U64} {lk : U64 → Prop}
    (hs : PathObl.StepOK (own K.toKLayout) cls ko User c lk m m') :
    PathObl.StepOK (ownV K.toKLayoutV) cls ko User c lk m m' := by
  have e : ∀ m x, ownV K.toKLayoutV m x = own K.toKLayout m x := fun _ x =>
    ownV_off (fun ⟨_, hv⟩ => not_inVcpu_empty nv hv)
  refine ⟨fun x hx => ?_, hs.2⟩
  rw [e, e] at hx ⊢
  exact hs.1 x hx

variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP}
variable {A : Type} {ar : machine.Arch A}

/-- **`move` at `PmPreG`** (gen 11's [W] `PmMoveW`, proved; module docstring). -/
theorem pm_mvG (hA : P0.ArchTotal ar) (hKP : RegionOKP K) (hUP : UserOKP K) {number : I64} {m : U64 → U64} :
    PmMoveW st ar number p K Locks m (PmPreG st Cs Ω Sg Ac Locks p K m) := by
  intro s a s1 a1 hE h
  have hJ := hE.1.1
  have hq := hE.1.2.1
  have hG := hE.1.2.2
  have Pb := hq.1.1.1
  have P := Pb.ptU hG
  have hK := hJ.regionOK
  have hU := hJ.userOK
  have hLA := hJ.ioLayA
  obtain ⟨m1, ⟨nv, -⟩, -⟩ := gateAg_of_ep hG
  -- the plan's slot
  obtain ⟨fp, rt, asid0, va0, mp, hcs, hsl, -, hlkS, -⟩ := pm_core hq
  have hsl0 : Locks s p.slot := hlkS (fun e => slJAt_slot0 hJ (e ▸ hsl))
  have hO : OutsideObjs st K.heap.tcbs Cs s p.slot := by
    obtain ⟨x, hx, hxs⟩ := hq.2
    obtain ⟨Cw, hroot, hcl, hC⟩ := Pb.walk
    obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hx
    rw [← hxs, hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).2.1
  have hnT : ¬ TcbSlot K.toKLayout p.slot := notTcbSlot_of hO
  have hnf := nof_of_frame_slot hcs
  -- the checked store's write facts
  have hW := mvWrS Pb hK hLA (c := L.cpu s) (lk := Locks s) (m := L.mem s)
  have hS0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) := by
    refine ⟨?_, fun hq => absurd hq ?_⟩
    · rw [← OwnMap.affA_fld]; exact Pb.curAff
    · rw [← OwnMap.stA_fld]; exact nq_run Pb.run
  have hsw : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      SWr (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st
        (L.curW s) v :=
    fun v hv X => OwnMap.gds_write_state (Pb.hT _ Pb.cT) hS0 (fun hq => absurd hq (nq_run hv))
  have hc0 : ∀ x v, NullOrFrame v →
      (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))).write x p.slot v
        = st.write x p.slot v :=
    fun x v hv => OwnMap.gds_write_cap0 hsl hnT hsl0 hnf hv
  have hW8 : WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))
      (core.num.U64.wrapping_add p.slot 8#u64) := by
    obtain ⟨q8, qf⟩ := Pb.lay.slot8 p.slot hsl
    have hv := PathObl.slot_word_val qf (o := 8#u64) (by simp)
    have hr := Pb.lay.slotw p.slot hsl _ (slot_inW qf (o := 8#u64) (by simp))
    have hne : core.num.U64.wrapping_add p.slot 8#u64 ≠ p.slot := fun e => by
      have := congrArg UScalar.val e; rw [hv] at this; simp at this
    have ha : Aligned (core.num.U64.wrapping_add p.slot 8#u64) := by
      unfold Aligned; rw [hv]; simp; omega
    exact fun _ _ => Or.inl (Or.inl ⟨ha, OwnMap.nondec_slotw hK hr hne⟩)
  have hWu : ∀ b, UserW K.toKLayout b → WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)) b :=
    fun b hb _ _ => Or.inl (Or.inl ⟨hb.1, fun hd => (OwnMap.decW_ok hU hd).2 hb.2⟩)
  have hWe : ∀ b, b ∈ K.ptes → WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)) b :=
    fun b hb _ _ => Or.inl (Or.inl ⟨(hUP.kern b hb).1, pte_nondec hKP hb⟩)
  -- the block on the checked store
  have hblk : ∀ info nx s1' s2 a1' buf length cap, msg.msg_info st s (L.curW s) = ok info →
      InvChk st ar s a (L.curW s) p nx s1' s2 a1' →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
        else ok info.length) = ok length →
      obj.Slot.cap st p.slot s2 = ok cap →
      ∀ y, syscall.decode_invocation st ar s2 a1' info.label length p.slot cap true true true false buf p.extra =
        ok y →
        syscall.decode_invocation (gd st (PmRSU st K Locks s)
            (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) ar s2 a1' info.label length p.slot cap
            true true true false buf p.extra = ok y ∧
        ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
          invRep (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
            (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧ z.2.2 = core.result.Result.Ok () ∧
          FinOK (L := L) (gd st (PmRSU st K Locks s)
              (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
            (IoRS (st := st) K.ptU Locks s) (WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
            ar s z.1 z.2.1 := by
    intro info nx s1' s2 a1' buf length cap emi C _ hcap y hy
    obtain ⟨hdec, hrep⟩ := pmAccG2 (R := PmRSU st K Locks s)
      (W := WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
      (gS := gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
      hA hE (fun _ h => pmRSU_ioRS hG h) (fun b hb => ⟨hb.1, Or.inl hb.2⟩) (fun b hb => ⟨hb.1, Or.inr hb⟩) hW hsw
      hc0 hW8 hWu hWe emi C hcap hy
    refine ⟨hdec, fun z hz => ⟨hrep z hz, ?_⟩⟩
    haveI : GRd (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st
        (IoRS (st := st) K.ptU Locks s) := gdr_sub (fun _ hy => pmRSU_ioRS hG hy)
    exact pmFinG hA hE hW (hsw _ (Or.inr rfl)) emi C hcap hy hz
  have r0 : IoRS (st := st) K.ptU Locks s p.slot := by
    have := pm_slotRS hJ hq P (o := 0#u64) (by simp) (by simp)
    rwa [wadd_zero (Pb.lay.slot8 _ hsl).2] at this
  have r8 := pm_slotRS hJ hq P (o := 8#u64) (by simp) (by simp)
  have hg : syscall.handle_invocation_local
      (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) ar s a number p =
      ok (true, s1, a1) := by
    haveI : GRd (gd st (PmRSU st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st
        (IoRS (st := st) K.ptU Locks s) := gdr_sub (fun _ hy => pmRSU_ioRS hG hy)
    exact inv_acc_gen2 hA P hW (pm_seen hJ hq P) ⟨r0, r8⟩ hblk h
  have hp := pm_isProgOn (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (p := p) (K := K)
    (μ := m) hA number
  rw [inv_hp hp (Narrow.gd _ _ _) (AltOf.pre hE.1) a] at hg
  rw [inv_hp hp (Narrow.mguard _ _) (AltOf.pre hE.1) a]
  exact interp_mguard_mono (fun x y hs => stepOKP_of_stepOKV (stepOKV_ofOwnPm nv hs)) _ s a _
    (OwnMap.run_gds_mguard hK hU hq.1.1.2 _ hg)

end mv

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **What is left of the PageMap slot's obligations** (`PmObl4` without `blk` and `mv`; module docstring). -/
structure PmObl6 (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop where
  /-- [W] `ReadOnce` of accepting runs (the buffer word read once before its write). -/
  roA : ∀ (j : I64 × localinv.Plan) K m,
    PmRoAccW st ar j.1 j.2 K Locks m (R.invBodyPmG j.1 j.2) (PmPreG st Cs Ω Sg Ac Locks j.2 K m)
  /-- [P] the core set is below 64. -/
  cs : ∀ c ∈ Cs, c.val < 64
  /-- [P] the locks survive a user write. -/
  lk : PmLk st Locks

variable {st ar}

/-- **The PageMap slot family with `blk` and `mv` proved.** -/
def pmPathsJ {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl6 st ar Cs Ω Sg Ac Locks) :
    PathsP (I64 × localinv.Plan) :=
  fun j K m hK hU =>
    pm_localPathU (K := K) (m0 := m) (Locks := Locks) ar hA hK hU j.1 j.2 hm
      (P := PmPreG st Cs Ω Sg Ac Locks j.2 K m) (fun _ h => h.1.2.1.1.1.1)
      (pm_accU_of_blkG hA hK (pm_blkG hA hK)) (fun s a r hE => pm_dec hA j.1 s a r hE.1) (pm_mvG hA hK hU)
      (fun s s' a r0 r hE => pm_ra hA j.1 s s' a r0 r hE.1)
      (pm_hufG (pm_iw B.cs) B.lk j K m)
      (R.invBodyPmG j.1 j.2)
      ((pm_isProgOn hA j.1).mono (fun _ hy => by
        obtain ⟨s0, hP, Al⟩ := hy
        exact ⟨s0, hP.1, alt_pmU Al⟩))
      (pm_noZero j.1 j.2) (B.roA j K m) (fun s s' a r hE => pm_ro hA j.1 s s' a r hE.1)

/-- **The PageMap slot's start fact** (gen 14's `StartPmH` for `pmPathsJ`). -/
def StartPmJ {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl6 st ar Cs Ω Sg Ac Locks)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : I64 × localinv.Plan) : Prop :=
  ∃ (σ : S) (a : A), Ch σ ∧ PmQF st Cs Ω Sg Ac Locks j.2 K m σ ∧ PmEx st j.2 σ ∧
    L.cpu σ = c ∧ Locks σ = hs ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x) ∧ q = (pmPathsJ hA hm B j K m hK hU).body σ a

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **`hSFQ` of `serializable_fl4_localW11PRI` for `pmPathsJ`** (as `pm_hSFQI`). -/
theorem pm_hSFQJ {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl6 st ar Cs Ω Sg Ac Locks) :
    ∀ Ch K m hK hU c hs q j, (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → m x = s1.mem x) →
      StartPmJ hA hm B Ch K m hK hU c hs q j → StartAt (pmPathsJ hA hm B j K m hK hU) c hs m q := by
  rintro Ch K m hK hU c hs q j ⟨σe, hC⟩ ⟨s1, hc1, hg⟩ ⟨σ, a, hCh, hQ, hEx, hc, hl, hμ, rfl⟩
  obtain ⟨Z, H, Cx, nc, -, -, -, hCL, -⟩ := hC
  exact ⟨σ, a, ⟨⟨hCL.bun σ hCh, hQ, s1.mem, hc1, fun x hx ha hu => (hμ x ha hu).trans (hg x hx)⟩, hEx,
    pmRoot_of_qf hQ⟩, hc, hl, hμ, rfl⟩

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end over W11's slots and the PageMap slot with `blk` and `mv` proved** (module docstring). -/
theorem serializable_fl4_localW11PRIPmJ (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl6 st ar Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPR (PathsP.sum (fl4LocW11J st ar hA hm hSt a0) (pmPathsJ hA hm B))
      (StartW11RI st ar hA hm hSt a0 arI AR MR (StartPmJ hA hm B)) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localW11PRI st ar hA hm hSt a0 P hIoa (pmPathsJ hA hm B) (pm_hSFQJ hA hm B) h0 hA0 hB hc0 hM0
    h hq

end top

end
end Fl4Proofs.P2.E2EP

/-
# P2 (line invj, generation 7): `move` of accepted Delete PTE-arm runs under rule 8 (`invMovePP`)

stpost's `move` route (`invMoveW_of2`: the accepted run on p2sl's checked store `gd st R (PWs …)`, then
`OwnMap.run_gds_mguard`) for the PTE arm, with the read set `InvRSP`:

* **`invBlkGdPP`**: both arms of the PTE-arm decode block on `gd st (InvRSP s) (PWs …)` — `length ≥ 2` by
  `delAcc2X` / `delFin2R` (the leaf write `e := 0` is a `PW` write: `e` is aligned and decides no owner,
  `pte_nondec`), `length < 2` by `truncAccR` / `truncFinR`;
* `stepOKV_of_own`: at a layout with no VCPU, `StepOK` for `own` is `StepOK` for `ownV` (`ownV_off`); with pte's
  `stepOKP_of_stepOKV` it is `StepOK` for `ownP`;
* **`invMovePP`**: an accepted run is an `mguard` run for `StepOK (ownP K)` (the run on `gd` by `inv_acc_genR`, then
  `run_gds_mguard` over the program tree `q` of `hp` [P], then `interp_mguard_mono`).

Inputs: `RegionOKP`, `UserOKP`, no VCPU, `PreP`, `hmA` (the start memory agrees with the state on every TCB's
`AFFINITY`, as `invMoveW_of2`) and `hp` (`IsProgOn` of the body, the slot's program premise). No new premise. New
module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteAcc2X
import Fl4Proofs.P2.InvDelPteOblP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame fld)

section blk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (invj gen 7) **Both arms of the PTE-arm decode block on `gd st (InvRSP s) (PWs …)`** (module docstring). -/
theorem invBlkGdPP {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hKP : RegionOKP K) (hUP : UserOKP K) (nv : K.vcpus = ∅) {s : S} (hE : PreP st Cs Ω Sg Ac Locks p K m s)
    {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A} {buf length : U64}
    {cap : capability.Cap} (emi : msg.msg_info st s (L.curW s) = ok info)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hl : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (y : (core.result.Result Unit error.Exc) × S × A)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (gd st (InvRSP st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (gd st (InvRSP st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
      z.2.2 = core.result.Result.Ok () ∧
      FinOK (L := L) (gd st (InvRSP st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        (IoRSR st K.toKLayout Locks s) (WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        ar s z.1 z.2.1 := by
  obtain ⟨hJ, hq, m1, hc, hag⟩ := hE
  have PE := hq.1.1.1
  have hks := ksNoE_conv hc
  have hK := hJ.regionOK
  have hU := hJ.userOK
  have hLA := hJ.ioLayA
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hq
  have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  have hW := mvWrS PE hK hLA (c := L.cpu s) (lk := Locks s) (m := L.mem s)
  have hS0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) := by
    refine ⟨?_, fun hq => absurd hq ?_⟩
    · rw [← OwnMap.affA_fld]; exact PE.curAff
    · rw [← OwnMap.stA_fld]; exact nq_run PE.run
  have hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      SWr (gd st (InvRSP st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st
        (L.curW s) v :=
    fun v hv X => OwnMap.gds_write_state (PE.hT _ PE.cT) hS0 (fun hq => absurd hq (nq_run hv))
  have hWu : ∀ b, UserW K.toKLayout b →
      WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)) b :=
    fun b hb _ _ => Or.inl (Or.inl ⟨hb.1, fun hd => (OwnMap.decW_ok hU hd).2 hb.2⟩)
  by_cases hlen : length < 2#u64
  · obtain ⟨hdec, hrep⟩ := truncAccR (R := InvRSP st K Locks s)
      (gS := gd st (InvRSP st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) hA PE
      (fun _ h => ioRSP_inv (ioRSR_P hKP hks h)) (fun _ h => ⟨h.1, Or.inl h.2⟩) hW hWu hcs hsK (invBufJ8_of hJ)
      C hcap hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := haveI : (GRd (gd st (InvRSP st K Locks s)
          (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st (IoRSR st K.toKLayout Locks s)) := gdr_sub (fun _ h => ioRSP_inv (ioRSR_P hKP hks h))
      truncFinR (gS := gd st (InvRSP st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        hA PE hW (hst _ (Or.inr rfl)) hcs hsK (invBufJ8_of hJ) C hcap hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · have E := delEntP_of (P := fun s => SlJAt (L := L) K.toKLayout s) hJ hq (invCdtJ_of (fun _ h => h))
      (hz_of _ s hJ)
    have hvs := invVsJ_of (st := st) (P := fun s => SlJAt (L := L) K.toKLayout s) (fun _ h => h)
    have hlf := invLeafJ_of (st := st) (P := fun s => SlJAt (L := L) K.toKLayout s) (fun _ h => h) s hJ
    have hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
        (16 ≤ o.val ∨ (¬ TcbSlot K.toKLayout q ∧ NullOrFrame (L.mem s q))) →
        WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)) (core.num.U64.wrapping_add q o) := by
      intro q o hq _ ho h8 h8' _
      obtain ⟨q8, qf⟩ := PE.lay.slot8 q hq
      have hv := PathObl.slot_word_val qf ho
      have hr := PE.lay.slotw q hq _ (slot_inW qf ho)
      have hne : core.num.U64.wrapping_add q o ≠ q := fun e => by
        have := congrArg UScalar.val e; rw [hv] at this; omega
      have ha : Aligned (core.num.U64.wrapping_add q o) := by unfold Aligned; rw [hv]; omega
      exact fun _ _ => Or.inl (Or.inl ⟨ha, OwnMap.nondec_slotw hK hr hne⟩)
    have hw0 : ∀ q, q ∈ K.slots → Locks s q → ¬ TcbSlot K.toKLayout q → NullOrFrame (L.mem s q) →
        ∀ x, (gd st (InvRSP st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))).write
          x q 0#u64 = st.write x q 0#u64 :=
      fun q hq hl hT hn x => OwnMap.gds_write_cap0 hq hT hl hn OwnMap.nof_zero
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
    have hsub : ∀ b, b ∈ K.ptes → Fl4Proofs.P3.Vs.PtW Zx.L1 b := fun b hb =>
      ptesR_sub B hag b (by rw [← hc]; exact hb)
    have hpte : ∀ asid va e, localinv.small_page_entry st s asid va = ok (some e) → e ∈ K.ptes :=
      fun asid va e he => by rw [hc]; exact ptesR_of_spe B hag nv he
    obtain ⟨hdec, hrep⟩ := delAcc2X (X := (· ∈ K.ptes)) (R := InvRSP st K Locks s)
      (gS := gd st (InvRSP st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
      hA PE hW hwS hw0 hst E hsK hlen (B.vsJX hsub)
      (fun b hb => ⟨(hUP.kern b hb).1, hKP.none b hb, (hUP.kern b hb).2⟩)
      (fun b h hx => ioRSP_inv ⟨h, fun hb => absurd hb hx⟩)
      (fun asid va e he hl' => ioRSP_inv ⟨VsW.ioRS (hlf asid va e he), fun _ => hl'⟩) hlf
      (fun asid va e he _ _ _ => Or.inl (Or.inl ⟨(hUP.kern e (hpte asid va e he)).1,
        pte_nondec hKP (hpte asid va e he)⟩)) C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := haveI : (GRd (gd st (InvRSP st K Locks s)
          (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st (IoRSR st K.toKLayout Locks s)) := gdr_sub (fun _ h => ioRSP_inv (ioRSR_P hKP hks h))
      delFin2R (gS := gd st (InvRSP st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        hA PE hW (hst _ (Or.inr rfl)) E hsK hlen
        (fun sl fp rt asid va hsl hc' hA' =>
          hvs s sl fp rt asid va ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ hsl hc' hA')
        hlf C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩

end blk

section mv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- At a layout with no VCPU, `StepOK` for `own` is `StepOK` for `ownV`. -/
theorem stepOKV_of_own {K : KLayoutP} (nv : K.vcpus = ∅) {m m' : U64 → U64}
    {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop} {c : U64} {lk : U64 → Prop}
    (hs : PathObl.StepOK (own K.toKLayout) cls ko User c lk m m') :
    PathObl.StepOK (ownV K.toKLayoutV) cls ko User c lk m m' := by
  have e : ∀ m x, ownV K.toKLayoutV m x = own K.toKLayout m x := fun _ x =>
    ownV_off (fun ⟨_, hv⟩ => not_inVcpu_empty nv hv)
  refine ⟨fun x hx => ?_, hs.2⟩
  rw [e, e] at hx ⊢
  exact hs.1 x hx

/-- (invj gen 7) **`move` of accepted PTE-arm runs under rule 8** (module docstring). -/
theorem invMovePP {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hKP : RegionOKP K) (hUP : UserOKP K) (nv : K.vcpus = ∅) {q : SProg Bool}
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (PreP st Cs Ω Sg Ac Locks p K m) (InvRSP st K Locks) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user)) q)
    (hmA : ∀ s, PreP st Cs Ω Sg Ac Locks p K m s → ∀ d, K.heap d = some .tcb →
      m (fld d OwnMap.oAFFINITY) = L.mem s (fld d OwnMap.oAFFINITY))
    {s s' : S} {a a' : A} (hE : PreP st Cs Ω Sg Ac Locks p K m s)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local (mguard st (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s a number p =
      ok (true, s', a') := by
  have hq := hE.2.1
  have PE := hq.1.1.1
  have hks := ksNoE_conv hE.2.2.choose_spec.1
  have hK := hE.1.regionOK
  have hU := hE.1.userOK
  have hLA := hE.1.ioLayA
  have hg : syscall.handle_invocation_local
      (gd st (InvRSP st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) ar s a number p =
      ok (true, s', a') :=
    haveI : (GRd (gd st (InvRSP st K Locks s)
        (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st (IoRSR st K.toKLayout Locks s)) := gdr_sub (fun _ h => ioRSP_inv (ioRSR_P hKP hks h))
    inv_acc_genR hA PE (mvWrS PE hK hLA) (invSeenR_of hE.1 hq) (invPsR_of hq)
      (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => invBlkGdPP hA hKP hUP nv hE emi hc hl hk y hy) h
  rw [inv_hp hp (Narrow.gd _ _ _) (AltOf.pre hE) a] at hg
  rw [inv_hp hp (Narrow.mguard _ _) (AltOf.pre hE) a]
  exact interp_mguard_mono (fun x y hs => stepOKP_of_stepOKV (stepOKV_of_own nv hs)) q s a _
    (OwnMap.run_gds_mguard hK hU (hmA s hE) q hg)

end mv

end Fl4Proofs.P2.E2EP

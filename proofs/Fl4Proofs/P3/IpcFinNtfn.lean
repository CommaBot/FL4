/-
P3 (DESIGN.md §9), IPC: **a notification's finalisation on `IRel`, the
slots kept** (toward `XFinHyps.ntfn`).

* `unbind_maybe_irel`: `unbind_maybe_notification` (the bound TCB's and the
  notification's bound words cleared, `bound_wr_irel`).
* `maybe_unbind_irel`: `maybe_unbind_ntfn` (`unbind_ntfn_refines0`, lifted by
  `tk_liftCW`). Named, at the start state: the notification's SC among `C`
  (`NSC`) and bound back to it (l4v `sym_refs` for the SC binding).
* `xFinNtfn_of`: **`XFinHyps.ntfn`** from the three (and
  `cancel_all_signals_irel`), at `Z.mv Z.G V'` (`XTopAt.irel_same`), the
  spec's finalisation keeping the caps (`finNtfn_nkc`). Named (`NtfnFinPre`,
  at the `XTopAt` states): `BufWordRel`, the IPC placement, `NSC`, the SC
  back-links, the spec's facts of `cancel_all_signals` at each notification
  of `Z.N` (`NtfnPre`: its queued threads' SCs ready and sufficient,
  `ScBack`, `ActReady`; carried to the loop by `ntfnQPre_of_pre`), the
  notification caps' objects among `Z.N`.
-/
import Fl4Proofs.P3.IpcSlotsSame
import Fl4Proofs.P3.IpcCancelSignals
import Fl4Proofs.P3.IpcTcbBind
import Fl4Proofs.P3.IpcSchedTail
import Fl4Proofs.P3.ScNtfnBind
import Fl4Proofs.P3.ScXProd
import Fl4Proofs.P3.SpecCaps
import Fl4Proofs.P3.DelOne
import Fl4Proofs.P3.TcbCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- **`unbind_maybe_notification` on `IRel`**, the slots kept. -/
theorem unbind_maybe_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {n : U64} (hn : n ∈ N) :
    notification.unbind_maybe_notification st s n ⦃ s' => ∃ σ',
      Fl4Spec.unbindMaybeNotification (Z := Unit) n.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c s' σ' ∧ IFrame (L := L) th s s' ∧ WritesIn st s s' (TSW T C) ⦄ := by
  obtain ⟨xn, hkn, -⟩ := hX.1.toN.ntfn n hn
  have hx := hX.1.toN.at_ntfn hn hkn
  have hg : Fl4Spec.getNtfnObjRef (Z := Unit) Fl4Spec.Notification.ntfnBoundTcb n.bv σ =
      ({(xn.ntfnBoundTcb, σ)}, False) := by
    unfold Fl4Spec.getNtfnObjRef Fl4Spec.getSkObjRef
    rw [nd_bind_one (m := Fl4Spec.getSimpleKo Fl4Spec.KernelObject.notification n.bv) (getNotification_eq hkn)]
    rfl
  unfold notification.unbind_maybe_notification
  rw [Sched.ntfn_bound_eq]
  simp only [bind_ok]
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  by_cases h0 : L.mem s (nBoundA n) = 0#u64
  · have hb' : b = true := by rw [hb, h0]; rfl
    simp only [hb', ↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, hX, IFrame.refl _ _, WritesIn.refl _ _⟩
    unfold Fl4Spec.unbindMaybeNotification
    rw [nd_bind_one hg, hx.bound, h0, Notif.optRef_zero]; rfl
  have hb' : b = false := by rw [hb]; simp [h0]
  simp only [hb', Bool.false_eq_true, ↓reduceIte]
  have hiT := hx.bound_mem h0
  obtain ⟨x, hk, -⟩ := hX.1.tcb _ hiT
  have hin : (L.mem s (nBoundA n)).bv ≠ n.bv := fun e => by rw [e, hkn] at hk; cases hk
  obtain ⟨s1, h1, rfl⟩ := spec_exists (P1.obj.Ntfn.set_bound_tcb.wr (L := L) s n 0#u64)
  rw [h1]; simp only [bind_ok]
  obtain ⟨s2, h2, rfl⟩ := spec_exists (P1.obj.Tcb.set_bound_ntfn.wr (L := L) (L.wr s (P1.ntfnBtA n) 0#u64)
    (L.mem s (nBoundA n)) 0#u64)
  rw [h2, WP.spec_ok]
  have hX2 := bound_wr_irel hP0 hX hiT hn hk hkn 0#u64 0#u64 (fun h => absurd rfl h)
  rw [Notif.optRef_zero] at hX2
  have hba : Aligned (nBoundA n) := by
    rw [nBoundA_eq]; exact (nword hP0.n hn (K := 24#u64) (by simp) (by simp)).1
  have hbv : (nBoundA n).val = n.val + 24 := by rw [nBoundA_eq]; exact nfield_val (hP0.n.ntfn n hn) (by simp)
  have hpa := hP0.e.tcb _ hiT
  have hta := (a_bound hpa).1
  have hbvp := val_bound hpa
  have hw2 := (writesIn_wr (s := s) (v := 0#u64) hba).trans
    (writesIn_wr (s := L.wr s (nBoundA n) 0#u64) (v := 0#u64) hta)
  refine ⟨_, ?_, hX2, IRel.iframe_of hX hw2 fun b hb => ?_, hw2.mono fun b hb => ?_⟩
  · unfold Fl4Spec.unbindMaybeNotification
    rw [nd_bind_one hg, hx.bound, Notif.optRef_ne h0]
    show (Fl4Spec.setNtfnObjRef Fl4Spec.ntfnBoundTcbUpdate n.bv none >>= fun _ =>
      Fl4Spec.setTcbObjRef Fl4Spec.tcbBoundNotificationUpdate (L.mem s (nBoundA n)).bv none) σ = _
    rw [nd_bind_one (setNtfnObjRef_eq hkn _ _)]
    exact Notif.threadSet_eq _ (by simp only [Notif.updK, Function.update_of_ne hin]; exact hk)
  · rcases hb with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, by rw [hbv]; omega, by rw [hbv]; omega⟩)))))
    · have e : (P1.boundA (L.mem s (nBoundA n))).val = (L.mem s (nBoundA n)).val + 3368 := hbvp
      exact Or.inr (Or.inr (Or.inl ⟨_, hiT, by first | rw [e]; omega | rw [hbvp]; omega,
        by first | rw [e]; omega | rw [hbvp]; omega⟩))
  · rcases hb with rfl | rfl
    · exact NWrite.tsw hX.2.2.1 (Or.inl ⟨n, hn, by rw [hbv]; omega, by rw [hbv]; omega⟩)
    · exact tsw_tcb hX.2.2.1 hiT (K0 := 3368) hbvp (by omega) (by omega) (by omega) (by omega)


set_option maxHeartbeats 4000000 in
/-- **`maybe_unbind_ntfn` on `IRel`**, the slots kept (module docstring). -/
theorem maybe_unbind_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {n : U64} (hn : n ∈ N) (hNs : NSC N C σ)
    (hlink : ∀ xn p, σ.kheap n.bv = some (.notification xn) → xn.ntfnSc = some p →
      ∃ y m, σ.kheap p = some (.schedContext y m) ∧ y.scNtfn = some n.bv) :
    schedcontext.maybe_unbind_ntfn st s n ⦃ s' => ∃ σ',
      Fl4Spec.schedContextMaybeUnbindNtfn (Z := Unit) n.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c s' σ' ∧ IFrame (L := L) th s s' ∧ WritesIn st s s' (TSW T C) ⦄ := by
  have hS := hX.2.2.1
  obtain ⟨xn, hkn, -⟩ := hX.1.toN.ntfn n hn
  have hx := hX.1.toN.at_ntfn hn hkn
  have hg : Fl4Spec.getNtfnObjRef (Z := Unit) Fl4Spec.Notification.ntfnSc n.bv σ = ({(xn.ntfnSc, σ)}, False) := by
    unfold Fl4Spec.getNtfnObjRef Fl4Spec.getSkObjRef
    rw [nd_bind_one (m := Fl4Spec.getSimpleKo Fl4Spec.KernelObject.notification n.bv) (getNotification_eq hkn)]
    rfl
  unfold schedcontext.maybe_unbind_ntfn
  step with P1.obj.Ntfn.sc.val as ⟨i, hi⟩
  step with P1.obj.Sc.is_null.spec as ⟨b, hb⟩
  have hsc : xn.ntfnSc = Notif.optRef i := by rw [hx.sc, hi]; rfl
  by_cases h0 : i = 0#u64
  · subst h0
    have hb' : b = true := by rw [hb]; rfl
    simp only [hb', ↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, hX, IFrame.refl _ _, WritesIn.refl _ _⟩
    unfold Fl4Spec.schedContextMaybeUnbindNtfn
    rw [nd_bind_one hg, hsc, Notif.optRef_zero]; rfl
  have hb' : b = false := by rw [hb]; simp [h0]
  simp only [hb', Bool.false_eq_true, ↓reduceIte]
  have hsn : xn.ntfnSc = some i.bv := by rw [hsc, Notif.optRef_ne h0]
  obtain ⟨sc, hscC, hscv⟩ := hNs n hn xn _ hkn hsn
  have e : sc = i := P1.eq_of_bv hscv
  subst e
  obtain ⟨y, m, hky, hyn⟩ := hlink xn _ hkn hsn
  have hsw := sw_hdr hS hscC (K := 40#u64) (by simp) (by simp) (by decide)
  have hgy : Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scNtfn sc.bv σ = ({(y.scNtfn, σ)}, False) := by
    unfold Fl4Spec.getScObjRef; rw [nd_bind_one (getSchedContext_eq hky)]; rfl
  refine WP.spec_mono (unbind_ntfn_refines0 s σ hS hX.1.toN hscC h0 hky
    (fun n' e => (P1.eq_of_bv (Option.some.inj (hyn.symm.trans e))) ▸ hn)) ?_
  rintro s' ⟨σ', he, hS', hR', hw, -⟩
  have hK : ScTKw (fun q => q = σ.curThread) σ σ' :=
    ScTKw.ofFalse (NKT.of_eq (Sched.nkt_schedContextUnbindNtfn _) he)
  have hkf : ∀ b, (Sched.NW N b ∨ b = scW sc 40#u64) → KFoot st T N C c s σ b := fun b hb => by
    rcases hb with h | h
    · exact KFoot.of_nw h
    · subst h; exact KFoot.of_sw hsw
  refine ⟨σ', ?_, tk_liftCW hP0 hX (hw.mono fun b hb => Or.inl (Or.inl (hkf b hb))) hK hS' hR',
    IRel.iframe_of hX hw fun b hb => tfoot_oobj hS (Or.inl (hkf b hb)), hw.mono fun b hb => KFoot.tsw hS (hkf b hb)⟩
  rw [← he]
  unfold Fl4Spec.schedContextMaybeUnbindNtfn Fl4Spec.schedContextUnbindNtfn
  rw [nd_bind_one hg, hsn, nd_bind_one hgy, hyn]
  rfl

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem finWork_ntfn {p b : U64} {w r : Bool} {fb : Bool} (h : FinWork (.Notification p b w r) fb) : fb = true := by
  unfold FinWork at h
  rcases h with ⟨hb | ⟨f, l, o, e, -⟩, -⟩ | ⟨p, sz, r, d, ep, asid, va, e⟩
  · exact hb
  · cases e
  · cases e

/-- **What a notification cap's finalisation at `XTop` reads** (module
docstring). -/
def NtfnFinPre (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  BufWordRel Z.T (L.mem s) σ ∧ IPlaced Z.N Z.T Z.E Z.R Z.B ∧ NSC Z.N Z.C σ ∧
  (∀ n ∈ Z.N, ∀ xn p, σ.kheap n.bv = some (.notification xn) → xn.ntfnSc = some p →
    ∃ y m, σ.kheap p = some (.schedContext y m) ∧ y.scNtfn = some n.bv) ∧
  (∀ n ∈ Z.N, NtfnPre σ n.bv) ∧
  ∀ sl p b w r, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r) → p ∈ Z.N

set_option maxHeartbeats 8000000 in
/-- **`XFinHyps.ntfn` holds** (module docstring). -/
theorem xFinNtfn_of {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}
    (hpre : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ → NtfnFinPre (L := L) Z s σ) :
    XFinAt (L := L) arI FinNtfnK AR th := by
  intro Z s a σ sl c hth hX hK hTh ⟨p, b, w, r, hc0⟩ hDS hA hc hk hw
  subst hth hc0
  obtain ⟨hBW, hP0, hNs, hlink, hAct, hpN⟩ := hpre Z s a σ rfl hX
  have hp := hpN sl p b w r hA hc
  have hfin := finWork_ntfn hw
  set fin := decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ) with hfd
  have hI := hX.irelK hK hBW
  have hAR : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  rw [finalise_cap_ntfn arI s a p b w r fin false]
  unfold objects.finalise_cap_object
  simp only [hfin, ↓reduceIte]
  refine WP.spec_bind (maybe_unbind_irel hP0 hI hp hNs (hlink p hp)) ?_
  rintro s1 ⟨σ1, he1, hI1, hk1, -⟩
  refine WP.spec_bind (unbind_maybe_irel hP0 hI1 hp) ?_
  rintro s2 ⟨σ2, he2, hI2, hk2, -⟩
  refine WP.spec_bind (cancel_all_signals_irel hP0 s2 σ2 hI2 hp (ntfnQPre_of_pre (hAct p hp) he1 he2)) ?_
  rintro s3 ⟨σ3, hm3, hI3, hk3, -⟩
  rw [WP.spec_ok]
  have hmem : ((absCap capability.Cap.Null, absCap capability.Cap.Null), σ3) ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Notification p b w r)) fin σ).1 := by
    rw [hfin]
    show _ ∈ (Fl4Spec.NonDet.liftM (fun _ => (Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap)) (Fl4Spec.NonDet.when true
      (do
        Fl4Spec.schedContextMaybeUnbindNtfn p.bv
        Fl4Spec.unbindMaybeNotification p.bv
        Fl4Spec.cancelAllSignals p.bv)) σ).1
    unfold Fl4Spec.NonDet.liftM Fl4Spec.NonDet.when
    simp only [↓reduceIte]
    refine mem_bind_nd (x := ((), σ3)) ?_ (Set.mem_singleton _)
    refine mem_bind_nd (x := ((), σ1)) (by rw [he1]; rfl) ?_
    exact mem_bind_nd (x := ((), σ2)) (by rw [he2]; rfl) hm3
  have hck := finNtfn_nkc p.bv b.bv _ fin σ _ hmem
  have hkk := (hk1.trans hk2).trans hk3
  obtain ⟨V', hX3⟩ := XTopAt.irel_same hX hI3 hAR hkk.1 hck.cdt hck.orig hck.ks hkk.2
  have hM := hDS.1.2.2.1
  refine ⟨rfl, trivial, trivial, σ3, Z.G, hmem, DState.of_same hDS hkk.1 hX3.rel.2.1 hck.ks, ?_,
    fun y hy _ => Or.inl (hkk.1.capV hy), MdbStep.of_same hM hkk.1, ⟨V', hX3⟩, hkk.2⟩
  rw [hkk.1.capV hA.isSlot]; exact capV_of_capAt hc

end

end

end Fl4Proofs.P3

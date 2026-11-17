/-
P3 (DESIGN.md §9), scheduling contexts: **the yielder's `complete_yield_to`
at `XTop`** (`ScYieldFinHyp`, used by `xFinSc_of` and `xFinThread_of`;
`scYieldFinHyp_of`).

* `badge_wr_irel`: the badge register written on `IRel` (IpcNtfnRecv's
  `set_badge_reg_relI`, the notification step).
* `set_consumed_irel`: `set_consumed sc t true` on `IRel`: the SC's consumed
  time (`update_consumed_irel`), then the reply from the kernel of one word
  (VsReplyTop's `reply1` order: the badge, `MR0`, the message info) against
  `set_consumed` (`reply_from_kernel_one`), with its write set.
* `complete_yield_to_irel`: the yield-to pair's SC reports its consumed time
  to the yielder, then the pair is cut (`cancel_yield_to_irel`), with its
  write set (`cancel_yield_to_foot`).
* `scYieldFinHyp_of`: from `XTopAt`, `IRel` by `irelK`, back to `XTopAt` at
  `Z`'s ghost tree by `XTopAt.irel_same`, the slots kept by the write set
  (words of the other objects).

Named: at the `XTopAt` states [J], `KsApart`, `BufWordRel`, the IPC
placement, the yield relation on `IRel`, and an SC's yielder among the
TCBs; the platform's `ticks_to_us` and `getMaxTicksToUs` [P].
-/
import Fl4Proofs.P3.XTopFinThread
import Fl4Proofs.P3.IpcTmo
import Fl4Proofs.P3.VsReplyTop
import Fl4Proofs.P3.IpcNtfnRecv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`IRel` across a write of the badge register.** -/
theorem badge_wr_irel (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (v : U64) :
    IRel st th cr N T C E R B c (L.wr s (badgeRegA t) v)
      (Notif.updK σ t.bv (.tcb (Notif.setReg x Fl4Spec.badge_register v.bv))) := by
  obtain ⟨hIR, hSRT⟩ := hX
  obtain ⟨hR', hW, hK⟩ := set_badge_reg_relI hP0 hIR ht hk v
  exact ⟨hR', hSRT.1.stableN hSRT.2.1.placed hW hK, hSRT.2.1.stable hW hK,
    hSRT.2.2.mono hW.1 (SzKeep.ntfnStep hK)⟩

/-- The write set of `set_consumed sc t true`. -/
def ConsW (sc t : U64) (b : U64) : Prop :=
  b = scW sc 8#u64 ∨ ∃ r : Fl4Spec.Register, b = regA t (regIdx r)

set_option maxHeartbeats 8000000 in
/-- **`set_consumed sc t true` on `IRel`** (module docstring). -/
theorem set_consumed_irel (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) {sc : U64} (hsc : sc ∈ C) {y : Fl4Spec.SchedContext} {n : Nat}
    (hky : σ.kheap sc.bv = some (.schedContext y n)) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x))
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    schedcontext.set_consumed st ar s a sc t true ⦃ s' => ∃ σ',
      Fl4Spec.setConsumed (Z := Unit) sc.bv t.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c s' σ' ∧ WritesIn st s s' (ConsW sc t) ⦄ := by
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hta := hc.tcbs t ht
  obtain ⟨y0, n0, hk0, hx0⟩ := hs.scs sc hsc
  rw [hky] at hk0; cases hk0
  have a8 := (hx0.hdr (K := 8#u64) (by simp) (by simp)).1
  unfold schedcontext.set_consumed
  refine WP.spec_bind (update_consumed_irel (ar := ar) hP0 s a σ hX hsc hky hmax htu) ?_
  rintro ⟨cv, s1⟩ ⟨hs1, hcv, he1, hX1⟩
  simp only at hs1 hcv he1 hX1
  subst hs1
  simp only [↓reduceIte]
  have hin : (do
      let buf ← msg.lookup_ipc_buffer st (L.wr s (scW sc 8#u64) 0#u64) true t
      let s2 ← obj.Tcb.set_reg st t (L.wr s (scW sc 8#u64) 0#u64) layout.reg.BADGE 0#u64
      let (n, s3) ← msg.set_mr st s2 t buf 0#u64 cv
      let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
      msg.set_msg_info st s3 t mi) ⦃ s3 => ∃ w : U64,
        s3 = L.wr (L.wr (L.wr (L.wr s (scW sc 8#u64) 0#u64) (regA t (regIdx Fl4Spec.badge_register)) 0#u64)
          (regA t (regIdx (mrIdx 0))) cv) (regA t (regIdx Fl4Spec.msg_info_register)) w ∧
        w.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 1, 0, 0, 0⟩ ⦄ := by
    refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st _ true t L.total) ?_
    rintro buf -
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ t layout.reg.BADGE 0#u64) ?_
    rintro s1 rfl
    have hset : ∀ s1 : S, msg.set_mr st s1 t buf 0#u64 cv ⦃ r =>
        r = (1#u64, L.wr s1 (regA t (regIdx (mrIdx 0))) cv) ⦄ := by
      intro s1
      unfold msg.set_mr
      have h4 : (0#u64 : U64) < msg.N_MSG_REGISTERS := by unfold msg.N_MSG_REGISTERS; decide
      simp only [h4, ↓reduceIte]
      refine WP.spec_bind (Endp.msg_register_spec 0#u64 (by decide)) ?_
      rintro r0 rfl
      refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ t _ cv) ?_
      rintro s2 rfl
      simp only [lift, bind_ok, WP.spec_ok]
      rfl
    refine WP.spec_bind (hset _) ?_
    rintro r rfl
    unfold msginfo.MessageInfo.new
    simp only [bind_ok]
    refine WP.spec_mono (Endp.set_msg_info_spec _ t 0#u64 1#u64 (by decide)) ?_
    rintro s3 ⟨w, rfl, hw⟩
    refine ⟨w, ?_, by rw [hw]; exact Vs.msg_info_one_bv⟩
    rw [Endp.regIdx_badge, Endp.regIdx_msgInfo]
  refine WP.spec_mono hin ?_
  rintro s3 ⟨w, rfl, hw⟩
  have hpt : sc.bv ≠ t.bv := fun e => by rw [e, hk] at hky; cases hky
  have hk1 : (updSc σ sc.bv { y with scConsumed := (0#u64 : U64).bv } n).kheap t.bv = some (.tcb x) := by
    simp [Notif.updK, Ne.symm hpt, hk]
  have hXa := badge_wr_irel hP0 hX1 ht hk1 0#u64
  rw [badgeRegA_eq_regA] at hXa
  have hkA : (Notif.updK (updSc σ sc.bv { y with scConsumed := (0#u64 : U64).bv } n) t.bv
      (.tcb (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv))).kheap t.bv =
      some (.tcb (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv)) := by simp
  have hXb := reg_wr_irel hP0 hXa ht hkA (mrIdx 0) (by decide) cv
  have hkB : (Notif.updK (Notif.updK (updSc σ sc.bv { y with scConsumed := (0#u64 : U64).bv } n) t.bv
      (.tcb (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv))) t.bv
      (.tcb (Notif.setReg (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv) (mrIdx 0) cv.bv))).kheap t.bv =
      some (.tcb (Notif.setReg (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv) (mrIdx 0) cv.bv)) := by
    simp
  have hXc := reg_wr_irel hP0 hXb ht hkB Fl4Spec.msg_info_register (by decide) w
  have hxC : Notif.setReg (Notif.setReg (Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv) (mrIdx 0) cv.bv)
      Fl4Spec.msg_info_register w.bv = Endp.replyTcb x cv.bv := by rw [hw]; rfl
  rw [Vs.updK_updK, Vs.updK_updK, hxC] at hXc
  refine ⟨_, ?_, hXc, ?_⟩
  · unfold Fl4Spec.setConsumed
    rw [nd_bind_one he1]
    have hu : Fl4Spec.wordsFromTime cv.bv = [cv.bv] := by
      unfold Fl4Spec.wordsFromTime Fl4Spec.ucast; simp
    rw [hu]
    exact Endp.replyFromKernel_one hk1 cv.bv
  · have ab := (a_reg hta Fl4Spec.badge_register).1
    have am := (a_reg hta (mrIdx 0)).1
    have ai := (a_reg hta Fl4Spec.msg_info_register).1
    refine ((((writesIn_wr a8).trans (writesIn_wr ab)).trans (writesIn_wr am)).trans (writesIn_wr ai)).mono
      fun b hb => ?_
    rcases hb with ((rfl | rfl) | rfl) | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩

/-- **`cancel_yield_to`'s write set**: the SC's `YIELD_FROM` word and the
thread's `YIELD_TO` word. -/
theorem cancel_yield_to_foot {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    (hY : YieldRel T C (L.mem s) σ) {t : U64} (ht : t ∈ T) :
    schedcontext.cancel_yield_to st s t ⦃ s' =>
      WritesIn st s s' (fun b => (∃ q ∈ C, b = scYieldFromA q) ∨ b = yieldA t) ⦄ := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hy0 : t ≠ 0#u64 := fun e => (hc.tcbs t ht).ne0 (by rw [e]; rfl)
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  have hb' : b = false := by rw [hb]; exact decide_eq_false hy0
  rw [hb']
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨i, hi⟩
  subst hi
  by_cases hi0 : L.mem s (yieldA t) = 0#u64
  · have : (L.mem s (yieldA t) != 0#u64) = false := by simp [hi0]
    simp only [this, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact WritesIn.refl _ _
  obtain ⟨p, hp⟩ : ∃ p, L.mem s (yieldA t) = p := ⟨_, rfl⟩
  rw [hp] at hi0 ⊢
  have hb2 : (p != 0#u64) = true := by simp [hi0]
  simp only [hb2, ↓reduceIte]
  obtain ⟨hpC, -⟩ := hY.toSc t ht (by rw [hp]; exact hi0)
  rw [hp] at hpC
  have hal56 : Aligned (scW p 56#u64) := by
    obtain ⟨x0, n0, -, hx0⟩ := hs.scs p hpC; exact (hx0.hdr (K := 56#u64) (by simp) (by simp)).1
  refine WP.spec_bind (obj.Sc.set_yield_from.spec s _ 0#u64) fun s3 h3 => ?_
  subst h3
  refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s4 h4 => ?_
  subst h4
  refine ((writesIn_wr (show Aligned (scYieldFromA p) by rw [scYieldFromA_eq]; exact hal56)).trans
    (writesIn_wr (yieldA_aligned hT ht))).mono fun b hb => ?_
  rcases hb with rfl | rfl
  · exact Or.inl ⟨p, hpC, rfl⟩
  · exact Or.inr rfl

/-- The write set of `complete_yield_to y`. -/
def CytW (C : Set U64) (y : U64) (b : U64) : Prop :=
  (∃ q ∈ C, b = scW q 8#u64 ∨ b = scYieldFromA q) ∨ (∃ r : Fl4Spec.Register, b = regA y (regIdx r)) ∨ b = yieldA y

set_option maxHeartbeats 8000000 in
/-- **`complete_yield_to` on `IRel`** (module docstring). -/
theorem complete_yield_to_irel (hP0 : IPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ)
    (hYa : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → YieldRel T C (L.mem s') σ') {y : U64} (hy : y ∈ T)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    schedcontext.complete_yield_to st ar s a y ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.completeYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c r.1 σ' ∧ WritesIn st s r.1 (CytW C y) ⦄ := by
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hy0 : y ≠ 0#u64 := fun e => (hc.tcbs y hy).ne0 (by rw [e]; rfl)
  obtain ⟨xy, hky, eyt⟩ := (hYa s σ hX).tcb y hy
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  have hb' : b = false := by rw [hb]; exact decide_eq_false hy0
  rw [hb']
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨i, hi⟩
  subst hi
  by_cases hi0 : L.mem s (yieldA y) = 0#u64
  · have : (L.mem s (yieldA y) != 0#u64) = false := by simp [hi0]
    simp only [this, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨trivial, σ, ?_, hX, WritesIn.refl _ _⟩
    unfold Fl4Spec.completeYieldTo
    rw [nd_bind_one (getTcbObjRef_eq _ hky), eyt, hi0, Notif.optRef_zero]; rfl
  have hb2 : (L.mem s (yieldA y) != 0#u64) = true := by simp [hi0]
  simp only [hb2, ↓reduceIte]
  obtain ⟨hpC, ysc, nsc, hksc, -⟩ := (hYa s σ hX).toSc y hy hi0
  refine WP.spec_bind (set_consumed_irel hP0 s a σ hX hpC hksc hy hky hmax htu) ?_
  rintro s1 ⟨σ1, he1, hX1, hw1⟩
  refine WP.spec_bind (WP.spec_and (cancel_yield_to_irel hP0 hX1 (hYa _ _ hX1) hy)
    (cancel_yield_to_foot hX1.2.2.1 (hYa _ _ hX1) hy)) ?_
  rintro s2 ⟨⟨σ2, he2, hX2, -⟩, hw2⟩
  rw [WP.spec_ok]
  refine ⟨by simp, σ2, ?_, hX2, (hw1.trans hw2).mono fun b hb => ?_⟩
  · unfold Fl4Spec.completeYieldTo
    rw [nd_bind_one (getTcbObjRef_eq _ hky), eyt, Notif.optRef_ne hi0]
    show (Fl4Spec.setConsumed (Z := Unit) _ _ >>= fun _ => Fl4Spec.schedContextCancelYieldTo _) σ = _
    rw [nd_bind_one he1, he2]
  · rcases hb with (e | ⟨r, e⟩) | (⟨q, hq, e⟩ | e)
    · exact Or.inl ⟨_, hpC, Or.inl e⟩
    · exact Or.inr (Or.inl ⟨r, e⟩)
    · exact Or.inl ⟨q, hq, Or.inr e⟩
    · exact Or.inr (Or.inr e)

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The yielder's `complete_yield_to` at `XTop`** (module docstring). -/
theorem scYieldFinHyp_of {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}
    (hpre : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ →
      KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧ BufWordRel Z.T (L.mem s) σ ∧ IPlaced Z.N Z.T Z.E Z.R Z.B ∧
      (∀ cr s' σ', IRel st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → YieldRel Z.T Z.C (L.mem s') σ') ∧
      ∀ p : U64, L.mem s (scYieldFromA p) ≠ 0#u64 → L.mem s (scYieldFromA p) ∈ Z.T)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    ∀ (Z : XSets) p, Z.th = th → ScYieldFinHyp (L := L) arI AR Z p := by
  intro Z p hth s a σ hX h0
  obtain ⟨hK, hBW, hP0, hYa, hyT⟩ := hpre Z s a σ hth hX
  have hI := hX.irelK hK hBW
  have hy := hyT p h0
  have hS := hX.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hta := hc.tcbs _ hy
  refine WP.spec_mono (complete_yield_to_irel (ar := arI) hP0 s a σ hI (hYa _) hy hmax (htu a)) ?_
  rintro ⟨s', a'⟩ ⟨ha, σ', he, hI', hw⟩
  simp only at ha
  subst ha
  have hck := nkc_completeYieldTo _ σ _ (by rw [he]; exact Set.mem_singleton _)
  have hif := IRel.iframe_of hI hw fun b hb => by
    rcases hb with ⟨q, hq, e | e⟩ | ⟨r, e⟩ | e
    · obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs q hq
      subst e
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hq, x0, n0, hk0, hx0.in_obj (hx0.hdr (K := 8#u64) (by simp) (by simp)).2⟩))))))
    · obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs q hq
      subst e
      rw [scYieldFromA_eq]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hq, x0, n0, hk0, hx0.in_obj (hx0.hdr (K := 56#u64) (by simp) (by simp)).2⟩))))))
    · subst e
      have hv := regA_val hta (regIdx_lt r)
      have := regIdx_lt r
      exact Or.inr (Or.inr (Or.inl ⟨_, hy, by rw [hv]; omega, by rw [hv]; omega⟩))
    · subst e
      exact Vs.tcb_oobj hy hta (by decide) (by decide)
  obtain ⟨V', hX'⟩ := XTopAt.irel_same hX hI' hX.fin.1.1.2.2.2.2.2.2 hif.1 hck.cdt hck.orig hck.ks hif.2
  exact ⟨σ', V', he, hX', hif.1, hif.2, hck⟩

end

end

end Fl4Proofs.P3

/-
P3 (DESIGN.md §9), TCB: **a thread cap's finalisation at `XTop`**
(`XFinHyps.thread`, `xFinThread_of`).

FL4's `finalise_cap_object` of a final thread cap: the remote stall (a
no-op on one core, `remote_tcb_stall_id`), the VCPU detach (a no-op, the
thread bound to no VCPU: P1's `ThreadObj`), `unbind_notification`
(`bound_wr_irel`), the timer-tree removal (`XTopAt.tmStep`, the
`REPROGRAM` word kept), `unbind_from_sc` (`unbind_tcb_refines` as an SC step,
`xtop_sc_step`; the yielder's `complete_yield_to`, `ScYieldFinHyp`),
`suspend` (`suspend_irel`), the debug-list removal, the FPU release; the
spec's `unbind_notification`, `unbind_from_sc`, `suspend`,
`prepare_thread_delete`. The steps on `IRel` go back to `XTopAt` at the same
sets by `IRel.xtopMv`; the slots and the kernel base are kept by P1's frame
of the whole finalisation (`fin_cap_thread.slots`), which with `IRel` after
gives `XTopAt` at `Z`'s ghost tree (`XTopAt.irel_same`).

Named: `ThreadFinPre` [J] at the `XTopAt` states (`KsApart`, `BufWordRel`,
the notifications apart from the kernel-global block, the IPC placement,
`SchedValid`, `ObjCover`, `Inv`, `NSC`, `OtherTmOK`, `RemoveTcbHyp`, the
yield relation on `IRel`); the thread cap's object among the TCBs [J]; P1's
`ThreadP1Hyp` and `ArchTotal`; `timer::remove`'s footprint [W] (P1's
`timer.remove.tf`); `ScYieldFinHyp` [W]; the debug-list removal keeping
`XTopAt` [W] (its words, the TCBs' debug links and the node's
`DEBUG_TCBS` word, are read by no relation); the FPU release at `XTop` [P].
-/
import Fl4Proofs.P3.XTopFinSc
import Fl4Proofs.P3.XTopTimer
import Fl4Proofs.P3.IpcSuspend
import Fl4Proofs.P3.IpcSetPrioX
import Fl4Proofs.P3.IpcSlotsSame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec side -/

section Spec
open Fl4Spec

theorem unbindNtfn_none {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hb : x.tcbBoundNotification = none) : unbindNotification (Z := Unit) t σ = ({((), σ)}, False) := by
  unfold unbindNotification
  rw [nd_bind_one (m := getTcbObjRef (Z := Unit) Tcb.tcbBoundNotification t) (Notif.threadGet_eq _ hk), hb]; rfl

theorem unbindFromSc_none {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hs : x.tcbSchedContext = none) : unbindFromSc (Z := Unit) t σ = ({((), σ)}, False) := by
  unfold unbindFromSc
  rw [nd_bind_one (m := getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t) (Notif.threadGet_eq _ hk), hs]
  rw [nd_bind_one (show NonDet.maybeM (schedContextUnbindTcb (Z := Unit)) (none : Option ObjRef) σ =
    ({((), σ)}, False) from rfl)]
  rfl

theorem unbindFromSc_some {σ σ1 σ2 : State Unit} {t q : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hs : x.tcbSchedContext = some q) (h1 : schedContextUnbindTcb (Z := Unit) q σ = ({((), σ1)}, False))
    {y : SchedContext} {n : Nat} (hq : σ1.kheap q = some (.schedContext y n))
    (h2 : NonDet.maybeM (completeYieldTo (Z := Unit)) y.scYieldFrom σ1 = ({((), σ2)}, False)) :
    unbindFromSc (Z := Unit) t σ = ({((), σ2)}, False) := by
  unfold unbindFromSc
  rw [nd_bind_one (m := getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t) (Notif.threadGet_eq _ hk), hs]
  rw [nd_bind_one (show NonDet.maybeM (schedContextUnbindTcb (Z := Unit)) (some q) σ = ({((), σ1)}, False) from h1)]
  show (getSchedContext (Z := Unit) q >>= fun sc => NonDet.maybeM completeYieldTo sc.scYieldFrom) σ1 = _
  rw [nd_bind_one (getSchedContext_eq hq)]; exact h2

/-- **The spec's thread finalisation** from its four steps. -/
theorem finThread_mem {σ σ1 σ2 σ3 σ4 : State Unit} {p : ObjRef}
    (h1 : unbindNotification (Z := Unit) p σ = ({((), σ1)}, False))
    (h2 : unbindFromSc (Z := Unit) p σ1 = ({((), σ2)}, False))
    (h3 : suspend (Z := Unit) p σ2 = ({((), σ3)}, False))
    (h4 : ((), σ4) ∈ (fpuRelease (Z := Unit) p σ3).1) :
    ((Cap.zombie p none 6, Cap.nullCap), σ4) ∈ (finaliseCap (Z := Unit) (.threadCap p) true σ).1 := by
  unfold finaliseCap NonDet.when prepareThreadDelete
  simp only [↓reduceIte]
  rw [nd_bind_one h1, nd_bind_one h2, nd_bind_one h3]
  exact mem_bind_nd (x := ((), σ4)) h4 (Set.mem_singleton _)

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem absCap_zombieTcb (p : U64) :
    absCap (.Zombie p capability.ZOMBIE_TCB 6#u64) = Fl4Spec.Cap.zombie p.bv none 6 := by
  simp [absCap, zombieBits, capability.ZOMBIE_TCB]

theorem unbind_ntfn_zero (s : S) (t : U64) (h0 : L.mem s (P1.boundA t) = 0#u64) :
    notification.unbind_notification st s t = ok s := by
  unfold notification.unbind_notification
  rw [tcb_bound_eq]
  simp [h0]

/-- `vcpu::detach` of a thread bound to no VCPU does nothing. -/
theorem vcpu_detach_none (s : S) (a : A) (t : U64)
    (h : L.mem s (core.num.U64.wrapping_add t 3664#u64) = 0#u64) :
    vcpu.detach st arI s a t ⦃ r => r = (s, a) ⦄ := by
  unfold vcpu.detach vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun v ev => ?_
  have hv : v = 0#u64 := by rw [ev, ho]; simpa [layout.tcb.VCPU] using h
  rw [hv, if_pos rfl]
  exact (WP.spec_ok _).2 rfl

/-- **`IRel` at `Z`'s sets gives `XTopAt` at `Z` with some ghost tree and
VSpace sets.** -/
theorem IRel.xtopMv {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {cr : Fl4Spec.Cr3} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : IRel st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ) (hAR : AR a cr) :
    ∃ (G : MdbGhost) (V : XVs), XTopAt (L := L) AR (Z.mv G V) s a σ := by
  obtain ⟨⟨Z', h1, h2, h3, h4, h5, h6, h7, h8, hX⟩, -, -⟩ := IRel.xtop (L := L) h hAR
  obtain ⟨th', G', P', L4', L3', L2', L1', N', T', C', E', R', B', c'⟩ := Z'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8
  subst h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨G', (P', L4', L3', L2', L1'), hX⟩

/-- **What a thread cap's finalisation at `XTop` reads** [J] (module
docstring), at an `XTopAt` state. -/
def ThreadFinPre (Cs : Set U64) (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧ BufWordRel Z.T (L.mem s) σ ∧
  (∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val) ∧
  IPlaced Z.N Z.T Z.E Z.R Z.B ∧ SchedValid σ ∧ ObjCover Z.N Z.T Z.E Z.R Z.C σ ∧ Inv σ ∧ NSC Z.N Z.C σ ∧
  OtherTmOK (L := L) Z Cs s σ ∧
  (∀ cr, RemoveTcbHyp st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c) ∧
  (∀ cr s' σ', IRel st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' → YieldRel Z.T Z.C (L.mem s') σ')

set_option maxHeartbeats 16000000 in
/-- **`XFinHyps.thread` holds** (module docstring). -/
theorem xFinThread_of {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (Cs : Set U64)
    (hpre : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ → ThreadFinPre (L := L) Cs Z s σ)
    (hpT : ∀ (Z : XSets) s a σ sl p, Z.th = th → XTopAt (L := L) AR Z s a σ → AbsSlot th sl →
      capAt (L.mem s) (cslotAddr sl) = ok (.Thread p) → p ∈ Z.T)
    (hP1 : ThreadP1Hyp (L := L) th) (hAT : P0.ArchTotal arI)
    (hTm : ∀ (Z : XSets) s a σ (p : U64), Z.th = th → XTopAt (L := L) AR Z s a σ → p ∈ Z.T →
      timer.remove st s p ⦃ s' => P1.WritesIn st s s' (TmW (L := L) Z.T Cs Z.c s) ∧
        L.mem s' (L.nodeAt s Z.c layout.node.REPROGRAM) = L.mem s (L.nodeAt s Z.c layout.node.REPROGRAM) ⦄)
    (hY : ∀ (Z : XSets) q, Z.th = th → ScYieldFinHyp (L := L) arI AR Z q)
    (hDbg : ∀ (Z : XSets) s a σ (p : U64), Z.th = th → XTopAt (L := L) AR Z s a σ → p ∈ Z.T →
      objects.debug_remove st s p ⦃ s' => XTopAt (L := L) AR Z s' a σ ⦄)
    (hFpu : ∀ (Z : XSets) s a σ (p : U64), Z.th = th → XTopAt (L := L) AR Z s a σ →
      arI.fpu_release a p ⦃ a' => ∃ σ', ((), σ') ∈ (Fl4Spec.fpuRelease (Z := Unit) p.bv σ).1 ∧
        XTopAt (L := L) AR Z s a' σ' ⦄) :
    XFinAt (L := L) arI FinThreadK AR th := by
  intro Z s a σ sl c hth hX hK hTh ⟨p, hc0⟩ hDS hA hc hk hw
  subst hth hc0
  have hpZ := hpT Z s a σ sl p rfl hX hA hc
  obtain ⟨X, hB, hSC, hO⟩ := hP1 s σ Z.G sl _ hDS hA hc hk
  obtain ⟨hpX, hna, hidle, hv0⟩ := hO p rfl
  have hfin : decide (Fl4Spec.isFinalCap' (absCap (.Thread p)) σ) = true := by
    simpa [FinWork, isFrame] using hw
  have hAR : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  rw [hfin]
  have hch : objects.finalise_cap st arI s a (.Thread p) true false ⦃ r => ∃ (σ' : Fl4Spec.State Unit)
      (G : MdbGhost) (V : XVs), ((Fl4Spec.Cap.zombie p.bv none 6, Fl4Spec.Cap.nullCap), σ') ∈
        (Fl4Spec.finaliseCap (Z := Unit) (.threadCap p.bv) true σ).1 ∧
      XTopAt (L := L) AR (Z.mv G V) r.2.1 r.2.2 σ' ⦄ := by
    have hfc : objects.finalise_cap st arI s a (.Thread p) true false =
        objects.finalise_cap_object st arI s a (.Thread p) true := by
      simp [objects.finalise_cap]
    rw [hfc]
    unfold objects.finalise_cap_object
    simp only [↓reduceIte]
    obtain ⟨hK0, hBW0, hNk0, hP0, hSV0, hOC0, hInv0, hNS0, hOt0, hRT0, hYR0⟩ := hpre Z s a σ rfl hX
    have hS0 := hX.fin.1.1.1
    -- the remote stall and the VCPU detach
    refine WP.spec_bind (remote_tcb_stall_id (ar := arI) a hS0 hpZ) ?_
    rintro ⟨s1, a1⟩ he1
    simp only [Prod.mk.injEq] at he1
    obtain ⟨hs1, ha1⟩ := he1
    subst s1; subst a1
    refine WP.spec_bind (vcpu_detach_none arI s a p hv0) ?_
    rintro ⟨s1, a1⟩ he1
    simp only [Prod.mk.injEq] at he1
    obtain ⟨hs1, ha1⟩ := he1
    subst s1; subst a1
    -- `unbind_notification`
    have hI0 := hX.irelK hK0 hBW0
    have h3 : notification.unbind_notification st s p ⦃ s3 => ∃ σ3,
        Fl4Spec.unbindNotification (Z := Unit) p.bv σ = ({((), σ3)}, False) ∧
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s3 σ3 ⦄ := by
      obtain ⟨x, hk, hx⟩ := hI0.1.tcb p hpZ
      by_cases h0 : L.mem s (P1.boundA p) = 0#u64
      · rw [unbind_ntfn_zero s p h0, WP.spec_ok]
        refine ⟨σ, unbindNtfn_none hk ?_, hI0⟩
        rw [hx.bound, show tBoundA p = P1.boundA p from rfl, h0, Notif.optRef_zero]
      · obtain ⟨x', xn, hk', hb, hn, hkn⟩ := bound_ntfn_of hI0 hSV0 hOC0 hpZ h0
        have hX2 := bound_wr_irel hP0 hI0 hpZ hn hk' hkn 0#u64 0#u64 (fun h => absurd rfl h)
        rw [Notif.optRef_zero] at hX2
        rw [Sched.unbind_ntfn_eq s p h0, WP.spec_ok]
        exact ⟨_, Sched.unbindNotification_eq hkn hk' hb, hX2⟩
    refine WP.spec_bind h3 ?_
    rintro s3 ⟨σ3, he3, hI3⟩
    obtain ⟨G3, V3, hX3⟩ := IRel.xtopMv hI3 hAR
    -- the timer-tree removal
    obtain ⟨-, -, -, -, -, -, -, -, hOt3, -, -⟩ := hpre (Z.mv G3 V3) s3 a σ3 rfl hX3
    refine WP.spec_bind (hTm (Z.mv G3 V3) s3 a σ3 p rfl hX3 hpZ) ?_
    rintro s4 ⟨hw4, hr4⟩
    obtain ⟨r, hX4r⟩ := hX3.tmStep hOt3 hw4 (Or.inl hr4)
    have e4 : (σ3.reprogramTimer || r) = σ3.reprogramTimer := by
      have h1 := hX4r.fin.1.1.1.repr
      have h0 := hX3.fin.1.1.1.repr
      simp only at h1
      rw [h1, h0]; unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw4.1, hr4]
    have hX4 : XTopAt (L := L) AR (Z.mv G3 V3) s4 a σ3 := by rw [e4] at hX4r; exact hX4r
    -- the rest, after `unbind_from_sc`
    have fin6 : ∀ (s5 : S) (a5 : A) (σ5 : Fl4Spec.State Unit) (G : MdbGhost) (V : XVs),
        XTopAt (L := L) AR (Z.mv G V) s5 a5 σ5 →
        Fl4Spec.unbindFromSc (Z := Unit) p.bv σ3 = ({((), σ5)}, False) →
        (do
          let (s6, a4) ← sched.suspend st arI s5 a5 p
          let s7 ← objects.debug_remove st s6 p
          let a6 ← arI.fpu_release a4 p
          let s8 ← obj.Tcb.slot p layout.tcb.SLOT_CTABLE
          ok ((capability.Cap.Zombie s8 capability.ZOMBIE_TCB layout.tcb.NUM_SLOTS, capability.Cap.Null), s7, a6))
          ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (G : MdbGhost) (V : XVs),
            ((Fl4Spec.Cap.zombie p.bv none 6, Fl4Spec.Cap.nullCap), σ') ∈
              (Fl4Spec.finaliseCap (Z := Unit) (.threadCap p.bv) true σ).1 ∧
            XTopAt (L := L) AR (Z.mv G V) r.2.1 r.2.2 σ' ⦄ := by
      intro s5 a5 σ5 G V hX5 he5
      obtain ⟨hK5, hBW5, -, -, hSV5, hOC5, hInv5, -, -, hRT5, hYR5⟩ := hpre (Z.mv G V) s5 a5 σ5 rfl hX5
      have hI5 := hX5.irelK hK5 hBW5
      refine WP.spec_bind (suspend_irel (ar := arI) hP0 (hRT5 _) s5 a5 σ5 hI5 hpZ hSV5 hOC5 hInv5 (hYR5 _)) ?_
      rintro ⟨s6, a6⟩ ⟨ha6, σ6, he6, hI6⟩
      simp only at ha6
      subst ha6
      obtain ⟨G6, V6, hX6⟩ := IRel.xtopMv hI6 hX5.fin.1.1.2.2.2.2.2.2
      refine WP.spec_bind (hDbg (Z.mv G6 V6) s6 a6 σ6 p rfl hX6 hpZ) ?_
      intro s7 hX7
      refine WP.spec_bind (hFpu (Z.mv G6 V6) s7 a6 σ6 p rfl hX7) ?_
      rintro a8 ⟨σ8, hm8, hX8⟩
      simp only [P1.tcb_slot_ctable, bind_ok, WP.spec_ok]
      exact ⟨σ8, G6, V6, finThread_mem he3 he5 he6 hm8, hX8⟩
    -- `unbind_from_sc`
    have hS4 := hX4.fin.1.1.1
    have hR4 := hX4.fin.1.1.2.2.1
    obtain ⟨-, -, hNk4, -, -, -, hInv4, hNS4, -, -, -⟩ := hpre (Z.mv G3 V3) s4 a σ3 rfl hX4
    obtain ⟨Q4, R4, hc4, hs4⟩ := hS4.lists
    obtain ⟨x4, hk4, -, -, hsc4, -⟩ := hs4.tcb p hpZ
    step with obj.Tcb.sc.spec as ⟨i, hi⟩
    step with obj.Sc.is_null.spec' as ⟨b, hb⟩
    by_cases h0 : i = 0#u64
    · have hb' : b = true := by rw [hb, h0]; rfl
      simp only [hb', ↓reduceIte, bind_ok]
      exact fin6 s4 a σ3 G3 V3 hX4 (unbindFromSc_none hk4 (by rw [hsc4, ← hi, h0, Notif.optRef_zero]))
    have hb' : b = false := by rw [hb]; simp [h0]
    simp only [hb', Bool.false_eq_true, ↓reduceIte]
    have hiC : i ∈ Z.C := by rw [hi]; exact hs4.scMem p hpZ (by rw [← hi]; exact h0)
    obtain ⟨y, n, hky, hxy⟩ := hs4.scs i hiC
    have hsp : x4.tcbSchedContext = some i.bv := by rw [hsc4, ← hi, Notif.optRef_ne h0]
    obtain ⟨y', n', hky', hyt⟩ := hInv4.back p.bv x4 i.bv hk4 hsp
    rw [hky] at hky'; cases hky'
    have hin : (do
        let s6 ← schedcontext.unbind_tcb st s4 i
        let i1 ← obj.Sc.yield_from st i s6
        let b1 ← obj.Tcb.is_null i1
        if b1 = true then ok (s6, a) else schedcontext.complete_yield_to st arI s6 a i1) ⦃ r =>
        ∃ σ5, ∃ V : XVs, XTopAt (L := L) AR (Z.mv G3 V) r.1 r.2 σ5 ∧
          Fl4Spec.unbindFromSc (Z := Unit) p.bv σ3 = ({((), σ5)}, False) ⦄ := by
      refine WP.spec_bind (unbind_tcb_refines s4 σ3 hS4 hR4 hNS4 hInv4 hiC hky hpZ hyt) ?_
      rintro s5 ⟨σ4, he4, hS5, hR5, -, -, -, hw5, -⟩
      have hX5 := xtop_sc_step (ct := σ3.curThread) hX4 hP0 hNk4
        (Sched.WritesIn.tfoot_of_kfoot (Sched.WritesIn.kfoot_of_sfoot_scw hS4 hiC (K := 24#u64) (by simp) (by simp)
          (by decide) hw5))
        ((nkt_schedContextUnbindTcb i.bv σ3 ((), σ4) (by rw [he4]; exact Set.mem_singleton _)).mono fun _ h => h.elim)
        hS5 hR5 id
      obtain ⟨Q5, R5, hc5, hs5⟩ := hS5.lists
      obtain ⟨y5, n5, hk5, hx5⟩ := hs5.scs i hiC
      step with obj.Sc.yield_from.spec' as ⟨j, hj⟩
      step with obj.Tcb.is_null.spec as ⟨b1, hb1⟩
      by_cases j0 : j = 0#u64
      · have hb1' : b1 = true := by rw [hb1, j0]; rfl
        simp only [hb1', ↓reduceIte, WP.spec_ok]
        refine ⟨σ4, V3, hX5, unbindFromSc_some hk4 hsp he4 hk5 ?_⟩
        rw [hx5.yieldFrom, ← scYieldFromA_eq, ← hj, j0, Notif.optRef_zero]; rfl
      · have hb1' : b1 = false := by rw [hb1]; simp [j0]
        simp only [hb1', Bool.false_eq_true, ↓reduceIte]
        rw [hj]
        refine WP.spec_mono (hY (Z.mv G3 V3) i rfl s5 a σ4 hX5 (by rw [← hj]; exact j0)) ?_
        rintro ⟨s6, a6⟩ ⟨σ6, V6, e6, hX6, -, -, -⟩
        refine ⟨σ6, V6, hX6, unbindFromSc_some hk4 hsp he4 hk5 ?_⟩
        rw [hx5.yieldFrom, ← scYieldFromA_eq, Notif.optRef_ne (by rw [← hj]; exact j0)]; exact e6
    refine WP.spec_bind hin ?_
    rintro ⟨s5, a5⟩ ⟨σ5, V5, hX5, he5⟩
    exact fin6 s5 a5 σ5 G3 V5 hX5 he5
  refine WP.spec_mono (WP.spec_and (P1.fin_cap_thread.slots hAT s a p true false hB hpX hna hidle hv0) hch) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨⟨e, -, f, hW⟩, σ', G, V, hm, hX'⟩
  simp only [Prod.mk.injEq, ite_true] at e
  obtain ⟨rfl, rfl⟩ := e
  have hSS := slotsSame_of_capw hX.rel.1 hSC hW
  have kb : L.ksb s' = L.ksb s := f.1
  obtain ⟨hK', hBW', -⟩ := hpre (Z.mv G V) s' a' σ' rfl hX'
  have hI' := hX'.irelK hK' hBW'
  have hck := finThread_nkc p.bv true σ _ hm
  obtain ⟨V', hX3⟩ := XTopAt.irel_same hX hI' hX'.fin.1.1.2.2.2.2.2.2 hSS hck.cdt hck.orig hck.ks kb
  refine ⟨by rw [hfin]; rfl, trivial, trivial, σ', Z.G, ?_, DState.of_same hDS hSS hX3.rel.2.1 hck.ks,
    by rw [hSS.capV hA.isSlot]; exact capV_of_capAt hc, fun y hy _ => Or.inl (hSS.capV hy),
    MdbStep.of_same hDS.1.2.2.1 hSS, ⟨V', hX3⟩, kb⟩
  rw [hfin, absCap_zombieTcb]
  exact hm

end

end

end Fl4Proofs.P3

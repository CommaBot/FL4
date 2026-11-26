/-
# P2 (line p3mc, gen 20): U20, vt's `VSafe9` discharged at every vt start

## The vt starts
The vt slot (`vq`'s right summand, `vtSlotA`) arms `localvm.handle_vm_timer_irq_local irq pl n` (the extracted tree).
At a P3 bundle state the current thread is bound to no VCPU (`vOf_zero`), so `vm_running` is false and every run
declines **writing nothing** (all checks precede `update_timestamp`). In the real memory too: the current thread is
homed on `c` (`vx_cur_home`), so its VCPU word is the view's. But the runs at the view and at the real memory read
different words when the earliest timer `tm` of `c`'s tree is another core's thread: really its `AFFINITY` is not the
core and `plan_objects` stops there; in the view it is `c` and the plan goes on into `tm`'s words, whose owner the view
moves. So the certificate runs at real values (as U17 / U19), split on `ρ (AFFINITY tm) = c`:

* `plan_objects.guard_off`: with `tm`'s `AFFINITY` not the core, `plan_objects` reads only `TIMER_MIN` and it;
* **`vt_fh_run`**: the run on any store answering the head's reads (the IRQ state word, the plan by `hpl`, the current
  thread's `CUR_THREAD` / `CUR_SC` / `STATE` / `BOUND_NTFN` / VCPU word, its bound notification's state) is the real
  run, and it declines, given the VCPU word 0;
* **`PathObl.safe_tr_dec`**: a generic decline certificate: a program whose run, at every state with the core's
  constants carrying `ρ` on a read set `Rd ⊆ Ro`, exists on every store answering `Rd`, is `Safe` (no write);
* **`vt_fh_annV`**: the read set `VtRd` at a vt view start (the IRQ word, `TIMER_MIN`, `tm`'s `AFFINITY`, if `tm` is
  homed in `ρ` its plan words and its bound notification's, the current thread's five words and its bound
  notification's state) is in `VexitRS ∖ PTE`, keeps its owner under the view, and, but for a foreign `tm`'s
  `AFFINITY`, its value; **`vt_annV`**: from `StartV2C` at a vt index (glue state `Ch σ ∧ VtEntJ8 σ`).

`VtAt`, `U20At := U19At ∨ VtAt`, **`serializable_fl4_localU20`**, **`serializable_fl4_localU19of20`**.

## Premises of `serializable_fl4_localU20` vs `serializable_fl4_localU19`
* **Removed: `VSafe9` [J] at every vt start**, so with U19 at every `vq` start. Nothing added; family and start facts
  unchanged (`fl4LocW11JC` / `StartV2C` [P]).
* Open: `VSafe9` [J] at irq (route (a)) and invocation starts; `VSafe` [J] unchanged.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPU19
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read bind_guard_congr)

section vtrun
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R]

set_option maxHeartbeats 4000000 in
/-- **`plan_objects` when the earliest thread is off the core**: it reads `TIMER_MIN` and the thread's
`AFFINITY` only. -/
theorem plan_objects.guard_off {s : S} (h1 : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) 3520#u64))
    (hoff : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s (affA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ L.cpu s) :
    localtimer.plan_objects gS s = localtimer.plan_objects st s := by
  unfold localtimer.plan_objects
  rw [PathObl.gst_cur_cpu (g := gS)]
  refine bind_guard_congr rfl fun cpu ecpu => ?_
  rw [L.cur_cpu_eq] at ecpu
  have hc := ok_inj_ff ecpu
  subst hc
  dsimp only
  rw [PathObl.obj.node_get.guard (gS := gS) s _ _ h1]
  refine bind_guard_congr rfl fun i ei => ?_
  rw [node_get_ok] at ei
  have hi := ok_inj_ff ei
  subst hi
  refine bind_guard_congr rfl fun b eb => ?_
  rw [is_null_eq eb]
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64
  · rw [if_pos (decide_eq_true h0), if_pos (decide_eq_true h0)]
  rw [if_neg (by simpa using h0), if_neg (by simpa using h0),
    PathObl.obj.Tcb.affinity.guard (gS := gS) _ s (h2 h0)]
  refine bind_guard_congr rfl fun i1 ei1 => ?_
  have ha : (i1 != L.cpu s) = true := by
    rw [aff_ok] at ei1
    rw [← ok_inj_ff ei1]
    simpa using hoff h0
  rw [if_pos ha, if_pos ha]

variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **A vt run whose current thread has no VCPU declines, on any store answering its reads** (module
docstring). -/
theorem vt_fh_run {s : S} {a : A} {irq n : U64} {pl : localtimer.TimerIrqPlan} {r : Bool × S × A}
    (hi : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hpl : localtimer.plan_objects gS s = localtimer.plan_objects st s)
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)) (h2 : R (L.nodeAt s (L.cpu s) layout.node.CUR_SC))
    (h3 : R (core.num.U64.wrapping_add (L.curW s) 3328#u64))
    (h4 : R (core.num.U64.wrapping_add (L.curW s) 3368#u64))
    (h5 : L.mem s (boundA (L.curW s)) = n → n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (h6 : R (core.num.U64.wrapping_add (L.curW s) 3664#u64))
    (hv0 : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) = 0#u64)
    (h : localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok r) :
    localvm.handle_vm_timer_irq_local gS ar s a irq pl n = ok r ∧ r.1 = false := by
  have h3' : R (stA (L.curW s)) := by rw [Fl4Proofs.P1.stA_eq]; exact h3
  have evm : localvm.vm_running st s (L.curW s) = ok false := by
    unfold localvm.vm_running
    rw [eq_of_spec_fd (vcpu.bound.spec (L := L) s (L.curW s)), hv0]
    simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  revert h
  rw [vtimer_eq, vtimer_eq]
  unfold vtimerHead
  rw [PathObl.gst_cur_cpu (g := gS), L.cur_cpu_eq]
  simp only [bind_ok, num_domains_ne_one_false, Bool.false_eq_true, ↓reduceIte]
  refine PathObl.stfh_bind (fun mx emx => ?_)
  refine PathObl.stfh_ite (fun _ => PathObl.stfh_ret) (fun hle => ?_)
  have hlt : irq.val < 128 := by
    rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
    have e := ok_inj_ff emx
    subst e
    scalar_tac
  have eirq : interrupt.irq_state gS s irq = interrupt.irq_state st s irq := by
    unfold interrupt.irq_state
    exact bind_guard_congr rfl fun i ei => PathObl.obj.ks_get.guard (gS := gS) s i (hi hlt i ei)
  rw [eirq]
  refine PathObl.stfh_bind (fun i1 _ => ?_)
  refine PathObl.stfh_ite (fun _ => PathObl.stfh_ret) (fun _ => ?_)
  rw [hpl]
  refine PathObl.stfh_bind (fun tip _ => ?_)
  refine PathObl.stfh_bind (fun b _ => ?_)
  refine PathObl.stfh_ite (fun _ => ?_) (fun _ => PathObl.stfh_ret)
  rw [PathObl.sched.cur_thread.guard (gS := gS) s h1, cur_thread_ok]
  simp only [bind_ok]
  rw [PathObl.sched.cur_sc.guard (gS := gS) s h2]
  refine PathObl.stfh_bind (fun csc _ => ?_)
  rw [PathObl.obj.Tcb.state.guard (gS := gS) _ s h3']
  refine PathObl.stfh_bind (fun i2 _ => ?_)
  refine PathObl.stfh_ite (fun _ => PathObl.stfh_ret) (fun _ => ?_)
  rw [PathObl.obj.Tcb.bound_ntfn.guard (gS := gS) _ s h4]
  refine PathObl.stfh_bind (fun i3 ei3 => ?_)
  refine PathObl.stfh_ite (fun _ => PathObl.stfh_ret) (fun hb3 => ?_)
  have e3 : i3 = n := by
    by_contra hne
    exact hb3 (bne_iff_ne.mpr hne)
  have eb : L.mem s (boundA (L.curW s)) = n := by
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at ei3
    rw [← e3]
    exact ok_inj_ff ei3
  rw [ntfn_quiet.guard (gS := gS) s n (fun hn => h5 eb hn)]
  refine PathObl.stfh_bind (fun b1 _ => ?_)
  refine PathObl.stfh_ite (fun _ => ?_) (fun _ => PathObl.stfh_ret)
  rw [vm_running.guard (gS := gS) s _ h6 (fun hne => absurd hv0 hne), evm]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  exact PathObl.stfh_ret

end vtrun

end Fl4Proofs.P2

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads safe_tr_of_states exists_mem_state OwnDep MasksWr masksOf masksOf_eq)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **A program that declines writing nothing, on every store answering a read set `Rd ⊆ Ro`, is `Safe`**
(module docstring): the run's states carry `ρ` on `Rd`. -/
theorem safe_tr_dec {X : Type} {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt : U64 → ClsOwner U64} {User : U64 → Prop} (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} (p : SProg X) (hz : NoZero p)
    (hc : L.cpu σ = c) {Ro Rd : U64 → Prop}
    (hal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → Ro q ∧ ¬ User q)
    (hRPO : ∀ x, ¬ User x → Ro x → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∀ (gS : machine.Store S) (R : U64 → Prop), GRd gS st R → (∀ b, Rd b → R b) →
        ∃ r, interp gS ar p s a = ok r) :
    Safe own cls kt c hs μ (tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar p ∅ a) := by
  refine safe_tr_of_states hL hO hmk (Hp := fun _ => False) _ a (fun x hx => hx.elim) hRPO ?_
  intro ν hν
  generalize hq : tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar p ∅ a = q
  obtain ⟨s, sc, sk, sm, hmem0⟩ := exists_mem_state hmk σ (fun x => if x ∈ reads q ν then ν x else ρ x)
  have hmem : ∀ x, Aligned x → L.mem s x = if x ∈ reads q ν then ν x else ρ x := hmem0
  have eR : ∀ b, Ro b → ¬ User b → (if b ∈ reads q ν then ν b else ρ b) = ρ b := by
    intro b hb hu'
    split_ifs
    · exact (hν.1 b (hRPO b hu' hb)).trans (hρμ b (hRPO b hu' hb)).symm
    · rfl
  have hag : ∀ b, Rd b → L.mem s b = ρ b := fun b hb => by
    rw [hmem b (hal b hb), eR b (hR0 b hb).1 (hR0 b hb).2]
  obtain ⟨r, hg⟩ := hgo s sc sk hag (guard st Rd (fun _ => False)) Rd inferInstance (fun _ h => h)
  have hW := (interp_guard _ s a r hg).2
  obtain ⟨r', hM⟩ := hgo s sc sk hag (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z)))
    (fun _ => True)
    { read := fun _ _ => rfl, read_pair := fun _ _ _ => rfl, ks_base := rfl, cur_cpu := rfl, frame_masks := rfl }
    (fun _ _ => trivial)
  have hWM := (interp_mguard _ s a r' hM).2
  have hO1 := once_of_guardG (R := Rd) (W := fun _ => False) (User := User)
    (fun q hq => (hR0 q hq).2) _ hz ∅ ∅ s a r hg
  have hOnce := once_monoR (R := Rd) (R' := Ro) (User := User)
    (fun b hb => (hR0 b hb).1) _ ∅ ∅ ∅ s a hO1 (fun _ h => h)
  refine ⟨s, fun _ => False, sc.trans hc, sk, sm.trans (masksOf_eq st σ),
    Within.mono (fun b hb => hal b hb) (fun b hb => hb) _ s a hW, hWM, hOnce,
    fun x hx => hx.elim, fun x hx hxa => by rw [hmem x hxa, if_pos hx], fun x hxa hu' hne hpo => hne ?_⟩
  rw [hmem x hxa]
  split_ifs
  · exact hν.1 x hpo
  · exact hρμ x hpo

end

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW GateField TimerField GField tcbOwner ntfnOwner)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD VDec nf_node nf_none vn_of_nf)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- **What a vt run reads at a view start** (module docstring), `tm` the earliest thread of `c`'s tree. -/
def VtRd (K : KLayoutP) (c : U64) (ρ : U64 → U64) (irq : U64) (σ : S) (b : U64) : Prop :=
  (irq.val < 128 ∧ ∃ i, interrupt.state_off irq = ok i ∧ b = core.num.U64.wrapping_add (L.ksb σ) i) ∨
  b = L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN ∨
  (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN) ≠ 0#u64 ∧
    b = core.num.U64.wrapping_add (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN)) 3520#u64) ∨
  (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN) ≠ 0#u64 ∧
    ρ (fld (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN)) oAFFINITY) = c ∧
    ((∃ k : U64, (k.val = 3568 ∨ k.val = 3368 ∨ k.val = 3328 ∨ k.val = 3336 ∨ k.val = 3360) ∧
        b = core.num.U64.wrapping_add (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN)) k) ∨
      (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))) ≠ 0#u64 ∧
        (b = core.num.U64.wrapping_add (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))))
            layout.ntfn.TAIL_STATE ∨
          b = core.num.U64.wrapping_add (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))))
            layout.ntfn.BOUND_TCB)))) ∨
  PathObl.VxRd (L := L) σ b ∨ b = core.num.U64.wrapping_add (L.curW σ) 3368#u64 ∨
  b = core.num.U64.wrapping_add (L.curW σ) 3664#u64 ∨
  (L.mem σ (boundA (L.curW σ)) ≠ 0#u64 ∧
    b = core.num.U64.wrapping_add (L.mem σ (boundA (L.curW σ))) layout.ntfn.TAIL_STATE)

set_option maxHeartbeats 8000000 in
/-- **U9's armed vt program is `Safe` at a view start** (module docstring). -/
theorem vt_fh_annV (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq n : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ)
    (hiq : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i →
      Aligned (core.num.U64.wrapping_add (L.ksb σ) i) ∧
        region K.toKLayout (core.num.U64.wrapping_add (L.ksb σ) i) = .none ∧
        ¬ ∃ w, InVcpu K.toKLayoutV w (core.num.U64.wrapping_add (L.ksb σ) i))
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (fun x => VexitRS K.toKLayoutV st lk σ x ∧ ¬ x ∈ K.ptes) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localvm.handle_vm_timer_irq_local irq pl n) ∅ a)) := by
  have hX := hJ.regionOKX
  have hK0 := hJ.regionOK
  obtain ⟨hk, -⟩ := hJ.kc
  obtain ⟨Ac, B⟩ := bunIx_of hJ
  have hI := B.bxi
  have hL := B.stLay
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayout.heap.tcbs := h0.tcbs
  have hN : NodePlaced st K.toKLayout.heap.tcbs σ (L.cpu σ) := h0.nodes _ h0.cur
  have hcT : L.curW σ ∈ K.toKLayout.heap.tcbs := h0.curT
  have hcur := vx_cur_home hJ hmm
  let Rs : U64 → Prop := fun x => VexitRS K.toKLayoutV st lk σ x ∧ ¬ x ∈ K.ptes
  have rsOf : ∀ x, Aligned x → region K.toKLayout x ≠ .none →
      PathObl.RPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) x → Rs x := fun x ha hr h =>
    ⟨⟨ha, Or.inr (rpermV_of_own (fun ⟨w, hw⟩ => hr (hK.base.none w x hw)) h)⟩, fun hp => hr (hK.none _ hp)⟩
  -- the good words: in the read set, kept by the view (value and owner), no user word
  let G : U64 → Prop := fun x => Rs x ∧ SR K c ρ x ∧ x ∉ K.user
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → G (L.nodeAt σ (L.cpu σ) o) := by
    intro o ho h8
    have hr : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) := hL.nd o ho
    have hr' : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node c := by rw [hr, hc]
    exact ⟨rsOf _ (nodeAt_aligned hN ho h8) (by rw [hr]; intro h; cases h)
        (Or.inl (held_core (hL.own_node _ ho))),
      sr_nf hK (by rw [hr']; intro h; cases h) (nf_node hr'), hL.nu_node ho⟩
  -- a thread's `AFFINITY` at the view is the core
  have affC : ∀ t, t ∈ K.toKLayout.heap.tcbs → L.mem σ (affA t) = L.cpu σ := fun t ht => by
    have hu : affA t ∉ K.user := hL.nu_tcb ht (k := 3520#u64) (by simp) (by simp)
    have ha : Aligned (affA t) := field_aligned (hT _ ht) (by simp) (by simp)
    rw [hmm _ ha hu, hc]
    exact CoreView.view_aff hK0 ht c ρ
  have ownT : ∀ t k, t ∈ K.toKLayout.heap.tcbs → 256 ≤ k.val → k.val < 4096 →
      OwnMap.own K.toKLayout (L.mem σ) (core.num.U64.wrapping_add t k) = tcbOwner (L.mem σ) t k.val :=
    fun t k ht h1 h2 => by
      have e := hL.own_tcb hT (L.mem σ) ht (k := k) h1 h2
      unfold fld at e
      exact e
  have homeR : ∀ t k, t ∈ K.toKLayout.heap.tcbs → 256 ≤ k.val → k.val < 4096 → ¬ GateField k.val →
      ¬ TimerField k.val → ¬ GField k.val →
      PathObl.RPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) (core.num.U64.wrapping_add t k) :=
    fun t k ht h1 h2 g1 g2 g3 => by
      refine Or.inl (held_core ?_)
      rw [ownT t k ht h1 h2, tcbOwner, if_neg g1, if_neg g2, if_neg g3]
      exact congrArg Owner.core (affC t ht)
  have gateR : ∀ t k, t ∈ K.toKLayout.heap.tcbs → 256 ≤ k.val → k.val < 4096 → GateField k.val →
      PathObl.RPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) (core.num.U64.wrapping_add t k) :=
    fun t k ht h1 h2 g => Or.inr (by unfold PathObl.GateOnly; rw [ownT t k ht h1 h2, tcbOwner, if_pos g])
  have tG : ∀ t k, t ∈ K.toKLayout.heap.tcbs → ρ (fld t oAFFINITY) = c → 256 ≤ k.val → k.val < 4096 →
      k.val % 8 = 0 →
      PathObl.RPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) (core.num.U64.wrapping_add t k) →
      G (core.num.U64.wrapping_add t k) := fun t k ht hh h1 h2 h3 hp => by
    have htH : K.toKLayout.heap t = some .tcb := ht
    obtain ⟨r, -, ha⟩ := hX.tcbW t htH k (by omega) h2 h3
    exact ⟨rsOf _ ha (by rw [r]; intro h; cases h) hp, sr_tcb hK hX htH hh (o := k) (by omega) h2 h3,
      hL.nu_tcb ht h1 h2⟩
  -- a homed thread's bound notification
  have ntG : ∀ t, t ∈ K.toKLayout.heap.tcbs → ρ (fld t oAFFINITY) = c → L.mem σ (boundA t) ≠ 0#u64 →
      G (core.num.U64.wrapping_add (L.mem σ (boundA t)) layout.ntfn.TAIL_STATE) ∧
        G (core.num.U64.wrapping_add (L.mem σ (boundA t)) layout.ntfn.BOUND_TCB) := by
    intro t ht hh hb
    have hNt : L.mem σ (boundA t) ∈ K.toKLayout.heap.ntfns := hI.2.2.1.2.2.bnd _ ht hb
    have hbt := hI.2.2.1.2.2.bs.tb _ ht hb
    generalize hpq : L.mem σ (boundA t) = p at hNt hbt ⊢
    have hpH : K.toKLayout.heap p = some .ntfn := hNt
    obtain ⟨r24, -, a24⟩ := hX.ntW _ hpH 24#u64 (by simp) (by simp)
    have r24' : region K.toKLayout (fld p 24#u64) = .ntfn p := r24
    have eA : fld p 24#u64 = ntfnBtA p := by
      unfold fld ntfnBtA layout.ntfn.BOUND_TCB
      rfl
    have hbσ : L.mem σ (fld p 24#u64) = t := by rw [eA]; exact hbt
    have hbρ : ρ (fld p 24#u64) = t := by
      have e1 : view K.toKLayout c ρ (fld p 24#u64) = ρ (fld p 24#u64) := view_ntfn r24'
      have e2 : L.mem σ (fld p 24#u64) = view K.toKLayout c ρ (fld p 24#u64) :=
        hmm (fld p 24#u64) a24 (hL.nu (by rw [r24']; intro h; cases h))
      rw [← e1, ← e2]; exact hbσ
    have hnf : ∀ b, region K.toKLayout b = .ntfn p → CoreView.NotForeign K.toKLayout c ρ b := fun b hr =>
      nf_ntfn hr (fun _ => by rw [hbρ]; exact hh)
    have one : ∀ k : U64, k.val < 64 → k.val % 8 = 0 →
        PathObl.RPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) (core.num.U64.wrapping_add p k) →
        G (core.num.U64.wrapping_add p k) := fun k h1 h2 hp => by
      obtain ⟨r, -, ha⟩ := hX.ntW _ hpH k h1 h2
      exact ⟨rsOf _ ha (by rw [r]; intro h; cases h) hp, sr_nf hK (by rw [r]; intro h; cases h) (hnf _ r),
        hL.nu (by rw [r]; intro h; cases h)⟩
    have ownN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 →
        OwnMap.own K.toKLayout (L.mem σ) (core.num.U64.wrapping_add p k) = ntfnOwner K.toKLayout (L.mem σ) p k.val :=
      fun k h1 h2 => by
        obtain ⟨r, v, -⟩ := hX.ntW _ hpH k h1 h2
        simp only [OwnMap.own, r, v]
    have htT : K.toKLayout.heap t = some .tcb := ht
    refine ⟨one _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]) (Or.inl (held_core ?_)),
      one _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]) (Or.inr ?_)⟩
    · have hv : layout.ntfn.TAIL_STATE.val = 8 := by simp [layout.ntfn.TAIL_STATE]
      rw [ownN _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]), hv, ntfnOwner,
        if_neg (by omega), hbσ, if_pos htT]
      exact congrArg Owner.core (affC t ht)
    · have hv : layout.ntfn.BOUND_TCB.val = 24 := by simp [layout.ntfn.BOUND_TCB]
      unfold PathObl.GateOnly
      rw [ownN _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]), hv, ntfnOwner, if_pos rfl]
  -- the IRQ word
  have iG : ∀ i, irq.val < 128 → interrupt.state_off irq = ok i → G (core.num.U64.wrapping_add (L.ksb σ) i) := by
    intro i hlt hi
    obtain ⟨ha, hr, hnv⟩ := hiq hlt i hi
    have hpt := hq.ksw (state_off_lt hlt hi)
    refine ⟨⟨⟨ha, Or.inr (rpermV_of_own hnv (Or.inr (by unfold PathObl.GateOnly; simp only [OwnMap.own, hr])))⟩,
      hpt⟩, ⟨vn_of_nf hK (nf_none hr), hpt⟩, fun hu => hJ.userKs hu (state_off_lt hlt hi) (by rw [hk])⟩
  -- the current thread's words
  have cG : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 →
      PathObl.RPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) (core.num.U64.wrapping_add (L.curW σ) k) →
      G (core.num.U64.wrapping_add (L.curW σ) k) := fun k h1 h2 h3 hp => tG _ k hcT hcur h1 h2 h3 hp
  -- the earliest thread
  set tm := L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN) with htm
  have tmT : tm ≠ 0#u64 → tm ∈ K.toKLayout.heap.tcbs := fun hne =>
    (tmin_facts (BXI.blk hI) h0.cur hne).1
  -- every word of `VtRd`: in `Ro`, no user word
  let Ro : U64 → Prop := fun q => Rs q ∧ VO K c ρ q
  have gRo : ∀ b, G b → Ro b ∧ b ∉ K.user := fun b hb => ⟨⟨hb.1, hb.2.1.1.2⟩, hb.2.2⟩
  have aG : tm ≠ 0#u64 → Ro (core.num.U64.wrapping_add tm 3520#u64) ∧
      core.num.U64.wrapping_add tm 3520#u64 ∉ K.user := fun hne => by
    have ht := tmT hne
    have htH : K.toKLayout.heap tm = some .tcb := ht
    obtain ⟨r, -, ha⟩ := hX.tcbW tm htH 3520#u64 (by simp) (by simp) (by simp)
    have hpt : core.num.U64.wrapping_add tm 3520#u64 ∉ K.ptes := fun hp => by
      have h := hK.none _ hp
      rw [r] at h
      cases h
    have hnv : ¬ ∃ w, InVcpu K.toKLayoutV w (core.num.U64.wrapping_add tm 3520#u64) := fun ⟨w, hw⟩ => by
      have h := hK.base.none w _ hw
      rw [r] at h
      cases h
    refine ⟨⟨rsOf _ ha (by rw [r]; intro h; cases h) (gateR tm 3520#u64 ht (by simp) (by simp)
      (by simp [GateField])), ?_⟩, hL.nu_tcb ht (k := 3520#u64) (by simp) (by simp)⟩
    show ownP K (view K.toKLayout c ρ) (fld tm oAFFINITY) = ownP K ρ (fld tm oAFFINITY)
    have hpt' : fld tm oAFFINITY ∉ K.ptes := hpt
    have hnv' : ¬ ∃ w, InVcpu K.toKLayoutV w (fld tm oAFFINITY) := hnv
    rw [ownP_off hpt', ownP_off hpt', ownV_off hnv', ownV_off hnv']
    exact (OwnMap.own_aff_gate hK0 htH _).trans (OwnMap.own_aff_gate hK0 htH _).symm
  have W : ∀ b, VtRd (L := L) K c ρ irq σ b → Ro b ∧ b ∉ K.user := by
    intro b hb
    rcases hb with ⟨hlt, i, hi, rfl⟩ | rfl | ⟨hne, rfl⟩ | ⟨hne, hh, hb⟩ | hb | rfl | rfl | ⟨hb0, rfl⟩
    · exact gRo _ (iG i hlt hi)
    · exact gRo _ (nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
    · exact aG hne
    · have ht := tmT hne
      rcases hb with ⟨k, hk', rfl⟩ | ⟨hb0, rfl | rfl⟩
      · rcases hk' with e | e | e | e | e
        · -- TIMER_HEIGHT: a timer word of an armed thread of `c`'s tree
          have htH : K.toKLayout.heap tm = some .tcb := ht
          obtain ⟨r, -, ha⟩ := hX.tcbW tm htH k (by omega) (by omega) (by omega)
          exact gRo _ ⟨⟨⟨ha, Or.inr (tmw_ownV hK.base hI hL B.ntw hne
              (Or.inl ⟨k, Or.inr (Or.inr (Or.inl e)), rfl⟩))⟩, fun hp => by
              have h := hK.none _ hp
              rw [r] at h
              cases h⟩,
            sr_tcb hK hX htH hh (o := k) (by omega) (by omega) (by omega), hL.nu_tcb ht (by omega) (by omega)⟩
        · exact gRo _ (tG tm k ht hh (by omega) (by omega) (by omega)
            (gateR tm k ht (by omega) (by omega) (by unfold GateField; omega)))
        all_goals exact gRo _ (tG tm k ht hh (by omega) (by omega) (by omega)
            (homeR tm k ht (by omega) (by omega) (by unfold GateField; omega) (by unfold TimerField; omega)
              (by unfold GField; omega)))
      · exact gRo _ (ntG tm ht hh hb0).1
      · exact gRo _ (ntG tm ht hh hb0).2
    · rcases hb with rfl | rfl | rfl
      · exact gRo _ (nR _ (by rw [curth_val]; omega) (by rw [curth_val]))
      · exact gRo _ (nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      · exact gRo _ (cG 3328#u64 (by simp) (by simp) (by simp)
          (homeR _ _ hcT (by simp) (by simp) (by simp [GateField]) (by simp [TimerField]) (by simp [GField])))
    · exact gRo _ (cG 3368#u64 (by simp) (by simp) (by simp)
        (gateR _ _ hcT (by simp) (by simp) (by simp [GateField])))
    · exact gRo _ (cG 3664#u64 (by simp) (by simp) (by simp)
        (gateR _ _ hcT (by simp) (by simp) (by simp [GateField])))
    · exact gRo _ (ntG _ hcT hcur hb0).1
  have hal : ∀ b, VtRd (L := L) K c ρ irq σ b → Aligned b := fun b hb => (W b hb).1.1.1.1
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hRPO : ∀ x, x ∉ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_off hx.1.2, ← hc, ← hl]
      exact po_of_rperm (hx.1.1.2.resolve_left hu)
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  have kv : ∀ b, G b → ρ b = L.mem σ b := fun b hb => hb.2.1.1.1.symm.trans (hmm b hb.1.1.1 hb.2.2).symm
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      localvm.handle_vm_timer_irq_local mm ar x a irq pl n =
        interp mm ar (R.localvm.handle_vm_timer_irq_local irq pl n) x a :=
    fun mm x a => congrFun (congrFun (vtimer_isProg S irq pl n A ar mm) x) a
  have gS8 : G (core.num.U64.wrapping_add (L.curW σ) 3368#u64) :=
    cG 3368#u64 (by simp) (by simp) (by simp) (gateR _ _ hcT (by simp) (by simp) (by simp [GateField]))
  have gS6 : G (core.num.U64.wrapping_add (L.curW σ) 3664#u64) :=
    cG 3664#u64 (by simp) (by simp) (by simp) (gateR _ _ hcT (by simp) (by simp) (by simp [GateField]))
  have hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ →
      (∀ b, VtRd (L := L) K c ρ irq σ b → L.mem s b = ρ b) →
      ∀ (gS : machine.Store S) (Rg : U64 → Prop), GRd gS st Rg → (∀ b, VtRd (L := L) K c ρ irq σ b → Rg b) →
        ∃ r, interp gS ar (R.localvm.handle_vm_timer_irq_local irq pl n) s a = ok r := by
    intro s hcs hks hag gS Rg iR hRR
    haveI := iR
    have eN : ∀ o, L.nodeAt s (L.cpu s) o = L.nodeAt σ (L.cpu σ) o := fun o => by
      rw [hcs]; exact nodeAt_of_ksb hks _ o
    have kvs : ∀ b, VtRd (L := L) K c ρ irq σ b → G b → L.mem s b = L.mem σ b := fun b hb hg =>
      (hag b hb).trans (kv b hg)
    have rTM : VtRd (L := L) K c ρ irq σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN) := Or.inr (Or.inl rfl)
    have eTM : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = tm := by
      rw [eN]; exact kvs _ rTM (nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
    have rCT : VtRd (L := L) K c ρ irq σ (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl rfl)))))
    have eCT : L.curW s = L.curW σ := by
      unfold LawfulStore.curW
      rw [eN]
      exact kvs _ rCT (nR _ (by rw [curth_val]; omega) (by rw [curth_val]))
    have hpl : localtimer.plan_objects gS s = localtimer.plan_objects st s := by
      have h1 : Rg (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by rw [eN]; exact hRR _ rTM
      by_cases hh : tm ≠ 0#u64 ∧ ρ (fld tm oAFFINITY) = c
      · refine plan_objects.guard (gS := gS) h1 (fun _ => ?_)
        rw [eTM]
        obtain ⟨hne, hho⟩ := hh
        have r4 : ∀ k : U64, (k.val = 3568 ∨ k.val = 3368 ∨ k.val = 3328 ∨ k.val = 3336 ∨ k.val = 3360) →
            Rg (core.num.U64.wrapping_add tm k) := fun k hk' =>
          hRR _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, hho, Or.inl ⟨k, hk', rfl⟩⟩))))
        refine ⟨hRR _ (Or.inr (Or.inr (Or.inl ⟨hne, rfl⟩))), r4 3568#u64 (by simp), r4 3368#u64 (by simp),
          fun _ => ⟨?_, r4 3336#u64 (by simp), r4 3360#u64 (by simp), fun nb enb hnb => ?_⟩⟩
        · have h3 : Rg (core.num.U64.wrapping_add tm 3328#u64) := r4 3328#u64 (by simp)
          rw [← Fl4Proofs.P1.stA_eq] at h3
          exact h3
        · have ht := tmT hne
          have gB := tG tm 3368#u64 ht hho (by simp) (by simp) (by simp)
            (gateR _ _ ht (by simp) (by simp) (by simp [GateField]))
          have rB : VtRd (L := L) K c ρ irq σ (core.num.U64.wrapping_add tm 3368#u64) :=
            Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, hho, Or.inl ⟨3368#u64, by simp, rfl⟩⟩)))
          have eB : L.mem s (boundA tm) = L.mem σ (boundA tm) := kvs _ rB gB
          have enb' : L.mem σ (boundA tm) = nb := by
            rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at enb
            rw [← eB]
            exact ok_inj_ff enb
          subst enb'
          exact ⟨hRR _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, hho, Or.inr ⟨hnb, Or.inl rfl⟩⟩)))),
            hRR _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, hho, Or.inr ⟨hnb, Or.inr rfl⟩⟩))))⟩
      · refine plan_objects.guard_off (gS := gS) h1 (fun hne => ?_) (fun hne => ?_)
        · rw [eTM] at hne ⊢
          exact hRR _ (Or.inr (Or.inr (Or.inl ⟨hne, rfl⟩)))
        · rw [eTM] at hne ⊢
          have hho : ρ (fld tm oAFFINITY) ≠ c := fun e => hh ⟨hne, e⟩
          have ea : L.mem s (core.num.U64.wrapping_add tm 3520#u64) = ρ (core.num.U64.wrapping_add tm 3520#u64) :=
            hag _ (Or.inr (Or.inr (Or.inl ⟨hne, rfl⟩)))
          show L.mem s (core.num.U64.wrapping_add tm 3520#u64) ≠ L.cpu s
          rw [ea, hcs, hc]
          exact hho
    obtain ⟨r, hr, -⟩ :=
      spec_ex_fd (P0.localvm.handle_vm_timer_irq_local.p0 st ar s a irq pl n LawfulStore.total hA)
    have r6 : VtRd (L := L) K c ρ irq σ (core.num.U64.wrapping_add (L.curW σ) 3368#u64) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    have r7 : VtRd (L := L) K c ρ irq σ (core.num.U64.wrapping_add (L.curW σ) 3664#u64) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    have hrun := vt_fh_run ar (gS := gS) (R := Rg) (n := n) (pl := pl)
      (fun hlt i hi => by rw [hks]; exact hRR _ (Or.inl ⟨hlt, i, hi, rfl⟩))
      hpl
      (by rw [eN]; exact hRR _ rCT)
      (by rw [eN]; exact hRR _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl rfl))))))))
      (by rw [eCT]; exact hRR _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr rfl))))))))
      (by rw [eCT]; exact hRR _ r6)
      (fun eb hn => by
        rw [eCT] at eb
        have e6 : L.mem s (boundA (L.curW σ)) = L.mem σ (boundA (L.curW σ)) := kvs _ r6 gS8
        have en : L.mem σ (boundA (L.curW σ)) = n := e6.symm.trans eb
        subst en
        exact hRR _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hn, rfl⟩))))))))
      (by rw [eCT]; exact hRR _ r7)
      (by rw [eCT, kvs _ r7 gS6]; exact vOf_zero hJ)
      hr
    exact ⟨r, by rw [← hp]; exact hrun.1⟩
  have h := PathObl.safe_tr_dec (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) hmk (a := a)
    (R.localvm.handle_vm_timer_irq_local irq pl n) (vtimer_noZero irq pl n) hc (Ro := Ro)
    (Rd := VtRd (L := L) K c ρ irq σ) hal W hRPO (fun x hx => hV.2.1 x hx) hgo
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The vt starts** (`vq`'s right summand). -/
def VtAt (_K : KLayoutP) (_c : U64) (_hs : U64 → Prop) (_ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.vq (.inr _)) => True
  | _ => False

/-- **The exempt starts of U20**: U19's and the vt starts. -/
def U20At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U19At (S := S) K c hs ρ k0 i ∨ VtAt (S := S) K c hs ρ k0 i

set_option maxHeartbeats 8000000 in
/-- **U9's re-annotated body is `Safe` at every vt start** (module docstring). -/
theorem vt_annV {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : VtAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · rcases j with j | j
    · exact False.elim hf
    · obtain ⟨hLk, hG0⟩ := hsf
      obtain ⟨q0, ⟨h1, σ, ⟨-, hEn⟩, hG⟩, e⟩ := hG0 (fun s => hLk.kernDetS _ s)
      obtain ⟨σ', a, hσ, hc, hl, hμ, rfl⟩ := hG (vtEu_of hEn)
      subst e
      have hEn' : VtEntJ8 st j K.toKLayoutV σ' := by rw [hσ]; exact hEn
      have hJ : SlJAt (L := L) K.toKLayout σ' := hEn'.ix.slJAtS.slJAt
      have hP := VtEntJ8.pre st hEn'
      have hc' : L.cpu σ' = c := hc
      have hl' : j.lk σ' = (fun l => s.lk l = some c) := hl
      have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x := hμ
      have hq : QPs K st σ' := by
        obtain ⟨s1, ⟨nv, he⟩, hkeep⟩ := hE
        exact qPs_of_convRN (S' := S) (st' := st) (L' := L) (L := L) (σ := σ') he nv ⟨σ', hJ⟩ hkeep hJ.kc.1 hmm
      unfold annV
      rw [hM.own, hM.cls, hM.ko] at hV ⊢
      have h := vt_fh_annV ar hA (masksWr_plain st) hK hU hV (lk := j.lk) (n := j.n) (pl := j.pl) (a := a)
        hJ hq (fun hlt i hi => hP.iq hlt i hi) hc' hl' hmm
      rw [tr_cut (VexitRS K.toKLayoutV st j.lk σ') (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ') (masksOf st σ') ar
        (R.localvm.handle_vm_timer_irq_local j.irq j.pl j.n) ∅ a] at h
      convert h using 3
      unfold LocalPath.body
      rw [hc]
      all_goals rfl
  · exact False.elim hf

/-- **FL4 end to end with vq's `VSafe9` discharged** (module docstring), over U18's family. The conclusion is about
the physical memory. -/
theorem serializable_fl4_localU20 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U20At (S := S)) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  refine serializable_e2ePV9 _ h0 hA0 hK0 hU0 hM0 (execPV9_of_WPRV10S ?_ ?_ ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  · intro Ch K s hK hU c hs q i hC hE hsf
    rcases i with i | ((j | j) | j)
    · exact startAt_UNC st ar hA a0 P hIoa hC hE hsf
    · exact delPteStart_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact invStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact cmStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · intro s K hK hU c k ρ i hM hV hn
    exact vSafe_ioC st ar hA a0 hM hV (not_not.mp hn)
  · intro Ch s K hK hU c k ρ i hC hE hsf hM hV hf
    rcases hf with ((((((hf | hf) | hf) | hf) | hf) | hf) | hf)
    · exact vmF_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact vmR_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact sl_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact st_annV_fh st ar hA a0 hC hE hsf hM hV hf
    · exact st_annV_h st ar hA a0 hC hE hsf hM hV hf
    · exact vx_annV st ar hA a0 hsf hM hV hf
    · exact vt_annV st ar hA a0 hE hsf hM hV hf

/-- **U19's statement follows from U20** (every U19 execution is a U20 one). -/
theorem serializable_fl4_localU19of20 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U19At (S := S)) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU20 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    (execWPRV10_mono (fun _ _ _ _ _ _ hf => Or.inl hf) h) hq

end all

end
end Fl4Proofs.P2.E2EP

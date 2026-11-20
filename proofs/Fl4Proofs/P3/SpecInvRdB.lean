/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd1): **the SC switch at the
kernel exit: `refill_unblock_check` and `switch_sched_context` give `OffReady`
and keep `Rdy`** (spec side only, outside the `JAtZ` cone).

* `wl_inv`: an invariant of `whileLoop`'s outcomes.
* `ruc_out`: `refill_unblock_check p` either changes nothing, or rewrites only
  the SC at `p` (and sets the reprogram flag), the new head at the current
  time, binding / refill max / period / sporadic flag kept, refills non-empty
  (`refill_head_overlapping_loop`'s merges keep the head's time).
* `icb_out`: the same for `if_constant_bandwidth_refill_unblock_check`.
* `Excl σ p`: no thread bound to `p` is ready-queued, the switch target, or in
  a `BlkR` state (at the SC switch, the only thread bound to the new SC is
  the new current thread, which is dequeued, not the switch target (the action
  is `resume_cur_thread`) and runnable). `rdy_framex`: `Rdy` across any
  rewrite of such an SC keeping its refill-max clause.
* **`sw_out`**: `switch_sched_context` from a state with `Rdy`, `OffReady`,
  `Suff` (the intra-entry sufficiency), the current SC an SC with refills when
  active, the current thread bound to an SC `p` with refills whose head is ready
  when `p` is not the current SC (the off1 item 6 obligation: from R1 / R2 /
  the idle SC), and `Excl σ p` when `p` is not the current SC: afterwards
  `Rdy`, **`OffReady`** and the current SC is `p`.
-/
import Fl4Proofs.P3.SpecInvRdA
open Classical
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

section
open Fl4Spec

/-- **An invariant of `whileLoop`'s outcomes.** -/
theorem wl_inv {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α} (P : State Unit → Prop)
    (hB : ∀ a s, P s → C a s → ∀ y ∈ (B a s).1, P y.2) {a : α} {s : State Unit} (hs : P s)
    {r : α × State Unit} (hr : r ∈ (NonDet.whileLoop C B a s).1) : P r.2 := by
  have hw : NonDet.WhileResults C B a s r := hr
  clear hr
  revert hs
  induction hw with
  | done _ => exact id
  | step hc hm _ ih => exact fun hs => ih (hB _ _ hs hc _ hm)

/-- The merge invariant of `refill_unblock_check` from `σ2`, SC `p`, head time `T`. -/
def UI (σ2 : State Unit) (p : ObjRef) (n : Nat) (T : Time) (y0 : SchedContext) (s : State Unit) : Prop :=
  ∃ z, s = updSc σ2 p z n ∧ z.scRefills ≠ [] ∧ (refillHd z).rTime = T ∧ z.scTcb = y0.scTcb ∧
    z.scRefillMax = y0.scRefillMax ∧ z.scSporadic = y0.scSporadic ∧ z.scPeriod = y0.scPeriod

theorem ui_merge {σ2 : State Unit} {p : ObjRef} {n : Nat} {T : Time} {y0 : SchedContext} (a : Unit)
    (s : State Unit) (hs : UI σ2 p n T y0 s) (hc : the (refillHeadOverlapping (Z := Unit) p s) = true) :
    ∀ y ∈ (mergeOverlappingRefills (Z := Unit) p s).1, UI σ2 p n T y0 y.2 := by
  obtain ⟨z, rfl, hz1, hz2, hz3, hz4, hz5, hz6⟩ := hs
  rw [refillHeadOverlapping_eq (kh_upd _ _ _ _)] at hc
  have hlen : z.scRefills.length > 1 := by
    simp only [Sched.the_some, decide_eq_true_eq] at hc; exact hc.1
  intro y hy
  unfold mergeOverlappingRefills at hy
  rw [nd_bind_one (refillPopHead_eq (kh_upd _ _ _ _) hz1), updateRefillHd_eq (kh_upd _ _ _ _), updSc_updSc,
    updSc_updSc] at hy
  obtain rfl : y = ((), _) := hy
  refine ⟨_, rfl, by simp, ?_, hz3, hz4, hz5, hz6⟩
  show (refillHd { z with scRefills := mergeRefill (refillHd z) (the z.scRefills.tail.head?) ::
    z.scRefills.tail.tail }).rTime = T
  simp only [refillHd, List.head?_cons, Sched.the_some, mergeRefill]
  exact hz2

/-- **`refill_unblock_check`** (module docstring). -/
theorem ruc_out {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) {r : Unit × State Unit}
    (hr : r ∈ (refillUnblockCheck (Z := Unit) p σ).1) :
    r.2 = σ ∨ UI { σ with reprogramTimer := true } p n σ.curTime y r.2 := by
  unfold refillUnblockCheck at hr
  rw [nd_bind_one (isRoundRobin_eq hk), nd_bind_one (getScRefillReady_eq hk hne)] at hr
  simp only [NonDet.when] at hr
  split_ifs at hr with hc
  · rw [nd_gets_bind, nd_bind_one (updateRefillHd_eq hk _), SInvV.sv_bind_modify] at hr
    right
    unfold refillHeadOverlappingLoop at hr
    refine wl_inv (UI { σ with reprogramTimer := true } p n σ.curTime y) (fun a s hs hc' => ui_merge a s hs hc')
      ?_ hr
    refine ⟨{ y with scRefills := { (the y.scRefills.head?) with rTime := σ.curTime } :: y.scRefills.tail }, rfl,
      by simp, ?_, rfl, rfl, rfl, rfl⟩
    simp only [refillHd, List.head?_cons, Sched.the_some]
  · left
    obtain rfl : r = ((), σ) := hr
    rfl

/-- **`if_constant_bandwidth_refill_unblock_check (some p)`**. -/
theorem icb_out {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) {r : Unit × State Unit}
    (hr : r ∈ (ifConstantBandwidthRefillUnblockCheck (Z := Unit) (some p) σ).1) :
    r.2 = σ ∨ UI { σ with reprogramTimer := true } p n σ.curTime y r.2 := by
  change r ∈ (ifCondRefillUnblockCheck (Z := Unit) (some p) none none σ).1 at hr
  unfold ifCondRefillUnblockCheck NonDet.maybeM at hr
  dsimp only at hr
  rw [nd_bind_one (getSchedContext_eq hk), nd_gets_bind, nd_pure_bind'] at hr
  simp only [NonDet.when] at hr
  split_ifs at hr
  all_goals first
    | exact ruc_out hk hne hr
    | (left; obtain rfl : r = ((), σ) := hr; rfl)

/-! ## The SC switch -/

/-- No thread bound to `p` is queued, the switch target, or `BlkR`. -/
def Excl (σ : State Unit) (p : ObjRef) : Prop :=
  ∀ t x, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some p →
    (∀ d q, t ∉ σ.readyQueues d q) ∧ σ.schedulerAction ≠ .switchThread t ∧ ¬ BlkR x.tcbState x.tcbFault

theorem rdyT_keep {σ σ' : State Unit} {p : ObjRef} (hk : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q)
    (ht : σ'.curTime = σ.curTime) (hpt : ∀ x, σ.kheap p ≠ some (.tcb x)) {t : ObjRef} (h : RdyT σ t)
    (hn : ∀ x, σ.kheap t = some (.tcb x) → x.tcbSchedContext ≠ some p) : RdyT σ' t := by
  obtain ⟨x, c, y, n, hx, hc, hy, ha, hr, hs⟩ := h
  have htp : t ≠ p := by rintro rfl; exact hpt x hx
  have hcp : c ≠ p := by rintro rfl; exact hn x hx hc
  exact ⟨x, c, y, n, by rw [hk t htp]; exact hx, hc, by rw [hk c hcp]; exact hy, ha, by rw [ht]; exact hr, hs⟩

/-- **`Rdy` across a rewrite of an `Excl` SC.** -/
theorem rdy_framex {σ σ' : State Unit} {p : ObjRef} (h : Rdy σ) (hk : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q)
    (ht : σ'.curTime = σ.curTime) (hq : σ'.readyQueues = σ.readyQueues)
    (ha : σ'.schedulerAction = σ.schedulerAction) (hX : Excl σ p)
    (hpt : ∀ x, σ.kheap p ≠ some (.tcb x)) (hpt' : ∀ x, σ'.kheap p ≠ some (.tcb x))
    (hpv : ∀ z n, σ'.kheap p = some (.schedContext z n) → scActive z = true → MIN_REFILLS ≤ z.scRefillMax) :
    Rdy σ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun d q t hm => ?_, fun t e => ?_, fun t x c hx hb hc => ?_, fun q z n hz hz' => ?_⟩
  · rw [hq] at hm
    exact rdyT_keep hk ht hpt (h1 d q t hm) fun x hx e => (hX t x hx e).1 d q hm
  · rw [ha] at e
    exact rdyT_keep hk ht hpt (h2 t e) fun x hx e' => (hX t x hx e').2.1 e
  · have htp : t ≠ p := by rintro rfl; exact hpt' x hx
    rw [hk t htp] at hx
    exact rdyT_keep hk ht hpt (h3 t x c hx hb hc) fun x' hx' e' => by
      rw [hx] at hx'; cases hx'; exact (hX t x hx e').2.2 hb
  · by_cases e : q = p
    · subst e; exact hpv z n hz hz'
    · rw [hk q e] at hz; exact h4 q z n hz hz'

/-- `Rdy` reads only the heap, the queues, the action and the time. -/
theorem rdy_congr {σ σ' : State Unit} (h : Rdy σ) (hk : σ'.kheap = σ.kheap) (ht : σ'.curTime = σ.curTime)
    (hq : σ'.readyQueues = σ.readyQueues) (ha : σ'.schedulerAction = σ.schedulerAction) : Rdy σ' := by
  have F : ∀ {t}, RdyT σ t → RdyT σ' t := fun {t} ⟨x, c, y, n, hx, hc, hy, h1, h2, h3⟩ =>
    ⟨x, c, y, n, by rw [hk]; exact hx, hc, by rw [hk]; exact hy, h1, by rw [ht]; exact h2, h3⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun d q t hm => F (h1 d q t (hq ▸ hm)), fun t e => F (h2 t (ha ▸ e)),
    fun t x c hx hb hc => F (h3 t x c (hk ▸ hx) hb hc), fun q z n hz hz' => h4 q z n (hk ▸ hz) hz'⟩

/-- **`switch_sched_context`** (module docstring). -/
theorem sw_out {σ : State Unit} {x : SchedContext} {n : Nat} {xt : Tcb} {p : ObjRef} {y : SchedContext} {m : Nat}
    (h : Rdy σ) (hk : σ.kheap σ.curSc = some (.schedContext x n)) (hO : Sched.OffReady σ) (hS : Suff σ)
    (hne : scActive x = true → x.scRefills ≠ []) (hct : σ.kheap σ.curThread = some (.tcb xt))
    (hsc : xt.tcbSchedContext = some p) (hp : σ.kheap p = some (.schedContext y m)) (hnp : y.scRefills ≠ [])
    (hHR : p ≠ σ.curSc → (refillHd y).rTime.toNat ≤ σ.curTime.toNat) (hX : p ≠ σ.curSc → Excl σ p)
    {r : Unit × State Unit} (hr : r ∈ (switchSchedContext (Z := Unit) σ).1) :
    Rdy r.2 ∧ Sched.OffReady r.2 ∧ r.2.curSc = p := by
  unfold switchSchedContext at hr
  rw [nd_gets_bind, nd_gets_bind, nd_bind_one (Endp.getTcbObjRef_eq _ hct), hsc,
    nd_bind_one (show NonDet.assertOpt (some p) σ = ({(p, σ)}, False) from rfl),
    nd_bind_one (getSchedContext_eq hk)] at hr
  -- the tail: reprogram test, commit, the new current SC
  have tail : ∀ s : State Unit, Rdy s → Sched.OffReady s → Suff s → s.curSc = σ.curSc →
      s.kheap σ.curSc = some (.schedContext x n) → (s.reprogramTimer = false → s.curSc = p) →
      (∀ z k, s.kheap p = some (.schedContext z k) → p ≠ σ.curSc → (refillHd z).rTime.toNat ≤ s.curTime.toNat) →
      ∀ r ∈ ((do
        let reprogram ← NonDet.gets fun s : State Unit => s.reprogramTimer
        NonDet.when reprogram commitTime
        NonDet.modify fun s : State Unit => { s with curSc := p }) s).1,
      Rdy r.2 ∧ Sched.OffReady r.2 ∧ r.2.curSc = p := by
    intro s hR hO' hS' hcs hks hrp hpz r hr
    rw [nd_gets_bind] at hr
    simp only [NonDet.when] at hr
    split_ifs at hr with hrt
    · obtain ⟨c, hc, hr⟩ := hr
      have hks' : s.kheap s.curSc = some (.schedContext x n) := by rw [hcs]; exact hks
      obtain ⟨hR2, hO2, y2, e, -, -, -, -, -, -, -, -⟩ := rdy_commitTime hR hks' hO' hS' hne hc
      obtain rfl : r = ((), _) := hr
      refine ⟨rdy_congr hR2 rfl rfl rfl rfl, fun z k hz => ?_, rfl⟩
      have hz0 : c.2.kheap p = some (.schedContext z k) := hz
      show (refillHd z).rTime.toNat + c.2.consumedTime.toNat ≤ c.2.curTime.toNat
      by_cases epc : p = s.curSc
      · have ec : c.2.curSc = p := by rw [e]; exact epc.symm
        exact hO2 z k (ec ▸ hz0)
      · rw [e] at hz0 ⊢
        have hz' : s.kheap p = some (.schedContext z k) := by simpa [Notif.updK, epc] using hz0
        show (refillHd z).rTime.toNat + (0 : Ticks).toNat ≤ s.curTime.toNat
        simpa using hpz z k hz' (by rw [← hcs]; exact epc)
    · rw [nd_bind_one (show NonDet.pure (σ := State Unit) () s = ({((), s)}, False) from rfl)] at hr
      obtain rfl : r = ((), _) := hr
      have e := hrp (by simpa using hrt)
      refine ⟨rdy_congr hR rfl rfl rfl rfl, fun z k hz => ?_, rfl⟩
      exact hO' z k (by rw [e]; exact hz)
  by_cases hpc : p = σ.curSc
  · rw [NonDet.when, if_neg (not_not.2 hpc),
      nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl)] at hr
    exact tail σ h hO hS rfl hk (fun _ => hpc.symm) (fun _ _ _ e => absurd hpc e) r hr
  · rw [NonDet.when, if_pos hpc, nd_bind_assoc', SInvV.sv_bind_modify] at hr
    obtain ⟨c, hc, hr⟩ := hr
    have hpS : σ.kheap p ≠ none := by rw [hp]; simp
    have hpk : ({ σ with reprogramTimer := true } : State Unit).kheap p = some (.schedContext y m) := hp
    have hcne : σ.curSc ≠ p := fun e => hpc e.symm
    rcases icb_out hpk hnp hc with e | ⟨z, e, hz1, hz2, hz3, hz4, hz5, hz6⟩
    · rw [e] at hr
      refine tail { σ with reprogramTimer := true } (rdy_congr h rfl rfl rfl rfl) hO hS rfl hk (fun e => by cases e) (fun z k hz _ => ?_) r hr
      have hz' : σ.kheap p = some (.schedContext z k) := hz
      rw [hp] at hz'; cases hz'; exact hHR hpc
    · rw [e] at hr
      have hkq : ∀ q, q ≠ p → (updSc { σ with reprogramTimer := true } p z m).kheap q = σ.kheap q :=
        fun q hq => by simp [Notif.updK, hq]
      refine tail (updSc { σ with reprogramTimer := true } p z m) ?_ ?_ ?_ rfl ((hkq _ hcne).trans hk) (fun e => by cases e) (fun z' k hz _ => ?_) r hr
      · refine rdy_framex h hkq rfl rfl rfl (hX hpc) (fun x0 hx0 => by rw [hp] at hx0; cases hx0)
          (fun x0 hx0 => by
            have hx1 : (updSc { σ with reprogramTimer := true } p z m).kheap p = some (.tcb x0) := hx0
            rw [kh_upd] at hx1; cases hx1) (fun z' k hz hz' => ?_)
        have hz0 : (updSc { σ with reprogramTimer := true } p z m).kheap p = some (.schedContext z' k) := hz
        rw [kh_upd] at hz0; cases hz0
        have ha : scActive y = true := by simpa only [scActive, hz4] using hz'
        rw [hz4]; exact h.2.2.2 p y m hp ha
      · intro z' k hz
        have hz' : σ.kheap σ.curSc = some (.schedContext z' k) := (hkq _ hcne).symm.trans hz
        exact hO z' k hz'
      · intro z' k hz hz' hz''
        have hz3 : σ.kheap σ.curSc = some (.schedContext z' k) := (hkq _ hcne).symm.trans hz
        exact hS z' k hz3 hz' hz''
      · have hz0 : (updSc { σ with reprogramTimer := true } p z m).kheap p = some (.schedContext z' k) := hz
        rw [kh_upd] at hz0; cases hz0
        show (refillHd z).rTime.toNat ≤ σ.curTime.toNat
        rw [hz2]

end

end

end Fl4Proofs.P3.SInvR

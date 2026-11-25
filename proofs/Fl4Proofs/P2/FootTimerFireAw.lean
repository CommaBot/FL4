/-
# P2 (p2lf): the waking fire case up to `awaken`

* `same_plan_all`, `plan_ep`: the plan's endpoint and reply are the due thread's `BLOCK_OBJ` / `REPLY` words at the
  entry state when the plan names an endpoint (`plan_objects`, localtimer.rs:333-367).
* `ks_ne_tcb`, `ntfn_wait_head`, `WkCase.tr` (`WkCase` across a run keeping the words it reads), `rel_head_run`,
  `rel_agree1` (`rel_agree` keeping only the SCs of no runnable thread).
* `AwFacts`: what the waking case knows at the state `Y` after `awaken`, relative to the entry state `s`.
* `fire_wk_aw`: `fire_tail_nw`'s prefix (copied), then the waking case at `s1` (`fireTail_wake`, `wake_ok_true`,
  `plan_ep` for the endpoint / reply under `Lk`), `fire_wk_step`, `RelNone` at `Y` (`rel_agree1`: the release head
  is runnable, the woken thread blocked, so their SCs differ) and `awaken` on both stores; the tail after `awaken`
  (`AwTailG`) is asked for every `Y` with `AwFacts` (`hTail`). Premise `hBA` (`BufAt` at the state after
  `handle_interrupt`) is still the caller's.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireWe
import Fl4Proofs.P2.FootTimerFireRs
import Fl4Proofs.P2.FootTimerFireWc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt bind_guard_congr)

theorem same_plan_all {x y : localtimer.TimerIrqPlan} (h : localtimer.same_plan x y = ok true) :
    x.tm = y.tm ∧ x.ntfn = y.ntfn ∧ x.waiter = y.waiter ∧ x.ep = y.ep ∧ x.reply = y.reply := by
  unfold localtimer.same_plan at h
  split_ifs at h with h1 h2 h3 h4 h5
  · exact ⟨h1, h2, h3, h4, h5⟩
  all_goals exact absurd (ok_inj_ff h) Bool.false_ne_true

section plan
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **The plan's endpoint and reply** (module docstring). -/
theorem plan_ep {s : S} {tip : localtimer.TimerIrqPlan} (h : localtimer.plan_objects st s = ok tip)
    (he : tip.ep ≠ 0#u64) : tip.ep = L.mem s (blockA tip.tm) ∧ tip.reply = L.mem s (replyA tip.tm) := by
  unfold localtimer.plan_objects at h
  obtain ⟨cpu, ecpu, h⟩ := bind_eq_ok h
  rw [L.cur_cpu_eq] at ecpu
  obtain rfl := ok_inj_ff ecpu
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  rw [node_get_ok] at ei
  obtain rfl := ok_inj_ff ei
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  rw [is_null_ok] at eb
  obtain rfl := ok_inj_ff eb
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64
  · rw [if_pos (decide_eq_true h0)] at h
    obtain rfl := ok_inj_ff h
    exact absurd rfl he
  rw [if_neg (by simpa using h0)] at h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  by_cases ha : (i1 != L.cpu s) = true
  · rw [if_pos ha] at h
    obtain rfl := ok_inj_ff h
    exact absurd rfl he
  rw [if_neg ha] at h
  have e1 : i1 = L.cpu s := by by_contra hne; exact ha (bne_iff_ne.mpr hne)
  subst e1
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  by_cases hb : (i2 != L.cpu s) = true
  · rw [if_pos hb] at h
    obtain rfl := ok_inj_ff h
    exact absurd rfl he
  rw [if_neg hb] at h
  have e2 : i2 = L.cpu s := by by_contra hne; exact hb (bne_iff_ne.mpr hne)
  subst e2
  have hh : TmHere st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) := And.intro ei1 ei2
  obtain ⟨n, en, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en
  obtain rfl := ok_inj_ff en
  by_cases hn : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = 0#u64
  · rw [if_pos hn] at h
    obtain rfl := ok_inj_ff h
    exact absurd rfl he
  rw [if_neg hn] at h
  obtain ⟨⟨x0, bk⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  by_cases h3 : (i3 != obj.NTFN_IDLE) = true
  · rw [if_pos h3] at h
    obtain rfl := ok_inj_ff h
    exact absurd rfl he
  rw [if_neg h3] at h
  obtain ⟨i4, -, h⟩ := bind_eq_ok h
  by_cases h4 : (i4 != L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) = true
  · rw [if_pos h4] at h
    obtain rfl := ok_inj_ff h
    exact absurd rfl he
  rw [if_neg h4] at h
  obtain ⟨i5, -, h⟩ := bind_eq_ok h
  by_cases h5 : (i5 != sched.TS_BLOCKED_ON_RECV) = true
  · rw [if_pos h5] at h
    obtain rfl := ok_inj_ff h
    exact absurd rfl he
  rw [if_neg h5] at h
  obtain ⟨ep, eep, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Tcb.block_obj.spec (L := L) s _)] at eep
  have eep' := ok_inj_ff eep
  by_cases h6 : ep = 0#u64
  · rw [if_pos h6] at h
    obtain rfl := ok_inj_ff h
    exact absurd rfl he
  rw [if_neg h6] at h
  obtain ⟨⟨y0, bk1⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨r, er, h⟩ := bind_eq_ok h
  rw [eq_of_spec_fd (obj.Tcb.reply_obj.spec (L := L) s _)] at er
  have er' := ok_inj_ff er
  by_cases h7 : (r != 0#u64) = true
  · rw [if_pos h7] at h
    obtain ⟨a3, -, h⟩ := bind_eq_ok h
    obtain rfl := ok_inj_ff h
    exact ⟨eep'.symm, er'.symm⟩
  rw [if_neg h7] at h
  obtain rfl := ok_inj_ff h
  have h7' : r = 0#u64 := UScalar.eq_of_val_eq (by simpa using h7)
  exact ⟨eep'.symm, by rw [er', h7']⟩

end plan

section help
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

theorem ks_ne_tcb {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {Rq : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q Rq) {o y K : U64} (ho : o.val < 13568) (hy : y ∈ T)
    (hK : K.val < 4096) : core.num.U64.wrapping_add (L.ksb s) o ≠ core.num.U64.wrapping_add y K := by
  intro e
  have e' := congrArg UScalar.val e
  rw [ks_val h ho, field_val (h.tcbs y hy) hK] at e'
  have := h.ksOut y hy
  simp only [Nat.reducePow] at this
  omega

/-- A notification's head / state words lie outside the objects, and a waiting one's head is a thread. -/
theorem ntfn_wait_head {X : S} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {N : U64}
    (h0 : SchedQueuesInv st T Cs Ω H X Q Rq) (hHN : H N = some .ntfn) :
    OutsideObjs st T Cs X (epHeadA N) ∧ OutsideObjs st T Cs X (epTSA N) ∧
    (L.epState X N = obj.NTFN_WAITING → (L.epQ X N).head ∈ T) := by
  obtain ⟨E, EQ, hEW⟩ := h0.eps
  have he : N ∈ E := (hEW.2.2.2.2.2.2.2.1 N).2 (Or.inr hHN)
  obtain ⟨hE, hEN, hqr⟩ := hEW.1 N he
  obtain ⟨oH, oS⟩ := ep_out hE hEN
  refine ⟨oH, oS, fun hw => ?_⟩
  have hwt1 : L.epState X N = 1#u64 := by rw [hw]; simp [obj.NTFN_WAITING]
  obtain ⟨-, -, -, -, -, k5⟩ := hEW.2.2.2.2.2
  have hne : EQ N ≠ [] := fun h => (k5 N he h).2 hHN hwt1
  obtain ⟨y0, ys, hys⟩ := List.exists_cons_of_ne_nil hne
  have e : (L.epQ X N).head = y0 := by rw [hqr.head, hys]; rfl
  rw [e]; exact hqr.mem y0 (by rw [hys]; exact List.mem_cons_self)

/-- **`WkCase` across a run** keeping the notification's words, the threads' words below the timer fields, the
current domain and the current thread. -/
theorem WkCase.tr {R W Lk : U64 → Prop} {cpu : U64} {X X' : S} {N t : U64}
    (oH : OutsideObjs st T Cs X (epHeadA N)) (oS : OutsideObjs st T Cs X (epTSA N))
    (oB : OutsideObjs st T Cs X (ntfnBtA N)) (oC : OutsideObjs st T Cs X (ntfnScA N))
    (hwT : L.epState X N = obj.NTFN_WAITING → (L.epQ X N).head ∈ T)
    (kO : ∀ b, OutsideObjs st T Cs X b → L.mem X' b = L.mem X b)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 3528 → K.val % 8 = 0 →
      L.mem X' (core.num.U64.wrapping_add y K) = L.mem X (core.num.U64.wrapping_add y K))
    (kD : L.mem X' (core.num.U64.wrapping_add (L.ksb X') layout.ks.CUR_DOMAIN) =
      L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN))
    (kC : L.curW X' = L.curW X) (htT : t ≠ 0#u64 → t ∈ T)
    (h : WkCase st R W Lk cpu X N t) : WkCase st R W Lk cpu X' N t := by
  have eS : L.epState X' N = L.epState X N := by unfold LawfulStore.epState; rw [kO _ oS]
  have eQ : L.epQ X' N = L.epQ X N := by unfold LawfulStore.epQ; rw [kO _ oH, kO _ oS]
  have eB := kO _ oB
  have eNs := kO _ oC
  have kA : ∀ y ∈ T, L.mem X' (affA y) = L.mem X (affA y) := fun y hy => kT y hy 3520#u64 (by simp) (by simp)
  have kDm : ∀ y ∈ T, L.mem X' (domA y) = L.mem X (domA y) := fun y hy => kT y hy 3432#u64 (by simp) (by simp)
  have kSc : ∀ y ∈ T, L.mem X' (scA y) = L.mem X (scA y) := fun y hy => kT y hy 3464#u64 (by simp) (by simp)
  have kSt : ∀ y ∈ T, L.mem X' (stA y) = L.mem X (stA y) := fun y hy => by
    rw [stA_eq]; exact kT y hy 3328#u64 (by simp) (by simp)
  have kBl : ∀ y ∈ T, L.mem X' (blockA y) = L.mem X (blockA y) := fun y hy => kT y hy 3336#u64 (by simp) (by simp)
  have kRp : ∀ y ∈ T, L.mem X' (replyA y) = L.mem X (replyA y) := fun y hy => kT y hy 3360#u64 (by simp) (by simp)
  have kYl : ∀ y ∈ T, L.mem X' (yieldA y) = L.mem X (yieldA y) := fun y hy => kT y hy 3472#u64 (by simp) (by simp)
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · have hy := hwT h1
    left
    rw [eS, eQ, kC, kD, kA _ hy, kDm _ hy, kSc _ hy, eNs, kYl _ hy]
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · have ht := htT h3
    right
    rw [eS, eB, kC, kD, kA _ ht, kDm _ ht, kSc _ ht, eNs, kSt _ ht, kBl _ ht, kRp _ ht, kYl _ ht]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- The release head is runnable. -/
theorem rel_head_run {X : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X)
    (h00 : L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) ≠ 0#u64) :
    Runnable (L.mem X (stA (L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD)))) := by
  obtain ⟨⟨Q, R, hq⟩, -, -, -, -⟩ := hI
  have hcC := hq.cur
  generalize hh : L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = h0 at h00 ⊢
  have hrel := hq.release _ hcC
  have hmem : h0 ∈ R (L.cpu X) := by
    have e := hrel.head
    change L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = _ at e
    rw [hh] at e
    cases hR : R (L.cpu X) with
    | nil => rw [hR] at e; exact absurd e h00
    | cons x xs => rw [hR] at e; simp only [List.headD_cons] at e; subst e; simp
  exact hq.runR _ hcC h0 hmem

/-- `rel_agree` keeping only the SCs other than `cx`, no runnable thread's SC. -/
theorem rel_agree1 {cx : U64} {X Y : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hk : L.ksb Y = L.ksb X)
    (hc : L.cpu Y = L.cpu X)
    (eh : L.mem Y (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD))
    (ect : L.curTime Y = L.curTime X) (esc : ∀ y ∈ T, L.mem Y (scA y) = L.mem X (scA y))
    (keep : ∀ c ∈ Scs, c ≠ cx → ∀ b, Aligned b → InSC c (Z c) b → L.mem Y b = L.mem X b)
    (hcx : ∀ y ∈ T, Runnable (L.mem X (stA y)) → L.mem X (scA y) ≠ 0#u64 → L.mem X (scA y) ≠ cx)
    (h : RelNone st X) : RelNone st Y := by
  obtain ⟨⟨Q, R, hq⟩, hB, hX, -, hS⟩ := hI
  have hcC := hq.cur
  have eA : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt X (L.cpu X) o := fun o => by rw [hc, nodeAt_of_ksb hk]
  unfold RelNone at h ⊢
  rw [ect, eA, eh]
  generalize hh : L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = h0 at h ⊢
  rcases h with h | h
  · exact Or.inl h
  by_cases h00 : h0 = 0#u64
  · exact Or.inl h00
  right
  have hrel := hq.release _ hcC
  have hmem : h0 ∈ R (L.cpu X) := by
    have e := hrel.head
    change L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = _ at e
    rw [hh] at e
    cases hR : R (L.cpu X) with
    | nil => rw [hR] at e; exact absurd e h00
    | cons x xs => rw [hR] at e; simp only [List.headD_cons] at e; subst e; simp
  have hhT : h0 ∈ T := hq.memTR hcC hmem
  rw [esc h0 hhT]
  have haff : L.mem X (affA h0) = L.cpu X := hq.inR _ hcC h0 hmem
  have hrb : (L.mem X (inqA h0) &&& sched.Q_RELEASE) ≠ 0#u64 := (hq.released h0 hhT).2 (by rw [haff]; exact hmem)
  have hsc0 : L.mem X (scA h0) ≠ 0#u64 := hB.r h0 hhT hrb
  have hscS : L.mem X (scA h0) ∈ Scs := (hX.2.2.bound h0 hhT hsc0).1
  have hAc : L.mem X (scA h0) ∈ Ac := hB.sact h0 hhT (Or.inr (Or.inl hrb)) hsc0
  have hncx := hcx h0 hhT (hq.runR _ hcC h0 hmem) hsc0
  generalize hsc : L.mem X (scA h0) = sc at h hscS hAc hncx ⊢
  have hmax : L.rmax X sc ≠ 0#u64 := (hS.act sc hscS).1 hAc
  obtain ⟨hwf, -, -⟩ := hS.all sc hscS
  have wf := hwf hmax
  obtain ⟨h8, hm, hfit⟩ := wf.bounds
  obtain ⟨-, -, -, hhd, -, hri⟩ := wf.inside
  have kp := keep sc hscS hncx
  have e1 : L.rhead Y sc = L.rhead X sc := kp _ (by unfold Aligned; rw [hhd]; omega) ⟨by rw [hhd]; omega, by rw [hhd]; omega⟩
  obtain ⟨r1, r2, r3⟩ := hri (L.rhead X sc) wf.head_lt
  have e2 : L.mem Y (rtA sc (L.rhead X sc)) = L.mem X (rtA sc (L.rhead X sc)) :=
    kp _ (by unfold Aligned; rw [r1]; omega) ⟨by rw [r1]; omega, by rw [r1]; omega⟩
  simp only [LawfulStore.refill] at h ⊢
  rw [e1, e2]
  exact h


/-- **What the waking fire case knows after `awaken`** (module docstring), relative to the entry state `s`. -/
def AwFacts (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (R : U64 → Prop) (s Y : S) (now w : U64) : Prop :=
  TInv st T Cs Ω H Sg Rp Scs Nt Z Ac Y ∧ L.ksb Y = L.ksb s ∧ L.cpu Y = L.cpu s ∧
  (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 40 → o.val ≠ 48 → o.val ≠ 56 →
    o.val ≠ 80 → o.val ≠ 104 → o.val ≠ 112 →
    L.mem Y (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o)) ∧
  (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) → K.val ≠ 3496 →
    K.val ≠ 3504 → (y = w → K.val ≠ 3328 ∧ K.val ≠ 256 ∧ K.val ≠ 3376) →
    L.mem Y (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
  (∀ c ∈ Scs, c ≠ L.mem s (scA w) → ∀ b, Aligned b → InSC c (Z c) b → L.mem Y b = L.mem s b) ∧
  RelNone st Y ∧ FireStop st R Y now ∧ L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.CUR_TIME) = now ∧
  w ∈ T ∧ Blocked (L.mem s (stA w)) ∧ L.mem s (affA w) = L.cpu s ∧ w ≠ L.curW s ∧
  (L.actionW Y = sched.ACTION_RESUME_CURRENT ∨ L.actionW Y = w) ∧ L.mem Y (stA w) = sched.TS_RUNNING ∧
  L.mem s (yieldA w) = 0#u64

end help

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 64000000 in
/-- **The waking fire case up to `awaken`** (module docstring). -/
theorem fire_wk_aw {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s1 s2 s3 : S} {a a1 a2 a3 : A} {mx irq now i2 : U64} {x : Bool}
    {tip p : localtimer.TimerIrqPlan}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hok : IrqOk st s)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hwH : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y →
      (L.mem X (tdA y) ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val ∧ v.val >>> 8 = (L.cpu s).val) →
      gS.write X (thA y) v = st.write X (thA y) v)
    (hwD : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y → L.mem X (affA y) = L.cpu s →
      L.mem s (affA y) = L.cpu s →
      (L.mem X (tdA y) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val) →
      gS.write X (tdA y) v = st.write X (tdA y) v)
    (hWk : ¬ NoWake st s) {Lk : U64 → Prop} {U : Set U64}
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (rL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StW st gS T Lk s)
    (hLkN : Lk p.ntfn) (hLkE : p.ep ≠ 0#u64 → Lk p.ep)
    (wNt : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → k.val ≠ 24 → W (core.num.U64.wrapping_add p.ntfn k))
    (rwE : p.ep ≠ 0#u64 → ∀ k : U64, k.val < 16 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add p.ep k) ∧ W (core.num.U64.wrapping_add p.ep k))
    (wRt : p.reply ≠ 0#u64 → W (rTcbA p.reply))
    (etip : localtimer.plan_objects st s = ok tip) (eb : localtimer.same_plan tip p = ok true)
    (eq : localtimer.sched_quiet st s (L.cpu s) = ok true)
    (eok : localtimer.current_ok st s (L.cpu s) (L.curW s) (L.cscW s) = ok true)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (enow : sched.cur_time st s1 = ok now)
    (erel : localtimer.release_due st s1 (L.cpu s) = ok false) (ei2 : sched.consumed st s1 = ok i2)
    (eb4 : sporadic.sufficient st ar s1 a1 (L.cscW s) i2 = ok true)
    (edue : localtimer.timer_due st s1 (L.cpu s) now = ok true)
    (efo : localtimer.fire_ok st s1 (L.cpu s) (L.curW s) p now = ok true)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2))
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (ehi : interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3))
    (hBA : BufAt st T Cs H Sg Scs Z U s3)
    (hTail : ∀ Y aY w, sched.awaken st ar s3 a3 = ok (Y, aY) →
      AwFacts st T Cs Ω H Sg Rp Scs Nt Z Ac R s Y now w → AwTailG st gS ar Y aY) :
    FireTailG st gS ar s3 a3 := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hNa : ∀ c ∈ Cs, NodePlaced st T s c := h0.nodes
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  obtain ⟨haff, hsct, hcore⟩ := hok
  obtain ⟨hmr, -, -⟩ := current_ok_true eok
  obtain ⟨-, -, hnvm, -⟩ := may_run_here_true hmr
  have hy0 : L.mem s (yieldA (L.curW s)) = 0#u64 := mrh_yield hmr
  have hX := hI.2.2.1
  have hS := hI.2.2.2.2
  have hSg := hI.2.2.2.1
  have hO := hX.1
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eq
  have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
  have hAc : L.cscW s ∈ Ac := by
    rw [← hsct]
    exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
  -- `s → s1`: the timestamp update
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  have k1 : L.ksb s1 = L.ksb s := by rw [er, utW_ksb]
  have c1 : L.cpu s1 = L.cpu s := by rw [er, utW_cpu]
  have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
    fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [er]; exact utW_placed hN n1
  have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c1, nodeAt_of_ksb k1]
  have hnode1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      L.mem s1 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48
    refine m1 _ (nodeAt_aligned hN ho h8) (fun e => ?_) (fun e => ?_)
    · have e' := congrArg UScalar.val e
      unfold ctA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CUR_TIME])] at e'
      simp [layout.node.CUR_TIME] at e'; omega
    · have e' := congrArg UScalar.val e
      unfold cnA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CONSUMED])] at e'
      simp [layout.node.CONSUMED] at e'; omega
  have hout1 : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b := fun b hb =>
    m1 b hb.1 (fun e => out_ne_node hb hcC hN (by simp [layout.node.CUR_TIME]) (congrArg UScalar.val e).symm)
      (fun e => out_ne_node hb hcC hN (by simp [layout.node.CONSUMED]) (congrArg UScalar.val e).symm)
  have agΩ1 : ∀ b ∈ Ω, L.mem s1 b = L.mem s b := fun b hb => hout1 b (h0.omega b hb)
  have htcb1 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8
    exact m1 _ (field_aligned (hT y hy) hK h8) (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CUR_TIME]))
      (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CONSUMED]))
  have hB1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
    have := sched.update_timestamp.bxc hA s a hI
    rw [eu, WP.spec_ok] at this
    try simp only [WP.uncurry'_pair] at this
    exact this.1.1
  have hnow : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_TIME) = now := by
    rw [cur_time_ok] at enow; exact ok_inj_ff enow
  -- the IRQ's state word after the timestamp update
  have hirq : irq.val ≤ 127 := by
    rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
    have e := ok_inj_ff emx
    subst e
    scalar_tac
  obtain ⟨i, hi, hiv⟩ : ∃ i, interrupt.state_off irq = ok i ∧ i.val = 224 + 8 * irq.val := by
    unfold interrupt.state_off
    simp only [lift, bind_ok]
    rw [eq_of_spec_fd layout.ks.IRQ_STATE.spec]
    simp only [bind_ok]
    refine ⟨_, rfl, ?_⟩
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    try omega
  have hi' : i.val < 13568 := by omega
  have hi8 : i.val % 8 = 0 := by omega
  have eis1 : interrupt.irq_state st s1 irq = ok interrupt.IRQ_TIMER := by
    rw [← ei1]
    unfold interrupt.irq_state
    rw [hi]
    simp only [bind_ok]
    rw [eq_of_spec_fd (obj.ks_get.spec (L := L) s1 i), eq_of_spec_fd (obj.ks_get.spec (L := L) s i), k1,
      m1 _ (ks_aligned hN hi' hi8) (ks_ne_node hN hi' (by simp [layout.node.CUR_TIME]))
        (ks_ne_node hN hi' (by simp [layout.node.CONSUMED]))]
  -- `check_budget`
  have ecs1 : sched.cur_sc st s1 = ok (L.cscW s) := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s1)]
    congr 1
    show L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_SC) = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_SC)
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  rw [check_budget_suf ar ecs1 ei2 eb4] at ecb
  have e2 := ok_inj_ff ecb
  simp only [Prod.mk.injEq] at e2
  obtain ⟨-, e2s, e2a⟩ := e2
  subst e2s e2a
  -- `handle_interrupt`: `s1 → s3`
  obtain ⟨s2', eh2, eh3, -⟩ := handle_interrupt_timer ar emx hle eis1 ehi
  have w13 : WritesIn st s1 s3 (HW st s1) := handle_interrupt_timer_writes hN1 eh2 eh3
  have hT3 : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s3 := by
    rw [eq_of_spec_fd (obj.node_set.spec (L := L) s1 _ _ _)] at eh2
    have e2 := ok_inj_ff eh2
    subst e2
    rw [eq_of_spec_fd (obj.node_set.spec (L := L) _ _ _ _)] at eh3
    rw [← ok_inj_ff eh3]
    have := armed.tinv (v := 0#u64) (reprogram.tinv (v := 1#u64) (BXI.blk hB1))
    rwa [LawfulStore.cpu_wr] at this
  have k3 : L.ksb s3 = L.ksb s := w13.1.trans k1
  have c3 : L.cpu s3 = L.cpu s := w13.2.1.trans c1
  have e3N : ∀ o, L.nodeAt s3 (L.cpu s3) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c3, nodeAt_of_ksb k3]
  have hnode3 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 → o.val ≠ 56 → o.val ≠ 80 →
      L.mem s3 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48 h56 h80
    have := hw_node hN1 w13 ho h8 ⟨h56, h80⟩
    rw [e1N] at this
    rw [this, hnode1 o ho h8 h40 h48]
  have htcb3 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun hy hK h8 => (hw_tcb hT hN1 w13 hy hK h8).trans (htcb1 hy hK h8)
  have hcC1 : L.cpu s1 ∈ Cs := by rw [c1]; exact hcC
  have hout3 : ∀ b, OutsideObjs st T Cs s b → L.mem s3 b = L.mem s b := fun b hb =>
    (hw_outside hN1 hcC1 w13 (hb.ksb k1)).trans (hout1 b hb)
  have hcC3 : L.cpu s3 ∈ Cs := by rw [c3]; exact hcC
  have hN3a : ∀ c ∈ Cs, NodePlaced st T s3 c := fun c hc => (hNa c hc).ksb k3
  have tm3 : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e3N]
    exact hnode3 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have ct3 : L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.CUR_TIME) = now := by
    rw [w13.2.1, nodeAt_of_ksb w13.1,
      hw_node hN1 w13 (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
        (by simp [layout.node.CUR_TIME])]
    exact hnow
  -- the due thread and its notification
  obtain ⟨hpt, hpn⟩ := same_plan_tm eb
  have hp0 : p.tm ≠ 0#u64 := by
    intro e
    have h' := efo
    rw [fire_ok_eq, if_pos e] at h'
    exact Bool.false_ne_true (ok_inj_ff h')
  obtain ⟨TM, eTM⟩ : ∃ x, L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = x := ⟨_, rfl⟩
  obtain ⟨hpTM, hne, hh, hpN⟩ : p.tm = TM ∧ TM ≠ 0#u64 ∧ TmHere st s TM ∧ p.ntfn = L.mem s (boundA TM) := by
    rcases plan_facts' etip with ⟨t1, -⟩ | ⟨t1, t2, t3, t4⟩
    · exact absurd (by rw [← hpt]; exact t1) hp0
    · rw [eTM] at t1
      rw [t1] at t2 t3 t4
      exact ⟨by rw [← hpt, t1], t2, t3, by rw [← hpn, t4]⟩
  rw [eTM] at tm3
  obtain ⟨N, eN⟩ : ∃ x, L.mem s (boundA TM) = x := ⟨_, rfl⟩
  have hTMs : TM ∈ T ∧ FootLtArmed st s (L.cpu s) TM := by
    have := tmin_facts (BXI.blk hI) hcC (by rw [eTM]; exact hne)
    rwa [eTM] at this
  have haffTM : L.mem s (affA TM) = L.cpu s := by
    have e := hh.1; rw [aff_ok] at e; exact ok_inj_ff e
  have nNt : N ≠ 0#u64 → N ∈ Nt := fun h => by
    have := hX.2.2.bnd _ hTMs.1 (by rw [eN]; exact h); rwa [eN] at this
  have oT : N ≠ 0#u64 → OutsideObjs st T Cs s (epTSA N) := fun h => ntfn_ts_out h0 (hNt N (nNt h))
  have oB : N ≠ 0#u64 → OutsideObjs st T Cs s (ntfnBdA N) := fun h => h0.omega _ (hSg.sub _ (hO.ntB N (nNt h)).1)
  have oBt : N ≠ 0#u64 → OutsideObjs st T Cs s (ntfnBtA N) := fun h => h0.omega _ (hSg.sub _ (hO.ntB N (nNt h)).2)
  have eTS : core.num.U64.wrapping_add N layout.ntfn.TAIL_STATE = epTSA N := by
    apply UScalar.eq_of_val_eq
    unfold epTSA
    simp [core.num.U64.wrapping_add_val_eq, layout.ntfn.TAIL_STATE, layout.ep.TAIL_STATE]
  -- the guarded store: what it admits
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩))
  have nW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → W (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gWr _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩)) (fun e => by
      rw [stA_eq] at e; exact node_ne_field hN h1 hcT ht' (by simp) e)
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 h5 h6 =>
    gRd _ (field_aligned ht' h2 h3) (Or.inl (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩)))
  have cW : ∀ K : U64, 256 ≤ K.val → K.val < 3328 → K.val % 8 = 0 → W (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K h1 h2 h3 =>
    gWr _ (field_aligned ht' (by omega) h3) (Or.inl (Or.inr (Or.inl ⟨K, h1, by omega, h3, rfl⟩))) (fun e => by
      rw [stA_eq] at e
      exact tcb_word_ne ht' ht' (by omega) (by simp) (fun _ h => by simp at h; omega) e)
  have rR : ∀ r : U64, r.val < 384 → R (regA (L.curW s) r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cR K (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have rW : ∀ r : U64, r.val < 384 → W (regA (L.curW s) r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cW K (by omega) (by omega) (by omega)
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha =>
    gRd _ ha (Or.inl (Or.inr (Or.inr (Or.inl hb))))
  have scNS : ∀ b, Aligned b → InSC (L.cscW s) (Z (L.cscW s)) b → b ≠ stA (L.curW s) := fun b ha hb e => by
    rw [stA_eq] at e
    exact out_ne_field (h0.omega b (hcq.2.1 b ha hb)) hcT ht' (by simp) (congrArg UScalar.val e).symm
  have hSc : ScAcc R W (L.cscW s) (Z (L.cscW s)) := ⟨fun b ha hb => scR b hb ha, fun b h1 h2 =>
    gWr _ h1 (Or.inl (Or.inr (Or.inr (Or.inl h2)))) (scNS b h1 ⟨by have := h2.1; omega, h2.2⟩),
    gWr _ hcq.2.2.1.2 (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (scNS _ hcq.2.2.1.2 hcq.2.2.1.1)⟩
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rIq : R (inqA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rYt : R (yieldA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  have nrm : ∀ Y : S, (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R W Y := fun Y e => by
    unfold PathObl.NodeSt
    rw [e, e]
    exact ⟨nR _ (by rw [curth_val]; omega) (by rw [curth_val]), nR _ (by rw [act_val]; omega) (by rw [act_val]),
      nW _ (by rw [act_val]; omega) (by rw [act_val])⟩
  have ndR : ∀ (Y : S), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → ∀ o : U64, o.val < 4288 →
      o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) := fun Y e o h1 h2 => by rw [e]; exact nR o h1 h2
  have rT : ∀ y ∈ T, FootLtArmed st s (L.cpu s) y → ∀ K : U64, 3528 ≤ K.val → K.val < 3576 → K.val % 8 = 0 →
      R (core.num.U64.wrapping_add y K) := fun y hy ha K h1 h2 h3 =>
    gRd _ (field_aligned (hT y hy) (by omega) h3) (Or.inr (Or.inl ⟨y, hy, ha, K, h1, h2, h3, rfl⟩))
  have wT : ∀ y ∈ T, FootLtArmed st s (L.cpu s) y → ∀ K : U64, 3536 ≤ K.val → K.val < 3568 → K.val % 8 = 0 →
      W (core.num.U64.wrapping_add y K) := fun y hy ha K h1 h2 h3 =>
    gWr _ (field_aligned (hT y hy) (by omega) h3) (Or.inr (Or.inl ⟨y, hy, ha, K, h1, h2, h3, rfl⟩)) (fun e => by
      rw [stA_eq] at e
      exact field_ne (hT y hy) ht' (by omega) (by simp) (fun _ => by simp; omega) e)
  have rN : N ≠ 0#u64 → ∀ K : U64, K.val < 64 → K.val % 8 = 0 → R (core.num.U64.wrapping_add N K) := fun h K h1 h2 => by
    obtain ⟨p1, p2⟩ := hO.ntP _ (nNt h)
    exact gRd _ (by unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega)
      (Or.inr (Or.inr ⟨by rw [eTM]; exact hne, by rw [eTM, eN]; exact h, K, h1, h2, by rw [eTM, eN]⟩))
  have wN : N ≠ 0#u64 → ∀ K : U64, K.val < 64 → K.val % 8 = 0 → K.val ≠ 24 →
      core.num.U64.wrapping_add N K ≠ stA (L.curW s) → W (core.num.U64.wrapping_add N K) := fun h K h1 h2 h24 hn => by
    obtain ⟨p1, p2⟩ := hO.ntP _ (nNt h)
    exact gWr _ (by unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega)
      (Or.inr (Or.inr ⟨by rw [eTM]; exact hne, by rw [eTM, eN]; exact h, K, h1, h2, h24, by rw [eTM, eN]⟩)) hn
  have nsO : ∀ b, OutsideObjs st T Cs s b → b ≠ stA (L.curW s) := fun b hb e => by
    rw [stA_eq] at e
    exact out_ne_field hb hcT ht' (by simp) (congrArg UScalar.val e).symm
  -- `remove` of the due thread at `s3`
  obtain ⟨Wk, ctk⟩ := (TInv.rb hT3).tree _ hcC3
  have armS : ∀ z ∈ Wk.keys, FootLtArmed st s (L.cpu s) z := fun z hz => by
    have zT := ctk.inT z hz
    refine ⟨?_, ?_⟩
    · have e : L.mem s3 (tdA z) = L.mem s (tdA z) := htcb3 zT (K := 3528#u64) (by simp) (by simp)
      rw [← e]; exact ctk.armed z hz
    · have e : L.mem s3 (thA z) = L.mem s (thA z) := htcb3 zT (K := 3568#u64) (by simp) (by simp)
      rw [← e, ← c3]; exact ctk.core z hz
  have C : TC st gS T s (L.cpu s) (fun z => z ∈ Wk.keys) R W :=
    { tcbs := hT, inT := ctk.inT, node := hN
      rd := fun w hw => by
        rcases hw with ⟨z, hz, k, h1, h2, h3, rfl⟩ | ⟨o, ho, h8, rfl⟩
        · exact rT z (ctk.inT z hz) (armS z hz) k h1 h2 h3
        · exact nR o ho h8
      wr := fun w hw => by
        rcases hw with ⟨z, hz, k, h1, h2, h3, rfl⟩ | ⟨o, ho, h8, rfl⟩
        · exact wT z (ctk.inT z hz) (armS z hz) k h1 h2 h3
        · exact nW o ho h8
      wh := fun X y v hy hc => hwH X y v (ctk.inT y hy) (armS y hy) hc
      wd := fun X y v hy ha1 ha0 hc => hwD X y v (ctk.inT y hy) (armS y hy) ha1 ha0 hc }
  have I3 : TI st s (L.cpu s) (fun z => z ∈ Wk.keys) (fun z => z ∈ Wk.keys) s3 :=
    { ksb := k3, cpu := c3, sub := fun _ hz => hz
      root := by
        have := ctk.rep.root_mem
        rw [c3, nodeAt_of_ksb k3] at this; exact this
      lnk := fun z hz => ctk.rep.links z hz
      hj := fun z hz _ => by rw [← c3]; exact ctk.core z hz
      af := fun z hz => htcb3 (ctk.inT z hz) (K := 3520#u64) (by simp) (by simp) }
  have hkt : TM ∈ Wk.keys := by
    have e := ctk.min
    rw [tm3] at e
    rw [e]
    exact Wk.minKey_mem.resolve_left (by rw [← e]; exact hne)
  have hrmg : timer.remove gS s3 TM = timer.remove st s3 TM :=
    (ge_remove C I3 hkt haffTM (fun i _ _ => by
      have e := timer.core_of.rb s3 TM ctk hkt
      rw [← c3]; exact eq_of_spec_fd e)).1
  -- the waking case, at `s1`
  unfold NoWake at hWk
  rw [eTM, eN] at hWk
  have hN0 : N ≠ 0#u64 := fun h => hWk (Or.inl h)
  have hNN : N ∈ Nt := nNt hN0
  have pn0 : p.ntfn ≠ 0#u64 := by rw [hpN, eN]; exact hN0
  have hbT : L.mem s (ntfnBtA N) = 0#u64 ∨ L.mem s (ntfnBtA N) ∈ T := by
    have := TInv.ntb hT3 N hNN; rwa [hout3 _ (oBt hN0)] at this
  obtain ⟨oHs, oSs, hwTs⟩ := ntfn_wait_head h0 (hNt N hNN)
  have oCs : OutsideObjs st T Cs s (ntfnScA N) := h0.omega _ (hSg.sub _ (hO.ntW N hNN))
  have eS1 : L.epState s1 p.ntfn = L.epState s N := by
    rw [hpN, eN]; unfold LawfulStore.epState; rw [hout1 _ (oT hN0)]
  have eB1 : L.mem s1 (ntfnBtA p.ntfn) = L.mem s (ntfnBtA N) := by rw [hpN, eN]; exact hout1 _ (oBt hN0)
  have hw1 : L.epState s1 p.ntfn = obj.NTFN_WAITING ∨ (L.epState s1 p.ntfn = obj.NTFN_IDLE ∧
      L.mem s1 (ntfnBtA p.ntfn) ≠ 0#u64 ∧
      L.mem s1 (stA (L.mem s1 (ntfnBtA p.ntfn))) = sched.TS_BLOCKED_ON_RECV) := by
    rw [eS1, eB1]
    by_cases hwt : L.epState s N = obj.NTFN_WAITING
    · exact Or.inl hwt
    · have hi : L.epState s N = obj.NTFN_IDLE := by
        by_contra hi; exact hWk (Or.inr (Or.inl ⟨hi, hwt⟩))
      have hb0 : L.mem s (ntfnBtA N) ≠ 0#u64 := fun hb => hWk (Or.inr (Or.inr ⟨hi, Or.inl hb⟩))
      have hrv : L.mem s (stA (L.mem s (ntfnBtA N))) = sched.TS_BLOCKED_ON_RECV := by
        by_contra hr; exact hWk (Or.inr (Or.inr ⟨hi, Or.inr hr⟩))
      refine Or.inr ⟨hi, hb0, ?_⟩
      rw [stA_eq, htcb1 (hbT.resolve_left hb0) (K := 3328#u64) (by simp) (by simp), ← stA_eq]
      exact hrv
  have hcur1 : L.curW s1 = L.curW s := by
    unfold LawfulStore.curW
    rw [e1N]
    exact hnode1 _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega)
  obtain ⟨tp1, -, -, tp4, tp5⟩ := same_plan_all eb
  have wk1 : WkCase st R W Lk (L.cpu s) s1 N TM := by
    rcases fireTail_wake (fire_ok_tail efo) pn0 hw1 with ⟨hwt, wok⟩ | ⟨hi, hbt, hrv, -, hep, wok⟩
    · obtain ⟨wne, mrh, dom, -, scn, -⟩ := wake_ok_true wok
      obtain ⟨-, aff, -, -⟩ := may_run_here_true mrh
      have yl := mrh_yield mrh
      rw [hpN, eN] at hwt wne aff dom scn yl
      exact Or.inl ⟨hwt, by rw [hcur1]; exact wne, aff, dom, scn, yl⟩
    · rw [hpTM] at hbt hrv wok
      obtain ⟨wne, mrh, dom, -, scn, -⟩ := wake_ok_true wok
      obtain ⟨-, aff, -, -⟩ := may_run_here_true mrh
      rw [hpN, eN] at hi hbt scn
      obtain ⟨pe1, pe2⟩ := plan_ep etip (by rw [tp4]; exact hep)
      have htm : tip.tm = TM := by rw [tp1, hpTM]
      rw [htm] at pe1 pe2
      have eBl : L.mem s1 (blockA TM) = p.ep := by
        rw [← tp4, pe1, blockA_eq, htcb1 hTMs.1 (K := 3336#u64) (by simp) (by simp)]
      have eRp : L.mem s1 (replyA TM) = p.reply := by
        rw [← tp5, pe2]; unfold replyA; exact htcb1 hTMs.1 (K := 3360#u64) (by simp) (by simp)
      refine Or.inr ⟨hi, hbt, hne, hrv, by rw [hcur1]; exact wne, aff, dom, scn, by rw [eBl]; exact hLkE hep,
        fun k hk h8 => by rw [eBl]; exact rwE hep k hk h8, fun h => by rw [eRp] at h ⊢; exact wRt h,
        mrh_yield mrh⟩
  -- `WkCase` at every state `remove` may reach
  obtain ⟨Q3, R3, hq3⟩ := hT3.1
  have hCD : layout.ks.CUR_DOMAIN.val < 13568 := by simp [layout.ks.CUR_DOMAIN]
  have aCD : Aligned (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) :=
    ks_aligned hN hCD (by simp [layout.ks.CUR_DOMAIN])
  have cD1 : L.mem s1 (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) =
      L.mem s (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) :=
    m1 _ aCD (ks_ne_node hN hCD (by simp [layout.node.CUR_TIME])) (ks_ne_node hN hCD (by simp [layout.node.CONSUMED]))
  have cD3 : L.mem s3 (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) =
      L.mem s1 (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) := by
    refine w13.mem_eq aCD ?_
    rintro ⟨o', -, ho', -, e⟩
    rw [e1N] at e
    exact ks_ne_node hN hCD ho' e
  have hcur3 : L.curW s3 = L.curW s := by
    unfold LawfulStore.curW
    rw [e3N]
    exact hnode3 _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega)
  have hwk : ∀ X1, WritesIn st s3 X1 (Fl4Proofs.P1.TW st T Cs s3) → WkCase st R W Lk (L.cpu s) X1 N TM := by
    intro X1 w
    have kX1 : L.ksb X1 = L.ksb s := w.1.trans k3
    have kO : ∀ b, OutsideObjs st T Cs s b → L.mem X1 b = L.mem s b := fun b hb =>
      (w.mem_eq hb.1 (out_not_tw hT hN3a (hb.ksb k3))).trans (hout3 b hb)
    have kT : ∀ y ∈ T, ∀ K : U64, K.val < 3528 → K.val % 8 = 0 →
        L.mem X1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
      intro y hy K hK h8
      refine (w.mem_eq (field_aligned (hT y hy) (by omega) h8) ?_).trans (htcb3 hy (by omega) h8)
      rintro (⟨y', hy', K', h1, h2, e⟩ | ⟨c, hc, o, ho, e⟩)
      · exact field_ne (hT y hy) (hT y' hy') (by omega) (by omega) (fun _ => by omega) e
      · exact tcb_node_ne (hN3a c hc) hy (hT y hy) (by omega) (by rcases ho with h | h <;> omega) e
    refine WkCase.tr (oHs.ksb k1) (oSs.ksb k1) ((oBt hN0).ksb k1) (oCs.ksb k1) ?_
      (fun b hb => (kO b (hb.ksb k1.symm)).trans (hout1 b (hb.ksb k1.symm)).symm)
      (fun y hy K hK h8 => (kT y hy K hK h8).trans (htcb1 hy (by omega) h8).symm) ?_ ?_
      (fun _ => hTMs.1) wk1
    · intro hw
      have eS : L.epState s1 N = L.epState s N := by unfold LawfulStore.epState; rw [hout1 _ oSs]
      have eQ : L.epQ s1 N = L.epQ s N := by unfold LawfulStore.epQ; rw [hout1 _ oHs, hout1 _ oSs]
      rw [eQ]; rw [eS] at hw; exact hwTs hw
    · rw [kX1, k1, cD1]
      refine (w.mem_eq aCD ?_).trans (cD3.trans cD1)
      rintro (⟨y', hy', K', h1, h2, e⟩ | ⟨c, hc, o, ho, e⟩)
      · have := ks_ne_tcb hq3 hCD hy' (K := K') (by omega)
        rw [k3] at this; exact this e
      · rw [nodeAt_of_ksb k3] at e
        exact ks_ne_node (hNa c hc) hCD (by rcases ho with h | h <;> omega) e
    · rw [hcur1, ← hcur3]
      unfold LawfulStore.curW
      rw [w.2.1, nodeAt_of_ksb w.1]
      exact w.mem_eq (nodeAt_aligned (hN3a _ hcC3) (by rw [curth_val]; omega) (by rw [curth_val]))
        (node_not_tw hq3 (by rw [curth_val]; omega) (by rw [curth_val]; omega) (by rw [curth_val]; omega))
  -- the fire step
  have rD3 : ∀ y ∈ T, FootLtArmed st s3 (L.cpu s3) y → R (tdA y) := fun y hy ha => by
    obtain ⟨a1', a2'⟩ := ha
    have e1 : L.mem s3 (tdA y) = L.mem s (tdA y) := htcb3 hy (K := 3528#u64) (by simp) (by simp)
    have e2 : L.mem s3 (thA y) = L.mem s (thA y) := htcb3 hy (K := 3568#u64) (by simp) (by simp)
    rw [e1] at a1'; rw [e2, c3] at a2'
    exact rT y hy ⟨a1', a2'⟩ 3528#u64 (by simp) (by simp) (by simp)
  have d3 : L.mem s3 (tdA TM) = L.mem s1 (tdA TM) :=
    (htcb3 hTMs.1 (K := 3528#u64) (by simp) (by simp)).trans (htcb1 hTMs.1 (K := 3528#u64) (by simp) (by simp)).symm
  have hdue1 : L.mem s1 (tdA TM) ≤ now := by
    have h := edue
    rw [← c1] at h
    unfold localtimer.timer_due at h
    rw [eq_of_spec_fd (obj.node_get.spec (L := L) s1 _ _)] at h; simp only [bind_ok] at h
    rw [eq_of_spec_fd (obj.Tcb.is_null.spec _)] at h; simp only [bind_ok] at h
    have tm1 : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) = TM := by
      rw [e1N, ← eTM]
      exact hnode1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
        (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
    rw [tm1] at h
    simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte] at h
    rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) s1 _)] at h; simp only [bind_ok] at h
    simpa using ok_inj_ff h
  have hac3 : L.actionW s3 = sched.ACTION_RESUME_CURRENT := by
    unfold LawfulStore.actionW
    rw [e3N, hnode3 _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega) (by rw [act_val]; omega)
      (by rw [act_val]; omega) (by rw [act_val]; omega)]
    exact hact0
  have eN3 : L.mem s3 (boundA TM) = N := by rw [← eN]; exact htcb3 hTMs.1 (K := 3368#u64) (by simp) (by simp)
  obtain ⟨Y, aY, hfire, gfire, TY, hstY, kY, cY, w, hwT, actY, fk, wbl, waf, wcur, wrun, wyl⟩ :=
    fire_wk_step ar hA (s := s) a3 (t := TM) (Lk := Lk) (U := U) (s1 := s1) (cpu := L.cpu s) (ct := L.curW s)
      (p := p) hT3 hBA hNt hAffSc k3 c3 (fun y hy K hK h8 _ => htcb3 hy hK h8) tm3 hne hTMs.1 haffTM ct3
      (by rw [d3]; exact not_lt.mpr hdue1) eN3 hN0 hac3 hwk hpTM
      (fun y hy K h1 h2 h3 => by rw [htcb3 hy (by omega) h3, htcb1 hy (by omega) h3]) efo (rN hN0)
      (fun k h1 h2 h3 => by rw [← eN, ← hpN]; exact wNt k h1 h2 h3) rL wL rS wS lkL
      (by rw [← eN, ← hpN]; exact hLkN) (fun o h1 h2 => ⟨nR o h1 h2, nW o h1 h2⟩) rCD hSW
      (rT TM hTMs.1 hTMs.2 3528#u64 (by simp) (by simp) (by simp))
      (rT TM hTMs.1 hTMs.2 3536#u64 (by simp) (by simp) (by simp)) rD3 hrmg
  -- the state after `fire`, relative to `s`
  have eYN : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cY, nodeAt_of_ksb kY]
  have nY : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 40 → o.val ≠ 48 → o.val ≠ 56 →
      o.val ≠ 80 → o.val ≠ 104 → o.val ≠ 112 →
      L.mem Y (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h16 h40 h48 h56 h80 h104 h112
    have := fk.1 o ho h8 h16 h56 h104 h112
    rw [e3N] at this
    rw [this]; exact hnode3 o ho h8 h40 h48 h56 h80
  have tY : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) → K.val ≠ 3496 →
      K.val ≠ 3504 → (y = w → K.val ≠ 3328 ∧ K.val ≠ 256 ∧ K.val ≠ 3376) →
      L.mem Y (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK h8 hK' h1 h2 hyw => (fk.2.1 y hy K hK h8 hK' h1 h2 hyw).trans (htcb3 hy hK h8)
  have scY : ∀ c ∈ Scs, c ≠ L.mem s (scA w) → ∀ b, Aligned b → InSC c (Z c) b → L.mem Y b = L.mem s b := by
    intro c hc hne b hb hin
    refine (fk.2.2 c hc (fun e => hne ?_) b hb hin).trans (hout3 b (h0.omega b (hO.scW c hc b hb hin)))
    rw [e, scA_eq, htcb3 hwT (K := 3464#u64) (by simp) (by simp)]
  have scaY : ∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y) := fun y hy =>
    tY y hy 3464#u64 (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp) (fun _ => by simp)
  have wbl' : Blocked (L.mem s (stA w)) := by
    rw [stA_eq, ← htcb3 hwT (K := 3328#u64) (by simp) (by simp), ← stA_eq]; exact wbl
  have waf' : L.mem s (affA w) = L.cpu s := by
    rw [← waf]; exact (htcb3 hwT (K := 3520#u64) (by simp) (by simp)).symm
  have wcur' : w ≠ L.curW s := by rw [← hcur3]; exact wcur
  -- no runnable thread shares `w`'s SC
  have hneR : ∀ y ∈ T, Runnable (L.mem s (stA y)) → L.mem s (scA y) ≠ 0#u64 →
      L.mem s (scA y) ≠ L.mem s (scA w) := by
    intro y hy hrun hs0 e
    have b1 := (hX.2.2.bound y hy hs0).2.1
    have hw0 : L.mem s (scA w) ≠ 0#u64 := by rw [← e]; exact hs0
    have b2 := (hX.2.2.bound w hwT hw0).2.1
    rw [e] at b1
    have hyw : y = w := b1.symm.trans b2
    subst hyw
    exact not_runnable_of_blocked wbl' hrun
  have ctY : L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.CUR_TIME) = now := by
    rw [eYN, ← e3N, fk.1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME])]
    exact ct3
  have rhY : L.mem Y (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) :=
    nY _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have relY : RelNone st Y := by
    have r1 : RelNone st s1 := rel_false (by rw [c1]; exact erel)
    refine rel_agree1 (cx := L.mem s (scA w)) hB1 (kY.trans k1.symm) (cY.trans c1.symm) ?_ ?_ ?_ ?_ ?_ r1
    · rw [e1N, rhY]; exact (hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).symm
    · unfold LawfulStore.curTime LawfulStore.nodeA
      rw [ctY, hnow]
    · intro y hy; rw [scaY y hy, scA_eq, htcb1 hy (K := 3464#u64) (by simp) (by simp)]
    · intro c hc hne b hb hin; rw [scY c hc hne b hb hin, (hout1 b (h0.omega b (hO.scW c hc b hb hin)))]
    · intro y hy hrun hs0
      rw [scA_eq, htcb1 hy (K := 3464#u64) (by simp) (by simp), ← scA_eq] at hs0 ⊢
      rw [stA_eq, htcb1 hy (K := 3328#u64) (by simp) (by simp), ← stA_eq] at hrun
      exact hneR y hy hrun hs0
  -- `awaken`
  have haw : sched.awaken st ar s3 a3 = ok (Y, aY) := by
    unfold sched.awaken
    rw [hfire]
    simp only [bind_ok, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
    rw [awaken_loop_none Y _ relY]
    simp only [bind_ok, bind_tc_ok]
  have hrs : ∀ hne' : L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD) ≠ 0#u64,
      R (scA (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD))) ∧
      RdHead (L := L) R Y (L.mem Y (scA (L.mem Y (L.nodeAt Y (L.cpu Y) layout.node.RELEASE_HEAD)))) := by
    intro hne'
    rw [eYN, rhY] at hne' ⊢
    obtain ⟨r1, -, r3, r4, r5⟩ := rel_facts hI hne'
    have hscw := hneR _ r1 (rel_head_run hI hne') r3
    rw [scaY _ r1]
    have hqr := scq_of hO hS r4
    refine ⟨gRd _ (by rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp))
      (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne', Or.inl rfl⟩))))), ?_⟩
    refine PathObl.ScAcc.head (W := fun _ => True)
      ⟨fun b ha hb => gRd _ ha (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne', Or.inr hb⟩))))), fun _ _ _ => trivial,
        trivial⟩ ((SCq.agree' hqr (fun b hb hin => scY _ r4 hscw b hb hin)).1 ?_)
    unfold LawfulStore.rmax
    rw [scY _ r4 hscw _ hqr.2.2.2.2 hqr.2.2.2.1]; exact r5
  have hawg : sched.awaken gS ar s3 a3 = sched.awaken st ar s3 a3 :=
    sched.awaken.guard_fire ar s3 a3 gfire (fun Y' a' e => by
      rw [hfire] at e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff e)
      rw [sched.awaken_loop.guard_nodue Y _
        (ndR Y eYN _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])) hrs
        (by unfold ctA; rw [eYN]; exact nR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])) relY,
        awaken_loop_none Y _ relY])
  exact fire_tail_of_aw ar hawg haw (hTail Y aY w haw ⟨TY, kY, cY, nY, tY, scY, relY, hstY, ctY, hwT, wbl', waf',
    wcur', actY, wrun, by rw [← wyl]; exact (htcb3 hwT (K := 3472#u64) (by simp) (by simp)).symm⟩)

end main

end Fl4Proofs.P2

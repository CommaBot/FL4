/-
# P2 (line p3mc, gen 26): an accepted waking fire run on a store answering the words of homed objects

Handoff §30c (W-h). The pieces the certificate (P2/IrqWhAnn) runs at the view start on its checked store:

* **`WH.fire_ok_guardWK`**: `fire_ok` after the timestamp on any `gS` answering `FireRd` and the words of the
  threads with `Hm` (`rH`, `rC`), `fire_rdG`'s walk (P2/FootTimerIrqFC) with the threads `may_run_here` reads asked
  to satisfy `Hm`: the due thread (`hHtm`), the notification's non-null head (`hHw`), the head of the highest ready
  queue (runnable, P1 `runQ`, hence `hHr`). `fire_rdG` asked every word `own` lets this core read, at a view start
  also other cores' threads' words.
* **`WH.irq_acc_fire_wkG`**: an accepted fire-case run whose signal wakes a thread, on any `gS` answering those
  reads and the waking chain's per-class premises asked of homed objects (`irq_accG_fire_pre` with
  `WH.fire_ok_guardWK` and `WH.fire_tail_wk2`, P2/IrqWhS), the deadline write asked only for the due thread.

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.IrqWhS
import Fl4Proofs.P2.IrqHnG
import Fl4Proofs.P2.FootTimerFireAk
import Fl4Proofs.P2.FootTimerFirePe
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.WH
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (guard RPerm WPerm HeldBy GateOnly bind_guard_congr)

section own
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

set_option maxHeartbeats 32000000 in
/-- **`fire_ok` after the timestamp on a store answering `FireRd` and the words of threads with `Hm`** (module
docstring): `fire_rdG`'s walk with the threads `may_run_here` reads (the due thread, the notification's head, the
head of the highest ready queue) asked to satisfy `Hm`: the due thread by `hHtm`, a non-null head by `hHw`, a
ready-queue member by `hHr` (it is runnable, P1 `runQ`). -/
theorem fire_ok_guardWK {R : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R] {s s1 : S}
    {Hm : U64 → Prop}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    (ntw : ∀ n ∈ Nt, ∀ k : U64, k.val < 64 → region K (core.num.U64.wrapping_add n k) = .ntfn n)
    (gRd : ∀ w, Aligned w → FireRd st T Z s w → R w)
    (rH : ∀ x ∈ T, Hm x → ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      k.val ≠ 3496 → k.val ≠ 3504 → R (core.num.U64.wrapping_add x k))
    (rC : ∀ x ∈ T, Hm x → L.mem s (scA x) ≠ 0#u64 → R (scCoreA (L.mem s (scA x))))
    (hHr : ∀ y ∈ T, Runnable (L.mem s (stA y)) → Hm y)
    (hHtm : Hm (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    (hHw : L.mem s (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s)
        layout.node.TIMER_MIN)))) layout.ntfn.HEAD) ≠ 0#u64 →
      Hm (L.mem s (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s)
        layout.node.TIMER_MIN)))) layout.ntfn.HEAD)))
    (hRD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (k1 : L.ksb s1 = L.ksb s) (c1 : L.cpu s1 = L.cpu s)
    (m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b)
    {tip p : localtimer.TimerIrqPlan} (etip : localtimer.plan_objects st s = ok tip)
    (esp : localtimer.same_plan tip p = ok true) (ct : obj.Tcb) (now : U64) :
    localtimer.fire_ok gS s1 (L.cpu s) ct p now =
      localtimer.fire_ok st s1 (L.cpu s) ct p now := by
  have hsp := same_plan_tm esp
  rcases plan_facts etip with ⟨t1, -⟩ | ⟨t1, t2, t3, t4⟩
  · have hp0 : p.tm = 0#u64 := by rw [← hsp.1]; exact t1
    rw [fire_ok_eq, fire_ok_eq, if_pos hp0, if_pos hp0]
  obtain ⟨Q, Rq, h0⟩ := hI.1
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hX := hI.2.2.1
  have hO := hX.1
  obtain ⟨TM, eTM⟩ : ∃ x, L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = x := ⟨_, rfl⟩
  have hpt : p.tm = TM := by rw [← hsp.1, t1, eTM]
  have hne : TM ≠ 0#u64 := by rw [← hpt, ← hsp.1]; exact t2
  have hh : TmHere st s TM := by rw [← hpt, ← hsp.1]; exact t3
  obtain ⟨N, eN⟩ : ∃ x, L.mem s (boundA TM) = x := ⟨_, rfl⟩
  rw [eTM, eN] at hHw
  rw [eTM] at hHtm
  have hpn : p.ntfn = 0#u64 ∨ p.ntfn = N := by rw [← eN, ← hsp.2, ← hpt, ← hsp.1]; exact t4
  have q1 : TM ∈ T := by
    have := (tmin_facts (BXI.blk hI) hcC (by rw [eTM]; exact hne)).1
    rw [eTM] at this
    exact this
  obtain ⟨tr, ctr⟩ := (TInv.rb (BXI.blk hI)).tree _ hcC
  have hk : TM ∈ tr.keys := by
    have e := ctr.min
    rw [eTM] at e
    rw [e]
    exact tr.minKey_mem.resolve_left (by rw [← e]; exact hne)
  have ha : L.mem s (affA TM) = L.cpu s := by
    have e := hh.1
    rw [aff_ok] at e
    exact ok_inj_ff e
  -- `s1` agrees with `s` off the node's `CUR_TIME` / `CONSUMED`
  have mT : ∀ {y k : U64}, y ∈ T → k.val < 4096 → k.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y k) = L.mem s (core.num.U64.wrapping_add y k) := by
    intro y k hy hk h8
    exact m1 _ (field_aligned (hT y hy) hk h8) (tcb_node_ne hN hy (hT y hy) hk (by simp [layout.node.CUR_TIME]))
      (tcb_node_ne hN hy (hT y hy) hk (by simp [layout.node.CONSUMED]))
  have mN : ∀ {n k : U64}, n ∈ Nt → k.val < 64 → k.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add n k) = L.mem s (core.num.U64.wrapping_add n k) := by
    intro n k hn hk h8
    obtain ⟨p1, p2⟩ := hO.ntP _ hn
    have hr := ntw _ hn k hk
    refine m1 _ (by unfold Aligned; rw [ntfn_word_val p1 p2 hk]; omega) (fun e => ?_) (fun e => ?_)
    · rw [e, hL.nd layout.node.CUR_TIME (by simp [layout.node.CUR_TIME])] at hr
      cases hr
    · rw [e, hL.nd layout.node.CONSUMED (by simp [layout.node.CONSUMED])] at hr
      cases hr
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
  have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c1, nodeAt_of_ksb k1]
  -- readable words
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd _ (nodeAt_aligned hN h1 h2) (Or.inl (Or.inl ⟨o, h1, h2, rfl⟩))
  have ndR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s1 (L.cpu s1) o) := fun o h1 h2 => by
    rw [e1N]; exact nR o h1 h2
  have keyR : ∀ {y k : U64}, y ∈ tr.keys → 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add y k) := @fun y k hy h1 h2 h3 => by
    have hyT := ctr.inT y hy
    exact gRd _ (field_aligned (hT _ hyT) (by omega) h3)
      (Or.inr (Or.inl ⟨y, hyT, ⟨ctr.armed y hy, ctr.core y hy⟩, k, h1, h2, h3, rfl⟩))
  have rD1 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) := hRD
  -- what `may_run_here` reads of a null thread or a TCB, at `s1`
  have mayZ : ∀ x : U64, (x = 0#u64 ∨ (x ∈ T ∧ Hm x)) → MayRdC st R s1 (L.cpu s1) x ∧
      (x ≠ 0#u64 → L.mem s1 (affA x) = L.cpu s1 → R (domA x) ∧ R (inqA x)) := fun x hx => by
    refine ⟨fun hx0 => ⟨rH x (hx.resolve_left hx0).1 (hx.resolve_left hx0).2 _ (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp), fun ha1 => ?_⟩, fun hx0 ha1 => ?_⟩
    · obtain ⟨hxT, hm⟩ := hx.resolve_left hx0
      have ms : L.mem s1 (scA x) = L.mem s (scA x) := mT (k := 3464#u64) hxT (by simp) (by simp)
      refine ⟨by rw [stA_eq]; exact rH x hxT hm _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
        rH x hxT hm _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
        rH x hxT hm _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
        rH x hxT hm _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), fun hs0 => ?_⟩
      rw [ms] at hs0 ⊢
      exact rC x hxT hm hs0
    · obtain ⟨hxT, hm⟩ := hx.resolve_left hx0
      exact ⟨rH x hxT hm _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
        rH x hxT hm _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)⟩
  have hdH : ∀ l : List U64, (∀ t ∈ l, t ∈ T ∧ Hm t) →
      l.headD 0#u64 = 0#u64 ∨ (l.headD 0#u64 ∈ T ∧ Hm (l.headD 0#u64)) := by
    intro l hl
    cases l with
    | nil => exact Or.inl rfl
    | cons y ys => exact Or.inr (hl y List.mem_cons_self)
  -- what `top_ok` reads at `s1`
  have eL1 : layout.node.L1_BITMAP = l1Off := by unfold layout.node.L1_BITMAP l1Off w64; rfl
  have topC : TopRdC st R s1 := by
    refine ⟨ndR _ (by simp [layout.node.L1_BITMAP]) (by simp [layout.node.L1_BITMAP]), by rw [k1]; exact rD1,
      ⟨ndR _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]), fun inv hinv => ndR _ (by simp; omega) (by simp)⟩,
      fun hl1 d pr q ed ep eq => ?_⟩
    have hB1 : BitmapOK st s1 (L.cpu s1) (fun p => Q (L.cpu s) p ≠ []) := by
      rw [c1]
      refine (h0.ready _ hcC).2.agree ?_ fun g hg => ?_
      · unfold LawfulStore.l1W
        rw [nodeAt_of_ksb k1]
        exact hnode1 _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega)
          (by rw [l1Off_val]; omega)
      · unfold LawfulStore.l2W
        rw [nodeAt_of_ksb k1]
        exact hnode1 _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
          (by rw [l2Off_val hg]; omega)
    have hne1 : L.l1W s1 (L.cpu s1) ≠ 0#u64 := by
      unfold LawfulStore.l1W
      rw [← eL1]
      exact hl1
    have hp : pr.val < 256 := by
      obtain ⟨q', hq', hq1, -, -⟩ :=
        spec_ex_fd (sched.highest_prio.spec (T := T) s1 d _ (by rw [c1]; exact hN.ksb k1) hB1 hne1)
      rw [hq'] at ep
      rw [← ok_inj_ff ep]
      exact hq1
    have eo : core.num.U64.wrapping_add q (core.num.U64.wrapping_mul pr 16#u64) = rqOff pr := by
      obtain ⟨off, hoff, ho1, -⟩ := spec_ex_fd (sched.rq_head_off.spec 0#u64 pr hp)
      unfold sched.rq_head_off at hoff
      simp only [rq_index_one, lift, bind_ok, eq] at hoff
      rw [← ho1]
      exact ok_inj_ff hoff
    have hov : (rqOff pr).val = 168 + 16 * pr.val := rqOff_val hp
    have hw : L.mem s1 (L.nodeAt s1 (L.cpu s1) (core.num.U64.wrapping_add q (core.num.U64.wrapping_mul pr 16#u64))) =
        (Q (L.cpu s) pr).headD 0#u64 := by
      rw [eo, e1N, hnode1 (rqOff pr) (by omega) (by omega) (by omega) (by omega),
        ← ((h0.ready _ hcC).1.rel pr hp).head]
      rfl
    rw [hw]
    exact ⟨by rw [eo, e1N]; exact nR (rqOff pr) (by omega) (by omega),
      (mayZ _ (hdH _ fun t ht => ⟨h0.memT hcC hp ht,
        hHr t (h0.memT hcC hp ht) (h0.runQ _ hcC pr hp t ht)⟩)).1⟩
  -- the due thread's tree links
  have lks := ctr.rep.links TM hk
  simp only [lk_l, lk_r, lk_p] at lks
  have mtr : L.mem s1 (trA TM) = L.mem s (trA TM) := mT (k := 3552#u64) q1 (by simp) (by simp)
  have mtp : L.mem s1 (tpA TM) = L.mem s (tpA TM) := mT (k := 3560#u64) q1 (by simp) (by simp)
  have hd1 : p.tm ≠ 0#u64 → ∀ x, obj.Tcb.timer_parent st p.tm s1 = ok x → x ≠ 0#u64 →
      R (core.num.U64.wrapping_add x 3528#u64) := fun _ x ex hx0 => by
    rw [hpt, eq_of_spec_fd (obj.Tcb.timer_parent.val (L := L) s1 TM), mtp] at ex
    have ex' := ok_inj_ff ex
    subst ex'
    exact keyR (lks.2.2.resolve_left hx0) (by simp) (by simp) (by simp)
  have hP0 : p.tm ≠ 0#u64 → ∀ x, obj.Tcb.timer_right st p.tm s1 = ok x → x ≠ 0#u64 → x ∈ tr.keys :=
    fun _ x ex hx0 => by
      rw [hpt, eq_of_spec_fd (obj.Tcb.timer_right.val (L := L) s1 TM), mtr] at ex
      have ex' := ok_inj_ff ex
      subst ex'
      exact lks.2.1.resolve_left hx0
  have hP : ∀ x, x ∈ tr.keys → R (core.num.U64.wrapping_add x 3544#u64) ∧
      ∀ y, obj.Tcb.timer_left st x s1 = ok y → y ≠ 0#u64 → y ∈ tr.keys := fun x hx => by
    refine ⟨keyR hx (by simp) (by simp) (by simp), fun y ey hy0 => ?_⟩
    have hl := ctr.rep.links x hx
    simp only [lk_l, lk_r, lk_p] at hl
    have mtl : L.mem s1 (tlA x) = L.mem s (tlA x) := mT (k := 3544#u64) (ctr.inT x hx) (by simp) (by simp)
    rw [eq_of_spec_fd (obj.Tcb.timer_left.val (L := L) s1 x), mtl] at ey
    have ey' := ok_inj_ff ey
    subst ey'
    exact hl.1.resolve_left hy0
  -- the tail: the due thread's bound notification
  have hTl : p.tm ≠ 0#u64 → fireTail gS s1 (L.cpu s1) ct p = fireTail st s1 (L.cpu s1) ct p :=
    fun _ => fireTail.guardC (fun hn0 => by
      have hpN : p.ntfn = N := hpn.resolve_left hn0
      have hb0 : L.mem s (boundA TM) ≠ 0#u64 := by rw [eN, ← hpN]; exact hn0
      have hNN : N ∈ Nt := by rw [← eN]; exact hX.2.2.bnd _ q1 hb0
      have eBt : L.mem s (ntfnBtA N) = TM := by rw [← eN]; exact hX.2.2.bs.tb _ q1 hb0
      obtain ⟨p1, p2⟩ := hO.ntP _ hNN
      have hN0 : N ≠ 0#u64 := by rw [← eN]; exact hb0
      have ntR : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → R (core.num.U64.wrapping_add N k) := fun k hk h8 =>
        gRd _ (by unfold Aligned; rw [ntfn_word_val p1 p2 hk]; omega)
          (Or.inr (Or.inr ⟨by rw [eTM]; exact hne, by rw [eTM, eN]; exact hN0, k, hk, h8, by rw [eTM, eN]⟩))
      rw [hpN, hpt]
      refine ⟨ntR layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]),
        ntR layout.ntfn.BOUND_TCB (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]),
        ntR layout.ntfn.HEAD (by simp [layout.ntfn.HEAD]) (by simp [layout.ntfn.HEAD]),
        by show R (stA TM); rw [stA_eq]; exact rH TM q1 hHtm _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
        ⟨(mayZ TM (Or.inr ⟨q1, hHtm⟩)).1, (mayZ TM (Or.inr ⟨q1, hHtm⟩)).2,
          ntR layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC]), topC⟩, fun w ew => ?_⟩
      have ehd : obj.Ntfn.head st N s1 = ok (L.mem s1 (core.num.U64.wrapping_add N layout.ntfn.HEAD)) := by
        unfold obj.Ntfn.head
        simp only [lift, bind_ok, L.read_eq]
      rw [ehd, mN (k := layout.ntfn.HEAD) hNN (by simp [layout.ntfn.HEAD]) (by simp [layout.ntfn.HEAD])] at ew
      have ew' := ok_inj_ff ew
      subst ew'
      have htz0 : L.mem s (core.num.U64.wrapping_add N layout.ntfn.HEAD) = 0#u64 ∨
          L.mem s (core.num.U64.wrapping_add N layout.ntfn.HEAD) ∈ T := by
        obtain ⟨E, EQ, hEW⟩ := h0.eps
        have he : N ∈ E := (hEW.2.2.2.2.2.2.2.1 N).2 (Or.inr (hNt N hNN))
        obtain ⟨-, -, hq⟩ := hEW.1 N he
        have e : L.mem s (core.num.U64.wrapping_add N layout.ntfn.HEAD) = (EQ N).headD 0#u64 := by
          rw [← hq.head, ntfn_head_eq]
          rfl
        rw [e]
        exact headD_tz _ hq.mem
      have htz : L.mem s (core.num.U64.wrapping_add N layout.ntfn.HEAD) = 0#u64 ∨
          (L.mem s (core.num.U64.wrapping_add N layout.ntfn.HEAD) ∈ T ∧
            Hm (L.mem s (core.num.U64.wrapping_add N layout.ntfn.HEAD))) := by
        rcases htz0 with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hHw (fun e => (hT _ h).ne0 (by rw [e]; rfl))⟩
      exact ⟨(mayZ _ htz).1, (mayZ _ htz).2,
        ntR layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC]), topC⟩)
  have g := fire_ok.guardK (gS := gS) (s := s1) (ct := ct) (p := p) (now := now) (fun x => x ∈ tr.keys)
    (fun _ => by rw [hpt]; exact keyR hk (by simp) (by simp) (by simp))
    (fun _ => by rw [hpt]; exact keyR hk (by simp) (by simp) (by simp))
    hd1 hP0 hP (fun x hx => keyR hx (by simp) (by simp) (by simp)) hTl
  rwa [c1] at g
end own

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 16000000 in
/-- **An accepted fire-case run waking a thread, on a store answering the words of homed objects** (module
docstring). -/
theorem irq_acc_fire_wkG {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    {Hm Hs Lk : U64 → Prop} {U : Set U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    (ntw : ∀ n ∈ Nt, ∀ k : U64, k.val < 64 → region K (core.num.U64.wrapping_add n k) = .ntfn n)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hq : IrqFire st ar s a) (hWk : ¬ NoWake st s)
    (gRd : IrqOk st s → ∀ w, Aligned w → FireRd st T Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → FireWr st T Z s w → w ≠ stA (L.curW s) → W w)
    (hIq : IrqOk st s → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hwS : IrqOk st s → ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RESTART → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hwH : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y →
      (L.mem X (tdA y) ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val ∧ v.val >>> 8 = (L.cpu s).val) →
      gS.write X (thA y) v = st.write X (thA y) v)
    (hwD : ∀ X y v, y ∈ T → FootLtArmed st s (L.cpu s) y →
      y = L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) → L.mem X (affA y) = L.cpu s →
      L.mem s (affA y) = L.cpu s →
      (L.mem X (tdA y) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem X (thA y)).val >>> 8 = (L.cpu s).val) →
      gS.write X (tdA y) v = st.write X (tdA y) v)
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (rH : ∀ x ∈ T, Hm x → ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      k.val ≠ 3496 → k.val ≠ 3504 → R (core.num.U64.wrapping_add x k))
    (rC : ∀ x ∈ T, Hm x → L.mem s (scA x) ≠ 0#u64 → R (scCoreA (L.mem s (scA x))))
    (rL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      ¬ TimerField K.val → ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → Hm y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      ¬ GateField K.val → ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → K.val ≠ 3336 →
      W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → Hs p → ∀ b, Aligned b → InSC p (Z p) b →
      b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (hSW : StWH st gS T Lk Hm s)
    (hLkN : p.ntfn ≠ 0#u64 → Lk p.ntfn) (hLkE : p.ep ≠ 0#u64 → Lk p.ep)
    (wN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → k.val ≠ 24 →
      W (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) k))
    (rwE : p.ep ≠ 0#u64 → ∀ k : U64, k.val < 16 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add p.ep k) ∧ W (core.num.U64.wrapping_add p.ep k))
    (wRt : p.reply ≠ 0#u64 → W (rTcbA p.reply))
    (hBA : ∀ s1 a1 x s2 a2 s3 a3, sched.update_timestamp st ar s a = ok (s1, a1) →
      sched.check_budget st ar s1 a1 = ok (x, s2, a2) → interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) →
      BufAt st T Cs H Sg Scs Z U s3)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hSlot : ∀ y, LocT st T s y → Hm y → R (vtA y) ∧ R (core.num.U64.wrapping_add (vtA y) 8#u64))
    (hKr : R (krA (L := L) s)) (hTab : PathObl.RdTab (L := L) R s)
    (hHr : ∀ y ∈ T, Runnable (L.mem s (stA y)) → Hm y) (hHsc : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hm y)
    (hHs : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → Hs (L.mem s (scA y)))
    (hHw : L.epState s (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) =
        obj.NTFN_WAITING →
      Hm (L.epQ s (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))).head)
    (hHw0 : L.mem s (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s)
        layout.node.TIMER_MIN)))) layout.ntfn.HEAD) ≠ 0#u64 →
      Hm (L.mem s (core.num.U64.wrapping_add (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s)
        layout.node.TIMER_MIN)))) layout.ntfn.HEAD)))
    (hHtm : Hm (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    localtimer.handle_timer_irq_local gS ar s a irq p = ok (true, s', a') := by
  have h0 := hI.1.choose_spec.choose_spec
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  obtain ⟨mx, now, i2, tip, x, s1, s2, s3, a1, a2, a3, emx, hle, ei1, etip, eb, eok, eq, eu, enow, erel, ei2, eb4,
    edue, efo, ecb, ehi⟩ := fire_eqs ar hA hq h
  refine irq_accG_fire_pre (gS := gS) (R := R) (W := W) ar hA hI hq
    (fun hok w ha hw => gRd hok w ha (Or.inl hw)) (fun hok w ha hw hn => gWr hok w ha (Or.inl hw) hn)
    hIq hD1 hD2 ?_ ?_ h
  · intro hok s1' a1' now' eu' _
    obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu'
    simp only at er
    exact WH.fire_ok_guardWK hI hL ntw (gRd hok) rH rC hHr hHtm hHw0 (hD1 hok) hNt (by rw [er, utW_ksb])
      (by rw [er, utW_cpu]) (fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2) etip eb _ _
  · intro hok s1' a1' x' s2' a2' s3' a3' now' eu' enow' efo' ecb' ehi'
    rw [eu] at eu'
    have e1 := ok_inj_ff eu'
    simp only [Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    rw [enow] at enow'
    obtain rfl := ok_inj_ff enow'
    obtain ⟨hTM0, hpN⟩ := plan_ntfn etip eb efo'
    have hB0 : L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ 0#u64 := fun e =>
      hWk (Or.inl e)
    have pn0 : p.ntfn ≠ 0#u64 := by rw [hpN]; exact hB0
    exact WH.fire_tail_wk2 (gS := gS) (R := R) (W := W) (Lk := Lk) (U := U) (Hm := Hm) (Hs := Hs) ar hA hI hNt hok
      (gRd hok) (gWr hok) (hD2 hok) (hwS hok) hwH hwD hWk hAffSc rL wL rS wS lkL (hD1 hok) hSW (hLkN pn0) hLkE
      (fun k h1 h2 h3 => by rw [hpN]; exact wN k h1 h2 h3) rwE wRt
      etip eb eq eok eu enow erel ei2 eb4 edue efo' ecb' emx hle ei1 ehi' (hBA _ _ _ _ _ _ _ eu ecb' ehi') hAs
      hSlot hKr hTab hHr hHsc hHs hHw hHtm

end acc

end Fl4Proofs.P2.WH

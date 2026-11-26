/-
# P2 (line stpost, generation 14): `move` of the CNodeDelete-no-PTE arm (`hmv` discharged)

`InvMoveW` by the I/O port's `io_move` route on the checked store **with slot `CAP0` writes**, `gd st (IoRS s)
(PWs …)` (`P2/MoveSlS.lean`; `PW`, `MoveSl`, `run_gd_mguard` untouched), whose successful runs are `mguard` runs for
`StepOK` (`run_gds_mguard`): the Delete arm's clear of `dest`'s `CAP0` (Frame → Null) keeps every owner.

* `obj.Slot.clear.guard0`, `cdt.empty_slot.guard_null0`, `invRep.guard_okS`: the gen-13 leaves with `dest`'s `CAP0`
  write and the caller's `STATE` write stated per value;
* **`delAcc2`**: `delAcc` with the writes stated one by one (slot words, `dest`'s `CAP0 := 0`, `STATE`);
* **`delFin2`**: `delFin` with the `STATE` write as `SWr`;
* `mvWrS` (`IoPre.mvWr` for `PWs`), `InvBlkGdW2` (the decode block on the new checked store, with the cap / length
  hypotheses of `InvBlkW2`), **`invBlkGdW2_of`** (proved at `Pre := SlJAt K ∧ InvQL`), **`invMoveW_of2`**;
* **`inv_pathsKF2`** / `inv_pathsKF2_startAt`: `inv_pathsKF` with `hmv` discharged.

No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvBlk
import Fl4Proofs.P2.MoveSlS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

section g
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

theorem obj.Slot.clear.guard0 (self : obj.Slot) (s : S) (h0 : ∀ x, gS.write x self 0#u64 = st.write x self 0#u64)
    (h8 : W (core.num.U64.wrapping_add self 8#u64)) (h16 : W (core.num.U64.wrapping_add self 16#u64))
    (h24 : W (core.num.U64.wrapping_add self 24#u64)) :
    obj.Slot.clear gS self s = obj.Slot.clear st self s := by
  unfold obj.Slot.clear
  simp only [lift, bind_ok, h0, gst_write h8, gst_write h16, gst_write h24]

/-- (gen 14) **`empty_slot` with a null cleanup**, the slot's `CAP0` write of `0` answered as `st`'s at every state, run-relative: the slot's words read and written, the
previous slot's `NEXT` word, the next slot's `PREV` and `NEXT` words. -/
theorem cdt.empty_slot.guard_null0 {x : S} {a : A} {slot : obj.Slot} {y : S × A}
    (r0 : R slot) (r8 : R (core.num.U64.wrapping_add slot 8#u64))
    (r16 : R (core.num.U64.wrapping_add slot layout.cte.PREV)) (r24 : R (core.num.U64.wrapping_add slot layout.cte.NEXT))
    (w0 : ∀ x, gS.write x slot 0#u64 = st.write x slot 0#u64) (w8 : W (core.num.U64.wrapping_add slot 8#u64)) (w16 : W (core.num.U64.wrapping_add slot 16#u64))
    (w24 : W (core.num.U64.wrapping_add slot 24#u64))
    (hp : L.mem x (core.num.U64.wrapping_add slot layout.cte.PREV) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem x (core.num.U64.wrapping_add slot layout.cte.PREV)) layout.cte.NEXT) ∧
      W (core.num.U64.wrapping_add (L.mem x (core.num.U64.wrapping_add slot layout.cte.PREV)) layout.cte.NEXT))
    (hn : ∀ nx, obj.Slot.next st slot x = ok nx → nx ≠ 0#u64 →
      W (core.num.U64.wrapping_add nx layout.cte.PREV) ∧ R (core.num.U64.wrapping_add nx layout.cte.NEXT) ∧
      W (core.num.U64.wrapping_add nx layout.cte.NEXT))
    (h : cdt.empty_slot st ar x a slot .Null = ok y) : cdt.empty_slot gS ar x a slot .Null = ok y := by
  unfold cdt.empty_slot at h ⊢
  rw [obj.Slot.cap.guard (gS := gS) slot x r0 r8]
  revert h
  refine tr_bind_same (fun c _ => ?_)
  refine tr_bind_same (fun b _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Slot.prev.guard (gS := gS) slot x r16]
  refine tr_bind_same (fun prev ep => ?_)
  rw [slot_prev_ok] at ep
  have eprev := (ok_inj_ff ep).symm
  subst eprev
  rw [obj.Slot.next.guard (gS := gS) slot x r24]
  refine tr_bind_same (fun nx en => ?_)
  rw [obj.Slot.first_badged.guard (gS := gS) slot x r24]
  refine tr_bind_same (fun fb _ => ?_)
  refine tr_bind_same (fun b1 eb1 => ?_)
  unfold obj.Slot.is_null at eb1
  have e1 := ok_inj_ff eb1
  refine tr_bind (fun s1 es1 _ => ?_) (fun s1 _ => ?_)
  · by_cases hb1 : b1 = true
    · rw [if_pos hb1] at es1 ⊢; exact es1
    · rw [if_neg hb1] at es1 ⊢
      have hne : L.mem x (core.num.U64.wrapping_add slot layout.cte.PREV) ≠ 0#u64 := fun e0 =>
        hb1 (by rw [← e1]; simp [e0])
      rw [obj.Slot.set_next.guard (gS := gS) _ x nx (hp hne).1 (hp hne).2]; exact es1
  refine tr_bind_same (fun b2 eb2 => ?_)
  unfold obj.Slot.is_null at eb2
  have e2 := ok_inj_ff eb2
  refine tr_bind (fun s2 es2 _ => ?_) (fun s2 _ => ?_)
  · by_cases hb2 : b2 = true
    · rw [if_pos hb2] at es2 ⊢; exact es2
    · rw [if_neg hb2] at es2 ⊢
      have hne : nx ≠ 0#u64 := fun e0 => hb2 (by rw [← e2]; simp [e0])
      obtain ⟨wp, rn, wn⟩ := hn nx en hne
      revert es2
      rw [obj.Slot.set_prev.guard (gS := gS) nx s1 _ wp]
      refine tr_bind_same (fun s3 _ => ?_)
      rw [obj.Slot.first_badged.guard (gS := gS) nx s3 rn]
      refine tr_bind_same (fun nfb _ => ?_)
      refine tr_ite (fun _ h => ?_) (fun _ h => ?_)
      · rw [obj.Slot.set_first_badged.guard (gS := gS) nx s3 _ rn wn]; exact h
      · rw [obj.Slot.set_first_badged.guard (gS := gS) nx s3 _ rn wn]; exact h
  rw [obj.Slot.clear.guard0 (gS := gS) slot s2 w0 w8 w16 w24]
  exact id

/-- (gen 14) **The reply after an `Ok` decode**, the `STATE` write as `SWr`, run-relative: the caller's `STATE`, the reply
registers, and `set_thread_state RUNNING` (its node words and the current SC's `REFILL_MAX`, at the state after the
reply). -/
theorem invRep.guard_okS {x : S} {a : A} {t : U64} {z : S × A × core.result.Result Unit error.Exc}
    (rst : R (stA t)) (wst : SWr gS st t sched.TS_RUNNING) (rsc : R (scA t)) (riq : R (inqA t))
    (wB : W (regA t layout.reg.BADGE)) (wM : W (regA t layout.reg.MSG_INFO))
    (h5 : ∀ s5, msg.reply_success_empty st x t = ok s5 → NodeSt (L := L) R W s5 ∧
      R (maxA (L.mem (L.wr s5 (stA t) sched.TS_RUNNING) (scA t))))
    (h : invRep st t x a (.Ok ()) = ok z) : invRep gS t x a (.Ok ()) = ok z := by
  unfold invRep at h ⊢
  rw [obj.Tcb.state.guard (gS := gS) t x rst]
  revert h
  refine tr_bind_same (fun i6 _ => ?_)
  refine tr_bind (fun t1 et1 _ => ?_) (fun _ _ h => h)
  by_cases hi : i6 = sched.TS_RESTART
  · rw [if_pos hi] at et1 ⊢
    rw [msg.reply_success_empty.guard (gS := gS) x t wB wM]
    revert et1
    refine tr_bind_same (fun s5 es5 => ?_)
    rw [sched.set_thread_state.guardV (gS := gS) s5 t _ (h5 s5 es5).1 wst rst rsc (h5 s5 es5).2 riq]
    exact id
  · rw [if_neg hi] at et1 ⊢; exact et1

end g

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayout}

set_option maxHeartbeats 2000000 in
/-- (stpost gen 14) **`delAcc` with the writes stated one by one** (the slot words, `dest`'s `CAP0` write of `0`, the
caller's `STATE` writes), so that p2sl's checked store with slot `CAP0` writes fits; the Delete decode and its reply run as on `st` (run-relative), at an entry with `IoPre` and `DelEnt`, after the prefix and checks
(`InvChk`), for a message of length at least 2. -/
theorem delAcc2 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s)
    (hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
      (16 ≤ o.val ∨ (¬ TcbSlot K q ∧ NullOrFrame (L.mem s q))) → W (core.num.U64.wrapping_add q o))
    (hw0 : ∀ q, q ∈ K.slots → Locks s q → ¬ TcbSlot K q → NullOrFrame (L.mem s q) →
      ∀ x, gS.write x q 0#u64 = st.write x q 0#u64)
    (hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING → SWr gS st (L.curW s) v)
    (E : DelEnt st K Cs Locks p s) (hsl : p.slot ∈ K.slots) (hlen : ¬ length < 2#u64)
    (hvs : ∀ sl fp rt asid va, sl ∈ K.slots →
      obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧
        VsRd st K s asid va)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y) :
    syscall.decode_invocation gS ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z → invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z := by
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, Cw, hcs, hlk, hdc, hm, hC, hcl, hWk, hd, hdO, hLd, hpv, hnx⟩ := E
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.ent (Locks := Locks) hW
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL : Slot8 K := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA P.tp P.np P.cT es1 eu
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact P.slot_keep w0 hq hbq hb
  have hcap' : cap = .CNode cp cr cg cgb := by
    rw [cap_agree hL hsl ag, hcs] at hcap; exact (ok_inj_ff hcap).symm
  subst hcap'
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned P.tA h1 h2) (preW_tcb P.tA P.np P.cT h1 h3)
  have r10 : L.mem s2 (regA (L.curW s) layout.reg.R10) = L.mem s (regA (L.curW s) layout.reg.R10) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R10) (by simp [layout.reg.R10])
      (by simp [layout.reg.R10]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r8 : L.mem s2 (regA (L.curW s) layout.reg.R8) = L.mem s (regA (L.curW s) layout.reg.R8) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R8) (by simp [layout.reg.R8])
      (by simp [layout.reg.R8]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have slotK : ∀ p r, Cw p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s2 = obj.Slot.cap st (cnSlot p (x &&& m)) s :=
    fun p r hp m hm x => cap_agree hL (hWk p r m x hp hm).1 ag
  have hCn' : ∀ p1 r1 gs1 g1, capability.Cap.CNode cp cr cg cgb = .CNode p1 r1 gs1 g1 → Cw p1 r1 := by
    intro p1 r1 gs1 g1 e; cases e; exact hC
  have hlk2 : cspace.lookup_target_slot st s2 (.CNode cp cr cg cgb) (L.mem s2 (regA (L.curW s) layout.reg.R10))
      (L.mem s2 (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) := by
    rw [r10, r8]
    unfold cspace.lookup_target_slot cspace.lookup_slot_for_cnode_op at hlk ⊢
    simp only [bind_ok, ↓reduceIte] at hlk ⊢
    by_cases d1 : L.mem s (regA (L.curW s) layout.reg.R8) < 1#u64
    · rw [if_pos d1] at hlk; simp at hlk
    rw [if_neg d1] at hlk ⊢
    by_cases d2 : L.mem s (regA (L.curW s) layout.reg.R8) > cspace.WORD_BITS
    · rw [if_pos d2] at hlk; simp at hlk
    rw [if_neg d2] at hlk ⊢
    unfold cspace.resolve_address_bits at hlk ⊢
    obtain ⟨res, eres, hl⟩ := bind_eq_ok hlk
    have eres' := rab_loop_congr2 st Cw slotK hcl 66 _ _ 65#u64 res (by simp) hCn' eres
    rw [eres']; simp only [bind_ok]; exact hl
  have hdc2 : obj.Slot.cap st dest s2 = ok (.Frame fp .Small rt false mp false asid va) := by
    rw [cap_agree hL hd ag]; exact hdc
  have hpv2 : L.mem s2 (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem s2 (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots := by
    rw [ag _ (slotW_of hL hd (by simp [layout.cte.PREV])) (slot_al hL hd (by simp [layout.cte.PREV])
      (by simp [layout.cte.PREV]))]
    exact fun h0 => (hpv h0).1
  have hnx2 : ∀ nx, obj.Slot.next st dest s2 = ok nx → nx ≠ 0#u64 → nx ∈ K.slots := fun nx e h0 =>
    (hnx nx (by rw [← next_agree hL hd ag]; exact e) h0).1
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact Ent.run
  have hK0 := SchedOK.of_sw I.F (by rw [hct]; exact Hf.sc) (by rw [hct]; exact Hf.nr)
  rw [hct] at hK0
  have hK : SchedOK (L := L) s2 (L.curW s) := hK0
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ SlotW K (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact P.node_notSlot ho
  have hmxS : ¬ SlotW K (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact P.sc_notSlot (P.hSc _ P.cscS) I.F.q.2.2.2.1
  have O : SlotOK (L := L) K s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => P.tcb_notSlot (P.hT _ P.cT) h1 h2, hmxS⟩
  -- the words
  have hLd' := hLd
  have hnT := notTcbSlot_of hdO
  have hnf := nof_of_frame_slot hdc
  have e0 : core.num.U64.wrapping_add dest 0#u64 = dest := wadd_zero (hL dest hd).2
  have dR : ∀ o : U64, o.val < 32 → o.val % 8 = 0 → IoRS (st := st) K Locks s (core.num.U64.wrapping_add dest o) :=
    fun o ho h8 => (P.lockSlot hd hLd' ho h8).1
  have dW : ∀ o : U64, o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val → W (core.num.U64.wrapping_add dest o) :=
    fun o ho h8 h8' => hwS dest o hd hLd' ho h8 h8' (Or.inr ⟨hnT, hnf⟩)
  have r0 : IoRS (st := st) K Locks s dest := by have := dR 0#u64 (by simp) (by simp); rwa [e0] at this
  have w0' := hw0 dest hd hLd' hnT hnf
  have nR : ∀ q, q ∈ K.slots → Locks s q → ∀ o : U64, o.val < 32 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add q o) := fun q hq hl o ho h8 =>
    (P.lockSlot hq hl ho h8).1
  have nW : ∀ q, q ∈ K.slots → Locks s q → ∀ o : U64, o.val < 32 → o.val % 8 = 0 → 16 ≤ o.val →
      W (core.num.U64.wrapping_add q o) := fun q hq hl o ho h8 h16 =>
    hwS q o hq hl ho h8 (by omega) (Or.inl h16)
  have nR0 : ∀ q, q ∈ K.slots → Locks s q → IoRS (st := st) K Locks s q := fun q hq hl => by
    have := nR q hq hl 0#u64 (by simp) (by simp); rwa [wadd_zero (hL q hq).2] at this
  -- the node, the caller's words
  have hctR : IoRS (st := st) K Locks s (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  have hN : ∀ x : S, (∀ o, L.nodeAt x (L.cpu x) o = L.nodeAt s (L.cpu s) o) →
      NodeSt (L := L) (IoRS (st := st) K Locks s) W x := by
    have n0 : IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    have n1 : IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      (P.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
    have n1w : W (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      hW.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    intro x hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hn]; exact n0
    · rw [hn]; exact n1
    · rw [hn]; exact n1w
  have hnd2 : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [I.cp, nodeAt_of_ksb I.k]
  have rst := P.stw (Locks := Locks)
  have rsc : IoRS (st := st) K Locks s (scA (L.curW s)) :=
    P.gate (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have riq : IoRS (st := st) K Locks s (inqA (L.curW s)) :=
    (P.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  have hmxR : IoRS (st := st) K Locks s (maxA (L.cscW s)) := by
    have hmx := maxA_facts P.bxi.2.2.1.1 P.cscS
    exact P.cscacc.rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩
  have hsc2 : L.mem s2 (scA (L.curW s)) = L.cscW s := by rw [← hct]; exact I.F.i
  -- the decode
  rw [decode_cnode_eq ar] at hy
  have hdg : syscall.decode_invocation gS ar s2 a1 fl4_abi.label.CNodeDelete length p.slot (.CNode cp cr cg cgb)
      true true true false buf p.extra = cnode.decode gS ar s2 a1 fl4_abi.label.CNodeDelete length
        (.CNode cp cr cg cgb) buf p.extra := by
    unfold syscall.decode_invocation
    rw [sched.cur_thread.guard (gS := gS) s2 hctR, cur_thread_ok]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  have hreg : ∀ i : U64, i.val < 2 → ∀ r, msg.msg_register i = ok r →
      IoRS (st := st) K Locks s (regA (L.curW s) r) := by
    intro i hi r hr
    unfold msg.msg_register at hr
    by_cases h0 : i = 0#u64
    · rw [if_pos h0] at hr; cases ok_inj_ff hr; exact (P.reg (by simp [layout.reg.R10])).1
    · rw [if_neg h0] at hr
      have h1 : i = 1#u64 := by
        apply UScalar.eq_of_val_eq
        have : i.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq (by simp [e]))
        simp; omega
      rw [if_pos h1] at hr; cases ok_inj_ff hr; exact (P.reg (by simp [layout.reg.R8])).1
  have hRc2 : WalkRc (st := st) (IoRS (st := st) K Locks s) s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    exact P.slot (hWk p r m y hp hm).1 (Or.inr (cap_not_nof hc (Or.inl ⟨_, _, _, _, rfl⟩)))
  have hcl2 : WalkCl (st := st) s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    exact hcl p r m y p' r' gs' g' hp hm hc
  have hRd : IoRS (st := st) K Locks s dest ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add dest 8#u64) :=
    ⟨r0, dR 8#u64 (by simp) (by simp)⟩
  -- the frame finalisation makes no access (stale mapped caps: `unmap_nop`)
  have hvs1 : mp = true → asid ≠ 0#u64 → va ≤ fl4_abi.consts.USER_TOP ∧ VsRd st K s asid va := fun hmp hA => by
    subst hmp; obtain ⟨h1, -, h3⟩ := hvs dest fp rt asid va hd hdc hA; exact ⟨h1, h3⟩
  have hr3 : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 →
      ∀ b, VsW K b → st.read x3 b = st.read s b := fun x3 hs3 b hb => by
    have K3 : KeepA (L := L) s2 (L.curW s) x3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
    rw [L.read_eq, L.read_eq, K3.mem hb.1 (P.vs_notIoTW hb), w0.2.2 b hb.1 (P.vs_notPreW hb)]
  have hk3 : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 →
      st.ks_base x3 = st.ks_base s := fun x3 hs3 => by
    have K3 : KeepA (L := L) s2 (L.curW s) x3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
    rw [L.ks_base_eq, L.ks_base_eq, K3.1.1, w0.1]
  have hfrS : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 →
      FrNo st ar x3 mp asid va fp := fun x3 hs3 => frNo_of ar hm hvs1 (hr3 x3 hs3) (hk3 x3 hs3)
  have hfrG : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 →
      FrNo gS ar x3 mp asid va fp := fun x3 hs3 => frNo_of ar hm hvs1
    (fun b hb => (gst_read (VsW.ioRS (Locks := Locks) (s := s) hb)).trans (hr3 x3 hs3 b hb))
    (by rw [show gS.ks_base = st.ks_base from gst_ks_base]; exact hk3 x3 hs3)
  -- the deletion at the state after `set_thread_state RESTART`
  have hdel : ∀ s3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok s3 →
      ∀ y', cdt.delete st ar s3 a1 dest true = ok y' → cdt.delete gS ar s3 a1 dest true = ok y' := by
    intro s3 hs3 y' hy'
    have K3 : KeepA (L := L) s2 (L.curW s) s3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
    have ag3 : ∀ b, SlotW K b → Aligned b → L.mem s3 b = L.mem s b := fun b hs hb =>
      (K3.mem hb (O.notT hK hs)).trans (ag b hs hb)
    have hc3 : obj.Slot.cap st dest s3 = ok (.Frame fp .Small rt false mp false asid va) := by
      rw [cap_agree hL hd ag3]; exact hdc
    have ep3 : L.mem s3 (core.num.U64.wrapping_add dest layout.cte.PREV) =
        L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV) :=
      ag3 _ (slotW_of hL hd (by simp [layout.cte.PREV])) (slot_al hL hd (by simp [layout.cte.PREV])
        (by simp [layout.cte.PREV]))
    have r16 := dR layout.cte.PREV (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV])
    have r24 := dR layout.cte.NEXT (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])
    have hfg : cdt.is_final_capability_with_cap gS s3 dest (.Frame fp .Small rt false mp false asid va) =
        cdt.is_final_capability_with_cap st s3 dest (.Frame fp .Small rt false mp false asid va) := by
      refine cdt.is_final_capability_with_cap.guard s3 dest _ r16 r24 (fun h0 => ?_) (fun nx e h0 => ?_)
      · rw [ep3] at h0 ⊢
        obtain ⟨hq, hl⟩ := hpv h0
        exact ⟨nR0 _ hq hl, nR _ hq hl 8#u64 (by simp) (by simp)⟩
      · rw [next_agree hL hd ag3] at e
        obtain ⟨hq, hl⟩ := hnx nx e h0
        exact ⟨nR0 _ hq hl, nR _ hq hl 8#u64 (by simp) (by simp)⟩
    refine cdt.delete.guard_frame ar hc3 (hfrS s3 hs3) (hfrG s3 hs3) r0 hRd.2 hfg (fun y'' he => ?_) hy'
    refine cdt.empty_slot.guard_null0 ar r0 hRd.2 r16 r24 w0' (dW 8#u64 (by simp) (by simp) (by simp))
      (dW 16#u64 (by simp) (by simp) (by simp)) (dW 24#u64 (by simp) (by simp) (by simp)) (fun h0 => ?_)
      (fun nx e h0 => ?_) he
    · rw [ep3] at h0 ⊢
      obtain ⟨hq, hl⟩ := hpv h0
      exact ⟨nR _ hq hl _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]),
        nW _ hq hl _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])⟩
    · rw [next_agree hL hd ag3] at e
      obtain ⟨hq, hl⟩ := hnx nx e h0
      exact ⟨nW _ hq hl _ (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV]),
        nR _ hq hl _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]),
        nW _ hq hl _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])⟩
  have hmx2 : IoRS (st := st) K Locks s
      (maxA (L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)))) := by
    have kw := (KeepA.refl ha2 hrun).wr hK (b := stA (L.curW s)) (v := sched.TS_RESTART) (Or.inr rfl)
      (fun _ => Or.inl rfl)
    have e : L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      kw.mem (field_aligned P.tA (by simp) (by simp)) (iotw_field P.tA (by simp) (by simp))
    rw [e, hsc2]
    exact hmxR
  refine ⟨?_, ?_⟩
  · rw [hdg]
    have h := hy
    unfold cnode.decode at h ⊢
    rw [if_neg lblD1, if_neg lblD2, if_neg hlen] at h ⊢
    rw [sched.cur_thread.guard (gS := gS) s2 hctR]
    rw [cur_thread_ok, hct] at h ⊢
    simp only [bind_ok] at h ⊢
    rw [msg.syscall_arg.guard_lt (gS := gS) s2 (L.curW s) buf 0#u64 (by simp [msg.N_MSG_REGISTERS])
        (hreg 0#u64 (by simp)),
      msg.syscall_arg.guard_lt (gS := gS) s2 (L.curW s) buf 1#u64 (by simp [msg.N_MSG_REGISTERS])
        (hreg 1#u64 (by simp))]
    rw [sarg0_reg, sarg1_reg, reg_ok, reg_ok] at h ⊢
    simp only [bind_ok] at h ⊢
    rw [hlk2] at h
    rw [cspace.lookup_target_slot.guardM (gS := gS) Cw hRc2 hcl2 hC hRd hlk2]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lblD3, lblD4, ↓reduceIte] at h ⊢
    revert h
    rw [sched.set_thread_state.guardV (gS := gS) s2 (L.curW s) _ (hN s2 hnd2) (hst _ (Or.inl rfl)) rst.1 rsc hmx2 riq]
    refine tr_bind_same (fun s3 hs3 => ?_)
    exact hdel s3 hs3 y
  · intro z hz'
    obtain ⟨hy1, kx⟩ := cnDel_keep ar hK O ha2 hrun hL hlen hlk2 hd hdc2 hfrS hpv2 hnx2 hy
    obtain ⟨r, x, a2⟩ := y
    simp only at hy1 kx hz' ⊢
    subst hy1
    have Fx := kx.sched hK O
    refine invRep.guard_okS (gS := gS) rst.1 (hst _ (Or.inr rfl)) rsc riq (hW.reg _ rB384) (hW.reg _ rM384) ?_ hz'
    intro s5 es5
    have k5 : KeepA (L := L) x (L.curW s) s5 := by
      unfold msg.reply_success_empty at es5
      rw [set_reg_ok'] at es5; simp only [bind_ok] at es5
      obtain ⟨mi, -, es5⟩ := bind_eq_ok es5
      unfold msg.set_msg_info at es5
      obtain ⟨w, -, es5⟩ := bind_eq_ok es5
      rw [set_reg_ok'] at es5
      cases ok_inj_ff es5
      exact ((KeepA.refl kx.2.1 kx.2.2).wr_reg Fx rB384).wr_reg Fx rM384
    have k6 := kx.keepA (k5.wr Fx (b := stA (L.curW s)) (v := sched.TS_RUNNING) (Or.inr rfl) (fun _ => Or.inr rfl))
    have k5' := kx.keepA k5
    refine ⟨hN s5 (fun o => (k5'.node o).trans (hnd2 o)), ?_⟩
    have e6 : L.mem (L.wr s5 (stA (L.curW s)) sched.TS_RUNNING) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      k6.tcbF hK O (k := 3464#u64) (by simp) (by simp) (by simp)
    rw [e6, hsc2]; exact hmxR

end acc

section fin
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

/-- (stpost gen 13) **`FinOK` after the CNodeDelete-no-PTE decode block** (the I/O port's `io_hfin` route with the
Delete arm's slot writes): at an accepted run's post-prefix state `s2` (`InvChk`), a decode of the CNode cap at the
plan's slot at `CNodeDelete` with `length ≥ 2`, then `invRep`, reply `Ok ()` and leave `FinOK`. Inputs: `IoPre` and
`DelEnt` at the entry, the plan's slot a capability slot, the write set `W` covering the prefix words (`IoWr`) and
the caller's `STATE`. -/
theorem delFin2 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A} {z : S × A × core.result.Result Unit error.Exc}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s) (hsw : SWr gS st (L.curW s) sched.TS_RUNNING)
    (E : DelEnt st K Cs Locks p s) (hsl : p.slot ∈ K.slots) (hlen : ¬ length < 2#u64)
    (hvs : ∀ sl fp rt asid va, sl ∈ K.slots →
      obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧
        VsRd st K s asid va)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ FinOK (L := L) gS (IoRS (st := st) K Locks s) W ar s z.1 z.2.1 := by
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, Cw, hcs, hlk, hdc, hm, hC, hcl, hWk, hd, -, -, hpv, hnx⟩ := E
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.ent (Locks := Locks) hW
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL : Slot8 K := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA P.tp P.np P.cT es1 eu
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact P.slot_keep w0 hq hbq hb
  -- the invoked cap is the CNode cap
  have hcap' : cap = .CNode cp cr cg cgb := by
    rw [cap_agree hL hsl ag, hcs] at hcap; exact (ok_inj_ff hcap).symm
  subst hcap'
  -- the registers `R10`, `R8`
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned P.tA h1 h2) (preW_tcb P.tA P.np P.cT h1 h3)
  have r10 : L.mem s2 (regA (L.curW s) layout.reg.R10) = L.mem s (regA (L.curW s) layout.reg.R10) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R10) (by simp [layout.reg.R10])
      (by simp [layout.reg.R10]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r8 : L.mem s2 (regA (L.curW s) layout.reg.R8) = L.mem s (regA (L.curW s) layout.reg.R8) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R8) (by simp [layout.reg.R8])
      (by simp [layout.reg.R8]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  -- the target lookup at `s2`
  have slotK : ∀ p r, Cw p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s2 = obj.Slot.cap st (cnSlot p (x &&& m)) s :=
    fun p r hp m hm x => cap_agree hL (hWk p r m x hp hm).1 ag
  have hCn' : ∀ p1 r1 gs1 g1, capability.Cap.CNode cp cr cg cgb = .CNode p1 r1 gs1 g1 → Cw p1 r1 := by
    intro p1 r1 gs1 g1 e; cases e; exact hC
  have hlk2 : cspace.lookup_target_slot st s2 (.CNode cp cr cg cgb) (L.mem s2 (regA (L.curW s) layout.reg.R10))
      (L.mem s2 (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) := by
    rw [r10, r8]
    unfold cspace.lookup_target_slot cspace.lookup_slot_for_cnode_op at hlk ⊢
    simp only [bind_ok, ↓reduceIte] at hlk ⊢
    by_cases d1 : L.mem s (regA (L.curW s) layout.reg.R8) < 1#u64
    · rw [if_pos d1] at hlk; simp at hlk
    rw [if_neg d1] at hlk ⊢
    by_cases d2 : L.mem s (regA (L.curW s) layout.reg.R8) > cspace.WORD_BITS
    · rw [if_pos d2] at hlk; simp at hlk
    rw [if_neg d2] at hlk ⊢
    unfold cspace.resolve_address_bits at hlk ⊢
    obtain ⟨res, eres, hl⟩ := bind_eq_ok hlk
    have eres' := rab_loop_congr2 st Cw slotK hcl 66 _ _ 65#u64 res (by simp) hCn' eres
    rw [eres']; simp only [bind_ok]; exact hl
  -- the target's facts at `s2`
  have hdc2 : obj.Slot.cap st dest s2 = ok (.Frame fp .Small rt false mp false asid va) := by
    rw [cap_agree hL hd ag]; exact hdc
  have hpv2 : L.mem s2 (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem s2 (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots := by
    rw [ag _ (slotW_of hL hd (by simp [layout.cte.PREV])) (slot_al hL hd (by simp [layout.cte.PREV])
      (by simp [layout.cte.PREV]))]
    exact fun h0 => (hpv h0).1
  have hnx2 : ∀ nx, obj.Slot.next st dest s2 = ok nx → nx ≠ 0#u64 → nx ∈ K.slots := fun nx e h0 =>
    (hnx nx (by rw [← next_agree hL hd ag]; exact e) h0).1
  -- the scheduler facts at `s2` (io_hfin)
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hy2 : L.mem s2 (yieldA (L.curW s)) = 0#u64 := by
    rw [eq_ok_of_spec (obj.Tcb.yield_to.spec (L := L) s2 (L.curW s))] at ey; exact ok_inj_ff ey
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact Ent.run
  have A0 := Ent.acc
  have hK0 := SchedOK.of_sw I.F (by rw [hct]; exact Hf.sc) (by rw [hct]; exact Hf.nr)
  rw [hct] at hK0
  have hK : SchedOK (L := L) s2 (L.curW s) := hK0
  -- the slot words miss the node, the TCB fields and the SC words
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ SlotW K (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact P.node_notSlot ho
  have hmx : ¬ SlotW K (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact P.sc_notSlot (P.hSc _ P.cscS) I.F.q.2.2.2.1
  have O : SlotOK (L := L) K s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => P.tcb_notSlot (P.hT _ P.cT) h1 h2, hmx⟩
  -- the run
  have hm3 : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 →
      FrNo st ar x3 mp asid va fp := by
    intro x3 hs3
    have K3 : KeepA (L := L) s2 (L.curW s) x3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
    rcases hm with h0 | h0 | hn
    · exact Or.inl h0
    · exact Or.inr (Or.inl h0)
    · cases mp with
      | false => exact Or.inl rfl
      | true =>
        by_cases hA : asid = 0#u64
        · exact Or.inr (Or.inl hA)
        · obtain ⟨hva, -, hV⟩ := hvs dest fp rt asid va hd hdc hA
          refine Or.inr (Or.inr (fun a' => unmap_nop ar (fun b hb => ?_) ?_ hV hva hn a'))
          · rw [L.read_eq, L.read_eq, K3.mem hb.1 (P.vs_notIoTW hb), w0.2.2 b hb.1 (P.vs_notPreW hb)]
          · rw [L.ks_base_eq, L.ks_base_eq, K3.1.1, w0.1]
  obtain ⟨hz2, kz⟩ := decDel_keep ar hK O ha2 hrun hL hlen hlk2 hd hdc2 hm3 hpv2 hnx2 hy hz
  refine ⟨hz2, ?_⟩
  -- `Ω` cut to the SC words
  have hrh0 : L.mem s (rhA (L := L) s) ≠ 0#u64 → L.mem s (scA (L.mem s (rhA (L := L) s))) ∈ K.heap.scs ∧
      InSC (L.mem s (scA (L.mem s (rhA (L := L) s)))) (K.heap.scBits (L.mem s (scA (L.mem s (rhA (L := L) s)))))
        (headA (L.mem s (scA (L.mem s (rhA (L := L) s))))) := fun h0 => by
    obtain ⟨-, hc, -⟩ := bxi_rh P.bxi h0
    obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact ⟨hc, by omega, by omega⟩
  have F0' := I.F0.shrink P.cscS rfl hrh0
  have F2' := F0'.frame I.w
  have rh0' : RhSc st {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b} s := fun h0 => by
    obtain ⟨-, hc, ha⟩ := bxi_rh P.bxi h0
    obtain ⟨hW', hΩ⟩ := bxi_scin P.bxi hc ha
    exact ⟨_, hW', fun b hb hin => ⟨hΩ b hb hin, _, hc, hin⟩⟩
  have rh2' := rh0'.frame F0' I.w
  have Q0 := QOK.of_sw F2' rh2' I.tm
  rw [hct] at Q0
  have ho' : ∀ b ∈ {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b}, ¬ SlotW K b := by
    rintro b ⟨-, c', hc', hin⟩
    exact P.sc_notSlot (P.hSc _ hc') hin
  have stm : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 → ¬ SlotW K (tdA (L.mem s2 (tmA (L := L) s2))) := fun h0 => by
    unfold tdA
    exact P.tcb_notSlot (I.tm h0) (by simp) (by simp)
  have srh : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → ¬ SlotW K (scA (L.mem s2 (rhA (L := L) s2))) ∧
      ¬ SlotW K (headA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))) ∧
      ¬ SlotW K (rtA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
        (L.rhead s2 (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2)))))) := fun h0 => by
    refine ⟨?_, ?_⟩
    · unfold scA; exact P.tcb_notSlot (F2'.rh h0).1 (by simp) (by simp)
    obtain ⟨zr, hW', hΩ⟩ := rh2' h0
    obtain ⟨h8, hmm, hfit⟩ := hW'.bounds
    obtain ⟨h96, -, -, hhd, -, hrt⟩ := hW'.inside
    obtain ⟨e1, e2, e3⟩ := hrt _ hW'.head_lt
    exact ⟨ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩),
      ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩)⟩
  have FIN := kz.fin hK O Q0 Hf.nd I.F.td I.F.rs stm srh
  have hcur3 : L.curW z.1 = L.curW s := kz.cur hK O
  have w3 : WritesIn st s2 z.1 (fun b => IoPW st s2 b ∨ SlotW K b) :=
    kz.1.mono fun b hb => hb.imp_left fun h => Or.inr (by rw [hct]; exact h)
  have Fz := F2'.frameE w3 hn2 (fun t ht k h1 h2 => P.tcb_notSlot ht (by omega) h2) ho'
  refine FinOK.of_sw hA (kz.1.1.trans I.k) (kz.1.2.1.trans I.cp) FIN.1 kz.2.1 Fz ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [hcur3]; exact hsw)
  · rw [hcur3]
    exact (kz.tcbF hK O (k := 3472#u64) (by simp) (by simp) (by simp)).trans hy2
  · rw [hcur3]; exact kz.2.2
  · rw [hcur3]; exact A0.ryl
  · rw [hcur3]; exact A0.rst
  · rw [hcur3]; exact A0.rfi
  · rw [hcur3]; exact A0.wnx
  · rw [hcur3]; exact A0.rin

end fin

section mv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- `IoPre.mvWr` for the checked store with slot `CAP0` writes. -/
theorem mvWrS {s : S} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hK : RegionOK K) (hA : IoLayA K) {c : U64}
    {lk : U64 → Prop} {m : U64 → U64} : IoWr st (WAll (OwnMap.PWs (L := L) K c lk m)) Z s :=
  have w := P.mvWr (c := c) (lk := lk) (m := m) hK hA
  ⟨fun o h1 h2 => OwnMap.wall_pw_pws (w.nd o h1 h2), fun r hr => OwnMap.wall_pw_pws (w.reg r hr),
    fun b hb hi => OwnMap.wall_pw_pws (w.ring b hb hi), OwnMap.wall_pw_pws w.cons⟩

/-- [W] (stpost gen 14) **The decode block on the checked store with slot `CAP0` writes** `gd st (IoRS s) (PWs …)`
(as `InvBlkW2`, with that store and its write set `WAll PWs`): what `move` of accepted runs needs besides the
program tree. Proved for the CNodeDelete-no-PTE arm by `invBlkGdW2_of`. -/
def InvBlkGdW2 (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (p : localinv.Plan)
    (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
      obj.Slot.cap st p.slot s2 = ok cap →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (gd st (IoRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) ar s2 a1
          info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (gd st (IoRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (gd st (IoRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))
          (IoRS (st := st) K Locks s) (WAll (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) ar s z.1 z.2.1

/-- (stpost gen 14) **`InvMoveW` from the decode block on the checked store with slot `CAP0` writes** (`PWs`) (I/O port's `io_move` route:
the accepted run on `gd`, then `OwnMap.run_gds_mguard` over the program tree `q`): `hA`; at each `Pre` state
[J] `hK` (`RegionOK`), [J] `hU` (`UserOK`), [J] `hLA` (`IoLayA`), `hPE`, [J] `hSeen`, [J] `hps`, [J] `hmA` (`m0`
agrees with the state on every TCB's `AFFINITY`); [P] `hp` (`IsProgOn` of the body, the `hpz` tree); [W] `hblk`. -/
theorem invMoveW_of2 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {m0 : U64 → U64} {P : S → Prop} (hK : ∀ s, P s → RegionOK K) (hU : ∀ s, P s → E2E.UserOK K)
    (hLA : ∀ s, P s → IoLayA K) (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hmA : ∀ s, P s → ∀ d, K.heap d = some .tcb → m0 (fld d OwnMap.oAFFINITY) = L.mem s (fld d OwnMap.oAFFINITY))
    {q : SProg Bool}
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q)
    (hblk : InvBlkGdW2 st ar p K Locks P) :
    InvMoveW st ar number p K Locks m0 P := by
  intro s a s1 a1 hE h
  have hg := inv_acc_gen2 (gS := gd st (IoRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))
    hA (hPE s hE) (mvWrS (hPE s hE) (hK s hE) (hLA s hE)) (hSeen s hE) (hps s hE)
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk => hblk s a info nx s1 s2 a1 buf length cap hE emi hc hl hk) h
  rw [inv_hp hp (Narrow.gd _ _ _) (AltOf.pre hE) a] at hg
  rw [inv_hp hp (Narrow.mguard _ _) (AltOf.pre hE) a]
  exact OwnMap.run_gds_mguard (hK s hE) (hU s hE) (hmA s hE) q hg

end mv

section arm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem nq_run {v : U64} (h : v = sched.TS_RESTART ∨ v = sched.TS_RUNNING) : ¬ OwnMap.QueuedState v := by
  rcases h with rfl | rfl <;> simp [OwnMap.QueuedState, sched.TS_RUNNING, sched.TS_RESTART]

/-- (stpost gen 14) **`InvBlkGdW2` for the CNodeDelete-no-PTE arm** at `Pre := SlJAt K ∧ InvQL` (`delAcc2`,
`delFin2` on `gd st (IoRS s) (PWs …)`), from [J] `hvs`, [J] `hcdt`, [J] `hz` (as `invBlkW2_of`). -/
theorem invBlkGdW2_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hvs : InvVsJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s))
    (hcdt : InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, SlJAt (L := L) K s → (0#u64) ∉ K.slots) :
    InvBlkGdW2 st ar p K Locks (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hl hcap y hy
  have hqf := hE.2.1
  have PE := hqf.1.1.1
  have hK := hE.1.regionOK
  have hLA := hE.1.ioLayA
  have E := delEnt_of (P := fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s) hE hqf hvs hcdt
    (hz s hE.1)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsK, -⟩ := del_core hqf
  have hlbl := (hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  have hlen := len_ge2 (hE.2.2 (L.curW s) info (cur_thread_ok s) emi) hl
  rw [hlbl] at hy ⊢
  have hW := mvWrS PE hK hLA (c := L.cpu s) (lk := Locks s) (m := L.mem s)
  have hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
      (16 ≤ o.val ∨ (¬ TcbSlot K q ∧ NullOrFrame (L.mem s q))) →
      WAll (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)) (core.num.U64.wrapping_add q o) := by
    intro q o hq _ ho h8 h8' _
    obtain ⟨q8, qf⟩ := PE.lay.slot8 q hq
    have hv := slot_word_val qf ho
    have hr := PE.lay.slotw q hq _ (slot_inW qf ho)
    have hne : core.num.U64.wrapping_add q o ≠ q := fun e => by
      have := congrArg UScalar.val e; rw [hv] at this; omega
    have ha : Aligned (core.num.U64.wrapping_add q o) := by unfold Aligned; rw [hv]; omega
    exact fun _ _ => Or.inl (Or.inl ⟨ha, OwnMap.nondec_slotw hK hr hne⟩)
  have hw0 : ∀ q, q ∈ K.slots → Locks s q → ¬ TcbSlot K q → NullOrFrame (L.mem s q) →
      ∀ x, (gd st (IoRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))).write x q 0#u64
        = st.write x q 0#u64 :=
    fun q hq hl hT hn x => OwnMap.gds_write_cap0 hq hT hl hn OwnMap.nof_zero
  have hS0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) := by
    refine ⟨?_, fun hq => absurd hq ?_⟩
    · rw [← OwnMap.affA_fld]; exact PE.curAff
    · rw [← OwnMap.stA_fld]; exact nq_run PE.run
  have hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      SWr (gd st (IoRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st
        (L.curW s) v :=
    fun v hv X => OwnMap.gds_write_state (PE.hT _ PE.cT) hS0 (fun hq => absurd hq (nq_run hv))
  obtain ⟨hdec, hrep⟩ := delAcc2 (gS := gd st (IoRS (st := st) K Locks s)
    (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) hA PE hW hwS hw0 hst E hsK hlen
    (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  obtain ⟨h1, h2⟩ := delFin2 (gS := gd st (IoRS (st := st) K Locks s)
    (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) hA PE hW (hst _ (Or.inr rfl)) E hsK hlen
    (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

end arm

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (stpost gen 14) **The CNodeDelete-no-PTE local path with `move` proved** (`Q := InvQL`): `inv_pathsKF` with
`hmv` from `invMoveW_of2` + `invBlkGdW2_of` (the checked store with slot `CAP0` writes). Premises: `hA`, [P] `hm`,
[J] `hvs : InvVsJ`, [J] `hcdt : InvCdtJ`, [J] `hz`, [J] `huf`, `hpz` ([P] IsProgOn ∧ [W] NoZero ∧ [W] InvRoW). -/
noncomputable def inv_pathsKF2 (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st)
    (hvs : ∀ K m, InvVsJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s))
    (hcdt : ∀ K m, InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s))
    (hz : ∀ K s, SlJAt (L := L) K s → (0#u64) ∉ K.slots)
    (huf : ∀ K m s b v, SlJAt (L := L) K s → InvQL st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ InvQL st Cs Ω Sg Ac Locks p K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∀ K m, ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s) (IoRS (st := st) K Locks)
        (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s)) :
    E2E.Paths Unit :=
  inv_pathsKD ar hA number p hm (InvQL st Cs Ω Sg Ac Locks p) (fun _ _ _ _ hq => hq.1.1.1.1)
    (fun K m => invAccW_of2 hA (fun _ h => h.2.1.1.1.1)
      (fun s h => invSeen_of (fun K _ s hJ _ => hz K s hJ) K m s h.1 h.2.1)
      (fun s h => invPs_of K m s h.1 h.2.1) (invBlkW2_of hA (hvs K m) (hcdt K m) (hz K)))
    (fun K m s hJ hq => invSeen_of (fun K _ s hJ _ => hz K s hJ) K m s hJ hq.1)
    (fun K m => invMoveW_of2 hA (fun _ h => h.1.regionOK) (fun _ h => h.1.userOK) (fun _ h => h.1.ioLayA)
      (fun _ h => h.2.1.1.1.1) (fun s h => invSeen_of (fun K _ s hJ _ => hz K s hJ) K m s h.1 h.2.1)
      (fun s h => invPs_of K m s h.1 h.2.1) (fun _ h => h.2.1.1.1.2) (hpz K m).choose_spec.1
      (invBlkGdW2_of hA (hvs K m) (hcdt K m) (hz K)))
    huf hpz

/-- (stpost gen 14) **`StartAt` of `inv_pathsKF2` at a chain state** (as `inv_pathsKD_startAt`; `hq : InvQL …` at
`σ`, its plan part from `loc_chain_all` clause 8's input `hp` via `invQ_intro` / `invLk_of_plan`). -/
theorem inv_pathsKF2_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st)
    (hvs : ∀ K m, InvVsJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s))
    (hcdt : ∀ K m, InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s))
    (hz : ∀ K s, SlJAt (L := L) K s → (0#u64) ∉ K.slots)
    (huf : ∀ K m s b v, SlJAt (L := L) K s → InvQL st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ InvQL st Cs Ω Sg Ac Locks p K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∀ K m, ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s) (IoRS (st := st) K Locks)
        (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {A3 : Type} {Rc : S → A3 → Fl4Spec.State Unit → Prop}
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), Rc σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : Rc σ a3 τ) (a : A) (hq : InvQL st Cs Ω Sg Ac Locks p K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (inv_pathsKF2 ar hA number p hm hvs hcdt hz huf hpz () K m hK hU) c hs μ
      ((inv_pathsKF2 ar hA number p hm hvs hcdt hz huf hpz () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨h7 σ a3 τ hR, hq⟩, hc, hl, hμ, rfl⟩

end paths

end Fl4Proofs.P2.PathObl

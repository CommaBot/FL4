/-
# P2 (line stpost, generation 13): the decode block of the CNodeDelete-no-PTE arm on the guarded store

`InvBlkW` (gen 12) quantifies the invoked slot's `cap` (and the message length) freely, although the accepted run
reads `cap` from the plan's slot (`obj.Slot.cap st p.slot s2`); for an arbitrary `cap` (an Untyped: retype) it is
false. `InvBlkW2` is `InvBlkW` with that read and the length's computation as hypotheses; the gen-12 chain is
redone for it (`invTail.guard2`, `…guard_acc2`, `inv_acc_gen2`, `invAccW_of2`), and `InvBlkW2` is **proved** for
the CNodeDelete-no-PTE arm:

* guarded-store leaves for the CDT: `obj.Slot.prev.guard`, `obj.Slot.next.guard`, `obj.Slot.first_badged.guard`,
  `obj.Slot.set_next.guard`, `obj.Slot.set_first_badged.guard`;
* `cdt.is_final_capability_with_cap.guard`, `finCap_frame_any`, `finImm_frame_any`,
  `cdt.finalise_slot_immediate.guard_frame`, `cdt.empty_slot.guard_null`, `cdt.delete.guard_frame`;
* `cspace.lookup_target_slot.guardM` (the masked walk from the invoked CNode cap), `invRep.guard_ok`;
* **`delAcc`**: at an entry with `IoPre` and `DelEnt`, after the prefix and checks (`InvChk`), the Delete decode and
  the reply run on any store reading `IoRS s` and writing a superset of `IoWS s` as on `st`;
* with `InvBlkFin.delFin` (reply `Ok ()`, `FinOK`): **`invBlkW2_of`** (`InvBlkW2` at `Pre := SlJAt K ∧ InvQL`).

`InvQL` = `InvQF ∧ InvLen` (the message length is at least 2). **Finding**: a truncated Delete (`length < 2`) is
accepted by `localinv.plan`, and its error reply (`reply_error`, `KERNEL_INVOCATION_REPORT_ERROR_IPC`) reads and
writes a word of the caller's IPC buffer — a user word, outside `IoRS` / `IoWS`, so `acc` is false for it; the arm
is cut to `length ≥ 2` (`InvLen`, a register word, stable under user writes).

**Finding (move)**: `InvBlkGdW` (`move` via p2sl's checked store `gd st (IoRS s) (PW …)`) is false for this arm:
`OwnMap.PW` allows no write of a capability slot's `CAP0` (a `DecW` word), and `empty_slot` clears `dest`'s `CAP0`
(Frame → Null, the owner unchanged since both are `NullOrFrame`). `hmv` stays a named premise here.

* **`inv_pathsKF`** / `inv_pathsKF_startAt`: the frame-cap invocation path at `Q := InvQL` with `acc`, `dec_alt`,
  `read_aligned` discharged and `hSeen`, `hps` proved (`invSeen_of`, `invPs_of`); premises: `hA`, [P] `hm`, [J]
  `hvs : InvVsJ` (gen 14; gen 13 had the false `InvMapJ`), [J] `hcdt : InvCdtJ`, [J] `hz` (`0 ∉ K.slots`), [W] `hmv` (`InvMoveW`), [J] `huf`, `hpz`
  ([P] IsProgOn ∧ [W] NoZero ∧ [W] InvRoW, unchanged shape; the hpzg line).

No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvSeen
import Fl4Proofs.P2.InvBlkFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

/-! ## Guarded-store leaves and the deletion -/

section g
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

theorem obj.Slot.prev.guard (self : obj.Slot) (s : S) (h : R (core.num.U64.wrapping_add self layout.cte.PREV)) :
    obj.Slot.prev gS self s = obj.Slot.prev st self s := by
  unfold obj.Slot.prev
  simp only [lift, bind_ok]
  rw [gst_read h]

theorem obj.Slot.next.guard (self : obj.Slot) (s : S) (h : R (core.num.U64.wrapping_add self layout.cte.NEXT)) :
    obj.Slot.next gS self s = obj.Slot.next st self s := by
  unfold obj.Slot.next
  rw [obj.Slot.next_word.guard self s h]

theorem obj.Slot.first_badged.guard (self : obj.Slot) (s : S)
    (h : R (core.num.U64.wrapping_add self layout.cte.NEXT)) :
    obj.Slot.first_badged gS self s = obj.Slot.first_badged st self s := by
  unfold obj.Slot.first_badged
  rw [obj.Slot.next_word.guard self s h]

theorem obj.Slot.set_next.guard (self : obj.Slot) (s : S) (n : obj.Slot)
    (hr : R (core.num.U64.wrapping_add self layout.cte.NEXT)) (hw : W (core.num.U64.wrapping_add self layout.cte.NEXT)) :
    obj.Slot.set_next gS self s n = obj.Slot.set_next st self s n := by
  unfold obj.Slot.set_next
  rw [obj.Slot.next_word.guard self s hr]
  simp only [lift, bind_ok, gst_write hw]

theorem obj.Slot.set_first_badged.guard (self : obj.Slot) (s : S) (v : Bool)
    (hr : R (core.num.U64.wrapping_add self layout.cte.NEXT)) (hw : W (core.num.U64.wrapping_add self layout.cte.NEXT)) :
    obj.Slot.set_first_badged gS self s v = obj.Slot.set_first_badged st self s v := by
  unfold obj.Slot.set_first_badged
  rw [obj.Slot.next_word.guard self s hr]
  simp only [lift, bind_ok, gst_write hw]

theorem slot_prev_ok (s : S) (q : U64) :
    obj.Slot.prev st q s = ok (L.mem s (core.num.U64.wrapping_add q layout.cte.PREV)) := by
  unfold obj.Slot.prev; simp only [lift, bind_ok, L.read_eq]

theorem slot_next_ok (s : S) (q : U64) : ∃ nx, obj.Slot.next st q s = ok nx := by
  unfold obj.Slot.next obj.Slot.next_word obj.sext48
  simp only [lift, bind_ok, L.read_eq]
  split <;> simp only [bind_ok] <;> exact ⟨_, rfl⟩

/-- **`is_final_capability_with_cap`**: the slot's CDT links and the neighbours' cap words. -/
theorem cdt.is_final_capability_with_cap.guard (s : S) (slot : obj.Slot) (c : capability.Cap)
    (r16 : R (core.num.U64.wrapping_add slot layout.cte.PREV)) (r24 : R (core.num.U64.wrapping_add slot layout.cte.NEXT))
    (hpv : L.mem s (core.num.U64.wrapping_add slot layout.cte.PREV) ≠ 0#u64 →
      R (L.mem s (core.num.U64.wrapping_add slot layout.cte.PREV)) ∧
      R (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add slot layout.cte.PREV)) 8#u64))
    (hnx : ∀ nx, obj.Slot.next st slot s = ok nx → nx ≠ 0#u64 → R nx ∧ R (core.num.U64.wrapping_add nx 8#u64)) :
    cdt.is_final_capability_with_cap gS s slot c = cdt.is_final_capability_with_cap st s slot c := by
  unfold cdt.is_final_capability_with_cap
  rw [obj.Slot.prev.guard (gS := gS) slot s r16, slot_prev_ok, obj.Slot.next.guard (gS := gS) slot s r24]
  obtain ⟨nx, enx⟩ := slot_next_ok (st := st) s slot
  rw [enx]
  simp only [bind_ok, obj.Slot.is_null]
  by_cases h0 : L.mem s (core.num.U64.wrapping_add slot layout.cte.PREV) = 0#u64
  · by_cases h1 : nx = 0#u64
    · simp only [h0, h1, decide_true, ↓reduceIte, bind_ok, Bool.false_eq_true]
    · simp only [h0, h1, decide_true, decide_false, ↓reduceIte, bind_ok, Bool.false_eq_true]
      rw [obj.Slot.cap.guard (gS := gS) nx s (hnx nx enx h1).1 (hnx nx enx h1).2]
  · rw [obj.Slot.cap.guard (gS := gS) _ s (hpv h0).1 (hpv h0).2]
    by_cases h1 : nx = 0#u64
    · simp only [h0, h1, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
    · simp only [h0, h1, decide_false, ↓reduceIte, Bool.false_eq_true]
      rw [obj.Slot.cap.guard (gS := gS) nx s (hnx nx enx h1).1 (hnx nx enx h1).2]

end g

section any
variable {S : Type} {A : Type} (ar : machine.Arch A)

/-- `finalise_cap` of an unmapped (or ASID 0) non-device non-EPT frame cap, on any store: no access. -/
theorem finCap_frame_any (m : machine.Store S) {x : S} {a : A} {fp rt asid va : U64}
    {mp fin : Bool} (hm : FrNo m ar x mp asid va fp) :
    objects.finalise_cap m ar x a (.Frame fp .Small rt false mp false asid va) fin false = ok ((.Null, .Null), x, a) := by
  unfold objects.finalise_cap objects.finalise_cap_object
  simp only [bind_ok]
  rcases hm with rfl | rfl | hu
  · cases fin <;> simp
  · cases mp <;> cases fin <;> simp
  · cases mp <;> by_cases hA : asid = 0#u64 <;> cases fin <;> simp [hA, hu]

set_option maxHeartbeats 4000000 in
/-- `finalise_slot_immediate` on a slot holding such a frame cap, on any store whose finality check returns. -/
theorem finImm_frame_any (m : machine.Store S) {x : S} {a : A} {slot fp rt asid va : U64} {mp fin : Bool}
    (hc : obj.Slot.cap m slot x = ok (.Frame fp .Small rt false mp false asid va))
    (hm : FrNo m ar x mp asid va fp)
    (hf : cdt.is_final_capability_with_cap m x slot (.Frame fp .Small rt false mp false asid va) = ok fin) :
    cdt.finalise_slot_immediate m ar x a slot = ok (.Ok { success := true, cleanup := .Null }, x, a) := by
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  rw [loop]
  have hfu : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨v, hv, -⟩ := spec_ex_fd (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64)
    (by simp [layout.WALK_FUEL, U64.rMax]))
  have hb : cdt.finalise_slot_immediate_loop.body m ar slot x a layout.WALK_FUEL =
      ok (ControlFlow.done (.Ok { success := true, cleanup := .Null }, x, a)) := by
    unfold cdt.finalise_slot_immediate_loop.body
    simp only [hfu, ↓reduceIte, hv, bind_ok, hc, capability.Cap.is_null, Bool.false_eq_true, hf,
      finCap_frame_any ar m hm, cdt.cap_removable, uncurry_apply_pair]
  dsimp only
  rw [hb]
  simp only [bind_ok]

end any

section g2
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **`finalise_slot_immediate` of a frame slot on the guarded store**, run-relative. -/
theorem cdt.finalise_slot_immediate.guard_frame {x : S} {a : A} {slot fp rt asid va : U64} {mp : Bool}
    (hc : obj.Slot.cap st slot x = ok (.Frame fp .Small rt false mp false asid va)) (hm : FrNo st ar x mp asid va fp)
    (hmg : FrNo gS ar x mp asid va fp)
    (r0 : R slot) (r8 : R (core.num.U64.wrapping_add slot 8#u64))
    (hfg : cdt.is_final_capability_with_cap gS x slot (.Frame fp .Small rt false mp false asid va) =
      cdt.is_final_capability_with_cap st x slot (.Frame fp .Small rt false mp false asid va))
    {y : core.result.Result cdt.Finalised error.Exc × S × A}
    (h : cdt.finalise_slot_immediate st ar x a slot = ok y) :
    cdt.finalise_slot_immediate gS ar x a slot = ok y := by
  have ey := finImm_frame_keep ar hc hm h
  subst ey
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop at h
  rw [loop] at h
  obtain ⟨cf, hb, -⟩ := bind_eq_ok h
  have hfu : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨v, hv, -⟩ := spec_ex_fd (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64)
    (by simp [layout.WALK_FUEL, U64.rMax]))
  unfold cdt.finalise_slot_immediate_loop.body at hb
  simp only [hfu, ↓reduceIte, hv, bind_ok, hc, capability.Cap.is_null, Bool.false_eq_true] at hb
  obtain ⟨fin, efin, -⟩ := bind_eq_ok hb
  exact finImm_frame_any ar gS (by rw [obj.Slot.cap.guard (gS := gS) slot x r0 r8]; exact hc) hmg (by rw [hfg]; exact efin)

/-- **`empty_slot` with a null cleanup on the guarded store**, run-relative: the slot's words read and written, the
previous slot's `NEXT` word, the next slot's `PREV` and `NEXT` words. -/
theorem cdt.empty_slot.guard_null {x : S} {a : A} {slot : obj.Slot} {y : S × A}
    (r0 : R slot) (r8 : R (core.num.U64.wrapping_add slot 8#u64))
    (r16 : R (core.num.U64.wrapping_add slot layout.cte.PREV)) (r24 : R (core.num.U64.wrapping_add slot layout.cte.NEXT))
    (w0 : W slot) (w8 : W (core.num.U64.wrapping_add slot 8#u64)) (w16 : W (core.num.U64.wrapping_add slot 16#u64))
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
  rw [obj.Slot.clear.guard (gS := gS) slot s2 w0 w8 w16 w24]
  exact id

/-- **Deleting a frame slot on the guarded store**, run-relative (given `empty_slot` transfers). -/
theorem cdt.delete.guard_frame {x : S} {a : A} {dest fp rt asid va : U64} {mp : Bool}
    (hc : obj.Slot.cap st dest x = ok (.Frame fp .Small rt false mp false asid va)) (hm : FrNo st ar x mp asid va fp)
    (hmg : FrNo gS ar x mp asid va fp)
    (r0 : R dest) (r8 : R (core.num.U64.wrapping_add dest 8#u64))
    (hfg : cdt.is_final_capability_with_cap gS x dest (.Frame fp .Small rt false mp false asid va) =
      cdt.is_final_capability_with_cap st x dest (.Frame fp .Small rt false mp false asid va))
    (hes : ∀ y', cdt.empty_slot st ar x a dest .Null = ok y' → cdt.empty_slot gS ar x a dest .Null = ok y')
    {y : core.result.Result Unit error.Exc × S × A}
    (h : cdt.delete st ar x a dest true = ok y) : cdt.delete gS ar x a dest true = ok y := by
  unfold cdt.delete at h ⊢
  simp only [↓reduceIte] at h ⊢
  obtain ⟨y1, hf, -⟩ := bind_eq_ok h
  have ey := finImm_frame_keep ar hc hm hf
  subst ey
  rw [cdt.finalise_slot_immediate.guard_frame ar hc hm hmg r0 r8 hfg hf]
  rw [hf] at h
  simp only [bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch] at h ⊢
  revert h
  exact tr_bind (fun y' e _ => hes y' e) (fun _ _ h => h)

/-- **The target lookup from a CNode cap on the guarded store** (the masked walk), run-relative. -/
theorem cspace.lookup_target_slot.guardM {s : S} {cp cr cg cgb cptr depth : U64} {dest : obj.Slot}
    (C : U64 → U64 → Prop) (hRc : WalkRc (st := st) R s C) (hcl : WalkCl (st := st) s C) (hC : C cp cr)
    (hRd : R dest ∧ R (core.num.U64.wrapping_add dest 8#u64))
    (h : cspace.lookup_target_slot st s (.CNode cp cr cg cgb) cptr depth = ok (.Ok dest)) :
    cspace.lookup_target_slot gS s (.CNode cp cr cg cgb) cptr depth = ok (.Ok dest) := by
  unfold cspace.lookup_target_slot cspace.lookup_slot_for_cnode_op at h ⊢
  simp only [bind_ok, ↓reduceIte] at h ⊢
  by_cases d1 : depth < 1#u64
  · rw [if_pos d1] at h; simp at h
  rw [if_neg d1] at h ⊢
  by_cases d2 : depth > cspace.WORD_BITS
  · rw [if_pos d2] at h; simp at h
  rw [if_neg d2] at h ⊢
  obtain ⟨res, eres, hl⟩ := bind_eq_ok h
  have hRf : ∀ x, res = .Ok x → R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64) := by
    intro x hx
    subst hx
    simp only at hl
    by_cases hb : (x.bits_left != 0#u64) = true
    · rw [if_pos hb] at hl; simp at hl
    · rw [if_neg hb] at hl
      have e := ok_inj_ff hl
      simp only [core.result.Result.Ok.injEq] at e
      rw [e]; exact hRd
  rw [rab.guardM C hRc hcl (fun p r gs g e => by cases e; exact hC) hRf eres]
  simp only [bind_ok]
  exact hl

/-- **The reply after an `Ok` decode on the guarded store**, run-relative: the caller's `STATE`, the reply
registers, and `set_thread_state RUNNING` (its node words and the current SC's `REFILL_MAX`, at the state after the
reply). -/
theorem invRep.guard_ok {x : S} {a : A} {t : U64} {z : S × A × core.result.Result Unit error.Exc}
    (rst : R (stA t)) (wst : W (stA t)) (rsc : R (scA t)) (riq : R (inqA t))
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
    rw [sched.set_thread_state.guard (gS := gS) s5 t _ (h5 s5 es5).1 wst rst rsc (h5 s5 es5).2 riq]
    exact id
  · rw [if_neg hi] at et1 ⊢; exact et1

end g2

/-! ## The Delete decode and its reply on the guarded store -/

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayout}

theorem notTcbSlot_of {Cs : Set U64} {s : S} {q : U64} (h : OutsideObjs st K.heap.tcbs Cs s q) : ¬ TcbSlot K q := by
  rintro ⟨t, ht, h1, h2⟩
  rcases h.2.1 t ht with e | e <;> omega

theorem wadd_zero {q : U64} (hq : q.val + 32 ≤ 2 ^ 64) : core.num.U64.wrapping_add q 0#u64 = q := by
  apply UScalar.eq_of_val_eq; rw [slot_word_val hq (by simp)]; simp

set_option maxHeartbeats 2000000 in
/-- (stpost gen 13) **The Delete decode and its reply on any store reading `IoRS s` and writing a superset of
`IoWS s`** run as on `st` (run-relative), at an entry with `IoPre` and `DelEnt`, after the prefix and checks
(`InvChk`), for a message of length at least 2. -/
theorem delAcc {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s) (hWs : ∀ b, IoWS (st := st) K Locks s b → W b)
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
  have dW : ∀ o : U64, o.val < 32 → o.val % 8 = 0 → W (core.num.U64.wrapping_add dest o) :=
    fun o ho h8 => hWs _ ((P.lockSlot hd hLd' ho h8).2 (Or.inr ⟨hnT, hnf⟩))
  have r0 : IoRS (st := st) K Locks s dest := by have := dR 0#u64 (by simp) (by simp); rwa [e0] at this
  have w0' : W dest := by have := dW 0#u64 (by simp) (by simp); rwa [e0] at this
  have nR : ∀ q, q ∈ K.slots → Locks s q → ∀ o : U64, o.val < 32 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add q o) := fun q hq hl o ho h8 =>
    (P.lockSlot hq hl ho h8).1
  have nW : ∀ q, q ∈ K.slots → Locks s q → ∀ o : U64, o.val < 32 → o.val % 8 = 0 → 16 ≤ o.val →
      W (core.num.U64.wrapping_add q o) := fun q hq hl o ho h8 h16 =>
    hWs _ ((P.lockSlot hq hl ho h8).2 (Or.inl h16))
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
    refine cdt.empty_slot.guard_null ar r0 hRd.2 r16 r24 w0' (dW 8#u64 (by simp) (by simp))
      (dW 16#u64 (by simp) (by simp)) (dW 24#u64 (by simp) (by simp)) (fun h0 => ?_) (fun nx e h0 => ?_) he
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
    rw [sched.set_thread_state.guard (gS := gS) s2 (L.curW s) _ (hN s2 hnd2) (hWs _ rst.2) rst.1 rsc hmx2 riq]
    refine tr_bind_same (fun s3 hs3 => ?_)
    exact hdel s3 hs3 y
  · intro z hz'
    obtain ⟨hy1, kx⟩ := cnDel_keep ar hK O ha2 hrun hL hlen hlk2 hd hdc2 hfrS hpv2 hnx2 hy
    obtain ⟨r, x, a2⟩ := y
    simp only at hy1 kx hz' ⊢
    subst hy1
    have Fx := kx.sched hK O
    refine invRep.guard_ok (gS := gS) rst.1 (hWs _ rst.2) rsc riq (hW.reg _ rB384) (hW.reg _ rM384) ?_ hz'
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

/-! ## `InvBlkW2` and the `acc` chain for it -/

section g3
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

set_option maxHeartbeats 1000000 in
/-- **The accepted frame-cap invocation tail on the guarded store** (`hblk`: the decode block). -/
theorem invTail.guard2 {A : Type} (ar : machine.Arch A) {s s' : S} {a a' : A} {t : U64}
    {info : msginfo.MessageInfo} {p : localinv.Plan}
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hnx : R (regA t layout.reg.NEXT_IP)) (hfi : W (regA t layout.reg.FAULT_IP))
    (hmid : ∀ nx s1 s2 a1, obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) → InvMid (L := L) R s s2 t)
    (hsh : ∀ x, localinv.Plan.still_holds gS p x = localinv.Plan.still_holds st p x)
    (hps : R p.slot ∧ R (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ nx s1 s2 a1 buf length cap, InvChk st ar s a t p nx s1 s2 a1 →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
        obj.Slot.cap st p.slot s2 = ok cap →
      ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
        syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
        ∀ z, invRep st t y.2.1 y.2.2 y.1 = ok z →
          invRep gS t y.2.1 y.2.2 y.1 = ok z ∧ z.2.2 = core.result.Result.Ok () ∧
          FinOK (L := L) gS R W ar s z.1 z.2.1)
    (h : invTail st ar s a t info p = ok (true, s', a')) :
    invTail gS ar s a t info p = ok (true, s', a') := by
  unfold invTail at h ⊢
  revert h
  refine tr_bind_same (fun b _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  refine tr_bind (fun x hx _ => by rw [obj.Tcb.reg.guard t s _ hnx]; exact hx) (fun nx enx => ?_)
  simp only [lift, bind_ok]
  refine tr_bind (fun x hx _ => by rw [obj.Tcb.set_reg.guard t s _ _ hfi]; exact hx) (fun s1 es1 => ?_)
  have e1 : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have k1 : L.ksb s1 = L.ksb s := by rw [e1, L.ksb_wr]
  have c1 : L.cpu s1 = L.cpu s := by rw [e1, LawfulStore.cpu_wr]
  refine tr_bind (fun x hx _ => by
      rw [sched.update_timestamp.guard ar s1 a (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2]; exact hx)
    (fun x eu => ?_)
  obtain ⟨s2, a1⟩ := x
  simp only [uncurry_apply_pair]
  have M := hmid nx s1 s2 a1 enx es1 eu
  have nd2 := nd_at hNd M.k M.c
  have Mc := M.cur
  subst Mc
  rw [sched.cur_sc.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.action.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1]
  refine tr_bind_same (fun i3 ei3 => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun hi3 => ?_)
  rw [obj.Tcb.yield_to.guard (gS := gS) (L.curW s2) s2 M.yld]
  refine tr_bind_same (fun i4 ei4 => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun hi4 => ?_)
  rw [sched.consumed.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1]
  refine tr_bind_same (fun i5 _ => ?_)
  have ecsc' : csc = L.cscW s2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2)] at ecsc; exact (ok_inj_ff ecsc).symm
  subst ecsc'
  rw [sporadic.sufficient.guard (gS := gS) ar s2 a1 _ i5 M.rh]
  refine tr_bind_same (fun b1 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [fastpath.schedulable_here.guard (gS := gS) s2 (L.curW s2) (nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
    (nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1 (nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).1
    M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
  refine tr_bind_same (fun b2 eb2 => ?_)
  beta_reduce
  refine tr_ite (fun hb2 => ?_) (fun _ h => h)
  rw [hsh s2]
  refine tr_bind_same (fun b3 eb3 => ?_)
  beta_reduce
  refine tr_ite (fun hb3 => ?_) (fun _ h => h)
  have C : InvChk st ar s a (L.curW s2) p nx s1 s2 a1 := by
    simp only [bne_iff_ne, ne_eq, not_not] at hi3 hi4
    subst hi3 hi4 hb2 hb3
    exact ⟨enx, es1, eu, ei3, ei4, eb2, eb3⟩
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s2)
  rw [msg.lookup_ipc_buffer.guard (gS := gS) s2 false (L.curW s2) hbsl M.ib (M.bs _ hbsl).1 (M.bs _ hbsl).2]
  refine tr_bind_same (fun buf _ => ?_)
  refine tr_bind_same (fun length elen => ?_)
  rw [obj.Slot.cap.guard (gS := gS) p.slot s2 hps.1 hps.2]
  refine tr_bind_same (fun cap ecap => ?_)
  refine tr_bind (fun y ey _ => (hblk nx s1 s2 a1 buf length cap C elen ecap y ey).1) (fun y ey => ?_)
  have B := (hblk nx s1 s2 a1 buf length cap C elen ecap y ey).2
  obtain ⟨r, s3, a2⟩ := y
  simp only [uncurry_apply_pair]
  refine tr_bind (fun z ez _ => (B z ez).1) (fun z ez => ?_)
  obtain ⟨-, hr1, F⟩ := B z ez
  obtain ⟨s4, a3, r1⟩ := z
  dsimp only at hr1 F
  subst hr1
  simp only [uncurry_apply_pair]
  rw [syscall.after_invocation.ok_eq, syscall.after_invocation.ok_eq]
  simp only [bind_ok, uncurry_apply_pair]
  rw [syscall.finish.guard_resume ar s4 a3 (nd_at hNd F.k F.c) F.nd F.td F.rs F.ha F.hsw F.hfr F.hact F.hvc]
  exact fun h => h


/-- **The accepted frame-cap invocation local path on the guarded store ends as the real run.** -/
theorem syscall.handle_invocation_local.guard_acc2 {A : Type} (ar : machine.Arch A) {s s' : S} {a a' : A}
    {number : I64} {p : localinv.Plan}
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hmi : R (regA (L.curW s) layout.reg.MSG_INFO))
    (hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hnx : R (regA (L.curW s) layout.reg.NEXT_IP)) (hfi : W (regA (L.curW s) layout.reg.FAULT_IP))
    (hmid : ∀ info nx s1 s2 a1, msg.msg_info st s (L.curW s) = ok info →
      obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) → InvMid (L := L) R s s2 (L.curW s))
    (hsh : ∀ x, localinv.Plan.still_holds gS p x = localinv.Plan.still_holds st p x)
    (hps : R p.slot ∧ R (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ info nx s1 s2 a1 buf length cap, msg.msg_info st s (L.curW s) = ok info →
      InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
        obj.Slot.cap st p.slot s2 = ok cap →
      ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
        syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
        ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
          invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧ z.2.2 = core.result.Result.Ok () ∧
          FinOK (L := L) gS R W ar s z.1 z.2.1)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local gS ar s a number p = ok (true, s', a') := by
  rw [handle_invocation_local_eq] at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := gS) s (hNd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [msg.msg_info.guard (gS := gS) s _ hmi]
  refine tr_bind_same (fun info emi => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard (gS := gS) _ s hfl]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  exact tr_ite (fun _ h => h) (fun _ ht => invTail.guard2 ar hNd hnx hfi
    (fun nx s1 s2 a1 e1 e2 e3 => hmid info nx s1 s2 a1 emi e1 e2 e3) hsh hps
    (fun nx s1 s2 a1 buf length cap hc hl hk => hblk info nx s1 s2 a1 buf length cap emi hc hl hk) ht)


end g3

section acc2
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- [W] (stpost gen 13) **The decode block, with the invoked slot's cap and the message length as the run reads
them** (`InvBlkW` with the hypotheses `obj.Slot.cap st p.slot s2 = ok cap` and the length's computation, which the
accepted run supplies): on `guard st (IoRS s) (IoWS s)` the decode and the reply run as on `st`, the reply is
`Ok ()`, and `FinOK` holds after it. Proved for the CNodeDelete-no-PTE arm by `invBlkW2_of`. -/
def InvBlkW2 (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (p : localinv.Plan)
    (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
      obj.Slot.cap st p.slot s2 = ok cap →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) ar s2 a1
          info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s))
          (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s) ar s z.1 z.2.1

/-- **The accepted run on a guarded store `gS` reading `IoRS s` as `st` and writing a set `W` the prefix's words lie
in (`IoWr`)**, from the entry facts, [J] `hSeen`, [J] `hps` and the decode block `hblk` on `gS`. -/
theorem inv_acc_gen2 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {s s' : S} {a a' : A} {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)]
    [GWr gS st W] (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hW : IoWr st W Z s)
    (hSeen : ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : IoRS (st := st) K Locks s p.slot ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ info nx s1 s2 a1 buf length cap, msg.msg_info st s (L.curW s) = ok info →
      InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
        obj.Slot.cap st p.slot s2 = ok cap →
      ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
        syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
        ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
          invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧ z.2.2 = core.result.Result.Ok () ∧
          FinOK (L := L) gS (IoRS (st := st) K Locks s) W ar s z.1 z.2.1)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local gS ar s a number p = ok (true, s', a') := by
  obtain ⟨info, -, -, -, ht⟩ := handle_inv_inv h
  obtain ⟨nx0, s10, s20, a10, -, -, es10, eu0, -, -, -, hh0, -⟩ := invTail_inv ht
  have hsc2 := (here_facts hh0).sc
  have w := prefix_writes ar hA P.tp P.np P.cT es10 eu0
  have e1 : L.mem s20 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (field_aligned P.tA (by simp) (by simp)) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s := (P.hcsc (by rw [← e1]; exact hsc2)).symm
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  refine syscall.handle_invocation_local.guard_acc2 (gS := gS) ar (P.ent (Locks := Locks) hW).acc.nd
    (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1
    (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
    (P.reg (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1 (hW.reg _ (by simp [layout.reg.FAULT_IP]))
    ?_ (fun x => still_holds_congr p x (fun w hw => GRd.read (hSeen w hw) x)) hps hblk h
  intro info nx s1 s2 a1 emi enx es1 eu
  have M2 := io_hmid' (a := a) ar hA hq.tcbs (hq.nodes _ hq.cur) hq.cur hq.curT
    (P.mid (Locks := Locks) (P.ioWr (Locks := Locks)) hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2) (hd hX.cur)
    (fun h0 => ⟨(bxi_rh P.bxi h0).1, hd (bxi_rh P.bxi h0).2.1⟩) info nx _ s2 a1 emi enx es1 eu
  exact ⟨M2.k, M2.c, M2.cur, M2.yld, M2.rh, M2.td, M2.rs, M2.dt, M2.cd, M2.af, M2.dom, M2.iok.1.sc, M2.iok.1.inq,
    M2.iok.1.ib, M2.iok.1.bs⟩


/-- (stpost gen 13) **`InvAccW` from the decode block** (`InvBlkW2`): `hA`, and at each `Pre` state `hPE` (`IoPre`), [J] `hSeen`
(the seen words in `IoRS`), [J] `hps` (the invoked slot's cap words in `IoRS`), and [W] `hblk : InvBlkW`. -/
theorem invAccW_of2 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : InvBlkW2 st ar p K Locks P) :
    InvAccW st ar number p K Locks P := fun s a _ _ hE h =>
  inv_acc_gen2 hA (hPE s hE) ((hPE s hE).ioWr (Locks := Locks)) (hSeen s hE) (hps s hE)
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk => hblk s a info nx s1 s2 a1 buf length cap hE emi hc hl hk) h

end acc2

/-! ## The arm with the length restriction, `InvBlkW2` proved, the path -/

section arm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- **The message has at least two words** (`info.length ≥ 2`): a truncated Delete's error reply writes the
caller's IPC buffer (module docstring), outside the path's sets. `MSG_INFO` is a register. -/
def InvLen (s : S) : Prop :=
  ∀ t info, sched.cur_thread st s = ok t → msg.msg_info st s t = ok info → 2 ≤ info.length.val

variable (st) in
/-- (stpost gen 13) **The canonical `Q` of the CNodeDelete-no-PTE arm**: `InvQF ∧ InvLen`. -/
def InvQL (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayout)
    (m : U64 → U64) (s : S) : Prop :=
  InvQF st Cs Ω Sg Ac Locks p K m s ∧ InvLen st s

theorem len_ge2 {info : msginfo.MessageInfo} {buf length : U64} (h2 : 2 ≤ info.length.val)
    (h : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length) : ¬ length < 2#u64 := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by simp [msg.N_MSG_REGISTERS]
  by_cases c1 : info.length > msg.N_MSG_REGISTERS
  · rw [if_pos c1] at h
    by_cases c2 : buf = 0#u64
    · rw [if_pos c2] at h
      obtain rfl := ok_inj_ff h
      intro hl; scalar_tac
    · rw [if_neg c2] at h
      obtain rfl := ok_inj_ff h
      intro hl; scalar_tac
  · rw [if_neg c1] at h
    obtain rfl := ok_inj_ff h
    intro hl; scalar_tac

/-- (stpost gen 13) **`InvBlkW2` for the CNodeDelete-no-PTE arm** at `Pre := SlJAt K ∧ InvQL`: `delAcc` (the decode
and the reply on the guarded store) and `delFin` (reply `Ok ()`, `FinOK`), from the entry facts `DelEnt`
(`delEnt_of`: [J] `hvs`, [J] `hcdt`, [J] `hz`). -/
theorem invBlkW2_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hvs : InvVsJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s))
    (hcdt : InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, SlJAt (L := L) K s → (0#u64) ∉ K.slots) :
    InvBlkW2 st ar p K Locks (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hl hcap y hy
  have hqf := hE.2.1
  have PE := hqf.1.1.1
  have E := delEnt_of (P := fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s) hE hqf hvs hcdt
    (hz s hE.1)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsK, -⟩ := del_core hqf
  have hlbl := (hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  have hlen := len_ge2 (hE.2.2 (L.curW s) info (cur_thread_ok s) emi) hl
  rw [hlbl] at hy ⊢
  obtain ⟨hdec, hrep⟩ := delAcc (gS := guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) hA PE
    PE.ioWr (fun _ h => h) E hsK hlen
    (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  obtain ⟨h1, h2⟩ := delFin (gS := guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) hA PE
    PE.ioWr PE.stw.2 E hsK hlen
    (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

end arm

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (stpost gen 13) **The CNodeDelete-no-PTE local path** (`Q := InvQL`): `inv_pathsKD` with `hacc` from
`invAccW_of2` + `invBlkW2_of`, `hSeen` from `invSeen_of`, the invoked slot's words from `invPs_of`. Premises: `hA`,
[P] `hm`, [J] `hvs : InvVsJ`, [J] `hcdt : InvCdtJ`, [J] `hz` (no capability slot at address 0), [W] `hmv`
(`InvMoveW`; `InvBlkGdW` is false for this arm, module docstring), [J] `huf`, `hpz` ([P] IsProgOn ∧ [W] NoZero ∧
[W] InvRoW, unchanged shape). -/
noncomputable def inv_pathsKF (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st)
    (hvs : ∀ K m, InvVsJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s))
    (hcdt : ∀ K m, InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s))
    (hz : ∀ K s, SlJAt (L := L) K s → (0#u64) ∉ K.slots)
    (hmv : ∀ K m, InvMoveW st ar number p K Locks m
      (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s))
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
    (fun K m s hJ hq => invSeen_of (fun K _ s hJ _ => hz K s hJ) K m s hJ hq.1) hmv huf hpz

/-- (stpost gen 13) **`StartAt` of `inv_pathsKF` at a chain state** (as `inv_pathsKD_startAt`; `hq : InvQL …` at
`σ`, its plan part from `loc_chain_all` clause 8's input `hp` via `invQ_intro` / `invLk_of_plan`). -/
theorem inv_pathsKF_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st)
    (hvs : ∀ K m, InvVsJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s))
    (hcdt : ∀ K m, InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s))
    (hz : ∀ K s, SlJAt (L := L) K s → (0#u64) ∉ K.slots)
    (hmv : ∀ K m, InvMoveW st ar number p K Locks m
      (fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s))
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
    E2E.StartAt (inv_pathsKF ar hA number p hm hvs hcdt hz hmv huf hpz () K m hK hU) c hs μ
      ((inv_pathsKF ar hA number p hm hvs hcdt hz hmv huf hpz () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨h7 σ a3 τ hR, hq⟩, hc, hl, hμ, rfl⟩

end paths

end Fl4Proofs.P2.PathObl

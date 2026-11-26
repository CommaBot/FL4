/-
(slhuf gen 13) **128-word copy** of `InvCMAcc.lean` (gen 12): stpost's 512-word `InvBufJ` is false at P3 states
(invj gen 1), so the buffer facts are the 128-word `InvBufJ8` (invj's InvTrunc8) and every declaration is renamed
with suffix `8`; `512` bounds are `128`. Otherwise verbatim.

# P2 (line slhuf, gen 12): the Copy / Mint decode block on a guarded store (`acc`)

At an entry with `IoPre` and `CMEnt` (`P2/InvCMEnt.lean`), after the prefix and checks (`InvChk`), the Copy / Mint
arm of `cnode.decode` and `invRep` run on any store answering, as `st`, reads of `IoRS s` and of aligned user words,
and writes of the IoTW-side words (`IoWr`), aligned user words, locked capability-slot words (per word), a locked
non-TCB Null / Frame slot's `CAP0` (per Null / Frame value) and the caller's `STATE` (per value), for every message
length (truncated, `DeleteFirst`, lookup, `copied_cap` and derive errors replied through `reply_error`; the
successful copy: `set_thread_state RESTART` + `insert_with_cap`):

* pure facts: `nof_enc_frame8` (an unmapped Frame cap's first word is a Null / Frame word, P3's `bvext`), `lblCM18`,
  `copied_cap_frame8` (Copy / Mint of a non-EPT Frame: a copy, not a move, of an unmapped Frame cap);
* guarded leaves: `msg.syscall_arg.guardB8` (a buffer word read only when the buffer is set),
  `cnode.copied_cap.guardB8`, `cdt.set_untyped_cap_as_full.frame8` (a no-op for a Frame source, any store),
  `cdt.insert_with_cap.guardF8` (the destination's `CAP0` write per value), `cnode.decode_copy.guardCM8`,
  `cnode.decode.guardCM8`, `invRep.guard_err8`;
* st run: `cm_dec_st8` (the decode state, or `Ok ()` after RESTART and the insertion), `wtr8`, `setCap_keepCM8`,
  `set_next_flags_keep8`, `insert_frame_keep8` (slot words only), `lss_keep8` / `lts_keep8` (walk transport);
* **`cmAcc8`** (generic store), **`cmAccG8`** (`guard st (InvCMRS s) (InvCMWS s)`, the `InvBlkUW2` store),
  **`cmAccGd8`** (`gd st (InvCMRS s) (PWs …)`, the `InvBlkGdUW2` store; [J] `RegionOK`, `UserOK`, `IoLayA`).

Hypotheses of `cmAcc8` beyond `IoPre`, `CMEnt`, `InvChk`, the cap read and the label (named for the assembly):
* `hnul` [J] — a capability slot whose first word decodes to `Null` holds a Null / Frame word (`decodeF` maps the
  unused tags 0 and 25..31 to `Null`, so `CMEnt`'s "decodes to Null" does not give the `NullOrFrame` that `IoWS` /
  `PWs` need for the destination's `CAP0` / `CAP1` writes; slot words are cap encodings);
* `hbufC` [J] — the decode's `buf` words (when `buf ≠ 0`, `i < 128`) are aligned user words: `copied_cap` reads
  `buf + 40` / `buf + 48`; note `InvBlkUW2` / `InvBlkGdUW2` quantify `buf` freely, so the assembly needs `buf`
  tied to the accepted run's `lookup_ipc_buffer st s2 false (curW s)` and a sender-side (`false`) `InvBufJ8`;
* `hbuf` [J] `InvBufJ8` (the error reply's receiver-side buffer); `hsl : p.slot ∈ K.slots`.
No existing statement changes.
-/
import Fl4Proofs.P2.InvCMEnt
import Fl4Proofs.P2.InvTrunc8
import Fl4Proofs.P2.InvMove
import Fl4Proofs.P3.Swap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

section pure

open Fl4Proofs.P3 in
theorem nof_enc_frame8 {p r : U64} {sz : capability.FrameSize} {d : Bool} {w0 w1 : U64}
    (h : capability.Cap.encode (.Frame p sz r d false false 0#u64 0#u64) = ok (w0, w1)) : NullOrFrame w0 := by
  rw [Fl4Proofs.P3.encode_eq] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  obtain ⟨e0, -⟩ := e
  subst e0
  right
  have h4 := Fl4Proofs.P3.codeF_hb sz
  have htag := Fl4Proofs.P3.tag_gen (w := (Fl4Proofs.P3.encodeF (.Frame p sz r d false false 0#u64 0#u64)).1)
    (k := 13) (by bvext) (by decide)
  have e1 : ((Fl4Proofs.P3.encodeF (.Frame p sz r d false false 0#u64 0#u64)).1 >>> 59).toNat =
      (Fl4Proofs.P3.encodeF (.Frame p sz r d false false 0#u64 0#u64)).1.toNat / 2 ^ 59 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have e2 : (⟨(Fl4Proofs.P3.encodeF (.Frame p sz r d false false 0#u64 0#u64)).1⟩ : U64).val =
      (Fl4Proofs.P3.encodeF (.Frame p sz r d false false 0#u64 0#u64)).1.toNat := rfl
  rw [e2, ← e1]
  exact htag

theorem lblCM18 {lbl : U64} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint) :
    ¬ lbl < fl4_abi.label.CNodeRevoke ∧ ¬ lbl > fl4_abi.label.CNodeRotate ∧ lbl ≥ fl4_abi.label.CNodeCopy ∧
      lbl ≤ fl4_abi.label.CNodeMutate := by
  have h1 : fl4_abi.label.CNodeRevoke.val = 25 := by simp [fl4_abi.label.CNodeRevoke]
  have h2 : fl4_abi.label.CNodeRotate.val = 32 := by simp [fl4_abi.label.CNodeRotate]
  have h3 : fl4_abi.label.CNodeCopy.val = 28 := by simp [fl4_abi.label.CNodeCopy]
  have h4 : fl4_abi.label.CNodeMint.val = 29 := by simp [fl4_abi.label.CNodeMint]
  have h5 : fl4_abi.label.CNodeMutate.val = 31 := by simp [fl4_abi.label.CNodeMutate]
  rcases hl with rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> scalar_tac

/-- `copied_cap` of a non-EPT Frame cap at Copy / Mint: a copy (not a move) of an unmapped Frame cap. -/
theorem copied_cap_frame8 {S : Type} (m : machine.Store S) {x : S} {lbl length buf src fp rt asid va : U64}
    {sz : capability.FrameSize} {d mp : Bool} {res : capability.Cap × Bool}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (h : cnode.copied_cap m x lbl length buf src (.Frame fp sz rt d mp false asid va) = ok (.Ok res)) :
    res.2 = false ∧ ∃ r', res.1 = .Frame fp sz r' d false false 0#u64 0#u64 := by
  unfold cnode.copied_cap at h
  obtain ⟨ct, -, h1⟩ := bind_eq_ok h
  rcases hl with rfl | rfl
  · rw [if_pos rfl] at h1
    by_cases h5 : length < 5#u64
    · rw [if_pos h5] at h1; simp [error.truncated] at h1
    rw [if_neg h5] at h1
    obtain ⟨i, -, h2⟩ := bind_eq_ok h1
    obtain ⟨r, -, h3⟩ := bind_eq_ok h2
    obtain ⟨c, ec, h4⟩ := bind_eq_ok h3
    obtain ⟨r1, er1, h6⟩ := bind_eq_ok h4
    unfold capability.mask_cap_rights at ec
    obtain ⟨i', -, ec'⟩ := bind_eq_ok ec
    have ec2 := ok_inj_ff ec'
    rw [← ec2] at er1
    unfold objects.derive_cap at er1
    have er2 := ok_inj_ff er1
    rw [← er2] at h6
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at h6
    have h7 := ok_inj_ff h6
    simp only [core.result.Result.Ok.injEq] at h7
    rw [← h7]
    exact ⟨rfl, _, rfl⟩
  · rw [if_neg lbl_mint_ne_copy, if_pos rfl] at h1
    by_cases h5 : length < 6#u64
    · rw [if_pos h5] at h1; simp [error.truncated] at h1
    rw [if_neg h5] at h1
    obtain ⟨i, -, h2⟩ := bind_eq_ok h1
    obtain ⟨r, -, h3⟩ := bind_eq_ok h2
    obtain ⟨dt, -, h3a⟩ := bind_eq_ok h3
    obtain ⟨c, ec, h4⟩ := bind_eq_ok h3a
    obtain ⟨c1, ec1, h4a⟩ := bind_eq_ok h4
    obtain ⟨r1, er1, h6⟩ := bind_eq_ok h4a
    unfold capability.mask_cap_rights at ec
    obtain ⟨i', -, ec'⟩ := bind_eq_ok ec
    have ec2 := ok_inj_ff ec'
    rw [← ec2] at ec1
    unfold objects.update_cap_data at ec1
    have ec3 := ok_inj_ff ec1
    rw [← ec3] at er1
    unfold objects.derive_cap at er1
    have er2 := ok_inj_ff er1
    rw [← er2] at h6
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at h6
    have h7 := ok_inj_ff h6
    simp only [core.result.Result.Ok.injEq] at h7
    rw [← h7]
    exact ⟨rfl, _, rfl⟩

end pure

section g
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

theorem msg.syscall_arg.guardB8 (s : S) (t : obj.Tcb) (buf i : U64)
    (hreg : ∀ r, msg.msg_register i = ok r → R (regA t r))
    (hbuf : buf ≠ 0#u64 → R (core.num.U64.wrapping_add buf
      (core.num.U64.wrapping_mul (core.num.U64.wrapping_add i 1#u64) 8#u64))) :
    msg.syscall_arg gS s t buf i = msg.syscall_arg st s t buf i := by
  unfold msg.syscall_arg
  split_ifs with h1 h2
  · obtain ⟨r, hr⟩ := msg_register_ok i
    rw [hr]; simp only [bind_ok]
    exact obj.Tcb.reg.guard t s r (hreg r hr)
  · simp only [lift, bind_ok]
    exact msg.buf_get.guard s buf _ (hbuf (by simpa using h2))
  · rfl

theorem cdt.set_untyped_cap_as_full.frame8 (m : machine.Store S) (s : S) {fp rt asid va : U64}
    {sz : capability.FrameSize} {d mp ep : Bool} (nc : capability.Cap) (src : obj.Slot) :
    cdt.set_untyped_cap_as_full m s (.Frame fp sz rt d mp ep asid va) nc src = ok s := by
  unfold cdt.set_untyped_cap_as_full; rfl


/-- `copied_cap` on the guarded store, the buffer words read only when the buffer is set. -/
theorem cnode.copied_cap.guardB8 (s : S) (lbl length buf : U64) (src : obj.Slot) (src_cap : capability.Cap)
    (hct : R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)) (hrg : Regs R (L.curW s))
    (hb : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      R (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)))
    (hs : SlotRd R src) (hn : ∀ nx, obj.Slot.next st src s = ok nx → nx ≠ 0#u64 → SlotRd R nx) :
    cnode.copied_cap gS s lbl length buf src src_cap = cnode.copied_cap st s lbl length buf src src_cap := by
  have hreg : ∀ i r, msg.msg_register i = ok r → R (regA (L.curW s) r) :=
    fun i r hr => hrg r (post_of_ok (msg.msg_register.lt _) hr)
  have ed : ∀ c, objects.derive_cap gS s src c = objects.derive_cap st s src c :=
    fun c => objects.derive_cap.guard s src c hs hn
  have v5 : (core.num.U64.wrapping_add 4#u64 1#u64).val < 128 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  have v6 : (core.num.U64.wrapping_add 5#u64 1#u64).val < 128 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  unfold cnode.copied_cap
  rw [sched.cur_thread.guard s hct, cur_thread_ok]
  simp only [bind_ok]
  rw [msg.syscall_arg.guardB8 s _ buf 4#u64 (hreg 4#u64) (fun h0 => hb h0 _ v5),
    msg.syscall_arg.guardB8 s _ buf 5#u64 (hreg 5#u64) (fun h0 => hb h0 _ v6)]
  simp only [ed]

/-- **`insert_with_cap` from a Frame source on the guarded store**, the destination's `CAP0` write stated per
value (a Null / Frame word): no write of the source's cap words (`set_untyped_cap_as_full` is a no-op). -/
theorem cdt.insert_with_cap.guardF8 (s : S) (nc : capability.Cap) {fp rt asid va : U64} {sz : capability.FrameSize}
    {d mp : Bool} (src dest : obj.Slot)
    (hnc : ∀ w0 w1, capability.Cap.encode nc = ok (w0, w1) → NullOrFrame w0)
    (rsn : R (core.num.U64.wrapping_add src layout.cte.NEXT)) (wsn : W (core.num.U64.wrapping_add src layout.cte.NEXT))
    (wd0 : ∀ X v, NullOrFrame v → gS.write X dest v = st.write X dest v)
    (wd8 : W (core.num.U64.wrapping_add dest 8#u64))
    (wdp : W (core.num.U64.wrapping_add dest layout.cte.PREV))
    (rdn : R (core.num.U64.wrapping_add dest layout.cte.NEXT)) (wdn : W (core.num.U64.wrapping_add dest layout.cte.NEXT))
    (hnx : ∀ nx, obj.Slot.next st src s = ok nx → nx ≠ 0#u64 → W (core.num.U64.wrapping_add nx layout.cte.PREV)) :
    cdt.insert_with_cap gS s nc (.Frame fp sz rt d mp false asid va) src dest =
      cdt.insert_with_cap st s nc (.Frame fp sz rt d mp false asid va) src dest := by
  have e2 : ∀ x, obj.Slot.set_cap gS dest x nc = obj.Slot.set_cap st dest x nc := fun x => by
    unfold obj.Slot.set_cap
    refine bind_guard_congr rfl (fun ⟨w0, w1⟩ ew => ?_)
    simp only [lift, bind_ok, uncurry_apply_pair]
    rw [wd0 _ _ (hnc w0 w1 ew)]
    refine bind_guard_congr rfl (fun x1 _ => ?_)
    exact gst_write wd8
  have e3 : ∀ x q, obj.Slot.set_prev gS dest x q = obj.Slot.set_prev st dest x q :=
    fun x q => obj.Slot.set_prev.guard dest x q wdp
  have e4 : ∀ x n rv fb, obj.Slot.set_next_flags gS dest x n rv fb = obj.Slot.set_next_flags st dest x n rv fb :=
    fun x n rv fb => obj.Slot.set_next_flags.guard dest x n rv fb rdn wdn
  have e5 : ∀ x n, obj.Slot.set_next gS src x n = obj.Slot.set_next st src x n :=
    fun x n => obj.Slot.set_next.guard src x n rsn wsn
  unfold cdt.insert_with_cap
  rw [obj.Slot.next.guard src s rsn, cdt.set_untyped_cap_as_full.frame8, cdt.set_untyped_cap_as_full.frame8]
  refine bind_guard_congr rfl fun rv _ => ?_
  refine bind_guard_congr rfl fun nx enx => ?_
  simp only [bind_ok, e2, e3, e4, e5]
  refine bind_guard_congr rfl fun s2 _ => ?_
  refine bind_guard_congr rfl fun s3 _ => ?_
  refine bind_guard_congr rfl fun s4 _ => ?_
  refine bind_guard_congr rfl fun s5 _ => ?_
  unfold obj.Slot.is_null
  simp only [bind_ok]
  by_cases h0 : nx = 0#u64
  · simp only [h0, decide_true, ↓reduceIte]
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact obj.Slot.set_prev.guard nx s5 dest (hnx nx enx h0)

/-- **The Copy / Mint copy on the guarded store** (`decode_copy` from the target `dest`), given the
`set_thread_state RESTART` and the insertion answer as on `st`. -/
theorem cnode.decode_copy.guardCM8 {x : S} {lbl length buf : U64} {ex : Aeneas.Std.Array obj.Slot 3#usize}
    {dest s1 src rp rr rg rgb fp rt asid va : U64} {sz : capability.FrameSize} {d mp : Bool}
    (C : U64 → U64 → Prop) (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (hct : R (L.nodeAt x (L.cpu x) layout.node.CUR_THREAD)) (hrg : Regs R (L.curW x))
    (hbuf : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      R (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)))
    (he : Aeneas.Std.Array.index_usize ex 0#usize = ok s1) (hs10 : s1 ≠ 0#u64)
    (hs1R : R s1 ∧ R (core.num.U64.wrapping_add s1 8#u64))
    (hsc1 : obj.Slot.cap st s1 x = ok (.CNode rp rr rg rgb))
    (hdR : R dest ∧ R (core.num.U64.wrapping_add dest 8#u64))
    (hRc : WalkRc (st := st) R x C) (hcl : WalkCl (st := st) x C) (hC : C rp rr)
    (hsR : SlotRd R src)
    (hls : cspace.lookup_source_slot st x (.CNode rp rr rg rgb) (L.mem x (regA (L.curW x) layout.reg.R9))
      (L.mem x (regA (L.curW x) layout.reg.R15)) = ok (.Ok src))
    (hsrc : obj.Slot.cap st src x = ok (.Frame fp sz rt d mp false asid va))
    (hnR : ∀ nx, obj.Slot.next st src x = ok nx → nx ≠ 0#u64 → SlotRd R nx)
    (hset : sched.set_thread_state gS x (L.curW x) sched.TS_RESTART =
      sched.set_thread_state st x (L.curW x) sched.TS_RESTART)
    (hins : ∀ x3, sched.set_thread_state st x (L.curW x) sched.TS_RESTART = ok x3 → ∀ nc : capability.Cap,
      (∀ w0 w1, capability.Cap.encode nc = ok (w0, w1) → NullOrFrame w0) →
      cdt.insert_with_cap gS x3 nc (.Frame fp sz rt d mp false asid va) src dest =
        cdt.insert_with_cap st x3 nc (.Frame fp sz rt d mp false asid va) src dest) :
    cnode.decode_copy gS x lbl length buf ex dest = cnode.decode_copy st x lbl length buf ex dest := by
  have hreg : ∀ i r, msg.msg_register i = ok r → R (regA (L.curW x) r) :=
    fun i r hr => hrg r (post_of_ok (msg.msg_register.lt _) hr)
  unfold cnode.decode_copy
  by_cases h4 : length < 4#u64
  · rw [if_pos h4, if_pos h4]
  rw [if_neg h4, if_neg h4, he]
  simp only [bind_ok, obj.Slot.is_null, hs10, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [sched.cur_thread.guard (gS := gS) x hct, cur_thread_ok]
  simp only [bind_ok]
  rw [msg.syscall_arg.guard_lt (gS := gS) x _ buf 2#u64 (by simp [msg.N_MSG_REGISTERS]) (hreg 2#u64),
    msg.syscall_arg.guard_lt (gS := gS) x _ buf 3#u64 (by simp [msg.N_MSG_REGISTERS]) (hreg 3#u64)]
  rw [sarg2_reg, sarg3_reg, reg_ok, reg_ok]
  simp only [bind_ok]
  rw [obj.Slot.cap.guard (gS := gS) s1 x hs1R.1 hs1R.2, hsc1]
  simp only [bind_ok]
  rw [cdt.ensure_empty_slot.guard (gS := gS) x dest hdR.1 hdR.2]
  refine bind_guard_congr rfl (fun r _ => ?_)
  cases r with
  | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] <;> rfl
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [cspace.lookup_source_slot.guardM (gS := gS) C hRc hcl hC ⟨hsR.1, hsR.2.1⟩ hls, hls]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [obj.Slot.cap.guard (gS := gS) src x hsR.1 hsR.2.1, hsrc]
    simp only [bind_ok, capability.Cap.is_null, Bool.false_eq_true, ↓reduceIte]
    rw [cnode.copied_cap.guardB8 (gS := gS) x lbl length buf src _ hct hrg hbuf hsR hnR]
    refine bind_guard_congr rfl (fun r2 er2 => ?_)
    cases r2 with
    | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] <;> rfl
    | Ok v =>
      obtain ⟨hmv, r', hnc⟩ := copied_cap_frame8 st hl er2
      obtain ⟨nc, mv⟩ := v
      simp only at hmv hnc
      rw [hmv, hnc]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      try dsimp only
      refine bind_guard_congr rfl (fun b2 eb2 => ?_)
      have hb2 : b2 = false := by
        first | exact (ok_inj_ff eb2).symm | (simp [capability.Cap.is_null] at eb2; first | exact eb2.symm | exact eb2)
      rw [hb2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hset]
      refine bind_guard_congr rfl (fun x3 ex3 => ?_)
      try simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hins x3 ex3 (.Frame fp sz r' d false false 0#u64 0#u64) (fun w0 w1 ew => nof_enc_frame8 ew)]

/-- **The CNode decode at Copy / Mint on the guarded store**, given the copy's answer as on `st`. -/
theorem cnode.decode.guardCM8 {A : Type} (ar : machine.Arch A) {x : S} {a : A} {lbl length buf cp cr cg cgb : U64}
    {ex : Aeneas.Std.Array obj.Slot 3#usize} {dest : U64}
    (C : U64 → U64 → Prop) (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (hct : R (L.nodeAt x (L.cpu x) layout.node.CUR_THREAD)) (hrg : Regs R (L.curW x))
    (hRc : WalkRc (st := st) R x C) (hcl : WalkCl (st := st) x C) (hC : C cp cr)
    (hdR : R dest ∧ R (core.num.U64.wrapping_add dest 8#u64))
    (hlk : cspace.lookup_target_slot st x (.CNode cp cr cg cgb) (L.mem x (regA (L.curW x) layout.reg.R10))
      (L.mem x (regA (L.curW x) layout.reg.R8)) = ok (.Ok dest))
    (hcopy : cnode.decode_copy gS x lbl length buf ex dest = cnode.decode_copy st x lbl length buf ex dest) :
    cnode.decode gS ar x a lbl length (.CNode cp cr cg cgb) buf ex =
      cnode.decode st ar x a lbl length (.CNode cp cr cg cgb) buf ex := by
  have hreg : ∀ i r, msg.msg_register i = ok r → R (regA (L.curW x) r) :=
    fun i r hr => hrg r (post_of_ok (msg.msg_register.lt _) hr)
  obtain ⟨l1, l2, l3, l4⟩ := lblCM18 hl
  unfold cnode.decode
  rw [if_neg l1, if_neg l1, if_neg l2, if_neg l2]
  by_cases h2 : length < 2#u64
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2, sched.cur_thread.guard (gS := gS) x hct, cur_thread_ok]
  simp only [bind_ok]
  rw [msg.syscall_arg.guard_lt (gS := gS) x _ buf 0#u64 (by simp [msg.N_MSG_REGISTERS]) (hreg 0#u64),
    msg.syscall_arg.guard_lt (gS := gS) x _ buf 1#u64 (by simp [msg.N_MSG_REGISTERS]) (hreg 1#u64)]
  rw [sarg0_reg, sarg1_reg, reg_ok, reg_ok]
  simp only [bind_ok]
  rw [cspace.lookup_target_slot.guardM (gS := gS) C hRc hcl hC hdR hlk, hlk]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [if_pos l3, if_pos l3, if_pos l4, if_pos l4, hcopy]

end g

section st
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The st run of the Copy / Mint decode**: the arch value is kept; either the state is the decode state, or the
result is `Ok ()` after `set_thread_state RESTART` and the insertion of a Null / Frame-encoded cap. -/
theorem cm_dec_st8 {A : Type} (ar : machine.Arch A) {x : S} {a : A}
    {lbl length buf cp cr cg cgb dest s1 src rp rr rg rgb fp rt asid va : U64} {sz : capability.FrameSize}
    {d mp : Bool} {ex : Aeneas.Std.Array obj.Slot 3#usize} {y : (core.result.Result Unit error.Exc) × S × A}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (hlk : cspace.lookup_target_slot st x (.CNode cp cr cg cgb) (L.mem x (regA (L.curW x) layout.reg.R10))
      (L.mem x (regA (L.curW x) layout.reg.R8)) = ok (.Ok dest))
    (he : Aeneas.Std.Array.index_usize ex 0#usize = ok s1) (hs10 : s1 ≠ 0#u64)
    (hsc1 : obj.Slot.cap st s1 x = ok (.CNode rp rr rg rgb))
    (hls : cspace.lookup_source_slot st x (.CNode rp rr rg rgb) (L.mem x (regA (L.curW x) layout.reg.R9))
      (L.mem x (regA (L.curW x) layout.reg.R15)) = ok (.Ok src))
    (hsrc : obj.Slot.cap st src x = ok (.Frame fp sz rt d mp false asid va))
    (hy : cnode.decode st ar x a lbl length (.CNode cp cr cg cgb) buf ex = ok y) :
    y.2.2 = a ∧ (y.2.1 = x ∨ (y.1 = .Ok () ∧ ∃ x3 nc, sched.set_thread_state st x (L.curW x) sched.TS_RESTART = ok x3 ∧
      (∀ w0 w1, capability.Cap.encode nc = ok (w0, w1) → NullOrFrame w0) ∧
      cdt.insert_with_cap st x3 nc (.Frame fp sz rt d mp false asid va) src dest = ok y.2.1)) := by
  obtain ⟨l1, l2, l3, l4⟩ := lblCM18 hl
  unfold cnode.decode at hy
  rw [if_neg l1, if_neg l2] at hy
  by_cases h2 : length < 2#u64
  · rw [if_pos h2] at hy
    obtain ⟨r, -, hy1⟩ := bind_eq_ok hy
    rw [← ok_inj_ff hy1]
    exact ⟨rfl, Or.inl rfl⟩
  rw [if_neg h2, cur_thread_ok] at hy
  simp only [bind_ok] at hy
  rw [sarg0_reg, sarg1_reg, reg_ok, reg_ok] at hy
  simp only [bind_ok] at hy
  rw [hlk] at hy
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at hy
  rw [if_pos l3, if_pos l4] at hy
  obtain ⟨⟨r1, x1⟩, ec, hy1⟩ := bind_eq_ok hy
  try simp only [uncurry_apply_pair] at hy1
  try dsimp only at hy1
  rw [← ok_inj_ff hy1]
  refine ⟨rfl, ?_⟩
  show x1 = x ∨ (r1 = .Ok () ∧ _)
  unfold cnode.decode_copy at ec
  by_cases h4 : length < 4#u64
  · rw [if_pos h4] at ec
    obtain ⟨r, -, ec1⟩ := bind_eq_ok ec
    exact Or.inl (Prod.mk.inj (ok_inj_ff ec1)).2.symm
  rw [if_neg h4, he] at ec
  simp only [bind_ok, obj.Slot.is_null, hs10, decide_false, Bool.false_eq_true, ↓reduceIte] at ec
  rw [cur_thread_ok] at ec
  simp only [bind_ok] at ec
  rw [sarg2_reg, sarg3_reg, reg_ok, reg_ok, hsc1] at ec
  simp only [bind_ok] at ec
  obtain ⟨r, -, ec2⟩ := bind_eq_ok ec
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at ec2
    obtain ⟨r', -, ec3⟩ := bind_eq_ok ec2
    exact Or.inl (Prod.mk.inj (ok_inj_ff ec3)).2.symm
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at ec2
    rw [hls] at ec2
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at ec2
    rw [hsrc] at ec2
    simp only [bind_ok, capability.Cap.is_null, Bool.false_eq_true, ↓reduceIte] at ec2
    obtain ⟨r2, er2, ec3⟩ := bind_eq_ok ec2
    cases r2 with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at ec3
      obtain ⟨r', -, ec4⟩ := bind_eq_ok ec3
      exact Or.inl (Prod.mk.inj (ok_inj_ff ec4)).2.symm
    | Ok v =>
      obtain ⟨hmv, r', hnc⟩ := copied_cap_frame8 st hl er2
      obtain ⟨nc, mv⟩ := v
      simp only at hmv hnc
      rw [hmv, hnc] at ec3
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at ec3
      try dsimp only at ec3
      obtain ⟨b2, eb2, ec3a⟩ := bind_eq_ok ec3
      have hb2 : b2 = false := by
        first | exact (ok_inj_ff eb2).symm | (simp [capability.Cap.is_null] at eb2; first | exact eb2.symm | exact eb2)
      rw [hb2] at ec3a
      simp only [Bool.false_eq_true, ↓reduceIte] at ec3a
      obtain ⟨x3, ex3, ec4⟩ := bind_eq_ok ec3a
      try simp only [Bool.false_eq_true, ↓reduceIte] at ec4
      obtain ⟨x4, ex4, ec5⟩ := bind_eq_ok ec4
      have e5 := Prod.mk.inj (ok_inj_ff ec5)
      refine Or.inr ⟨e5.1.symm, x3, .Frame fp sz r' d false false 0#u64 0#u64, ex3, fun w0 w1 ew => nof_enc_frame8 ew, ?_⟩
      rw [← e5.2]; exact ex4


variable {K : KLayout}

theorem wtr8 {a b c : S} {P : U64 → Prop} (h1 : WritesIn st a b P) (h2 : WritesIn st b c P) : WritesIn st a c P :=
  (h1.trans h2).mono (fun _ h => h.elim id id)

theorem setCap_keepCM8 {x x' : S} {q : U64} {c : capability.Cap} (hL : Slot8 K) (hq : q ∈ K.slots)
    (h : obj.Slot.set_cap st q x c = ok x') : WritesIn st x x' (SlotW K) := by
  unfold obj.Slot.set_cap at h
  obtain ⟨⟨w0, w1⟩, -, h1⟩ := bind_eq_ok h
  simp only [lift, bind_ok, L.write_eq, uncurry_apply_pair] at h1
  cases ok_inj_ff h1
  have e : core.num.U64.wrapping_add q 0#u64 = q := by
    apply UScalar.eq_of_val_eq; rw [slot_word_val (hL q hq).2 (by simp)]; simp
  have w0' : WritesIn st x (L.wr x q w0) (SlotW K) := by
    have := wr_slotW (st := st) (x := x) (v := w0) hL hq (o := 0#u64) (by simp) (by simp)
    rw [e] at this; exact this
  exact w0'.trans1 (wr_slotW hL hq (by simp) (by simp))

theorem set_next_flags_keep8 {x x' : S} {q n : U64} {rv fb : Bool} (hL : Slot8 K) (hq : q ∈ K.slots)
    (h : obj.Slot.set_next_flags st q x n rv fb = ok x') : WritesIn st x x' (SlotW K) := by
  rw [Fl4Proofs.P3.set_next_flags_eq] at h
  cases ok_inj_ff h
  exact wr_slotW hL hq (by simp) (by simp)

/-- **The insertion from a Frame source writes slot words only** (the destination's, the source's `NEXT`, the old
successor's `PREV`). -/
theorem insert_frame_keep8 {x x' : S} {nc : capability.Cap} {fp rt asid va src dest : U64}
    {sz : capability.FrameSize} {d mp : Bool} (hL : Slot8 K) (hd : dest ∈ K.slots) (hs : src ∈ K.slots)
    (hn : ∀ nx, obj.Slot.next st src x = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
    (h : cdt.insert_with_cap st x nc (.Frame fp sz rt d mp false asid va) src dest = ok x') :
    WritesIn st x x' (SlotW K) := by
  unfold cdt.insert_with_cap at h
  rw [cdt.set_untyped_cap_as_full.frame8] at h
  obtain ⟨rv, -, h1⟩ := bind_eq_ok h
  obtain ⟨nx, enx, h2⟩ := bind_eq_ok h1
  simp only [bind_ok] at h2
  obtain ⟨s2, es2, h3⟩ := bind_eq_ok h2
  obtain ⟨s3, es3, h4⟩ := bind_eq_ok h3
  obtain ⟨s4, es4, h5⟩ := bind_eq_ok h4
  obtain ⟨s5, es5, h6⟩ := bind_eq_ok h5
  have w5 : WritesIn st x s5 (SlotW K) :=
    wtr8 (wtr8 (wtr8 (setCap_keepCM8 hL hd es2) (set_prev_keep hL hd es3)) (set_next_flags_keep8 hL hd es4))
      (set_next_keep hL hs es5)
  unfold obj.Slot.is_null at h6
  simp only [bind_ok] at h6
  by_cases h0 : nx = 0#u64
  · simp only [h0, decide_true, ↓reduceIte] at h6
    cases ok_inj_ff h6; exact w5
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at h6
    exact wtr8 w5 (set_prev_keep hL (hn nx enx h0) h6)

/-- The source lookup survives states agreeing on the walk's slots. -/
theorem lss_keep8 {x x' : S} {rp rr rg rgb c dp : U64} {src : obj.Slot} (Cw : U64 → U64 → Prop)
    (slotK : ∀ p r, Cw p r → ∀ m, cspace.mask r = ok m → ∀ y : U64,
      obj.Slot.cap st (cnSlot p (y &&& m)) x' = obj.Slot.cap st (cnSlot p (y &&& m)) x)
    (hcl : WalkCl (st := st) x Cw) (hC : Cw rp rr)
    (h : cspace.lookup_source_slot st x (.CNode rp rr rg rgb) c dp = ok (.Ok src)) :
    cspace.lookup_source_slot st x' (.CNode rp rr rg rgb) c dp = ok (.Ok src) := by
  have hCn' : ∀ p1 r1 gs1 g1, capability.Cap.CNode rp rr rg rgb = .CNode p1 r1 gs1 g1 → Cw p1 r1 := by
    intro p1 r1 gs1 g1 e; cases e; exact hC
  unfold cspace.lookup_source_slot cspace.lookup_slot_for_cnode_op at h ⊢
  simp only [bind_ok, ↓reduceIte] at h ⊢
  by_cases d1 : dp < 1#u64
  · rw [if_pos d1] at h; simp at h
  rw [if_neg d1] at h ⊢
  by_cases d2 : dp > cspace.WORD_BITS
  · rw [if_pos d2] at h; simp at h
  rw [if_neg d2] at h ⊢
  unfold cspace.resolve_address_bits at h ⊢
  obtain ⟨res, eres, hl⟩ := bind_eq_ok h
  have eres' := rab_loop_congr2 st Cw slotK hcl 66 _ _ 65#u64 res (by simp) hCn' eres
  rw [eres']; simp only [bind_ok]; exact hl

/-- The target lookup likewise. -/
theorem lts_keep8 {x x' : S} {rp rr rg rgb c dp : U64} {src : obj.Slot} (Cw : U64 → U64 → Prop)
    (slotK : ∀ p r, Cw p r → ∀ m, cspace.mask r = ok m → ∀ y : U64,
      obj.Slot.cap st (cnSlot p (y &&& m)) x' = obj.Slot.cap st (cnSlot p (y &&& m)) x)
    (hcl : WalkCl (st := st) x Cw) (hC : Cw rp rr)
    (h : cspace.lookup_target_slot st x (.CNode rp rr rg rgb) c dp = ok (.Ok src)) :
    cspace.lookup_target_slot st x' (.CNode rp rr rg rgb) c dp = ok (.Ok src) := by
  have hCn' : ∀ p1 r1 gs1 g1, capability.Cap.CNode rp rr rg rgb = .CNode p1 r1 gs1 g1 → Cw p1 r1 := by
    intro p1 r1 gs1 g1 e; cases e; exact hC
  unfold cspace.lookup_target_slot cspace.lookup_slot_for_cnode_op at h ⊢
  simp only [bind_ok, ↓reduceIte] at h ⊢
  by_cases d1 : dp < 1#u64
  · rw [if_pos d1] at h; simp at h
  rw [if_neg d1] at h ⊢
  by_cases d2 : dp > cspace.WORD_BITS
  · rw [if_pos d2] at h; simp at h
  rw [if_neg d2] at h ⊢
  unfold cspace.resolve_address_bits at h ⊢
  obtain ⟨res, eres, hl⟩ := bind_eq_ok h
  have eres' := rab_loop_congr2 st Cw slotK hcl 66 _ _ 65#u64 res (by simp) hCn' eres
  rw [eres']; simp only [bind_ok]; exact hl

end st

section g4
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

/-- `invRep` of an error on the guarded store, given the error reply answers as on `st`. -/
theorem invRep.guard_err8 {A : Type} {x : S} {a : A} {t : U64} (e : error.Exc)
    (hre : ∀ e1, syscall.reply_error gS x t e1 = syscall.reply_error st x t e1) :
    invRep gS t x a (.Err e) = invRep st t x a (.Err e) := by
  unfold invRep
  cases e <;> (try simp only [hre]) <;> rfl

end g4

/-! ## The Copy / Mint decode and its reply on a guarded store -/

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayout}

set_option maxHeartbeats 4000000 in
/-- (slhuf gen 12) **The Copy / Mint decode block on any store answering as `st`** (run-relative): reads of
`IoRS s` and of aligned user words, writes of `IoTW`-side words (`hW`), of aligned user words (the error reply's
buffer words), of locked capability-slot words (`hwS`, per word; `hw0`, a locked non-TCB Null / Frame slot's
`CAP0` written with a Null / Frame word) and the caller's `STATE` (`hst`, per value). At an entry with `IoPre`
and `CMEnt`, after the prefix and checks (`InvChk`), for any message length: `cnode.decode`'s Copy / Mint arm
(truncated, `DeleteFirst`, lookup, `copied_cap` errors and the successful `insert_with_cap`) and `invRep`
(`reply_error` on an error, `reply_success_empty` / `set_thread_state RUNNING` on `Ok`).
Hypotheses beyond `CMEnt`: `hnul` (a capability slot whose first word decodes to `Null` holds a Null / Frame
word, i.e. a canonical encoding; `decodeF` maps the unused tags 0 and 25..31 to `Null`), `hbufC` (the decode's
buffer words, when the buffer is set, are aligned user words) and [J] `hbuf : InvBufJ8` (the error reply's
buffer). -/
theorem cmAcc8 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {lbl length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hR : ∀ b, IoRS (st := st) K Locks s b → R b) (hRu : ∀ b, UserW K b → R b)
    (hW : IoWr st W K.heap.scBits s) (hWu : ∀ b, UserW K b → W b)
    (hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
      (16 ≤ o.val ∨ (¬ TcbSlot K q ∧ NullOrFrame (L.mem s q))) → W (core.num.U64.wrapping_add q o))
    (hw0 : ∀ q, q ∈ K.slots → Locks s q → ¬ TcbSlot K q → NullOrFrame (L.mem s q) →
      ∀ x v, NullOrFrame v → gS.write x q v = st.write x q v)
    (hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING → SWr gS st (L.curW s) v)
    (E : CMEnt st K Cs Locks p s) (hsl : p.slot ∈ K.slots)
    (hnul : ∀ q, q ∈ K.slots → ∀ c, capability.Cap.decode (L.mem s (core.num.U64.wrapping_add q layout.cte.CAP0))
      0#u64 = ok c → capability.Cap.is_null c = ok true → NullOrFrame (L.mem s q))
    (hbufC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)))
    (hbuf : InvBufJ8 st K s)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation gS ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z → invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z := by
  obtain ⟨cp, cr, cg, cgb, dest, sx, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, Cw, hcs, he, hs10,
    hlk, hsc1, hls, hsrc, hdc0, hdn, hC, hC', hcl, hWk, hs1K, hs1O, hd, hdO, hLd, hsK, hsO, hLs, hnx⟩ := E
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.ent (Locks := Locks) (P.ioWr (Locks := Locks))
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
  have rk : ∀ r : U64, r.val < 384 → r.val ≠ 17 →
      L.mem s2 (regA (L.curW s) r) = L.mem s (regA (L.curW s) r) := fun r h1 h2 => by
    have e := reg_keepK (st := st) P.tA (r := r) h1 h2 tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r10 := rk layout.reg.R10 (by simp [layout.reg.R10]) (by simp [layout.reg.R10])
  have r8 := rk layout.reg.R8 (by simp [layout.reg.R8]) (by simp [layout.reg.R8])
  have r9 := rk layout.reg.R9 (by simp [layout.reg.R9]) (by simp [layout.reg.R9])
  have r15 := rk layout.reg.R15 (by simp [layout.reg.R15]) (by simp [layout.reg.R15])
  have slotK : ∀ p r, Cw p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s2 = obj.Slot.cap st (cnSlot p (x &&& m)) s :=
    fun p r hp m hm x => cap_agree hL (hWk p r m x hp hm).1 ag
  have hlk2 : cspace.lookup_target_slot st s2 (.CNode cp cr cg cgb) (L.mem s2 (regA (L.curW s2) layout.reg.R10))
      (L.mem s2 (regA (L.curW s2) layout.reg.R8)) = ok (.Ok dest) := by
    rw [hct, r10, r8]; exact lts_keep8 Cw slotK hcl hC hlk
  have hls2 : cspace.lookup_source_slot st s2 (.CNode rp rr rg rgb) (L.mem s2 (regA (L.curW s2) layout.reg.R9))
      (L.mem s2 (regA (L.curW s2) layout.reg.R15)) = ok (.Ok src) := by
    rw [hct, r9, r15]; exact lss_keep8 Cw slotK hcl hC' hls
  have hsc1' : obj.Slot.cap st sx s2 = ok (.CNode rp rr rg rgb) := by rw [cap_agree hL hs1K ag]; exact hsc1
  have hsrc2 : obj.Slot.cap st src s2 = ok (.Frame fp sz rt d mp false asid va) := by
    rw [cap_agree hL hsK ag]; exact hsrc
  have hRc2 : WalkRc (st := st) R s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    have h := P.slot (Locks := Locks) (hWk p r m y hp hm).1 (Or.inr (cap_not_nof hc (Or.inl ⟨_, _, _, _, rfl⟩)))
    exact ⟨hR _ h.1, hR _ h.2⟩
  have hcl2 : WalkCl (st := st) s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    exact hcl p r m y p' r' gs' g' hp hm hc
  -- the slot words
  have nR : ∀ q, q ∈ K.slots → Locks s q → ∀ o : U64, o.val < 32 → o.val % 8 = 0 →
      R (core.num.U64.wrapping_add q o) := fun q hq hl o ho h8 => hR _ (P.lockSlot hq hl ho h8).1
  have nR0 : ∀ q, q ∈ K.slots → Locks s q → R q := fun q hq hl => by
    have := nR q hq hl 0#u64 (by simp) (by simp); rwa [wadd_zero (hL q hq).2] at this
  have hdR : R dest ∧ R (core.num.U64.wrapping_add dest 8#u64) := ⟨nR0 _ hd hLd, nR _ hd hLd 8#u64 (by simp) (by simp)⟩
  have hsR : SlotRd R src := ⟨nR0 _ hsK hLs, nR _ hsK hLs 8#u64 (by simp) (by simp),
    nR _ hsK hLs _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])⟩
  have hnR : ∀ n, obj.Slot.next st src s2 = ok n → n ≠ 0#u64 → SlotRd R n := by
    intro n e h0
    rw [next_agree hL hsK ag] at e
    obtain ⟨hq, hl⟩ := hnx n e h0
    exact ⟨nR0 _ hq hl, nR _ hq hl 8#u64 (by simp) (by simp),
      nR _ hq hl _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])⟩
  have hs1R : R sx ∧ R (core.num.U64.wrapping_add sx 8#u64) := by
    have h := P.slot (Locks := Locks) hs1K (Or.inr (cap_not_nof hsc1 (Or.inl ⟨_, _, _, _, rfl⟩)))
    exact ⟨hR _ h.1, hR _ h.2⟩
  have hnT := notTcbSlot_of hdO
  have hnfd : NullOrFrame (L.mem s dest) := hnul dest hd c1 hdc0 hdn
  -- the node, the caller's words
  have hctR : R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact hR _ (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  have hrg2 : Regs R (L.curW s2) := by rw [hct]; exact fun r hr => hR _ (P.reg hr).1
  have hbufR : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      R (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) := fun h0 i hi => hRu _ (hbufC h0 i hi)
  have hN : ∀ x : S, (∀ o, L.nodeAt x (L.cpu x) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R W x := by
    have n0 : IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    have n1 : IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      (P.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
    have n1w : W (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      hW.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    intro x hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hn]; exact hR _ n0
    · rw [hn]; exact hR _ n1
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
  have hmx2 : IoRS (st := st) K Locks s
      (maxA (L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)))) := by
    have kw := (KeepA.refl ha2 hrun).wr hK (b := stA (L.curW s)) (v := sched.TS_RESTART) (Or.inr rfl)
      (fun _ => Or.inl rfl)
    have e : L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      kw.mem (field_aligned P.tA (by simp) (by simp)) (iotw_field P.tA (by simp) (by simp))
    rw [e, hsc2]
    exact hmxR
  -- `set_thread_state RESTART` and the insertion
  have hset : sched.set_thread_state gS s2 (L.curW s2) sched.TS_RESTART =
      sched.set_thread_state st s2 (L.curW s2) sched.TS_RESTART := by
    rw [hct]
    exact sched.set_thread_state.guardV (gS := gS) s2 (L.curW s) _ (hN s2 hnd2) (hst _ (Or.inl rfl)) (hR _ rst.1)
      (hR _ rsc) (hR _ hmx2) (hR _ riq)
  have hins : ∀ x3, sched.set_thread_state st s2 (L.curW s2) sched.TS_RESTART = ok x3 → ∀ nc : capability.Cap,
      (∀ w0 w1, capability.Cap.encode nc = ok (w0, w1) → NullOrFrame w0) →
      cdt.insert_with_cap gS x3 nc (.Frame fp sz rt d mp false asid va) src dest =
        cdt.insert_with_cap st x3 nc (.Frame fp sz rt d mp false asid va) src dest := by
    intro x3 hs3 nc hnc
    rw [hct] at hs3
    have K3 : KeepA (L := L) s2 (L.curW s) x3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
    have ag3 : ∀ b, SlotW K b → Aligned b → L.mem x3 b = L.mem s b := fun b hs hb =>
      (K3.mem hb (O.notT hK hs)).trans (ag b hs hb)
    refine cdt.insert_with_cap.guardF8 (gS := gS) x3 nc src dest hnc
      (nR _ hsK hLs _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]))
      (hwS src _ hsK hLs (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])
        (Or.inl (by simp [layout.cte.NEXT])))
      (hw0 dest hd hLd hnT hnfd)
      (hwS dest 8#u64 hd hLd (by simp) (by simp) (by simp) (Or.inr ⟨hnT, hnfd⟩))
      (hwS dest _ hd hLd (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV])
        (Or.inl (by simp [layout.cte.PREV])))
      (nR _ hd hLd _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]))
      (hwS dest _ hd hLd (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])
        (Or.inl (by simp [layout.cte.NEXT])))
      (fun n e h0 => ?_)
    rw [next_agree hL hsK ag3] at e
    obtain ⟨hq, hl⟩ := hnx n e h0
    exact hwS n _ hq hl (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV])
      (Or.inl (by simp [layout.cte.PREV]))
  -- the decode
  rw [decode_cnode_eq ar] at hy
  have hdg : syscall.decode_invocation gS ar s2 a1 lbl length p.slot (.CNode cp cr cg cgb)
      true true true false buf p.extra = cnode.decode gS ar s2 a1 lbl length (.CNode cp cr cg cgb) buf p.extra := by
    unfold syscall.decode_invocation
    rw [sched.cur_thread.guard (gS := gS) s2 hctR, cur_thread_ok]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  have hcopy := cnode.decode_copy.guardCM8 (gS := gS) (lbl := lbl) (length := length) Cw hl hctR hrg2 hbufR he hs10
    hs1R hsc1' hdR hRc2 hcl2 hC' hsR hls2 hsrc2 hnR hset hins
  refine ⟨by rw [hdg, cnode.decode.guardCM8 (gS := gS) ar Cw hl hctR hrg2 hRc2 hcl2 hC hdR hlk2 hcopy]; exact hy, ?_⟩
  -- the reply
  intro z hz
  obtain ⟨-, hcase⟩ := cm_dec_st8 ar hl hlk2 he hs10 hsc1' hls2 hsrc2 hy
  obtain ⟨r, x, a2⟩ := y
  simp only at hcase hz ⊢
  cases r with
  | Ok u =>
    cases u
    have kx : KeepS st K s2 (L.curW s) x := by
      rcases hcase with hx | ⟨-, x3, nc, hs3, -, hins3⟩
      · rw [hx]; exact KeepS.of_keepA (KeepA.refl ha2 hrun)
      · rw [hct] at hs3
        have K3 : KeepA (L := L) s2 (L.curW s) x3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
        have ag3 : ∀ b, SlotW K b → Aligned b → L.mem x3 b = L.mem s b := fun b hs hb =>
          (K3.mem hb (O.notT hK hs)).trans (ag b hs hb)
        exact (KeepS.of_keepA K3).slots hK O (insert_frame_keep8 hL hd hsK
          (fun n e h0 => (hnx n (by rw [← next_agree hL hsK ag3]; exact e) h0).1) hins3)
    have Fx := kx.sched hK O
    refine invRep.guard_okS (gS := gS) (hR _ rst.1) (hst _ (Or.inr rfl)) (hR _ rsc) (hR _ riq)
      (hW.reg _ rB384) (hW.reg _ rM384) ?_ hz
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
    rw [e6, hsc2]; exact hR _ hmxR
  | Err e =>
    have hx : x = s2 := by
      rcases hcase with hx | ⟨h, -⟩
      · exact hx
      · cases h
    rw [hx] at hz ⊢
    obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
    obtain ⟨hb1, hb2⟩ := P.lay.tslot _ (P.hT _ P.cT) _ bsl hbsl (by simp [layout.tcb.SLOT_BUFFER])
    have hbs := P.slot (Locks := Locks) hb1 (Or.inl hb2)
    have hI : R (core.num.U64.wrapping_add (L.curW s) 3512#u64) :=
      hR _ (P.gate (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
    have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
      lookup_buf_keep P.tA true tk
    have hbw : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → BufW W b ∧ BufW R b := by
      intro b eb
      rw [hlb] at eb
      exact ⟨fun h0 i hi => hWu _ (hbuf b eb h0 i (by omega)), fun h0 i hi => hRu _ (hbuf b eb h0 i (by omega))⟩
    rw [invRep.guard_err8 (gS := gS) e (fun e1 => syscall.reply_error.guard (gS := gS) s2 (L.curW s) e1 hbsl hI
      (hR _ hbs.1) (hR _ hbs.2) (fun r hr => hW.reg r hr) hbw)]
    exact hz

/-- (slhuf gen 12) **`cmAcc8` on the store guarded to the user-word sets** `guard st (InvCMRS s) (InvCMWS s)` (the
`InvBlkUW2` store): the slot, `CAP0` and `STATE` writes are `IoWS` words (`IoPre.lockSlot`, `IoPre.stw`). -/
theorem cmAccG8 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {lbl length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A}
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (E : CMEnt st K Cs Locks p s) (hsl : p.slot ∈ K.slots)
    (hnul : ∀ q, q ∈ K.slots → ∀ c, capability.Cap.decode (L.mem s (core.num.U64.wrapping_add q layout.cte.CAP0))
      0#u64 = ok c → capability.Cap.is_null c = ok true → NullOrFrame (L.mem s q))
    (hbufC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)))
    (hbuf : InvBufJ8 st K s)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) ar s2 a1
        lbl length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) (L.curW s) y.2.1 y.2.2 y.1
        = ok z :=
  cmAcc8 (gS := guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) hA P
    (fun _ h => ioRS_cm h) (fun _ h => ⟨h.1, Or.inl h.2⟩) (P.ioWr.mono (fun _ h => ioWS_cm h))
    (fun _ h => ⟨h.1, Or.inl h.2⟩)
    (fun q o hq hlk ho h8 _ hw => ioWS_cm ((P.lockSlot hq hlk ho h8).2 hw))
    (fun q hq hlk hT hn x v _ => by
      have h := (P.lockSlot hq hlk (o := 0#u64) (by simp) (by simp)).2 (Or.inr ⟨hT, hn⟩)
      rw [wadd_zero (P.lay.slot8 q hq).2] at h
      exact gst_write (ioWS_cm h))
    (fun _ _ => SWr.of_W (ioWS_cm P.stw.2)) E hsl hnul hbufC hbuf hl C hcap hy

/-- (slhuf gen 12) **`cmAcc8` on p2sl's checked store with slot `CAP0` writes, reading the user-word set**
`gd st (InvCMRS s) (PWs …)` (the `InvBlkGdUW2` store): the destination's `CAP0` write (Null → the derived
Frame cap's word) is a `PWs` slot write, the other slot words and user words are non-deciding aligned words
(`PW`), `STATE` as stpost's `gds_write_state`. [J] `hK` (`RegionOK`), `hU` (`UserOK`), `hLA` (`IoLayA`). -/
theorem cmAccGd8 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {lbl length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A}
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hK : RegionOK K) (hU : E2E.UserOK K) (hLA : IoLayA K)
    (E : CMEnt st K Cs Locks p s) (hsl : p.slot ∈ K.slots)
    (hnul : ∀ q, q ∈ K.slots → ∀ c, capability.Cap.decode (L.mem s (core.num.U64.wrapping_add q layout.cte.CAP0))
      0#u64 = ok c → capability.Cap.is_null c = ok true → NullOrFrame (L.mem s q))
    (hbufC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)))
    (hbuf : InvBufJ8 st K s)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))
        ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))
        (L.curW s) y.2.1 y.2.2 y.1 = ok z := by
  have hS0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) := by
    refine ⟨?_, fun hq => absurd hq ?_⟩
    · rw [← OwnMap.affA_fld]; exact P.curAff
    · rw [← OwnMap.stA_fld]; exact nq_run P.run
  have hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
      (16 ≤ o.val ∨ (¬ TcbSlot K q ∧ NullOrFrame (L.mem s q))) →
      WAll (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)) (core.num.U64.wrapping_add q o) := by
    intro q o hq _ ho h8 h8' _
    obtain ⟨q8, qf⟩ := P.lay.slot8 q hq
    have hv := slot_word_val qf ho
    have hr := P.lay.slotw q hq _ (slot_inW qf ho)
    have hne : core.num.U64.wrapping_add q o ≠ q := fun e => by
      have := congrArg UScalar.val e; rw [hv] at this; omega
    have ha : Aligned (core.num.U64.wrapping_add q o) := by unfold Aligned; rw [hv]; omega
    exact fun _ _ => Or.inl (Or.inl ⟨ha, OwnMap.nondec_slotw hK hr hne⟩)
  exact cmAcc8 (gS := gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) hA P
    (fun _ h => ioRS_cm h) (fun _ h => ⟨h.1, Or.inl h.2⟩) (mvWrS P hK hLA)
    (fun b hb _ _ => Or.inl (Or.inl ⟨hb.1, fun hd => (OwnMap.decW_ok hU hd).2 hb.2⟩))
    hwS (fun q hq hlk hT hn x v hv => OwnMap.gds_write_cap0 hq hT hlk hn hv)
    (fun v hv X => OwnMap.gds_write_state (P.hT _ P.cT) hS0 (fun hq => absurd hq (nq_run hv)))
    E hsl hnul hbufC hbuf hl C hcap hy

end acc

end Fl4Proofs.P2.PathObl

/-
(slhuf gen 13) **128-word copy** of `InvCMFin.lean` (gen 12): stpost's 512-word `InvBufJ` is false at P3 states
(invj gen 1), so the buffer facts are the 128-word `InvBufJ8` (invj's InvTrunc8) and every declaration is renamed
with suffix `8`; `512` bounds are `128`. Otherwise verbatim.

# P2 (line slhuf, gen 12): `FinOK` after the Copy / Mint decode block

stpost's `delFin` (P2/InvBlkFin.lean) and `truncFin` (P2/InvTrunc.lean) for the CNodeCopy / CNodeMint arm, any
message length. The st run of the block writes `IoTW t` words, capability-slot words (the success path:
`set_thread_state RESTART`, then `insert_with_cap` on the target, the source's `NEXT` and the old successor's `PREV`)
and aligned user words (every error path: `reply_error` writes the error MRs past the registers and the debug word
into the caller's IPC buffer). Both kinds are kept apart from everything `finish` reads by one layout trick:

* `KSU8 K` is `K` with the capability-slot words added to its user words, so InvTrunc's `KeepU` / `UsrOK` /
  `KeepU.fin` / `SwOK.frameU` at `KSU8 K` are the "slot or user word" variants (`usu_of_user8`, `usu_of_slot8`,
  `not_usu8`, `wi_usu8`);
* footprints: `set_cap_keep8`, `snf_keep8`, `insert_keep8` (an insert under a Frame source writes slot words only),
  `set_mr_ku8`, `set_mrs_lf_ku8`, `error_mrs_ku8`, **`reply_error_ku8`** (any `SysError`), `invRep_ok_ku8`;
* the run: `copied_frame8` (a Frame source: truncated, or a cap and no move), `ees_err8`, `cmCopy8` (`decode_copy`:
  `Ok ()` with `KeepU`, or a `Sys` error with the state unchanged), `cmDec8` (`cnode.decode`), `cmRun8` (decode then
  `invRep`: reply `Ok ()`, `KeepU`);
* **`cmFin8`**: `FinOK` after the block at an accepted run's post-prefix state, from `CMEnt` and [J] `InvBufJ8`, on any
  store `gS` reading `IoRS s` as `st` and writing `W` (`IoWr`) with the caller's `STATE` write (`SWr`): it covers
  `guard st (InvCMRS s) (InvCMWS s)` (InvBlkUW2) and `gd st (InvCMRS s) (PWs …)` (InvBlkGdUW2) alike.

Named premise: [J] `InvBufJ8` (InvTrunc: the caller's IPC buffer words, when set, are aligned user words).
No existing statement changes.
-/
import Fl4Proofs.P2.InvCMEnt
import Fl4Proofs.P2.InvTrunc8
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

/-- `K` with its capability-slot words counted as user words. -/
def KSU8 (K : KLayout) : KLayout := { K with user := {b | b ∈ K.user ∨ SlotW K b} }

section ksu
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s0 x y : S} {t : U64}

theorem usu_of_user8 {b : U64} (h : UserW K b) : UserW (KSU8 K) b := ⟨h.1, Or.inl h.2⟩

theorem usu_of_slot8 {b : U64} (ha : Aligned b) (h : SlotW K b) : UserW (KSU8 K) b := ⟨ha, Or.inr h⟩

theorem not_usu8 {b : U64} (h1 : ¬ UserW K b) (h2 : ¬ SlotW K b) : ¬ UserW (KSU8 K) b := fun h =>
  Or.elim h.2 (fun hu => h1 ⟨h.1, hu⟩) h2

theorem wi_usu8 (h : WritesIn st x y (SlotW K)) : WritesIn st x y (UserW (KSU8 K)) :=
  h.mono' fun b ha hs => usu_of_slot8 ha hs

theorem KU_reg8 (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (h : KeepU st K s0 t x) {r v : U64}
    (hr : r.val < 384) : KeepU st K s0 t (L.wr x (regA t r) v) :=
  h.keepA ((KeepA.refl h.2.1 h.2.2).wr_reg (h.sched F O) hr)

theorem KU_user8 (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (h : KeepU st K s0 t x) {b v : U64}
    (hu : UserW K b) : KeepU st K s0 t (L.wr x b v) :=
  h.users F O ((writesIn_wr hu.1).mono fun _ e => by subst e; exact hu)

/-- A `KSU8` user word is no `IoTW t` word (`UsrOK.tf`). -/
theorem UsrOK.notT8 {t b : U64} (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (hs : UserW K b) :
    ¬ IoTW t b := by
  rintro (⟨r, hr, e⟩ | e)
  · obtain ⟨k, hk, ek⟩ := regA_eq F.tcb hr
    rw [ek] at e; subst e
    exact O.tf k (by omega) (by omega) hs
  · subst e
    exact O.tf _ (by rw [st_val]; omega) (by rw [st_val]; omega) hs

end ksu

/-! ## Footprints -/

section foot
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s0 x : S} {t : U64}

theorem set_cap_keep8 {x' : S} {q : U64} {c : capability.Cap} (hL : Slot8 K) (hq : q ∈ K.slots)
    (h : obj.Slot.set_cap st q x c = ok x') : WritesIn st x x' (SlotW K) := by
  unfold obj.Slot.set_cap at h
  obtain ⟨⟨w0, w1⟩, -, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  simp only [lift, bind_ok, L.write_eq] at h
  cases ok_inj_ff h
  have w0' : WritesIn st x (L.wr x q w0) (SlotW K) := by
    have e : core.num.U64.wrapping_add q 0#u64 = q := by
      apply UScalar.eq_of_val_eq; rw [slot_word_val (hL q hq).2 (by simp)]; simp
    have := wr_slotW (st := st) (x := x) (v := w0) hL hq (o := 0#u64) (by simp) (by simp)
    rw [e] at this; exact this
  exact w0'.trans1 (wr_slotW hL hq (o := 8#u64) (by simp) (by simp))

theorem snf_keep8 {x' : S} {q n : U64} {rv fb : Bool} (hL : Slot8 K) (hq : q ∈ K.slots)
    (h : obj.Slot.set_next_flags st q x n rv fb = ok x') : WritesIn st x x' (SlotW K) := by
  unfold obj.Slot.set_next_flags obj.Slot.next_word at h
  simp only [lift, bind_ok, L.read_eq] at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  try simp only [lift, bind_ok] at h
  obtain ⟨i3, -, h⟩ := bind_eq_ok h
  try simp only [lift, bind_ok] at h
  obtain ⟨r, -, h⟩ := bind_eq_ok h
  obtain ⟨f, -, h⟩ := bind_eq_ok h
  simp only [lift, bind_ok, L.write_eq] at h
  cases ok_inj_ff h
  exact wr_slotW hL hq (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])

/-- **`insert_with_cap` under a Frame source writes slot words only** (the target's four words, the source's
`NEXT`, the old successor's `PREV`), given those slots are capability slots. -/
theorem insert_keep8 {x' : S} {nc : capability.Cap} {src dest fp rt asid va : U64} {sz : capability.FrameSize}
    {d mp ep : Bool} (hL : Slot8 K) (hsK : src ∈ K.slots) (hdK : dest ∈ K.slots)
    (hnx : ∀ nx, obj.Slot.next st src x = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
    (h : cdt.insert_with_cap st x nc (.Frame fp sz rt d mp ep asid va) src dest = ok x') :
    WritesIn st x x' (SlotW K) := by
  unfold cdt.insert_with_cap at h
  obtain ⟨rv, -, h⟩ := bind_eq_ok h
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
  obtain ⟨x1, e1, h⟩ := bind_eq_ok h
  have e1' : x1 = x := by
    unfold cdt.set_untyped_cap_as_full at e1
    exact (ok_inj_ff e1).symm
  rw [e1'] at h
  obtain ⟨x2, e2, h⟩ := bind_eq_ok h
  obtain ⟨x3, e3, h⟩ := bind_eq_ok h
  obtain ⟨x4, e4, h⟩ := bind_eq_ok h
  obtain ⟨x5, e5, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  have w : WritesIn st x x5 (SlotW K) :=
    (((set_cap_keep8 hL hdK e2).trans1 (set_prev_keep hL hdK e3)).trans1 (snf_keep8 hL hdK e4)).trans1
      (set_next_keep hL hsK e5)
  unfold obj.Slot.is_null at eb
  have eb' := ok_inj_ff eb
  by_cases hb : b = true
  · rw [if_pos hb] at h; cases ok_inj_ff h; exact w
  · rw [if_neg hb] at h
    have hne : nx ≠ 0#u64 := fun e0 => hb (by rw [← eb']; simp [e0])
    exact w.trans1 (set_prev_keep hL (hnx nx enx hne) h)

theorem set_mr_ku8 (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (hk : KeepU st K s0 t x)
    {buf i v : U64} {r : U64 × S}
    (hb : buf ≠ 0#u64 → ∀ j : U64, j.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul j 8#u64)))
    (hi : i.val < 127) (h : msg.set_mr st x t buf i v = ok r) : KeepU st K s0 t r.2 := by
  unfold msg.set_mr at h
  by_cases hc : i < msg.N_MSG_REGISTERS
  · rw [if_pos hc] at h
    obtain ⟨r1, er1, h⟩ := bind_eq_ok h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    rw [set_reg_ok'] at es1
    try simp only [lift, bind_ok] at h
    cases ok_inj_ff h
    cases ok_inj_ff es1
    exact KU_reg8 F O hk (post_of_ok (msg.msg_register.lt _) er1)
  · rw [if_neg hc] at h
    by_cases hb0 : (buf != 0#u64) = true
    · rw [if_pos hb0] at h
      have hne : buf ≠ 0#u64 := by simpa using hb0
      try simp only [lift, bind_ok] at h
      obtain ⟨s1, es1, h⟩ := bind_eq_ok h
      try simp only [lift, bind_ok] at h
      cases ok_inj_ff h
      unfold msg.buf_set at es1
      simp only [lift, bind_ok, L.write_eq] at es1
      cases ok_inj_ff es1
      have hv : (core.num.U64.wrapping_add i 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      exact KU_user8 F O hk (hb hne _ hv)
    · rw [if_neg hb0] at h
      cases ok_inj_ff h
      exact hk

theorem set_mrs_lf_ku8 (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (hk : KeepU st K s0 t x)
    {buf : U64} {lf : error.LookupFault} {r : U64 × S}
    (hb : buf ≠ 0#u64 → ∀ j : U64, j.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul j 8#u64)))
    (h : faults.set_mrs_lookup_failure_at st x t buf lf 1#u64 = ok r) : KeepU st K s0 t r.2 := by
  unfold faults.set_mrs_lookup_failure_at faults.set_mrs_lookup_failure at h
  have h1 : (core.num.U64.wrapping_add 1#u64 1#u64).val < 127 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  have h2 : (core.num.U64.wrapping_add 1#u64 2#u64).val < 127 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  have h3 : (core.num.U64.wrapping_add 1#u64 3#u64).val < 127 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨i1, s1⟩, e1, h⟩ := bind_eq_ok h
  have k1 : KeepU st K s0 t s1 := set_mr_ku8 F O hk hb (by simp) e1
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  cases lf with
  | InvalidRoot => cases ok_inj_ff h; exact k1
  | MissingCapability bl =>
    try simp only [lift, bind_ok] at h
    exact set_mr_ku8 F O k1 hb h1 h
  | DepthMismatch bf bl =>
    try simp only [lift, bind_ok] at h
    obtain ⟨⟨j, s2⟩, e2, h⟩ := bind_eq_ok h
    have k2 : KeepU st K s0 t s2 := set_mr_ku8 F O k1 hb h1 e2
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    try simp only [lift, bind_ok] at h
    exact set_mr_ku8 F O k2 hb h2 h
  | GuardMismatch gf bl gs =>
    try simp only [lift, bind_ok] at h
    obtain ⟨⟨j, s2⟩, e2, h⟩ := bind_eq_ok h
    have k2 : KeepU st K s0 t s2 := set_mr_ku8 F O k1 hb h1 e2
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    try simp only [lift, bind_ok] at h
    obtain ⟨⟨j', s3⟩, e3, h⟩ := bind_eq_ok h
    have k3 : KeepU st K s0 t s3 := set_mr_ku8 F O k2 hb h2 e3
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    try simp only [lift, bind_ok] at h
    exact set_mr_ku8 F O k3 hb h3 h

theorem error_mrs_ku8 (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (hk : KeepU st K s0 t x)
    {buf : U64} {e : error.SysError} {r : U64 × S}
    (hb : buf ≠ 0#u64 → ∀ j : U64, j.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul j 8#u64)))
    (h : syscall.error_mrs st x t buf e = ok r) : KeepU st K s0 t r.2 := by
  unfold syscall.error_mrs at h
  cases e with
  | InvalidArgument arg => exact set_mr_ku8 F O hk hb (by simp) h
  | InvalidCapability arg => exact set_mr_ku8 F O hk hb (by simp) h
  | IllegalOperation => cases ok_inj_ff h; exact hk
  | RangeError mn mx =>
    obtain ⟨⟨j, s1⟩, e1, h⟩ := bind_eq_ok h
    have k1 : KeepU st K s0 t s1 := set_mr_ku8 F O hk hb (by simp) e1
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    exact set_mr_ku8 F O k1 hb (by simp) h
  | AlignmentError => cases ok_inj_ff h; exact hk
  | FailedLookup src lf =>
    cases src
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨j, s1⟩, e1, h⟩ := bind_eq_ok h
      have k1 : KeepU st K s0 t s1 := set_mr_ku8 F O hk hb (by simp) e1
      try simp only [uncurry_apply_pair] at h
      try dsimp only at h
      exact set_mrs_lf_ku8 F O k1 hb h
    · simp only [↓reduceIte] at h
      obtain ⟨⟨j, s1⟩, e1, h⟩ := bind_eq_ok h
      have k1 : KeepU st K s0 t s1 := set_mr_ku8 F O hk hb (by simp) e1
      try simp only [uncurry_apply_pair] at h
      try dsimp only at h
      exact set_mrs_lf_ku8 F O k1 hb h
  | TruncatedMessage => cases ok_inj_ff h; exact hk
  | DeleteFirst => cases ok_inj_ff h; exact hk
  | RevokeFirst => cases ok_inj_ff h; exact hk
  | NotEnoughMemory bytes => exact set_mr_ku8 F O hk hb (by simp) h

/-- **The error reply, any `SysError`, keeps `KeepU`** given the receiver's IPC buffer words are user words. -/
theorem reply_error_ku8 (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (hk : KeepU st K s0 t x)
    (hbuf : ∀ b, msg.lookup_ipc_buffer st x true t = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)))
    {e : error.SysError} {z : S} (h : syscall.reply_error st x t e = ok z) : KeepU st K s0 t z := by
  unfold syscall.reply_error at h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  rw [set_reg_ok'] at h
  simp only [bind_ok] at h
  have u1 : KeepU st K s0 t (L.wr x (regA t layout.reg.BADGE) 0#u64) := KU_reg8 F O hk rB384
  have hb : b ≠ 0#u64 → ∀ j : U64, j.val < 128 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul j 8#u64)) := hbuf b eb
  obtain ⟨⟨len, s2⟩, e2, h⟩ := bind_eq_ok h
  have u2 : KeepU st K s0 t s2 := error_mrs_ku8 F O u1 hb e2
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  simp only [fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, if_true, ↓reduceIte] at h
  obtain ⟨q, eq, h⟩ := bind_eq_ok h
  have uq : KeepU st K s0 t q.1 := by
    by_cases hb0 : (b != 0#u64) = true
    · rw [if_pos hb0] at eq
      have hne : b ≠ 0#u64 := by simpa using hb0
      obtain ⟨i, hi, hiv⟩ := dbg_idx8
      rw [hi] at eq
      simp only [bind_ok] at eq
      obtain ⟨w, -, eq⟩ := bind_eq_ok eq
      try simp only [lift, bind_ok] at eq
      obtain ⟨s4, es4, eq⟩ := bind_eq_ok eq
      cases ok_inj_ff eq
      unfold msg.buf_set at es4
      simp only [lift, bind_ok, L.write_eq] at es4
      cases ok_inj_ff es4
      exact KU_user8 F O u2 (hb hne i hiv)
    · rw [if_neg hb0] at eq
      cases ok_inj_ff eq
      exact u2
  obtain ⟨s3, len1⟩ := q
  simp only [uncurry_apply_pair] at h uq
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  obtain ⟨mi, -, h⟩ := bind_eq_ok h
  unfold msg.set_msg_info at h
  obtain ⟨wv, -, h⟩ := bind_eq_ok h
  rw [set_reg_ok'] at h
  cases ok_inj_ff h
  exact KU_reg8 F O uq rM384

/-- `invRep` of `Ok` from a `KeepU` state (InvBlkFin's `invRep_ok_keep` for `KeepU`). -/
theorem invRep_ok_ku8 {A : Type} {a : A} {z : S × A × core.result.Result Unit error.Exc}
    (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (hk : KeepU st K s0 t x)
    (h : invRep st t x a (.Ok ()) = ok z) : z.2.2 = .Ok () ∧ KeepU st K s0 t z.1 := by
  have Fx := hk.sched F O
  unfold invRep at h
  obtain ⟨i6, -, h⟩ := bind_eq_ok h
  obtain ⟨t1, et1, h⟩ := bind_eq_ok h
  cases ok_inj_ff h
  refine ⟨rfl, ?_⟩
  by_cases hi : i6 = sched.TS_RESTART
  · rw [if_pos hi] at et1
    obtain ⟨s5, es5, et1⟩ := bind_eq_ok et1
    have k5 : KeepA (L := L) x t s5 := by
      unfold msg.reply_success_empty at es5
      rw [set_reg_ok'] at es5; simp only [bind_ok] at es5
      obtain ⟨mi, -, es5⟩ := bind_eq_ok es5
      unfold msg.set_msg_info at es5
      obtain ⟨w, -, es5⟩ := bind_eq_ok es5
      rw [set_reg_ok'] at es5
      cases ok_inj_ff es5
      exact ((KeepA.refl hk.2.1 hk.2.2).wr_reg Fx rB384).wr_reg Fx rM384
    exact hk.keepA (k5.sts Fx (Or.inr rfl) et1)
  · rw [if_neg hi] at et1
    cases ok_inj_ff et1
    exact hk

end foot

/-! ## The run -/

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable {K : KLayout}

theorem br_ok8 {T E : Type} (v : T) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok v : core.result.Result T E) =
      ok (core.ops.control_flow.ControlFlow.Continue v) := rfl

theorem br_err8 {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Err e : core.result.Result T E) =
      ok (core.ops.control_flow.ControlFlow.Break (core.result.Result.Err e)) := rfl

theorem fr_same8 {T E : Type} (e : E) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T (core.convert.FromSame E)
      (core.result.Result.Err e) = ok (core.result.Result.Err e) := by
  unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
  simp [core.convert.FromSame]

theorem ees_err8 {x : S} {d : U64} {e : error.Exc} (h : cdt.ensure_empty_slot st x d = ok (.Err e)) :
    e = .Sys .DeleteFirst := by
  unfold cdt.ensure_empty_slot at h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  by_cases hb : b = true
  · rw [if_pos hb] at h; simp at h
  · rw [if_neg hb] at h
    have := ok_inj_ff h
    simp only [core.result.Result.Err.injEq] at this
    exact this.symm

/-- `copied_cap` of a Frame source at Copy / Mint: truncated, or a cap and no move. -/
theorem copied_frame8 {x : S} {lbl length buf src fp rt asid va : U64} {sz : capability.FrameSize}
    {d mp ep : Bool} {r : core.result.Result (capability.Cap × Bool) error.Exc}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (h : cnode.copied_cap st x lbl length buf src (.Frame fp sz rt d mp ep asid va) = ok r) :
    r = .Err (.Sys .TruncatedMessage) ∨ ∃ c, r = .Ok (c, false) := by
  unfold cnode.copied_cap at h
  rw [cur_thread_ok] at h
  simp only [bind_ok] at h
  rcases hl with rfl | rfl
  · rw [if_pos rfl] at h
    by_cases h5 : length < 5#u64
    · rw [if_pos h5] at h; unfold error.truncated at h; exact Or.inl (ok_inj_ff h).symm
    · rw [if_neg h5] at h
      obtain ⟨i, -, h⟩ := bind_eq_ok h
      obtain ⟨rr, -, h⟩ := bind_eq_ok h
      obtain ⟨c, ec, h⟩ := bind_eq_ok h
      simp only [capability.mask_cap_rights] at ec
      obtain ⟨i2, -, ec⟩ := bind_eq_ok ec
      cases ok_inj_ff ec
      simp only [objects.derive_cap, bind_ok, br_ok8] at h
      exact Or.inr ⟨_, (ok_inj_ff h).symm⟩
  · rw [if_neg lbl_mint_ne_copy, if_pos rfl] at h
    by_cases h6 : length < 6#u64
    · rw [if_pos h6] at h; unfold error.truncated at h; exact Or.inl (ok_inj_ff h).symm
    · rw [if_neg h6] at h
      obtain ⟨i, -, h⟩ := bind_eq_ok h
      obtain ⟨rr, -, h⟩ := bind_eq_ok h
      obtain ⟨dt, -, h⟩ := bind_eq_ok h
      obtain ⟨c, ec, h⟩ := bind_eq_ok h
      simp only [capability.mask_cap_rights] at ec
      obtain ⟨i2, -, ec⟩ := bind_eq_ok ec
      cases ok_inj_ff ec
      obtain ⟨c1, ec1, h⟩ := bind_eq_ok h
      simp only [objects.update_cap_data] at ec1
      cases ok_inj_ff ec1
      simp only [objects.derive_cap, bind_ok, br_ok8] at h
      exact Or.inr ⟨_, (ok_inj_ff h).symm⟩

theorem lblC18 {lbl : U64} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint) :
    ¬ lbl < fl4_abi.label.CNodeRevoke := by
  have h1 : fl4_abi.label.CNodeRevoke.val = 25 := by simp [fl4_abi.label.CNodeRevoke]
  rcases hl with rfl | rfl
  · have h2 : fl4_abi.label.CNodeCopy.val = 28 := by simp [fl4_abi.label.CNodeCopy]
    scalar_tac
  · have h2 : fl4_abi.label.CNodeMint.val = 29 := by simp [fl4_abi.label.CNodeMint]
    scalar_tac
theorem lblC28 {lbl : U64} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint) :
    ¬ lbl > fl4_abi.label.CNodeRotate := by
  have h1 : fl4_abi.label.CNodeRotate.val = 32 := by simp [fl4_abi.label.CNodeRotate]
  rcases hl with rfl | rfl
  · have h2 : fl4_abi.label.CNodeCopy.val = 28 := by simp [fl4_abi.label.CNodeCopy]
    scalar_tac
  · have h2 : fl4_abi.label.CNodeMint.val = 29 := by simp [fl4_abi.label.CNodeMint]
    scalar_tac
theorem lblC38 {lbl : U64} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint) :
    lbl ≥ fl4_abi.label.CNodeCopy := by
  have h1 : fl4_abi.label.CNodeCopy.val = 28 := by simp [fl4_abi.label.CNodeCopy]
  rcases hl with rfl | rfl
  · scalar_tac
  · have h2 : fl4_abi.label.CNodeMint.val = 29 := by simp [fl4_abi.label.CNodeMint]
    scalar_tac
theorem lblC48 {lbl : U64} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint) :
    lbl ≤ fl4_abi.label.CNodeMutate := by
  have h1 : fl4_abi.label.CNodeMutate.val = 31 := by simp [fl4_abi.label.CNodeMutate]
  rcases hl with rfl | rfl
  · have h2 : fl4_abi.label.CNodeCopy.val = 28 := by simp [fl4_abi.label.CNodeCopy]
    scalar_tac
  · have h2 : fl4_abi.label.CNodeMint.val = 29 := by simp [fl4_abi.label.CNodeMint]
    scalar_tac

/-- **`decode_copy` at Copy / Mint** from the decode state `x` (`t` current, schedulable, action
`RESUME_CURRENT`): with the source root, source and its Frame cap as at `x`, either `Ok ()` and only `IoTW t` and
slot words written, or a `Sys` error and nothing written. -/
theorem cmCopy8 {x : S} {t lbl length buf dest s1 src rp rr rg rgb fp rt asid va : U64}
    {sz : capability.FrameSize} {d mp : Bool} {ex : Aeneas.Std.Array obj.Slot 3#usize}
    (F : SchedOK (L := L) x t) (O : UsrOK (L := L) (KSU8 K) x t) (ha : L.actionW x = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING)
    (hL : Slot8 K) (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (hdK : dest ∈ K.slots) (hex : Aeneas.Std.Array.index_usize ex 0#usize = ok s1)
    (hrc : obj.Slot.cap st s1 x = ok (.CNode rp rr rg rgb))
    (hlss : cspace.lookup_source_slot st x (.CNode rp rr rg rgb) (L.mem x (regA t layout.reg.R9))
      (L.mem x (regA t layout.reg.R15)) = ok (.Ok src))
    (hsc : obj.Slot.cap st src x = ok (.Frame fp sz rt d mp false asid va)) (hsK : src ∈ K.slots)
    (hnx : ∀ nx, obj.Slot.next st src x = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
    {r : core.result.Result Unit error.Exc} {x' : S}
    (h : cnode.decode_copy st x lbl length buf ex dest = ok (r, x')) :
    (r = .Ok () ∧ KeepU st (KSU8 K) x t x') ∨ (∃ e, r = .Err (.Sys e) ∧ x' = x) := by
  unfold cnode.decode_copy at h
  by_cases h4 : length < 4#u64
  · rw [if_pos h4] at h
    unfold error.truncated at h
    simp only [bind_ok] at h
    have e := ok_inj_ff h
    simp only [Prod.mk.injEq] at e
    exact Or.inr ⟨_, e.1.symm, e.2.symm⟩
  rw [if_neg h4, hex] at h
  simp only [bind_ok] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  by_cases hb : b = true
  · rw [if_pos hb] at h
    unfold error.truncated at h
    simp only [bind_ok] at h
    have e := ok_inj_ff h
    simp only [Prod.mk.injEq] at e
    exact Or.inr ⟨_, e.1.symm, e.2.symm⟩
  rw [if_neg hb, cur_thread_ok, F.cur] at h
  simp only [bind_ok] at h
  rw [sarg2_reg, sarg3_reg, reg_ok, reg_ok] at h
  simp only [bind_ok] at h
  rw [hrc] at h
  simp only [bind_ok] at h
  obtain ⟨r0, er0, h⟩ := bind_eq_ok h
  cases r0 with
  | Err e0 =>
    simp only [br_err8, fr_same8, bind_ok] at h
    have e := ok_inj_ff h
    simp only [Prod.mk.injEq] at e
    exact Or.inr ⟨_, by rw [← e.1, ees_err8 er0], e.2.symm⟩
  | Ok u =>
    simp only [br_ok8, bind_ok] at h
    rw [hlss] at h
    simp only [br_ok8, bind_ok] at h
    rw [hsc] at h
    simp only [bind_ok, capability.Cap.is_null, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨r2, er2, h⟩ := bind_eq_ok h
    rcases copied_frame8 hl er2 with e2 | ⟨nc, e2⟩ <;> rw [e2] at h
    · simp only [br_err8, fr_same8, bind_ok] at h
      have e := ok_inj_ff h
      simp only [Prod.mk.injEq] at e
      exact Or.inr ⟨_, e.1.symm, e.2.symm⟩
    simp only [br_ok8, bind_ok] at h
    try simp only [bind_ok, uncurry_apply_pair] at h
    try dsimp only at h
    obtain ⟨b2, -, h⟩ := bind_eq_ok h
    by_cases hb2 : b2 = true
    · rw [if_pos hb2] at h
      unfold error.illegal at h
      simp only [bind_ok] at h
      have e := ok_inj_ff h
      simp only [Prod.mk.injEq] at e
      exact Or.inr ⟨_, e.1.symm, e.2.symm⟩
    rw [if_neg hb2] at h
    obtain ⟨x3, ex3, h⟩ := bind_eq_ok h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨x4, ex4, h⟩ := bind_eq_ok h
    have e := ok_inj_ff h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine Or.inl ⟨rfl, ?_⟩
    have K3 : KeepA (L := L) x t x3 := (KeepA.refl ha hr).sts F (Or.inl rfl) ex3
    have ag : ∀ b, SlotW K b → Aligned b → L.mem x3 b = L.mem x b := fun b hs hb =>
      K3.mem hb (UsrOK.notT8 F O (usu_of_slot8 hb hs))
    have hnx3 : ∀ nx, obj.Slot.next st src x3 = ok nx → nx ≠ 0#u64 → nx ∈ K.slots := fun nx en hne =>
      hnx nx (by rw [← next_agree hL hsK ag]; exact en) hne
    exact (KeepU.of_keepA K3).users F O (wi_usu8 (insert_keep8 hL hsK hdK hnx3 ex4))

/-- **The CNode decode at Copy / Mint** from the decode state `x`, with the target lookup as at `x`. -/
theorem cmDec8 {x : S} {a : A} {t lbl length buf cp cr cg cgb dest s1 src rp rr rg rgb fp rt asid va : U64}
    {sz : capability.FrameSize} {d mp : Bool} {ex : Aeneas.Std.Array obj.Slot 3#usize}
    (F : SchedOK (L := L) x t) (O : UsrOK (L := L) (KSU8 K) x t) (ha : L.actionW x = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING)
    (hL : Slot8 K) (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (hlk : cspace.lookup_target_slot st x (.CNode cp cr cg cgb) (L.mem x (regA t layout.reg.R10))
      (L.mem x (regA t layout.reg.R8)) = ok (.Ok dest))
    (hdK : dest ∈ K.slots) (hex : Aeneas.Std.Array.index_usize ex 0#usize = ok s1)
    (hrc : obj.Slot.cap st s1 x = ok (.CNode rp rr rg rgb))
    (hlss : cspace.lookup_source_slot st x (.CNode rp rr rg rgb) (L.mem x (regA t layout.reg.R9))
      (L.mem x (regA t layout.reg.R15)) = ok (.Ok src))
    (hsc : obj.Slot.cap st src x = ok (.Frame fp sz rt d mp false asid va)) (hsK : src ∈ K.slots)
    (hnx : ∀ nx, obj.Slot.next st src x = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
    {y : core.result.Result Unit error.Exc × S × A}
    (h : cnode.decode st ar x a lbl length (.CNode cp cr cg cgb) buf ex = ok y) :
    (y.1 = .Ok () ∧ KeepU st (KSU8 K) x t y.2.1) ∨ (∃ e, y.1 = .Err (.Sys e) ∧ y.2.1 = x) := by
  unfold cnode.decode at h
  rw [if_neg (lblC18 hl), if_neg (lblC28 hl)] at h
  by_cases h2 : length < 2#u64
  · rw [if_pos h2] at h
    unfold error.truncated at h
    simp only [bind_ok] at h
    cases ok_inj_ff h
    exact Or.inr ⟨_, rfl, rfl⟩
  rw [if_neg h2, cur_thread_ok, F.cur] at h
  simp only [bind_ok] at h
  rw [sarg0_reg, sarg1_reg, reg_ok, reg_ok] at h
  simp only [bind_ok] at h
  rw [hlk] at h
  simp only [bind_ok, br_ok8] at h
  rw [if_pos (lblC38 hl), if_pos (lblC48 hl)] at h
  obtain ⟨⟨r1, x1⟩, e1, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  cases ok_inj_ff h
  exact cmCopy8 F O ha hr hL hl hdK hex hrc hlss hsc hsK hnx e1

/-- **The block's st run**: decode then `invRep`, reply `Ok ()`, `KeepU` at `KSU8 K` from the decode state. -/
theorem cmRun8 {x : S} {a : A} {t lbl length buf slot cp cr cg cgb dest s1 src rp rr rg rgb fp rt asid va : U64}
    {sz : capability.FrameSize} {d mp : Bool} {ex : Aeneas.Std.Array obj.Slot 3#usize}
    (F : SchedOK (L := L) x t) (O : UsrOK (L := L) (KSU8 K) x t) (ha : L.actionW x = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING)
    (hL : Slot8 K) (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (hlk : cspace.lookup_target_slot st x (.CNode cp cr cg cgb) (L.mem x (regA t layout.reg.R10))
      (L.mem x (regA t layout.reg.R8)) = ok (.Ok dest))
    (hdK : dest ∈ K.slots) (hex : Aeneas.Std.Array.index_usize ex 0#usize = ok s1)
    (hrc : obj.Slot.cap st s1 x = ok (.CNode rp rr rg rgb))
    (hlss : cspace.lookup_source_slot st x (.CNode rp rr rg rgb) (L.mem x (regA t layout.reg.R9))
      (L.mem x (regA t layout.reg.R15)) = ok (.Ok src))
    (hsc : obj.Slot.cap st src x = ok (.Frame fp sz rt d mp false asid va)) (hsK : src ∈ K.slots)
    (hnx : ∀ nx, obj.Slot.next st src x = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
    (hbuf : ∀ b, msg.lookup_ipc_buffer st x true t = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)))
    {y : core.result.Result Unit error.Exc × S × A} {z : S × A × core.result.Result Unit error.Exc}
    (hy : syscall.decode_invocation st ar x a lbl length slot (.CNode cp cr cg cgb) true true true false buf ex
      = ok y)
    (hz : invRep st t y.2.1 y.2.2 y.1 = ok z) : z.2.2 = .Ok () ∧ KeepU st (KSU8 K) x t z.1 := by
  rw [decode_cnode_eq ar] at hy
  rcases cmDec8 ar F O ha hr hL hl hlk hdK hex hrc hlss hsc hsK hnx hy with ⟨hy1, k1⟩ | ⟨e, hy1, hy2⟩
  · rw [hy1] at hz
    exact invRep_ok_ku8 F O k1 hz
  · rw [hy1, hy2] at hz
    unfold invRep at hz
    obtain ⟨q0, eq0, hz⟩ := bind_eq_ok hz
    cases ok_inj_ff hz
    obtain ⟨s5, es5, e5⟩ := bind_eq_ok eq0
    cases ok_inj_ff e5
    refine ⟨rfl, ?_⟩
    exact reply_error_ku8 F O (KeepU.of_keepA (KeepA.refl ha hr))
      (fun b eb hne i hi => usu_of_user8 (hbuf b eb hne i hi)) es5

end run

/-! ## `FinOK` after the block -/

section fin
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

set_option maxHeartbeats 8000000 in
/-- (slhuf gen 12) **`FinOK` after the Copy / Mint decode block** (`delFin` / `truncFin`'s route, writes of
`IoTW t`, capability-slot and user words): at an accepted run's post-prefix state `s2` (`InvChk`), a decode of the
cap at the plan's slot at `CNodeCopy` / `CNodeMint` (any length), then `invRep`, reply `Ok ()` and leave `FinOK`.
Inputs: `IoPre` and `CMEnt` at the entry, the plan's slot a capability slot, [J] `InvBufJ8` at the entry, the write
set `W` covering the prefix words (`IoWr`) and the caller's `STATE` write (`SWr`). -/
theorem cmFin8 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {lbl length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A} {z : S × A × core.result.Result Unit error.Exc}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s) (hsw : SWr gS st (L.curW s) sched.TS_RUNNING)
    (E : CMEnt st K Cs Locks p s) (hsl : p.slot ∈ K.slots) (hbuf : InvBufJ8 st K s)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ FinOK (L := L) gS (IoRS (st := st) K Locks s) W ar s z.1 z.2.1 := by
  obtain ⟨cp, cr, cg, cgb, dest, x1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, Cw, hcs, hex, -, hlk,
    hrc, hlss, hsc, -, -, hC, hCr, hcl, hWk, hs1K, -, hdK, -, -, hsK, -, -, hnx⟩ := E
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
  -- the registers `R10`, `R8`, `R9`, `R15`
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
  have r9 : L.mem s2 (regA (L.curW s) layout.reg.R9) = L.mem s (regA (L.curW s) layout.reg.R9) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R9) (by simp [layout.reg.R9])
      (by simp [layout.reg.R9]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r15 : L.mem s2 (regA (L.curW s) layout.reg.R15) = L.mem s (regA (L.curW s) layout.reg.R15) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R15) (by simp [layout.reg.R15])
      (by simp [layout.reg.R15]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  -- the lookups at `s2`
  have slotK : ∀ p r, Cw p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s2 = obj.Slot.cap st (cnSlot p (x &&& m)) s :=
    fun p r hp m hm x => cap_agree hL (hWk p r m x hp hm).1 ag
  have hCn' : ∀ p1 r1 gs1 g1, capability.Cap.CNode cp cr cg cgb = .CNode p1 r1 gs1 g1 → Cw p1 r1 := by
    intro p1 r1 gs1 g1 e; cases e; exact hC
  have hCr' : ∀ p1 r1 gs1 g1, capability.Cap.CNode rp rr rg rgb = .CNode p1 r1 gs1 g1 → Cw p1 r1 := by
    intro p1 r1 gs1 g1 e; cases e; exact hCr
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
  have hlss2 : cspace.lookup_source_slot st s2 (.CNode rp rr rg rgb) (L.mem s2 (regA (L.curW s) layout.reg.R9))
      (L.mem s2 (regA (L.curW s) layout.reg.R15)) = ok (.Ok src) := by
    rw [r9, r15]
    unfold cspace.lookup_source_slot cspace.lookup_slot_for_cnode_op at hlss ⊢
    simp only [bind_ok, ↓reduceIte] at hlss ⊢
    by_cases d1 : L.mem s (regA (L.curW s) layout.reg.R15) < 1#u64
    · rw [if_pos d1] at hlss; simp at hlss
    rw [if_neg d1] at hlss ⊢
    by_cases d2 : L.mem s (regA (L.curW s) layout.reg.R15) > cspace.WORD_BITS
    · rw [if_pos d2] at hlss; simp at hlss
    rw [if_neg d2] at hlss ⊢
    unfold cspace.resolve_address_bits at hlss ⊢
    obtain ⟨res, eres, hl⟩ := bind_eq_ok hlss
    have eres' := rab_loop_congr2 st Cw slotK hcl 66 _ _ 65#u64 res (by simp) hCr' eres
    rw [eres']; simp only [bind_ok]; exact hl
  have hrc2 : obj.Slot.cap st x1 s2 = ok (.CNode rp rr rg rgb) := by
    rw [cap_agree hL hs1K ag]; exact hrc
  have hsc2 : obj.Slot.cap st src s2 = ok (.Frame fp sz rt d mp false asid va) := by
    rw [cap_agree hL hsK ag]; exact hsc
  have hnx2 : ∀ nx, obj.Slot.next st src s2 = ok nx → nx ≠ 0#u64 → nx ∈ K.slots := fun nx e h0 =>
    (hnx nx (by rw [← next_agree hL hsK ag]; exact e) h0).1
  have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
    lookup_buf_keep P.tA true tk
  have hbuf2 : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) := fun b eb hne i hi =>
    hbuf b (by rw [← hlb]; exact eb) hne i hi
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
  -- slot and user words miss the node, the TCB fields and the SC words
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ UserW (KSU8 K) (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact not_usu8 (P.node_notUser ho) (P.node_notSlot ho)
  have hmx : ¬ UserW (KSU8 K) (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact not_usu8 (P.sc_notUser (P.hSc _ P.cscS) I.F.q.2.2.2.1) (P.sc_notSlot (P.hSc _ P.cscS) I.F.q.2.2.2.1)
  have htU : ∀ t, K.heap t = some .tcb → ∀ k : U64, 192 ≤ k.val → k.val < 4096 →
      ¬ UserW (KSU8 K) (core.num.U64.wrapping_add t k) := fun t ht k h1 h2 =>
    not_usu8 (P.tcb_notUser ht h1 h2) (P.tcb_notSlot ht h1 h2)
  have O : UsrOK (L := L) (KSU8 K) s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => htU _ (P.hT _ P.cT) k h1 h2, hmx⟩
  -- the run
  have hex' : Aeneas.Std.Array.index_usize p.extra 0#usize = ok x1 := hex
  obtain ⟨hz2, kz⟩ := cmRun8 ar hK O ha2 hrun hL hl hlk2 hdK hex' hrc2 hlss2 hsc2 hsK hnx2 hbuf2 hy hz
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
  have ho' : ∀ b ∈ {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b}, ¬ UserW (KSU8 K) b := by
    rintro b ⟨-, c', hc', hin⟩
    exact not_usu8 (P.sc_notUser (P.hSc _ hc') hin) (P.sc_notSlot (P.hSc _ hc') hin)
  have stm : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 → ¬ UserW (KSU8 K) (tdA (L.mem s2 (tmA (L := L) s2))) :=
    fun h0 => by
      unfold tdA
      exact htU _ (I.tm h0) _ (by simp) (by simp)
  have srh : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → ¬ UserW (KSU8 K) (scA (L.mem s2 (rhA (L := L) s2))) ∧
      ¬ UserW (KSU8 K) (headA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))) ∧
      ¬ UserW (KSU8 K) (rtA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
        (L.rhead s2 (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2)))))) := fun h0 => by
    refine ⟨?_, ?_⟩
    · unfold scA; exact htU _ (F2'.rh h0).1 _ (by simp) (by simp)
    obtain ⟨zr, hW', hΩ⟩ := rh2' h0
    obtain ⟨h8, hmm, hfit⟩ := hW'.bounds
    obtain ⟨h96, -, -, hhd, -, hrt⟩ := hW'.inside
    obtain ⟨e1, e2, e3⟩ := hrt _ hW'.head_lt
    exact ⟨ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩),
      ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩)⟩
  have FIN := kz.fin hK O Q0 Hf.nd I.F.td I.F.rs stm srh
  have hcur3 : L.curW z.1 = L.curW s := kz.cur hK O
  have w3 : WritesIn st s2 z.1 (fun b => IoPW st s2 b ∨ UserW (KSU8 K) b) :=
    kz.1.mono fun b hb => hb.imp_left fun h => Or.inr (by rw [hct]; exact h)
  have Fz := F2'.frameU w3 hn2 (fun t ht k h1 h2 => htU t (P.hT t ht) k (by omega) h2) ho'
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

end Fl4Proofs.P2.PathObl

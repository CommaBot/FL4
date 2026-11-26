/-
# P2 (line pte, generation 15): footprints of the PageMap block's st run (`KeepU` at `KSUPm K`)

Copied from line slhuf's `P2/InvCMFin8.lean` (gen 13, int19 7443e8055: the `KSUPm` layout and the footprint
lemmas, verbatim but renamed with suffix `Pm`; that file itself cannot be copied unchanged, it imports
`InvCMEnt`, whose proofs step over the pre-#109 `plan_with`). `KSUPm K` is `K` with the capability-slot words
counted as user words, so InvTrunc's `KeepU` / `UsrOK` at `KSUPm K` are the "slot or user word" variants:

* `usu_of_userPm`, `usu_of_slotPm`, `not_usuPm`, `wi_usuPm`, `KU_regPm`, `KU_userPm`;
* footprints: `set_cap_keepPm`, `set_mr_kuPm`, `set_mrs_lf_kuPm`, `error_mrs_kuPm`, **`reply_error_kuPm`** (any
  `SysError`), `invRep_ok_kuPm`.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvTrunc8
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

/-- `K` with its capability-slot words counted as user words. -/
def KSUPm (K : KLayout) : KLayout := { K with user := {b | b ∈ K.user ∨ SlotW K b} }

section ksu
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s0 x y : S} {t : U64}

theorem usu_of_userPm {b : U64} (h : UserW K b) : UserW (KSUPm K) b := ⟨h.1, Or.inl h.2⟩

theorem usu_of_slotPm {b : U64} (ha : Aligned b) (h : SlotW K b) : UserW (KSUPm K) b := ⟨ha, Or.inr h⟩

theorem not_usuPm {b : U64} (h1 : ¬ UserW K b) (h2 : ¬ SlotW K b) : ¬ UserW (KSUPm K) b := fun h =>
  Or.elim h.2 (fun hu => h1 ⟨h.1, hu⟩) h2

theorem wi_usuPm (h : WritesIn st x y (SlotW K)) : WritesIn st x y (UserW (KSUPm K)) :=
  h.mono' fun b ha hs => usu_of_slotPm ha hs

theorem KU_regPm (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (h : KeepU st K s0 t x) {r v : U64}
    (hr : r.val < 384) : KeepU st K s0 t (L.wr x (regA t r) v) :=
  h.keepA ((KeepA.refl h.2.1 h.2.2).wr_reg (h.sched F O) hr)

theorem KU_userPm (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (h : KeepU st K s0 t x) {b v : U64}
    (hu : UserW K b) : KeepU st K s0 t (L.wr x b v) :=
  h.users F O ((writesIn_wr hu.1).mono fun _ e => by subst e; exact hu)

/-- A `KSUPm` user word is no `IoTW t` word (`UsrOK.tf`). -/
theorem UsrOK.notTPm {t b : U64} (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (hs : UserW K b) :
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

theorem set_cap_keepPm {x' : S} {q : U64} {c : capability.Cap} (hL : Slot8 K) (hq : q ∈ K.slots)
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


theorem set_mr_kuPm (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (hk : KeepU st K s0 t x)
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
    exact KU_regPm F O hk (post_of_ok (msg.msg_register.lt _) er1)
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
      exact KU_userPm F O hk (hb hne _ hv)
    · rw [if_neg hb0] at h
      cases ok_inj_ff h
      exact hk

theorem set_mrs_lf_kuPm (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (hk : KeepU st K s0 t x)
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
  have k1 : KeepU st K s0 t s1 := set_mr_kuPm F O hk hb (by simp) e1
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  cases lf with
  | InvalidRoot => cases ok_inj_ff h; exact k1
  | MissingCapability bl =>
    try simp only [lift, bind_ok] at h
    exact set_mr_kuPm F O k1 hb h1 h
  | DepthMismatch bf bl =>
    try simp only [lift, bind_ok] at h
    obtain ⟨⟨j, s2⟩, e2, h⟩ := bind_eq_ok h
    have k2 : KeepU st K s0 t s2 := set_mr_kuPm F O k1 hb h1 e2
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    try simp only [lift, bind_ok] at h
    exact set_mr_kuPm F O k2 hb h2 h
  | GuardMismatch gf bl gs =>
    try simp only [lift, bind_ok] at h
    obtain ⟨⟨j, s2⟩, e2, h⟩ := bind_eq_ok h
    have k2 : KeepU st K s0 t s2 := set_mr_kuPm F O k1 hb h1 e2
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    try simp only [lift, bind_ok] at h
    obtain ⟨⟨j', s3⟩, e3, h⟩ := bind_eq_ok h
    have k3 : KeepU st K s0 t s3 := set_mr_kuPm F O k2 hb h2 e3
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    try simp only [lift, bind_ok] at h
    exact set_mr_kuPm F O k3 hb h3 h

theorem error_mrs_kuPm (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (hk : KeepU st K s0 t x)
    {buf : U64} {e : error.SysError} {r : U64 × S}
    (hb : buf ≠ 0#u64 → ∀ j : U64, j.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul j 8#u64)))
    (h : syscall.error_mrs st x t buf e = ok r) : KeepU st K s0 t r.2 := by
  unfold syscall.error_mrs at h
  cases e with
  | InvalidArgument arg => exact set_mr_kuPm F O hk hb (by simp) h
  | InvalidCapability arg => exact set_mr_kuPm F O hk hb (by simp) h
  | IllegalOperation => cases ok_inj_ff h; exact hk
  | RangeError mn mx =>
    obtain ⟨⟨j, s1⟩, e1, h⟩ := bind_eq_ok h
    have k1 : KeepU st K s0 t s1 := set_mr_kuPm F O hk hb (by simp) e1
    try simp only [uncurry_apply_pair] at h
    try dsimp only at h
    exact set_mr_kuPm F O k1 hb (by simp) h
  | AlignmentError => cases ok_inj_ff h; exact hk
  | FailedLookup src lf =>
    cases src
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨j, s1⟩, e1, h⟩ := bind_eq_ok h
      have k1 : KeepU st K s0 t s1 := set_mr_kuPm F O hk hb (by simp) e1
      try simp only [uncurry_apply_pair] at h
      try dsimp only at h
      exact set_mrs_lf_kuPm F O k1 hb h
    · simp only [↓reduceIte] at h
      obtain ⟨⟨j, s1⟩, e1, h⟩ := bind_eq_ok h
      have k1 : KeepU st K s0 t s1 := set_mr_kuPm F O hk hb (by simp) e1
      try simp only [uncurry_apply_pair] at h
      try dsimp only at h
      exact set_mrs_lf_kuPm F O k1 hb h
  | TruncatedMessage => cases ok_inj_ff h; exact hk
  | DeleteFirst => cases ok_inj_ff h; exact hk
  | RevokeFirst => cases ok_inj_ff h; exact hk
  | NotEnoughMemory bytes => exact set_mr_kuPm F O hk hb (by simp) h

/-- **The error reply, any `SysError`, keeps `KeepU`** given the receiver's IPC buffer words are user words. -/
theorem reply_error_kuPm (F : SchedOK (L := L) s0 t) (O : UsrOK (L := L) K s0 t) (hk : KeepU st K s0 t x)
    (hbuf : ∀ b, msg.lookup_ipc_buffer st x true t = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)))
    {e : error.SysError} {z : S} (h : syscall.reply_error st x t e = ok z) : KeepU st K s0 t z := by
  unfold syscall.reply_error at h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  rw [set_reg_ok'] at h
  simp only [bind_ok] at h
  have u1 : KeepU st K s0 t (L.wr x (regA t layout.reg.BADGE) 0#u64) := KU_regPm F O hk rB384
  have hb : b ≠ 0#u64 → ∀ j : U64, j.val < 128 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul j 8#u64)) := hbuf b eb
  obtain ⟨⟨len, s2⟩, e2, h⟩ := bind_eq_ok h
  have u2 : KeepU st K s0 t s2 := error_mrs_kuPm F O u1 hb e2
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
      exact KU_userPm F O u2 (hb hne i hiv)
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
  exact KU_regPm F O uq rM384

/-- `invRep` of `Ok` from a `KeepU` state (InvBlkFin's `invRep_ok_keep` for `KeepU`). -/
theorem invRep_ok_kuPm {A : Type} {a : A} {z : S × A × core.result.Result Unit error.Exc}
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

end Fl4Proofs.P2.PathObl

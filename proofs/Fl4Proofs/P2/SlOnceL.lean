/-
# P2 (line slhuf, gen 7): `Once` through the user-word loop of the ReplyRecv fast path

The syscall entry's read set `SlRS` holds user words on purpose: the ReplyRecv fast path's
`handle_fault_reply` copies the handler's reply message from its IPC buffer
(`faults.copy_mrs_fault_reply_loop1`, `msg.buf_get`). User words are racy for `E2E.Once` whatever the
read set, so each must be read at most once and never after a user write to it.

Which user words the syscall entry touches (call closure of `syscall.handle_syscall_local`, 232
definitions): reads only in `faults.copy_mrs_fault_reply_loop1.body` (`msg.buf_get`, the sender's buffer
at index `i + 1` for the loop index `i`); writes only through `msg.buf_set` (`copy_mrs_fault_loop1`,
`set_mr`: the trap arm's receiver buffer, and `switch_to`'s tail). `msg.copy_mrs` (send buffer to receive
buffer) is not in the closure. So on the ReplyRecv arm every user read comes before every user write and
the reads are at distinct indices; on the trap arm there is no user read at all. The overlap risk of
`copy_mrs` (a write of the receive buffer read back through an overlapping send buffer) does not arise.

* `racy_monoR`, `tch_monoR`, **`once_monoR`**: `Once` for a smaller read set gives `Once` for a larger one.
* `l1W buf j`: the word iteration `j` of the loop reads; `l1W_val`, `l1W_ne` (distinct for distinct
  indices below 127).
* **`loop1_once`**: `Once` of the loop followed by any continuation, from a touched set holding none of the
  words the loop still reads (`L1Rd`), the receiver's register words not user words, and the continuation
  `Once` for every touched set at every state satisfying an invariant `P` that the receiver-register writes
  keep.

No premises.
-/
import Fl4Proofs.P2.OnceWalk
import Fl4Proofs.P2.VmOnce
import Fl4Proofs.P2.ProgGenL21
import Fl4Proofs.P2.AccessReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once)

section gen
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {User : U64 → Prop}

theorem racy_monoR {R R' : U64 → Prop} {Wd : Set U64} {q : U64} (hR : ∀ b, R b → R' b)
    (h : E2E.Racy R' User Wd q) : E2E.Racy R User Wd q := by
  unfold E2E.Racy at *
  rintro ⟨h1, h2⟩
  exact h ⟨h1, h2.imp_left (hR q)⟩

theorem tch_monoR {R R' : U64 → Prop} {Wd T T' : Set U64} {q : U64} (hR : ∀ b, R b → R' b)
    (hT : T' ⊆ T) : E2E.tch R' User Wd q T' ⊆ E2E.tch R User Wd q T := by
  by_cases h' : E2E.Racy R' User Wd q
  · have h := racy_monoR hR h'
    have e1 : E2E.tch R' User Wd q T' = insert q T' := by unfold E2E.tch; exact if_pos h'
    have e2 : E2E.tch R User Wd q T = insert q T := by unfold E2E.tch; exact if_pos h
    rw [e1, e2]
    exact Set.insert_subset_insert hT
  · have e1 : E2E.tch R' User Wd q T' = T' := by unfold E2E.tch; exact if_neg h'
    rw [e1]
    exact hT.trans E2E.tch_sub

/-- **`Once` for a smaller read set gives `Once` for a larger one** (fewer racy words), from a smaller
touched set. -/
theorem once_monoR {R R' : U64 → Prop} (hR : ∀ b, R b → R' b) {X : Type} (p : SProg X) :
    ∀ (Wd T T' : Set U64) (s : S) (a : A),
      Once st ar R User Wd T p s a → T' ⊆ T → Once st ar R' User Wd T' p s a := by
  induction p with
  | ret x => intros; simp only [Once]
  | err e => intros; simp only [Once]
  | rd q k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact ⟨fun hr hq => h.1 (racy_monoR hR hr) (hT hq),
      fun v hv => ih v _ _ _ s a (h.2 v hv) (tch_monoR hR hT)⟩
  | rdp q k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact ⟨fun hr hq => h.1 (racy_monoR hR hr) (hT hq),
      fun hr hq => h.2.1 (racy_monoR hR hr) (tch_monoR hR hT hq),
      fun v hv => ih v _ _ _ s a (h.2.2 v hv) (tch_monoR hR (tch_monoR hR hT))⟩
  | wr q v k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    intro s' hs'
    have h1 := h s' hs'
    by_cases hu : User q
    · simp only [if_pos hu] at h1 ⊢
      exact ih _ _ _ s' a h1 (Set.insert_subset_insert hT)
    · simp only [if_neg hu] at h1 ⊢
      exact ih _ _ _ s' a h1 hT
  | zero q n k ih => intro Wd T T' s a h; simp only [Once] at h
  | clr q n k ih => intro Wd T T' s a h; simp only [Once] at h
  | ksb k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ s a (h v hv) hT
  | cpu k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ s a (h v hv) hT
  | masks k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ s a (h v hv) hT
  | arch op k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v a' hv => ih v _ _ _ s a' (h v a' hv) hT

/-- **A guarded run whose continuation holds for every touched set**: a prefix on `guard st R0 W0` (`R0`
inside `R`, no user word; writes anywhere) makes no racy read. -/
theorem once_sbind_guardW {X Y : Type} {R R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → R q ∧ ¬ User q)
    (p : SProg X) (hz : NoZero p) (f : X → SProg Y) :
    ∀ (Wd T : Set U64) (s : S) (a : A) (r : X × S × A), interp (guard st R0 W0) ar p s a = ok r →
      (∀ Wd' T', Once st ar R User Wd' T' (f r.1) r.2.1 r.2.2) →
      Once st ar R User Wd T (p.sbind f) s a := by
  induction p with
  | ret x =>
    intro Wd T s a r h hf
    rw [interp_ret'] at h
    have e := ok_inj_ff h
    subst e
    exact hf Wd T
  | err e => intro Wd T s a r h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R0 q
    · rw [guard_read hq] at hv
      have nr : ¬ E2E.Racy R User Wd q := fun hr => hr ⟨(hR0 q hq).2, Or.inl (hR0 q hq).1⟩
      simp only [SProg.sbind, Once]
      refine ⟨fun hr => absurd hr nr, fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      exact ih _ (hz _) _ _ s a r hk hf
    · rw [guard_read_out hq] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R0 q ∧ R0 (core.num.U64.wrapping_add q 8#u64)
    · rw [guard_read_pair hq.1 hq.2] at hv
      have nr1 : ¬ E2E.Racy R User Wd q := fun hr => hr ⟨(hR0 q hq.1).2, Or.inl (hR0 q hq.1).1⟩
      have nr2 : ¬ E2E.Racy R User Wd (core.num.U64.wrapping_add q 8#u64) := fun hr =>
        hr ⟨(hR0 _ hq.2).2, Or.inl (hR0 _ hq.2).1⟩
      simp only [SProg.sbind, Once]
      refine ⟨fun hr => absurd hr nr1, fun hr => absurd hr nr2, fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      exact ih _ (hz _) _ _ s a r hk hf
    · have : (PathObl.guard st R0 W0).read_pair s q = fail .panic := by
        show (if R0 q ∧ R0 (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = _
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | wr q v k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨s', hv, hk⟩ := bok.mp h
    by_cases hq : W0 q
    · rw [guard_write hq] at hv
      simp only [SProg.sbind, Once]
      intro s'' hs''
      rw [hv] at hs''
      have e := ok_inj_ff hs''
      subst e
      exact ih hz _ _ s' a r hk hf
    · rw [guard_write_out hq] at hv; exact absurd hv fail_not_ok
  | zero q n k ih => exact absurd hz id
  | clr q n k ih => exact absurd hz id
  | ksb k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.ks_base s = ok v := hv
    simp only [SProg.sbind, Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) Wd T s a r hk hf
  | cpu k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.cur_cpu s = ok v := hv
    simp only [SProg.sbind, Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) Wd T s a r hk hf
  | masks k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.frame_masks s = ok v := hv
    simp only [SProg.sbind, Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) Wd T s a r hk hf
  | arch op k ih =>
    intro Wd T s a r h hf
    simp only [interp] at h
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    simp only [SProg.sbind, Once]
    intro v' a'' hv'
    rw [hv] at hv'
    obtain ⟨e1, e2⟩ := Prod.mk.inj (ok_inj_ff hv')
    subst e1
    subst e2
    exact ih _ (hz _) Wd T s _ r hk hf

/-- `once_sbind_guardW` in the run-hypothesis form of `once_gstep`. -/
theorem once_gstepW {X Y : Type} {R R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → R q ∧ ¬ User q)
    {p : SProg X} (hz : NoZero p) {k : X → SProg Y} {Wd T : Set U64}
    {s : S} {a : A} {r' : Y × S × A} (h : interp st ar (p.sbind k) s a = ok r')
    (hg : ∀ r, interp st ar p s a = ok r → interp (guard st R0 W0) ar p s a = ok r)
    (hk : ∀ r, interp st ar p s a = ok r → interp st ar (k r.1) r.2.1 r.2.2 = ok r' →
      ∀ Wd' T', Once st ar R User Wd' T' (k r.1) r.2.1 r.2.2) :
    Once st ar R User Wd T (p.sbind k) s a := by
  rw [interp_sbind] at h
  obtain ⟨r, h1, h2⟩ := bind_eq_ok' h
  exact once_sbind_guardW hR0 p hz k Wd T s a r (hg r h1) (hk r h1 h2)

end gen

/-! ## The loop -/

/-- The word iteration `j` of `copy_mrs_fault_reply_loop1` reads (`msg.buf_get buf (j + 1)`). -/
def l1W (buf : U64) (j : Usize) : U64 :=
  core.num.U64.wrapping_add buf
    (core.num.U64.wrapping_mul (core.num.U64.wrapping_add (UScalar.cast .U64 j) 1#u64) 8#u64)

theorem l1W_val (buf : U64) (j : Usize) (hj : j.val < 127) :
    (l1W buf j).val = (buf.val + 8 * (j.val + 1)) % 2 ^ 64 := by
  unfold l1W
  rw [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, core.num.U64.wrapping_add_val_eq,
    usize_cast_val]
  simp only [U64.size_def, U64.numBits]
  have e1 : (j.val + (1#u64).val) % 2 ^ 64 = j.val + 1 := by
    simp only [UScalar.ofNat_val_eq]; omega
  simp only [UScalarTy.numBits] at *
  rw [e1]
  have e2 : ((j.val + 1) * (8#u64).val) % 2 ^ 64 = 8 * (j.val + 1) := by
    simp only [UScalar.ofNat_val_eq]; omega
  rw [e2]

theorem l1W_ne (buf : U64) {i j : Usize} (hi : i.val < 127) (hj : j.val < 127) (h : i.val ≠ j.val) :
    l1W buf i ≠ l1W buf j := by
  intro e
  have e' := congrArg UScalar.val e
  rw [l1W_val buf i hi, l1W_val buf j hj] at e'
  have hb := buf.hBounds
  simp only [U64.size_def, U64.numBits, UScalarTy.numBits] at hb
  omega

/-- The words the loop still reads from index `i`. -/
def L1Rd (buf : U64) (i n : Usize) (q : U64) : Prop :=
  ∃ j : Usize, i.val ≤ j.val ∧ j.val < n.val ∧ q = l1W buf j

section loop
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {Rd User : U64 → Prop}

/-- **The loop over the sender's buffer reads each of its words once** (module docstring): by the
iteration budget. -/
theorem loop1_once_iter {Y : Type} (rcv : U64) (regs : Slice U64) (n : Usize) (buf : U64)
    (hreg : ∀ r ∈ regs.val, r.val < 384) (hn : n.val ≤ (Slice.len regs).val)
    (hl : (Slice.len regs).val < 127)
    (hrw : ∀ r : U64, r.val < 384 → ¬ User (regA rcv r))
    (P : S → A → Prop)
    (hP : ∀ s a r v s', P s a → r.val < 384 → st.write s (regA rcv r) v = ok s' → P s' a)
    (k : Unit → SProg Y) {r' : Y × S × A}
    (hk : ∀ s1 a1, P s1 a1 → interp st ar (k ()) s1 a1 = ok r' → ∀ Wd' T', Once st ar Rd User Wd' T' (k ()) s1 a1) :
    ∀ (m : Nat) (i : Usize) (s : S) (a : A) (Wd T : Set U64),
      (∀ q ∈ T, ¬ L1Rd buf i n q) → P s a →
      interp st ar ((SProg.iter (fun x => R.faults.copy_mrs_fault_reply_loop1.body rcv regs n buf x) m i).sbind k)
        s a = ok r' →
      Once st ar Rd User Wd T
        ((SProg.iter (fun x => R.faults.copy_mrs_fault_reply_loop1.body rcv regs n buf x) m i).sbind k) s a
  | 0, i, s, a, Wd, T, _, _, _ => by simp only [SProg.iter, SProg.sbind, Once]
  | m + 1, i, s, a, Wd, T, hT, hPs, h => by
    rw [SProg.iter, SProg.sbind_assoc] at h ⊢
    unfold R.faults.copy_mrs_fault_reply_loop1.body at h ⊢
    by_cases h1 : i < n
    swap
    · rw [if_neg h1] at h ⊢
      simp only [SProg.pure_eq_ret, SProg.sbind] at h ⊢
      exact hk s a hPs h Wd T
    rw [if_pos h1] at h ⊢
    by_cases h2 : i < Slice.len regs
    swap
    · simp only [if_neg h2] at h ⊢
      simp only [SProg.pure_eq_ret, SProg.sbind] at h ⊢
      exact hk s a hPs h Wd T
    simp only [if_pos h2] at h ⊢
    unfold R.msg.buf_get R.obj.Tcb.set_reg at h ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.read,
      SProg.write] at h ⊢
    refine once_liftR h (fun r hr h => ?_)
    have hj' : i.val < regs.length := by
      have := h2; simp only [Slice.len, UScalar.lt_equiv] at this ⊢; simpa using this
    have hrv : r.val < 384 := by
      rw [eq_ok_of_spec (Slice.index_usize_spec regs i hj')] at hr
      cases ok_inj_ff hr
      exact hreg _ (List.getElem_mem _)
    have hiv : i.val < n.val := by scalar_tac
    have hil : i.val < 127 := by omega
    simp only [Once]
    refine ⟨fun _ hq => hT _ hq ⟨i, le_refl _, hiv, rfl⟩, fun v hv => ?_⟩
    simp only [interp] at h
    obtain ⟨v', hv', h⟩ := bok.mp h
    rw [hv] at hv'
    cases ok_inj_ff hv'
    refine once_liftR h (fun i4 _ h => ?_)
    simp only [SProg.sbind, Once]
    intro s' hs'
    simp only [interp] at h
    obtain ⟨s'', hs'', h⟩ := bok.mp h
    rw [hs'] at hs''
    cases ok_inj_ff hs''
    have hu : ¬ User (regA rcv r) := hrw r hrv
    have hu' : ¬ User (core.num.U64.wrapping_add (core.num.U64.wrapping_add rcv layout.tcb.REGS)
        (core.num.U64.wrapping_mul r 8#u64)) := hu
    rw [if_neg hu', if_neg hu']
    refine once_liftR h (fun i5 hi5 h => ?_)
    obtain ⟨z, hz, hzv⟩ := spec_ex_fd (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [hz] at hi5
    cases ok_inj_ff hi5
    try simp only [SProg.sbind] at h ⊢
    refine loop1_once_iter rcv regs n buf hreg hn hl hrw P hP k hk m z s' a _ _ ?_ (hP s a r i4 s' hPs hrv hs') h
    intro q hq hR
    obtain ⟨j, hj1, hj2, rfl⟩ := hR
    have hzv' : z.val = i.val + 1 := by rw [hzv]; simp
    unfold E2E.tch at hq
    split at hq
    · rcases hq with e | hq
      · exact l1W_ne buf (by omega) hil (by omega) e
      · exact hT _ hq ⟨j, by omega, hj2, rfl⟩
    · exact hT _ hq ⟨j, by omega, hj2, rfl⟩

end loop

end Fl4Proofs.P2.PathObl

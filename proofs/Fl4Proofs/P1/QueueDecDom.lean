/-
P1: InvGaps' `domain` family: `domain.decode` (SetSet, ScheduleConfigure,
ScheduleSetStart) keeps the invariants, from `DecPre`.  SetSet is the
caller's restart and `set_domain` (`set_domain.blkF`); the schedule
invocations write kernel-global words (outside the frame words, so cap-slot
words for `blk_of_capw`) and reschedule.
-/
import Fl4Proofs.P1.QueueDecSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- A write of a kernel-global word keeps `BlkOK`. -/
theorem obj.ks_set.blk (s : S) (o v : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ho : o.val < 13568)
    (h8 : o.val % 8 = 0) :
    obj.ks_set st s o v ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.curW s' = L.curW s ∧
      L.ksb s' = L.ksb s ∧ (∀ y ∈ T, ∀ K : U64, 192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ⦄ := by
  refine WP.spec_mono (obj.ks_set.spec s o v) fun s' e => ?_
  subst e
  have h0 := h.1.choose_spec.choose_spec
  have hSg := h.2.2.2.2
  have hw := writesIn_wr (st := st) (s := s) (v := v) (ks_aligned h0 ho h8)
  obtain ⟨b1, -, ec, -, -, f, -, -⟩ := blk_of_capw h hw fun b e => Or.inr ⟨e ▸ hSg.ksΩ o ho h8, fun hb => by
    have := hSg.ks b hb; rw [e, ks_val h0 ho] at this; omega⟩
  exact ⟨b1, ec, hw.1, f⟩

theorem DecPost.ok_bxi {s s' : S} {Ac' : Set U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s') :
    DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s (.Ok ()) s' := DecPost.of_bxi h (by simp)

theorem sched.set_dom_sched.blk (s : S) (i d du : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hi : i.val < 1) :
    sched.set_dom_sched st s i d du ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hi0 : i = 0#u64 := UScalar.eq_of_val_eq (by simp; omega)
  subst hi0
  unfold sched.set_dom_sched layout.ks.DOM_SCHEDULE
  simp only [lift, bind_ok, layout.WORD]
  step as ⟨w, hw⟩
  have o1 : (core.num.U64.wrapping_add w (core.num.U64.wrapping_mul 0#u64 16#u64)).val = 192 := by
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, hw]
  have o2 : (core.num.U64.wrapping_add (core.num.U64.wrapping_add w (core.num.U64.wrapping_mul 0#u64 16#u64))
      8#u64).val = 200 := by
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, hw]
  refine WP.spec_bind (obj.ks_set.blk s _ d h (by rw [o1]; omega) (by rw [o1])) fun s1 h1 => ?_
  exact WP.spec_mono (obj.ks_set.blk s1 _ du h1.1 (by rw [o2]; omega) (by rw [o2])) fun s2 h2 => h2.1

set_option maxHeartbeats 2000000 in
/-- **`domain.decode`** keeps the invariants. -/
theorem domain.decode.dec (s : S) (lbl len buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s .Domain extra) :
    domain.decode st s lbl len buf extra ⦃ r => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h := D.bxi
  have hct : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  have Er : ∀ e : error.SysError, (ok ((core.result.Result.Err (error.Exc.Sys e) : core.result.Result Unit error.Exc),
      s) : Result _) ⦃ r => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := fun e =>
    (WP.spec_ok _).2 (DecPost.of_bxi h (by simp))
  have RS := sched.set_thread_state.restart_blk (Es := ∅) s _ h.blk hct (runnable_ok D.run).1 (runnable_ok D.run).2
  unfold domain.decode
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  simp only [error.illegal, error.truncated, error.invalid_cap, error.invalid_arg, error.range, bind_ok]
  split
  · -- SetSet
    split
    · exact Er _
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dom _ => ?_
    split
    · exact Er _
    have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl hsl => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · exact Er _
    rename_i h0
    refine WP.spec_bind (D.extra s (WritesIn.refl _ _) sl (hsl ▸ List.getElem_mem hl0) (by simpa using h0))
      fun c hc => ?_
    cases c
    all_goals first | exact Er _ | skip
    rename_i ptr
    have hpT : ptr ∈ T := hc.2.1 ptr rfl
    dsimp only
    refine WP.spec_bind RS fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (sched.set_domain.blkF s2 ptr dom h2 hpT) fun s3 ⟨h3, _⟩ => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  have CF : ∀ index dom du : U64, index.val < 1 → (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      let s2 ← sched.set_dom_sched st s1 index dom du
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2)) ⦃ r =>
        DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := fun index dom du hi =>
    WP.spec_bind RS fun s2 ⟨h2, _, _, _⟩ =>
      WP.spec_bind (sched.set_dom_sched.blk s2 index dom du h2 hi) fun s3 h3 =>
        (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  split
  · -- ScheduleConfigure
    split
    · exact Er _
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun index _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dom _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun du _ => ?_
    simp only [layout.NUM_DOMAIN_SCHEDULES, fl4_abi.config.NUM_DOMAIN_SCHEDULES]
    step as ⟨i, hi⟩
    split
    · step*
      all_goals exact Er _
    rename_i hix
    have hix' : index.val < 1 := by simp at hix hi; omega
    split
    · step as ⟨i1, _⟩
      exact DecPost.of_bxi h (by simp)
    unfold domain.MAX_DURATION
    step as ⟨m1, _⟩
    step as ⟨m2, _⟩
    have KG : ∀ {P : Prop} [Decidable P] (k : Result ((core.result.Result Unit error.Exc) × S)),
        k ⦃ r => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ →
        (do
          let i2 ← obj.ks_get st s layout.ks.DOM_SCHED_START
          if index = i2 then k
          else do
            let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
            let s2 ← sched.set_dom_sched st s1 index dom du
            ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2)) ⦃ r =>
              DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := fun k hk => by
      refine WP.spec_bind (P0.obj.ks_get.p0 st s _ hS) fun i2 _ => ?_
      split
      · exact hk
      · exact CF _ _ _ hix'
    split
    · exact Er _
    split
    · split
      · exact Er _
      · refine KG (P := True) _ ?_
        first | exact CF _ _ _ hix' | exact Er _ | (split <;> first | exact Er _ | exact CF _ _ _ hix')
    · refine KG (P := True) _ ?_
      first | exact CF _ _ _ hix' | exact Er _ | (split <;> first | exact Er _ | exact CF _ _ _ hix')
  split
  · -- ScheduleSetStart
    split
    · exact Er _
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun index _ => ?_
    simp only [layout.NUM_DOMAIN_SCHEDULES, fl4_abi.config.NUM_DOMAIN_SCHEDULES]
    split
    · step as ⟨i, _⟩
      exact DecPost.of_bxi h (by simp)
    refine WP.spec_bind (sched.dom_sched_duration.spec s index) fun i _ => ?_
    split
    · exact Er _
    refine WP.spec_bind RS fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (obj.ks_set.blk s2 _ index h2 (by simp [layout.ks.DOM_SCHED_START])
      (by simp [layout.ks.DOM_SCHED_START])) fun s3 h3 => ?_
    refine WP.spec_bind (obj.ks_set.blk s3 _ 0#u64 h3.1 (by simp [layout.ks.DOMAIN_TIME])
      (by simp [layout.ks.DOMAIN_TIME])) fun s4 h4 => ?_
    step as ⟨i1, _⟩
    refine WP.spec_bind (obj.ks_set.blk s4 _ i1 h4.1 (by simp [layout.ks.DOM_SCHED_IDX])
      (by simp [layout.ks.DOM_SCHED_IDX])) fun s5 h5 => ?_
    refine WP.spec_bind (sched.reschedule_required.blk s5 h5.1) fun s6 h6 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h6.1))
  · exact Er _

/-- **InvGaps' `domain`, discharged.** -/
theorem decGap_domain {A : Type _} (ar : machine.Arch A) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .domain := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · refine WP.spec_bind (domain.decode.dec s lbl len buf extra D) ?_
    rintro ⟨r, s1⟩ hr
    exact (WP.spec_ok _).2 hr

end

end Fl4Proofs.P1

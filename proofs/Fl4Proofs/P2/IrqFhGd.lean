/-
# P2 (line p3mc, gen 23): runs on a store checking writes by state, moved between states; the tail's totality

Handoff §27b item 1, the generic part of `irq_fh_annV`. `PathObl.gd st R P` (P2/GSt) answers reads in `R` and lets
a write through when `P` holds of the state, the address and the value (no `zero` / `clear_free`).

* **`interp_agree_gd`**: `interp_agree` (P2/PathAgree) for `gd`: a run from `s` gives a run from every state that
  agrees with `s` on `R` (and on the kernel base, the core and the frame masks), with the same answer and Arch value,
  when `P` is decided by the words of `R` (`hP`) and every write `P` admits is aligned.
* **`interp_gd_to`**: a run on `gd st R P` is the same run on any store answering the reads in `R` as `st` and the
  writes `P` admits as `st` (a larger `gd`, a `guard` whose write set holds what `P` admits, or `st` itself).
* `irqTailF_total`: the timer interrupt's tail (`irqTailF`, P2/IrqTailE) is total (`p0_split`, as P0's
  `handle_timer_irq_local.p0`).
* `current_ok.guardC2`: `current_ok.guardC` (P2/FootTimerIrqDec) with the current SC's `CORE` word asked for only
  where the current thread's `SC` word names the current SC (the only place `current_ok` reads it).

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.IrqFhHead
import Fl4Proofs.P2.SafeTrWr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Classical

section
variable {S A X : Type} {st : machine.Store S} {ar : machine.Arch A} {R : U64 → Prop}
  {P : S → U64 → U64 → Prop}

/-- **A run on `gd` transfers to agreeing states** (module docstring). -/
theorem interp_agree_gd [L : LawfulStore st] (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hRal : ∀ w, R w → Aligned w) (hPal : ∀ x q v, P x q v → Aligned q)
    (hP : ∀ x x' q v, (∀ w, R w → L.mem x' w = L.mem x w) → P x q v → P x' q v) (p : SProg X) (hz : NoZero p) :
    ∀ (s s' : S) (a : A) (x : X) (s1 : S) (a1 : A), L.ksb s' = L.ksb s → L.cpu s' = L.cpu s →
      st.frame_masks s' = st.frame_masks s → (∀ w, R w → L.mem s' w = L.mem s w) →
      interp (gd st R P) ar p s a = ok (x, s1, a1) →
      ∃ s1', interp (gd st R P) ar p s' a = ok (x, s1', a1) := by
  induction p with
  | ret x =>
    intro s s' a y s1 a1 _ _ _ _ h
    simp only [interp] at h ⊢
    obtain ⟨rfl, -, rfl⟩ := by simpa using Result.ok_injective h
    exact ⟨s', rfl⟩
  | err e => intro s s' a y s1 a1 _ _ _ _ h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : (if R q then st.read s q else fail .panic) = ok v := hv
    by_cases hq : R q
    · rw [if_pos hq, L.read_eq, ← e4 q hq, ← L.read_eq] at hv'
      obtain ⟨s1', h'⟩ := ih v (hz v) s s' a y s1 a1 e1 e2 e3 e4 hk
      refine ⟨s1', bok.mpr ⟨v, ?_, h'⟩⟩
      show (if R q then st.read s' q else fail .panic) = ok v
      rw [if_pos hq]; exact hv'
    · rw [if_neg hq] at hv'; exact absurd hv' fail_not_ok
  | rdp q k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : (if R q ∧ R (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = ok v := hv
    by_cases hq : R q ∧ R (core.num.U64.wrapping_add q 8#u64)
    · rw [if_pos hq, L.read_pair_eq, ← e4 q hq.1, ← e4 _ hq.2, ← L.read_pair_eq] at hv'
      obtain ⟨s1', h'⟩ := ih v (hz v) s s' a y s1 a1 e1 e2 e3 e4 hk
      refine ⟨s1', bok.mpr ⟨v, ?_, h'⟩⟩
      show (if R q ∧ R (core.num.U64.wrapping_add q 8#u64) then st.read_pair s' q else fail .panic) = ok v
      rw [if_pos hq]; exact hv'
    · rw [if_neg hq] at hv'; exact absurd hv' fail_not_ok
  | wr q v k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨s2, hv, hk⟩ := bok.mp h
    have hv' : (if P s q v then st.write s q v else fail .panic) = ok s2 := hv
    by_cases hq : P s q v
    · rw [if_pos hq, L.write_eq] at hv'
      obtain rfl := Result.ok_injective hv'
      have ha := hPal s q v hq
      obtain ⟨s1', h'⟩ := ih hz (L.wr s q v) (L.wr s' q v) a y s1 a1 (by rw [L.ksb_wr, L.ksb_wr, e1])
        (by rw [L.cpu_wr, L.cpu_wr, e2]) (by rw [hm, hm, e3])
        (fun w hw => by
          rw [L.mem_wr _ _ _ _ ha (hRal w hw), L.mem_wr _ _ _ _ ha (hRal w hw), e4 w hw]) hk
      refine ⟨s1', bok.mpr ⟨L.wr s' q v, ?_, h'⟩⟩
      show (if P s' q v then st.write s' q v else fail .panic) = ok (L.wr s' q v)
      rw [if_pos (hP s s' q v e4 hq), L.write_eq]
    · rw [if_neg hq] at hv'; exact absurd hv' fail_not_ok
  | zero q n k ih => exact absurd hz id
  | clr q n k ih => exact absurd hz id
  | ksb k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    obtain ⟨s1', h'⟩ := ih v (hz v) s s' a y s1 a1 e1 e2 e3 e4 hk
    refine ⟨s1', bok.mpr ⟨v, ?_, h'⟩⟩
    show st.ks_base s' = ok v
    have : st.ks_base s = ok v := hv
    rw [L.ks_base_eq] at this ⊢; rw [e1]; exact this
  | cpu k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    obtain ⟨s1', h'⟩ := ih v (hz v) s s' a y s1 a1 e1 e2 e3 e4 hk
    refine ⟨s1', bok.mpr ⟨v, ?_, h'⟩⟩
    show st.cur_cpu s' = ok v
    have : st.cur_cpu s = ok v := hv
    rw [L.cur_cpu_eq] at this ⊢; rw [e2]; exact this
  | masks k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    obtain ⟨s1', h'⟩ := ih v (hz v) s s' a y s1 a1 e1 e2 e3 e4 hk
    refine ⟨s1', bok.mpr ⟨v, ?_, h'⟩⟩
    show st.frame_masks s' = ok v
    have : st.frame_masks s = ok v := hv
    rw [e3]; exact this
  | arch op k ih =>
    intro s s' a y s1 a1 e1 e2 e3 e4 h
    simp only [interp] at h ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    obtain ⟨s1', h'⟩ := ih v (hz v) s s' a' y s1 a1 e1 e2 e3 e4 hk
    exact ⟨s1', bok.mpr ⟨(v, a'), hv, h'⟩⟩

/-- **A run on `gd` is the same run on a store answering its reads and admitted writes as `st`** (module
docstring). -/
theorem interp_gd_to {st' : machine.Store S} (hr : ∀ s q, R q → st'.read s q = st.read s q)
    (hp : ∀ s q, R q → R (core.num.U64.wrapping_add q 8#u64) → st'.read_pair s q = st.read_pair s q)
    (hw : ∀ s q v, P s q v → st'.write s q v = st.write s q v)
    (h1 : st'.ks_base = st.ks_base) (h2 : st'.cur_cpu = st.cur_cpu) (h3 : st'.frame_masks = st.frame_masks)
    (p : SProg X) :
    ∀ (s : S) (a : A) (r : X × S × A), interp (gd st R P) ar p s a = ok r → interp st' ar p s a = ok r := by
  induction p with
  | ret x => intro s a r h; exact h
  | err e => intro s a r h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : (if R q then st.read s q else fail .panic) = ok v := hv
    by_cases hq : R q
    · rw [if_pos hq] at hv'
      exact bok.mpr ⟨v, by rw [hr s q hq]; exact hv', ih v s a r hk⟩
    · rw [if_neg hq] at hv'; exact absurd hv' fail_not_ok
  | rdp q k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : (if R q ∧ R (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = ok v := hv
    by_cases hq : R q ∧ R (core.num.U64.wrapping_add q 8#u64)
    · rw [if_pos hq] at hv'
      exact bok.mpr ⟨v, by rw [hp s q hq.1 hq.2]; exact hv', ih v s a r hk⟩
    · rw [if_neg hq] at hv'; exact absurd hv' fail_not_ok
  | wr q v k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    have hv' : (if P s q v then st.write s q v else fail .panic) = ok s' := hv
    by_cases hq : P s q v
    · rw [if_pos hq] at hv'
      exact bok.mpr ⟨s', by rw [hw s q v hq]; exact hv', ih s' a r hk⟩
    · rw [if_neg hq] at hv'; exact absurd hv' fail_not_ok
  | zero q n k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨s', hv, _⟩ := bok.mp h
    exact absurd hv fail_not_ok
  | clr q n k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨s', hv, _⟩ := bok.mp h
    exact absurd hv fail_not_ok
  | ksb k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, by rw [h1]; exact hv, ih v s a r hk⟩
  | cpu k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, by rw [h2]; exact hv, ih v s a r hk⟩
  | masks k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, by rw [h3]; exact hv, ih v s a r hk⟩
  | arch op k ih =>
    intro s a r h
    simp only [interp] at h ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨(v, a'), hv, ih v s a' r hk⟩

/-- A run on `gd st R P` is a run on `guard st R' W` when `R ⊆ R'` and `P` admits only `W` words. -/
theorem interp_gd_guard {R' W : U64 → Prop} (hR : ∀ q, R q → R' q) (hW : ∀ x q v, P x q v → W q) (p : SProg X)
    (s : S) (a : A) (r : X × S × A) (h : interp (gd st R P) ar p s a = ok r) :
    interp (guard st R' W) ar p s a = ok r :=
  interp_gd_to (fun _ q hq => guard_read (hR q hq)) (fun _ q h1 h2 => guard_read_pair (hR q h1) (hR _ h2))
    (fun _ q _ hq => guard_write (hW _ q _ hq)) rfl rfl rfl p s a r h

/-- A run on `gd st R P` is a run on `gd st R' P'` for `R ⊆ R'`, `P ⊆ P'`. -/
theorem interp_gd_mono {R' : U64 → Prop} {P' : S → U64 → U64 → Prop} (hR : ∀ q, R q → R' q)
    (hP : ∀ x q v, P x q v → P' x q v) (p : SProg X) (s : S) (a : A) (r : X × S × A)
    (h : interp (gd st R P) ar p s a = ok r) : interp (gd st R' P') ar p s a = ok r :=
  interp_gd_to (fun s q hq => by
      show (if R' q then st.read s q else fail .panic) = _
      rw [if_pos (hR q hq)])
    (fun s q h1 h2 => by
      show (if R' q ∧ R' (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = _
      rw [if_pos ⟨hR q h1, hR _ h2⟩])
    (fun s q v hq => gd_write (hP s q v hq)) rfl rfl rfl p s a r h

/-- A run on `gd st R P` is the run on `st`. -/
theorem interp_gd_st (p : SProg X) (s : S) (a : A) (r : X × S × A) (h : interp (gd st R P) ar p s a = ok r) :
    interp st ar p s a = ok r :=
  interp_gd_to (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rfl rfl rfl p s a r h

end

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (irqTailF bind_guard_congr)

section tot
variable {S : Type} {A : Type} (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **The tail is total** (module docstring). -/
theorem irqTailF_p0 (s : S) (a : A) (irq cpu : U64) (p : localtimer.TimerIrqPlan) (hS : P0.StoreTotal st)
    (hA : P0.ArchTotal ar) : irqTailF st ar s a irq cpu p ⦃ _ => True ⦄ := by
  unfold irqTailF; p0_split

end tot

section g
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R]

/-- **`current_ok` on the guarded store** (module docstring): as `current_ok.guardC`, the current SC's `CORE` word
asked for only where the current thread's `SC` word is the current SC (nonzero). -/
theorem current_ok.guardC2 (s : S) (cpu ct csc : U64) (hc0 : csc ≠ 0#u64) (h1 : R (affA ct))
    (h : L.mem s (affA ct) = cpu → R (stA ct) ∧ R (yieldA ct) ∧ R (core.num.U64.wrapping_add ct 3664#u64) ∧
      R (scA ct) ∧ (L.mem s (scA ct) ≠ 0#u64 → R (scCoreA (L.mem s (scA ct)))) ∧
      R (L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD) ∧ R (domA ct) ∧
      R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)) :
    localtimer.current_ok gS s cpu ct csc = localtimer.current_ok st s cpu ct csc := by
  unfold localtimer.current_ok
  rw [may_run_here.guardC s cpu ct h1 (fun ha => by
    obtain ⟨a2, a3, a4, a5, a6, -⟩ := h ha
    exact ⟨a2, a3, a4, a5, a6⟩)]
  refine bind_guard_congr rfl fun b eb => ?_
  cases b
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  obtain ⟨-, haff, -, -⟩ := may_run_here_true eb
  obtain ⟨-, -, -, a5, a6, a8, a9, a10⟩ := h haff
  rw [if_pos rfl, if_pos rfl, PathObl.obj.Tcb.sc.guard ct s a5, eq_of_spec_fd (obj.Tcb.sc.spec s ct)]
  simp only [bind_ok]
  by_cases hi : L.mem s (scA ct) = csc
  · have a7 := a6 (by rw [hi]; exact hc0)
    rw [hi] at a7
    rw [if_pos hi, if_pos hi, PathObl.obj.Sc.cpu.guard csc s a7, PathObl.sched.idle_thread.guard s a8,
      PathObl.obj.Tcb.domain.guard ct s a9, PathObl.sched.cur_domain.guard s a10]
  · rw [if_neg hi, if_neg hi]

end g

end Fl4Proofs.P2

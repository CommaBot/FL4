/-
P2: **the bridge from the per-path obligation to the trace form**
(`P2/PathObl.lean`, module docstring).

* `interp_guard` (projection and trace): a run of a trait-call tree on the
  guarded store that succeeds is the same run on the real store, and every
  access along it lies in the guard's sets (`Within`).
* `PathObl.within`: for a body that is a trait-call tree (`IsProg` [P]) and
  meets `PathObl.access` [W], every access of its sequential run lies in
  `ReadSet` / `WriteSet` of the entry state.
* `PathObl.allowed_steps` (accepted runs) / `allowed_steps_dec` (declined
  runs): with `read_own` / `write_own`, every kernel read of an accepted run is
  in `RPerm` and every kernel write of either is in `WPerm` of the entry
  state's ownership;
  these are `Serial.Allowed`'s conditions for the path's steps (the owners a
  path holds do not change under its own writes, `Serial.inv_wr`, nor under
  other cores' steps, `Serial.InvH`).

## Premises

* **The trait-call schema** [P], stated once: *every extracted body generic
  over `machine.Store` is `IsProg f p` for some trait-call tree `p`*. Lean has
  no parametricity theorem, so this cannot be proved for the extracted terms in
  general, and Lean cannot quantify over "extracted" functions; the theorems
  below take `IsProg f p` as a hypothesis, always this one schema. Why it
  holds: `fl4-core` is `#![forbid(unsafe_code)]`, has no globals, `Cell`s,
  atomics or raw pointers (AGENTS.md), and reaches memory only through the
  `Store` trait; a function generic in `S: Store` cannot inspect `S`, so its
  memory behaviour is the sequence of trait calls it makes, each depending only
  on earlier results; Charon/Aeneas (trusted, DESIGN §9) keep that sequence,
  threading the state value only through the trait methods. The sim's
  footprint oracle exercises the same fact on the real store.
* `PathObl` [W], per local path (`PathObl.lean`).

## Sets fixed at entry, memory moving during the run

`PathObl.within` bounds the accesses of the *sequential* run from the entry
state `s` by `ReadSet s` / `WriteSet s`, sets computed once from `s`. In an
interleaved execution the path's run is that same run: `Serial`'s simulation
invariant (`LocInv.sim`) shows every value it reads in its permitted set is the
value the sequential run from the entry state (with its own writes) reads,
because no other core writes a word in its permission while it runs; the
permission itself does not change meanwhile (`Serial.inv_wr`: other cores'
writes change no owner the path holds or the gate owns; its own writes move
owners only between owners it holds). So the interleaved run makes exactly the
accesses of the sequential one, and the entry-state sets bound them.
-/
import Fl4Proofs.P2.PathObl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

noncomputable section
open Classical

variable {S : Type} {A X : Type}

theorem bok {α β : Type _} {m : Result α} {f : α → Result β} {r : β} :
    m >>= f = ok r ↔ ∃ x, m = ok x ∧ f x = ok r := by
  cases m with
  | ret x =>
    rw [bind_tc_ok]
    exact ⟨fun h => ⟨x, rfl, h⟩, fun ⟨y, hy, h⟩ => by rw [Result.ok_injective hy]; exact h⟩
  | vis e k =>
    rw [bind_tc_vis]
    exact ⟨fun h => absurd h vis_not_ok, fun ⟨_, hy, _⟩ => absurd hy vis_not_ok⟩
  | div =>
    rw [bind_tc_div]
    exact ⟨fun h => absurd h div_not_ok, fun ⟨_, hy, _⟩ => absurd hy div_not_ok⟩

/-- Every access of the run of `p` on `st` from `(s, a)` lies in `R` (reads)
and `W` (writes). -/
def Within (st : machine.Store S) (R W : U64 → Prop) : SProg A X → S → A → Prop
  | .ret _, _, _ => True
  | .err _, _, _ => True
  | .rd q k, s, a => R q ∧ ∀ v, st.read s q = ok v → Within st R W (k v) s a
  | .rdp q k, s, a => R q ∧ R (core.num.U64.wrapping_add q 8#u64) ∧
      ∀ v, st.read_pair s q = ok v → Within st R W (k v) s a
  | .wr q v k, s, a => W q ∧ ∀ s', st.write s q v = ok s' → Within st R W k s' a
  | .zero q n k, s, a => (∀ b, InRange q n b → W b) ∧
      ∀ s', st.zero s q n = ok s' → Within st R W k s' a
  | .clr q n k, s, a => (∀ b, InRange q n b → W b) ∧
      ∀ s', st.clear_free s q n = ok s' → Within st R W k s' a
  | .ksb k, s, a => ∀ v, st.ks_base s = ok v → Within st R W (k v) s a
  | .cpu k, s, a => ∀ v, st.cur_cpu s = ok v → Within st R W (k v) s a
  | .masks k, s, a => ∀ v, st.frame_masks s = ok v → Within st R W (k v) s a
  | .eff g k, s, a => ∀ b a', g a = ok (b, a') → Within st R W (k b) s a'

/-- **Projection and trace**: a successful guarded run is the real run, and
all its accesses lie in the guard's sets. -/
theorem interp_guard {st : machine.Store S} {R W : U64 → Prop} (p : SProg A X) :
    ∀ (s : S) (a : A) (r : X × S × A), interp (guard st R W) p s a = ok r →
      interp st p s a = ok r ∧ Within st R W p s a := by
  induction p with
  | ret x => intro s a r h; exact ⟨h, trivial⟩
  | err e => intro s a r h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q
    · rw [guard_read hq] at hv
      obtain ⟨h1, h2⟩ := ih v s a r hk
      refine ⟨?_, ?_⟩
      · simp only [interp]; exact bok.mpr ⟨v, hv, h1⟩
      · simp only [Within]
        exact ⟨hq, fun v' hv' => by obtain rfl := Result.ok_injective (hv.symm.trans hv'); exact h2⟩
    · rw [guard_read_out hq] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q ∧ R (core.num.U64.wrapping_add q 8#u64)
    · rw [guard_read_pair hq.1 hq.2] at hv
      obtain ⟨h1, h2⟩ := ih v s a r hk
      refine ⟨?_, ?_⟩
      · simp only [interp]; exact bok.mpr ⟨v, hv, h1⟩
      · simp only [Within]
        exact ⟨hq.1, hq.2, fun v' hv' => by obtain rfl := Result.ok_injective (hv.symm.trans hv'); exact h2⟩
    · have : (guard st R W).read_pair s q = fail .panic := by
        show (if R q ∧ R (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q
          else fail .panic) = _
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | wr q v k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨s', hv, hk⟩ := bok.mp h
    by_cases hq : W q
    · rw [guard_write hq] at hv
      obtain ⟨h1, h2⟩ := ih s' a r hk
      refine ⟨?_, ?_⟩
      · simp only [interp]; exact bok.mpr ⟨s', hv, h1⟩
      · simp only [Within]
        exact ⟨hq, fun s'' hv' => by obtain rfl := Result.ok_injective (hv.symm.trans hv'); exact h2⟩
    · rw [guard_write_out hq] at hv; exact absurd hv fail_not_ok
  | zero q n k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨s', hv, hk⟩ := bok.mp h
    by_cases hq : ∀ b, InRange q n b → W b
    · rw [guard_zero hq] at hv
      obtain ⟨h1, h2⟩ := ih s' a r hk
      refine ⟨?_, ?_⟩
      · simp only [interp]; exact bok.mpr ⟨s', hv, h1⟩
      · simp only [Within]
        exact ⟨hq, fun s'' hv' => by obtain rfl := Result.ok_injective (hv.symm.trans hv'); exact h2⟩
    · have : (guard st R W).zero s q n = fail .panic := by
        show (if ∀ b, InRange q n b → W b then st.zero s q n else fail .panic) = _
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | clr q n k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨s', hv, hk⟩ := bok.mp h
    by_cases hq : ∀ b, InRange q n b → W b
    · rw [guard_clear_free hq] at hv
      obtain ⟨h1, h2⟩ := ih s' a r hk
      refine ⟨?_, ?_⟩
      · simp only [interp]; exact bok.mpr ⟨s', hv, h1⟩
      · simp only [Within]
        exact ⟨hq, fun s'' hv' => by obtain rfl := Result.ok_injective (hv.symm.trans hv'); exact h2⟩
    · have : (guard st R W).clear_free s q n = fail .panic := by
        show (if ∀ b, InRange q n b → W b then st.clear_free s q n else fail .panic) = _
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | ksb k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    obtain ⟨h1, h2⟩ := ih v s a r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨v, hv, h1⟩
    · simp only [Within]
      exact fun v' hv' => by
        have hv0 : st.ks_base s = ok v := hv
        obtain rfl := Result.ok_injective (hv0.symm.trans hv'); exact h2
  | cpu k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    obtain ⟨h1, h2⟩ := ih v s a r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨v, hv, h1⟩
    · simp only [Within]
      exact fun v' hv' => by
        have hv0 : st.cur_cpu s = ok v := hv
        obtain rfl := Result.ok_injective (hv0.symm.trans hv'); exact h2
  | masks k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    obtain ⟨h1, h2⟩ := ih v s a r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨v, hv, h1⟩
    · simp only [Within]
      exact fun v' hv' => by
        have hv0 : st.frame_masks s = ok v := hv
        obtain rfl := Result.ok_injective (hv0.symm.trans hv'); exact h2
  | eff g k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨⟨b, a'⟩, hv, hk⟩ := bok.mp h
    obtain ⟨h1, h2⟩ := ih b s a' r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨(b, a'), hv, h1⟩
    · simp only [Within]
      intro b' a'' hv'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective (hv.symm.trans hv'))
      exact h2

/-- Every write of the run of `p` on `st` from `(s, a)` satisfies `Q` between
the states before and after it. -/
def WithinM (st : machine.Store S) (Q : S → S → Prop) : SProg A X → S → A → Prop
  | .ret _, _, _ => True
  | .err _, _, _ => True
  | .rd q k, s, a => ∀ v, st.read s q = ok v → WithinM st Q (k v) s a
  | .rdp q k, s, a => ∀ v, st.read_pair s q = ok v → WithinM st Q (k v) s a
  | .wr q v k, s, a => ∀ s', st.write s q v = ok s' → Q s s' ∧ WithinM st Q k s' a
  | .zero q n k, s, a => ∀ s', st.zero s q n = ok s' → Q s s' ∧ WithinM st Q k s' a
  | .clr q n k, s, a => ∀ s', st.clear_free s q n = ok s' → Q s s' ∧ WithinM st Q k s' a
  | .ksb k, s, a => ∀ v, st.ks_base s = ok v → WithinM st Q (k v) s a
  | .cpu k, s, a => ∀ v, st.cur_cpu s = ok v → WithinM st Q (k v) s a
  | .masks k, s, a => ∀ v, st.frame_masks s = ok v → WithinM st Q (k v) s a
  | .eff g k, s, a => ∀ b a', g a = ok (b, a') → WithinM st Q (k b) s a'

/-- A checked write that succeeds is the real write, and the check held. -/
theorem mchk {st : machine.Store S} {Q : S → S → Prop} {s s'' : S} {m : Result S}
    (h : (do let s' ← m; if Q s s' then ok s' else fail .panic) = ok s'') :
    m = ok s'' ∧ Q s s'' := by
  obtain ⟨s', hm, hq⟩ := bok.mp h
  by_cases hQ : Q s s'
  · rw [if_pos hQ] at hq
    obtain rfl := Result.ok_injective hq
    exact ⟨hm, hQ⟩
  · rw [if_neg hQ] at hq; exact absurd hq fail_not_ok

/-- **Projection and per-write check**: a successful run on `mguard` is the
real run, and every write along it satisfies the check. -/
theorem interp_mguard {st : machine.Store S} {Q : S → S → Prop} (p : SProg A X) :
    ∀ (s : S) (a : A) (r : X × S × A), interp (mguard st Q) p s a = ok r →
      interp st p s a = ok r ∧ WithinM st Q p s a := by
  induction p with
  | ret x => intro s a r h; exact ⟨h, trivial⟩
  | err e => intro s a r h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : st.read s q = ok v := hv
    obtain ⟨h1, h2⟩ := ih v s a r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨v, hv', h1⟩
    · simp only [WithinM]
      exact fun v' hv'' => by obtain rfl := Result.ok_injective (hv'.symm.trans hv''); exact h2
  | rdp q k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : st.read_pair s q = ok v := hv
    obtain ⟨h1, h2⟩ := ih v s a r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨v, hv', h1⟩
    · simp only [WithinM]
      exact fun v' hv'' => by obtain rfl := Result.ok_injective (hv'.symm.trans hv''); exact h2
  | wr q v k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨s', hv, hk⟩ := bok.mp h
    obtain ⟨hw, hQ⟩ := mchk (st := st) hv
    obtain ⟨h1, h2⟩ := ih s' a r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨s', hw, h1⟩
    · simp only [WithinM]
      exact fun s'' hv'' => by
        obtain rfl := Result.ok_injective (hw.symm.trans hv''); exact ⟨hQ, h2⟩
  | zero q n k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨s', hv, hk⟩ := bok.mp h
    obtain ⟨hw, hQ⟩ := mchk (st := st) hv
    obtain ⟨h1, h2⟩ := ih s' a r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨s', hw, h1⟩
    · simp only [WithinM]
      exact fun s'' hv'' => by
        obtain rfl := Result.ok_injective (hw.symm.trans hv''); exact ⟨hQ, h2⟩
  | clr q n k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨s', hv, hk⟩ := bok.mp h
    obtain ⟨hw, hQ⟩ := mchk (st := st) hv
    obtain ⟨h1, h2⟩ := ih s' a r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨s', hw, h1⟩
    · simp only [WithinM]
      exact fun s'' hv'' => by
        obtain rfl := Result.ok_injective (hw.symm.trans hv''); exact ⟨hQ, h2⟩
  | ksb k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : st.ks_base s = ok v := hv
    obtain ⟨h1, h2⟩ := ih v s a r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨v, hv', h1⟩
    · simp only [WithinM]
      exact fun v' hv'' => by obtain rfl := Result.ok_injective (hv'.symm.trans hv''); exact h2
  | cpu k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : st.cur_cpu s = ok v := hv
    obtain ⟨h1, h2⟩ := ih v s a r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨v, hv', h1⟩
    · simp only [WithinM]
      exact fun v' hv'' => by obtain rfl := Result.ok_injective (hv'.symm.trans hv''); exact h2
  | masks k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv' : st.frame_masks s = ok v := hv
    obtain ⟨h1, h2⟩ := ih v s a r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨v, hv', h1⟩
    · simp only [WithinM]
      exact fun v' hv'' => by obtain rfl := Result.ok_injective (hv'.symm.trans hv''); exact h2
  | eff g k ih =>
    intro s a r h
    simp only [interp] at h
    obtain ⟨⟨b, a'⟩, hv, hk⟩ := bok.mp h
    obtain ⟨h1, h2⟩ := ih b s a' r hk
    refine ⟨?_, ?_⟩
    · simp only [interp]; exact bok.mpr ⟨(b, a'), hv, h1⟩
    · simp only [WithinM]
      intro b' a'' hv'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective (hv.symm.trans hv'))
      exact h2

/-- Accesses of a run within sets stay within larger ones. -/
theorem Within.mono {st : machine.Store S} {R W R' W' : U64 → Prop}
    (hR : ∀ b, R b → R' b) (hW : ∀ b, W b → W' b) (p : SProg A X) :
    ∀ (s : S) (a : A), Within st R W p s a → Within st R' W' p s a := by
  induction p with
  | ret x => intro _ _ _; trivial
  | err e => intro _ _ _; trivial
  | rd q k ih =>
    intro s a h; simp only [Within] at h ⊢
    exact ⟨hR _ h.1, fun v hv => ih v s a (h.2 v hv)⟩
  | rdp q k ih =>
    intro s a h; simp only [Within] at h ⊢
    exact ⟨hR _ h.1, hR _ h.2.1, fun v hv => ih v s a (h.2.2 v hv)⟩
  | wr q v k ih =>
    intro s a h; simp only [Within] at h ⊢
    exact ⟨hW _ h.1, fun s' hv => ih s' a (h.2 s' hv)⟩
  | zero q n k ih =>
    intro s a h; simp only [Within] at h ⊢
    exact ⟨fun b hb => hW _ (h.1 b hb), fun s' hv => ih s' a (h.2 s' hv)⟩
  | clr q n k ih =>
    intro s a h; simp only [Within] at h ⊢
    exact ⟨fun b hb => hW _ (h.1 b hb), fun s' hv => ih s' a (h.2 s' hv)⟩
  | ksb k ih => intro s a h; simp only [Within] at h ⊢; exact fun v hv => ih v s a (h v hv)
  | cpu k ih => intro s a h; simp only [Within] at h ⊢; exact fun v hv => ih v s a (h v hv)
  | masks k ih => intro s a h; simp only [Within] at h ⊢; exact fun v hv => ih v s a (h v hv)
  | eff g k ih =>
    intro s a h; simp only [Within] at h ⊢
    exact fun b a' hv => ih b s a' (h b a' hv)

section obl
variable {st : machine.Store S} [L : LawfulStore st]
  {f : machine.Store S → S → A → Result (X × S × A)} {Acc : X → Prop}
  {own : (U64 → U64) → U64 → Serial.Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop}
  {RS WS DS : S → U64 → Prop}

/-- **Accepted runs, trace form**: every access of an accepted sequential run
lies in its stated sets. -/
theorem PathObl.within {p : SProg A X} (hp : IsProg f p)
    (O : PathObl st f Acc own cls ko User Locks Pre RS WS DS) {s : S} {a : A} {r : X × S × A}
    (hpre : Pre s) (h : f st s a = ok r) (hacc : Acc r.1) : Within st (RS s) (WS s) p s a := by
  have hg := O.acc s a r hpre h hacc
  rw [hp (guard st (RS s) (WS s))] at hg
  exact (interp_guard p s a r hg).2

/-- **Declined runs, trace form**: every write of a declined sequential run
lies in `DecSet`. -/
theorem PathObl.within_dec {p : SProg A X} (hp : IsProg f p)
    (O : PathObl st f Acc own cls ko User Locks Pre RS WS DS) {s : S} {a : A} {r : X × S × A}
    (hpre : Pre s) (h : f st s a = ok r) (hdec : ¬ Acc r.1) :
    Within st (fun _ => True) (DS s) p s a := by
  have hg := O.dec hpre h hdec
  rw [hp (guard st (fun _ => True) (DS s))] at hg
  exact (interp_guard p s a r hg).2

/-- The guarded run is the real one (projection), accepted runs. -/
theorem PathObl.same {p : SProg A X} (hp : IsProg f p)
    (O : PathObl st f Acc own cls ko User Locks Pre RS WS DS) {s : S} {a : A} {r : X × S × A}
    (hpre : Pre s) (h : f st s a = ok r) (hacc : Acc r.1) :
    f (guard st (RS s) (WS s)) s a = f st s a := by
  rw [O.acc s a r hpre h hacc, h]

/-- **Ownership along an accepted run**: every read is a user word or in
`RPerm`, every write a user word or in `WPerm`, of the entry state. -/
theorem PathObl.allowed_steps {p : SProg A X} (hp : IsProg f p)
    (O : PathObl st f Acc own cls ko User Locks Pre RS WS DS) {s : S} {a : A} {r : X × S × A}
    (hpre : Pre s) (h : f st s a = ok r) (hacc : Acc r.1) :
    Within st (fun b => User b ∨ RPerm own (L.cpu s) (Locks s) (L.mem s) b)
      (fun b => User b ∨ WPerm own (L.cpu s) (Locks s) (L.mem s) b) p s a := by
  refine Within.mono (fun b hb => ?_) (fun b hb => ?_) p s a (O.within hp hpre h hacc)
  · by_cases hu : User b
    · exact Or.inl hu
    · exact Or.inr (O.read_own s b hpre hb hu)
  · by_cases hu : User b
    · exact Or.inl hu
    · exact Or.inr (O.write_own s b hpre (Or.inl hb) hu)

/-- **Ownership along a declined run**: every write is a user word or in
`WPerm` of the entry state. -/
theorem PathObl.allowed_steps_dec {p : SProg A X} (hp : IsProg f p)
    (O : PathObl st f Acc own cls ko User Locks Pre RS WS DS) {s : S} {a : A} {r : X × S × A}
    (hpre : Pre s) (h : f st s a = ok r) (hdec : ¬ Acc r.1) :
    Within st (fun _ => True)
      (fun b => User b ∨ WPerm own (L.cpu s) (Locks s) (L.mem s) b) p s a := by
  refine Within.mono (fun _ _ => trivial) (fun b hb => ?_) p s a (O.within_dec hp hpre h hdec)
  by_cases hu : User b
  · exact Or.inl hu
  · exact Or.inr (O.write_own s b hpre (Or.inr hb) hu)

/-- **Owners and classes along the run**: every write of the body's sequential
run passes `StepOK` (the per-step `Serial.Allowed` write conditions). -/
theorem PathObl.move_steps {p : SProg A X} (hp : IsProg f p)
    (O : PathObl st f Acc own cls ko User Locks Pre RS WS DS) {s : S} {a : A} {r : X × S × A}
    (hpre : Pre s) (h : f st s a = ok r) :
    WithinM st (fun x y => StepOK own cls ko User (L.cpu s) (Locks s) (L.mem x) (L.mem y))
      p s a := by
  have hg := O.move s a r hpre h
  rw [hp (mguard st _)] at hg
  exact (interp_mguard p s a r hg).2

end obl

end

end Fl4Proofs.P2.PathObl

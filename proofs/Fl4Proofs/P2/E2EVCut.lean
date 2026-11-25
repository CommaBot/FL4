/-
P2 (line vlift): **cutting a path's read set to `rsV K RS` generically**, for the paths the `userV` route
(`E2EVUser`) does not cover (a `ReadSet` holding user words: `SlRS`, `MaxR`).

`LocalPath.cutV P hA` is `P` with `ReadSet := rsV K P.RS` (`RS` minus the VCPU data words, `E2EVTop.rsV`),
so `NoVcpuRd` holds by definition (`noVcpuRd_cutV`). What the path must still show is **`AvoidV`** [W],
about the words its runs actually read, and nothing about its declines' writes, owners, classes, read
multiplicity or alignment, which carry over:

* `AvoidV.acc`: an accepted run is a run on `guard (rsV K RS s) (WS s)` (its `acc` for the cut set:
  re-running the path's guard walk with each read word shown outside the VCPUs);
* `AvoidV.dec`: from every alternative (`Alt` for the *old* `RS`) of a declining entry, the run reads no
  VCPU data word.

How the rest carries over (the generic part): an alternative `s'` for the cut set may differ from the entry at
the VCPU data words of `RS`; writing those words back (`wrs`, finitely many: `U64` is finite) gives an
alternative `s''` for the old `RS`, equal to `s'` on every aligned non-`VData` word (`AgOff`). The run from
`s''` reads only aligned non-`VData` words (from `AvoidV` and `read_aligned`) and writes only aligned words
(`WS` / `DS`), so the run from `s'` follows it step for step (`sim_off`): same result value, same accesses
(`dec_alt`'s guarded run, `read_aligned`), same per-write checks (`sim_offM`, with `own`'s congruence off the
VCPUs and `ko = .free` on them) and the same racy reads (`sim_offO`, `ReadOnce`).

For an *accepting* entry the alternative's run is the accepted run's trace (it reads only `RS` words, equal at
`s''`), so `AvoidV` needs nothing about it.
-/
import Fl4Proofs.P2.E2EVUser
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.Serial (Owner ClsOwner)

noncomputable section
open Classical

instance u64_finite : Finite U64 :=
  Finite.of_injective (fun x : U64 => (⟨x.val, x.hBounds⟩ : Fin (2 ^ UScalarTy.U64.numBits)))
    (fun _ _ h => UScalar.eq_of_val_eq (congrArg Fin.val h))

/-! ## Two states equal off a set of words -/

section sim
variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A} {E : U64 → Prop}

/-- `σ1` and `σ2` agree on the constants and on every aligned word outside `E`. -/
structure AgOff (st : machine.Store S) [L : LawfulStore st] (E : U64 → Prop) (σ1 σ2 : S) : Prop where
  cpu : L.cpu σ1 = L.cpu σ2
  ksb : L.ksb σ1 = L.ksb σ2
  masks : st.frame_masks σ1 = st.frame_masks σ2
  mem : ∀ b, Aligned b → ¬ E b → L.mem σ1 b = L.mem σ2 b

theorem AgOff.wr (hmk : MasksWr st) {σ1 σ2 : S} (h : AgOff st E σ1 σ2) {q : U64} (hq : Aligned q) (v : U64) :
    AgOff st E (L.wr σ1 q v) (L.wr σ2 q v) where
  cpu := by rw [L.cpu_wr, L.cpu_wr, h.cpu]
  ksb := by rw [L.ksb_wr, L.ksb_wr, h.ksb]
  masks := by rw [hmk, hmk, h.masks]
  mem b hb hE := by
    rw [L.mem_wr _ _ _ _ hq hb, L.mem_wr _ _ _ _ hq hb]
    split_ifs
    · rfl
    · exact h.mem b hb hE

variable {G W R U : U64 → Prop}

/-- **The run from `σ1` follows the run from `σ2`** when they agree off `E` and the `σ2` run reads only
aligned words outside `E` (`G`) and writes only aligned words (`W`); `Once` at `σ2` rules out ranges. -/
theorem sim_off (hmk : MasksWr st) (hG : ∀ b, G b → Aligned b ∧ ¬ E b) (hW : ∀ b, W b → Aligned b)
    (p : SProg X) :
    ∀ (σ1 σ2 : S) (a : A) (Wd T : Set U64), AgOff st E σ1 σ2 → Within st ar G W p σ2 a →
      Once st ar R U Wd T p σ2 a →
      Within st ar G W p σ1 a ∧
      (∀ r2, interp st ar p σ2 a = ok r2 →
        ∃ σ1', interp st ar p σ1 a = ok (r2.1, σ1', r2.2.2) ∧ AgOff st E σ1' r2.2.1) := by
  induction p with
  | ret x =>
    intro σ1 σ2 a Wd T hA _ _
    refine ⟨trivial, fun r2 h => ?_⟩
    simp only [interp] at h
    obtain rfl := Result.ok_injective h
    exact ⟨σ1, rfl, hA⟩
  | err e =>
    intro σ1 σ2 a Wd T _ _ _
    exact ⟨trivial, fun r2 h => absurd h fail_not_ok⟩
  | rd q k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    have hv2 : st.read σ2 q = ok (L.mem σ2 q) := L.read_eq _ _
    have e : L.mem σ1 q = L.mem σ2 q := hA.mem q (hG q hW2.1).1 (hG q hW2.1).2
    have ih' := ih (L.mem σ2 q) σ1 σ2 a Wd _ hA (hW2.2 _ hv2) (hO.2 _ hv2)
    refine ⟨⟨hW2.1, fun v hv => ?_⟩, fun r2 h => ?_⟩
    · rw [L.read_eq, e] at hv; obtain rfl := Result.ok_injective hv; exact ih'.1
    · simp only [interp] at h ⊢
      obtain ⟨v, hv, hk⟩ := bok.mp h
      rw [hv2] at hv; obtain rfl := Result.ok_injective hv
      obtain ⟨σ1', h1, h2⟩ := ih'.2 r2 hk
      exact ⟨σ1', bok.mpr ⟨_, by rw [L.read_eq, e], h1⟩, h2⟩
  | rdp q k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    have hv2 : st.read_pair σ2 q = ok (L.mem σ2 q, L.mem σ2 (core.num.U64.wrapping_add q 8#u64)) :=
      L.read_pair_eq _ _
    have e1 : L.mem σ1 q = L.mem σ2 q := hA.mem q (hG q hW2.1).1 (hG q hW2.1).2
    have e2 : L.mem σ1 (core.num.U64.wrapping_add q 8#u64) = L.mem σ2 (core.num.U64.wrapping_add q 8#u64) :=
      hA.mem _ (hG _ hW2.2.1).1 (hG _ hW2.2.1).2
    have ih' := ih _ σ1 σ2 a Wd _ hA (hW2.2.2 _ hv2) (hO.2.2 _ hv2)
    refine ⟨⟨hW2.1, hW2.2.1, fun v hv => ?_⟩, fun r2 h => ?_⟩
    · rw [L.read_pair_eq, e1, e2] at hv; obtain rfl := Result.ok_injective hv; exact ih'.1
    · simp only [interp] at h ⊢
      obtain ⟨v, hv, hk⟩ := bok.mp h
      rw [hv2] at hv; obtain rfl := Result.ok_injective hv
      obtain ⟨σ1', h1, h2⟩ := ih'.2 r2 hk
      exact ⟨σ1', bok.mpr ⟨_, by rw [L.read_pair_eq, e1, e2], h1⟩, h2⟩
  | wr q v k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    have hw2 : st.write σ2 q v = ok (L.wr σ2 q v) := L.write_eq _ _ _
    have ih' := ih (L.wr σ1 q v) (L.wr σ2 q v) a _ _ (hA.wr hmk (hW q hW2.1) v) (hW2.2 _ hw2) (hO _ hw2)
    refine ⟨⟨hW2.1, fun s' hs => ?_⟩, fun r2 h => ?_⟩
    · rw [L.write_eq] at hs; obtain rfl := Result.ok_injective hs; exact ih'.1
    · simp only [interp] at h ⊢
      obtain ⟨s', hs, hk⟩ := bok.mp h
      rw [hw2] at hs; obtain rfl := Result.ok_injective hs
      obtain ⟨σ1', h1, h2⟩ := ih'.2 r2 hk
      exact ⟨σ1', bok.mpr ⟨_, L.write_eq _ _ _, h1⟩, h2⟩
  | zero q n k ih => intro _ _ _ _ _ _ _ hO; simp only [Once] at hO
  | clr q n k ih => intro _ _ _ _ _ _ _ hO; simp only [Once] at hO
  | ksb k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    have hv2 : st.ks_base σ2 = ok (L.ksb σ2) := L.ks_base_eq _
    have ih' := ih (L.ksb σ2) σ1 σ2 a Wd T hA (hW2 _ hv2) (hO _ hv2)
    refine ⟨fun v hv => ?_, fun r2 h => ?_⟩
    · rw [L.ks_base_eq, hA.ksb] at hv; obtain rfl := Result.ok_injective hv; exact ih'.1
    · simp only [interp] at h ⊢
      obtain ⟨v, hv, hk⟩ := bok.mp h
      rw [hv2] at hv; obtain rfl := Result.ok_injective hv
      obtain ⟨σ1', h1, h2⟩ := ih'.2 r2 hk
      exact ⟨σ1', bok.mpr ⟨_, by rw [L.ks_base_eq, hA.ksb], h1⟩, h2⟩
  | cpu k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    have hv2 : st.cur_cpu σ2 = ok (L.cpu σ2) := L.cur_cpu_eq _
    have ih' := ih (L.cpu σ2) σ1 σ2 a Wd T hA (hW2 _ hv2) (hO _ hv2)
    refine ⟨fun v hv => ?_, fun r2 h => ?_⟩
    · rw [L.cur_cpu_eq, hA.cpu] at hv; obtain rfl := Result.ok_injective hv; exact ih'.1
    · simp only [interp] at h ⊢
      obtain ⟨v, hv, hk⟩ := bok.mp h
      rw [hv2] at hv; obtain rfl := Result.ok_injective hv
      obtain ⟨σ1', h1, h2⟩ := ih'.2 r2 hk
      exact ⟨σ1', bok.mpr ⟨_, by rw [L.cur_cpu_eq, hA.cpu], h1⟩, h2⟩
  | masks k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    obtain ⟨mk, hv2⟩ := masks_ok st σ2
    have ih' := ih mk σ1 σ2 a Wd T hA (hW2 _ hv2) (hO _ hv2)
    refine ⟨fun v hv => ?_, fun r2 h => ?_⟩
    · rw [hA.masks, hv2] at hv; obtain rfl := Result.ok_injective hv; exact ih'.1
    · simp only [interp] at h ⊢
      obtain ⟨v, hv, hk⟩ := bok.mp h
      rw [hv2] at hv; obtain rfl := Result.ok_injective hv
      obtain ⟨σ1', h1, h2⟩ := ih'.2 r2 hk
      exact ⟨σ1', bok.mpr ⟨_, by rw [hA.masks, hv2], h1⟩, h2⟩
  | arch op k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    refine ⟨fun v a' hv => (ih v σ1 σ2 a' Wd T hA (hW2 v a' hv) (hO v a' hv)).1, fun r2 h => ?_⟩
    simp only [interp] at h ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    obtain ⟨σ1', h1, h2⟩ := (ih v σ1 σ2 a' Wd T hA (hW2 v a' hv) (hO v a' hv)).2 r2 hk
    exact ⟨σ1', bok.mpr ⟨(v, a'), hv, h1⟩, h2⟩

/-- **The per-write checks carry over** along `sim_off`. -/
theorem sim_offM (hmk : MasksWr st) (hG : ∀ b, G b → Aligned b ∧ ¬ E b) (hW : ∀ b, W b → Aligned b)
    {Q1 Q2 : S → S → Prop}
    (hQ : ∀ σ1 σ2 q v, AgOff st E σ1 σ2 → W q → Q2 σ2 (L.wr σ2 q v) → Q1 σ1 (L.wr σ1 q v)) (p : SProg X) :
    ∀ (σ1 σ2 : S) (a : A) (Wd T : Set U64), AgOff st E σ1 σ2 → Within st ar G W p σ2 a →
      Once st ar R U Wd T p σ2 a → WithinM st ar Q2 p σ2 a → WithinM st ar Q1 p σ1 a := by
  induction p with
  | ret x => intros; simp only [WithinM]
  | err e => intros; simp only [WithinM]
  | rd q k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO hM
    simp only [Within, Once, WithinM] at hW2 hO hM ⊢
    have hv2 : st.read σ2 q = ok (L.mem σ2 q) := L.read_eq _ _
    have e : L.mem σ1 q = L.mem σ2 q := hA.mem q (hG q hW2.1).1 (hG q hW2.1).2
    intro v hv
    rw [L.read_eq, e] at hv; obtain rfl := Result.ok_injective hv
    exact ih _ σ1 σ2 a Wd _ hA (hW2.2 _ hv2) (hO.2 _ hv2) (hM _ hv2)
  | rdp q k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO hM
    simp only [Within, Once, WithinM] at hW2 hO hM ⊢
    have hv2 : st.read_pair σ2 q = ok (L.mem σ2 q, L.mem σ2 (core.num.U64.wrapping_add q 8#u64)) :=
      L.read_pair_eq _ _
    have e1 : L.mem σ1 q = L.mem σ2 q := hA.mem q (hG q hW2.1).1 (hG q hW2.1).2
    have e2 : L.mem σ1 (core.num.U64.wrapping_add q 8#u64) = L.mem σ2 (core.num.U64.wrapping_add q 8#u64) :=
      hA.mem _ (hG _ hW2.2.1).1 (hG _ hW2.2.1).2
    intro v hv
    rw [L.read_pair_eq, e1, e2] at hv; obtain rfl := Result.ok_injective hv
    exact ih _ σ1 σ2 a Wd _ hA (hW2.2.2 _ hv2) (hO.2.2 _ hv2) (hM _ hv2)
  | wr q v k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO hM
    simp only [Within, Once, WithinM] at hW2 hO hM ⊢
    have hw2 : st.write σ2 q v = ok (L.wr σ2 q v) := L.write_eq _ _ _
    intro s' hs
    rw [L.write_eq] at hs; obtain rfl := Result.ok_injective hs
    exact ⟨hQ σ1 σ2 q v hA hW2.1 (hM _ hw2).1,
      ih _ _ a _ _ (hA.wr hmk (hW q hW2.1) v) (hW2.2 _ hw2) (hO _ hw2) (hM _ hw2).2⟩
  | zero q n k ih => intro _ _ _ _ _ _ _ hO; simp only [Once] at hO
  | clr q n k ih => intro _ _ _ _ _ _ _ hO; simp only [Once] at hO
  | ksb k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO hM
    simp only [Within, Once, WithinM] at hW2 hO hM ⊢
    have hv2 : st.ks_base σ2 = ok (L.ksb σ2) := L.ks_base_eq _
    intro v hv
    rw [L.ks_base_eq, hA.ksb] at hv; obtain rfl := Result.ok_injective hv
    exact ih _ σ1 σ2 a Wd T hA (hW2 _ hv2) (hO _ hv2) (hM _ hv2)
  | cpu k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO hM
    simp only [Within, Once, WithinM] at hW2 hO hM ⊢
    have hv2 : st.cur_cpu σ2 = ok (L.cpu σ2) := L.cur_cpu_eq _
    intro v hv
    rw [L.cur_cpu_eq, hA.cpu] at hv; obtain rfl := Result.ok_injective hv
    exact ih _ σ1 σ2 a Wd T hA (hW2 _ hv2) (hO _ hv2) (hM _ hv2)
  | masks k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO hM
    simp only [Within, Once, WithinM] at hW2 hO hM ⊢
    intro v hv
    rw [hA.masks] at hv
    exact ih _ σ1 σ2 a Wd T hA (hW2 _ hv) (hO _ hv) (hM _ hv)
  | arch op k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO hM
    simp only [Within, Once, WithinM] at hW2 hO hM ⊢
    exact fun v a' hv => ih v σ1 σ2 a' Wd T hA (hW2 v a' hv) (hO v a' hv) (hM v a' hv)

theorem racy_congr {R1 R2 : U64 → Prop} {Wd : Set U64} {q : U64} (h : R1 q ↔ R2 q) :
    Racy R1 U Wd q ↔ Racy R2 U Wd q := by
  unfold Racy; rw [h]

theorem tch_congr {R1 R2 : U64 → Prop} {Wd T : Set U64} {q : U64} (h : R1 q ↔ R2 q) :
    tch R1 U Wd q T = tch R2 U Wd q T := by
  unfold tch; rw [propext (racy_congr (U := U) (Wd := Wd) h)]

/-- **The racy reads carry over** along `sim_off`, for read sets agreeing on the words read. -/
theorem sim_offO (hG : ∀ b, G b → Aligned b ∧ ¬ E b) (hW : ∀ b, W b → Aligned b) (hmk : MasksWr st)
    {R1 R2 : U64 → Prop} (hR : ∀ q, G q → (R1 q ↔ R2 q)) (p : SProg X) :
    ∀ (σ1 σ2 : S) (a : A) (Wd T : Set U64), AgOff st E σ1 σ2 → Within st ar G W p σ2 a →
      Once st ar R2 U Wd T p σ2 a → Once st ar R1 U Wd T p σ1 a := by
  induction p with
  | ret x => intros; simp only [Once]
  | err e => intros; simp only [Once]
  | rd q k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    have hv2 : st.read σ2 q = ok (L.mem σ2 q) := L.read_eq _ _
    have e : L.mem σ1 q = L.mem σ2 q := hA.mem q (hG q hW2.1).1 (hG q hW2.1).2
    refine ⟨fun hr => hO.1 ((racy_congr (hR q hW2.1)).mp hr), fun v hv => ?_⟩
    rw [L.read_eq, e] at hv; obtain rfl := Result.ok_injective hv
    rw [tch_congr (hR q hW2.1)]
    exact ih _ σ1 σ2 a Wd _ hA (hW2.2 _ hv2) (hO.2 _ hv2)
  | rdp q k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    have hv2 : st.read_pair σ2 q = ok (L.mem σ2 q, L.mem σ2 (core.num.U64.wrapping_add q 8#u64)) :=
      L.read_pair_eq _ _
    have e1 : L.mem σ1 q = L.mem σ2 q := hA.mem q (hG q hW2.1).1 (hG q hW2.1).2
    have e2 : L.mem σ1 (core.num.U64.wrapping_add q 8#u64) = L.mem σ2 (core.num.U64.wrapping_add q 8#u64) :=
      hA.mem _ (hG _ hW2.2.1).1 (hG _ hW2.2.1).2
    refine ⟨fun hr => hO.1 ((racy_congr (hR q hW2.1)).mp hr), fun hr => ?_, fun v hv => ?_⟩
    · rw [tch_congr (hR q hW2.1)]; exact hO.2.1 ((racy_congr (hR _ hW2.2.1)).mp hr)
    · rw [L.read_pair_eq, e1, e2] at hv; obtain rfl := Result.ok_injective hv
      rw [tch_congr (hR q hW2.1), tch_congr (hR _ hW2.2.1)]
      exact ih _ σ1 σ2 a Wd _ hA (hW2.2.2 _ hv2) (hO.2.2 _ hv2)
  | wr q v k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    have hw2 : st.write σ2 q v = ok (L.wr σ2 q v) := L.write_eq _ _ _
    intro s' hs
    rw [L.write_eq] at hs; obtain rfl := Result.ok_injective hs
    exact ih _ _ a _ _ (hA.wr hmk (hW q hW2.1) v) (hW2.2 _ hw2) (hO _ hw2)
  | zero q n k ih => intro _ _ _ _ _ _ _ hO; simp only [Once] at hO
  | clr q n k ih => intro _ _ _ _ _ _ _ hO; simp only [Once] at hO
  | ksb k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    have hv2 : st.ks_base σ2 = ok (L.ksb σ2) := L.ks_base_eq _
    intro v hv
    rw [L.ks_base_eq, hA.ksb] at hv; obtain rfl := Result.ok_injective hv
    exact ih _ σ1 σ2 a Wd T hA (hW2 _ hv2) (hO _ hv2)
  | cpu k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    have hv2 : st.cur_cpu σ2 = ok (L.cpu σ2) := L.cur_cpu_eq _
    intro v hv
    rw [L.cur_cpu_eq, hA.cpu] at hv; obtain rfl := Result.ok_injective hv
    exact ih _ σ1 σ2 a Wd T hA (hW2 _ hv2) (hO _ hv2)
  | masks k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    intro v hv
    rw [hA.masks] at hv
    exact ih _ σ1 σ2 a Wd T hA (hW2 _ hv) (hO _ hv)
  | arch op k ih =>
    intro σ1 σ2 a Wd T hA hW2 hO
    simp only [Within, Once] at hW2 hO ⊢
    exact fun v a' hv => ih v σ1 σ2 a' Wd T hA (hW2 v a' hv) (hO v a' hv)

/-- The converse of `interp_guard`: a run whose accesses lie in the sets is the guarded run. -/
theorem guard_of_within {R' W' : U64 → Prop} (p : SProg X) :
    ∀ (s : S) (a : A) (r : X × S × A), interp st ar p s a = ok r → Within st ar R' W' p s a →
      interp (guard st R' W') ar p s a = ok r := by
  induction p with
  | ret x => intro s a r h _; exact h
  | err e => intro s a r h _; exact h
  | rd q k ih =>
    intro s a r h hw
    simp only [interp, Within] at h hw ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, by rw [guard_read hw.1]; exact hv, ih v s a r hk (hw.2 v hv)⟩
  | rdp q k ih =>
    intro s a r h hw
    simp only [interp, Within] at h hw ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, by rw [guard_read_pair hw.1 hw.2.1]; exact hv, ih v s a r hk (hw.2.2 v hv)⟩
  | wr q v k ih =>
    intro s a r h hw
    simp only [interp, Within] at h hw ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨s', by rw [guard_write hw.1]; exact hv, ih s' a r hk (hw.2 s' hv)⟩
  | zero q n k ih =>
    intro s a r h hw
    simp only [interp, Within] at h hw ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨s', by rw [guard_zero hw.1]; exact hv, ih s' a r hk (hw.2 s' hv)⟩
  | clr q n k ih =>
    intro s a r h hw
    simp only [interp, Within] at h hw ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨s', by rw [guard_clear_free hw.1]; exact hv, ih s' a r hk (hw.2 s' hv)⟩
  | ksb k ih =>
    intro s a r h hw
    simp only [interp, Within] at h hw ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk (hw v hv)⟩
  | cpu k ih =>
    intro s a r h hw
    simp only [interp, Within] at h hw ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk (hw v hv)⟩
  | masks k ih =>
    intro s a r h hw
    simp only [interp, Within] at h hw ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk (hw v hv)⟩
  | arch op k ih =>
    intro s a r h hw
    simp only [interp, Within] at h hw ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨(v, a'), hv, ih v s a' r hk (hw v a' hv)⟩

/-- The converse of `interp_mguard`. -/
theorem mguard_of_withinM {Q : S → S → Prop} (p : SProg X) :
    ∀ (s : S) (a : A) (r : X × S × A), interp st ar p s a = ok r → WithinM st ar Q p s a →
      interp (mguard st Q) ar p s a = ok r := by
  induction p with
  | ret x => intro s a r h _; exact h
  | err e => intro s a r h _; exact h
  | rd q k ih =>
    intro s a r h hw
    simp only [interp, WithinM] at h hw ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk (hw v hv)⟩
  | rdp q k ih =>
    intro s a r h hw
    simp only [interp, WithinM] at h hw ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk (hw v hv)⟩
  | wr q v k ih =>
    intro s a r h hw
    simp only [interp, WithinM] at h hw ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨s', mguard_write hv (hw s' hv).1, ih s' a r hk (hw s' hv).2⟩
  | zero q n k ih =>
    intro s a r h hw
    simp only [interp, WithinM] at h hw ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    refine bok.mpr ⟨s', ?_, ih s' a r hk (hw s' hv).2⟩
    show (do let s'' ← st.zero s q n; if Q s s'' then ok s'' else fail .panic) = _
    rw [hv, bind_tc_ok, if_pos (hw s' hv).1]
  | clr q n k ih =>
    intro s a r h hw
    simp only [interp, WithinM] at h hw ⊢
    obtain ⟨s', hv, hk⟩ := bok.mp h
    refine bok.mpr ⟨s', ?_, ih s' a r hk (hw s' hv).2⟩
    show (do let s'' ← st.clear_free s q n; if Q s s'' then ok s'' else fail .panic) = _
    rw [hv, bind_tc_ok, if_pos (hw s' hv).1]
  | ksb k ih =>
    intro s a r h hw
    simp only [interp, WithinM] at h hw ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk (hw v hv)⟩
  | cpu k ih =>
    intro s a r h hw
    simp only [interp, WithinM] at h hw ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk (hw v hv)⟩
  | masks k ih =>
    intro s a r h hw
    simp only [interp, WithinM] at h hw ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨v, hv, ih v s a r hk (hw v hv)⟩
  | arch op k ih =>
    intro s a r h hw
    simp only [interp, WithinM] at h hw ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    exact bok.mpr ⟨(v, a'), hv, ih v s a' r hk (hw v a' hv)⟩

end sim

end
end Fl4Proofs.P2.E2EV

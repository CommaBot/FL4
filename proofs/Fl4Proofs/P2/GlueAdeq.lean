/-
# P2 (line glue, gen 3): **adequacy of `tr`** — the deterministic sequential run of a translated body is the store
run of the path's `F` (gap G1 of gen 2)

Gen 2 (`E2EPU5` module docstring) found three gaps between Serial's history and P3's chain. This module closes
**G1**: no lemma linked Serial's sequential meaning `Run (tr …)` (speculative reads `rds` / class reads `rdc`
returning any value) to the store-level result of the path's body `F`.

* `Serial.RunD`: the **deterministic** sequential run, every read (`rd`, `rds`, `rdc`) returning the current memory's
  value — the run of a body "agreeing with F's reads". `RunD.run`: it is a `Run` (for `rdc`, when the class
  relation is reflexive at the value read: always so for `tr`'s `rdc`, `cls q u = cls q w`); `RunD.det`: it is
  unique.
* **`E2E.runD_tr`**: if the tree `p` runs on the store from `s` to `r` (`interp … = ok r`) with aligned accesses and
  `Once` (no `zero` / `clear_free`; no user word read after the run wrote it), and `m` agrees with `s` on aligned
  words (user words: those not yet written), then `tr … p` has a deterministic run from `m` to an `m'` that is
  `r`'s memory on aligned kernel words and `m` elsewhere (user writes are dropped by `tr`).
* **`E2E.LocalPath.body_runD`** / **`E2E.LocalPath.runD_result`**: for a local path `P` from a `Pre` state `σ`
  (accepted or declined: writes in `WS ∪ DS`, aligned by `PathObl.aligned`, reads aligned by `PathSide.read_aligned`,
  `Once` by `ReadOnce` at `Alt.refl`), the body `P.body σ a` has a deterministic run from any `m` agreeing with
  `σ` on aligned words, and **every** deterministic run of it from such an `m` ends in `F`'s result on aligned
  kernel words. This is the statement G1 asked for: a Serial run of the tree that agrees with `F`'s reads gives
  `F`'s result. Only `IsProgOn` [P], `PathObl` [W], `PathSide` [W], `ReadOnce` [W], `MasksWr` [P] of the path are
  used — the fields every `LocalPath` already carries; nothing new is assumed.

What G1 does **not** give (and why the start [P] is not discharged by it alone; `GlueFrame` module docstring): the
Serial history records an arbitrary `Run` (`LocInv.sim` is existential over the speculative values), and the memory
a completed local body is replayed from is the prefix memory at completion, not at start (G3).

Also here, for step 5 (declines): **`Serial.veq_revert`**, the general form of gen 2's `veq_offCore`: from `VEq H μ`,
reverting words that some other core owns at `μ`, whose class nobody but such a core tracks, and that change no
owner, keeps `VEq`. So the starting core's start fact may be stated at the prefix memory with another core's
declined writes (`FAULT_IP`, `CUR_TIME`, `CONSUMED`: `PathObl.write_own` puts every `DecSet` word in that core's
permission) taken back out, whenever those words are that core's (`own … = .core d`).

No premise added; no existing statement changed.
-/
import Fl4Proofs.P2.E2EPU5
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Serial

noncomputable section

section rund
variable {A V L : Type} [DecidableEq A]

/-- **The deterministic sequential run**: every read returns the current memory's value (module docstring). Bodies
take no locks and have no `start`, so there are no such steps. -/
inductive RunD : Prog A V L → (A → V) → (A → V) → Prop
  | done (m : A → V) : RunD .done m m
  | rd {a : A} {k : V → Prog A V L} {m m' : A → V} : RunD (k (m a)) m m' → RunD (.rd a k) m m'
  | wr {a : A} {v : V} {k : Prog A V L} {m m' : A → V} :
      RunD k (Function.update m a v) m' → RunD (.wr a v k) m m'
  | rds {a : A} {k : V → Prog A V L} {m m' : A → V} : RunD (k (m a)) m m' → RunD (.rds a k) m m'
  | rdc {a : A} {K : V → V → Prop} {k : V → Prog A V L} {m m' : A → V} :
      K (m a) (m a) → RunD (k (m a)) m m' → RunD (.rdc a K k) m m'

/-- A deterministic run is a sequential run. -/
theorem RunD.run {q : Prog A V L} {m m' : A → V} (h : RunD q m m') : Run q m m' := by
  induction h with
  | done m => exact .done m
  | rd _ ih => exact .rd ih
  | wr _ ih => exact .wr ih
  | rds _ ih => exact .rds _ ih
  | rdc hK _ ih => exact .rdc _ hK ih

/-- **The deterministic run is unique.** -/
theorem RunD.det {q : Prog A V L} {m m1 m2 : A → V} (h1 : RunD q m m1) (h2 : RunD q m m2) : m1 = m2 := by
  induction h1 generalizing m2 with
  | done m => cases h2; rfl
  | rd _ ih => cases h2 with | rd h => exact ih h
  | wr _ ih => cases h2 with | wr h => exact ih h
  | rds _ ih => cases h2 with | rds h => exact ih h
  | rdc _ _ ih => cases h2 with | rdc _ h => exact ih h

end rund

section veq
variable {A V C L : Type}

/-- **Reverting words another core owns keeps `VEq`** (module docstring, step 5): `ρ` differs from `H` only on
words owned at `μ` by a core other than `c`, whose class neither the gate nor `c` tracks, and has `H`'s owners. -/
theorem veq_revert {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C} {c : C}
    {hs : L → Prop} {H ρ μ : A → V} (hV : VEq own cls ko c hs H μ) (hown : own ρ = own H)
    (hval : ∀ y, ρ y ≠ H y → ∃ e, e ≠ c ∧ own μ y = .core e)
    (hko : ∀ y, ρ y ≠ H y → ¬ (ko y = .gate ∨ ko y = .core c)) :
    VEq own cls ko c hs ρ μ := by
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [hown] at hx ⊢; exact hV.1 x hx
  · by_cases e : ρ y = H y
    · rw [e]; exact hV.2.1 y hy
    · obtain ⟨d, hdc, hd⟩ := hval y e
      rw [hd] at hy
      rcases hy with h | h
      · exact absurd h hdc
      · cases h
  · by_cases e : ρ y = H y
    · rw [e]; exact hV.2.2 y hy
    · exact absurd hy (hko y e)

end veq

end
end Fl4Proofs.P2.Serial

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner Prog RunD)

noncomputable section
open Classical

section adeq
variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
  {R User : U64 → Prop} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {c kb : U64} {mk : U64 × U64}

theorem runD_rdN {Wd : Set U64} {q : U64} {k : U64 → SP} {m m' : U64 → U64}
    (h : RunD (k (m q)) m m') : RunD (rdN R User cls ko c Wd q k) m m' := by
  unfold rdN
  split_ifs <;> first | exact .rd h | exact .rds h | exact .rdc rfl h

/-- **Adequacy of `tr`** (module docstring): the store run of the tree `p` is the deterministic sequential run of
its translation, on aligned kernel words. -/
theorem runD_tr (hmk : MasksWr st) (p : SProg X) :
    ∀ (s : S) (a : A) (Wd T : Set U64) (m : U64 → U64) (r : X × S × A),
      interp st ar p s a = ok r →
      Within st ar (fun b => Aligned b) (fun b => Aligned b) p s a →
      Once st ar R User Wd T p s a →
      st.frame_masks s = ok mk → L.ksb s = kb → L.cpu s = c →
      (∀ y, Aligned y → (¬ User y ∨ y ∉ T) → m y = L.mem s y) →
      ∃ m', RunD (tr R User cls ko c kb mk ar p Wd a) m m' ∧
        (∀ y, Aligned y → ¬ User y → m' y = L.mem r.2.1 y) ∧
        (∀ y, ¬ (Aligned y ∧ ¬ User y) → m' y = m y) := by
  induction p with
  | ret x =>
    intro s a Wd T m r h _ _ _ _ _ hK
    simp only [interp] at h
    obtain rfl := Result.ok_injective h
    refine ⟨m, ?_, fun y hy hu => hK y hy (Or.inl hu), fun _ _ => rfl⟩
    simp only [tr]; exact .done m
  | err e =>
    intro s a Wd T m r h
    simp only [interp] at h
    exact absurd h fail_not_ok
  | zero q n k ih =>
    intro s a Wd T m r _ _ hN
    simp only [Once] at hN
  | clr q n k ih =>
    intro s a Wd T m r _ _ hN
    simp only [Once] at hN
  | rd q k ih =>
    intro s a Wd T m r h hW hN hm hk hc hK
    simp only [interp] at h
    obtain ⟨v, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    obtain ⟨hal, hW⟩ := hW
    obtain ⟨ho, hN⟩ := hN
    have ev : v = L.mem s q := Result.ok_injective (hv.symm.trans (L.read_eq s q))
    subst ev
    have hu : ¬ User q ∨ q ∉ T := by
      by_cases hu : User q
      · exact Or.inr (ho fun h => h.1 hu)
      · exact Or.inl hu
    have e : m q = L.mem s q := hK q hal hu
    obtain ⟨m', h1, h2, h3⟩ := ih (L.mem s q) s a Wd _ m r hk' (hW _ hv) (hN _ hv) hm hk hc
      (fun y hy hyu => hK y hy (hyu.imp_right fun h hT => h (tch_sub hT)))
    refine ⟨m', ?_, h2, h3⟩
    simp only [tr]
    have h1' : RunD (tr R User cls ko c kb mk ar (k (m q)) Wd a) m m' := by rw [e]; exact h1
    exact runD_rdN h1'
  | rdp q k ih =>
    intro s a Wd T m r h hW hN hm hk hc hK
    simp only [interp] at h
    obtain ⟨v, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    simp only [tr]
    have hrp := L.read_pair_eq s q
    generalize core.num.U64.wrapping_add q 8#u64 = q8 at *
    obtain ⟨hal, hal8, hW⟩ := hW
    obtain ⟨ho, ho8, hN⟩ := hN
    have ev : v = (L.mem s q, L.mem s q8) := Result.ok_injective (hv.symm.trans hrp)
    subst ev
    have hu : ¬ User q ∨ q ∉ T := by
      by_cases hu : User q
      · exact Or.inr (ho fun h => h.1 hu)
      · exact Or.inl hu
    have hu8 : ¬ User q8 ∨ q8 ∉ T := by
      by_cases hu : User q8
      · exact Or.inr fun h => ho8 (fun h => h.1 hu) (tch_sub h)
      · exact Or.inl hu
    have e : m q = L.mem s q := hK q hal hu
    have e8 : m q8 = L.mem s q8 := hK q8 hal8 hu8
    obtain ⟨m', h1, h2, h3⟩ := ih _ s a Wd _ m r hk' (hW _ hv) (hN _ hv) hm hk hc
      (fun y hy hyu => hK y hy (hyu.imp_right fun h hT => h (tch_sub (tch_sub hT))))
    refine ⟨m', ?_, h2, h3⟩
    have h1' : RunD (tr R User cls ko c kb mk ar (k (m q, m q8)) Wd a) m m' := by rw [e, e8]; exact h1
    exact runD_rdN (runD_rdN h1')
  | wr q v k ih =>
    intro s a Wd T m r h hW hN hm hk hc hK
    simp only [interp] at h
    obtain ⟨s', hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    obtain ⟨hal, hW⟩ := hW
    have es : s' = L.wr s q v := Result.ok_injective (hv.symm.trans (L.write_eq s q v))
    subst es
    have hm' : st.frame_masks (L.wr s q v) = ok mk := by rw [hmk]; exact hm
    have hk2 : L.ksb (L.wr s q v) = kb := by rw [L.ksb_wr]; exact hk
    have hc2 : L.cpu (L.wr s q v) = c := by rw [L.cpu_wr]; exact hc
    have hN := hN _ hv
    by_cases hu : User q
    · simp only [if_pos hu] at hN
      have hK' : ∀ y, Aligned y → (¬ User y ∨ y ∉ insert q T) → m y = L.mem (L.wr s q v) y := by
        intro y hy hyu
        have hne : q ≠ y := by
          rintro rfl
          rcases hyu with h | h
          · exact h hu
          · exact h (Set.mem_insert _ _)
        rw [L.mem_wr s q v y hal hy, if_neg hne]
        exact hK y hy (hyu.imp_right fun h hT => h (Set.mem_insert_of_mem _ hT))
      obtain ⟨m', h1, h2, h3⟩ := ih _ a Wd _ m r hk' (hW _ hv) hN hm' hk2 hc2 hK'
      refine ⟨m', ?_, h2, h3⟩
      simp only [tr, if_pos hu]; exact h1
    · simp only [if_neg hu] at hN
      have hK' : ∀ y, Aligned y → (¬ User y ∨ y ∉ T) →
          Function.update m q v y = L.mem (L.wr s q v) y := by
        intro y hy hyu
        rw [L.mem_wr s q v y hal hy]
        by_cases hne : q = y
        · subst hne; rw [if_pos rfl, Function.update_self]
        · rw [if_neg hne, Function.update_of_ne (Ne.symm hne)]; exact hK y hy hyu
      obtain ⟨m', h1, h2, h3⟩ := ih _ a _ T (Function.update m q v) r hk' (hW _ hv) hN hm' hk2 hc2 hK'
      refine ⟨m', ?_, h2, fun y hy => ?_⟩
      · simp only [tr, if_neg hu]; exact .wr h1
      · rw [h3 y hy, Function.update_of_ne]
        rintro rfl; exact hy ⟨hal, hu⟩
  | ksb k ih =>
    intro s a Wd T m r h hW hN hm hk hc hK
    simp only [interp] at h
    obtain ⟨v, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    have ev : v = kb := Result.ok_injective (hv.symm.trans (by rw [← hk]; exact L.ks_base_eq s))
    subst ev
    simp only [tr]
    exact ih _ s a Wd T m r hk' (hW _ hv) (hN _ hv) hm hk hc hK
  | cpu k ih =>
    intro s a Wd T m r h hW hN hm hk hc hK
    simp only [interp] at h
    obtain ⟨v, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    have ev : v = c := Result.ok_injective (hv.symm.trans (by rw [← hc]; exact L.cur_cpu_eq s))
    subst ev
    simp only [tr]
    exact ih _ s a Wd T m r hk' (hW _ hv) (hN _ hv) hm hk hc hK
  | masks k ih =>
    intro s a Wd T m r h hW hN hm hk hc hK
    simp only [interp] at h
    obtain ⟨v, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    have ev : v = mk := Result.ok_injective (hv.symm.trans hm)
    subst ev
    simp only [tr]
    exact ih _ s a Wd T m r hk' (hW _ hv) (hN _ hv) hm hk hc hK
  | arch op k ih =>
    intro s a Wd T m r h hW hN hm hk hc hK
    simp only [interp] at h
    obtain ⟨⟨b, a'⟩, hv, hk'⟩ := bok.mp h
    simp only [Within] at hW
    simp only [Once] at hN
    have hca : ∃ r, callArch ar op a = ok r := ⟨_, hv⟩
    have e2 : hca.choose = (b, a') := Result.ok_injective (hca.choose_spec.symm.trans hv)
    simp only [tr, dif_pos hca]
    rw [e2]
    exact ih b s a' Wd T m r hk' (hW _ _ hv) (hN _ _ hv) hm hk hc hK

end adeq

section path
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **A started body's deterministic run is its store run** (module docstring): from a `Pre` state `σ`, a run of `F`
(accepted or declined) to `r`, and any `m` agreeing with `σ` on aligned words. -/
theorem LocalPath.body_runD (P : LocalPath own cls ko User) {σ : P.S} {a : P.A} {r : P.X × P.S × P.A}
    (hpre : P.Pre σ) (h : P.F P.ar P.st σ a = ok r) {m : U64 → U64}
    (hm : ∀ y, Aligned y → m y = P.L.mem σ y) :
    ∃ m', RunD (P.body σ a) m m' ∧ (∀ y, Aligned y → ¬ User y → m' y = P.L.mem r.2.1 y) ∧
      (∀ y, ¬ (Aligned y ∧ ¬ User y) → m' y = m y) := by
  letI := P.L
  have gu : AltOf P.st P.Pre P.RS cls ko User σ := AltOf.pre hpre
  have hI : interp P.st P.ar P.p σ a = ok r := by
    rw [← P.isProg _ (Narrow.self _) σ gu a]; exact h
  have hA := P.side.read_aligned σ σ a r hpre (Alt.refl σ) h
  rw [P.isProg _ (Narrow.guard _ _ _) σ gu a] at hA
  have hA := (interp_guard P.p σ a r hA).2
  have hWr : Within P.st P.ar (fun _ => True) (fun b => Aligned b) P.p σ a := by
    by_cases hacc : P.Acc r.1
    · exact Within.mono (fun _ _ => trivial) (fun b hb => P.obl.aligned σ b hpre (Or.inl hb)) P.p σ a
        (P.obl.within P.isProg hpre gu h hacc)
    · exact Within.mono (fun _ _ => trivial) (fun b hb => P.obl.aligned σ b hpre (Or.inr hb)) P.p σ a
        (P.obl.within_dec P.isProg hpre gu h hacc)
  have hW := Within.mono (fun b hb => hb.1) (fun b hb => hb.2) P.p σ a (within_and P.p σ a hA hWr)
  have hO := P.once σ σ a r hpre (Alt.refl σ) hI
  exact runD_tr P.masks P.p σ a ∅ ∅ m r hI hW hO (masksOf_eq P.st σ) rfl rfl (fun y hy _ => hm y hy)

/-- **Every deterministic run of a started body ends in `F`'s result** on aligned kernel words (G1, module
docstring). -/
theorem LocalPath.runD_result (P : LocalPath own cls ko User) {σ : P.S} {a : P.A} {r : P.X × P.S × P.A}
    (hpre : P.Pre σ) (h : P.F P.ar P.st σ a = ok r) {m m' : U64 → U64}
    (hm : ∀ y, Aligned y → m y = P.L.mem σ y) (hr : RunD (P.body σ a) m m') :
    ∀ y, Aligned y → ¬ User y → m' y = P.L.mem r.2.1 y := by
  obtain ⟨m'', h1, h2, -⟩ := P.body_runD hpre h hm
  rw [hr.det h1]; exact h2

/-- **A started body has a run from `σ`'s memory ending in `F`'s result** (G1 with `Run`; the total body runs). -/
theorem LocalPath.body_run (P : LocalPath own cls ko User) {σ : P.S} {a : P.A} (hpre : P.Pre σ)
    {m : U64 → U64} (hm : ∀ y, Aligned y → m y = P.L.mem σ y) :
    ∃ r, P.F P.ar P.st σ a = ok r ∧ ∃ m', Fl4Proofs.P2.Serial.Run (P.body σ a) m m' ∧
      ∀ y, Aligned y → ¬ User y → m' y = P.L.mem r.2.1 y := by
  obtain ⟨r, h⟩ := P.total σ a
  obtain ⟨m', h1, h2, -⟩ := P.body_runD hpre h hm
  exact ⟨r, h, m', h1.run, h2⟩

end path

end
end Fl4Proofs.P2.E2E

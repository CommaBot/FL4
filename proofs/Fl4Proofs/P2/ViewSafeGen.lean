/-
# P2 (line p3mc, gen 4): a started body is `Safe` from a start at a **different** memory (`body_safeV`)

`E2EH.body_safeH` turns a start whose store state agrees with `ρ` into `Safe` at every `μ` with `VEq ρ μ`. At a
core's view `ρv := CoreView.view K c ρ` this fails (`CoreView.veq_view_false`): the view and `ρ` differ on gate
words. `body_safeV` is `body_safeH` for a store state that agrees with `ρv` while `VEq` holds between `ρ` and `μ`,
given a set `N` of words on which `ρv` and `ρ` agree in value and owner and to which the path's runs keep:

* **`simN`** (the `sim` variant): the translated body's run is certified with a check memory `κ` that has to equal
  the store memory only **off a set `D`** (the words where `ρv` and `ρ` differ), not on all kernel words. The run
  reads only words of `Rr ⊆ N` and writes only words of `Wr ⊆ N`. A write's owner check at `κ` is carried from the
  one at the store memory by two owner facts (`hO1`: off a set `DD` the owner is fixed by the words off `D`;
  `hO2`: the path's writes change no owner on `DD`). The class owner of the path (`ko`) and of the target (`kt`)
  may differ; they need to agree only on the words `Kc` that the run reads racily or writes;
* **`body_safeV`**: from `PathObl`/`PathSide`/`ReadOnce` of the path at the view and the two narrowed run facts
  `hNarA` (accepted runs from a view state read only `N ∧ (RS ∨ Kc)` words and write only `NW` words) and `hNarD`
  (the same for declined runs at every alternative). A declined run's alternative store state is built from the
  racy values patched to `ρv` off `N ∧ Kc` (so it is an alternative of the view state), and the certificate's
  check memory takes `ρ`'s value on `D`;
* **`LocalPath.safeV`**: the same for a `LocalPath` start.

No premise: every fact about the path is a hypothesis of the theorems. No existing statement changed.
-/
import Fl4Proofs.P2.E2EH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner Prog HeldV PO MoveV Safe MoveHeld AltRun Adm
  Diff RInv WrOK VEq)

noncomputable section
open Classical

section simN
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko kt : U64 → ClsOwner U64} {c : U64} {hs : U64 → Prop} {R User Hp N Kc : U64 → Prop}

/-- `altRun_rdN` for a read of a word of `N`, racy only where the two class owners agree. -/
theorem altRun_rdNN {P : Set U64} {Wd T : Set U64} {q : U64} {k : U64 → SP} {ν κ : U64 → U64}
    (hKc : ∀ x, Kc x → ko x = kt x)
    (hWd : ∀ x ∈ Wd, Hp x) (hPT : P ⊆ T) (ho : Racy R User Wd q → q ∉ T) (hq : N q ∧ (R q ∨ Kc q))
    (hk : ∀ P', P' ⊆ tch R User Wd q T →
      AltRun own cls kt c hs (RpOf (fun x => R x ∧ N x) User Hp) Hp P' (k (ν q)) ν κ) :
    AltRun own cls kt c hs (RpOf (fun x => R x ∧ N x) User Hp) Hp P (rdN R User cls ko c Wd q k) ν κ := by
  by_cases hr : Racy R User Wd q
  · have hq' : q ∉ P := fun h => ho hr (hPT h)
    have hsub : insert q P ⊆ tch R User Wd q T := by
      unfold tch; rw [if_pos hr]; exact Set.insert_subset_insert hPT
    unfold rdN
    rw [if_neg (not_not.mpr hr)]
    split_ifs with hko
    · have hnR : ¬ R q := fun h => hr ⟨hko.1, Or.inl h⟩
      have e : ko q = kt q := hKc q (hq.2.resolve_left hnR)
      simp only [AltRun]
      refine ⟨hq', ?_, fun u w h => h, hk _ hsub⟩
      rw [← e]; exact hko.2
    · simp only [AltRun]; exact ⟨hq', hk _ hsub⟩
  · unfold rdN
    rw [if_pos hr]
    simp only [AltRun]
    refine ⟨?_, hk P (hPT.trans tch_sub)⟩
    obtain ⟨hu, h | h⟩ := not_not.mp hr
    · exact Or.inl ⟨hu, h, hq.1⟩
    · exact Or.inr (hWd q h)

variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}

/-- **The write check carried to a check memory that differs from the store memory on `D`** (module docstring). -/
theorem wrOK_offD {D DD : U64 → Prop} {s s' : S} {κ : U64 → U64} {q v : U64}
    (hO1 : ∀ m m' : U64 → U64, (∀ x, Aligned x → ¬ User x → ¬ D x → m x = m' x) → ∀ y, ¬ DD y → own m y = own m' y)
    (hO2 : ∀ (m : U64 → U64) v y, DD y → own (Function.update m q v) y = own m y)
    (hKc : ∀ x, Kc x → ko x = kt x) (hq : Aligned q) (hu : ¬ User q) (hDq : ¬ D q) (hKq : Kc q)
    (hK : ∀ x, Aligned x → ¬ User x → ¬ D x → κ x = L.mem s x) (hs' : s' = L.wr s q v)
    (h : StepOK own cls ko User c hs (L.mem s) (L.mem s')) :
    WrOK own cls kt c hs κ q v := by
  subst hs'
  have em : L.mem (L.wr s q v) q = v := by rw [L.mem_wr s q v q hq hq, if_pos rfl]
  have hagr : ∀ x, Aligned x → ¬ User x → ¬ D x → Function.update κ q v x = L.mem (L.wr s q v) x := by
    intro x hx hxu hxd
    rw [L.mem_wr s q v x hq hx]
    by_cases hxq : q = x
    · subst hxq; rw [if_pos rfl, Function.update_self]
    · rw [if_neg hxq, Function.update_of_ne (Ne.symm hxq)]; exact hK x hx hxu hxd
  refine ⟨fun y hy => ?_, ?_⟩
  · by_cases hd : DD y
    · exact absurd (hO2 κ v y hd) hy
    · have e1 : own κ y = own (L.mem s) y := hO1 _ _ hK y hd
      have e2 : own (Function.update κ q v) y = own (L.mem (L.wr s q v)) y := hO1 _ _ hagr y hd
      rw [e1, e2] at hy ⊢
      have := h.1 y hy
      exact ⟨heldBy_iff.mp this.1, heldBy_iff.mp this.2⟩
  · rw [← hKc q hKq, hK q hq hu hDq]
    by_cases hv : L.mem (L.wr s q v) q = L.mem s q
    · left; rw [← hv, em]
    · have := h.2 q hv hu
      rw [em] at this; exact this

/-- **`sim` with the check memory off `D`** (module docstring): the run on the store follows the translated body's
run on `ν`, every read in `Rr ⊆ N`, every write in `Wr ⊆ N`, and certifies it with check memory `κ` equal to the
store memory off `D`, for the target class owner `kt`. -/
theorem simN (hmk : MasksWr st) {kb : U64} {mk : U64 × U64} {Rr Wr D DD : U64 → Prop}
    (hWr : ∀ x, Wr x → Aligned x ∧ (¬ User x → Hp x) ∧ N x ∧ Kc x)
    (hRr : ∀ x, Rr x → N x ∧ (R x ∨ Kc x)) (hND : ∀ x, N x → ¬ D x) (hKc : ∀ x, Kc x → ko x = kt x)
    (hO1 : ∀ m m' : U64 → U64, (∀ x, Aligned x → ¬ User x → ¬ D x → m x = m' x) → ∀ y, ¬ DD y → own m y = own m' y)
    (hO2 : ∀ q, Wr q → ∀ (m : U64 → U64) v y, DD y → own (Function.update m q v) y = own m y) (p : SProg X) :
    ∀ (s : S) (a : A) (Wd T P : Set U64) (ν κ : U64 → U64),
      Within st ar (fun b => Aligned b ∧ Rr b) Wr p s a →
      WithinM st ar (fun x y => StepOK own cls ko User c hs (L.mem x) (L.mem y)) p s a →
      Once st ar R User Wd T p s a →
      (∀ x ∈ Wd, Hp x) → P ⊆ T → st.frame_masks s = ok mk → L.ksb s = kb → L.cpu s = c →
      (∀ x, Aligned x → ¬ User x → ¬ D x → κ x = L.mem s x) →
      (∀ x ∈ reads (tr R User cls ko c kb mk ar p Wd a) ν, Aligned x → Rr x →
        (¬ User x ∨ x ∉ T) → L.mem s x = ν x) →
      AltRun own cls kt c hs (RpOf (fun x => R x ∧ N x) User Hp) Hp P (tr R User cls ko c kb mk ar p Wd a) ν κ := by
  induction p with
  | ret x => intros; simp only [tr, AltRun]
  | err e => intros; simp only [tr, AltRun]
  | zero q n k ih => intros; simp only [tr, AltRun]
  | clr q n k ih => intros; simp only [tr, AltRun]
  | rd q k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    rw [reads_rdN] at hν
    obtain ⟨⟨hal, hr⟩, hW⟩ := hW
    obtain ⟨ho, hN⟩ := hN
    have hu : ¬ User q ∨ q ∉ T := by
      by_cases hu : User q
      · exact Or.inr (ho fun h => h.1 hu)
      · exact Or.inl hu
    have e : L.mem s q = ν q := hν q (List.mem_cons_self ..) hal hr hu
    have hrd : st.read s q = ok (ν q) := by rw [← e]; exact L.read_eq s q
    refine altRun_rdNN hKc hWd hPT ho (hRr q hr) fun P' hP' => ?_
    refine ih (ν q) s a Wd _ P' ν κ (hW _ hrd) (hM _ hrd) (hN _ hrd) hWd hP' hm hk hc hK ?_
    intro x hx hxa hxr hxu
    exact hν x (List.mem_cons_of_mem _ hx) hxa hxr (hxu.imp_right fun h hT => h (tch_sub hT))
  | rdp q k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    rw [reads_rdN, reads_rdN] at hν
    have hrp := L.read_pair_eq s q
    generalize core.num.U64.wrapping_add q 8#u64 = q8 at *
    obtain ⟨⟨hal, hr⟩, ⟨hal8, hr8⟩, hW⟩ := hW
    obtain ⟨ho, ho8, hN⟩ := hN
    have hu : ¬ User q ∨ q ∉ T := by
      by_cases hu : User q
      · exact Or.inr (ho fun h => h.1 hu)
      · exact Or.inl hu
    have hu8 : ¬ User q8 ∨ q8 ∉ T := by
      by_cases hu : User q8
      · exact Or.inr fun h => ho8 (fun h => h.1 hu) (tch_sub h)
      · exact Or.inl hu
    have e : L.mem s q = ν q := hν q (List.mem_cons_self ..) hal hr hu
    have e8 : L.mem s q8 = ν q8 :=
      hν q8 (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hal8 hr8 hu8
    have hrd : st.read_pair s q = ok (ν q, ν q8) := by rw [hrp, e, e8]
    refine altRun_rdNN hKc hWd hPT ho (hRr q hr) fun P' hP' => ?_
    refine altRun_rdNN hKc hWd hP' ho8 (hRr q8 hr8) fun P'' hP'' => ?_
    refine ih (ν q, ν q8) s a Wd _ P'' ν κ (hW _ hrd) (hM _ hrd) (hN _ hrd) hWd hP'' hm hk hc hK ?_
    intro x hx hxa hxr hxu
    exact hν x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) hxa hxr
      (hxu.imp_right fun h hT => h (tch_sub (tch_sub hT)))
  | wr q v k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have hw := L.write_eq s q v
    obtain ⟨hWq, hW⟩ := hW
    have hW := hW _ hw
    obtain ⟨hQ, hM⟩ := hM _ hw
    have hN := hN _ hw
    obtain ⟨hal, hHp, hNq, hKq⟩ := hWr q hWq
    have hDq := hND q hNq
    have hm' : st.frame_masks (L.wr s q v) = ok mk := by rw [hmk]; exact hm
    have hk' : L.ksb (L.wr s q v) = kb := by rw [L.ksb_wr]; exact hk
    have hc' : L.cpu (L.wr s q v) = c := by rw [L.cpu_wr]; exact hc
    by_cases hu : User q
    · rw [if_pos hu] at hN hν ⊢
      rw [if_pos hu] at hN
      refine ih _ a Wd _ P ν κ hW hM hN hWd (hPT.trans (Set.subset_insert _ _)) hm' hk' hc' ?_ ?_
      · intro x hx hxu hxd
        have hne : q ≠ x := by rintro rfl; exact hxu hu
        rw [L.mem_wr s q v x hal hx, if_neg hne]; exact hK x hx hxu hxd
      · intro x hx hxa hxr hxu
        have hne : q ≠ x := by
          rintro rfl
          rcases hxu with h | h
          · exact h hu
          · exact h (Set.mem_insert _ _)
        rw [L.mem_wr s q v x hal hxa, if_neg hne]
        exact hν x hx hxa hxr (hxu.imp_right fun h hT => h (Set.mem_insert_of_mem _ hT))
    · rw [if_neg hu] at hN hν ⊢
      rw [if_neg hu] at hN
      simp only [reads] at hν
      simp only [AltRun]
      refine ⟨hHp hu, wrOK_offD hO1 (hO2 q hWq) hKc hal hu hDq hKq hK rfl hQ, ?_⟩
      refine ih _ a _ T P _ _ hW hM hN ?_ hPT hm' hk' hc' ?_ ?_
      · intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · exact hHp hu
        · exact hWd x hx
      · intro x hx hxu hxd
        rw [L.mem_wr s q v x hal hx]
        by_cases hne : q = x
        · subst hne; rw [if_pos rfl, Function.update_self]
        · rw [if_neg hne, Function.update_of_ne (Ne.symm hne)]; exact hK x hx hxu hxd
      · intro x hx hxa hxr hxu
        rw [L.mem_wr s q v x hal hxa]
        by_cases hne : q = x
        · subst hne; rw [if_pos rfl, Function.update_self]
        · rw [if_neg hne, Function.update_of_ne (Ne.symm hne)]; exact hν x hx hxa hxr hxu
  | ksb k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have h : st.ks_base s = ok kb := by rw [← hk]; exact L.ks_base_eq s
    exact ih kb s a Wd T P ν κ (hW _ h) (hM _ h) (hN _ h) hWd hPT hm hk hc hK hν
  | cpu k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have h : st.cur_cpu s = ok c := by rw [← hc]; exact L.cur_cpu_eq s
    exact ih c s a Wd T P ν κ (hW _ h) (hM _ h) (hN _ h) hWd hPT hm hk hc hK hν
  | masks k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    exact ih mk s a Wd T P ν κ (hW _ hm) (hM _ hm) (hN _ hm) hWd hPT hm hk hc hK hν
  | arch op k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    by_cases hca : ∃ r, callArch ar op a = ok r
    · have e := hca.choose_spec
      simp only [tr, dif_pos hca] at hν ⊢
      exact ih _ s _ Wd T P ν κ (hW _ _ e) (hM _ _ e) (hN _ _ e) hWd hPT hm hk hc hK hν
    · simp only [tr, dif_neg hca, AltRun]

end simN

section body
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko kt : U64 → ClsOwner U64} {User : U64 → Prop}
  {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
  {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A)}
  {p : SProg X} {Acc : X → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop}
  {RS WS DS : S → U64 → Prop}

/-- **A body is `Safe` at `μ` from a start at a memory `ρv` other than the `ρ` that `VEq` relates to `μ`**
(module docstring). `N`: words where `ρv` and `ρ` agree in value and owner; `Kc`: words where the path's class
owner `ko` is the target's `kt`; `NW`: the words the runs may write; `DD`: words whose owner the words off
`{ρv ≠ ρ}` do not fix. -/
theorem body_safeV (hL : MoveHeld own) (hO : OwnDep own User)
    (hp : IsProgOn (F ar) ar st (AltOf st Pre RS cls ko User) p)
    (O : PathObl st (F ar) Acc own cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS)
    (hN : ReadOnce st ar p cls ko User Pre RS) (hT : ∀ s a, ∃ r, F ar st s a = ok r)
    (hmk : MasksWr st) {σ : S} {a : A} (hpre : Pre σ) {ρv ρ μ : U64 → U64}
    (hρ : ∀ x, Aligned x → ¬ User x → L.mem σ x = ρv x)
    (hV : VEq own cls kt (L.cpu σ) (Locks σ) ρ μ)
    {N Kc NW DD : U64 → Prop}
    (hN1 : ∀ x, N x → ρv x = ρ x) (hN2 : ∀ x, N x → own ρv x = own ρ x) (hKc : ∀ x, Kc x → ko x = kt x)
    (hNW : ∀ x, NW x → N x ∧ Kc x)
    (hO1 : ∀ m m' : U64 → U64, (∀ x, Aligned x → ¬ User x → ρv x = ρ x → m x = m' x) →
      ∀ y, ¬ DD y → own m y = own m' y)
    (hO2 : ∀ q, NW q → ∀ (m : U64 → U64) v y, DD y → own (Function.update m q v) y = own m y)
    {NR NWs : S → U64 → Prop} (hNR : ∀ s0 b, NR s0 b → N b ∧ (RS s0 b ∨ Kc b)) (hNWs : ∀ s0 b, NWs s0 b → NW b)
    (hNarA : ∀ s0 r, Pre s0 → (∀ x, Aligned x → ¬ User x → L.mem s0 x = ρv x) → F ar st s0 a = ok r → Acc r.1 →
      F ar (guard st (NR s0) (NWs s0)) s0 a = ok r)
    (hNarD : ∀ s0 r, Pre s0 → (∀ x, Aligned x → ¬ User x → L.mem s0 x = ρv x) → F ar st s0 a = ok r →
      ¬ Acc r.1 → ∀ s' r', Alt st (RS s0) cls ko User s0 s' → F ar st s' a = ok r' →
        F ar (guard st (NR s0) (NWs s0)) s' a = ok r') :
    Safe own cls kt (L.cpu σ) (Locks σ) μ
      (tr (RS σ) User cls ko (L.cpu σ) (L.ksb σ) (masksOf st σ) ar p ∅ a) := by
  have e0 : own (L.mem σ) = own ρv := hO _ _ hρ
  have hDN : ∀ x, N x → ¬ (ρv x ≠ ρ x) := fun x hx h => h (hN1 x hx)
  have hO1' : ∀ m m' : U64 → U64, (∀ x, Aligned x → ¬ User x → ¬ (ρv x ≠ ρ x) → m x = m' x) →
      ∀ y, ¬ DD y → own m y = own m' y :=
    fun m m' h => hO1 m m' fun x hx hu he => h x hx hu (not_not.mpr he)
  let Hp : U64 → Prop := fun x => ¬ User x ∧ (WS σ x ∨ DS σ x) ∧ N x
  have hRI : RInv own (L.cpu σ) (Locks σ) (RpOf (fun x => RS σ x ∧ N x) User Hp) Hp μ := by
    have hH : ∀ x, Hp x → HeldV (L.cpu σ) (Locks σ) (own μ x) := by
      intro x hx
      have h : HeldV (L.cpu σ) (Locks σ) (own ρ x) := by
        rw [← hN2 x hx.2.2, ← e0]; exact heldBy_iff.mp (O.write_own σ x hpre hx.2.1 hx.1)
      rw [hV.1 x (Or.inl h)]; exact h
    refine ⟨hH, fun x hx => ?_⟩
    rcases hx with ⟨hu, hr, hn⟩ | hx
    · rcases O.read_own σ x hpre hr hu with h | h
      · have h' : HeldV (L.cpu σ) (Locks σ) (own ρ x) := by
          rw [← hN2 x hn, ← e0]; exact heldBy_iff.mp h
        rw [hV.1 x (Or.inl h')]; exact Or.inl h'
      · have h' : own ρ x = .gate := by rw [← hN2 x hn, ← e0]; exact h
        rw [hV.1 x (Or.inr h')]; exact Or.inr h'
    · exact Or.inl (hH x hx)
  refine Fl4Proofs.P2.Serial.safe_of_runs hL (Rp := RpOf (fun x => RS σ x ∧ N x) User Hp) (Hp := Hp) _ ∅ μ
    (fun _ => none) ⟨fun ν hν => ?_, fun y u hu => (by cases hu), fun y u hu => (by cases hu),
      fun y u hu => (by cases hu), hRI⟩
  have hνR : ∀ x, ¬ User x → RS σ x → N x → ν x = μ x :=
    fun x hu hr hn => hν.1 x (hRI.2 x (Or.inl ⟨hu, hr, hn⟩))
  have hρR : ∀ x, ¬ User x → RS σ x → N x → ρ x = μ x :=
    fun x hu hr hn => hV.2.1 x (hRI.2 x (Or.inl ⟨hu, hr, hn⟩))
  generalize hq : tr (RS σ) User cls ko (L.cpu σ) (L.ksb σ) (masksOf st σ) ar p ∅ a = q
  let rl := (reads q ν).filter (fun x => decide (Aligned x))
  let ul := rl.filter (fun x => decide (User x))
  let kl := rl.filter (fun x => decide (¬ User x))
  have hul : ∀ x, x ∈ ul ↔ (x ∈ reads q ν ∧ Aligned x) ∧ User x := by
    intro x; simp only [ul, rl, List.mem_filter, decide_eq_true_eq]
  have hkl : ∀ x, x ∈ kl ↔ (x ∈ reads q ν ∧ Aligned x) ∧ ¬ User x := by
    intro x; simp only [kl, rl, List.mem_filter, decide_eq_true_eq]
  let ν' : U64 → U64 := fun x => if N x ∧ Kc x then ν x else ρv x
  obtain ⟨σu, hσu⟩ : ∃ s, s = wrs st ν ul σ := ⟨_, rfl⟩
  obtain ⟨σν, hσν⟩ : ∃ s, s = wrs st ν' kl σu := ⟨_, rfl⟩
  obtain ⟨uP, uL, uR, uW, uD⟩ := wrs_user st Sd (ν := ν) ul σ
    (fun x hx => ⟨((hul x).mp hx).2, ((hul x).mp hx).1.2⟩) hpre
  obtain ⟨uc, ub, um⟩ := wrs_const st (ν := ν) hmk ul σ
  have uM := wrs_mem st (ν := ν) ul σ (fun x hx => ((hul x).mp hx).1.2)
  rw [← hσu] at uP uL uR uW uD uc ub um uM
  obtain ⟨kc, kb, km⟩ := wrs_const st (ν := ν') hmk kl σu
  have kM := wrs_mem st (ν := ν') kl σu (fun x hx => ((hkl x).mp hx).1.2)
  rw [← hσν] at kc kb km kM
  have hmσ := masksOf_eq st σ
  have uMk : ∀ x, Aligned x → ¬ User x → L.mem σu x = ρv x := by
    intro x hx hu
    rw [uM x hx, if_neg (fun h => hu ((hul x).mp h).2)]; exact hρ x hx hu
  -- a kernel word the path may read and `N` keeps has the same value at `ν`, `μ`, `ρ` and `ρv`
  have hRN : ∀ x, ¬ User x → RS σ x → N x → ν x = ρv x := fun x hu hr hn =>
    (hνR x hu hr hn).trans ((hρR x hu hr hn).symm.trans (hN1 x hn).symm)
  obtain ⟨ru, hru⟩ := hT σu a
  by_cases hacc : Acc ru.1
  · -- accepted at `σu`
    refine ⟨fun x => if Aligned x ∧ ¬ User x then ρ x else μ x, fun y hy hpo => hy ?_, ?_⟩
    · show (if Aligned y ∧ ¬ User y then ρ y else μ y) = μ y
      split_ifs
      · exact hV.2.1 y hpo
      · rfl
    have gu : AltOf st Pre RS cls ko User σu := AltOf.pre uP
    have hW := O.acc σu a ru uP hru hacc
    rw [hp _ (Narrow.guard _ _ _) σu gu a] at hW
    have hW := (interp_guard p σu a ru hW).2
    have hA := Sd.read_aligned σu σu a ru uP (Alt.refl σu) hru
    rw [hp _ (Narrow.guard _ _ _) σu gu a] at hA
    have hA := (interp_guard p σu a ru hA).2
    have hNa := hNarA σu ru uP uMk hru hacc
    rw [hp _ (Narrow.guard _ _ _) σu gu a] at hNa
    have hNa := (interp_guard p σu a ru hNa).2
    have hM := O.move_steps hp uP gu hru
    have hO1 := hN σu σu a ru uP (Alt.refl σu) (by rw [← hp _ (Narrow.self st) σu gu a]; exact hru)
    rw [uR] at hW hO1; rw [uW] at hW; rw [uc, uL] at hM
    have hWi : Within st ar (fun b => Aligned b ∧ (RS σ b ∧ (N b ∧ (RS σ b ∨ Kc b))))
        (fun b => WS σ b ∧ NW b) p σu a :=
      Within.mono (fun b h => ⟨h.1.1, h.1.2, by have := hNR σu b h.2; rw [uR] at this; exact this⟩)
        (fun b h => ⟨h.1.2, hNWs σu b h.2⟩) p σu a
        (within_and p σu a (within_and p σu a hA hW) hNa)
    rw [← hq]
    refine simN (L := L) hmk (Rr := fun b => RS σ b ∧ (N b ∧ (RS σ b ∨ Kc b))) (Wr := fun x => WS σ x ∧ NW x)
      (D := fun x => ρv x ≠ ρ x) (DD := DD) ?_ (fun x h => ⟨h.2.1, Or.inl h.1⟩) hDN hKc hO1'
      (fun q h => hO2 q h.2) p σu a ∅ ∅ ∅ ν
      (fun x => if Aligned x ∧ ¬ User x then ρ x else μ x)
      hWi hM hO1 (fun x hx => absurd hx (Set.notMem_empty x)) subset_rfl
      (um.trans hmσ) ub uc (fun x hx hu hd => by
        show (if Aligned x ∧ ¬ User x then ρ x else μ x) = _
        rw [if_pos ⟨hx, hu⟩, uMk x hx hu]; exact (not_not.mp hd).symm) ?_
    · intro x hx
      have hn := hNW x hx.2
      exact ⟨O.aligned σ x hpre (Or.inl hx.1), fun hu => ⟨hu, Or.inl hx.1, hn.1⟩, hn⟩
    · rw [hq]
      intro x hx hxa hxr _
      by_cases hu : User x
      · rw [uM x hxa, if_pos ((hul x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
      · rw [uMk x hxa hu]; exact (hRN x hu hxr.1 hxr.2.1).symm
  · -- declined at `σu`
    have hAlt : Alt st (RS σu) cls ko User σu σν := by
      refine ⟨kc, kb, km, fun x hx => ?_, fun x hx hu hko => ?_⟩
      · have hxa := Sd.rs_aligned σu x uP hx
        rw [uR] at hx
        rw [kM x hxa]
        split_ifs with h
        · have hu := ((hkl x).mp h).2
          show (if N x ∧ Kc x then ν x else ρv x) = _
          rw [uMk x hxa hu]
          split_ifs with hn
          · exact hRN x hu hx hn.1
          · rfl
        · rfl
      · have hxa : Aligned x := Sd.ko_aligned x (by rcases hko with h | h <;> rw [h] <;> simp)
        rw [kM x hxa]
        split_ifs with h
        · show cls x (if N x ∧ Kc x then ν x else ρv x) = _
          rw [uMk x hxa hu]
          split_ifs with hn
          · rw [uc, hKc x hn.2] at hko
            rw [hν.2.2 x hko, ← hV.2.2 x hko, hN1 x hn.1]
          · rfl
        · rfl
    obtain ⟨rν, hrν⟩ := hT σν a
    have gν : AltOf st Pre RS cls ko User σν := ⟨σu, uP, hAlt⟩
    obtain ⟨-, hW, hM⟩ := O.dec_alt σu a ru uP hru hacc σν rν hAlt hrν
    rw [hp _ (Narrow.guard _ _ _) σν gν a] at hW
    rw [hp _ (Narrow.mguard _ _) σν gν a] at hM
    have hW := (interp_guard p σν a rν hW).2
    have hM := (interp_mguard p σν a rν hM).2
    have hA := Sd.read_aligned σu σν a rν uP hAlt hrν
    rw [hp _ (Narrow.guard _ _ _) σν gν a] at hA
    have hA := (interp_guard p σν a rν hA).2
    have hNd := hNarD σu ru uP uMk hru hacc σν rν hAlt hrν
    rw [hp _ (Narrow.guard _ _ _) σν gν a] at hNd
    have hNd := (interp_guard p σν a rν hNd).2
    have hO1 := hN σu σν a rν uP hAlt (by rw [← hp _ (Narrow.self st) σν gν a]; exact hrν)
    rw [uR] at hO1; rw [uD] at hW; rw [uc, uL] at hM
    have hWi : Within st ar (fun b => Aligned b ∧ (N b ∧ (RS σ b ∨ Kc b)))
        (fun b => DS σ b ∧ NW b) p σν a :=
      Within.mono (fun b h => ⟨h.1.1, by have := hNR σu b h.2; rw [uR] at this; exact this⟩)
        (fun b h => ⟨h.1.2, hNWs σu b h.2⟩) p σν a
        (within_and p σν a (within_and p σν a hA hW) hNd)
    refine ⟨fun x => if Aligned x ∧ ¬ User x then (if ρv x ≠ ρ x then ρ x else L.mem σν x) else μ x,
      fun y hy hpo => ?_, ?_⟩
    · apply hy
      beta_reduce
      split_ifs with h hd
      · exact hV.2.1 y hpo
      · rw [kM y h.1, uMk y h.1 h.2]
        split_ifs
        · show (if N y ∧ Kc y then ν y else ρv y) = μ y
          split_ifs
          · exact hν.1 y hpo
          · rw [not_not.mp hd]; exact hV.2.1 y hpo
        · rw [not_not.mp hd]; exact hV.2.1 y hpo
      · rfl
    · rw [← hq]
      refine simN (L := L) hmk (Rr := fun b => N b ∧ (RS σ b ∨ Kc b)) (Wr := fun x => DS σ x ∧ NW x)
        (D := fun x => ρv x ≠ ρ x) (DD := DD) ?_ (fun x h => h) hDN hKc hO1'
        (fun q h => hO2 q h.2) p σν a ∅ ∅ ∅ ν _ hWi hM hO1 (fun x hx => absurd hx (Set.notMem_empty x))
        subset_rfl (km.trans (um.trans hmσ)) (kb.trans ub) (kc.trans uc)
        (fun x hx hu hd => by rw [if_pos ⟨hx, hu⟩, if_neg hd]) ?_
      · intro x hx
        have hn := hNW x hx.2
        exact ⟨O.aligned σ x hpre (Or.inr hx.1), fun hu => ⟨hu, Or.inr hx.1, hn.1⟩, hn⟩
      · rw [hq]
        intro x hx hxa hxr _
        rw [kM x hxa]
        by_cases hu : User x
        · rw [if_neg (fun h => ((hkl x).mp h).2 hu), uM x hxa,
            if_pos ((hul x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
        · rw [if_pos ((hkl x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
          show (if N x ∧ Kc x then ν x else ρv x) = ν x
          split_ifs with hn
          · rfl
          · have hr : RS σ x := hxr.2.resolve_right fun hk => hn ⟨hxr.1, hk⟩
            exact (hRN x hu hr hxr.1).symm

end body

/-- **`LocalPath.safeH` from a start at another memory** (`body_safeV`, module docstring). -/
theorem LocalPath.safeV {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {ko kt : U64 → ClsOwner U64} {User : U64 → Prop} (P : LocalPath own cls ko User) (hL : MoveHeld own)
    (hO : OwnDep own User) {c : U64} {hs : U64 → Prop} {ρv ρ μ : U64 → U64} {q : SP}
    (h : StartAt P c hs ρv q) (hV : VEq own cls kt c hs ρ μ)
    {N Kc NW DD : U64 → Prop}
    (hN1 : ∀ x, N x → ρv x = ρ x) (hN2 : ∀ x, N x → own ρv x = own ρ x) (hKc : ∀ x, Kc x → ko x = kt x)
    (hNW : ∀ x, NW x → N x ∧ Kc x)
    (hO1 : ∀ m m' : U64 → U64, (∀ x, Aligned x → ¬ User x → ρv x = ρ x → m x = m' x) →
      ∀ y, ¬ DD y → own m y = own m' y)
    (hO2 : ∀ q, NW q → ∀ (m : U64 → U64) v y, DD y → own (Function.update m q v) y = own m y)
    {NR NWs : P.S → U64 → Prop} (hNR : ∀ s0 b, NR s0 b → N b ∧ (P.RS s0 b ∨ Kc b)) (hNWs : ∀ s0 b, NWs s0 b → NW b)
    (hNarA : ∀ s0 a r, P.Pre s0 → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) → P.F P.ar P.st s0 a = ok r →
      P.Acc r.1 → P.F P.ar (guard P.st (NR s0) (NWs s0)) s0 a = ok r)
    (hNarD : ∀ s0 a r, P.Pre s0 → (∀ x, Aligned x → ¬ User x → P.L.mem s0 x = ρv x) → P.F P.ar P.st s0 a = ok r →
      ¬ P.Acc r.1 → ∀ s' r', @Alt _ P.st P.L (P.RS s0) cls ko User s0 s' → P.F P.ar P.st s' a = ok r' →
        P.F P.ar (guard P.st (NR s0) (NWs s0)) s' a = ok r') :
    Safe own cls kt c hs μ q := by
  obtain ⟨σ, a, hpre, rfl, rfl, hρ, rfl⟩ := h
  let _ := P.L
  exact body_safeV hL hO P.isProg P.obl P.side P.once P.total P.masks hpre hρ hV hN1 hN2 hKc hNW hO1 hO2 hNR hNWs
    (fun s0 r h1 h2 h3 h4 => hNarA s0 a r h1 h2 h3 h4) (fun s0 r h1 h2 h3 h4 => hNarD s0 a r h1 h2 h3 h4)

end

end Fl4Proofs.P2.E2E

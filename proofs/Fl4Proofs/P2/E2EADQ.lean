/-
# P2 (line mmuAD, gen 6): **a started body is run-relatively insensitive when its store runs read `G` words only
through `Q`-insensitive continuations** — the masked bridge at the store level

`E2EAD.body_insA` needs the store runs to touch no `G` word (`hNG`). The delPte and CNodeDelete paths read paging
words by design (their `unmap_page` walks, the held leaf), using the value only through masks that clear bits 5, 6,
and store `0` into the held leaf. Here:

* **`InsT st ar G Q NP User p s a`**: along the store run of the tree `p` from `s`, at every read of a `G` word the
  continuation is the same tree for every value `Q`-equivalent to the one read; no `read_pair` of a `G` word; every
  kernel store into a `G` word stores an `NP` value. A tree-level fact **along the real run only** (garbage branches,
  `MmuADEpoch.sadIns_rd_sens`, are not constrained).
* `insT_of_within`: a run touching no `G` word is `InsT`; **`insT_sbind`**: `InsT` of a sequence from `InsT` of the
  first part and of the rest at every result of the first part's run.
* `insRun_rdN`, **`insT_sim`**: the translated body's run on `ν` is `SafeCertADQ.InsRun` when the store run it follows
  (`E2E.sim`'s correspondence) is `InsT` and reads `G` words only in the translation's read set `R` (so they are
  translated to `rd`, not to racy reads).
* **`body_insAQ`** / **`LocalPath.insAQ`**: `E2EAD.body_insA` / `LocalPath.insA` with `hNG` replaced by
  `hAcc` (accepted runs from entry states are `InsT`) and `hDec` (runs from alternatives of *declined* entry states
  touch no `G` word): exactly the two uses `body_insA` makes of `hNG`.

No premise: everything is a hypothesis of the theorems. No existing statement changed.
-/
import Fl4Proofs.P2.E2EAD
import Fl4Proofs.P2.SafeCertADQ
import Fl4Proofs.P2.ProgReify
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner Prog HeldV PO MoveV Safe MoveHeld AltRun Adm
  Diff RInv WrOK InsRun InsA DInvQ insA_of_runsQ)

noncomputable section
open Classical

section inst
variable {S A X : Type} (st : machine.Store S) (ar : machine.Arch A)

/-- **Run-relative insensitivity of a store tree** (module docstring). -/
def InsT (G : U64 → Prop) (Q : U64 → U64 → Prop) (NP : U64 → Prop) (User : U64 → Prop) :
    SProg X → S → A → Prop
  | .ret _, _, _ => True
  | .err _, _, _ => True
  | .rd q k, s, a => ∀ v, st.read s q = ok v → (G q → ∀ u, Q u v → k u = k v) ∧ InsT G Q NP User (k v) s a
  | .rdp q k, s, a => ¬ G q ∧ ¬ G (core.num.U64.wrapping_add q 8#u64) ∧
      ∀ v, st.read_pair s q = ok v → InsT G Q NP User (k v) s a
  | .wr q v k, s, a => (G q → User q ∨ NP v) ∧ ∀ s', st.write s q v = ok s' → InsT G Q NP User k s' a
  | .zero _ _ _, _, _ => True
  | .clr _ _ _, _, _ => True
  | .ksb k, s, a => ∀ v, st.ks_base s = ok v → InsT G Q NP User (k v) s a
  | .cpu k, s, a => ∀ v, st.cur_cpu s = ok v → InsT G Q NP User (k v) s a
  | .masks k, s, a => ∀ v, st.frame_masks s = ok v → InsT G Q NP User (k v) s a
  | .arch op k, s, a => ∀ v a', callArch ar op a = ok (v, a') → InsT G Q NP User (k v) s a'

variable {st ar} {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop} {User : U64 → Prop}

/-- A run touching no `G` word is `InsT`. -/
theorem insT_of_within (p : SProg X) : ∀ (s : S) (a : A),
    Within st ar (fun b => ¬ G b) (fun b => User b ∨ ¬ G b) p s a → InsT st ar G Q NP User p s a := by
  induction p with
  | ret x => intros; trivial
  | err e => intros; trivial
  | zero q n k ih => intros; trivial
  | clr q n k ih => intros; trivial
  | rd q k ih =>
    intro s a h
    simp only [Within] at h; simp only [InsT]
    exact fun v hv => ⟨fun hg => absurd hg h.1, ih v s a (h.2 v hv)⟩
  | rdp q k ih =>
    intro s a h
    simp only [Within] at h; simp only [InsT]
    exact ⟨h.1, h.2.1, fun v hv => ih v s a (h.2.2 v hv)⟩
  | wr q v k ih =>
    intro s a h
    simp only [Within] at h; simp only [InsT]
    exact ⟨fun hg => h.1.imp id (fun h' => absurd hg h'), fun s' hs => ih s' a (h.2 s' hs)⟩
  | ksb k ih => intro s a h; simp only [Within] at h; simp only [InsT]; exact fun v hv => ih v s a (h v hv)
  | cpu k ih => intro s a h; simp only [Within] at h; simp only [InsT]; exact fun v hv => ih v s a (h v hv)
  | masks k ih => intro s a h; simp only [Within] at h; simp only [InsT]; exact fun v hv => ih v s a (h v hv)
  | arch op k ih =>
    intro s a h; simp only [Within] at h; simp only [InsT]; exact fun v a' hv => ih v s a' (h v a' hv)

/-- **`InsT` of a sequence** from `InsT` of its first part and of the rest at the first part's results. -/
theorem insT_sbind {Y : Type} (p : SProg X) (f : X → SProg Y) : ∀ (s : S) (a : A),
    InsT st ar G Q NP User p s a →
    (∀ r, interp st ar p s a = ok r → InsT st ar G Q NP User (f r.1) r.2.1 r.2.2) →
    InsT st ar G Q NP User (p.sbind f) s a := by
  induction p with
  | ret x => intro s a _ hf; exact hf (x, s, a) (by simp [interp])
  | err e => intros; simp only [SProg.sbind, InsT]
  | zero q n k ih => intros; simp only [SProg.sbind, InsT]
  | clr q n k ih => intros; simp only [SProg.sbind, InsT]
  | rd q k ih =>
    intro s a h hf
    simp only [InsT] at h; simp only [SProg.sbind, InsT]
    intro v hv
    refine ⟨fun hg u hu => by rw [(h v hv).1 hg u hu], ih v s a (h v hv).2 fun r hr => hf r ?_⟩
    simp only [interp, hv, bind_ok]; exact hr
  | rdp q k ih =>
    intro s a h hf
    simp only [InsT] at h; simp only [SProg.sbind, InsT]
    refine ⟨h.1, h.2.1, fun v hv => ih v s a (h.2.2 v hv) fun r hr => hf r ?_⟩
    simp only [interp, hv, bind_ok]; exact hr
  | wr q v k ih =>
    intro s a h hf
    simp only [InsT] at h; simp only [SProg.sbind, InsT]
    refine ⟨h.1, fun s' hs => ih s' a (h.2 s' hs) fun r hr => hf r ?_⟩
    simp only [interp, hs, bind_ok]; exact hr
  | ksb k ih =>
    intro s a h hf
    simp only [InsT] at h; simp only [SProg.sbind, InsT]
    refine fun v hv => ih v s a (h v hv) fun r hr => hf r ?_
    simp only [interp, hv, bind_ok]; exact hr
  | cpu k ih =>
    intro s a h hf
    simp only [InsT] at h; simp only [SProg.sbind, InsT]
    refine fun v hv => ih v s a (h v hv) fun r hr => hf r ?_
    simp only [interp, hv, bind_ok]; exact hr
  | masks k ih =>
    intro s a h hf
    simp only [InsT] at h; simp only [SProg.sbind, InsT]
    refine fun v hv => ih v s a (h v hv) fun r hr => hf r ?_
    simp only [interp, hv, bind_ok]; exact hr
  | arch op k ih =>
    intro s a h hf
    simp only [InsT] at h; simp only [SProg.sbind, InsT]
    refine fun v a' hv => ih v s a' (h v a' hv) fun r hr => hf r ?_
    simp only [interp, hv, bind_ok]; exact hr

end inst

section sim
variable {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {c : U64} {R User : U64 → Prop}

theorem insRun_rdN {Wd : Set U64} {q : U64} {k : U64 → SP} {ν : U64 → U64} (hgr : G q → R q ∧ ¬ User q)
    (hk : G q → ∀ u, Q u (ν q) → k u = k (ν q)) (h : InsRun G Q NP (k (ν q)) ν) :
    InsRun G Q NP (rdN R User cls ko c Wd q k) ν := by
  unfold rdN
  by_cases ha : ¬ Racy R User Wd q
  · rw [if_pos ha]; exact ⟨hk, h⟩
  · rw [if_neg ha]
    have hg : ¬ G q := fun hg => ha (fun hr => by
      unfold Racy at hr; exact hr ⟨(hgr hg).2, Or.inl (hgr hg).1⟩)
    by_cases hb : ¬ User q ∧ (ko q = .gate ∨ ko q = .core c)
    · rw [if_pos hb]; exact ⟨hg, h⟩
    · rw [if_neg hb]; exact ⟨hg, h⟩

variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}

/-- **The translated body's run on `ν` reads `G` words insensitively when the store run it follows does**
(`E2E.sim`'s correspondence hypotheses; `G` reads in the translation's read set `R`). -/
theorem insT_sim (hmk : MasksWr st) {kb : U64} {mk : U64 × U64} {Rr Wr : U64 → Prop}
    (hWr : ∀ x, Wr x → Aligned x) (p : SProg X) :
    ∀ (s : S) (a : A) (Wd T : Set U64) (ν : U64 → U64),
      Within st ar (fun b => Aligned b ∧ Rr b) Wr p s a →
      InsT st ar G Q NP User p s a →
      Within st ar (fun b => G b → R b ∧ ¬ User b) (fun _ => True) p s a →
      Once st ar R User Wd T p s a →
      st.frame_masks s = ok mk → L.ksb s = kb → L.cpu s = c →
      (∀ x ∈ reads (tr R User cls ko c kb mk ar p Wd a) ν, Aligned x → Rr x →
        (¬ User x ∨ x ∉ T) → L.mem s x = ν x) →
      InsRun G Q NP (tr R User cls ko c kb mk ar p Wd a) ν := by
  induction p with
  | ret x => intros; simp only [tr, InsRun]
  | err e => intros; simp only [tr, InsRun]
  | zero q n k ih => intros; simp only [tr, InsRun]
  | clr q n k ih => intros; simp only [tr, InsRun]
  | rd q k ih =>
    intro s a Wd T ν hW hG hGR hN hm hk hc hν
    simp only [Within] at hW hGR
    simp only [InsT] at hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    rw [reads_rdN] at hν
    obtain ⟨⟨hal, hr⟩, hW⟩ := hW
    obtain ⟨hgr, hGR⟩ := hGR
    obtain ⟨ho, hN⟩ := hN
    have hu : ¬ User q ∨ q ∉ T := by
      by_cases hu : User q
      · exact Or.inr (ho fun h => h.1 hu)
      · exact Or.inl hu
    have e : L.mem s q = ν q := hν q (List.mem_cons_self ..) hal hr hu
    have hrd : st.read s q = ok (ν q) := by rw [← e]; exact L.read_eq s q
    obtain ⟨hins, hG⟩ := hG _ hrd
    refine insRun_rdN hgr (fun hg u hu => ?_)
      (ih (ν q) s a Wd _ ν (hW _ hrd) hG (hGR _ hrd) (hN _ hrd) hm hk hc ?_)
    · show tr R User cls ko c kb mk ar (k u) Wd a = tr R User cls ko c kb mk ar (k (ν q)) Wd a
      rw [hins hg u hu]
    intro x hx hxa hxr hxu
    exact hν x (List.mem_cons_of_mem _ hx) hxa hxr (hxu.imp_right fun h hT => h (tch_sub hT))
  | rdp q k ih =>
    intro s a Wd T ν hW hG hGR hN hm hk hc hν
    simp only [Within] at hW hGR
    simp only [InsT] at hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    rw [reads_rdN, reads_rdN] at hν
    have hrp := L.read_pair_eq s q
    generalize core.num.U64.wrapping_add q 8#u64 = q8 at *
    obtain ⟨⟨hal, hr⟩, ⟨hal8, hr8⟩, hW⟩ := hW
    obtain ⟨hgr, hgr8, hGR⟩ := hGR
    obtain ⟨hg, hg8, hG⟩ := hG
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
    refine insRun_rdN hgr (fun h => absurd h hg) (insRun_rdN hgr8 (fun h => absurd h hg8)
      (ih (ν q, ν q8) s a Wd _ ν (hW _ hrd) (hG _ hrd) (hGR _ hrd) (hN _ hrd) hm hk hc ?_))
    intro x hx hxa hxr hxu
    exact hν x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) hxa hxr
      (hxu.imp_right fun h hT => h (tch_sub (tch_sub hT)))
  | wr q v k ih =>
    intro s a Wd T ν hW hG hGR hN hm hk hc hν
    simp only [Within] at hW hGR
    simp only [InsT] at hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have hw := L.write_eq s q v
    obtain ⟨hWq, hW⟩ := hW
    have hW := hW _ hw
    obtain ⟨hGq, hG⟩ := hG
    have hG := hG _ hw
    have hGR := hGR.2 _ hw
    have hN := hN _ hw
    have hal := hWr q hWq
    have hm' : st.frame_masks (L.wr s q v) = ok mk := by rw [hmk]; exact hm
    have hk' : L.ksb (L.wr s q v) = kb := by rw [L.ksb_wr]; exact hk
    have hc' : L.cpu (L.wr s q v) = c := by rw [L.cpu_wr]; exact hc
    by_cases hu : User q
    · rw [if_pos hu] at hN hν ⊢
      rw [if_pos hu] at hN
      refine ih _ a Wd _ ν hW hG hGR hN hm' hk' hc' ?_
      intro x hx hxa hxr hxu
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
      simp only [InsRun]
      refine ⟨fun hg => (hGq hg).resolve_left hu, ih _ a _ T _ hW hG hGR hN hm' hk' hc' ?_⟩
      intro x hx hxa hxr hxu
      rw [L.mem_wr s q v x hal hxa]
      by_cases hne : q = x
      · subst hne; rw [if_pos rfl, Function.update_self]
      · rw [if_neg hne, Function.update_of_ne (Ne.symm hne)]; exact hν x hx hxa hxr hxu
  | ksb k ih =>
    intro s a Wd T ν hW hG hGR hN hm hk hc hν
    simp only [Within] at hW hGR
    simp only [InsT] at hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have h : st.ks_base s = ok kb := by rw [← hk]; exact L.ks_base_eq s
    exact ih kb s a Wd T ν (hW _ h) (hG _ h) (hGR _ h) (hN _ h) hm hk hc hν
  | cpu k ih =>
    intro s a Wd T ν hW hG hGR hN hm hk hc hν
    simp only [Within] at hW hGR
    simp only [InsT] at hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have h : st.cur_cpu s = ok c := by rw [← hc]; exact L.cur_cpu_eq s
    exact ih c s a Wd T ν (hW _ h) (hG _ h) (hGR _ h) (hN _ h) hm hk hc hν
  | masks k ih =>
    intro s a Wd T ν hW hG hGR hN hm hk hc hν
    simp only [Within] at hW hGR
    simp only [InsT] at hG
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    exact ih mk s a Wd T ν (hW _ hm) (hG _ hm) (hGR _ hm) (hN _ hm) hm hk hc hν
  | arch op k ih =>
    intro s a Wd T ν hW hG hGR hN hm hk hc hν
    simp only [Within] at hW hGR
    simp only [InsT] at hG
    simp only [Once] at hN
    by_cases hca : ∃ r, callArch ar op a = ok r
    · have e := hca.choose_spec
      simp only [tr, dif_pos hca] at hν ⊢
      exact ih _ s _ Wd T ν (hW _ _ e) (hG _ _ e) (hGR _ _ e) (hN _ _ e) hm hk hc hν
    · simp only [tr, dif_neg hca, InsRun]

end sim

/-! ## A started body is run-relatively insensitive -/

section body
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}
  {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
  {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A)}
  {p : SProg X} {Acc : X → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop}
  {RS WS DS : S → U64 → Prop}

/-- **A body is `InsA` when it starts**, from its per-path obligations, `hAcc` (accepted runs from entry states
read `G` words insensitively, `InsT`) and `hDec` (runs from alternatives of declined entry states touch no `G`
word). `E2EAD.body_insA` with the masked bridge. -/
theorem body_insAQ {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop} (hQ : Equivalence Q)
    (hL : MoveHeld own) (hO : OwnDep own User)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m')
    (hGko : ∀ x, G x → ko x = .free) (hGU : ∀ x, G x → ¬ User x)
    (hp : IsProgOn (F ar) ar st (AltOf st Pre RS cls ko User) p)
    (O : PathObl st (F ar) Acc own cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS)
    (hN : ReadOnce st ar p cls ko User Pre RS) (hT : ∀ s a, ∃ r, F ar st s a = ok r)
    (hmk : MasksWr st)
    (hAcc : ∀ s a r, Pre s → F ar st s a = ok r → Acc r.1 → InsT st ar G Q NP User p s a)
    (hDec : ∀ s s' a r, Pre s → F ar st s a = ok r → ¬ Acc r.1 → Alt st (RS s) cls ko User s s' →
      Within st ar (fun b => ¬ G b) (fun b => User b ∨ ¬ G b) p s' a)
    {σ : S} {a : A} (hpre : Pre σ) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → ¬ User x → L.mem σ x = μ x) :
    InsA G Q NP own cls ko (L.cpu σ) (Locks σ) μ
      (tr (RS σ) User cls ko (L.cpu σ) (L.ksb σ) (masksOf st σ) ar p ∅ a) := by
  have e0 : own (L.mem σ) = own μ := hO _ _ hμ
  let Hp : U64 → Prop := fun x => ¬ User x ∧ (WS σ x ∨ DS σ x)
  have hRI : RInv own (L.cpu σ) (Locks σ) (RpOf (RS σ) User Hp) Hp μ := by
    have hH : ∀ x, Hp x → HeldV (L.cpu σ) (Locks σ) (own μ x) := by
      intro x hx
      rw [← e0]; exact heldBy_iff.mp (O.write_own σ x hpre hx.2 hx.1)
    refine ⟨hH, fun x hx => ?_⟩
    rcases hx with ⟨hu, hr⟩ | hx
    · rw [← e0]
      rcases O.read_own σ x hpre hr hu with h | h
      · exact Or.inl (heldBy_iff.mp h)
      · exact Or.inr h
    · exact Or.inl (hH x hx)
  refine insA_of_runsQ hQ hL hGo hGko (Rp := RpOf (RS σ) User Hp) (Hp := Hp) _ ∅ μ
    (fun _ => none) ⟨fun ν hν => ?_, fun y u hu => (by cases hu), fun y u hu => (by cases hu),
      fun y u hu => (by cases hu), hRI, fun y u hu => (by cases hu)⟩
  have hνR : ∀ x, ¬ User x → RS σ x → ν x = μ x := fun x hu hr => hν.1 x (hRI.2 x (Or.inl ⟨hu, hr⟩))
  generalize hq : tr (RS σ) User cls ko (L.cpu σ) (L.ksb σ) (masksOf st σ) ar p ∅ a = q
  let rl := (reads q ν).filter (fun x => decide (Aligned x))
  let ul := rl.filter (fun x => decide (User x))
  let kl := rl.filter (fun x => decide (¬ User x))
  have hul : ∀ x, x ∈ ul ↔ (x ∈ reads q ν ∧ Aligned x) ∧ User x := by
    intro x; simp only [ul, rl, List.mem_filter, decide_eq_true_eq]
  have hkl : ∀ x, x ∈ kl ↔ (x ∈ reads q ν ∧ Aligned x) ∧ ¬ User x := by
    intro x; simp only [kl, rl, List.mem_filter, decide_eq_true_eq]
  obtain ⟨σu, hσu⟩ : ∃ s, s = wrs st ν ul σ := ⟨_, rfl⟩
  obtain ⟨σν, hσν⟩ : ∃ s, s = wrs st ν kl σu := ⟨_, rfl⟩
  obtain ⟨uP, uL, uR, uW, uD⟩ := wrs_user st Sd (ν := ν) ul σ
    (fun x hx => ⟨((hul x).mp hx).2, ((hul x).mp hx).1.2⟩) hpre
  obtain ⟨uc, ub, um⟩ := wrs_const st (ν := ν) hmk ul σ
  have uM := wrs_mem st (ν := ν) ul σ (fun x hx => ((hul x).mp hx).1.2)
  rw [← hσu] at uP uL uR uW uD uc ub um uM
  obtain ⟨kc, kb, km⟩ := wrs_const st (ν := ν) hmk kl σu
  have kM := wrs_mem st (ν := ν) kl σu (fun x hx => ((hkl x).mp hx).1.2)
  rw [← hσν] at kc kb km kM
  have hmσ := masksOf_eq st σ
  have uMk : ∀ x, Aligned x → ¬ User x → L.mem σu x = μ x := by
    intro x hx hu
    rw [uM x hx, if_neg (fun h => hu ((hul x).mp h).2)]; exact hμ x hx hu
  obtain ⟨ru, hru⟩ := hT σu a
  by_cases hacc : Acc ru.1
  · -- accepted at `σu`
    have gu : AltOf st Pre RS cls ko User σu := AltOf.pre uP
    have hW := O.acc σu a ru uP hru hacc
    rw [hp _ (Narrow.guard _ _ _) σu gu a] at hW
    have hW := (interp_guard p σu a ru hW).2
    have hA := Sd.read_aligned σu σu a ru uP (Alt.refl σu) hru
    rw [hp _ (Narrow.guard _ _ _) σu gu a] at hA
    have hA := (interp_guard p σu a ru hA).2
    have hM := O.move_steps hp uP gu hru
    have hO1 := hN σu σu a ru uP (Alt.refl σu) (by rw [← hp _ (Narrow.self st) σu gu a]; exact hru)
    have hG := hAcc σu a ru uP hru hacc
    rw [uR] at hW hO1; rw [uW] at hW; rw [uc, uL] at hM
    have hWa : ∀ x, True ∧ WS σ x → Aligned x ∧ (¬ User x → Hp x) := fun x hx =>
      ⟨O.aligned σ x hpre (Or.inl hx.2), fun hu => ⟨hu, Or.inl hx.2⟩⟩
    have hνa : ∀ x ∈ reads q ν, Aligned x → RS σ x → (¬ User x ∨ x ∉ (∅ : Set U64)) →
        L.mem σu x = ν x := by
      intro x hx hxa hxr _
      by_cases hu : User x
      · rw [uM x hxa, if_pos ((hul x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
      · rw [uMk x hxa hu, hνR x hu hxr]
    have hGR : Within st ar (fun b => G b → RS σ b ∧ ¬ User b) (fun _ => True) p σu a :=
      Within.mono (fun b hb hg => ⟨hb.2, hGU b hg⟩) (fun _ _ => trivial) p σu a (within_and p σu a hA hW)
    rw [← hq] at hνa ⊢
    exact ⟨μ, fun y hy => absurd rfl hy,
      sim (L := L) hO hmk (Rr := RS σ) (Wr := fun x => True ∧ WS σ x) hWa p σu a ∅ ∅ ∅ ν μ
        (within_and p σu a hA hW) hM hO1 (fun x hx => absurd hx (Set.notMem_empty x)) subset_rfl
        (um.trans hmσ) ub uc (fun x hx hu => (uMk x hx hu).symm) hνa,
      insT_sim (L := L) hmk (Rr := RS σ) (Wr := fun x => True ∧ WS σ x) (fun x hx => (hWa x hx).1) p σu a
        ∅ ∅ ν (within_and p σu a hA hW) hG hGR hO1 (um.trans hmσ) ub uc hνa⟩
  · -- declined at `σu`
    have hAlt : Alt st (RS σu) cls ko User σu σν := by
      refine ⟨kc, kb, km, fun x hx => ?_, fun x hx hu hko => ?_⟩
      · have hxa := Sd.rs_aligned σu x uP hx
        rw [uR] at hx
        rw [kM x hxa]
        split_ifs with h
        · have hu := ((hkl x).mp h).2
          rw [hνR x hu hx, uMk x hxa hu]
        · rfl
      · have hxa : Aligned x := Sd.ko_aligned x (by rcases hko with h | h <;> rw [h] <;> simp)
        rw [kM x hxa]
        split_ifs with h
        · rw [uc] at hko
          rw [hν.2.2 x hko, uMk x hxa hu]
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
    have hO1 := hN σu σν a rν uP hAlt (by rw [← hp _ (Narrow.self st) σν gν a]; exact hrν)
    have hG0 := hDec σu σν a ru uP hru hacc hAlt
    have hG := insT_of_within (Q := Q) (NP := NP) p σν a hG0
    have hGR : Within st ar (fun b => G b → RS σ b ∧ ¬ User b) (fun _ => True) p σν a :=
      Within.mono (fun b hb hg => absurd hg hb) (fun _ _ => trivial) p σν a hG0
    rw [uR] at hO1; rw [uD] at hW; rw [uc, uL] at hM
    have hWa : ∀ x, True ∧ DS σ x → Aligned x ∧ (¬ User x → Hp x) := fun x hx =>
      ⟨O.aligned σ x hpre (Or.inr hx.2), fun hu => ⟨hu, Or.inr hx.2⟩⟩
    have hνa : ∀ x ∈ reads q ν, Aligned x → True → (¬ User x ∨ x ∉ (∅ : Set U64)) →
        L.mem σν x = ν x := by
      intro x hx hxa _ _
      rw [kM x hxa]
      by_cases hu : User x
      · rw [if_neg (fun h => ((hkl x).mp h).2 hu), uM x hxa,
          if_pos ((hul x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
      · rw [if_pos ((hkl x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
    refine ⟨fun x => if Aligned x ∧ ¬ User x then L.mem σν x else μ x, fun y hy hpo => ?_, ?_⟩
    · apply hy
      beta_reduce
      split_ifs with h
      · rw [kM y h.1, uMk y h.1 h.2]
        split_ifs
        · exact hν.1 y hpo
        · rfl
      · rfl
    · rw [← hq] at hνa ⊢
      exact ⟨sim (L := L) hO hmk (Rr := fun _ => True) (Wr := fun x => True ∧ DS σ x) hWa p σν a
        ∅ ∅ ∅ ν _ (within_and p σν a hA hW) hM hO1 (fun x hx => absurd hx (Set.notMem_empty x))
        subset_rfl (km.trans (um.trans hmσ)) (kb.trans ub) (kc.trans uc)
        (fun x hx hu => if_pos ⟨hx, hu⟩) hνa,
        insT_sim (L := L) hmk (Rr := fun _ => True) (Wr := fun x => True ∧ DS σ x) (fun x hx => (hWa x hx).1)
          p σν a ∅ ∅ ν (within_and p σν a hA hW) hG hGR hO1 (km.trans (um.trans hmσ)) (kb.trans ub)
          (kc.trans uc) hνa⟩

end body

section top
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **A body a local path starts is run-relatively insensitive** to `G` (the masked bridge): accepted runs from
entry states are `InsT` (`hAcc`), runs from alternatives of declined entry states touch no `G` word (`hDec`). -/
theorem LocalPath.insAQ (P : LocalPath own cls ko User) {G : U64 → Prop} {Q : U64 → U64 → Prop}
    {NP : U64 → Prop} (hQ : Equivalence Q) (hL : MoveHeld own) (hO : OwnDep own User)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m')
    (hGko : ∀ x, G x → ko x = .free) (hGU : ∀ x, G x → ¬ User x)
    (hAcc : ∀ s a r, P.Pre s → P.F P.ar P.st s a = ok r → P.Acc r.1 → InsT P.st P.ar G Q NP User P.p s a)
    (hDec : ∀ s s' a r, P.Pre s → P.F P.ar P.st s a = ok r → ¬ P.Acc r.1 →
      @Alt P.S P.st P.L (P.RS s) cls ko User s s' →
      Within P.st P.ar (fun b => ¬ G b) (fun b => User b ∨ ¬ G b) P.p s' a)
    {c : U64} {hs : U64 → Prop} {μ : U64 → U64} {q : SP}
    (h : StartAt P c hs μ q) : InsA G Q NP own cls ko c hs μ q := by
  obtain ⟨σ, a, hpre, rfl, rfl, hμ, rfl⟩ := h
  let _ := P.L
  exact body_insAQ hQ hL hO hGo hGko hGU P.isProg P.obl P.side P.once P.total P.masks hAcc hDec hpre hμ

end top

end

end Fl4Proofs.P2.E2E

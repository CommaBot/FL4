/-
# P2 (line mmuAD, gen 9): **PageMap's leaf store under A/D writes** — `write_mapping` is `InsTP`

`vspace.rs` l. 444-458:

```rust
fn write_mapping(s, a, slot, e, asid, vaddr, defer) {
    let old = s.read(slot);            // l. 445: used only through `old & P_PRESENT`, rights_raised / rights_lowered
    s.write(slot, e);                  // l. 446: the present store; `slot` joins the done set
    if old & P_PRESENT == 0 { return; }
    if rights_raised(old, e) { a.invalidate_page(asid, vaddr); return; }
    if defer && rights_lowered(old, e) { return; }
    a.invalidate_asid(asid);
}
```

* Constants `adP_RW_eq` … `adP_XD_eq`; **`sameFT_adEq`**, **`rr_adEq`**, **`rl_adEq`**: `same_frame_and_type` /
  `rights_raised` / `rights_lowered` are `ADEq`-blind in `old` (they test `ADDR_MASK | PWT | PCD | PAT_4K |
  PAT_LARGE | PS`, `RW`, `US`, `XD` — no bit 5 or 6).
* `insTP_ret`, `insTP_arch`, `insTP_ite`, `insTP_liftR_sbind` (tree-shape steps of `E2EADQP.InsTP`).
* **`insTP_write_mapping`**: for every state, `write_mapping` is `InsTP … E D` provided the leaf may be stored
  (`slot ∉ D` unless it is a user word) and the done set after the store, `dU G NotPresent D slot e`, is inside `E`.

No premise. New module; no existing statement changed.
-/
import Fl4Proofs.P2.MmuADStep
import Fl4Proofs.P2.E2EADQP
import Fl4Proofs.P2.ProgGenPmTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.MmuAD (ADEq NotPresent and_eq_of_adEq kP kRW kUS kXD adBits)
open Fl4Proofs.P3.Vs (P_PRESENT_eq P_PS_eq)
open Fl4Proofs.P2.E2E (InsTP InsT)
open Fl4Proofs.P2.Serial (dU)

noncomputable section

theorem adP_RW_eq : vspace.P_RW = ok 2#u64 := by
  unfold vspace.P_RW; rw [Fl4Proofs.P3.shl_eq _ _ (by decide) (by decide)]; rfl
theorem adP_US_eq : vspace.P_US = ok 4#u64 := by
  unfold vspace.P_US; rw [Fl4Proofs.P3.shl_eq _ _ (by decide) (by decide)]; rfl
theorem adP_PWT_eq : vspace.P_PWT = ok 8#u64 := by
  unfold vspace.P_PWT; rw [Fl4Proofs.P3.shl_eq _ _ (by decide) (by decide)]; rfl
theorem adP_PCD_eq : vspace.P_PCD = ok 16#u64 := by
  unfold vspace.P_PCD; rw [Fl4Proofs.P3.shl_eq _ _ (by decide) (by decide)]; rfl
theorem adP_PAT4_eq : vspace.P_PAT_4K = ok 128#u64 := by
  unfold vspace.P_PAT_4K; rw [Fl4Proofs.P3.shl_eq _ _ (by decide) (by decide)]; rfl
theorem adP_PATL_eq : vspace.P_PAT_LARGE = ok 4096#u64 := by
  unfold vspace.P_PAT_LARGE; rw [Fl4Proofs.P3.shl_eq _ _ (by decide) (by decide)]; rfl
theorem adP_XD_eq : vspace.P_XD = ok 9223372036854775808#u64 := by
  unfold vspace.P_XD; rw [Fl4Proofs.P3.shl_eq _ _ (by decide) (by decide)]; rfl

/-- `same_frame_and_type` ignores bits 5 and 6 of the old entry. -/
theorem sameFT_adEq {u v : U64} (h : ADEq u v) (e : U64) :
    vspace.same_frame_and_type u e = vspace.same_frame_and_type v e := by
  unfold vspace.same_frame_and_type
  simp only [adP_PWT_eq, adP_PCD_eq, adP_PAT4_eq, adP_PATL_eq, P_PS_eq, lift, bind_ok]
  rw [and_eq_of_adEq h]
  unfold vspace.ADDR_MASK adBits; decide

/-- `rights_raised` ignores bits 5 and 6 of the old entry. -/
theorem rr_adEq {u v : U64} (h : ADEq u v) (e : U64) : vspace.rights_raised u e = vspace.rights_raised v e := by
  unfold vspace.rights_raised
  rw [sameFT_adEq h]
  simp only [adP_RW_eq, adP_US_eq, adP_XD_eq, lift, bind_ok, and_eq_of_adEq h kRW, and_eq_of_adEq h kUS,
    and_eq_of_adEq h kXD]

/-- `rights_lowered` ignores bits 5 and 6 of the old entry. -/
theorem rl_adEq {u v : U64} (h : ADEq u v) (e : U64) : vspace.rights_lowered u e = vspace.rights_lowered v e := by
  unfold vspace.rights_lowered
  rw [sameFT_adEq h]
  simp only [adP_RW_eq, adP_US_eq, adP_XD_eq, lift, bind_ok, and_eq_of_adEq h kRW, and_eq_of_adEq h kUS,
    and_eq_of_adEq h kXD]

section tree
variable {S A X Y : Type} {st : machine.Store S} {ar : machine.Arch A} {G Q' : U64 → Prop}
  {Q : U64 → U64 → Prop} {NP User : U64 → Prop} {E D : Set U64}

theorem insTP_ret {x : X} {s : S} {a : A} (h : D ⊆ E) : InsTP st ar G Q NP User E D (.ret x) s a := by
  simp only [InsTP]; exact h

theorem insTP_arch {op : ArchCall} {k : AV → SProg X} {s : S} {a : A}
    (h : ∀ v a', callArch ar op a = ok (v, a') → InsTP st ar G Q NP User E D (k v) s a') :
    InsTP st ar G Q NP User E D (.arch op k) s a := by
  simp only [InsTP]; exact h

theorem insTP_ite {c : Prop} [Decidable c] {p q : SProg X} {s : S} {a : A}
    (hp : InsTP st ar G Q NP User E D p s a) (hq : InsTP st ar G Q NP User E D q s a) :
    InsTP st ar G Q NP User E D (if c then p else q) s a := by
  by_cases h : c
  · rw [if_pos h]; exact hp
  · rw [if_neg h]; exact hq

theorem insTP_liftR_sbind {r : Result X} {f : X → SProg Y} {s : S} {a : A}
    (hf : ∀ x, InsTP st ar G Q NP User E D (f x) s a) :
    InsTP st ar G Q NP User E D ((SProg.liftR r).sbind f) s a := by
  unfold SProg.liftR
  by_cases h1 : ∃ v, r = ok v
  · rw [dif_pos h1]; exact hf _
  · rw [dif_neg h1]
    by_cases h2 : ∃ e, r = fail e
    · rw [dif_pos h2]; simp only [SProg.sbind, InsTP]
    · rw [dif_neg h2]; simp only [SProg.sbind, InsTP]

end tree

macro "wm_rest_tac" hE:term : tactic => `(tactic| repeat' (first
  | exact insTP_ret $hE
  | apply insTP_ite
  | (refine insTP_liftR_sbind fun _ => ?_)
  | (refine insTP_arch fun _ _ _ => ?_)
  | (simp only [SProg.sbind, AR.invalidate_page, AR.invalidate_asid])))

/-- **`write_mapping` is `InsTP`** (module docstring): the old entry is read through `&&& P_PRESENT`,
`rights_raised`, `rights_lowered` only; the new entry is stored once. -/
theorem insTP_write_mapping {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {G User : U64 → Prop}
    {E D : Set U64} (slot e asid vaddr : U64) (defer : Bool) (hslot : ¬ User slot → slot ∉ D)
    (hE : dU G NotPresent D slot e ⊆ E) :
    ∀ (s : S) (a : A), InsTP st ar G ADEq NotPresent User E D (R.vspace.write_mapping slot e asid vaddr defer) s a := by
  intro s a
  unfold R.vspace.write_mapping
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.read, SProg.write, SProg.sbind, P_PRESENT_eq,
    SProg.liftR_ok]
  simp only [InsTP]
  intro v _
  refine ⟨fun _ u huv => ?_, hslot, fun s' _ => ?_⟩
  · simp only [and_eq_of_adEq huv kP, rr_adEq huv, rl_adEq huv]
  · wm_rest_tac hE

/-! ## Splitting `InsTP` into reads and stores -/

section split
variable {S A X : Type} (st : machine.Store S) (ar : machine.Arch A)

/-- **The store discipline of `InsTP`** alone: no kernel store into a done word; a present store into a `G` word
joins the done set; the done set ends inside `E`. Reads are unconstrained. -/
def StOnce (G : U64 → Prop) (NP : U64 → Prop) (User : U64 → Prop) (E : Set U64) :
    Set U64 → SProg X → S → A → Prop
  | D, .ret _, _, _ => D ⊆ E
  | _, .err _, _, _ => True
  | D, .rd q k, s, a => ∀ v, st.read s q = ok v → StOnce G NP User E D (k v) s a
  | D, .rdp q k, s, a => ∀ v, st.read_pair s q = ok v → StOnce G NP User E D (k v) s a
  | D, .wr q v k, s, a => (¬ User q → q ∉ D) ∧
      ∀ s', st.write s q v = ok s' → StOnce G NP User E (dU G NP D q v) k s' a
  | _, .zero _ _ _, _, _ => True
  | _, .clr _ _ _, _, _ => True
  | D, .ksb k, s, a => ∀ v, st.ks_base s = ok v → StOnce G NP User E D (k v) s a
  | D, .cpu k, s, a => ∀ v, st.cur_cpu s = ok v → StOnce G NP User E D (k v) s a
  | D, .masks k, s, a => ∀ v, st.frame_masks s = ok v → StOnce G NP User E D (k v) s a
  | D, .arch op k, s, a => ∀ v a', callArch ar op a = ok (v, a') → StOnce G NP User E D (k v) s a'

variable {st ar} {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP User : U64 → Prop}

/-- **`InsTP` = the reads of `InsT` (stores unconstrained: `NP := True`) + `StOnce`.** So the gen 6 / 7 `InsT`
walk tools (`insT_gstep`, `insT_entR`, …, all generic in `NP`) give the read half at `NP := fun _ => True`. -/
theorem insTP_of_split (p : SProg X) : ∀ (E D : Set U64) (s : S) (a : A),
    InsT st ar G Q (fun _ => True) User p s a → StOnce st ar G NP User E D p s a →
    InsTP st ar G Q NP User E D p s a := by
  induction p with
  | ret x => intro E D s a _ h; exact h
  | err e => intros; trivial
  | zero q n k ih => intros; trivial
  | clr q n k ih => intros; trivial
  | rd q k ih =>
    intro E D s a hr hw
    simp only [InsT] at hr; simp only [StOnce] at hw; simp only [InsTP]
    exact fun v hv => ⟨(hr v hv).1, ih v E D s a (hr v hv).2 (hw v hv)⟩
  | rdp q k ih =>
    intro E D s a hr hw
    simp only [InsT] at hr; simp only [StOnce] at hw; simp only [InsTP]
    exact ⟨hr.1, hr.2.1, fun v hv => ih v E D s a (hr.2.2 v hv) (hw v hv)⟩
  | wr q v k ih =>
    intro E D s a hr hw
    simp only [InsT] at hr; simp only [StOnce] at hw; simp only [InsTP]
    exact ⟨hw.1, fun s' hs => ih _ _ s' a (hr.2 s' hs) (hw.2 s' hs)⟩
  | ksb k ih =>
    intro E D s a hr hw; simp only [InsT] at hr; simp only [StOnce] at hw; simp only [InsTP]
    exact fun v hv => ih v E D s a (hr v hv) (hw v hv)
  | cpu k ih =>
    intro E D s a hr hw; simp only [InsT] at hr; simp only [StOnce] at hw; simp only [InsTP]
    exact fun v hv => ih v E D s a (hr v hv) (hw v hv)
  | masks k ih =>
    intro E D s a hr hw; simp only [InsT] at hr; simp only [StOnce] at hw; simp only [InsTP]
    exact fun v hv => ih v E D s a (hr v hv) (hw v hv)
  | arch op k ih =>
    intro E D s a hr hw; simp only [InsT] at hr; simp only [StOnce] at hw; simp only [InsTP]
    exact fun v a' hv => ih v E D s a' (hr v a' hv) (hw v a' hv)

/-- A run storing into no `G` word keeps a done set of `G` words (`StOnce` of a guarded segment). -/
theorem stOnce_of_within (hGU : ∀ x, G x → ¬ User x) {E D : Set U64} (hDG : ∀ x ∈ D, G x) (hDE : D ⊆ E)
    {Rd : U64 → Prop} (p : SProg X) : ∀ (s : S) (a : A),
    Within st ar Rd (fun b => User b ∨ ¬ G b) p s a → StOnce st ar G NP User E D p s a := by
  induction p with
  | ret x => intros; exact hDE
  | err e => intros; trivial
  | zero q n k ih => intros; trivial
  | clr q n k ih => intros; trivial
  | rd q k ih =>
    intro s a h; simp only [Within] at h; simp only [StOnce]; exact fun v hv => ih v s a (h.2 v hv)
  | rdp q k ih =>
    intro s a h; simp only [Within] at h; simp only [StOnce]; exact fun v hv => ih v s a (h.2.2 v hv)
  | wr q v k ih =>
    intro s a h
    simp only [Within] at h; simp only [StOnce]
    have hg : ¬ G q := by
      rcases h.1 with hu | hg
      · exact fun hg => hGU q hg hu
      · exact hg
    refine ⟨fun _ hq => hg (hDG q hq), fun s' hs => ?_⟩
    rw [Fl4Proofs.P2.E2E.dU_nG hg]; exact ih s' a (h.2 s' hs)
  | ksb k ih => intro s a h; simp only [Within] at h; simp only [StOnce]; exact fun v hv => ih v s a (h v hv)
  | cpu k ih => intro s a h; simp only [Within] at h; simp only [StOnce]; exact fun v hv => ih v s a (h v hv)
  | masks k ih => intro s a h; simp only [Within] at h; simp only [StOnce]; exact fun v hv => ih v s a (h v hv)
  | arch op k ih =>
    intro s a h; simp only [Within] at h; simp only [StOnce]; exact fun v a' hv => ih v s a' (h v a' hv)

end split

end
end Fl4Proofs.P2.PathObl

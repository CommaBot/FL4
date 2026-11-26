/-
# P2 (line mmuAD, gen 7): **walking `InsT` along a run** — step lemmas and the `unmap_page` site

The accepted-run obligation `E2EPU3e.AccIns` is `E2EADQ.InsT` of `R.invBodyG` along the real run. Here the walk's
tools, in the run-hypothesis form of `OnceWalk.once_gstep` (the run of the whole tree, `h`, is carried along):

* **`insT_gstep`**: a call whose run is reproduced on `guard st R0 W0` with `R0`, `W0` off `G` touches no `G`
  word, so `InsT` of `p.sbind k` reduces to `InsT` of `k` at the call's result; `insT_liftR`, `insT_ite`
  (pure steps), `insT_rdN` (one read of a non-`G` word);
* **`SInsW Q NP`**: insensitive on every branch (reads by `Q`-insensitive continuations, stores of `NP` values,
  frame masks and Arch calls free); `sInsW_of_sIns`, `sInsW_sbind`, `sInsW_liftR_sbind`, `sInsW_ite`,
  **`insT_of_sInsW`** (every word set, every state);
* **`sInsW_unmap_rest`**: `unmap_page`'s tree after `find_vspace_for_asid` is `SInsW ADEq NotPresent` for every
  frame size and root: the walk (`MmuADTree.sIns_lookup_*`), the leaf read (used only through `&&& 1`, `&&& 128`
  and `frame_base`, i.e. `&&& ADDR_MASK` / `kLarge` / `kHuge`), `frame_gpa` (frame masks), the store `0`
  (`NotPresent 0`) and `invalidate_page`;
* **`insT_unmap_page`**: `InsT` of `(R.vspace.unmap_page size asid va fp).sbind f` from a run of
  `find_vspace_for_asid` reproduced on a store guarded to a read set off `G` (the ASID words) and `InsT` of `f` at
  the results of `unmap_page`'s run.

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.MmuADTree
import Fl4Proofs.P2.OnceWalk
import Fl4Proofs.P2.ProgGenCd10
import Fl4Proofs.P2.MmuADProg
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.MmuAD (ADEq NotPresent and_eq_of_adEq kP kPS kADDR kLarge kHuge)
open Fl4Proofs.P3.Vs (P_PRESENT_eq P_PS_eq)
open Fl4Proofs.P2.E2E (InsT insT_of_within insT_sbind)

noncomputable section

section steps
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {G : U64 → Prop} {Q : U64 → U64 → Prop}
  {NP User : U64 → Prop}

/-- **A call run alike on a store guarded off `G`** (module docstring). -/
theorem insT_gstep {X Y : Type} {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → ¬ G q) (hW0 : ∀ q, W0 q → ¬ G q)
    {p : SProg X} {k : X → SProg Y} {s : S} {a : A} {r' : Y × S × A}
    (h : interp st ar (p.sbind k) s a = ok r')
    (hg : ∀ r, interp st ar p s a = ok r → interp (guard st R0 W0) ar p s a = ok r)
    (hk : ∀ r, interp st ar p s a = ok r → interp st ar (k r.1) r.2.1 r.2.2 = ok r' →
      InsT st ar G Q NP User (k r.1) r.2.1 r.2.2) :
    InsT st ar G Q NP User (p.sbind k) s a := by
  rw [interp_sbind] at h
  obtain ⟨r0, h0, hk0⟩ := bind_eq_ok' h
  have w := (interp_guard p s a r0 (hg r0 h0)).2
  refine insT_sbind p k s a (insT_of_within p s a
    (Within.mono (fun b hb => hR0 b hb) (fun b hb => Or.inr (hW0 b hb)) p s a w)) fun r hr => ?_
  rw [h0] at hr
  cases ok_inj_ff hr
  exact hk r0 h0 hk0

/-- A pure step keeps the run hypothesis. -/
theorem insT_liftR {X Y : Type} {e : Result X} {k : X → SProg Y} {s : S} {a : A} {r' : Y × S × A}
    (h : interp st ar ((SProg.liftR e).sbind k) s a = ok r')
    (hk : ∀ v, e = ok v → interp st ar (k v) s a = ok r' → InsT st ar G Q NP User (k v) s a) :
    InsT st ar G Q NP User ((SProg.liftR e).sbind k) s a := by
  unfold SProg.liftR at h ⊢
  by_cases hx : ∃ v, e = ok v
  · rw [dif_pos hx] at h ⊢
    simp only [SProg.sbind] at h ⊢
    exact hk _ hx.choose_spec h
  · rw [dif_neg hx]
    split <;> simp only [SProg.sbind, InsT]

/-- An `if` on a pure condition keeps the run hypothesis. -/
theorem insT_ite {X : Type} {c : Prop} [Decidable c] {p q : SProg X} {s : S} {a : A} {r' : X × S × A}
    (h : interp st ar (if c then p else q) s a = ok r')
    (hp : c → interp st ar p s a = ok r' → InsT st ar G Q NP User p s a)
    (hq : ¬ c → interp st ar q s a = ok r' → InsT st ar G Q NP User q s a) :
    InsT st ar G Q NP User (if c then p else q) s a := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢; exact hp hc h
  · rw [if_neg hc] at h ⊢; exact hq hc h

/-- One read of a word off `G`. -/
theorem insT_rdN {X : Type} {q : U64} {k : U64 → SProg X} {s : S} {a : A} {r' : X × S × A} (hq : ¬ G q)
    (h : interp st ar (.rd q k) s a = ok r')
    (hk : ∀ v, st.read s q = ok v → interp st ar (k v) s a = ok r' → InsT st ar G Q NP User (k v) s a) :
    InsT st ar G Q NP User (.rd q k) s a := by
  simp only [interp] at h
  obtain ⟨v0, hv0, h⟩ := bind_eq_ok' h
  simp only [InsT]
  intro v hv
  rw [hv0] at hv
  cases ok_inj_ff hv
  exact ⟨fun hg => absurd hg hq, hk v0 hv0 h⟩

end steps

/-! ## Insensitive on every branch, with stores -/

section sinsw
variable (Q : U64 → U64 → Prop) (NP : U64 → Prop)

/-- **Insensitive on every branch, stores allowed** (module docstring). -/
inductive SInsW {X : Type} : SProg X → Prop
  | ret (x : X) : SInsW (.ret x)
  | err (e : Error) : SInsW (.err e)
  | rd {q : U64} {k : U64 → SProg X} : (∀ u v, Q u v → k u = k v) → (∀ v, SInsW (k v)) → SInsW (.rd q k)
  | wr {q v : U64} {k : SProg X} : NP v → SInsW k → SInsW (.wr q v k)
  | masks {k : U64 × U64 → SProg X} : (∀ v, SInsW (k v)) → SInsW (.masks k)
  | arch {op : ArchCall} {k : AV → SProg X} : (∀ v, SInsW (k v)) → SInsW (.arch op k)

variable {Q NP}

theorem sInsW_sbind {X Y : Type} {p : SProg X} {f : X → SProg Y} (hp : SInsW Q NP p)
    (hf : ∀ x, SInsW Q NP (f x)) : SInsW Q NP (p.sbind f) := by
  induction hp with
  | ret x => exact hf x
  | err e => exact .err e
  | rd hk _ ih => exact .rd (fun u v huv => by simp only [hk u v huv]) ih
  | wr hv _ ih => exact .wr hv ih
  | masks _ ih => exact .masks ih
  | arch _ ih => exact .arch ih

theorem sInsW_of_sIns {X : Type} {p : SProg X} (hp : SInsQ Q p) : SInsW Q NP p := by
  induction hp with
  | ret x => exact .ret x
  | err e => exact .err e
  | rd hk _ ih => exact .rd hk ih

theorem sInsW_liftR_sbind {X Y : Type} {r : Result X} {f : X → SProg Y} (hf : ∀ x, SInsW Q NP (f x)) :
    SInsW Q NP ((SProg.liftR r).sbind f) := by
  unfold SProg.liftR
  by_cases h1 : ∃ v, r = ok v
  · rw [dif_pos h1]; exact hf _
  · rw [dif_neg h1]
    by_cases h2 : ∃ e, r = fail e
    · rw [dif_pos h2]; exact .err _
    · rw [dif_neg h2]; exact .err _

theorem sInsW_ite {X : Type} {c : Prop} [Decidable c] {p q : SProg X} (hp : SInsW Q NP p)
    (hq : SInsW Q NP q) : SInsW Q NP (if c then p else q) := by
  by_cases h : c
  · rw [if_pos h]; exact hp
  · rw [if_neg h]; exact hq

/-- **An everywhere-insensitive tree with `NP` stores is `InsT`** for every word set and state. -/
theorem insT_of_sInsW {S A X : Type} {st : machine.Store S} {ar : machine.Arch A} {G User : U64 → Prop}
    {p : SProg X} (hp : SInsW Q NP p) : ∀ (s : S) (a : A), InsT st ar G Q NP User p s a := by
  induction hp with
  | ret x => intros; trivial
  | err e => intros; trivial
  | rd hk _ ih =>
    intro s a
    simp only [InsT]
    exact fun v _ => ⟨fun _ u huv => hk u v huv, ih v s a⟩
  | wr hv _ ih =>
    intro s a
    simp only [InsT]
    exact ⟨fun _ => Or.inr hv, fun s' _ => ih s' a⟩
  | masks _ ih => intro s a; simp only [InsT]; exact fun v _ => ih v s a
  | arch _ ih => intro s a; simp only [InsT]; exact fun v a' _ => ih v s a'

end sinsw

/-! ## The `unmap_page` site -/

section unmap

theorem frame_base_adEq {u v : U64} (h : ADEq u v) (sz : capability.FrameSize) :
    vspace.frame_base u sz = vspace.frame_base v sz := by
  cases sz <;> simp only [vspace.frame_base]
  · rw [and_eq_of_adEq h kADDR]
  · rw [and_eq_of_adEq h kLarge]
  · rw [and_eq_of_adEq h kHuge]

theorem np_zero : NotPresent 0#u64 := by unfold NotPresent; decide

theorem sInsW_frame_gpa_sbind {Y : Type} (i : U64) {f : U64 → SProg Y} (hf : ∀ x, SInsW ADEq NotPresent (f x)) :
    SInsW ADEq NotPresent ((R.vspace.frame_gpa i).sbind f) := by
  unfold R.vspace.frame_gpa
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind, SProg.frameMasks]
  exact .masks fun v => by
    obtain ⟨a, b⟩ := v
    exact hf _

macro "unmap_rest_tac" : tactic => `(tactic| repeat' (first
  | exact SInsW.ret _
  | exact SInsW.err _
  | apply sInsW_ite
  | (refine sInsW_liftR_sbind fun _ => ?_)
  | (refine sInsW_frame_gpa_sbind _ fun _ => ?_)
  | (apply SInsW.wr np_zero)
  | (refine SInsW.arch fun _ => ?_)
  | (simp only [SProg.write, SProg.sbind, AR.invalidate_page])))

/-- **`InsT` of an `unmap_page` call** (module docstring): its `find_vspace_for_asid` runs alike on a store
guarded to `R0` (off `G`); everything after it is `SInsW ADEq NotPresent`. -/
theorem insT_unmap_page {S A Y : Type} {st : machine.Store S} {ar : machine.Arch A} {G User R0 : U64 → Prop}
    (hR0 : ∀ q, R0 q → ¬ G q) (sz : capability.FrameSize) (asid va fp : U64) {f : Unit → SProg Y} {s : S}
    {a : A} {r' : Y × S × A}
    (h : interp st ar ((R.vspace.unmap_page sz asid va fp).sbind f) s a = ok r')
    (hg : ∀ r, vspace.find_vspace_for_asid st s asid = ok r →
      vspace.find_vspace_for_asid (guard st R0 (fun _ => False)) s asid = ok r)
    (hf : ∀ r, interp st ar (R.vspace.unmap_page sz asid va fp) s a = ok r →
      interp st ar (f r.1) r.2.1 r.2.2 = ok r' → InsT st ar G ADEq NotPresent User (f r.1) r.2.1 r.2.2) :
    InsT st ar G ADEq NotPresent User ((R.vspace.unmap_page sz asid va fp).sbind f) s a := by
  rw [interp_sbind] at h
  obtain ⟨r0, h0, hk0⟩ := bind_eq_ok' h
  refine insT_sbind _ f s a ?_ (fun r hr => by rw [h0] at hr; cases ok_inj_ff hr; exact hf r0 h0 hk0)
  unfold R.vspace.unmap_page at h0 ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h0 ⊢
  refine insT_gstep (R0 := R0) (W0 := fun _ => False) hR0 (fun _ h => h.elim) h0 (fun r h1 => ?_)
    (fun r _ _ => insT_of_sInsW ?_ _ _)
  · rw [R.vspace.find_vspace_for_asid_eq] at h1 ⊢
    obtain ⟨v, hv, e⟩ := bind_eq_ok' h1
    cases ok_inj_ff e
    rw [hg v hv]
    exact bok.mpr ⟨_, rfl, rfl⟩
  obtain ⟨rr, -, -⟩ := r
  cases rr with
  | Err _ => exact .ret _
  | Ok r1 =>
    dsimp only
    refine sInsW_liftR_sbind fun pa => ?_
    cases sz
    · dsimp only
      refine sInsW_sbind (sInsW_of_sIns (sIns_lookup_pt_slot _ _)) fun r2 => ?_
      cases r2 with
      | Err _ => exact .ret _
      | Ok x =>
        dsimp only
        simp only [SProg.read, SProg.sbind, P_PRESENT_eq, P_PS_eq, SProg.liftR_ok]
        refine .rd (fun u v huv => ?_) (fun v => ?_)
        · simp only [and_eq_of_adEq huv kP, and_eq_of_adEq huv kPS, frame_base_adEq huv]
        · unmap_rest_tac
    · dsimp only
      refine sInsW_sbind (sInsW_of_sIns (sIns_lookup_pd_slot _ _)) fun r2 => ?_
      cases r2 with
      | Err _ => exact .ret _
      | Ok x =>
        dsimp only
        simp only [SProg.read, SProg.sbind, P_PRESENT_eq, P_PS_eq, SProg.liftR_ok]
        refine .rd (fun u v huv => ?_) (fun v => ?_)
        · simp only [and_eq_of_adEq huv kP, and_eq_of_adEq huv kPS, frame_base_adEq huv]
        · unmap_rest_tac
    · dsimp only
      refine sInsW_sbind (sInsW_of_sIns (sIns_lookup_pdpt_slot _ _)) fun r2 => ?_
      cases r2 with
      | Err _ => exact .ret _
      | Ok x =>
        dsimp only
        simp only [SProg.read, SProg.sbind, P_PRESENT_eq, P_PS_eq, SProg.liftR_ok]
        refine .rd (fun u v huv => ?_) (fun v => ?_)
        · simp only [and_eq_of_adEq huv kP, and_eq_of_adEq huv kPS, frame_base_adEq huv]
        · unmap_rest_tac

end unmap

end
end Fl4Proofs.P2.PathObl

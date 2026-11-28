/-
P1 (aarch64, gen 34): **the parametrised finaliser footprint `FootCfg`** and **`foot_of_exact`** (the a64-34
contract): a finaliser proves its *exact* write set once (`ExactW`: the TCB field offsets, node offsets and object
words it writes), and every footprint that the existing invariant lemmas consume follows by one monotonicity lemma,
instead of a new whole-namespace copy of the footprint cone (gen 31's `K7`, gen 32's `K8`).

* **`FootCfg`** `{tcbSlotEnd, tcbExcl, objExcl}`: TCB offsets below `tcbSlotEnd` are the TCB's cap slots (never in
  the footprint: 192 on x86_64, 224 on AArch64, where offsets 192–223 are slot 6, `SLOT_HIGH_VSPACE`,
  arch/aarch64/layout.rs:20); `tcbExcl` lists further TCB offsets left out (the debug links 3576 / 3584, the VCPU
  links 3664 / 3672, arch/aarch64/layout.rs); `objExcl` words left out of the object classes (the `Sg` words, the SC
  objects, the endpoint queue words).
* **`KWc C`**: the footprint word class of a configuration; **`FootCfg.Le C C'`** (`C'` coarser), `KWc.mono`.
* The three existing classes are instances, with equivalences, so **K8 stays for its users**: `kw_iff`
  (QueueFoot's `KW` = `KWc K0cfg`), `kw7_iff` (`K7.KW` = `KWc K7cfg`), `kw8_iff` (`K8.KW` = `KWc K8cfg`);
  `K8cfg ≤ K7cfg ≤ K0cfg`.
* **`ExactW`** (an exact write set: TCB offsets, node offsets, object words) with `ExactW.Fits C` (decidable on
  the offset lists), and **`foot_of_exact`**: an exact write set that fits `C`, and `C ≤ C'`, give the `KWc C'`
  footprint. `FootDc` (the footprint with the debug words, QueueFinal's `Foot.d` shape), **`K8.FootD.of_cfg`** (a
  `KWc C` footprint with `C ≤ K8cfg` is a `K8.FootD` footprint, so it feeds gen 31–33's `OSKeep.of_kwd7` /
  `VKeep.of_kwd8` unchanged), `K8.FootD.to_cfg`.
* **Exact write sets of the gen-33 Zombie-loop finalisers**: the CNode and Zombie finalisers write nothing
  (`fin_cnode.exact`, `fin_zombie.exact`: `ExactW.none`), and through `foot_of_exact` their `K8.FootD` footprints
  (`fin_cnode.foot8`, `fin_zombie.foot8`); every `K8.FootD` footprint (the leaf finalisers' of the loop:
  endpoint / notification / reply) restated over `KWc K8cfg` and carried to `K7cfg` by `KWc.mono`
  (`K8.FootD.to_cfg`, `K8.FootD.to7cfg`): the parametrised route gives what `K7` / `K8` gave, with no copy.

The thread finaliser has no exact write set here (it writes VCPU words and the two VCPU-link words, outside every
`KWc`; gen 32's `DS` frame covers it). No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueZombieV
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64}

local notation "wa" => core.num.U64.wrapping_add

/-! ## The configuration and its word class -/

/-- **A footprint configuration** (module docstring). -/
structure FootCfg where
  tcbSlotEnd : Nat
  tcbExcl : Nat → Prop
  objExcl : U64 → Prop

/-- The object words of a footprint: `Sg`, SC objects, endpoint queue words. -/
def ObjW (Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64) (b : U64) : Prop :=
  b ∈ Sg ∨ (∃ c ∈ Scs, InSC c (Z c) b) ∨ (∃ e ∈ Es, b = epHeadA e ∨ b = epTSA e)

/-- **The footprint words of a configuration** (relative to the nodes of `s0`). -/
def KWc (C : FootCfg) (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat)
    (Es : Set U64) (s0 : S) (b : U64) : Prop :=
  (∃ y ∈ T, ∃ K : U64, C.tcbSlotEnd ≤ K.val ∧ K.val < 4096 ∧ ¬ C.tcbExcl K.val ∧ b = wa y K) ∨
  (∃ c ∈ Cs, ∃ o : U64, o.val < 4288 ∧ o.val ≠ 88 ∧ b = L.nodeAt s0 c o) ∨
  (ObjW Sg Scs Z Es b ∧ ¬ C.objExcl b)

/-- `C'` is coarser than `C`: fewer slot offsets, fewer exclusions. -/
def FootCfg.Le (C C' : FootCfg) : Prop :=
  C'.tcbSlotEnd ≤ C.tcbSlotEnd ∧ (∀ k, C'.tcbExcl k → C.tcbExcl k) ∧ (∀ b, C'.objExcl b → C.objExcl b)

theorem FootCfg.Le.refl (C : FootCfg) : C.Le C := ⟨le_rfl, fun _ h => h, fun _ h => h⟩

theorem FootCfg.Le.trans {C1 C2 C3 : FootCfg} (h1 : C1.Le C2) (h2 : C2.Le C3) : C1.Le C3 :=
  ⟨h2.1.trans h1.1, fun k h => h1.2.1 k (h2.2.1 k h), fun b h => h1.2.2 b (h2.2.2 b h)⟩

/-- **Monotonicity of the word class.** -/
theorem KWc.mono {C C' : FootCfg} (hle : C.Le C') {s0 : S} {b : U64} (h : KWc C st T Cs Sg Scs Z Es s0 b) :
    KWc C' st T Cs Sg Scs Z Es s0 b := by
  rcases h with ⟨y, hy, K, k1, k2, k3, e⟩ | h | ⟨ho, hx⟩
  · exact Or.inl ⟨y, hy, K, le_trans hle.1 k1, k2, fun hk => k3 (hle.2.1 _ hk), e⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨ho, fun hb => hx (hle.2.2 _ hb)⟩)

theorem KWc.ksb {C : FootCfg} {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0)
    (h : KWc C st T Cs Sg Scs Z Es s1 b) : KWc C st T Cs Sg Scs Z Es s0 b := by
  rcases h with h | ⟨c, hc, o, ho, h88, e⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨c, hc, o, ho, h88, by rw [e, nodeAt_of_ksb hk]⟩)
  · exact Or.inr (Or.inr h)

/-! ## The existing classes are instances -/

/-- QueueFoot's x86_64-bound class. -/
def K0cfg : FootCfg := ⟨192, fun k => k = 3576 ∨ k = 3584, fun _ => False⟩
/-- Gen 31's `K7` (A64 slot bound 224). -/
def K7cfg : FootCfg := ⟨224, fun k => k = 3576 ∨ k = 3584, fun _ => False⟩
/-- Gen 32's `K8` (also without the VCPU links 3664 / 3672). -/
def K8cfg : FootCfg := ⟨224, fun k => k = 3576 ∨ k = 3584 ∨ k = 3664 ∨ k = 3672, fun _ => False⟩

theorem K8cfg_le_K7cfg : K8cfg.Le K7cfg :=
  ⟨le_rfl, fun k h => by rcases h with h | h <;> simp [K8cfg, h], fun _ h => h⟩

theorem K7cfg_le_K0cfg : K7cfg.Le K0cfg := ⟨by decide, fun _ h => h, fun _ h => h⟩

theorem objW_iff {b : U64} : (ObjW Sg Scs Z Es b ∧ ¬ False) ↔
    (b ∈ Sg ∨ (∃ c ∈ Scs, InSC c (Z c) b) ∨ (∃ e ∈ Es, b = epHeadA e ∨ b = epTSA e)) := by
  unfold ObjW; simp

theorem kw_iff {s0 : S} {b : U64} : KW st T Cs Sg Scs Z Es s0 b ↔ KWc K0cfg st T Cs Sg Scs Z Es s0 b := by
  unfold KW KWc K0cfg
  simp only
  rw [objW_iff]
  constructor
  · rintro (⟨y, hy, K, k1, k2, k3, k4, e⟩ | h)
    · exact Or.inl ⟨y, hy, K, k1, k2, by omega, e⟩
    · exact Or.inr h
  · rintro (⟨y, hy, K, k1, k2, k3, e⟩ | h)
    · exact Or.inl ⟨y, hy, K, k1, k2, by omega, by omega, e⟩
    · exact Or.inr h

theorem kw7_iff {s0 : S} {b : U64} : K7.KW st T Cs Sg Scs Z Es s0 b ↔ KWc K7cfg st T Cs Sg Scs Z Es s0 b := by
  unfold K7.KW KWc K7cfg
  simp only
  rw [objW_iff]
  constructor
  · rintro (⟨y, hy, K, k1, k2, k3, k4, e⟩ | h)
    · exact Or.inl ⟨y, hy, K, k1, k2, by omega, e⟩
    · exact Or.inr h
  · rintro (⟨y, hy, K, k1, k2, k3, e⟩ | h)
    · exact Or.inl ⟨y, hy, K, k1, k2, by omega, by omega, e⟩
    · exact Or.inr h

theorem kw8_iff {s0 : S} {b : U64} : K8.KW st T Cs Sg Scs Z Es s0 b ↔ KWc K8cfg st T Cs Sg Scs Z Es s0 b := by
  unfold K8.KW KWc K8cfg
  simp only
  rw [objW_iff]
  constructor
  · rintro (⟨y, hy, K, k1, k2, k3, k4, e⟩ | h)
    · exact Or.inl ⟨y, hy, K, k1, k2, by omega, e⟩
    · exact Or.inr h
  · rintro (⟨y, hy, K, k1, k2, k3, e⟩ | h)
    · exact Or.inl ⟨y, hy, K, k1, k2, by omega, ⟨by omega, by omega, by omega⟩, e⟩
    · exact Or.inr h

/-! ## Exact write sets -/

/-- **An exact write set**: the TCB field offsets (of threads in `Tw`), the node offsets (of nodes in `Cw`) and
the object words a function writes. -/
structure ExactW where
  tcbOffs : List Nat
  nodeOffs : List Nat
  obj : U64 → Prop

/-- The words of an exact write set (relative to the nodes of `s0`). -/
def ExactW.W (E : ExactW) (st : machine.Store S) [L : LawfulStore st] (Tw Cw : Set U64) (s0 : S) (b : U64) :
    Prop :=
  (∃ y ∈ Tw, ∃ K : U64, K.val ∈ E.tcbOffs ∧ b = wa y K) ∨
  (∃ c ∈ Cw, ∃ o : U64, o.val ∈ E.nodeOffs ∧ b = L.nodeAt s0 c o) ∨ E.obj b

/-- The write set that writes nothing. -/
def ExactW.none : ExactW := ⟨[], [], fun _ => False⟩

/-- **An exact write set fits a configuration**: its TCB offsets are footprint offsets of `C`, its node offsets
are node words of the footprint, its object words are footprint object words of `C`. -/
def ExactW.Fits (E : ExactW) (C : FootCfg) (Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64) : Prop :=
  (∀ k ∈ E.tcbOffs, C.tcbSlotEnd ≤ k ∧ k < 4096 ∧ ¬ C.tcbExcl k) ∧
  (∀ o ∈ E.nodeOffs, o < 4288 ∧ o ≠ 88) ∧ (∀ b, E.obj b → ObjW Sg Scs Z Es b ∧ ¬ C.objExcl b)

theorem ExactW.none_fits (C : FootCfg) : ExactW.none.Fits C Sg Scs Z Es :=
  ⟨fun _ h => by simp [ExactW.none] at h, fun _ h => by simp [ExactW.none] at h, fun _ h => h.elim⟩

/-- **`foot_of_exact`**: an exact write set that fits `C` (threads in `T`, nodes in `Cs`), and `C ≤ C'`, give the
`KWc C'` footprint. -/
theorem foot_of_exact {E : ExactW} {C C' : FootCfg} {Tw Cw : Set U64} {s s' : S}
    (h : WritesIn st s s' (E.W st Tw Cw s)) (hT : Tw ⊆ T) (hC : Cw ⊆ Cs) (hf : E.Fits C Sg Scs Z Es)
    (hle : C.Le C') : WritesIn st s s' (KWc C' st T Cs Sg Scs Z Es s) :=
  WritesIn.mono h fun b hb => KWc.mono hle (by
    rcases hb with ⟨y, hy, K, hk, e⟩ | ⟨c, hc, o, ho, e⟩ | hb
    · obtain ⟨k1, k2, k3⟩ := hf.1 _ hk
      exact Or.inl ⟨y, hT hy, K, k1, k2, k3, e⟩
    · obtain ⟨o1, o2⟩ := hf.2.1 _ ho
      exact Or.inr (Or.inl ⟨c, hC hc, o, o1, o2, e⟩)
    · exact Or.inr (Or.inr (hf.2.2 b hb)))

/-- The footprint with the debug-list words (QueueFinal's `Foot.d` shape) at a configuration. -/
abbrev FootDc (C : FootCfg) (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64)
    (Z : U64 → Nat) (Es : Set U64) (s s' : S) : Prop :=
  WritesIn st s s' (fun b => KWc C st T Cs Sg Scs Z Es s b ∨ DbgW st T Cs s b)

theorem FootDc.mono {C C' : FootCfg} (hle : C.Le C') {s s' : S} (h : FootDc C st T Cs Sg Scs Z Es s s') :
    FootDc C' st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono h fun _ hb => Or.imp (KWc.mono hle) id hb

/-- **A footprint finer than `K8cfg` is a `K8.FootD` footprint**, so the gen 31–33 keep lemmas
(`OSKeep.of_kwd7`, `VKeep.of_kwd8`, `VcTy.of_fin8`) apply to it unchanged. -/
theorem K8.FootD.of_cfg {C : FootCfg} (hle : C.Le K8cfg) {s s' : S} (h : FootDc C st T Cs Sg Scs Z Es s s') :
    K8.FootD st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono h fun _ hb => Or.imp (fun hk => kw8_iff.2 (KWc.mono hle hk)) id hb

theorem K8.FootD.to_cfg {s s' : S} (h : K8.FootD st T Cs Sg Scs Z Es s s') : FootDc K8cfg st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono h fun _ hb => Or.imp kw8_iff.1 id hb

/-- A `K8.FootD` footprint is a `K7cfg` footprint (`K8cfg ≤ K7cfg`). -/
theorem K8.FootD.to7cfg {s s' : S} (h : K8.FootD st T Cs Sg Scs Z Es s s') : FootDc K7cfg st T Cs Sg Scs Z Es s s' :=
  FootDc.mono K8cfg_le_K7cfg (K8.FootD.to_cfg h)

/-- An exact write set fitting `C ≤ K8cfg` gives a `K8.FootD` footprint. -/
theorem K8.FootD.of_exact {E : ExactW} {C : FootCfg} {Tw Cw : Set U64} {s s' : S}
    (h : WritesIn st s s' (E.W st Tw Cw s)) (hT : Tw ⊆ T) (hC : Cw ⊆ Cs) (hf : E.Fits C Sg Scs Z Es)
    (hle : C.Le K8cfg) : K8.FootD st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono (foot_of_exact h hT hC hf hle) fun _ hb => Or.inl (kw8_iff.2 hb)

end

/-! ## The gen-33 finalisers through `foot_of_exact` -/

section fin
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}
variable {Cs Sg Scs : Set U64} {Z : U64 → Nat} {Es : Set U64}

namespace W7
namespace R
namespace ST

/-- **The CNode finaliser's exact write set**: nothing (objects.rs `finalise_cap_object`, CNode arm). -/
theorem fin_cnode.exact {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (p r g b : U64) (fin : Bool) :
    objects.finalise_cap st ar s a (.CNode p r g b) fin false ⦃ x =>
      WritesIn st s x.2.1 (ExactW.none.W st ∅ ∅ s) ⦄ :=
  WP.spec_mono (fin_cnode.z ar s a p r g b fin) fun x hx => by rw [hx.1]; exact WritesIn.refl _ _

/-- **The Zombie finaliser's exact write set**: nothing. -/
theorem fin_zombie.exact {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (p t n : U64) (fin : Bool) :
    objects.finalise_cap st ar s a (.Zombie p t n) fin false ⦃ x =>
      WritesIn st s x.2.1 (ExactW.none.W st ∅ ∅ s) ⦄ := by
  rw [fin_zombie.z, WP.spec_ok]; exact WritesIn.refl _ _

/-- The CNode finaliser's `K8.FootD` footprint, through `foot_of_exact`. -/
theorem fin_cnode.foot8 {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (p r g b : U64) (fin : Bool) :
    objects.finalise_cap st ar s a (.CNode p r g b) fin false ⦃ x =>
      K8.FootD st T Cs Sg Scs Z Es s x.2.1 ⦄ :=
  WP.spec_mono (fin_cnode.exact ar s a p r g b fin) fun _ h =>
    K8.FootD.of_exact h (Set.empty_subset _) (Set.empty_subset _) (ExactW.none_fits K8cfg) (FootCfg.Le.refl _)

/-- The Zombie finaliser's `K8.FootD` footprint, through `foot_of_exact`. -/
theorem fin_zombie.foot8 {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (p t n : U64) (fin : Bool) :
    objects.finalise_cap st ar s a (.Zombie p t n) fin false ⦃ x =>
      K8.FootD st T Cs Sg Scs Z Es s x.2.1 ⦄ :=
  WP.spec_mono (fin_zombie.exact ar s a p t n fin) fun _ h =>
    K8.FootD.of_exact h (Set.empty_subset _) (Set.empty_subset _) (ExactW.none_fits K8cfg) (FootCfg.Le.refl _)

end ST
end R
end W7

end fin

end Fl4ProofsA64.P1

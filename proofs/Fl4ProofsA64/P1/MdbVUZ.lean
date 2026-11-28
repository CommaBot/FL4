/-
P1 (aarch64, gen 58): **`ValidUntypedA` through the `LoopMZ` deletion loops** — gen 57's `LoopMZ.mdbSTR` field with
the free-region fact added (`M := (MdbST ∧ UtRev) ∧ ValidUntypedA Hv`, any heap `Hv`), and gen 41 / 39's deletion
tops with it.

* `ValidUntypedA.oka`: an `OKA` step (every `OS` slot's cap kept or nulled) keeps the fact.
* **`cdt.empty_slot.vuJ`**: `empty_slot` with a `ClOK` cleanup cap under `JV` (MdbLoop's `cdt.empty_slot.mdbS`
  derivation of the post-deletion frame, MdbVU's `cdt.empty_slot.vu`).
* **`LoopMZ.mdbSTV`**: `fin` from `finXQG`'s `OKA` (so `TyK` is a hypothesis, as on the tops), `setz` from
  `obj.Slot.set_cap.vuZ`, `swap` from `cdt.cap_swap_for_delete.vu`, `pre` from `sched.preemption_point.jv`'s
  `OSKeep`, `emp` from `cdt.empty_slot.vuJ`; the `MdbST ∧ UtRev` half is `LoopMZ.mdbSTR`'s.
* Tops: **`cdt.delete.zqIGTmdbSTV`**, **`cdt.delete_deferred.zqGmdbSTV`** (gen 57's `zqIGTmdbSTR` / `zqGmdbSTR`
  with `ValidUntypedA Hv` before and after).

* (gen 61) **One loop field for any cap-map-monotone fact**: `UBm` (MdbVU's cap map) is reflexive and transitive
  (`UBm.refl` / `UBm.trans`, `UB.trans`) and every loop step yields it — `UBm.oka` (`fin`), `obj.Slot.set_cap.ubmZ`
  (`setz`), `cdt.cap_swap_for_delete.ubF` (`swap`, with its cap-slot write frame), `UBm.keepO` (`pre`),
  `cdt.empty_slot.caps` / **`capsJ`** → `ubm` / **`ubmJ`** (`emp`; `empty_slot.vuJ` is now its instance). **`LoopMZ.mdbSTQ`**:
  the `LoopMZ` field for `(MdbST ∧ UtRev) ∧ Q` for every `Q` with `Q s → UBm s s' → Q s'`; `LoopMZ.mdbSTV` is its
  `ValidUntypedA Hv` instance (`ValidUntypedA.oka` its `UBm.oka` instance), MdbUZD uses it at `Q := UBm s`.

No named premise; hypotheses those of gen 57's tops.
-/
import Fl4ProofsA64.P1.MdbVUS
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

theorem UB.trans {a b c : capability.Cap} (h1 : UB a b) (h2 : UB b c) : UB a c := fun p q i e => by
  obtain ⟨i1, e1, l1⟩ := h1 p q i e
  obtain ⟨i0, e0, l0⟩ := h2 p q i1 e1
  exact ⟨i0, e0, le_trans l0 l1⟩

theorem UBm.refl (s : S) : UBm st OS s s := fun y hy => ⟨y, hy, UB.refl _⟩

theorem UBm.trans {s1 s2 s3 : S} (h1 : UBm st OS s1 s2) (h2 : UBm st OS s2 s3) : UBm st OS s1 s3 := fun y hy => by
  obtain ⟨y1, hy1, b1⟩ := h2 y hy
  obtain ⟨y0, hy0, b0⟩ := h1 y1 hy1
  exact ⟨y0, hy0, b1.trans b0⟩

/-- (gen 61) An `OKA` step's cap map (every `OS` slot's cap kept or nulled). -/
theorem UBm.oka {kb : U64} {s s' : S} (k : OKA st OS kb s s') : UBm st OS s s' := fun y hy => ⟨y, hy, by
    rcases k y hy with e | ⟨-, e⟩
    · rw [okinj ((capA_eq s' y).symm.trans (e.trans (capA_eq s y)))]; exact UB.refl _
    · rw [okinj ((capA_eq s' y).symm.trans e)]; exact UB.null _⟩

theorem UBm.keepO {s s' : S} (k : OSKeep st OS s s') : UBm st OS s s' := fun y hy =>
  ⟨y, hy, by rw [k.capA hy]; exact UB.refl _⟩

theorem ValidUntypedA.oka {Hv : Heap} {kb : U64} {s s' : S} (h : ValidUntypedA st Hv OS s)
    (k : OKA st OS kb s s') : ValidUntypedA st Hv OS s' :=
  h.of_ub (fun _ _ e => e) (UBm.oka k)

/-- (gen 61) **A `Zombie` write's cap map.** -/
theorem obj.Slot.set_cap.ubmZ (hO : OSOK T Ω Sg OS) {s : S} {x p t n : U64} (hx : x ∈ OS) (hp : Canon p) :
    obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => UBm st OS s s' ⦄ := by
  rw [set_cap_zombie, WP.spec_ok]
  intro y hy
  refine ⟨y, hy, ?_⟩
  by_cases e : y = x
  · rw [e, capA_wr2_self hO hx (decode_zw p t n hp)]; exact UB.of_not fun _ _ _ e => by cases e
  · rw [capA_wr2_other hO hx hy e]; exact UB.refl _

/-- (gen 61) **`cap_swap_for_delete`'s cap map and cap-slot write frame** (MdbVU's `swap.ubF`). -/
theorem cdt.cap_swap_for_delete.ubF (hO : OSOK T Ω Sg OS) {s : S} (hS : MdbS st OS s) {x1 x2 : U64} (hx1 : x1 ∈ OS)
    (hx2 : x2 ∈ OS) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => WritesIn st s s' (W7.CapW T Ω Sg) ∧ UBm st OS s s' ⦄ := by
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 ⟨WritesIn.refl _ _, UBm.refl _⟩
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    exact cdt.swap.ubF hO hS hx1 hx2 hne hs1 hs2 (CapRt.decodeF_encWf _ _) (CapRt.decodeF_encWf _ _)
      (UB.refl _) (UB.refl _)

section zq
variable {Vc Ub D Fp : Set U64} {Pt : Set U64} {K : capability.Cap → Prop} {Ty : S → Prop}
variable {A : Type _} {ar : machine.Arch A}

/-- (gen 61) **`empty_slot`'s caps**: the slot emptied, the other `OS` slots kept (`cdt.empty_slot.mdbFLG`). -/
theorem cdt.empty_slot.caps (hO : OSOK T Ω Sg OS) {s : S} (hS : MdbS st OS s) {a : A} {x : U64} (hx : x ∈ OS)
    {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => (∀ y ∈ OS, y ≠ x → capA st r.1 y = capA st s y) ∧
      capA st r.1 x = .Null ⦄ := by
  obtain ⟨G, hM, hRO, hK, -, -⟩ := hS
  refine WP.spec_mono (cdt.empty_slot.mdbFLG hO hO.nz hM hRO hK hx hpw hpcd) ?_
  rintro r ⟨⟨G', -, -, -, -, -, hcr, -, hx0, -⟩, -, -⟩
  exact ⟨hcr, hx0⟩

/-- The cap map of a step emptying `x` and keeping the other `OS` slots. -/
theorem UBm.empty {s s' : S} {x : U64} (hcr : ∀ y ∈ OS, y ≠ x → capA st s' y = capA st s y)
    (hx0 : capA st s' x = .Null) : UBm st OS s s' := fun y hy => ⟨y, hy, by
  by_cases e : y = x
  · rw [e, hx0]; exact UB.null _
  · rw [hcr y hy e]; exact UB.refl _⟩

/-- (gen 61) **`empty_slot`'s cap map.** -/
theorem cdt.empty_slot.ubm (hO : OSOK T Ω Sg OS) {s : S} (hS : MdbS st OS s) {a : A} {x : U64} (hx : x ∈ OS)
    {cl : capability.Cap} {Pw : U64 → Prop} (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => UBm st OS s r.1 ⦄ :=
  WP.spec_mono (cdt.empty_slot.caps hO hS hx hpw hpcd) fun _ h => UBm.empty h.1 h.2

/-- (gen 61) **`empty_slot` with a `ClOK` cleanup cap under `JV`: its caps** (gen 58's `empty_slot.vuJ`
derivation of the post-deletion frame, the fact abstracted). -/
theorem cdt.empty_slot.capsJ (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hap : IrqStApart OS (L.ksb s0)) (hm : MdbS st OS s)
    {a : A} {x : U64} (hx : x ∈ OS) {cl : capability.Cap} (hcl : ClOK cl) :
    cdt.empty_slot st ar s a x cl ⦃ r => (∀ y ∈ OS, y ≠ x → capA st r.1 y = capA st s y) ∧
      capA st r.1 x = .Null ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hk : L.ksb s = L.ksb s0 := h.ksb
  rcases hcl with rfl | ⟨irq, rfl, hi⟩
  · refine cdt.empty_slot.caps (Pw := fun _ => False) hO hm hx (fun _ e => e.elim) fun s1 a1 _ => ?_
    rw [pcd_null]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · have hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
        objects.post_cap_deletion st ar s1 a1 (.IrqHandler irq) ⦃ r =>
          WritesIn st s1 r.1 (IrqStW (L.ksb s) irq) ⦄ :=
      fun s1 a1 k1 => WP.spec_mono (pcd_irq.wr hP s1 a1 irq hi) fun r ⟨o, ho, v, e⟩ => by
        rw [e]
        have al := ks_aligned (o := o) q (by omega) (by omega)
        rw [← k1] at al
        exact (writesIn_wr al).mono fun b eb => ⟨o, ho, by rw [eb, k1]⟩
    refine cdt.empty_slot.caps hO hm hx ?_ hpcd
    rintro b ⟨o, ho, eb⟩ ⟨y, hy, h1, h2⟩
    exact hap o (by omega) (by omega) y hy ⟨by rw [← hk, ← eb]; exact h1, by rw [← hk, ← eb]; exact h2⟩

/-- (gen 61) **`empty_slot` with a `ClOK` cleanup cap under `JV`: its cap map.** -/
theorem cdt.empty_slot.ubmJ (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hap : IrqStApart OS (L.ksb s0)) (hm : MdbS st OS s)
    {a : A} {x : U64} (hx : x ∈ OS) {cl : capability.Cap} (hcl : ClOK cl) :
    cdt.empty_slot st ar s a x cl ⦃ r => UBm st OS s r.1 ⦄ :=
  WP.spec_mono (cdt.empty_slot.capsJ hP hO h hap hm hx hcl) fun _ h => UBm.empty h.1 h.2

/-- **`empty_slot` with a `ClOK` cleanup cap under `JV` keeps `ValidUntypedA`** (module docstring). -/
theorem cdt.empty_slot.vuJ {Hv : Heap} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hap : IrqStApart OS (L.ksb s0)) (hm : MdbS st OS s)
    (hv : ValidUntypedA st Hv OS s) {a : A} {x : U64} (hx : x ∈ OS) {cl : capability.Cap} (hcl : ClOK cl) :
    cdt.empty_slot st ar s a x cl ⦃ r => ValidUntypedA st Hv OS r.1 ⦄ :=
  WP.spec_mono (cdt.empty_slot.ubmJ hP hO h hap hm hx hcl) fun _ k => hv.of_ub (fun _ _ e => e) k

/-- (gen 61) **The `LoopMZ` field for `(MdbST ∧ UtRev) ∧ Q`, any `Q` monotone along cap maps** (module
docstring; gen 58's `LoopMZ.mdbSTV` proof, `ValidUntypedA` abstracted). -/
theorem LoopMZ.mdbSTQ {Q : S → Prop} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D) {s0 : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty) (hW : WuApart OS (L.ksb s0))
    (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0)) (hQ : ∀ s s', Q s → UBm st OS s s' → Q s') :
    LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) (XQF st K Vc D Scs Fp Ty (L.ksb s0))
      (fun s x p t => ZrA st OS s x p t ∧ ZrT st s x p t)
      (fun s => (MdbST st OS s ∧ UtRev st OS s) ∧ Q s) where
  fin s a x c f hC m hx hc hX hf := WP.spec_mono (WP.spec_and
    ((LoopMZ.mdbSTR (Fp := Fp) hP hO hA hV hDO hDC hR hK hW hIO hap).fin s a x c f hC m.1 hx hc hX hf)
    (finXQG hP hO hA hV hR hK hTy hC hIO hX.2.2 hX.2.1 hC.ksb hx hc hX.1 a f))
    fun r ⟨⟨m1, z1⟩, ⟨_, _, k, _⟩⟩ => ⟨⟨m1, hQ s r.2.1 m.2 (UBm.oka k)⟩, z1⟩
  zz _ _ _ _ _ hc := ⟨zr_z hc, Or.inr (Or.inr ⟨_, okinj ((capA_eq _ _).symm.trans hc)⟩)⟩
  setz s x p t n hC m hx hp hz := WP.spec_mono (WP.spec_and
    ((LoopMZ.mdbSTR (Fp := Fp) hP hO hA hV hDO hDC hR hK hW hIO hap).setz s x p t n hC m.1 hx hp hz)
    (obj.Slot.set_cap.ubmZ hO hx hp)) fun s' ⟨h1, h2⟩ => ⟨h1, hQ s s' m.2 h2⟩
  swap s p y hC m hp hy hne hz := WP.spec_mono (WP.spec_and
    ((LoopMZ.mdbSTR (Fp := Fp) hP hO hA hV hDO hDC hR hK hW hIO hap).swap s p y hC m.1 hp hy hne hz)
    (cdt.cap_swap_for_delete.ubF hO m.1.1.mdbS (hDO hp) (hDO hy) (hDC p hp) (hDC y hy)))
    fun s' ⟨h1, h2⟩ => ⟨h1, hQ s s' m.2 h2.2⟩
  pre s a hC m := WP.spec_mono (WP.spec_and
    ((LoopMZ.mdbSTR (Fp := Fp) hP hO hA hV hDO hDC hR hK hW hIO hap).pre s a hC m.1)
    (sched.preemption_point.jv hP hO hV hC (by rw [hC.ksb]; exact hW)))
    fun r ⟨h1, ⟨_, k, _⟩⟩ => ⟨h1, hQ s r.2.1 m.2 (UBm.keepO k)⟩
  emp s a x cl hC m hx hcl := WP.spec_mono (WP.spec_and
    ((LoopMZ.mdbSTR (Fp := Fp) hP hO hA hV hDO hDC hR hK hW hIO hap).emp s a x cl hC m.1 hx hcl)
    (cdt.empty_slot.ubmJ hP hO hC hap m.1.1.mdbS hx hcl)) fun r ⟨h1, h2⟩ => ⟨h1, hQ s r.1 m.2 h2⟩

/-- **The `LoopMZ` field for `(MdbST ∧ UtRev) ∧ ValidUntypedA Hv`** (module docstring). -/
theorem LoopMZ.mdbSTV {Hv : Heap} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D) {s0 : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty) (hW : WuApart OS (L.ksb s0))
    (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0)) :
    LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) (XQF st K Vc D Scs Fp Ty (L.ksb s0))
      (fun s x p t => ZrA st OS s x p t ∧ ZrT st s x p t)
      (fun s => (MdbST st OS s ∧ UtRev st OS s) ∧ ValidUntypedA st Hv OS s) :=
  LoopMZ.mdbSTQ hP hO hA hV hDO hDC hR hK hTy hW hIO hap fun _ _ h k => h.of_ub (fun _ _ e => e) k

set_option maxHeartbeats 1000000 in
/-- **`MdbST ∧ UtRev ∧ ValidUntypedA` through gen 41's exposed deletion** (`cdt.delete.zqIGTMZ`). -/
theorem cdt.delete.zqIGTmdbSTV {Hv : Heap} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    (hm : MdbST st OS s ∧ UtRev st OS s) (hv : ValidUntypedA st Hv OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧
      ((MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ∧ ValidUntypedA st Hv OS r.2.1) ⦄ :=
  cdt.delete.zqIGTMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY
    (LoopMZ.mdbSTV hP hO hA hV hDO hDC hR hK hTy hW hIO hap) ⟨hm, hv⟩

set_option maxHeartbeats 1000000 in
/-- **`MdbST ∧ UtRev ∧ ValidUntypedA` through gen 39's deferred deletion** (`cdt.delete_deferred.zqGMZ`). -/
theorem cdt.delete_deferred.zqGmdbSTV {Hv : Heap} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    (hm : MdbST st OS s ∧ UtRev st OS s) (hv : ValidUntypedA st Hv OS s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧
      ((MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ∧ ValidUntypedA st Hv OS r.2.1) ⦄ :=
  cdt.delete_deferred.zqGMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY
    (LoopMZ.mdbSTV hP hO hA hV hDO hDC hR hK hTy hW hIO hap) ⟨hm, hv⟩

end zq

end ST
end R
end W7

end

end Fl4ProofsA64.P1

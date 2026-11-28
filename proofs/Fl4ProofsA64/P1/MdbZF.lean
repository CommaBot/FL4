/-
P1 (aarch64, gen 61): **`ZombiesFinal`** (Architect ruling of gen 61, item 2; l4v Invariants_AI `zombies_final`: a
Zombie cap is final) as a state fact with its boot case and its steps along the deletion loops, and **the finding on
item 1** (Zombie coverage `idx < n` inside `CovBy`).

* **`ZombiesFinal st OS s`**: for every `OS` slot `z` holding `Zombie p _ _`, no other `OS` slot holds a key cap
  (`RngKeyA`: physical, not untyped, not a frame) of base `p` — the form MdbFin's `final_uniq` gives for a final
  `CNode` / `Thread` cap and `ZrA`'s first disjunct carries (hence stronger than "no other cap `same_object_as` the
  Zombie": `same_object_as` with a CNode / TCB / Zombie cap implies the same base, `so_cnode` / `so_thread`).
  x86: P3 `LiveJ` has no such field (its `zslots` / `zdead` read the spec's zombies); the A64 memory-side statement
  is new. FL4: cdt.rs `finalise_slot_*` write a `Zombie` only for a final cap (`is_final_capability_with_cap`) or over
  the same Zombie (`Zr`), objects.rs `finalise_cap_object`.
* Boot **`ZombiesFinal.empty`**. Transfer: **`.recap`** (each `OS` cap kept or nulled: `OKA`, `OSKeep`, `empty_slot`),
  **`.perm`** (caps permuted by an involution of `OS`: `swap`), **`.setZ`** (a `Zombie p _ _` written over a slot with
  `ZrA … p _`: the cap there was final, or already a `Zombie p _ _`).
* Steps: `cdt.cap_swap_for_delete.zf`, `cdt.empty_slot.zfJ`; **`LoopMZ.mdbSTZF`** (the `LoopMZ` field for
  `(MdbST ∧ UtRev) ∧ ZombiesFinal`; `setz` from `ZrA`, gen 57's `LoopMZ.mdbSTR` for the first half); tops
  **`cdt.delete.zqIGTmdbSTZF`**, **`cdt.delete_deferred.zqGmdbSTZF`**.
* **Item 1 as stated breaks an existing statement.** With the Zombie coverage restricted to `idx < n`
  (`ZIdx`) inside `CovBy`, gen 60's `CovBy.ua` (`UA d c → CovBy c y → CovBy d y`, MdbCovC, statement frozen) is false:
  `UA (Zombie p r 0) (CNode p r g b)` (`UA.zombie_cnode`) while the CNode covers its slot 0 and the Zombie covers
  nothing — **`CovBy.ua_zidx_fails`** (same with `UA.zombie`: `Zombie p t 0` vs `Zombie p t 1`, the decrement).
  So the redefinition is not made; see the gen-61 handoff for the plan (a separate coverage predicate).

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbUZD
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

/-- **l4v `zombies_final`, A64 form** (module docstring). -/
def ZombiesFinal (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop :=
  ∀ z ∈ OS, ∀ p t n, capA st s z = .Zombie p t n →
    ∀ y ∈ OS, y ≠ z → RngKeyA (capA st s y) → ptrA (capA st s y) ≠ p

/-- **Boot**: null `OS` slots. -/
theorem ZombiesFinal.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : ZombiesFinal st OS s :=
  fun z hz p t n hc => by rw [h z hz] at hc; cases hc

/-- **Each `OS` cap kept or nulled.** -/
theorem ZombiesFinal.recap {s s' : S} (h : ZombiesFinal st OS s)
    (hc : ∀ y ∈ OS, capA st s' y = capA st s y ∨ capA st s' y = .Null) : ZombiesFinal st OS s' := by
  intro z hz p t n hcz y hy hyz hky
  have ez : capA st s' z = capA st s z := (hc z hz).resolve_right fun e => by rw [e] at hcz; cases hcz
  have ey : capA st s' y = capA st s y := (hc y hy).resolve_right fun e => RngKeyA.not_null (e ▸ hky)
  rw [ez] at hcz
  rw [ey] at hky ⊢
  exact h z hz p t n hcz y hy hyz hky

/-- **Caps permuted by an involution of `OS`.** -/
theorem ZombiesFinal.perm {s s' : S} (h : ZombiesFinal st OS s) (f : U64 → U64) (hf : ∀ y ∈ OS, f y ∈ OS)
    (hff : ∀ y, f (f y) = y) (hc : ∀ y ∈ OS, capA st s' y = capA st s (f y)) : ZombiesFinal st OS s' := by
  intro z hz p t n hcz y hy hyz hky
  rw [hc z hz] at hcz
  rw [hc y hy] at hky ⊢
  exact h (f z) (hf z hz) p t n hcz (f y) (hf y hy) (fun e => hyz (by rw [← hff y, e, hff z])) hky

/-- **A `Zombie p _ _` written over a slot with `ZrA … p _`** (module docstring). -/
theorem ZombiesFinal.setZ (hO : OSOK T Ω Sg OS) {s : S} (h : ZombiesFinal st OS s) {x p t n : U64} (hx : x ∈ OS)
    (hp : Canon p) (hz : ZrA st OS s x p t) :
    obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => ZombiesFinal st OS s' ⦄ := by
  rw [set_cap_zombie, WP.spec_ok]
  have cx := capA_wr2_self (st := st) (s := s) hO hx (decode_zw p t n hp)
  have co : ∀ y ∈ OS, y ≠ x → capA st (L.wr (L.wr s x (zw p t)) (wa x 8#u64) n) y = capA st s y :=
    fun y hy e => capA_wr2_other hO hx hy e
  obtain ⟨hk, hpx, hu⟩ := hz
  have U : ∀ y ∈ OS, y ≠ x → RngKeyA (capA st s y) → ptrA (capA st s y) ≠ p := by
    rcases hu with hu | ⟨n0, e0⟩
    · exact hu
    · exact h x hx p t n0 e0
  intro z hz p' t' n' hcz y hy hyz hky
  by_cases ezx : z = x
  · subst ezx
    rw [cx] at hcz
    injection hcz with e1
    subst e1
    have eyx : y ≠ z := hyz
    rw [co y hy eyx] at hky ⊢
    exact U y hy eyx hky
  · rw [co z hz ezx] at hcz
    by_cases eyx : y = x
    · subst eyx
      rw [cx, ptrA_zombie]
      intro e
      subst e
      exact h z hz _ t' n' hcz y hy hyz hk hpx
    · rw [co y hy eyx] at hky ⊢
      exact h z hz p' t' n' hcz y hy hyz hky

/-! ## Steps -/

/-- **`cap_swap_for_delete`** of two canonical `OS` slots keeps `ZombiesFinal` (the caps exchanged). -/
theorem cdt.cap_swap_for_delete.zf (hO : OSOK T Ω Sg OS) {s : S} (h : ZombiesFinal st OS s) (hS : MdbS st OS s)
    {x1 x2 : U64} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => ZombiesFinal st OS s' ⦄ := by
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    obtain ⟨p1, n1⟩ := hS.lnk hO hx1
    obtain ⟨p2, n2⟩ := hS.lnk hO hx2
    refine WP.spec_mono (cdt.swap.lrW hO (LR.self s) hx1 hx2 hne hs1 hs2 (CapRt.decodeF_encWf _ _)
      (CapRt.decodeF_encWf _ _) p1 n1 p2 n2) ?_
    rintro s' ⟨-, e1, e2, ek⟩
    let f : U64 → U64 := fun y => if y = x1 then x2 else if y = x2 then x1 else y
    have f1 : ∀ y, y = x1 → f y = x2 := fun y a => by simp only [f]; rw [if_pos a]
    have f2 : ∀ y, y ≠ x1 → y = x2 → f y = x1 := fun y a b => by simp only [f]; rw [if_neg a, if_pos b]
    have f3 : ∀ y, y ≠ x1 → y ≠ x2 → f y = y := fun y a b => by simp only [f]; rw [if_neg a, if_neg b]
    have hff : ∀ y, f (f y) = y := fun y => by
      by_cases a : y = x1
      · rw [f1 y a, f2 x2 (Ne.symm hne) rfl, a]
      · by_cases b : y = x2
        · rw [f2 y a b, f1 x1 rfl, b]
        · rw [f3 y a b, f3 y a b]
    refine h.perm f (fun y hy => ?_) hff fun y hy => ?_
    · by_cases a : y = x1
      · rw [f1 y a]; exact hx2
      · by_cases b : y = x2
        · rw [f2 y a b]; exact hx1
        · rw [f3 y a b]; exact hy
    · by_cases a : y = x1
      · rw [f1 y a, a]; exact e1
      · by_cases b : y = x2
        · rw [f2 y a b, b]; exact e2
        · rw [f3 y a b]; exact ek y hy a b

section zq
variable {Vc Ub D Fp : Set U64} {Pt : Set U64} {K : capability.Cap → Prop} {Ty : S → Prop}
variable {A : Type _} {ar : machine.Arch A}

/-- **`empty_slot` with a `ClOK` cleanup cap under `JV` keeps `ZombiesFinal`** (MdbVUZ's `capsJ`). -/
theorem cdt.empty_slot.zfJ (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hap : IrqStApart OS (L.ksb s0)) (hm : MdbS st OS s)
    (hz : ZombiesFinal st OS s) {a : A} {x : U64} (hx : x ∈ OS) {cl : capability.Cap} (hcl : ClOK cl) :
    cdt.empty_slot st ar s a x cl ⦃ r => ZombiesFinal st OS r.1 ⦄ :=
  WP.spec_mono (cdt.empty_slot.capsJ hP hO h hap hm hx hcl) fun _ ⟨hcr, hx0⟩ => hz.recap fun y hy => by
    by_cases e : y = x
    · rw [e]; exact Or.inr hx0
    · exact Or.inl (hcr y hy e)

/-- **The `LoopMZ` field for `(MdbST ∧ UtRev) ∧ ZombiesFinal`** (module docstring). -/
theorem LoopMZ.mdbSTZF (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D) {s0 : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty) (hW : WuApart OS (L.ksb s0))
    (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0)) :
    LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) (XQF st K Vc D Scs Fp Ty (L.ksb s0))
      (fun s x p t => ZrA st OS s x p t ∧ ZrT st s x p t)
      (fun s => (MdbST st OS s ∧ UtRev st OS s) ∧ ZombiesFinal st OS s) where
  fin s a x c f hC m hx hc hX hf := WP.spec_mono (WP.spec_and
    ((LoopMZ.mdbSTR (Fp := Fp) hP hO hA hV hDO hDC hR hK hW hIO hap).fin s a x c f hC m.1 hx hc hX hf)
    (finXQG hP hO hA hV hR hK hTy hC hIO hX.2.2 hX.2.1 hC.ksb hx hc hX.1 a f))
    fun r ⟨⟨m1, z1⟩, ⟨_, _, k, _⟩⟩ => ⟨⟨m1, m.2.recap fun y hy => by
      rcases k y hy with e | ⟨-, e⟩
      · exact Or.inl (okinj ((capA_eq r.2.1 y).symm.trans (e.trans (capA_eq s y))))
      · exact Or.inr (okinj ((capA_eq r.2.1 y).symm.trans e))⟩, z1⟩
  zz _ _ _ _ _ hc := ⟨zr_z hc, Or.inr (Or.inr ⟨_, okinj ((capA_eq _ _).symm.trans hc)⟩)⟩
  setz s x p t n hC m hx hp hz := WP.spec_mono (WP.spec_and
    ((LoopMZ.mdbSTR (Fp := Fp) hP hO hA hV hDO hDC hR hK hW hIO hap).setz s x p t n hC m.1 hx hp hz)
    (ZombiesFinal.setZ hO m.2 hx hp hz.1)) fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩
  swap s p y hC m hp hy hne hz := WP.spec_mono (WP.spec_and
    ((LoopMZ.mdbSTR (Fp := Fp) hP hO hA hV hDO hDC hR hK hW hIO hap).swap s p y hC m.1 hp hy hne hz)
    (cdt.cap_swap_for_delete.zf hO m.2 m.1.1.mdbS (hDO hp) (hDO hy) (hDC p hp) (hDC y hy)))
    fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩
  pre s a hC m := WP.spec_mono (WP.spec_and
    ((LoopMZ.mdbSTR (Fp := Fp) hP hO hA hV hDO hDC hR hK hW hIO hap).pre s a hC m.1)
    (sched.preemption_point.jv hP hO hV hC (by rw [hC.ksb]; exact hW)))
    fun _ ⟨h1, ⟨_, k, _⟩⟩ => ⟨h1, m.2.recap fun y hy => Or.inl (k.capA hy)⟩
  emp s a x cl hC m hx hcl := WP.spec_mono (WP.spec_and
    ((LoopMZ.mdbSTR (Fp := Fp) hP hO hA hV hDO hDC hR hK hW hIO hap).emp s a x cl hC m.1 hx hcl)
    (cdt.empty_slot.zfJ hP hO hC hap m.1.1.mdbS m.2 hx hcl)) fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩

set_option maxHeartbeats 1000000 in
/-- **`MdbST ∧ UtRev ∧ ZombiesFinal` through gen 41's exposed deletion** (`cdt.delete.zqIGTMZ`). -/
theorem cdt.delete.zqIGTmdbSTZF (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    (hm : MdbST st OS s ∧ UtRev st OS s) (hz : ZombiesFinal st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧
      ((MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ∧ ZombiesFinal st OS r.2.1) ⦄ :=
  cdt.delete.zqIGTMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY
    (LoopMZ.mdbSTZF hP hO hA hV hDO hDC hR hK hTy hW hIO hap) ⟨hm, hz⟩

set_option maxHeartbeats 1000000 in
/-- **`MdbST ∧ UtRev ∧ ZombiesFinal` through gen 39's deferred deletion** (`cdt.delete_deferred.zqGMZ`). -/
theorem cdt.delete_deferred.zqGmdbSTZF (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    (hm : MdbST st OS s ∧ UtRev st OS s) (hz : ZombiesFinal st OS s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ ((MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ∧ ZombiesFinal st OS r.2.1) ⦄ :=
  cdt.delete_deferred.zqGMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY
    (LoopMZ.mdbSTZF hP hO hA hV hDO hDC hR hK hTy hW hIO hap) ⟨hm, hz⟩

end zq

/-! ## Item 1: the Zombie coverage inside `CovBy` -/

/-- The ruling's coverage restriction: a `Zombie p _ n` covers only slots below index `n`. -/
def ZIdx (c : capability.Cap) (y : U64) : Prop := ∀ p t n, c = .Zombie p t n → y.val < p.val + 32 * n.val

/-- **`CovBy.ua` fails for `CovBy ∧ ZIdx`** (module docstring): a non-wrapping CNode cap and the count-0 Zombie of
its range are `UA`, the CNode covers its slot 0 under `ZIdx`, the Zombie does not. -/
theorem CovBy.ua_zidx_fails {p r g b : U64} (hreg : baseA (.CNode p r g b) ≤ topA (.CNode p r g b))
    (hr : r.val < 64) (hfit : (slotIdx p 0#u64).val + 32 ≤ 2 ^ 64) :
    UA (.Zombie p r 0#u64) (.CNode p r g b) ∧
      (CovBy (.CNode p r g b) (slotIdx p 0#u64) ∧ ZIdx (.CNode p r g b) (slotIdx p 0#u64)) ∧
      ¬ ZIdx (.Zombie p r 0#u64) (slotIdx p 0#u64) := by
  have hi : (0#u64 : U64).val < 2 ^ (r.val % 64) := by
    have := Nat.two_pow_pos (r.val % 64); simpa using this
  have hc := cn_cov (g := g) (b := b) hreg hr hi hfit
  refine ⟨UA.zombie_cnode p r g b 0#u64 hr, ⟨hc, fun _ _ _ e => by cases e⟩, fun hz => ?_⟩
  have h1 := hz p r 0#u64 rfl
  have h2 := hc.2.2.1
  unfold baseA at h2
  rw [ptrA_cnode] at h2
  simp at h1
  omega

end ST
end R
end W7

end

end Fl4ProofsA64.P1

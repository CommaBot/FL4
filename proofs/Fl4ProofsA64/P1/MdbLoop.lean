/-
P1 (aarch64, gen 49): **the MDB facts as a loop field of the Zombie loops** — `MdbS` (`MdbLk ∧ RngOneA64 ∧ KindA ∧
NullLk ∧ ClsA` over some ghost) through gen 49's `LoopMC` (QueueZombieQ) at `C := JV s0`.

* `MdbS st OS s`, **`MdbS.keep`** (every `OS` slot's four words kept, `OSKeep`).
* Three of `LoopMC`'s five obligations discharged:
  * `pre` — **`sched.preemption_point.mdbS`**: `preemption_point` keeps every `OS` word under `JV`
    (`sched.preemption_point.jv`'s `OSKeep`);
  * `swap` — **`cdt.cap_swap_for_delete.mdbS`**: the second slot holds the `Zombie` (a member), the first is a member
    or null (gen 49's `cdt.cap_swap_for_delete.mdbO`, `NullLk`), both canonical (`DCan D`);
  * `emp` — **`cdt.empty_slot.mdbS`**: a `ClOK` cleanup's `post_cap_deletion` writes nothing (`Null`) or the
    IRQ-state word `ks + 224 + 8·irq` (`pcd_irq.wr`), apart from the `OS` slots by `IrqStApart OS (ks s0)` at the `ks`
    base `JV` keeps (gen 48's table: `ksb = kb`); gen 49's `cdt.empty_slot.mdbF` takes its cleanup hypothesis at
    the `ks` base of the start state.
* **`LoopMC.mdb`**: the field, given the remaining two obligations `fin` (`finalise_cap`) and `setz` (the `Zombie`
  rewrite) as hypotheses `hfin` / `hsetz` — **not discharged here** (still owed: `fin` needs a `delete_one` MDB lemma
  for the IRQ-node slot and the link words under `finalise_cap`; `setz` needs the finality of the rewritten cap at
  the rewrite, which the obligation does not see yet).
* **`cdt.delete.zqIGTmdb`** / **`cdt.delete_deferred.zqGmdb`**: gen 41's exposed deletion and gen 39's deferred
  deletion with `MdbS` from start to end, under `hfin` / `hsetz`.

Named premises: none. `hfin` / `hsetz` are hypotheses of `LoopMC.mdb` and the two corollaries (owed obligations).
-/
import Fl4ProofsA64.P1.MdbMint
import Fl4ProofsA64.P1.QueueZombieQ
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **The MDB field** (module docstring). -/
def MdbS (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop :=
  ∃ G : List (List U64), MdbLk st OS G s ∧ RngOneA64 st G s ∧ KindA st OS s ∧ NullLk st OS s ∧ ClsA st OS s

section gen
variable {OS : Set U64}

/-- **`MdbS` along a step keeping every `OS` slot's words.** -/
theorem MdbS.keep {s s' : S} (h : MdbS st OS s) (k : OSKeep st OS s s') : MdbS st OS s' := by
  obtain ⟨G, hM, hRO, hK, hN, hC⟩ := h
  have cp : ∀ y ∈ OS, capA st s' y = capA st s y := fun y hy => by
    unfold capA; rw [(k y hy).1, (k y hy).2.1]
  have nx : ∀ y ∈ OS, NxA st s' y = NxA st s y := fun y hy => by
    unfold NxA; rw [(k y hy).2.2.2]
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  refine ⟨G, hM.keep (fun y hy => ⟨(k y hy).2.2.1, (k y hy).2.2.2⟩) (fun y hy => by rw [cp y hy]),
    hRO.keep fun y hy => ?_, hK.keep fun y hy => ?_, hN.keep fun y hy hn => ?_, hC.of fun y hy kk => ?_⟩
  · rw [cp y (inOS y hy)]; exact ⟨Iff.rfl, fun _ => rfl⟩
  · rw [cp y hy]; exact ⟨Iff.rfl, fun _ => ⟨rfl, rfl⟩⟩
  · rw [cp y hy] at hn; exact ⟨hn, (k y hy).2.2.1, nx y hy⟩
  · rw [cp y hy] at kk ⊢; exact ⟨y, hy, kk, rfl⟩

end gen

section zq
variable {OS Vc Ub D Fp : Set U64} {Pt : Set U64} {K : capability.Cap → Prop} {Ty : S → Prop}
variable {A : Type _} {ar : machine.Arch A}

/-- **`pre`**: `preemption_point` keeps `MdbS` under `JV` (it keeps every `OS` word). -/
theorem sched.preemption_point.mdbS (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s0 s : S} {a : A} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hW : WuApart OS (L.ksb s))
    (hm : MdbS st OS s) : sched.preemption_point st ar s a ⦃ r => MdbS st OS r.2.1 ⦄ :=
  WP.spec_mono (sched.preemption_point.jv hP hO hV h hW) fun _ ⟨_, k, _⟩ => hm.keep k

/-- **`swap`**: `cap_swap_for_delete` of two canonical domain slots, the second holding a `Zombie`. -/
theorem cdt.cap_swap_for_delete.mdbS (hO : OSOK T Ω Sg OS) (hDO : D ⊆ OS) (hDC : DCan D) {s : S}
    (hm : MdbS st OS s) {p y : U64} (hp : p ∈ D) (hy : y ∈ D)
    (hz : ∃ p' t n, obj.Slot.cap st y s = ok (.Zombie p' t n)) :
    cdt.cap_swap_for_delete st s p y ⦃ s' => MdbS st OS s' ⦄ := by
  obtain ⟨G, hM, hRO, hK, hN, hC⟩ := hm
  obtain ⟨p', t, n, hc⟩ := hz
  have hyc : capA st s y = .Zombie p' t n := okinj ((capA_eq s y).symm.trans hc)
  have hyG : y ∈ G.flatten := (hM.members y).2 ⟨hDO hy, by rw [hyc]; exact fun e => by cases e⟩
  exact WP.spec_mono (cdt.cap_swap_for_delete.mdbO hO hM hRO hK hN hC (hDO hp) hyG (hDC p hp) (hDC y hy))
    fun _ ⟨G', h'⟩ => ⟨G', h'⟩

set_option maxHeartbeats 1000000 in
/-- **`emp`**: `empty_slot` with a `ClOK` cleanup keeps `MdbS` under `JV` and `IrqStApart OS (ks s0)`. -/
theorem cdt.empty_slot.mdbS (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hap : IrqStApart OS (L.ksb s0)) (hm : MdbS st OS s)
    {a : A} {x : U64} (hx : x ∈ OS) {cl : capability.Cap} (hcl : ClOK cl) :
    cdt.empty_slot st ar s a x cl ⦃ r => MdbS st OS r.1 ⦄ := by
  obtain ⟨G, hM, hRO, hK, hN, hC⟩ := hm
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hk : L.ksb s = L.ksb s0 := h.ksb
  rcases hcl with rfl | ⟨irq, rfl, hi⟩
  · refine WP.spec_mono (cdt.empty_slot.mdbO (Pw := fun _ => False) hO hM hRO hK hN hC hx (fun _ e => e.elim)
      fun s1 a1 _ => ?_) fun _ ⟨G', h'⟩ => ⟨G', h'⟩
    rw [pcd_null]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · have hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
        objects.post_cap_deletion st ar s1 a1 (.IrqHandler irq) ⦃ r =>
          WritesIn st s1 r.1 (IrqStW (L.ksb s) irq) ⦄ :=
      fun s1 a1 k1 => WP.spec_mono (pcd_irq.wr hP s1 a1 irq hi) fun r ⟨o, ho, v, e⟩ => by
        rw [e]
        have al := ks_aligned (o := o) q (by omega) (by omega)
        rw [← k1] at al
        exact (writesIn_wr al).mono fun b eb => ⟨o, ho, by rw [eb, k1]⟩
    refine WP.spec_mono (cdt.empty_slot.mdbO hO hM hRO hK hN hC hx ?_ hpcd) fun _ ⟨G', h'⟩ => ⟨G', h'⟩
    rintro b ⟨o, ho, eb⟩ ⟨y, hy, h1, h2⟩
    exact hap o (by omega) (by omega) y hy ⟨by rw [← hk, ← eb]; exact h1, by rw [← hk, ← eb]; exact h2⟩

/-- **The MDB loop field** (module docstring): `pre`, `swap`, `emp` discharged; `fin` and `setz` taken as the
hypotheses `hfin` / `hsetz`. -/
theorem LoopMC.mdb (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS)
    (hDC : DCan D) {s0 : S} (hW : WuApart OS (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    (hfin : ∀ (s : S) (a : A) (x : U64) (c : capability.Cap) (f : Bool),
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s → MdbS st OS s → x ∈ OS → obj.Slot.cap st x s = ok c →
      objects.finalise_cap st ar s a c f false ⦃ r => MdbS st OS r.2.1 ⦄)
    (hsetz : ∀ (s : S) (x p t n : U64), JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s → MdbS st OS s → x ∈ OS →
      obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => MdbS st OS s' ⦄) :
    LoopMC st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) (MdbS st OS) where
  fin := hfin
  setz := hsetz
  swap s p y _ m hp hy _ hz := cdt.cap_swap_for_delete.mdbS hO hDO hDC m hp hy hz
  pre s a h m := sched.preemption_point.mdbS hP hO hV h (by rw [h.ksb]; exact hW) m
  emp s a x cl h m hx hcl := cdt.empty_slot.mdbS hP hO h hap m hx hcl

set_option maxHeartbeats 1000000 in
/-- **`MdbS` through gen 41's exposed deletion** (`cdt.delete.zqIGTMC` at `LoopMC.mdb`), under `hfin` / `hsetz`. -/
theorem cdt.delete.zqIGTmdb (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    (hfin : ∀ (s : S) (a : A) (x : U64) (c : capability.Cap) (f : Bool),
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s → MdbS st OS s → x ∈ OS → obj.Slot.cap st x s = ok c →
      objects.finalise_cap st ar s a c f false ⦃ r => MdbS st OS r.2.1 ⦄)
    (hsetz : ∀ (s : S) (x p t n : U64), JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s → MdbS st OS s → x ∈ OS →
      obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => MdbS st OS s' ⦄)
    (hm : MdbS st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧
      MdbS st OS r.2.1 ⦄ :=
  cdt.delete.zqIGTMC (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY
    (LoopMC.mdb hP hO hV hDO hDC hW hap hfin hsetz) hm

set_option maxHeartbeats 1000000 in
/-- **`MdbS` through gen 39's deferred deletion** (`cdt.delete_deferred.zqGMC` at `LoopMC.mdb`). -/
theorem cdt.delete_deferred.zqGmdb (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    (hfin : ∀ (s : S) (a : A) (x : U64) (c : capability.Cap) (f : Bool),
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s → MdbS st OS s → x ∈ OS → obj.Slot.cap st x s = ok c →
      objects.finalise_cap st ar s a c f false ⦃ r => MdbS st OS r.2.1 ⦄)
    (hsetz : ∀ (s : S) (x p t n : U64), JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s → MdbS st OS s → x ∈ OS →
      obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => MdbS st OS s' ⦄)
    (hm : MdbS st OS s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ MdbS st OS r.2.1 ⦄ :=
  cdt.delete_deferred.zqGMC (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY
    (LoopMC.mdb hP hO hV hDO hDC hW hap hfin hsetz) hm

end zq

end ST
end R
end W7

end

end Fl4ProofsA64.P1

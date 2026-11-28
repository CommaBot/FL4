/-
P1 (aarch64, gen 37): **the Zombie loop with mapped frames and VSpace roots inside covered slots** — the typical
thread (CSpace root CNode, mapped VSpace root, mapped IPC-buffer frame in its TCB slots) — over `JV` and the
VSpace typing `VsTy` (QueueVsTy), extending gen 36's `ZS` loop (QueueZombieS).

* **Frame positions.** `finalise_slot_deferred` swaps the Zombie it made into `Slot(ptr)`, the first slot of the
  object (cdt.rs `cap_swap_for_delete(Slot(ptr), slot)`), so the cap of that slot moves into `slot`; QueueZombieT's
  swap needs both caps non-frame (a frame cap moved into a TCB's buffer slot would retype `RunBuf`). A ghost set
  `Fp ⊆ D` of **frame positions** (state-free): `VsCap` caps (non-device, non-EPT frames, mapped or not;
  `Pml4` / `HighVSpace` roots) may sit only at positions of `Fp`, and every object cap of the domain
  (`CNode p`, `Thread p`, `Zombie p`) has its first slot `p ∉ Fp` (`ObjOut`). A remainder Zombie's pointer is its
  cap's object (`remP`), so the swap's first slot is no frame position and holds a `ZS` cap.
* **`ZP Vc D Scs Fp I Is y c`** = (`ZS` cap ∧ `ObjOut Fp`) ∨ (`y ∈ Fp` ∧ `VsCap`); `DomP`, `XP`.
* **Finalisers.** `finVZ` (every `ZS` cap's finaliser is a `VsZ` step: QueueVsWs's `TW` write sets, the IRQ
  node's `delete_one` by `cdt.delete_one.vz`), `remP`, **`finXP`** (gen 36's `finXS` and, for `VsCap` caps,
  QueueVsPt's `fin_frame.pt` / `fin_root.pt` / `fin_hvs.pt` over `JV.ptw` with the walk facts from `VsTy` at the
  round's state — `VsTy.ptWalk` / `VsTy.ptPool` — and QueueVsTy's zero-write frames for `VsZ`).
* **The loop** (invariant gen 36's `JV ∧ DomS ∧ OKD ∧ idle = I ∧ scA I = Is` with `DomP` for `DomS`, plus
  `VsTy st (ks) Pp Tb Lv`): `cdt.cap_swap_for_delete.zp` (QueueVsWs's `swap.jvo`), `cdt.empty_slot.vz`,
  **`cdt.finalise_slot_deferred.zp`**, **`cdt.delete_deferred.zp`**, **`cdt.finalise_slot_immediate.zp`**,
  **`cdt.delete.zpI`**, **`cdt.delete.zp`**, instances **`cdt.delete.threadP`**, **`cdt.delete.typical`** (a thread
  cap whose CSpace slot holds a CNode, whose VSpace slot holds a VSpace root and whose IPC-buffer slot holds a
  frame, mapped or not).

Case hypotheses (state-free or facts of the start state): `Fp` (with `ObjOut`, `VsCap` at `Fp` inside `DomP`),
`Pp ⊆ Pt`, `Tb ⊆ Pt`, `VrOK … (ks) Pt` (QueueVsWs), `VsTy (ks) Pp Tb Lv s` at the start, and gen 36's. No named
premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueVsWs
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}

namespace W7
namespace R
namespace ST

local notation "wa" => core.num.U64.wrapping_add

section zp
variable {OS Vc Ub D Fp : Set U64} {kb : U64} {Pp Tb Pt : Set U64} {Lv : U64 → Nat}

/-! ## The domain class with frame positions -/

/-- `p` is the object (first slot) of a CNode, thread or Zombie cap. -/
def ObjPtr (c : capability.Cap) (p : U64) : Prop :=
  (∃ r g b, c = .CNode p r g b) ∨ c = .Thread p ∨ (∃ t n, c = .Zombie p t n)

/-- The cap's object is no frame position. -/
def ObjOut (Fp : Set U64) (c : capability.Cap) : Prop := ∀ p, ObjPtr c p → p ∉ Fp

/-- **A VSpace cap of the covered kinds**: a non-device, non-EPT frame (mapped or not), a `Pml4` or `HighVSpace`
root. -/
def VsCap (c : capability.Cap) : Prop :=
  (∃ ptr size rights mapped asid vaddr, c = .Frame ptr size rights false mapped false asid vaddr) ∨
  (∃ p m a, c = .Pml4 p m a) ∨ (∃ p m a, c = .HighVSpace p m a)

/-- **The domain class with frame positions** (module docstring). -/
def ZP (Vc D Scs Fp : Set U64) (I Is y : U64) (c : capability.Cap) : Prop :=
  (ZS Vc D Scs I Is c ∧ ObjOut Fp c) ∨ (y ∈ Fp ∧ VsCap c)

def DomP (st : machine.Store S) [L : LawfulStore st] (Vc D Scs Fp : Set U64) (I Is : U64) (s : S) : Prop :=
  ∀ y ∈ D, ∀ c, obj.Slot.cap st y s = ok c → ZP Vc D Scs Fp I Is y c

def XP (st : machine.Store S) [L : LawfulStore st] (Vc D Scs Fp : Set U64) (I Is : U64) (x : U64) (s : S) : Prop :=
  ∀ c, obj.Slot.cap st x s = ok c → ZP Vc D Scs Fp I Is x c

/-- A Zombie remainder covering slots of `D` whose object is no frame position. -/
def ZRemP (D Fp : Set U64) (rem : capability.Cap) : Prop :=
  rem = .Null ∨ ∃ p t n, rem = .Zombie p t n ∧ Canon p ∧ (∀ i : U64, i.val < n.val → slotIdx p i ∈ D) ∧ p ∉ Fp

theorem objout_z {p t n : U64} (h : p ∉ Fp) : ObjOut Fp (.Zombie p t n) := by
  rintro p' (⟨r, g, b, e⟩ | e | ⟨t', n', e⟩)
  · cases e
  · cases e
  · simp at e; rw [← e.1]; exact h

theorem objout_null : ObjOut Fp .Null := by
  rintro p' (⟨r, g, b, e⟩ | e | ⟨t', n', e⟩) <;> cases e

theorem zp_null {I Is y : U64} : ZP Vc D Scs Fp I Is y .Null := Or.inl ⟨zs_null, objout_null⟩

theorem zp_z {I Is y p t n : U64} (hcov : ∀ i : U64, i.val < n.val → slotIdx p i ∈ D) (h : p ∉ Fp) :
    ZP Vc D Scs Fp I Is y (.Zombie p t n) :=
  Or.inl ⟨Or.inl (Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩))), objout_z h⟩

theorem DomP.oka {I Is kb' : U64} {s s' : S} (h : DomP st Vc D Scs Fp I Is s) (hI : ∀ y ∈ D, ¬ IslN kb' y)
    (hDO : D ⊆ OS) (k : OKA st OS kb' s s') : DomP st Vc D Scs Fp I Is s' := fun y hy c hc => by
  rcases k y (hDO hy) with e | e
  · rw [e] at hc; exact h y hy c hc
  · exact absurd e.1 (hI y hy)

theorem DomP.upd {I Is : U64} {s s' : S} (h : DomP st Vc D Scs Fp I Is s)
    (hk : ∀ y ∈ D, obj.Slot.cap st y s' = obj.Slot.cap st y s ∨
      ∀ c, obj.Slot.cap st y s' = ok c → ZP Vc D Scs Fp I Is y c) :
    DomP st Vc D Scs Fp I Is s' := fun y hy c hc => by
  rcases hk y hy with e | e
  · rw [e] at hc; exact h y hy c hc
  · exact e c hc

theorem XP.oka {I Is kb' x : U64} {s s' : S} (h : XP st Vc D Scs Fp I Is x s) (hx : x ∈ OS)
    (hxI : ¬ IslN kb' x) (k : OKA st OS kb' s s') : XP st Vc D Scs Fp I Is x s' := fun c hc => by
  rcases k x hx with e | e
  · rw [e] at hc; exact h c hc
  · exact absurd e.1 hxI

/-! ## The finalisers -/

variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **`delete_one` of an IRQ-node slot holding a notification or `Null`** is a `VsZ` step. -/
theorem cdt.delete_one.vz (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {isl : U64} (hisl : isl ∈ OS)
    (hN : ∀ c, obj.Slot.cap st isl s = ok c → IrqNt c) :
    cdt.delete_one st ar s a isl ⦃ r => VsZ st kb Pt s r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  unfold cdt.delete_one
  obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st isl s hS)
  rw [hc, bind_ok]
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 (VsZ.refl _)
  refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s isl c hS) fun fin _ => ?_
  have hl : ZL c := by
    rcases hN c hc with ⟨n, b0, b1, b2, rfl⟩ | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨n, b0, b1, b2, rfl⟩))
    · exact zl_null
  have hnI : ∀ i, c ≠ .IrqHandler i := by
    rcases hN c hc with ⟨n, b0, b1, b2, rfl⟩ | rfl <;> intro i e <;> cases e
  rw [← fc_eq_fco ar s a fin hnI]
  refine WP.spec_bind (WP.spec_and (finL hP hO hA hV h hisl hc hl a fin) (finL.tw hP h hisl hc hl a fin)) ?_
  rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨e2, h2, k2⟩, w2⟩
  try simp only at e2 h2 k2 w2
  try dsimp only
  refine WP.spec_mono (cdt.empty_slot.os (P := fun _ => False) hO h2.1.2 hisl fun s1 a1 _ => by
    rw [pcd_null]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)) fun r w3 => ?_
  exact (vsz_tw hR w2).trans (vsz_cw q hR (WritesIn.mono w3 fun b hb => hb.elim id False.elim))

set_option maxHeartbeats 2000000 in
/-- **A final IrqHandler cap's `finalise_cap`** (its node slot a notification or `Null`) is a `VsZ` step. -/
theorem finalise_cap.irq_vz (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {irq kb' : U64} (hIO : irqSlotA kb' irq ∈ OS)
    (hN : ∀ c, obj.Slot.cap st (irqSlotA kb' irq) s = ok c → IrqNt c) (hk : L.ksb s = kb') :
    objects.finalise_cap st ar s a (.IrqHandler irq) true false ⦃ r => VsZ st kb Pt s r.2.1 ⦄ := by
  unfold objects.finalise_cap
  simp only [↓reduceIte]
  unfold interrupt.deleting_irq_handler
  refine WP.spec_bind (Pₘ := fun r : S × A => VsZ st kb Pt s r.1) ?_ ?_
  · refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl e => ?_
    subst e
    rw [hk]
    exact cdt.delete_one.vz hP hO hA hV hR h hIO hN
  · rintro ⟨s2, a2⟩ h2
    first
    | (simp only [objects.finalise_cap_object, ↓reduceIte, WP.spec_ok]; exact h2)
    | (simp only [objects.finalise_cap_object, ↓reduceIte]; exact (WP.spec_ok _).2 h2)
    | (simp [objects.finalise_cap_object, WP.spec_ok]; exact h2)

set_option maxHeartbeats 4000000 in
/-- **Every `ZS` cap's finalisation is a `VsZ` step.** -/
theorem finVZ (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hIO : IrqOK OS D (L.ksb s0)) (hN : IrqN st (L.ksb s0) s) {x : U64} (hx : x ∈ OS) {c : capability.Cap}
    (hc : obj.Slot.cap st x s = ok c) (hX : ZS Vc D Scs (L.idleW s) (L.mem s (scA (L.idleW s))) c) (a : A)
    (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => VsZ st kb Pt s r.2.1 ⦄ := by
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  rcases hX with ((hl | ⟨p, r, g, b, rfl, -⟩ | ⟨p, t, n, rfl, -⟩) | ⟨p, rfl, hid, -⟩ | ⟨v, rfl, hvV⟩) |
    ⟨p, b, rfl, hp, hp0, hpI⟩ | ⟨irq, rfl⟩
  · exact WP.spec_mono (finL.tw hP h hx hc hl a fin) fun r hr => vsz_tw hR hr
  · exact WP.spec_mono (fin_cnode.z ar s a p r g b fin) fun r hr => by rw [hr.1]; exact VsZ.refl _
  · rw [fin_zombie.z]; exact (WP.spec_ok _).2 (VsZ.refl _)
  · have hp : p ∈ T := hty.1.2.2.2.2.2 p rfl
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_thread.tw hP hO hV h.1.1.1 h.2 a p fin hp hid) fun r hr => vsz_tw hR hr
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_vcpu.tw hP hO hV h.1.1.1 h.2 a v fin hvV) fun r hr => vsz_tw hR hr
  · have hk := scpl_of h hc hp hp0 hpI rfl
    exact WP.spec_mono (fin_sc.tw hP h a fin hk hc) fun r hr => vsz_tw hR hr
  · have hi : irq.val < 5376 := hty.1.2.1 irq rfl
    cases fin
    · rw [finalise_cap.nonfin ar s a (irqH_nonfin irq), WP.spec_ok]; exact VsZ.refl _
    · exact finalise_cap.irq_vz hP hO hA hV hR h (hIO.1 irq hi) (hN irq hi) h.ksb

set_option maxHeartbeats 4000000 in
/-- **A remainder Zombie's pointer is the finalised cap's object.** -/
theorem remP (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s0 s : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hIO : IrqOK OS D (L.ksb s0))
    (hN : IrqN st (L.ksb s0) s) {x : U64} (hx : x ∈ OS) {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c)
    (hX : ZS Vc D Scs (L.idleW s) (L.mem s (scA (L.idleW s))) c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => ∀ p t n, r.1.1 = .Zombie p t n → ObjPtr c p ⦄ := by
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  rcases hX with ((hl | ⟨p, r, g, b, rfl, -⟩ | ⟨p, t, n, rfl, -⟩) | ⟨p, rfl, hid, -⟩ | ⟨v, rfl, hvV⟩) |
    ⟨p, b, rfl, hp, hp0, hpI⟩ | ⟨irq, rfl⟩
  · exact WP.spec_mono (finL hP hO hA hV h hx hc hl a fin) fun r hr p t n e => by simp [hr.1] at e
  · refine WP.spec_mono (fin_cnode.z ar s a p r g b fin) fun x' hr p' t n e => ?_
    rcases hr.2.2 with e' | ⟨n', e', -⟩
    · rw [e'] at e; cases e
    · rw [e'] at e; simp at e; rw [← e.1]; exact Or.inl ⟨r, g, b, rfl⟩
  · rw [fin_zombie.z]
    exact (WP.spec_ok _).2 fun p' t' n' e => by simp at e; rw [← e.1]; exact Or.inr (Or.inr ⟨t, n, rfl⟩)
  · rw [fin_cap_eq_obj (by simp)]
    refine WP.spec_mono (fin_thread.rem hP s a p fin) fun r hr p' t n e => ?_
    rw [hr] at e
    cases fin
    · simp at e
    · simp at e; rw [← e.1]; exact Or.inr (Or.inl rfl)
  · exact WP.spec_mono (finJV_vcpu hP hO hV h hc hvV a _ fin hc) fun r hr p t n e => by simp [hr.1] at e
  · have hk := scpl_of h hc hp hp0 hpI rfl
    exact WP.spec_mono (finJV_sc hP hO hA hV h hk a _ fin hc) fun r hr p' t n e => by simp [hr.1] at e
  · have hi : irq.val < 5376 := hty.1.2.1 irq rfl
    cases fin
    · rw [finalise_cap.nonfin ar s a (irqH_nonfin irq), WP.spec_ok]; intro p t n e; cases e
    · exact WP.spec_mono (finalise_cap.irq_finZS hP hO hA hV h hi (hIO.1 irq hi) (hN irq hi) h.ksb)
        fun r hr p t n e => by simp [hr.1] at e

set_option maxHeartbeats 4000000 in
/-- **The finalisation of a `ZP` cap** (at the round's idle word and idle `SC` field, `VsTy` at the round's state):
gen 36's `finXS` facts, a `ZRemP` remainder and a `VsZ` step. -/
theorem finXP (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hIO : IrqOK OS D (L.ksb s0))
    (hN : IrqN st (L.ksb s0) s) (hY : VsTy st kb Pp Tb Lv s) (hk : L.ksb s = kb) {x : U64} (hx : x ∈ OS)
    {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c)
    (hX : ZP Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => ClOK r.1.2 ∧
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ OKA st OS (L.ksb s0) s r.2.1 ∧ ZRemP D Fp r.1.1 ∧
      L.idleW r.2.1 = L.idleW s ∧ L.mem r.2.1 (scA (L.idleW s)) = L.mem s (scA (L.idleW s)) ∧
      VsZ st kb Pt s r.2.1 ⦄ := by
  rcases hX with ⟨hz, hout⟩ | ⟨-, hvs⟩
  · refine WP.spec_mono (WP.spec_and (WP.spec_and (finXS hP hO hA hV h hIO hN hx hc hz a fin)
      (finVZ hP hO hA hV hR h hIO hN hx hc hz a fin)) (remP hP hO hA hV h hIO hN hx hc hz a fin)) ?_
    rintro r ⟨⟨⟨e, h2, k2, z2, i2, j2⟩, v2⟩, p2⟩
    refine ⟨e, h2, k2, ?_, i2, j2, v2⟩
    rcases z2 with e' | ⟨p, t, n, e', hcp, hcov⟩
    · exact Or.inl e'
    · exact Or.inr ⟨p, t, n, e', hcp, hcov, hout p (p2 p t n e')⟩
  · have hiT := h.idleT
    have hPt : PtOK T Ω Sg OS Vc Pt := hR.pt
    rcases hvs with ⟨ptr, size, rights, mapped, asid, vaddr, rfl⟩ | ⟨p, m, ad, rfl⟩ | ⟨p, m, ad, rfl⟩
    · have hpt := hY.ptWalk hTb hk asid vaddr
      rw [fin_cap_eq_obj (by simp)]
      refine WP.spec_mono (WP.spec_and (fin_frame.pt hP s a ptr size rights mapped asid vaddr fin hPt.vs hpt)
        (fin_frame.z hP s a ptr size rights mapped asid vaddr fin hpt)) ?_
      rintro r ⟨⟨e, w⟩, -, z⟩
      obtain ⟨h2, k2, i2, K2⟩ := JV.ptw hO hV hPt h w
      rw [e]
      exact ⟨Or.inl rfl, h2, OKA.of_osk k2, Or.inl rfl, i2, K2 _ hiT, Wr0.vsz hR.al z⟩
    · have hpool := hY.ptPool hPp hk ad
      rw [fin_cap_eq_obj (by simp)]
      refine WP.spec_mono (WP.spec_and (fin_root.pt hP s a p m ad fin hPt.vs hpool)
        (fin_root.z hP s a p m ad fin hpool)) ?_
      rintro r ⟨⟨e, w⟩, -, z⟩
      obtain ⟨h2, k2, i2, K2⟩ := JV.ptw hO hV hPt h w
      rw [e]
      exact ⟨Or.inl rfl, h2, OKA.of_osk k2, Or.inl rfl, i2, K2 _ hiT, Wr0.vsz hR.al z⟩
    · have hpool := hY.ptPool hPp hk ad
      rw [fin_cap_eq_obj (by simp)]
      refine WP.spec_mono (WP.spec_and (fin_hvs.pt hP s a p m ad fin hPt.vs hpool)
        (fin_hvs.z hP s a p m ad fin hpool)) ?_
      rintro r ⟨⟨e, w⟩, -, z⟩
      obtain ⟨h2, k2, i2, K2⟩ := JV.ptw hO hV hPt h w
      rw [e]
      exact ⟨Or.inl rfl, h2, OKA.of_osk k2, Or.inl rfl, i2, K2 _ hiT, Wr0.vsz hR.al z⟩

/-! ## The swap, `empty_slot`, the deferred round -/

set_option maxHeartbeats 4000000 in
/-- **`cap_swap_for_delete` of a slot of `D` outside `Fp` and a slot of `D` holding a `ZS` cap.** -/
theorem cdt.cap_swap_for_delete.zp (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS)
    (hDC : DCan D) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S} {I Is kb' : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hD : DomP st Vc D Scs Fp I Is s) {p y : U64}
    (hp : p ∈ D) (hpF : p ∉ Fp) (hy : y ∈ D)
    (hyc : ∀ c, obj.Slot.cap st y s = ok c → ZS Vc D Scs I Is c ∧ ObjOut Fp c) (hne : p ≠ y) :
    cdt.cap_swap_for_delete st s p y ⦃ s' => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s' ∧
      DomP st Vc D Scs Fp I Is s' ∧ OKD st OS D kb' s s' ∧ L.idleW s' = L.idleW s ∧ ScK st T s s' ∧
      VsZ st kb Pt s s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · rename_i he; exfalso; apply hne; simpa using he
  obtain ⟨c1, hc1⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st p s hS)
  obtain ⟨c2, hc2⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st y s hS)
  rw [hc1, bind_ok, hc2, bind_ok]
  have z1 : ZS Vc D Scs I Is c1 ∧ ObjOut Fp c1 := by
    rcases hD p hp c1 hc1 with h1 | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hpF
  have z2 := hyc c2 hc2
  refine WP.spec_mono (cdt.swap.jvo hO hV h (hDO hp) (hDO hy) hne (hDC p hp) (hDC y hy) hc1 hc2 (zs_nf z1.1)
    (zs_nf z2.1)) ?_
  rintro s' ⟨⟨⟨h', e1, e2, ek⟩, w⟩, o⟩
  refine ⟨h', fun z hz c hc => ?_,
    fun z hz hzD => Or.inl (ek z hz (fun e => hzD (e ▸ hp)) (fun e => hzD (e ▸ hy))), JV.idle_cw h w,
    JV.sik_cw h w, vsz_cw q hR o⟩
  by_cases e1' : z = p
  · subst e1'; rw [e1] at hc; rw [← okinj hc]; exact Or.inl z2
  · by_cases e2' : z = y
    · subst e2'; rw [e2] at hc; rw [← okinj hc]; exact Or.inl z1
    · rw [ek z (hDO hz) e1' e2'] at hc; exact hD z hz c hc

set_option maxHeartbeats 2000000 in
/-- **`empty_slot` of a slot of `OS` with a `ClOK` cleanup is a `VsZ` step.** -/
theorem cdt.empty_slot.vz (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    {s0 s : S} {a : A} {x : U64} {cl : capability.Cap} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hx : x ∈ OS) (hcl : ClOK cl) (hk : L.ksb s = kb) :
    cdt.empty_slot st ar s a x cl ⦃ r => VsZ st kb Pt s r.1 ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  rcases hcl with rfl | ⟨irq, rfl, hi⟩
  · exact WP.spec_mono (cdt.empty_slot.os (P := fun _ => False) hO h.1.2 hx fun s1 a1 _ => by
      rw [pcd_null]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)) fun r hr =>
      vsz_cw q hR (WritesIn.mono hr fun b hb => hb.elim id False.elim)
  · have hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
        objects.post_cap_deletion st ar s1 a1 (.IrqHandler irq) ⦃ r => WritesIn st s1 r.1 (IrqStW kb irq) ⦄ :=
      fun s1 a1 k1 => WP.spec_mono (pcd_irq.wr hP s1 a1 irq hi) fun r ⟨o, ho, v, e⟩ => by
        rw [e]
        have al := ks_aligned (o := o) q (by omega) (by omega)
        rw [← k1] at al
        exact (writesIn_wr al).mono fun b eb => ⟨o, ho, by rw [eb, k1, hk]⟩
    exact WP.spec_mono (cdt.empty_slot.os hO h.1.2 hx hpcd) fun r hr => vsz_irq q hR hi hr

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred` of a slot of a domain of `ZP` caps**: gen 36's facts, `DomP` and `VsTy`. -/
theorem cdt.finalise_slot_deferred.zp (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomP st Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) :
    cdt.finalise_slot_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomP st Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac0, hb0⟩ := h.1.parts
  have q0 := hb0.1.choose_spec.choose_spec
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun z => z.2.2.val)
    (inv := fun z => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 z.1 ∧ DomP st Vc D Scs Fp I Is z.1 ∧
      OKD st OS D (L.ksb s0) s z.1 ∧ L.idleW z.1 = I ∧ L.mem z.1 (scA I) = Is ∧ VsTy st (L.ksb s0) Pp Tb Lv z.1)
  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, o1, i1, j1, y1⟩
    simp only at h1 d1 o1 i1 j1 y1
    dsimp only
    unfold cdt.finalise_slot_deferred_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, y1, by intro v hv; simp_all⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st y s1 hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, y1, fun v hv => by cases hv; exact Or.inl rfl⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 y c hS) fun fin _ => ?_
    have hN1 : IrqN st (L.ksb s0) s1 := hN.okd hIO o1
    refine WP.spec_bind (finXP hP hO hA hV hPp hTb hR h1 hIO hN1 y1 h1.ksb (hDO hy) hc
      (by rw [i1, j1]; exact d1 y hy c hc) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨hcl, h2, k2, hrem, j2, sc2, v2⟩
    simp only at hcl hrem j2 sc2 v2
    have d2 : DomP st Vc D Scs Fp I Is s2 := d1.oka hIO.2 hDO k2
    have o2 : OKD st OS D (L.ksb s0) s s2 := o1.trans k2.okd
    have i2 : L.idleW s2 = I := j2.trans i1
    have js2 : L.mem s2 (scA I) = Is := by rw [i1] at sc2; exact sc2.trans j1
    have y2 : VsTy st (L.ksb s0) Pp Tb Lv s2 := y1.keepZ hPp hTb v2
    rcases hrem with rfl | ⟨p, t, n, rfl, hcp, hcov, hpF⟩
    · try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h2, d2, o2, i2, js2, y2, fun v hv => by cases hv; exact hcl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]
         exact ⟨h2, d2, o2, i2, js2, y2, fun v hv => by cases hv; exact hcl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact ⟨h2, d2, o2, i2, js2, y2, hcl⟩)
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_removable.p0 (.Zombie p t n) y)) fun b1 hb1 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h2, d2, o2, i2, js2, y2, fun v hv => by cases hv; exact hcl⟩
    rename_i hnr
    have hn0 : n ≠ 0#u64 := by
      have hb := hb1.1
      rintro rfl
      simp [cdt.cap_removable] at hb
      simp_all
    have hnp : 0 < n.val := by
      rcases Nat.eq_zero_or_pos n.val with e | e
      · exact absurd (UScalar.eq_of_val_eq (by simpa using e)) hn0
      · exact e
    have hp0 : p ∈ D := by have := hcov 0#u64 (by simpa using hnp); rwa [slotIdx0] at this
    refine WP.spec_bind (WP.spec_and (WP.spec_and (JV.setz hO hV h2 (hDO hy) hcp ⟨hDO hp0, fun i hi => hDO (hcov i hi)⟩)
      (W7.obj.Slot.set_cap.capw (hO.slot _ (hDO hy)))) (W7.obj.Slot.set_cap.capw (osw hO (hDO hy)))) ?_
    rintro s3 ⟨⟨⟨h3, k3, c3⟩, w3⟩, ow3⟩
    have i3 : L.idleW s3 = I := (JV.idle_cw h2 w3).trans i2
    have js3 : L.mem s3 (scA I) = Is := ((JV.sik_cw h2 w3) I (i2 ▸ h2.idleT)).trans js2
    have y3 : VsTy st (L.ksb s0) Pp Tb Lv s3 := y2.keepZ hPp hTb (vsz_cw q0 hR ow3)
    have d3 : DomP st Vc D Scs Fp I Is s3 := DomP.upd d2 fun z hz => by
      by_cases e : z = y
      · right; subst e; intro c' hc'; rw [c3] at hc'; rw [← okinj hc']
        exact zp_z hcov hpF
      · left; exact capk4 k3 (hDO hz) e
    have o3 : OKD st OS D (L.ksb s0) s s3 := o2.trans fun z hz hzD => Or.inl (capk4 k3 hz (fun e => hzD (e ▸ hy)))
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_cyclic_zombie.p0 (.Zombie p (t) n) y)) fun b2 hb2 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h3, d3, o3, i3, js3, y3, fun v hv => by
        cases hv; first | exact Or.inl rfl | exact hcl⟩
    rename_i hcy
    have hpy : p ≠ y := by
      intro e
      have hb := hb2.1
      subst e
      simp [cdt.cap_cyclic_zombie] at hb
      simp_all
    try dsimp only
    try simp only []
    have hyc : ∀ c', obj.Slot.cap st y s3 = ok c' → ZS Vc D Scs I Is c' ∧ ObjOut Fp c' := fun c' hc' => by
      rw [c3] at hc'; rw [← okinj hc']
      exact ⟨Or.inl (Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩))), objout_z hpF⟩
    refine WP.spec_bind (cdt.cap_swap_for_delete.zp (kb' := L.ksb s0) hO hV hDO hDC hR h3 d3 hp0 hpF hy hyc hpy) ?_
    rintro s4 ⟨h4, d4, o4, j4, K4, v4⟩
    refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.preemption_point.jv hP hO hV h4 (by rw [h4.ksb]; exact hW))
      (sched.preemption_point.si hP h4)) (sched.preemption_point.vz hP hR h4 h4.ksb)) ?_
    rintro ⟨rr, s5, a5⟩ ⟨⟨⟨h5, k5, j5⟩, K5⟩, v5⟩
    try simp only [uncurry_apply_pair] at h5 k5 j5 K5 v5 ⊢
    have i5 : L.idleW s5 = I := j5.trans (j4.trans i3)
    have hIT : I ∈ T := i3 ▸ h3.idleT
    have js5 : L.mem s5 (scA I) = Is := (K5 I hIT).trans ((K4 I hIT).trans js3)
    have d5 : DomP st Vc D Scs Fp I Is s5 := DomP.oka d4 hIO.2 hDO (OKA.of_osk k5)
    have o5 : OKD st OS D (L.ksb s0) s s5 := (o3.trans o4).trans (OKA.of_osk k5).okd
    have y5 : VsTy st (L.ksb s0) Pp Tb Lv s5 := (y3.keepZ hPp hTb v4).keepZ hPp hTb v5
    rcases rr with _ | ee
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
      refine (WP.spec_ok _).2 ⟨h5, d5, o5, i5, js5, y5, ?_⟩
      show fuel1.val < fuel.val
      omega
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h5, d5, o5, i5, js5, y5, fun v hv => by cases hv⟩
  · exact ⟨h, hD, OKD.refl s, hI, hIs, hY⟩

set_option maxHeartbeats 4000000 in
/-- **`delete_deferred` of a slot of a domain of `ZP` caps.** -/
theorem cdt.delete_deferred.zp (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomP st Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomP st Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ⦄ := by
  unfold cdt.delete_deferred
  refine WP.spec_bind (cdt.finalise_slot_deferred.zp (a := a) hP hO hA hV hDO hDC hPp hTb hR hW hIO h hy hD hI hIs
    hN hY) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, d1, o1, i1, j1, y1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 d1 o1 i1 j1 y1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    · refine WP.spec_bind (WP.spec_and (cdt.empty_slot.zs (a := a1) hP hO hV h1 (hDO hy) (hv1 v rfl) hap)
        (cdt.empty_slot.vz hP hO hR h1 (hDO hy) (hv1 v rfl) h1.ksb)) ?_
      rintro ⟨s2, a2⟩ ⟨⟨h2, k2, c2, w2, K2⟩, v2⟩
      try simp only [uncurry_apply_pair] at h2 k2 c2 w2 K2 v2 ⊢
      refine (WP.spec_ok _).2 ⟨h2, DomP.upd d1 fun z hz => ?_, o1.trans (OKD.of_ck k2 hy), w2.trans i1,
        (K2 I (i1 ▸ h1.idleT)).trans j1, y1.keepZ hPp hTb v2⟩
      by_cases e : z = y
      · right; subst e; intro c hc; rw [c2] at hc; rw [← okinj hc]; exact zp_null
      · left; exact k2.cap (hDO hz) e
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, y1⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, y1⟩

/-! ## The immediate loop -/

set_option hygiene false in
/-- The preemption-point tail of an immediate round. -/
local macro "ztailP" : tactic => `(tactic| (
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.preemption_point.jv hP hO hV h5 (by rw [h5.ksb]; exact hW))
    (sched.preemption_point.si hP h5)) (sched.preemption_point.vz hP hR h5 h5.ksb)) ?_
  rintro ⟨rr, s6, a6⟩ ⟨⟨⟨h6, k6, i6⟩, K6⟩, v6⟩
  try simp only [uncurry_apply_pair] at h6 k6 i6 K6 v6 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h6, DomP.oka d5 hIO.2 hDO (OKA.of_osk k6), XP.oka x5 hx hxI (OKA.of_osk k6),
      i6.trans j5, (K6 I (j5 ▸ h5.idleT)).trans js5, IrqN.oka hIO N5 (OKA.of_osk k6), y5.keepZ hPp hTb v6, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h6, fun v hv => by cases hv⟩))

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_immediate` of a slot of `OS` whose cap is `ZP` over a domain `D` of `ZP` caps**: `JV` to
`JV`, a `ClOK` cleanup. -/
theorem cdt.finalise_slot_immediate.zp (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomP st Vc D Scs Fp I Is s) (hX : XP st Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : VsTy st (L.ksb s0) Pp Tb Lv s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ ∀ v, r.1 = .Ok v → ClOK v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac0, hb0⟩ := h.1.parts
  have q0 := hb0.1.choose_spec.choose_spec
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧ DomP st Vc D Scs Fp I Is y.1 ∧
      XP st Vc D Scs Fp I Is x y.1 ∧ L.idleW y.1 = I ∧ L.mem y.1 (scA I) = Is ∧ IrqN st (L.ksb s0) y.1 ∧
      VsTy st (L.ksb s0) Pp Tb Lv y.1)
  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, x1, j1, js1, N1, y1⟩
    simp only at h1 d1 x1 j1 js1 N1 y1
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, by intro v hv; simp_all⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s1 hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact Or.inl rfl⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (finXP hP hO hA hV hPp hTb hR h1 hIO N1 y1 h1.ksb hx hc
      (by rw [j1, js1]; exact x1 c hc) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨hcl, h2, k2, hrem, j2', sc2, v2⟩
    simp only at hcl hrem j2' sc2 v2
    have d2 : DomP st Vc D Scs Fp I Is s2 := d1.oka hIO.2 hDO k2
    have j2 : L.idleW s2 = I := j2'.trans j1
    have js2 : L.mem s2 (scA I) = Is := by rw [j1] at sc2; exact sc2.trans js1
    have N2 : IrqN st (L.ksb s0) s2 := N1.oka hIO k2
    have y2 : VsTy st (L.ksb s0) Pp Tb Lv s2 := y1.keepZ hPp hTb v2
    rcases hrem with rfl | ⟨p, t, n, rfl, hcp, hcov, hpF⟩
    · try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; exact hcl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]; exact ⟨h2, fun v hv => by cases hv; exact hcl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact ⟨h2, hcl⟩)
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_removable.p0 (.Zombie p t n) x)) fun b1 hb1 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; exact hcl⟩
    rename_i hnr
    have hn0 : n ≠ 0#u64 := by
      have hb := hb1.1
      rintro rfl
      simp [cdt.cap_removable] at hb
      simp_all
    have hnp : 0 < n.val := by
      rcases Nat.eq_zero_or_pos n.val with e | e
      · exact absurd (UScalar.eq_of_val_eq (by simpa using e)) hn0
      · exact e
    have hp0 : p ∈ D := by have := hcov 0#u64 (by simpa using hnp); rwa [slotIdx0] at this
    refine WP.spec_bind (WP.spec_and (WP.spec_and (JV.setz hO hV h2 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i hi)⟩)
      (W7.obj.Slot.set_cap.capw (hO.slot _ hx))) (W7.obj.Slot.set_cap.capw (osw hO hx))) ?_
    rintro s3 ⟨⟨⟨h3, k3, c3⟩, w3⟩, ow3⟩
    have j3 : L.idleW s3 = I := (JV.idle_cw h2 w3).trans j2
    have hIT : I ∈ T := j2 ▸ h2.idleT
    have js3 : L.mem s3 (scA I) = Is := ((JV.sik_cw h2 w3) I hIT).trans js2
    have N3 : IrqN st (L.ksb s0) s3 := N2.ck hIO hxI fun y hy e => capk4 k3 hy e
    have y3 : VsTy st (L.ksb s0) Pp Tb Lv s3 := y2.keepZ hPp hTb (vsz_cw q0 hR ow3)
    have d3 : DomP st Vc D Scs Fp I Is s3 := DomP.upd d2 fun z hz => by
      by_cases e : z = x
      · right; subst e; intro c' hc'; rw [c3] at hc'; rw [← okinj hc']
        exact zp_z hcov hpF
      · left; exact capk4 k3 (hDO hz) e
    try dsimp only
    first
      | (refine WP.spec_bind (Pₘ := fun i => i = core.num.U64.wrapping_sub n 1#u64) ((WP.spec_ok _).2 rfl)
          fun i hi => ?_; subst hi)
      | simp only [lift, bind_ok]
    refine WP.spec_bind (slot_index_in p _) fun e he => ?_
    subst he
    have heD : slotIdx p (core.num.U64.wrapping_sub n 1#u64) ∈ D := hcov _ (by rw [wsub1 hn0]; omega)
    refine WP.spec_bind (cdt.delete_deferred.zp (a := a2) hP hO hA hV hDO hDC hPp hTb hR hW hIO hap h3 heD d3 j3 js3
      N3 y3) ?_
    rintro ⟨r4, s4, a4⟩ ⟨h4, d4, o4, j4, js4, y4⟩
    try simp only [uncurry_apply_pair] at h4 d4 o4 j4 js4 y4 ⊢
    have N4 : IrqN st (L.ksb s0) s4 := N3.okd hIO o4
    have xo4 : XP st Vc D Scs Fp I Is x s4 := fun c' hc' => by
      by_cases hxD : x ∈ D
      · exact d4 x hxD c' hc'
      · rcases o4 x hx hxD with e | e
        · rw [e, c3] at hc'
          rw [← okinj hc']
          exact zp_z hcov hpF
        · exact absurd e.1 hxI
    rcases r4 with _ | ee
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨c4, hc4⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s4 hS)
      rw [hc4, bind_ok]
      try dsimp only
      refine WP.spec_bind (Pₘ := fun y : S × A => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧
        DomP st Vc D Scs Fp I Is y.1 ∧ XP st Vc D Scs Fp I Is x y.1 ∧ L.idleW y.1 = I ∧ L.mem y.1 (scA I) = Is ∧
        IrqN st (L.ksb s0) y.1 ∧ VsTy st (L.ksb s0) Pp Tb Lv y.1) ?_ ?_
      · split
        all_goals first
          | exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4, y4⟩
          | skip
        split
        · split
          · refine WP.spec_bind (Pₘ := fun s5 => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s5 ∧
              DomP st Vc D Scs Fp I Is s5 ∧ XP st Vc D Scs Fp I Is x s5 ∧ L.idleW s5 = I ∧ L.mem s5 (scA I) = Is ∧
              IrqN st (L.ksb s0) s5 ∧ VsTy st (L.ksb s0) Pp Tb Lv s5) ?_ fun s5 h5 => (WP.spec_ok _).2 h5
            split
            · try simp only [lift, bind_ok]
              refine WP.spec_mono (WP.spec_and (WP.spec_and (JV.setz hO hV h4 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i (by
                rw [wsub1 hn0] at hi; omega))⟩) (W7.obj.Slot.set_cap.capw (hO.slot _ hx)))
                (W7.obj.Slot.set_cap.capw (osw hO hx))) ?_
              rintro s5 ⟨⟨⟨h5, k5, c5⟩, w5⟩, ow5⟩
              refine ⟨h5, DomP.upd d4 fun z hz => ?_, fun c' hc' => ?_, (JV.idle_cw h4 w5).trans j4,
                ((JV.sik_cw h4 w5) I (j4 ▸ h4.idleT)).trans js4, N4.ck hIO hxI fun y hy e => capk4 k5 hy e,
                y4.keepZ hPp hTb (vsz_cw q0 hR ow5)⟩
              · by_cases e : z = x
                · right; subst e; intro c' hc'; rw [c5] at hc'; rw [← okinj hc']
                  exact zp_z (fun i hi => hcov i (by rw [wsub1 hn0] at hi; omega)) hpF
                · left; exact capk4 k5 (hDO hz) e
              · rw [c5] at hc'; rw [← okinj hc']
                exact zp_z (fun i hi => hcov i (by rw [wsub1 hn0] at hi; omega)) hpF
            · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4, y4⟩
          · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4, y4⟩
        · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4, js4, N4, y4⟩
      rintro ⟨s5, a5⟩ ⟨h5, d5, x5, j5, js5, N5, y5⟩
      try simp only [uncurry_apply_pair] at h5 d5 x5 j5 js5 N5 y5 ⊢
      try dsimp only
      ztailP
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h4, fun v hv => by cases hv⟩
  · exact ⟨h, hD, hX, hI, hIs, hN, hY⟩

/-! ## The exposed deletion -/

set_option maxHeartbeats 4000000 in
/-- **The exposed `cdt.delete` of a slot of `OS` whose cap is `ZP` over a domain of `ZP` caps keeps `JV`** (ghost
`I`, `Is`: the start state's idle word and idle `SC` field). -/
theorem cdt.delete.zpI (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomP st Vc D Scs Fp I Is s) (hX : XP st Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : VsTy st (L.ksb s0) Pp Tb Lv s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.zp (a := a) hP hO hA hV hDO hDC hPp hTb hR hW hIO hap h hx hxI
    hD hX hI hIs hN hY) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (cdt.empty_slot.zs hP hO hV h1 hx (hv1 v rfl) hap) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2.1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

/-- **`cdt.delete.zpI` at the start state's idle word and idle `SC` field.** -/
theorem cdt.delete.zp (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomP st Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XP st Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zpI hP hO hA hV hDO hDC hPp hTb hR hW hIO hap h hx hxI hD hX rfl rfl hN hY

/-- **The thread kind over a domain of `ZP` caps**: the exposed `cdt.delete` of `Thread p` (`p` not the idle
thread and no frame position, its seven TCB slots in `D`), the slots of `D` holding gen 36's `ZS` caps whose objects
are no frame positions, or — at frame positions — mapped or unmapped frames and VSpace roots, keeps `JV`. -/
theorem cdt.delete.threadP (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomP st Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zp hP hO hA hV hDO hDC hPp hTb hR hW hIO hap h hx hxI hD (fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']
    refine Or.inl ⟨Or.inl (Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩)), ?_⟩
    rintro p' (⟨r, g, b, e⟩ | e | ⟨t', n', e⟩)
    · cases e
    · cases e; exact hpF
    · cases e) hN hY

/-- **The typical thread.** The exposed `cdt.delete` of a thread cap `Thread p` (not the idle thread) whose TCB
slots lie in `D`, whose CSpace slot (`slotIdx p 0`) holds a CNode cap of a CNode `cn` with its slots in `D`, whose
VSpace slot `vs` holds a VSpace root (`Pml4` or `HighVSpace`, mapped or not) and whose IPC-buffer slot
`sbWordA p` holds a non-device frame (mapped or not), every other slot of `D` holding a `ZS` cap whose object is
no frame position, keeps `JV`. The frame positions are `{vs, sbWordA p}`. -/
theorem cdt.delete.typical (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p cn r g b vs : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hN : IrqN st (L.ksb s0) s) (hY : VsTy st (L.ksb s0) Pp Tb Lv s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D)
    (hp : p ≠ vs ∧ p ≠ sbWordA p) (hcn : cn ≠ vs ∧ cn ≠ sbWordA p)
    (hc0 : obj.Slot.cap st (slotIdx p 0#u64) s = ok (.CNode cn r g b))
    (hcnD : ∀ i : U64, i.val < 2 ^ (r.val % 64) → slotIdx cn i ∈ D)
    (hvs : ∀ c, obj.Slot.cap st vs s = ok c → (∃ q m ad, c = .Pml4 q m ad) ∨ (∃ q m ad, c = .HighVSpace q m ad))
    (hbuf : ∀ c, obj.Slot.cap st (sbWordA p) s = ok c →
      ∃ ptr size rights mapped asid vaddr, c = .Frame ptr size rights false mapped false asid vaddr)
    (hrest : ∀ y ∈ D, y ≠ slotIdx p 0#u64 → y ≠ vs → y ≠ sbWordA p → ∀ c, obj.Slot.cap st y s = ok c →
      ZS Vc D Scs (L.idleW s) (L.mem s (scA (L.idleW s))) c ∧ ObjOut {vs, sbWordA p} c) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ := by
  have hpF : p ∉ ({vs, sbWordA p} : Set U64) := by
    rintro (e | e)
    · exact hp.1 e
    · exact hp.2 e
  refine cdt.delete.threadP (Fp := {vs, sbWordA p}) hP hO hA hV hDO hDC hPp hTb hR hW hIO hap h hx hxI ?_ hN hY
    hc hid hpF hcov
  intro y hy c hcy
  by_cases e0 : y = slotIdx p 0#u64
  · subst e0
    rw [hc0] at hcy; rw [← okinj hcy]
    refine Or.inl ⟨Or.inl (Or.inl (Or.inr (Or.inl ⟨cn, r, g, b, rfl, hcnD⟩))), ?_⟩
    rintro p' (⟨r', g', b', e⟩ | e | ⟨t', n', e⟩)
    · simp at e; rw [← e.1]
      rintro (e' | e')
      · exact hcn.1 e'
      · exact hcn.2 e'
    · cases e
    · cases e
  by_cases e1 : y = vs
  · subst e1
    refine Or.inr ⟨Or.inl rfl, ?_⟩
    rcases hvs c hcy with ⟨q, m, ad, rfl⟩ | ⟨q, m, ad, rfl⟩
    · exact Or.inr (Or.inl ⟨q, m, ad, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, m, ad, rfl⟩)
  by_cases e2 : y = sbWordA p
  · subst e2
    refine Or.inr ⟨Or.inr rfl, ?_⟩
    obtain ⟨ptr, size, rights, mapped, asid, vaddr, rfl⟩ := hbuf c hcy
    exact Or.inl ⟨ptr, size, rights, mapped, asid, vaddr, rfl⟩
  exact Or.inl (hrest y hy e0 e1 e2 c hcy)

end zp

end ST
end R
end W7

end

end Fl4ProofsA64.P1

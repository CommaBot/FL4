/-
# P2: `PathObl`, `PathSide`, `ReadOnce` of the VM-fault local path (line p2e, VM paths)

`vm_pathObl` / `vm_pathSide` / `vm_readOnce`: the per-path obligations of `syscall.handle_vm_fault_local`
(fault address `addr`, code `code`) with the maximal sets `IoRS` / `IoWS` and `DecSet = IoDS`, for
`OwnMap.own K`, the class maps `OwnMap.cls K` / `OwnMap.ko K m0` and user memory `K.user`, under `VmPre`:
`VmFPre` (`P2/AccessVmAcc.lean`), `VmGlue` (`P2/AccessVmDec.lean`) and `RdTab` (`P2/AccessVmTail.lean`).

* `acc`: `vm_acc`; `dec_alt`: `vm_dec_alt`; `read_own` / `write_own` / `aligned`: the sets' definitions and
  `VmBase.dsSafe`; `move`: declined runs by `vm_dec_alt`, accepted runs a premise (`hmv`);
* `PathSide.read_aligned`: an accepting entry by `vm_acc` and `interp_agree`; a declining one by `vm_dec_tr`
  on `IoRS s ∪ VmRep` (all aligned words); `ko_aligned` by `ko_unaligned`;
* `once_of_guard`: a run of a tree on `PathObl.guard st R W` (`R` holding no user word) makes no racy read;
* `vm_readOnce`: from the guarded runs (accepting entry: `vm_acc`, `interp_agree`; declining entry whose
  handler is homed here or not reached: `vm_dec_tr` on `IoRS s`), except a declining entry whose handler is
  homed on another core (`hro`);
* `vm_total`: P0's totality.

Premises:
* `VmPre`'s: `VmFPre`'s (`hyp` [J], `lk` [P], `hEp` / `hRp` [J], `hyt` [J], `VmBase`'s), `VmGlue` [P],
  `RdTab` [J] (`hTab` of `vm_acc`);
* `hK` [J] (`RegionOK`), `hLA` [J] (`IoLayA`);
* `hp` [P] (`IsProg`: the body is the tree `p`), `hz` [P] (`NoZero p`, the same commitment), `hm` [P]
  (writes leave `frame_masks`);
* `hmv` [W]: `move` of accepted runs;
* `hro` [W]: `ReadOnce` at an entry whose handler (the head of the fault endpoint) is homed on another core:
  the declined run reads one word outside `IoRS s`, the handler's home-owned `REPLY_OBJ`, and the extracted
  text (`fastpath_vm::vm_fault`) reads it once; no store instance can count reads (`P2/ReadGap.lean`), so
  this is a fact about `p`, like `IsProg`. A kernel reorder (`schedulable_here` before `reply_obj`) would
  remove it;
* `huf` [J] (`PathSide.user_free`).
-/
import Fl4Proofs.P2.AccessVmDec
import Fl4Proofs.P2.AccessVmTail
import Fl4Proofs.P2.PathAgree
import Fl4Proofs.P2.E2E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-! ## A guarded run makes no racy read -/

section once
open Classical
variable {S A X : Type} {st : machine.Store S} {ar : machine.Arch A} {R W : U64 → Prop}

/-- **A run on `PathObl.guard st R W` reads only `R` words**, so with no user word in `R` it reads no racy word. -/
theorem once_of_guard {User : U64 → Prop} (hU : ∀ q, R q → ¬ User q) (p : SProg X) (hz : NoZero p) :
    ∀ (Wd T : Set U64) (s : S) (a : A) (r : X × S × A), interp (PathObl.guard st R W) ar p s a = ok r →
      Once st ar R User Wd T p s a := by
  induction p with
  | ret x => intro Wd T s a r _; simp only [Once]
  | err e => intro Wd T s a r h; exact absurd h fail_not_ok
  | rd q k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q
    · rw [guard_read hq] at hv
      simp only [Once]
      refine ⟨fun hr => absurd (show ¬ User q ∧ (R q ∨ q ∈ Wd) from ⟨hU q hq, Or.inl hq⟩) hr, fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      exact ih _ (hz _) _ _ s a r hk
    · rw [guard_read_out hq] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R q ∧ R (core.num.U64.wrapping_add q 8#u64)
    · rw [guard_read_pair hq.1 hq.2] at hv
      simp only [Once]
      refine ⟨fun hr => absurd (show ¬ User q ∧ (R q ∨ q ∈ Wd) from ⟨hU q hq.1, Or.inl hq.1⟩) hr,
        fun hr => absurd (show ¬ User (core.num.U64.wrapping_add q 8#u64) ∧
          (R (core.num.U64.wrapping_add q 8#u64) ∨ core.num.U64.wrapping_add q 8#u64 ∈ Wd) from
            ⟨hU _ hq.2, Or.inl hq.2⟩) hr, fun v' hv' => ?_⟩
      rw [hv] at hv'
      have e := ok_inj_ff hv'
      subst e
      exact ih _ (hz _) _ _ s a r hk
    · have : (PathObl.guard st R W).read_pair s q = fail .panic := by
        show (if R q ∧ R (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = _
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | wr q v k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨s', hv, hk⟩ := bok.mp h
    by_cases hq : W q
    · rw [guard_write hq] at hv
      simp only [Once]
      intro s'' hs''
      rw [hv] at hs''
      have e := ok_inj_ff hs''
      subst e
      exact ih hz _ _ _ a r hk
    · rw [guard_write_out hq] at hv; exact absurd hv fail_not_ok
  | zero q n k ih => exact absurd hz id
  | clr q n k ih => exact absurd hz id
  | ksb k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.ks_base s = ok v := hv
    simp only [Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ s a r hk
  | cpu k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.cur_cpu s = ok v := hv
    simp only [Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ s a r hk
  | masks k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.frame_masks s = ok v := hv
    simp only [Once]
    intro v' hv'
    rw [hv2] at hv'
    have e := ok_inj_ff hv'
    subst e
    exact ih _ (hz _) _ _ s a r hk
  | arch op k ih =>
    intro Wd T s a r h
    simp only [interp] at h
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    simp only [Once]
    intro v' a'' hv'
    rw [hv] at hv'
    obtain ⟨e1, e2⟩ := Prod.mk.inj (ok_inj_ff hv')
    subst e1
    subst e2
    exact ih _ (hz _) _ _ s _ r hk

end once

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **The entry facts of the VM-fault local path**: `VmFPre`, the glue's lock (`VmGlue` [P]) and the ASID
words readable (`RdTab` [J], `vm_acc`'s `hTab`). -/
def VmPre (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (K : KLayout)
    (T Cs Ω U : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64)
    (Locks : S → U64 → Prop) (s : S) : Prop :=
  VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s ∧ VmGlue st ar Locks s ∧
    RdTab (L := L) (IoRS (st := st) K Locks s) s

/-- P0's totality of the body. -/
theorem vm_total (hA : P0.ArchTotal ar) (addr code : U64) (s : S) (a : A) :
    ∃ r, syscall.handle_vm_fault_local st ar s a addr code = ok r := by
  obtain ⟨r, e, -⟩ := spec_ex_fd (P0.syscall.handle_vm_fault_local.p0 st ar s a addr code L.total hA)
  exact ⟨r, e⟩

/-- **`PathObl` for the VM-fault local path** (module docstring), `move` of accepted runs a premise. -/
theorem vm_pathObl (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K) {addr code : U64}
    (hmv : ∀ s a s1 a1, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s →
      syscall.handle_vm_fault_local st ar s a addr code = ok (true, s1, a1) →
      syscall.handle_vm_fault_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s a addr code = ok (true, s1, a1)) :
    PathObl st (fun m s a => syscall.handle_vm_fault_local m ar s a addr code) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks
      (VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks)
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact vm_acc hA hE.1 hE.2.2 h
  · intro s a r hE h hn s' r' Al h'
    exact vm_dec_alt hA hK hLA hE.1 hE.2.1 h hn Al h'
  · intro s x _ hx _; exact hx.2.2
  · intro s x hE hx _
    rcases hx with hx | hx
    · exact hx.2
    · rcases hx with rfl | rfl | rfl
      · exact (hE.1.base.reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).2.2
      · exact (hE.1.base.nd (Locks := Locks) _ (by simp [layout.node.CUR_TIME])
          (by simp [layout.node.CUR_TIME])).2.2
      · exact (hE.1.base.nd (Locks := Locks) _ (by simp [layout.node.CONSUMED])
          (by simp [layout.node.CONSUMED])).2.2
  · intro s x hE hx
    rcases hx with hx | hx
    · exact hx.1
    · exact (hE.1.base.dsSafe hx).1
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (vm_dec_alt hA hK hLA hE.1 hE.2.1 h Bool.false_ne_true (Alt.refl s) h).2.2
    · exact hmv s a s1 a1 hE h

/-- **`PathSide` for the VM-fault local path** (module docstring). -/
theorem vm_pathSide (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K) {addr code : U64}
    {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_vm_fault_local m ar x a addr code = interp m ar p x a) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (huf : ∀ s b v, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → b ∈ K.user → Aligned b →
      VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    PathSide st (fun m s a => syscall.handle_vm_fault_local m ar s a addr code)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks (VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks)
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, fun s x _ hx => hx.1, fun x hx => ?_, huf⟩
  · intro s s' a r hE Al h
    obtain ⟨⟨b0, z0, c0⟩, h0⟩ := vm_total (st := st) hA addr code s a
    cases b0
    · have hn := (vm_dec_alt (m0 := m0) hA hK hLA hE.1 hE.2.1 h0 Bool.false_ne_true Al h).1
      have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
      have hg := vm_dec_tr hA hE.1 hE.2.1 G
        (R'' := fun b => IoRS (st := st) K Locks s b ∨ VmRep st ar s a b) (fun b hb => Or.inl hb)
        (fun s1 a1 sl ptr badge x y g gr eu hsl hcap hst hne =>
          Or.inr ⟨s1, a1, sl, ptr, badge, x, y, g, gr, eu, hsl, hcap, hst, hne, rfl⟩) h hn
      show syscall.handle_vm_fault_local _ ar s' a addr code = ok r
      rw [hp] at hg ⊢
      refine interp_mono (fun q hq => ?_) (fun _ _ => trivial) p hz s' a r hg
      rcases hq with hq | hq
      · exact hq.1
      · exact VmRep.aligned hA hE.1 hE.2.1 hq
    · have hacc := vm_acc (Locks := Locks) hA hE.1 hE.2.2 h0
      rw [hp] at hacc
      obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) p hz s s' a true z0 c0
        Al.ksb Al.cpu Al.masks Al.read hacc
      have hs := interp_to (st := st) (st' := st) (fun _ _ _ => rfl)
        (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
        rfl rfl rfl p hz s' a _ hg'
      show syscall.handle_vm_fault_local _ ar s' a addr code = ok r
      rw [hp] at h ⊢
      rw [hs] at h
      rw [← h]
      exact interp_mono (fun _ hw => hw.1) (fun _ _ => trivial) p hz s' a _ hg'
  · by_contra hn
    exact hx (ko_unaligned hK hLA hn)

/-- **`ReadOnce` for the VM-fault local path** (module docstring), the entries with a handler homed on
another core a premise (`hro` [W]). -/
theorem vm_readOnce (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K) {addr code : U64}
    {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_vm_fault_local m ar x a addr code = interp m ar p x a) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hro : ∀ s s' a r, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → (∃ b, VmRep st ar s a b) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar p s' a = ok r → Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)
      (VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks) (IoRS (st := st) K Locks) := by
  intro s s' a r hE Al h
  have hU : ∀ q, IoRS (st := st) K Locks s q → ¬ q ∈ K.user := fun q hq => hq.2.1
  obtain ⟨⟨b0, z0, c0⟩, h0⟩ := vm_total (st := st) hA addr code s a
  cases b0
  · by_cases hrem : ∃ b, VmRep st ar s a b
    · exact hro s s' a r hE hrem Al h
    · have h' : syscall.handle_vm_fault_local st ar s' a addr code = ok r := by rw [hp]; exact h
      have hn := (vm_dec_alt (m0 := m0) hA hK hLA hE.1 hE.2.1 h0 Bool.false_ne_true Al h').1
      have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
      have hg := vm_dec_tr hA hE.1 hE.2.1 G (R'' := IoRS (st := st) K Locks s) (fun b hb => hb)
        (fun s1 a1 sl ptr badge x y g gr eu hsl hcap hst hne =>
          (hrem ⟨_, s1, a1, sl, ptr, badge, x, y, g, gr, eu, hsl, hcap, hst, hne, rfl⟩).elim) h' hn
      rw [hp] at hg
      exact once_of_guard hU p hz ∅ ∅ s' a r hg
  · have hacc := vm_acc (Locks := Locks) hA hE.1 hE.2.2 h0
    rw [hp] at hacc
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) p hz s s' a true z0 c0
      Al.ksb Al.cpu Al.masks Al.read hacc
    exact once_of_guard hU p hz ∅ ∅ s' a _ hg'

end

end Fl4Proofs.P2.PathObl

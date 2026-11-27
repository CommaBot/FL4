/-
P3x for virtualization (line virt, gen 21, item 3a): **the VCPU retype loop with the sharp per-object footprint**,
and with it the whole of `JExtV` after the loop.

Gen 20 found that `JExtV.bnd` for the old TCBs and `JExtV.back` for the old VCPUs do not follow from
`create_new_objects_vcpu`: its frame obligation `hMc` is stated over `CrW` (the window, the head word and *all*
words of `V`'s VCPUs), so its companion invariant cannot carry "the old VCPUs' `TCB` words are kept". But
VirtRetypeLoop's `iter_create` already computes `init`'s precise words (`InitL`, JExtVListSteps): the new object,
the list head word, and only the **old head's `PREV` link** (offset `0x5010`).

* `CrL V B n hd`: the window, the head word, an old VCPU's `PREV` word (`w + 20496`); `CrL.crW` (`CrL ⊆ CrW`).
* **`iter_createL`**, **`create_new_objects_vcpuL`**: VirtRetypeLoop's `iter_create` / `create_new_objects_vcpu`
  re-proved with `hMc` over `CrL` (same proof; the `V`-case of the footprint now lands in the `PREV` clause).
* `MK th' m0 V s`: the old VCPUs' `TCB` words (`vTcbA`, offset 0x5000) and the TCBs' VCPU words (`tVcpuA`, offset
  3664) as in `m0`. `vtcb_off` / `tvcpu_off`: neither is a `CrL` word nor inside a slot (placement).
* **`create_new_objects_vcpu_jext`**: VirtLoopFrame's `create_new_objects_vcpu_loopR` with, in addition, from
  `JExtV V X th' s`: **`JExtV (VsI V B n) X th' res.1`** after the loop — caps by VirtLoopInv0's `loop_vtxCap`,
  `bnd` for every TCB and `back` for the old VCPUs by `MK` (their words are untouched), `back` for the new VCPUs by
  `new_tcb0`, `nz` by `JExtV.nz` / `vI_ne0`. **`create_new_objects_vcpu_jextS`**: the same from the untyped
  invoke's setup facts (`LoopInv.zero`).

State hypotheses (placement / freshness, as `hSW` of `create_new_objects_vcpu_loop`): `hMl` (the MDB links at the
start, for the old chain members), `hTW` (every TCB of `th'` a `TcbAddr`, off the window and the VCPUs of `V`, its
VCPU word not the head word and inside no slot). Named premises: `CapAgree ar a` [P], `VirtCodeAgree ar a` [P]
(unchanged, from `create_new_objects_vcpu`'s per-object step). No new premise. New file only; no existing statement
changed.
-/
import Fl4Proofs.P3.VirtLoopInv0
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtLoopSharp
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtReplyKeep
open Fl4Proofs.P3.VirtRetypeLoop Fl4Proofs.P3.VirtLoopFrame Fl4Proofs.P3.VirtLoopInv0

noncomputable section

/-- `vcpu::init`'s words during a VCPU retype, sharp: the window, the list head word, an old VCPU's `PREV` link. -/
def CrL (V : Set U64) (B n : Nat) (hd : U64) (b : U64) : Prop :=
  (B ≤ b.val ∧ b.val < B + n * 32768) ∨ b = hd ∨ ∃ w ∈ V, b.val = w.val + 20496 ∧ w.val + 32768 ≤ 2 ^ 64

theorem CrL.crW {V : Set U64} {B n : Nat} {hd b : U64} (h : CrL V B n hd b) : CrW V B n hd b := by
  rcases h with h | h | ⟨w, hw, e, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨w, hw, by omega, by omega⟩)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}
variable {V : Set U64} {th : TypedHeap}

set_option maxHeartbeats 8000000 in
/-- **The creation half of one iteration** (module docstring). -/
theorem iter_createL (hA : P0.ArchTotal ar) (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {B n : Nat} {hd k0 : U64}
    (R : RPl st V B n hd) (hhd : ∀ s : S, L.ksb s = k0 → P1.vHeadA st s = hd) (M : S → Nat → Prop)
    (hMc : ∀ s s' i, M s i → P1.WritesIn st s s' (CrL V B n hd) → M s' i)
    {s : S} {i : Nat} (hi : i < n) (I : VirtRetypeLoop.RInv st V th B n k0 M s i) (dev : Bool) :
    objects.create_arch_object st ar s a fl4_abi.consts.object.X86Vcpu (vI B i) dev ⦃ r =>
      r.1 = capability.Cap.Vcpu (vI B i) ∧ r.2.2 = a ∧
        VirtRetypeLoop.RInv st V th B n k0 (fun s' _ => M s' i) r.2.1 (i + 1) ⦄ := by
  have hiN : i ≤ n := Nat.le_of_lt hi
  have ev := R.vIv hi
  have hv := R.vIfit hi
  have hb0 := R.b0
  have hbw := R.hw
  have eh : P1.vHeadA st s = hd := hhd s I.ksb
  have hv0 : vI B i ≠ 0#u64 := fun e => by
    have := congrArg UScalar.val e; rw [ev] at this; simp at this; omega
  have hvV : vI B i ∉ VsI V B i := by
    rintro (h | ⟨j, hj, e⟩)
    · have := R.vw _ h; omega
    · have := congrArg UScalar.val e; rw [ev, R.vIv (by omega)] at this; omega
  have hvI : vI B i ∈ VsI V B (i + 1) := Or.inr ⟨i, by omega, rfl⟩
  have hap : ∀ w ∈ VsI V B i, w.val + 32768 ≤ (vI B i).val ∨ (vI B i).val + 32768 ≤ w.val := by
    intro w hw
    have hw' : w ∈ VsI V B (i + 1) := by rw [← vsI_succ]; exact Set.mem_insert_of_mem _ hw
    have hne : w ≠ vI B i := fun e => hvV (e ▸ hw)
    exact R.apI hi w hw' _ hvI hne
  have hhv : ∀ w, w ∈ insert (vI B i) (VsI V B i) →
      (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val := by
    intro w hw; rw [vsI_succ] at hw; rw [eh]; exact R.hdI hi w hw
  have hin : B + i * 32768 ≤ (vI B i).val ∧ (vI B i).val + 32768 ≤ B + i * 32768 + (n - i) * 32768 := by
    rw [ev]; omega
  have hko : vTcbA (vI B i) ≠ P1.vHeadA st s := by
    intro e; have := congrArg UScalar.val e; rw [lay_vTcb_val hv.2, eh, ev] at this; omega
  refine WP.spec_mono (create_vcpu_listR hA hc hk I.vl (R.fitI hiN) (R.apI hiN) hv hv0 hvV hap hhv I.win hin hko
    dev) ?_
  rintro ⟨cap, s2, a2⟩ ⟨e1, e2, w, Vl', hrel⟩
  simp only at e1 e2 w Vl' hrel ⊢
  refine ⟨e1, e2, ?_⟩
  have hk2 : L.ksb s2 = k0 := w.1.trans I.ksb
  -- `InitL`'s words: in the new object, the head word, or the old head's `PREV` word
  have hIL : ∀ b, InitL st s (vI B i) b → (B + i * 32768 ≤ b.val ∧ b.val < B + (i + 1) * 32768) ∨ b = hd ∨
      ∃ h0 ∈ VsI V B i, b.val = h0.val + 20496 ∧ h0.val + 32768 ≤ 2 ^ 64 := by
    rintro b (h | e | e | ⟨hn, e⟩)
    · have := vwl_val hv h; rw [ev] at this; left; omega
    · have := congrArg UScalar.val e; rw [lay_next_val hv.2, ev] at this; left; omega
    · right; left; rw [e, eh]
    · right; right
      have hw := I.vl.head hn
      have hf := (R.fitI hiN) _ hw
      exact ⟨_, hw, by rw [e, lay_prev_val hf.2], hf.2⟩
  refine ⟨hk2, vsI_succ V B i ▸ Vl', fun j hj => ?_, ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji; exact hrel
    have hj' : j < i := by omega
    have hvj := R.vIfit (j := j) (by omega)
    have evj := R.vIv (j := j) (by omega)
    refine VRelInit.congrAL (fun o h1 h2 h3 h4 => ?_) (I.rel j hj')
    have ho := size_nat h1
    have hl := links_nat ⟨h3, h4⟩
    have hval := vo_val hvj ho
    have hal : P1.Aligned (⟨(vI B j).bv + o⟩ : U64) := by unfold P1.Aligned; rw [hval]; have := hvj.1; omega
    unfold memW
    rw [w.mem_eq hal ?_]
    intro hb
    rcases hIL _ hb with h | e | ⟨h0, hh0, e, -⟩
    · rw [hval, evj] at h; omega
    · have := congrArg UScalar.val e; rw [hval, evj] at this; omega
    · rw [hval, evj] at e
      rcases R.memI hiN hh0 with ⟨-, h'⟩ | ⟨j', hj'', e'⟩
      · omega
      · omega
  · have e1 : n - i = n - (i + 1) + 1 := by omega
    have hw0 := I.win
    rw [e1] at hw0
    have := winZero_shift hw0 rfl fun x hx g1 g2 => w.mem_eq hx fun hb => by
      rcases hIL _ hb with h | e | ⟨h0, hh0, e, -⟩
      · omega
      · rw [e] at g1 g2; omega
      · rcases R.memI hiN hh0 with ⟨-, h'⟩ | ⟨j', hj'', e'⟩
        · have : (n - (i + 1) + 1) * 32768 = (n - i) * 32768 := by rw [← e1]
          omega
        · omega
    rwa [show B + i * 32768 + 32768 = B + (i + 1) * 32768 by ring] at this
  · exact hMc s s2 i I.m (w.mono fun b hb => by
      rcases hIL _ hb with h | e | ⟨h0, hh0, e, hf0⟩
      · left; omega
      · right; left; exact e
      · rcases R.memI hiN hh0 with ⟨hm, -⟩ | ⟨j', hj'', e'⟩
        · right; right; exact ⟨h0, hm, e, hf0⟩
        · left; omega)

set_option maxHeartbeats 8000000 in
/-- **`create_new_objects` over `n` VCPUs** (module docstring). -/
theorem create_new_objects_vcpuL (hA : P0.ArchTotal ar) (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {B n : Nat}
    {hd : U64} (R : RPl st V B n hd) {s : S} (hhd : ∀ s' : S, L.ksb s' = L.ksb s → P1.vHeadA st s' = hd)
    (M : S → Nat → Prop) (hMc : ∀ s s' i, M s i → P1.WritesIn st s s' (CrL V B n hd) → M s' i)
    {FW : U64 → Prop} (hFW : ∀ b, FW b → (b.val + 8 ≤ B ∨ B + n * 32768 ≤ b.val) ∧ b ≠ hd ∧
      ∀ w ∈ V, b.val + 8 ≤ w.val ∨ w.val + 32768 ≤ b.val)
    (parent dest off : U64) (hIns : ∀ iw : U64, iw.val < n → ∀ s2, M s2 iw.val →
      cdt.insert_new_cap st s2 parent (slotAddr dest.bv (core.num.U64.wrapping_add off iw).bv)
        (capability.Cap.Vcpu (vI B iw.val)) ⦃ s3 => M s3 (iw.val + 1) ∧ P1.WritesIn st s2 s3 FW ⦄)
    (Vl : VList st V th s) (hwz : WinZero (L.mem s) B 32768 n False) (hM0 : M s 0)
    (nW base us : U64) (hnW : nW.val = n) (hbase : base.val = B) (dev : Bool) :
    objects.create_new_objects st ar s a fl4_abi.consts.object.X86Vcpu parent dest off nW base us dev ⦃ res =>
      res.2 = a ∧ VList st (VsI V B n) th res.1 ∧ (∀ j, j < n → VRelInit (memW st res.1) (vI B j).bv) ∧
        M res.1 n ⦄ := by
  have hbf := R.bfit
  have I0 : VirtRetypeLoop.RInv st V th B n (L.ksb s) M s 0 := by
    refine ⟨rfl, ?_, fun j hj => absurd hj (Nat.not_lt_zero _), by simpa using hwz, hM0⟩
    have e : VsI V B 0 = V := by
      ext w; simp only [VsI, Set.mem_setOf_eq]
      exact ⟨fun h => h.elim id fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero _), Or.inl⟩
    rw [e]; exact Vl
  unfold objects.create_new_objects
  rw [object_size_vcpu]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have h63 : (15#u64 &&& 63#u64).val = 15 := by decide
  refine loop.spec_decr_nat (measure := fun x => n - x.2.2.val)
    (inv := fun x => x.2.1 = a ∧ x.2.2.val ≤ n ∧ VirtRetypeLoop.RInv st V th B n (L.ksb s) M x.1 x.2.2.val) _ _ _ ?_
    ⟨rfl, by simp, I0⟩
  rintro ⟨s1, a1, i⟩ ⟨ha, hin, I⟩
  simp only at ha hin I ⊢
  subst ha
  unfold objects.create_new_objects_loop.body
  by_cases hit : i < nW
  · rw [if_pos hit]
    have hit' : i.val < n := by rw [← hnW]; exact hit
    simp only [lift, bind_ok]
    obtain ⟨i2, hi2, hv2, -⟩ := spec_exists (UScalar.ShiftLeft_spec i (15#u64 &&& 63#u64) _
      (by rw [h63]; simp [UScalarTy.U64_numBits_eq]) rfl)
    rw [hi2]; simp only [bind_ok]
    have hi2v : i2.val = i.val * 32768 := by
      rw [hv2, h63, Nat.shiftLeft_eq]
      simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
    have hi3 : core.num.U64.wrapping_add base i2 = vI B i.val := by
      have e : (core.num.U64.wrapping_add base i2).val = B + i.val * 32768 := by
        have hlt : B + i.val * 32768 < 2 ^ 64 := lt_of_le_of_lt (by omega) hbf
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v]
        omega
      exact u64_ofNat_eq _ _ e
    rw [hi3, create_object_vcpu]
    refine WP.spec_bind (iter_createL hA hc hk R (fun s' e => hhd s' e) M hMc hit' I dev) fun r hr => ?_
    obtain ⟨cap, s2, a2⟩ := r
    obtain ⟨e1, e2, I'⟩ := hr
    simp only at e1 e2 I' ⊢
    subst e1 e2
    obtain ⟨sl, hsl, hsle⟩ := spec_exists (slot_index_spec dest (core.num.U64.wrapping_add off i))
    rw [hsl]; simp only [bind_ok]
    subst hsle
    refine WP.spec_bind (hIns i hit' s2 I'.m) fun s3 h3 => ?_
    step as ⟨i5, hi5⟩
    have hi5' : i5.val = i.val + 1 := by omega
    refine ⟨by omega, ?_, by omega⟩
    rw [hi5']
    exact iter_ins R (fun s' e => hhd s' e) M hFW hit' I' h3.1 h3.2
  · rw [if_neg hit, WP.spec_ok]
    have : i.val = n := by have : ¬ i.val < nW.val := hit; omega
    rw [this] at I
    exact ⟨rfl, I.vl, I.rel, I.m⟩

end

/-! ## The old objects' binding words -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}
variable {V : Set U64} {th : TypedHeap}

/-- The old VCPUs' `TCB` words and the TCBs' VCPU words as in `m0`. -/
def MK (st : machine.Store S) [L : P1.LawfulStore st] (th' : TypedHeap) (m0 : U64 → U64) (V : Set U64) (s : S) :
    Prop :=
  (∀ v ∈ V, L.mem s (vTcbA v) = m0 (vTcbA v)) ∧ (∀ t, th' t = some .tcb → L.mem s (tVcpuA t) = m0 (tVcpuA t))

/-- An old VCPU's `TCB` word: aligned, not a `CrL` word, inside no slot of `th'`. -/
theorem vtcb_off {B n : Nat} {hd : U64} (R : RPl st V B n hd) {th' : TypedHeap}
    (hSW : ∀ y, IsSlot th' y → (y.val + 32 ≤ B ∨ B + n * 32768 ≤ y.val) ∧
      (hd.val + 8 ≤ y.val ∨ y.val + 32 ≤ hd.val) ∧ ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    {v : U64} (hv : v ∈ V) :
    P1.Aligned (vTcbA v) ∧ ¬ CrL V B n hd (vTcbA v) ∧
      ∀ y, IsSlot th' y → ¬ (y.val ≤ (vTcbA v).val ∧ (vTcbA v).val < y.val + 32) := by
  have hf := R.vf v hv
  have e := lay_vTcb_val hf.2
  refine ⟨by unfold P1.Aligned; rw [e]; omega, ?_, fun y hy h => ?_⟩
  · rintro (⟨h1, h2⟩ | e' | ⟨w, hw, e', -⟩)
    · have := R.vw v hv; omega
    · have := congrArg UScalar.val e'; have := R.hv v hv; omega
    · by_cases hvw : v = w
      · subst hvw; omega
      · have := R.vv v hv w hw hvw; omega
  · have := (hSW y hy).2.2 v hv; omega

/-- A TCB's VCPU word: aligned, not a `CrL` word, inside no slot of `th'` (from `hTW`). -/
theorem tvcpu_off {B n : Nat} {hd : U64} {th' : TypedHeap} {t : U64}
    (ht : P1.TcbAddr t ∧ ((t.val + 4096 ≤ B ∨ B + n * 32768 ≤ t.val) ∧ tVcpuA t ≠ hd ∧
        ∀ w ∈ V, t.val + 4096 ≤ w.val ∨ w.val + 32768 ≤ t.val) ∧
        ∀ y, IsSlot th' y → ¬ (y.val ≤ (tVcpuA t).val ∧ (tVcpuA t).val < y.val + 32)) :
    P1.Aligned (tVcpuA t) ∧ ¬ CrL V B n hd (tVcpuA t) := by
  obtain ⟨hta, ⟨hw, hne, hV⟩, -⟩ := ht
  have e := lay_tVcpu_val hta
  have hal := hta.align
  have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
  rw [h12] at hal
  refine ⟨by unfold P1.Aligned; rw [e]; omega, ?_⟩
  rintro (⟨h1, h2⟩ | e' | ⟨w, hw', e', -⟩)
  · omega
  · exact hne e'
  · have := hV w hw'; omega

set_option maxHeartbeats 8000000 in
/-- **The VCPU retype loop with all of `JExtV` after it** (module docstring). -/
theorem create_new_objects_vcpu_jext {Z : Type} (hA : P0.ArchTotal ar) (hc : CapAgree ar a)
    (hk : VirtCodeAgree ar a)
    {B n : Nat} {hd : U64} (R : RPl st V B n hd) {s : S}
    (hhd : ∀ s' : S, L.ksb s' = L.ksb s → P1.vHeadA st s' = hd)
    (Vl : VList st V th s) (hwz : WinZero (L.mem s) B 32768 n False)
    (th' : TypedHeap) (hP' : Placed th') {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (off nW base us : U64) (hnW : nW.val = n) (hbase : base.val = B) (dev : Bool)
    (hwin : off.val + n ≤ 2 ^ r) (hcan : CanonR B (B + n * 32768))
    (hpA : p.val ≤ B) (hAp : B + n * 32768 ≤ p.val + 2 ^ sb.val)
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (hzW : ∀ b, CrW V B n hd b → ¬ (zlo ≤ b.val ∧ b.val < zhi))
    (hSW : ∀ y, IsSlot th' y → (y.val + 32 ≤ B ∨ B + n * 32768 ≤ y.val) ∧
      (hd.val + 8 ≤ y.val ∨ y.val + 32 ≤ hd.val) ∧ ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    (G0 : MdbGhost)
    (hsrcd : ∀ j, j < n → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 B) n 32768))
      B 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 (L.mem s) (vcj B) s 0)
    {X : Set U64} (E : JExtV (L := L) V X th' s) (hMl : MdbLinks th' (L.mem s) G0)
    (hTW : ∀ t, th' t = some .tcb → P1.TcbAddr t ∧ ((t.val + 4096 ≤ B ∨ B + n * 32768 ≤ t.val) ∧ tVcpuA t ≠ hd ∧
        ∀ w ∈ V, t.val + 4096 ≤ w.val ∨ w.val + 32768 ≤ t.val) ∧
        ∀ y, IsSlot th' y → ¬ (y.val ≤ (tVcpuA t).val ∧ (tVcpuA t).val < y.val + 32)) :
    objects.create_new_objects st ar s a fl4_abi.consts.object.X86Vcpu (cslotAddr (pp.bv, idx)) dest off nW base us
      dev ⦃ res =>
      res.2 = a ∧ VList st (VsI V B n) th res.1 ∧
        LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
          (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
          ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 B) n 32768))
          B 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 (L.mem s) (vcj B) res.1 n ∧
        (∀ j, j < n → ∀ (l : List Fl4Spec.ObjRef) (σ : Fl4Spec.State Z) (x : Unit × Fl4Spec.State Z),
          x ∈ (Fl4Spec.NonDet.mapMx (fun v => Fl4Spec.setVcpu (Z := Z) v (Fl4Spec.initVcpu Fl4Spec.virtKind)) l σ).1 →
          (vI B j).bv ∈ l → VRelAt (memW st res.1) x.2 (vI B j).bv) ∧
        JExtV (L := L) (VsI V B n) X th' res.1 ⦄ := by
  obtain ⟨hMc, hFW, hIns⟩ := mv_obligations (L := L) R th' hP' hpp hidx hsb hpfit σ1 hdest hr off us dev hwin hcan
    hpA hAp zlo zhi hzs hzW hSW G0 (L.mem s) hsrcd
  have hvT := fun v (hv : v ∈ V) => vtcb_off (L := L) R hSW hv
  have htT := fun t (ht : th' t = some .tcb) => tvcpu_off (V := V) (hTW t ht)
  refine WP.spec_mono (create_new_objects_vcpuL hA hc hk R hhd
    (fun s' i => MV (L := L) th' pp idx p sb fi d σ1 us dev dest r off B n zlo zhi G0 (L.mem s) s' i ∧
      MK st th' (L.mem s) V s')
    (fun s1 s2 i h hw => ⟨hMc s1 s2 i h.1 (hw.mono fun b hb => CrL.crW hb),
      fun v hv => (hw.mem_eq (hvT v hv).1 (hvT v hv).2.1).trans (h.2.1 v hv),
      fun t ht => (hw.mem_eq (htT t ht).1 (htT t ht).2).trans (h.2.2 t ht)⟩)
    hFW (cslotAddr (pp.bv, idx)) dest off
    (fun iw hiw s2 h => WP.spec_mono (hIns iw hiw s2 h.1) fun s3 ⟨h1, hw⟩ =>
      ⟨⟨h1, fun v hv => (hw.mem_eq (hvT v hv).1 fun hs => by
          obtain ⟨-, y, hy, g1, g2⟩ := hs
          exact (hvT v hv).2.2 y hy ⟨g1, g2⟩).trans (h.2.1 v hv),
        fun t ht => (hw.mem_eq (htT t ht).1 fun hs => by
          obtain ⟨-, y, hy, g1, g2⟩ := hs
          exact (hTW t ht).2.2 y hy ⟨g1, g2⟩).trans (h.2.2 t ht)⟩, hw⟩)
    Vl hwz ⟨⟨hinv, Nat.zero_le _⟩, fun _ _ => rfl, fun _ _ => rfl⟩ nW base us hnW hbase dev) ?_
  rintro res ⟨h1, h2, h3, ⟨hI, -⟩, hK⟩
  refine ⟨h1, h2, hI, fun j hj l σ x hx hm => retype_vcpu_rel (h3 j hj) l hx hm, ?_⟩
  refine ⟨loop_vtxCap hI (fun x hx => E.cap x ((hMl.members x).1 hx).1), fun t ht => ?_, fun v hv => ?_,
    fun v hv => ?_⟩
  · rw [hK.2 t ht]
    rcases E.bnd t ht with h0 | ⟨hw, hb⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Or.inl hw, by rw [hK.1 _ hw]; exact hb⟩
  · rcases hv with hv | ⟨j, hj, rfl⟩
    · rw [hK.1 v hv]
      rcases E.back v hv with h0 | ⟨ht, hb⟩
      · exact Or.inl h0
      · exact Or.inr ⟨ht, by rw [hK.2 _ ht]; exact hb⟩
    · exact Or.inl (new_tcb0 (h3 j hj))
  · rcases hv with hv | ⟨j, hj, rfl⟩
    · exact E.nz v hv
    · exact vI_ne0 R hj


set_option maxHeartbeats 8000000 in
/-- **`create_new_objects_vcpu_jext` from the untyped invoke's setup facts** (VirtLoopInv0's `LoopInv.zero`; the
start's MDB links give the old chain members). -/
theorem create_new_objects_vcpu_jextS {Z : Type} (hA : P0.ArchTotal ar) (hc : CapAgree ar a)
    (hk : VirtCodeAgree ar a)
    {B n : Nat} {hd : U64} (R : RPl st V B n hd) {s : S}
    (hhd : ∀ s' : S, L.ksb s' = L.ksb s → P1.vHeadA st s' = hd)
    (Vl : VList st V th s) (hwz : WinZero (L.mem s) B 32768 n False)
    (th' : TypedHeap) (hP' : Placed th') {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σb : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (off nW base us : U64) (hnW : nW.val = n) (hbase : base.val = B) (dev : Bool)
    (hwin : off.val + n ≤ 2 ^ r) (hcan : CanonR B (B + n * 32768))
    (hpA : p.val ≤ B) (hAp : B + n * 32768 ≤ p.val + 2 ^ sb.val)
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (hzW : ∀ b, CrW V B n hd b → ¬ (zlo ≤ b.val ∧ b.val < zhi))
    (hSW : ∀ y, IsSlot th' y → (y.val + 32 ≤ B ∨ B + n * 32768 ≤ y.val) ∧
      (hd.val + 8 ≤ y.val ∨ y.val + 32 ≤ hd.val) ∧ ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    (G : MdbGhost)
    (hsrcd : ∀ j, j < n → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (hR : StateRel th' (L.mem s) σb) (hV : SlotsValid th' (L.mem s)) (hM : MdbLinks th' (L.mem s) G)
    (hC : CdtRel th' (L.mem s) σb G) (hI : MdbInv (L.mem s) G)
    (hsrc : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi d))
    (hdst : ∀ j, 0 ≤ j → j < n → capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) = ok .Null)
    (hph : ∀ x ∈ G.chains.flatten, physF (capV (L.mem s) x) = true →
      baseF (capV (L.mem s) x) ≤ topF (capV (L.mem s) x) ∧
      (DisjR (capV (L.mem s) x) (B + 0 * 32768) (B + n * 32768) ∨
        (isUt (capV (L.mem s) x) = true ∧ Within (.Untyped p sb fi d) (capV (L.mem s) x))))
    (hds : ∀ y, Mdb.Desc G.par y (cslotAddr (pp.bv, idx)) →
      DisjR (capV (L.mem s) y) (B + 0 * 32768) (B + n * 32768))
    (hz : ZeroRegion (L.mem s) zlo zhi)
    {X : Set U64} (E : JExtV (L := L) V X th' s)
    (hTW : ∀ t, th' t = some .tcb → P1.TcbAddr t ∧ ((t.val + 4096 ≤ B ∨ B + n * 32768 ≤ t.val) ∧ tVcpuA t ≠ hd ∧
        ∀ w ∈ V, t.val + 4096 ≤ w.val ∨ w.val + 32768 ≤ t.val) ∧
        ∀ y, IsSlot th' y → ¬ (y.val ≤ (tVcpuA t).val ∧ (tVcpuA t).val < y.val + 32)) :
    objects.create_new_objects st ar s a fl4_abi.consts.object.X86Vcpu (cslotAddr (pp.bv, idx)) dest off nW base us
      dev ⦃ res =>
      res.2 = a ∧ VList st (VsI V B n) th res.1 ∧
        LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σb
          (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
          ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 B) n 32768))
          B 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G (L.mem s) (vcj B) res.1 n ∧
        (∀ j, j < n → ∀ (l : List Fl4Spec.ObjRef) (σ : Fl4Spec.State Z) (x : Unit × Fl4Spec.State Z),
          x ∈ (Fl4Spec.NonDet.mapMx (fun v => Fl4Spec.setVcpu (Z := Z) v (Fl4Spec.initVcpu Fl4Spec.virtKind)) l σ).1 →
          (vI B j).bv ∈ l → VRelAt (memW st res.1) x.2 (vI B j).bv) ∧
        JExtV (L := L) (VsI V B n) X th' res.1 ⦄ :=
  create_new_objects_vcpu_jext (Z := Z) hA hc hk R hhd Vl hwz th' hP' hpp hidx hsb hpfit σb hdest hr off nW base us
    hnW hbase dev hwin hcan hpA hAp zlo zhi hzs hzW hSW G hsrcd
    (LoopInv.zero (vcj B) hR hV hM hC hI hsrc hdst hph hds hz) E hM hTW

end

end
end Fl4Proofs.P3.VirtLoopSharp

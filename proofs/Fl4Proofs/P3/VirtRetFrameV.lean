/-
P3x for virtualization (line virt, gen 25, item 1, FL4 half): **the write frame of a VCPU retype** — FL4's
`untyped::retype` (reset = false) for type 14 writes only `vcpu::init`'s words (the window, the list head word, the
old head's `PREV` link: VirtLoopSharp's `CrL`) and slot words, so every VCPU present before keeps all its aligned
words but the links (`AgreeAtAL`), hence its `VRelAt` (the relation reads no link word, VirtRetypeLoop's
`VcpuRelVmx.congrAL` / `VcpuRelSvm.congrAL`).

FL4 source: `crates/fl4-core/src/untyped.rs` `retype` (cap update, then `objects::create_new_objects`,
VirtRetVcpuPre's `retype_noreset_eq14`); `objects.rs` `create_new_objects` (per object `create_object` =
`vcpu::init`, then `cdt::insert_new_cap` after the untyped's slot); `cdt.rs` l. 28-46 (`insert_new_cap` writes the
new slot, the parent's `next` and the old next's `prev`: all slot words when the parent's next is null or a slot,
which it is at the start (`MdbLinks.next_mem`) and after every insertion (ScUtRetypeDev's `insert_new_next`)).

* `RetW V th B n hd` = `CrL V B n hd ∪ SlotW th`; `crl_not_slot` (a word inside a slot is no `CrL` word).
* **`create_vcpu_frame`**: VirtLoopSharp's `create_new_objects_vcpuL` with the companion invariant "writes so far
  in `RetW`, the parent's next null or a slot" (obligations: `CrL` writes miss the parent's `next` word;
  `insert_new_cap` by UntypedInsert's `insert_new_frame` + `insert_new_next`, footprint `SlotW th`), as
  ScUtRetypeDev's `create_dev_frame` for device untypeds.
* **`retype_vcpu_frame`**: the whole `untyped.retype … false … 14 …` writes in `RetW` (the cap update by
  UntypedFrameBase's `set_cap_frame`, `VList` and the zero window carried across it).
* `agreeAL_of_off`, **`agreeAL_of_retW`**: writes in `RetW` keep `AgreeAtAL` at every VCPU of `V`;
  `vrelAt_frameAL` (VRelAt across `AgreeAtAL` with the spec VCPU kept).

State hypotheses (placement, as `create_new_objects_vcpu_jext`'s): `RPl` (window aligned, fitting, apart from `V`
and the head word; `V`'s VCPUs aligned, apart), `hSW` (every slot apart from the window, the head word and `V`),
the source slot's next null or a slot, `VList V`, the window zero. Named premises: `CapAgree ar a` [P],
`VirtCodeAgree ar a` [P] (unchanged, from `create_new_objects_vcpuL`'s per-object step). No new premise. New file
only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtRetFullV
import Fl4Proofs.P3.ScUtRetypeDev
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtRetFrameV
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtRetypeLoop
open Fl4Proofs.P3.VirtLoopFrame Fl4Proofs.P3.VirtLoopSharp Fl4Proofs.P3.VirtRetVcpuPre Fl4Proofs.P3.VirtReplyKeep
open Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel

noncomputable section

/-- The words a VCPU retype of `n` objects at `B` writes: `vcpu::init`'s (`CrL`) and slot words. -/
abbrev RetW (V : Set U64) (th : TypedHeap) (B n : Nat) (hd : U64) (b : U64) : Prop := CrL V B n hd b ∨ SlotW th b

/-- A word inside a slot (apart from the window, the head word and `V`) is no `CrL` word. -/
theorem crl_not_slot {V : Set U64} {th : TypedHeap} {B n : Nat} {hd : U64}
    (hSW : ∀ y, IsSlot th y → (y.val + 32 ≤ B ∨ B + n * 32768 ≤ y.val) ∧
      (hd.val + 8 ≤ y.val ∨ y.val + 32 ≤ hd.val) ∧ ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    {y : U64} (hy : IsSlot th y) {b : U64} (h1 : y.val ≤ b.val) (h2 : b.val < y.val + 32) : ¬ CrL V B n hd b := by
  obtain ⟨g1, g2, g3⟩ := hSW y hy
  rintro (⟨c1, c2⟩ | rfl | ⟨w, hw, e, -⟩)
  · omega
  · omega
  · have := g3 w hw; omega

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}
variable {V : Set U64} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **`create_new_objects` over `n` VCPUs writes in `RetW`** (module docstring). -/
theorem create_vcpu_frame (hA : P0.ArchTotal ar) (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {B n : Nat}
    {hd : U64} (R : RPl st V B n hd) {s : S} (hhd : ∀ s' : S, L.ksb s' = L.ksb s → P1.vHeadA st s' = hd)
    (hP : Placed th)
    (hSW : ∀ y, IsSlot th y → (y.val + 32 ≤ B ∨ B + n * 32768 ≤ y.val) ∧
      (hd.val + 8 ≤ y.val ∨ y.val + 32 ≤ hd.val) ∧ ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    {src : U64} (hs : IsSlot th src) (hnx : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src))
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r)) (hr : r ≤ 64) (off : U64) (hwin : off.val + n ≤ 2 ^ r)
    (Vl : VList st V th s) (hwz : WinZero (L.mem s) B 32768 n False)
    (nW base us : U64) (hnW : nW.val = n) (hbase : base.val = B) (dev : Bool) :
    objects.create_new_objects st ar s a fl4_abi.consts.object.X86Vcpu src dest off nW base us dev ⦃ res =>
      res.2 = a ∧ P1.WritesIn st s res.1 (RetW V th B n hd) ⦄ := by
  have hrr : 2 ^ r ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hr
  have e24 : (wordOf src 24#u64).val = src.val + 24 := by rw [slot_word_val hP hs off24]; rfl
  have ha24 := slot_word_aligned hP hs off24
  have hn24 : ¬ CrL V B n hd (wordOf src 24#u64) := crl_not_slot hSW hs (by omega) (by omega)
  refine WP.spec_mono (create_new_objects_vcpuL hA hc hk R hhd
    (fun s' _ => P1.WritesIn st s s' (RetW V th B n hd) ∧
      (nextOf (L.mem s') src = 0#u64 ∨ IsSlot th (nextOf (L.mem s') src)))
    (fun s1 s2 i h hw => ⟨(h.1.trans hw).mono fun b hb => hb.elim id Or.inl, by
        have e : nextOf (L.mem s2) src = nextOf (L.mem s1) src := by unfold nextOf; rw [hw.mem_eq ha24 hn24]
        rw [e]; exact h.2⟩)
    (FW := SlotW th) ?_ src dest off ?_ Vl hwz ⟨P1.WritesIn.refl s _, hnx⟩ nW base us hnW hbase dev) ?_
  · rintro b ⟨hal, y, hy, h1, h2⟩
    have hya := hy.align hP
    unfold P1.Aligned at hal
    obtain ⟨g1, g2, g3⟩ := hSW y hy
    exact ⟨by omega, fun e => by subst e; omega, fun w hw => by have := g3 w hw; omega⟩
  · rintro iw hiw s2 ⟨hW2, hx⟩
    have hi4 : (core.num.U64.wrapping_add off iw).bv = BitVec.ofNat 64 (off.val + iw.val) := by
      rw [bv_eq_ofNat]; congr 1
      have : off.val + iw.val < 2 ^ 64 := by omega
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
    rw [hi4]
    have hds : IsSlot th (slotAddr dest.bv (BitVec.ofNat 64 (off.val + iw.val))) :=
      ⟨dest, off.val + iw.val, Or.inl ⟨r, hdest, by omega⟩, rfl⟩
    refine WP.spec_mono (WP.spec_and (insert_new_frame hP s2 _ _ _ hs hds hx)
      (WP.spec_and (insert_new_cap_kc s2 _ _ _) (Sched.insert_new_next hP s2 _ _ _ hs hds))) ?_
    rintro s3 ⟨hfr, hk3, hn3⟩
    have hsl : ∀ a', (a' = src ∨ a' = slotAddr dest.bv (BitVec.ofNat 64 (off.val + iw.val)) ∨
        (nextOf (L.mem s2) src ≠ 0#u64 ∧ a' = nextOf (L.mem s2) src)) → IsSlot th a' := by
      rintro a' (e | e | ⟨h0, e⟩) <;> rw [e]
      · exact hs
      · exact hds
      · exact hx.resolve_left h0
    have hW3 : P1.WritesIn st s2 s3 (SlotW th) :=
      ⟨hk3.1, hk3.2, fun w hw hnp => hfr w hw (fun a' ha hin => hnp ⟨hw, a', hsl a' ha, hin.1, hin.2⟩)⟩
    exact ⟨⟨(hW2.trans hW3).mono fun b hb => hb.elim id Or.inr, Or.inr (by rw [hn3]; exact hds)⟩, hW3⟩
  · rintro res ⟨h1, -, -, h4⟩
    exact ⟨h1, h4.1⟩

set_option maxHeartbeats 4000000 in
/-- **The whole VCPU retype writes in `RetW`** (module docstring). -/
theorem retype_vcpu_frame (hA : P0.ArchTotal ar) (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {B n : Nat}
    {hd : U64} (R : RPl st V B n hd) {s : S} (hhd0 : P1.vHeadA st s = hd) (hP : Placed th)
    (hSW : ∀ y, IsSlot th y → (y.val + 32 ≤ B ∨ B + n * 32768 ≤ y.val) ∧
      (hd.val + 8 ≤ y.val ∨ y.val + 32 ≤ hd.val) ∧ ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    {src : U64} (hs : IsSlot th src) {p sb fi : U64} {d : Bool}
    (hcap : capAt (L.mem s) src = ok (.Untyped p sb fi d))
    (hnx : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src))
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r)) (hr : r ≤ 64) (off win : U64) (hnW : win.val = n)
    (hwin : off.val + n ≤ 2 ^ r) (Vl : VList st V th s) (hwz : WinZero (L.mem s) B 32768 n False)
    (nt us : U64) (hnt : nt.val = 14) (base : U64) (hbase : base.val = B) (dev : Bool) :
    untyped.retype st ar s a src false base nt us dest off win dev ⦃ res =>
      res.2.2 = a ∧ P1.WritesIn st s res.2.1 (RetW V th B n hd) ⦄ := by
  have hz15 : zOf nt.val us.val = 15 := by rw [hnt]; simp [zOf]
  obtain ⟨total, -, hret⟩ := retype_noreset_eq14 (L := L) ar s a src base nt us dest off win dev hnt
    (by rw [hz15]; norm_num) p sb fi d hcap
  rw [hret]
  have h0 := slot_word_aligned hP hs off0
  rw [wordOf_zero] at h0
  have hfit := hs.fit hP
  have hsa := hs.align hP
  refine WP.spec_bind (set_cap_frame s src _ h0 (by omega)) fun s1 hW1 => ?_
  have hW1' : P1.WritesIn st s s1 (SlotW th) :=
    ⟨hW1.1, hW1.2.1, fun w hw hn => hW1.2.2 w hw fun h => hn ⟨hw, src, hs, h.1, by omega⟩⟩
  have Vl1 : VList st V th s1 := Vl.writes hW1' (fun b hb => ⟨Vl.lw_al R.vf hb, by
    rintro ⟨-, y, hy, h1, h2⟩
    obtain ⟨-, g2, g3⟩ := hSW y hy
    rcases hb with e | ⟨w, hw, e | e⟩ <;> subst e
    · rw [hhd0] at h1 h2; omega
    · have := lay_next_val (R.vf w hw).2; have := g3 w hw; omega
    · have := lay_prev_val (R.vf w hw).2; have := g3 w hw; omega⟩)
  have hwz1 : WinZero (L.mem s1) B 32768 n False := fun w hw h1 h2 => by
    rw [hW1.2.2 w hw (fun h => by have := (hSW src hs).1; omega)]
    exact hwz w hw h1 h2
  have e24 : (wordOf src 24#u64).val = src.val + 24 := by rw [slot_word_val hP hs off24]; rfl
  have hnx1 : nextOf (L.mem s1) src = nextOf (L.mem s) src := by
    unfold nextOf
    rw [hW1.2.2 _ (slot_word_aligned hP hs off24) (fun h => by have := h.2; omega)]
  have hhd1 : ∀ s' : S, L.ksb s' = L.ksb s1 → P1.vHeadA st s' = hd := fun s' e => by
    rw [← hhd0]; exact hd_of_ksb (e.trans hW1.1)
  have hntc : nt = fl4_abi.consts.object.X86Vcpu := by unfold fl4_abi.consts.object.X86Vcpu; scalar_tac
  rw [hntc]
  refine WP.spec_bind (create_vcpu_frame hA hc hk R hhd1 hP hSW hs (hnx1 ▸ hnx) hdest hr off hwin Vl1 hwz1 win base
    us hnW hbase dev) ?_
  rintro ⟨s2, a2⟩ ⟨h1, h2⟩
  exact (WP.spec_ok _).2 ⟨h1, (hW1'.trans h2).mono fun b hb => hb.elim Or.inr id⟩

/-- Writes whose aligned words in the object at `v` are at most its `PREV` link keep `AgreeAtAL` there. -/
theorem agreeAL_of_off {v : U64} (hv : VFits v) {s s' : S} {W : U64 → Prop} (h : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → P1.Aligned b → b.val + 8 ≤ v.val ∨ v.val + 32768 ≤ b.val ∨ b.val = v.val + 20496) :
    AgreeAtAL (memW st s) (memW st s') v.bv := by
  intro o h1 h8 hn1 hn2
  have ho : o.toNat < 32768 := size_nat h1
  have e := vo_val hv ho
  have hl := links_nat ⟨hn1, hn2⟩
  have hal : P1.Aligned (⟨v.bv + o⟩ : U64) := by
    unfold P1.Aligned; rw [e]; have := hv.1; omega
  unfold memW
  refine congrArg UScalar.bv (h.2.2 _ hal fun hb => ?_)
  rcases hW _ hb hal with c | c | c <;> rw [e] at c <;> omega

/-- **Writes in `RetW` keep `AgreeAtAL` at every VCPU of `V`** (module docstring). -/
theorem agreeAL_of_retW {B n : Nat} {hd : U64} (R : RPl st V B n hd)
    (hSV : ∀ y, IsSlot th y → ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    {s s' : S} (h : P1.WritesIn st s s' (RetW V th B n hd)) {v : U64} (hv : v ∈ V) :
    AgreeAtAL (memW st s) (memW st s') v.bv := by
  have hf := R.vf v hv
  refine agreeAL_of_off hf h fun b hb hal => ?_
  unfold P1.Aligned at hal
  rcases hb with (⟨c1, c2⟩ | rfl | ⟨w, hw, e, -⟩) | ⟨-, y, hy, h1, h2⟩
  · have := R.vw v hv; omega
  · have := R.hv v hv; omega
  · by_cases hvw : v = w
    · subst hvw; omega
    · have := R.vv v hv w hw hvw; omega
  · have := hSV y hy v hv; omega

end

theorem vrelAt_frameAL {Z : Type} {mem mem' : Fl4Spec.Word → Fl4Spec.Word} {σ σ' : Fl4Spec.State Z} {v : Fl4Spec.Word}
    (hm : AgreeAtAL mem mem' v) (hs : Fl4Spec.vcpuAt σ' v = Fl4Spec.vcpuAt σ v) (h : VRelAt mem σ v) :
    VRelAt mem' σ' v := by
  obtain ⟨vs, hvs, h1, h2⟩ := h
  exact ⟨vs, by rw [hs]; exact hvs, fun e => VcpuRelSvm.congrAL hm (h1 e), fun e => VcpuRelVmx.congrAL hm (h2 e)⟩

end
end Fl4Proofs.P3.VirtRetFrameV

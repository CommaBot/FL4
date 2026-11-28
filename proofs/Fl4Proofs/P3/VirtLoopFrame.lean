/-
P3x for virtualization (line virt, gen 19, item 2): **the VCPU retype loop with P3's capability side** —
`create_new_objects_vcpu`'s companion invariant `M` (P3/VirtRetypeLoop) instantiated with UntypedLoop's
`LoopInv` over the VCPU caps, both obligations discharged.

* `SlotW th b`: `b` is an aligned word inside a slot of `th`. **`loop_stepC_frame`**: VirtLoopC's `loop_stepC`
  together with `insert_new_cap`'s footprint as `WritesIn … (SlotW th')` (`insert_new_frame`, `insert_new_cap_ksb`, VirtInsCpu's `insert_new_cap_cpu`).
* `slotsSame_of_writesOff` (writes missing every slot keep the slots), `FinM.of_capV`, **`LoopInv.frame`**: `LoopInv`
  survives any memory change that keeps the slot words of `th'` (`SlotsSame`) and the zero region — every
  component is a slot fact (`StateRel` / `SlotsValid` by `of_caps`, `MdbLinks` / `CdtRel` / `MdbInv` / `NullKeep`
  by `of_same`, chain caps / revocable bits by `SlotsSame.capV` / `revOf`, `FinM` by `of_capV`).
* `vcj B j := Cap.Vcpu (vI B j)` and its cap facts (`baseF_vcpu`, `topF_vcpu`, `capRel_vcpu`): the VCPU caps
  satisfy `loop_stepC`'s parameters (`NewKindV.vcpu`, `physF_vcpu`, `EncWf` from the window's canonicity).
* **`create_new_objects_vcpu_loop`** / **`create_new_objects_vcpu_loopR`**: `objects.create_new_objects … X86Vcpu …`
  from `LoopInv … (vcj B) s 0` ends with `res.2 = a`, `VList` over `V` and the `n` new VCPUs, every new VCPU
  `VRelInit` (resp. `VRelAt` to the spec's retype hook state), **and `LoopInv … (vcj B) res.1 n`** (all `n` VCPU
  caps inserted, related to the spec's `createCap (.archObject .vcpuObj)` loop, MDB invariant kept).

  `hMc` (VirtRetypeLoop's frame obligation) is discharged by `LoopInv.frame` from the placement fact `hSW`
  (every slot of `th'` misses the window, the VCPU list head word and the VCPUs of `V`) and `hzW` (`init`'s
  words miss the zero region; take it empty for a VCPU retype); `hIns` by `loop_stepC_frame`, `FW := SlotW th'`
  (inside slots, so off the window / head word / `V` by `hSW`).

The facts `hSW`, `hzW`, `hcan` (canonical window), `hwin`, `hpA` / `hAp` (window inside the untyped), `hsrcd`
are the retype's placement / freshness facts, state hypotheses as in `loop_step` / `create_loop_rel` /
`create_new_objects_vcpu`. Named premises: `CapAgree ar a` [P], `VirtCodeAgree ar a` [P] (unchanged, from
`create_new_objects_vcpu`). No new premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtLoopC
import Fl4Proofs.P3.VirtRetypeLoop
import Fl4Proofs.P3.VirtInsCpu
import Fl4Proofs.P3.CreateLoopE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtLoopFrame
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtReplyKeep
open Fl4Proofs.P3.VirtRetypeLoop Fl4Proofs.P3.VirtInsCpu

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-! ## `LoopInv` across writes off the slots -/

theorem slotsSame_of_writesOff {th : TypedHeap} (hP : Placed th) {s s' : S} {W : U64 → Prop}
    (hW : P1.WritesIn st s s' W) (hWo : ∀ b, W b → ∀ y, IsSlot th y → ¬ (y.val ≤ b.val ∧ b.val < y.val + 32)) :
    SlotsSame th (L.mem s) (L.mem s') :=
  fun a ha =>
    have h : ∀ k, Off k → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := fun k hk =>
      hW.2.2 _ (slot_word_aligned hP ha hk) fun hw =>
        hWo _ hw a ha (by rw [slot_word_val hP ha hk]; have := hk.lt; omega)
    ⟨by have := h 0#u64 (Or.inl rfl); rwa [wordOf_zero] at this, h _ (Or.inr (Or.inl rfl)),
      h _ (Or.inr (Or.inr (Or.inl rfl))), h _ (Or.inr (Or.inr (Or.inr rfl)))⟩

theorem FinM.of_capV {m m' : U64 → U64} {G : MdbGhost} (h : FinM m G)
    (hc : ∀ x ∈ G.chains.flatten, capV m' x = capV m x) : FinM m' G := by
  have hf : ∀ ch ∈ G.chains, ∀ x ∈ ch, x ∈ G.chains.flatten := fun ch hch x hx => List.mem_flatten.2 ⟨ch, hch, hx⟩
  refine ⟨fun ch1 h1 ch2 h2 x hx y hy hov => ?_, fun x hx y hy hne hov hzx hzy hfr => ?_,
    fun x hx y hy hne hfx hfy hs => ?_, fun x hx y hy hne hz => ?_⟩
  · rw [hc x (hf _ h1 x hx), hc y (hf _ h2 y hy)] at hov; exact h.conn ch1 h1 ch2 h2 x hx y hy hov
  · simp only [hc x hx, hc y hy] at hov hzx hzy hfr ⊢; exact h.key x hx y hy hne hov hzx hzy hfr
  · unfold srM at hs; simp only [hc x hx, hc y hy] at hfx hfy hs ⊢
    exact h.fnest x hx y hy hne hfx hfy (by unfold srM; exact hs)
  · simp only [hc x hx, hc y hy] at hz ⊢; exact h.zfin x hx y hy hne hz

/-- **`LoopInv` is a slot fact** (module docstring). -/
theorem LoopInv.frame {th' : TypedHeap} {srcSl : Fl4Spec.CslotPtr} {srcC : capability.Cap} {σ1 : Fl4Spec.State Unit}
    {f : Fl4Spec.CslotPtr × Fl4Spec.ObjRef → Fl4Spec.NonDet (Fl4Spec.State Unit) Unit}
    {pairs : List (Fl4Spec.CslotPtr × Fl4Spec.ObjRef)} {A k win : Nat} {dslot : Nat → U64} {zlo zhi : Nat}
    {G0 : MdbGhost} {m0 : U64 → U64} {cj : Nat → capability.Cap} {s s' : S} {i : Nat}
    (hI : LoopInv (L := L) th' srcSl srcC σ1 f pairs A k win dslot zlo zhi G0 m0 cj s i)
    (hSS : SlotsSame th' (L.mem s) (L.mem s'))
    (hsrcS : IsSlot th' (cslotAddr srcSl)) (hds : ∀ j, j < win → IsSlot th' (dslot j)) (hiw : i ≤ win)
    (hz : ∀ a : U64, P1.Aligned a → zlo ≤ a.val → a.val < zhi → L.mem s' a = L.mem s a) :
    LoopInv (L := L) th' srcSl srcC σ1 f pairs A k win dslot zlo zhi G0 m0 cj s' i := by
  obtain ⟨σi, Gi, hchain, hR, hV, hM, hC, hIv, hsrc, hnull, hno, hdd, hzr, hT1, hT1b, hT2a, hT2b, hT3, hFM,
    hCh, hRv, hNK⟩ := hI
  have hsl : ∀ x, x ∈ Gi.chains.flatten → IsSlot th' x := fun x h => ((hM.members x).1 h).1
  have hcv : ∀ x ∈ Gi.chains.flatten, capV (L.mem s') x = capV (L.mem s) x := fun x hx => hSS.capV (hsl x hx)
  refine ⟨σi, Gi, hchain, StateRel.of_caps hR (fun x hx => hSS.capAt hx),
    SlotsValid.of_caps hV (fun x hx => hSS.capAt hx), MdbLinks.of_same hM hSS, CdtRel.of_same hC hSS rfl rfl,
    MdbInv.of_same hM hIv hSS, (hSS.capAt hsrcS).trans hsrc,
    fun j h1 h2 => (hSS.capAt (hds j h2)).trans (hnull j h1 h2), ?_, ?_,
    fun a ha h1 h2 => (hz a ha h1 h2).trans (hzr a ha h1 h2), hT1, hT1b,
    fun j hj => (hSS.capV (hds j (by omega))).trans (hT2a j hj),
    fun x hx => (hSS.capV (hsl x (hT1b x hx))).trans (hT2b x hx), hT3, fun h0 => FinM.of_capV (hFM h0) hcv, hCh,
    fun x hx => (hSS.revOf (hsl x (hT1b x hx))).trans (hRv x hx), hNK.trans (NullKeep.of_same hSS)⟩
  · intro x hx hp; rw [hcv x hx] at hp ⊢; exact hno x hx hp
  · intro y hy; rw [hSS.capV (hsl y (desc_mem hM hy).1)]; exact hdd y hy

/-! ## The VCPU caps -/

/-- The caps a VCPU retype of objects at `B` inserts. -/
def vcj (B : Nat) : Nat → capability.Cap := fun j => .Vcpu (vI B j)

theorem ptrF_vcpu (v : U64) : ptrF (.Vcpu v) = v := ptrF_of (by unfold capability.Cap.ptr; rfl)

theorem sizeF_vcpu (v : U64) : sizeF (.Vcpu v) = 15#u64 := sizeF_of (by
  unfold objects.cap_size_bits; simp [fl4_abi.consts.bits.VCPU])

theorem baseF_vcpu (v : U64) : baseF (.Vcpu v) = v.val := by unfold baseF; rw [ptrF_vcpu]

theorem topF_vcpu {v : U64} (hv : v.val + 32768 ≤ 2 ^ 64) : topF (.Vcpu v) = v.val + 32768 - 1 := by
  unfold topF
  rw [ptrF_vcpu, sizeF_vcpu]
  have hm := maskF_val (b := 15#u64) (by decide)
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hm]
  omega

theorem capRel_vcpu (B j bits : Nat) (dev : Bool) :
    CapRel (vcj B j) (Fl4Spec.defaultCap (.archObject .vcpuObj) (BitVec.ofNat 64 (B + j * 32768)) bits dev) :=
  ⟨trivial, rfl⟩

theorem vcj_base {B j : Nat} (e : (vI B j).val = B + j * 32768) : baseF (vcj B j) = B + j * 32768 := by
  unfold vcj; rw [baseF_vcpu, e]

theorem vcj_top {B n j : Nat} (hbf : B + n * 32768 < 2 ^ 64) (hj : j < n) (e : (vI B j).val = B + j * 32768) :
    topF (vcj B j) = B + j * 32768 + 32768 - 1 := by
  have h1 : j * 32768 + 32768 ≤ n * 32768 := by omega
  have h : (vI B j).val + 32768 ≤ 2 ^ 64 := by rw [e]; omega
  unfold vcj; rw [topF_vcpu h, e]

theorem vcj_enc {B n j : Nat} (hcan : CanonR B (B + n * 32768)) (hj : j < n) (e : (vI B j).val = B + j * 32768) :
    EncWf (vcj B j) := by
  have h1 : j * 32768 + 32768 ≤ n * 32768 := by omega
  show Canonical (vI B j)
  exact hcan.canonical (by rw [e]; omega) (by rw [e]; omega)

end

/-! ## The loop -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}
variable {V : Set U64} {th : TypedHeap}

/-- The companion invariant: UntypedLoop's `LoopInv` over the VCPU caps, and the counter in range. -/
abbrev MV (th' : TypedHeap) (pp : U64) (idx : List Bool) (p sb fi : U64) (d : Bool) (σ1 : Fl4Spec.State Unit)
    (us : U64) (dev : Bool) (dest : U64) (r : Nat) (off : U64) (B n : Nat) (zlo zhi : Nat) (G0 : MdbGhost)
    (m0 : U64 → U64) (s : S) (i : Nat) : Prop :=
  LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 B) n 32768))
      B 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0 (vcj B) s i ∧ i ≤ n

set_option maxHeartbeats 8000000 in
/-- The two obligations of `create_new_objects_vcpu` for `MV` (module docstring). -/
theorem mv_obligations {B n : Nat} {hd : U64} (R : RPl st V B n hd)
    (th' : TypedHeap) (hP' : Placed th') {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r)) (hr : r ≤ 64)
    (off us : U64) (dev : Bool)
    (hwin : off.val + n ≤ 2 ^ r) (hcan : CanonR B (B + n * 32768))
    (hpA : p.val ≤ B) (hAp : B + n * 32768 ≤ p.val + 2 ^ sb.val)
    (zlo zhi : Nat) (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ zlo ∨ zhi ≤ a.val)
    (hzW : ∀ b, CrW V B n hd b → ¬ (zlo ≤ b.val ∧ b.val < zhi))
    (hSW : ∀ y, IsSlot th' y → (y.val + 32 ≤ B ∨ B + n * 32768 ≤ y.val) ∧
      (hd.val + 8 ≤ y.val ∨ y.val + 32 ≤ hd.val) ∧ ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < n → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :
    (∀ s s' i, MV (L := L) th' pp idx p sb fi d σ1 us dev dest r off B n zlo zhi G0 m0 s i →
      P1.WritesIn st s s' (CrW V B n hd) → MV (L := L) th' pp idx p sb fi d σ1 us dev dest r off B n zlo zhi G0 m0 s' i) ∧
    (∀ b, SlotW th' b → (b.val + 8 ≤ B ∨ B + n * 32768 ≤ b.val) ∧ b ≠ hd ∧
      ∀ w ∈ V, b.val + 8 ≤ w.val ∨ w.val + 32768 ≤ b.val) ∧
    (∀ iw : U64, iw.val < n → ∀ s2, MV (L := L) th' pp idx p sb fi d σ1 us dev dest r off B n zlo zhi G0 m0 s2 iw.val →
      cdt.insert_new_cap st s2 (cslotAddr (pp.bv, idx)) (slotAddr dest.bv (core.num.U64.wrapping_add off iw).bv)
        (capability.Cap.Vcpu (vI B iw.val)) ⦃ s3 =>
          MV (L := L) th' pp idx p sb fi d σ1 us dev dest r off B n zlo zhi G0 m0 s3 (iw.val + 1) ∧
          P1.WritesIn st s2 s3 (SlotW th') ⦄) := by
  have hbf := R.bfit
  have hrr : 2 ^ r ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hr
  have hAs : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hsrcS : IsSlot th' (cslotAddr (pp.bv, idx)) := hAs.isSlot
  have hds : ∀ j, j < n → IsSlot th' (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :=
    fun j hj => ⟨dest, off.val + j, Or.inl ⟨r, hdest, by omega⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro s s' i ⟨hI, hle⟩ hW
    refine ⟨LoopInv.frame hI (slotsSame_of_writesOff hP' hW fun b hb y hy hin => ?_) hsrcS hds hle
      (fun x hx h1 h2 => hW.2.2 x hx fun hc => hzW x hc ⟨h1, h2⟩), hle⟩
    obtain ⟨g1, g2, g3⟩ := hSW y hy
    rcases hb with ⟨h1, h2⟩ | rfl | ⟨w, hw, h1, h2⟩
    · omega
    · omega
    · have := g3 w hw; omega
  · rintro b ⟨hal, y, hy, h1, h2⟩
    have hya := hy.align hP'
    unfold P1.Aligned at hal
    obtain ⟨g1, g2, g3⟩ := hSW y hy
    refine ⟨by omega, fun e => by subst e; omega, fun w hw => by have := g3 w hw; omega⟩
  · rintro iw hiw s2 ⟨hI2, -⟩
    have hi4 : (core.num.U64.wrapping_add off iw).bv = BitVec.ofNat 64 (off.val + iw.val) := by
      rw [bv_eq_ofNat]; congr 1
      have : off.val + iw.val < 2 ^ 64 := by omega
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
    rw [hi4]
    have hstep := loop_stepC_frame (L := L) th' hP' hpp hidx hsb hpfit σ1 hdest hr (.archObject .vcpuObj) us.val dev
      (vcj B) off.val n B 32768 (by norm_num) hwin (le_of_lt hbf) hpA hAp
      (fun j hj => vcj_base (R.vIv hj)) (fun j hj => vcj_top hbf hj (R.vIv hj))
      (fun j _ => rfl) (fun j _ => capRel_vcpu B j us.val dev)
      (fun j hj => vcj_enc hcan hj (R.vIv hj))
      (fun j _ => NewKindV.vcpu _) (fun j _ => physF_vcpu _) (fun j _ => trivial)
      zlo zhi hzs G0 m0 hsrcd s2 iw.val hiw hI2
    exact WP.spec_mono hstep fun s3 ⟨h1, h2⟩ => ⟨⟨h1, by omega⟩, h2⟩

set_option maxHeartbeats 8000000 in
/-- **The VCPU retype loop with P3's capability side** (module docstring). -/
theorem create_new_objects_vcpu_loop (hA : P0.ArchTotal ar) (hc : CapAgree ar a) (hk : VirtCodeAgree ar a)
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
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < n → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 B) n 32768))
      B 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0 (vcj B) s 0) :
    objects.create_new_objects st ar s a fl4_abi.consts.object.X86Vcpu (cslotAddr (pp.bv, idx)) dest off nW base us
      dev ⦃ res =>
      res.2 = a ∧ VList st (VsI V B n) th res.1 ∧ (∀ j, j < n → VRelInit (memW st res.1) (vI B j).bv) ∧
        LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
          (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
          ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 B) n 32768))
          B 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0 (vcj B) res.1 n ⦄ := by
  obtain ⟨hMc, hFW, hIns⟩ := mv_obligations (L := L) R th' hP' hpp hidx hsb hpfit σ1 hdest hr off us dev hwin hcan
    hpA hAp zlo zhi hzs hzW hSW G0 m0 hsrcd
  exact WP.spec_mono (create_new_objects_vcpu hA hc hk R hhd _ hMc hFW (cslotAddr (pp.bv, idx)) dest off hIns Vl hwz
    ⟨hinv, Nat.zero_le _⟩ nW base us hnW hbase dev) fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4.1⟩

set_option maxHeartbeats 8000000 in
/-- **The same, each new VCPU related (`VRelAt`) to the spec's retype hook state** (`create_new_objects_vcpu_rel`). -/
theorem create_new_objects_vcpu_loopR {Z : Type} (hA : P0.ArchTotal ar) (hc : CapAgree ar a)
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
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < n → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 B) n 32768))
      B 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0 (vcj B) s 0) :
    objects.create_new_objects st ar s a fl4_abi.consts.object.X86Vcpu (cslotAddr (pp.bv, idx)) dest off nW base us
      dev ⦃ res =>
      res.2 = a ∧ VList st (VsI V B n) th res.1 ∧
        LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
          (Fl4Spec.createCap (Z := Unit) (.archObject .vcpuObj) us.val (pp.bv, idx) dev)
          ((windowSlots dest r off.val n).zip (regionPtrs (BitVec.ofNat 64 B) n 32768))
          B 32768 n (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) zlo zhi G0 m0 (vcj B) res.1 n ∧
        ∀ j, j < n → ∀ (l : List Fl4Spec.ObjRef) (σ : Fl4Spec.State Z) (x : Unit × Fl4Spec.State Z),
          x ∈ (Fl4Spec.NonDet.mapMx (fun v => Fl4Spec.setVcpu (Z := Z) v (Fl4Spec.initVcpu Fl4Spec.virtKind)) l σ).1 →
          (vI B j).bv ∈ l → VRelAt (memW st res.1) x.2 (vI B j).bv ⦄ := by
  obtain ⟨hMc, hFW, hIns⟩ := mv_obligations (L := L) R th' hP' hpp hidx hsb hpfit σ1 hdest hr off us dev hwin hcan
    hpA hAp zlo zhi hzs hzW hSW G0 m0 hsrcd
  exact WP.spec_mono (create_new_objects_vcpu_rel (Z := Z) hA hc hk R hhd _ hMc hFW (cslotAddr (pp.bv, idx)) dest off
    hIns Vl hwz ⟨hinv, Nat.zero_le _⟩ nW base us hnW hbase dev) fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3.1, h4⟩

end

end

end Fl4Proofs.P3.VirtLoopFrame

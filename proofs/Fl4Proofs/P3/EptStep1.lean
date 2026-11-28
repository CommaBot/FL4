/-
P3 (line mmuAD, gen 42b1): **the first EPT-touching steps at `VmEptState`** — one word written inside a guest table of
`X` (`mark_core`'s core bitmap, the walker's accessed / dirty bits), with the base, `VcpuCore` and `EptCore` kept and the
spec state unchanged; plus the architect's checks (a)–(c) as theorems where they are statements about the records.

## A word of a table of `X`, written (`JAtZB.eptWr`, `VcpuCore.ofW`, `EptCore.wrIn`, **`VmEptState.wrIn`**)

* **Base** (`JAtZB.eptUserW` → `JAtZB.eptWr`): a table of `X` is `H`'s `.other 12` (`JAtZB.eptHeap`) and a spec
  `.ept` object, so P3's relation reads none of its words: the five side facts of `JAtZB.frameWrJ` (P3/JAtZBWr, the
  lemma `JAtZB.vcpuWrJ` uses for a VCPU word) follow from the table's placement — apart from every other `H` object
  (`JAtZB.eptApartH`), from the typed heap's CNodes / TCBs and the VSpace tables / pools (spec objects of other kinds),
  from the IPC-buffer words (`BufPgHyp` + `EptCore.sep`), off the kernel-global area (`EptCore.ks`). The slots are
  kept (`slotsSame_wr`).
* **`VcpuCore.ofW`**: `VcpuCore.ofBS` (P3/VmState) with its two uses of `OObj` replaced by what they gave — the slots
  kept (`SlotsSame`) and the writes off every VCPU of `V` — so any write set apart from the VCPUs, the VCPU list head
  and the TCB VCPU words keeps `VcpuCore`. A table word is apart from all three (`EptCore.apartV`,
  `JAtZB.eptHead`, `JAtZB.oobjX` on the TCB word `t + 3664`).
  Gen 42b7: generalised in place to **`VcpuCore.ofWE`** (each slot's cap kept or rewritten into an `Ept` cap of the
  same `shape`: the EPT pool assign, P3/EptAssignV); `ofW` is its `SlotsSame` corollary, statement unchanged.
* **`EptCore.wrIn`**: the word `eptA t0 i0` written with a value that is either (i) outside the relation —
  `XL t0 = 0` and `256 ≤ i0` (the root's upper half, where FL4 keeps `mark_core`'s bitmap, ept.rs l. 14, l. 43-54) —
  or (ii) equal to the old word up to the hardware-written bits (`EptWord virtKind new old`). Case (i) needs that no
  related entry of another table shares the word (`EptCore.sep` between two tables of `X`).

## The steps

* **`mark_core`** (ept.rs l. 43-54; called once per VM entry from fl4-kernel entry.rs l. 757-760 on the root
  `ept::root` returned for the thread's `SLOT_EPT` cap): **`ept_markCore`** computes it — it writes nothing or the
  word `root + 4080 + 8 · ⌊cpu / 32⌋` = `eptA root (510 + ⌊cpu / 32⌋)` (the CPU is below 64, `JKern.csLt`), and
  **`VmEptState.markCore`** keeps `VmEptState` with σ unchanged (the spec has no step: `mark_core` is FL4 bookkeeping
  for its TLB shoot-down, l4v has no counterpart). Its hypothesis on `root` is the call site's: `ept::root` succeeds
  only on an `Ept { ptr, level: 0, mapped: true, .. }` cap and returns `ptr` (ept.rs l. 24-41), read from a TCB slot,
  so `root ∈ X` and `XL root = 0` follow from `EptCore.exte` / `capL` (**`EptCore.ofCap`**).
* **Guest execution** (SVM nested paging writes A/D bits 5/6, `eptHw virtKind = 0x60`; VMX writes nothing, EPTP
  A/D off, fl4-arch-x86_64 vm.rs l. 1002): **`VmEptState.hwWr`** — any word of a table of `X` rewritten with a value
  equal to the old one up to `eptHw` keeps `VmEptState` with σ unchanged (the spec's guest tables are the abstract
  ones; l4v does not model the walker's A/D writes). One write per lemma application; a run of the guest is a
  sequence of them.

## The architect's checks (gen 42b1)

* (a) **`RngOne` covers `Ept` caps**: `RngOne` (P3/VirtRngOne) quantifies over every exact range class (`RngKey`:
  physical, not untyped, not a frame); an `Ept` cap is physical (objects.rs l. 51-72, `Cap::Ept` in the list) with
  size 12 for every level / mapped / asid (objects.rs `cap_size_bits`, extracted `| Ept _ _ _ _ _ => ok 12`), so
  **`key_ept`** and **`eptOneChain_of_rngOne`**: all `Ept p …` caps (whatever their other fields) lie in one ghost
  chain. No new field is needed; `RngOne` stays in `VcpuCore` as the shared MDB fact.
* (b) **SetEPTRoot's slot is inside the slot quantification**: `IsSlot th y` (P3/Layout l. 48-51) covers a TCB's
  slots `i < tcbSlots = 6` (P3/StateRel l. 111), and `SLOT_EPT = 5` (fl4-core x86_64/layout.rs l. 14): **`isSlot_ept`**.
  So `EptCapL`, `JExtEpt` and `JExtVcpu` constrain the TCB's EPT-root slot.
* (c) **No guest mapping overwrites root words 510 / 511**: every map / unmap entry index is `(gpa >> shift) & 511`
  with `gpa < LIMIT = 2^47` (ept.rs l. 13, 134, 290-293; unmap's `gpa` is the cap's `vaddr`, set only at map,
  l. 183/308), and the root is reached only at shift 39 (`lookup`, l. 72-84), so a root entry index is
  `gpa / 2^39 < 256`: **`eptRootIdx_lt`**. A table unmap zeroes a non-root table only (`decode` refuses level 0,
  l. 246-255). `mark_core` writes the whole word `old | bit` with `bit ≥ 2^32` (l. 47), so the lower half stays as it
  was; `EptRel` relates no root entry ≥ 256 at all (P3/JAtZV3EptRel), so this matches. `GuestTag` stays
  one-directional (pool entry ⇒ root in `X` at level 0).

Gen 42b2 (`UnmappedEmpty`): `EptCore.wrIn` / `VmEptState.wrIn` take `hz` (a word of the table of an unmapped cap is
written 0); `VmEptState.hwWr` takes `h0` (the walker writes A/D only into a present, so non-zero, entry) and
`VmEptState.markCore` proves `hz` from `ue`'s uniqueness (the root has a mapped cap, so no unmapped one).

No named premise. New file only; root import after `P3.EptCore`.
-/
import Fl4Proofs.P3.EptCore
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## (a) `RngOne` covers `Ept` caps -/

theorem physF_ept (p l a v : U64) (m : Bool) : physF (.Ept p l m a v) = true := ok_inj (phys_eq _).symm

theorem key_ept (p l a v : U64) (m : Bool) : VirtRngOne.RngKey (.Ept p l m a v) := ⟨physF_ept p l a v m, rfl, rfl⟩

theorem ptrF_ept (p l a v : U64) (m : Bool) : ptrF (.Ept p l m a v) = p := ok_inj (ptr_eq _).symm

theorem sizeF_ept (p l a v p' l' a' v' : U64) (m m' : Bool) : sizeF (.Ept p l m a v) = sizeF (.Ept p' l' m' a' v') := by
  have h : objects.cap_size_bits (.Ept p l m a v) = objects.cap_size_bits (.Ept p' l' m' a' v') := rfl
  rw [size_eq, size_eq] at h; exact ok_inj h

/-- All `Ept` caps to one table lie in one ghost chain. -/
def EptOneChain (G : MdbGhost) (mem : U64 → U64) : Prop :=
  ∀ p, ∀ ch ∈ G.chains, ∀ ch' ∈ G.chains, ∀ y ∈ ch, ∀ y' ∈ ch', ∀ l m a v l' m' a' v',
    capV mem y = .Ept p l m a v → capV mem y' = .Ept p l' m' a' v' → ch = ch'

/-- **`EptOneChain` from `RngOne`** (module docstring, check (a)). -/
theorem eptOneChain_of_rngOne {mem : U64 → U64} {G : MdbGhost} (hnd : G.chains.flatten.Nodup)
    (h : VirtRngOne.RngOne mem G) : EptOneChain G mem := by
  intro p ch hch ch' hch' y hy y' hy' l m a v l' m' a' v' h1 h2
  have hy0 := List.mem_flatten.2 ⟨ch, hch, hy⟩
  have hy0' := List.mem_flatten.2 ⟨ch', hch', hy'⟩
  obtain ⟨d, hd, e1, e2⟩ := h y hy0 y' hy0' (by rw [h1]; exact key_ept _ _ _ _ _)
    (by rw [h2]; exact key_ept _ _ _ _ _) (by rw [h1, h2]; unfold baseF; rw [ptrF_ept, ptrF_ept])
    (by rw [h1, h2]; unfold topF; rw [ptrF_ept, ptrF_ept, sizeF_ept p l a v p l' a' v' m m'])
  exact (VirtVChunkIns.vchain_eq hnd hch hd hy e1).trans (VirtVChunkIns.vchain_eq hnd hd hch' e2 hy')

/-! ## (b) the TCB's EPT-root slot is a slot -/

/-- **`SLOT_EPT = 5` is one of a TCB's `tcbSlots = 6` slots** (check (b)). -/
theorem isSlot_ept {th : TypedHeap} {t : U64} (ht : th t = some .tcb) : IsSlot th (slotOf t 5) :=
  ⟨t, 5, Or.inr ⟨ht, by unfold tcbSlots; omega⟩, rfl⟩

/-! ## (c) root entries of a guest mapping -/

/-- **A guest address below `LIMIT = 2^47` indexes a root entry below 256** (check (c)). -/
theorem eptRootIdx_lt {gpa : Nat} (h : gpa < 2 ^ 47) : (gpa / 2 ^ 39) % 512 < 256 := by
  have : gpa / 2 ^ 39 < 256 := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq h (by norm_num))
  exact lt_of_le_of_lt (Nat.mod_le _ _) this

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

/-- **A slot's `Ept r 0 …` cap names a root of `X` at level 0** (`exte`, `capL`). -/
theorem EptCore.ofCap (C : EptCore (L := L) X XL th s σ) {y r a v : U64} {mm : Bool} (hy : IsSlot th y)
    (hc : capV (L.mem s) y = .Ept r 0#u64 mm a v) : r ∈ X ∧ XL r = 0 := by
  have h := C.exte.cap y hy
  rw [hc] at h
  have hl := C.capL y hy r 0#u64 a v mm hc
  exact ⟨h, by simpa using hl.symm⟩

/-- **A slot's `Ept p l …` cap names a table of `X` at a valid level and with `PaM`** (gen 42b12: `exte`, `capL`,
`tbl`). -/
theorem EptCore.capTbl (C : EptCore (L := L) X XL th s σ) {y p l a v : U64} {mm : Bool} (hy : IsSlot th y)
    (hc : capV (L.mem s) y = .Ept p l mm a v) :
    p ∈ X ∧ (l.val = 0 ∨ l.val = 39 ∨ l.val = 30 ∨ l.val = 21) ∧ Vs.PaM p 4503599627366400#u64 := by
  have h := C.exte.cap y hy
  rw [hc] at h
  have hl := C.capL y hy p l a v mm hc
  obtain ⟨h1, h2⟩ := C.tbl p h
  exact ⟨h, by rw [hl]; exact h1, h2⟩

/-! ## `EptCore` across one table word -/

/-- Two related words of tables of `X` at the same address are the same entry of the same table. -/
theorem EptCore.eptA_inj (C : EptCore (L := L) X XL th s σ) {t t0 : U64} (ht : t ∈ X) (ht0 : t0 ∈ X)
    {i i0 : BitVec 9} (he : (eptA t i).val = (eptA t0 i0).val) : t = t0 ∧ i.toNat = i0.toNat := by
  have p1 := C.rel.place t ht
  have p0 := C.rel.place t0 ht0
  rw [eptA_val p1.2, eptA_val p0.2] at he
  have hi := i.isLt
  have hi0 := i0.isLt
  by_cases e : t = t0
  · subst e; exact ⟨rfl, by omega⟩
  · exfalso
    obtain ⟨es0, hk0, -⟩ := C.rel.obj t0 ht0
    have hne : t0.bv ≠ t.bv := fun h => e (UScalar.eq_of_val_eq (by
      show t.bv.toNat = t0.bv.toNat; rw [h]))
    have hs := C.sep t ht t0.bv _ hk0 hne
    have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
    unfold EptApart at hs
    rw [ept_bits, h12] at hs
    have : t0.bv.toNat = t0.val := rfl
    rw [this] at hs
    omega

/-- **`EptCore` across one word of a table of `X`** (module docstring): the new word is outside the relation (the
root's entries ≥ 256) or equal to the old one up to the hardware-written bits; the slots and σ kept. -/
theorem EptCore.wrIn (C : EptCore (L := L) X XL th s σ) {s' : S} (hSS : SlotsSame th (L.mem s) (L.mem s'))
    {t0 : U64} (ht0 : t0 ∈ X) {i0 : BitVec 9} (hw : P1.WritesIn st s s' (· = eptA t0 i0))
    (hU : (XL t0 = 0 ∧ 256 ≤ i0.toNat) ∨
      EptWord Fl4Spec.virtKind (L.mem s' (eptA t0 i0)).bv (L.mem s (eptA t0 i0)).bv)
    (hz : ∀ y l a v, IsSlot th y → capV (L.mem s) y = .Ept t0 l false a v → L.mem s' (eptA t0 i0) = 0#u64) :
    EptCore (L := L) X XL th s' σ where
  rel := by
    refine ⟨fun t ht => ?_, C.rel.spec, C.rel.place⟩
    obtain ⟨es, hk, hwd⟩ := C.rel.obj t ht
    refine ⟨es, hk, fun i hi => ?_⟩
    have hp := C.rel.place t ht
    have e := eptA_val hp.2 i
    have hi9 := i.isLt
    have hal : P1.Aligned (eptA t i) := by unfold P1.Aligned; rw [e]; omega
    by_cases hq : eptA t i = eptA t0 i0
    · obtain ⟨rfl, hii⟩ := C.eptA_inj ht ht0 (congrArg UScalar.val hq)
      rcases hU with ⟨h0, h256⟩ | hU
      · exfalso; rcases hi with h | h
        · exact h h0
        · omega
      · have hold := hwd i hi
        unfold EptWord at hU hold ⊢
        rw [hq, hU, ← hq]; exact hold
    · rw [hw.mem_eq hal hq]; exact hwd i hi
  capL y hy p l a v mm hc := C.capL y hy p l a v mm (by rw [← hSS.capV hy]; exact hc)
  exte := C.exte.of_eq fun y hy => hSS.capV hy
  tag := C.tag
  ks t ht := by rw [hw.1]; exact C.ks t ht
  sep := C.sep
  ue y hy p l a v hc := by
    rw [hSS.capV hy] at hc
    obtain ⟨h1, h2, h3, h4⟩ := C.ue y hy p l a v hc
    have hpX : p ∈ X := by have h := C.exte.cap y hy; rw [hc] at h; exact h
    refine ⟨fun i => ?_, h2, fun y' hy' hne l' mm a' v' hc' => h3 y' hy' hne l' mm a' v'
      (by rw [← hSS.capV hy']; exact hc'), h4⟩
    have hp := C.rel.place p hpX
    have e := eptA_val hp.2 i
    have hi9 := i.isLt
    by_cases hq : eptA p i = eptA t0 i0
    · obtain ⟨rfl, -⟩ := C.eptA_inj hpX ht0 (congrArg UScalar.val hq)
      rw [hq]; exact hz y l a v hy hc
    · rw [hw.mem_eq (by unfold P1.Aligned; rw [e]; omega) hq]; exact h1 i
  eslot := C.eslot.step (EptSlotStep.ofSS hSS)
  walk := C.walk
  named := C.named.ofSS hSS rfl fun _ _ h => h
  tbl := C.tbl

end

/-! ## The base across one table word -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}
  {XL : U64 → Nat}

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 4000000 in
/-- **The side facts of `JAtZB.frameWrJ` for a word of a table of `X`** (module docstring; `JAtZB.vcpuWrJ`'s
argument with the table's placement). -/
theorem JAtZB.eptUserW (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {p w : U64} (hp : p ∈ X) (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 4096) :
    UserW (L := L) Z s σ w ∧ (∀ wp ∈ Z.B, wp.1 ≠ w) ∧
      (∀ q k, H q = some k → (∀ z, k ≠ .other z) → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ w.val) ∧
      (∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ w.val ∧ w.val < o.toNat + 2 ^ Fl4Spec.objBits ko) ∧
      (w.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ w.val) := by
  obtain ⟨es, hσx, -⟩ := C.rel.obj p hp
  have hH : H p = some (.other 12) := J.eptHeap C hp
  have hks := C.ks p hp
  have hw8 : w.val % 8 = 0 := hal
  have hpa : p.val % 4096 = 0 := (C.rel.place p hp).1
  -- apart from every other `H` object
  have wap : ∀ q k', H q = some k' → q ≠ p → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k'.bits ≤ w.val := by
    intro q k' hq hne
    rcases J.eptApartH C hp q k' hq hne with h | h
    · right; omega
    · left; omega
  have hneK : ∀ q k', H q = some k' → (∀ z, k' ≠ .other z) → q ≠ p := fun q k' hq hk' e => by
    subst e; rw [hH] at hq; exact hk' 12 (Option.some.inj hq).symm
  have hAp : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ w.val :=
    fun q k hq hk => wap q k hq (hneK q k hq hk)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hR := J.xtop.rel.2.1.1
  have hcn : ∀ q r, Z.th q = some (.cnode r) → w.val + 8 ≤ q.val ∨ q.val + 32 * 2 ^ r ≤ w.val := by
    intro q r hq
    have hne : q ≠ p := fun e => by
      subst e; obtain ⟨cs, hc, -⟩ := hR.cnode q r hq; rw [hc] at hσx; cases hσx
    have e32 : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; norm_num; ring
    have := wap q _ (hJ.cnode q r hq) hne
    simp only [P1.HKind.bits] at this; rw [e32] at this; exact this
  have htc : ∀ t, Z.th t = some .tcb → w.val + 8 ≤ t.val ∨ t.val + 4096 ≤ w.val := by
    intro t ht
    have hHt := (hJ.tcb t).1 ht
    have := hAp t _ hHt fun _ e => by cases e
    simpa [P1.HKind.bits] using this
  have hF := J.xtop.fin
  have hvs : ∀ q', (q' ∈ Z.P ∨ q' ∈ Z.L4 ∨ q' ∈ Z.L3 ∨ q' ∈ Z.L2 ∨ q' ∈ Z.L1) →
      w.val + 8 ≤ q'.val ∨ q'.val + 4096 ≤ w.val := by
    intro q' hq'
    obtain ⟨n', hn', hH'⟩ := J.vsFr_other hq'
    have hne : q' ≠ p := by
      intro e; subst e
      rcases hq' with hv | hv | hv | hv | hv
      · obtain ⟨f, hf, -⟩ := hF.2.1.pool q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l4 q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l3 q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l2 q' hv; rw [hf] at hσx; cases hσx
      · obtain ⟨f, hf, -⟩ := hF.2.2.1.l1 q' hv; rw [hf] at hσx; cases hσx
    have h4 : 2 ^ 12 ≤ 2 ^ n' := Nat.pow_le_pow_right (by decide) hn'
    rcases wap q' _ hH' hne with h | h
    · exact Or.inl h
    · simp only [P1.HKind.bits] at h; right; omega
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
  have hc64 := J.kern.csLt Z.c hcC
  have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
  have hksw : w.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ w.val := by omega
  have hu : UserW (L := L) Z s σ w :=
    { al := hal
      far := ⟨by rw [hnb]; omega,
        fun t ht => by
          have := hAp t _ (J.zH.1 t ht) fun _ e => by cases e
          simpa [P1.HKind.bits] using this,
        fun sc hsc y n hky => by
          have hHs := (hJ.sc sc y n (J.c0 sc hsc) hky).2
          have := hAp sc _ hHs fun _ e => by cases e
          simpa [P1.HKind.bits] using this⟩
      vobj := fun hv => by
        rcases hv with ⟨q, r, hq, c1, c2⟩ | ⟨t, ht, c1, c2⟩ | ⟨q', hq', c1, c2⟩ | h
        · have := hcn q r hq; omega
        · have := htc t ht; omega
        · have := hvs q' hq'; omega
        · omega
      ep := fun e he => by
        have := hAp e _ (J.zH.2.1 e he) fun _ e => by cases e
        simpa [P1.HKind.bits] using this
      rep := fun r hr => by
        have := hAp r _ (J.zH.2.2.1 r hr) fun _ e => by cases e
        simpa [P1.HKind.bits] using this
      ntfn := fun n hn => by
        have := hAp n _ (J.zH.2.2.2 n hn) fun _ e => by cases e
        simpa [P1.HKind.bits] using this }
  have hnB : ∀ wp ∈ Z.B, wp.1 ≠ w := by
    intro wp hwp e
    obtain ⟨q, vms, hq, q1, q2⟩ := J.carry.bufPg wp hwp
    have hne : q ≠ p.bv := fun e' => by rw [e', hσx] at hq; cases hq
    have eb : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := by
      simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
    have hs := C.sep p hp q _ hq hne
    unfold EptApart at hs
    rw [eb] at hs
    rw [e] at q1 q2
    omega
  have hObj : ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ w.val ∧ w.val < o.toNat + 2 ^ Fl4Spec.objBits ko :=
    ⟨p.bv, _, hσx, g1, by
      show w.val < p.val + 2 ^ Fl4Spec.objBits (.archObj (.ept (XL p) es))
      rw [ept_bits]; have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
      rw [h12]; omega⟩
  exact ⟨hu, hnB, hAp, hObj, hksw⟩

/-- **A word of a table of `X` written at the base** (σ unchanged; `JAtZB.frameWrJ`), and the slots kept. -/
theorem JAtZB.eptWr (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : EptCore (L := L) X XL Z.th s σ)
    {p w : U64} (hp : p ∈ X) (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 4096) (v : U64) :
    JAtZB (L := L) arI AR Z H Cs Ac Lst D (L.wr s w v) a σ ∧ SlotsSame Z.th (L.mem s) (L.mem (L.wr s w v)) := by
  obtain ⟨hu, hnB, hAp, hObj, hks⟩ := J.eptUserW C hp hal g1 g2
  have hP := J.xtop.fin.1.2
  exact ⟨J.frameWrJ hu hnB hAp hObj hks v, slotsSame_wr hP.pl s v hal fun x hx ⟨h1, h2⟩ =>
    hu.vobj (vobj_of_slot hP.pl Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) hx h1 h2)⟩

set_option maxHeartbeats 4000000 in
/-- **`VcpuCore.ofWE` for any same-shape slot rewrite** (gen 42b12, `ofWE` generalised in place: each slot's cap
kept, or rewritten into a cap of the old cap's `shape` that is `VcpuCapV`-fine and no I/O-port cap — the EPT frame
map's `Frame … false → Frame … mp mp asid gpa`; `ofWE` is the corollary for `Ept` caps). -/
theorem VcpuCore.ofWG (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hcs : ∀ y, IsSlot Z.th y → capV (L.mem s') y = capV (L.mem s) y ∨
      (shape (capV (L.mem s') y) = shape (capV (L.mem s) y) ∧ VcpuCapV V (capV (L.mem s') y) ∧
        ∀ f l o, capV (L.mem s') y ≠ .IoPort f l o))
    (nV : ∀ u ∈ V, ∀ b, W b → b.val < u.val ∨ u.val + 32768 ≤ b.val) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s')
    (hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hrv : ∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM)
    (hnv : ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs))) :
    VcpuCore (L := L) V Z H s' σ' := by
  have Ly := B.jvLay C.vm
  have kV : ∀ u ∈ V, L.mem s' (vTcbA u) = L.mem s (vTcbA u) := by
    intro u hu
    have hf := Ly.vfit u hu
    have e := lay_vTcb_val hf.2
    exact hw.mem_eq (by unfold P1.Aligned; rw [e]; omega) fun hb => by
      rcases nV u hu _ hb with h | h <;> omega
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := B.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have kTV : ∀ t, Z.th t = some .tcb → L.mem s' (tVcpuA t) = L.mem s (tVcpuA t) := hv
  have E0 := C.extv
  have E' : JExtVcpu (L := L) V Z.th s' :=
    { cap := fun y hy => by
        rcases hcs y hy with e | ⟨-, hv, -⟩
        · rw [e]; exact E0.cap y hy
        · exact hv
      bnd := fun t ht => by
        rcases E0.bnd t ht with h | ⟨h1, h2⟩
        · left; rw [kTV t ht]; exact h
        · right; rw [kTV t ht]; exact ⟨h1, by rw [kV _ h1]; exact h2⟩
      back := fun v hv => by
        rcases E0.back v hv with h | ⟨h1, h2⟩
        · left; rw [kV v hv]; exact h
        · right; rw [kV v hv]; exact ⟨h1, by rw [kTV _ h1]; exact h2⟩
      nz := E0.nz }
  have R' : RunVmB (L := L) Z.th s' := by
    intro t ht h8
    rw [hv t ht]
    refine C.rvm t ht ?_
    obtain ⟨x', hk', -⟩ := B'.xtop.rel.2.1.1.tcb t ht
    have w' := (B'.xtop.fin.1.1.2.2.1.at_tcb (B'.thT t ht) hk').st
    rw [Sched.stA_tStA] at h8 ⊢
    rw [h8] at w'
    have hx' : x'.tcbState = .runningVM := by
      cases hx : x'.tcbState <;> rw [hx] at w' <;> simp_all [tsCode]
    obtain ⟨x, hk, hx⟩ := hrv _ x' hk' hx'
    have w0 := (B.xtop.fin.1.1.2.2.1.at_tcb (B.thT t ht) hk).st
    rw [hx] at w0
    apply UScalar.eq_of_val_eq
    rw [w0]; simp [tsCode]
  have Jv' : JVm (L := L) V H s' σ' :=
    C.vm.step (fun _ h => h) (fun _ _ => rfl) hw.1 (fun u hu => by rw [hvk u hu]; exact C.vm.spec u hu)
      (fun o ko' ho => Or.inl (hsz o ko' ho))
  have Vl' : VList st V Z.th s' := C.vl.writes hw fun b hb => by
    refine ⟨C.vl.lw_al Ly.vfit hb, fun hW => ?_⟩
    rcases hb with rfl | ⟨u, hu, rfl | rfl⟩
    · exact hh _ hW rfl
    · have := lay_next_val (Ly.vfit u hu).2
      rcases nV u hu _ hW with h | h <;> omega
    · have := lay_prev_val (Ly.vfit u hu).2
      rcases nV u hu _ hW with h | h <;> omega
  exact ⟨E', C.vo.frame hnv,
    C.vr.frame (fun u _ vs hu => hnv _ vs hu) (v3_agreeW (L := L) hw (fun u hu => (Ly.vfit u hu).2) nV),
    fun y hy f l o hc => by
      rcases hcs y (isSlot_thTcb hy) with e | ⟨-, -, hn⟩
      · rw [e] at hc; exact C.noIoTcb y hy f l o hc
      · exact absurd hc (hn f l o),
    VirtRngOne.rngOne_congr C.rngOne fun z hz _ => by
      rcases hcs z (hsl z hz) with e | ⟨e, -⟩
      · rw [e]; exact NoA.refl _
      · exact NoA.of_shape e,
    R', Jv', Vl', C.vb.ofV hvk kV⟩

/-- **`VcpuCore.ofW` with slot caps rewritten into `Ept` caps of the same shape** (gen 42b7, `ofW` generalised in
place: each slot's cap kept, or rewritten into an `Ept` cap of the old cap's `shape` — the EPT pool assign's
`Ept r 0 false → Ept r 0 true asid 0`; `ofW` is the corollary for `SlotsSame`; gen 42b12: the corollary of
`ofWG`). -/
theorem VcpuCore.ofWE (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hcs : ∀ y, IsSlot Z.th y → capV (L.mem s') y = capV (L.mem s) y ∨
      (shape (capV (L.mem s') y) = shape (capV (L.mem s) y) ∧
        ∃ (p l : U64) (mm : Bool) (a v : U64), capV (L.mem s') y = .Ept p l mm a v))
    (nV : ∀ u ∈ V, ∀ b, W b → b.val < u.val ∨ u.val + 32768 ≤ b.val) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s')
    (hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hrv : ∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM)
    (hnv : ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs))) :
    VcpuCore (L := L) V Z H s' σ' :=
  C.ofWG B B' hw (fun y hy => (hcs y hy).imp id fun ⟨h1, p, l, mm, a, v, e⟩ =>
    ⟨h1, by rw [e]; trivial, fun f l' o h => by rw [e] at h; cases h⟩) nV hh hv hvk hsz hrv hnv


/-- **`VcpuCore` across writes off the VCPUs, the list head and the TCB VCPU words, slots kept** (`VcpuCore.ofBS`
with its `OObj` facts as hypotheses; module docstring). Gen 42b7: the `SlotsSame` case of `VcpuCore.ofWE`. -/
theorem VcpuCore.ofW (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (C : VcpuCore (L := L) V Z H s σ)
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (nV : ∀ u ∈ V, ∀ b, W b → b.val < u.val ∨ u.val + 32768 ≤ b.val) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s')
    (hvk : ∀ u ∈ V, σ'.kheap u.bv = σ.kheap u.bv)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hrv : ∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM)
    (hnv : ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs))) :
    VcpuCore (L := L) V Z H s' σ' :=
  C.ofWE B B' hw (fun y hy => Or.inl (hSS.capV hy)) nV hh hv hvk hsz hrv hnv

end

/-! ## `VmEptState` across one table word -/

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched

set_option maxHeartbeats 4000000 in
/-- **`VmEptState` across one word of a table of `X`** (module docstring; σ unchanged): the word `eptA t0 i0` written
with a value outside the relation (root entry ≥ 256) or equal to the old one up to `eptHw`. -/
theorem VmEptState.wrIn (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {t0 : U64} (ht0 : t0 ∈ X)
    {i0 : BitVec 9} (v : U64)
    (hU : (XL t0 = 0 ∧ 256 ≤ i0.toNat) ∨ EptWord Fl4Spec.virtKind v.bv (L.mem s (eptA t0 i0)).bv)
    (hz : ∀ y l aa vv, IsSlot Z.th y → capV (L.mem s) y = .Ept t0 l false aa vv → v = 0#u64) :
    VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D (L.wr s (eptA t0 i0) v) a σ := by
  obtain ⟨⟨B, Cv⟩, C⟩ := J
  have hp := C.rel.place t0 ht0
  have e := eptA_val hp.2 i0
  have hi9 := i0.isLt
  have hal : P1.Aligned (eptA t0 i0) := by unfold P1.Aligned; rw [e]; omega
  obtain ⟨B', hSS⟩ := B.eptWr C ht0 hal (by rw [e]; omega) (by rw [e]; omega) v
  have hw : P1.WritesIn st s (L.wr s (eptA t0 i0) v) (· = eptA t0 i0) := P1.writesIn_wr hal
  have hmem : L.mem (L.wr s (eptA t0 i0) v) (eptA t0 i0) = v := by
    rw [L.mem_wr s _ v _ hal hal, if_pos rfl]
  -- the write misses the VCPUs, the list head and the TCB VCPU words
  have nV : ∀ u ∈ V, ∀ b, b = eptA t0 i0 → b.val < u.val ∨ u.val + 32768 ≤ b.val := by
    intro u hu b hb
    subst hb
    rcases C.apartV Cv.vm t0 ht0 u hu with h | h <;> omega
  have hh : ∀ b, b = eptA t0 i0 → b ≠ P1.vHeadA st s := by
    intro b hb he
    subst hb
    have h2 : (eptA t0 i0).val = (P1.vHeadA st s).val := by rw [he]
    rcases B.eptHead C ht0 with h | h <;> omega
  obtain ⟨Q, R0, hcq, -⟩ := B.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  have hv : VKeep (L := L) Z.th s (L.wr s (eptA t0 i0) v) := by
    intro t ht
    have htT := B.thT t ht
    have ev := tVcpuA_val hT htT
    refine hw.mem_eq (tVcpuA_aligned hT htT) fun he => ?_
    have hO : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ (tVcpuA t) :=
      Or.inr (Or.inr (Or.inl ⟨t, htT, by omega, by omega⟩))
    have h2 : (tVcpuA t).val = (eptA t0 i0).val := by rw [he]
    rcases B.oobjX C ht0 hO with h | h <;> omega
  refine ⟨⟨B', Cv.ofW B B' hw hSS nV hh hv (fun _ _ => rfl) (fun o ko' ho => ⟨ko', ho, rfl⟩)
    (fun o x' ho hx => ⟨x', ho, hx⟩) (fun _ _ h => h)⟩, C.wrIn hSS ht0 hw ?_
      fun y l aa vv hy hc => by rw [hmem]; exact hz y l aa vv hy hc⟩
  rw [hmem]; exact hU

/-- **Guest execution** (module docstring): a hardware write of accessed / dirty bits (`eptHw`) to a word of a table of
`X` keeps `VmEptState`, σ unchanged. The walker sets A/D only in a present entry it used (`h0`: a zero word stays
zero; gen 42b2, for `UnmappedEmpty`). -/
theorem VmEptState.hwWr (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {t0 : U64} (ht0 : t0 ∈ X)
    {i0 : BitVec 9} (v : U64) (hU : EptWord Fl4Spec.virtKind v.bv (L.mem s (eptA t0 i0)).bv)
    (h0 : L.mem s (eptA t0 i0) = 0#u64 → v = 0#u64) :
    VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D (L.wr s (eptA t0 i0) v) a σ :=
  J.wrIn ht0 v (Or.inr hU) fun y l aa vv hy hc => h0 ((J.2.ue y hy t0 l aa vv hc).1 i0)

end

end

/-! ## `mark_core` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **`ept::mark_core`** (ept.rs l. 43-54): with the CPU below 64 and the root's 4 KiB in the address space, it
writes nothing or the root word `510 + ⌊cpu / 32⌋`. -/
theorem ept_markCore (s : S) {root : U64} (hc : (L.cpu s).val < 64) (hr : root.val + 4096 ≤ 2 ^ 64) :
    ept.mark_core st s root = ok s ∨
      ∃ v, ept.mark_core st s root = ok (L.wr s (eptA root (BitVec.ofNat 9 (510 + (L.cpu s).val / 32))) v) := by
  unfold ept.mark_core
  rw [L.cur_cpu_eq, bind_ok]
  obtain ⟨c, hce, hcv⟩ := spec_exists (U64.mul_spec (x := 510#u64) (y := 8#u64) (by scalar_tac))
  have hC : ept.CORES = ok c := by unfold ept.CORES; exact hce
  rw [hC, bind_ok]
  simp only [lift, bind_ok]
  obtain ⟨d, hde, hdv⟩ := spec_exists (U64.div_spec (x := L.cpu s) (y := 32#u64) (by decide))
  rw [hde, bind_ok]
  have hd : d.val = (L.cpu s).val / 32 := by have := hdv; simp at this; omega
  obtain ⟨e, hee, hev⟩ := spec_exists (U64.mul_spec (x := d) (y := 8#u64) (by scalar_tac))
  rw [hee, bind_ok]
  have he : e.val = 8 * ((L.cpu s).val / 32) := by have := hev; simp at this; omega
  have hcv' : c.val = 4080 := by have := hcv; simp at this; omega
  try simp only [lift, bind_ok]
  rw [L.read_eq, bind_ok]
  obtain ⟨m, hme, hmv⟩ := spec_exists (UScalar.rem_spec (L.cpu s) (y := 32#u64) (by decide))
  rw [hme, bind_ok]
  have hm : m.val = (L.cpu s).val % 32 := by rw [hmv]; rfl
  obtain ⟨k, hke, hkv⟩ := spec_exists (U64.add_spec (x := 32#u64) (y := m) (by scalar_tac))
  rw [hke, bind_ok]
  have hk : k.val = 32 + (L.cpu s).val % 32 := by have := hkv; simp at this; omega
  obtain ⟨b, hbe, -, -⟩ := spec_exists (UScalar.ShiftLeft_spec (1#u64 : U64) k _
    (by rw [hk]; simp [UScalarTy.U64_numBits_eq] <;> omega) rfl)
  rw [hbe, bind_ok]
  try simp only [lift, bind_ok]
  -- the address
  have hi : (BitVec.ofNat 9 (510 + (L.cpu s).val / 32)).toNat = 510 + (L.cpu s).val / 32 := by
    rw [BitVec.toNat_ofNat]; omega
  have ha : core.num.U64.wrapping_add (core.num.U64.wrapping_add root c) e =
      eptA root (BitVec.ofNat 9 (510 + (L.cpu s).val / 32)) := by
    apply UScalar.eq_of_val_eq
    rw [eptA_val hr, hi, Sched.wadd_val' (by rw [Sched.wadd_val' (by omega), he, hcv']; omega),
      Sched.wadd_val' (by omega), he, hcv']
    omega
  rw [ha]
  by_cases hn : (L.mem s (eptA root (BitVec.ofNat 9 (510 + (L.cpu s).val / 32))) !=
      (L.mem s (eptA root (BitVec.ofNat 9 (510 + (L.cpu s).val / 32))) ||| b)) = true
  · rw [if_pos hn, L.write_eq]; exact Or.inr ⟨_, rfl⟩
  · rw [if_neg hn]; exact Or.inl rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}
  {XL : U64 → Nat}

/-- **`mark_core` at `VmEptState`** (module docstring; σ unchanged): for a root a slot names at level 0 (the call site's
`ept::root` on the thread's `SLOT_EPT` cap). -/
theorem VmEptState.markCore (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {y root asid vv : U64}
    (hy : IsSlot Z.th y) (hc : capV (L.mem s) y = .Ept root 0#u64 true asid vv) :
    ∃ s', ept.mark_core st s root = ok s' ∧ VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s' a σ := by
  obtain ⟨hX, h0⟩ := J.2.ofCap hy hc
  have hcpu : (L.cpu s).val < 64 := J.1.1.kern.csLt _ J.1.1.kern.cpuCs
  have hr := (J.2.rel.place root hX).2
  rcases ept_markCore (st := st) s hcpu hr with h | ⟨v, h⟩
  · exact ⟨s, h, J⟩
  · refine ⟨_, h, J.wrIn hX v (Or.inl ⟨h0, ?_⟩) fun y' l aa vv' hy' hc' => ?_⟩
    · rw [BitVec.toNat_ofNat]; omega
    · -- the root's mapped cap at `y` and an unmapped one at `y'`: `UnmappedEmpty`'s uniqueness
      have hne : y ≠ y' := fun e => by subst e; rw [hc] at hc'; cases hc'
      exact absurd hc ((J.2.ue y' hy' root l aa vv' hc').2.2.1 y hy hne 0#u64 true asid vv)

end

end

end Fl4Proofs.P3

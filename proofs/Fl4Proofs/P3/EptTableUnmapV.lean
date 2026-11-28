/-
P3 (line mmuAD, gen 42b14): **the EPT table unmap at `VmEptState`** — the perform half after P3/EptTableUnmapDec's
decode: FL4's `ept::decode` unmap arm (crates/fl4-core/src/ept.rs l. 265-283: `is_final_capability`, the caller's
restart, when mapped `ept::unmap(asid, gpa, ptr, level, true)` and `s.zero(ptr, 4096)`, then `set_cap` of
`Ept { mapped: false, asid: 0, vaddr: 0 }`) against the extended spec's `decodeEptInvocation` then
`setThreadState cur Restart` and `performEptInvocation (.tableUnmap …)` (Fl4Spec/Ext/VirtEptInv l. 154-159,
l. 227-233), modelled on P3/EptTableMapV.

* **`VmEptState.unmapEntry`** (the hit of `ept::unmap`): FL4's `wr s (eptA t i) 0` and the spec's
  `storeGuestEntry t i 0` at a table `t ∈ X` on the walk path: P3/EptStep1's `JAtZB.eptWr`, P3/JAtZBVcpuX's
  `XTopAt.archSpec` + `JAtZB.arFrS`, `VcpuCore.ofW`, P3/EptFrameMap's **`EptCore.frameEntryG`** (gen 42b14:
  `frameEntry` generalised in place to the root's level).
* **`VmEptState.unmapClear`**: the zeroing of the unmapped table `ptr` (FL4 writes in `ptr`'s frame with its words
  zero after, spec `.ept (XL ptr) 0`) and the `set_cap` / `setCap` of `dest`'s unmapped cap, from a state where
  `dest` is the unique cap to `ptr` and `ptr` is unreachable: `XTopAt.archSpec` + `JAtZB.arFrS` (spec zero),
  P3/UtResetZ's `XTopAt.userWs` (FL4 zero: each word a `UserW` word by `JAtZB.eptUserW`, `UserW.ofSc` for the spec
  step), `XTopAt.slotStep` and P3/JAtZBRecap's `JAtZB.vsStepJXB` with the off-set frame `{ptr}` (`TabsArch`);
  `VcpuCore.ofWE`; P3/EptUnmapCore's `EptCore.clearZ` then `EptCore.unmapSlot`. The `Ept` caps' `VsLike` by
  P3/EptAssignJ's **`vsLike_eptG`** (gen 42b14: `vsLike_ept` generalised in place to any mapped flags).
* **`VmEptState.tableUnmap`** — the top: from `VmEptState` at an `Entered` spec state, the invoked
  `Ept ptr level m asid va` cap (`level ≠ 0`) in a CNode slot, the unmap label and FL4's finality of the slot: the
  spec decoder's single outcome `.tableUnmap ptr level mapped slot`, and FL4's `ept.decode` ⦃ `Ok ()`, and for some
  `σ'` the restart + perform has the single outcome `σ'` (`EptTableUnmapSpec`) and `VmEptState` holds at FL4's state
  and arch after and `σ'` ⦄. Finality gives `huq` (no other slot names `ptr`: P3/FinDefs' `finF_iff`); mapped:
  P3/EptUnmapCore's `EptCore.unmapUnreach` (the spec's outcome and `ptr` unreachable after); unmapped: `ue` gives
  `ptr` zero on both sides and `unmUnreach` its unreachability, and the spec does nothing (`performTableUnmap_none`)
  while FL4's rewrite `Ept … false a v → Ept … false 0 0` keeps the abstract cap (`setCnodeSlot_self`).
* **`eptTableUnmap_decode_vmEpt`**: the same through `syscall.decode_invocation` and the extended decoder
  `fl4DecodeInvocationV` (P3/JAtZV3EptE's `zv_sysdec_ept` / `zv_decV_ept`).

Premise: `ArchRefines arI AR` [P] (as P3/EptUnmapRel). No new named premise. New file; root import after
`P3.EptUnmapCore`.
-/
import Fl4Proofs.P3.EptUnmapCore
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
  Fl4Proofs.P1

/-- `UserW` across a spec step keeping the SCs. -/
theorem UserW.ofSc {s : S} {σ σ' : Fl4Spec.State Unit} {b : U64} (hu : UserW (L := L) Z s σ b)
    (hsc : ∀ p x n, σ'.kheap p = some (.schedContext x n) → σ.kheap p = some (.schedContext x n)) :
    UserW (L := L) Z s σ' b :=
  ⟨hu.al, ⟨hu.far.1, hu.far.2.1, fun sc hsc' x n hk => hu.far.2.2 sc hsc' x n (hsc _ x n hk)⟩, hu.vobj, hu.ep,
    hu.rep, hu.ntfn⟩

set_option maxHeartbeats 4000000 in
/-- **`VmEptState` across the hit of `ept::unmap`** (module docstring). -/
theorem VmEptState.unmapEntry (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ X)
    {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex} {g : Fl4Spec.Word} (hg : g.toNat < 2 ^ 47)
    (hp : GPath σ hi lo g (XL t) t.bv) {es : BitVec 9 → Fl4Spec.Word}
    (hk : σ.kheap t.bv = some (.archObj (.ept (XL t) es))) (i : BitVec 9) :
    VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D (L.wr s (eptA t i) 0#u64) a
      (updK σ t.bv (.archObj (.ept (XL t) (Function.update es i 0)))) ∧
    SlotsSame Z.th (L.mem s) (L.mem (L.wr s (eptA t i) 0#u64)) := by
  have B := J.1.1
  have Cv := J.1.2
  have C := J.2
  set w := eptA t i with hw
  set σ2 := updK σ t.bv (.archObj (.ept (XL t) (Function.update es i 0))) with hσ2
  have hpl := C.rel.place t ht
  have ew : w.val = t.val + 8 * i.toNat := eptA_val hpl.2 i
  have hi9 := i.isLt
  have hal : P1.Aligned w := by unfold P1.Aligned; rw [ew]; omega
  obtain ⟨B2, hSS2⟩ := B.eptWr C ht hal (by rw [ew]; omega) (by rw [ew]; omega) 0#u64
  have hX2 : XTopAt (L := L) AR Z (L.wr s w 0#u64) a σ2 :=
    B2.xtop.archSpec hk (Or.inr ⟨_, _, rfl⟩) (.ept (XL t) (Function.update es i 0)) rfl
  have B2' : JAtZB (L := L) arI AR Z H Cs Ac Lst D (L.wr s w 0#u64) a σ2 :=
    B2.arFrS (arFr_arch hk (.ept (XL t) (Function.update es i 0)) rfl) hX2
  have hk2t : σ2.kheap t.bv = some (.archObj (.ept (XL t) (Function.update es i 0))) := by simp [hσ2, updK]
  have hoth2 : ∀ q, q ≠ t.bv → σ2.kheap q = σ.kheap q := fun q hq => by simp [hσ2, updK, hq]
  have hw12 : P1.WritesIn st s (L.wr s w 0#u64) (· = w) := P1.writesIn_wr hal
  obtain ⟨Q, R0, hcq, -⟩ := B.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  have nV : ∀ u ∈ V, ∀ b, b = w → b.val < u.val ∨ u.val + 32768 ≤ b.val := by
    intro u hu b hb
    subst hb
    rcases C.apartV Cv.vm t ht u hu with h | h <;> omega
  have hh : ∀ b, b = w → b ≠ P1.vHeadA st s := by
    intro b hb he
    subst hb
    have h2 : w.val = (P1.vHeadA st s).val := by rw [he]
    rcases B.eptHead C ht with h | h <;> omega
  have hv : VKeep (L := L) Z.th s (L.wr s w 0#u64) := by
    intro t' ht'
    have htT := B.thT t' ht'
    have ev := tVcpuA_val hT htT
    refine hw12.mem_eq (tVcpuA_aligned hT htT) fun he => ?_
    have hO : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ (tVcpuA t') :=
      Or.inr (Or.inr (Or.inl ⟨t', htT, by omega, by omega⟩))
    have h2 : (tVcpuA t').val = w.val := by rw [he]
    rcases B.oobjX C ht hO with h | h <;> omega
  have hvt : ∀ u ∈ V, u.bv ≠ t.bv := fun u hu e => by
    obtain ⟨vx, hvx⟩ := Cv.vm.spec u hu
    rw [e, hk] at hvx; cases hvx
  have Cv2 : VcpuCore (L := L) V Z H (L.wr s w 0#u64) σ2 :=
    Cv.ofW B B2' hw12 hSS2 nV hh hv (fun u hu => hoth2 _ (hvt u hu))
      (fun o ko' ho => by
        by_cases e : o = t.bv
        · subst e; rw [hk2t] at ho; cases ho
          exact ⟨_, hk, by rw [ept_bits, ept_bits]⟩
        · rw [hoth2 _ e] at ho; exact ⟨ko', ho, rfl⟩)
      (fun o x' ho hx => by
        have e : o ≠ t.bv := fun e => by rw [e, hk2t] at ho; cases ho
        rw [hoth2 _ e] at ho; exact ⟨x', ho, hx⟩)
      (fun p vs hp => by
        have e : p ≠ t.bv := fun e => by rw [e, hk2t] at hp; cases hp
        rw [hoth2 _ e] at hp; exact hp)
  have hmw : L.mem (L.wr s w 0#u64) w = 0#u64 := by rw [L.mem_wr s _ _ _ hal hal, if_pos rfl]
  have C2 : EptCore (L := L) X XL Z.th (L.wr s w 0#u64) σ2 :=
    C.frameEntryG ht hg hp hk (fun h => h.2.2.1 (by simp)) hw12 (by unfold EptWord; rw [hmw]; rfl) hk2t hoth2 rfl
      hSS2
  exact ⟨⟨⟨B2', Cv2⟩, C2⟩, hSS2⟩

set_option maxHeartbeats 4000000 in
/-- **`VmEptState` across the zeroing of the unmapped table and the unmapped cap's `set_cap`** (module docstring):
`dest = cslotAddr (pc, idx)` holds the unique `Ept ptr lv` cap, `ptr` is unreachable; FL4 writes `ptr`'s frame,
`s4` has its words zero; the spec clears `ptr` and sets the slot to the unmapped cap. -/
theorem VmEptState.unmapClear (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr lv a0 v0 : U64} {mm0 : Bool} (hcv : capV (L.mem s) (cslotAddr (pc.bv, idx)) = .Ept ptr lv mm0 a0 v0)
    (hlv : lv.val ≠ 0)
    (huq : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pc.bv, idx) → ∀ l (mm : Bool) a v, capV (L.mem s) y ≠ .Ept ptr l mm a v)
    (hun : ∀ hi lo g l, g.toNat < 2 ^ 47 → l ≠ 0 → ¬ GPath σ hi lo g l ptr.bv)
    {s4 : S} (hw : P1.WritesIn st s s4 (fun b => ptr.val ≤ b.val ∧ b.val < ptr.val + 4096))
    (hwP : P1.WritesIn st s s4 (PtW {ptr})) (hz : ∀ i : BitVec 9, L.mem s4 (eptA ptr i) = 0#u64) :
    ∃ cs, σ.kheap pc.bv = some (.cnode r cs) ∧ Fl4Spec.wellFormedCnodeN r cs ∧
      VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D
        (wrCap (L := L) s4 (cslotAddr (pc.bv, idx)) (.Ept ptr lv false 0#u64 0#u64)) a
        (setCnodeSlot (updK σ ptr.bv (.archObj (.ept (XL ptr) fun _ => 0))) pc.bv r cs idx
          (.archObjectCap (.eptCap ptr.bv lv.val none))) := by
  have B := J.1.1
  have Cv := J.1.2
  have C := J.2
  set x := cslotAddr (pc.bv, idx) with hxdef
  have hP : Placed Z.th := B.xtop.rel.1
  have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hxs : IsSlot Z.th x := hA.isSlot
  have hpX : ptr ∈ X := by have h := C.exte.cap x hxs; rw [hcv] at h; exact h
  obtain ⟨esp, hkp, -⟩ := C.rel.obj ptr hpX
  have hpl := C.rel.place ptr hpX
  have hxa : ∀ b, SlotWd Z.th b → ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val := B.slotWd_ept C
  -- the zeroing keeps the slots
  have hSS4 : SlotsSame Z.th (L.mem s) (L.mem s4) := SlotsSame.of_wd fun y hy k hk =>
    hw.mem_eq (slot_word_aligned hP hy hk) fun hb => by
      rcases hxa _ ⟨y, hy, k, hk, rfl⟩ ptr hpX with h | h <;> omega
  -- the spec's zeroing
  obtain ⟨cs, hkc, hwf, -⟩ := B.xtop.rel.2.1.1.cnode pc r hpc
  have hppc : ptr.bv ≠ pc.bv := kheap_ne hkp hkc (fun _ h1 h2 => by subst h1; cases h2)
  set σ3 := updK σ ptr.bv (.archObj (.ept (XL ptr) fun _ => 0)) with hσ3
  have hk3p : σ3.kheap ptr.bv = some (.archObj (.ept (XL ptr) fun _ => 0)) := by simp [hσ3, updK]
  have hoth3 : ∀ q, q ≠ ptr.bv → σ3.kheap q = σ.kheap q := fun q hq => by simp [hσ3, updK, hq]
  have hkc3 : σ3.kheap pc.bv = some (.cnode r cs) := by rw [hoth3 _ hppc.symm]; exact hkc
  have hX3 : XTopAt (L := L) AR Z s a σ3 := B.xtop.archSpec hkp (Or.inr ⟨_, _, rfl⟩) _ rfl
  have B3 : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ3 := B.arFrS (arFr_arch hkp _ rfl) hX3
  -- FL4's zeroing at `XTopAt`
  have hfr : ∀ b, PtW {ptr} b → ptr.val ≤ b.val ∧ b.val + 8 ≤ ptr.val + 4096 ∧ b.val % 8 = 0 := by
    rintro b ⟨q, hq, i, hi, rfl⟩
    rw [Set.mem_singleton_iff.1 hq]
    have hv := peA_val (tbl_fit hpl.1) hi
    exact ⟨by omega, by omega, by omega⟩
  have hEU : ∀ b, PtW {ptr} b → UserW (L := L) Z s σ b ∧ ∀ wp ∈ Z.B, wp.1 ≠ b := by
    intro b hb
    obtain ⟨g1, g2, g3⟩ := hfr b hb
    obtain ⟨hu, hnB, -⟩ := B.eptUserW C hpX (w := b) g3 g1 (by omega)
    exact ⟨hu, hnB⟩
  have hsc3 : ∀ p x n, σ3.kheap p = some (.schedContext x n) → σ.kheap p = some (.schedContext x n) := by
    intro p x' n hk'
    by_cases e : p = ptr.bv
    · subst e; rw [hk3p] at hk'; cases hk'
    · rw [hoth3 _ e] at hk'; exact hk'
  have hX4 : XTopAt (L := L) AR Z s4 a σ3 :=
    hX3.userWs hwP (fun b hb => (hEU b hb).1.ofSc hsc3) (fun wp hwp hb => (hEU _ hb).2 wp hwp rfl)
  -- the `set_cap` / `setCap` pair
  have hcv4 : capV (L.mem s4) x = .Ept ptr lv mm0 a0 v0 := by rw [hSS4.capV hxs]; exact hcv
  have hcx4 : capAt (L.mem s4) x = ok (.Ept ptr lv mm0 a0 v0) := by rw [capAt_capV, hcv4]
  have hcl := hcx4
  rw [capAt_words] at hcl
  have hew0 := decode_encWf hcl
  set c : capability.Cap := .Ept ptr lv false 0#u64 0#u64 with hc
  set nc : Fl4Spec.Cap := .archObjectCap (.eptCap ptr.bv lv.val none) with hnc
  have hew : EncWf c := ⟨hew0.1, hew0.2.1, by decide, by decide⟩
  have hca : CapRel c nc := ⟨trivial, rfl⟩
  obtain ⟨hSt4, hSV4, -, -, -⟩ := hX4.rel.2.1
  have hSC := set_cap_refines (L := L) Z.th s4 σ3 hSt4 hSV4 hP hpc hidx c nc hca trivial hew
  rw [set_cap_eq, WP.spec_ok] at hSC
  obtain ⟨σ5, hsc, hSt5, hSV5, -, -, -, -⟩ := hSC
  have hσ5 : σ5 = setCnodeSlot σ3 pc.bv r cs idx nc := by
    rw [setCap_cnode nc hkc3 hwf hidx] at hsc
    have := congrArg Prod.fst hsc
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst hσ5
  set s5 := wrCap (L := L) s4 x c with hs5
  have hF5 := set_cap_foot (L := L) hP hxs s4 c hew
  rw [set_cap_eq, WP.spec_ok] at hF5
  obtain ⟨hSF5, hcv5⟩ := hF5
  have hfx := hxs.fit hP
  have hal32 := hxs.align hP
  have hWF := set_cap_frame (L := L) s4 x c (by omega) (by omega)
  rw [set_cap_eq, WP.spec_ok] at hWF
  have h8 : (wordOf x 8#u64).val = x.val + 8 := wa8_val (by omega)
  have hW5 : P1.WritesIn st s4 s5 (fun b => b = x ∨ b = wordOf x 8#u64) := by
    refine ⟨hWF.1, hWF.2.1, fun b hb hn => hWF.2.2 b hb fun hr => hn (by
      obtain ⟨g1, g2⟩ := hr
      have hb8 : b.val % 8 = 0 := hb
      by_cases e : b.val = x.val
      · exact Or.inl (UScalar.eq_of_val_eq e)
      · exact Or.inr (UScalar.eq_of_val_eq (by rw [h8]; omega)))⟩
  have hks5 : L.ksb s5 = L.ksb s := hW5.1.trans hw.1
  have hcap5 : ∀ y, IsSlot Z.th y → y ≠ x → capV (L.mem s5) y = capV (L.mem s4) y := fun y hy hne => by
    unfold capV; rw [((hSF5 y hy).2.2 hne).1, ((hSF5 y hy).2.2 hne).2]
  have hcap35 : ∀ y, IsSlot Z.th y → y ≠ x → capV (L.mem s5) y = capV (L.mem s) y := fun y hy hne => by
    rw [hcap5 y hy hne, hSS4.capV hy]
  have hLk : VsLike (capV (L.mem s5) x) (capV (L.mem s4) x) := by
    rw [hcv5, hcv4]; exact vsLike_eptG ptr lv false 0#u64 0#u64 mm0 a0 v0
  have hK5 : KFoot σ3 (setCnodeSlot σ3 pc.bv r cs idx nc) := KFoot.cnode hkc3 hwf idx nc
  obtain ⟨-, hCR4, hFI4, -, hMO4, -, -⟩ := hX4.rel
  obtain ⟨hCR5, hFI5, hMO5⟩ := crelM_after hCR4 hFI4 hMO4 hcx4 hSt5 hSV5 hSF5 (by rw [← hcv4]; exact hLk) hK5 rfl
  have hTS : ∀ t', Z.th t' = some .tcb → capAt (L.mem s5) (slotOf t' 1) = capAt (L.mem s4) (slotOf t' 1) := by
    intro t' ht'
    have hs : IsSlot Z.th (slotOf t' 1) := ⟨t', 1, Or.inr ⟨ht', by simp [tcbSlots]⟩, rfl⟩
    have he : cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 1) = slotOf t' 1 := by
      show slotAddr t'.bv (Fl4Spec.ofBl _) = _
      rw [slotAddr_ofBl, tcbCnodeIndex_blVal 1 (by decide)]
    have hne : slotOf t' 1 ≠ x := fun e => cnode_slot_ne_tcb hP hpc hidx ht' 1 (by decide) (by rw [he, e])
    rw [capAt_capV, capAt_capV, hcap5 _ hs hne]
  have hSW : ∀ b, (b = x ∨ b = wordOf x 8#u64) → SlotWd Z.th b := by
    rintro b (rfl | rfl)
    · exact ⟨x, hxs, 0#u64, Or.inl rfl, by rw [wordOf_zero]⟩
    · exact ⟨x, hxs, 8#u64, Or.inr (Or.inl rfl), rfl⟩
  have hX5 : XTopAt (L := L) AR { Z with G := Z.G } s5 a (setCnodeSlot σ3 pc.bv r cs idx nc) :=
    XTopAt.slotStep hX4 (hW5.mono hSW) (cnK_setCnodeSlot hkc3 hwf hidx nc) (keepC_setCnodeSlot hkc3 nc)
      hCR5 hFI5 hMO5 hTS
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s5) := fun y hy => by
    by_cases e : y = x
    · rw [e, hcv5]; trivial
    · rw [hcap35 y hy e]; exact B3.vsc y hy
  have hvn : Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s5) (L.ksb s5) :=
    B3.vsShr (G' := Z.G) hX5 hks5 (VsKeep.of_vk fun y hy => by
      by_cases e : y = x
      · rw [e, hcv5, hcv]; exact ⟨rfl, rfl⟩
      · rw [hcap35 y hy e]; exact ⟨rfl, rfl⟩)
      (ArchShr.of_keep rfl fun q ao hq => by
        have hq' : q ≠ pc.bv := fun e => by rw [e, hkc3] at hq; cases hq
        simp [setCnodeSlot, hq'])
  have hXa : TabsArch {ptr} σ3 := fun q hq => by
    rw [Set.mem_singleton_iff.1 hq]
    exact ⟨hpl.1, _, hk3p, ept_bits _ _⟩
  have hW35 : P1.WritesIn st s s5 (fun b => VsXW Z (L.ksb s) x b ∨ PtW {ptr} b) :=
    (hwP.trans hW5).mono fun b hb => hb.elim Or.inr fun h => Or.inl (Or.inr h)
  have B' : JAtZB (L := L) arI AR Z H Cs Ac Lst D s5 a (setCnodeSlot σ3 pc.bv r cs idx nc) :=
    B3.vsStepJXB ⟨B3.scOut⟩ hpc hidx hXa (L3' := Z.L3) (L2' := Z.L2) (L1' := Z.L1) hX5
      (vsSFr_setCnodeSlot hkc3 hwf hidx nc) hW35 hcap35
      (by rw [hcv5, hcv]; exact (vsLike_eptG ptr lv false 0#u64 0#u64 mm0 a0 v0).1.1)
      (by rw [hcv5, hcv]; exact (vsLike_eptG ptr lv false 0#u64 0#u64 mm0 a0 v0).1.2.1)
      (by rw [hcv]; rfl)
      (fun y hy => ⟨((hSF5 y hy).1).trans (hSS4 y hy).2.2.1, ((hSF5 y hy).2.1).trans (hSS4 y hy).2.2.2⟩) hvc
      ⟨subset_rfl, subset_rfl, subset_rfl⟩ hvn
  -- `VcpuCore`
  obtain ⟨Q, R0, hcq, -⟩ := B.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  have hW15 : P1.WritesIn st s s5 (fun b => PtW {ptr} b ∨ (b = x ∨ b = wordOf x 8#u64)) := hwP.trans hW5
  have hothc : ∀ q, q ≠ pc.bv → (setCnodeSlot σ3 pc.bv r cs idx nc).kheap q = σ3.kheap q :=
    fun q hq => by simp [setCnodeSlot, hq]
  have hoth5 : ∀ q, q ≠ pc.bv → q ≠ ptr.bv → (setCnodeSlot σ3 pc.bv r cs idx nc).kheap q = σ.kheap q :=
    fun q h1 h2 => by rw [hothc q h1, hoth3 q h2]
  have hvpc : ∀ u ∈ V, u.bv ≠ pc.bv ∧ u.bv ≠ ptr.bv := fun u hu => by
    obtain ⟨vx, hvx⟩ := Cv.vm.spec u hu
    exact ⟨fun e => (by rw [e, hkc] at hvx; cases hvx), fun e => (by rw [e, hkp] at hvx; cases hvx)⟩
  have hko : ∀ o ko', (setCnodeSlot σ3 pc.bv r cs idx nc).kheap o = some ko' →
      (o = pc.bv ∧ ∃ cs', ko' = .cnode r cs') ∨ (o = ptr.bv ∧ ko' = .archObj (.ept (XL ptr) fun _ => 0)) ∨
      σ.kheap o = some ko' := by
    intro o ko' ho
    by_cases e1 : o = pc.bv
    · subst e1
      simp only [setCnodeSlot, Function.update_self, Option.some.injEq] at ho
      exact Or.inl ⟨rfl, _, ho.symm⟩
    · by_cases e2 : o = ptr.bv
      · subst e2; rw [hothc _ e1, hk3p] at ho; cases ho; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rw [hoth5 _ e1 e2] at ho; exact Or.inr (Or.inr ho)
  have Cv' : VcpuCore (L := L) V Z H s5 (setCnodeSlot σ3 pc.bv r cs idx nc) :=
    Cv.ofWE B B' hW15
      (fun y hy => by
        by_cases e : y = x
        · right; rw [e]
          exact ⟨by rw [hcv5, hcv]; exact (vsLike_eptG ptr lv false 0#u64 0#u64 mm0 a0 v0).1.1, _, _, _, _, _, hcv5⟩
        · exact Or.inl (hcap35 y hy e))
      (fun u hu b hb => by
        rcases hb with hb | hb
        · obtain ⟨g1, g2, -⟩ := hfr b hb
          rcases C.apartV Cv.vm ptr hpX u hu with h | h <;> omega
        · exact B.slotWd_vcpu Cv.vm (hSW b hb) u hu)
      (fun b hb => by
        rcases hb with hb | hb
        · obtain ⟨g1, g2, -⟩ := hfr b hb
          intro he
          rw [he] at g1 g2
          rcases B.eptHead C hpX with h | h <;> omega
        · exact B.slotWd_head (hSW b hb))
      (fun t' ht' => by
        have htT := B.thT t' ht'
        have ev := tVcpuA_val hT htT
        refine hW15.mem_eq (tVcpuA_aligned hT htT) fun hb => ?_
        rcases hb with hb | hb
        · obtain ⟨g1, g2, -⟩ := hfr _ hb
          have hO : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ (tVcpuA t') :=
            Or.inr (Or.inr (Or.inl ⟨t', htT, by omega, by omega⟩))
          rcases B.oobjX C hpX hO with h | h <;> omega
        · exact B.slotWd_tcb (hSW _ hb) ht' (by omega) (by omega) rfl)
      (fun u hu => hoth5 _ (hvpc u hu).1 (hvpc u hu).2)
      (fun o ko' ho => by
        rcases hko o ko' ho with ⟨rfl, cs', rfl⟩ | ⟨rfl, rfl⟩ | h
        · exact ⟨_, hkc, rfl⟩
        · exact ⟨_, hkp, by rw [ept_bits, ept_bits]⟩
        · exact ⟨ko', h, rfl⟩)
      (fun o x' ho hx => by
        rcases hko o _ ho with ⟨-, cs', h⟩ | ⟨-, h⟩ | h
        · cases h
        · cases h
        · exact ⟨x', h, hx⟩)
      (fun p vs hp => by
        rcases hko p _ hp with ⟨-, cs', h⟩ | ⟨-, h⟩ | h
        · cases h
        · cases h
        · exact h)
  -- `EptCore`
  have C3 : EptCore (L := L) X XL Z.th s4 σ3 := C.clearZ hpX hw (fun b hb => hb) hz hSS4
  have hpa : ∀ hi lo e, PoolAt σ3 hi lo e → PoolAt σ hi lo e := by
    rintro hi lo e ⟨q, f, g1, g2, g3⟩
    have hq : q ≠ ptr.bv := fun e' => by subst e'; rw [hk3p] at g2; cases g2
    exact ⟨q, f, g1, by rw [← hoth3 q hq]; exact g2, g3⟩
  have hobj : ∀ r l es, σ3.kheap r = some (.archObj (.ept l es)) →
      σ.kheap r = some (.archObj (.ept l es)) ∨ es = fun _ => 0 := by
    intro r l es hk
    by_cases hr : r = ptr.bv
    · subst hr; rw [hk3p] at hk; cases hk; exact Or.inr rfl
    · exact Or.inl (by rw [← hoth3 r hr]; exact hk)
  have hun3 : ∀ hi lo g l, g.toNat < 2 ^ 47 → l ≠ 0 → ¬ GPath σ3 hi lo g l ptr.bv := fun hi lo g l hg hl hp =>
    hun hi lo g l hg hl (GPath.mono' (fun hi lo e h _ => Or.inl (hpa hi lo e h)) hobj _ _ _ _ _ hp hl)
  have C5 : EptCore (L := L) X XL Z.th s5 (setCnodeSlot σ3 pc.bv r cs idx nc) :=
    C3.unmapSlot hW5 (fun b hb => hxa b (hSW b hb)) hxs hcv4 hlv hz hk3p
      (fun y hy hne l mm a v => by rw [hSS4.capV hy]; exact huq y hy hne l mm a v) hun3 hcv5 hcap5
      (cnK_setCnodeSlot hkc3 hwf hidx nc)
  exact ⟨cs, hkc, hwf, ⟨B', Cv'⟩, C5⟩

set_option maxHeartbeats 4000000 in
/-- **The EPT table unmap at `VmEptState`** (module docstring). -/
theorem VmEptState.tableUnmap (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hA : ArchRefines arI AR) {lbl len ptr level asid va : U64} {m : Bool} (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Ept ptr level m asid va)) (h0 : level ≠ 0#u64)
    (hu : lbl.val = (Fl4Spec.eptTableLabels level.val).2) (hf : finF (L.mem s) (cslotAddr (pc.bv, idx)) = true)
    (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    ExceptT.run (Fl4Spec.decodeEptInvocation (Z := Unit) lbl.bv args (pc.bv, idx)
        (.eptCap ptr.bv level.val (if m then some (asid.bv, va.bv) else none)) ec) σ =
      ({(.ok (.tableUnmap ptr.bv level.val (if m then some (asid.bv, va.bv) else none) (pc.bv, idx)), σ)}, False) ∧
    ept.decode st arI s a lbl len (.Ept ptr level m asid va) (cslotAddr (pc.bv, idx)) buf ex ⦃ res =>
      res.1 = .Ok () ∧ ∃ σ' : Fl4Spec.State Unit,
        EptTableUnmapSpec σ ptr.bv level.val (if m then some (asid.bv, va.bv) else none) (pc.bv, idx) σ' ∧
        ∃ Lst' : U64 → List U64, VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst' D res.2.1 res.2.2 σ' ⦄ := by
  have B := J.1.1
  have C := J.2
  set x := cslotAddr (pc.bv, idx) with hxdef
  have hP : Placed Z.th := B.xtop.rel.1
  have hA0 : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hxs : IsSlot Z.th x := hA0.isSlot
  have hcv0 : capV (L.mem s) x = .Ept ptr level m asid va := capV_of_capAt hcx
  obtain ⟨hpX, hlv4, -⟩ := C.capTbl hxs hcv0
  have hlv : level.val = 39 ∨ level.val = 30 ∨ level.val = 21 := by
    rcases hlv4 with h | h
    · exact absurd (UScalar.eq_of_val_eq (by rw [h]; rfl) : level = 0#u64) h0
    · exact h
  have hl0 : level.val ≠ 0 := by omega
  -- finality: no other slot names `ptr`
  obtain ⟨hPl, ⟨-, -, hML, -, hMI⟩, hFI0, -⟩ := B.xtop.rel
  have hx0 : x ∈ Z.G.chains.flatten := (hML.members _).2 ⟨hxs, _, hcx, fun h => by cases h⟩
  have hfin := (finF_iff hPl hML hMI hFI0 hx0 (by rw [hcv0]; exact Or.inl ⟨trivial, rfl⟩) (by rw [hcv0]; rfl)).1 hf
  have hmem : ∀ (l : U64) (mm : Bool) (a' v' : U64),
      Fl4Spec.GenObjRef.objRef ptr.bv ∈ Fl4Spec.genObjRefs (absCap (.Ept ptr l mm a' v')) := fun l mm a' v' =>
    Set.mem_union_left _ (Set.mem_union_left _ ⟨ptr.bv, by simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef], rfl⟩)
  have huq0 : ∀ y, IsSlot Z.th y → y ≠ x → ∀ l (mm : Bool) a' v', capV (L.mem s) y ≠ .Ept ptr l mm a' v' := by
    intro y hy hne l mm a' v' hc
    have hy0 : y ∈ Z.G.chains.flatten :=
      (hML.members y).2 ⟨hy, _, capAt_capV _ _, by rw [hc]; intro h; cases h⟩
    refine hfin y hy0 hne ?_
    rw [hcv0, hc]
    intro h
    have hm : Fl4Spec.GenObjRef.objRef ptr.bv ∈ Fl4Spec.genObjRefs (absCap (.Ept ptr level m asid va)) ∩
        Fl4Spec.genObjRefs (absCap (.Ept ptr l mm a' v')) := ⟨hmem _ _ _ _, hmem _ _ _ _⟩
    rw [h] at hm
    exact hm
  -- the restart
  have hct := P1.cur_thread_ok (L := L) s
  obtain ⟨hcur, xct, hkt, -⟩ := B.curRunnable hni hct
  have hSS1 : ∀ {s1 : S}, sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s1 →
      SlotsSame Z.th (L.mem s) (L.mem s1) := fun {s1} hs1 => by
    have h := set_thread_state_slots (L := L) Z.th hP s (L.curW s) sched.TS_RESTART (B.xtop.curTcb hcur).1
      B.kern.act
    rw [hs1, WP.spec_ok] at h; exact h
  have hAR : AR a σ.archState.x64CurrentCr3 := B.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨s1, σ1, Lst1, hs1, hst1, J1, hdec, hwp⟩ :=
    J.tableUnmapDec hni hA hAR buf ex hpc hidx hcx h0 hu hf args ec
  have e1 : σ1 = stsAct (updK σ (L.curW s).bv (.tcb { xct with tcbState := .restart })) (L.curW s).bv := by
    have hst := hst1
    rw [hcur, Notif.setThreadState_eq .restart hkt] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  have har1 : σ1.archState = σ.archState := by rw [e1]; unfold stsAct; split <;> rfl
  have hSS := hSS1 hs1
  have hcv1 : capV (L.mem s1) x = .Ept ptr level m asid va := by rw [hSS.capV hxs]; exact hcv0
  have huq1 : ∀ y, IsSlot Z.th y → y ≠ x → ∀ l (mm : Bool) a' v', capV (L.mem s1) y ≠ .Ept ptr l mm a' v' :=
    fun y hy hne l mm a' v' => by rw [hSS.capV hy]; exact huq0 y hy hne l mm a' v'
  refine ⟨hdec, WP.spec_mono hwp ?_⟩
  rintro res ⟨h1, hAR2, hcase⟩
  refine ⟨h1, ?_⟩
  have hAR2' : AR res.2.2 σ1.archState.x64CurrentCr3 := by rw [har1]; exact hAR2
  rcases hcase with ⟨rfl, hres⟩ | ⟨rfl, s3, hU, hres⟩
  · -- unmapped: the spec does nothing, FL4 rewrites the cap to the same abstract cap
    obtain ⟨u1, u2, u3, -⟩ := J1.2.ue x hxs ptr level asid va hcv1
    have hun1 : ∀ hi lo g l, g.toNat < 2 ^ 47 → l ≠ 0 → ¬ GPath σ1 hi lo g l ptr.bv :=
      fun hi lo g l hg hl => J1.2.named.unmUnreach hxs hcv1 hi lo g l hg hl
    obtain ⟨cs, hkc1, hwf, J5⟩ := J1.unmapClear hpc hidx hcv1 hl0 u3 hun1 (P1.WritesIn.refl _ _)
      (P1.WritesIn.refl _ _) u1
    obtain ⟨cs', hkc', -, hsl⟩ := J1.1.1.xtop.rel.2.1.1.cnode pc r hpc
    rw [hkc1] at hkc'
    cases hkc'
    have hcs : cs idx = some (.archObjectCap (.eptCap ptr.bv level.val none)) := by
      obtain ⟨c0, ac, hc0, hac, hca⟩ := hsl idx hidx
      have hc0' : capAt (L.mem s1) x = ok c0 := hc0
      rw [capAt_capV, hcv1] at hc0'
      have e : c0 = .Ept ptr level false asid va := (ok_inj hc0').symm
      subst e
      rw [hac, ← hca.2]; rfl
    rw [Endp.updK_self u2, setCnodeSlot_self hkc1 hcs] at J5
    refine ⟨σ1, ?_, Lst1, ?_⟩
    · show (Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
        Fl4Spec.performEptInvocation (.tableUnmap ptr.bv level.val none (pc.bv, idx))) σ = _
      rw [Notif.nd_bind_one hst1, performTableUnmap_none]
    · rw [hres]; exact J5.archV hAR2'
  · -- mapped: the unmap, the zeroing, the cap
    have hva : va.val < 2 ^ 47 := C.exte.vtop.1 _ hxs _ _ _ _ hcv0
    obtain ⟨σ2, hG, hcs2, hun2⟩ := J1.2.unmapUnreach hxs hcv1 hlv huq1 hU
    obtain ⟨J3, hSS3, har2⟩ : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst1 D s3 a σ2 ∧
        SlotsSame Z.th (L.mem s1) (L.mem s3) ∧ σ2.archState = σ1.archState := by
      rcases hcs2 with ⟨rfl, rfl⟩ | ⟨t, ht, es, hXt, hPt, hk, rfl, rfl⟩
      · exact ⟨J1, SlotsSame.refl _ _, rfl⟩
      · obtain ⟨J3, hSS3⟩ := J1.unmapEntry ht (g := va.bv) hva (by rw [hXt]; exact hPt) hk _
        exact ⟨J3, hSS3, rfl⟩
    have hcv3 : capV (L.mem s3) x = .Ept ptr level true asid va := by rw [hSS3.capV hxs]; exact hcv1
    have huq3 : ∀ y, IsSlot Z.th y → y ≠ x → ∀ l (mm : Bool) a' v', capV (L.mem s3) y ≠ .Ept ptr l mm a' v' :=
      fun y hy hne l mm a' v' => by rw [hSS3.capV hy]; exact huq1 y hy hne l mm a' v'
    have hpl := J3.2.rel.place ptr hpX
    obtain ⟨esp, hkp2, -⟩ := J3.2.rel.obj ptr hpX
    have h4096 : (4096#u64 : U64).val = 4096 := rfl
    have hal : P1.Aligned ptr := by unfold P1.Aligned; omega
    have hw : P1.WritesIn st s3 (L.zr s3 ptr 4096#u64) (fun b => ptr.val ≤ b.val ∧ b.val < ptr.val + 4096) :=
      (P1.writesIn_zr hal (by rw [h4096]) (by rw [h4096]; omega)).mono fun b hb => by rw [h4096] at hb; exact hb
    have hwP : P1.WritesIn st s3 (L.zr s3 ptr 4096#u64) (PtW {ptr}) := writes_zero hpl.1 (Set.mem_singleton ptr) s3
    have hz : ∀ i : BitVec 9, L.mem (L.zr s3 ptr 4096#u64) (eptA ptr i) = 0#u64 := by
      intro i
      have e := eptA_val hpl.2 i
      have hi9 := i.isLt
      rw [L.mem_zr _ _ _ _ hal (by rw [h4096]) (by rw [h4096]; omega) (by unfold P1.Aligned; rw [e]; omega),
        if_pos ⟨by rw [e]; omega, by rw [e, h4096]; omega⟩]
    obtain ⟨cs, hkc2, hwf, J5⟩ := J3.unmapClear hpc hidx hcv3 hl0 huq3 hun2 hw hwP hz
    refine ⟨setCnodeSlot (updK σ2 ptr.bv (.archObj (.ept (XL ptr) fun _ => 0))) pc.bv r cs idx
      (.archObjectCap (.eptCap ptr.bv level.val none)), ?_, Lst1, ?_⟩
    · show (Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
        Fl4Spec.performEptInvocation (.tableUnmap ptr.bv level.val (some (asid.bv, va.bv)) (pc.bv, idx))) σ = _
      rw [Notif.nd_bind_one hst1]
      exact performTableUnmap_some hG hkp2 hkc2 hwf hidx
    · rw [hres]
      refine J5.archV ?_
      show AR res.2.2 σ2.archState.x64CurrentCr3
      rw [har2]; exact hAR2'

set_option maxHeartbeats 4000000 in
/-- **The extended decoder and FL4's `syscall.decode_invocation` on an EPT table cap with the unmap label, at
`VmEptState`** (module docstring; P3/JAtZV3EptE's `zv_sysdec_ept` / `zv_decV_ept` + `VmEptState.tableUnmap`). -/
theorem eptTableUnmap_decode_vmEpt (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    (hni : Entered σ) (hA : ArchRefines arI AR) {lbl len ptr level asid va : U64} {m : Bool}
    (block call cd fp : Bool) (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Ept ptr level m asid va)) (h0 : level ≠ 0#u64)
    (hu : lbl.val = (Fl4Spec.eptTableLabels level.val).2) (hf : finF (L.mem s) (cslotAddr (pc.bv, idx)) = true)
    (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (fp' : Bool) (cref : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOut (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp' lbl.bv args cref (pc.bv, idx)
        (absCap (.Ept ptr level m asid va)) ec buffer) σ
      (.ept (.tableUnmap ptr.bv level.val (if m then some (asid.bv, va.bv) else none) (pc.bv, idx))) ∧
    syscall.decode_invocation st arI s a lbl len (cslotAddr (pc.bv, idx)) (.Ept ptr level m asid va)
        block call cd fp buf ex ⦃ res =>
      res.1 = .Ok () ∧ ∃ σ' : Fl4Spec.State Unit,
        EptTableUnmapSpec σ ptr.bv level.val (if m then some (asid.bv, va.bv) else none) (pc.bv, idx) σ' ∧
        ∃ Lst' : U64 → List U64, VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst' D res.2.1 res.2.2 σ' ⦄ := by
  obtain ⟨hd, hw⟩ := VmEptState.tableUnmap J hni hA buf ex hpc hidx hcx h0 hu hf args ec
  have habs : absCap (.Ept ptr level m asid va) =
      .archObjectCap (.eptCap ptr.bv level.val (if m then some (asid.bv, va.bv) else none)) := rfl
  refine ⟨?_, by rw [zv_sysdec_ept]; exact hw⟩
  rw [habs, zv_decV_ept]
  exact DecOut.liftME (DecOut.of_eq hd)

end

end

end Fl4Proofs.P3

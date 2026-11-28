/-
P3 (DESIGN.md §9), invariant line G2 (g2a): **`kernel_entryJ31`**, the newest
top. Its premise list is `kernel_entryJ30`'s, except that the bundles inside
`hK` no longer hold the ∀-state `JDelParts.vt` and those inside `hFin` no
longer hold the ∀-state `KFinAtR27.vt`.

`JDelParts.vt : JVtHyps` (XTopJointFinVtJ: the VT-x placement facts at EVERY
`JAtZ` state of the typed heap: the VCPU list, the EPT walks, the EPT-mapped
frames' ASIDs, the VCPUs) was false for an instance with misplaced VT-x
objects. g2a carries the native scope in `JAtZ.ext` (`JExt.nat`: every slot's
cap is `Vs.NativeCap`, no VCPU or EPT cap, no EPT-mapped frame cap, no IO-port
cap owned by a VCPU). `JVtHyps`'s `io` and `ept` now ask for a VT-x cap in a
slot (they are read only when such a cap is finalised), so every field's
hypotheses are refuted by `J.ext`, and `JVtHyps.ofExt` proves `JVtHyps` with no
premise.

* `JDelPartsN`: `JDelParts` without `vt` (`archRef`, `arKeep` [P], `thr`
  [S]/[P]); `JDelPartsN.toJ` fills `vt` by `JVtHyps.ofExt`.
* `JEntryGlobM31`: `JEntryGlobM` with `delParts : JDelPartsN`; `.toM`.
* `KDispHypsKV31`: `KDispHypsKV27b` with `JEntryGlobM31`; `.to27b`.
* `KFinAtR31`: `KFinAtR27` without `vt` (the ∀-`JAtZR` vtable-ASID premise,
  INV-PLAN F2), which `vtAsid_ofR` proves from `JAtZR.vsc`; `.to27`.
* `kernel_entryJ31`: `kernel_entryJ30` with `hK` giving `KDispHypsKV31` and
  `hFin` giving `KFinAtR31`. No premise added.
-/
import Fl4Proofs.P3.XTopJointKEntry29
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JDelParts` without the VT-x placement** (module docstring): the [P]
arch facts and the thread finalisation's facts. -/
structure JDelPartsN (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop where
  /-- [P] `JDelParts.archRef`. -/
  archRef : ArchRefines arI AR
  /-- [P] `JDelParts.arKeep`. -/
  arKeep : ARKeep arI AR
  /-- `JDelParts.thr` ([S] `obj`, [P] `ticks`). -/
  thr : JThreadFinHypsU (L := L) arI AR th

/-- **`JEntryGlobM` with `JDelPartsN`** (module docstring). -/
structure JEntryGlobM31 (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (th : TypedHeap) : Prop where
  ari : ARIface arI AR
  tot : P0.ArchTotal arI
  delParts : JDelPartsN (L := L) arI AR th
  nd : Fl4Spec.numDomains = 1
  ppA : PPPlatA arI AR
  dom : DomConfig
  portIn : PortInValMR arI MR
  timeAg : TimeAgree arI
  maxTU : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  tu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄

/-- **`KDispHypsKV27b` with `JEntryGlobM31`** (module docstring). -/
structure KDispHypsKV31 (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlobM31 (L := L) arI AR MR Z.th ∧ JEntryAtR2 (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlobM31 (L := L) arI AR MR Z.th ∧ JEntryAtR2 (L := L) arI AR Z H Cs s a σ ∧
    JPathAtM (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    JVtxHypMU (L := L) arI AR MR Z H Cs D s a σ ct

/-- **`KFinAtR27` without `vt`** (module docstring): `vt` is `vtAsid_ofR`. -/
structure KFinAtR31 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  sni : SniHyp st arI Z.N Z.T Z.C Z.c
  send : SendHyp st arI Z.N Z.T Z.C Z.c
  tail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄
  /-- [J] the idle TCB's vtable (`IdleVt`, from `KFinAtR8.idle`) and the arch premises `ArchRefines` [P] /
  `ARKeep` the g7e scheduler chain needs, carried to the old finish lemmas. -/
  rr : FinRootR arI AR σ

/-- **`KFinAtR27.vt` is a theorem** (g2a; INV-PLAN F2 `VtAsidJ`, JProducers'
`VtAsidJ` [J]): a set TCB is the typed heap's (`JPlaced.tcb`, `zH`), so its
vtable slot (slot 1) is a slot of the typed heap, and `JAtZR.vsc` (l4v
`valid_cap` of the arch caps, `Vs.VCapOK`'s `.Pml4` clause) gives a mapped
PML4 cap a non-zero ASID. -/
theorem vtAsid_ofR (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) :
    ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64 := by
  intro V1 s1 a1 σ1 Ac1 Lst1 D1 J1 t ht
  obtain ⟨Tr, Cq, hJ⟩ := J1.jpl
  have hth : Z.th t = some .tcb := (hJ.tcb t).2 (J1.zH.1 t ht)
  refine ⟨hth, fun p asid hc => ?_⟩
  have hx : IsSlot Z.th (slotOf t 1) := ⟨t, 1, Or.inr ⟨hth, by decide⟩, rfl⟩
  have h := J1.vsc _ hx
  rw [capV_of_capAt hc] at h
  have h' : (true = false → p ∈ _) ∧ p ≠ 0#u64 ∧ (true = true → asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) := h
  exact (h'.2.2 rfl).1

variable {arI}

theorem KFinAtR31.to27 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (F : KFinAtR31 (L := L) arI AR Z H Cs s a σ) : KFinAtR27 (L := L) arI AR Z H Cs s a σ :=
  ⟨F.hd, vtAsid_ofR arI AR Z H Cs, F.arch, F.archNd, F.sni, F.send, F.tail, F.rr⟩

/-- `JDelParts` from `JDelPartsN`: `vt` by `JVtHyps.ofExt` (g2a). -/
theorem JDelPartsN.toJ {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (h : JDelPartsN (L := L) arI AR th) :
    JDelParts (L := L) arI AR th :=
  ⟨h.archRef, h.arKeep, JVtHyps.ofExt arI AR th, h.thr⟩

theorem JEntryGlobM31.toM {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {th : TypedHeap} (h : JEntryGlobM31 (L := L) arI AR MR th) :
    JEntryGlobM (L := L) arI AR MR th :=
  ⟨h.ari, h.tot, h.delParts.toJ, h.nd, h.ppA, h.dom, h.portIn, h.timeAg, h.maxTU, h.tu⟩

theorem KDispHypsKV31.to27b {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets}
    {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKV31 (L := L) arI AR MR Z H Cs D s a σ n c) : KDispHypsKV27b (L := L) arI AR MR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hI => let ⟨g, e, p, v⟩ := h.inv ct call bl don hct hI; ⟨g.toM, e, p, v⟩,
    fun ct rg sr cr hct hM => let ⟨g, e, p, v⟩ := h.mid ct rg sr cr hct hM; ⟨g.toM, e, p, v⟩⟩

end

end

end Fl4Proofs.P3

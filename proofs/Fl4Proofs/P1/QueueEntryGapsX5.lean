/-
P1 (x86_64): **`Hyps5X`, the x86 entry record without the false walk fields**, and the entry tops over it
(namespace `X5`).

`Hyps4` (QueueEntryGaps4, used by `kernel_entry.entry_of4` … `entry_of10`) holds `∃ V, DelPlace V`, whose
`pt` / `pd` / `pdpt` are false as stated (QueueDelVsX5's docstring); `InvGaps4.gaps3` builds the deletion gaps,
the IRQ handler and the VSpace families from them. `Hyps5X` is `Hyps4` with `∃ V, X5.DelPlace V` in that place
and `InvGaps4 ∧ X5.InvVa` in `InvGaps4`'s; `gaps5` assembles `InvGaps` from it with `X5.delGaps_of`
(QueueDelVsX5), `X5.decGap_cnode2`, `X5.decGap_thread` (QueueDecTcbX5), `X5.decGap_irqHandler`,
`X5.decGap_vspace` (QueueDecVsX5); every other family as `InvGaps4.gaps3` / `InvGaps3.gaps`.
`X5.kernel_entry.entry_of4G` / `entry_of4` … `entry_of10` are the `Hyps4` tops' text (by script,
`handoff/a64-wip/gen24/gen_entryx5.py`) over `Hyps5X`.

Named premises: `Hyps5X`'s (as `Hyps4`, with [J] `X5.DelPlaceAt.walk` / `.walk0` / `.va` for the false
`DelPlaceAt.pt` / `.pd` / `.pdpt`, and [J] `X5.InvVa`), plus each top's own (`StoreExt` [P], `AsidOff` [J],
`RRSumAt` [J], `CnOffAt` [J], … unchanged).

**Vacuous, as the originals** (p1g, P1/EntryVacuous): `Hyps5X` keeps `Hyps4`'s `P3Place`, which no `EntryInv`
state satisfies (`P3Place.blkU` / `tmoOK` / `tmoAny`); this module removes only the walk fields' falsity from the
record. The x86 entry theorem to use stays P3's `kernel_entry_entryInvU29` (P3/XTopJointEntryInv29), which does
not use `DelPlaceAt` at all.
-/
import Fl4Proofs.P1.QueueDecVsX5
import Fl4Proofs.P1.QueueDecTcbX5
import Fl4Proofs.P1.FastTailRR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

namespace X5

/-- **`Hyps4` without the false walk fields**: `P3Place`, `CdtHyps2`, `∃ V, X5.DelPlace V` (for `∃ V, DelPlace V`),
`TcbPlace`, `InvGaps4 ∧` [J] `X5.InvVa`, the notification heap. Same positions as `Hyps4`.
**Contradictory as `Hyps4`** (its `P3Place`, P1/EntryVacuous). -/
def Hyps5X (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (Adm : PSets → Prop)
    (Cs U : Set U64) (P3Ok : S → Prop) (σ : PSets) : Prop :=
  P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ CdtHyps2 st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z P3Ok ∧
    (∃ V : U64 → Prop, DelPlace st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z V P3Ok) ∧
    TcbPlace st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
    (InvGaps4 st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
      InvVa st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok) ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn

/-- **`InvGaps` from `Hyps5X`'s parts** (as `InvGaps4.gaps3` then `InvGaps3.gaps`, with the X5 deletion gaps and
the X5 cnode / thread / IRQ handler / VSpace families). -/
theorem gaps5 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {V : U64 → Prop}
    (P : P3Place st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (Pd : DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) (Pt : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (G : InvGaps4 st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok ∧ InvVa st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok :=
  have DG : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok := fun s0 hE =>
    delGaps_of hA (Pd s0 hE) (X5.FinGapsAt.kinds hA (Pd s0 hE)
      (⟨finGap_ioPort hA (G.1.vcpuPl.ioPl s0 hE), G.1.fin s0 hE⟩ : FinGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0))
  ⟨decGap_untyped hA hσ (G.1.utPl.choose_spec.1.utPlace hA) G.1.utPl.choose_spec.2,
    decGap_reply hA P.xfer P.tmoAny (fun Ac s h => (P.blkU Ac s h).2),
    decGap_cnode2 hA C DG,
    decGap_thread hA G.1.thread Pt P.xfer DG C.toCdtHyps,
    decGap_irqControl hA C.toCdtHyps,
    decGap_irqHandler hA C.toCdtHyps Pd G.1.irqPl,
    decGap_domain hA,
    decGap_sc hA P.xfer (scYieldGap_holds hA U),
    decGap_schedControl hA G.1.scCtl,
    decGap_vspace hA Pd G.1.vsPl G.1.eptPl.pl C.toCdtHyps P.xfer G.1.irqPl DG G.2,
    decGap_vcpu hA G.1.vcpuPl P.xfer G.1.irqPl.extra,
    decGap_ept hA G.1.eptPl,
    decGap_ioPortControl C.toCdtHyps,
    decGap_ioPort hA P.xfer,
    decGap_tdx hA P.xfer⟩

/-- `kernel_entry.entry_of4G` over `Hyps5X`. **Vacuous** as the original (P1/EntryVacuous). -/
theorem kernel_entry.entry_of4G {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps5X st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall_old st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  Fl4Proofs.P1.kernel_entry.entry_of hA (tmoXG_holds hA) (ibKeep_holds hA) (fun σ h' => by
    obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, hNt⟩ := GF σ h'
    exact ⟨P, gaps5 hA h' P C Pd Pt G, hNt⟩) hσ s a hP h

/-- `kernel_entry.entry_of4` over `Hyps5X`. **Vacuous** as the original (P1/EntryVacuous). -/
theorem kernel_entry.entry_of4 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps5X st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hF : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter →
      FastAcc st ar s a number (fun r => ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' r.1)) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  let hG := kernel_entry.entry_of4G hA GF hσ s a hP h
  ⟨fun number hN => WP.spec_mono (FastAgree.spec st ar (FastAgree.of_acc st ar LawfulStore.total hA (hF number hN)) (WP.spec_mono (hG.1 number hN)
      fun r hr => by obtain ⟨s', a'⟩ := r; exact hr)) fun r hr => by obtain ⟨s', a'⟩ := r; exact hr,
    hG.2⟩

/-- `kernel_entry.entry_of5` (FastEntry) over `Hyps5X`. **Vacuous** as the original (P1/EntryVacuous). -/
theorem kernel_entry.entry_of5 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps5X st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hFt : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → FastFaultOK (L := L) ar s a number)
    (hRR : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter →
      FastRRP (st := st) ar s a number (fun r => ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' r.1)) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  kernel_entry.entry_of4 hA GF hσ s a hP h fun number hN =>
    FastAcc.of_split ar hX (hFt number hN) (hRR number hN)

/-- `kernel_entry.entry_of6` (FastFinInv) over `Hyps5X`. **Vacuous** as the original (P1/EntryVacuous). -/
theorem kernel_entry.entry_of6 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps5X st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hFP : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter →
      FastFaultPre (L := L) ar T Cs Ω U Sg Rp s a number)
    (hRR : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter →
      FastRRP (st := st) ar s a number (fun r => ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' r.1)) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact gaps5 hA hσ P C Pd Pt G
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  exact kernel_entry.entry_of5 hA GF hσ s a hP h hX
    (fun number hN => FastFaultOK.of_pre ar hA E0 hP h (hFP number hN)) hRR

/-- `kernel_entry.entry_of7` (FastFaultEnt) over `Hyps5X`. **Vacuous** as the original (P1/EntryVacuous). -/
theorem kernel_entry.entry_of7 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps5X st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hNv : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → FaultNvmPre (L := L) ar s a number)
    (hRR : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter →
      FastRRP (st := st) ar s a number (fun r => ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' r.1)) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact gaps5 hA hσ P C Pd Pt G
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  exact kernel_entry.entry_of6 hA GF hσ s a hP h hX
    (fun number hN => FastFaultPre.of_asid ar hA E0 (GF _ hσ).1.xfer hP h hAs (hNv number hN)) hRR

/-- `kernel_entry.entry_of7r` (FastRRSame) over `Hyps5X`. **Vacuous** as the original (P1/EntryVacuous). -/
theorem kernel_entry.entry_of7r {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps5X st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hNv : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → FaultNvmPre (L := L) ar s a number)
    (hRP : RRPreAt (L := L) ar s a) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact gaps5 hA hσ P C Pd Pt G
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  exact kernel_entry.entry_of4 hA GF hσ s a hP h fun number hN =>
    FastAcc.of_split_rr ar hX
      (FastFaultOK.of_pre ar hA E0 hP h
        (FastFaultPre.of_asid ar hA E0 (GF _ hσ).1.xfer hP h hAs (hNv number hN))) hRP

/-- `kernel_entry.entry_of7r2` (FastRREnt) over `Hyps5X`. **Vacuous** as the original (P1/EntryVacuous). -/
theorem kernel_entry.entry_of7r2 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps5X st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hNv : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → FaultNvmPre (L := L) ar s a number)
    (hRP : RRPreAt2 (L := L) ar s a) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact gaps5 hA hσ P C Pd Pt G
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  exact kernel_entry.entry_of7r hA GF hσ s a hP h hX hAs hNv (RRPreAt.of2 ar hA E0 hP h hRP)

/-- `kernel_entry.entry_of8` (FastRRFoot) over `Hyps5X`. **Vacuous** as the original (P1/EntryVacuous). -/
theorem kernel_entry.entry_of8 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps5X st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hNv : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → FaultNvmPre (L := L) ar s a number)
    (hSum : RRSumAt (L := L) ar Scs s a)
    (hRP : RRPreAt3 (L := L) ar s a) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact gaps5 hA hσ P C Pd Pt G
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  have hNt : ∀ n ∈ Nt, H n = some .ntfn := (GF _ hσ).2.2.2.2.2
  exact kernel_entry.entry_of7r2 hA GF hσ s a hP h hX hAs hNv (RRPreAt2.of3 ar hA E0 hNt hP h hSum hRP)

/-- `kernel_entry.entry_of9` (FastRRLk) over `Hyps5X`. **Vacuous** as the original (P1/EntryVacuous). -/
theorem kernel_entry.entry_of9 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps5X st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hNv : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → FaultNvmPre (L := L) ar s a number)
    (hSum : RRSumAt (L := L) ar Scs s a)
    (hCn : CnOffAt (L := L) ar T Cs Sg s a)
    (hRP : RRPreAt5 (L := L) ar s a) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact gaps5 hA hσ P C Pd Pt G
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  have hNt : ∀ n ∈ Nt, H n = some .ntfn := (GF _ hσ).2.2.2.2.2
  exact kernel_entry.entry_of7r2 hA GF hσ s a hP h hX hAs hNv (RRPreAt2.of5 ar hA E0 hNt hP h hSum hCn hRP)

/-- `kernel_entry.entry_of10` (FastTailRR) over `Hyps5X`. **Vacuous** as the original (P1/EntryVacuous). -/
theorem kernel_entry.entry_of10 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps5X st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hSum : RRSumAt (L := L) ar Scs s a)
    (hCn : CnOffAt (L := L) ar T Cs Sg s a) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact gaps5 hA hσ P C Pd Pt G
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  have hNt : ∀ n ∈ Nt, H n = some .ntfn := (GF _ hσ).2.2.2.2.2
  exact kernel_entry.entry_of9 hA GF hσ s a hP h hX hAs
    (fun _ _ => FaultNvmPre.of_asid ar hA E0 (GF _ hσ).1.xfer hP h hAs) hSum hCn
    (RRPreAt5.of_inv ar hA E0 hNt hP h hSum)

end X5

end

end Fl4Proofs.P1

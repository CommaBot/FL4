/-
P3 (DESIGN.md §9), scheduler: **`schedule`'s steps at `XTop`** (the entry
tail's frame, stage 2): a step of FL4 writing only `TFoot` words, the spec
changing only scheduling fields, the current thread, and the current CR3
(`SchStep`), keeps the composite relation, given the scheduler and
notification relations after, the current thread's `CurOK` and the CR3
relation after (the arch switch's facts, `xtop_sched_step`).

* `SchStep P σ σ'`: `ScTKw P` but for the current thread and the arch
  state's current CR3 (`choose_thread`/`switch_to_thread`'s
  `set_vm_root`). Reflexive, transitive; `ScTKw.toSch`.
* `SchStep.toTK`: an `ScTKw` step to `σ'` with `σ`'s current thread and
  arch state (same heap), for the heap-reading lemmas.
-/
import Fl4Proofs.P3.ScXStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- **A scheduler step** (module docstring). -/
structure SchStep (P : ObjRef → Prop) (σ σ' : State Unit) : Prop where
  kh : ∀ p, OTK (P p) (σ.kheap p) (σ'.kheap p)
  um : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  dl : σ'.domainList = σ.domainList
  dsi : σ'.domainStartIndex = σ.domainStartIndex
  arch : σ'.archState = { σ.archState with x64CurrentCr3 := σ'.archState.x64CurrentCr3 }
  ist : σ'.interruptStates = σ.interruptStates
  inode : σ'.interruptIrqNode = σ.interruptIrqNode

theorem SchStep.refl (P : ObjRef → Prop) (σ : State Unit) : SchStep P σ σ :=
  ⟨fun _ => OTK.refl _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SchStep.trans {P : ObjRef → Prop} {σ1 σ2 σ3 : State Unit} (h1 : SchStep P σ1 σ2) (h2 : SchStep P σ2 σ3) :
    SchStep P σ1 σ3 :=
  ⟨fun p => (h1.kh p).trans (h2.kh p), h2.um.trans h1.um, h2.cdt.trans h1.cdt, h2.orig.trans h1.orig,
    h2.dl.trans h1.dl, h2.dsi.trans h1.dsi, by rw [h2.arch, h1.arch], h2.ist.trans h1.ist,
    h2.inode.trans h1.inode⟩

theorem ScTKw.toSch {P : ObjRef → Prop} {σ σ' : State Unit} (h : ScTKw P σ σ') : SchStep P σ σ' :=
  ⟨h.kh, h.um, h.cdt, h.orig, h.dl, h.dsi, by rw [h.arch], h.ist, h.inode⟩

/-- The state `σ'` with `σ`'s current thread and arch state. -/
def schBack (σ σ' : State Unit) : State Unit := { σ' with curThread := σ.curThread, archState := σ.archState }

theorem SchStep.toTK {P : ObjRef → Prop} {σ σ' : State Unit} (h : SchStep P σ σ') : ScTKw P σ (schBack σ σ') :=
  ⟨h.kh, h.um, h.cdt, h.orig, h.dl, h.dsi, rfl, h.ist, h.inode, rfl⟩

/-- A field of the arch state other than the current CR3 is kept. -/
theorem SchStep.archF {P : ObjRef → Prop} {σ σ' : State Unit} (h : SchStep P σ σ') {β : Type}
    (f : ArchState → β) (hf : ∀ a c, f { a with x64CurrentCr3 := c } = f a) : f σ'.archState = f σ.archState := by
  rw [h.arch, hf]

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 2000000 in
/-- **A scheduler step keeps `XTop`** at the same sets (module docstring). -/
theorem xtop_sched_step {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} {ct : Fl4Spec.ObjRef}
    (hX : XTopAt (L := L) AR Z s a σ) (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B)
    (hNk : ∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hW : WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ))
    (hK : SchStep (fun p => p = ct) σ σ')
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ') (hN' : NtfnStateRel Z.N Z.T (L.mem s') σ')
    (hCur' : Vs.CurOK st Z.th s' σ') (hAR' : AR a' σ'.archState.x64CurrentCr3) :
    XTopAt (L := L) AR Z s' a' σ' := by
  have hT := hK.toTK
  obtain ⟨hF, hB, -, hA⟩ := hX
  obtain ⟨⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hTP⟩, hVs, hPt, hPI, hCur⟩ := hF
  have hks : L.ksb s' = L.ksb s := hW.1
  have hmem : ∀ b, Aligned b → ¬ TFoot st Z.T Z.N Z.C Z.c s σ b → L.mem s' b = L.mem s b := hW.2.2
  have hiw : ∀ b, TFoot st Z.T Z.N Z.C Z.c s σ b →
      IWords Z.N Z.T Z.E Z.R Z.B b ∨ NodeW (L.ksb s) Z.c b ∨ ScObjW Z.C σ b := fun b hb => tfoot_iw hSch hb
  have hoo : ∀ b, TFoot st Z.T Z.N Z.C Z.c s σ b → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b :=
    fun b hb => tfoot_oobj hSch hb
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hTP.vs.ksb_fit; omega
  have hka := hTP.vs.ksb_al
  have hkw : ∀ b, Aligned b → (L.ksb s).val ≤ b.val → b.val < (L.ksb s).val + 13568 → L.mem s' b = L.mem s b :=
    fun b hb h1 h2 => hmem b hb fun ht => by rcases tfoot_ksb hSch hNk ht with e | e <;> omega
  have hvw : ∀ b, Aligned b → Vs.VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b → L.mem s' b = L.mem s b :=
    fun b hb hv => hmem b hb fun ht => hTP.disj b (hoo b ht) hv
  -- the endpoint relation (it reads the heap only)
  have hE0 : EpStateRel Z.T Z.E Z.R Z.B (L.mem s') (schBack σ σ') := EpStateRel.scStep (σ' := schBack σ σ') hEp hTP.ep
    (fun x hx hf hns => hmem x hx fun ht => by
      obtain ⟨t, htT, rfl⟩ := tfoot_efoot hP0 hSch hA ht hf; exact hns t htT rfl)
    (fun t ht x' hk => by
      obtain ⟨y, hky, hy⟩ := hN'.tcb t ht
      have hk' : σ'.kheap t.bv = some (.tcb x') := hk
      rw [hk'] at hky; cases hky; exact hy.st) hT
  have hE' : EpStateRel Z.T Z.E Z.R Z.B (L.mem s') σ' := by
    obtain ⟨e1, e2, e3, e4⟩ := hE0; exact ⟨e1, e2, e3, e4⟩
  have hIrq' : IrqRel (L.mem s') (L.ksb s') σ' := by
    rw [hks]
    refine ⟨fun i hi => ?_, fun i hi => by rw [hK.inode]; exact hIrq.node i hi⟩
    have hv := irqStA_val hkf hi
    rw [hK.ist, hkw _ (by unfold Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)]
    exact hIrq.st i hi
  have hIo' : IoRel (L.mem s') (L.ksb s') σ' := by
    rw [hks]
    intro p hp
    have hw : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have hv := ioA_val hkf hw
    unfold bitOf
    rw [hkw _ (by unfold Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega),
      hK.archF (fun a => a.x64AllocatedIoPorts) (fun _ _ => rfl)]
    exact hIo p hp
  have hKr' : Vs.KRootRel (L.mem s') (L.ksb s') σ' := by
    unfold Vs.KRootRel Vs.globCr3 at hKr ⊢
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [hks, hkw _ (by unfold Aligned; rw [hkv]; omega) (by rw [hkv]; omega) (by rw [hkv]; omega),
      hK.archF (fun a => a.x64GlobalPml4) (fun _ _ => rfl)]
    exact hKr
  have hz : SzKeep σ σ' := hT.szKeep
  have hTP' : Vs.TopPlaced st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' := by
    have hnb : L.nodeBase s' Z.c = L.nodeBase s Z.c := by simp [LawfulStore.nodeBase, hks]
    exact ⟨hTP.ep, by rw [hks]; exact hTP.vs, hTP.pt, hTP.pl,
      fun x hx => by rw [hks]; exact hTP.disj x (OObj.of_szKeep hks hz hx),
      fun x h1 h2 => by rw [hnb] at h1 h2; exact hTP.nodeE x h1 h2, hTP.po, hTP.ps,
      by rw [hks]; exact hTP.pv, by rw [hks]; exact hTP.vo, by rw [hks]; exact hTP.sd, by rw [hks]; exact hTP.tko⟩
  have hVs' : Vs.VsRel Z.P (L.mem s') (L.ksb s') σ' := by
    rw [hks]
    refine Vs.VsRel.frame hVs (fun b hb => hvw b (hb.aligned hTP.vs) (Vs.vsWrite_vobj hTP.vs hb))
      (hK.archF (fun a => a.x64AsidTable) (fun _ _ => rfl)) fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hVs.pool p hp
    exact hT.arch_obj hf
  have hPt' : Vs.PtRel Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s') σ' := by
    refine Vs.PtRel.frame hPt (fun b ⟨q, hq, i, hi, e⟩ => ?_) fun q hq => ?_
    · subst e
      have hq4 := hTP.pt q hq
      refine hvw _ (by show _ % 8 = 0; rw [Vs.peA_val (Vs.tbl_fit hq4) hi]; omega)
        (Vs.table_vobj hTP.pt hq hi _)
    · rcases hq with hq | hq | hq | hq
      · obtain ⟨f, hf, -⟩ := hPt.l4 q hq; exact hT.arch_obj hf
      · obtain ⟨f, hf, -⟩ := hPt.l3 q hq; exact hT.arch_obj hf
      · obtain ⟨f, hf, -⟩ := hPt.l2 q hq; exact hT.arch_obj hf
      · obtain ⟨f, hf, -⟩ := hPt.l1 q hq; exact hT.arch_obj hf
  have hPI' : Vs.PoolsIn Z.P Z.L4 (L.mem s') :=
    Vs.PoolsIn.of_writes hPI hW hTP.vs fun b hb hv => hTP.disj b (hoo b hb) (Vs.vsWrite_vobj hTP.vs hv)
  have hck : Fl4Proofs.P3.CKeep σ σ' := by
    obtain ⟨c1, c2, c3, c4, c5⟩ := hT.ckeep
    exact ⟨c1, c2, c3, c4, c5⟩
  have hB' := RelTopB.frameS hB hW hiw
    (fun x ⟨sc, hsc, y, n, hk, hobj⟩ => (hSch.scOut sc hsc y n hk x hobj).2.2.2) hck hK.dl hK.dsi hz
  exact ⟨⟨⟨⟨hS', hE', hN', hIrq', hIo', hKr', hAR'⟩, hTP'⟩, hVs', hPt', hPI', hCur'⟩, hB',
    IpcRel.of hN' hE' (sched_sc hS'), hA.mono hks hz⟩

end

end

end Fl4Proofs.P3.Sched

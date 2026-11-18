/-
P3 (DESIGN.md §9), IPC: **the cap transfer** (the grant path of
`do_ipc_transfer`): FL4's `transfer_caps` against l4v's `transfer_caps` on
the composite relation `IpcRel ∧ SRE ∧ RelTopB`.

* The spec side of `cap_insert`: `CnK` (only CNodes, TCBs' caps, the CDT,
  the original bits and the extended state change), `capInsert_nkn`;
  `CnK.ikview`, `CnK.schedStep`, `CnK.inUserFrame`.
* `insert_top`: `cdt::insert` of a derived cap refines `cap_insert`
  (`insert_full_fin`, `insert_ws`), keeping the merged IPC relation, the
  scheduler relation (`sre_slotw`: slot writes are no scheduler word) and
  `RelTopB` with the same typed heap.
* `buf_set_top`: a badge into the receive buffer refines `store_word_offs`.
* `tcl_*`: the spec's `transfer_caps_loop` one cap at a time (unwrapped
  badge, insert, derive failure or null, no receive slot, end).
* `tc_body`, `transfer_loop_top`: FL4's loop against the spec's, with the
  extra caps related to the spec's (`SrcOK`); `derive_cap`'s MDB fact
  (`NoChildrenRel`) at the sources from the relation (`noChildren_of_adj`),
  and the frame of the loop (`KeepC`: the spec's heap changes in CNodes only,
  by `capInsert_nko`; FL4 writes slot and buffer words only, `FW`). FL4
  (like seL4's C) reads
  each source's cap again; the spec uses the caps looked up before. They
  agree (`UwEq`): before the one insert only buffer words change; after it
  the receive slot is gone, so only the unwrap test matters, and a later
  source equal to the insert's source holds an untyped cap on both sides
  (`set_untyped_cap_as_full`), one equal to the receive slot holds the
  derived cap in FL4 and the null cap in the spec, both failing the test
  (the derived cap has the source's shape, which failed it) (`insert_capfr2`,
  IpcInsFrame.lean).
* `transfer_caps_top`: `transfer_caps`, from the receive-slot lookup
  against `get_receive_slots` (`hG1`, named: G1) and the spec's lookup
  being deterministic (`hGRs`, EpBufMapHyps' `recvSlots`).
-/
import Fl4Proofs.P3.IpcWake
import Fl4Proofs.P3.SpecCnK
import Fl4Proofs.P3.SpecNKO
import Fl4Proofs.P3.IpcInsFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section CnK
open Fl4Spec

/-- `KeepC` with the arch state, the IRQ state and node and the current
thread kept (for the VSpace parts, `VsKeep`). -/
def KeepCV (σ σ' : State Unit) : Prop :=
  KeepC σ σ' ∧ σ'.archState = σ.archState ∧ σ'.interruptStates = σ.interruptStates ∧
    σ'.interruptIrqNode = σ.interruptIrqNode ∧ σ'.curThread = σ.curThread

theorem KeepCV.refl (σ : State Unit) : KeepCV σ σ := ⟨KeepC.refl σ, rfl, rfl, rfl, rfl⟩

theorem KeepCV.trans {σ1 σ2 σ3 : State Unit} (h1 : KeepCV σ1 σ2) (h2 : KeepCV σ2 σ3) : KeepCV σ1 σ3 :=
  ⟨h1.1.trans h2.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem KeepCV.vsKeep {σ σ' : State Unit} (h : KeepCV σ σ') : VsKeep σ σ' := by
  refine ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, fun q ao hq => ?_, fun p x n hp => ?_, fun p x hp => ?_⟩
  · rcases h.1 q with e | ⟨r, cs, cs', h1, -⟩
    · exact e
    · rw [hq] at h1; cases h1
  · rcases h.1 p with e | ⟨r, cs, cs', -, h2⟩
    · exact ⟨x, e ▸ hp⟩
    · rw [hp] at h2; cases h2
  · rcases h.1 p with e | ⟨r, cs, cs', h1, -⟩
    · exact ⟨x, by rw [e]; exact hp, rfl⟩
    · rw [hp] at h1; cases h1

theorem CnK.keepCV {σ σ' : State Unit} (hK : CnK σ σ') (hC : KeepC σ σ') : KeepCV σ σ' :=
  ⟨hC, by have e := congrArg AbstractState.archState hK.1; exact e,
    by have e := congrArg AbstractState.interruptStates hK.1; exact e,
    by have e := congrArg AbstractState.interruptIrqNode hK.1; exact e,
    by have e := congrArg AbstractState.curThread hK.1; exact e⟩

theorem CnK.other {σ σ' : State Unit} (h : CnK σ σ') {p : ObjRef} {o : KernelObject}
    (hp : σ.kheap p = some o) (hc : ∀ r cs, o ≠ .cnode r cs) (ht : ∀ x, o ≠ .tcb x) : σ'.kheap p = some o := by
  rcases h.2 p with e | ⟨r, cs, cs', h1, -⟩ | ⟨a, b, h1, -, -⟩
  · rw [e, hp]
  · rw [hp] at h1; cases h1; exact absurd rfl (hc r cs)
  · rw [hp] at h1; cases h1; exact absurd rfl (ht a)

theorem CnK.tcb {σ σ' : State Unit} (h : CnK σ σ') {p : ObjRef} {x : Tcb} (hp : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ CapsOnly x y := by
  rcases h.2 p with e | ⟨r, cs, cs', h1, -⟩ | ⟨a, b, h1, h2, hab⟩
  · exact ⟨x, by rw [e, hp], CapsOnly.refl x⟩
  · rw [hp] at h1; cases h1
  · rw [hp] at h1; injection h1 with h1; injection h1 with h1; subst h1; exact ⟨b, h2, hab⟩

theorem CnK.sc' {σ σ' : State Unit} (h : CnK σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext y n)) : σ.kheap p = some (.schedContext y n) := by
  rcases h.2 p with e | ⟨r, cs, cs', h1, h2⟩ | ⟨a, b, h1, h2, hab⟩
  · rw [← e]; exact hp
  · rw [hp] at h2; cases h2
  · rw [hp] at h2; cases h2

/-- The IPC relation's view is kept. -/
theorem CnK.ikview {σ σ' : State Unit} (h : CnK σ σ') : IKView σ σ' := by
  have hms : σ'.machineState = σ.machineState := by have := congrArg AbstractState.machineState h.1; exact this
  refine ⟨⟨fun p x hp => h.other hp (fun _ _ e => by cases e) (fun _ e => by cases e), fun p x hp => ?_⟩,
    ⟨fun p x hp => h.other hp (fun _ _ e => by cases e) (fun _ e => by cases e),
     fun p x hp => ⟨x, h.other hp (fun _ _ e => by cases e) (fun _ e => by cases e), rfl⟩, fun p x hp => ?_,
     by rw [hms]⟩, fun p x hp => ?_⟩
  · obtain ⟨y, hy, c1, -, -, -, -, -, -, c8, -, -, c11⟩ := h.tcb hp
    exact ⟨y, hy, c1, by unfold badgeOf; rw [c11], c8⟩
  · obtain ⟨y, hy, c1, -, c3, c4, -, -, -, c8, -, -, c11⟩ := h.tcb hp
    exact ⟨y, hy, c1, by rw [c11], c8, c3, c4⟩
  · obtain ⟨y, hy, -, -, -, -, -, c6, -⟩ := h.tcb hp
    exact ⟨y, hy, c6⟩

/-- The scheduler's fields are kept. -/
theorem CnK.schedStep {σ σ' : State Unit} (h : CnK σ σ') : SchedStep σ σ' := by
  have e := h.1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun p x hp => ?_, fun p x n hp => ?_, fun p x n hp => ?_⟩
  · have := congrArg AbstractState.readyQueues e; exact this
  · have := congrArg AbstractState.releaseQueue e; exact this
  · have := congrArg AbstractState.curThread e; exact this
  · have := congrArg AbstractState.schedulerAction e; exact this
  · have := congrArg AbstractState.curSc e; exact this
  · have := congrArg AbstractState.curTime e; exact this
  · have := congrArg AbstractState.consumedTime e; exact this
  · have := congrArg AbstractState.reprogramTimer e; exact this
  · have := congrArg AbstractState.curDomain e; exact this
  · have := congrArg AbstractState.domainTime e; exact this
  · have := congrArg AbstractState.idleThread e; exact this
  · have := congrArg AbstractState.idleSc e; exact this
  · obtain ⟨y, hy, hab⟩ := h.tcb hp
    exact ⟨y, hy, hab.2.2.2.2.2.2.2.2.1, hab.2.2.2.2.2.1, hab.2.2.2.2.2.2.2.1⟩
  · exact h.other hp (fun _ _ e => by cases e) (fun _ e => by cases e)
  · exact ⟨x, h.sc' hp⟩

end CnK


/-! ## `cdt::insert` on the composite relation -/

section Insert
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem slotWd_range {th : TypedHeap} (hP : Placed th) {b : U64} (h : Sched.SlotWd th b) :
    ∃ y, IsSlot th y ∧ y.val ≤ b.val ∧ b.val < y.val + 32 := by
  obtain ⟨y, hy, k, hk, rfl⟩ := h
  have := hy.fit hP; have := hk.lt
  exact ⟨y, hy, by rw [wordOf_val (by omega)]; omega, by rw [wordOf_val (by omega)]; omega⟩

theorem IFoot.iwords (hP0 : IPlaced N T E R B) {a : U64} (h : IFoot N T E R B a) : IWords N T E R B a := by
  rcases h with (⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hw, rfl⟩) | ⟨n, hn, h1, h2⟩ | ⟨t, ht, rfl⟩
  · exact Or.inr (Or.inl ⟨e, he, by omega, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨r, hr, by omega, by omega⟩))
  · have := h.range; exact Or.inl ⟨t, ht, by omega, by omega⟩
  · unfold TL at h; exact Or.inl ⟨t, ht, by omega, by omega⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h1, h2⟩)))
  · have := scA_val (hP0.e.tcb t ht); exact Or.inl ⟨t, ht, by omega, by omega⟩

/-- **Slot writes keep what `SchedRel` reads.** -/
theorem sagree_slotw {th : TypedHeap} (hP : Placed th) {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hA : IpcApart th N T E R B (L.ksb s) c) (hSA : ScApart th C σ)
    (hw : WritesIn st s s' (Sched.SlotWd th)) : SAgree st T C c s s' := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
  have h1 := hc.node.align
  have h2 := hc.node.fits
  simp only [LawfulStore.nodeBase] at h1 h2
  refine ⟨hw.1, hw.2.1, fun o ho h8 _ _ _ _ _ => hw.mem_eq (nodeAt_aligned hc.node ho h8) fun hsw => ?_,
    fun y hy K hK => ?_, ?_, ?_, fun sc hsc a ha hin => hw.mem_eq ha fun hsw => ?_⟩
  · obtain ⟨y, hy, g1, g2⟩ := slotWd_range hP hsw
    have hv := nodeAt_val hc.node ho
    exact hA.node _ (by rw [hv, ← hnb]; omega) (by rw [hv, ← hnb]; omega) y hy ⟨g1, g2⟩
  · obtain ⟨k1, k2, -⟩ := schedField_ok hK
    refine hw.mem_eq (field_aligned (hc.tcbs y hy) k1 k2) fun hsw => ?_
    obtain ⟨x, hx, g1, g2⟩ := slotWd_range hP hsw
    have hv := tfield_val (hc.tcbs y hy) k1
    have hK' : 256 ≤ K.val := by rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hA.slot _ (Or.inl ⟨y, hy, by rw [hv]; omega, by rw [hv]; omega⟩) x hx ⟨g1, g2⟩
  · have hal : Aligned (curDomA st s) := by
      unfold Aligned curDomA
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
      omega
    refine hw.mem_eq hal fun hsw => ?_
    obtain ⟨x, hx, g1, g2⟩ := slotWd_range hP hsw
    have hv : (curDomA st s).val = (L.ksb s).val + 8 := by
      unfold curDomA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    exact hA.ks _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) x hx ⟨g1, g2⟩
  · refine hw.mem_eq (dtA_aligned hc.node) fun hsw => ?_
    obtain ⟨x, hx, g1, g2⟩ := slotWd_range hP hsw
    have hv := dtA_val hc.node
    exact hA.ks _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) x hx ⟨g1, g2⟩
  · obtain ⟨x, hx, g1, g2⟩ := slotWd_range hP hsw
    obtain ⟨y, n, hk, hy⟩ := hs.scs sc hsc
    exact hSA sc hsc y n hk a (hy.in_obj hin) x hx ⟨g1, g2⟩

/-- **The scheduler relation across slot writes and a `CnK` spec step.** -/
theorem sre_slotw {th : TypedHeap} (hP : Placed th) {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SRE st N T C E R B c s σ) (hA : IpcApart th N T E R B (L.ksb s) c) (hSA : ScApart th C σ)
    (hw : WritesIn st s s' (Sched.SlotWd th)) (hK : CnK σ σ') : SRE st N T C E R B c s' σ' := by
  obtain ⟨Q, R0, hc, -⟩ := hS.1.lists
  have ha := sagree_slotw hP hS.1 hA hSA hw
  have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
  have hn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → nodeW st s' c o = nodeW st s c o := fun o ho h8 => by
    unfold Fl4Proofs.P3.Sched.nodeW; rw [Sched.nodeAt_ksb (st := st) hw.1]
    refine hw.mem_eq (nodeAt_aligned hc.node ho h8) fun hsw => ?_
    obtain ⟨y, hy, g1, g2⟩ := slotWd_range hP hsw
    have hv := nodeAt_val hc.node ho
    have h2 := hc.node.fits
    simp only [LawfulStore.nodeBase] at h2
    exact hA.node _ (by rw [hv, ← hnb]; omega) (by rw [hv, ← hnb]; omega) y hy ⟨g1, g2⟩
  exact ⟨hS.1.of_sagreeE ha (hn _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    (hn _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])) hS.1.nodeNW hS.1.domNW hS.1.dtNW
    hK.schedStep, hS.2.mono hw.1 (fun p y n hp => ⟨y, hK.sc' hp⟩)⟩

/-- **`cdt::insert` of a derived cap refines `cap_insert` on the composite
relation**: the merged IPC relation, the scheduler relation and the CSpace
relation with the same typed heap (`insert_full_fin`, `insert_ws`). -/
theorem insert_top (hP0 : IPlaced N T E R B) {th : TypedHeap} {G : MdbGhost} {s : S} {σ : Fl4Spec.State Unit}
    (hB : RelTopB (L := L) th G N T C E R B c s σ) (hR : IpcRel N T E R B (L.mem s) σ)
    (hS : SRE st N T C E R B c s σ)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (cc : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cc a) (hcv : CapValid th cc) (he : EncWf cc)
    (hcnn : cc ≠ .Null) (hsh : shape cc = shape srcC) (hbd : badgeF cc = badgeF srcC ∨ badgeF srcC = 0#u64)
    (hut : isUt srcC = true → ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs))) (hzb : isZb srcC = false)
    (hkey : okey cc = okey srcC)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC → Vs.VCapOK P L4 L3 L2 L1 cc)
    (huc : isUt srcC = true → cc = srcC) :
    cdt.insert st s cc (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦃ s' =>
      ∃ σ', Fl4Spec.capInsert (Z := Unit) a (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) ∧
        IpcRel N T E R B (L.mem s') σ' ∧ SRE st N T C E R B c s' σ' ∧
        (WritesIn st s s' (Sched.SlotWd th) ∧ KeepCV σ σ') ∧
        ∃ G', RelTopB (L := L) th G' N T C E R B c s' σ' ⦄ := by
  obtain ⟨hPl, ⟨hSt, hV, hM, hC, hI⟩, hFI, hD, hMO, hA, hSA⟩ := hB
  have hsI : IsSlot th (cslotAddr (ps.bv, idxs)) :=
    AbsSlot.isSlot (⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩ : AbsSlot th (ps.bv, idxs))
  have hdI : IsSlot th (cslotAddr (pd.bv, idxd)) :=
    AbsSlot.isSlot (⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩ : AbsSlot th (pd.bv, idxd))
  have hnx : nextOf (L.mem s) (cslotAddr (ps.bv, idxs)) = 0#u64 ∨
      IsSlot th (nextOf (L.mem s) (cslotAddr (ps.bv, idxs))) := by
    have hm := (hM.members _).2 ⟨hsI, srcC, hsrcC, hsnn⟩
    rcases hM.next_mem hm with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ((hM.members _).1 h).1
  refine WP.spec_mono (WP.spec_and (insert_full_fin th s σ G hSt hV hPl hM hC hI hFI hps hpd hls hld hsrcC hsnn
    hdst cc a hca hcv he hcnn hsh hbd hut hzb hkey hv) (Sched.insert_ws hPl s cc _ _ hsI hdI srcC hsrcC hnx)) ?_
  rintro s' ⟨⟨σ', G', heq, hSt', hV', hM', hC', hI', hFI', hstep⟩, hw⟩
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) a (ps.bv, idxs) (pd.bv, idxd) σ).1 := by rw [heq]; rfl
  have hK := capInsert_nkn a _ _ σ _ hmem
  have hKC : KeepC σ σ' := keepC_of hK (capInsert_nko a _ _ σ _ hmem) (by
    rintro p (rfl | hp)
    · obtain ⟨cs, h, -⟩ := hSt.cnode ps rs hps; exact ⟨rs, cs, h⟩
    · rw [Set.mem_singleton_iff.1 hp]; obtain ⟨cs, h, -⟩ := hSt.cnode pd rd hpd; exact ⟨rd, cs, h⟩)
  have hDS : DomSame (L.mem s) (L.mem s') (L.ksb s) :=
    Vs.domSame_low hA.kfit hA.kal fun b hb h1 h2 => hw.mem_eq hb fun hsw => by
      obtain ⟨y, hy, g1, g2⟩ := slotWd_range hPl hsw
      exact hA.ks b h1 (by omega) (by omega) y hy ⟨g1, g2⟩
  refine ⟨σ', heq, hR.frame hP0 (fun b hb hf => hw.mem_eq hb fun hsw => ?_) hK.ikview,
    sre_slotw hPl hS hA hSA hw hK, ⟨hw, hK.keepCV hKC⟩, G', hPl, ⟨hSt', hV', hM', hC', hI'⟩, hFI', ?_, ?_, ?_,
    hSA.mono (fun p y n hp => ⟨y, hK.sc' hp⟩)⟩
  · obtain ⟨y, hy, g1, g2⟩ := slotWd_range hPl hsw
    exact hA.slot _ (IFoot.iwords hP0 hf) y hy ⟨g1, g2⟩
  · rw [hw.1]
    exact hD.of_same hDS (by have := congrArg Fl4Spec.AbstractState.domainList hK.1; exact this)
      (by have := congrArg Fl4Spec.AbstractState.domainStartIndex hK.1; exact this)
  · rw [hw.1]; exact (hstep huc).okv hMO
  · rw [hw.1]; exact hA

end Insert


/-! ## A badge into the receive buffer -/

section Buf
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **Writing a word of a mapped IPC buffer** refines `store_word_offs` on
the composite relation. -/
theorem buf_set_top (hP0 : IPlaced N T E R B) {th : TypedHeap} {G : MdbGhost} {s : S} {σ : Fl4Spec.State Unit}
    (hB : RelTopB (L := L) th G N T C E R B c s σ) (hR : IpcRel N T E R B (L.mem s) σ)
    (hS : SRE st N T C E R B c s σ) {w : U64} {p : Fl4Spec.Word} (hm : BufMap B w p) {k : U64} (hk : k.val < 128)
    (v : U64) (hu : Fl4Spec.inUserFrame (bufAddr p k.val) σ) :
    msg.buf_set st s w k v ⦃ s' => s' = L.wr s (fl4BufA w k) v ∧
      Fl4Spec.storeWordOffs (Z := Unit) p k.val v.bv σ =
        ({((), setUm σ (storeMem σ.machineState.underlyingMemory (bufAddr p k.val) v.bv))}, False) ∧
      IpcRel N T E R B (L.mem s') (setUm σ (storeMem σ.machineState.underlyingMemory (bufAddr p k.val) v.bv)) ∧
      SRE st N T C E R B c s' (setUm σ (storeMem σ.machineState.underlyingMemory (bufAddr p k.val) v.bv)) ∧
      RelTopB (L := L) th G N T C E R B c s'
        (setUm σ (storeMem σ.machineState.underlyingMemory (bufAddr p k.val) v.bv)) ⦄ := by
  refine WP.spec_mono (msg.buf_set.spec s w k v) ?_
  rintro s' rfl
  have hw := hm k hk
  set wp : U64 × Fl4Spec.Word := (fl4BufA w k, bufAddr p k.val) with hwp
  have hal := hP0.e.balign wp hw
  set σ' := setUm σ (storeMem σ.machineState.underlyingMemory (bufAddr p k.val) v.bv) with hσ'
  have hag := agree_wr (L := L) (s := s) (v := v) hal.1
  have g : ∀ a, Aligned a → a.val ≠ wp.1.val → L.mem (L.wr s wp.1 v) a = L.mem s a := fun a ha h => hag a ha h
  have hE := hR.toE.upd_buf hP0.e hw v hag (rd_wr_eq hal.1)
  have hkv : Notif.KView σ σ' := ⟨fun _ _ h => h, fun _ x h => ⟨x, h, rfl, rfl, rfl⟩⟩
  have hN := hR.toN.frame hP0.n (fun a ha hf => g a ha fun hv => by
    rcases hf with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩
    · have := hP0.nb n hn wp hw; omega
    · have hta := hP0.e.tcb t ht
      have := hP0.e.bt wp hw t ht
      have hv' : a.val = (tStA t).val ∨ a.val = (tBlockA t).val ∨ a.val = (badgeRegA t).val ∨
          a.val = (prioA t).val ∨ a.val = (nextA .Ep t).val ∨ a.val = (prevA .Ep t).val := by
        rcases h with h | h | h | h | h | h <;> simp [h]
      rw [val_st hta, val_blk hta, val_prio hta, val_next hta, val_prev hta, badgeRegA_eq_regA,
        regA_val hta (regIdx_lt _)] at hv'
      have := regIdx_lt Fl4Spec.badge_register
      omega) hkv
  have hR' : IpcRel N T E R B (L.mem (L.wr s wp.1 v)) σ' := by
    refine IpcRel.of hN hE fun t ht x hx => ?_
    have hta := hP0.e.tcb t ht
    rw [hR.sc t ht x hx, g _ (scA_aligned hta) (by
      rw [scA_val hta]; have := hP0.e.bt wp hw t ht; omega)]
  have hW : WritesIn st s (L.wr s wp.1 v) (EWrite T E R B) :=
    (writesIn_wr hal.1).mono fun b hb => Or.inr (Or.inr (Or.inr ⟨_, hw, hb⟩))
  refine ⟨rfl, storeWordOffs_eq σ p k.val v.bv hal.2 hu, hR', ⟨hS.1.stableE hP0.e hS.2 hW (EpStep.setUm' _ _),
    hS.2.mono hW.1 (SzKeep.of_kheap rfl)⟩, hB.frameN hW (fun a ha => Or.inl (EWrite.iwords ha))
    (CKeep.of_eq rfl rfl rfl) rfl rfl (SzKeep.of_kheap rfl)⟩

end Buf


/-! ## The spec's transfer loop, one cap at a time -/

section SpecLoop
open Fl4Spec

/-- The message info a transfer ends with after `n` caps. -/
def miAt (mi : MessageInfo) (n : Nat) : MessageInfo :=
  ⟨mi.miLength, BitVec.ofNat 64 n, mi.miCapsUnwrapped, mi.miLabel⟩

/-- The message info after unwrapping the `n`-th cap. -/
def miUnwrap (mi : MessageInfo) (n : Nat) : MessageInfo :=
  ⟨mi.miLength, mi.miExtraCaps, mi.miCapsUnwrapped ||| ((1 : Data) <<< n), mi.miLabel⟩

variable {ep : Option ObjRef} {rb : ObjRef} {σ : State Unit}

theorem tcl_nil (n : Nat) (slots : List CslotPtr) (mi : MessageInfo) :
    transferCapsLoop (Z := Unit) ep rb n [] slots mi σ = ({(miAt mi n, σ)}, False) := rfl

theorem tcl_badge {n : Nat} {cap : Cap} {slot : CslotPtr} {more : List (Cap × CslotPtr)} {slots : List CslotPtr}
    {mi : MessageInfo} {σ1 σ2 : State Unit} {r : MessageInfo}
    (hc : isEpCap cap ∧ ep = some (objRefOf cap))
    (h1 : setExtraBadge (Z := Unit) rb (capEpBadge cap) n σ = ({((), σ1)}, False))
    (h2 : transferCapsLoop (Z := Unit) ep rb (n + 1) more slots (miUnwrap mi n) σ1 = ({(r, σ2)}, False)) :
    transferCapsLoop (Z := Unit) ep rb n ((cap, slot) :: more) slots mi σ = ({(r, σ2)}, False) := by
  rw [transferCapsLoop]
  unfold constOnFailure
  refine Vs.catch_ok ?_
  rw [run_bind_ok (run_returnOk _ σ), if_pos hc, run_bind_ok_st (run_liftE' h1)]
  exact run_liftE' h2

theorem tcl_insert {n : Nat} {cap cap' : Cap} {slot d : CslotPtr} {more : List (Cap × CslotPtr)}
    {rest : List CslotPtr} {mi : MessageInfo} {σ1 σ2 : State Unit} {r : MessageInfo}
    (hc : ¬ (isEpCap cap ∧ ep = some (objRefOf cap)))
    (hd : (deriveCap (Z := Unit) slot cap).run σ = ({(.ok cap', σ)}, False)) (hn : cap' ≠ .nullCap)
    (hi : capInsert (Z := Unit) cap' slot d σ = ({((), σ1)}, False))
    (h2 : transferCapsLoop (Z := Unit) ep rb (n + 1) more rest mi σ1 = ({(r, σ2)}, False)) :
    transferCapsLoop (Z := Unit) ep rb n ((cap, slot) :: more) (d :: rest) mi σ = ({(r, σ2)}, False) := by
  rw [transferCapsLoop]
  unfold constOnFailure
  refine Vs.catch_ok ?_
  rw [run_bind_ok (run_returnOk _ σ), if_neg hc, if_pos (List.cons_ne_nil d rest), run_bind_ok hd]
  unfold NonDetE.whenE
  rw [if_neg hn]
  rw [run_bind_ok (show (pure () : NonDetE (State Unit) SyscallError Unit).run σ = ({(.ok (), σ)}, False) from rfl)]
  refine (run_bind_ok_st (m := NonDetE.liftE (capInsert (Z := Unit) cap' slot (the (d :: rest).head?)))
    (run_liftE' hi) _).trans ?_
  exact run_liftE' h2

theorem tcl_derr {n : Nat} {cap : Cap} {slot d : CslotPtr} {more : List (Cap × CslotPtr)}
    {rest : List CslotPtr} {mi : MessageInfo} {e : SyscallError}
    (hc : ¬ (isEpCap cap ∧ ep = some (objRefOf cap)))
    (hd : (deriveCap (Z := Unit) slot cap).run σ = ({(.error e, σ)}, False)) :
    transferCapsLoop (Z := Unit) ep rb n ((cap, slot) :: more) (d :: rest) mi σ = ({(miAt mi n, σ)}, False) := by
  rw [transferCapsLoop]
  unfold constOnFailure
  rw [Vs.catch_err (e := e) (σ' := σ)]
  · rfl
  rw [run_bind_ok (run_returnOk _ σ), if_neg hc, if_pos (List.cons_ne_nil d rest), run_bind_error hd]

theorem tcl_dnull {n : Nat} {cap : Cap} {slot d : CslotPtr} {more : List (Cap × CslotPtr)}
    {rest : List CslotPtr} {mi : MessageInfo}
    (hc : ¬ (isEpCap cap ∧ ep = some (objRefOf cap)))
    (hd : (deriveCap (Z := Unit) slot cap).run σ = ({(.ok .nullCap, σ)}, False)) :
    transferCapsLoop (Z := Unit) ep rb n ((cap, slot) :: more) (d :: rest) mi σ = ({(miAt mi n, σ)}, False) := by
  rw [transferCapsLoop]
  unfold constOnFailure
  rw [Vs.catch_err (e := undefined) (σ' := σ)]
  · rfl
  rw [run_bind_ok (run_returnOk _ σ), if_neg hc, if_pos (List.cons_ne_nil d rest), run_bind_ok hd]
  unfold NonDetE.whenE
  rw [if_pos rfl]
  exact run_bind_error (run_throwError _ σ) _

theorem tcl_noslot {n : Nat} {cap : Cap} {slot : CslotPtr} {more : List (Cap × CslotPtr)} {mi : MessageInfo}
    (hc : ¬ (isEpCap cap ∧ ep = some (objRefOf cap))) :
    transferCapsLoop (Z := Unit) ep rb n ((cap, slot) :: more) [] mi σ = ({(miAt mi n, σ)}, False) := by
  rw [transferCapsLoop]
  unfold constOnFailure
  refine Vs.catch_ok ?_
  rw [run_bind_ok (run_returnOk _ σ), if_neg hc, if_neg (fun h => h rfl)]
  rfl

end SpecLoop




/-! ## Unwrapping an endpoint cap -/

section Unwrap

/-- The badge of an endpoint cap. -/
def epBadgeW : capability.Cap → U64
  | .Endpoint _ b _ _ _ _ => b
  | _ => 0#u64

/-- FL4's unwrap test is the spec's (`is_ep_cap` of the transfer's endpoint). -/
def UnwrapP (ep : U64) (a : Fl4Spec.Cap) : Prop :=
  Fl4Spec.isEpCap a = true ∧ some ep.bv = some (Fl4Spec.objRefOf a)

instance (ep : U64) (a : Fl4Spec.Cap) : Decidable (UnwrapP ep a) := by unfold UnwrapP; infer_instance

theorem unwrap_eq (c : capability.Cap) (ep : U64) :
    ipc.unwrapped_badge c ep = ok (if UnwrapP ep (absCap c) then some (epBadgeW c) else none) := by
  cases c <;> simp [ipc.unwrapped_badge, absCap, UnwrapP, Fl4Spec.isEpCap, Fl4Spec.objRefOf, epBadgeW]
  rename_i p b s r g gr
  by_cases h : p = ep
  · subst h; simp
  · have : ¬ ep.bv = p.bv := fun e => h (P1.eq_of_bv e.symm)
    simp [h, this]

theorem capEpBadge_of {c : capability.Cap} {ep : U64} (h : UnwrapP ep (absCap c)) :
    Fl4Spec.capEpBadge (absCap c) = (epBadgeW c).bv := by
  cases c <;> simp [UnwrapP, absCap, Fl4Spec.isEpCap] at h
  rfl

/-- FL4's cap at a source and the spec's agree on the unwrap test and the
badge. -/
def UwEq (ep : U64) (cv : capability.Cap) (a : Fl4Spec.Cap) : Prop :=
  (UnwrapP ep (absCap cv) ↔ UnwrapP ep a) ∧ (UnwrapP ep a → (epBadgeW cv).bv = Fl4Spec.capEpBadge a)

theorem UwEq.of_abs {ep : U64} {cv : capability.Cap} {a : Fl4Spec.Cap} (h : absCap cv = a) : UwEq ep cv a := by
  subst h; exact ⟨Iff.rfl, fun h => (capEpBadge_of h).symm⟩

/-- The unwrap test reads only a cap's shape. -/
theorem unwrap_shape (ep : U64) (c : capability.Cap) : UnwrapP ep (absCap c) ↔ UnwrapP ep (absCap (shape c)) := by
  cases c <;> simp [UnwrapP, absCap, shape, Fl4Spec.isEpCap, Fl4Spec.objRefOf]

theorem not_unwrap_of_null {ep : U64} : ¬ UnwrapP ep (absCap .Null) := by
  simp [UnwrapP, absCap, Fl4Spec.isEpCap]

theorem not_unwrap_of_ut {ep : U64} {c : capability.Cap} (h : ∃ p sb f d, c = .Untyped p sb f d) :
    ¬ UnwrapP ep (absCap c) := by
  obtain ⟨p, sb, f, d, rfl⟩ := h; simp [UnwrapP, absCap, Fl4Spec.isEpCap]

end Unwrap


/-! ## The transfer loop -/

section Loop
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- A source cap of the transfer: the cap in a CNode slot, related to the
spec's. -/
def SrcOK (th : TypedHeap) (m : U64 → U64) (x : U64) (y : Fl4Spec.Cap × Fl4Spec.CslotPtr) : Prop :=
  ∃ ps rs idx cv, th ps = some (.cnode rs) ∧ idx.length = rs ∧ y.2 = (ps.bv, idx) ∧ x = cslotAddr (ps.bv, idx) ∧
    capAt m x = ok cv ∧ y.1 = absCap cv ∧ CapWf cv ∧ EncWf cv ∧ CapValid th cv

/-- The receive slot: an empty CNode slot. -/
def DestOK (th : TypedHeap) (m : U64 → U64) (dest : U64) (d : Fl4Spec.CslotPtr) : Prop :=
  ∃ pd rd idx, th pd = some (.cnode rd) ∧ idx.length = rd ∧ d = (pd.bv, idx) ∧ dest = cslotAddr (pd.bv, idx) ∧
    capAt m dest = ok .Null

/-- FL4's message info and the spec's. -/
def MiRel (out : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo) : Prop :=
  out.length.bv = mi.miLength ∧ out.caps_unwrapped.bv = mi.miCapsUnwrapped ∧ out.label.bv = mi.miLabel

/-- Slot `j` of the extra caps. -/
def exAt (extra : Aeneas.Std.Array obj.Slot 3#usize) (j : Nat) : U64 := extra.val.getD j 0#u64

theorem index_exAt (extra : Aeneas.Std.Array obj.Slot 3#usize) (i : Usize) (hi : i.val < 3) :
    Aeneas.Std.Array.index_usize extra i = ok (exAt extra i.val) := by
  have hl : extra.val.length = 3 := by simpa using extra.property
  unfold Aeneas.Std.Array.index_usize exAt
  have : extra[i]? = some (extra.val[i.val]'(by omega)) := by
    simp [Aeneas.Std.Array.getElem?_Usize_eq, List.getElem?_eq_getElem (by omega : i.val < extra.val.length)]
  rw [this, List.getD_eq_getElem _ _ (by omega)]

theorem cast_us_val (i : U64) (h : i.val < 3) : (UScalar.cast .Usize i).val = i.val := by
  rw [UScalar.cast_val_eq]
  refine Nat.mod_eq_of_lt ?_
  rw [UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> omega

end Loop

section Loop2
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem CnK.inUserFrame {σ σ' : Fl4Spec.State Unit} (h : CnK σ σ') {a : Fl4Spec.Word}
    (hu : Fl4Spec.inUserFrame a σ) : Fl4Spec.inUserFrame a σ' := by
  obtain ⟨sz, hsz⟩ := hu
  exact ⟨sz, h.other hsz (fun _ _ e => by cases e) (fun _ e => by cases e)⟩

/-- The words the transfer loop writes: slot words and receive-buffer words. -/
def FW (th : TypedHeap) (B : Set (U64 × Fl4Spec.Word)) (b : U64) : Prop := Sched.SlotWd th b ∨ BufW B b

/-- **The transfer loop's invariant** at FL4's state `x` (state, message
info, receive slot, index). -/
def TInv (th : TypedHeap) (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ep : U64) (rb : Fl4Spec.Word) (s0 : S) (σ0 : Fl4Spec.State Unit) (dest0 : U64)
    (slots0 : List Fl4Spec.CslotPtr) (mi0 : Fl4Spec.MessageInfo) (x : S × msginfo.MessageInfo × obj.Slot × U64) :
    Prop :=
  ∃ σ mi slots, x.2.2.2.val ≤ caps.length ∧ MiRel x.2.1 mi ∧ mi.miLength = mi0.miLength ∧
    mi.miLabel = mi0.miLabel ∧
    (∀ r σf, Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb x.2.2.2.val (caps.drop x.2.2.2.val) slots mi σ =
        ({(r, σf)}, False) →
      Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb 0 caps slots0 mi0 σ0 = ({(r, σf)}, False)) ∧
    IpcRel N T E R B (L.mem x.1) σ ∧ SRE st N T C E R B c x.1 σ ∧ (∃ G, RelTopB (L := L) th G N T C E R B c x.1 σ) ∧
    (∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rb k) σ) ∧
    (∀ j (hj : j < caps.length), x.2.2.2.val ≤ j →
      ∃ cv, capAt (L.mem x.1) (exAt extra j) = ok cv ∧ UwEq ep cv (caps[j]).1) ∧
    ((x.2.2.1 = 0#u64 ∧ slots = []) ∨
      (x.2.2.1 = dest0 ∧ slots = slots0 ∧ dest0 ≠ 0#u64 ∧ SlotsSame th (L.mem s0) (L.mem x.1) ∧ σ.cdt = σ0.cdt)) ∧
    KeepCV σ0 σ ∧ WritesIn st s0 x.1 (FW th B) ∧ x.2.1.caps_unwrapped.val < 8

/-- The transfer loop's result. -/
def TPost (th : TypedHeap) (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (ep : U64) (rb : Fl4Spec.Word)
    (s0 : S) (σ0 : Fl4Spec.State Unit) (slots0 : List Fl4Spec.CslotPtr) (mi0 : Fl4Spec.MessageInfo)
    (y : S × msginfo.MessageInfo × U64) : Prop :=
  ∃ σ' mf, Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb 0 caps slots0 mi0 σ0 = ({(mf, σ')}, False) ∧
    MiRel y.2.1 mf ∧ mf.miExtraCaps = BitVec.ofNat 64 y.2.2.val ∧
    y.2.1.caps_unwrapped.val < 8 ∧ y.2.2.val ≤ 3 ∧ mf.miLabel = mi0.miLabel ∧
    IpcRel N T E R B (L.mem y.1) σ' ∧ SRE st N T C E R B c y.1 σ' ∧ (KeepCV σ0 σ' ∧ WritesIn st s0 y.1 (FW th B)) ∧
    ∃ G, RelTopB (L := L) th G N T C E R B c y.1 σ'

/-- A loop exit with the spec's loop ending at the same index. -/
theorem tpost_of {th : TypedHeap} {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {ep : U64} {rb : Fl4Spec.Word}
    {σ0 σ : Fl4Spec.State Unit} {slots0 slots : List Fl4Spec.CslotPtr} {mi0 mi : Fl4Spec.MessageInfo} {s : S}
    {out : msginfo.MessageInfo} {i : U64}
    (hmi : MiRel out mi)
    (hch : ∀ r σf, Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb i.val (caps.drop i.val) slots mi σ =
        ({(r, σf)}, False) →
      Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb 0 caps slots0 mi0 σ0 = ({(r, σf)}, False))
    (hend : Fl4Spec.transferCapsLoop (Z := Unit) (some ep.bv) rb i.val (caps.drop i.val) slots mi σ =
      ({(miAt mi i.val, σ)}, False))
    (hcu : out.caps_unwrapped.val < 8) (hi3 : i.val ≤ 3) (hlb : mi.miLabel = mi0.miLabel)
    (hR : IpcRel N T E R B (L.mem s) σ) (hS : SRE st N T C E R B c s σ) {s0 : S} (hK : KeepCV σ0 σ)
    (hW : WritesIn st s0 s (FW th B))
    (hB : ∃ G, RelTopB (L := L) th G N T C E R B c s σ) :
    TPost (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps ep rb s0 σ0
      slots0 mi0 (s, out, i) :=
  ⟨σ, miAt mi i.val, hch _ _ hend, hmi, rfl, hcu, hi3, hlb, hR, hS, ⟨hK, hW⟩, hB⟩

end Loop2

section Loop3
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem buf_caps_eq : msg.BUF_CAPS = ok 122#u64 := by
  unfold msg.BUF_CAPS msg.BUF_USER_DATA msg.MSG_MAX_LENGTH
  obtain ⟨z, hz, hzv⟩ := spec_exists (U64.add_spec (x := 1#u64) (y := 120#u64) (by scalar_tac))
  rw [hz]; simp only [bind_ok]
  obtain ⟨z2, hz2, hzv2⟩ := spec_exists (U64.add_spec (x := z) (y := 1#u64) (by scalar_tac))
  rw [hz2]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hzv2, hzv]; rfl

theorem SlotsSame.trans' {th : TypedHeap} {m1 m2 m3 : U64 → U64} (h1 : SlotsSame th m1 m2) (h2 : SlotsSame th m2 m3) :
    SlotsSame th m1 m3 := fun a ha =>
  let ⟨a1, a2, a3, a4⟩ := h1 a ha
  let ⟨b1, b2, b3, b4⟩ := h2 a ha
  ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩

set_option maxHeartbeats 8000000 in
/-- **One step of the transfer loop.** -/
theorem tc_body (hP0 : IPlaced N T E R B) {th : TypedHeap} {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {ep rbw : U64} {rb : Fl4Spec.Word} {s0 : S}
    {σ0 : Fl4Spec.State Unit} {dest0 : U64} {slots0 : List Fl4Spec.CslotPtr} {mi0 : Fl4Spec.MessageInfo}
    (hlen : caps.length ≤ 3)
    (hsrc : ∀ j (hj : j < caps.length), SrcOK th (L.mem s0) (exAt extra j) caps[j])
    (hnull : ∀ j, caps.length ≤ j → j < 3 → exAt extra j = 0#u64)
    (hdest : dest0 ≠ 0#u64 → ∃ d, slots0 = [d] ∧ DestOK th (L.mem s0) dest0 d)
    (hm : BufMap B rbw rb) (x : S × msginfo.MessageInfo × obj.Slot × U64)
    (hx : TInv (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps extra ep rb
      s0 σ0 dest0 slots0 mi0 x) :
    ipc.transfer_caps_loop.body st extra ep rbw x.1 x.2.1 x.2.2.1 x.2.2.2 ⦃ r => match r with
      | .done y => TPost (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps ep
          rb s0 σ0 slots0 mi0 y
      | .cont x' => TInv (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps
          extra ep rb s0 σ0 dest0 slots0 mi0 x' ∧ 3 - x'.2.2.2.val < 3 - x.2.2.2.val ⦄ := by
  obtain ⟨s, out, dest, i⟩ := x
  obtain ⟨σ, mi, slots, hi, hmi, hml, hmlb, hch, hR, hS, ⟨G, hB⟩, hu, hpend, hdst, hK0, hW0, hcu⟩ := hx
  dsimp only at hi hmi hch hR hS hB hpend hdst ⊢
  have hPl : Placed th := hB.1
  unfold ipc.transfer_caps_loop.body
  by_cases h3 : i < 3#u64
  · have hi3 : i.val < 3 := by scalar_tac
    rw [if_pos h3]
    simp only [lift, bind_ok]
    rw [index_exAt extra _ (by rw [cast_us_val i hi3]; exact hi3), cast_us_val i hi3]
    simp only [bind_ok, obj.Slot.is_null]
    by_cases hlt : i.val < caps.length
    · obtain ⟨ps, rs, idx, cv0, hps, hls, hsl, hxa, hcv0, habs0, hw0, he0, hcvv0⟩ := hsrc i.val hlt
      have hsI : IsSlot th (exAt extra i.val) := by
        rw [hxa]; exact AbsSlot.isSlot (⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩ : AbsSlot th (ps.bv, idx))
      have hne : exAt extra i.val ≠ 0#u64 := hsI.ne_zero hPl
      simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨cv, hcv, huw⟩ := hpend i.val hlt le_rfl
      rw [slot_cap_eq, hcv]
      simp only [bind_ok]
      rw [unwrap_eq]
      simp only [bind_ok]
      have hdrop : caps.drop i.val = caps[i.val] :: caps.drop (i.val + 1) := List.drop_eq_getElem_cons hlt
      by_cases hu' : UnwrapP ep (absCap cv)
      · rw [if_pos hu']
        simp only [buf_caps_eq, bind_ok]
        have hk : (core.num.U64.wrapping_add 122#u64 i).val = 122 + i.val := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        refine WP.spec_bind (buf_set_top hP0 hB hR hS hm (k := core.num.U64.wrapping_add 122#u64 i)
          (by rw [hk]; omega) (epBadgeW cv) (hu _ (by rw [hk]; omega))) ?_
        rintro s2 ⟨rfl, hst, hR2, hS2, hB2⟩
        try simp only [lift, bind_ok]
        have hand : (i &&& 63#u64).val = i.val := by
          rw [UScalar.val_and]
          have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
          rcases this with h | h | h <;> rw [h] <;> rfl
        obtain ⟨i6, h6e, h6v, h6⟩ := spec_exists (U64.ShiftLeft_spec 1#u64 (i &&& 63#u64) (by rw [hand]; omega))
        have hi6 : i6.val < 8 := by
          rw [h6v, hand]
          rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 by omega) with h | h | h <;> rw [h] <;>
            simp [U64.size, U64.numBits]
        rw [h6e]
        simp only [bind_ok]
        obtain ⟨i8, h8e, h8⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
        rw [h8e, bind_ok, WP.spec_ok]
        have hi8 : i8.val = i.val + 1 := by simpa using h8
        set σ1 := setUm σ (storeMem σ.machineState.underlyingMemory (bufAddr rb (core.num.U64.wrapping_add 122#u64 i).val)
          (epBadgeW cv).bv) with hσ1
        have hwp := hm _ (by rw [hk]; omega : (core.num.U64.wrapping_add 122#u64 i).val < 128)
        have hal := (hP0.e.balign _ hwp).1
        have hSS : SlotsSame th (L.mem s) (L.mem (L.wr s (fl4BufA rbw (core.num.U64.wrapping_add 122#u64 i))
            (epBadgeW cv))) :=
          slotsSame_wr hPl s _ hal fun a ha h => hB.2.2.2.2.2.1.slot _
            (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hwp, le_refl _, by omega⟩)))) a ha h
        refine ⟨⟨σ1, miUnwrap mi i.val, slots, by rw [hi8]; omega, ⟨hmi.1, ?_, hmi.2.2⟩, hml, hmlb, ?_, hR2, hS2,
          ⟨G, hB2⟩, fun k hk => (inUserFrame_setUm _ _ _).2 (hu k hk), fun j hj hij => ?_, ?_, ⟨fun p => hK0.1 p, hK0.2⟩,
          (hW0.trans (writesIn_wr hal)).mono fun b h => h.elim id (fun e => Or.inr ⟨_, hwp, e⟩),
          by show (out.caps_unwrapped ||| i6).val < 2 ^ 3; rw [UScalar.val_or]; exact Nat.or_lt_two_pow hcu hi6⟩,
          by rw [hi8]; omega⟩
        · show (out.caps_unwrapped ||| i6).bv = mi.miCapsUnwrapped ||| ((1 : Fl4Spec.Data) <<< i.val)
          rw [UScalar.bv_or, h6, hand]; exact congrArg₂ (· ||| ·) hmi.2.1 rfl
        · intro r σf hr
          refine hch r σf ?_
          rw [hdrop]
          refine tcl_badge (hc := huw.1.mp hu') ?_
            (by rw [hi8] at hr; exact hr)
          unfold Fl4Spec.setExtraBadge
          show Fl4Spec.storeWordOffs rb (Fl4Spec.bufferCptrIndex + i.val) (Fl4Spec.capEpBadge (caps[i.val]).1) σ = _
          rw [← huw.2 (huw.1.mp hu')]
          rw [show Fl4Spec.bufferCptrIndex + i.val = (core.num.U64.wrapping_add 122#u64 i).val by
            rw [hk]; rfl]
          exact hst
        · obtain ⟨cv', h1, h2⟩ := hpend j hj (by rw [hi8] at hij; omega)
          exact ⟨cv', by rw [hSS.capAt (by
            obtain ⟨ps', rs', idx', cv'', hps', hls', -, hxa', -⟩ := hsrc j hj
            rw [hxa']; exact AbsSlot.isSlot (⟨ps', rfl, Or.inl (by simpa [hls'] using hps')⟩ :
              AbsSlot th (ps'.bv, idx')))]; exact h1, h2⟩
        · rcases hdst with h | ⟨h1, h2, h3', h4, h5⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, h2, h3', SlotsSame.trans' h4 hSS, h5⟩
      · rw [if_neg hu']
        simp only []
        rcases hdst with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hd0, hSS, hcdt⟩
        · simp only [decide_true, ↓reduceIte, WP.spec_ok]
          refine tpost_of hmi hch ?_ hcu (by omega) hmlb hR hS hK0 hW0 ⟨G, hB⟩
          rw [hdrop]
          exact tcl_noslot (fun h => hu' (huw.1.mpr h))
        · obtain ⟨d, hsl0, ⟨pd, rd, idxd, hpd, hld, rfl, hdA, hdN⟩⟩ := hdest hd0
          subst hsl0
          simp only [hd0, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hcvs : capAt (L.mem s) (exAt extra i.val) = ok cv0 := by rw [hSS.capAt hsI, hcv0]
          rw [hcv] at hcvs
          have hcvs' : cv = cv0 := by simpa using hcvs
          subst hcvs'
          have hsl' : (caps[i.val]).2 = (ps.bv, idx) := hsl
          have hnot : ¬ UnwrapP ep (caps[i.val]).1 := fun h => hu' (huw.1.mpr h)
          have hAs : AbsSlot th (ps.bv, idx) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
          have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
          have hdI : IsSlot th dest := by rw [hdA]; exact hAd.isSlot
          have hncs : cv ≠ .Null → NoChildrenRel (st := st) s σ (exAt extra i.val) (caps[i.val]).2 := by
            intro hut
            obtain ⟨-, ⟨-, -, hM, hC, hI⟩, -⟩ := hB
            rw [hsl', hxa]
            refine noChildren_of_adj th hPl s σ G hM hC (hI.parentAdj (th := th)) _ hAs
              ((hM.members _).2 ⟨hAs.isSlot, cv, by rw [← hxa]; exact hcv, ?_⟩)
            exact hut
          obtain ⟨r, hr, r', hr', hdr⟩ := derive_rel (Z := Unit) s σ (exAt extra i.val) (caps[i.val]).2 cv hw0 he0
            (fun h => hncs (by rintro rfl; exact h))
          rw [← habs0] at hr'
          rw [hr]
          simp only [bind_ok]
          cases r with
          | Err e =>
            cases r' with
            | ok _ => exact hdr.elim
            | error e' =>
              simp only [WP.spec_ok]
              refine tpost_of hmi hch ?_ hcu (by omega) hmlb hR hS hK0 hW0 ⟨G, hB⟩
              rw [hdrop]
              exact tcl_derr hnot hr'
          | Ok c' =>
            cases r' with
            | error _ => exact hdr.elim
            | ok a' =>
              obtain ⟨hw', ha', he', hv', hk'⟩ := hdr
              simp only []
              by_cases hn : c' = .Null
              · subst hn
                rw [cap_is_null_null]
                simp only [bind_ok, ↓reduceIte, WP.spec_ok]
                refine tpost_of hmi hch ?_ hcu (by omega) hmlb hR hS hK0 hW0 ⟨G, hB⟩
                rw [hdrop]
                rw [← ha'] at hr'
                exact tcl_dnull hnot hr'
              · rw [cap_is_null_ne hn]
                simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
                have hcvn : cv ≠ .Null := by
                  rintro rfl; unfold objects.derive_cap at hr; simp at hr; exact hn hr.symm
                obtain ⟨hsh, hbd, hzb, hnu⟩ := derive_shape hr hn (hncs hcvn)
                have hsnn : cv ≠ .Null := fun h => hn ((Vs.shape_kind hsh).2.2.2.2.2 h)
                have hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idx)) = ok cv := by rw [← hxa]; exact hcv
                have hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null := by
                  rw [← hdA, hSS.capAt hdI]; exact hdN
                have hut : isUt cv = true → ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idx)) := by
                  intro hu0 y hy
                  obtain ⟨z, hz⟩ := desc_tail_child hy
                  exact hnu hu0 (by rw [hsl']; exact (hB.2.1.2.2.2.1.has_child_iff hPl hAs).2 ⟨z, hz⟩)
                have hsI' : IsSlot th (cslotAddr (ps.bv, idx)) := hAs.isSlot
                have hnx : nextOf (L.mem s) (cslotAddr (ps.bv, idx)) = 0#u64 ∨
                    IsSlot th (nextOf (L.mem s) (cslotAddr (ps.bv, idx))) := by
                  have hm := (hB.2.1.2.2.1.members _).2 ⟨hsI', cv, hsrcC, hsnn⟩
                  rcases hB.2.1.2.2.1.next_mem hm with h | ⟨h, -⟩
                  · exact Or.inl h
                  · exact Or.inr ((hB.2.1.2.2.1.members _).1 h).1
                have hins := WP.spec_and (insert_top hP0 hB hR hS hps hpd hls hld hsrcC hsnn hdst c' a' ⟨hw', ha'⟩
                  (hv' th hcvv0) he' hn hsh (Or.inl hbd) hut hzb (derive_okey hr hn)
                  (fun P L4 L3 L2 L1 => derive_vcap hr P L4 L3 L2 L1) (derive_ut hr))
                  (insert_capfr2 hPl s c' _ _ hsI' hAd.isSlot cv hsrcC he0 he' hnx)
                rw [← hxa, ← hdA] at hins
                refine WP.spec_bind hins ?_
                rintro s2 ⟨⟨σ2, hci, hR2, hS2, ⟨hW2, hK2⟩, G2, hB2⟩, hfr⟩
                obtain ⟨i3, h3e, h3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
                rw [h3e, bind_ok, WP.spec_ok]
                have hi3v : i3.val = i.val + 1 := by simpa using h3v
                have hmem : ((), σ2) ∈ (Fl4Spec.capInsert (Z := Unit) a' (ps.bv, idx) (pd.bv, idxd) σ).1 := by
                  rw [hci]; rfl
                have hK := capInsert_nkn a' _ _ σ _ hmem
                refine ⟨⟨σ2, mi, [], by rw [hi3v]; omega, hmi, hml, hmlb, fun r σf hr0 => ?_, hR2, hS2, ⟨G2, hB2⟩,
                  fun k hk => hK.inUserFrame (hu k hk), fun j hj hij => ?_, Or.inl ⟨rfl, rfl⟩, hK0.trans hK2,
                  (hW0.trans hW2).mono fun b h => h.elim id Or.inl, hcu⟩, by rw [hi3v]; omega⟩
                · refine hch r σf ?_
                  rw [hdrop]
                  refine tcl_insert hnot hr' (fun h => hn ((CapRel.null_iff ⟨hw', ha'⟩).1 h)) ?_
                    (by rw [hi3v] at hr0; exact hr0)
                  show Fl4Spec.capInsert a' (caps[i.val]).2 (pd.bv, idxd) σ = _
                  rw [hsl']; exact hci
                · obtain ⟨cv', h1, h2⟩ := hpend j hj (by rw [hi3v] at hij; omega)
                  obtain ⟨ps', rs', idx', cv'', hps', hls', -, hxa', -⟩ := hsrc j hj
                  have hjI : IsSlot th (exAt extra j) := by
                    rw [hxa']; exact AbsSlot.isSlot (⟨ps', rfl, Or.inl (by simpa [hls'] using hps')⟩ :
                      AbsSlot th (ps'.bv, idx'))
                  obtain ⟨-, -, -, cvj, -, -, -, -, hcvj, habsj, -⟩ := hsrc j hj
                  have hsrcfull : ∀ c'', fullF cv c' = some c'' → ¬ UnwrapP ep (absCap cv) := fun c'' hf =>
                    not_unwrap_of_ut (by
                      cases cv <;> simp [fullF] at hf
                      exact ⟨_, _, _, _, rfl⟩)
                  by_cases ejd : exAt extra j = dest
                  · refine ⟨c', by rw [ejd]; exact hfr.2.1, ?_, fun h => ?_⟩
                    · rw [ejd, hdN] at hcvj
                      have : cvj = .Null := by simpa using hcvj.symm
                      rw [habsj, this]
                      refine ⟨fun h => absurd ((unwrap_shape ep cv).2 (hsh ▸ (unwrap_shape ep c').1 h)) hu',
                        fun h => absurd h not_unwrap_of_null⟩
                    · rw [ejd, hdN] at hcvj
                      have : cvj = .Null := by simpa using hcvj.symm
                      rw [habsj, this] at h; exact absurd h not_unwrap_of_null
                  · rcases hfr.2.2 _ hjI ejd with heq | ⟨ejs, c'', hfc, hc''⟩
                    · exact ⟨cv', by rw [heq]; exact h1, h2⟩
                    · rw [ejs, hcv0] at hcvj
                      have : cvj = cv := by simpa using hcvj.symm
                      have hnu := hsrcfull c'' hfc
                      have hnu'' := not_unwrap_of_ut (ep := ep) (fullF_ut hfc)
                      refine ⟨c'', hc'', ⟨fun h => absurd h hnu'', fun h => ?_⟩, fun h => ?_⟩
                      · rw [habsj, this] at h; exact absurd h hnu
                      · rw [habsj, this] at h; exact absurd h hnu
    · have hieq : i.val = caps.length := by omega
      rw [hnull i.val (by omega) hi3]
      simp only [decide_true, ↓reduceIte, WP.spec_ok]
      refine tpost_of hmi hch ?_ hcu (by omega) hmlb hR hS hK0 hW0 ⟨G, hB⟩
      rw [hieq, List.drop_length, ← hieq]
      exact tcl_nil _ _ _
  · rw [if_neg h3]
    simp only [WP.spec_ok]
    have hieq : i.val = caps.length := by
      have : 3 ≤ i.val := by scalar_tac
      omega
    refine tpost_of hmi hch ?_ hcu (by omega) hmlb hR hS hK0 hW0 ⟨G, hB⟩
    rw [hieq, List.drop_length, ← hieq]
    exact tcl_nil _ _ _

end Loop3


/-! ## The loop and `transfer_caps` -/

section Transfer
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- The receive slot FL4 found and the spec's receive slots. -/
def DestConf (th : TypedHeap) (m : U64 → U64) (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (dest : U64) (slots : List Fl4Spec.CslotPtr) : Prop :=
  (dest = 0#u64 ∧ slots = []) ∨
    (dest ≠ 0#u64 ∧ ∃ d, slots = [d] ∧ DestOK th m dest d)

/-- **The transfer loop refines the spec's** on the composite relation. -/
theorem transfer_loop_top (hP0 : IPlaced N T E R B) {th : TypedHeap} {G : MdbGhost}
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {extra : Aeneas.Std.Array obj.Slot 3#usize} {ep rbw : U64}
    {rb : Fl4Spec.Word} {s0 : S} {σ0 : Fl4Spec.State Unit} {dest0 : U64} {slots0 : List Fl4Spec.CslotPtr}
    {mi0 : Fl4Spec.MessageInfo} (out0 : msginfo.MessageInfo) (hmi0 : MiRel out0 mi0)
    (hcu0 : out0.caps_unwrapped.val < 8) (hB0 : RelTopB (L := L) th G N T C E R B c s0 σ0) (hR0 : IpcRel N T E R B (L.mem s0) σ0)
    (hS0 : SRE st N T C E R B c s0 σ0) (hlen : caps.length ≤ 3)
    (hsrc : ∀ j (hj : j < caps.length), SrcOK th (L.mem s0) (exAt extra j) caps[j])
    (hnull : ∀ j, caps.length ≤ j → j < 3 → exAt extra j = 0#u64)
    (hD : DestConf th (L.mem s0) caps extra dest0 slots0)
    (hm : BufMap B rbw rb) (hu : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rb k) σ0) :
    ipc.transfer_caps_loop st s0 extra ep rbw out0 dest0 0#u64 ⦃ y =>
      TPost (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps ep rb s0 σ0
        slots0 mi0 y ⦄ := by
  have hdest : dest0 ≠ 0#u64 → ∃ d, slots0 = [d] ∧ DestOK th (L.mem s0) dest0 d := fun h => by
    rcases hD with ⟨h0, -⟩ | ⟨-, hd⟩
    · exact absurd h0 h
    · exact hd
  unfold ipc.transfer_caps_loop
  refine loop.spec_decr_nat (fun x => 3 - x.2.2.2.val)
    (TInv (L := L) (st := st) (N := N) (T := T) (C := C) (E := E) (R := R) (B := B) (c := c) th caps extra ep rb
      s0 σ0 dest0 slots0 mi0) _ _ _ (fun x hx => ?_) ?_
  · obtain ⟨s, o, d, i⟩ := x
    have h := tc_body hP0 hlen hsrc hnull hdest hm (s, o, d, i) hx
    refine WP.spec_mono h ?_
    intro r hr
    cases r with
    | done y => exact hr
    | cont x' => exact hr
  · refine ⟨σ0, mi0, slots0, by simp, hmi0, rfl, rfl, fun r σf h => by simpa using h, hR0, hS0, ⟨G, hB0⟩, hu,
      fun j hj _ => ?_, ?_, KeepCV.refl σ0, WritesIn.refl s0 _, hcu0⟩
    · obtain ⟨ps, rs, idx, cv, -, -, -, -, hcv, habs, -⟩ := hsrc j hj
      exact ⟨cv, hcv, UwEq.of_abs habs.symm⟩
    · rcases hD with ⟨h0, h1⟩ | ⟨h0, -⟩
      · exact Or.inl ⟨h0, h1⟩
      · exact Or.inr ⟨rfl, rfl, h0, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩


/-- **`transfer_caps` refines `transfer_caps`** on the composite relation,
from FL4's receive-slot lookup against the spec's (`hG1`, the remaining
named fact of the transfer: `get_receive_slot` against
`get_receive_slots`) and the extra caps related to the spec's
(`hsrc`, `hnull`). -/
theorem transfer_caps_top (hP0 : IPlaced N T E R B) {th : TypedHeap} {G : MdbGhost} {s : S}
    {σ : Fl4Spec.State Unit} (hB : RelTopB (L := L) th G N T C E R B c s σ) (hR : IpcRel N T E R B (L.mem s) σ)
    (hS : SRE st N T C E R B c s σ) (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo)
    (hil : info.length.bv = mi.miLength) (hlb : info.label.bv = mi.miLabel)
    {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hlen : caps.length ≤ 3)
    (hsrc : ∀ j (hj : j < caps.length), SrcOK th (L.mem s) (exAt extra j) caps[j])
    (hnull : ∀ j, caps.length ≤ j → j < 3 → exAt extra j = 0#u64)
    (ep : U64) (receiver : obj.Tcb) (rbw : U64) (rbo : Option Fl4Spec.Word) (hrb : rbw = 0#u64 ↔ rbo = none)
    (hm : ∀ rb, rbo = some rb → BufMap B rbw rb ∧ ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rb k) σ)
    (hGRs : ∀ rb, rbo = some rb → ∃ sl, Fl4Spec.getReceiveSlots (Z := Unit) receiver.bv (some rb) σ = ({(sl, σ)}, False))
    (hG1 : ∀ rb, rbo = some rb → ipc.get_receive_slot st s receiver rbw ⦃ dest => ∃ slots,
      Fl4Spec.getReceiveSlots (Z := Unit) receiver.bv (some rb) σ = ({(slots, σ)}, False) ∧
      DestConf th (L.mem s) caps extra dest slots ⦄) :
    ipc.transfer_caps st s info extra ep receiver rbw ⦃ r => ∃ σ' mf,
      Fl4Spec.transferCaps (Z := Unit) mi caps (some ep.bv) receiver.bv rbo σ = ({(mf, σ')}, False) ∧
      MiRel r.1 mf ∧ r.1.extra_caps.bv = mf.miExtraCaps ∧ IpcRel N T E R B (L.mem r.2) σ' ∧
      r.1.caps_unwrapped.val < 8 ∧ r.1.extra_caps.val ≤ 3 ∧ mf.miLabel = mi.miLabel ∧
      SRE st N T C E R B c r.2 σ' ∧ (KeepCV σ σ' ∧ WritesIn st s r.2 (FW th B)) ∧
      ∃ G', RelTopB (L := L) th G' N T C E R B c r.2 σ' ⦄ := by
  have hmi0 : MiRel { label := info.label, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := info.length }
      ⟨mi.miLength, 0, 0, mi.miLabel⟩ := ⟨hil, rfl, hlb⟩
  -- the spec without caps or without a receive buffer
  have hnone : rbo = none → Fl4Spec.transferCaps (Z := Unit) mi caps (some ep.bv) receiver.bv rbo σ =
      ({(⟨mi.miLength, 0, 0, mi.miLabel⟩, σ)}, False) := by
    rintro rfl
    unfold Fl4Spec.transferCaps
    rw [nd_bind_one (show Fl4Spec.getReceiveSlots (Z := Unit) receiver.bv none σ = ({([], σ)}, False) from rfl),
      nd_pure_bind']
    rfl
  have hnil : caps = [] → ∀ rb, rbo = some rb → Fl4Spec.transferCaps (Z := Unit) mi caps (some ep.bv) receiver.bv rbo σ =
      ({(⟨mi.miLength, 0, 0, mi.miLabel⟩, σ)}, False) := by
    rintro rfl rb rfl
    obtain ⟨sl, hsl⟩ := hGRs rb rfl
    unfold Fl4Spec.transferCaps
    rw [nd_bind_one hsl, nd_pure_bind']
    exact tcl_nil _ _ _
  unfold ipc.transfer_caps msginfo.MessageInfo.new
  simp only [bind_ok]
  rw [index_exAt extra 0#usize (by decide), show ((0#usize : Usize).val) = 0 from rfl]
  simp only [bind_ok, obj.Slot.is_null]
  by_cases h0 : exAt extra 0 = 0#u64
  · have hcn : caps = [] := by
      cases caps with
      | nil => rfl
      | cons y ys =>
        exfalso
        obtain ⟨ps, rs, idx, cv, hps, hls, -, hxa, -⟩ := hsrc 0 (by simp)
        have := (AbsSlot.isSlot (⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩ : AbsSlot th (ps.bv, idx))).ne_zero hB.1
        rw [← hxa] at this; exact this h0
    rw [decide_eq_true h0, if_pos rfl, WP.spec_ok]
    refine ⟨σ, ⟨mi.miLength, 0, 0, mi.miLabel⟩, ?_, hmi0, rfl, hR, by simp, by simp, rfl, hS,
      ⟨KeepCV.refl σ, WritesIn.refl s _⟩, G, hB⟩
    cases e : rbo with
    | none => rw [← e]; exact hnone e
    | some rb => rw [← e]; exact hnil hcn rb e
  · rw [decide_eq_false h0, if_neg Bool.false_ne_true]
    by_cases hr0 : rbw = 0#u64
    · rw [if_pos hr0, WP.spec_ok]
      exact ⟨σ, _, hnone (hrb.1 hr0), hmi0, rfl, hR, by simp, by simp, rfl, hS, ⟨KeepCV.refl σ, WritesIn.refl s _⟩,
        G, hB⟩
    · rw [if_neg hr0]
      obtain ⟨rb, hrbo⟩ : ∃ rb, rbo = some rb := by
        cases e : rbo with
        | none => exact absurd (hrb.2 e) hr0
        | some rb => exact ⟨rb, rfl⟩
      obtain ⟨hmb, hu⟩ := hm rb hrbo
      refine WP.spec_bind (hG1 rb hrbo) ?_
      rintro dest ⟨slots, hsl, hD⟩
      refine WP.spec_bind (transfer_loop_top hP0 _ hmi0 (by simp) hB hR hS hlen hsrc hnull hD hmb hu) ?_
      rintro ⟨s2, out1, i⟩ ⟨σ', mf, hloop, hmi1, hex, hcu1, hi31, hlb1, hR', hS', hF', hB'⟩
      refine (WP.spec_ok _).2 ⟨σ', mf, ?_, hmi1, ?_, hR', hcu1, hi31, hlb1, hS', hF', hB'⟩
      swap
      · show i.bv = mf.miExtraCaps
        rw [hex]; apply BitVec.eq_of_toNat_eq
        show i.val = (BitVec.ofNat 64 i.val).toNat
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by scalar_tac)]
      subst hrbo
      unfold Fl4Spec.transferCaps
      rw [nd_bind_one hsl, nd_pure_bind']
      exact hloop

end Transfer


/-! ## The extra caps (G2) -/

section Extra
open Fl4Spec

variable {ε α β : Type} {f : α → NonDetE (State Unit) ε β} {σ : State Unit}

theorem mapME_nil' : (NonDetE.mapME f []).run σ = ({(.ok [], σ)}, False) := rfl

theorem mapME_cons_ok {a : α} {xs : List α} {b : β} {bs : List β}
    (hf : (f a).run σ = ({(.ok b, σ)}, False)) (hr : (NonDetE.mapME f xs).run σ = ({(.ok bs, σ)}, False)) :
    (NonDetE.mapME f (a :: xs)).run σ = ({(.ok (b :: bs), σ)}, False) := by
  unfold NonDetE.mapME
  rw [run_bind_ok hf, run_bind_ok hr]; rfl

theorem mapME_cons_tail_err {a : α} {xs : List α} {b : β} {e : ε}
    (hf : (f a).run σ = ({(.ok b, σ)}, False)) (hr : (NonDetE.mapME f xs).run σ = ({(.error e, σ)}, False)) :
    (NonDetE.mapME f (a :: xs)).run σ = ({(.error e, σ)}, False) := by
  unfold NonDetE.mapME
  rw [run_bind_ok hf, run_bind_error hr]

theorem mapME_cons_err {a : α} {xs : List α} {e : ε} (hf : (f a).run σ = ({(.error e, σ)}, False)) :
    (NonDetE.mapME f (a :: xs)).run σ = ({(.error e, σ)}, False) := by
  unfold NonDetE.mapME
  rw [run_bind_error hf]

/-- A looked-up extra cap. -/
theorem lcs_ok {t : ObjRef} {cptr : CapRef} {sl : CslotPtr} {rest : CapRef} {a : Cap} (x : ObjRef)
    (h : (lookupSlotForThread (Z := Unit) t cptr).run σ = ({(.ok (sl, rest), σ)}, False))
    (hg : getCap (Z := Unit) sl σ = ({(a, σ)}, False)) :
    (capFaultOnFailure (Z := Unit) x false (lookupCapAndSlot t cptr)).run σ = ({(.ok (a, sl), σ)}, False) := by
  unfold capFaultOnFailure
  apply run_handleE_ok
  unfold lookupCapAndSlot
  rw [run_bind_ok h]
  dsimp only
  rw [run_bind_ok (run_liftE hg)]; rfl

theorem lcs_err {t : ObjRef} {cptr : CapRef} {lf : LookupFailure} (x : ObjRef)
    (h : (lookupSlotForThread (Z := Unit) t cptr).run σ = ({(.error lf, σ)}, False)) :
    (capFaultOnFailure (Z := Unit) x false (lookupCapAndSlot t cptr)).run σ =
      ({(.error (.capFault x false lf), σ)}, False) := by
  unfold capFaultOnFailure
  rw [run_handleE_err]
  · rfl
  unfold lookupCapAndSlot
  rw [run_bind_error h]

end Extra


section ExtraLoop
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- The extra-cap array and the spec's extra caps. -/
def ExtraOK (th : TypedHeap) (m : U64 → U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop :=
  caps.length ≤ 3 ∧ (∀ j (hj : j < caps.length), SrcOK th m (exAt extra j) caps[j]) ∧
    ∀ j, caps.length ≤ j → j < 3 → exAt extra j = 0#u64

/-- The spec's extra cap pointers: words `122 ..` of the sender's buffer. -/
def xCptrs (um : Fl4Spec.Word → Fl4Spec.Word8) (sb : Fl4Spec.Word) (n : Nat) : List Fl4Spec.CapRef :=
  (List.range' 122 n).map (fun k => Fl4Spec.dataToCptr (loadWordAt um (bufAddr sb k)))

/-- The spec's lookup of one extra cap. -/
abbrev xLook (t : Fl4Spec.ObjRef) (cptr : Fl4Spec.CapRef) :
    Fl4Spec.NonDetE (Fl4Spec.State Unit) Fl4Spec.Fault (Fl4Spec.Cap × Fl4Spec.CslotPtr) :=
  Fl4Spec.capFaultOnFailure (Z := Unit) (Fl4Spec.ofBl cptr) false (Fl4Spec.lookupCapAndSlot t cptr)

theorem exAt_none (j : Nat) (hj : j < 3) : exAt ipc.NO_EXTRA_CAPS j = 0#u64 := by
  unfold exAt ipc.NO_EXTRA_CAPS
  interval_cases j <;> rfl

theorem exAt_set (extra : Aeneas.Std.Array obj.Slot 3#usize) (i : Usize) (x : U64) (j : Nat) :
    exAt (extra.set i x) j = if i.val = j ∧ j < 3 then x else exAt extra j := by
  have hl : extra.val.length = 3 := by simpa using extra.property
  unfold exAt
  rw [Aeneas.Std.Array.set_val_eq]
  by_cases h : i.val = j
  · subst h
    by_cases h3 : i.val < 3
    · rw [if_pos ⟨rfl, h3⟩, List.getD_eq_getElem _ _ (by simp; omega)]; simp
    · rw [if_neg (fun h => h3 h.2), List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]
  · rw [if_neg (fun h' => h h'.1)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

set_option maxHeartbeats 8000000 in
/-- **`lookup_extra_caps`' loop refines the spec's lookups** of the extra
caps (`map_mE` of `lookup_cap_and_slot`). -/
theorem lookup_extra_loop {th : TypedHeap} {G : MdbGhost} {s : S} {σ : Fl4Spec.State Unit}
    (hB : RelTopB (L := L) th G N T C E R B c s σ) (hR : IpcRel N T E R B (L.mem s) σ)
    {t : U64} (ht : th t = some .tcb) {sbw : U64} {sb : Fl4Spec.Word} (hm : BufMap B sbw sb) (n : U64)
    (hn : n.val ≤ 3) :
    ipc.lookup_extra_caps_loop st s t sbw ipc.NO_EXTRA_CAPS n 0#u64 ⦃ r => match r with
      | .Ok e => ∃ caps, (Fl4Spec.NonDetE.mapME (xLook t.bv)
          (xCptrs σ.machineState.underlyingMemory sb n.val)).run σ = ({(.ok caps, σ)}, False) ∧
          ExtraOK th (L.mem s) e caps
      | .Err _ => ∃ e', (Fl4Spec.NonDetE.mapME (xLook t.bv)
          (xCptrs σ.machineState.underlyingMemory sb n.val)).run σ = ({(.error e', σ)}, False) ⦄ := by
  obtain ⟨hPl, ⟨hSt, hV, -⟩, -⟩ := hB
  set cp := xCptrs σ.machineState.underlyingMemory sb n.val with hcp
  have hcpl : cp.length = n.val := by simp [hcp, xCptrs]
  unfold ipc.lookup_extra_caps_loop
  refine loop.spec_decr_nat (fun x => 3 - x.2.val)
    (fun x => x.2.val ≤ n.val ∧ ∃ acc : List (Fl4Spec.Cap × Fl4Spec.CslotPtr), acc.length = x.2.val ∧
      (∀ j (hj : j < acc.length), SrcOK th (L.mem s) (exAt x.1 j) acc[j]) ∧
      (∀ j, x.2.val ≤ j → j < 3 → exAt x.1 j = 0#u64) ∧
      (∀ res, (Fl4Spec.NonDetE.mapME (xLook t.bv) (cp.drop x.2.val)).run σ = ({(.ok res, σ)}, False) →
        (Fl4Spec.NonDetE.mapME (xLook t.bv) cp).run σ = ({(.ok (acc ++ res), σ)}, False)) ∧
      (∀ e, (Fl4Spec.NonDetE.mapME (xLook t.bv) (cp.drop x.2.val)).run σ = ({(.error e, σ)}, False) →
        (Fl4Spec.NonDetE.mapME (xLook t.bv) cp).run σ = ({(.error e, σ)}, False))) _ _ _ (fun x hx => ?_) ?_
  · obtain ⟨arr, i⟩ := x
    obtain ⟨hi, acc, hacc, hsrc, hz, hok, herr⟩ := hx
    dsimp only at hi hacc hsrc hz hok herr ⊢
    unfold ipc.lookup_extra_caps_loop.body
    by_cases hin : i < n
    · have hin' : i.val < n.val := by scalar_tac
      have hi3 : i < 3#u64 := by scalar_tac
      rw [if_pos hin, if_pos hi3, buf_caps_eq]
      simp only [lift, bind_ok]
      have hk : (core.num.U64.wrapping_add 122#u64 i).val = 122 + i.val := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have hwp := hm _ (by rw [hk]; omega : (core.num.U64.wrapping_add 122#u64 i).val < 128)
      have hw : (L.mem s (fl4BufA sbw (core.num.U64.wrapping_add 122#u64 i))).bv =
          loadWordAt σ.machineState.underlyingMemory (bufAddr sb (122 + i.val)) := by
        rw [← hk]; exact hR.buf _ hwp
      have hdrop : cp.drop i.val = Fl4Spec.dataToCptr (loadWordAt σ.machineState.underlyingMemory
          (bufAddr sb (122 + i.val))) :: cp.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by omega)]
        simp [hcp, xCptrs, List.getElem_range']
      refine WP.spec_bind (msg.buf_get.spec s sbw _) ?_
      rintro w rfl
      refine WP.spec_bind (lookup_slot_refines th s σ hSt hV t ht _) ?_
      rintro r ⟨e, he, hrel, hsok⟩
      have he' : (Fl4Spec.lookupSlotForThread (Z := Unit) t.bv
          (Fl4Spec.dataToCptr (loadWordAt σ.machineState.underlyingMemory (bufAddr sb (122 + i.val))))).run σ =
          ({(e, σ)}, False) := by
        rw [← hw]; exact he
      cases r with
      | Ok r1 =>
        cases e with
        | error _ => exact hrel.elim
        | ok v =>
          obtain ⟨sl, rest⟩ := v
          obtain ⟨hsl, -⟩ := hrel
          obtain ⟨p, hp1, hp, -⟩ := hsok
          obtain ⟨cv, a, hcv, hca, hg⟩ := hSt.slot_cap (Z := Unit) hp1 hp
          have hel := lcs_ok (Fl4Spec.ofBl (Fl4Spec.dataToCptr (loadWordAt σ.machineState.underlyingMemory
            (bufAddr sb (122 + i.val))))) he' hg
          simp only []
          rw [show (UScalar.cast .Usize i : Usize) = UScalar.cast .Usize i from rfl]
          obtain ⟨a', ha', ha'v⟩ := spec_exists (Aeneas.Std.Array.update_spec arr (UScalar.cast .Usize i) r1.slot
            (by have hl : arr.val.length = 3 := by simpa using arr.property
                rw [cast_us_val i (by omega)]; simp [Aeneas.Std.Array.length, hl]; omega))
          rw [ha']
          simp only [bind_ok]
          obtain ⟨i4, h4e, h4v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
          rw [h4e, bind_ok, WP.spec_ok]
          have hi4 : i4.val = i.val + 1 := by simpa using h4v
          subst ha'v
          have hex : ∀ j, exAt (arr.set (UScalar.cast .Usize i) r1.slot) j =
              if i.val = j ∧ j < 3 then r1.slot else exAt arr j := fun j => by
            rw [exAt_set, cast_us_val i (by omega)]
          have hAs : AbsSlot th sl := ⟨p, hp1, Or.inl hp⟩
          refine ⟨⟨by rw [hi4]; omega, acc ++ [(a, sl)], by simp [hacc, hi4], fun j hj => ?_, fun j hj hj3 => ?_,
            fun res hres => ?_, fun e hres => ?_⟩, by rw [hi4]; omega⟩
          · by_cases hji : j < acc.length
            · rw [List.getElem_append_left hji, hex, if_neg (fun h => by omega)]
              exact hsrc j hji
            · have hje : j = acc.length := by simp at hj; omega
              subst hje
              rw [List.getElem_append_right (by omega)]
              simp only [Nat.sub_self, List.getElem_cons_zero]
              rw [hex, if_pos ⟨hacc.symm, by omega⟩, hsl]
              refine ⟨p, sl.2.length, sl.2, cv, hp, rfl, by rw [← hp1], by rw [← hp1], ?_, hca.2.symm, hca.1,
                ?_, hV.abs hAs hcv⟩
              · exact hcv
              · rw [capAt_words] at hcv; exact decode_encWf hcv
          · rw [hex, if_neg (fun h => by rw [hi4] at hj; omega)]
            exact hz j (by rw [hi4] at hj; omega) hj3
          · rw [hi4] at hres
            have := hok ((a, sl) :: res) (by rw [hdrop]; exact mapME_cons_ok hel hres)
            simpa using this
          · rw [hi4] at hres
            exact herr e (by rw [hdrop]; exact mapME_cons_tail_err hel hres)
      | Err lf =>
        cases e with
        | ok _ => exact hrel.elim
        | error lf' =>
          simp only [WP.spec_ok]
          exact ⟨_, herr _ (by rw [hdrop]; exact mapME_cons_err (lcs_err _ he'))⟩
    · rw [if_neg hin, WP.spec_ok]
      have hieq : i.val = n.val := by have : ¬ i.val < n.val := fun h => hin (by scalar_tac); omega
      refine ⟨acc, ?_, by omega, fun j hj => by rw [← hacc] at *; exact hsrc j hj, fun j hj hj3 => hz j (by omega) hj3⟩
      have := hok [] (by rw [hieq, ← hcpl, List.drop_length]; rfl)
      simpa using this
  · refine ⟨by simp, [], rfl, fun j hj => by simp at hj, fun j _ hj3 => exAt_none j hj3, fun res h => by simpa using h,
      fun e h => by simpa using h⟩

end ExtraLoop


section ExtraTop
open Fl4Spec

theorem mapM_load (sb : Word) : ∀ (xs : List Nat) (σ : State Unit), (∀ x ∈ xs, (bufAddr sb x).toNat % 8 = 0) →
    NonDet.mapM (loadWordOffs (Z := Unit) sb) xs σ =
      ({(xs.map fun k => loadWordAt σ.machineState.underlyingMemory (bufAddr sb k), σ)}, False)
  | [], σ, _ => by
    show (pure [] : NonDet (State Unit) (List Word)) σ = _
    rw [nd_pure_apply']; rfl
  | x :: xs, σ, h => by
    unfold NonDet.mapM
    rw [nd_bind_one' (loadWordOffs_eq σ sb x (h x (by simp))),
      nd_bind_one' (mapM_load sb xs σ fun y hy => h y (by simp [hy]))]
    rfl

theorem getExtraCptrs_some {σ : State Unit} {sb : Word} {mi : MessageInfo} (h3 : unat mi.miExtraCaps ≤ 3)
    (hal : ∀ k, k < 128 → (bufAddr sb k).toNat % 8 = 0) :
    getExtraCptrs (Z := Unit) (some sb) mi σ =
      ({(xCptrs σ.machineState.underlyingMemory sb (unat mi.miExtraCaps), σ)}, False) := by
  unfold getExtraCptrs
  dsimp only
  rw [show bufferCptrIndex + unat mi.miExtraCaps - bufferCptrIndex = unat mi.miExtraCaps by omega]
  unfold NonDet.liftM
  rw [nd_bind_one' (mapM_load sb _ σ fun k hk => hal k (by
    simp [List.mem_range'] at hk; unfold bufferCptrIndex msgMaxLength at hk; omega))]
  simp [xCptrs, bufferCptrIndex, msgMaxLength, NonDet.pure]

end ExtraTop

section ExtraTop2
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem extraOK_none (th : TypedHeap) (m : U64 → U64) : ExtraOK th m ipc.NO_EXTRA_CAPS [] :=
  ⟨by simp, fun j hj => by simp at hj, fun j _ hj3 => exAt_none j hj3⟩

/-- **`lookup_extra_caps` refines `lookup_extra_caps`** under the
transfer's `catch` (a failed lookup transfers no cap, on both sides). -/
theorem lookup_extra_top (hP0 : IPlaced N T E R B) {th : TypedHeap} {G : MdbGhost} {s : S}
    {σ : Fl4Spec.State Unit} (hB : RelTopB (L := L) th G N T C E R B c s σ) (hR : IpcRel N T E R B (L.mem s) σ)
    {t : U64} (ht : th t = some .tcb) (sbw : U64) (sbo : Option Fl4Spec.Word) (hsb : sbw = 0#u64 ↔ sbo = none)
    (hm : ∀ sb, sbo = some sb → BufMap B sbw sb) (info : msginfo.MessageInfo) (mi : Fl4Spec.MessageInfo)
    (hn : info.extra_caps.val = Fl4Spec.unat mi.miExtraCaps) (hn3 : info.extra_caps.val ≤ 3) :
    ipc.lookup_extra_caps st s t sbw info ⦃ r => ∃ caps,
      Fl4Spec.NonDetE.catch (Fl4Spec.lookupExtraCaps (Z := Unit) t.bv sbo mi) (fun _ => pure []) σ =
        ({(caps, σ)}, False) ∧
      ExtraOK th (L.mem s) (match r with | .Ok e => e | .Err _ => ipc.NO_EXTRA_CAPS) caps ⦄ := by
  unfold ipc.lookup_extra_caps
  by_cases h0 : sbw = 0#u64
  · rw [if_pos h0, WP.spec_ok]
    exact ⟨[], catch_lookupExtraCaps_nil (Or.inl (hsb.1 h0)), extraOK_none th _⟩
  · rw [if_neg h0]
    obtain ⟨sb, hsbo⟩ : ∃ sb, sbo = some sb := by
      cases e : sbo with
      | none => exact absurd (hsb.2 e) h0
      | some sb => exact ⟨sb, rfl⟩
    subst hsbo
    have hmb := hm sb rfl
    have hal : ∀ k, k < 128 → (bufAddr sb k).toNat % 8 = 0 := fun k hk => by
      have hv : (⟨BitVec.ofNat 64 k⟩ : U64).val = k := by
        show (BitVec.ofNat 64 k).toNat = k; simp; omega
      have h := (hP0.e.balign _ (hmb ⟨BitVec.ofNat 64 k⟩ (by rw [hv]; omega))).2
      rw [hv] at h; exact h
    have hge := getExtraCptrs_some (σ := σ) (sb := sb) (mi := mi) (by omega) hal
    rw [← hn] at hge
    refine WP.spec_mono (lookup_extra_loop hB hR ht hmb info.extra_caps hn3) ?_
    intro r hr
    have hrun : ∀ res, (Fl4Spec.NonDetE.mapME (xLook t.bv)
        (xCptrs σ.machineState.underlyingMemory sb info.extra_caps.val)).run σ = res →
        (Fl4Spec.lookupExtraCaps (Z := Unit) t.bv (some sb) mi).run σ = res := by
      intro res h
      unfold Fl4Spec.lookupExtraCaps
      rw [runE_liftE_bind hge]; exact h
    cases r with
    | Ok e =>
      obtain ⟨caps, hc, hok⟩ := hr
      exact ⟨caps, Vs.catch_ok (hrun _ hc), hok⟩
    | Err _ =>
      obtain ⟨e', he⟩ := hr
      refine ⟨[], ?_, extraOK_none th _⟩
      rw [Vs.catch_err (hrun _ he)]; rfl

end ExtraTop2


/-! ## The receive slot (G1) -/

section Recv
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem buf_recv_eq : msg.BUF_RECV_CNODE = ok 125#u64 ∧ msg.BUF_RECV_INDEX = ok 126#u64 ∧
    msg.BUF_RECV_DEPTH = ok 127#u64 := by
  have h1 : msg.BUF_RECV_CNODE = ok 125#u64 := by
    unfold msg.BUF_RECV_CNODE msg.MSG_MAX_EXTRA_CAPS
    rw [buf_caps_eq]; simp only [bind_ok]
    obtain ⟨z, hz, hzv⟩ := spec_exists (U64.add_spec (x := 122#u64) (y := 3#u64) (by scalar_tac))
    rw [hz]; congr 1; apply UScalar.eq_of_val_eq; rw [hzv]; rfl
  have h2 : msg.BUF_RECV_INDEX = ok 126#u64 := by
    unfold msg.BUF_RECV_INDEX
    rw [h1]; simp only [bind_ok]
    obtain ⟨z, hz, hzv⟩ := spec_exists (U64.add_spec (x := 125#u64) (y := 1#u64) (by scalar_tac))
    rw [hz]; congr 1; apply UScalar.eq_of_val_eq; rw [hzv]; rfl
  refine ⟨h1, h2, ?_⟩
  unfold msg.BUF_RECV_DEPTH
  rw [h2]; simp only [bind_ok]
  obtain ⟨z, hz, hzv⟩ := spec_exists (U64.add_spec (x := 126#u64) (y := 1#u64) (by scalar_tac))
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; rw [hzv]; rfl

theorem dmo_loadWord_eq (σ : Fl4Spec.State Unit) (a : Fl4Spec.Word) (h : a.toNat % 8 = 0) :
    Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.loadWord a) σ =
      ({(loadWordAt σ.machineState.underlyingMemory a, σ)}, False) := by
  unfold Fl4Spec.doMachineOp
  rw [nd_gets_bind, loadWord_eq _ _ h, nd_bind_one (selectF_one _ σ)]
  dsimp only
  rw [nd_bind_one (show Fl4Spec.NonDet.modify (fun state : Fl4Spec.State Unit =>
    { state with machineState := σ.machineState }) σ = ({((), σ)}, False) from rfl)]
  rfl

/-- The spec's cap-transfer words: words 125–127 of the receive buffer. -/
theorem loadCapTransfer_eq {σ : Fl4Spec.State Unit} {rb : Fl4Spec.Word}
    (hal : ∀ k, k < 128 → (bufAddr rb k).toNat % 8 = 0) :
    Fl4Spec.loadCapTransfer (Z := Unit) rb σ =
      ({(⟨Fl4Spec.dataToCptr (loadWordAt σ.machineState.underlyingMemory (bufAddr rb 125)),
          Fl4Spec.dataToCptr (loadWordAt σ.machineState.underlyingMemory (bufAddr rb 126)),
          loadWordAt σ.machineState.underlyingMemory (bufAddr rb 127)⟩, σ)}, False) := by
  unfold Fl4Spec.loadCapTransfer Fl4Spec.captransferFromWords
  rw [nd_pure_bind']
  have e0 : rb + BitVec.ofNat 64 (Fl4Spec.msgMaxLength + Fl4Spec.msgMaxExtraCaps + 2) *
      BitVec.ofNat 64 Fl4Spec.wordSize = bufAddr rb 125 := by
    unfold bufAddr; congr 1
  have e1 : bufAddr rb 125 + BitVec.ofNat 64 Fl4Spec.wordSize = bufAddr rb 126 := by
    unfold bufAddr; rw [BitVec.add_assoc]; congr 1
  have e2 : bufAddr rb 125 + 2 * BitVec.ofNat 64 Fl4Spec.wordSize = bufAddr rb 127 := by
    unfold bufAddr; rw [BitVec.add_assoc]; congr 1
  rw [e0, e1, e2, nd_bind_one (dmo_loadWord_eq σ _ (hal 125 (by omega))),
    nd_bind_one (dmo_loadWord_eq σ _ (hal 126 (by omega))), nd_bind_one (dmo_loadWord_eq σ _ (hal 127 (by omega)))]
  rfl

/-- `lookup_cap` with the validity of the cap found. -/
theorem lookup_cap_valid (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (t : U64) (ht : th t = some .tcb)
    (cptr : U64) :
    cspace.lookup_cap st s t cptr ⦃ r =>
      Single ((Fl4Spec.lookupCap (Z := Unit) t.bv (Fl4Spec.toBl cptr.bv)).run σ) σ (CapResRel r) ∧
      ∀ c, r = .Ok c → CapValid th c ⦄ := by
  unfold cspace.lookup_cap
  refine WP.spec_bind (lookup_slot_refines th s σ hR hV t ht cptr) ?_
  rintro r ⟨e, he, hrel, hok⟩
  unfold Fl4Spec.lookupCap
  cases r with
  | Ok r1 =>
    cases e with
    | ok v =>
      obtain ⟨sl, rest⟩ := v
      obtain ⟨hsl, -⟩ := hrel
      obtain ⟨p, hp, hth, -⟩ := hok
      obtain ⟨c, a, hc, hca, hget⟩ := hR.slot_cap hp hth
      simp only
      rw [slot_cap_eq, hsl, hc]
      simp only [bind_ok, WP.spec_ok]
      exact ⟨⟨.ok a, by rw [run_bind_ok he]; exact run_liftE hget, hca⟩, fun c' h => by
        cases h; exact hV.abs ⟨p, hp, Or.inl hth⟩ hc⟩
    | error lf' => exact hrel.elim
  | Err lf =>
    cases e with
    | ok v => exact hrel.elim
    | error lf' =>
      simp only [WP.spec_ok]
      exact ⟨⟨.error lf', run_bind_error he _, hrel⟩, fun c h => by cases h⟩

set_option maxHeartbeats 4000000 in
/-- **`get_receive_slot` refines `get_receive_slots`** (G1). -/
theorem get_receive_slot_top (hP0 : IPlaced N T E R B) {th : TypedHeap} {G : MdbGhost} {s : S}
    {σ : Fl4Spec.State Unit} (hB : RelTopB (L := L) th G N T C E R B c s σ) (hR : EpStateRel T E R B (L.mem s) σ)
    {t : U64} (ht : th t = some .tcb) {rbw : U64} {rb : Fl4Spec.Word} (hm : BufMap B rbw rb) (hr0 : rbw ≠ 0#u64)
    (caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (extra : Aeneas.Std.Array obj.Slot 3#usize) :
    ipc.get_receive_slot st s t rbw ⦃ dest => ∃ slots,
      Fl4Spec.getReceiveSlots (Z := Unit) t.bv (some rb) σ = ({(slots, σ)}, False) ∧
      DestConf th (L.mem s) caps extra dest slots ⦄ := by
  classical
  obtain ⟨hPl, ⟨hSt, hV, -⟩, -⟩ := hB
  have hal : ∀ k, k < 128 → (bufAddr rb k).toNat % 8 = 0 := fun k hk => by
    have hv : (⟨BitVec.ofNat 64 k⟩ : U64).val = k := by
      show (BitVec.ofNat 64 k).toNat = k; simp; omega
    have h := (hP0.e.balign _ (hm ⟨BitVec.ofNat 64 k⟩ (by rw [hv]; omega))).2
    rw [hv] at h; exact h
  have hw : ∀ k : U64, k.val < 128 → (L.mem s (fl4BufA rbw k)).bv =
      loadWordAt σ.machineState.underlyingMemory (bufAddr rb k.val) := fun k hk => hR.buf _ (hm k hk)
  have hlct := loadCapTransfer_eq (σ := σ) hal
  -- the spec, from the inner computation
  have hspec : ∀ R, Fl4Spec.emptyOnFailure (Z := Unit) (do
        let cnode ← Fl4Spec.unifyFailure (Fl4Spec.lookupCap t.bv
          (Fl4Spec.dataToCptr (loadWordAt σ.machineState.underlyingMemory (bufAddr rb 125))))
        let slot ← Fl4Spec.unifyFailure (Fl4Spec.lookupTargetSlot cnode
          (Fl4Spec.dataToCptr (loadWordAt σ.machineState.underlyingMemory (bufAddr rb 126)))
          (Fl4Spec.unat (loadWordAt σ.machineState.underlyingMemory (bufAddr rb 127))))
        let cap ← Fl4Spec.NonDetE.liftE (Fl4Spec.getCap slot)
        Fl4Spec.NonDetE.whenE (cap ≠ .nullCap) (Fl4Spec.NonDetE.throwError ())
        Fl4Spec.NonDetE.returnOk [slot]) σ = R →
      Fl4Spec.getReceiveSlots (Z := Unit) t.bv (some rb) σ = R := by
    intro R h
    unfold Fl4Spec.getReceiveSlots
    dsimp only
    rw [nd_bind_one hlct]
    exact h
  unfold ipc.get_receive_slot
  rw [if_neg hr0, buf_recv_eq.1, buf_recv_eq.2.1, buf_recv_eq.2.2]
  simp only [bind_ok]
  refine WP.spec_bind (msg.buf_get.spec s rbw _) ?_
  intro root hroot
  refine WP.spec_bind (msg.buf_get.spec s rbw _) ?_
  intro index hindex
  refine WP.spec_bind (msg.buf_get.spec s rbw _) ?_
  intro depth hdepth
  have hrv : root.bv = loadWordAt σ.machineState.underlyingMemory (bufAddr rb 125) := by
    rw [hroot]; exact hw 125#u64 (by decide)
  have hiv : index.bv = loadWordAt σ.machineState.underlyingMemory (bufAddr rb 126) := by
    rw [hindex]; exact hw 126#u64 (by decide)
  have hdv : depth.bv = loadWordAt σ.machineState.underlyingMemory (bufAddr rb 127) := by
    rw [hdepth]; exact hw 127#u64 (by decide)
  have hthrow : ∀ (R : Type) (m : Fl4Spec.NonDetE (Fl4Spec.State Unit) Fl4Spec.LookupFailure R) lf,
      m.run σ = ({(.error lf, σ)}, False) →
      (Fl4Spec.unifyFailure (Z := Unit) m).run σ = ({(.error (), σ)}, False) := by
    intro R m lf h
    unfold Fl4Spec.unifyFailure
    rw [run_handleE_err h]; rfl
  have hthrow' : ∀ (R : Type) (m : Fl4Spec.NonDetE (Fl4Spec.State Unit) Fl4Spec.SyscallError R) lf,
      m.run σ = ({(.error lf, σ)}, False) →
      (Fl4Spec.unifyFailure (Z := Unit) m).run σ = ({(.error (), σ)}, False) := by
    intro R m lf h
    unfold Fl4Spec.unifyFailure
    rw [run_handleE_err h]; rfl
  have hempty : ∀ (m : Fl4Spec.NonDetE (Fl4Spec.State Unit) Unit (List Fl4Spec.CslotPtr)),
      m.run σ = ({(.error (), σ)}, False) → Fl4Spec.emptyOnFailure (Z := Unit) m σ = ({([], σ)}, False) := by
    intro m h
    unfold Fl4Spec.emptyOnFailure
    rw [Vs.catch_err h]; rfl
  refine WP.spec_bind (lookup_cap_valid th s σ hSt hV t ht root) ?_
  rintro r ⟨⟨e, he, hrel⟩, hval⟩
  rw [hrv] at he
  cases r with
  | Err lf =>
    cases e with
    | ok _ => simp [CapResRel] at hrel
    | error lf' =>
      simp only [WP.spec_ok]
      refine ⟨[], hspec _ (hempty _ ?_), Or.inl ⟨rfl, rfl⟩⟩
      exact run_bind_error (hthrow _ _ _ he) _
  | Ok c0 =>
    cases e with
    | error _ => simp [CapResRel] at hrel
    | ok a =>
      have hcv := hval c0 rfl
      simp only []
      unfold cspace.lookup_target_slot
      refine WP.spec_bind (lookup_slot_for_cnode_op_refines th s σ hSt hV false c0 a hrel hcv index depth) ?_
      rintro r1 ⟨e1, he1, hrel1⟩
      rw [hiv] at he1
      have hd : depth.val = Fl4Spec.unat (loadWordAt σ.machineState.underlyingMemory (bufAddr rb 127)) := by
        rw [← hdv]; rfl
      rw [hd] at he1
      have hcn : (Fl4Spec.unifyFailure (Z := Unit) (Fl4Spec.lookupCap t.bv
          (Fl4Spec.dataToCptr (loadWordAt σ.machineState.underlyingMemory (bufAddr rb 125))))).run σ =
          ({(.ok a, σ)}, False) := run_handleE_ok he
      cases r1 with
      | Err e' =>
        cases e1 with
        | ok _ => exact hrel1.elim
        | error e'' =>
          simp only [WP.spec_ok]
          refine ⟨[], hspec _ (hempty _ ?_), Or.inl ⟨rfl, rfl⟩⟩
          rw [run_bind_ok hcn]
          exact run_bind_error (hthrow' _ _ _ he1) _
      | Ok slot =>
        cases e1 with
        | error _ => exact hrel1.elim
        | ok sl =>
          obtain ⟨hsl, p, hp1, hp, -⟩ := hrel1
          obtain ⟨c1, a1, hc1, hca1, hg1⟩ := hSt.slot_cap (Z := Unit) hp1 hp
          simp only []
          rw [slot_cap_eq, hsl, hc1]
          simp only [bind_ok]
          have hts : (Fl4Spec.unifyFailure (Z := Unit) (Fl4Spec.lookupTargetSlot a
              (Fl4Spec.dataToCptr (loadWordAt σ.machineState.underlyingMemory (bufAddr rb 126)))
              (Fl4Spec.unat (loadWordAt σ.machineState.underlyingMemory (bufAddr rb 127))))).run σ =
              ({(.ok sl, σ)}, False) := run_handleE_ok he1
          by_cases hn : c1 = .Null
          · subst hn
            rw [cap_is_null_null, bind_ok, if_pos rfl, WP.spec_ok]
            have ha1 : a1 = .nullCap := (CapRel.null_iff hca1).2 rfl
            refine ⟨[sl], hspec _ ?_, Or.inr ⟨(AbsSlot.isSlot ⟨p, hp1, Or.inl hp⟩).ne_zero hPl, sl, rfl,
              ⟨p, sl.2.length, sl.2, hp, rfl, by rw [← hp1], by rw [← hp1], hc1⟩⟩⟩
            unfold Fl4Spec.emptyOnFailure
            refine Vs.catch_ok ?_
            rw [run_bind_ok hcn, run_bind_ok hts, run_bind_ok (run_liftE hg1)]
            unfold Fl4Spec.NonDetE.whenE
            rw [ha1, if_neg (fun h => h rfl)]
            exact (run_bind_ok (show (pure () : Fl4Spec.NonDetE (Fl4Spec.State Unit) Unit Unit).run σ =
              ({(.ok (), σ)}, False) from rfl) _).trans rfl
          · rw [cap_is_null_ne hn, bind_ok, if_neg Bool.false_ne_true, WP.spec_ok]
            have ha1 : a1 ≠ .nullCap := fun h => hn ((CapRel.null_iff hca1).1 h)
            refine ⟨[], hspec _ (hempty _ ?_), Or.inl ⟨rfl, rfl⟩⟩
            rw [run_bind_ok hcn, run_bind_ok hts, run_bind_ok (run_liftE hg1)]
            unfold Fl4Spec.NonDetE.whenE
            rw [if_pos ha1]
            exact run_bind_error (run_throwError _ σ) _

end Recv

end

end Fl4Proofs.P3.Ipc

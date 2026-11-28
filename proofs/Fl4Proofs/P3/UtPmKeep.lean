/-
P3 (DESIGN.md §9), untyped: **`JAtZ`'s scheduler and untyped-cap fields
across a retype whose FL4 writes also hit a window of fresh memory** (the
PML4 retype's kernel-half copy; handoff/utj.md "uttypes (line ut22-)").
Copies of `inSlot_keeps`, `JAtZ.uaRest`, `JAtZ.addRP` and `JAtZ.ret_utc`
with the write set `InSlot th ∪ Win`, the window's words apart from what
each reads.
-/
import Fl4Proofs.P3.UtPmAdd
import Fl4Proofs.P3.UtUtRet
import Fl4Proofs.P3.UtPmCont
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **`retExp_pml4_back` for mapped PML4 caps**: a slot holding a mapped PML4
cap after a retype whose new caps are no mapped PML4 caps held it before. -/
theorem retExp_pml4_backT {th : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hE : RetExp th th m m' G G' A k w dslot cj xs) (hM : MdbLinks th m G) (hM' : MdbLinks th m' G')
    (hcj : ∀ j, j < w → ∀ p a, cj j ≠ .Pml4 p true a) {x p : U64} {asid : U64} (hxs : IsSlot th x)
    (hx : capAt m' x = ok (.Pml4 p true asid)) : capAt m x = ok (.Pml4 p true asid) := by
  have hmem' : x ∈ G'.chains.flatten := (hM'.members x).2 ⟨hxs, _, hx, by simp⟩
  have hv' := capV_of_capAt hx
  rcases hE.gmem x hmem' with hx0 | ⟨j, hj, rfl⟩
  · obtain ⟨-, c, hc, -⟩ := (hM.members x).1 hx0
    have hv := capV_of_capAt hc
    cases hu : isUt (capV m x)
    · have e := (hE.keep x hx0 hu).2
      rw [hv', hv] at e
      rw [hc, ← e]
    · have e := hE.utk x hx0 hu
      rw [hv'] at e; cases e
  · have e := hE.newc j hj
    rw [hv'] at e
    exact absurd e.symm (hcj j hj _ _)

/-- **Another untyped cap's free part misses the source's free part** (l4v
`untyped_inc`, `untyped_range_overlap`): a byte of the source cap's free part
lies outside the free part of any other untyped cap of the MDB. -/
theorem ut_free_other {mem : U64 → U64} {G : MdbGhost} (hU : UtInv mem G) {x src : U64}
    (hx : x ∈ G.chains.flatten) (hs : src ∈ G.chains.flatten) (hne : x ≠ src)
    {p sb fi p0 sb0 fi0 : U64} {d d0 : Bool} (hcx : capV mem x = .Untyped p sb fi d)
    (hcs : capV mem src = .Untyped p0 sb0 fi0 d0) {b : Nat} (hb1 : p0.val + fi0.val ≤ b)
    (hb2 : b < p0.val + 2 ^ sb0.val) :
    b < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ b := by
  have hsb := capV_ut_sb hcx
  have hsb0 := capV_ut_sb hcs
  have hxr := hU.reg x hx (by rw [hcx]; exact physF_ut _ _ _ _)
  rw [hcx] at hxr
  obtain ⟨x1, x2, -⟩ := ut_range hsb hxr
  have hsr := hU.reg src hs (by rw [hcs]; exact physF_ut _ _ _ _)
  rw [hcs] at hsr
  obtain ⟨s1, s2, -⟩ := ut_range hsb0 hsr
  have h1 := Nat.one_le_two_pow (n := sb.val)
  have h2 := Nat.one_le_two_pow (n := sb0.val)
  have hfi := hU.fib x hx p sb fi d hcx
  have hfi0 := hU.fib src hs p0 sb0 fi0 d0 hcs
  rcases hU.noov x hx p sb fi d hcx src hs (by rw [hcs]; exact physF_ut _ _ _ _) with hd | ⟨-, hw⟩
  · unfold DisjR at hd; rw [hcs, s1, s2] at hd; omega
  · unfold Within at hw; rw [hcx, x1, x2, hcs, s1, s2] at hw
    rcases hU.noov src hs p0 sb0 fi0 d0 hcs x hx (by rw [hcx]; exact physF_ut _ _ _ _) with hd | ⟨-, hw2⟩
    · unfold DisjR at hd; rw [hcx, x1, x2] at hd; omega
    · unfold Within at hw2; rw [hcx, x1, x2, hcs, s1, s2] at hw2
      have hp' : p = p0 := UScalar.eq_of_val_eq (by omega)
      have h22 : 2 ^ sb.val = 2 ^ sb0.val := by omega
      have hsb'' : sb = sb0 := UScalar.eq_of_val_eq (Nat.pow_right_injective (le_refl 2) h22)
      subst hp' hsb''
      rcases hU.excl x hx src hs hne p sb fi fi0 d d0 hcx hcs with hf | hf <;> omega

section SpecCo
open Fl4Spec

/-- **`invokeUntyped_noreset_co` for PML4s**: the CDT and the original bits
change at the window's slots only (`init_arch_objects` changes PML4 objects
only). -/
theorem invokeUntyped_noreset_coP (bitsApi : ApiObjectType → Nat → Nat) (sl : CslotPtr) (pb rb : ObjRef)
    (us : Nat) (slots : List CslotPtr) (dev : Bool) (σ : State Unit)
    (Ps : Set ObjRef) (hsl : sl.1 ∈ Ps) (hcn : ∀ p ∈ Ps, ∃ r cs, σ.kheap p = some (.cnode r cs))
    (hfree : ∀ q ∈ regionPtrs rb slots.length (2 ^ bitsApi (.archObject .pml4Obj) us), σ.kheap q = none)
    (hal : ∀ q ∈ regionPtrs rb slots.length (2 ^ bitsApi (.archObject .pml4Obj) us),
      q.toNat % 4096 = 0 ∧ q.toNat + 4096 ≤ 2 ^ 64)
    (hg : HasPm σ σ.archState.x64GlobalPml4)
    (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0) (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64) :
    NAll (invokeUntypedWith (Z := Unit) bitsApi (.retype sl false pb rb (.archObject .pml4Obj) us slots dev)).run σ
      (fun y => CdtKeepOff (· ∈ slots) σ y.2 ∧ OKeep (· ∈ slots) σ y.2) := by
  set ptrs := regionPtrs rb slots.length (2 ^ bitsApi (.archObject .pml4Obj) us) with hptrs
  have hpre : NAll (NonDetE.whenE (false = true) (resetUntypedCap (Z := Unit) sl)).run σ
      (fun y => y.1 = .ok () ∧ y.2 = σ) := by
    unfold NonDetE.whenE
    rw [if_neg (by decide)]
    exact nall_det rfl ⟨rfl, rfl⟩
  have hgP : σ.archState.x64GlobalPml4 ∉ Ps := fun h => by
    obtain ⟨r, cs, hk⟩ := hcn _ h; obtain ⟨pt, hpt⟩ := hg; rw [hk] at hpt; cases hpt
  have hgW : σ.archState.x64GlobalPml4 ∉ ptrs := fun h => by
    obtain ⟨pt, hpt⟩ := hg; rw [hfree _ h] at hpt; cases hpt
  unfold invokeUntypedWith
  apply nallE_bind
  refine hpre.mono (fun x ⟨hx1, hx2⟩ => ?_)
  rcases x with ⟨e | u, σr⟩
  · cases hx1
  dsimp only at hx2 ⊢
  subst hx2
  apply nall_liftE
  apply nall_bind
  refine (show NAll (getCap (Z := Unit) sl) σr
      (fun x => CnKO Ps σr x.2 ∧ CdtKeepOff (· ∈ slots) σr x.2 ∧ OKeep (· ∈ slots) σr x.2)
    from fun x hx => ⟨nall_cnko (nkn_getCap sl) (nko_getCap (Ps := Ps) sl) σr x hx, ncd_getCap sl σr x hx,
      no_getCap sl σr x hx⟩).mono (fun x hx => ?_)
  apply nall_bind; refine nall_det rfl ?_
  apply nall_bind; refine nall_det rfl ?_
  apply nall_bind
  refine (show NAll (setCap (Z := Unit) _ sl) x.2
      (fun x2 => CnKO Ps x.2 x2.2 ∧ CdtKeepOff (· ∈ slots) x.2 x2.2 ∧ OKeep (· ∈ slots) x.2 x2.2)
    from fun x2 hx2 => ⟨nall_cnko (nkn_setCap _ sl) (nko_setCap (Ps := Ps) _ sl hsl) _ x2 hx2,
      ncd_setCap _ sl _ x2 hx2, no_setCap _ sl _ x2 hx2⟩).mono (fun x2 hx2 => ?_)
  apply nall_bind
  refine nall_det (retypeRegionWith_eq bitsApi rb slots.length us (.archObject .pml4Obj) dev x2.2) ?_
  rw [if_pos (by simp)]
  have h01 : CnKO Ps σr x2.2 := ⟨hx.1.1.trans hx2.1.1, fun p hp => (hx2.1.2 p hp).trans (hx.1.2 p hp)⟩
  have har0 : x2.2.archState = σr.archState := by
    have e := congrArg AbstractState.archState h01.1.1
    exact e
  set o0 := defaultObject (.archObject .pml4Obj) dev us x2.2.curDomain with ho0
  have hR0 : ∀ q, (regionHeap x2.2 ptrs o0).kheap q = if q ∈ ptrs then some o0 else x2.2.kheap q := fun q => by
    dsimp only [regionHeap]; rw [foldr_update_apply]
  have hg0 : HasPm (regionHeap x2.2 ptrs o0) (regionHeap x2.2 ptrs o0).archState.x64GlobalPml4 := by
    show HasPm _ x2.2.archState.x64GlobalPml4
    rw [har0]
    obtain ⟨pt, hpt⟩ := hg
    exact ⟨pt, by rw [hR0, if_neg hgW, h01.2 _ hgP]; exact hpt⟩
  have hr0 : ∀ q ∈ ptrs, HasPm (regionHeap x2.2 ptrs o0) q ∧ q.toNat % 4096 = 0 ∧ q.toNat + 4096 ≤ 2 ^ 64 :=
    fun q hq => ⟨⟨fun _ => .invalidPML4E, by rw [hR0, if_pos hq]; rfl⟩, hal q hq⟩
  obtain ⟨k, hk, -, -⟩ := initArch_pml4H (regionHeap x2.2 ptrs o0) dev rb slots.length us ptrs hg0
    (by show x2.2.archState.x64GlobalPml4.toNat % 4096 = 0; rw [har0]; exact hga)
    (by show x2.2.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64; rw [har0]; exact hgf)
    (by show x2.2.archState.x64GlobalPml4 ∉ ptrs; rw [har0]; exact hgW) hr0
  apply nall_bind
  refine nall_det hk ?_
  intro y hy
  have hmem : ∀ a ∈ slots.zip ptrs, a.1 ∈ slots := fun a ha => (List.of_mem_zip ha).1
  have h3c := ncd_mapMx_mem (d := (· ∈ slots)) _ (fun a ha => ncd_createCap _ us sl dev a (hmem a ha)) _ y hy
  have h3o := no_mapMx_mem (d := (· ∈ slots)) _ (fun a ha => no_createCap _ us sl dev a (hmem a ha)) _ y hy
  exact ⟨(hx.2.1.trans hx2.2.1).trans h3c, (hx.2.2.trans hx2.2.2).trans h3o⟩

end SpecCo

/-- `inSlotW_keeps` over `JAtZB` (mmuAD gen 42b26, in place; `inSlotW_keeps` is its corollary). -/
theorem inSlotW_keepsB {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {Win : U64 → Prop} (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWT : ∀ b, Win b → ∀ t ∈ Z.T, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hWC : ∀ b, Win b → ∀ q ∈ Z.C, ∀ x n, σ.kheap q.bv = some (.schedContext x n) →
      b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val)
    (hWR : ∀ b, Win b → ∀ r ∈ Z.R, b.val < r.val ∨ r.val + 32 ≤ b.val) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t) ∧ L.mem s' (flagsA t) = L.mem s (flagsA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have hA := J.apart
  have kw : ∀ b : U64, P1.Aligned b → (∀ x, IsSlot Z.th x → b.val < x.val ∨ x.val + 32 ≤ b.val) → ¬ Win b →
      L.mem s' b = L.mem s b := fun b hb hs hn =>
    hw.mem_eq hb fun h => h.elim (fun ⟨x, hx, h1, h2⟩ => by rcases hs x hx with e | e <;> omega) hn
  have tw : ∀ t ∈ Z.T, ∀ b : U64, P1.Aligned b → t.val + 256 ≤ b.val → b.val < t.val + 4096 → L.mem s' b = L.mem s b :=
    fun t ht b hb h1 h2 => kw b hb (fun x hx => by rcases (hA x hx).1 t ht with h | h <;> omega)
      (fun h => by rcases hWT b h t ht with e | e <;> omega)
  refine ⟨fun t ht => ⟨tw t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega),
      tw t ht _ (flagsA_aligned hT ht) (by rw [flagsA_val hT ht]; omega) (by rw [flagsA_val hT ht]; omega)⟩,
    fun t ht => tw t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega),
    fun t ht => tw t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega), fun q hq => ?_, fun r hr => ?_⟩
  · obtain ⟨hal, hv, hfit⟩ := sc_reply_word hS hq
    obtain ⟨x, n, hk, -⟩ := (hS.lists.choose_spec.choose_spec.2).scs q hq
    have hf := hfit x n hk
    exact kw _ hal (fun y hy => by rcases (hA y hy).2.2.2.1 q hq x n hk with h | h <;> omega)
      (fun h => by rcases hWC _ h q hq x n hk with e | e <;> omega)
  · have hal := J.rp.align r hr
    have h8 := rPrevA_val hal
    have h16 := rNextA_val hal
    refine ⟨kw _ (J.rp.aligned hr (Or.inl h8)) (fun y hy => ?_) (fun h => ?_),
      kw _ (J.rp.aligned hr (Or.inr h16)) (fun y hy => ?_) (fun h => ?_)⟩
    · rcases (hA y hy).2.2.2.2 r hr with h | h <;> omega
    · rcases hWR _ h r hr with e | e <;> omega
    · rcases (hA y hy).2.2.2.2 r hr with h | h <;> omega
    · rcases hWR _ h r hr with e | e <;> omega

/-- **`inSlot_keeps` with window writes**: the TCBs' `MCP`, `YIELD_TO` and
IPC-buffer words, the SCs' `REPLY` words and the replies' links are kept by
writes of slot words and of window words apart from `T`, `C`'s SCs and `R`. -/
theorem inSlotW_keeps {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {Win : U64 → Prop} (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWT : ∀ b, Win b → ∀ t ∈ Z.T, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hWC : ∀ b, Win b → ∀ q ∈ Z.C, ∀ x n, σ.kheap q.bv = some (.schedContext x n) →
      b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val)
    (hWR : ∀ b, Win b → ∀ r ∈ Z.R, b.val < r.val ∨ r.val + 32 ≤ b.val) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t) ∧ L.mem s' (flagsA t) = L.mem s (flagsA t)) ∧ (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) :=
  inSlotW_keepsB J.toB hw hWT hWC hWR


set_option maxHeartbeats 2000000 in
/-- `uaRestW` over `JAtZB` (mmuAD gen 42b26, in place; `JAtZ.uaRestW` is its corollary). -/
theorem JAtZB.uaRestW {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {Win : U64 → Prop} (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWT : ∀ b, Win b → ∀ t ∈ Z.T, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hWC : ∀ b, Win b → ∀ q ∈ Z.C, ∀ x n, σ.kheap q.bv = some (.schedContext x n) →
      b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val)
    (hWR : ∀ b, Win b → ∀ r ∈ Z.R, b.val < r.val ∨ r.val + 32 ≤ b.val)
    {σB σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}
    (hA : SpecAdd σ σB W o) (hi : IdleNew W o) (hcn : CnK σB σ') {Nn : Set U64} (hWn : ∀ n ∈ Nn, W n.bv) :
    CallRel (L.mem s') Z.R Z.C σ' Lst ∧ RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ' ∧ RFree (L.mem s') Z.R Z.C σ' Lst ∧
    RRecv (L.mem s') Z.R σ' ∧ YieldRel Z.T Z.C (L.mem s') σ' ∧ McpRel Z.T (L.mem s') σ' ∧
    BufWordRel Z.T (L.mem s') σ' ∧ NSC (Z.N ∪ Nn) Z.C σ' ∧ Inv σ' ∧
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurOwnW Z.T Z.C σ' ∧ OffOK σ' ∧ ActIdle σ' ∧
    BlockedScActive σ' ∧ IpcSorted σ' ∧ CurRunM σ' := by
  have hC := CnStep.of_cnK hcn
  obtain ⟨k1, k2, kb, k3, k4⟩ := inSlotW_keepsB J hw hWT hWC hWR
  have ck := uaCKeep hA hi hC
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  refine ⟨hCR', hRP', RFree.carry J.rfree J.call k4 ck, J.rrecv.uadd hA hi hC k4,
    J.yld.frame k2 (uaYKeep hA hi hC), J.mcp.frame k1 (uaMcpKeep hA hi hC), J.buf.frame kb (uaBufKeep hA hi hC),
    (J.nsc.uadd hA hi hWn).cn hC.toHStep, (Inv.add J.inv hA hi.fresh).cn hC,
    CurInvW.cn (CurInvW.uadd J.cur hA hi) hC, (J.own.uadd hA hi).cn hC.toHStep, (J.off.uadd hA hi).cn hC.toHStep,
    (J.act.uadd hA hi).cn hC, (BlockedScActive.add J.bsa hA hi.fresh).cn hC.toHStep,
    (J.isorted.uadd hA hi).cn hC.toHStep, (J.curRun.uadd hA hi).cn hC.toHStep (Or.inr hC.act)⟩



/-- **`JAtZ.uaRest` with window writes: a retype's fresh idle objects**
(module docstring): from `JAtZ` before, FL4 writing slot words and window words `Win` (apart from `T`, `C`'s SCs and `R`), and the
spec's `SpecAdd` of idle endpoints or notifications followed by a CNode-only
step: the call stacks and reply placement (`CallRel.carry`, at the old
notifications), `RFree`, `RRecv`, yield, MCP and buffer words, `NSC` at the
notifications grown by `Nn`, `Inv`, `CurInv` unless rescheduling,
`CurOwnW`, `OffOK`, `ActIdle`, `BlockedScActive`, `IpcSorted`, `CurRunM`. -/
theorem JAtZ.uaRestW {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {Win : U64 → Prop} (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWT : ∀ b, Win b → ∀ t ∈ Z.T, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hWC : ∀ b, Win b → ∀ q ∈ Z.C, ∀ x n, σ.kheap q.bv = some (.schedContext x n) →
      b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val)
    (hWR : ∀ b, Win b → ∀ r ∈ Z.R, b.val < r.val ∨ r.val + 32 ≤ b.val)
    {σB σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}
    (hA : SpecAdd σ σB W o) (hi : IdleNew W o) (hcn : CnK σB σ') {Nn : Set U64} (hWn : ∀ n ∈ Nn, W n.bv) :
    CallRel (L.mem s') Z.R Z.C σ' Lst ∧ RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ' ∧ RFree (L.mem s') Z.R Z.C σ' Lst ∧
    RRecv (L.mem s') Z.R σ' ∧ YieldRel Z.T Z.C (L.mem s') σ' ∧ McpRel Z.T (L.mem s') σ' ∧
    BufWordRel Z.T (L.mem s') σ' ∧ NSC (Z.N ∪ Nn) Z.C σ' ∧ Inv σ' ∧
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurOwnW Z.T Z.C σ' ∧ OffOK σ' ∧ ActIdle σ' ∧
    BlockedScActive σ' ∧ IpcSorted σ' ∧ CurRunM σ' :=
  JAtZB.uaRestW J.toB hw hWT hWC hWR hA hi hcn hWn

set_option maxHeartbeats 2000000 in
/-- `addRPW` over `JAtZB` (mmuAD gen 42b26, in place; `JAtZ.addRPW` is its corollary). -/
theorem JAtZB.addRPW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} {Win : U64 → Prop} (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWT : ∀ b, Win b → ∀ t ∈ Z.T, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hWC : ∀ b, Win b → ∀ q ∈ Z.C, ∀ x n, σ.kheap q.bv = some (.schedContext x n) →
      b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val)
    (hWR : ∀ b, Win b → ∀ r ∈ Z.R, b.val < r.val ∨ r.val + 32 ≤ b.val) {σB σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop}
    {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject} (hA : SpecAdd σ σB W o) (hid : IdleNew W o) (hcn : CnK σB σ')
    {Nn Rn : Set U64} (hWn : ∀ n ∈ Nn, W n.bv) {lo hi : Nat} (hlo0 : 0 < lo) (hhi64 : hi ≤ 2 ^ 64)
    (hfree : RegionFree Z.th lo hi)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat)
    (hNw : ∀ n ∈ Nn, lo ≤ n.val ∧ n.val + 64 ≤ hi)
    (hRw : ∀ r ∈ Rn, r.val % 32 = 0 ∧ lo ≤ r.val ∧ r.val + 32 ≤ hi)
    (hRks : ∀ r ∈ Rn, r.val + 32 ≤ (L.ksb s').val ∨ L.nodeBase s' Z.c + 4288 ≤ r.val)
    (hNR : Nn = ∅ ∨ Rn = ∅) :
    RPlaced st (Z.N ∪ Nn) Z.T Z.C (Z.R ∪ Rn) Z.c s' σ' ∧
      SlotsApart (st := st) Z.th Z.T (Z.N ∪ Nn) Z.C (Z.R ∪ Rn) Z.c s' σ' := by
  obtain ⟨-, hRP, -⟩ := J.uaRestW hw hWT hWC hWR hA hid hcn hWn
  have offR : ∀ r ∈ Z.R, r.val + 32 ≤ lo ∨ hi ≤ r.val := by
    intro r hr
    obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r hr
    have := hspec _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this; omega
  have offN : ∀ n ∈ Z.N, n.val + 64 ≤ lo ∨ hi ≤ n.val := by
    intro n hn
    obtain ⟨x, hx, -⟩ := J.xtop.fin.1.1.2.2.1.ntfn n hn
    have := hspec _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this; omega
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have offT : ∀ t ∈ Z.T, t.val + 4096 ≤ lo ∨ hi ≤ t.val := by
    intro t ht
    have hth : Z.th t = some .tcb := (hJ.tcb t).2 (J.zH.1 t ht)
    have := hfree t .tcb hth
    simp only [objSize] at this; omega
  have hP := J.xtop.rel.1
  have slotOff : ∀ x, IsSlot Z.th x → x.val + 32 ≤ lo ∨ hi ≤ x.val := by
    rintro x ⟨p, i, hpi, rfl⟩
    obtain ⟨k, hk, hs⟩ := hpi.size
    rw [hpi.val hP]
    have := hfree p k hk; omega
  have hsz := uaSzKeep hA hid (CnStep.of_cnK hcn)
  have hAp := J.apart.sc_frame hw.1 hsz
  refine ⟨⟨fun r hr => ?_, fun r hr => ?_, fun r hr t ht => ?_, fun r hr n hn => ?_,
    fun r hr sc hsc x n hx => ?_⟩, fun x hx => ?_⟩
  · rcases hr with hr | hr
    · exact hRP.align r hr
    · obtain ⟨h0, h1, h2⟩ := hRw r hr
      refine ⟨h0, fun e => ?_, by omega⟩
      rw [e] at h1; simp at h1; omega
  · rcases hr with hr | hr
    · exact hRP.ksb r hr
    · exact hRks r hr
  · rcases hr with hr | hr
    · exact hRP.tcb r hr t ht
    · have := offT t ht; have := hRw r hr; omega
  · rcases hr with hr | hr <;> rcases hn with hn | hn
    · exact hRP.ntfn r hr n hn
    · have := offR r hr; have := hNw n hn; omega
    · have := offN n hn; have := hRw r hr; omega
    · rcases hNR with h | h
      · rw [h] at hn; exact hn.elim
      · rw [h] at hr; exact hr.elim
  · rcases hr with hr | hr
    · exact hRP.sc r hr sc hsc x n hx
    · obtain ⟨x0, hx0⟩ := hsz _ _ _ hx
      have := hspec _ _ hx0
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      have := hRw r hr
      rw [Nat.add_comm n]; omega
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hAp x hx
    refine ⟨h1, h2, fun n hn => ?_, h4, fun r hr => ?_⟩
    · rcases hn with hn | hn
      · exact h3 n hn
      · have := slotOff x hx; have := hNw n hn; omega
    · rcases hr with hr | hr
      · exact h5 r hr
      · have := slotOff x hx; have := hRw r hr; omega


/-- **`JAtZ.addRP` with window writes**: `RPlaced` and `SlotsApart` at the notifications and replies grown by
the window across the retype (`JAtZ.uaRest`'s `RPlaced` at the old sets,
`SlotsApart.sc_frame`): the new notifications and replies lie in `[lo, hi)`,
where no spec object (so no reply, notification or SC) and no object of the
typed heap (so no slot, no TCB) is; at most one of the two sets is new. -/
theorem JAtZ.addRPW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} {Win : U64 → Prop} (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWT : ∀ b, Win b → ∀ t ∈ Z.T, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hWC : ∀ b, Win b → ∀ q ∈ Z.C, ∀ x n, σ.kheap q.bv = some (.schedContext x n) →
      b.val < q.val ∨ q.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ b.val)
    (hWR : ∀ b, Win b → ∀ r ∈ Z.R, b.val < r.val ∨ r.val + 32 ≤ b.val) {σB σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop}
    {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject} (hA : SpecAdd σ σB W o) (hid : IdleNew W o) (hcn : CnK σB σ')
    {Nn Rn : Set U64} (hWn : ∀ n ∈ Nn, W n.bv) {lo hi : Nat} (hlo0 : 0 < lo) (hhi64 : hi ≤ 2 ^ 64)
    (hfree : RegionFree Z.th lo hi)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat)
    (hNw : ∀ n ∈ Nn, lo ≤ n.val ∧ n.val + 64 ≤ hi)
    (hRw : ∀ r ∈ Rn, r.val % 32 = 0 ∧ lo ≤ r.val ∧ r.val + 32 ≤ hi)
    (hRks : ∀ r ∈ Rn, r.val + 32 ≤ (L.ksb s').val ∨ L.nodeBase s' Z.c + 4288 ≤ r.val)
    (hNR : Nn = ∅ ∨ Rn = ∅) :
    RPlaced st (Z.N ∪ Nn) Z.T Z.C (Z.R ∪ Rn) Z.c s' σ' ∧
      SlotsApart (st := st) Z.th Z.T (Z.N ∪ Nn) Z.C (Z.R ∪ Rn) Z.c s' σ' :=
  JAtZB.addRPW J.toB hw hWT hWC hWR hA hid hcn hWn hlo0 hhi64 hfree hspec hNw hRw hRks hNR

set_option maxHeartbeats 4000000 in
/-- `ret_utcW` over `JAtZB` (mmuAD gen 42b26, in place; `JAtZ.ret_utcW` is its corollary). -/
theorem JAtZB.ret_utcW {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    {xs : Fl4Spec.CslotPtr} {p0 sb0 fi0 fi1 : U64} (hxs : AbsSlot Z.th xs)
    (hc0 : capV (L.mem s) (cslotAddr xs) = .Untyped p0 sb0 fi0 false)
    (hc1 : capV (L.mem s') (cslotAddr xs) = .Untyped p0 sb0 fi1 false) (hfi : fi0.val ≤ fi1.val)
    (hfi1 : fi1.val ≤ 2 ^ sb0.val) (Dst : Fl4Spec.CslotPtr → Prop)
    (hDa : ∀ d, Dst d → AbsSlot Z.th d) (hDn : ∀ d, Dst d → capAt (L.mem s) (cslotAddr d) = ok .Null)
    (hDu : ∀ d, Dst d → ∀ p sb fi dv, capV (L.mem s') (cslotAddr d) ≠ .Untyped p sb fi dv)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr xs → (∀ d, Dst d → y ≠ cslotAddr d) →
      capV (L.mem s') y = capV (L.mem s) y)
    {Win : U64 → Prop} (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWs : ∀ b, Win b → b.val < p0.val + fi1.val)
    (hWo : ∀ sl p sb fi, AbsSlot Z.th sl → cslotAddr sl ≠ cslotAddr xs →
      capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi false → ∀ b, Win b → b.val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ b.val)
    (hWd : ¬ Win (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) (hcdt : ∀ x, ¬ Dst x → σ'.cdt x = σ.cdt x)
    (horig : ∀ sl, ¬ Dst sl → σ'.isOriginalCap sl = σ.isOriginalCap sl)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hM' : MdbLinks Z.th (L.mem s') G') (hchild : ∃ x, σ'.cdt x = some xs)
    (hlv : ∀ d, Dst d → ∀ sl p sb fi dev, AbsSlot Z.th sl → capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev →
      dev = false → (¬ ∃ x, σ.cdt x = some sl) →
      ((cslotAddr d).val < p.val ∨ p.val + 2 ^ sb.val ≤ (cslotAddr d).val) ∧
        AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) d) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' G' sl p sb fi := by
  intro sl p sb fi dev hsl hcap' hdF
  obtain ⟨hP, ⟨-, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  -- a slot misses the free part of a cap with the facts `U`
  have hobjU : ∀ {sl1 : Fl4Spec.CslotPtr} {p1 sb1 fi1' : U64}, UtCapP3 (L := L) arI Z.th s σ Z.G sl1 p1 sb1 fi1' →
      ∀ y, IsSlot Z.th y → y.val + 32 ≤ p1.val + fi1'.val ∨ p1.val + 2 ^ sb1.val ≤ y.val := by
    intro sl1 p1 sb1 fi1' U y hy
    obtain ⟨q, i, hi, rfl⟩ := hy
    obtain ⟨k, hk, hs⟩ := hi.size
    have hv := hi.val hP
    rcases U.free q k hk with e | e <;> omega
  by_cases hsx : cslotAddr sl = cslotAddr xs
  · -- the source: its free index raised
    have e := cslotAddr_inj hP hsl hxs hsx
    subst e
    have hcv := capV_of_capAt hcap'
    rw [hc1] at hcv
    injection hcv with e1 e2 e3 e4
    rw [← e1, ← e2, ← e3]
    have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p0 sb0 fi0 false) := by rw [capAt_capV, hc0]
    have U := J.utc sl p0 sb0 fi0 false hsl hcap0 rfl
    have B0 : NotDev (L.mem s) (cslotAddr sl) p0 sb0 fi0 := by unfold NotDev; rw [hc0]; simp
    have hobj := hobjU U
    refine ⟨U.pal, U.pfit, hfi1, fun _ => U.high B0, fun _ => by rw [hcpu, hna]; exact U.actZ B0,
      fun q k hq => (U.free q k hq).imp (fun e => by omega) id,
      fun _ w hal h1 h2 => ?_, U.sb4, U.nostr, fun y hy => ?_, fun h0 => absurd hchild h0,
      fun _ h0 => absurd hchild h0,
      fun _ => by rw [hna]; exact U.dwReg B0, fun _ => by rw [hgp]; exact U.gReg B0⟩
    · rw [hw.mem_eq hal fun h => h.elim (fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega)
        (fun h => by have := hWs w h; omega)]
      exact U.zero B0 w hal (by omega) h2
    · have := hobj y ((hM'.members y).1 hy).1
      omega
  -- another untyped cap: unchanged
  have hnd : ∀ d, Dst d → cslotAddr sl ≠ cslotAddr d := fun d hd e =>
    hDu d hd p sb fi dev (by rw [← e]; exact capV_of_capAt hcap')
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hcap _ hsl.isSlot hsx hnd]; exact capV_of_capAt hcap'
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdF
  have hobj := hobjU U
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun h => h.elim (fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩) hWd
  have hdnm : ∀ d, Dst d → cslotAddr d ∉ Z.G.chains.flatten := fun d hd h => by
    obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hDn d hd] at h0; exact hn (eq_of_ok_eq h0).symm
  have hnc' : (¬ ∃ x, σ'.cdt x = some sl) → ¬ ∃ x, σ.cdt x = some sl := by
    rintro h0 ⟨x, hx⟩
    apply h0
    by_cases e : Dst x
    · exfalso
      have h1 := hC.cdt _ (hDa x e)
      rw [hx] at h1
      exact hdnm x e (hM.tree.par_mem _ _ h1.symm).1
    · exact ⟨x, by rw [hcdt x e]; exact hx⟩
  have B := notDev_back (capV_of_capAt hcap') hcv
  have hxsG : cslotAddr xs ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hxs.isSlot, _, by rw [capAt_capV, hc0], by simp⟩
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free,
    fun g w hal h1 h2 => ?_, U.sb4,
    U.nostr, fun y hy => ?_, fun h0 y hy => ?_, 
    fun g h0 hf0 => ?_, fun g => by rw [hna]; exact U.dwReg (B g), fun g => by rw [hgp]; exact U.gReg (B g)⟩
  · rw [hw.mem_eq hal fun h => h.elim (fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega)
      (fun h => by
        have hdv : dev = false := hdF
        subst hdv
        rcases hWo sl p sb fi hsl hsx hcv w h with e | e <;> omega)]
    exact U.zero (B g) w hal h1 h2
  · have := hobj y ((hM'.members y).1 hy).1
    omega
  · have hnc := hnc' h0
    by_cases ed : ∃ d, Dst d ∧ y = cslotAddr d
    · obtain ⟨d, hd, rfl⟩ := ed
      exact (hlv d hd sl p sb fi dev hsl hcv hdF hnc).1
    · by_cases ex : y = cslotAddr xs
      · subst ex; exact U.ns hnc _ hxsG
      · obtain ⟨hys, c0, h0', hn⟩ := (hM'.members y).1 hy
        have hc0' : capAt (L.mem s) y = ok c0 := by
          rw [capAt_capV, ← hcap y hys ex (fun d hd e => ed ⟨d, hd, e⟩), ← capAt_capV]; exact h0'
        exact U.ns hnc y ((hM.members y).2 ⟨hys, c0, hc0', hn⟩)
  · have hnc := hnc' h0
    obtain ⟨r1, r3⟩ := U.rst (B g) hnc hf0
    refine ⟨fun sl' h => ?_, by rw [hna, hDbg]; exact r3⟩
    by_cases e : Dst sl'
    · exact (hlv sl' e sl p sb fi dev hsl hcv hdF hnc).2
    · exact r1 sl' (by rw [← horig sl' e]; exact h)


/-- **The untyped caps' facts after a retype that keeps the typed heap**
(`JAtZ.ret_utc` with FL4 also writing the window `Win`, below the source's new free index and off
every other RAM untyped cap's free part and the debug word; `ins_utcG` for the
creation's insertions `Dst` and the source's free index raised from `fi0`
to `fi1`): the source keeps its facts at the higher free index (its free
part shrinks; it has a child after, `hchild`); every other untyped cap keeps
them as in `ins_utcG` (the new MDB slots miss every childless untyped
region, `hlv`, from the destination's liveness). -/
theorem JAtZ.ret_utcW {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    {xs : Fl4Spec.CslotPtr} {p0 sb0 fi0 fi1 : U64} (hxs : AbsSlot Z.th xs)
    (hc0 : capV (L.mem s) (cslotAddr xs) = .Untyped p0 sb0 fi0 false)
    (hc1 : capV (L.mem s') (cslotAddr xs) = .Untyped p0 sb0 fi1 false) (hfi : fi0.val ≤ fi1.val)
    (hfi1 : fi1.val ≤ 2 ^ sb0.val) (Dst : Fl4Spec.CslotPtr → Prop)
    (hDa : ∀ d, Dst d → AbsSlot Z.th d) (hDn : ∀ d, Dst d → capAt (L.mem s) (cslotAddr d) = ok .Null)
    (hDu : ∀ d, Dst d → ∀ p sb fi dv, capV (L.mem s') (cslotAddr d) ≠ .Untyped p sb fi dv)
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr xs → (∀ d, Dst d → y ≠ cslotAddr d) →
      capV (L.mem s') y = capV (L.mem s) y)
    {Win : U64 → Prop} (hw : P1.WritesIn st s s' (fun b => InSlot Z.th b ∨ Win b))
    (hWs : ∀ b, Win b → b.val < p0.val + fi1.val)
    (hWo : ∀ sl p sb fi, AbsSlot Z.th sl → cslotAddr sl ≠ cslotAddr xs →
      capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi false → ∀ b, Win b → b.val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ b.val)
    (hWd : ¬ Win (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) (hcdt : ∀ x, ¬ Dst x → σ'.cdt x = σ.cdt x)
    (horig : ∀ sl, ¬ Dst sl → σ'.isOriginalCap sl = σ.isOriginalCap sl)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hM' : MdbLinks Z.th (L.mem s') G') (hchild : ∃ x, σ'.cdt x = some xs)
    (hlv : ∀ d, Dst d → ∀ sl p sb fi dev, AbsSlot Z.th sl → capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev →
      dev = false → (¬ ∃ x, σ.cdt x = some sl) →
      ((cslotAddr d).val < p.val ∨ p.val + 2 ^ sb.val ≤ (cslotAddr d).val) ∧
        AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) d) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s' σ' G' sl p sb fi :=
  JAtZB.ret_utcW J.toB hxs hc0 hc1 hfi hfi1 Dst hDa hDn hDu hcap hw hWs hWo hWd hcdt horig hgp hM' hchild hlv

end

end

end Fl4Proofs.P3

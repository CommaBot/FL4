/-
P3 (DESIGN.md §9), untyped: **the no-reset retype of endpoints or
notifications at `J`**, the pieces around `JAtZ.utEpXTop` (handoff/utj.md
"Round 4c").

* `invokeUntyped_noreset_co`: the spec's `invoke_untyped` without a reset
  keeps the CDT and the original bits of every slot but the destination
  window's (`create_cap` sets them at its destination only).
* `Sched.JPlaced.of_kheap`: `JPlaced` reads the spec state's heap only.
* `XSets.addW_two`, `XSets.addW_ne`: `XSets.addW` as a record update with
  both sets grown (one by nothing).
* `JKern.hout`: `JKern` over P1's heap after a no-reset retype (`HOut` over
  the window, the new objects off the kernel-state block and the nodes).
* `JAtZ.create_noreset`: P1's creation over `H` after the restart
  (`creation_step`; the window's objects dead and unreferenced by
  `RegionUnrefJ` [J]), giving `BlkOK`, `HOut` and `JCovD` after.
-/
import Fl4Proofs.P3.UtRetJ
import Fl4Proofs.P3.SlotCdt
import Fl4Proofs.P3.XTopJointRunPost
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-! ## The spec's CDT and original bits -/

section Spec
open Fl4Spec

variable {d : CslotPtr → Prop}

theorem ncd_gets_bind {α β : Type} (f : State Unit → α) (g : α → NonDet (State Unit) β)
    (h : ∀ σ, ∀ x ∈ (g (f σ) σ).1, CdtKeepOff d σ x.2) : NCd d (NonDet.gets f >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx

theorem ncdAt_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} {σ : State Unit}
    (hm : ∀ x ∈ (m σ).1, CdtKeepOff d σ x.2) (hf : ∀ a, NCd d (f a)) :
    ∀ x ∈ ((m >>= f) σ).1, CdtKeepOff d σ x.2 := by
  intro x ⟨y, hy, hx⟩
  exact (hm y hy).trans (hf y.1 y.2 x hx)

theorem ncdAt_setCdt {sl0 : CslotPtr} (hd : d sl0) (v : Option CslotPtr) (σ : State Unit) :
    ∀ x ∈ (setCdt (Z := Unit) (Function.update σ.cdt sl0 v) σ).1, CdtKeepOff d σ x.2 := by
  unfold setCdt
  intro x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  intro sl h
  exact Function.update_of_ne (fun e => h (by subst e; exact hd)) _ _

/-- `create_cap` changes the CDT at its destination only. -/
theorem ncd_createCap (t : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (dev : Bool)
    (x : CslotPtr × ObjRef) (hx : d x.1) : NCd d (createCap (Z := Unit) t bits untyped dev x) := by
  obtain ⟨dst, o⟩ := x
  unfold createCap
  refine ncd_bind (ncd_gets _) (fun _ => ncd_gets_bind _ _ (fun σ => ncdAt_bind (ncdAt_setCdt hx _ σ) (fun _ => ?_)))
  repeat (first | exact ncd_setOriginal _ _ | exact ncd_setCap _ _ | exact ncd_doExtendedOp _ | ncd_step)

/-- `create_cap` changes the original bit at its destination only. -/
theorem no_createCap (t : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (dev : Bool)
    (x : CslotPtr × ObjRef) (hx : d x.1) : NO d (createCap (Z := Unit) t bits untyped dev x) := by
  obtain ⟨dst, o⟩ := x
  unfold createCap setCdt
  repeat (first | exact no_setOriginal hx _ | exact no_getCap _ | exact no_setCap _ _ | exact no_doExtendedOp _ |
    no_step)

theorem ncd_mapMx_mem {α β : Type} {f : α → NonDet (State Unit) β} :
    ∀ l : List α, (∀ a ∈ l, NCd d (f a)) → NCd d (NonDet.mapMx f l)
  | [], _ => ncd_pure' _
  | a :: l, h => ncd_bind (h a (List.mem_cons_self ..))
      (fun _ => ncd_mapMx_mem l (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem no_mapMx_mem {α β : Type} {f : α → NonDet (State Unit) β} :
    ∀ l : List α, (∀ a ∈ l, NO d (f a)) → NO d (NonDet.mapMx f l)
  | [], _ => no_pure' _
  | a :: l, h => no_bind (h a (List.mem_cons_self ..))
      (fun _ => no_mapMx_mem l (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- **The spec's `invoke_untyped` without a reset keeps the CDT and the
original bits off the destination slots.** -/
theorem invokeUntyped_noreset_co (bitsApi : ApiObjectType → Nat → Nat) (sl : CslotPtr) (pb rb : ObjRef)
    (t : ApiObjectType) (us : Nat) (slots : List CslotPtr) (dev : Bool) (σ : State Unit)
    (ht : t ≠ .untyped) (hp4 : t ≠ .archObject .pml4Obj) :
    NAll (invokeUntypedWith (Z := Unit) bitsApi (.retype sl false pb rb t us slots dev)).run σ
      (fun y => CdtKeepOff (· ∈ slots) σ y.2 ∧ OKeep (· ∈ slots) σ y.2) := by
  set ptrs := regionPtrs rb slots.length (2 ^ bitsApi t us) with hptrs
  have hpre : NAll (NonDetE.whenE (false = true) (resetUntypedCap (Z := Unit) sl)).run σ
      (fun y => y.1 = .ok () ∧ y.2 = σ) := by
    unfold NonDetE.whenE
    rw [if_neg (by decide)]
    exact nall_det rfl ⟨rfl, rfl⟩
  unfold invokeUntypedWith
  apply nallE_bind
  refine hpre.mono (fun x ⟨hx1, hx2⟩ => ?_)
  rcases x with ⟨e | u, σr⟩
  · cases hx1
  dsimp only at hx2 ⊢
  subst hx2
  apply nall_liftE
  apply nall_bind
  refine (show NAll (getCap (Z := Unit) sl) σr (fun x => CdtKeepOff (· ∈ slots) σr x.2 ∧ OKeep (· ∈ slots) σr x.2)
    from fun x hx => ⟨ncd_getCap sl σr x hx, no_getCap sl σr x hx⟩).mono (fun x hx => ?_)
  apply nall_bind; refine nall_det rfl ?_
  apply nall_bind; refine nall_det rfl ?_
  apply nall_bind
  refine (show NAll (setCap (Z := Unit) _ sl) x.2
      (fun x2 => CdtKeepOff (· ∈ slots) x.2 x2.2 ∧ OKeep (· ∈ slots) x.2 x2.2)
    from fun x2 hx2 => ⟨ncd_setCap _ sl _ x2 hx2, no_setCap _ sl _ x2 hx2⟩).mono (fun x2 hx2 => ?_)
  apply nall_bind
  refine nall_det (retypeRegionWith_eq bitsApi rb slots.length us t dev x2.2) ?_
  rw [if_pos ht]
  apply nall_bind
  refine nall_det (show initArchObjects (Z := Unit) t dev rb slots.length us ptrs
      (regionHeap x2.2 ptrs (defaultObject t dev us x2.2.curDomain)) =
      ({((), regionHeap x2.2 ptrs (defaultObject t dev us x2.2.curDomain))}, False) by
    unfold initArchObjects NonDet.when; rw [if_neg hp4]; rfl) ?_
  intro y hy
  have hmem : ∀ a ∈ slots.zip ptrs, a.1 ∈ slots := fun a ha => (List.of_mem_zip ha).1
  have h3c := ncd_mapMx_mem (d := (· ∈ slots)) _ (fun a ha => ncd_createCap t us sl dev a (hmem a ha)) _ y hy
  have h3o := no_mapMx_mem (d := (· ∈ slots)) _ (fun a ha => no_createCap t us sl dev a (hmem a ha)) _ y hy
  exact ⟨(hx.1.trans hx2.1).trans h3c, (hx.2.trans hx2.2).trans h3o⟩

end Spec

/-! ## Small frames -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `JPlaced` reads the spec state's heap only. -/
theorem Sched.JPlaced.of_kheap {th : TypedHeap} {H : Heap} {Tr C : Set U64} {s : S} {σ σ' : Fl4Spec.State Unit}
    (h : JPlaced (L := L) th H Tr C s σ) (hk : σ'.kheap = σ.kheap) : JPlaced (L := L) th H Tr C s σ' :=
  { h with sc := fun c y n hc hk' => h.sc c y n hc (by rw [← hk]; exact hk') }

end

theorem XSets.addW_two {Z : XSets} {nt : U64} {G' : MdbGhost} {W : Set U64} (h : nt.val = 2) :
    Z.addW nt G' W = { Z with G := G', E := Z.E ∪ W, N := Z.N ∪ ∅ } := by
  unfold XSets.addW; rw [if_pos h, Set.union_empty]

theorem XSets.addW_ne {Z : XSets} {nt : U64} {G' : MdbGhost} {W : Set U64} (h : nt.val ≠ 2) :
    Z.addW nt G' W = { Z with G := G', E := Z.E ∪ ∅, N := Z.N ∪ W } := by
  unfold XSets.addW; rw [if_neg h, Set.union_empty]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`JKern` over P1's heap after a no-reset retype**: `H'` is `HOut` over
the window (objects meeting it dropped, the new ones added); the new
objects are no `other` objects and lie off the kernel-state block and the
nodes; the current thread's and SC's objects are kept. -/
theorem JKern.hout {H H' : Heap} {Cs D D' : Set U64} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}
    (K : JKern (L := L) H Cs D th s σ) (hH' : HeapOK H') {A k w : Nat} {Kd : Option HKind}
    (hout : HOut H H' A (A + w * k) A k w Kd) (hk1 : 1 ≤ k) (hA0 : 0 < A)
    (hnew : ∀ q kd, NewAt A k w q → Kd = some kd →
      (q.val + 2 ^ kd.bits ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ q.val) ∧
      ∀ c ∈ Cs, q.val + 2 ^ kd.bits ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ q.val)
    (hcur : (L.curW s).val + 2 ^ 12 ≤ A ∨ A + w * k ≤ (L.curW s).val)
    (hcsc : H' (L.cscW s) ≠ none) :
    JKern (L := L) H' Cs D' th s σ := by
  have back := fun {q} {kd} (h : H' q = some kd) => hout_back hout h
  have h0' : H' 0#u64 = none := by
    cases e : H' 0#u64 with
    | none => rfl
    | some kd =>
      rcases back e with ⟨hn, -⟩ | h
      · have := (newAt_bd hk1 hn).1; simp at this; omega
      · rw [K.h0] at h; cases h
  refine ⟨K.orig, K.cur, K.curT, K.act, K.dwAl, K.dwObj, K.dwNe, K.head, K.gpm, K.ga, K.gf, hH', h0',
    fun q kd hq ho => ?_, fun q z hq => ?_, fun q kd hq c hc => ?_, K.ksbFit, K.ksbAl, K.nodeFit, K.cpuCs, ?_, hcsc,
    K.csLt, K.cs0⟩
  · rcases back hq with ⟨hn, hK⟩ | h
    · exact (hnew q kd hn hK).1
    · exact K.hks q kd h ho
  · rcases back hq with ⟨hn, hK⟩ | h
    · exact Or.imp_right Or.inl (hnew q _ hn hK).1
    · exact K.hksIn q z h
  · rcases back hq with ⟨hn, hK⟩ | h
    · exact (hnew q kd hn hK).2 c hc
    · exact K.hnd q kd h c hc
  · exact hout_old hout rfl rfl hk1 K.curH hcur

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- A slot word is no TCB word past the TCB's cap slots (offset `K ≥ 256`). -/
theorem slot_word_ne_tw {th : TypedHeap} {H : P1.Heap} {Tr C : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (hJP : JPlaced (L := L) th H Tr C s σ) {v : U64} (hv : SlotSpan th v) {y : U64} (hy : H y = some .tcb)
    {K : U64} (hK : 256 ≤ K.val) (hK2 : K.val < 4096) : v ≠ core.num.U64.wrapping_add y K := by
  obtain ⟨a, ha, h1, h2⟩ := hv
  obtain ⟨q, kq, hq, e1, e2, e3, -⟩ := hJP.slot_in ha
  have hyK : (core.num.U64.wrapping_add y K).val = y.val + K.val := tcb_word hJP.heap hy hK2
  intro e
  rw [e, hyK] at h1 h2
  by_cases hyq : y = q
  · subst hyq; rw [hy] at hq; cases hq
    have := e3 rfl
    omega
  · have hd := hJP.heap.disj y .tcb q kq hy hq hyq
    rw [show (2 : Nat) ^ HKind.tcb.bits = 4096 from rfl] at hd
    omega

/-- **`DeadX` across a write frame** (jc6e): the frame misses the TCB's
`DEBUG_PREV` and deadline words, and each core's head word is unwritten or
names another object after. -/
theorem deadX_of_frame {H : P1.Heap} {Cs : Set U64} {s s' : S} {q : U64} {Pw : U64 → Prop} (hH : P1.HeapOK H)
    (hW : WFrame (L := L) s s' Pw)
    (hpw : H q = some .tcb → ∀ v, Pw v → v ≠ P1.dpA q ∧ v ≠ P1.tdA q)
    (hhd : H q = some .tcb → ∀ c ∈ Cs, (∀ v, Pw v → v ≠ L.nodeAt s c layout.node.DEBUG_TCBS) ∨
      L.mem s' (L.nodeAt s c layout.node.DEBUG_TCBS) ≠ q)
    (hnal : ∀ c ∈ Cs, P1.Aligned (L.nodeAt s c layout.node.DEBUG_TCBS))
    (hd : Sched.DeadX (L := L) H Cs s q) : Sched.DeadX (L := L) H Cs s' q := by
  intro hq
  obtain ⟨d1, d2, d3⟩ := hd hq
  have hal := hH.align q .tcb hq
  simp only [HKind.bits] at hal
  have hdp : (P1.dpA q).val = q.val + 3584 := tcb_word hH hq (by simp)
  have htd : (P1.tdA q).val = q.val + 3528 := tcb_word hH hq (by simp)
  have hp := hpw hq
  refine ⟨?_, fun c hc => ?_, ?_⟩
  · rw [hW.2.2 (P1.dpA q) (by unfold P1.Aligned; rw [hdp]; omega) (fun h => (hp _ h).1 rfl)]; exact d1
  · rw [P1.nodeAt_of_ksb hW.1]
    rcases hhd hq c hc with h | h
    · rw [hW.2.2 _ (hnal c hc) (fun hp' => h _ hp' rfl)]; exact d2 c hc
    · exact h
  · rw [hW.2.2 (P1.tdA q) (by unfold P1.Aligned; rw [htd]; omega) (fun h => (hp _ h).2 rfl)]; exact d3

/-- **`DeadX` across the restart** (jc6e): it writes the current thread's
state word and the current core's scheduler-action word, none of a dead
TCB's words nor a core's head word. -/
theorem deadX_restart {H : P1.Heap} {Cs : Set U64} {s0 s : S} {c q : U64} (hH : P1.HeapOK H)
    (hfr : Frame2 (L := L) s0 s (P1.stA c) (L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION))
    (hks : L.ksb s = L.ksb s0) (hc : H c = some .tcb) (hqc : q ≠ c)
    (hnd : ∀ p k, H p = some k → ∀ c' ∈ Cs, p.val + 2 ^ k.bits ≤ L.nodeBase s0 c' ∨ L.nodeBase s0 c' + 4288 ≤ p.val)
    (hcpu : L.cpu s0 ∈ Cs) (hnf : (L.ksb s0).val + 13568 + ((L.cpu s0).val + 1) * 4288 ≤ 2 ^ 64)
    (hDv : ∀ c' ∈ Cs, (L.nodeAt s0 c' layout.node.DEBUG_TCBS).val = L.nodeBase s0 c' + 88)
    (hnal : ∀ c' ∈ Cs, P1.Aligned (L.nodeAt s0 c' layout.node.DEBUG_TCBS))
    (hd : Sched.DeadX (L := L) H Cs s0 q) : Sched.DeadX (L := L) H Cs s q := by
  intro hq
  obtain ⟨d1, d2, d3⟩ := hd hq
  have b12 : (2 : Nat) ^ HKind.tcb.bits = 4096 := rfl
  have hal := hH.align q .tcb hq
  simp only [HKind.bits] at hal
  have hdp : (P1.dpA q).val = q.val + 3584 := tcb_word hH hq (by simp)
  have htd : (P1.tdA q).val = q.val + 3528 := tcb_word hH hq (by simp)
  have kw := restart_keeps_obj hH hfr hq hc hqc (hnd q .tcb hq _ hcpu) hnf
  refine ⟨?_, fun c' hc' => ?_, ?_⟩
  · rw [kw (P1.dpA q) (by omega) (by omega) (by omega)]; exact d1
  · have hst : (P1.stA c).val = c.val + 3328 := by rw [P1.stA_eq]; exact tcb_word hH hc (by simp)
    have hsa := nodeAt_val' (L := L) (s := s0) (off := layout.node.SCHED_ACTION) hnf
      (by simp [layout.node.SCHED_ACTION])
    have h16 : layout.node.SCHED_ACTION.val = 16 := by simp [layout.node.SCHED_ACTION]
    have hcn := hnd c .tcb hc c' hc'
    have hdv := hDv c' hc'
    unfold LawfulStore.nodeBase at hcn hdv
    rw [P1.nodeAt_of_ksb hks, hfr (L.nodeAt s0 c' layout.node.DEBUG_TCBS) (hnal c' hc') (by omega) (by omega)]
    exact d2 c' hc'
  · rw [kw (P1.tdA q) (by omega) (by omega) (by omega)]; exact d3

set_option maxHeartbeats 4000000 in
/-- **P1's creation after the restart, without a reset** (module docstring):
from `JAtZ` at the decode (no switch pending) and after the restart, a CNode
slot's RAM untyped cap, the creation's `RetExp` over a window `[A0, A0 + w * k)`
of objects of type `n` (no TCB; an SC of at least the minimum size: endpoints,
notifications, replies, SCs, VSpace tables, frames, untypeds; the new caps no
untyped caps when the type has `H` objects), its frame (slot words, and the window's words when `pml4`: the new PML4s'
kernel half) and zero window: P1's heap after (`HOut` over
the window), `BlkOK` and `JCovD` after (the window's objects dead,
`retype_window_dead`, and unreferenced, `RegionUnrefJ` [J]). -/
theorem JAtZ.create_noresetW {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    {s1 : S} {σ1 : Fl4Spec.State Unit} {Ac1 : Set U64} {Lst1 : U64 → List U64} {D1 : Set U64}
    (J1 : JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 s1 ar σ1)
    (hs1 : sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s1)
    (hct1 : σ1.curThread = σ.curThread) (hcsc1 : σ1.curSc = σ.curSc) (hid1 : σ1.idleThread = σ.idleThread)
    (hisc1 : σ1.idleSc = σ.idleSc) (hns1 : ∀ u, σ1.schedulerAction = .switchThread u → False)
    (hRU : RegionUnrefAt (L := L) H Cs D s)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {s' : S} {th' : TypedHeap} {G' : MdbGhost} {A0 k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
    (hE : RetExp Z.th th' (L.mem s) (L.mem s') Z.G G' A0 k w dslot cj (cslotAddr (pp.bv, idx)))
    {n us : Nat} (hcjU : newKind n us ≠ none → ∀ j, j < w → isUt (cj j) = false)
    (hn : n ≠ 1 ∧ (n = 5 → 7 ≤ us)) (hk : k = 2 ^ zOf n us) (hAk : A0 % k = 0)
    {T pml4 : Prop} (hT : ¬ T)
    (hW : WFrame (L := L) s1 s' (fun v => ((T ∧ TcbLoopW Z.th A0 w (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS)
      (L.mem s1 (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan Z.th v) ∨
      (pml4 ∧ A0 ≤ v.val ∧ v.val < A0 + w * k)))
    (hWZ : (∀ z, newKind n us ≠ some (.other z)) → WinZero (L.mem s') A0 k w T) (hidl : IdleKeep (L := L) s s') :
    ∃ (H' : Heap) (Ac' : Set U64),
      BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H')
        (Heap.ntfns H') (Heap.scBits H') Ac' s' ∧
      HOut H H' A0 (A0 + w * k) A0 k w (newKind n us) ∧
      JCovD (L := L) th' H' G' {q | q ∈ D ∧ ¬ NewQ A0 k w cj q} Cs s' := by
  let ex : Aeneas.Std.Array obj.Slot 3#usize := Aeneas.Std.Array.repeat 3#usize 0#u64
  have hres : σ.schedulerAction ≠ .chooseNewThread := by rw [hni.2]; simp
  have UJ := J.utJoint (extra := ex) hres hpp hidx rfl hcap (by
    intro x hx h0; exfalso; apply h0; simpa [ex, Aeneas.Std.Array.repeat, List.mem_replicate] using hx)
  obtain ⟨hfr, hks1, hcpu1, -⟩ := UJ.restart hs1
  obtain ⟨hP, ⟨-, -, hM, -, hI⟩, -⟩ := J.xtop.rel
  have hS := J.xtop.fin.1.1.1
  have hS1 := J1.xtop.fin.1.1.1
  have hna : ∀ c o, L.nodeAt s1 c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS1.lists
  have hcw : L.curW s1 = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu1, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hct1]
  have hcs : L.cscW s1 = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu1, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hcsc1]
  have hact : ∀ y ∈ H.tcbs, L.actionW s1 ≠ y := fun y hy =>
    actionW_ne_of hS1 (by rw [J1.tcbs_eq.1]; exact hy) (fun e => hns1 _ e)
  obtain ⟨-, x, hkx, hrx⟩ := J.curRunnable hni (cur_thread_eq s)
  have hcT : L.curW s ∈ Z.T := by rw [J.tcbs_eq.1]; exact J.kern.curH
  have hrun : Runnable (L.mem s (stA (L.curW s))) := by
    show Runnable (L.mem s (P1.stA (L.curW s))); rw [stA_tStA]; exact (runnable_iff (J.xtop.fin.1.1.2.2.1.at_tcb hcT hkx).st).2 hrx
  -- the window, in the source's free part
  have hcv := capV_of_capAt hcap
  obtain ⟨hxG, p1, sb1, fi0', fi1, d1, e0, -, hpA, -, hAs, -, -⟩ := hE.usrc
  rw [hcv] at e0
  simp only [capability.Cap.Untyped.injEq] at e0
  obtain ⟨hp1, hsb1, hfi1, -⟩ := e0
  subst p1 sb1 fi0'
  have hAs' : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have U := J.utc _ p sb fi false hAs' hcap rfl
  obtain ⟨hk1', hk2, -⟩ := J.jcov.ks _ hxG p sb fi hcv
  have hk1 : 1 ≤ k := hE.k1
  have hfitW : A0 + w * k ≤ 2 ^ 64 := le_trans hAs U.pfit
  have hpos : 0 < A0 := by
    have := U.high (notDev_ram hcv); omega
  have hnb : ∀ c, L.nodeBase s1 c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hks1]
  have RD : ∀ q kd, H q = some kd → RegionD H A0 (A0 + w * k) q → q ∈ D ∧ DeadP (L := L) H s q := by
    intro q kd hq hr
    refine (retype_window_dead J.jcov J.ut hI hE ⟨p, sb, fi, hcv⟩).1 q kd hq ?_
    unfold RegionD at hr; rw [hq] at hr; simp only [Option.elim] at hr
    unfold MeetsR at hr; unfold MeetsW; omega
  have hreg : A0 + w * k ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ A0 := by rcases hk1' with h | h <;> omega
  obtain ⟨hKR, hDT⟩ := hRU s1 hs1 A0 (A0 + w * k) (fun q kd hq hr => (RD q kd hq hr).1)
  have hdrop := dead_dropOK UJ RD hfr hks1 hcpu1 hcw hcs hact hrun hKR hDT hreg
  have hRON : RegionOffNodes st Cs s1 A0 (A0 + w * k) := by
    refine ⟨fun c hc => ?_, ?_⟩
    · rw [hnb]; rcases hk2 c hc with h | h <;> omega
    · rw [hks1]; rcases hk1' with h | h <;> omega
  have hb1 := J1.blk
  have hTm : TimerOK st H.tcbs Cs s1 := hb1.2.2.1.2.2.tm
  obtain ⟨Tr, Cq, hJP⟩ := J.jpl
  have hSC : SlotCapW Z.th H.tcbs H.omega H.frame := slotCapW_of_in hP J.kern.heap (fun a ha => hJP.slot_in ha)
  have hsoff : ∀ v, SlotSpan Z.th v → (∀ y, H y = some .tcb → v ≠ dnA y ∧ v ≠ dpA y) ∧
      (∀ c ∈ Cs, v.val < L.nodeBase s1 c ∨ L.nodeBase s1 c + 4288 ≤ v.val) := fun v hv => by
    obtain ⟨o1, o2⟩ := slot_word_off hJP J.kern.hnd hv
    exact ⟨o1, fun c hc => by rw [hnb]; exact o2 c hc⟩
  have hn1 : n ≠ 1 := hn.1
  have hdbg : DbgLinksOK st H Cs s' A0 (A0 + w * k) A0 k w n := by
    refine dbgLinks_nonTcb hn1 hdrop hTm hW (fun v hv => ?_) (fun y hy => ?_) (fun c hc => ?_)
    · rcases hv with (⟨hT', -⟩ | hsl) | ⟨-, hv1, hv2⟩
      · exact absurd hT' hT
      · obtain ⟨o1, o2⟩ := hsoff v hsl
        refine ⟨fun y hy _ => o1 y hy, fun c hc e => ?_⟩
        have hv0 := nodeAt_val (hTm.npl c hc) (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
        have := o2 c hc
        rw [e, hv0] at this
        have : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
        omega
      · refine ⟨fun y hy hyD => ?_, fun c hc e => ?_⟩
        · have hy' : H y = some .tcb := hy
          have hdn : (dnA y).val = y.val + 3576 := tcb_word J.kern.heap hy (by simp)
          have hdp : (dpA y).val = y.val + 3584 := tcb_word J.kern.heap hy (by simp)
          refine ⟨fun e => hyD ?_, fun e => hyD ?_⟩ <;>
            (unfold RegionD MeetsR; rw [hy']; simp only [Option.elim, HKind.bits, Nat.reducePow]; subst e; omega)
        · have hv0 := nodeAt_val (hTm.npl c hc) (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
          have h4 : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
          have hc2 := hk2 c hc
          have hnc := hnb c
          subst e
          rw [hv0, hnc] at hv1 hv2
          rcases hc2 with h | h <;> omega
    · have hal := J.kern.heap.align y .tcb hy
      simp only [HKind.bits] at hal
      have hdn : (dnA y).val = y.val + 3576 := tcb_word J.kern.heap hy (by simp)
      have hdp : (dpA y).val = y.val + 3584 := tcb_word J.kern.heap hy (by simp)
      unfold P1.Aligned
      rw [hdn, hdp]; omega
    · exact nodeAt_aligned (hTm.npl c hc) (by simp [layout.node.DEBUG_TCBS]) (by simp [layout.node.DEBUG_TCBS])
  have hkd : ∀ kd, newKind n us = some kd → 2 ^ kd.bits = k := fun kd h => by rw [newKind_bits h, hk]
  have hwp : WinPlaced A0 k w n us := by
    refine ⟨fun kd h => ?_, hfitW, hpos, hn.2⟩
    rw [hkd kd h]
    exact ⟨hAk, Nat.mod_self _⟩
  have hh0 : L.mem s1 (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
      L.mem s1 (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS) ∈ Heap.tcbs H :=
    fun hne => (hTm.dh _ J.kern.cs0).resolve_left hne
  obtain ⟨H', Ac', hb', hkeep, hshape, hnew, hdead'⟩ := creation_step (n := n) (us := us) hb1
    (fun kd h => (hkd kd h).le) hdrop hRON hdbg hwp hW hP hSC J.kern.cs0 hh0 (fun h => absurd h hT) hfitW
    (fun _ hz w0 hw0 h1 h2 => Or.inl ((hWZ hz w0 hw0 h1 h2).resolve_right (fun h => hT h.1))) (fun h => absurd h hn1)
  have hout : HOut H H' A0 (A0 + w * k) A0 k w (newKind n us) :=
    hOut_of_steps hk1 le_rfl le_rfl (Or.inl ⟨rfl, rfl, rfl⟩) hkeep hshape hnew
  -- deadness kept by the restart
  have hidle1 := J.idleW_keep hS1 hid1 hisc1
  have hdk : ∀ q kd, H q = some kd → DeadP (L := L) H s q → DeadQ st H s1 q := by
    intro q kd hq hd
    have hqc : q ≠ L.curW s := by
      intro e; subst e
      exact P1.runnable_ne_inactive hrun (hd.1 J.kern.curH).1
    exact deadQ_keep J.kern.heap hq hd (restart_keeps_obj J.kern.heap hfr hq J.kern.curH hqc
      (J.kern.hnd q kd hq _ J.kern.cpuCs) J.kern.nodeFit) hidle1.1 (fun hqt e => hact q hqt e.symm)
  have hnewQ : ∀ q, NewAt A0 k w q → newKind n us ≠ none → NewQ A0 k w cj q := by
    rintro q ⟨j, hj, hq⟩ hK
    exact ⟨j, hj, hq, hcjU hK j hj⟩
  -- jc6e: a surviving dead TCB lies off the window; the restart and the creation keep its `DeadX` words
  have hTm0 : TimerOK st H.tcbs Cs s := J.blk.2.2.1.2.2.tm
  have hdx' : ∀ q ∈ D, ¬ NewQ A0 k w cj q → H' q = H q → Sched.DeadX (L := L) H Cs s q →
      Sched.DeadX (L := L) H Cs s' q := by
    intro q hqD hnq e hd
    have hqc : q ≠ L.curW s := by
      intro e'; subst e'
      exact P1.runnable_ne_inactive hrun ((J.jcov.dead _ hqD).1 J.kern.curH).1
    have hd1 : Sched.DeadX (L := L) H Cs s1 q :=
      deadX_restart (c := L.curW s) J.kern.heap hfr hks1 J.kern.curH hqc J.kern.hnd J.kern.cpuCs J.kern.nodeFit
        (fun c hc => by
          rw [nodeAt_val (hTm0.npl c hc) (by simp [layout.node.DEBUG_TCBS] : layout.node.DEBUG_TCBS.val < 4288)]
          simp [layout.node.DEBUG_TCBS])
        (fun c hc => nodeAt_aligned (hTm0.npl c hc) (by simp [layout.node.DEBUG_TCBS]) (by simp [layout.node.DEBUG_TCBS]))
        hd
    refine deadX_of_frame J.kern.heap hW (fun hq v hv => ?_) (fun hq c hc => Or.inl ?_)
      (fun c hc => nodeAt_aligned (hTm.npl c hc) (by simp [layout.node.DEBUG_TCBS]) (by simp [layout.node.DEBUG_TCBS]))
      hd1
    · have hq' : H' q = some .tcb := e.trans hq
      have hm : q.val + 4096 ≤ A0 ∨ A0 + w * k ≤ q.val := by
        rcases hshape q .tcb hq' with ⟨-, hm⟩ | ⟨hna', hk''⟩
        · unfold MeetsR at hm
          have b12 : (2 : Nat) ^ HKind.tcb.bits = 4096 := rfl
          omega
        · exact absurd (hnewQ q hna' (by rw [hk'']; simp)) hnq
      have hdp : (P1.dpA q).val = q.val + 3584 := tcb_word J.kern.heap hq (by simp)
      have htd : (P1.tdA q).val = q.val + 3528 := tcb_word J.kern.heap hq (by simp)
      rcases hv with (⟨hT', -⟩ | hsl) | ⟨-, hv1, hv2⟩
      · exact absurd hT' hT
      · exact ⟨((hsoff v hsl).1 q hq).2, slot_word_ne_tw hJP hsl hq (K := 3528#u64) (by simp) (by simp)⟩
      · exact ⟨fun e' => by rw [e', hdp] at hv1 hv2; omega, fun e' => by rw [e', htd] at hv1 hv2; omega⟩
    · intro v hv e'
      rcases hv with (⟨hT', -⟩ | hsl) | ⟨-, hv1, hv2⟩
      · exact absurd hT' hT
      · have hv0 := nodeAt_val (hTm.npl c hc) (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
        have := (hsoff v hsl).2 c hc
        rw [e', hv0] at this
        have : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
        omega
      · have hv0 := nodeAt_val (hTm.npl c hc) (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
        have h4 : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
        have hc2 := hk2 c hc
        have hnc := hnb c
        subst e'
        rw [hv0, hnc] at hv1 hv2
        rcases hc2 with h | h <;> omega
  refine ⟨H', Ac', hb', hout, J.jcov.retype hE (fun q kd hq => ?_) (fun q hqD hnq e hd => ?_) (hW.1.trans hks1)
    hidl hdx' ⟨p, sb, fi, hcv⟩⟩
  · rcases hshape q kd hq with ⟨h1, hm⟩ | ⟨hna', hk'⟩
    · refine Or.inl ⟨h1, ?_⟩
      rintro ⟨j, hj, hv, -⟩
      apply hm
      unfold MeetsR
      have h1' : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at h1'
      have := Nat.one_le_two_pow (n := kd.bits)
      omega
    · exact Or.inr ⟨hnewQ q hna' (by rw [hk']; simp), (hkd kd hk').le⟩
  · cases hHq : H q with
    | none => exact DeadP.none (e.trans hHq)
    | some kd =>
      have hq' : H' q = some kd := e.trans hHq
      rcases hshape q kd hq' with ⟨h1, -⟩ | ⟨hna', hk''⟩
      · exact hdead' q (hq'.trans h1.symm) (hdk q kd hHq hd)
      · exact absurd (hnewQ q hna' (by rw [hk'']; simp)) hnq


/-- `JAtZ.create_noresetW` for a type other than PML4 (its frame slot words only). -/
theorem JAtZ.create_noresetG {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    {s1 : S} {σ1 : Fl4Spec.State Unit} {Ac1 : Set U64} {Lst1 : U64 → List U64} {D1 : Set U64}
    (J1 : JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 s1 ar σ1)
    (hs1 : sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s1)
    (hct1 : σ1.curThread = σ.curThread) (hcsc1 : σ1.curSc = σ.curSc) (hid1 : σ1.idleThread = σ.idleThread)
    (hisc1 : σ1.idleSc = σ.idleSc) (hns1 : ∀ u, σ1.schedulerAction = .switchThread u → False)
    (hRU : RegionUnrefAt (L := L) H Cs D s)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {s' : S} {th' : TypedHeap} {G' : MdbGhost} {A0 k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
    (hE : RetExp Z.th th' (L.mem s) (L.mem s') Z.G G' A0 k w dslot cj (cslotAddr (pp.bv, idx)))
    {n us : Nat} (hcjU : newKind n us ≠ none → ∀ j, j < w → isUt (cj j) = false)
    (hn : n ≠ 1 ∧ (n = 5 → 7 ≤ us)) (hk : k = 2 ^ zOf n us) (hAk : A0 % k = 0)
    {T pml4 : Prop} (hT : ¬ T) (_hP4 : ¬ pml4)
    (hW : WFrame (L := L) s1 s' (fun v => ((T ∧ TcbLoopW Z.th A0 w (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS)
      (L.mem s1 (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan Z.th v) ∨
      (pml4 ∧ A0 ≤ v.val ∧ v.val < A0 + w * k)))
    (hWZ : WinZero (L.mem s') A0 k w T) (hidl : IdleKeep (L := L) s s') :
    ∃ (H' : Heap) (Ac' : Set U64),
      BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H')
        (Heap.ntfns H') (Heap.scBits H') Ac' s' ∧
      HOut H H' A0 (A0 + w * k) A0 k w (newKind n us) ∧
      JCovD (L := L) th' H' G' {q | q ∈ D ∧ ¬ NewQ A0 k w cj q} Cs s' :=
  J.create_noresetW hni J1 hs1 hct1 hcsc1 hid1 hisc1 hns1 hRU hpp hidx hcap hE hcjU hn hk hAk hT hW (fun _ => hWZ) hidl

/-- `JAtZ.create_noresetG` with no new untyped cap. -/
theorem JAtZ.create_noreset {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    {s1 : S} {σ1 : Fl4Spec.State Unit} {Ac1 : Set U64} {Lst1 : U64 → List U64} {D1 : Set U64}
    (J1 : JAtZ (L := L) arI AR Z H Cs Ac1 Lst1 D1 s1 ar σ1)
    (hs1 : sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s1)
    (hct1 : σ1.curThread = σ.curThread) (hcsc1 : σ1.curSc = σ.curSc) (hid1 : σ1.idleThread = σ.idleThread)
    (hisc1 : σ1.idleSc = σ.idleSc) (hns1 : ∀ u, σ1.schedulerAction = .switchThread u → False)
    (hRU : RegionUnrefAt (L := L) H Cs D s)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {s' : S} {th' : TypedHeap} {G' : MdbGhost} {A0 k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
    (hE : RetExp Z.th th' (L.mem s) (L.mem s') Z.G G' A0 k w dslot cj (cslotAddr (pp.bv, idx)))
    (hcjU : ∀ j, j < w → isUt (cj j) = false)
    {n us : Nat} (hn : n ≠ 1 ∧ (n = 5 → 7 ≤ us)) (hk : k = 2 ^ zOf n us) (hAk : A0 % k = 0)
    {T pml4 : Prop} (hT : ¬ T) (hP4 : ¬ pml4)
    (hW : WFrame (L := L) s1 s' (fun v => ((T ∧ TcbLoopW Z.th A0 w (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS)
      (L.mem s1 (L.nodeAt s1 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan Z.th v) ∨
      (pml4 ∧ A0 ≤ v.val ∧ v.val < A0 + w * k)))
    (hWZ : WinZero (L.mem s') A0 k w T) (hidl : IdleKeep (L := L) s s') :
    ∃ (H' : Heap) (Ac' : Set U64),
      BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H')
        (Heap.ntfns H') (Heap.scBits H') Ac' s' ∧
      HOut H H' A0 (A0 + w * k) A0 k w (newKind n us) ∧
      JCovD (L := L) th' H' G' {q | q ∈ D ∧ ¬ NewQ A0 k w cj q} Cs s'  := by
  exact J.create_noresetG hni J1 hs1 hct1 hcsc1 hid1 hisc1 hns1 hRU hpp hidx hcap hE
    (fun (_ : newKind n us ≠ none) => hcjU) hn hk hAk hT hP4 hW hWZ hidl

end

end

end Fl4Proofs.P3

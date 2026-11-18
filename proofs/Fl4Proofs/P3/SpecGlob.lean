/-
P3 (DESIGN.md §9), CSpace: **spec-only invariants carried by the deletion
loop** (`SpecGlob`), spec side only.

* `SpecGlob σ`: the IRQ node's slots hold null or notification caps (l4v
  `valid_irq_node` with the IRQ handler slots' contents; IntInv's
  `SpecIrqNode`, `SpecGlob.irqNode`), and no cap but a frame cap names an
  IRQ node CNode (l4v `valid_global_refs`, the IRQ node in `global_refs`;
  frame caps left out: a device frame's base is a physical address that
  #34's device untypeds may place anywhere).
* `SlotK σ σ'`: every cap of `σ'` is null or the cap of `σ` in the same
  slot (`capOpt`, CnodeOther); `NSK m`: every outcome of `m` is
  `SlotK`-related to its start. With the IRQ node kept (`GK`,
  SpecGlobFK) it keeps `SpecGlob` (`SpecGlob.of_slotK`).
* `NSK` of the deletion's steps: `finalise_cap` (`nsk_finaliseCap`: the
  object finalisations keep the caps, SpecFinFrames' `NKC`; the arch one
  `archF`; an IRQ handler's `cap_delete_one` of its IRQ node slot empties
  it), `empty_slot` with a null cleanup (`nsk_emptySlot_null`).
* The slot edits that write caps: `set_cap` of a zombie over a cap naming
  the same objects (`SpecGlob.setCap`, the slot not an IRQ node slot) and
  `cap_swap_for_delete` of two slots off the IRQ node (`SpecGlob.swap`:
  caps only move).
* Steps keeping the heap, the IRQ node and the idle thread
  (`SpecGlob.of_eq`: the preemption point, `post_cap_deletion`'s
  kernel-state steps).
-/
import Fl4Proofs.P3.SpecGlobFK
import Fl4Proofs.P3.SpecFinFrames
import Fl4Proofs.P3.XTopJointFinVsSpec
import Fl4Proofs.P3.IntInv
import Fl4Proofs.P3.DelAbs
import Fl4Proofs.P3.FinDefs
import Fl4Proofs.P3.CnodeOther
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Fl4Spec Classical Fl4Proofs.P3.Vs

noncomputable section

/-- A frame cap (its base a physical address, outside `SpecGlob.ref`). -/
def IsPageCap : Cap → Prop
  | .archObjectCap (.pageCap ..) => True
  | _ => False

/-- No IRQ node CNode among the objects a cap names. -/
def NodeFree (σ : State Unit) (a : Cap) : Prop := ∀ irq, σ.interruptIrqNode irq ∉ objRefs a

/-- **The spec-only invariants of the deletion loop** (module docstring). -/
structure SpecGlob (σ : State Unit) : Prop where
  /-- The IRQ node's slots hold null or notification caps. -/
  irq : ∀ irq a, capOpt (σ.kheap (σ.interruptIrqNode irq)) [] = some a →
    a = .nullCap ∨ ∃ r b rs, a = .notificationCap r b rs
  /-- No cap but a frame cap names an IRQ node CNode. -/
  ref : ∀ p cref a, capOpt (σ.kheap p) cref = some a → ¬ IsPageCap a → NodeFree σ a

/-- **IntInv's `SpecIrqNode` from `SpecGlob`.** -/
theorem SpecGlob.irqNode {σ : State Unit} (h : SpecGlob σ) : SpecIrqNode σ := by
  intro irq a hg
  have e := (getCap_set_iff σ _ _ a).1 (congrArg Prod.fst hg)
  exact h.irq irq a e

/-! ## `SlotK`: caps only emptied -/

/-- Every cap of `σ'` is null or the one of `σ` in the same slot. -/
def SlotK (σ σ' : State Unit) : Prop :=
  ∀ p cref a, capOpt (σ'.kheap p) cref = some a → a = .nullCap ∨ capOpt (σ.kheap p) cref = some a

theorem SlotK.refl (σ : State Unit) : SlotK σ σ := fun _ _ _ h => Or.inr h

theorem SlotK.trans {σ1 σ2 σ3 : State Unit} (h1 : SlotK σ1 σ2) (h2 : SlotK σ2 σ3) : SlotK σ1 σ3 := by
  intro p cref a h
  rcases h2 p cref a h with e | h'
  · exact Or.inl e
  · exact h1 p cref a h'

theorem SlotK.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : SlotK σ σ' := by
  intro p cref a ha; rw [h] at ha; exact Or.inr ha

/-- **`SpecGlob` across a step emptying caps only, the IRQ node kept.** -/
theorem SpecGlob.of_slotK {σ σ' : State Unit} (h : SpecGlob σ) (hk : SlotK σ σ')
    (hn : σ'.interruptIrqNode = σ.interruptIrqNode) : SpecGlob σ' := by
  refine ⟨fun irq a ha => ?_, fun p cref a ha hp => ?_⟩
  · rw [hn] at ha
    rcases hk _ _ _ ha with e | h'
    · exact Or.inl e
    · exact h.irq irq a h'
  · rcases hk _ _ _ ha with e | h'
    · subst e; intro irq; simp [objRefs]
    · intro irq; rw [hn]; exact h.ref p cref a h' hp irq

/-- `SpecGlob` across a step keeping the heap and the IRQ node. -/
theorem SpecGlob.of_eq {σ σ' : State Unit} (h : SpecGlob σ) (hk : σ'.kheap = σ.kheap)
    (hn : σ'.interruptIrqNode = σ.interruptIrqNode) : SpecGlob σ' :=
  h.of_slotK (SlotK.of_kheap hk) hn

/-- `CKeep` (SpecCaps: CNodes and TCB caps kept, none created) empties no
cap. -/
theorem SlotK.of_ckeep {σ σ' : State Unit} (hc : CKeep σ σ') : SlotK σ σ' := by
  intro p cref a h
  right
  cases hk' : σ'.kheap p with
  | none => rw [hk'] at h; simp [capOpt] at h
  | some o =>
    rw [hk'] at h
    cases o with
    | cnode r cs =>
      simp only [capOpt] at h
      split_ifs at h with hw
      obtain ⟨cs0, h0, hw0⟩ := (hc.ks p).1 r cs hk' hw
      have e := hc.cn p r cs0 h0 hw0
      rw [hk'] at e
      cases e
      rw [h0]; simp only [capOpt, if_pos hw0]; exact h
    | tcb t =>
      obtain ⟨t0, h0⟩ := (hc.ks p).2.1 t hk'
      obtain ⟨t', h', e⟩ := hc.tc p t0 h0
      rw [hk'] at h'
      cases h'
      rw [h0]; simp only [capOpt] at h ⊢; rw [← e]; exact h
    | _ => simp [capOpt] at h

/-- An arch step (`archF` kept: the objects but arch ones) empties no cap. -/
theorem SlotK.of_archF {σ σ' : State Unit} (h : archF σ' = archF σ) : SlotK σ σ' := by
  intro p cref a ha
  right
  rcases (ArFr.of_eq h).kh p with e | ⟨x, x', -, e', -⟩
  · rw [← e]; exact ha
  · rw [e'] at ha; simp [capOpt] at ha

/-! ## `NSK`: every outcome empties caps only -/

/-- Every outcome of `m` is `SlotK`-related to its start. -/
def NSK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → SlotK σ x.2

theorem nsk_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NSK m)
    (hf : ∀ a, NSK (f a)) : NSK (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem nsk_bind' {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NSK m)
    (hf : ∀ a, NSK (f a)) : NSK (NonDet.bind m f) := nsk_bind hm hf

theorem nsk_pure {α : Type} (a : α) : NSK (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SlotK.refl σ

theorem nsk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : NSK m1)
    (h2 : NSK m2) : NSK (if P then m1 else m2) := by
  split <;> assumption

theorem nsk_of_nkc {α : Type} {m : NonDet (State Unit) α} (h : NKC m) : NSK m :=
  fun σ x hx => SlotK.of_ckeep (h σ x hx)

theorem nsk_of_kh {α : Type} {m : NonDet (State Unit) α} (h : FK (fun σ : State Unit => σ.kheap) m) : NSK m :=
  fun σ x hx => SlotK.of_kheap (h σ x hx)

/-! ## `set_cap` -/

/-- An object's caps after `set_cap` of a written cap at index `r`. -/
theorem capOpt_cnode_set {sz : Nat} {cs : CnodeContents} {r : CnodeIndex} (c : Cap)
    (hc : r ∈ dom cs ∧ wellFormedCnodeN sz cs) (cref : CnodeIndex) :
    capOpt (some (.cnode sz (Function.update cs r (some c)))) cref =
      Function.update (capOpt (some (.cnode sz cs))) r (some c) cref := by
  have hw' : wellFormedCnodeN sz (Function.update cs r (some c)) := by
    unfold wellFormedCnodeN at hc ⊢
    rw [← hc.2]
    ext y
    simp only [dom, Set.mem_ofPred_eq, Function.update_apply]
    by_cases e : y = r
    · subst e; simp only [if_true]; exact ⟨fun _ => hc.1, fun _ => by simp⟩
    · simp only [e, if_false]
  have e1 : capOpt (some (.cnode sz (Function.update cs r (some c)))) = Function.update cs r (some c) := by
    funext x; simp only [capOpt, if_pos hw']
  have e2 : capOpt (some (.cnode sz cs)) = cs := by
    funext x; simp only [capOpt, if_pos hc.2]
  rw [e1, e2]

theorem capOpt_tcb_set (t : Tcb) {i : Nat} (hi : i < tcbSlots) (c : Cap) (cref : CnodeIndex) :
    capOpt (some (.tcb (tcbSet t i c))) cref = Function.update (capOpt (some (.tcb t))) (tcbCnodeIndex i) (some c) cref := by
  have e1 : capOpt (some (.tcb (tcbSet t i c))) = tcbCnodeMap (tcbSet t i c) := by funext x; rfl
  have e2 : capOpt (some (.tcb t)) = tcbCnodeMap t := by funext x; rfl
  rw [e1, e2, tcbCnodeMap_set t hi c]

/-- **The caps after `set_cap`**: the written one at its slot, the old ones
elsewhere. -/
theorem setCap_capOpt {c : Cap} {o : ObjRef} {r : CnodeIndex} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setCap (Z := Unit) c (o, r) σ).1) :
    ∀ p cref a, capOpt (x.2.kheap p) cref = some a →
      (p = o ∧ cref = r ∧ a = c) ∨ ((p ≠ o ∨ cref ≠ r) ∧ capOpt (σ.kheap p) cref = some a) := by
  unfold setCap at hx
  dsimp only at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap o = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap o with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  have key : ∀ k', (∀ cref, capOpt (some k') cref = Function.update (capOpt (some k)) r (some c) cref) →
      x ∈ (setObject (Z := Unit) o k' σ).1 → ∀ p cref a, capOpt (x.2.kheap p) cref = some a →
      (p = o ∧ cref = r ∧ a = c) ∨ ((p ≠ o ∨ cref ≠ r) ∧ capOpt (σ.kheap p) cref = some a) := by
    intro k' hk' hx' p cref a h
    rw [Ipc.setObject_out hx'] at h
    by_cases hp : p = o
    · subst hp
      simp only [Function.update_self] at h
      rw [hk'] at h
      by_cases hr : cref = r
      · subst hr; rw [Function.update_self] at h
        exact Or.inl ⟨rfl, rfl, (Option.some.inj h).symm⟩
      · rw [Function.update_of_ne hr, ← hk] at h
        exact Or.inr ⟨Or.inr hr, h⟩
    · simp only [Function.update_of_ne hp] at h
      exact Or.inr ⟨Or.inl hp, h⟩
  have pb : ∀ o', x ∈ ((pure o' >>= fun obj' => setObject (Z := Unit) o obj') σ).1 →
      x ∈ (setObject (Z := Unit) o o' σ).1 := by
    intro o' hx'; obtain ⟨z, hz, hx'⟩ := hx'; rw [Set.mem_singleton_iff.1 hz] at hx'; exact hx'
  have fb : ∀ (f : KernelObject → NonDet (State Unit) Unit), x ∈ ((NonDet.fail >>= f) σ).1 → False := by
    intro f hx'; obtain ⟨z, hz, -⟩ := hx'; exact hz
  cases k with
  | cnode sz cs =>
    dsimp only at hx
    split at hx
    · rename_i hc
      exact key _ (capOpt_cnode_set c hc) (pb _ hx)
    · exact (fb _ hx).elim
  | tcb t =>
    dsimp only at hx
    repeat' split at hx
    all_goals first
      | exact (fb _ hx).elim
      | (rename_i h; subst h
         first
          | exact key _ (capOpt_tcb_set t (i := 0) (by decide) c) (pb _ hx)
          | exact key _ (capOpt_tcb_set t (i := 1) (by decide) c) (pb _ hx)
          | exact key _ (capOpt_tcb_set t (i := 2) (by decide) c) (pb _ hx)
          | exact key _ (capOpt_tcb_set t (i := 3) (by decide) c) (pb _ hx)
          | exact key _ (capOpt_tcb_set t (i := 4) (by decide) c) (pb _ hx)
          | exact key _ (capOpt_tcb_set t (i := 5) (by decide) c) (pb _ hx))
  | _ => dsimp only at hx; exact (fb _ hx).elim

theorem nsk_setCap_null (sl : CslotPtr) : NSK (setCap (Z := Unit) .nullCap sl) := by
  obtain ⟨o, r⟩ := sl
  intro σ x hx p cref a ha
  rcases setCap_capOpt hx p cref a ha with ⟨-, -, e⟩ | ⟨-, h⟩
  · exact Or.inl e
  · exact Or.inr h

/-! ## The deletion's steps -/

theorem nsk_emptySlot_null (sl : CslotPtr) : NSK (emptySlot (Z := Unit) sl .nullCap) := by
  unfold emptySlot
  refine nsk_bind (nsk_of_nkc (nkc_getCap _)) (fun cap => ?_)
  refine nsk_ite _ (nsk_pure _) ?_
  refine nsk_bind (nsk_of_kh (dk_gets _)) (fun _ => nsk_bind (nsk_of_kh (dk_gets _)) (fun _ =>
    nsk_bind (nsk_pure _) (fun _ => nsk_bind (nsk_of_kh (by unfold setCdt; kh_auto)) (fun _ =>
      nsk_bind (nsk_of_kh (kh_doExtendedOp _)) (fun _ => nsk_bind (nsk_of_kh (by unfold setOriginal; kh_auto))
        (fun _ => nsk_bind (nsk_setCap_null _) (fun _ => ?_)))))))
  simp only [postCapDeletion]
  exact nsk_pure _

theorem nkc_fastFinalise (c : Cap) (b : Bool) : NKC (fastFinalise (Z := Unit) c b) := by
  cases c with
  | nullCap => simp only [fastFinalise]; exact nkc_pure _
  | replyCap r R =>
    simp only [fastFinalise]
    refine nkc_when (nkc_bind (nkc_liftM _ (nkc_getSimpleKo _ _)) (fun o => ?_))
    cases o with
    | none => exact nkc_pure _
    | some tp =>
      dsimp only
      refine nkc_bind (nkc_threadGet _ _) (fun st => ?_)
      split
      · exact nkc_replyRemove _ _
      · exact nkc_cancelIpc _
  | endpointCap r b R => simp only [fastFinalise]; exact nkc_when (nkc_cancelAllIpc r)
  | notificationCap r b R =>
    simp only [fastFinalise]
    exact nkc_when (nkc_bind (nkc_schedContextMaybeUnbindNtfn r) (fun _ =>
      nkc_bind (nkc_unbindMaybeNotification r) (fun _ => nkc_cancelAllSignals r)))
  | _ => simp only [fastFinalise]; exact nkc_fail

theorem nsk_capDeleteOne (sl : CslotPtr) : NSK (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne isFinalCap
  refine nsk_bind (nsk_of_nkc (nkc_getCap _)) (fun cap => ?_)
  unfold NonDet.unless
  refine nsk_ite _ (nsk_pure _) ?_
  exact nsk_bind (nsk_of_kh (dk_gets _)) (fun fin => nsk_bind (nsk_of_nkc (nkc_fastFinalise cap fin))
    (fun _ => nsk_emptySlot_null sl))

theorem nsk_deletingIrqHandler (irq : Irq) : NSK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler getIrqSlot
  exact nsk_bind (nsk_of_kh (dk_gets _)) (fun sl => nsk_capDeleteOne sl)

/-- **Every outcome of `finalise_cap` empties caps only.** -/
theorem nsk_finaliseCap (c : Cap) (b : Bool) : NSK (finaliseCap (Z := Unit) c b) := by
  cases c with
  | replyCap r R => exact nsk_of_nkc (finReply_nkc r R b)
  | endpointCap r bd R => exact nsk_of_nkc (finEp_nkc r bd R b)
  | notificationCap r bd R => exact nsk_of_nkc (finNtfn_nkc r bd R b)
  | threadCap r => exact nsk_of_nkc (finThread_nkc r b)
  | schedContextCap p n => exact nsk_of_nkc (finSc_nkc p n b)
  | irqHandlerCap irq =>
    simp only [finaliseCap]
    exact nsk_ite _ (nsk_bind (nsk_deletingIrqHandler irq) fun _ => nsk_pure _) (nsk_pure _)
  | archObjectCap a =>
    intro σ x hx
    exact SlotK.of_archF (fa_finaliseCap_arch a b σ x hx)
  | zombie r bt n =>
    simp only [finaliseCap]
    exact nsk_bind (nsk_of_kh (dk_assert _)) (fun _ => nsk_pure _)
  | _ => simp only [finaliseCap]; exact nsk_pure _

/-- **`finalise_cap` keeps `SpecGlob`.** -/
theorem SpecGlob.fin {c : Cap} {b : Bool} {σ : State Unit} {x : (Cap × Cap) × State Unit}
    (hx : x ∈ (finaliseCap (Z := Unit) c b σ).1) (h : SpecGlob σ) : SpecGlob x.2 :=
  h.of_slotK (nsk_finaliseCap c b σ x hx) ((gk_finaliseCap c b).inode hx)

/-- **`empty_slot` with a null cleanup keeps `SpecGlob`.** -/
theorem SpecGlob.empty {sl : CslotPtr} {σ σ' : State Unit}
    (hx : ((), σ') ∈ (emptySlot (Z := Unit) sl .nullCap σ).1) (h : SpecGlob σ) : SpecGlob σ' :=
  h.of_slotK (nsk_emptySlot_null sl σ _ hx) ((gk_emptySlot' sl .nullCap).inode hx)

/-- **The preemption point keeps `SpecGlob`** (it writes no object). -/
theorem SpecGlob.pp {σ σ' : State Unit} {r : Except Unit Unit}
    (hx : (r, σ') ∈ ((preemptionPoint (Z := Unit)).run σ).1) (h : SpecGlob σ) : SpecGlob σ' := by
  have hk : FKE (fun σ : State Unit => σ.kheap) (preemptionPoint (Z := Unit)) := by
    unfold preemptionPoint orChoiceE updateTimeStamp getScActive; kh_auto
  exact h.of_eq (hk σ _ hx) (GK.inode (show GK (ExceptT.run (preemptionPoint (Z := Unit))) from gke_preemptionPoint') hx)

/-- **`set_thread_state` keeps `SpecGlob`** (the caller's restart). -/
theorem SpecGlob.sts {t : ObjRef} {ts : ThreadState} {σ σ' : State Unit}
    (hx : ((), σ') ∈ (setThreadState (Z := Unit) t ts σ).1) (h : SpecGlob σ) : SpecGlob σ' :=
  h.of_slotK (SlotK.of_ckeep (nkc_setThreadState t ts σ _ hx)) ((gk_setThreadState' t ts).inode hx)

/-! ## The slot edits writing caps -/

/-- **A cap written over one naming the same objects, off the IRQ node,
keeps `SpecGlob`** (the deletion's zombie). -/
theorem SpecGlob.setCap {c a0 : Cap} {sl : CslotPtr} {σ σ' : State Unit}
    (hx : ((), σ') ∈ (Fl4Spec.setCap (Z := Unit) c sl σ).1) (h : SpecGlob σ)
    (ha0 : capOpt (σ.kheap sl.1) sl.2 = some a0) (hrefs : objRefs c = objRefs a0)
    (hp : ¬ IsPageCap c) (hp0 : ¬ IsPageCap a0) (hnode : ∀ irq, sl ≠ (σ.interruptIrqNode irq, [])) :
    SpecGlob σ' := by
  obtain ⟨o, r⟩ := sl
  have hn : σ'.interruptIrqNode = σ.interruptIrqNode := (gk_setCap c (o, r)).inode hx
  refine ⟨fun irq a ha => ?_, fun p cref a ha hpa => ?_⟩
  · rw [hn] at ha
    rcases setCap_capOpt hx _ _ _ ha with ⟨e1, e2, -⟩ | ⟨-, h'⟩
    · exact absurd (by rw [e1, e2]) (hnode irq)
    · exact h.irq irq a h'
  · intro irq
    rw [hn]
    rcases setCap_capOpt hx _ _ _ ha with ⟨-, -, rfl⟩ | ⟨-, h'⟩
    · rw [hrefs]; exact h.ref o r a0 ha0 hp0 irq
    · exact h.ref p cref a h' hpa irq

/-- The caps after `cap_swap`: each one of `σ`'s, at its slot off the two
swapped. -/
theorem capSwap_capOpt {c1 c2 : Cap} {s1 s2 : CslotPtr} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (capSwap (Z := Unit) c1 s1 c2 s2 σ).1) :
    ∀ p cref a, capOpt (x.2.kheap p) cref = some a →
      ((p, cref) = s2 ∧ a = c1) ∨ ((p, cref) = s1 ∧ a = c2) ∨
        ((p, cref) ≠ s1 ∧ (p, cref) ≠ s2 ∧ capOpt (σ.kheap p) cref = some a) := by
  obtain ⟨o1, r1⟩ := s1
  obtain ⟨o2, r2⟩ := s2
  unfold capSwap at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨y2, hy2, hx⟩ := hx
  have H : ∀ {β : Type} {m : NonDet (State Unit) β} (σ0 : State Unit) (z : β × State Unit),
      FK (fun σ : State Unit => σ.kheap) m → z ∈ (m σ0).1 → z.2.kheap = σ0.kheap :=
    fun σ0 z h hz => h σ0 z hz
  have hk : x.2.kheap = y2.2.kheap := H y2.2 x (by unfold setCdt setOriginal; kh_auto) hx
  intro p cref a ha
  rw [hk] at ha
  rcases setCap_capOpt hy2 _ _ _ ha with ⟨e1, e2, rfl⟩ | ⟨hne2, h2⟩
  · exact Or.inl ⟨by rw [e1, e2], rfl⟩
  rcases setCap_capOpt hy1 _ _ _ h2 with ⟨e1, e2, rfl⟩ | ⟨hne1, h1⟩
  · exact Or.inr (Or.inl ⟨by rw [e1, e2], rfl⟩)
  refine Or.inr (Or.inr ⟨fun e => ?_, fun e => ?_, h1⟩)
  · simp only [Prod.mk.injEq] at e; rcases hne1 with h | h <;> exact h (by first | exact e.1 | exact e.2)
  · simp only [Prod.mk.injEq] at e; rcases hne2 with h | h <;> exact h (by first | exact e.1 | exact e.2)

/-- **`cap_swap_for_delete` of two slots off the IRQ node keeps
`SpecGlob`**: caps only move. -/
theorem SpecGlob.swap {s1 s2 : CslotPtr} {c1 c2 : Cap} {σ σ' : State Unit}
    (hx : ((), σ') ∈ (capSwapForDelete (Z := Unit) s1 s2 σ).1) (h : SpecGlob σ)
    (hc1 : getCap (Z := Unit) s1 σ = ({(c1, σ)}, False)) (hc2 : getCap (Z := Unit) s2 σ = ({(c2, σ)}, False))
    (hn1 : ∀ irq, s1 ≠ (σ.interruptIrqNode irq, [])) (hn2 : ∀ irq, s2 ≠ (σ.interruptIrqNode irq, [])) :
    SpecGlob σ' := by
  have hn : σ'.interruptIrqNode = σ.interruptIrqNode := (gk_capSwapForDelete' s1 s2).inode hx
  have e1 := (getCap_set_iff σ s1.1 s1.2 c1).1 (congrArg Prod.fst hc1)
  have e2 := (getCap_set_iff σ s2.1 s2.2 c2).1 (congrArg Prod.fst hc2)
  unfold capSwapForDelete NonDet.when at hx
  split at hx
  · rw [nd_bind_single hc1, nd_bind_single hc2] at hx
    have hs := capSwap_capOpt hx
    refine ⟨fun irq a ha => ?_, fun p cref a ha hpa => ?_⟩
    · rw [hn] at ha
      rcases hs _ _ _ ha with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, h'⟩
      · exact absurd e.symm (hn2 irq)
      · exact absurd e.symm (hn1 irq)
      · exact h.irq irq a h'
    · intro irq; rw [hn]
      rcases hs _ _ _ ha with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, h'⟩
      · exact h.ref _ _ _ e1 hpa irq
      · exact h.ref _ _ _ e2 hpa irq
      · exact h.ref p cref a h' hpa irq
  · have e : σ' = σ := congrArg Prod.snd (Set.mem_singleton_iff.1 hx)
    rw [e]; exact h

end

end Fl4Proofs.P3

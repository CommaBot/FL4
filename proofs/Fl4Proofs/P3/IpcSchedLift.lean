/-
P3 (DESIGN.md §9), IPC: **scheduling-context steps lifted to `IRel`**.

A step that refines on `SchedRel` alone, writes FL4 words only in SC objects
of `C` (`SW`) and core `c`'s node, and changes the spec's state only in SC
objects of the same size and in fields no IPC relation reads (`ScOnlyK`),
keeps `IRel` (`sc_step_lift`): the merged IPC relation by its frame
(`scw_not_ifoot`: SC words are apart from every IPC word by `SchedRel`'s
`scOut` and `EpSchedApart.sc`; node words by `sfootI_not_ifoot`), `RelTopI`
by `RelTopB.frameS` (SC words hold no slot, `ScApart`, and are not the
domain words, `scOut`), and `EpSchedApart` by its monotonicity.

* `NKS`: every outcome of a spec operation is `ScOnlyK`-related to its
  start; `nks_refillUnblockCheck`, `nks_postpone`.
* `unblock_top` (`ReplyHyps.unblock`): the reply's inline sporadic test and
  `unblock_check` (ScUnblock's `unblock_check_refines`, its writes
  `unblock_check_scw`).
* `postpone_top` (`ReplyTmoHyps.postpone`): ScResume's `postpone_refines`
  with its writes at `SFootI` precision (`postpone_sfootI`), from the spec
  facts IRel lacks (`PostponeOK`: l4v `valid_sched`'s sorted release queue
  with SCs, the thread not released, `sym_refs` of its SC).
* `ReplyHyps.ofL`: `ReplyHyps` from `remove`, `PostponeOK`, the timeout
  transfer from a thread with an SC (`tmoXfer`) and the timeout handler's
  endpoint in `E` (`epE`).
-/
import Fl4Proofs.P3.IpcTimeout
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

/-! ## Spec steps that change only SC objects -/

section Spec
open Fl4Spec

/-- The spec state changed only in SC objects (same size) and in fields no
IPC or CSpace relation reads. -/
def ScOnlyK (σ σ' : State Unit) : Prop :=
  (∀ p, σ'.kheap p = σ.kheap p ∨
    ∃ y n y', σ.kheap p = some (.schedContext y n) ∧ σ'.kheap p = some (.schedContext y' n)) ∧
  σ'.machineState = σ.machineState ∧ σ'.cdt = σ.cdt ∧ σ'.isOriginalCap = σ.isOriginalCap ∧
  σ'.domainList = σ.domainList ∧ σ'.domainStartIndex = σ.domainStartIndex ∧
  (σ'.archState = σ.archState ∧ σ'.interruptStates = σ.interruptStates ∧
    σ'.interruptIrqNode = σ.interruptIrqNode ∧ σ'.curThread = σ.curThread)

theorem ScOnlyK.refl (σ : State Unit) : ScOnlyK σ σ :=
  ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ScOnlyK.trans {σ1 σ2 σ3 : State Unit} (h1 : ScOnlyK σ1 σ2) (h2 : ScOnlyK σ2 σ3) : ScOnlyK σ1 σ3 := by
  refine ⟨fun p => ?_, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2.2⟩
  rcases h1.1 p with e1 | ⟨y, n, y', a1, a2⟩ <;> rcases h2.1 p with e2 | ⟨z, m, z', b1, b2⟩
  · exact Or.inl (e2.trans e1)
  · rw [e1] at b1; exact Or.inr ⟨z, m, z', b1, b2⟩
  · rw [e2, a2]; exact Or.inr ⟨y, n, y', a1, rfl⟩
  · rw [a2] at b1; cases b1; exact Or.inr ⟨y, n, z', a1, b2⟩

/-- A non-SC object stays. -/
theorem ScOnlyK.fwd {σ σ' : State Unit} (h : ScOnlyK σ σ') {p : ObjRef} {o : KernelObject}
    (hp : σ.kheap p = some o) (ho : ∀ y n, o ≠ .schedContext y n) : σ'.kheap p = some o := by
  rcases h.1 p with e | ⟨y, n, y', a1, -⟩
  · rw [e, hp]
  · rw [hp] at a1; cases a1; exact absurd rfl (ho y n)

theorem ScOnlyK.bwd {σ σ' : State Unit} (h : ScOnlyK σ σ') {p : ObjRef} {o : KernelObject}
    (hp : σ'.kheap p = some o) (ho : ∀ y n, o ≠ .schedContext y n) : σ.kheap p = some o := by
  rcases h.1 p with e | ⟨y, n, y', -, a2⟩
  · rw [← e, hp]
  · rw [hp] at a2; cases a2; exact absurd rfl (ho y' n)

theorem ScOnlyK.ikview {σ σ' : State Unit} (h : ScOnlyK σ σ') : IKView σ σ' := by
  have mu : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory := by rw [h.2.1]
  refine ⟨⟨fun p x hp => h.fwd hp (by intros; nofun), fun p x hp => ⟨x, h.fwd hp (by intros; nofun), rfl, rfl, rfl⟩⟩,
    ⟨fun p x hp => h.fwd hp (by intros; nofun), fun p x hp => ⟨x, h.fwd hp (by intros; nofun), rfl⟩,
      fun p x hp => ⟨x, h.fwd hp (by intros; nofun), rfl, rfl, rfl, rfl, rfl⟩, mu⟩,
    fun p x hp => ⟨x, h.fwd hp (by intros; nofun), rfl⟩⟩

theorem ScOnlyK.ckeep {σ σ' : State Unit} (h : ScOnlyK σ σ') : CKeep σ σ' := by
  refine ⟨fun o => ⟨fun r cs hc hw => ⟨cs, h.bwd hc (by intros; nofun), hw⟩,
      fun t ht => ⟨t, h.bwd ht (by intros; nofun)⟩, fun hn => ?_⟩,
    fun o r cs hc _ => h.fwd hc (by intros; nofun),
    fun o t ht => ⟨t, h.fwd ht (by intros; nofun), rfl⟩, h.2.2.1, h.2.2.2.1⟩
  rcases h.1 o with e | ⟨y, n, y', a1, -⟩
  · rw [e, hn]
  · rw [hn] at a1; cases a1

theorem ScOnlyK.szKeep {σ σ' : State Unit} (h : ScOnlyK σ σ') : SzKeep σ σ' := by
  intro p x n hp
  rcases h.1 p with e | ⟨y, m, y', a1, a2⟩
  · exact ⟨x, by rw [← e]; exact hp⟩
  · rw [hp] at a2; cases a2; exact ⟨y, a1⟩

theorem ScOnlyK.vsKeep {σ σ' : State Unit} (h : ScOnlyK σ σ') : VsKeep σ σ' := by
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2,
    fun q ao hq => by rw [h.fwd hq (by intros; nofun), hq], h.szKeep,
    fun q x hq => ⟨x, by rw [h.fwd hq (by intros; nofun)], rfl⟩⟩

/-- Every outcome changes only SC objects. -/
def NKS {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → ScOnlyK σ x.2

theorem nks_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NKS m)
    (hf : ∀ a, NKS (f a)) : NKS (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem nks_pure {α : Type} (a : α) : NKS (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ScOnlyK.refl σ

theorem nks_pure' {α : Type} (a : α) : NKS (NonDet.pure a : NonDet (State Unit) α) := nks_pure a

theorem nks_gets {α : Type} (f : State Unit → α) : NKS (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ScOnlyK.refl σ

theorem nks_get : NKS (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ScOnlyK.refl σ

theorem nks_modify {f : State Unit → State Unit} (hf : ∀ σ, (f σ).kheap = σ.kheap ∧
    (f σ).machineState = σ.machineState ∧ (f σ).cdt = σ.cdt ∧ (f σ).isOriginalCap = σ.isOriginalCap ∧
    (f σ).domainList = σ.domainList ∧ (f σ).domainStartIndex = σ.domainStartIndex ∧
    ((f σ).archState = σ.archState ∧ (f σ).interruptStates = σ.interruptStates ∧
      (f σ).interruptIrqNode = σ.interruptIrqNode ∧ (f σ).curThread = σ.curThread)) : NKS (NonDet.modify f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hf σ
  exact ⟨fun p => Or.inl (by rw [h1]), h2, h3, h4, h5, h6, h7⟩

theorem nks_assert (P : Prop) : NKS (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact ScOnlyK.refl σ

theorem nks_fail {α : Type} : NKS (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem nks_assertOpt {α : Type} (o : Option α) : NKS (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact nks_fail
  · exact nks_pure' _

theorem nks_getsThe {α : Type} (f : State Unit → Option α) : NKS (NonDet.getsThe f) := by
  intro σ x hx
  exact nks_assertOpt (f σ) σ x hx

theorem nks_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : NKS m1) (h2 : NKS m2) :
    NKS (if P then m1 else m2) := by
  split <;> assumption

theorem nks_when {P : Prop} {inst : Decidable P} {m : NonDet (State Unit) Unit} (h : NKS m) :
    NKS (@NonDet.when _ P inst m) := by
  unfold NonDet.when; split; exact h; exact nks_pure' _

theorem nks_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, NKS (B r)) (r : α) : NKS (NonDet.whileLoop C B r) := by
  intro σ x hx
  change NonDet.WhileResults C B r σ x at hx
  induction hx with
  | done _ => exact ScOnlyK.refl _
  | step _ hb _ ih => exact (hB _ _ _ hb).trans ih

theorem nks_getObject (p : ObjRef) : NKS (getObject (Z := Unit) p) := nks_getsThe _

theorem nks_getSchedContext (p : ObjRef) : NKS (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext
  refine nks_bind (nks_getObject _) (fun o => ?_)
  cases o <;> first | exact nks_pure _ | exact nks_fail

theorem nks_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext) :
    NKS (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  intro σ x hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  cases k with
  | schedContext sc n =>
    simp only at hx
    unfold setSchedContext setObject at hx
    obtain ⟨z, hz, hx⟩ := hx
    obtain ⟨w, hw⟩ : ∃ w, σ.kheap p = some w ∧ z = (w, σ) := by
      unfold getObject NonDet.getsThe readObject at hz
      rw [hk] at hz ⊢; exact ⟨_, rfl, Set.mem_singleton_iff.1 hz⟩
    obtain ⟨hw, rfl⟩ := hw
    obtain ⟨u, hu, hx⟩ := hx
    obtain ⟨-, rfl⟩ := hu
    obtain ⟨v, hv, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hv] at hx
    rw [Set.mem_singleton_iff.1 hx]
    refine ⟨fun q => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    by_cases e : q = p
    · subst e
      exact Or.inr ⟨sc, n, f sc, hk, by simp⟩
    · exact Or.inl (by show Function.update σ.kheap p _ q = _; rw [Function.update_of_ne e])
  | _ => exact hx.elim

theorem nks_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, NKS (g a)) :
    ∀ xs : List α, NKS (NonDet.mapM g xs)
  | [] => nks_pure' _
  | a :: l => nks_bind (h a) (fun _ => nks_bind (nks_mapM h l) (fun _ => nks_pure' _))

macro "nks_step" : tactic => `(tactic| first
  | exact nks_pure _ | exact nks_pure' _ | exact nks_fail | exact nks_gets _ | exact nks_get
  | exact nks_assert _ | exact nks_assertOpt _ | exact nks_getObject _ | exact nks_getsThe _
  | exact nks_modify (fun σ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  | exact nks_getSchedContext _
  | exact nks_updateSchedContext _ _
  | (apply nks_when) | (apply nks_ite)
  | (apply nks_whileLoop; intro _)
  | (apply nks_mapM; intro _)
  | (refine nks_bind ?_ (fun _ => ?_))
  | split)

macro "nks_auto" : tactic => `(tactic| repeat nks_step)

theorem nks_refillUnblockCheck (p : ObjRef) : NKS (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck isRoundRobin getScRefillReady refillHeadOverlappingLoop mergeOverlappingRefills
    refillPopHead getRefillHead updateRefillHd
  nks_auto

theorem nks_postpone (p : ObjRef) : NKS (postpone (Z := Unit) p) := by
  unfold postpone getScObjRef tcbSchedAction threadGet getTcbQueue setTcbQueue tcbReleaseEnqueue readyTimesAppend
    orderedInsert
  nks_auto

end Spec


/-! ## FL4's SC and node words -/

section Foot
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **The words an SC step writes**: SC words (`SW`) and core `c`'s node. -/
def ScW (st : machine.Store S) [L : LawfulStore st] (C : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit)
    (b : U64) : Prop :=
  SW C σ b ∨ (L.nodeBase s c ≤ b.val ∧ b.val < L.nodeBase s c + 4288)

/-- A word of an SC object of `C`. -/
def ScObjW (C : Set U64) (σ : Fl4Spec.State Unit) (a : U64) : Prop :=
  ∃ sc ∈ C, ∃ x n, σ.kheap sc.bv = some (.schedContext x n) ∧ Sched.ScObj sc n a

/-- **No SC word is an IPC-buffer word.** -/
theorem scObjW_nobuf (hT : TcbPlaced T) {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {a : U64} (h : ScObjW C σ a) : NoBufW T a :=
  let ⟨sc, hsc, x, n, hk, hobj⟩ := h
  NoBufW.out hT (hS.scOut sc hsc x n hk a hobj).2.2.1

/-- An SC-step word is a node word or no IPC-buffer word. -/
theorem scW_nobuf (hT : TcbPlaced T) {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    {a : U64} (h : ScW st C c s σ a ∨ SFootI st T c s a) : NodeW (L.ksb s) c a ∨ NoBufW T a := by
  rcases h with (⟨sc, hsc, x, n, hk, hobj, -⟩ | ⟨g1, g2⟩) | hI
  · exact Or.inr (scObjW_nobuf hT hS ⟨sc, hsc, x, n, hk, hobj⟩)
  · have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
    exact Or.inl ⟨by omega, by omega⟩
  · exact sfootI_nobuf hT hI

/-- **No SC or node word is read by the merged IPC relation.** -/
theorem scw_not_ifoot (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hA : EpSchedApart st T C E R B c s σ) {b : U64} (h1 : ScW st C c s σ b)
    (h2 : IFoot N T E R B b) : False := by
  rcases h1 with ⟨sc, hsc, x, n, hk, hobj, -⟩ | ⟨g1, g2⟩
  · obtain ⟨hNW, -, hT, -⟩ := hS.scOut sc hsc x n hk b hobj
    have hE := hA.sc sc hsc x n hk b hobj
    rcases h2 with (⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hw, h⟩) | ⟨n', hn, n1, n2⟩ | ⟨t, ht, h⟩
    · exact hE (Or.inl ⟨e, he, h⟩)
    · exact hE (Or.inr (Or.inl ⟨r, hr, h⟩))
    · obtain ⟨h1, h2⟩ := h; unfold TOffN at h2; have := hT t ht; omega
    · unfold TL at h; have := hT t ht; omega
    · exact hE (Or.inr (Or.inr (Or.inr ⟨wp, hw, h⟩)))
    · exact hNW (Or.inl ⟨n', hn, n1, n2⟩)
    · have hv := congrArg UScalar.val h
      rw [scA_val (hP0.e.tcb t ht)] at hv
      have := hT t ht; omega
  · exact nodeRange_not_ifoot hP0 hS hA g1 g2 h2

/-- **The frame of `RelTopB`** for FL4 writing IPC words, node words and SC
words (no slot, `ScApart`; not the domain words, `hSD`). -/
theorem RelTopB.frameS {th : TypedHeap} {G : MdbGhost} {s s' : S} {σ σ' : Fl4Spec.State Unit} {W : U64 → Prop}
    (h : RelTopB (L := L) th G N T C E R B c s σ) (hW : WritesIn st s s' W)
    (hWI : ∀ a, W a → IWords N T E R B a ∨ NodeW (L.ksb s) c a ∨ ScObjW C σ a)
    (hSD : ∀ a, ScObjW C σ a → a.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ a.val)
    (hK : CKeep σ σ') (hdl : σ'.domainList = σ.domainList) (hds : σ'.domainStartIndex = σ.domainStartIndex)
    (hz : Sched.SzKeep σ σ') :
    RelTopB (L := L) th G N T C E R B c s' σ' := by
  obtain ⟨hPl, hCR, hFI, hD, hMO, hA, hSA⟩ := h
  obtain ⟨hksb, -, hmem⟩ := hW
  have hSS : SlotsSame th (L.mem s) (L.mem s') := by
    intro a ha
    have hf := ha.fit hPl
    have hal := ha.align hPl
    have w : ∀ k : U64, k.val < 32 → k.val % 8 = 0 → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := by
      intro k hk hk8
      have hv := wordOf_val (a := a) (k := k) (by omega)
      refine hmem _ (by unfold P1.Aligned; rw [hv]; omega) fun hw => ?_
      rcases hWI _ hw with hi | ⟨h1, h2⟩ | ⟨sc, hsc, x, n, hk', hobj⟩
      · exact hA.slot _ hi a ha (by rw [hv]; omega)
      · exact hA.node _ h1 h2 a ha (by rw [hv]; omega)
      · exact hSA sc hsc x n hk' _ hobj a ha ⟨by rw [hv]; omega, by rw [hv]; omega⟩
    refine ⟨?_, w 8#u64 (by decide) (by decide), w 16#u64 (by decide) (by decide), w 24#u64 (by decide) (by decide)⟩
    have := w 0#u64 (by decide) (by decide)
    rwa [wordOf_zero] at this
  have hDS : DomSame (L.mem s) (L.mem s') (L.ksb s) :=
    Vs.domSame_low hA.kfit hA.kal fun b hb h1 h2 => hmem b hb fun hw => by
      rcases hWI _ hw with hi | ⟨h3, -⟩ | ho
      · have := hA.dom _ hi; omega
      · omega
      · have := hSD _ ho; omega
  refine ⟨hPl, ⟨(hCR.1.of_ckeep hK).of_caps (fun x hx => hSS.capAt hx),
      SlotsValid.of_caps hCR.2.1 (fun y hy => hSS.capAt hy), hCR.2.2.1.of_same hSS,
      hCR.2.2.2.1.of_same hSS hK.cdt hK.orig, MdbInv.of_same hCR.2.2.1 hCR.2.2.2.2 hSS⟩,
    hFI.of_same hCR.2.2.1 hSS hK.ks, ?_, ?_, ?_, hSA.mono hz⟩
  · rw [hksb]; exact hD.of_same hDS hdl hds
  · rw [hksb]; exact MdbOKV.of_same hCR.2.2.1 hSS hMO
  · rw [hksb]; exact hA

end Foot

/-! ## The lift -/

section Lift
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **An SC step lifts to `IRel`**: FL4 writing SC and node words only, the
spec changing SC objects only (`ScOnlyK`), and `SchedRel` after. -/
theorem sc_step_lift (hP0 : IPlaced N T E R B) {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) (hW : WritesIn st s s' (fun b => ScW st C c s σ b ∨ SFootI st T c s b))
    (hK : ScOnlyK σ σ')
    (hS' : SchedRel st N T C c s' σ') : IRel st th cr N T C E R B c s' σ' := by
  obtain ⟨hR, ⟨⟨G, hB⟩, hV⟩, hS, hA⟩ := hX
  have hWI1 : ∀ a, (ScW st C c s σ a ∨ SFootI st T c s a) →
      IWords N T E R B a ∨ NodeW (L.ksb s) c a ∨ ScObjW C σ a := by
    intro a ha
    rcases ha with (⟨sc, hsc, x, n, hk, hobj, -⟩ | ⟨g1, g2⟩) | hI
    · exact Or.inr (Or.inr ⟨sc, hsc, x, n, hk, hobj⟩)
    · have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · rcases sfootI_iwords hP0.e.tcb hI with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hB' := hB.frameS hW hWI1 (fun a ⟨sc, hsc, x, n, hk, hobj⟩ => (hS.scOut sc hsc x n hk a hobj).2.2.2)
    hK.ckeep hK.2.2.2.2.1 hK.2.2.2.2.2.1 hK.szKeep
  refine ⟨hR.frame hP0 (fun a ha hf => hW.mem_eq ha (fun hw => hw.elim (fun hw => scw_not_ifoot hP0 hS hA hw hf)
      (fun hw => sfootI_not_ifoot hP0 hS hA hw hf))) hK.ikview,
    ⟨⟨G, hB'⟩, hV.frame hB.2.2.2.2.2.1 hB.1 hW (fun b hb => (hWI1 b hb).elim Or.inl
      (fun h => h.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h)))))
      (fun b hb => scW_nobuf hP0.e.tcb hS hb) hK.vsKeep
      hB'.2.1.2.2.1 hB'.2.2.2.2.1.2.2⟩, hS', hA.mono hW.1 hK.szKeep⟩

end Lift


/-! ## `unblock_check` and the reply's sporadic unblock -/

section Unblock
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `unblock_check` writes SC words and the `REPROGRAM` node word. -/
theorem unblock_check_scw {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {p : U64} (hp : p ∈ C) (ha : (L.rmax s p).val ≠ 0) :
    sporadic.unblock_check st s p ⦃ s' => WritesIn st s s' (ScW st C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs p hp
  have hN := hc.node
  have ho : (layout.node.REPROGRAM).val < 4288 := by simp [layout.node.REPROGRAM]
  have e : L.nodeA s layout.node.REPROGRAM = L.nodeAt s c layout.node.REPROGRAM := by
    unfold LawfulStore.nodeA; rw [hc.cur]
  have hal : Aligned (L.nodeA s layout.node.REPROGRAM) := by
    rw [e]; exact nodeAt_aligned hN ho (by simp [layout.node.REPROGRAM])
  have hout : Outside (L.nodeA s layout.node.REPROGRAM) p (n + Fl4Spec.minSchedContextBits) := by
    unfold Outside
    by_contra hin
    push_neg at hin
    have := (hS.scOut p hp x n hk _ ⟨hin.1, hin.2⟩).2.1
    rw [e, nodeAt_val hN ho] at this
    omega
  refine WP.spec_mono (sporadic.unblock_check.fr (hx.act ha).wf ⟨hal, hout⟩) fun s' hw => hw.mono fun b hb => ?_
  rcases hb with hb | hb
  · exact Or.inl (sw_ring hS hp hk hb)
  · rw [hb, e]; exact Or.inr ⟨by rw [nodeAt_val hN ho]; omega, by rw [nodeAt_val hN ho]; omega⟩

set_option maxHeartbeats 4000000 in
/-- **The reply's sporadic unblock on `IRel`** (`ReplyHyps.unblock`): the
SC's sporadic test and `unblock_check` (`unblock_check_refines`), lifted by
`sc_step_lift`. -/
theorem unblock_top (hP0 : IPlaced N T E R B) :
    ∀ s σ (t : U64) (x : Fl4Spec.Tcb) (k : S → Result (S × A)) (P : S × A → Prop),
    IRel st th cr N T C E R B c s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
    (∀ s' σ', (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ = ({((), σ')}, False) → IRel st th cr N T C E R B c s' σ' →
      (∀ p y, σ.kheap p = some (.tcb y) → σ'.kheap p = some (.tcb y)) → k s' ⦃ P ⦄) →
    (do
      let i2 ← obj.Tcb.sc st t s
      let b1 ← sporadic.sc_sporadic st s i2
      let s2 ←
        if b1
        then
          do
          let i3 ← obj.Sc.cpu st i2 s
          let i4 ← obj.node_get st s i3 layout.node.CUR_SC
          if i2 != i4
          then sporadic.unblock_check st s i2
          else ok s
        else ok s
      k s2) ⦃ P ⦄ := by
  intro s σ t x0 k P hX ht hkx hk
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  have hspec0 : (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ = (Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)
      (optRef (L.mem s (scA t)))) σ := by
    unfold Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hkt), hsct]
  have skip : (Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t)))) σ =
      ({((), σ)}, False) → k s ⦃ P ⦄ := fun h =>
    hk s σ (by rw [hspec0, h]) hX (fun _ _ h => h)
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
  step with sporadic.sc_sporadic.spec' as ⟨b, b_post⟩
  subst hi2
  by_cases h0 : L.mem s (scA t) = 0#u64
  · have hb : b = false := by rw [b_post]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact skip (by rw [h0, optRef_zero]; rfl)
  have hscC := hs.scMem t ht h0
  obtain ⟨y, n, hky, hy⟩ := hs.scs _ hscC
  have hsp : (y.scSporadic = true) ↔ L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64 := by
    rw [hy.sporadic]; simp
  have hif : ∀ (P : Prop) [Decidable P] (Q : Prop) [Decidable Q],
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
        (if y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc then
          Fl4Spec.refillUnblockCheck (L.mem s (scA t)).bv σ else ({((), σ)}, False)) := by
    intro _ _ _ _
    rw [Notif.optRef_ne h0]
    unfold Fl4Spec.ifSporadicCurScTestRefillUnblockCheck Fl4Spec.ifCondRefillUnblockCheck
    simp only [Fl4Spec.NonDet.maybeM]
    rw [nd_bind_one (getSchedContext_eq hky), nd_gets_bind, nd_pure_bind']
    simp only [Fl4Spec.NonDet.when]
    by_cases e : y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc
    · simp only [e, ne_eq, not_false_eq_true, forall_const, and_self, ↓reduceIte, Option.some.injEq,
        Bool.false_eq_true, IsEmpty.forall_iff]
    · simp only [ne_eq, forall_const, ↓reduceIte, Option.some.injEq]
      rw [ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e),
        ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e)]
      rfl
  have hif' := hif True True
  by_cases hsp' : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
  swap
  · have hb : b = false := by rw [b_post]; simp [h0]; simpa using hsp'
    simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact skip (by rw [hif', ite_f (fun h => hsp' (hsp.1 h.1))])
  have hb : b = true := by rw [b_post]; simp [h0, hsp']
  simp only [hb, ↓reduceIte]
  step with obj.Sc.cpu.spec as ⟨cpu, hcpu⟩
  have hcpu' : cpu = c := by rw [hcpu, Fl4Proofs.P3.Sched.scCoreA_eq]; exact hS.core _ hscC
  step with obj.node_get.spec as ⟨i4, hi4⟩
  rw [hcpu'] at hi4
  by_cases e : L.mem s (scA t) = nodeW st s c layout.node.CUR_SC
  · have : (L.mem s (scA t) != i4) = false := by rw [hi4]; simpa [nodeW] using e
    simp only [this, Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact skip (by rw [hif', ite_f]; rw [e, ← hs.curSc]; simp)
  · have : (L.mem s (scA t) != i4) = true := by rw [hi4]; simpa [nodeW] using e
    simp only [this, ↓reduceIte]
    refine WP.spec_bind (WP.spec_and (unblock_check_refines s σ hS hscC (hy.spor hsp')) (unblock_check_scw hS hscC (hy.spor hsp'))) ?_
    rintro s' ⟨⟨σ', he, -, -, hS'⟩, hW⟩
    have hK := nks_refillUnblockCheck _ σ ((), σ') (by rw [he]; rfl)
    refine hk s' σ' ?_ (sc_step_lift hP0 hX (hW.mono fun _ h => Or.inl h) hK hS') (fun p y' h => hK.fwd h (by intros; nofun))
    rw [hspec0, hif', ite_t ⟨hsp.2 hsp', by rw [hs.curSc]; exact bv_ne e⟩, he]

end Unblock


/-! ## `postpone` -/

section Postpone
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`dequeue`'s footprint** at the precision of `SFootI`. -/
theorem dequeue_sfootI {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => WritesIn st s s' (SFootI st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  refine WP.spec_mono (sched.dequeue.foot s t _ hc.tcbs ht hp hN hN' (hR1.1.rel _ hp) (hc.queued t ht).1) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  exact hw.mono fun b hb => qfoot_sfootI hc.tcbs (fun w hw' => (hc.ready.1.rel _ hp).mem w hw') ht hc.node hc.cur hb
    (by omega)

/-- **`release_enqueue`'s footprint** at the precision of `SFootI`. -/
theorem release_enqueue_sfootI {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.release_enqueue st s t ⦃ s' => WritesIn st s s' (SFootI st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hrel : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) R := by rw [haf]; exact hc.release
  have htR : t ∉ R := fun hm => (hc.released t ht).2 hm hr0
  refine WP.spec_mono (sched.release_enqueue.foot s t _ hc.tcbs ht htR hN hN' hrel) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  refine hw.mono fun b hb => qfoot_sfootI hc.tcbs (fun w hw' => ?_) ht hc.node hc.cur hb (by simp [RelOffs])
  rcases List.mem_cons.1 hw' with rfl | hw'
  · exact ht
  · exact hc.release.mem w hw'

/-- An SC word the relation reads is no scheduler word. -/
theorem scIn_not_sfootI {s s' : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {sc a : U64}
    (hsc : sc ∈ C) (hin : ScIn st s sc a) (hk : L.ksb s' = L.ksb s) : ¬ SFootI st T c s' a := by
  obtain ⟨-, hn, hT, -⟩ := hS.scOutIn hsc hin
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  rintro (⟨y, hy, hb⟩ | ⟨g1, g2, -⟩)
  · have hya := hc.tcbs y hy
    have := hT y hy
    rcases hb with rfl | rfl | rfl <;> (rw [tfield_val hya (by decide)] at this; simp at this <;> omega)
  · have e : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
    rw [e] at g1 g2; omega

/-- **`postpone`'s footprint** at the precision of `SFootI`. -/
theorem postpone_sfootI {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {t : U64} (ht : t ∈ T)
    (htw : L.mem s (scW sc 24#u64) = t) (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.postpone st s sc ⦃ s' => WritesIn st s s' (SFootI st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨y, n, hky, hy⟩ := hs.scs sc hsc
  obtain ⟨h8, -, hfit⟩ := hy.bounds
  have h16 : (16#u64 : U64).val = 16 := rfl
  have hcoreIn : ScIn st s sc (scW sc 16#u64) := by
    unfold ScIn; rw [scW_val (by rw [h16]; omega), h16]; omega
  have hcoreAl : Aligned (scW sc 16#u64) := by unfold Aligned; rw [scW_val (by rw [h16]; omega), h16]; omega
  unfold sched.postpone
  step with obj.Sc.tcb.spec as ⟨i, i_post⟩
  have hi : i = t := by rw [i_post, scTcbA_eq, htw]
  subst hi
  refine WP.spec_bind (WP.spec_and (dequeue_refines s σ hS i ht) (dequeue_sfootI hS ht)) ?_
  rintro s1 ⟨⟨σ1, -, -, hq1, -, hS1⟩, hw1⟩
  obtain ⟨Q1, R1, hc1, hs1⟩ := hS1.lists
  have hr01 : (L.mem s1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hne
    have hm := (hc1.released i ht).1 hne
    have : i.bv ∈ σ.releaseQueue := by rw [← hq1, hs1.rel]; exact List.mem_map_of_mem hm
    rw [hs.rel, mem_map_bv] at this
    exact (hc.released i ht).2 this hr0
  refine WP.spec_bind (release_enqueue_sfootI hS1 ht hr01) ?_
  rintro s2 hw2
  step with obj.Sc.cpu.spec as ⟨cpu, cpu_post⟩
  have hcpu : cpu = c := by
    rw [cpu_post, scCoreA_eq, hw2.mem_eq hcoreAl (scIn_not_sfootI hS hsc hcoreIn hw1.1),
      hw1.mem_eq hcoreAl (scIn_not_sfootI hS hsc hcoreIn rfl)]
    exact hS.core sc hsc
  subst hcpu
  refine WP.spec_mono (sched.set_reprogram_on.spec s2 cpu) ?_
  rintro s3 rfl
  have hN2 : NodePlaced st T s2 cpu := hc.node.ksb (hw2.1.trans hw1.1)
  have ho : (layout.node.REPROGRAM).val < 4288 := by simp [layout.node.REPROGRAM]
  have hal : Aligned (L.nodeAt s2 cpu layout.node.REPROGRAM) := nodeAt_aligned hN2 ho (by simp [layout.node.REPROGRAM])
  refine WritesIn.sfootI_trans (WritesIn.sfootI_trans hw1 hw2) ((writesIn_wr hal).mono fun b hb => ?_)
  subst hb
  exact sfootI_node hN2 ho (by simp [layout.node.REPROGRAM])

/-- **What `postpone` needs of the spec beyond `IRel`** (l4v `valid_sched`
and `sym_refs`): the release queue sorted with SCs (`RelOK`), the thread in
no release queue, and the SC bound back to it. -/
def PostponeOK (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (y : Fl4Spec.SchedContext) : Prop :=
  RelOK σ ∧ t ∉ σ.releaseQueue ∧ y.scTcb = some t

set_option maxHeartbeats 4000000 in
/-- **`postpone` on `IRel`** (`ReplyTmoHyps.postpone`): `postpone_refines`
with its footprint (`postpone_sfootI`), lifted by `sc_step_lift`. -/
theorem postpone_top (hP0 : IPlaced N T E R B) :
    ∀ s (a : A) σ (t sc : U64) (x : Fl4Spec.Tcb) (y : Fl4Spec.SchedContext) (n : Nat),
    IRel st th cr N T C E R B c s σ → t ∈ T → sc ∈ C → σ.kheap t.bv = some (.tcb x) →
    x.tcbSchedContext = some sc.bv → σ.kheap sc.bv = some (.schedContext y n) → PostponeOK σ t.bv y →
    Fl4Spec.scActive y = true →
    (do let s4 ← sched.postpone st s sc; ok (s4, a)) ⦃ res =>
      ∃ z ∈ (Fl4Spec.postpone (Z := Unit) sc.bv σ).1, IRel st th cr N T C E R B c res.1 z.2 ⦄ := by
  intro s a σ t sc x y n hX ht hsc hkx hxsc hky ⟨hRel, hnr, hyt⟩ hya
  have hS := hX.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  rw [hkx] at hkt; cases hkt
  have h0 : L.mem s (scA t) ≠ 0#u64 := (Notif.optRef_some (hsct.symm.trans hxsc)).1
  obtain ⟨y', n', hky', hy'⟩ := hs.scs sc hsc
  rw [hky] at hky'; cases hky'
  have htw : L.mem s (scW sc 24#u64) = t := eq_of_bv (Notif.optRef_some (hy'.tcb.symm.trans hyt)).2
  have hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hne
    have hm := (hc.released t ht).1 hne
    exact hnr (by rw [hs.rel, mem_map_bv]; exact hm)
  have hst : L.mem s (scA t) = sc := eq_of_bv (Notif.optRef_some (hsct.symm.trans hxsc)).2
  refine WP.spec_bind (WP.spec_and (postpone_refines s σ hS hRel hsc ht htw h0 hr0 (by rw [hst]; exact hy'.rmax_ne hya))
    (postpone_sfootI hS hsc ht htw hr0)) ?_
  rintro s' ⟨⟨σ', he, -, -, -, -, -, -, hS'⟩, hW⟩
  have hK := nks_postpone _ σ ((), σ') (by rw [he]; rfl)
  exact (WP.spec_ok _).2 ⟨((), σ'), by rw [he]; rfl, sc_step_lift hP0 hX (hW.mono fun _ h => Or.inr h) hK hS'⟩

end Postpone


/-! ## The reply's named steps -/

section Reply
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`ReplyTmoHyps` with `postpone` proved** (`postpone_top`), from the
spec facts it needs (`PostponeOK`). -/
theorem ReplyTmoHyps.ofPost (hP0 : IPlaced N T E R B)
    (hPO : ∀ s σ (t sc : U64) (x : Fl4Spec.Tcb) (y : Fl4Spec.SchedContext) (n : Nat),
      IRel st th cr N T C E R B c s σ → t ∈ T → sc ∈ C → σ.kheap t.bv = some (.tcb x) →
      Fl4Spec.runnable x.tcbState = true → x.tcbSchedContext = some sc.bv →
      σ.kheap sc.bv = some (.schedContext y n) → t.bv ∉ σ.releaseQueue → PostponeOK σ t.bv y)
    (htx : ∀ (a : A) (t : U64) (xt : Fl4Spec.Tcb) (bb : Fl4Spec.Word) (e bdg : U64) (g : Bool) (d : U64)
      (xd : Fl4Spec.Tcb), t ∈ T → d ∈ T → t ≠ d → xt.tcbFault = some (.timeout bb) → xt.tcbSchedContext ≠ none →
      ∀ (s1 : S) (σ1 : Fl4Spec.State Unit),
        EpStateRel T E R B (L.mem s1) σ1 → SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s1 σ1 →
        σ1.kheap t.bv = some (.tcb xt) → σ1.kheap d.bv = some (.tcb xd) →
        ipc.do_ipc_transfer st ar s1 a t e bdg g d ⦃ s' => XferPost (L := L) T E R B
          (SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))) s1 σ1 t d e bdg g xd s' ⦄)
    (hepE : ∀ s σ (t : U64) (x : Fl4Spec.Tcb) (p bd : Fl4Spec.Word) (r : Fl4Spec.CapRights),
      IRel st th cr N T C E R B c s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
      x.tcbTimeoutHandler = .endpointCap p bd r → ∀ e : U64, e.bv = p → e ∈ E) :
    ReplyTmoHyps st ar th cr N T C E R B c :=
  ⟨fun s a σ t sc x y n h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    postpone_top hP0 s a σ t sc x y n h1 h2 h3 h4 h6 h7 (hPO s σ t sc x y n h1 h2 h3 h4 h5 h6 h7 h9) h8, htx, hepE⟩

/-- **`ReplyHyps` from `remove` and the spec facts of the timeout branch**:
`unblock` (`unblock_top`), `postpone` (`postpone_top`), `faultReply`,
`grantXfer` and `tmo` proved. -/
theorem ReplyHyps.ofL (hH : IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hTl : IpcEpTailHyps st A N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)))
    (hP : IPlaced N T E R B)
    (hSV : ∀ s' σ', IRel st th cr N T C E R B c s' σ' → Sched.SchedValid σ')
    (hrem : ∀ s (a : A) σ (r t : U64) (x : Fl4Spec.Tcb), IRel st th cr N T C E R B c s σ → r ∈ R → t ∈ T →
      σ.kheap t.bv = some (.tcb x) → x.tcbState = .blockedOnReply r.bv →
      ipc.reply_remove st ar s a r t ⦃ res => res.2 = a ∧ ∃ σ' x',
        Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧ IRel st th cr N T C E R B c res.1 σ' ∧
        σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive ∧ x'.tcbFault = x.tcbFault ∧
        (∀ p y n, σ'.kheap p = some (.schedContext y n) → y.scTcb = some t.bv → Fl4Spec.scActive y = true) ∧
        ∀ p y, p ≠ t.bv → σ.kheap p = some (.tcb y) → ∃ y', σ'.kheap p = some (.tcb y') ∧
          y'.tcbFault = y.tcbFault ∧ y'.tcbState = y.tcbState ⦄)
    (hPO : ∀ s σ (t sc : U64) (x : Fl4Spec.Tcb) (y : Fl4Spec.SchedContext) (n : Nat),
      IRel st th cr N T C E R B c s σ → t ∈ T → sc ∈ C → σ.kheap t.bv = some (.tcb x) →
      Fl4Spec.runnable x.tcbState = true → x.tcbSchedContext = some sc.bv →
      σ.kheap sc.bv = some (.schedContext y n) → t.bv ∉ σ.releaseQueue → PostponeOK σ t.bv y)
    (htx : ∀ (a : A) (t : U64) (xt : Fl4Spec.Tcb) (bb : Fl4Spec.Word) (e bdg : U64) (g : Bool) (d : U64)
      (xd : Fl4Spec.Tcb), t ∈ T → d ∈ T → t ≠ d → xt.tcbFault = some (.timeout bb) → xt.tcbSchedContext ≠ none →
      ∀ (s1 : S) (σ1 : Fl4Spec.State Unit),
        EpStateRel T E R B (L.mem s1) σ1 → SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c))) s1 σ1 →
        σ1.kheap t.bv = some (.tcb xt) → σ1.kheap d.bv = some (.tcb xd) →
        ipc.do_ipc_transfer st ar s1 a t e bdg g d ⦃ s' => XferPost (L := L) T E R B
          (SRN st N T (SRS st T (SRT st th cr N T C E R B c (SRE st N T C E R B c)))) s1 σ1 t d e bdg g xd s' ⦄)
    (hepE : ∀ s σ (t : U64) (x : Fl4Spec.Tcb) (p bd : Fl4Spec.Word) (r : Fl4Spec.CapRights),
      IRel st th cr N T C E R B c s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
      x.tcbTimeoutHandler = .endpointCap p bd r → ∀ e : U64, e.bv = p → e ∈ E)
    (hinv : ∀ s σ, IRel st th cr N T C E R B c s σ → Sched.Inv σ) :
    ReplyHyps st ar th cr N T C E R B c :=
  ReplyHyps.ofT hH hBf hBm hTl hP hSV (ReplyTmoHyps.ofPost hP hPO htx hepE) hrem (unblock_top hP) hinv

end Reply

end

end Fl4Proofs.P3.Ipc

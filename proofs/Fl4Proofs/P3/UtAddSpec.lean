/-
P3 (DESIGN.md §9), untyped: **the spec's invariants across a retype's fresh
idle endpoints or notifications** (handoff/utj.md "Round 3b part 2", c).

A no-reset retype of endpoints or notifications changes the spec's state in
two parts (UtEpXTop's `invokeUntyped_noreset_add`): `SpecAdd` (the window's
objects, `defaultEp` or `defaultNotification`, at addresses the heap had
free) and a CNode-only step (`CnK`). `IdleNew` names the first part's
objects (idle endpoints, notifications, free replies, arch objects or CNodes).
Each scheduler-side invariant `JAtZ` carries survives `SpecAdd` (no TCB or
SC is added; the new endpoints' and notifications' queues are empty, their SC
and bound thread null; the new replies have no TCB and no SC): `NSC` (at the notifications
grown by the window), `CurInv`, `CurOwnW`, `OffOK`, `ActIdle`, `Inv`
(`Inv.add`), `BlockedScActive` (`BlockedScActive.add`), `IpcSorted`,
`CurRunM`; the keep relations the FL4-side frames read (`CKeep`, `YKeep`,
`McpKeep`, the buffer words, `RecvB` back) hold across `SpecAdd` followed by
a `CnStep` (`uaCKeep`, …). The CNode step's part is SpecKeepC's.
-/
import Fl4Proofs.P3.XTopJointUtEp
import Fl4Proofs.P3.XTopJointRest
import Fl4Proofs.P3.ScFreshSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section Spec
open Fl4Spec

/-- The added objects are idle endpoints, notifications, replies, arch
objects or CNodes. -/
def IdleNew (W : ObjRef → Prop) (o : ObjRef → KernelObject) : Prop :=
  ∀ p, W p → o p = .endpoint defaultEp ∨ o p = .notification defaultNotification ∨ o p = .reply defaultReply ∨
    (∃ ao, o p = .archObj ao) ∨ ∃ r cs, o p = .cnode r cs

variable {σ σ' σ'' : State Unit} {W : ObjRef → Prop} {o : ObjRef → KernelObject}

theorem IdleNew.fresh (hi : IdleNew W o) : ∀ p, W p → FreshOK (o p) := by
  intro p hp
  rcases hi p hp with e | e | e | ⟨ao, e⟩ | ⟨r, cs, e⟩ <;> rw [e]
  · exact Or.inr (Or.inr (Or.inr ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))

/-- An object of a kind `SpecAdd` with `IdleNew` does not add is looked up alike. -/
theorem Sched.SpecAdd.lookI (h : SpecAdd σ σ' W o) (hi : IdleNew W o) {p : ObjRef} {ko : KernelObject}
    (he : ∀ x, ko ≠ .endpoint x) (hn : ∀ x, ko ≠ .notification x) (hr : ∀ x, ko ≠ .reply x)
    (ha : ∀ x, ko ≠ .archObj x) (hc : ∀ r cs, ko ≠ .cnode r cs) :
    σ'.kheap p = some ko ↔ σ.kheap p = some ko := by
  refine ⟨fun hk => ?_, h.kold⟩
  rcases h.kback hk with e | ⟨hw, rfl⟩
  · exact e
  · rcases hi p hw with e | e | e | ⟨_, e⟩ | ⟨_, _, e⟩
    · exact absurd e (he _)
    · exact absurd e (hn _)
    · exact absurd e (hr _)
    · exact absurd e (ha _)
    · exact absurd e (hc _ _)

theorem Sched.SpecAdd.tcbI (h : SpecAdd σ σ' W o) (hi : IdleNew W o) {p : ObjRef} {x : Tcb} :
    σ'.kheap p = some (.tcb x) ↔ σ.kheap p = some (.tcb x) :=
  h.lookI hi (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)
    (fun _ _ e => by cases e)

theorem Sched.SpecAdd.scI (h : SpecAdd σ σ' W o) (hi : IdleNew W o) {p : ObjRef} {y : SchedContext} {n : Nat} :
    σ'.kheap p = some (.schedContext y n) ↔ σ.kheap p = some (.schedContext y n) :=
  h.lookI hi (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)
    (fun _ _ e => by cases e)

/-- A reply after: one before, or a new free one. -/
theorem Sched.SpecAdd.replyB (h : SpecAdd σ σ' W o) (hi : IdleNew W o) {p : ObjRef} {x : Reply}
    (hk : σ'.kheap p = some (.reply x)) : σ.kheap p = some (.reply x) ∨ (W p ∧ x = defaultReply) := by
  rcases h.kback hk with e | ⟨hw, e⟩
  · exact Or.inl e
  · rcases hi p hw with e' | e' | e' | ⟨_, e'⟩ | ⟨_, _, e'⟩ <;> rw [e'] at e <;> cases e
    exact Or.inr ⟨hw, rfl⟩

/-- A notification after: one before, or a new idle one. -/
theorem Sched.SpecAdd.ntfnB (h : SpecAdd σ σ' W o) (hi : IdleNew W o) {p : ObjRef} {x : Notification}
    (hk : σ'.kheap p = some (.notification x)) : σ.kheap p = some (.notification x) ∨ (W p ∧ x = defaultNotification) := by
  rcases h.kback hk with e | ⟨hw, e⟩
  · exact Or.inl e
  · rcases hi p hw with e' | e' | e' | ⟨_, e'⟩ | ⟨_, _, e'⟩ <;> rw [e'] at e <;> cases e
    exact Or.inr ⟨hw, rfl⟩

/-- An endpoint after: one before, or a new idle one. -/
theorem Sched.SpecAdd.epB (h : SpecAdd σ σ' W o) (hi : IdleNew W o) {p : ObjRef} {x : Endpoint}
    (hk : σ'.kheap p = some (.endpoint x)) : σ.kheap p = some (.endpoint x) ∨ x = defaultEp := by
  rcases h.kback hk with e | ⟨hw, e⟩
  · exact Or.inl e
  · rcases hi p hw with e' | e' | e' | ⟨_, e'⟩ | ⟨_, _, e'⟩ <;> rw [e'] at e <;> cases e
    exact Or.inr rfl

theorem Sched.SpecAdd.sched_eq (h : SpecAdd σ σ' W o) (hi : IdleNew W o) (t : ObjRef) :
    schedulable t σ' = schedulable t σ := by
  have hrel := h.f.2.1
  cases e : schedulable t σ with
  | true =>
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv e
    exact schedulable_of ((h.tcbI hi).2 h1) h2 h3 ((h.scI hi).2 h4) h5 (by rw [hrel]; exact h6)
  | false =>
    cases e' : schedulable t σ' with
    | false => rfl
    | true =>
      obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv e'
      rw [schedulable_of ((h.tcbI hi).1 h1) h2 h3 ((h.scI hi).1 h4) h5 (by rw [← hrel]; exact h6)] at e
      cases e

theorem prioOf_uadd (h : SpecAdd σ σ' W o) (hi : IdleNew W o) (u : ObjRef) : Sched.prioOf σ' u = Sched.prioOf σ u := by
  cases hk : σ.kheap u with
  | some k =>
    have hk' := h.kold hk
    unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [hk, hk']
  | none =>
    cases hk' : σ'.kheap u with
    | none => unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [hk, hk']
    | some k =>
      rcases h.kback hk' with e | ⟨hw, rfl⟩
      · rw [hk] at e; cases e
      · unfold Sched.prioOf tcbsOf tcbsOfKh optMap; rw [hk, hk']
        rcases hi u hw with e | e | e | ⟨_, e⟩ | ⟨_, _, e⟩ <;> rw [e] <;> rfl

theorem Sched.NSC.uadd {N Nn C : Set U64} (hN : NSC N C σ) (h : SpecAdd σ σ' W o) (hi : IdleNew W o)
    (hW : ∀ n ∈ Nn, W n.bv) : NSC (N ∪ Nn) C σ' := by
  intro n hn x p hx hp
  rcases h.ntfnB hi hx with e | ⟨-, rfl⟩
  · rcases hn with hn | hn
    · exact hN n hn x p e hp
    · rw [(h.new _ (hW n hn)).1] at e; cases e
  · cases hp

theorem Sched.CurInv.uadd (hI : CurInv σ) (h : SpecAdd σ σ' W o) (hi : IdleNew W o) : CurInv σ' := by
  obtain ⟨-, hrel, hct, -, hcsc, -, -, -, -, -, -, hisc⟩ := h.f
  obtain ⟨xt, hkt, hxs, hnb⟩ := hI.tcb
  obtain ⟨x, n, hx⟩ := hI.sc
  refine ⟨⟨xt, by rw [hct]; exact (h.tcbI hi).2 hkt, by rw [hcsc]; exact hxs, hnb⟩,
    ⟨x, n, by rw [hcsc]; exact (h.scI hi).2 hx⟩, fun hne y m hy => ?_, by rw [hct, hrel]; exact hI.notRel⟩
  rw [hcsc, hisc] at hne; rw [hcsc] at hy
  exact hI.active hne y m ((h.scI hi).1 hy)

theorem CurInvW.uadd (hC : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) (h : SpecAdd σ σ' W o)
    (hi : IdleNew W o) : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
  rcases hC with e | hI
  · left; rw [h.f.2.2.2.1]; exact e
  · right; exact hI.uadd h hi

theorem Sched.OffOK.uadd (hO : OffOK σ) (h : SpecAdd σ σ' W o) (hi : IdleNew W o) : OffOK σ' := by
  obtain ⟨-, -, -, -, hcsc, htime, hcons, -, -, -, -, hisc⟩ := h.f
  intro hc y n hy ha
  rw [hcons] at hc ⊢; rw [htime]
  rw [hcsc] at hy; rw [hcsc, hisc] at ha
  exact hO hc y n ((h.scI hi).1 hy) ha

theorem Sched.ActIdle.uadd (hA : ActIdle σ) (h : SpecAdd σ σ' W o) (hi : IdleNew W o) : ActIdle σ' := by
  obtain ⟨-, hrel, -, hact, -, -, -, -, -, -, hidle, hisc⟩ := h.f
  obtain ⟨hS, x, hx, h1, h2, h3⟩ := hA
  refine ⟨fun t ht => ?_, x, by rw [hidle]; exact (h.tcbI hi).2 hx, by rw [hisc]; exact h1, h2,
    by rw [hidle, hrel]; exact h3⟩
  rw [hact] at ht
  rw [h.sched_eq hi]; exact hS t ht

theorem Sched.CurOwnW.uadd {T C : Set U64} (hO : CurOwnW T C σ) (h : SpecAdd σ σ' W o) (hi : IdleNew W o) :
    CurOwnW T C σ' := by
  obtain ⟨-, hrel, -, -, hcsc, -, hcons, -, -, -, -, -⟩ := h.f
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨⟨sc, hsc, hb⟩, hun⟩
  · refine Or.inl ⟨u, hu, xt, (h.tcbI hi).2 hkt, by rw [hcsc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [hcsc] at hy; exact hown y n ((h.scI hi).1 hy)
    · rw [hcons] at h0; rw [hrel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨⟨sc, hsc, by rw [hcsc]; exact hb⟩, fun y n hy => ?_⟩
    rw [hcsc] at hy; exact hun y n ((h.scI hi).1 hy)

theorem Sched.IpcSorted.uadd (hS : IpcSorted σ) (h : SpecAdd σ σ' W o) (hi : IdleNew W o) : IpcSorted σ' := by
  refine ⟨fun p x hp => ?_, fun p x hp => ?_⟩
  · rcases h.epB hi hp with e | rfl
    · exact (hS.1 p x e).congr fun u _ => prioOf_uadd h hi u
    · exact List.Pairwise.nil
  · rcases h.ntfnB hi hp with e | ⟨-, rfl⟩
    · exact (hS.2 p x e).congr fun u _ => prioOf_uadd h hi u
    · exact List.Pairwise.nil

theorem CurRunM.uadd (hR : CurRunM σ) (h : SpecAdd σ σ' W o) (hi : IdleNew W o) : CurRunM σ' := by
  obtain ⟨-, -, hct, hact, -, -, -, -, -, -, hidle, -⟩ := h.f
  rcases hR with e | e
  · left; rw [hact]; exact e
  · right
    rcases e with r | r
    · left; intro y hy; rw [hct] at hy; exact r y ((h.tcbI hi).1 hy)
    · right; rw [hct, hidle]; exact r

/-- `RecvB` back across `SpecAdd` (no TCB added, the new replies free). -/
theorem Sched.SpecAdd.recvB (h : SpecAdd σ σ' W o) (hi : IdleNew W o) {d : U64} (hd : RecvB σ' d) : RecvB σ d := by
  obtain ⟨x, t, xt, h1, h2, h3, h4⟩ := hd
  rcases h.replyB hi h1 with e | ⟨-, rfl⟩
  · exact ⟨x, t, xt, e, h2, (h.tcbI hi).1 h3, h4⟩
  · cases h2

/-! ### Across `SpecAdd` then a `CnStep` -/

theorem uaCKeep (h : SpecAdd σ σ' W o) (hi : IdleNew W o) (hC : CnStep σ' σ'') : Sched.CKeep σ σ'' :=
  ⟨fun q y n hq => ⟨y, hC.sc.2 ((h.scI hi).2 hq), rfl⟩,
    fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 (h.kold hq), rfl, rfl⟩,
    fun p x n hp => ⟨x, (h.scI hi).1 (hC.sc.1 hp)⟩⟩

theorem uaYKeep (h : SpecAdd σ σ' W o) (hi : IdleNew W o) (hC : CnStep σ' σ'') : YKeep σ σ'' :=
  ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF ((h.tcbI hi).2 hp); ⟨y, hy, hc.yld⟩,
    fun p x n hp => ⟨x, hC.sc.2 ((h.scI hi).2 hp), rfl⟩,
    fun p y n hp => ⟨y, (h.scI hi).1 (hC.sc.1 hp), rfl⟩⟩

theorem uaMcpKeep (h : SpecAdd σ σ' W o) (hi : IdleNew W o) (hC : CnStep σ' σ'') : McpKeep σ σ'' :=
  fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF ((h.tcbI hi).2 hp); ⟨y, hy, hc.mcp⟩

theorem uaBufKeep (h : SpecAdd σ σ' W o) (hi : IdleNew W o) (hC : CnStep σ' σ'') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ''.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF ((h.tcbI hi).2 hp); ⟨y, hy, hc.buf⟩

theorem uaRecvB (h : SpecAdd σ σ' W o) (hi : IdleNew W o) (hC : CnStep σ' σ'') {d : U64} (hd : RecvB σ'' d) :
    RecvB σ d :=
  h.recvB hi (hC.toHStep.khrb.recvB hd)

theorem Sched.RRecv.uadd {R : Set U64} {m m' : U64 → U64} (hR : RRecv m R σ) (h : SpecAdd σ σ' W o) (hi : IdleNew W o)
    (hC : CnStep σ' σ'') (hm : ∀ d ∈ R, m' (rPrevA d) = m (rPrevA d) ∧ m' (rNextA d) = m (rNextA d)) :
    RRecv m' R σ'' := fun d hd hr => by
  obtain ⟨h1, h2⟩ := hR d hd (uaRecvB h hi hC hr)
  exact ⟨(hm d hd).2.trans h1, (hm d hd).1.trans h2⟩

/-- `SzKeep` across `SpecAdd` then a `CnStep`. -/
theorem uaSzKeep (h : SpecAdd σ σ' W o) (hi : IdleNew W o) (hC : CnStep σ' σ'') : SzKeep σ σ'' := by
  intro p x n hp
  exact ⟨x, (h.scI hi).1 (hC.sc.1 hp)⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 2000000 in
/-- **`JRest`'s scheduler-side fields across a retype's fresh idle objects**
(module docstring): from `JAtZ` before, FL4 writing slot words only, and the
spec's `SpecAdd` of idle endpoints or notifications followed by a CNode-only
step: the call stacks and reply placement (`CallRel.carry`, at the old
notifications), `RFree`, `RRecv`, yield, MCP and buffer words, `NSC` at the
notifications grown by `Nn`, `Inv`, `CurInv` unless rescheduling,
`CurOwnW`, `OffOK`, `ActIdle`, `BlockedScActive`, `IpcSorted`, `CurRunM`. -/
theorem JAtZ.uaRest {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (InSlot Z.th))
    {σB σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}
    (hA : SpecAdd σ σB W o) (hi : IdleNew W o) (hcn : CnK σB σ') {Nn : Set U64} (hWn : ∀ n ∈ Nn, W n.bv) :
    CallRel (L.mem s') Z.R Z.C σ' Lst ∧ RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ' ∧ RFree (L.mem s') Z.R Z.C σ' Lst ∧
    RRecv (L.mem s') Z.R σ' ∧ YieldRel Z.T Z.C (L.mem s') σ' ∧ McpRel Z.T (L.mem s') σ' ∧
    BufWordRel Z.T (L.mem s') σ' ∧ NSC (Z.N ∪ Nn) Z.C σ' ∧ Inv σ' ∧
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ CurOwnW Z.T Z.C σ' ∧ OffOK σ' ∧ ActIdle σ' ∧
    BlockedScActive σ' ∧ IpcSorted σ' ∧ CurRunM σ' := by
  have hC := CnStep.of_cnK hcn
  obtain ⟨k1, k2, kb, k3, k4⟩ := inSlot_keeps arI J hw
  have ck := uaCKeep hA hi hC
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hw.1 ck
  refine ⟨hCR', hRP', RFree.carry J.rfree J.call k4 ck, J.rrecv.uadd hA hi hC k4,
    J.yld.frame k2 (uaYKeep hA hi hC), J.mcp.frame k1 (uaMcpKeep hA hi hC), J.buf.frame kb (uaBufKeep hA hi hC),
    (J.nsc.uadd hA hi hWn).cn hC.toHStep, (Inv.add J.inv hA hi.fresh).cn hC,
    CurInvW.cn (CurInvW.uadd J.cur hA hi) hC, (J.own.uadd hA hi).cn hC.toHStep, (J.off.uadd hA hi).cn hC.toHStep,
    (J.act.uadd hA hi).cn hC, (BlockedScActive.add J.bsa hA hi.fresh).cn hC.toHStep,
    (J.isorted.uadd hA hi).cn hC.toHStep, (J.curRun.uadd hA hi).cn hC.toHStep (Or.inr hC.act)⟩

end

end

end Fl4Proofs.P3

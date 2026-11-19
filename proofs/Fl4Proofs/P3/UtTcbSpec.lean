/-
P3 (DESIGN.md §9), untyped: **the spec's invariants across a retype's fresh
objects, TCBs included** (handoff/utj.md "uttypes (lines ut31 and ut35)", plan
item 4; l4v `retype_region` of `TCBObject`s, `default_tcb`).

UtAddSpec's `IdleNew` names the fresh objects of a no-reset retype other than
TCBs. `IdleNewT` also admits `default_tcb d` (inactive, no SC, no bound
notification, no yield, MCP and priority 0, buffer 0). Each lemma of
UtAddSpec is restated over `IdleNewT` (suffix `T`); the old `IdleNew`
statements are untouched (`IdleNew.toT` lifts their premise):

* a TCB after is one before or a new default one (`SpecAdd.tcbBT`); a new TCB
  has no SC, so `schedulable` is unchanged (`SpecAdd.sched_eqT`) and its
  priority (0) is `prioOf`'s default (`prioOf_uaddT`);
* a new TCB is inactive, so it is neither receive-blocked (`recvBT`) nor
  runnable: `CurRunM` needs the current thread not new (`hcW`).
-/
import Fl4Proofs.P3.UtAddSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section Spec
open Fl4Spec

/-- **The added objects**: `IdleNew`'s kinds or default TCBs. -/
def IdleNewT (W : ObjRef → Prop) (o : ObjRef → KernelObject) : Prop :=
  ∀ p, W p → o p = .endpoint defaultEp ∨ o p = .notification defaultNotification ∨ o p = .reply defaultReply ∨
    (∃ ao, o p = .archObj ao) ∨ (∃ r cs, o p = .cnode r cs) ∨ ∃ d, o p = .tcb (defaultTcb d)

variable {σ σ' σ'' : State Unit} {W : ObjRef → Prop} {o : ObjRef → KernelObject}

theorem IdleNew.toT (hi : IdleNew W o) : IdleNewT W o := fun p hp => by
  rcases hi p hp with e | e | e | e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))

theorem IdleNewT.fresh (hi : IdleNewT W o) : ∀ p, W p → FreshOK (o p) := by
  intro p hp
  rcases hi p hp with e | e | e | ⟨ao, e⟩ | ⟨r, cs, e⟩ | ⟨d, e⟩ <;> rw [e]
  · exact Or.inr (Or.inr (Or.inr ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
  · exact Or.inl ⟨d, rfl⟩

/-- An object of a kind `SpecAdd` with `IdleNewT` does not add is looked up alike. -/
theorem Sched.SpecAdd.lookIT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) {p : ObjRef} {ko : KernelObject}
    (he : ∀ x, ko ≠ .endpoint x) (hn : ∀ x, ko ≠ .notification x) (hr : ∀ x, ko ≠ .reply x)
    (ha : ∀ x, ko ≠ .archObj x) (hc : ∀ r cs, ko ≠ .cnode r cs) (ht : ∀ x, ko ≠ .tcb x) :
    σ'.kheap p = some ko ↔ σ.kheap p = some ko := by
  refine ⟨fun hk => ?_, h.kold⟩
  rcases h.kback hk with e | ⟨hw, rfl⟩
  · exact e
  · rcases hi p hw with e | e | e | ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, e⟩
    · exact absurd e (he _)
    · exact absurd e (hn _)
    · exact absurd e (hr _)
    · exact absurd e (ha _)
    · exact absurd e (hc _ _)
    · exact absurd e (ht _)

theorem Sched.SpecAdd.scIT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) {p : ObjRef} {y : SchedContext} {n : Nat} :
    σ'.kheap p = some (.schedContext y n) ↔ σ.kheap p = some (.schedContext y n) :=
  h.lookIT hi (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)
    (fun _ _ e => by cases e) (fun _ e => by cases e)

/-- A TCB after: one before, or a new default one. -/
theorem Sched.SpecAdd.tcbBT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) {p : ObjRef} {x : Tcb}
    (hk : σ'.kheap p = some (.tcb x)) : σ.kheap p = some (.tcb x) ∨ (W p ∧ ∃ d, x = defaultTcb d) := by
  rcases h.kback hk with e | ⟨hw, e⟩
  · exact Or.inl e
  · rcases hi p hw with e' | e' | e' | ⟨_, e'⟩ | ⟨_, _, e'⟩ | ⟨d, e'⟩ <;> rw [e'] at e <;> cases e
    exact Or.inr ⟨hw, d, rfl⟩

/-- A TCB after is one before, or new and inactive with no SC. -/
theorem Sched.SpecAdd.tcbIn (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) {p : ObjRef} {x : Tcb}
    (hk : σ'.kheap p = some (.tcb x)) :
    σ.kheap p = some (.tcb x) ∨ (W p ∧ x.tcbState = .inactive ∧ x.tcbSchedContext = none) := by
  rcases h.tcbBT hi hk with e | ⟨hw, d, rfl⟩
  · exact Or.inl e
  · exact Or.inr ⟨hw, rfl, rfl⟩

theorem Sched.SpecAdd.replyBT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) {p : ObjRef} {x : Reply}
    (hk : σ'.kheap p = some (.reply x)) : σ.kheap p = some (.reply x) ∨ (W p ∧ x = defaultReply) := by
  rcases h.kback hk with e | ⟨hw, e⟩
  · exact Or.inl e
  · rcases hi p hw with e' | e' | e' | ⟨_, e'⟩ | ⟨_, _, e'⟩ | ⟨_, e'⟩ <;> rw [e'] at e <;> cases e
    exact Or.inr ⟨hw, rfl⟩

theorem Sched.SpecAdd.ntfnBT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) {p : ObjRef} {x : Notification}
    (hk : σ'.kheap p = some (.notification x)) :
    σ.kheap p = some (.notification x) ∨ (W p ∧ x = defaultNotification) := by
  rcases h.kback hk with e | ⟨hw, e⟩
  · exact Or.inl e
  · rcases hi p hw with e' | e' | e' | ⟨_, e'⟩ | ⟨_, _, e'⟩ | ⟨_, e'⟩ <;> rw [e'] at e <;> cases e
    exact Or.inr ⟨hw, rfl⟩

theorem Sched.SpecAdd.epBT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) {p : ObjRef} {x : Endpoint}
    (hk : σ'.kheap p = some (.endpoint x)) : σ.kheap p = some (.endpoint x) ∨ x = defaultEp := by
  rcases h.kback hk with e | ⟨hw, e⟩
  · exact Or.inl e
  · rcases hi p hw with e' | e' | e' | ⟨_, e'⟩ | ⟨_, _, e'⟩ | ⟨_, e'⟩ <;> rw [e'] at e <;> cases e
    exact Or.inr rfl

theorem Sched.SpecAdd.sched_eqT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) (t : ObjRef) :
    schedulable t σ' = schedulable t σ := by
  have hrel := h.f.2.1
  cases e : schedulable t σ with
  | true =>
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv e
    exact schedulable_of (h.kold h1) h2 h3 (h.kold h4) h5 (by rw [hrel]; exact h6)
  | false =>
    cases e' : schedulable t σ' with
    | false => rfl
    | true =>
      obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv e'
      rcases h.tcbIn hi h1 with h1' | ⟨-, -, hsc⟩
      · rw [schedulable_of h1' h2 h3 ((h.scIT hi).1 h4) h5 (by rw [← hrel]; exact h6)] at e
        cases e
      · rw [hsc] at h2; cases h2

theorem prioOf_uaddT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) (u : ObjRef) :
    Sched.prioOf σ' u = Sched.prioOf σ u := by
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
        rcases hi u hw with e | e | e | ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, e⟩ <;> rw [e] <;> rfl

theorem Sched.NSC.uaddT {N Nn C : Set U64} (hN : NSC N C σ) (h : SpecAdd σ σ' W o) (hi : IdleNewT W o)
    (hW : ∀ n ∈ Nn, W n.bv) : NSC (N ∪ Nn) C σ' := by
  intro n hn x p hx hp
  rcases h.ntfnBT hi hx with e | ⟨-, rfl⟩
  · rcases hn with hn | hn
    · exact hN n hn x p e hp
    · rw [(h.new _ (hW n hn)).1] at e; cases e
  · cases hp

theorem Sched.CurInv.uaddT (hI : CurInv σ) (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) : CurInv σ' := by
  obtain ⟨-, hrel, hct, -, hcsc, -, -, -, -, -, -, hisc⟩ := h.f
  obtain ⟨xt, hkt, hxs, hnb⟩ := hI.tcb
  obtain ⟨x, n, hx⟩ := hI.sc
  refine ⟨⟨xt, by rw [hct]; exact h.kold hkt, by rw [hcsc]; exact hxs, hnb⟩,
    ⟨x, n, by rw [hcsc]; exact h.kold hx⟩, fun hne y m hy => ?_, by rw [hct, hrel]; exact hI.notRel⟩
  rw [hcsc, hisc] at hne; rw [hcsc] at hy
  exact hI.active hne y m ((h.scIT hi).1 hy)

theorem CurInvW.uaddT (hC : σ.schedulerAction = .chooseNewThread ∨ CurInv σ) (h : SpecAdd σ σ' W o)
    (hi : IdleNewT W o) : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
  rcases hC with e | hI
  · left; rw [h.f.2.2.2.1]; exact e
  · right; exact hI.uaddT h hi

theorem Sched.OffOK.uaddT (hO : OffOK σ) (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) : OffOK σ' := by
  obtain ⟨-, -, -, -, hcsc, htime, hcons, -, -, -, -, hisc⟩ := h.f
  intro hc y n hy ha
  rw [hcons] at hc ⊢; rw [htime]
  rw [hcsc] at hy; rw [hcsc, hisc] at ha
  exact hO hc y n ((h.scIT hi).1 hy) ha

theorem Sched.ActIdle.uaddT (hA : ActIdle σ) (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) : ActIdle σ' := by
  obtain ⟨-, hrel, -, hact, -, -, -, -, -, -, hidle, hisc⟩ := h.f
  obtain ⟨hS, x, hx, h1, h2, h3⟩ := hA
  refine ⟨fun t ht => ?_, x, by rw [hidle]; exact h.kold hx, by rw [hisc]; exact h1, h2,
    by rw [hidle, hrel]; exact h3⟩
  rw [hact] at ht
  rw [h.sched_eqT hi]; exact hS t ht

theorem Sched.CurOwnW.uaddT {T C : Set U64} (hO : CurOwnW T C σ) (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) :
    CurOwnW T C σ' := by
  obtain ⟨-, hrel, -, -, hcsc, -, hcons, -, -, -, -, -⟩ := h.f
  rcases hO with ⟨u, hu, xt, hkt, hxs, hown, hnr⟩ | ⟨⟨sc, hsc, hb⟩, hun⟩
  · refine Or.inl ⟨u, hu, xt, h.kold hkt, by rw [hcsc]; exact hxs, fun y n hy => ?_, fun h0 hm => ?_⟩
    · rw [hcsc] at hy; exact hown y n ((h.scIT hi).1 hy)
    · rw [hcons] at h0; rw [hrel] at hm; exact hnr h0 hm
  · refine Or.inr ⟨⟨sc, hsc, by rw [hcsc]; exact hb⟩, fun y n hy => ?_⟩
    rw [hcsc] at hy; exact hun y n ((h.scIT hi).1 hy)

theorem Sched.IpcSorted.uaddT (hS : IpcSorted σ) (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) : IpcSorted σ' := by
  refine ⟨fun p x hp => ?_, fun p x hp => ?_⟩
  · rcases h.epBT hi hp with e | rfl
    · exact (hS.1 p x e).congr fun u _ => prioOf_uaddT h hi u
    · exact List.Pairwise.nil
  · rcases h.ntfnBT hi hp with e | ⟨-, rfl⟩
    · exact (hS.2 p x e).congr fun u _ => prioOf_uaddT h hi u
    · exact List.Pairwise.nil

/-- `CurRunM` across `SpecAdd`, the current thread not a new one. -/
theorem CurRunM.uaddT (hR : CurRunM σ) (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) (hcW : ¬ W σ.curThread) :
    CurRunM σ' := by
  obtain ⟨-, -, hct, hact, -, -, -, -, -, -, hidle, -⟩ := h.f
  rcases hR with e | e
  · left; rw [hact]; exact e
  · right
    rcases e with r | r
    · left; intro y hy; rw [hct] at hy
      rcases h.tcbIn hi hy with hy' | ⟨hw, -⟩
      · exact r y hy'
      · exact absurd hw hcW
    · right; rw [hct, hidle]; exact r

/-- `RecvB` back across `SpecAdd` (a new TCB is inactive, a new reply free). -/
theorem Sched.SpecAdd.recvBT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) {d : U64} (hd : RecvB σ' d) : RecvB σ d := by
  obtain ⟨x, t, xt, h1, h2, h3, h4⟩ := hd
  rcases h.replyBT hi h1 with e | ⟨-, rfl⟩
  · rcases h.tcbIn hi h3 with e3 | ⟨-, hst, -⟩
    · exact ⟨x, t, xt, e, h2, e3, h4⟩
    · rw [hst] at h4; cases h4
  · cases h2

/-! ### Across `SpecAdd` then a `CnStep` -/

theorem uaCKeepT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) (hC : CnStep σ' σ'') : Sched.CKeep σ σ'' :=
  ⟨fun q y n hq => ⟨y, hC.sc.2 (h.kold hq), rfl⟩,
    fun q x hq => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 (h.kold hq), rfl, rfl⟩,
    fun p x n hp => ⟨x, (h.scIT hi).1 (hC.sc.1 hp)⟩⟩

theorem uaYKeepT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) (hC : CnStep σ' σ'') : YKeep σ σ'' :=
  ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF (h.kold hp); ⟨y, hy, hc.yld⟩,
    fun p x n hp => ⟨x, hC.sc.2 (h.kold hp), rfl⟩,
    fun p y n hp => ⟨y, (h.scIT hi).1 (hC.sc.1 hp), rfl⟩⟩

theorem uaMcpKeepT (h : SpecAdd σ σ' W o) (hC : CnStep σ' σ'') : McpKeep σ σ'' :=
  fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF (h.kold hp); ⟨y, hy, hc.mcp⟩

theorem uaBufKeepT (h : SpecAdd σ σ' W o) (hC : CnStep σ' σ'') :
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ''.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
  fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF (h.kold hp); ⟨y, hy, hc.buf⟩

theorem uaRecvBT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) (hC : CnStep σ' σ'') {d : U64} (hd : RecvB σ'' d) :
    RecvB σ d :=
  h.recvBT hi (hC.toHStep.khrb.recvB hd)

theorem Sched.RRecv.uaddT {R : Set U64} {m m' : U64 → U64} (hR : RRecv m R σ) (h : SpecAdd σ σ' W o)
    (hi : IdleNewT W o) (hC : CnStep σ' σ'')
    (hm : ∀ d ∈ R, m' (rPrevA d) = m (rPrevA d) ∧ m' (rNextA d) = m (rNextA d)) :
    RRecv m' R σ'' := fun d hd hr => by
  obtain ⟨h1, h2⟩ := hR d hd (uaRecvBT h hi hC hr)
  exact ⟨(hm d hd).2.trans h1, (hm d hd).1.trans h2⟩

theorem uaSzKeepT (h : SpecAdd σ σ' W o) (hi : IdleNewT W o) (hC : CnStep σ' σ'') : SzKeep σ σ'' := by
  intro p x n hp
  exact ⟨x, (h.scIT hi).1 (hC.sc.1 hp)⟩

end Spec

end

end Fl4Proofs.P3

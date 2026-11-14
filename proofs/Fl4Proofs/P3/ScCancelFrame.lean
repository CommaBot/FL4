/-
P3 (DESIGN.md §9), scheduling contexts: **what the spec's `cancel_all_ipc`
keeps** of the scheduler side, for the fault-handler install over a final
endpoint cap (`FinEpSpecHyp`).

* `Fr SR ER`: a frame of the heap and the scheduler queues, with the
  threads' states related by `SR` and the endpoints by `ER`: TCBs stay TCBs
  with their SC, SCs stay SCs with their TCB and non-empty refills,
  notifications are kept, a new ready-queue member has an SC, the release
  queue and the current thread are kept. `PF SR ER m`: every outcome of
  `m` is `Fr`; combinators.
* `cancelAllIpc_fr`: `cancel_all_ipc e` is `Fr` with the states kept,
  restarted or made inactive and `e`'s queue shrinking, keeps the target's
  membership in `e`'s queue when it is blocked on `e` (`Kp`), and ends with
  the state unchanged or the scheduler action `choose_new_thread`.
-/
import Fl4Proofs.P3.ScInstSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Classical

noncomputable section

section Spec
open Fl4Spec

/-- The frame (module docstring). -/
structure Fr (SR : ThreadState → ThreadState → Prop) (ER : ObjRef → Endpoint → Endpoint → Prop)
    (σ σ' : State Unit) : Prop where
  tcb : ∀ u x, σ.kheap u = some (.tcb x) → ∃ y, σ'.kheap u = some (.tcb y) ∧ SR x.tcbState y.tcbState ∧
    y.tcbSchedContext = x.tcbSchedContext ∧ tcbCnodeMap y = tcbCnodeMap x
  tcb' : ∀ u y, σ'.kheap u = some (.tcb y) → ∃ x, σ.kheap u = some (.tcb x)
  sc : ∀ c y n, σ.kheap c = some (.schedContext y n) → ∃ y', σ'.kheap c = some (.schedContext y' n) ∧
    y'.scTcb = y.scTcb ∧ (y.scRefills ≠ [] → y'.scRefills ≠ [])
  ep : ∀ e ep, σ.kheap e = some (.endpoint ep) → ∃ ep', σ'.kheap e = some (.endpoint ep') ∧ ER e ep ep'
  ntfn : ∀ n x, σ.kheap n = some (.notification x) → σ'.kheap n = some (.notification x)
  cn : ∀ u a b, σ.kheap u = some (.cnode a b) → σ'.kheap u = some (.cnode a b)
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  rq : ∀ d pr u, u ∈ σ'.readyQueues d pr → u ∈ σ.readyQueues d pr ∨
    ∃ x c, σ'.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some c
  rel : σ'.releaseQueue = σ.releaseQueue
  ct : σ'.curThread = σ.curThread

/-- The state relation is a preorder. -/
structure FrOK (SR : ThreadState → ThreadState → Prop) (ER : ObjRef → Endpoint → Endpoint → Prop) : Prop where
  sr : ∀ a, SR a a
  srt : ∀ a b c, SR a b → SR b c → SR a c
  er : ∀ e a, ER e a a
  ert : ∀ e a b c, ER e a b → ER e b c → ER e a c

theorem Fr.refl {SR ER} (h : FrOK SR ER) (σ : State Unit) : Fr SR ER σ σ :=
  ⟨fun _ x hx => ⟨x, hx, h.sr _, rfl, rfl⟩, fun _ y hy => ⟨y, hy⟩, fun _ y _ hy => ⟨y, hy, rfl, id⟩,
    fun e ep he => ⟨ep, he, h.er e ep⟩, fun _ _ h => h, fun _ _ _ h => h, rfl, rfl, fun _ _ _ hu => Or.inl hu,
    rfl, rfl⟩

theorem Fr.trans {SR ER} (h : FrOK SR ER) {σ1 σ2 σ3 : State Unit} (h1 : Fr SR ER σ1 σ2) (h2 : Fr SR ER σ2 σ3) :
    Fr SR ER σ1 σ3 := by
  refine ⟨fun u x hx => ?_, fun u y hy => ?_, fun c y n hy => ?_, fun e ep he => ?_,
    fun n x hn => h2.ntfn n x (h1.ntfn n x hn), fun u a b hu => h2.cn u a b (h1.cn u a b hu),
    h2.cdt.trans h1.cdt, h2.orig.trans h1.orig, fun d pr u hu => ?_, h2.rel.trans h1.rel, h2.ct.trans h1.ct⟩
  · obtain ⟨y, hy, s1, c1, m1⟩ := h1.tcb u x hx
    obtain ⟨z, hz, s2, c2, m2⟩ := h2.tcb u y hy
    exact ⟨z, hz, h.srt _ _ _ s1 s2, c2.trans c1, m2.trans m1⟩
  · obtain ⟨x, hx⟩ := h2.tcb' u y hy; exact h1.tcb' u x hx
  · obtain ⟨y', hy', t1, n1⟩ := h1.sc c y n hy
    obtain ⟨y'', hy'', t2, n2⟩ := h2.sc c y' n hy'
    exact ⟨y'', hy'', t2.trans t1, fun h0 => n2 (n1 h0)⟩
  · obtain ⟨ep', he', r1⟩ := h1.ep e ep he
    obtain ⟨ep'', he'', r2⟩ := h2.ep e ep' he'
    exact ⟨ep'', he'', h.ert _ _ _ _ r1 r2⟩
  · rcases h2.rq d pr u hu with h3 | ⟨x, c, hx, hc⟩
    · rcases h1.rq d pr u h3 with h4 | ⟨x, c, hx, hc⟩
      · exact Or.inl h4
      · obtain ⟨y, hy, -, hs, -⟩ := h2.tcb u x hx
        exact Or.inr ⟨y, c, hy, by rw [hs, hc]⟩
    · exact Or.inr ⟨x, c, hx, hc⟩

theorem Fr.mono {SR SR' ER ER'} {σ σ' : State Unit} (h : Fr SR ER σ σ') (hs : ∀ a b, SR a b → SR' a b)
    (he : ∀ e a b, ER e a b → ER' e a b) : Fr SR' ER' σ σ' := by
  refine ⟨fun u x hx => ?_, h.tcb', h.sc, fun e ep h' => ?_, h.ntfn, h.cn, h.cdt, h.orig, h.rq, h.rel, h.ct⟩
  · obtain ⟨y, hy, s, c, m⟩ := h.tcb u x hx; exact ⟨y, hy, hs _ _ s, c, m⟩
  · obtain ⟨ep', h1, h2⟩ := h.ep e ep h'; exact ⟨ep', h1, he _ _ _ h2⟩

/-- A state change keeping the heap, the CDT, the original flags, the ready
queues, the release queue and the current thread. -/
theorem Fr.of_eq {SR ER} (h : FrOK SR ER) {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap)
    (hd : σ'.cdt = σ.cdt) (ho : σ'.isOriginalCap = σ.isOriginalCap)
    (hq : σ'.readyQueues = σ.readyQueues) (hr : σ'.releaseQueue = σ.releaseQueue)
    (hc : σ'.curThread = σ.curThread) : Fr SR ER σ σ' := by
  refine ⟨fun u x hx => ⟨x, by rw [hk]; exact hx, h.sr _, rfl, rfl⟩, fun u y hy => ⟨y, by rw [← hk]; exact hy⟩,
    fun c y n hy => ⟨y, by rw [hk]; exact hy, rfl, id⟩, fun e ep he => ⟨ep, by rw [hk]; exact he, h.er _ _⟩,
    fun n x hn => by rw [hk]; exact hn, fun u a b hu => by rw [hk]; exact hu, hd, ho,
    fun d pr u hu => Or.inl (by rw [← hq]; exact hu), hr, hc⟩

/-- The object changes `Fr` allows. -/
def Compat (SR : ThreadState → ThreadState → Prop) (ER : ObjRef → Endpoint → Endpoint → Prop) (q : ObjRef)
    (o o' : KernelObject) : Prop :=
  (∃ x y, o = .tcb x ∧ o' = .tcb y ∧ SR x.tcbState y.tcbState ∧ y.tcbSchedContext = x.tcbSchedContext ∧
    tcbCnodeMap y = tcbCnodeMap x) ∨
  (∃ y y' n, o = .schedContext y n ∧ o' = .schedContext y' n ∧ y'.scTcb = y.scTcb ∧
    (y.scRefills ≠ [] → y'.scRefills ≠ [])) ∨
  (∃ ep ep', o = .endpoint ep ∧ o' = .endpoint ep' ∧ ER q ep ep') ∨
  (∃ r r', o = .reply r ∧ o' = .reply r')

theorem Fr.upd {SR ER} (h : FrOK SR ER) {σ : State Unit} {q : ObjRef} {o o' : KernelObject}
    (hk : σ.kheap q = some o) (hc : Compat SR ER q o o') :
    Fr SR ER σ { σ with kheap := Function.update σ.kheap q (some o') } := by
  have hkn : ∀ u, u ≠ q → (Function.update σ.kheap q (some o')) u = σ.kheap u :=
    fun u hu => Function.update_of_ne hu _ _
  refine ⟨fun u x hx => ?_, fun u y hy => ?_, fun c y n hy => ?_, fun e ep he => ?_, fun n x hn => ?_,
    fun u a b hu => ?_, rfl, rfl, fun d pr u hu => Or.inl hu, rfl, rfl⟩
  · by_cases e : u = q
    · subst e; rw [hk] at hx; cases hx
      rcases hc with ⟨x', y, e1, rfl, h1, h2, h3⟩ | ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
      exact ⟨y, by simp, h1, h2, h3⟩
    · exact ⟨x, by simp only [hkn u e]; exact hx, h.sr _, rfl, rfl⟩
  · by_cases e : u = q
    · subst e
      rcases hc with ⟨x, y', rfl, rfl, -⟩ | ⟨_, _, _, -, rfl, -⟩ | ⟨_, _, -, rfl, -⟩ | ⟨_, _, -, rfl⟩
      · exact ⟨x, hk⟩
      all_goals simp at hy
    · exact ⟨y, by simp only [hkn u e] at hy; exact hy⟩
  · by_cases e : c = q
    · subst e; rw [hk] at hy; cases hy
      rcases hc with ⟨_, _, e1, -⟩ | ⟨y0, y', n', e1, rfl, h1, h2⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
      exact ⟨y', by simp, h1, h2⟩
    · exact ⟨y, by simp only [hkn c e]; exact hy, rfl, id⟩
  · by_cases e' : e = q
    · subst e'; rw [hk] at he; cases he
      rcases hc with ⟨_, _, e1, -⟩ | ⟨_, _, _, e1, -⟩ | ⟨ep0, ep', e1, rfl, h1⟩ | ⟨_, _, e1, -⟩ <;> cases e1
      exact ⟨ep', by simp, h1⟩
    · exact ⟨ep, by simp only [hkn e e']; exact he, h.er _ _⟩
  · have : n ≠ q := by
      rintro rfl; rw [hk] at hn; cases hn
      rcases hc with ⟨_, _, e1, -⟩ | ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    simp only [hkn n this]; exact hn
  · have : u ≠ q := by
      rintro rfl; rw [hk] at hu; cases hu
      rcases hc with ⟨_, _, e1, -⟩ | ⟨_, _, _, e1, -⟩ | ⟨_, _, e1, -⟩ | ⟨_, _, e1, -⟩ <;> cases e1
    simp only [hkn u this]; exact hu

/-! ### `PF` -/

/-- Every outcome is `Fr`. -/
def PF (SR : ThreadState → ThreadState → Prop) (ER : ObjRef → Endpoint → Endpoint → Prop) {α : Type}
    (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → Fr SR ER σ x.2

variable {SR : ThreadState → ThreadState → Prop} {ER : ObjRef → Endpoint → Endpoint → Prop}

theorem pf_bind (h : FrOK SR ER) {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β}
    (hm : PF SR ER m) (hf : ∀ a, PF SR ER (f a)) : PF SR ER (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans h (hf y.1 y.2 x hx)

theorem pf_pure (h : FrOK SR ER) {α : Type} (a : α) : PF SR ER (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact Fr.refl h σ

theorem pf_pure' (h : FrOK SR ER) {α : Type} (a : α) : PF SR ER (NonDet.pure a : NonDet (State Unit) α) :=
  pf_pure h a

theorem pf_gets (h : FrOK SR ER) {α : Type} (f : State Unit → α) : PF SR ER (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact Fr.refl h σ

theorem pf_assert (h : FrOK SR ER) (P : Prop) : PF SR ER (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact Fr.refl h σ

theorem pf_fail {α : Type} : PF SR ER (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem pf_assertOpt (h : FrOK SR ER) {α : Type} (o : Option α) :
    PF SR ER (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact pf_fail
  · exact pf_pure' h _

theorem pf_getsThe (h : FrOK SR ER) {α : Type} (f : State Unit → Option α) : PF SR ER (NonDet.getsThe f) := by
  intro σ x hx
  exact pf_assertOpt h (f σ) σ x hx

theorem pf_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : PF SR ER m1)
    (h2 : PF SR ER m2) : PF SR ER (if P then m1 else m2) := by
  split <;> assumption

theorem pf_when (h : FrOK SR ER) {P : Prop} {inst : Decidable P} {m : NonDet (State Unit) Unit} (hm : PF SR ER m) :
    PF SR ER (@NonDet.when _ P inst m) := by
  unfold NonDet.when; split; exact hm; exact pf_pure' h _

theorem pf_maybeM (h : FrOK SR ER) {α : Type} {f : α → NonDet (State Unit) Unit} (hf : ∀ a, PF SR ER (f a)) :
    ∀ o, PF SR ER (NonDet.maybeM f o)
  | none => pf_pure' h _
  | some a => hf a

theorem pf_whileLoop (h : FrOK SR ER) {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, PF SR ER (B r)) (r : α) : PF SR ER (NonDet.whileLoop C B r) := by
  intro σ x hx
  change NonDet.WhileResults C B r σ x at hx
  induction hx with
  | done _ => exact Fr.refl h _
  | step _ hb _ ih => exact (hB _ _ _ hb).trans h ih

theorem pf_modify (h : FrOK SR ER) {f : State Unit → State Unit} (hf : ∀ σ, (f σ).kheap = σ.kheap ∧
    (f σ).cdt = σ.cdt ∧ (f σ).isOriginalCap = σ.isOriginalCap ∧
    (f σ).readyQueues = σ.readyQueues ∧ (f σ).releaseQueue = σ.releaseQueue ∧ (f σ).curThread = σ.curThread) :
    PF SR ER (NonDet.modify f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨a, b, c, d, e, g⟩ := hf σ
  exact Fr.of_eq h a b c d e g

theorem pf_threadGet (h : FrOK SR ER) {α : Type} (f : Tcb → α) (t : ObjRef) :
    PF SR ER (threadGet (Z := Unit) f t) := by
  unfold threadGet; exact pf_bind h (pf_getsThe h _) (fun _ => pf_pure h _)

theorem pf_getObject (h : FrOK SR ER) (p : ObjRef) : PF SR ER (getObject (Z := Unit) p) := pf_getsThe h _

theorem pf_getSimpleKo (h : FrOK SR ER) {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) :
    PF SR ER (getSimpleKo (Z := Unit) f p) := by
  unfold getSimpleKo
  refine pf_bind h (pf_getObject h _) (fun _ => pf_bind h (pf_assert h _) (fun _ => ?_))
  split
  · exact pf_pure h _
  · exact pf_fail

theorem pf_getSchedContext (h : FrOK SR ER) (p : ObjRef) : PF SR ER (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext
  refine pf_bind h (pf_getObject h _) (fun o => ?_)
  cases o <;> first | exact pf_pure h _ | exact pf_fail

/-- `set_object` of a compatible object. -/
theorem pf_setObject_at (h : FrOK SR ER) {σ : State Unit} {q : ObjRef} {o o' : KernelObject}
    (hk : σ.kheap q = some o) (hc : Compat SR ER q o o') :
    ∀ x, x ∈ (setObject (Z := Unit) q o' σ).1 → Fr SR ER σ x.2 := by
  intro x hx
  unfold setObject at hx
  rw [nd_bind_one (Notif.getObject_eq hk)] at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hy
  obtain ⟨z, hz, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hz] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact Fr.upd h hk hc

theorem getTcb_some {σ : State Unit} {t : ObjRef} {x : Tcb} (h : getTcb (Z := Unit) t σ = some x) :
    σ.kheap t = some (.tcb x) := by
  unfold getTcb readObject at h
  cases hk : σ.kheap t with
  | none => rw [hk] at h; cases h
  | some o => rw [hk] at h; cases o <;> simp at h; rw [h]

theorem pf_threadSet (h : FrOK SR ER) (f : Tcb → Tcb)
    (hf : ∀ x, SR x.tcbState (f x).tcbState ∧ (f x).tcbSchedContext = x.tcbSchedContext ∧
      tcbCnodeMap (f x) = tcbCnodeMap x) (t : ObjRef) :
    PF SR ER (threadSet (Z := Unit) f t) := by
  intro σ x hx
  unfold threadSet at hx
  obtain ⟨⟨tcb, σa⟩, ha, hx⟩ := hx
  simp only [NonDet.getsThe] at ha
  cases hg : getTcb (Z := Unit) t σ with
  | none => rw [hg] at ha; exact ha.elim
  | some tcb0 =>
    rw [hg] at ha
    obtain ⟨e1, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 ha)
    subst e1
    exact pf_setObject_at h (getTcb_some hg) (Or.inl ⟨_, _, rfl, rfl, (hf _).1, (hf _).2.1, (hf _).2.2⟩) x hx

theorem partialInv_some {α β : Type} [Nonempty α] {f : α → β} {x : β} (h : partialInv f x ≠ none) :
    ∃ y, f y = x := by
  unfold partialInv at h
  split at h
  · rename_i hh; obtain ⟨y, hy, -⟩ := hh; exact ⟨y, hy⟩
  · exact absurd rfl h

/-- `set_simple_ko` of a reply. -/
theorem pf_setReply (h : FrOK SR ER) (r : ObjRef) (v : Reply) :
    PF SR ER (setSimpleKo (Z := Unit) KernelObject.reply r v) := by
  intro σ x hx
  unfold setSimpleKo at hx
  cases hk : σ.kheap r with
  | none =>
    have : getObject (Z := Unit) r σ = (∅, True) := by
      simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt, NonDet.fail]
    rw [nd_bind_apply, this] at hx
    obtain ⟨_, h', _⟩ := hx; exact h'.elim
  | some o =>
    rw [nd_bind_one (Notif.getObject_eq hk)] at hx
    obtain ⟨y, hy, hx⟩ := hx
    obtain ⟨-, rfl⟩ := hy
    obtain ⟨z, hz, hx⟩ := hx
    obtain ⟨hpi, rfl⟩ := hz
    obtain ⟨r0, rfl⟩ := partialInv_some hpi
    exact pf_setObject_at h hk (Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl⟩))) x hx

/-- `update_sched_context` keeping the SC's TCB and non-empty refills. -/
theorem pf_updateSchedContext (h : FrOK SR ER) (p : ObjRef) (g : SchedContext → SchedContext)
    (hg : ∀ y, (g y).scTcb = y.scTcb ∧ (g y).scRefills ≠ []) : PF SR ER (updateSchedContext (Z := Unit) p g) := by
  intro σ x hx
  unfold updateSchedContext at hx
  cases hk : σ.kheap p with
  | none =>
    have : getObject (Z := Unit) p σ = (∅, True) := by
      simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt, NonDet.fail]
    rw [nd_bind_apply, this] at hx
    obtain ⟨_, h', _⟩ := hx; exact h'.elim
  | some o =>
    rw [nd_bind_one (Notif.getObject_eq hk)] at hx
    cases o with
    | schedContext y n =>
      exact pf_setObject_at h hk (Or.inr (Or.inl ⟨_, _, _, rfl, rfl, (hg y).1, fun _ => (hg y).2⟩)) x hx
    | _ => exact hx.elim

theorem pf_updateRefillHd (h : FrOK SR ER) (p : ObjRef) (f : Refill → Refill) :
    PF SR ER (updateRefillHd (Z := Unit) p f) :=
  pf_updateSchedContext h p _ fun _ => ⟨rfl, List.cons_ne_nil _ _⟩

theorem getsThe_state {α : Type} {f : State Unit → Option α} {σ : State Unit} {x : α × State Unit}
    (h : x ∈ (NonDet.getsThe f σ).1) : x.2 = σ := by
  simp only [NonDet.getsThe] at h
  cases e : f σ with
  | none => rw [e] at h; exact h.elim
  | some a => rw [e] at h; rw [Set.mem_singleton_iff.1 h]

/-- The outcome of `update_sched_context`. -/
theorem updSc_out {σ : State Unit} {p : ObjRef} {g : SchedContext → SchedContext} {x : Unit × State Unit}
    (hx : x ∈ (updateSchedContext (Z := Unit) p g σ).1) :
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧
      x.2 = { σ with kheap := Function.update σ.kheap p (some (.schedContext (g y) n)) } := by
  unfold updateSchedContext at hx
  cases hk : σ.kheap p with
  | none =>
    have : getObject (Z := Unit) p σ = (∅, True) := by
      simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt, NonDet.fail]
    rw [nd_bind_apply, this] at hx
    obtain ⟨_, h', _⟩ := hx; exact h'.elim
  | some o =>
    rw [nd_bind_one (Notif.getObject_eq hk)] at hx
    cases o with
    | schedContext y n =>
      refine ⟨y, n, rfl, ?_⟩
      unfold setSchedContext setObject at hx
      dsimp only at hx
      rw [nd_bind_one (Notif.getObject_eq hk)] at hx
      obtain ⟨y1, hy, hx⟩ := hx
      obtain ⟨-, rfl⟩ := hy
      obtain ⟨z, hz, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 hz] at hx
      rw [Set.mem_singleton_iff.1 hx]
    | _ => exact hx.elim

/-- `merge_overlapping_refills`: the head popped, then merged into the new
head. -/
theorem pf_mergeOverlappingRefills (h : FrOK SR ER) (p : ObjRef) :
    PF SR ER (mergeOverlappingRefills (Z := Unit) p) := by
  intro σ x hx
  unfold mergeOverlappingRefills refillPopHead getRefillHead at hx
  obtain ⟨⟨hd, σa⟩, ha, hx⟩ := hx
  obtain ⟨⟨r0, σ0⟩, h0, ha⟩ := ha
  have e0 : σ0 = σ := getsThe_state h0
  subst e0
  obtain ⟨⟨u, σb⟩, hb, hc⟩ := ha
  have eab : σa = σb := (Prod.mk.inj (Set.mem_singleton_iff.1 hc)).2
  subst eab
  obtain ⟨y, n, hk, e1⟩ := updSc_out hb
  simp only at e1
  subst e1
  unfold updateRefillHd at hx
  obtain ⟨y', n', hk', e2⟩ := updSc_out hx
  simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hk'
  obtain ⟨rfl, rfl⟩ := hk'
  rw [e2]
  simp only [Function.update_idem]
  exact Fr.upd h hk (Or.inr (Or.inl ⟨_, _, _, rfl, rfl, rfl, fun _ => List.cons_ne_nil _ _⟩))

/-! ### Reads, and the dependent steps -/

/-- Every outcome keeps the state. -/
def RO {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → x.2 = σ

theorem ro_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : RO m)
    (hf : ∀ a, RO (f a)) : RO (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  rw [hf y.1 y.2 x hx, hm σ y hy]

theorem ro_pure {α : Type} (a : α) : RO (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem ro_gets {α : Type} (f : State Unit → α) : RO (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem ro_getsThe {α : Type} (f : State Unit → Option α) : RO (NonDet.getsThe f) :=
  fun _ _ h => getsThe_state h

theorem ro_assert (P : Prop) : RO (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; rfl

theorem ro_assertOpt {α : Type} (o : Option α) : RO (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · intro σ x hx; exact hx.elim
  · exact ro_pure _

theorem ro_threadGet {α : Type} (f : Tcb → α) (t : ObjRef) : RO (threadGet (Z := Unit) f t) := by
  unfold threadGet; exact ro_bind (ro_getsThe _) fun _ => ro_pure _

theorem threadGet_out {α : Type} {f : Tcb → α} {t : ObjRef} {σ : State Unit} {x : α × State Unit}
    (h : x ∈ (threadGet (Z := Unit) f t σ).1) : x.2 = σ ∧ ∃ tcb, σ.kheap t = some (.tcb tcb) ∧ x.1 = f tcb := by
  unfold threadGet at h
  obtain ⟨⟨tcb, σa⟩, ha, hx⟩ := h
  simp only [NonDet.getsThe] at ha
  cases hg : getTcb (Z := Unit) t σ with
  | none => rw [hg] at ha; exact ha.elim
  | some tcb0 =>
    rw [hg] at ha
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 ha)
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨rfl, _, getTcb_some hg, rfl⟩

theorem pf_ro (h : FrOK SR ER) {α : Type} {m : NonDet (State Unit) α} (hm : RO m) : PF SR ER m := by
  intro σ x hx; rw [hm σ x hx]; exact Fr.refl h σ

/-- After reads, a dependent step. -/
theorem dpf_bind_ro {α β : Type} {P : State Unit → Prop} {m : NonDet (State Unit) α}
    {f : α → NonDet (State Unit) β} (hm : RO m)
    (hf : ∀ a σ, P σ → ∀ x, x ∈ (f a σ).1 → Fr SR ER σ x.2) :
    ∀ σ, P σ → ∀ x, x ∈ ((m >>= f) σ).1 → Fr SR ER σ x.2 := by
  intro σ hP x ⟨y, hy, hx⟩
  have e := hm σ y hy
  rw [e] at hx
  exact hf y.1 σ hP x hx

/-- **Enqueueing a thread with an SC.** -/
theorem fr_enq (h : FrOK SR ER) {σ : State Unit} {t : ObjRef}
    (hsc : ∃ x c, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c) :
    ∀ x, x ∈ (tcbSchedAction (Z := Unit) tcbSchedEnqueue t σ).1 → Fr SR ER σ x.2 := by
  intro x hx
  unfold tcbSchedAction getTcbQueue setTcbQueue at hx
  obtain ⟨⟨d, σ1⟩, h1, hx⟩ := hx
  rw [ro_threadGet _ _ σ _ h1] at hx
  obtain ⟨⟨pr, σ2⟩, h2, hx⟩ := hx
  rw [ro_threadGet _ _ σ _ h2] at hx
  obtain ⟨⟨q, σ3⟩, h3, hx⟩ := hx
  obtain ⟨⟨q0, σ4⟩, h4, h3⟩ := h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h4)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h3)
  obtain ⟨⟨q', σ5⟩, h5, hx⟩ := hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h5)
  rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨xt, c, hkt, hct⟩ := hsc
  refine ⟨fun u x hx => ⟨x, hx, h.sr _, rfl, rfl⟩, fun u y hy => ⟨y, hy⟩, fun c y n hy => ⟨y, hy, rfl, id⟩,
    fun e ep he => ⟨ep, he, h.er _ _⟩, fun n x hn => hn, fun _ _ _ hu => hu, rfl, rfl, fun d' p' u hu => ?_,
    rfl, rfl⟩
  simp only at hu
  split at hu
  · rename_i hdp
    obtain ⟨rfl, rfl⟩ := hdp
    unfold tcbSchedEnqueue at hu
    split at hu
    · rcases List.mem_cons.1 hu with rfl | hu
      · exact Or.inr ⟨xt, c, hkt, hct⟩
      · exact Or.inl hu
    · exact Or.inl hu
  · exact Or.inl hu

theorem pf_setSchedulerAction (h : FrOK SR ER) (a : SchedulerAction) :
    PF SR ER (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; exact pf_modify h fun σ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pf_rescheduleRequired (h : FrOK SR ER) : PF SR ER (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  intro σ x ⟨⟨a, σ1⟩, h1, hx⟩
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
  subst σ1
  simp only at hx
  clear e1 h1
  cases a with
  | switchThread t =>
    dsimp only at hx
    obtain ⟨⟨b, σ2⟩, h2, hx⟩ := hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h2)
    obtain ⟨y, hy, hx⟩ := hx
    refine Fr.trans h ?_ (pf_setSchedulerAction h _ _ x hx)
    unfold NonDet.when at hy
    split at hy
    · rename_i hs
      have hsc : ∃ x c, σ2.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c := by
        obtain ⟨x, c, _, _, hk, hc, -⟩ := schedulable_inv hs
        exact ⟨x, c, hk, hc⟩
      clear hx
      unfold getScRefillSufficient getScRefillReady at hy
      revert y
      refine dpf_bind_ro (P := fun σ => ∃ x c, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c)
        (ro_threadGet _ _) (fun _ => dpf_bind_ro (ro_assertOpt _) fun _ => dpf_bind_ro (ro_getsThe _)
          fun _ => dpf_bind_ro (ro_getsThe _) fun _ => dpf_bind_ro (ro_assert _) fun _ σ hσ => fr_enq h hσ)
        σ2 hsc
    · exact pf_pure' h _ σ2 y hy
  | _ => exact pf_setSchedulerAction h _ _ x hx

/-- A TCB with an SC. -/
def HasSC (σ : State Unit) (t : ObjRef) : Prop := ∃ x c, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c

theorem HasSC.fr {σ σ' : State Unit} {t : ObjRef} (h : HasSC σ t) (hf : Fr SR ER σ σ') : HasSC σ' t := by
  obtain ⟨x, c, hk, hc⟩ := h
  obtain ⟨y, hy, -, hs, -⟩ := hf.tcb t x hk
  exact ⟨y, c, hy, by rw [hs, hc]⟩

theorem pf_possibleSwitchTo (h : FrOK SR ER) (t : ObjRef) : PF SR ER (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef
  intro σ x ⟨⟨sco, σ1⟩, h1, hx⟩
  obtain ⟨e1, tcb, hk, hsco⟩ := threadGet_out h1
  simp only at e1 hsco
  subst σ1
  obtain ⟨⟨b, σ2⟩, h2, hx⟩ := hx
  obtain ⟨-, e2⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h2)
  subst σ2
  simp only at hx
  unfold NonDet.when at hx
  split at hx
  · rename_i hg
    have hsc : HasSC σ t := by
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hg.1
      exact ⟨tcb, c, hk, by rw [← hsco, hc]⟩
    revert x
    refine dpf_bind_ro (P := fun σ => HasSC σ t) (ro_gets _) (fun _ => dpf_bind_ro (ro_threadGet _ _)
      fun _ => dpf_bind_ro (ro_gets _) fun _ σ hσ => ?_) σ hsc
    split
    · exact fr_enq h hσ
    · split
      · intro x ⟨y, hy, hx⟩
        have F := pf_rescheduleRequired h σ y hy
        exact F.trans h (fr_enq h (hσ.fr F) x hx)
      · exact pf_setSchedulerAction h _ σ
  · exact pf_pure' h _ σ x hx

theorem pf_refillUnblockCheck (h : FrOK SR ER) (p : ObjRef) : PF SR ER (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck isRoundRobin getScRefillReady
  refine pf_bind h (pf_bind h (pf_getSchedContext h _) (fun _ => pf_pure h _)) (fun _ =>
    pf_bind h (pf_getsThe h _) (fun _ => pf_when h ?_))
  refine pf_bind h (pf_gets h _) (fun _ => pf_bind h (pf_updateRefillHd h _ _) (fun _ =>
    pf_bind h (pf_modify h (fun σ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)) (fun _ => ?_)))
  unfold refillHeadOverlappingLoop
  exact pf_whileLoop h (fun _ => pf_mergeOverlappingRefills h _) _

theorem pf_ifCondRefillUnblockCheck (h : FrOK SR ER) (o : Option ObjRef) (a b : Option Bool) :
    PF SR ER (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck
  refine pf_maybeM h (fun _ => ?_) _
  exact pf_bind h (pf_getSchedContext h _) (fun _ => pf_bind h (pf_gets h _) (fun _ => pf_bind h (pf_pure h _)
    (fun _ => pf_when h (pf_when h (pf_refillUnblockCheck h _)))))

theorem pf_setThreadStateAct (h : FrOK SR ER) (t : ObjRef) : PF SR ER (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct
  exact pf_bind h (pf_gets h _) (fun _ => pf_bind h (pf_gets h _) (fun _ => pf_bind h (pf_gets h _)
    (fun _ => pf_when h (pf_setSchedulerAction h _))))

theorem pf_setThreadState (h : FrOK SR ER) (t : ObjRef) (ts : ThreadState) (hts : ∀ a, SR a ts) :
    PF SR ER (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact pf_bind h (pf_threadSet h (fun tcb => { tcb with tcbState := ts }) (fun x => ⟨hts _, rfl, rfl⟩) t)
    (fun _ => pf_setThreadStateAct h t)

/-! ### The relations of `cancel_all_ipc` -/

/-- States kept. -/
def SR0 (a b : ThreadState) : Prop := b = a
/-- Endpoints kept. -/
def ER0 (_ : ObjRef) (a b : Endpoint) : Prop := b = a
/-- States kept, restarted or made inactive. -/
def SRr (a b : ThreadState) : Prop := b = a ∨ b = .restart ∨ b = .inactive
/-- Endpoints kept, but `e0`'s queue may shrink. -/
def ERq (e0 : ObjRef) (e : ObjRef) (a b : Endpoint) : Prop :=
  (e = e0 → ∀ u ∈ b.epQueue, u ∈ a.epQueue) ∧ (e ≠ e0 → b = a)

theorem srr_trans (a b c : ThreadState) (h1 : SRr a b) (h2 : SRr b c) : SRr a c := by
  rcases h2 with rfl | rfl | rfl
  · exact h1
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem frOK0 : FrOK SR0 ER0 := ⟨fun _ => rfl, fun _ _ _ h1 h2 => h2.trans h1, fun _ _ => rfl,
  fun _ _ _ _ h1 h2 => h2.trans h1⟩

theorem frOKr0 : FrOK SRr ER0 := ⟨fun _ => Or.inl rfl, srr_trans, fun _ _ => rfl, fun _ _ _ _ h1 h2 => h2.trans h1⟩

theorem frOKrq (e0 : ObjRef) : FrOK SRr (ERq e0) :=
  ⟨fun _ => Or.inl rfl, srr_trans, fun _ _ => ⟨fun _ _ h => h, fun _ => rfl⟩,
    fun _ _ _ _ h1 h2 => ⟨fun e u hu => h1.1 e u (h2.1 e u hu), fun e => (h2.2 e).trans (h1.2 e)⟩⟩

theorem fr_sr0 {σ σ' : State Unit} (h : Fr SR0 ER0 σ σ') : Fr SRr ER0 σ σ' :=
  h.mono (fun _ _ e => Or.inl e) (fun _ _ _ e => e)

theorem fr_er0 {e0 : ObjRef} {σ σ' : State Unit} (h : Fr SRr ER0 σ σ') : Fr SRr (ERq e0) σ σ' :=
  h.mono (fun _ _ e => e) (fun _ _ _ e => by subst e; exact ⟨fun _ _ h => h, fun _ => rfl⟩)

/-- The thread's state after a step keeping states. -/
theorem Fr.state0 {σ σ' : State Unit} (h : Fr SR0 ER σ σ') {t : ObjRef} {y : Tcb}
    (hy : σ'.kheap t = some (.tcb y)) : ∃ z, σ.kheap t = some (.tcb z) ∧ y.tcbState = z.tcbState := by
  obtain ⟨z, hz⟩ := h.tcb' t y hy
  obtain ⟨y', hy', e, -⟩ := h.tcb t z hz
  rw [hy] at hy'; cases hy'
  exact ⟨z, hz, e⟩

/-- After `set_thread_state t ts`, `t` is in state `ts`. -/
theorem setThreadState_st {σ : State Unit} {t : ObjRef} {ts : ThreadState} {x : Unit × State Unit}
    (hx : x ∈ (setThreadState (Z := Unit) t ts σ).1) {y : Tcb} (hy : x.2.kheap t = some (.tcb y)) :
    y.tcbState = ts := by
  unfold setThreadState at hx
  obtain ⟨⟨u, σa⟩, ha, hx⟩ := hx
  obtain ⟨z, hz, ez⟩ := (pf_setThreadStateAct frOK0 t σa x hx).state0 hy
  unfold threadSet at ha
  obtain ⟨⟨tcb, σb⟩, hb, ha⟩ := ha
  have eb : σb = σ := getsThe_state hb
  subst σb
  simp only [NonDet.getsThe] at hb
  cases hg : getTcb (Z := Unit) t σ with
  | none => rw [hg] at hb; exact hb.elim
  | some tcb0 =>
    rw [hg] at hb
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hb)
    simp only at ha
    unfold setObject at ha
    rw [nd_bind_one (Notif.getObject_eq (getTcb_some hg))] at ha
    obtain ⟨y1, hy1, ha⟩ := ha
    obtain ⟨-, rfl⟩ := hy1
    obtain ⟨z1, hz1, ha⟩ := ha
    rw [Set.mem_singleton_iff.1 hz1] at ha
    have eσ := (Prod.mk.inj (Set.mem_singleton_iff.1 ha)).2
    rw [eσ] at hz
    simp at hz
    rw [ez, ← hz]

theorem pf_replyUnlinkTcb (h : FrOK SR ER) (hI : ∀ a, SR a .inactive) (t r : ObjRef) :
    PF SR ER (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState setReplyObjRef updateSkObjRef
  refine pf_bind h (pf_getSimpleKo h _ _) (fun _ => pf_bind h (pf_assert h _) (fun _ =>
    pf_bind h (pf_threadGet h _ _) (fun _ => pf_bind h (pf_assert h _) (fun _ => ?_))))
  exact pf_bind h (pf_bind h (pf_getSimpleKo h _ _) (fun _ => pf_setReply h _ _))
    (fun _ => pf_setThreadState h _ _ hI)

theorem pf_restartThreadIfNoFault (h : FrOK SR ER) (hR : ∀ a, SR a .restart) (hI : ∀ a, SR a .inactive)
    (t : ObjRef) : PF SR ER (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault getTcbObjRef ifSporadicCurScAssertRefillUnblockCheck
  refine pf_bind h (pf_threadGet h _ _) (fun _ => ?_)
  split
  · exact pf_bind h (pf_setThreadState h _ _ hR) (fun _ => pf_bind h (pf_threadGet h _ _) (fun _ =>
      pf_bind h (pf_ifCondRefillUnblockCheck h _ _ _) (fun _ => pf_possibleSwitchTo h _)))
  · exact pf_setThreadState h _ _ hI

/-- After `restart_thread_if_no_fault t`, `t` is restarted or inactive. -/
theorem restartThreadIfNoFault_st {σ : State Unit} {t : ObjRef} {x : Unit × State Unit}
    (hx : x ∈ (restartThreadIfNoFault (Z := Unit) t σ).1) {y : Tcb} (hy : x.2.kheap t = some (.tcb y)) :
    y.tcbState = .restart ∨ y.tcbState = .inactive := by
  unfold restartThreadIfNoFault getTcbObjRef ifSporadicCurScAssertRefillUnblockCheck at hx
  obtain ⟨⟨f, σ1⟩, h1, hx⟩ := hx
  have e1 : σ1 = σ := ro_threadGet _ _ σ _ h1
  subst σ1
  simp only at hx
  split at hx
  · obtain ⟨⟨u, σa⟩, ha, hx⟩ := hx
    have F : Fr SR0 ER0 σa x.2 := (pf_bind frOK0 (pf_threadGet frOK0 _ _) (fun _ =>
      pf_bind frOK0 (pf_ifCondRefillUnblockCheck frOK0 _ _ _) (fun _ => pf_possibleSwitchTo frOK0 _))) σa x hx
    obtain ⟨z, hz, ez⟩ := F.state0 hy
    rw [ez, setThreadState_st ha hz]; exact Or.inl rfl
  · exact Or.inr (setThreadState_st hx hy)

theorem getEndpoint_mem {σ : State Unit} {e : ObjRef} {x : Endpoint × State Unit}
    (hx : x ∈ (getEndpoint (Z := Unit) e σ).1) : σ.kheap e = some (.endpoint x.1) ∧ x.2 = σ := by
  unfold getEndpoint getSimpleKo at hx
  obtain ⟨⟨o, σ1⟩, h1, hx⟩ := hx
  have e1 : σ1 = σ := getsThe_state h1
  subst σ1
  have hko : σ.kheap e = some o := by
    simp only [getObject, NonDet.getsThe, readObject] at h1
    cases hk : σ.kheap e with
    | none => rw [hk] at h1; exact h1.elim
    | some v => rw [hk] at h1; rw [(Prod.mk.inj (Set.mem_singleton_iff.1 h1)).1]
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hy
  simp only at hx
  revert hx
  cases hpi : partialInv KernelObject.endpoint o with
  | none => intro hx; exact hx.elim
  | some a =>
    intro hx
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨by rw [hko, ← partialInv_eq hpi], rfl⟩

/-- **`tcb_ep_dequeue t e`**: `e`'s queue loses `t`, all else kept. -/
theorem tcbEpDequeue_out {σ : State Unit} {t e : ObjRef} {x : Unit × State Unit}
    (hx : x ∈ (tcbEpDequeue (Z := Unit) t e σ).1) :
    ∃ ep ep', σ.kheap e = some (.endpoint ep) ∧ t ∈ ep.epQueue ∧ ep'.epQueue = removeAll t ep.epQueue ∧
      x.2 = { σ with kheap := Function.update σ.kheap e (some (.endpoint ep')) } := by
  unfold tcbEpDequeue at hx
  obtain ⟨⟨ep, σ1⟩, h1, hx⟩ := hx
  obtain ⟨hk, e1⟩ := getEndpoint_mem h1
  simp only at hk e1
  subst σ1
  obtain ⟨⟨q, σ2⟩, h2, hx⟩ := hx
  obtain ⟨e2, e2'⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h2)
  simp only at e2 e2'
  subst q σ2
  obtain ⟨⟨u, σ3⟩, h3, hx⟩ := hx
  obtain ⟨hq, h3'⟩ := h3
  obtain ⟨-, e3⟩ := Prod.mk.inj h3'
  simp only at e3
  subst σ3
  obtain ⟨⟨q', σ4⟩, h4, hx⟩ := hx
  obtain ⟨e4, e4'⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h4)
  simp only at e4 e4'
  subst q' σ4
  obtain ⟨⟨ep', σ5⟩, h5, hx⟩ := hx
  obtain ⟨e5, e5'⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h5)
  simp only at e5 e5'
  subst σ5
  simp only at hx hq
  refine ⟨ep, ep', hk, hq, ?_, ?_⟩
  · rw [e5]
    split
    · rename_i hnil; rw [hnil]; rfl
    · cases ep <;> rfl
  · rw [Endp.setEndpoint_eq _ hk] at hx
    rw [Set.mem_singleton_iff.1 hx]; rfl

theorem removeAll_mem {t u : ObjRef} {q : List ObjRef} : u ∈ removeAll t q ↔ u ∈ q ∧ u ≠ t := by
  unfold removeAll
  simp only [List.mem_filter, decide_eq_true_eq, ne_eq]
  exact ⟨fun ⟨a, b⟩ => ⟨a, fun e => b e.symm⟩, fun ⟨a, b⟩ => ⟨a, fun e => b e.symm⟩⟩

theorem pf_tcbEpDequeue (t e : ObjRef) : PF SRr (ERq e) (tcbEpDequeue (Z := Unit) t e) := by
  intro σ x hx
  obtain ⟨ep, ep', hk, -, hq, hx2⟩ := tcbEpDequeue_out hx
  rw [hx2]
  refine Fr.upd (frOKrq e) hk (Or.inr (Or.inr (Or.inl ⟨ep, ep', rfl, rfl, fun _ u hu => ?_, fun h => absurd rfl h⟩)))
  rw [hq] at hu; exact (removeAll_mem.1 hu).1

theorem pf_mapMx (h : FrOK SR ER) {α β : Type} {f : α → NonDet (State Unit) β} (hf : ∀ a, PF SR ER (f a)) :
    ∀ l, PF SR ER (NonDet.mapMx f l)
  | [] => pf_pure' h _
  | a :: l => pf_bind h (hf a) (fun _ => pf_mapMx h hf l)

/-- The rest of `remove_and_restart_ep_queued_thread` after the dequeue. -/
theorem pf_rarTail (t e : ObjRef) : PF SRr ER0 (do
    let st ← getThreadState (Z := Unit) t
    let replyOpt ← pure (if isBlockedOnReceive st then replyObject st else none)
    NonDet.maybeM (replyUnlinkTcb t) replyOpt
    restartThreadIfNoFault t) := by
  unfold getThreadState
  exact pf_bind frOKr0 (pf_threadGet frOKr0 _ _) (fun _ => pf_bind frOKr0 (pf_pure frOKr0 _) (fun _ =>
    pf_bind frOKr0 (pf_maybeM frOKr0 (fun _ => pf_replyUnlinkTcb frOKr0 (fun _ => Or.inr (Or.inr rfl)) _ _) _)
      (fun _ => pf_restartThreadIfNoFault frOKr0 (fun _ => Or.inr (Or.inl rfl)) (fun _ => Or.inr (Or.inr rfl)) _)))

theorem pf_removeAndRestart (t e : ObjRef) :
    PF SRr (ERq e) (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread
  intro σ x ⟨y, hy, hx⟩
  exact (pf_tcbEpDequeue t e σ y hy).trans (frOKrq e) (fr_er0 (pf_rarTail t e y.2 x hx))

/-- **The target's membership in `e`'s queue when it is blocked on `e`.** -/
def Kp (e p : ObjRef) (σ : State Unit) : Prop :=
  ∀ x, σ.kheap p = some (.tcb x) → epBlocked x.tcbState = some e →
    ∃ ep, σ.kheap e = some (.endpoint ep) ∧ p ∈ ep.epQueue

theorem Kp.fr0 {e p : ObjRef} {σ σ' : State Unit} (h : Kp e p σ) (hf : Fr SR0 ER0 σ σ') : Kp e p σ' := by
  intro x hx hb
  obtain ⟨z, hz, ez⟩ := hf.state0 hx
  rw [ez] at hb
  obtain ⟨ep, hk, hm⟩ := h z hz hb
  obtain ⟨ep', hk', e'⟩ := hf.ep e ep hk
  exact ⟨ep', hk', by rw [e']; exact hm⟩

theorem kp_removeAndRestart {t e p : ObjRef} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (removeAndRestartEpQueuedThread (Z := Unit) t e σ).1) (hK : Kp e p σ) : Kp e p x.2 := by
  unfold removeAndRestartEpQueuedThread at hx
  obtain ⟨⟨u, σa⟩, ha, hx⟩ := hx
  obtain ⟨ep, ep', hk, -, hq, hσa⟩ := tcbEpDequeue_out ha
  simp only at hσa
  have F := pf_rarTail t e σa x hx
  -- `t`'s final state
  have hfin : ∀ y, x.2.kheap t = some (.tcb y) → y.tcbState = .restart ∨ y.tcbState = .inactive := by
    intro y hy
    unfold getThreadState at hx
    obtain ⟨⟨st, σb⟩, hb, hx⟩ := hx
    obtain ⟨⟨ro, σc⟩, hc, hx⟩ := hx
    obtain ⟨⟨w, σd⟩, hd, hx⟩ := hx
    exact restartThreadIfNoFault_st hx hy
  intro xp hxp hb
  obtain ⟨z, hz⟩ := F.tcb' p xp hxp
  obtain ⟨y', hy', sr, -⟩ := F.tcb p z hz
  rw [hxp] at hy'; cases hy'
  have hst : xp.tcbState = z.tcbState := by
    rcases sr with e1 | e1 | e1
    · exact e1
    · rw [e1] at hb; simp [epBlocked] at hb
    · rw [e1] at hb; simp [epBlocked] at hb
  have hpe : p ≠ e := by
    rintro rfl; rw [hσa] at hz; simp at hz
  have hz0 : σ.kheap p = some (.tcb z) := by
    rw [hσa] at hz; simpa [Function.update_of_ne hpe] using hz
  rw [hst] at hb
  obtain ⟨ep0, hk0, hm⟩ := hK z hz0 hb
  rw [hk] at hk0; cases hk0
  have hpt : p ≠ t := by
    rintro rfl
    rcases hfin xp hxp with e1 | e1 <;> rw [← hst, e1] at hb <;> simp [epBlocked] at hb
  have hka : σa.kheap e = some (.endpoint ep') := by rw [hσa]; simp
  obtain ⟨ep'', hk'', e''⟩ := F.ep e ep' hka
  refine ⟨ep'', hk'', ?_⟩
  rw [e'', hq]
  exact removeAll_mem.2 ⟨hm, hpt⟩

theorem kp_mapMx {e p : ObjRef} : ∀ (l : List ObjRef) {σ : State Unit} {x : Unit × State Unit},
    x ∈ (NonDet.mapMx (fun t => removeAndRestartEpQueuedThread (Z := Unit) t e) l σ).1 → Kp e p σ → Kp e p x.2
  | [], σ, x, hx, hK => by
    have : x.2 = σ := ro_pure () σ x hx
    rw [this]; exact hK
  | a :: l, σ, x, hx, hK => by
    obtain ⟨y, hy, hx⟩ := hx
    exact kp_mapMx l hx (kp_removeAndRestart hy hK)

theorem resched_choose {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (rescheduleRequired (Z := Unit) σ).1) : x.2.schedulerAction = .chooseNewThread := by
  unfold rescheduleRequired at hx
  obtain ⟨⟨a, σ1⟩, h1, hx⟩ := hx
  simp only at hx
  have hs : ∀ σ2, x ∈ (setSchedulerAction (Z := Unit) .chooseNewThread σ2).1 →
      x.2.schedulerAction = .chooseNewThread := by
    intro σ2 h; unfold setSchedulerAction at h; rw [Set.mem_singleton_iff.1 h]
  cases a with
  | switchThread t =>
    dsimp only at hx
    obtain ⟨_, _, hx⟩ := hx
    obtain ⟨y, -, hx⟩ := hx
    exact hs _ hx
  | _ => exact hs _ hx

/-- **What `cancel_all_ipc e` keeps** (module docstring). -/
theorem cancelAllIpc_fr (e : ObjRef) {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (cancelAllIpc (Z := Unit) e σ).1) :
    Fr SRr (ERq e) σ x.2 ∧ (∀ p, Kp e p σ → Kp e p x.2) ∧
      (x.2 = σ ∨ x.2.schedulerAction = .chooseNewThread) := by
  unfold cancelAllIpc at hx
  obtain ⟨⟨ep, σ1⟩, h1, hx⟩ := hx
  have e1 : σ1 = σ := (getEndpoint_mem h1).2
  subst σ1
  try simp only at hx
  split at hx
  · have : x.2 = σ := ro_pure () σ x hx
    rw [this]; exact ⟨Fr.refl (frOKrq e) σ, fun _ h => h, Or.inl rfl⟩
  · obtain ⟨⟨q, σ2⟩, h2, hx⟩ := hx
    have e2 : σ2 = σ := (Prod.mk.inj (Set.mem_singleton_iff.1 h2)).2
    subst σ2
    obtain ⟨⟨w, σ3⟩, h3, hx⟩ := hx
    have F3 := pf_mapMx (frOKrq e) (fun t => pf_removeAndRestart t e) _ σ _ h3
    have F4 := pf_rescheduleRequired frOK0 σ3 x hx
    refine ⟨F3.trans (frOKrq e) (fr_er0 (fr_sr0 F4)), fun p hK => (kp_mapMx _ h3 hK).fr0 F4,
      Or.inr (resched_choose hx)⟩

/-! ### `SpecPost` across `cancel_all_ipc` -/

theorem Endpoint.ne_idle_of_mem {ep : Endpoint} {p : ObjRef} (h : p ∈ ep.epQueue) : ep ≠ .idleEP := by
  rintro rfl; simp [Endpoint.epQueue] at h

/-- **`SpecPost` across `cancel_all_ipc e`** (`cancelAllIpc_fr`). -/
theorem SpecPost.cancel {σ σ' : State Unit} {p e : ObjRef} {sco : Option (Option ObjRef)} (h : SpecPost σ p sco)
    (F : Fr SRr (ERq e) σ σ') (hK : Kp e p σ → Kp e p σ') (hact : σ' = σ ∨ σ'.schedulerAction = .chooseNewThread) :
    SpecPost σ' p sco := by
  rcases hact with rfl | hact
  · exact h
  obtain ⟨x, hk, -, hQ, hIn, hU, hB⟩ := h
  have hK0 : Kp e p σ := fun x' hx' hb => by rw [hk] at hx'; cases hx'; exact hIn e hb
  have hK1 := hK hK0
  have hA' : Notif.ActReady σ' := fun t ht => by rw [hact] at ht; cases ht
  have htcb : ∀ u, (∃ xu, σ.kheap u = some (.tcb xu)) → ∃ xu, σ'.kheap u = some (.tcb xu) := by
    rintro u ⟨xu, hu⟩
    obtain ⟨y, hy, -⟩ := F.tcb u xu hu
    exact ⟨y, hy⟩
  obtain ⟨y, hy, sr, hsc, -⟩ := F.tcb p x hk
  have hQIn : BlkQ σ' p y.tcbState ∧ BlkIn σ' p y.tcbState := by
    rcases sr with est | est | est
    · rw [est]
      obtain ⟨hE, hN⟩ := hQ
      refine ⟨⟨fun e' he' => ?_, fun n hn => ?_⟩, fun e' he' => ?_⟩
      · obtain ⟨ep, hke, h1, h2, h3⟩ := hE e' he'
        obtain ⟨ep', hke', r⟩ := F.ep e' ep hke
        by_cases ee : e' = e
        · subst ee
          obtain ⟨ep2, hk2, hm2⟩ := hK1 y hy (by rw [est]; exact he')
          rw [hke'] at hk2; cases hk2
          refine ⟨ep', hke', Endpoint.ne_idle_of_mem hm2, List.ne_nil_of_mem hm2, fun u hu hup => ?_⟩
          exact htcb u (h3 u (r.1 rfl u hu) hup)
        · rw [r.2 ee] at hke'
          exact ⟨ep, hke', h1, h2, fun u hu hup => htcb u (h3 u hu hup)⟩
      · obtain ⟨xn, hkn, h1, h2, h3⟩ := hN n hn
        exact ⟨xn, F.ntfn _ _ hkn, h1, h2, fun u hu hup => htcb u (h3 u hu hup)⟩
      · by_cases ee : e' = e
        · subst ee; exact hK1 y hy (by rw [est]; exact he')
        · obtain ⟨ep, hke, hm⟩ := hIn e' he'
          obtain ⟨ep', hke', r⟩ := F.ep e' ep hke
          rw [r.2 ee] at hke'
          exact ⟨ep, hke', hm⟩
    all_goals rw [est]; exact ⟨⟨fun e' he' => by simp [epBlocked] at he', fun n hn => by simp [ntfnBlocked] at hn⟩,
      fun e' he' => by simp [epBlocked] at he'⟩
  refine ⟨y, hy, hA', hQIn.1, hQIn.2, fun e1 => ?_, fun v ev => ?_⟩
  · obtain ⟨c, z, n, h1, h2, h3⟩ := hU e1
    obtain ⟨z', hz', t', -⟩ := F.sc c z n h2
    exact ⟨c, z', n, by rw [hsc, h1], hz', by rw [t', h3]⟩
  · obtain ⟨x0, yv, n, hkt, hxs, hkc, hyt, hne, hnot, hrq, hnc, hrel, -⟩ := hB v ev
    rw [hk] at hkt; cases hkt
    obtain ⟨yv', hkc', t', n'⟩ := F.sc v yv n hkc
    refine ⟨y, yv', n, hy, by rw [hsc, hxs], hkc', by rw [t', hyt], n' hne, fun u xu hu => ?_, fun d pr hm => ?_,
      by rw [F.ct]; exact hnc, fun u hu => ?_, hA'⟩
    · obtain ⟨x1, hx1⟩ := F.tcb' u xu hu
      obtain ⟨y1, hy1, -, hs1, -⟩ := F.tcb u x1 hx1
      rw [hu] at hy1; cases hy1
      rw [hs1]; exact hnot u x1 hx1
    · rcases F.rq d pr p hm with h0 | ⟨x2, c2, hx2, hc2⟩
      · exact hrq d pr h0
      · rw [hy] at hx2; cases hx2
        rw [hsc, hxs] at hc2; cases hc2
    · rw [F.rel] at hu
      obtain ⟨xu, cu, yu, nu, h1, h2, h3, h4⟩ := hrel u hu
      obtain ⟨xu', h1', -, h2', -⟩ := F.tcb u xu h1
      obtain ⟨yu', h3', -, h4'⟩ := F.sc cu yu nu h3
      exact ⟨xu', cu, yu', nu, h1', by rw [h2', h2], h3', h4' h4⟩

/-! ### The spec's `cap_delete` of a slot holding an endpoint cap -/

/-- `SpecPost` of every thread is kept. -/
def Post (σ σ' : State Unit) : Prop := ∀ p sco, SpecPost σ p sco → SpecPost σ' p sco

theorem bindE_mem_inv {σ ε α β : Type} {m : NonDetE σ ε α} {f : α → NonDetE σ ε β} {s : σ}
    {x : Except ε β × σ} (hx : x ∈ ((m >>= f).run s).1) :
    ∃ z ∈ (m.run s).1, (∃ a, z.1 = .ok a ∧ x ∈ ((f a).run z.2).1) ∨ (∃ e, z.1 = .error e ∧ x = (.error e, z.2)) := by
  rw [ExceptT.run_bind] at hx
  obtain ⟨z, hz, hxz⟩ := hx
  refine ⟨z, hz, ?_⟩
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok a => exact Or.inl ⟨a, rfl, hxz⟩
  | error e => exact Or.inr ⟨e, rfl, Set.mem_singleton_iff.1 hxz⟩

theorem liftE_mem_inv' {σ ε α : Type} {m : NonDet σ α} {s : σ} {y : Except ε α × σ}
    (h : y ∈ ((NonDetE.liftE (ε := ε) m).run s).1) : ∃ x ∈ (m s).1, y = (.ok x.1, x.2) := by
  unfold NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨x, hx, Set.mem_singleton_iff.1 hy⟩

theorem psk_emptySlot_null (sl : CslotPtr) : PSK (emptySlot (Z := Unit) sl .nullCap) := by
  unfold emptySlot postCapDeletion
  repeat (first | exact psk_getCap _ | exact psk_setCap _ _ | exact psk_doExtendedOp _ | exact psk_setCdt _ |
    exact psk_setOriginal _ _ | exact psk_pure _ | exact psk_pure' _ | exact psk_gets _ |
    (refine psk_bind ?_ (fun _ => ?_)) | (apply psk_ite))

/-- What a `rec_del` call keeps when its slot holds an endpoint cap. -/
def QD (sl : CslotPtr) : RecDelCall → State Unit → Except Unit (Bool × Cap) × State Unit → Prop
  | .finaliseSlotCall sl' _, σ, x => sl' = sl → (∃ e b R, getCap (Z := Unit) sl σ = ({(.endpointCap e b R, σ)}, False)) →
      x.1 = .ok (true, .nullCap) ∧ Post σ x.2
  | .cTEDeleteCall sl' _, σ, x => sl' = sl → (∃ e b R, getCap (Z := Unit) sl σ = ({(.endpointCap e b R, σ)}, False)) →
      ∀ v, x.1 = .ok v → Post σ x.2
  | .reduceZombieCall _ _ _, _, _ => True

theorem qd_prefixed (sl : CslotPtr) :
    ∀ k t, RDF (fun c σ => ({x | QD sl c σ x}, True)) k t ≤ (fun c σ => ({x | QD sl c σ x}, True)) k t := by
  intro k t
  refine ⟨fun x hx => ?_, fun _ => trivial⟩
  show QD sl k t x
  cases k with
  | cTEDeleteCall sl' ex =>
    intro hs hg v hv
    subst hs
    change x ∈ ((recDelF (Z := Unit) _ (.cTEDeleteCall sl' ex)).run t).1 at hx
    unfold recDelF at hx
    obtain ⟨y, hy, ⟨a, ha, hx⟩ | ⟨e, he, rfl⟩⟩ := bindE_mem_inv hx
    · obtain ⟨hy1, hP⟩ := (show QD sl' (.finaliseSlotCall sl' ex) t y from hy) rfl hg
      rw [hy1] at ha; cases ha
      simp only [withoutPreemption] at hx
      obtain ⟨z, hz, ⟨b, hb, hx⟩ | ⟨e, he, rfl⟩⟩ := bindE_mem_inv hx
      · obtain ⟨w, hw, rfl⟩ := liftE_mem_inv' hz
        have e2 : x.2 = w.2 := by
          simp only [run_returnOk] at hx; rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hx)).2]
        rw [e2]
        have hsk : SK y.2 w.2 := by
          unfold NonDet.when at hw
          split at hw
          · exact psk_emptySlot_null sl' y.2 w hw
          · rw [Set.mem_singleton_iff.1 hw]; exact SK.refl _
        exact fun p sco h => (hP p sco h).sk hsk
      · obtain ⟨w, -, hw⟩ := liftE_mem_inv' hz
        rw [hw] at he; cases he
    · cases hv
  | finaliseSlotCall sl' ex =>
    intro hs hg
    subst hs
    obtain ⟨e, b, R, hg⟩ := hg
    change x ∈ ((recDelF (Z := Unit) _ (.finaliseSlotCall sl' ex)).run t).1 at hx
    unfold recDelF withoutPreemption at hx
    rw [run_bind_ok_st (run_liftE hg)] at hx
    rw [if_neg (by simp)] at hx
    rw [run_bind_ok_st (run_liftE (m := isFinalCap (Z := Unit) (.endpointCap e b R)) rfl)] at hx
    obtain ⟨z, hz, ⟨a, ha, hx⟩ | ⟨e', he, rfl⟩⟩ := bindE_mem_inv hx
    · obtain ⟨w, hw, rfl⟩ := liftE_mem_inv' hz
      simp only [Except.ok.injEq] at ha
      subst ha
      unfold finaliseCap NonDet.liftM at hw
      obtain ⟨w', hw', hw⟩ := hw
      rw [Set.mem_singleton_iff.1 hw] at hx
      simp only at hx
      rw [if_pos (by trivial)] at hx
      rw [Set.mem_singleton_iff.1 hx]
      refine ⟨rfl, fun p sco h => ?_⟩
      unfold NonDet.when at hw'
      split at hw'
      · obtain ⟨F, hK, hact⟩ := cancelAllIpc_fr e hw'
        exact h.cancel F (hK p) hact
      · rw [Set.mem_singleton_iff.1 hw']; exact h
    · obtain ⟨w, -, hw⟩ := liftE_mem_inv' hz
      rw [hw] at he; cases he
  | reduceZombieCall _ _ _ => trivial

/-- **The spec's `cap_delete` of a slot holding an endpoint cap keeps
`SpecPost`** (final: `cancel_all_ipc`, `SpecPost.cancel`; then
`empty_slot`, `SK`). -/
theorem capDelete_ep_post {sl : CslotPtr} {σ σd : State Unit} {e : ObjRef} {b : Badge} {R : CapRights}
    (hg : getCap (Z := Unit) sl σ = ({(.endpointCap e b R, σ)}, False))
    (hd : (.ok (), σd) ∈ ((capDelete (Z := Unit) sl).run σ).1) : Post σ σd := by
  unfold capDelete at hd
  obtain ⟨z, hz, ⟨a, ha, hd⟩ | ⟨e', he, hd⟩⟩ := bindE_mem_inv hd
  · have e2 : σd = z.2 := by
      simp only [run_returnOk] at hd; exact (Prod.mk.inj (Set.mem_singleton_iff.1 hd)).2
    rw [e2]
    rw [recDel_run] at hz
    have := (lfp_le_prefixed _ _ (qd_prefixed sl) _ σ).1 hz
    exact (show QD sl (.cTEDeleteCall sl true) σ z from this) rfl ⟨e, b, R, hg⟩ a ha
  · cases hd

end Spec

end

end Fl4Proofs.P3.Sched

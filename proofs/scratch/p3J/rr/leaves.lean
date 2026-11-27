/-- An `a_type` that is neither an SC's nor a garbage one. -/
def NoScT (t : AType) : Prop := (∀ n, t ≠ .aSchedContext n) ∧ ∀ n, t ≠ .aGarbage n

theorem pv1_zero_of_noScT {k : KernelObject} (h : NoScT (aType k)) : pv1 k = 0 := by
  cases k with
  | schedContext sc n =>
    exfalso
    by_cases hv : validSchedContextSize n
    · exact h.1 n (by simp only [aType, if_pos hv])
    · exact h.2 (minSchedContextBits + n) (by simp only [aType, if_neg hv])
  | _ => rfl

theorem noScT_simple {k : KernelObject}
    (h : aType k ∈ ({.aEndpoint, .aNTFN, .aReply} : Set AType)) : NoScT (aType k) := by
  refine ⟨fun n e => ?_, fun n e => ?_⟩ <;> rw [e] at h <;> simp at h

theorem getObject_out {p : ObjRef} {σ : State Unit} {y : KernelObject × State Unit}
    (hy : y ∈ (getObject (Z := Unit) p σ).1) : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
  unfold getObject NonDet.getsThe readObject at hy
  cases h : σ.kheap p with
  | none => rw [h] at hy; exact hy.elim
  | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩

theorem setObject_out {p : ObjRef} {o : KernelObject} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setObject (Z := Unit) p o σ).1) :
    ∃ k, σ.kheap p = some k ∧ aType k = aType o ∧
      x.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ := getObject_out hy
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨k, hk, hty, rfl⟩

theorem rpV_update {σ : State Unit} {p : ObjRef} {o k : KernelObject} (hk : σ.kheap p = some k)
    (h : pv1 o = pv1 k) : rpV { σ with kheap := Function.update σ.kheap p (some o) } = rpV σ := by
  funext q
  unfold rpV
  by_cases e : q = p
  · subst e; simp [Function.update_self, hk, h]
  · simp only [Function.update_of_ne e]

/-- `set_object` of an object whose `a_type` is neither an SC's nor garbage. -/
theorem rq_setObject_nsc (p : ObjRef) (o : KernelObject) (ho : NoScT (aType o)) :
    RQ (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := setObject_out hx
  rw [e]
  exact rpV_update hk (by rw [pv1_zero_of_noScT ho, pv1_zero_of_noScT (by rw [hty]; exact ho)])
/-- Discharge `NoScT (aType o)` for a literal non-SC, non-CNode object. -/
macro "noScT_lit" : tactic =>
  `(tactic| (refine ⟨fun _ h => ?_, fun _ h => ?_⟩ <;> first | cases h | (simp [aType] at h; done)))
macro_rules | `(tactic| zq_leaf) => `(tactic| ((with_reducible refine rq_setObject_nsc _ _ ?_) <;> noScT_lit))

/-- `update_sched_context` with an update that keeps the period. -/
theorem rq_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ sc, (f sc).scPeriod = sc.scPeriod) : RQ (updateSchedContext (Z := Unit) q f) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk, rfl⟩ := getObject_out hy
  cases k with
  | schedContext sc n =>
    have hx' : x ∈ (setObject (Z := Unit) q (.schedContext (f sc) n) σ).1 := hx
    obtain ⟨-, -, -, e⟩ := setObject_out hx'
    rw [e]
    exact rpV_update hk (hf sc)
  | _ => exact False.elim hx
macro_rules | `(tactic| zq_leaf) => `(tactic| ((with_reducible refine rq_updateSchedContext' _ _ ?_) <;>
  (intro _; rfl)))

theorem rq_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    RQ (setSimpleKo (Z := Unit) C q e) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk, rfl⟩ := getObject_out hy
  obtain ⟨z1, ⟨hs, rfl⟩, hx⟩ := hx
  obtain ⟨z2, ⟨-, rfl⟩, hx⟩ := hx
  have hx' : x ∈ (setObject (Z := Unit) q (C e) σ).1 := hx
  obtain ⟨k2, hk2, hty, e2⟩ := setObject_out hx'
  have ek : k2 = k := Option.some.inj (hk2.symm.trans hk)
  rw [ek] at hty
  rw [e2]
  have hs' : NoScT (aType k) := noScT_simple hs
  exact rpV_update hk (by rw [pv1_zero_of_noScT hs', pv1_zero_of_noScT (by rw [← hty]; exact hs')])
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setSimpleKo' _ _ _)

theorem rq_setCap (c : Cap) (sl : CslotPtr) : RQ (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk, rfl⟩ := getObject_out hy
  have key : ∀ k' : KernelObject, pv1 k' = 0 → pv1 k = 0 → x ∈ (setObject (Z := Unit) o k' σ).1 →
      rpV x.2 = rpV σ := by
    intro k' h1 h2 hx'
    obtain ⟨-, -, -, e⟩ := setObject_out hx'
    rw [e]
    exact rpV_update hk (by rw [h1, h2])
  cases k <;> (try simp only at hx) <;> (repeat' split at hx) <;> first
    | exact False.elim hx
    | (obtain ⟨z, hz, -⟩ := hx; exact False.elim hz)
    | (obtain ⟨z, hz, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hz; exact key _ rfl rfl hx)
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setCap _ _)

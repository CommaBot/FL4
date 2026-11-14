/-
P3 (DESIGN.md §9), endpoints: updating the relation.

`EpStateRel.upd_tcb`, `upd_ep`, `upd_reply`: replacing one spec object
keeps the relation when FL4's memory agrees on the footprint words the other
objects read (`EPlaced`: TCBs, endpoints, replies and buffer words do not
overlap). Single word writes give that agreement (`agree_wr`).
-/
import Fl4Proofs.P3.EpSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

/-! ## Disjointness -/

theorem val_ne_of_ne {x y : U64} (h : x ≠ y) : x.val ≠ y.val := fun e => h (UScalar.eq_of_val_eq e)

theorem tcb_disj (hP : EPlaced T E R B) {t y : U64} (ht : t ∈ T) (hy : y ∈ T) (hne : y ≠ t) :
    y.val + 4096 ≤ t.val ∨ t.val + 4096 ≤ y.val := by
  have h1 := (hP.tcb t ht).align
  have h2 := (hP.tcb y hy).align
  have := val_ne_of_ne hne
  omega

theorem ep_disj (hP : EPlaced T E R B) {e e' : U64} (he : e ∈ E) (he' : e' ∈ E) (hne : e' ≠ e) :
    e'.val + 16 ≤ e.val ∨ e.val + 16 ≤ e'.val := by
  have h1 := (hP.ep e he).1
  have h2 := (hP.ep e' he').1
  have := val_ne_of_ne hne
  omega

theorem rep_disj (hP : EPlaced T E R B) {r r' : U64} (hr : r ∈ R) (hr' : r' ∈ R) (hne : r' ≠ r) :
    r'.val + 32 ≤ r.val ∨ r.val + 32 ≤ r'.val := by
  have h1 := (hP.rep r hr).1
  have h2 := (hP.rep r' hr').1
  have := val_ne_of_ne hne
  omega

theorem TF.range {t a : U64} (h : TF t a) : t.val + 256 ≤ a.val ∧ a.val ≤ t.val + 3448 := by
  obtain ⟨h1, h2⟩ := h
  unfold TOffN at h2; omega

theorem TWF.tf {t a : U64} (h : TWF t a) : TF t a := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  unfold TWOffN at h2; unfold TOffN; omega

theorem TF.of_val {t a b : U64} (h : TF t a) (e : b.val = a.val) : TF t b := by
  obtain ⟨h1, h2⟩ := h; exact ⟨e ▸ h1, e ▸ h2⟩

theorem TL.not_tf {t a : U64} (h : TL t a) : ¬ TF t a := by
  rintro ⟨h1, h2⟩; unfold TOffN at h2; unfold TL at h; omega

/-- A single write agrees on the words at other addresses. -/
theorem agree_wr {S : Type _} {st : machine.Store S} [L : LawfulStore st] {s : S} {a v : U64} (ha : Aligned a) :
    Agree (L.mem s) (L.mem (L.wr s a v)) (fun b => b.val ≠ a.val) :=
  fun _ hb hne => L.mem_wr_ne ha hb (Ne.symm hne)

/-! ## Replacing a TCB -/

section Upd
open Fl4Spec
variable {Z : Type}

/-- The words another object of the relation reads are not fields of the TCB
at `t`. -/
theorem notTF_ep (hP : EPlaced T E R B) {t e a : U64} (ht : t ∈ T) (he : e ∈ E)
    (ha : a.val = e.val ∨ a.val = e.val + 8) : ¬ TF t a := by
  intro h; have := h.range; have := hP.et e he t ht; omega
theorem notTF_rep (hP : EPlaced T E R B) {t r a : U64} (ht : t ∈ T) (hr : r ∈ R) (ha : a.val = r.val) :
    ¬ TF t a := by
  intro h; have := h.range; have := hP.rt r hr t ht; omega
theorem notTF_buf (hP : EPlaced T E R B) {t : U64} (ht : t ∈ T) {wp} (hw : wp ∈ B) : ¬ TF t wp.1 := by
  intro h; have := h.range; have := hP.bt wp hw t ht; omega
theorem notTF_tcb (hP : EPlaced T E R B) {t y a : U64} (ht : t ∈ T) (hy : y ∈ T) (hne : y ≠ t)
    (ha : TF y a ∨ TL y a) : ¬ TF t a := by
  intro h; have := h.range; have := tcb_disj hP ht hy hne
  rcases ha with ha | ha
  · have := ha.range; omega
  · unfold TL at ha; omega

theorem kheap_ne {σ : State Z} {p q : ObjRef} {o o' : KernelObject} (hp : σ.kheap p = some o)
    (hq : σ.kheap q = some o') (h : ∀ x : KernelObject, o = x → o' = x → False) : p ≠ q := by
  intro e; subst e; rw [hq] at hp; injection hp with hp; exact h o' hp.symm rfl

/-- Replacing the TCB at `t`: the other objects keep their relation when
memory agrees outside `t`'s fields; `t`'s state and block object may only
change if `t` is in no endpoint queue. -/
theorem EpStateRel.upd_tcb {m m' : U64 → U64} {σ : State Z} (hR : EpStateRel T E R B m σ)
    (hP : EPlaced T E R B) {t : U64} (ht : t ∈ T) (x' : Tcb)
    (hA : Agree m m' (fun b => EFoot T E R B b ∧ ¬ TF t b))
    (hq : (∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) ∨
      (m' (tStA t) = m (tStA t) ∧ m' (tBlockA t) = m (tBlockA t)))
    (hx : TcbRelE R m' t x') :
    EpStateRel T E R B m' (updK σ t.bv (.tcb x')) := by
  obtain ⟨x, hk, -⟩ := hR.tcb t ht
  have hta := hP.tcb t ht
  refine ⟨fun e he => ?_, fun r hr => ?_, fun y hy => ?_, fun wp hw => ?_⟩
  · obtain ⟨z, hkz, hz⟩ := hR.ep e he
    have hne : e.bv ≠ t.bv := kheap_ne hkz hk (fun _ h1 h2 => by subst h1; cases h2)
    refine ⟨z, by simp [hne, hkz], hz.frame (hA _ (a_head hP he).1 ⟨(a_head hP he).2,
      notTF_ep hP ht he (Or.inl (val_head e))⟩) (hA _ (a_ts hP he).1 ⟨(a_ts hP he).2,
      notTF_ep hP ht he (Or.inr (val_ts hP he))⟩) fun y hy hq' => ?_⟩
    have hya := hP.tcb y hy
    have hl : TLinksEq m m' y := by
      refine ⟨hA _ (a_prev hya).1 ⟨Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr (a_prev hya).2⟩)), ?_⟩,
        hA _ (a_next hya).1 ⟨Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr (a_next hya).2⟩)), ?_⟩⟩
      · by_cases e' : y = t
        · subst e'; exact (a_prev hya).2.not_tf
        · exact notTF_tcb hP ht hy e' (Or.inr (a_prev hya).2)
      · by_cases e' : y = t
        · subst e'; exact (a_next hya).2.not_tf
        · exact notTF_tcb hP ht hy e' (Or.inr (a_next hya).2)
    by_cases e' : y = t
    · subst e'
      rcases hq with hq | ⟨e1, e2⟩
      · exact absurd hq' (hq e he z hkz)
      · exact ⟨e1, e2, hl⟩
    · refine ⟨hA _ (a_st hya).1 ⟨Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_st hya).2⟩)),
        notTF_tcb hP ht hy e' (Or.inl (a_st hya).2)⟩,
        hA _ (a_blk hya).1 ⟨Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_blk hya).2⟩)),
        notTF_tcb hP ht hy e' (Or.inl (a_blk hya).2)⟩, hl⟩
  · obtain ⟨z, hkz, hz⟩ := hR.reply r hr
    have hne : r.bv ≠ t.bv := kheap_ne hkz hk (fun _ h1 h2 => by subst h1; cases h2)
    refine ⟨z, by simp [hne, hkz], ?_⟩
    rw [hz, hA _ (a_rtcb hP hr).1 ⟨(a_rtcb hP hr).2, notTF_rep hP ht hr (rTcbA_val r)⟩]
  · by_cases e : y = t
    · subst e; exact ⟨x', by simp, hx⟩
    · obtain ⟨z, hkz, hz⟩ := hR.tcb y hy
      refine ⟨z, by simp [bv_inj e, hkz], hz.frame (hP.tcb y hy) fun a ha hf => hA a ha
        ⟨Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl hf⟩)), notTF_tcb hP ht hy e (Or.inl hf)⟩⟩
  · have hal : Aligned wp.1 := (hP.balign wp hw).1
    show (m' wp.1).bv = loadWordAt σ.machineState.underlyingMemory wp.2
    rw [hA _ hal ⟨Or.inr (Or.inr (Or.inr ⟨wp, hw, rfl⟩)), notTF_buf hP ht hw⟩]
    exact hR.buf wp hw

/-- The words of the endpoint at `e`. -/
def EW (e a : U64) : Prop := a.val = e.val ∨ a.val = e.val + 8

/-- The `Ep` links of TCBs blocked on `e` (in memory `m`). -/
def LinkOn (T : Set U64) (m : U64 → U64) (e a : U64) : Prop := ∃ y ∈ T, m (tBlockA y) = e ∧ TL y a

/-- Replacing the endpoint at `e`: the other objects keep their relation when
memory agrees outside `e`'s words and the links of TCBs blocked on `e`. -/
theorem EpStateRel.upd_ep {m m' : U64 → U64} {σ : State Z} (hR : EpStateRel T E R B m σ)
    (hP : EPlaced T E R B) {e : U64} (he : e ∈ E) (x' : Endpoint)
    (hA : Agree m m' (fun b => EFoot T E R B b ∧ ¬ EW e b ∧ ¬ LinkOn T m e b))
    (hx : EpObjRel m' T e x') :
    EpStateRel T E R B m' (updK σ e.bv (.endpoint x')) := by
  obtain ⟨x, hk, -⟩ := hR.ep e he
  have hfield : ∀ y ∈ T, ∀ a, Aligned a → TF y a → m' a = m a := by
    intro y hy a ha hf
    refine hA a ha ⟨Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl hf⟩)), ?_, ?_⟩
    · intro hw; have := hf.range; have := hP.et e he y hy; unfold EW at hw; omega
    · rintro ⟨z, hz, -, hl⟩
      by_cases e' : z = y
      · subst e'; exact hl.not_tf hf
      · exact notTF_tcb hP hy hz e' (Or.inr hl) hf
  refine ⟨fun e' he' => ?_, fun r hr => ?_, fun y hy => ?_, fun wp hw => ?_⟩
  · by_cases ee : e' = e
    · subst ee; exact ⟨x', by simp, hx⟩
    · obtain ⟨z, hkz, hz⟩ := hR.ep e' he'
      have hd := ep_disj hP he he' ee
      have hnl : ∀ a, (a.val = e'.val ∨ a.val = e'.val + 8) → ¬ LinkOn T m e a := by
        rintro a ha ⟨y, hy, -, hl⟩
        have := hP.et e' he' y hy; unfold TL at hl; omega
      refine ⟨z, by simp [bv_inj ee, hkz], hz.frame
        (hA _ (a_head hP he').1 ⟨(a_head hP he').2, by unfold EW; rw [val_head]; omega,
          hnl _ (Or.inl (val_head e'))⟩)
        (hA _ (a_ts hP he').1 ⟨(a_ts hP he').2, by unfold EW; rw [val_ts hP he']; omega,
          hnl _ (Or.inr (val_ts hP he'))⟩) fun y hy hq' => ?_⟩
      have hya := hP.tcb y hy
      have hb : m (tBlockA y) = e' := (hz.blocked hq').2
      have hnl' : ∀ a, TL y a → ¬ LinkOn T m e a := by
        rintro a hl ⟨y', hy', hb', hl'⟩
        by_cases e2 : y' = y
        · subst e2; exact ee (hb.symm.trans hb')
        · have := tcb_disj hP hy hy' e2; unfold TL at hl hl'; omega
      have hnw : ∀ a, TL y a → ¬ EW e a := by
        intro a hl hw; have := hP.et e he y hy; unfold TL at hl; unfold EW at hw; omega
      exact ⟨hfield y hy _ (a_st hya).1 (a_st hya).2, hfield y hy _ (a_blk hya).1 (a_blk hya).2,
        hA _ (a_prev hya).1 ⟨Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr (a_prev hya).2⟩)), hnw _ (a_prev hya).2,
          hnl' _ (a_prev hya).2⟩,
        hA _ (a_next hya).1 ⟨Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr (a_next hya).2⟩)), hnw _ (a_next hya).2,
          hnl' _ (a_next hya).2⟩⟩
  · obtain ⟨z, hkz, hz⟩ := hR.reply r hr
    have hne : r.bv ≠ e.bv := kheap_ne hkz hk (fun _ h1 h2 => by subst h1; cases h2)
    refine ⟨z, by simp [hne, hkz], ?_⟩
    rw [hz, hA _ (a_rtcb hP hr).1 ⟨(a_rtcb hP hr).2, ?_, ?_⟩]
    · unfold EW; rw [rTcbA_val]; have := hP.er e he r hr; omega
    · rintro ⟨y, hy, -, hl⟩; have := hP.rt r hr y hy; unfold TL at hl; rw [rTcbA_val] at hl; omega
  · obtain ⟨z, hkz, hz⟩ := hR.tcb y hy
    have hne : y.bv ≠ e.bv := kheap_ne hkz hk (fun _ h1 h2 => by subst h1; cases h2)
    exact ⟨z, by simp [hne, hkz], hz.frame (hP.tcb y hy) fun a ha hf => hfield y hy a ha hf⟩
  · have hal : Aligned wp.1 := (hP.balign wp hw).1
    show (m' wp.1).bv = loadWordAt σ.machineState.underlyingMemory wp.2
    rw [hA _ hal ⟨Or.inr (Or.inr (Or.inr ⟨wp, hw, rfl⟩)), ?_, ?_⟩]
    · exact hR.buf wp hw
    · unfold EW; have := hP.be wp hw e he; omega
    · rintro ⟨y, hy, -, hl⟩; have := hP.bt wp hw y hy; unfold TL at hl; omega

/-- Replacing the reply object at `r`. -/
theorem EpStateRel.upd_reply {m m' : U64 → U64} {σ : State Z} (hR : EpStateRel T E R B m σ)
    (hP : EPlaced T E R B) {r : U64} (hr : r ∈ R) (x' : Reply)
    (hA : Agree m m' (fun b => EFoot T E R B b ∧ b.val ≠ r.val))
    (hx : x'.replyTcb = optRef (m' (rTcbA r))) :
    EpStateRel T E R B m' (updK σ r.bv (.reply x')) := by
  obtain ⟨x, hk, -⟩ := hR.reply r hr
  have hfield : ∀ y ∈ T, ∀ a, Aligned a → (TF y a ∨ TL y a) → m' a = m a := by
    intro y hy a ha hf
    refine hA a ha ⟨Or.inr (Or.inr (Or.inl ⟨y, hy, hf⟩)), ?_⟩
    intro hv; have := hP.rt r hr y hy
    rcases hf with hf | hf
    · have := hf.range; omega
    · unfold TL at hf; omega
  refine ⟨fun e he => ?_, fun r' hr' => ?_, fun y hy => ?_, fun wp hw => ?_⟩
  · obtain ⟨z, hkz, hz⟩ := hR.ep e he
    have hne : e.bv ≠ r.bv := kheap_ne hkz hk (fun _ h1 h2 => by subst h1; cases h2)
    have := hP.er e he r hr
    refine ⟨z, by simp [hne, hkz], hz.frame
      (hA _ (a_head hP he).1 ⟨(a_head hP he).2, by rw [val_head]; omega⟩)
      (hA _ (a_ts hP he).1 ⟨(a_ts hP he).2, by rw [val_ts hP he]; omega⟩) fun y hy _ => ?_⟩
    have hya := hP.tcb y hy
    exact ⟨hfield y hy _ (a_st hya).1 (Or.inl (a_st hya).2), hfield y hy _ (a_blk hya).1 (Or.inl (a_blk hya).2),
      hfield y hy _ (a_prev hya).1 (Or.inr (a_prev hya).2), hfield y hy _ (a_next hya).1 (Or.inr (a_next hya).2)⟩
  · by_cases ee : r' = r
    · subst ee; exact ⟨x', by simp, hx⟩
    · obtain ⟨z, hkz, hz⟩ := hR.reply r' hr'
      have := rep_disj hP hr hr' ee
      refine ⟨z, by simp [bv_inj ee, hkz], ?_⟩
      rw [hz, hA _ (a_rtcb hP hr').1 ⟨(a_rtcb hP hr').2, by rw [rTcbA_val]; omega⟩]
  · obtain ⟨z, hkz, hz⟩ := hR.tcb y hy
    have hne : y.bv ≠ r.bv := kheap_ne hkz hk (fun _ h1 h2 => by subst h1; cases h2)
    exact ⟨z, by simp [hne, hkz], hz.frame (hP.tcb y hy) fun a ha hf => hfield y hy a ha (Or.inl hf)⟩
  · have hal : Aligned wp.1 := (hP.balign wp hw).1
    show (m' wp.1).bv = loadWordAt σ.machineState.underlyingMemory wp.2
    rw [hA _ hal ⟨Or.inr (Or.inr (Or.inr ⟨wp, hw, rfl⟩)), by have := hP.br wp hw r hr; omega⟩]
    exact hR.buf wp hw

/-! ## Spec steps -/

theorem EpStep.trans {σ₁ σ₂ σ₃ : State Z} (h₁ : EpStep σ₁ σ₂) (h₂ : EpStep σ₂ σ₃) : EpStep σ₁ σ₃ := by
  obtain ⟨a1, b1, c1⟩ := h₁
  obtain ⟨a2, b2, c2⟩ := h₂
  refine ⟨a2.trans a1, ?_, fun p => ?_⟩
  · rw [b2]
    have hm : σ₂.machineState = { σ₁.machineState with underlyingMemory := σ₂.machineState.underlyingMemory } :=
      congrArg AbstractState.machineState b1
    rw [show σ₂.toAbstractState = _ from b1]
    rfl
  · rcases c1 p with e1 | ⟨x, y, hx, hy⟩ | ⟨x, y, hx, hy, f1⟩ | ⟨x, y, hx, hy, f⟩ <;>
    rcases c2 p with e2 | ⟨x', y', hx', hy'⟩ | ⟨x', y', hx', hy', f1'⟩ | ⟨x', y', hx', hy', f'⟩
    · exact Or.inl (e2.trans e1)
    · rw [e1] at hx'; exact Or.inr (Or.inl ⟨x', y', hx', hy'⟩)
    · rw [e1] at hx'; exact Or.inr (Or.inr (Or.inl ⟨x', y', hx', hy', f1'⟩))
    · rw [e1] at hx'; exact Or.inr (Or.inr (Or.inr ⟨x', y', hx', hy', f'⟩))
    · rw [← e2] at hy; exact Or.inr (Or.inl ⟨x, y, hx, hy⟩)
    · exact Or.inr (Or.inl ⟨x, y', hx, hy'⟩)
    · rw [hy] at hx'; cases hx'
    · rw [hy] at hx'; cases hx'
    · rw [← e2] at hy; exact Or.inr (Or.inr (Or.inl ⟨x, y, hx, hy, f1⟩))
    · rw [hy] at hx'; cases hx'
    · rw [hy] at hx'; cases hx'
      exact Or.inr (Or.inr (Or.inl ⟨x, y', hx, hy', f1'.trans f1⟩))
    · rw [hy] at hx'; cases hx'
    · rw [← e2] at hy; exact Or.inr (Or.inr (Or.inr ⟨x, y, hx, hy, f⟩))
    · rw [hy] at hx'; cases hx'
    · rw [hy] at hx'; cases hx'
    · rw [hy] at hx'; cases hx'
      refine Or.inr (Or.inr (Or.inr ⟨x, y', hx, hy', ?_⟩))
      rw [f', f]

/-- Writing an endpoint. -/
theorem EpStep.ep {σ : State Z} {p : ObjRef} {x y : Endpoint} (hk : σ.kheap p = some (.endpoint x)) :
    EpStep σ (updK σ p (.endpoint y)) := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases e : q = p
  · subst e; exact Or.inr (Or.inl ⟨x, y, hk, by simp⟩)
  · exact Or.inl (by simp [e])

/-- Writing the TCB of a reply. -/
theorem EpStep.reply {σ : State Z} {p : ObjRef} {x : Reply} (hk : σ.kheap p = some (.reply x)) (v : Option ObjRef) :
    EpStep σ (updK σ p (.reply { x with replyTcb := v })) := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases e : q = p
  · subst e; exact Or.inr (Or.inr (Or.inl ⟨x, { x with replyTcb := v }, hk, by simp, rfl⟩))
  · exact Or.inl (by simp [e])

/-- Writing a TCB's state and user context. -/
theorem EpStep.tcb {σ : State Z} {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) (ts : ThreadState)
    (a : ArchTcb) :
    EpStep σ (updK σ p (.tcb { x with tcbState := ts, tcbArch := a })) := by
  refine ⟨rfl, rfl, fun q => ?_⟩
  by_cases e : q = p
  · subst e; exact Or.inr (Or.inr (Or.inr ⟨x, { x with tcbState := ts, tcbArch := a }, hk, by simp, rfl⟩))
  · exact Or.inl (by simp [e])

end Upd

end

end

end Fl4Proofs.P3.Endp

/-
P3 (DESIGN.md §9), scheduling contexts: **the MCP relation across steps**.

* `McpKeep`: the spec's `tcb_mcpriority` of every TCB kept;
  `McpRel.frame` moves `McpRel` across a step that keeps the `MCP` words
  and `McpKeep`;
* `McpRel.set`: writing a TCB's `MCP` word with the spec's
  `tcb_mcpriority := p`;
* `hback_of_tsc`: `sc_decode_refines`' back-pointer hypothesis from P1's
  `TSc`;
* `set_mcp_refines`: FL4's `Tcb::set_mcp` refines l4v `set_mcpriority`
  (`thread_set`), keeping the scheduler, notification, yield, call-stack
  and MCP relations, `Inv` and `ActIdle`.
-/
import Fl4Proofs.P3.ScDecodeSc
import Fl4Proofs.P1.QueueTcbInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The spec's `tcb_mcpriority` of every TCB is kept. -/
def McpKeep (σ σ' : State Unit) : Prop :=
  ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbMcpriority = x.tcbMcpriority

theorem McpKeep.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : McpKeep σ σ' :=
  fun p x hp => ⟨x, by rw [h]; exact hp, rfl⟩

theorem McpKeep.refl (σ : State Unit) : McpKeep σ σ := McpKeep.of_kheap rfl

theorem McpKeep.trans {σ σ1 σ2 : State Unit} (h1 : McpKeep σ σ1) (h2 : McpKeep σ1 σ2) : McpKeep σ σ2 :=
  fun p x hp => by
    obtain ⟨y, hy, e⟩ := h1 p x hp; obtain ⟨z, hz, e'⟩ := h2 p y hy; exact ⟨z, hz, e'.trans e⟩

/-- Replacing a TCB by one with the same `tcb_mcpriority`. -/
theorem McpKeep.updTcb {σ : State Unit} {p : ObjRef} {x x' : Tcb} (hk : σ.kheap p = some (.tcb x))
    (e : x'.tcbMcpriority = x.tcbMcpriority) : McpKeep σ (updK σ p (.tcb x')) := by
  intro q y hq
  by_cases h : q = p
  · subst h; rw [hk] at hq; cases hq; exact ⟨x', by simp [updK], e⟩
  · exact ⟨y, by simp [updK, h, hq], rfl⟩

/-- Replacing an object that is no TCB by one that is no TCB. -/
theorem McpKeep.updOther {σ : State Unit} {p : ObjRef} {o : KernelObject}
    (hp : ∀ x, σ.kheap p ≠ some (.tcb x)) (ho : ∀ x, o ≠ .tcb x) : McpKeep σ (updK σ p o) := by
  intro q y hq
  have h : q ≠ p := by rintro rfl; exact hp y hq
  exact ⟨y, by simp [updK, h, hq], rfl⟩

theorem McpKeep.stsAct {σ : State Unit} (t : ObjRef) : McpKeep σ (Fl4Proofs.P3.Notif.stsAct σ t) :=
  McpKeep.of_kheap (by unfold Fl4Proofs.P3.Notif.stsAct; split <;> rfl)

/-- Replacing a TCB by one with the same state, SC, priority and domain
keeps the scheduler frame. -/
theorem SFrame.tcbUpd {σ : State Unit} {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) (x' : Tcb)
    (est : x'.tcbState = x.tcbState) (esc : x'.tcbSchedContext = x.tcbSchedContext)
    (ep : x'.tcbPriority = x.tcbPriority) (ed : x'.tcbDomain = x.tcbDomain) :
    SFrame σ (updK σ p (.tcb x')) := by
  refine ⟨fun q y hq => ?_, fun q y m hq => ?_, rfl, rfl, rfl, rfl⟩
  · by_cases h : q = p
    · subst h; rw [hk] at hq; cases hq
      exact ⟨x', by simp [updK], est, esc, ep, ed⟩
    · exact ⟨y, by simp [updK, h, hq], rfl, rfl, rfl, rfl⟩
  · have h : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨y, by simp [updK, h, hq], rfl, rfl⟩

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem mcpA_aligned {T : Set U64} (hT : TcbPlaced T) {t : U64} (ht : t ∈ T) : Aligned (mcpA t) :=
  field_aligned (hT t ht) (K := 3440#u64) (by simp) (by simp)

/-- **`McpRel` across a step** that keeps the `MCP` words and the spec's
`tcb_mcpriority`. -/
theorem McpRel.frame {T : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} (h : McpRel T m σ)
    (hm : ∀ t ∈ T, m' (mcpA t) = m (mcpA t)) (hk : McpKeep σ σ') : McpRel T m' σ' := by
  intro t ht
  obtain ⟨x, hx, e⟩ := h t ht
  obtain ⟨y, hy, e'⟩ := hk _ x hx
  exact ⟨y, hy, by rw [hm t ht, e, e']⟩

/-- `McpRel` across a step whose writes avoid the `MCP` words (`WritesIn`
with a footprint that misses them). -/
theorem McpRel.writes {T : Set U64} {s s' : S} {σ σ' : Fl4Spec.State Unit} {P : U64 → Prop}
    (h : McpRel T (L.mem s) σ) (hT : TcbPlaced T) (hw : WritesIn st s s' P) (hP : ∀ t ∈ T, ¬ P (mcpA t))
    (hk : McpKeep σ σ') : McpRel T (L.mem s') σ' :=
  h.frame (fun t ht => hw.mem_eq (mcpA_aligned hT ht) (hP t ht)) hk

/-- **Writing a TCB's `MCP` word** with the spec's `tcb_mcpriority := p`. -/
theorem McpRel.set {T : Set U64} {s : S} {σ : Fl4Spec.State Unit} (h : McpRel T (L.mem s) σ)
    (hT : TcbPlaced T) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    {v : U64} {p : Fl4Spec.Priority} (hv : v.val = p.toNat) :
    McpRel T (L.mem (L.wr s (mcpA t) v)) (updK σ t.bv (.tcb { x with tcbMcpriority := p })) := by
  intro u hu
  by_cases e : u = t
  · subst e
    exact ⟨{ x with tcbMcpriority := p }, by simp [updK], by rw [rd_wr_eq (mcpA_aligned hT ht)]; exact hv⟩
  · obtain ⟨y, hy, ey⟩ := h u hu
    refine ⟨y, by simp [updK, bv_ne e, hy], ?_⟩
    rw [rd_wr_ne (mcpA_aligned hT ht) (mcpA_aligned hT hu) (fun e' => e ?_)]
    · exact ey
    · have := (tt_eq_iff (hT t ht) (hT u hu) (K1 := 3440#u64) (K2 := 3440#u64) (by simp) (by simp)).1 e'
      exact this.1.symm

/-- **`sc_decode_refines`' `hback` from P1's `TSc`** (the SC → TCB
back-pointer of `ScExtra`), given that a bound thread is one of `T` other
than the idle thread. -/
theorem hback_of_tsc {Scs T : Set U64} {s : S} {σ : Fl4Spec.State Unit} (h : TSc st Scs s) {sc : U64}
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (hT : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ T ∧ (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread) :
    L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ T ∧ L.mem s (scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread := fun h0 => by
  have e := h sc hsc hsc0 (by rw [scTcbA_eq]; exact h0)
  rw [scTcbA_eq] at e
  exact ⟨(hT h0).1, e, (hT h0).2⟩

/-- **`Tcb::set_mcp` refines l4v `set_mcpriority`**, keeping every relation
of the SchedContext decode. -/
theorem set_mcp_refines {N T C R : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit) {Lst : U64 → List U64}
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hAI : ActIdle σ) (hM : McpRel T (L.mem s) σ)
    (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ) (hRF : RFree (L.mem s) R C σ Lst)
    {t : U64} (ht : t ∈ T) {v : U64} {p : Fl4Spec.Priority} (hv : v.val = p.toNat) :
    obj.Tcb.set_mcp st t s v ⦃ s' => ∃ σ', Fl4Spec.setMcpriority (Z := Unit) t.bv p σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      YieldRel T C (L.mem s') σ' ∧ ActIdle σ' ∧ McpRel T (L.mem s') σ' ∧
      CallRel (L.mem s') R C σ' Lst ∧ RPlaced st N T C R c s' σ' ∧ RFree (L.mem s') R C σ' Lst ⦄ := by
  refine WP.spec_mono (obj.Tcb.set_mcp.wr s t v) fun s' e => ?_
  obtain ⟨Q, Rq, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  obtain ⟨x, hk, -⟩ := hM t ht
  set x' := { x with tcbMcpriority := p }
  have hA := mcpA_aligned hT ht
  obtain ⟨hS', hF, hV⟩ := hS.set_tw ht hk (K := 3440#u64) (by simp) (by simp) (by simp [SchedField])
    (by decide) (by decide) (by decide) (by decide) (by decide) x' rfl rfl rfl rfl rfl v
  subst e
  have hR' := hR.frame hS.placed hF hV
  -- words other than the `MCP` word of `t`
  have ko : ∀ b : U64, Aligned b → b ≠ mcpA t → L.mem (L.wr s (mcpA t) v) b = L.mem s b :=
    fun b hb hne => rd_wr_ne hA hb (Ne.symm hne)
  have hyw : ∀ u ∈ T, L.mem (L.wr s (mcpA t) v) (yieldA u) = L.mem s (yieldA u) := fun u hu =>
    ko _ (yieldA_aligned hT hu) (fun e' => by
      have := (tt_eq_iff (hT u hu) (hT t ht) (K1 := 3472#u64) (K2 := 3440#u64) (by simp) (by simp)).1 e'
      exact absurd this.2 (by decide))
  have hscr : ∀ sc ∈ C, L.mem (L.wr s (mcpA t) v) (scReplyA sc) = L.mem s (scReplyA sc) := by
    intro sc hsc
    obtain ⟨y, n, hky, hy⟩ := hs.scs sc hsc
    have ha := hy.hdr (K := 32#u64) (by simp) (by simp)
    rw [scReplyA_eq]
    refine ko _ ha.1 (fun e' => ?_)
    have h3 := (hS.scOutIn hsc ha.2).2.2.1 t ht
    rw [e', show (mcpA t).val = t.val + 3440 from tfield_val (hT t ht) (K := 3440#u64) (by simp)] at h3
    omega
  have hrw : ∀ r ∈ R, L.mem (L.wr s (mcpA t) v) (rPrevA r) = L.mem s (rPrevA r) ∧
      L.mem (L.wr s (mcpA t) v) (rNextA r) = L.mem s (rNextA r) := by
    intro r hr
    have hAr := hRP.align r hr
    have k2 := hRP.tcb r hr t ht
    have hm : (mcpA t).val = t.val + 3440 := tfield_val (hT t ht) (K := 3440#u64) (by simp)
    refine ⟨ko _ (hRP.aligned hr (Or.inl (rPrevA_val hAr))) (fun e' => ?_),
      ko _ (hRP.aligned hr (Or.inr (rNextA_val hAr))) (fun e' => ?_)⟩
    · have := congrArg UScalar.val e'; rw [rPrevA_val hAr, hm] at this; omega
    · have := congrArg UScalar.val e'; rw [rNextA_val hAr, hm] at this; omega
  have hsc : ∀ sc ∈ C, ∀ y n, σ.kheap sc.bv = some (.schedContext y n) →
      ∃ y', (updK σ t.bv (.tcb x')).kheap sc.bv = some (.schedContext y' n) ∧ y'.scReplies = y.scReplies := by
    intro sc _ y n hy
    have : sc.bv ≠ t.bv := fun e' => by rw [e', hk] at hy; cases hy
    exact ⟨y, by simp [updK, this, hy], rfl⟩
  have hrp : ∀ r ∈ R, ∀ xr, σ.kheap r.bv = some (.reply xr) →
      ∃ xr', (updK σ t.bv (.tcb x')).kheap r.bv = some (.reply xr') ∧ xr'.replySc = xr.replySc := by
    intro r _ xr hr
    have : r.bv ≠ t.bv := fun e' => by rw [e', hk] at hr; cases hr
    exact ⟨xr, by simp [updK, this, hr], rfl⟩
  have hfree : ∀ d ∈ R, Free (updK σ t.bv (.tcb x')) d → Free σ d := by
    rintro d _ ⟨xr, hxr, e'⟩
    have : d.bv ≠ t.bv := fun e2 => by rw [e2] at hxr; simp [updK] at hxr
    exact ⟨xr, by simpa [updK, this] using hxr, e'⟩
  refine ⟨updK σ t.bv (.tcb x'), threadSet_eq _ hk, hS', hR', hN.updTcb, hI.tcbUpd hk x' rfl rfl,
    hY.frame hyw (YKeep.updTcb hk rfl), hAI.sframe (SFrame.tcbUpd hk x' rfl rfl rfl rfl),
    hM.set hT ht hk hv, hCR.frame hscr hrw hsc hrp,
    hRP.frame (L.ksb_wr _ _ _) (SzKeep.updK hk fun _ _ e' => by cases e'),
    hRF.frame hrw hfree⟩

end

end

end Fl4Proofs.P3.Sched

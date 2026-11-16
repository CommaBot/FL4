/-
P3 (DESIGN.md §9), scheduling contexts: **`BlockedScActive` ([J]) across the
SC steps** (the fold's preservation phase, plan §5.1).

* `BlockedScActive.back`: across any spec step whose SCs come from SCs of
  the start (same size), keep their activeness, link no new thread and no
  new call stack to an inactive SC, and whose IPC-blocked threads were
  IPC-blocked.
* `ScTKw.tcb_back`: an `ScTKw` step (the SC code's) changes thread states
  only between IPC-free ones, so its IPC-blocked threads were IPC-blocked.
* `BlockedScActive.tkw`: across an `ScTKw` step with that SC condition.
* `BlockedScActive.sck`: across a step keeping every SC's `REFILL_MAX` and
  bound thread (`MaxK.SCK`), shrinking no... call stack grows, and every
  TCB's state.
* `reply_remove_tcb_sc_bsa`: across `replyRemoveTcbSc` (the reply cut).
-/
import Fl4Proofs.P3.ScJoint
import Fl4Proofs.P3.ScRemoveTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

section Spec

/-- **`BlockedScActive` across a step, backwards** (module docstring). -/
theorem BlockedScActive.back {σ σ' : State Unit} (h : BlockedScActive σ)
    (hsc : ∀ p y n, σ'.kheap p = some (.schedContext y n) → scActive y = false →
      ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧ scActive y0 = false ∧
        (∀ t, y.scTcb = some t → y0.scTcb = some t) ∧ (y.scReplies ≠ [] → y0.scReplies ≠ []))
    (htcb : ∀ t x, σ'.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = true →
      ∃ x0, σ.kheap t = some (.tcb x0) ∧ ipcQueuedThreadState x0.tcbState = true) :
    BlockedScActive σ' := by
  refine ⟨fun p y n t x hp hyt hx hq => ?_, fun p y n hp hr => ?_⟩
  · by_contra ha
    obtain ⟨y0, hp0, ha0, ht0, -⟩ := hsc p y n hp (by simpa using ha)
    obtain ⟨x0, hx0, hq0⟩ := htcb t x hx hq
    have := h.tcb p y0 n t x0 hp0 (ht0 t hyt) hx0 hq0
    rw [ha0] at this; cases this
  · by_contra ha
    obtain ⟨y0, hp0, ha0, -, hr0⟩ := hsc p y n hp (by simpa using ha)
    have := h.replies p y0 n hp0 (hr0 hr)
    rw [ha0] at this; cases this

theorem ipcFree_not_queued {ts : ThreadState} (h : IpcFree ts) : ipcQueuedThreadState ts = false := by
  obtain ⟨h1, h2, h3⟩ := h
  cases ts <;> first | rfl | simp_all [epBlocked, ntfnBlocked, ipcQueuedThreadState]

/-- **An `ScTKw` step's IPC-blocked threads were IPC-blocked.** -/
theorem ScTKw.tcb_back {P : ObjRef → Prop} {σ σ' : State Unit} (hK : ScTKw P σ σ') :
    ∀ t x, σ'.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = true →
      ∃ x0, σ.kheap t = some (.tcb x0) ∧ ipcQueuedThreadState x0.tcbState = true := by
  intro t x hx hq
  have hk := hK.kh t
  rw [hx] at hk
  cases h0 : σ.kheap t with
  | none => rw [h0] at hk; exact hk.elim
  | some o =>
    rw [h0] at hk
    rcases hk with e | ⟨x0, y, e1, e2, -, hst⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, e, -⟩ | ⟨_, _, _, e, -⟩
    · exact ⟨x, by rw [← e], hq⟩
    · cases e2
      rcases hst with e | ⟨-, -, hf⟩
      · exact ⟨x0, e1 ▸ rfl, by rw [← e]; exact hq⟩
      · rw [ipcFree_not_queued hf] at hq; cases hq
    all_goals cases e

/-- **`BlockedScActive` across an `ScTKw` step** with the SC condition of
`BlockedScActive.back`. -/
theorem BlockedScActive.tkw {P : ObjRef → Prop} {σ σ' : State Unit} (h : BlockedScActive σ) (hK : ScTKw P σ σ')
    (hsc : ∀ p y n, σ'.kheap p = some (.schedContext y n) → scActive y = false →
      ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧ scActive y0 = false ∧
        (∀ t, y.scTcb = some t → y0.scTcb = some t) ∧ (y.scReplies ≠ [] → y0.scReplies ≠ [])) :
    BlockedScActive σ' :=
  h.back hsc hK.tcb_back

/-- **`BlockedScActive` across a step keeping the SCs' `REFILL_MAX` and bound
threads** (`MaxK.SCK`), growing no call stack from empty, and keeping the
TCBs' states. -/
theorem BlockedScActive.sck {σ σ' : State Unit} (h : BlockedScActive σ) (hK : MaxK.SCK σ σ')
    (hr : ∀ p y n, σ'.kheap p = some (.schedContext y n) → y.scReplies ≠ [] →
      ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧ y0.scReplies ≠ [])
    (htcb : ∀ t x, σ'.kheap t = some (.tcb x) → ∃ x0, σ.kheap t = some (.tcb x0) ∧ x0.tcbState = x.tcbState) :
    BlockedScActive σ' := by
  refine h.back (fun p y n hp ha => ?_) (fun t x hx hq => ?_)
  · obtain ⟨y0, hp0, hm, ht⟩ := hK p y n hp
    refine ⟨y0, hp0, by simpa [scActive, hm] using ha, fun t e => by rw [← ht]; exact e, fun hne => ?_⟩
    obtain ⟨y1, hp1, h1⟩ := hr p y n hp hne
    rw [hp0] at hp1; cases hp1; exact h1
  · obtain ⟨x0, hx0, e⟩ := htcb t x hx
    exact ⟨x0, hx0, by rw [e]; exact hq⟩

end Spec

/-! ## The reply cut -/

section
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`BlockedScActive` across the reply cut** (`replyRemoveTcbSc`): the cut
stack's SC keeps its `REFILL_MAX` and thread, its stack only shrinks; the
reply loses its `reply_sc`; no TCB changes. -/
theorem reply_remove_tcb_sc_bsa {R C : Set U64} {m : U64 → U64} {σ σ' : Fl4Spec.State Unit}
    {Lst : U64 → List U64} (hCR : CallRel m R C σ Lst)
    (hSCs : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ q ∈ C, q.bv = p)
    {r : U64} (hr : r ∈ R) (hrem : replyRemoveTcbSc r.bv σ = ({((), σ')}, False)) (hB : BlockedScActive σ) :
    BlockedScActive σ' := by
  obtain ⟨xr, hkr, hxr⟩ := hCR.reply r hr
  have hmemb : ∀ q ∈ C, ∀ y n, σ.kheap q.bv = some (.schedContext y n) → (r.bv ∈ y.scReplies ↔ r ∈ Lst q) := by
    intro q hq y n hk
    obtain ⟨⟨y0, n0, hk0, hy0⟩, -⟩ := hCR.stack q hq
    rw [hk] at hk0; cases hk0
    rw [hy0, List.mem_map]
    exact ⟨fun ⟨d, hd, e⟩ => (P1.eq_of_bv e) ▸ hd, fun h => ⟨r, h, rfl⟩⟩
  by_cases hlive : ∃ sc ∈ C, r ∈ Lst sc
  swap
  · have hdet : Detached C Lst r := fun q hq h => hlive ⟨q, hq, h⟩
    have h0 : replyRemoveTcbSc r.bv σ = ({((), σ)}, False) := by
      unfold replyRemoveTcbSc
      rw [nd_gets_bind, scWithReply_none fun q y n hq hm => by
        obtain ⟨q', hq', rfl⟩ := hSCs q y n hq
        exact hdet q' hq' ((hmemb q' hq' y n hq).1 hm)]
      rfl
    rw [h0] at hrem
    have : σ' = σ := (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hrem))).symm
    rw [this]; exact hB
  obtain ⟨sc, hsc, hrL⟩ := hlive
  obtain ⟨⟨y, n, hk, hyL⟩, hLR, hLnd, hLw⟩ := hCR.stack sc hsc
  have hwr : Fl4Spec.scWithReply r.bv σ = some sc.bv := scWithReply_some fun q =>
    ⟨fun ⟨y', n', hq, hm⟩ => by
      obtain ⟨q', hq', rfl⟩ := hSCs q y' n' hq
      rw [hCR.excl q' hq' sc hsc r ((hmemb q' hq' y' n' hq).1 hm) hrL],
     fun e => by subst e; exact ⟨y, n, hk, (hmemb sc hsc y n hk).2 hrL⟩⟩
  have hpr : sc.bv ≠ r.bv := fun e => by rw [e, hkr] at hk; cases hk
  -- the spec's step, whatever the head
  have hstep : ∃ l : List Fl4Spec.ObjRef, (∀ x ∈ l, x ∈ y.scReplies) ∧
      σ' = updK (updSc σ sc.bv { y with scReplies := l } n) r.bv (.reply { xr with replySc := none }) := by
    by_cases hh : Fl4Spec.the y.scReplies.head? = r.bv
    · have hrs : xr.replySc = some sc.bv := by
        obtain ⟨k, hkl, e⟩ := List.getElem_of_mem hrL
        have hk0 : k = 0 := by
          by_contra hk0
          rw [hyL, List.head?_map] at hh
          have hhd : (Lst sc).head? = some (Lst sc)[0] := by
            rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
          rw [hhd] at hh
          have := nodup_idx hLnd (by omega) hkl ((P1.eq_of_bv hh).trans e.symm); omega
        subst hk0
        exact (hxr sc.bv).2 ⟨sc, hsc, rfl, by
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hkl, e]⟩
      unfold replyRemoveTcbSc at hrem
      rw [nd_gets_bind, hwr] at hrem
      dsimp only at hrem
      rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _), nd_bind_one (getReplySc_eq hkr), if_pos hh,
        nd_bind_one (nd_assert_true hrs σ), nd_bind_one (updateSchedContext_eq hk _),
        setReplySc_eq none (by rw [show (updSc σ sc.bv _ n).kheap r.bv = σ.kheap r.bv by simp [updK, hpr.symm]]; exact hkr)] at hrem
      refine ⟨y.scReplies.takeWhile fun x => decide (x ≠ r.bv), fun x hx => (List.takeWhile_sublist _).subset hx, ?_⟩
      simp only [Fl4Spec.scRepliesUpdate] at hrem
      exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hrem))).symm
    · have hrs : xr.replySc = none := by
        cases h : xr.replySc with
        | none => rfl
        | some p =>
          obtain ⟨sc', hsc', e, hh'⟩ := (hxr p).1 h
          have := hCR.excl sc' hsc' sc hsc _ (List.mem_of_mem_head? hh') hrL
          subst this
          exact absurd (by rw [hyL, List.head?_map, hh']; rfl) hh
      unfold replyRemoveTcbSc at hrem
      rw [nd_gets_bind, hwr] at hrem
      dsimp only at hrem
      rw [nd_bind_one (nd_liftM_one (getSchedContext_eq hk) _), nd_bind_one (getReplySc_eq hkr), if_neg hh,
        nd_bind_one (nd_assert_true hrs σ), nd_bind_one (updateSchedContext_eq hk _),
        setReplySc_eq none (by rw [show (updSc σ sc.bv _ n).kheap r.bv = σ.kheap r.bv by simp [updK, hpr.symm]]; exact hkr)] at hrem
      refine ⟨y.scReplies.takeWhile fun x => decide (x ≠ r.bv), fun x hx => (List.takeWhile_sublist _).subset hx, ?_⟩
      simp only [Fl4Spec.scRepliesUpdate] at hrem
      exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hrem))).symm
  obtain ⟨l, hl, rfl⟩ := hstep
  refine hB.sck (fun p y' n' hp => ?_) (fun p y' n' hp hne => ?_) (fun t x hx => ?_)
  · by_cases e1 : p = r.bv
    · subst e1; simp [updK] at hp
    by_cases e2 : p = sc.bv
    · subst e2; simp [updK, e1] at hp; obtain ⟨rfl, rfl⟩ := hp; exact ⟨y, hk, rfl, rfl⟩
    · simp [updK, e1, e2] at hp; exact ⟨y', hp, rfl, rfl⟩
  · by_cases e1 : p = r.bv
    · subst e1; simp [updK] at hp
    by_cases e2 : p = sc.bv
    · subst e2; simp [updK, e1] at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨y, hk, fun h0 => ?_⟩
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
      have := hl x hx; rw [h0] at this; simp at this
    · simp [updK, e1, e2] at hp; exact ⟨y', hp, hne⟩
  · by_cases e1 : t = r.bv
    · subst e1; simp [updK] at hx
    by_cases e2 : t = sc.bv
    · subst e2; simp [updK, e1] at hx
    · simp [updK, e1, e2] at hx; exact ⟨x, hx, rfl⟩

end

end

end Fl4Proofs.P3.Sched

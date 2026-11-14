/-
P3 (DESIGN.md §9), scheduling contexts: **the call stack** (l4v
`sc_replies`, `reply_sc`) against FL4's SC `REPLY` word and the replies'
`PREV`/`NEXT` words.

FL4 (as seL4's C kernel) keeps each SC's call stack as a list: the SC's
`REPLY` word is the newest reply; a reply's `PREV` word is the next older
one (0 at the bottom); the newest reply's `NEXT` word is the SC with bit 0
set (`is_head`), an older one's is the next newer reply. Replies cut off a
stack (`reply_remove` of a non-head, `unbind_reply`) keep their links among
themselves; they are *detached*: their `NEXT` words are untagged, and their
links point to detached replies, consistently (`PREV (NEXT d) = d`).

* `RPlaced`: the replies `R` are 32-byte objects outside the kernel-global
  area and the node, the TCBs, the notifications and the SCs.
* `CallRel m R C σ Lst`: with ghost stacks `Lst sc` (newest first), the
  spec's `sc_replies` of each SC of `C`, `reply_sc` (the head's SC), and the
  detached replies.
* `SchedRel.wr_far`, `NtfnStateRel` frames: writes to reply words keep the
  scheduler and notification relations.
-/
import Fl4Proofs.P3.ScNtfnBind
import Fl4Proofs.P1.QueueAppend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Defs
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- A word far from what `SchedRel` reads: the kernel-global area and the
node, the TCBs, and the SC objects. -/
def Far (T C : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) (a : U64) : Prop :=
  (a.val + 8 ≤ (L.ksb s).val ∨ L.nodeBase s c + 4288 ≤ a.val) ∧
  (∀ t ∈ T, a.val + 8 ≤ t.val ∨ t.val + 4096 ≤ a.val) ∧
  (∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → a.val + 8 ≤ sc.val ∨ sc.val + 2 ^ n ≤ a.val)

/-- The replies of `R`: 32-byte objects outside the kernel-global area and
the node, the TCBs, the notifications and the SCs of `C`. -/
structure RPlaced (N T C R : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  align : ∀ r ∈ R, r.val % 32 = 0 ∧ r ≠ 0#u64 ∧ r.val + 32 ≤ 2 ^ 64
  ksb : ∀ r ∈ R, r.val + 32 ≤ (L.ksb s).val ∨ L.nodeBase s c + 4288 ≤ r.val
  tcb : ∀ r ∈ R, ∀ t ∈ T, r.val + 32 ≤ t.val ∨ t.val + 4096 ≤ r.val
  ntfn : ∀ r ∈ R, ∀ n ∈ N, r.val + 32 ≤ n.val ∨ n.val + 64 ≤ r.val
  sc : ∀ r ∈ R, ∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) →
    r.val + 32 ≤ sc.val ∨ sc.val + 2 ^ n ≤ r.val

end Defs

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **A write far from what the scheduler relation reads keeps it.** -/
theorem SchedRel.wr_far {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {a : U64} (ha : Aligned a) (hf : Far st T C c s σ a) (v : U64) :
    SchedRel st N T C c (L.wr s a v) σ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hk, ht, hsc⟩ := hf
  have hN := hc.node
  have hnode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem (L.wr s a v) (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun o ho h8 => L.mem_wr_ne ha (nodeAt_aligned hN ho h8) (by
      rw [nodeAt_val hN ho]; simp only [LawfulStore.nodeBase] at hk ⊢; omega)
  have hksb : ∀ K : U64, 8 ≤ K.val → K.val < 13568 → K.val % 8 = 0 →
      L.mem (L.wr s a v) (core.num.U64.wrapping_add (L.ksb s) K) = L.mem s (core.num.U64.wrapping_add (L.ksb s) K) := by
    intro K h1 h2 h3
    have hf := hN.fits; have hal := hN.align
    simp only [LawfulStore.nodeBase] at hf hal hk
    have hv : (core.num.U64.wrapping_add (L.ksb s) K).val = (L.ksb s).val + K.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine L.mem_wr_ne ha ?_ (by rw [hv]; omega)
    unfold Aligned; rw [hv]; omega
  have ha' : SAgree st T C c s (L.wr s a v) := by
    refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun o ho h8 _ _ => hnode o ho h8, fun y hy K hK => ?_,
      by unfold curDomA; exact hksb 8#u64 (by simp) (by simp) (by simp),
      by unfold dtA; exact hksb 16#u64 (by simp) (by simp) (by simp), fun sc' hsc' b hb hin => ?_⟩
    · obtain ⟨h1, h2, -⟩ := schedField_ok hK
      have hya := hc.tcbs y hy
      refine L.mem_wr_ne ha (field_aligned hya h1 h2) ?_
      rw [tfield_val hya h1]; have := ht y hy; omega
    · obtain ⟨x, n, hkx, hx⟩ := hs.scs sc' hsc'
      have hin' := hx.in_obj hin
      refine L.mem_wr_ne ha hb ?_
      have := hsc sc' hsc' x n hkx; unfold ScObj at hin'; omega
  refine hS.of_sagree ha' ?_ ?_ ⟨rfl, rfl, fun _ => Or.inl rfl⟩
  · unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb (L.ksb_wr _ _ _)]
    exact hnode _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  · unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb (L.ksb_wr _ _ _)]
    exact hnode _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])

/-- A word outside the notifications and the TCBs is outside the
notification relation's footprint. -/
theorem footEq_wr_far {N T : Set U64} (hP : NPlaced T N) {s : S} {a : U64} (ha : Aligned a)
    (hn : ∀ n ∈ N, a.val + 8 ≤ n.val ∨ n.val + 64 ≤ a.val)
    (ht : ∀ t ∈ T, a.val + 8 ≤ t.val ∨ t.val + 4096 ≤ a.val) (v : U64) :
    FootEq N T (L.mem s) (L.mem (L.wr s a v)) := by
  intro b hb hf
  refine L.mem_wr_ne ha hb ?_
  rcases hf with ⟨n, hn', h1, h2⟩ | ⟨t, ht', e⟩
  · have := hn n hn'; omega
  · have hta := hP.tcb t ht'
    have := ht t ht'
    rcases e with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [tStA_eq, tfield_val hta (by simp)]; simp; omega
    · rw [tBlockA_eq, tfield_val hta (by simp)]; simp; omega
    · rw [badgeRegA_eq, tfield_val hta (by simp)]; simp; omega
    · rw [prioA_eq', tfield_val hta (by simp)]; simp; omega
    · rw [nextEp_eq, tfield_val hta (by simp)]; simp; omega
    · rw [prevEp_eq, tfield_val hta (by simp)]; simp; omega

/-! ## Placement and the relation -/

theorem RPlaced.frame {N T C R : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : RPlaced st N T C R c s σ) (hk : L.ksb s' = L.ksb s) (hz : SzKeep σ σ') : RPlaced st N T C R c s' σ' := by
  refine ⟨h.align, fun r hr => ?_, h.tcb, h.ntfn, fun r hr sc hsc x n hx => ?_⟩
  · have := h.ksb r hr; simp only [LawfulStore.nodeBase, hk] at this ⊢; exact this
  · obtain ⟨x0, hx0⟩ := hz sc.bv x n hx; exact h.sc r hr sc hsc x0 n hx0

/-- Word `K` (`< 32`) of a reply. -/
theorem rword_val {r K : U64} (h : r.val % 32 = 0 ∧ r ≠ 0#u64 ∧ r.val + 32 ≤ 2 ^ 64) (hK : K.val < 32) :
    (core.num.U64.wrapping_add r K).val = r.val + K.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem rPrevA_val {r : U64} (h : r.val % 32 = 0 ∧ r ≠ 0#u64 ∧ r.val + 32 ≤ 2 ^ 64) : (rPrevA r).val = r.val + 8 := by
  unfold rPrevA layout.reply.PREV; rw [rword_val h (by simp)]; rfl
theorem rNextA_val {r : U64} (h : r.val % 32 = 0 ∧ r ≠ 0#u64 ∧ r.val + 32 ≤ 2 ^ 64) : (rNextA r).val = r.val + 16 := by
  unfold rNextA layout.reply.NEXT; rw [rword_val h (by simp)]; rfl

/-- A reply word is far from what `SchedRel` reads. -/
theorem RPlaced.far {N T C R : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (h : RPlaced st N T C R c s σ)
    {r : U64} (hr : r ∈ R) {a : U64} (ha : a.val = r.val + 8 ∨ a.val = r.val + 16) : Far st T C c s σ a := by
  refine ⟨?_, fun t ht => ?_, fun sc hsc x n hx => ?_⟩
  · have := h.ksb r hr; omega
  · have := h.tcb r hr t ht; omega
  · have := h.sc r hr sc hsc x n hx; omega

theorem RPlaced.aligned {N T C R : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (h : RPlaced st N T C R c s σ)
    {r : U64} (hr : r ∈ R) {a : U64} (ha : a.val = r.val + 8 ∨ a.val = r.val + 16) : Aligned a := by
  have := (h.align r hr).1; unfold Aligned; omega

/-- The words of one SC's call stack `Ls` (newest first). -/
def StackW (m : U64 → U64) (sc : U64) (Ls : List U64) : Prop :=
  m (scReplyA sc) = Ls.headD 0#u64 ∧
  ∀ i (h : i < Ls.length), m (rPrevA Ls[i]) = Ls.getD (i + 1) 0#u64 ∧
    m (rNextA Ls[i]) = (match i with | 0 => sc ||| 1#u64 | j + 1 => Ls.getD j 0#u64)

/-- A reply on no call stack. -/
def Detached (C : Set U64) (Lst : U64 → List U64) (d : U64) : Prop := ∀ sc ∈ C, d ∉ Lst sc

/-- **The call-stack relation**, with ghost stacks `Lst`. -/
structure CallRel (m : U64 → U64) (R C : Set U64) (σ : Fl4Spec.State Unit) (Lst : U64 → List U64) : Prop where
  stack : ∀ sc ∈ C, (∃ y n, σ.kheap sc.bv = some (.schedContext y n) ∧ y.scReplies = (Lst sc).map UScalar.bv) ∧
    (∀ r ∈ Lst sc, r ∈ R) ∧ (Lst sc).Nodup ∧ StackW m sc (Lst sc)
  excl : ∀ sc ∈ C, ∀ sc' ∈ C, ∀ r, r ∈ Lst sc → r ∈ Lst sc' → sc = sc'
  reply : ∀ r ∈ R, ∃ x, σ.kheap r.bv = some (.reply x) ∧
    ∀ p, x.replySc = some p ↔ ∃ sc ∈ C, sc.bv = p ∧ (Lst sc).head? = some r
  det : ∀ d ∈ R, Detached C Lst d → (m (rNextA d) &&& 1#u64) = 0#u64 ∧
    (m (rNextA d) ≠ 0#u64 → m (rNextA d) ∈ R ∧ Detached C Lst (m (rNextA d)) ∧ m (rPrevA (m (rNextA d))) = d) ∧
    (m (rPrevA d) ≠ 0#u64 → m (rPrevA d) ∈ R ∧ Detached C Lst (m (rPrevA d)) ∧ m (rNextA (m (rPrevA d))) = d)

/-- A reply with no links that no reply links to. -/
def Isolated (m : U64 → U64) (R : Set U64) (r : U64) : Prop :=
  m (rNextA r) = 0#u64 ∧ m (rPrevA r) = 0#u64 ∧ ∀ d ∈ R, m (rNextA d) ≠ r ∧ m (rPrevA d) ≠ r

end

end

end Fl4Proofs.P3.Sched

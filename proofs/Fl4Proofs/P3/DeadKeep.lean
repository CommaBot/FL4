/-
P3 (DESIGN.md §9), CSpace: **the dead stay dead, for any step** (`JAtZ.deadP_keep`):
ScDeadStep's `deadP_sc_step` with its write set (`TFoot`) and spec step
(`ScTKw`, `LK`) replaced by what the proof reads: a dead TCB's state, bound
notification and SC (cut only), an endpoint, a notification's object, bound
TCB and SC (cut only), a reply's TCB, an SC's TCB and notification (cut
only), the SCs' `REPLY` words, and the words of `H`'s SCs outside `Z.C`.
`deadP_sc_step` is the instance for an SC step; the CSpace kinds' instances
are in XTopJointRest.
-/
import Fl4Proofs.P3.ScDeadStep
import Fl4Proofs.P3.SpecKeepC
import Fl4Proofs.P3.ScJointRest
import Fl4Proofs.P3.SlotCover
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead** (module docstring). -/
theorem JAtZ.deadP_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ') (hI' : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s') σ')
    {q : U64}
    (hT : ∀ x, σ.kheap q.bv = some (.tcb x) → tsCode x.tcbState = 0 → ∃ y, σ'.kheap q.bv = some (.tcb y) ∧
      y.tcbState = x.tcbState ∧ y.tcbBoundNotification = x.tcbBoundNotification ∧
      (y.tcbSchedContext = x.tcbSchedContext ∨ y.tcbSchedContext = none))
    (hE : ∀ x, σ.kheap q.bv = some (.endpoint x) → σ'.kheap q.bv = some (.endpoint x))
    (hN : ∀ x, σ.kheap q.bv = some (.notification x) → ∃ y, σ'.kheap q.bv = some (.notification y) ∧
      (y.ntfnObj = x.ntfnObj ∨ ∀ l, y.ntfnObj ≠ .waitingNtfn l) ∧ y.ntfnBoundTcb = x.ntfnBoundTcb ∧
      (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none))
    (hRp : ∀ x, σ.kheap q.bv = some (.reply x) → ∃ y, σ'.kheap q.bv = some (.reply y) ∧ y.replyTcb = x.replyTcb)
    (hSc : ∀ x n, σ.kheap q.bv = some (.schedContext x n) → ∃ y, σ'.kheap q.bv = some (.schedContext y n) ∧
      (y.scTcb = x.scTcb ∨ y.scTcb = none) ∧ (y.scNtfn = x.scNtfn ∨ y.scNtfn = none))
    (hRW : q ∈ Z.C → L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q))
    (hOut : ∀ z, H q = some (.sc z) → q ∉ Z.C → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K))
    (hidle : σ'.idleThread = σ.idleThread) (hAS : ActSched σ')
    (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have hI := hX.ipc
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_, fun z hq => ?_⟩
  · -- a TCB
    obtain ⟨d1, d2, d3, d4, d5⟩ := hd.1 hq
    have hqT : q ∈ Z.T := by rw [J.tcbs_eq.1]; exact hq
    obtain ⟨x, hk, hR⟩ := hI.tcb q hqT
    obtain ⟨x', hk', hR'⟩ := hI'.tcb q hqT
    have hst0 : tsCode x.tcbState = 0 := by
      have := hR.st; rw [← stA_tStA, d1] at this; unfold sched.TS_INACTIVE at this; simpa using this.symm
    obtain ⟨y, hy, hstate, hso, e⟩ := hT x hk hst0
    rw [hk'] at hy; cases hy
    have hxs : x.tcbSchedContext = none := by rw [hR.sc, d2, optRef_zero]
    have hxs' : x'.tcbSchedContext = none := by
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have h1 : (L.mem s' (tStA q)).val = (L.mem s (tStA q)).val := by rw [hR'.st, hR.st, hstate]
      rw [stA_tStA, UScalar.eq_of_val_eq h1, ← stA_tStA, d1]
    · exact optRef_eq_none (by rw [← hR'.sc, hxs'])
    · have hb : x'.tcbBoundNotification = x.tcbBoundNotification := hso
      have h1 := hR.bound
      rw [show tBoundA q = P1.boundA q from rfl, d3, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.boundA q = tBoundA q from rfl, ← hR'.bound, hb, h1])
    · intro e
      have hact := hS'.act
      have ea : L.actionW s' = nodeW st s' Z.c layout.node.SCHED_ACTION := by
        unfold P1.LawfulStore.actionW nodeW; rw [hc'.cur]
      rw [← ea, ← e] at hact
      revert hact
      cases hsa : σ'.schedulerAction with
      | resumeCurThread =>
        intro h; simp only [ActRel] at h; subst h
        rw [J.kern.h0] at hq; cases hq
      | chooseNewThread =>
        intro h; simp only [ActRel] at h; subst h
        have := J.kern.heap.align _ _ hq
        simp [P1.HKind.bits] at this
      | switchThread t =>
        intro h; simp only [ActRel] at h
        obtain ⟨-, -, ht⟩ := h
        obtain ⟨x2, scp, -, -, hk2, hsc2, -⟩ := schedulable_inv (hAS t hsa)
        rw [← ht, hk'] at hk2; cases hk2
        rw [hxs'] at hsc2; cases hsc2
    · have ei : L.idleW s' = L.idleW s := by
        unfold P1.LawfulStore.idleW
        apply P1.eq_of_bv
        have h1 := hs'.idleTh; have h2 := hs.idleTh
        unfold nodeW at h1 h2
        rw [hc'.cur, hc.cur, ← h1, ← h2, hidle]
      rw [ei]; exact d5
  · -- an endpoint
    have hqE : q ∈ Z.E := J.hset.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ep q hqE
    obtain ⟨x', hk', hR'⟩ := hI'.ep q hqE
    rw [hE x hk] at hk'; cases hk'
    rw [epState_eq, stOf_ep hR hR', ← epState_eq]; exact hd.2.1 hq
  · -- a notification
    obtain ⟨d1, d2, d3⟩ := hd.2.2.1 hq
    have hqN : q ∈ Z.N := J.hset.2.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ntfn q hqN
    obtain ⟨x', hk', hR'⟩ := hI'.ntfn q hqN
    obtain ⟨y, hy, ho, hb, e⟩ := hN x hk
    rw [hk'] at hy; cases hy
    have hxs : x.ntfnSc = none := by rw [hR.sc, show nScA q = P1.ntfnScA q from rfl, d3, optRef_zero]
    have hxs' : x'.ntfnSc = none := by
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_⟩
    · rw [epState_eq]
      have hO' := hR'.obj
      rcases ho with ho | ho
      · rw [ho] at hO'
        rw [stOf_ntfn hR.obj hO', ← epState_eq]; exact d1
      · revert hO'
        cases hx' : x'.ntfnObj with
        | waitingNtfn l => exact absurd hx' (ho l)
        | idleNtfn => intro hO'; rw [hO'.1]; decide
        | activeNtfn b => intro hO'; rw [hO'.1]; decide
    · have h1 := hR.bound
      rw [show nBoundA q = P1.ntfnBtA q from rfl, d2, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.ntfnBtA q = nBoundA q from rfl, ← hR'.bound, hb, h1])
    · exact optRef_eq_none (by rw [show P1.ntfnScA q = nScA q from rfl, ← hR'.sc, hxs'])
  · -- a reply
    have hqR : q ∈ Z.R := J.hset.2.2 q hq
    obtain ⟨x, hk, hR⟩ := hI.reply q hqR
    obtain ⟨x', hk', hR'⟩ := hI'.reply q hqR
    obtain ⟨y, hy, e⟩ := hRp x hk
    rw [hk'] at hy; cases hy
    have h1 := hR
    rw [show Endp.rTcbA q = P1.rTcbA q from rfl, hd.2.2.2.1 hq, optRef_zero] at h1
    exact optRef_eq_none (by rw [show P1.rTcbA q = Endp.rTcbA q from rfl, ← hR', e, h1])
  · -- an SC
    obtain ⟨d1, d2, d3⟩ := hd.2.2.2.2 z hq
    by_cases hqC : q ∈ Z.C
    · obtain ⟨x, n, hk, hR⟩ := hs.scs q hqC
      obtain ⟨x', n', hk', hR'⟩ := hs'.scs q hqC
      obtain ⟨y, hy, e1, e2⟩ := hSc x n hk
      rw [hk'] at hy; cases hy
      have hxt : x.scTcb = none := by rw [hR.tcb, scW_tcb, d1, optRef_zero]
      have hxn : x.scNtfn = none := by rw [hR.ntfn, scW_ntfn, d3, optRef_zero]
      refine ⟨?_, ?_, ?_⟩
      · rw [← scW_tcb]; refine optRef_eq_none ?_; rw [← hR'.tcb]
        rcases e1 with e | e
        · rw [e, hxt]
        · exact e
      · rw [hRW hqC]; exact d2
      · rw [← scW_ntfn]; refine optRef_eq_none ?_; rw [← hR'.ntfn]
        rcases e2 with e | e
        · rw [e, hxn]
        · exact e
    · refine ⟨?_, ?_, ?_⟩
      · rw [← scW_tcb, hOut z hq hqC _ (by decide) (by decide), scW_tcb]; exact d1
      · rw [scReplyA_eq', hOut z hq hqC _ (by decide) (by decide), ← scReplyA_eq']; exact d2
      · rw [← scW_ntfn, hOut z hq hqC _ (by decide) (by decide), scW_ntfn]; exact d3


/-- **An SC of `H`'s words**: within its object, aligned. -/
theorem JAtZ.scW_in {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {q : U64} {z : Nat} (hq : H q = some (.sc z)) {K : U64}
    (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    P1.Aligned (scW q K) ∧ (scW q K).val = q.val + K.val ∧ q.val + K.val + 8 ≤ q.val + 2 ^ z := by
  have hH := J.kern.heap
  have hal := hH.align q _ hq
  have hfit := hH.fits q _ hq
  have hz := hH.scmin q z hq
  simp only [P1.HKind.bits] at hal hfit
  have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
  have hq8 : q.val % 8 = 0 := by
    have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
    rw [← Nat.mod_mod_of_dvd q.val hd, hal]
  have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
  exact ⟨by show (scW q K).val % 8 = 0; rw [hv]; omega, hv, by omega⟩

/-- **A slot lies in an object of `H`** (a TCB or a CNode). -/
theorem JAtZ.slot_in_H {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : IsSlot Z.th x) :
    ∃ p k, H p = some k ∧ (∀ z, k ≠ .sc z) ∧ p.val ≤ x.val ∧ x.val + 32 ≤ p.val + 2 ^ k.bits := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  obtain ⟨p, i, hi, rfl⟩ := hx
  have hv := hi.val hJ.pl
  rcases hi with ⟨r, hp, hlt⟩ | ⟨hp, hlt⟩
  · refine ⟨p, .other (r + 5), hJ.cnode p r hp, (fun z e => by cases e), by omega, ?_⟩
    simp only [P1.HKind.bits]
    have : 32 * (i + 1) ≤ 32 * 2 ^ r := by
      have : i + 1 ≤ 2 ^ r := hlt; omega
    rw [pow_add]; omega
  · refine ⟨p, .tcb, (hJ.tcb p).1 hp, (fun z e => by cases e), by omega, ?_⟩
    simp only [P1.HKind.bits]
    have : i < tcbSlots := hlt
    simp [tcbSlots] at this; omega

/-- **`H`'s SC words are kept by slot writes** (`H`'s objects disjoint). -/
theorem JAtZ.inSlot_scKeep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (InSlot Z.th))
    {q : U64} {z : Nat} (hq : H q = some (.sc z)) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  obtain ⟨hal, hv, hf⟩ := J.scW_in hq hK8 hK
  refine hw.mem_eq hal fun ⟨x, hx, h1, h2⟩ => ?_
  obtain ⟨p, k, hp, hk, g1, g2⟩ := J.slot_in_H hx
  have hne : q ≠ p := fun e => by rw [e, hp] at hq; cases hq; exact hk _ rfl
  have := J.kern.heap.disj q _ p _ hq hp hne
  rw [show (P1.HKind.sc z).bits = z from rfl] at this
  rw [hv] at h1 h2
  rcases this with h | h <;> omega

/-- **`H`'s SC words are kept by kernel-state writes** (`H` off the block). -/
theorem JAtZ.ksW_scKeep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (KsW (L.ksb s)))
    {q : U64} {z : Nat} (hq : H q = some (.sc z)) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  obtain ⟨hal, hv, hf⟩ := J.scW_in hq hK8 hK
  have := J.kern.hks q _ hq
  simp only [P1.HKind.bits] at this
  refine hw.mem_eq hal fun h => ?_
  obtain ⟨K', h1, h2, -, e⟩ := h
  omega

/-- **`H`'s SC words are kept by scheduler writes** (`H`'s objects disjoint
from the TCBs, apart from the node and the kernel-state block). -/
theorem JAtZ.schW_scKeep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hw : P1.WritesIn st s s' (SchW (L := L) Z.T Z.c s))
    {q : U64} {z : Nat} (hq : H q = some (.sc z)) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  obtain ⟨hal, hv, hf⟩ := J.scW_in hq hK8 hK
  have hS := J.xtop.fin.1.1.1
  have hP := J.xtop.fin.1.2
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hks := J.kern.hks q _ hq
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hnd := J.kern.hnd q _ hq Z.c hcC
  simp only [P1.HKind.bits] at hks hnd
  refine hw.mem_eq hal fun hb => ?_
  rcases schW_val hc.tcbs hkf hb with ⟨y, hy, e⟩ | ⟨g1, g2⟩ | ⟨g1, g2, -⟩
  · have hHy : H y = some .tcb := J.zH.1 y hy
    have hne : q ≠ y := fun e' => by rw [e', hHy] at hq; cases hq
    have := J.kern.heap.disj q _ y _ hq hHy hne
    simp only [P1.HKind.bits] at this
    omega
  · omega
  · omega

/-- **The dead stay dead across a heap-keeping step** (`deadP_keep` with
every object but the CNodes kept, `HStep`). -/
theorem JAtZ.deadP_hstep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {G' : MdbGhost} (hX' : XTopAt (L := L) AR { Z with G := G' } s' a' σ') (hC : HStep σ σ')
    (hRW : ∀ q ∈ Z.C, L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q))
    (hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K)) (hAS : ActSched σ')
    {q : U64} (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q :=
  J.deadP_keep hX'.fin.1.1.1 hX'.ipc (fun x hx _ => let ⟨y, hy, hc⟩ := hC.tcbF hx; ⟨y, hy, hc.st, hc.ntfn, Or.inl hc.sc⟩)
    (fun x hx => (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx)
    (fun x hx => ⟨x, hC.ntfn.2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
    (fun x hx => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx, rfl⟩)
    (fun x n hx => ⟨x, hC.sc.2 hx, Or.inl rfl, Or.inl rfl⟩) (hRW q) (fun z hz _ => hOut q z hz) hC.idle hAS hd

/-- **`JCovD` across a step keeping every slot and the dead dead**
(`JCovD.same`, the MDB kept). -/
theorem JAtZ.jcov_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hks : L.ksb s' = L.ksb s)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hdead : ∀ q ∈ D, DeadP (L := L) H s' q) :
    JCovD (L := L) Z.th H Z.G D Cs s' := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  refine J.jcov.same (fun y hy _ _ => ⟨hy, hSS.capV (hsl y hy)⟩) (fun q hq _ => hdead q hq)
    fun x hx p sb fi d hc => ?_
  rw [hSS.capV (hsl x hx)] at hc
  obtain ⟨h1, h2⟩ := J.jcov.ks x hx p sb fi d hc
  exact ⟨by rw [hks]; exact h1, fun c hc' => by rw [hnb]; exact h2 c hc'⟩

theorem covered_keepC {th : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost} {lo hi : Nat}
    (hM : MdbLinks th m G) (hM' : MdbLinks th m' G') (hc : Covered m G lo hi)
    (hk : CoverKept th m m') : Covered m' G' lo hi := by
  obtain ⟨y, hy, hp, hu, hb, ht⟩ := hc
  obtain ⟨y', hy', hp', hu', eb, et⟩ := hk y ((hM.members y).1 hy).1 hp hu
  refine ⟨y', (hM'.members y').2 ⟨hy', _, capAt_capV _ _, fun h0 => ?_⟩, hp', hu', by rw [eb]; exact hb,
    by rw [et]; exact ht⟩
  rw [h0, physF_null] at hp'; cases hp'

/-- **`JCovD` across a step moving caps** (`CoverKept`, `UtKept`), the dead
set kept: nothing loses its cover, the untyped regions are the old ones. -/
theorem JAtZ.jcov_cover {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {G' : MdbGhost} (hks : L.ksb s' = L.ksb s)
    (hM' : MdbLinks Z.th (L.mem s') G')
    (hC : CoverKept Z.th (L.mem s) (L.mem s')) (hU : UtKept Z.th (L.mem s) (L.mem s'))
    (hdead : ∀ q ∈ D, DeadP (L := L) H s' q) :
    JCovD (L := L) Z.th H G' D Cs s' := by
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  refine ⟨fun q k hq => (J.jcov.th q k hq).imp_left fun hc => covered_keepC hM hM' hc hC,
    fun q k hq => (J.jcov.h q k hq).imp_left fun hc => covered_keepC hM hM' hc hC, hdead, fun x hx p sb fi d hc => ?_⟩
  obtain ⟨y, hy, fi', d', hc', -⟩ := hU x ((hM'.members x).1 hx).1 p sb fi d hc
  have hym : y ∈ Z.G.chains.flatten := (hM.members y).2 ⟨hy, _, capAt_capV _ _, by rw [hc']; simp⟩
  obtain ⟨h1, h2⟩ := J.jcov.ks y hym p sb fi' d' hc'
  exact ⟨by rw [hks]; exact h1, fun c hc' => by rw [hnb]; exact h2 c hc'⟩

/-- **`SpecFree` across a step moving caps** (`UtKept`: each untyped region
after an old one, its free index no lower or the new one full; the spec's
objects kept in kind, `KSz`; `UtInv`'s `fib` before). -/
theorem JAtZ.sfree_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    (hM' : MdbLinks Z.th (L.mem s') G') (hU : UtKept Z.th (L.mem s) (L.mem s')) (hk : KSz σ σ') :
    Sched.SpecFree (L.mem s') G' σ' := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  intro x hx p sb fi d hc o ko' ho
  obtain ⟨y, hy, fi', d', hc', hle⟩ := hU x ((hM'.members x).1 hx).1 p sb fi d hc
  have hym : y ∈ Z.G.chains.flatten := (hM.members y).2 ⟨hy, _, capAt_capV _ _, by rw [hc']; simp⟩
  obtain ⟨ko, hko, hty⟩ := hk o ko' ho
  rw [← objBits_of_aType hty]
  have hfib := J.ut.fib y hym p sb fi' d' hc'
  rcases J.sfree y hym p sb fi' d' hc' o ko hko with e | e
  · exact Or.inl e
  · right; rcases hle with h | h <;> omega

/-- **`JCs` after a slot step** (`DelInv` after given; `UtInv` from the
step's `MdbOKV`, `FinM` at every tree from `FinInv` after, `SpecFree` from
`sfree_keep`). -/
theorem JAtZ.jcs_slot {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {G' : MdbGhost} {kb : U64}
    (hM' : MdbLinks Z.th (L.mem s') G') (hMO : MdbOKV kb (L.mem s') G') (hFI : FinInv Z.th (L.mem s') σ' G')
    (hU : UtKept Z.th (L.mem s) (L.mem s')) (hk : KSz σ σ') (hD : DelInv Z.th (L.mem s')) :
    JCs (L := L) { Z with G := G' } s' σ' :=
  ⟨hD, hMO.1.2.1, fun G hG => FinM.of_links J.xtop.rel.1 hM' hG hFI.fm, J.sfree_keep hM' hU hk⟩

/-- **`JKern` across a step** keeping the kernel-state base, the core, the
current thread and SC, the original bits (new ones only at `AbsSlot`s), the
global PML4 and the arch
objects (ScJointRest's `sc_kern` for any write set). -/
theorem JAtZ.kern_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {D' : Set U64}
    (hks : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ')
    (hct : σ'.curThread = σ.curThread) (hcsc : σ'.curSc = σ.curSc)
    (horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hao : ∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = some (.archObj ao))
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hcl : L.cscW s ∉ D') : JKern (L := L) H Cs D' Z.th s' σ' := by
  have K := J.kern
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have ecw : L.curW s' = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hct]
  have ecs : L.cscW s' = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hcsc]
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  obtain ⟨pt, hpt⟩ := K.gpm
  refine ⟨fun sl h => (horig sl h).elim (K.orig sl) id, by rw [ecw, hct]; exact K.cur,
    by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
    ⟨pt, by rw [hgp]; exact hao _ _ hpt⟩, by rw [hgp]; exact K.ga, by rw [hgp]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
    fun h => hcl (by rw [ecs] at h; exact h), K.csLt, K.cs0⟩
  rw [hna, hDbg]; exact K.head


end

end

end Fl4Proofs.P3

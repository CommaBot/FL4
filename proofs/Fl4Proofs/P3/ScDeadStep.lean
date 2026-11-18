/-
P3 (DESIGN.md §9), scheduling contexts: **the dead stay dead across an SC
step** (the SC steps' dead set).

`deadP_sc_step`: from `JAtZ` before, `XTopAt` after, FL4's writes in the SC
footprint (`TFoot`), the spec step changing only scheduling fields
(`ScTKw P`, a thread changing state only if runnable before), cutting links
only outside `W` (`LK W`, ScLinkKeep), keeping the idle thread (`FK`) and
`ActSched` after: an object dead before (`DeadP`) and not in `W` is dead
after. Each `DeadP` word is read through the relation before and after:

* a TCB (in `Z.T`): its state is kept (the only state change is a runnable
  thread's, and a dead thread is inactive), its SC cut only, its bound
  notification kept; it is not the action (`ActSched`: a thread switched to
  has an SC) nor the idle thread (`FK`);
* an endpoint, a notification, a reply (in `Z.E`, `Z.N`, `Z.R`: `hset`): the
  state, bound-thread and reply-thread words are functions of the kept spec
  fields; a notification's SC cut only;
* an SC of `Z.C`: its thread and notification words by `ScRelW`, cut only;
  its `REPLY` word kept (`TFoot.keep`). An SC of `H` outside `Z.C`: no
  footprint word lies in it (`H`'s objects are disjoint, the node apart).
-/
import Fl4Proofs.P3.ScLinkKeep
import Fl4Proofs.P3.ScJointFrame
import Fl4Proofs.P3.ScJointRest
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

theorem tsCode_ne_of_runnable {ts : ThreadState} (h : runnable ts = true) : tsCode ts ≠ 0 := by
  cases ts <;> simp [runnable, tsCode] at h ⊢

end Spec

theorem optRef_eq_none {w : U64} (h : optRef w = none) : w = 0#u64 := by
  by_contra h0; rw [Sched.optRef_ne h0] at h; cases h

theorem stOf_ep {m m' : U64 → U64} {T : Set U64} {e : U64} {x : Fl4Spec.Endpoint} (h : EpObjRel m T e x)
    (h' : EpObjRel m' T e x) : stOf m' e = stOf m e := by
  cases x
  · rw [h.1, h'.1]
  · rw [h.1, h'.1]
  · rw [h.1, h'.1]

theorem stOf_ntfn {m m' : U64 → U64} {T : Set U64} {n : U64} {o : Fl4Spec.Ntfn} (h : NtfnObjRel m T n o)
    (h' : NtfnObjRel m' T n o) : stOf m' n = stOf m n := by
  cases o
  · rw [h.1, h'.1]
  · rw [h.1, h'.1]
  · rw [h.1, h'.1]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **An SC of `H` outside `Z.C` keeps its words** across an SC step: its
`TCB`, `REPLY` and `NTFN` words are in no TCB, notification or SC of the
sets, nor in the node (`H`'s objects disjoint, `hnd`). -/
theorem JAtZ.sc_out_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) {q : U64} {z : Nat}
    (hq : H q = some (.sc z)) (hqC : q ∉ Z.C) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
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
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  refine hw.mem_eq (by show (scW q K).val % 8 = 0; rw [hv]; omega) fun hb => ?_
  rcases tfoot_tcb hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
  · have hHy : H y = some .tcb := J.zH.1 y hy
    have hne : q ≠ y := fun e => by rw [e, hHy] at hq; cases hq
    have := hH.disj q _ y _ hq hHy hne
    simp only [P1.HKind.bits] at this
    omega
  · have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
    have := J.kern.hnd q _ hq Z.c hcC
    simp only [P1.HKind.bits] at this
    omega
  · have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
    have hne : q ≠ n := fun e => by rw [e, hHn] at hq; cases hq
    have := hH.disj q _ n _ hq hHn hne
    simp only [P1.HKind.bits] at this
    omega
  · have hHs := (hJ.sc sc x n (J.c0 sc hsc) hk).2
    have hne : q ≠ sc := fun e => hqC (e ▸ hsc)
    have := hH.disj q _ sc _ hq hHs hne
    simp only [P1.HKind.bits] at this
    omega


theorem Sched.Covered.mono {m : U64 → U64} {G : MdbGhost} {lo hi hi' : Nat} (h : Sched.Covered m G lo hi)
    (hh : hi' ≤ hi) : Sched.Covered m G lo hi' := by
  obtain ⟨y, hy, hp, hu, hb, ht⟩ := h
  exact ⟨y, hy, hp, hu, hb, by omega⟩

theorem range_thread (p : U64) (hfit : p.val + 2 ^ 12 ≤ 2 ^ 64) :
    baseF (.Thread p) = p.val ∧ topF (.Thread p) = p.val + 2 ^ 12 - 1 :=
  Sched.capRange (b := 12#u64) (ok_inj (ptr_eq _).symm)
    (ok_inj (by rw [← size_eq]; simp [objects.cap_size_bits, fl4_abi.consts.bits.TCB])) (by decide) hfit

theorem range_sc (p sb : U64) (hb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) :
    baseF (.SchedContext p sb) = p.val ∧ topF (.SchedContext p sb) = p.val + 2 ^ sb.val - 1 :=
  Sched.capRange (b := sb) (ok_inj (ptr_eq _).symm)
    (ok_inj (by rw [← size_eq]; simp [objects.cap_size_bits])) hb hfit

/-- **A cap in a slot covers its object after an SC step** (both kinds of
`JCovD`'s cover): the slot is in the MDB, its cap kept (slots apart), the
object `H`'s of at most the cap's size and not an `other` (so not a CNode
of `Z.th`; a TCB of `Z.th` is `H`'s, `thk`). -/
theorem JAtZ.cover_cap {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) {x : U64} (hxS : IsSlot Z.th x)
    {c : capability.Cap} (hc : capAt (L.mem s) x = ok c) (hnn : c ≠ .Null) (hph : physF c = true)
    (hu : isUt c = false) {q : U64} {b : Nat} (hr : baseF c = q.val ∧ topF c = q.val + 2 ^ b - 1)
    (hH : ∀ k, H q = some k → k.bits ≤ b ∧ ∀ z, k ≠ .other z) :
    (∀ k, Z.th q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
    (∀ k, H q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits)) := by
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj J.xtop.fin.1.1.1 h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hxm : x ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hxS, _, hc, hnn⟩
  have hC : Sched.Covered (L.mem s') Z.G q.val (q.val + 2 ^ b) :=
    Sched.covered_keep (Sched.covered_of_cap hxm (capV_of_capAt hc) hph hu hr)
      fun y hy _ _ => ⟨hy, hSS.capV (hsl y hy)⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  swap
  · have := Nat.pow_le_pow_right (n := 2) (by norm_num) (hH k hk).1
    exact hC.mono (by omega)
  rcases J.thk q k hk with rfl | ⟨r, rfl⟩
  · have hq : H q = some .tcb := (hJ.tcb q).1 hk
    have h12 := (hH _ hq).1
    simp only [P1.HKind.bits] at h12
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) h12
    exact hC.mono (by simp only [objSize]; omega)
  · exact absurd rfl ((hH _ (hJ.cnode q r hk)).2 (r + 5))

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across an SC step** (module docstring), for one
dead object `q`: if `q` is a thread whose state may change (`P`), it keeps an
`Inactive` state (`deadP_sc_stepG` for every such thread). -/
theorem JAtZ.deadP_sc_stepQ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ') {q : U64}
    (hP : ∀ x, P q.bv → σ.kheap q.bv = some (.tcb x) → tsCode x.tcbState = 0 →
      ∀ y, σ'.kheap q.bv = some (.tcb y) → y.tcbState = x.tcbState)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hS' := hX'.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have hI := hX.ipc
  have hI' := hX'.ipc
  refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_, fun hq => ?_, fun z hq => ?_⟩
  · -- a TCB
    obtain ⟨d1, d2, d3, d4, d5⟩ := hd.1 hq
    have hqT : q ∈ Z.T := by rw [J.tcbs_eq.1]; exact hq
    obtain ⟨x, hk, hR⟩ := hI.tcb q hqT
    obtain ⟨x', hk', hR'⟩ := hI'.tcb q hqT
    obtain ⟨y, hy, hso, hst⟩ := hK.tcb hk
    rw [hk'] at hy; cases hy
    have hst0 : tsCode x.tcbState = 0 := by
      have := hR.st; rw [← stA_tStA, d1] at this; unfold sched.TS_INACTIVE at this; simpa using this.symm
    have hstate : x'.tcbState = x.tcbState := by
      rcases hst with e | ⟨hp, -, -⟩
      · exact e
      · exact hP _ hp hk hst0 _ hk'
    have hxs : x.tcbSchedContext = none := by rw [hR.sc, d2, optRef_zero]
    have hxs' : x'.tcbSchedContext = none := by
      obtain ⟨y2, hy2, e⟩ := hL.tcb hW hk
      rw [hk'] at hy2; cases hy2
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have h1 : (L.mem s' (tStA q)).val = (L.mem s (tStA q)).val := by rw [hR'.st, hR.st, hstate]
      rw [stA_tStA, UScalar.eq_of_val_eq h1, ← stA_tStA, d1]
    · exact optRef_eq_none (by rw [← hR'.sc, hxs'])
    · have hb : x'.tcbBoundNotification = x.tcbBoundNotification := by rw [hso]
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
        rw [hc'.cur, hc.cur, ← h1, ← h2, hF.2.1]
      rw [ei]; exact d5
  · -- an endpoint
    have hqE : q ∈ Z.E := J.hset.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ep q hqE
    obtain ⟨x', hk', hR'⟩ := hI'.ep q hqE
    rw [hK.ep hk] at hk'; cases hk'
    rw [epState_eq, stOf_ep hR hR', ← epState_eq]; exact hd.2.1 hq
  · -- a notification
    obtain ⟨d1, d2, d3⟩ := hd.2.2.1 hq
    have hqN : q ∈ Z.N := J.hset.2.1 q hq
    obtain ⟨x, hk, hR⟩ := hI.ntfn q hqN
    obtain ⟨x', hk', hR'⟩ := hI'.ntfn q hqN
    obtain ⟨y, hy, ho, hb⟩ := hK.ntfn' hk
    rw [hk'] at hy; cases hy
    have hxs : x.ntfnSc = none := by rw [hR.sc, show nScA q = P1.ntfnScA q from rfl, d3, optRef_zero]
    have hxs' : x'.ntfnSc = none := by
      obtain ⟨y2, hy2, e⟩ := hL.ntfn hW hk
      rw [hk'] at hy2; cases hy2
      rcases e with e | e
      · rw [e, hxs]
      · exact e
    refine ⟨?_, ?_, ?_⟩
    · rw [epState_eq]
      have hO' := hR'.obj
      rw [ho] at hO'
      rw [stOf_ntfn hR.obj hO', ← epState_eq]; exact d1
    · have h1 := hR.bound
      rw [show nBoundA q = P1.ntfnBtA q from rfl, d2, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.ntfnBtA q = nBoundA q from rfl, ← hR'.bound, hb, h1])
    · exact optRef_eq_none (by rw [show P1.ntfnScA q = nScA q from rfl, ← hR'.sc, hxs'])
  · -- a reply
    have hqR : q ∈ Z.R := J.hset.2.2 q hq
    obtain ⟨x, hk, hR⟩ := hI.reply q hqR
    obtain ⟨x', hk', hR'⟩ := hI'.reply q hqR
    obtain ⟨y, hy, e⟩ := hK.reply hk
    rw [hk'] at hy; cases hy
    have h1 := hR
    rw [show Endp.rTcbA q = P1.rTcbA q from rfl, hd.2.2.2.1 hq, optRef_zero] at h1
    exact optRef_eq_none (by rw [show P1.rTcbA q = Endp.rTcbA q from rfl, ← hR', e, h1])
  · -- an SC
    obtain ⟨d1, d2, d3⟩ := hd.2.2.2.2 z hq
    by_cases hqC : q ∈ Z.C
    · obtain ⟨x, n, hk, hR⟩ := hs.scs q hqC
      obtain ⟨x', n', hk', hR'⟩ := hs'.scs q hqC
      obtain ⟨y, hy, e1, e2⟩ := hL.sc hW hk
      rw [hk'] at hy; cases hy
      have hxt : x.scTcb = none := by rw [hR.tcb, scW_tcb, d1, optRef_zero]
      have hxn : x.scNtfn = none := by rw [hR.ntfn, scW_ntfn, d3, optRef_zero]
      refine ⟨?_, ?_, ?_⟩
      · rw [← scW_tcb]; refine optRef_eq_none ?_; rw [← hR'.tcb]
        rcases e1 with e | e
        · rw [e, hxt]
        · exact e
      · rw [(TFoot.keep hS J.rp hw).2.1 q hqC]; exact d2
      · rw [← scW_ntfn]; refine optRef_eq_none ?_; rw [← hR'.ntfn]
        rcases e2 with e | e
        · rw [e, hxn]
        · exact e
    · refine ⟨?_, ?_, ?_⟩
      · rw [← scW_tcb, J.sc_out_keep hw hq hqC (by decide) (by decide), scW_tcb]; exact d1
      · rw [scReplyA_eq', J.sc_out_keep hw hq hqC (by decide) (by decide), ← scReplyA_eq']; exact d2
      · rw [← scW_ntfn, J.sc_out_keep hw hq hqC (by decide) (by decide), scW_ntfn]; exact d3

set_option maxHeartbeats 400000 in
/-- **The dead stay dead across an SC step** (module docstring); a thread
whose state may change (`P`) keeps an `Inactive` state. -/
theorem JAtZ.deadP_sc_stepG {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ')
    (hP : ∀ p x, P p → σ.kheap p = some (.tcb x) → tsCode x.tcbState = 0 →
      ∀ y, σ'.kheap p = some (.tcb y) → y.tcbState = x.tcbState)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    {q : U64} (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q :=
  J.deadP_sc_stepQ hX' hw hK (fun x => hP _ x) hL hF hAS hW hd

/-- **The dead stay dead across an SC step** (module docstring;
`deadP_sc_stepG` with the changed threads runnable). -/
theorem JAtZ.deadP_sc_step {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ')
    (hP : ∀ p x, P p → σ.kheap p = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    {q : U64} (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q :=
  J.deadP_sc_stepG hX' hw hK (fun p x hp hk h0 => absurd h0 (tsCode_ne_of_runnable (hP p x hp hk))) hL hF hAS hW hd

end

end

end Fl4Proofs.P3

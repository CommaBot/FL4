/-
P3 (line mmuAD, gen 27): **the first native scheduler step from a VM-epoch state: `possible_switch_to` at
`JAtZV V X` for any `V`** (gen 24/25 goal 2), and the generic VM-epoch frame for native steps.

* Copies over `JAtZB` (generator `scratch/mmu24_jatzb_gen.py switchJ`; proofs verbatim): `sc_out_keep`,
  `deadP_sc_stepQm`, `ymd`, `deadP_sc_stepQ`, `kw_dbg`, `kw_dbgKeep`, `tfoot_vkeep`, `vsW`, `sc_frame`, `sc_buf`,
  `sc_apart`, `sc_jpl`, `dxKeep`, `dxk`, `tfoot_td`, `sc_jcov`, `sc_kern`, `sc_utc`, `switchJ` (the copies
  already in P3/JAtZBWr — `tcbs_eq`, `deadY_tcb`, `liveX`, `zDX`, `idleW_keep`, `tcbZ` — reused). The only
  change: `sc_frame` ends in `JAtZB` and drops its `ext` entry (`J.ext.ss hSS (J.tfoot_vkeep hw)`), the one
  `J.ext` read in the chain. **`JAtZB.switchJ`** is P3/XTopJointSwitch's `JAtZ.switchJ` over `JAtZB`.
* **`JAtZV.oobj_v`**: every word of the other subsystems' objects (`OObj`: core `Z.c`'s node, the kernel-state
  block, TCB words past 256, endpoints, replies, notifications, `Z.C`'s SCs, IPC-buffer words) lies outside every
  VCPU of `V` (`HeapOK.disj` against `JVm.heap`'s `.other 15`, `JVm.ks`, `JKern.cpuCs`/`csLt`, `JCarry.bufPg` +
  `JVm.sep`).
* **`JAtZV.ofB`** (the footprint fact of gen 24 item 2, as one lemma): from `JAtZV V X` at `(s, σ)`, a post-state
  `JAtZB` at `(s', σ')` with the same sets, FL4's writes in `OObj` words other than the VCPU-list head,
  every TCB's VCPU word kept (`VKeep`) and the spec heap unchanged give `JAtZV V X` at `(s', σ')`: slots by
  `slotsSame_of`, the VCPUs' `TCB` and list words by `oobj_v`, `RunVmB` through both states' TCB relations
  (state word = `tsCode` of the same spec state), `JVm` by the unchanged heap.
* **`JAtZV.switchJ`**: `possible_switch_to` of a schedulable thread, neither current nor idle, keeps
  `JAtZV V X` (no premise beyond `JAtZ.switchJ`'s own): `JAtZB.switchJ` + `possible_switch_to_refines`
  (heap unchanged) + `possible_switch_to_sfoot` (`SFoot` ⊆ `TFoot`: `tfoot_oobj`, `VKeep.of_tfoot`; no
  kernel-state word, `SFoot.range` + `JKern.hks`), the outcomes identified by the spec's singleton result.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBWr
import Fl4Proofs.P3.XTopJointSwitch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

-- from Fl4Proofs/P3/ScDeadStep.lean
section
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 1000000 in
/-- **An SC of `H` outside `Z.C` keeps its words** across an SC step: its
`TCB`, `REPLY` and `NTFN` words are in no TCB, notification or SC of the
sets, nor in the node (`H`'s objects disjoint, `hnd`). -/
theorem JAtZB.sc_out_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
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

end


-- from Fl4Proofs/P3/ScDeadStep.lean
section
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across an SC step** (module docstring), for one
dead object `q`: if `q` is a thread whose state may change (`P`), it keeps an
`Inactive` state (`deadP_sc_stepG` for every such thread). -/
theorem JAtZB.deadP_sc_stepQm {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ') {q : U64}
    (hP : ∀ x, P q.bv → σ.kheap q.bv = some (.tcb x) → tsCode x.tcbState = 0 →
      ∀ y, σ'.kheap q.bv = some (.tcb y) → y.tcbState = x.tcbState)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    (hYm : YMemDead (L := L) H Z.C s s' q)
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
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd.1 hq
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
    refine ⟨?_, ?_, ?_, ?_, ?_, hYm.1 hq d6⟩
    · have h1 : (L.mem s' (tStA q)).val = (L.mem s (tStA q)).val := by rw [hR'.st, hR.st, hstate]
      rw [stA_tStA, UScalar.eq_of_val_eq h1, ← stA_tStA, d1]
    · exact optRef_eq_none (by rw [← hR'.sc, hxs'])
    · have hb : x'.tcbBoundNotification = x.tcbBoundNotification := by rw [hso]
      have h1 := hR.bound
      rw [show tBoundA q = P1.boundA q from rfl, d3, optRef_zero] at h1
      exact optRef_eq_none (by rw [show P1.boundA q = tBoundA q from rfl, ← hR'.bound, hb, h1])
    · intro e
      have hact := hS'.act
      have ea : L.actionW s' = Sched.nodeW st s' Z.c layout.node.SCHED_ACTION := by
        unfold P1.LawfulStore.actionW Sched.nodeW; rw [hc'.cur]
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
        unfold Sched.nodeW at h1 h2
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
    obtain ⟨d1, d2, d3, d4⟩ := hd.2.2.2.2 z hq
    by_cases hqC : q ∈ Z.C
    · obtain ⟨x, n, hk, hR⟩ := hs.scs q hqC
      obtain ⟨x', n', hk', hR'⟩ := hs'.scs q hqC
      obtain ⟨y, hy, e1, e2⟩ := hL.sc hW hk
      rw [hk'] at hy; cases hy
      have hxt : x.scTcb = none := by rw [hR.tcb, scW_tcb, d1, optRef_zero]
      have hxn : x.scNtfn = none := by rw [hR.ntfn, scW_ntfn, d3, optRef_zero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← scW_tcb]; refine optRef_eq_none ?_; rw [← hR'.tcb]
        rcases e1 with e | e
        · rw [e, hxt]
        · exact e
      · rw [(TFoot.keep hS J.rp hw).2.1 q hqC]; exact d2
      · rw [← scW_ntfn]; refine optRef_eq_none ?_; rw [← hR'.ntfn]
        rcases e2 with e | e
        · rw [e, hxn]
        · exact e
      · exact hYm.2 z hq hqC d4
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← scW_tcb, J.sc_out_keep hw hq hqC (by decide) (by decide), scW_tcb]; exact d1
      · rw [scReplyA_eq', J.sc_out_keep hw hq hqC (by decide) (by decide), ← scReplyA_eq']; exact d2
      · rw [← scW_ntfn, J.sc_out_keep hw hq hqC (by decide) (by decide), scW_ntfn]; exact d3
      · rw [scYieldFromA_eq, J.sc_out_keep hw hq hqC (by decide) (by decide), ← scYieldFromA_eq]; exact d4

end


-- from Fl4Proofs/P3/ScDeadStep.lean
section
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- `YMemDead` from the spec (`YieldRel` and `ScRelW` before and after, the
spec's fields kept null). -/
theorem JAtZB.ymd {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ') (hY' : YieldRel Z.T Z.C (L.mem s') σ') {q : U64}
    (hYD : YDeadKeep σ σ' q.bv) : YMemDead (L := L) H Z.C s s' q := by
  refine ⟨fun hq h0 => J.deadY_tcb hY' hYD (by rw [J.tcbs_eq.1]; exact hq) h0, fun z hq hqC h0 => ?_⟩
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  obtain ⟨x, n, hk, hR⟩ := hs.scs q hqC
  obtain ⟨x', n', hk', hR'⟩ := hs'.scs q hqC
  rw [scYieldFromA_eq]; refine optRef_eq_none ?_; rw [← hR'.yieldFrom]
  exact hYD.2 x _ hk (by rw [hR.yieldFrom, ← scYieldFromA_eq, h0, optRef_zero]) x' _ hk'

end


-- from Fl4Proofs/P3/ScDeadStep.lean
section
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **The dead stay dead across an SC step** (`deadP_sc_stepQm` with the
yield words read through the spec, `ymd`). -/
theorem JAtZB.deadP_sc_stepQ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    {P : Fl4Spec.ObjRef → Prop} (hK : ScTKw P σ σ') {q : U64}
    (hP : ∀ x, P q.bv → σ.kheap q.bv = some (.tcb x) → tsCode x.tcbState = 0 →
      ∀ y, σ'.kheap q.bv = some (.tcb y) → y.tcbState = x.tcbState)
    {W : Fl4Spec.ObjRef → Prop} (hL : LK W σ σ') (hF : FK σ σ') (hAS : ActSched σ')
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') (hYD : YDeadKeep σ σ' q.bv)
    (hW : ¬ W q.bv) (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q :=
  J.deadP_sc_stepQm hX' hw hK hP hL hF hAS (J.ymd hX'.fin.1.1.1 hY' hYD) hW hd

end


-- from Fl4Proofs/P3/XTopJointFinW.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **Core 0's `DEBUG_TCBS` word is kept by P1's footprint** (`KW` leaves it
out; core 0 among the cores, `JKern.cs0`). -/
theorem JAtZB.kw_dbg {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s)) :
    L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
  hw.mem_eq J.kern.dwAl fun hk => P1.dbg0_not_schedW J.blk J.kern.cs0 (Or.inl hk)

end


-- from Fl4Proofs/P3/XTopJointFinW.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **P1's footprint keeps every debug word** (`P1.Foot.dbgKeep`; KENTRY-PLAN
g2i, the `DbgKeep` of the construction sites' `LiveDN` frame). -/
theorem JAtZB.kw_dbgKeep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s)) : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
  P1.Foot.dbgKeep J.blk (fun _ h => h) hw

end


-- from Fl4Proofs/P3/ScJointFrame.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **A `TFoot` step keeps every TCB's VCPU word** (KENTRY-PLAN g2b): the
scheduler's offsets (`KFoot.ne_vcpu`) and the `YIELD_TO` words (3472). -/
theorem JAtZB.tfoot_vkeep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) : VKeep (L := L) Z.th s s' :=
  VKeep.of_tfoot J.xtop.fin.1.1.1 J.thT hw

end


-- from Fl4Proofs/P3/JointAt.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- (F1 stage 5, item 4) **`vsNamed` across a step writing `OObj` words** (`XTopAt.vsNamed_of`). -/
theorem JAtZB.vsW (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hWO : ∀ b, W b → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) :
    Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s') :=
  fun h => J.xtop.vsNamed_of (J.carry.vsNamed h) J.vsc hw hWO

end


-- from Fl4Proofs/P3/ScJointFrame.lean (EXT)
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

set_option maxHeartbeats 1000000 in
/-- **`JAtZ` across an SC step** (module docstring). -/
theorem JAtZB.sc_frame {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ')
    (hX : XTopAt (L := L) AR Z s' a' σ')
    (hcall : Sched.CallRel (L.mem s') Z.R Z.C σ' Lst') (hrf : Sched.RFree (L.mem s') Z.R Z.C σ' Lst')
    (hyl : Sched.YieldRel Z.T Z.C (L.mem s') σ') (hmcp : Sched.McpRel Z.T (L.mem s') σ')
    (hbuf : BufWordRel Z.T (L.mem s') σ')
    (hrp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ') (hap : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ')
    (hjpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ') (hjc : Sched.JCovD (L := L) Z.th H Z.G D' Cs s')
    (hkern : JKern (L := L) arI H Cs D' Z.th s' σ')
    (hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi)
    (hnsc : Sched.NSC Z.N Z.C σ') (hinv : Sched.Inv σ') (hcur : σ'.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ')
    (hown : Sched.CurOwnW Z.T Z.C σ') (hoff : Sched.OffOK σ')
    (hact : Sched.ActIdle σ') (hbsa : Sched.BlockedScActive σ') (hcr : CurRunM σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hidl : L.idleW s' = L.idleW s) (hDD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have hks : L.ksb s' = L.ksb s := hw.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj J.xtop.fin.1.1.1 h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl' : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hsl : Sched.ScLinkHyp σ' := scLink_rebuild hX J.tcbs_eq.1 (J.obj.tkw hK) hblk J.hset.2.1 hjpl J.c0
  have hsv : Sched.SchedValid σ' := schedValid_rebuild hX J.tcbs_eq.1 J.tcbs_eq.2 (J.obj.tkw hK) hblk J.hset.1
    J.hset.2.1 hcall hyl J.c0 hinv hsl
  refine ⟨hX, hcall, hrf,
    J.rrecv.frame (Sched.TFoot.keep J.xtop.fin.1.1.1 J.rp hw).2.2 (Sched.KhRB.of_sctkw hK), hyl, hmcp, hbuf,
    by rw [hks]; exact J.ks, J.thT, J.thk, J.ip, hrp, hap,
    fun n hn => by rw [hks]; exact J.nk n hn,
    fun wp hw c hc => by simp only [P1.LawfulStore.nodeBase, hks]; exact J.nodeB wp hw c hc, hjpl, J.cover.tkw hK, J.obj.tkw hK, J.zH, ?_, J.hset, J.hscC, hjc, hkern,
    J.del.of_same hSS, UtInv.of_same hM J.ut hSS, J.bound, fun G hG => ?_, hutc, hnsc, hinv, hcur, hown, hoff, hact,
    J.c0, hbsa, hsv, J.isorted.tkw hK, hsl, hcr, hblk, by rw [hks]; exact J.intL,
    J.vsc.of_eq fun y hy => hSS.capV hy,
    J.bok.keep (IpcFrKeep.of_otk hK.kh), J.fcov.ipcFr (IpcFrKeep.of_otk hK.kh),
    J.fcap.keepU (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (IpcFrKeep.of_otk hK.kh).page,
    J.liveX hX rfl rfl rfl hSS hKd hK.orig hidl (fun p hp => hjc.dead p (hDD p hp)), J.zDX hSS hDD,
    (J.carry.frame subset_rfl (IpcFrKeep.of_otk hK.kh) hK.ksz).withP
      (J.carry.devKeep J.xtop.rel.2.1.2.2.1 hks hSS hX.rel.2.1.2.2.1 (idleH_of hX (J.obj.tkw hK) J.zH.1 hjpl hinv hact))
      (J.carry.vsSame hSS hks (ArchFwd.of_ipcFr (IpcFrKeep.of_otk hK.kh)))
      (J.carry.tabKeep J.xtop.rel.2.1.2.2.1 hSS hX.rel.2.1.2.2.1 hK.ksz)
      (J.vsW hw fun b h => Sched.tfoot_oobj J.xtop.fin.1.1.1 h)⟩
  · refine SpecFree.frame J.sfree (fun x' hx' p sb fi' d hc => ⟨x', hx', fi', ?_, le_rfl⟩) hK.ksz
    rw [← hSS.capV (hsl' x' hx')]; exact hc
  · have hG0 : MdbLinks Z.th (L.mem s) G := hG.of_same_symm hSS
    have hsl' : ∀ x ∈ G.chains.flatten, IsSlot Z.th x := fun x h => ((hG0.members x).1 h).1
    exact (J.finM G hG0).of_capV fun x hx => hSS.capV (hsl' x hx)

end


-- from Fl4Proofs/P3/ScJointRest.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`BufWordRel` after an SC step.** -/
theorem JAtZB.sc_buf {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ') :
    BufWordRel Z.T (L.mem s') σ' := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  exact J.buf.frame (fun t ht => hw.mem_eq (tIpcBufA_aligned (hc.tcbs t ht)) fun hb => hb.ne_buf hS ht rfl)
    hK.bufKeep

end


-- from Fl4Proofs/P3/ScJointRest.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`SlotsApart` after an SC step.** -/
theorem JAtZB.sc_apart {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ') :
    Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ' :=
  J.apart.sc_frame hw.1 hK.szKeep

end


-- from Fl4Proofs/P3/ScJointRest.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`JPlaced` after an SC step.** -/
theorem JAtZB.sc_jpl {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ')
    (hiw : Sched.idleScW (L := L) s' = Sched.idleScW (L := L) s) :
    ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ' := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hwU : P1.WritesIn st s s' (UFoot st Z.T Z.N Z.C Z.R Z.c s σ) := hw.mono fun b hb => Or.inl hb
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := slotsSame_of_ufoot hJ.pl hS J.rp J.apart hwU
  have hIA := hJ.irqApart (c := Z.c) J.zH.1 J.zH.2.2.2 J.c0 J.zH.2.2.1 J.kern.ksbFit
  exact ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => hK.szKeep q.bv y n hq) hw.1 (irq_of_ufoot hS J.rp hIA hwU) hiw⟩

end


-- from Fl4Proofs/P3/JointAt.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **The dead set's `DeadX` after a step keeping the words it reads.** -/
theorem JAtZB.dxKeep (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} (hk : Sched.DXKeep (L := L) H Cs s s') :
    ∀ q ∈ D, Sched.DeadX (L := L) H Cs s' q := J.jcov.dxKeep hk

end


-- from Fl4Proofs/P3/JointAt.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **`DXKeep` from the debug words and the deadline words kept.** -/
theorem JAtZB.dxk (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hTd : Sched.TdKeep (L := L) H s s') :
    ∀ q ∈ D, Sched.DeadX (L := L) H Cs s' q := J.dxKeep (DXKeep.of_dbg hKd hTd)

end


-- from Fl4Proofs/P3/ScJointFrame.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **A `TFoot` step keeps every deadline word** (KENTRY-PLAN jc6e). -/
theorem JAtZB.tfoot_td {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) : Sched.TdKeep (L := L) H s s' :=
  TdKeep.of_tfoot J.xtop.fin.1.1.1 (fun _ ht => J.tcbZ ht) hw

end


-- from Fl4Proofs/P3/ScJointRest.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`JCovD` after an SC step**, the dead set shrinking to `D'`: the dead
of `D'` dead after (`hdead`), the others of `D` covered after (`hcov`). -/
theorem JAtZB.sc_jcov {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {D' : Set U64}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    (hdead : ∀ q ∈ D', Sched.DeadP (L := L) H s' q)
    (hcov : ∀ q ∈ D, q ∉ D' →
      (∀ k, Z.th q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
      (∀ k, H q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits)))
    (hidl : Sched.IdleKeep (L := L) s s')
    (hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hDD : D' ⊆ D) :
    Sched.JCovD (L := L) Z.th H Z.G D' Cs s' := by
  have hks : L.ksb s' = L.ksb s := hw.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj J.xtop.fin.1.1.1 h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hk : ∀ y ∈ Z.G.chains.flatten, physF (capV (L.mem s) y) = true → isUt (capV (L.mem s) y) = false →
      y ∈ Z.G.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y :=
    fun y hy _ _ => ⟨hy, hSS.capV (hsl y hy)⟩
  have JC := J.jcov
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, hdead,
    JC.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩,
    JC.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩,
    fun q hq => J.dxk hKd (J.tfoot_td hw) q (hDD hq)⟩
  · rcases JC.th q k hq with hc | hd | hi
    · exact Or.inl (Sched.covered_keep hc hk)
    · by_cases h : q ∈ D'
      · exact Or.inr (Or.inl h)
      · exact Or.inl ((hcov q hd h).1 k hq)
    · exact Or.inr (Or.inr ((Sched.exAt_of hidl hks).2 hi))
  · rcases JC.h q k hq with hc | hd | hi
    · exact Or.inl (Sched.covered_keep hc hk)
    · by_cases h : q ∈ D'
      · exact Or.inr (Or.inl h)
      · exact Or.inl ((hcov q hd h).2 k hq)
    · exact Or.inr (Or.inr ((Sched.exAt_of hidl hks).2 hi))

end


-- from Fl4Proofs/P3/ScJointRest.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`JKern` after an SC step**: the current thread and SC words are the
spec's, which the step keeps (`ScTKw`, `FK`); the node-0 `DEBUG_TCBS` word
kept (`hDbg`, P1-supplied); the dead set shrinking. -/
theorem JAtZB.sc_kern {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {P : Fl4Spec.ObjRef → Prop} {D' : Set U64}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ') (hF : FK σ σ')
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hD : D' ⊆ D) : JKern (L := L) arI H Cs D' Z.th s' σ' := by
  have K := J.kern
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hX'.fin.1.1.1.lists
  have ecw : L.curW s' = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu, hna, hc.cur]
    unfold Sched.nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hK.ct]
  have ecs : L.cscW s' = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu, hna, hc.cur]
    unfold Sched.nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hF.1]
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  obtain ⟨pt, hpt⟩ := K.gpm
  refine ⟨fun sl h => K.orig sl (by rw [← hK.orig]; exact h), by rw [ecw, hK.ct]; exact K.cur,
    by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
    ⟨pt, by rw [hK.arch]; exact hK.archObj hpt⟩, by rw [hK.arch]; exact K.ga, by rw [hK.arch]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, by rw [hks]; exact K.hksIn, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
    K.csLt, K.cs0, K.csN, K.tdx.frame (by rw [hK.arch])⟩
  rw [hna, hDbg]; exact K.head

end


-- from Fl4Proofs/P3/ScJointRest.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after an SC step**: the caps kept (slots
apart), the free parts zero (no SC-step word there: the TCBs are typed, the
notifications and SCs are spec objects outside it, `SpecFree`, the node is
outside every untyped cap, `JCovD`), the rest by the kept kernel state and
the node-0 `DEBUG_TCBS` word (`hDbg`, P1-supplied). -/
theorem JAtZB.sc_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj hS h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdv
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hfi := U.fiLe
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hK.cdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [hK.arch]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases tfoot_tcb hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
    · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
      have := U.free y .tcb hth
      simp only [objSize] at this; omega
    · have := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).2.1 Z.c hcC
      omega
    · obtain ⟨x, hx, -⟩ := hR.ntfn n hn
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) n.bv _ hx
      simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this
      omega
    · have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) sc.bv _ hk
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this
      omega
  · intro g h0 hf0
    rw [hK.cdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← hK.orig]; exact h), by rw [hna, hDbg]; exact r3⟩

end


-- from Fl4Proofs/P3/XTopJointSwitch.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 16000000 in
/-- **`possible_switch_to` at `J`** (module docstring). -/
theorem JAtZB.switchJ (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) (hs : Fl4Spec.schedulable t.bv σ = true) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZB (L := L) arI AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hwd := (schedulable_eq hR hS ht).trans hs
  obtain ⟨hrw, -, hmx, -⟩ := of_decide_eq_true hwd
  have hrun : P1.Runnable (L.mem s (P1.stA t)) := by rw [stA_tStA]; exact hrw
  refine WP.spec_mono (WP.spec_and (WP.spec_and (possible_switch_to_refines s σ hR hS J.inv.actReady t ht)
    (possible_switch_to_sfoot hR hS J.inv.actReady ht))
    (P1.sched.possible_switch_to.blk (Es := P1.EH H) s t J.blk htH hrun (fun _ e => by
      rw [e] at hmx; simp at hmx))) ?_
  rintro s' ⟨⟨⟨σ', he, hke, hfe, hS'⟩, hw⟩, hblk, hfoot⟩
  have mem : ((), σ') ∈ (Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ).1 := by rw [he]; exact Set.mem_singleton _
  have hR' : NtfnStateRel Z.N Z.T (L.mem s') σ' := hR.frame hS.placed hfe (KView.of_kheap hke)
  have hwK : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.kfoot_of_sfoot hw
  have hwT := WritesIn.tfoot_of_kfoot hwK
  have hK : ScTKw (fun _ => False) σ σ' := nkt_possibleSwitchTo t.bv σ _ mem
  have hX' : XTopAt (L := L) AR Z s' a σ' := xtop_sc_step hX J.ip J.nk hwT (hK.ofFalse (P := fun p => p = t.bv)) hS' hR' id
  have hq := possibleSwitchTo_qchange J.inv hs he
  have hc := possibleSwitchTo_calm J.inv hs he
  have hI' : Inv σ' := J.inv.qchange hq
  have hL : LK (fun _ => False) σ σ' := lkm_possibleSwitchTo t.bv σ _ mem
  have hN' : NSC Z.N Z.C σ' := nsc_of_lk J.nsc hK hL
  have hsok : SOK (true, true) σ σ' := pres_possibleSwitchTo (f := (true, true)) t.bv σ _ mem
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hwK, hsok⟩
  have hF : FK σ σ' := ⟨hc.2.2.1, hc.2.2.2.2.2.1, hK.isc⟩
  have hMK := mkn_possibleSwitchTo ⟨hti, htc⟩ _ mem
  have hAI : ActIdle σ' := J.act.possibleSwitchTo J.inv hs he
  have hBK : BK σ σ' := bkm_of (nkt_possibleSwitchTo t.bv) (MaxK.mk_possibleSwitchTo' t.bv) σ _ mem
  have hbsa : BlockedScActive σ' := J.bsa.bk hBK hsok
  have hcur : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases J.cur with e | hC
    · exact Or.inl (possibleSwitchTo_cn J.inv hs he e)
    · exact (hMK.mid3 hC J.off J.inv ⟨L.curW s, J.thT _ J.kern.curT, J.kern.cur.symm⟩).1
  have hown : CurOwnW Z.T Z.C σ' := J.own.sub hc (fun u hu => by rw [hq.2.1] at hu; exact hu)
  have hoff : OffOK σ' := by
    intro h0 y n hy ha
    rw [hc.2.2.2.2.1] at h0 ⊢
    rw [hc.2.2.2.1]
    rw [hc.1, hc.2.2.1] at hy
    rw [hc.2.2.1, hc.2.2.2.2.2.2.2.2] at ha
    exact J.off h0 y n hy ha
  have hcr : CurRunM σ' := by
    by_cases hr : σ'.schedulerAction = .resumeCurThread
    · have h0 : σ.schedulerAction = .resumeCurThread := by
        by_contra h
        exact possibleSwitchTo_nr J.inv hs he h hr
      right
      rcases J.curRun.resolve_left (fun h => h h0) with h | h
      · left
        intro y hy
        rw [hc.2.1, hc.1] at hy
        exact h y hy
      · right; rw [hc.2.1, hc.2.2.2.2.2.1]; exact h
    · exact Or.inl hr
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_stepQ hX' hwT hK (fun _ hp => hp.elim) hL hF hAI.1 hY' ((hsok.ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  exact ⟨σ', he, Lst', J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2) (J.sc_jcov hwT hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2) hKd subset_rfl)
    (J.sc_kern hwT hK hF hX' hDbg fun _ h => h) (J.sc_utc hwT hK hDbg) hN' hI' hcur hown hoff hAI hbsa hcr hblk hKd (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).1 J.zD⟩

end
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched

/-- **The other subsystems' words lie outside every VCPU** (module docstring). -/
theorem JAtZV.oobj_v (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {v : U64} (hv : v ∈ V) {b : U64}
    (hb : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) : b.val < v.val ∨ v.val + 32768 ≤ b.val := by
  have B := J.base
  have hvH := J.vm.heap v hv
  have dH : ∀ p k, H p = some k → k ≠ .other 15 → p.val + 2 ^ k.bits ≤ v.val ∨ v.val + 32768 ≤ p.val := by
    intro p k hp hk
    have hne : p ≠ v := fun e => by subst e; rw [hvH] at hp; cases hp; exact hk rfl
    rcases B.kern.heap.disj p k v _ hp hvH hne with h | h
    · exact Or.inl h
    · simp only [P1.HKind.bits, Nat.reducePow] at h; exact Or.inr h
  have hks := J.vm.ks v hv
  rcases hb with ⟨g1, g2⟩ | ⟨g1, g2, -⟩ | ⟨t, ht, g1, g2⟩ | ⟨e, he, g1, g2⟩ | ⟨r, hr, g1, g2⟩ | ⟨n, hn, g1, g2⟩ |
      ⟨sc, hsc, x, n, hk, hso⟩ | ⟨wp, hwp, g1, g2⟩
  · obtain ⟨Q, R0, hcq, -⟩ := B.xtop.fin.1.1.1.lists
    have hcC : Z.c ∈ Cs := hcq.cur ▸ B.kern.cpuCs
    have hc64 := B.kern.csLt Z.c hcC
    have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
    rw [hnb] at g1 g2
    omega
  · omega
  · have d := dH t _ (B.zH.1 t ht) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH e _ (B.zH.2.1 e he) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH r _ (B.zH.2.2.1 r hr) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · have d := dH n _ (B.zH.2.2.2 n hn) (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d; omega
  · obtain ⟨Tr, Cq, hJ⟩ := B.jpl
    have hH := (hJ.sc sc x n (B.c0 sc hsc) hk).2
    have d := dH sc _ hH (by intro h; cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    unfold Sched.ScObj at hso
    omega
  · obtain ⟨q, vms, hq, q1, q2⟩ := B.carry.bufPg wp hwp
    obtain ⟨y, hy⟩ := J.vm.spec v hv
    have hne : q ≠ v.bv := fun e' => by rw [e', hy] at hq; cases hq
    have eb : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := by
      simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
    rcases J.vm.sep v hv q _ hq hne with e1 | e1
    · rw [eb] at e1; omega
    · omega

/-- **The VM-epoch frame of a native step** (module docstring). -/
theorem JAtZV.ofB (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s') (hke : σ'.kheap = σ.kheap) :
    JAtZV (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have B := J.base
  have Ly := B.jvLay J.vm
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := B.xtop.slotsSame_of hw hO
  have nV : ∀ u ∈ V, ∀ b, W b → b.val < u.val ∨ u.val + 32768 ≤ b.val := fun u hu b hb => J.oobj_v hu (hO b hb)
  have kV : ∀ u ∈ V, L.mem s' (vTcbA u) = L.mem s (vTcbA u) := by
    intro u hu
    have hf := Ly.vfit u hu
    have e := lay_vTcb_val hf.2
    exact hw.mem_eq (by unfold P1.Aligned; rw [e]; omega) fun hb => by rcases nV u hu _ hb with h | h <;> omega
  have E' : JExtV (L := L) V X Z.th s' := J.extv.of_eq (fun y hy => hSS.capV hy) hv kV
  have R' : RunVmB (L := L) Z.th s' := by
    intro t ht h8
    rw [hv t ht]
    refine J.rvm t ht ?_
    obtain ⟨x, hk, -⟩ := B'.xtop.rel.2.1.1.tcb t ht
    have w' := (B'.xtop.fin.1.1.2.2.1.at_tcb (B'.thT t ht) hk).st
    rw [hke] at hk
    have w0 := (B.xtop.fin.1.1.2.2.1.at_tcb (B.thT t ht) hk).st
    rw [Sched.stA_tStA] at h8 ⊢
    apply UScalar.eq_of_val_eq
    rw [w0, ← w', h8]
  have Jv' : JVm (L := L) V H s' σ' :=
    ⟨fun u hu => by rw [hke]; exact J.vm.spec u hu, J.vm.heap, fun u hu => by rw [hw.1]; exact J.vm.ks u hu,
      fun u hu o ko ho hne => J.vm.sep u hu o ko (by rw [hke] at ho; exact ho) hne⟩
  have Vl' : VList st V Z.th s' := J.vl.writes hw fun b hb => by
    refine ⟨J.vl.lw_al Ly.vfit hb, fun hW => ?_⟩
    rcases hb with rfl | ⟨u, hu, rfl | rfl⟩
    · exact hh _ hW rfl
    · have := lay_next_val (Ly.vfit u hu).2
      rcases nV u hu _ hW with h | h <;> omega
    · have := lay_prev_val (Ly.vfit u hu).2
      rcases nV u hu _ hW with h | h <;> omega
  exact ⟨B', E', R', Jv', Vl'⟩

set_option maxHeartbeats 4000000 in
/-- **`possible_switch_to` at `JAtZV V X`** (module docstring). -/
theorem JAtZV.switchJ (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) (hs : Fl4Spec.schedulable t.bv σ = true) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZV (L := L) arI V X AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have B := J.base
  have hS := B.xtop.fin.1.1.1
  have hR := B.xtop.fin.1.1.2.2.1
  refine WP.spec_mono (WP.spec_and (WP.spec_and (B.switchJ ht hti htc hs)
    (possible_switch_to_refines s σ hR hS B.inv.actReady t ht)) (possible_switch_to_sfoot hR hS B.inv.actReady ht)) ?_
  rintro s' ⟨⟨⟨σ1, he1, Lst', B'⟩, ⟨σ2, he2, hke, -, -⟩⟩, hw⟩
  have e12 : σ2 = σ1 := by
    rw [he1] at he2
    have h := congrArg Prod.fst he2
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at h
    exact h.symm
  subst e12
  have hwT : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) :=
    WritesIn.tfoot_of_kfoot (WritesIn.kfoot_of_sfoot hw)
  have hv : VKeep (L := L) Z.th s s' := VKeep.of_tfoot hS B.thT hwT
  have hvh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val B.kern.ksbFit
  have hh : ∀ b, SFoot st Z.T Z.c s b → b ≠ P1.vHeadA st s := by
    intro b hb e
    subst e
    rcases SFoot.range hS.placed.tcb hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩
    · have d := B.kern.hks y _ (B.zH.1 y hy) (fun _ h => by cases h)
      simp only [P1.HKind.bits, Nat.reducePow] at d
      omega
    · have hnb : L.nodeBase s Z.c = (L.ksb s).val + 13568 + Z.c.val * 4288 := rfl
      omega
  exact ⟨σ2, he1, Lst', J.ofB B' hw (fun b h => tfoot_oobj hS (Or.inl (Or.inl h))) hh hv hke⟩

end

end

end

end Fl4Proofs.P3

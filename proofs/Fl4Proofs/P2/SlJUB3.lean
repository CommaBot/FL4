/-
# P2 (line slhuf, gen 4): the ReplyRecv-guarded fields of `SlPreB` across a user-word write

Completes P2/SlJUB2.lean: `SlPreRR` (`hPl`, `hy0r`, `hSu`) is carried from `s` to
`L.wr s b v` (`b` a user word) at a bundle state.

* `rr_chk_backG`: P2's `rr_chk_back` at any fault type (ReplyRecv's checks at a state agreeing
  on `R` with `X` hold at `X`, given `RrDR R X`).
* `rrDR_nu`: the words the ReplyRecv checks read at a prefix state are `NU` (the current
  thread's, fl4-sync's reply and endpoint (`SlSyncC`), the replied thread's (`ReplyInv.back`),
  its SC's head refill (`ScExtra0.bound`, `BoundInv.sact`, `SCsOK`), the bound notification's).
* `rrPl_ag`: `RRPl` at an agreeing state (node, TCB, reply, endpoint and SC words, the bitmap).
* **`SlJAt.preRR_wr`**, **`SlJAt.preB_wrF`**: `SlPreB` across a user-word write, from
  `UserOK` (`hUO` [J]), `SlSyncC` and the locks (`hl` [P]) only.
* `slQ_wrF`, **`sl_pathsKC3`**, `sl_pathsKC3_startAt`: `sl_pathsKC` with `hPBw` and `hArw`
  replaced by `hUO` [J]. Remaining premises: `hUO` [J], `hlk` [P], `hpz`, and `hSt`, `hA`,
  `hm`, `a0`.
-/
import Fl4Proofs.P2.SlJUB2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}


/-- **`rr_chk_back` (P2/AccessVmRRD.lean) at any fault type `ty`.** -/
theorem rr_chk_backG {ty : U64} {R : U64 → Prop} {X y : S} {a : A} {t rptr ep u usc : U64}
    (D : RrDR (L := L) R X t rptr ep) (G1 : Ag st R X y)
    (C : RRChecksG st ar ty y a t rptr ep u usc) :
    RRChecksG st ar ty X a t rptr ep u usc := by
  have nd' : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt y (L.cpu y) o) := fun o ho h8 => by
    rw [G1.node]; exact D.nd o ho h8
  have bm : RdBitmap (L := L) R X := ⟨D.nd l1Off (by rw [l1Off_val]; omega) (by rw [l1Off_val]),
    fun inv hinv => D.nd _ (by simp only [w64_val]; omega) (by simp only [w64_val]; omega)⟩
  have bm' : RdBitmap (L := L) R y := ⟨nd' l1Off (by rw [l1Off_val]; omega) (by rw [l1Off_val]),
    fun inv hinv => nd' _ (by simp only [w64_val]; omega) (by simp only [w64_val]; omega)⟩
  -- the receiver
  have etc : obj.Reply.tcb st rptr y = obj.Reply.tcb st rptr X :=
    ro_congr G1 (fun m z => obj.Reply.tcb m rptr z) (fun _ => rfl)
      (obj.Reply.tcb.guard (gS := PathObl.guard st R (fun _ => True)) rptr X D.rRt)
      (obj.Reply.tcb.guard (gS := PathObl.guard st R (fun _ => True)) rptr y D.rRt)
  have htcb : obj.Reply.tcb st rptr X = ok u := by rw [← etc]; exact C.tcb
  have hu : L.mem X (rTcbA rptr) = u := by
    have h0 := htcb
    rw [eq_of_spec_fd (obj.Reply.tcb.blk (L := L) X rptr)] at h0; exact ok_inj_ff h0
  have hu0 : u ≠ 0#u64 := by
    obtain ⟨b, hb, hbn⟩ := C.u0
    rw [is_null_ok] at hb; have e := ok_inj_ff hb; subst e; simpa using hbn
  obtain ⟨gSc, gAf, gDo, gPr⟩ := D.uG u hu hu0
  obtain ⟨bh, hbh, hbt⟩ := C.here
  have HF := here_facts (L := L) (show fastpath.schedulable_here st y u = ok true by rw [hbh, hbt])
  have haff : L.mem X (affA u) = L.cpu X := by rw [← G1.m _ gAf, ← G1.c]; exact HF.aff
  obtain ⟨hSt, hFt, hIq⟩ := D.uH u hu hu0 haff
  have ehere : fastpath.schedulable_here st y u = fastpath.schedulable_here st X u :=
    here_congr G1 (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])) D.tm D.rh D.dt D.cd
      gAf gDo gSc hIq
  have est : obj.Tcb.state st u y = obj.Tcb.state st u X :=
    ro_congr G1 (fun m z => obj.Tcb.state m u z) (fun _ => rfl)
      (obj.Tcb.state.guard (gS := PathObl.guard st R (fun _ => True)) u X hSt)
      (obj.Tcb.state.guard (gS := PathObl.guard st R (fun _ => True)) u y hSt)
  have eft : obj.Tcb.fault_type st u y = obj.Tcb.fault_type st u X :=
    ro_congr G1 (fun m z => obj.Tcb.fault_type m u z) (fun _ => rfl)
      (obj.Tcb.fault_type.guard (gS := PathObl.guard st R (fun _ => True)) u X hFt)
      (obj.Tcb.fault_type.guard (gS := PathObl.guard st R (fun _ => True)) u y hFt)
  have esc : obj.Tcb.sc st u y = obj.Tcb.sc st u X :=
    ro_congr G1 (fun m z => obj.Tcb.sc m u z) (fun _ => rfl)
      (obj.Tcb.sc.guard (gS := PathObl.guard st R (fun _ => True)) u X gSc)
      (obj.Tcb.sc.guard (gS := PathObl.guard st R (fun _ => True)) u y gSc)
  have hscX : L.mem X (scA u) = usc := by
    have h0 := C.sc; rw [esc, tcb_sc_ok] at h0; exact ok_inj_ff h0
  have hsc0 : usc ≠ 0#u64 := by
    obtain ⟨b, hb, hbn⟩ := C.sc0
    rw [eq_of_spec_fd (obj.Sc.is_null.spec _)] at hb; have e := ok_inj_ff hb; subst e; simpa using hbn
  have hstX : L.mem X (stA u) = sched.TS_BLOCKED_ON_REPLY := by
    obtain ⟨ist, hist, hist'⟩ := C.ust
    rw [est] at hist
    have hv := obj.Tcb.state.spec (L := L) X u
    rw [hist, WP.spec_ok] at hv
    have h5 : ist.val = 5 := by simpa using hist'
    rw [← hv]
    exact UScalar.eq_of_val_eq (by rw [h5]; simp [sched.TS_BLOCKED_ON_REPLY])
  have hH := D.uS u hu hu0 haff hstX (by rw [hscX]; exact hsc0)
  rw [hscX] at hH
  have erdy : sporadic.ready st y usc = sporadic.ready st X usc :=
    ro_congr G1 (fun m z => sporadic.ready m z usc) (fun _ => rfl)
      (sporadic.ready.guard (gS := PathObl.guard st R (fun _ => True)) X usc hH
        (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])))
      (sporadic.ready.guard (gS := PathObl.guard st R (fun _ => True)) y usc (G1.rdHead hH)
        (nd' _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])))
  have esuf : sporadic.sufficient st ar y a usc 0#u64 = sporadic.sufficient st ar X a usc 0#u64 :=
    suff_congr G1 a hH
  -- the current thread, the reply, the endpoint
  have eact : sched.action st y = sched.action st X :=
    ro_congr G1 (fun m z => sched.action m z) (fun _ => rfl)
      (sched.action.guard (gS := PathObl.guard st R (fun _ => True)) X
        (D.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])))
      (sched.action.guard (gS := PathObl.guard st R (fun _ => True)) y
        (nd' _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])))
  have esch : sched.is_schedulable st y t = sched.is_schedulable st X t :=
    ro_congr G1 (fun m z => sched.is_schedulable m z t) (fun _ => rfl)
      (is_sched_guardC (gS := PathObl.guard st R (fun _ => True)) X t D.tSt D.tSc D.tMx D.tIq)
      (is_sched_guardC (gS := PathObl.guard st R (fun _ => True)) y t D.tSt D.tSc
        (fun h0 => by rw [G1.m _ D.tSc] at h0 ⊢; exact D.tMx h0) D.tIq)
  have einfo : msg.msg_info st y t = msg.msg_info st X t :=
    ro_congr G1 (fun m z => msg.msg_info m z t) (fun _ => rfl)
      (msg.msg_info.guard (gS := PathObl.guard st R (fun _ => True)) X t D.tMi)
      (msg.msg_info.guard (gS := PathObl.guard st R (fun _ => True)) y t D.tMi)
  have enx : obj.Reply.next st rptr y = obj.Reply.next st rptr X :=
    ro_congr G1 (fun m z => obj.Reply.next m rptr z) (fun _ => rfl)
      (obj.Reply.next.guard (gS := PathObl.guard st R (fun _ => True)) X rptr D.rNx)
      (obj.Reply.next.guard (gS := PathObl.guard st R (fun _ => True)) y rptr D.rNx)
  have enh : obj.Reply.next_is_head st rptr y = obj.Reply.next_is_head st rptr X :=
    ro_congr G1 (fun m z => obj.Reply.next_is_head m rptr z) (fun _ => rfl)
      (obj.Reply.next_is_head.guard (gS := PathObl.guard st R (fun _ => True)) X rptr D.rNx)
      (obj.Reply.next_is_head.guard (gS := PathObl.guard st R (fun _ => True)) y rptr D.rNx)
  have ebn : obj.Tcb.bound_ntfn st t y = obj.Tcb.bound_ntfn st t X :=
    ro_congr G1 (fun m z => obj.Tcb.bound_ntfn m t z) (fun _ => rfl)
      (obj.Tcb.bound_ntfn.guard (gS := PathObl.guard st R (fun _ => True)) t X D.tBn)
      (obj.Tcb.bound_ntfn.guard (gS := PathObl.guard st R (fun _ => True)) t y D.tBn)
  have etsc : obj.Tcb.sc st t y = obj.Tcb.sc st t X :=
    ro_congr G1 (fun m z => obj.Tcb.sc m t z) (fun _ => rfl)
      (obj.Tcb.sc.guard (gS := PathObl.guard st R (fun _ => True)) t X D.tSc)
      (obj.Tcb.sc.guard (gS := PathObl.guard st R (fun _ => True)) t y D.tSc)
  have eep : obj.Ep.state st ep y = obj.Ep.state st ep X :=
    ro_congr G1 (fun m z => obj.Ep.state m ep z) (fun _ => rfl)
      (obj.Ep.state.guard (gS := PathObl.guard st R (fun _ => True)) ep X D.eTS)
      (obj.Ep.state.guard (gS := PathObl.guard st R (fun _ => True)) ep y D.eTS)
  have eidle : sched.idle_thread st y = sched.idle_thread st X :=
    ro_congr G1 (fun m z => sched.idle_thread m z) (fun _ => rfl)
      (sched.idle_thread.guard (gS := PathObl.guard st R (fun _ => True)) X
        (D.nd _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])))
      (sched.idle_thread.guard (gS := PathObl.guard st R (fun _ => True)) y
        (nd' _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])))
  have epu : obj.Tcb.prio st u y = obj.Tcb.prio st u X :=
    ro_congr G1 (fun m z => obj.Tcb.prio m u z) (fun _ => rfl)
      (obj.Tcb.prio.guard (gS := PathObl.guard st R (fun _ => True)) u X gPr)
      (obj.Tcb.prio.guard (gS := PathObl.guard st R (fun _ => True)) u y gPr)
  have ept : obj.Tcb.prio st t y = obj.Tcb.prio st t X :=
    ro_congr G1 (fun m z => obj.Tcb.prio m t z) (fun _ => rfl)
      (obj.Tcb.prio.guard (gS := PathObl.guard st R (fun _ => True)) t X D.tPr)
      (obj.Tcb.prio.guard (gS := PathObl.guard st R (fun _ => True)) t y D.tPr)
  have ecd : sched.cur_domain st y = sched.cur_domain st X :=
    ro_congr G1 (fun m z => sched.cur_domain m z) (fun _ => rfl)
      (sched.cur_domain.guard (gS := PathObl.guard st R (fun _ => True)) X D.cd)
      (sched.cur_domain.guard (gS := PathObl.guard st R (fun _ => True)) y (by rw [G1.k]; exact D.cd))
  have ehi : ∀ d p, sched.is_highest_prio st y d p = sched.is_highest_prio st X d p := fun d p =>
    ro_congr G1 (fun m z => sched.is_highest_prio m z d p) (fun _ => rfl)
      (sched.is_highest_prio.guard (gS := PathObl.guard st R (fun _ => True)) X d p bm)
      (sched.is_highest_prio.guard (gS := PathObl.guard st R (fun _ => True)) y d p bm')
  refine ⟨?_, ?_, ?_, htcb, C.u0, ?_, ?_, ?_, ?_, C.sc0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i, h1, h2⟩ := C.act; exact ⟨i, by rw [← eact]; exact h1, h2⟩
  · obtain ⟨b, h1, h2⟩ := C.sch; exact ⟨b, by rw [← esch]; exact h1, h2⟩
  · obtain ⟨i, h1, h2, h3⟩ := C.info; exact ⟨i, by rw [← einfo]; exact h1, h2, h3⟩
  · obtain ⟨i, h1, h2⟩ := C.ust; exact ⟨i, by rw [← est]; exact h1, h2⟩
  · obtain ⟨i, h1, h2⟩ := C.uft; exact ⟨i, by rw [← eft]; exact h1, h2⟩
  · rcases C.nxt with ⟨i, h1, h2⟩ | ⟨i, h1, h2, b, hb, hb'⟩
    · exact Or.inl ⟨i, by rw [← enx]; exact h1, h2⟩
    · exact Or.inr ⟨i, by rw [← enx]; exact h1, h2, b, by rw [← enh]; exact hb, hb'⟩
  · rw [← esc]; exact C.sc
  · obtain ⟨b, h1, h2⟩ := C.rdy; exact ⟨b, by rw [← erdy]; exact h1, h2⟩
  · obtain ⟨b, h1, h2⟩ := C.suf; exact ⟨b, by rw [← esuf]; exact h1, h2⟩
  · exact ⟨bh, by rw [← ehere]; exact hbh, hbt⟩
  · rcases C.ntfn with ⟨i, h1, h2⟩ | ⟨i, h1, h2, i7, h7, h7', i8, h8, h8'⟩
    · exact Or.inl ⟨i, by rw [← ebn]; exact h1, h2⟩
    · have hiX : obj.Tcb.bound_ntfn st t X = ok i := by rw [← ebn]; exact h1
      have hi : i = L.mem X (boundA t) := by
        have hv := obj.Tcb.bound_ntfn.val (L := L) X t
        rw [hiX, WP.spec_ok] at hv; exact hv
      have h0 : L.mem X (boundA t) ≠ 0#u64 := by rw [← hi]; exact bne_iff_ne.mp h2
      subst hi
      have ens : obj.Ntfn.state st (L.mem X (boundA t)) y = obj.Ntfn.state st (L.mem X (boundA t)) X :=
        ro_congr G1 (fun m z => obj.Ntfn.state m (L.mem X (boundA t)) z) (fun _ => rfl)
          (obj.Ntfn.state.guard (gS := PathObl.guard st R (fun _ => True)) _ X (D.ntf h0).1)
          (obj.Ntfn.state.guard (gS := PathObl.guard st R (fun _ => True)) _ y (D.ntf h0).1)
      have ensc : obj.Ntfn.sc st (L.mem X (boundA t)) y = obj.Ntfn.sc st (L.mem X (boundA t)) X :=
        ro_congr G1 (fun m z => obj.Ntfn.sc m (L.mem X (boundA t)) z) (fun _ => rfl)
          (obj.Ntfn.sc.guard (gS := PathObl.guard st R (fun _ => True)) _ X (D.ntf h0).2)
          (obj.Ntfn.sc.guard (gS := PathObl.guard st R (fun _ => True)) _ y (D.ntf h0).2)
      refine Or.inr ⟨_, hiX, h2, i7, by rw [← ens]; exact h7, h7', i8, by rw [← ensc]; exact h8, ?_⟩
      rcases h8' with h8' | ⟨h8a, i9, h9, h9'⟩
      · exact Or.inl h8'
      · exact Or.inr ⟨h8a, i9, by rw [← etsc]; exact h9, h9'⟩
  · obtain ⟨i, h1, h2⟩ := C.ep; exact ⟨i, by rw [← eep]; exact h1, h2⟩
  · obtain ⟨t1, b7, ff, e71, e72, e73, hff⟩ := C.hp
    refine ⟨t1, b7, ff, by rw [← eidle]; exact e71, e72, by rw [epu, ept] at e73; exact e73, ?_⟩
    rcases hff with h1 | ⟨h1, i11, i12, b8, h11, h12, h13, hb8⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, i11, i12, b8, by rw [← ecd]; exact h11, by rw [← epu]; exact h12,
        by rw [← ehi]; exact h13, hb8⟩

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem scs_heap {K : KLayout} {sc : U64} (h : sc ∈ K.heap.scs) : K.heap sc = some (.sc (K.heap.scBits sc)) := by
  obtain ⟨z, hz⟩ := h
  rw [hz]; simp [Heap.scBits, hz]

/-- An SC's first words are `NU`. -/
theorem nu_scw {K : KLayout} (hX : RegionOKX K) {sc : U64} {z : Nat} (hz : K.heap sc = some (.sc z)) {o : U64}
    (ho : o.val < 128) (h8 : o.val % 8 = 0) : NU K (core.num.U64.wrapping_add sc o) := by
  obtain ⟨-, am, -, rm⟩ := sc_off hX hz ho h8
  exact nu_of_region hX am (by rw [rm]; intro h; cases h)

/-- `RefillsWF` of a heap SC at an agreeing state. -/
theorem refillsWF_ag {K : KLayout} (hX : RegionOKX K) {X X' : S} (G : Ag st (NU K) X X') {sc : U64} {z zc : Nat}
    (hz : K.heap sc = some (.sc z)) (h : RefillsWF st X sc zc) : RefillsWF st X' sc zc := by
  have e1 : L.rmax X' sc = L.rmax X sc :=
    G.m _ (nu_scw hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX]))
  have e2 : L.rhead X' sc = L.rhead X sc :=
    G.m _ (nu_scw hX hz (o := layout.sc.REFILL_HEAD) (by simp [layout.sc.REFILL_HEAD]) (by simp [layout.sc.REFILL_HEAD]))
  have e3 : L.rtail X' sc = L.rtail X sc :=
    G.m _ (nu_scw hX hz (o := layout.sc.REFILL_TAIL) (by simp [layout.sc.REFILL_TAIL]) (by simp [layout.sc.REFILL_TAIL]))
  exact ⟨h.placed, by rw [e1]; exact h.min_le, by rw [e1]; exact h.le_abs, by rw [e1, e2]; exact h.head_lt,
    by rw [e1, e3]; exact h.tail_lt⟩

variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {Cs Ω Sg Ac : Set U64}

/-- **The ReplyRecv checks' read words at a prefix state are `NU`** (`RrDR (NU K)`). -/
theorem rrDR_nu (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hC : SlSyncC st n found s) (hS : ¬ SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    RrDR (L := L) (NU K) X (L.curW s) found.1 found.2 := by
  have hX := B.regionOKX
  obtain ⟨hk, hcp⟩ := B.kc
  have C := slCom_nu ar hA B E LP
  have hcH := E.hSt.1
  obtain ⟨hrp, hep⟩ := B.rrG hC.fd hS (hC.arm hS)
  obtain ⟨⟨Q, Rq, hq⟩, hB, hXI, -, hSC⟩ := E.hI a X a1 LP
  have hX0 := hXI.2.2.toScExtra0
  have tw : ∀ y, K.heap y = some .tcb → ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      NU K (core.num.U64.wrapping_add y o) := fun y hy o h1 h2 h3 => nu_tcb hX hy h1 h2 h3
  have uT : ∀ u, L.mem X (rTcbA found.1) = u → u ≠ 0#u64 → K.heap u = some .tcb := fun u hu hu0 => by
    obtain ⟨-, hT', -, -⟩ := hXI.2.1.back _ hrp (by rw [hu]; exact hu0)
    rw [hu] at hT'; exact hT'
  obtain ⟨KM, hKM, eKM⟩ := regA_eq (E.hT _ E.hcT) (r := layout.reg.MSG_INFO)
    (by simp [layout.reg.MSG_INFO])
  refine ⟨C.nd, C.dt, C.cd, C.tm, C.rh, tw _ hcH layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)
    (by rw [st_val]), tw _ hcH 3464#u64 (by simp) (by simp) (by simp), fun h0 => ?_,
    tw _ hcH 3592#u64 (by simp) (by simp) (by simp), ?_, tw _ hcH 3368#u64 (by simp) (by simp) (by simp),
    tw _ hcH 3448#u64 (by simp) (by simp) (by simp), fun h0 => ?_,
    nu_rp hX hrp (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB]),
    nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT]),
    nu_ep hX hep (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE]),
    fun u hu hu0 => ?_, fun u hu hu0 _ => ?_, fun u hu hu0 _ hst hsc => ?_⟩
  · have hz := scs_heap (K := K) (hX0.bound _ hcH h0).1
    exact nu_scw hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])
  · have hKM' : KM.val = 256 + 8 * layout.reg.MSG_INFO.val := hKM
    rw [eKM]
    exact tw _ hcH KM (by rw [hKM']; simp [layout.reg.MSG_INFO]) (by rw [hKM']; simp [layout.reg.MSG_INFO])
      (by rw [hKM']; simp [layout.reg.MSG_INFO])
  · have eB : L.mem X (boundA (L.curW s)) = L.mem s (boundA (L.curW s)) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hcH 3368#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT hcH hk hcp hcH (by simp) (by simp) (by simp) (by simp))
    have hn := (ntf_of ar hA hX (slSets_conv K) E hk hcp LP (by rw [← eB]; exact h0)).1
    rw [eB]
    obtain ⟨r1, -, a1⟩ := hX.ntW _ hn layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE])
      (by simp [layout.ntfn.TAIL_STATE])
    obtain ⟨r2, -, a2⟩ := hX.ntW _ hn layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])
    exact ⟨nu_of_region hX a1 (by rw [r1]; intro h; cases h), nu_of_region hX a2 (by rw [r2]; intro h; cases h)⟩
  · have hu' := uT u hu hu0
    exact ⟨tw _ hu' 3464#u64 (by simp) (by simp) (by simp), tw _ hu' 3520#u64 (by simp) (by simp) (by simp),
      tw _ hu' 3432#u64 (by simp) (by simp) (by simp), tw _ hu' 3448#u64 (by simp) (by simp) (by simp)⟩
  · have hu' := uT u hu hu0
    exact ⟨tw _ hu' layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega) (by rw [st_val]),
      tw _ hu' 3376#u64 (by simp) (by simp) (by simp), tw _ hu' 3592#u64 (by simp) (by simp) (by simp)⟩
  · have huT : u ∈ K.heap.tcbs := uT u hu hu0
    have hcS := (hX0.bound u huT hsc).1
    have hact := hB.sact u huT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hst)))))) hsc
    have hWF := (hSC.all _ hcS).1 ((hSC.act _ hcS).1 hact)
    have hz := scs_heap (K := K) hcS
    exact ScAcc.head (R := NU K) (W := fun _ => True)
      ⟨fun b ha hb => nu_sc hX hz ha hb, fun _ _ _ => trivial, trivial⟩ hWF

/-- **`RRPl` at an agreeing state.** -/
theorem rrPl_ag {X X' : S} {t rptr ep u usc : U64} (hX : RegionOKX K)
    (hnd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → NU K (L.nodeAt X (L.cpu X) o))
    (hrp : K.heap rptr = some .reply) (hep : K.heap ep = some .ep)
    (BX : BXI st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac X)
    (G : Ag st (NU K) X X')
    (P : RRPl (L := L) K.heap.tcbs Cs Ω Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits X t rptr ep u usc) :
    RRPl (L := L) K.heap.tcbs Cs Ω Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits X' t rptr ep u usc := by
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem X' (L.nodeAt X' (L.cpu X') o) = L.mem X (L.nodeAt X (L.cpu X) o) := fun o ho h8 => by
    rw [G.node]; exact G.m _ (hnd o ho h8)
  have enb : ∀ c, L.nodeBase X' c = L.nodeBase X c := fun c => by simp [LawfulStore.nodeBase, G.k]
  have eT : ∀ y ∈ K.heap.tcbs, ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      L.mem X' (core.num.U64.wrapping_add y o) = L.mem X (core.num.U64.wrapping_add y o) :=
    fun y hy o h1 h2 h3 => G.m _ (nu_tcb hX hy h1 h2 h3)
  have eNx : L.mem X' (rNextA rptr) = L.mem X (rNextA rptr) :=
    G.m _ (nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT]))
  have ePv : L.mem X' (rPrevA rptr) = L.mem X (rPrevA rptr) :=
    G.m _ (nu_rp hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV]))
  have eSu : L.mem X' (scA u) = L.mem X (scA u) := eT u P.hu 3464#u64 (by simp) (by simp) (by simp)
  have eBn : L.mem X' (boundA t) = L.mem X (boundA t) := eT t P.ht 3368#u64 (by simp) (by simp) (by simp)
  have eHd : L.mem X' (epHeadA ep) = L.mem X (epHeadA ep) :=
    G.m _ (nu_ep hX hep (o := layout.ep.HEAD) (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD]))
  have hO := P.hO
  have hSg := P.hSg
  obtain ⟨NE, hBM⟩ := P.hBM
  exact
  { P with
    hN := by rw [G.c]; exact NodePlaced.of_ksb G.k P.hN
    hcC := by rw [G.c]; exact P.hcC
    hΩ := fun a ha => (P.hΩ a ha).ksb G.k
    hSg := ⟨hSg.sub, by rw [G.k]; exact hSg.ks, by rw [G.k]; exact hSg.ksΩ⟩
    hO := by cases hO; constructor <;> assumption
    hnx := by rw [eNx]; exact P.hnx
    hpv := by rw [ePv]; exact P.hpv
    husc := by rw [eSu]; exact P.husc
    hWF := refillsWF_ag hX G (scs_heap P.hcS) P.hWF
    hEN := ⟨fun c hc => by rw [enb]; exact P.hEN.1 c hc, by rw [G.k]; exact P.hEN.2⟩
    hq0 := by rw [eHd]; exact P.hq0
    hcur := by
      unfold LawfulStore.curW
      rw [eN _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]
      exact P.hcur
    hNt := by
      rw [eBn]
      intro h0
      obtain ⟨a1, a2, a3, a4⟩ := P.hNt h0
      exact ⟨a1, a2, ⟨fun c hc => by rw [enb]; exact a3.1 c hc, by rw [G.k]; exact a3.2⟩, a4⟩
    hTM := by
      rw [eN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])]; exact P.hTM
    hRel := by
      rw [eN _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])]
      intro h0
      obtain ⟨hT', zc, hwf, hin⟩ := P.hRel h0
      obtain ⟨-, hscS, -⟩ := bxi_rh BX h0
      rw [show L.mem X' (scA (L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD))) =
          L.mem X (scA (L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD))) from
        eT _ hT' 3464#u64 (by simp) (by simp) (by simp)]
      exact ⟨hT', zc, refillsWF_ag hX G (scs_heap hscS) hwf, hin⟩
    hBM := by
      refine ⟨NE, ?_⟩
      rw [G.c]
      refine BitmapOK.agree hBM ?_ (fun g hg => ?_)
      · unfold LawfulStore.l1W
        rw [nodeAt_of_ksb G.k]
        exact G.m _ (hnd l1Off (by simp [l1Off]) (by simp [l1Off]))
      · unfold LawfulStore.l2W
        rw [nodeAt_of_ksb G.k]
        exact G.m _ (hnd (l2Off g) (by simp only [l2Off, w64_val]; omega) (by simp only [l2Off, w64_val]; omega)) }

/-- **The ReplyRecv-guarded fields of `SlPreB` across a user-word write** at a bundle state. -/
theorem SlJAt.preRR_wr (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hC : SlSyncC st n found s) {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s) :
    SlPreRR (st := st) ar K Locks found K.heap.tcbs Cs Ω Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits (L.wr s b v) := by
  have hX := B.regionOKX
  have ecur := B.curW_wr hb hba v
  have etr := B.trap_wr hb hba v
  have rws := B.slRWS_wr hb hba v Locks hl
  have back : ∀ a X' a1, LocalPre (st := st) ar (L.wr s b v) a (X', a1) →
      ∃ X, LocalPre (st := st) ar s a (X, a1) ∧ Ag st (NU K) X X' :=
    fun a X' a1 LP' => B.lp_wr ar hA E.hT E.hN E.hcT E.hSt.1 hb hba v LP'
  refine ⟨fun hS' a X' a1 LP' u usc C => ?_, fun hS' a X' a1 LP' u usc C => ?_,
    fun hS' a X' a1 LP' u usc C => ?_⟩
  · have hS : ¬ SlTrap st s := fun h => hS' (etr.2 h)
    rw [ecur] at C ⊢
    obtain ⟨X, LP, G⟩ := back a X' a1 LP'
    obtain ⟨hrp, hep⟩ := B.rrG hC.fd hS (hC.arm hS)
    have C0 := rr_chk_backG (rrDR_nu ar hA B E hC hS LP) G C
    exact rrPl_ag hX (slCom_nu ar hA B E LP).nd hrp hep (E.hI a X a1 LP) G (E.hPl hS a X a1 LP u usc C0)
  · have hS : ¬ SlTrap st s := fun h => hS' (etr.2 h)
    rw [ecur] at C
    obtain ⟨X, LP, G⟩ := back a X' a1 LP'
    have C0 := rr_chk_backG (rrDR_nu ar hA B E hC hS LP) G C
    have hu := (E.hSu hS a X a1 LP u usc C0).1
    rw [G.m (yieldA u) (nu_tcb hX hu (o := 3472#u64) (by simp) (by simp) (by simp))]
    exact E.hy0r hS a X a1 LP u usc C0
  · have hS : ¬ SlTrap st s := fun h => hS' (etr.2 h)
    rw [ecur] at C ⊢
    obtain ⟨X, LP, G⟩ := back a X' a1 LP'
    have C0 := rr_chk_backG (rrDR_nu ar hA B E hC hS LP) G C
    obtain ⟨h1, h2, h3, h4, h5⟩ := E.hSu hS a X a1 LP u usc C0
    rw [L.cpu_wr, hl, rws.2]
    exact ⟨h1, safe0_wr hX hb hba v h1 h2, h3, h4, h5⟩

/-- **`SlPreB` across a user-word write** at a bundle state, from P1's `UserOK` for the layout's
user words (`hUO` [J]), fl4-sync's contract `SlSyncC` and the locks (`hl` [P]). -/
theorem SlJAt.preB_wrF (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hUO : UserOK st K.heap.tcbs Cs Ω K.heap K.user s) (hC : SlSyncC st n found s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s) :
    SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v) :=
  B.preB_wr ar hA E hUO hC hb hba v hl (B.preRR_wr ar hA E hC hb hba v hl)

end

/-! ## The syscall local path with `hPBw`, `hArw` discharged -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Locks : S → U64 → Prop}
variable {A : Type}
variable {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **`hQ` for `SlQ` from `UserOK` and the locks** (`hUO` [J], `hlk` [P]). -/
theorem slQ_wrF (ar : machine.Arch A) (hA : P0.ArchTotal ar)
    (hUO : ∀ K s, SlJAt (L := L) K s → UserOK st K.heap.tcbs Cs Ω K.heap K.user s)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ K m s b v, SlJAt (L := L) K s → SlQ st ar Locks n found Cs Ω Sg Ac K m s → b ∈ K.user →
      Aligned b → SlQ st ar Locks n found Cs Ω Sg Ac K m (L.wr s b v) :=
  fun K m s b v hJ q hb hba =>
    have hl := hlk K s b v hJ hb hba
    ⟨hJ.preB_wrF ar hA q.1 (hUO K s hJ) q.2.2.1 hb hba v hl, hJ.entL_wr hb hba v hl q.2.1,
      hJ.syncC_wr hb hba v q.2.2.1, hJ.accR_wr ar hA q.1 hb hba v hl q.2.2.2⟩

/-- **The syscall local path with the canonical `Q`, its frame premises discharged**
(`sl_pathsKC` without `hPBw` / `hArw`). Premises: `hUO` [J] (P1's `UserOK` for the layout's
user words at every bundle state), `hlk` [P], `hpz`, and `hSt`, `hA`, `hm`, `a0`. -/
noncomputable def sl_pathsKC3 (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hUO : ∀ K s, SlJAt (L := L) K s → UserOK st K.heap.tcbs Cs Ω K.heap K.user s)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
        (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  sl_pathsKF (Locks := Locks) ar hSt hA hm a0 (SlQ st ar Locks n found Cs Ω Sg Ac)
    (fun _ _ _ _ q => q.1) (fun _ _ _ _ q => q.2.1) (fun _ _ _ _ q => q.2.2.1) (fun _ _ _ _ q => q.2.2.2)
    (slQ_wrF ar hA hUO hlk) hlk hpz

/-- **`StartAt` for `sl_pathsKC3`**. -/
theorem sl_pathsKC3_startAt (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hUO : ∀ K s, SlJAt (L := L) K s → UserOK st K.heap.tcbs Cs Ω K.heap K.user s)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
        (SlRS (st := st) K Locks))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : SlQ st ar Locks n found Cs Ω Sg Ac K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsKC3 (Locks := Locks) ar hSt hA hm a0 hUO hlk hpz () K m hK hU) c hs μ
      ((sl_pathsKC3 (Locks := Locks) ar hSt hA hm a0 hUO hlk hpz () K m hK hU).body σ a) :=
  sl_pathsKF_startAt ar hSt hA hm a0 _ _ _ _ _ (slQ_wrF ar hA hUO hlk) hlk hpz K m hK hU a hJ hq hc hl hμ

end

end Fl4Proofs.P2.PathObl

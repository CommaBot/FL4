/-
# P2: the VM ReplyRecv local path's declines (line p2e, VM paths)

`PathObl.dec_alt` for `syscall.handle_reply_recv_vm_local` (`found = (rptr, ep)`), with the read set
`IoRS K Locks s` and the decline set `IoDS s` (the current thread's `FAULT_IP`, which the prefix writes,
and the two node words `update_timestamp` writes), and the guarded declined runs `PathSide` /
`ReadOnce` use. The counterpart of `P2/AccessVmDec.lean` for the VM-fault path.

* `rrTail_fst`: P1's `rrTail`, when it returns, accepts; `rr_found_chk`: under the checks
  `RRChecksG … VMFault` the fast path is `rrTail`;
* `is_sched_guardC`: `is_schedulable` on a store answering as `st`, the SC's `REFILL_MAX` only when the
  SC is not null;
* `RrDR`: the words a declining fast path reads at its state `X` (the receiver `u` = the reply's
  `TCB`: its gate words; its `STATE` / `FAULT_TYPE` / `IN_Q` when homed here; its SC's head refill when
  homed here, `BLOCKED_ON_REPLY` and with an SC); `rr_found_guard_dec`, `rr_local_guard_dec`: **a
  declined run on `st` runs the same on any store answering as `st` on those words**, and on the
  receiver's `STATE` / `FAULT_TYPE` when it is homed elsewhere (`hrep`), writing the prefix words as `st`;
* `VmRRPre`: the entry facts (`VmRPre`, the found objects typed, `RdTab`); `rr_dr`: `RrDR` for
  `IoRS s` at the state after the prefix; `RrDR.alt`: moved to an alternative (`Ag` on `IoRS s`);
* `rr_chk_back`: checks passing at an alternative's dispatch state pass at the entry's;
  **`rr_alt_not_acc`**: a run that declines at `s` is accepted at no alternative;
* `RrRep`: the receiver's `STATE` / `FAULT_TYPE` words when it is homed on another core;
  **`rr_dec_tr`**: a declined run at an alternative on `PathObl.guard st R'' (IoDS s)`, `R''` holding
  `IoRS s` and `RrRep`; `rr_dec_top`: on any store reading as `st` and writing `IoDS s` as `st`;
* **`rr_dec_alt`**: `PathObl.dec_alt`.

Premises: `VmRPre`'s (`P2/AccessVmRRA.lean`), `RegionOK` / `IoLayA` [J] (`rr_dec_alt`), `RdTab` [J]
(as `rr_vm_acc`'s `hTab`), and
* `hrR` [P]: fl4-sync's `local_syscall` found `rptr` through the current thread's reply capability,
  so P1's capability typing (`CapTyped`, as `rrPl_lkG`'s `hrR`) makes it one of P1's reply objects;
* `hpE` [P]: likewise `ep` through its endpoint capability: an endpoint of P1's heap (`rrPl_lkG`'s
  `hpH`).

The fast path (the extraction, `fastpath_vm::reply_recv_vm_found`) reads the receiver's `STATE`,
`FAULT_TYPE` and `SC` before `schedulable_here` checks its `AFFINITY`, and its SC's refills only after:
for a receiver homed elsewhere a declining run reads the two home-owned words `STATE` / `FAULT_TYPE`
(the `SC` word is a gate word), each once (`RrRep`).
-/
import Fl4Proofs.P2.AccessVmRRM
import Fl4Proofs.P2.AccessVmDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout fld own GateField TimerField GField RegionOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}

/-! ## The tail accepts; the checks give the tail -/

theorem rrTail_fst {s : S} {a : A} {t rptr ep u usc : U64} {r : Bool × S × A}
    (h : rrTail st ar s a t rptr ep u usc = ok r) : r.1 = true := by
  unfold rrTail at h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨_, _⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨restart, _, _⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  cases restart
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨⟨_, _⟩, -, h⟩ := bind_eq_ok h
    exact (congrArg Prod.fst (ok_inj_ff h)).symm
  · simp only [↓reduceIte] at h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨_, -, h⟩ := bind_eq_ok h
    obtain ⟨⟨_, _⟩, -, h⟩ := bind_eq_ok h
    exact (congrArg Prod.fst (ok_inj_ff h)).symm

set_option maxHeartbeats 4000000 in
/-- **Under the checks the fast path is `rrTail`.** -/
theorem rr_found_chk {X : S} {a : A} {t : obj.Tcb} {rptr ep u usc : U64}
    (C : RRChecksG st ar fl4_abi.consts.fault.VMFault X a t rptr ep u usc) :
    fastpath_vm.reply_recv_vm_found st ar X a t rptr ep = rrTail st ar X a t rptr ep u usc := by
  unfold fastpath_vm.reply_recv_vm_found
  obtain ⟨i0, ha0, hna⟩ := C.act
  rw [ha0]; simp only [bind_ok]
  rw [if_neg hna]
  obtain ⟨b0, hs0, hb0⟩ := C.sch
  rw [hs0]; simp only [bind_ok]
  rw [if_pos hb0]
  obtain ⟨info, hi, hi1, hi2⟩ := C.info
  rw [hi]; simp only [bind_ok]
  rw [if_neg hi1, if_neg hi2]
  rw [C.tcb]; simp only [bind_ok]
  obtain ⟨bn, hbn, hbn'⟩ := C.u0
  rw [hbn]; simp only [bind_ok]; rw [if_neg hbn']
  obtain ⟨ist, hist, hist'⟩ := C.ust
  rw [hist]; simp only [bind_ok]; rw [if_neg hist']
  obtain ⟨ift, hift, hift'⟩ := C.uft
  rw [hift]; simp only [bind_ok]; rw [if_neg hift']
  rcases C.nxt with ⟨i4, hn4, hn4'⟩ | ⟨i4, hn4, hn4', bh, hbh, hbh'⟩
  on_goal 1 => rw [hn4]; simp only [bind_ok]; rw [if_neg hn4']
  on_goal 2 =>
    rw [hn4]; simp only [bind_ok]; rw [if_pos hn4', hbh]
    simp only [bind_ok]; rw [if_neg hbh']
  all_goals
    rw [C.sc]; simp only [bind_ok]
    obtain ⟨b3, hb3, hb3'⟩ := C.sc0
    rw [hb3]; simp only [bind_ok]; rw [if_neg hb3']
    obtain ⟨b6, hb6, hb6'⟩ := C.here
    rw [hb6]; simp only [bind_ok]
    rw [if_pos hb6']
    obtain ⟨b4, hb4, hb4'⟩ := C.rdy
    rw [hb4]; simp only [bind_ok]
    rw [if_pos hb4']
    obtain ⟨b5, hb5, hb5'⟩ := C.suf
    rw [hb5]; simp only [bind_ok]
    rw [if_pos hb5']
    rcases C.ntfn with ⟨i6, h6, h6'⟩ | ⟨i6, h6, h6', i7, h7, h7', i8, h8, h8'⟩
    on_goal 1 => rw [h6]; simp only [bind_ok]; rw [if_neg h6']
    on_goal 2 =>
      rw [h6]; simp only [bind_ok]
      rw [if_pos h6', h7]; simp only [bind_ok]
      rw [if_neg h7', h8]; simp only [bind_ok]
      rcases h8' with h8' | ⟨h8a, i9, h9, h9'⟩
      on_goal 1 => rw [if_neg h8']
      on_goal 2 => rw [if_pos h8a, h9]; simp only [bind_ok]; rw [if_neg h9']
    all_goals
      obtain ⟨i10, h10, h10'⟩ := C.ep
      rw [h10]; simp only [bind_ok]; rw [if_neg h10']
      obtain ⟨t1, b7, ff, e71, e72, e73, hff⟩ := C.hp
      rw [e71]; simp only [bind_ok]
      rw [e72]; simp only [bind_ok]
      by_cases hb7 : b7 = true
      on_goal 1 =>
        rw [if_pos hb7] at e73 ⊢
        cases ok_inj_ff e73
        simp only [bind_ok]
      on_goal 2 =>
        rw [if_neg hb7] at e73 ⊢
        obtain ⟨j1, hj1, e'⟩ := bind_eq_ok e73
        obtain ⟨j2, hj2, e''⟩ := bind_eq_ok e'
        rw [hj1]; simp only [bind_ok]; rw [hj2]; simp only [bind_ok]
        by_cases hlt : j1 < j2
        on_goal 1 => rw [if_pos hlt] at e'' ⊢; cases ok_inj_ff e''; simp only [bind_ok]
        on_goal 2 => rw [if_neg hlt] at e'' ⊢; cases ok_inj_ff e''; simp only [bind_ok]
      all_goals
        rcases hff with hff | ⟨hff, i11, i12, b8, h11, h12, h13, hb8⟩
        · first
            | exact absurd rfl hff
            | (simp only [Bool.false_eq_true, ↓reduceIte]; rfl)
        · first
            | exact (Bool.false_ne_true hff).elim
            | (simp only [↓reduceIte]
               rw [h11]; simp only [bind_ok]
               first
                 | (rw [h12]; simp only [bind_ok])
                 | (rw [hj1] at h12; cases ok_inj_ff h12)
               rw [h13]; simp only [bind_ok]
               rw [if_pos hb8]; rfl)

/-! ## The words a declining fast path reads -/

/-- **The words a declining ReplyRecv fast path reads** at its state `X` (current thread `t`, reply
`rptr`, endpoint `ep`; the receiver `u` the reply's `TCB` word). -/
structure RrDR (R : U64 → Prop) (X : S) (t rptr ep : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)
  tm : L.mem X (tmA (L := L) X) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64)
  rh : L.mem X (rhA (L := L) X) ≠ 0#u64 → R (scA (L.mem X (rhA (L := L) X))) ∧
    RdHead (L := L) R X (L.mem X (scA (L.mem X (rhA (L := L) X))))
  tSt : R (stA t)
  tSc : R (scA t)
  tMx : L.mem X (scA t) ≠ 0#u64 → R (maxA (L.mem X (scA t)))
  tIq : R (inqA t)
  tMi : R (regA t layout.reg.MSG_INFO)
  tBn : R (boundA t)
  tPr : R (prioA t)
  ntf : L.mem X (boundA t) ≠ 0#u64 →
    R (core.num.U64.wrapping_add (L.mem X (boundA t)) layout.ntfn.TAIL_STATE) ∧
    R (core.num.U64.wrapping_add (L.mem X (boundA t)) layout.ntfn.SC)
  rRt : R (rTcbA rptr)
  rNx : R (rNextA rptr)
  eTS : R (epTSA ep)
  uG : ∀ u, L.mem X (rTcbA rptr) = u → u ≠ 0#u64 →
    R (scA u) ∧ R (affA u) ∧ R (core.num.U64.wrapping_add u 3432#u64) ∧ R (prioA u)
  uH : ∀ u, L.mem X (rTcbA rptr) = u → u ≠ 0#u64 → L.mem X (affA u) = L.cpu X →
    R (stA u) ∧ R (core.num.U64.wrapping_add u 3376#u64) ∧ R (inqA u)
  uS : ∀ u, L.mem X (rTcbA rptr) = u → u ≠ 0#u64 → L.mem X (affA u) = L.cpu X →
    L.mem X (stA u) = sched.TS_BLOCKED_ON_REPLY → L.mem X (scA u) ≠ 0#u64 →
    RdHead (L := L) R X (L.mem X (scA u))

theorem rdHead_top (X : S) (c : U64) : RdHead (L := L) (fun _ => True) X c := by
  unfold RdHead; exact ⟨trivial, trivial, trivial⟩

/-- Every store reads all words. -/
theorem RrDR.top (X : S) (t rptr ep : U64) : RrDR (L := L) (fun _ => True) X t rptr ep :=
  ⟨fun _ _ _ => trivial, trivial, trivial, fun _ => trivial, fun _ => ⟨trivial, rdHead_top X _⟩, trivial,
    trivial, fun _ => trivial, trivial, trivial, trivial, trivial, fun _ => ⟨trivial, trivial⟩, trivial, trivial,
    trivial, fun _ _ _ => ⟨trivial, trivial, trivial, trivial⟩, fun _ _ _ _ => ⟨trivial, trivial, trivial⟩,
    fun _ _ _ _ _ _ => rdHead_top X _⟩

/-- **`RrDR` at an alternative state** (`Ag` on `R`). -/
theorem RrDR.alt {R R' : U64 → Prop} {X y : S} {t rptr ep : U64} (D : RrDR (L := L) R X t rptr ep)
    (G : Ag st R X y) (hRR : ∀ b, R b → R' b) : RrDR (L := L) R' y t rptr ep := by
  have etm : L.mem y (tmA (L := L) y) = L.mem X (tmA (L := L) X) := by
    show L.mem y (L.nodeAt y (L.cpu y) layout.node.TIMER_MIN) = L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)
    rw [G.node]; exact G.m _ (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
  have erh : L.mem y (rhA (L := L) y) = L.mem X (rhA (L := L) X) := by
    show L.mem y (L.nodeAt y (L.cpu y) layout.node.RELEASE_HEAD) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD)
    rw [G.node]; exact G.m _ (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  have ert : L.mem y (rTcbA rptr) = L.mem X (rTcbA rptr) := G.m _ D.rRt
  refine ⟨fun o ho h8 => by rw [G.node]; exact hRR _ (D.nd o ho h8), by rw [G.k]; exact hRR _ D.dt,
    by rw [G.k]; exact hRR _ D.cd, fun h0 => by rw [etm] at h0 ⊢; exact hRR _ (D.tm h0), fun h0 => ?_,
    hRR _ D.tSt, hRR _ D.tSc, fun h0 => ?_, hRR _ D.tIq, hRR _ D.tMi, hRR _ D.tBn, hRR _ D.tPr, fun h0 => ?_,
    hRR _ D.rRt, hRR _ D.rNx, hRR _ D.eTS, fun u hu hu0 => ?_, fun u hu hu0 haff => ?_,
    fun u hu hu0 haff hst hsc => ?_⟩
  · rw [erh] at h0 ⊢
    obtain ⟨h1, h2⟩ := D.rh h0
    rw [G.m _ h1]
    have h3 := G.rdHead h2
    refine ⟨hRR _ h1, ?_⟩
    unfold RdHead at h3 ⊢
    exact ⟨hRR _ h3.1, hRR _ h3.2.1, hRR _ h3.2.2⟩
  · rw [G.m _ D.tSc] at h0 ⊢; exact hRR _ (D.tMx h0)
  · rw [G.m _ D.tBn] at h0 ⊢; exact ⟨hRR _ (D.ntf h0).1, hRR _ (D.ntf h0).2⟩
  · rw [ert] at hu
    obtain ⟨a1, a2, a3, a4⟩ := D.uG u hu hu0
    exact ⟨hRR _ a1, hRR _ a2, hRR _ a3, hRR _ a4⟩
  · rw [ert] at hu
    have g := D.uG u hu hu0
    rw [G.m _ g.2.1, G.c] at haff
    obtain ⟨a1, a2, a3⟩ := D.uH u hu hu0 haff
    exact ⟨hRR _ a1, hRR _ a2, hRR _ a3⟩
  · rw [ert] at hu
    have g := D.uG u hu hu0
    rw [G.m _ g.2.1, G.c] at haff
    have hh := D.uH u hu hu0 haff
    rw [G.m _ hh.1] at hst
    rw [G.m _ g.1] at hsc ⊢
    have h3 := G.rdHead (D.uS u hu hu0 haff hst hsc)
    unfold RdHead at h3 ⊢
    exact ⟨hRR _ h3.1, hRR _ h3.2.1, hRR _ h3.2.2⟩

section gen
variable {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]

/-- **`is_schedulable` on `gS`**, the SC's `REFILL_MAX` only when the SC is not null. -/
theorem is_sched_guardC (s : S) (t : obj.Tcb) (h1 : R (stA t)) (h2 : R (scA t))
    (h3 : L.mem s (scA t) ≠ 0#u64 → R (maxA (L.mem s (scA t)))) (h4 : R (inqA t)) :
    sched.is_schedulable gS s t = sched.is_schedulable st s t := by
  by_cases h0 : L.mem s (scA t) = 0#u64
  · unfold sched.is_schedulable
    rw [sched.is_runnable.guard (gS := gS) s t h1, obj.Tcb.sc.guard (gS := gS) t s h2, tcb_sc_ok s t]
    simp only [bind_ok]
    rw [h0, eq_of_spec_fd (obj.Sc.is_null.spec 0#u64)]
    simp only [bind_ok, decide_true, ↓reduceIte]
  · exact sched.is_schedulable.guard (gS := gS) s t h1 h2 (h3 h0) h4

set_option maxHeartbeats 4000000 in
/-- **A declined ReplyRecv fast path on `gS`** (`R` holding `RrDR`, and the receiver's `STATE` /
`FAULT_TYPE` when it is homed elsewhere, `hrep`). -/
theorem rr_found_guard_dec {X : S} {a : A} {t : obj.Tcb} {rptr ep : U64} {r : Bool × S × A}
    (D : RrDR (L := L) R X t rptr ep)
    (hrep : ∀ u, L.mem X (rTcbA rptr) = u → u ≠ 0#u64 → L.mem X (affA u) ≠ L.cpu X →
      R (stA u) ∧ R (core.num.U64.wrapping_add u 3376#u64))
    (h : fastpath_vm.reply_recv_vm_found st ar X a t rptr ep = ok r) (hn : r.1 ≠ true) :
    fastpath_vm.reply_recv_vm_found gS ar X a t rptr ep = ok r := by
  have bm : RdBitmap (L := L) R X := ⟨D.nd l1Off (by rw [l1Off_val]; omega) (by rw [l1Off_val]),
    fun inv hinv => D.nd _ (by simp only [w64_val]; omega) (by simp only [w64_val]; omega)⟩
  unfold fastpath_vm.reply_recv_vm_found at h ⊢
  revert h
  rw [sched.action.guard (gS := gS) X (D.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [is_sched_guardC (gS := gS) X t D.tSt D.tSc D.tMx D.tIq]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h' => h')
  rw [msg.msg_info.guard (gS := gS) X t D.tMi]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [obj.Reply.tcb.guard (gS := gS) rptr X D.rRt]
  refine tr_bind_same (fun u eu => ?_)
  have hu : L.mem X (rTcbA rptr) = u := by
    rw [eq_of_spec_fd (obj.Reply.tcb.blk (L := L) X rptr)] at eu; exact ok_inj_ff eu
  refine tr_bind_same (fun bn ebn => ?_)
  refine tr_ite (fun _ h' => h') (fun hbn => ?_)
  have hu0 : u ≠ 0#u64 := by
    rw [is_null_ok] at ebn; have e := ok_inj_ff ebn; subst e; simpa using hbn
  obtain ⟨gSc, gAf, gDo, gPr⟩ := D.uG u hu hu0
  have hSF : R (stA u) ∧ R (core.num.U64.wrapping_add u 3376#u64) := by
    by_cases hh : L.mem X (affA u) = L.cpu X
    · exact ⟨(D.uH u hu hu0 hh).1, (D.uH u hu hu0 hh).2.1⟩
    · exact hrep u hu hu0 hh
  rw [obj.Tcb.state.guard (gS := gS) u X hSF.1]
  refine tr_bind_same (fun ist eist => ?_)
  refine tr_ite (fun _ h' => h') (fun hist => ?_)
  have hst : L.mem X (stA u) = sched.TS_BLOCKED_ON_REPLY := by
    have hv := obj.Tcb.state.spec (L := L) X u
    rw [eist, WP.spec_ok] at hv
    have h5 : ist.val = 5 := by simpa using hist
    rw [← hv]
    exact UScalar.eq_of_val_eq (by rw [h5]; simp [sched.TS_BLOCKED_ON_REPLY])
  rw [obj.Tcb.fault_type.guard (gS := gS) u X hSF.2]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [obj.Reply.next.guard (gS := gS) X rptr D.rNx]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ => ?_)
  on_goal 1 =>
    rw [obj.Reply.next_is_head.guard (gS := gS) X rptr D.rNx]
    refine tr_bind_same (fun _ _ => ?_)
    refine tr_ite (fun _ h' => h') (fun _ => ?_)
  all_goals
    rw [obj.Tcb.sc.guard (gS := gS) u X gSc]
    refine tr_bind_same (fun usc eusc => ?_)
    have husc : L.mem X (scA u) = usc := by rw [tcb_sc_ok] at eusc; exact ok_inj_ff eusc
    refine tr_bind_same (fun b3 eb3 => ?_)
    refine tr_ite (fun _ h' => h') (fun hb3 => ?_)
    have hsc0 : usc ≠ 0#u64 := by
      rw [eq_of_spec_fd (obj.Sc.is_null.spec _)] at eb3; have e := ok_inj_ff eb3; subst e; simpa using hb3
    rw [vm_here_guard (gS := gS) X u
      (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
      D.tm D.rh D.dt D.cd gAf (fun hh => ⟨gDo, gSc, (D.uH u hu hu0 hh).2.2⟩)]
    refine tr_bind_same (fun b4 eb4 => ?_)
    refine tr_ite (fun hb4 => ?_) (fun _ h' => h')
    have HF := here_facts (L := L) (show fastpath.schedulable_here st X u = ok true by rw [eb4, hb4])
    have hH := D.uS u hu hu0 HF.aff hst (by rw [husc]; exact hsc0)
    rw [husc] at hH
    rw [sporadic.ready.guard (gS := gS) X usc hH
      (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))]
    refine tr_bind_same (fun _ _ => ?_)
    refine tr_ite (fun _ => ?_) (fun _ h' => h')
    rw [sporadic.sufficient.guard (gS := gS) ar X a usc 0#u64 hH]
    refine tr_bind_same (fun _ _ => ?_)
    refine tr_ite (fun _ => ?_) (fun _ h' => h')
    rw [obj.Tcb.bound_ntfn.guard (gS := gS) t X D.tBn]
    refine tr_bind_same (fun i6 ei6 => ?_)
    have hi6 : i6 = L.mem X (boundA t) := by
      have hv := obj.Tcb.bound_ntfn.val (L := L) X t
      rw [ei6, WP.spec_ok] at hv; exact hv
    refine tr_ite (fun h6 => ?_) (fun _ => ?_)
    on_goal 1 =>
      have h0 : L.mem X (boundA t) ≠ 0#u64 := by rw [← hi6]; exact bne_iff_ne.mp h6
      rw [hi6, obj.Ntfn.state.guard (gS := gS) _ X (D.ntf h0).1]
      refine tr_bind_same (fun _ _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [obj.Ntfn.sc.guard (gS := gS) _ X (D.ntf h0).2]
      refine tr_bind_same (fun _ _ => ?_)
      refine tr_ite (fun _ => ?_) (fun _ => ?_)
      on_goal 1 =>
        rw [obj.Tcb.sc.guard (gS := gS) t X D.tSc]
        refine tr_bind_same (fun _ _ => ?_)
        refine tr_ite (fun _ h' => h') (fun _ => ?_)
    all_goals
      rw [obj.Ep.state.guard (gS := gS) ep X D.eTS]
      refine tr_bind_same (fun _ _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [sched.idle_thread.guard (gS := gS) X
        (D.nd _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]))]
      refine tr_bind_same (fun _ _ => ?_)
      refine tr_bind_same (fun _ _ => ?_)
      rw [obj.Tcb.prio.guard (gS := gS) u X gPr, obj.Tcb.prio.guard (gS := gS) t X D.tPr]
      refine tr_bind_same (fun _ _ => ?_)
      refine tr_ite (fun _ => ?_)
        (fun _ hk => absurd (rrTail_fst (show rrTail st ar X a t rptr ep u usc = ok r from hk)) hn)
      rw [sched.cur_domain.guard (gS := gS) X D.cd]
      refine tr_bind_same (fun _ _ => ?_)
      refine tr_bind_same (fun _ _ => ?_)
      rw [sched.is_highest_prio.guard (gS := gS) X _ _ bm]
      refine tr_bind_same (fun _ _ => ?_)
      exact tr_ite (fun _ hk => absurd (rrTail_fst (show rrTail st ar X a t rptr ep u usc = ok r from hk)) hn)
        (fun _ h' => h')

/-- **A declined VM ReplyRecv local path on `gS`**: the prefix's words, then `RrDR` and `hrep` at the
state after `update_timestamp`. -/
theorem rr_local_guard_dec {X : S} {a : A} {rptr ep : U64} {r : Bool × S × A}
    (hct : R (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD))
    (hfl : R (core.num.U64.wrapping_add (L.curW X) 3456#u64))
    (hni : R (regA (L.curW X) layout.reg.NEXT_IP)) (hfi : W (regA (L.curW X) layout.reg.FAULT_IP))
    (hut : R (ctA (L := L) X) ∧ W (ctA (L := L) X) ∧ R (cnA (L := L) X) ∧ W (cnA (L := L) X))
    (hmid : ∀ v X2 a2,
      sched.update_timestamp st ar (L.wr X (regA (L.curW X) layout.reg.FAULT_IP) v) a = ok (X2, a2) →
      R (L.nodeAt X2 (L.cpu X2) layout.node.CUR_SC) ∧ R (L.nodeAt X2 (L.cpu X2) layout.node.CONSUMED) ∧
      RdHead (L := L) R X2 (L.cscW X2) ∧ RrDR (L := L) R X2 (L.curW X) rptr ep ∧
      ∀ u, L.mem X2 (rTcbA rptr) = u → u ≠ 0#u64 → L.mem X2 (affA u) ≠ L.cpu X2 →
        R (stA u) ∧ R (core.num.U64.wrapping_add u 3376#u64))
    (h : syscall.handle_reply_recv_vm_local st ar X a (rptr, ep) = ok r) (hn : r.1 ≠ true) :
    syscall.handle_reply_recv_vm_local gS ar X a (rptr, ep) = ok r := by
  unfold syscall.handle_reply_recv_vm_local at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := gS) X hct]
  refine tr_bind_same (fun t et => ?_)
  have et' : t = L.curW X := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  subst et'
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard (gS := gS) (L.curW X) X hfl]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.reg.guard (gS := gS) (L.curW X) X _ hni]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_bind_same (fun v _ => ?_)
  rw [obj.Tcb.set_reg.guard (gS := gS) (L.curW X) X _ _ hfi]
  refine tr_bind_same (fun s1 e1 => ?_)
  rw [set_reg_ok'] at e1
  obtain rfl := ok_inj_ff e1
  rw [sched.update_timestamp.guard (gS := gS) ar _ a (by rw [ctA_wr]; exact hut.1) (by rw [ctA_wr]; exact hut.2.1)
    (by rw [cnA_wr]; exact hut.2.2.1) (by rw [cnA_wr]; exact hut.2.2.2)]
  refine tr_bind_same (fun x eu => ?_)
  obtain ⟨s2, a1⟩ := x
  simp only [uncurry_apply_pair]
  obtain ⟨h1, h2, h3, D, hrep⟩ := hmid v s2 a1 eu
  rw [sched.cur_sc.guard (gS := gS) s2 h1]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.consumed.guard (gS := gS) s2 h2]
  refine tr_bind_same (fun u _ => ?_)
  have ec : csc = L.cscW s2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecsc; exact (ok_inj_ff ecsc).symm
  rw [ec, sporadic.sufficient.guard (gS := gS) ar s2 a1 (L.cscW s2) u h3]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h' => h')
  exact fun h' => rr_found_guard_dec D hrep h' hn

end gen

end

/-! ## The entry facts and the read facts after the prefix -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **The entry facts of the VM ReplyRecv local path** for `found = (rptr, ep)`: `VmRPre`, the found
objects typed in P1's sets (`hrR` [P], `hpE` [P], module docstring), and the ASID words readable
(`RdTab` [J], `rr_vm_acc`'s `hTab`). -/
def VmRRPre (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (K : KLayout)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64)
    (Locks : S → U64 → Prop) (rptr ep : U64) (s : S) : Prop :=
  VmRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep ∧ rptr ∈ Rp ∧ H ep = some .ep ∧
    RdTab (L := L) (IoRS (st := st) K Locks s) s

/-- The reply's `TCB` word is kept by the prefix, and names a thread of `T` when not null. -/
theorem rr_uX (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {rptr : U64} (hrR : rptr ∈ Rp) (v n : U64) :
    L.mem (rrX (L := L) s v n) (rTcbA rptr) = L.mem s (rTcbA rptr) ∧
      (L.mem s (rTcbA rptr) ≠ 0#u64 → L.mem s (rTcbA rptr) ∈ T) := by
  have hN := P.np
  have hcT := P.cT
  have hc := P.tA
  obtain ⟨⟨Qs, Rq, hq⟩, hB, hX, hSg, hS⟩ := P.bxi
  have hO := hX.1
  have hrΩ : rTcbA rptr ∈ Ω := by
    refine hSg.sub _ (hO.rpW rptr hrR _ ?_ ?_ ?_)
    · show (rTcbA rptr).val % 8 = 0
      rw [rTcbA_val0]; have := (hO.rp rptr hrR).1; omega
    · rw [rTcbA_val0]
    · rw [rTcbA_val0]; omega
  exact ⟨rrX_out hN hc hcT hq.cur v n (hq.omega _ hrΩ), fun h0 => (hX.2.1.back rptr hrR h0).2.1⟩

/-- **`RrDR` for `IoRS s` at the state after the prefix.** -/
theorem rr_dr {rptr ep : U64} (Q : VmRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep)
    (hrR : rptr ∈ Rp) (hpE : H ep = some .ep) (v n : U64) :
    RrDR (L := L) (IoRS (st := st) K Locks s) (rrX (L := L) s v n) (L.curW s) rptr ep := by
  have P := Q.base
  have hN := P.np
  have hT := P.tp
  have hcT := P.cT
  have hc := P.tA
  obtain ⟨⟨Qs, Rq, hq⟩, hB, hX, hSg, hS⟩ := P.bxi
  have hO := hX.1
  have hX0 : ScExtra0 st T Cs Scs Nt s := hX.2.2.toScExtra0
  have hcC : L.cpu s ∈ Cs := hq.cur
  obtain ⟨eRt, hRtT⟩ := rr_uX P hrR v n
  have uI : ∀ u, L.mem (rrX (L := L) s v n) (rTcbA rptr) = u → u ≠ 0#u64 → u ∈ T := by
    intro u hu hu0
    rw [eRt] at hu
    subst hu
    exact hRtT hu0
  have esct : L.mem (rrX (L := L) s v n) (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    rrX_tcb hN hT hcT v n hcT (Kx := 3464#u64) (by simp) (by simp) (fun _ => by simp)
  have etm : L.mem (rrX (L := L) s v n) (tmA (L := L) (rrX (L := L) s v n)) = L.mem s (tmA (L := L) s) := by
    show L.mem (rrX (L := L) s v n) (L.nodeAt (rrX (L := L) s v n) (L.cpu (rrX (L := L) s v n))
      layout.node.TIMER_MIN) = _
    rw [rrX_nodeAt]
    exact rrX_node hN hc hcT v n (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
  have erh : L.mem (rrX (L := L) s v n) (rhA (L := L) (rrX (L := L) s v n)) = L.mem s (rhA (L := L) s) := by
    show L.mem (rrX (L := L) s v n) (L.nodeAt (rrX (L := L) s v n) (L.cpu (rrX (L := L) s v n))
      layout.node.RELEASE_HEAD) = _
    rw [rrX_nodeAt]
    exact rrX_node hN hc hcT v n (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
  have rp := hO.rp rptr hrR
  have hrK := Q.hRp rptr hrR
  have hE := vm_epP P.bxi hpE
  refine
  { nd := fun o ho h8 => by rw [rrX_nodeAt]; exact (P.nd (Locks := Locks) o ho h8).1
    dt := by rw [rrX_ksb]; exact P.ksw (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
    cd := by rw [rrX_ksb]; exact P.ksw (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
    tm := fun h0 => by rw [etm] at h0 ⊢; exact P.td h0
    rh := fun h0 => by
      rw [erh] at h0 ⊢
      obtain ⟨hrT, -, -⟩ := bxi_rh P.bxi h0
      have e1 : L.mem (rrX (L := L) s v n) (scA (L.mem s (rhA (L := L) s))) =
          L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        rrX_tcb hN hT hcT v n hrT (Kx := 3464#u64) (by simp) (by simp) (fun _ => by simp)
      rw [e1]
      obtain ⟨hqS, -⟩ := P.rsAcc (Locks := Locks) h0
      exact ⟨(P.rs h0).1, rdHead_rrX hN hc hcT hcC v n (bxi_headOut P.bxi hqS) (P.rs h0).2⟩
    tSt := (P.stw (Locks := Locks)).1
    tSc := P.gate (off := 3464#u64) hcT (by simp) (by simp) (by simp) (by simp [GateField])
    tMx := fun h0 => by
      rw [esct] at h0 ⊢
      rw [← P.hcsc h0]
      have hw := sc_word_in hO P.cscS (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact (P.cscacc (Locks := Locks)).rd _ hw.1 hw.2
    tIq := (P.home (Locks := Locks) (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField])).1
    tMi := (P.reg (Locks := Locks) (r := layout.reg.MSG_INFO) (lt384 (Or.inr (Or.inr (Or.inr rfl))))).1
    tBn := P.gate (off := 3368#u64) hcT (by simp) (by simp) (by simp) (by simp [GateField])
    tPr := P.gate (off := 3448#u64) hcT (by simp) (by simp) (by simp) (by simp [GateField])
    ntf := fun h0 => by
      have eb : L.mem (rrX (L := L) s v n) (boundA (L.curW s)) = L.mem s (boundA (L.curW s)) :=
        rrX_tcb hN hT hcT v n hcT (Kx := 3368#u64) (by simp) (by simp) (fun _ => by simp)
      rw [eb] at h0 ⊢
      have hnN := hX0.bnd (L.curW s) hcT h0
      obtain ⟨-, h64, hfit, hreg⟩ := Q.hNt _ hnN
      have hbt := Q.nbt h0
      exact ⟨P.ntfnRd hreg h64 hfit hbt (o := layout.ntfn.TAIL_STATE) (by simp [layout.ntfn.TAIL_STATE])
          (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]),
        P.ntfnRd hreg h64 hfit hbt (o := layout.ntfn.SC) (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])
          (by simp [layout.ntfn.SC])⟩
    rRt := by
      have h := rTcbA_val0 rptr; have := rp.1; have := rp.2
      exact (P.reply hrK (b := rTcbA rptr) ⟨by omega, by omega⟩ (by unfold Aligned; omega) Q.lk.1).1
    rNx := by
      have h := rNextA_val rp; have := rp.1; have := rp.2
      exact (P.reply hrK (b := rNextA rptr) ⟨by omega, by omega⟩ (by unfold Aligned; omega) Q.lk.1).1
    eTS := by
      have h := epTSA_val hE; have := hE.fits; have := hE.align
      exact (P.ep Q.hEp (b := epTSA ep) ⟨by omega, by omega⟩ (by unfold Aligned; omega) Q.lk.2).1
    uG := fun u hu hu0 => by
      have huT := uI u hu hu0
      exact ⟨P.gate (off := 3464#u64) huT (by simp) (by simp) (by simp) (by simp [GateField]),
        P.gate (off := 3520#u64) huT (by simp) (by simp) (by simp) (by simp [GateField]),
        P.gate (off := 3432#u64) huT (by simp) (by simp) (by simp) (by simp [GateField]),
        P.gate (off := 3448#u64) huT (by simp) (by simp) (by simp) (by simp [GateField])⟩
    uH := fun u hu hu0 haff => by
      have huT := uI u hu hu0
      have ea : L.mem (rrX (L := L) s v n) (affA u) = L.mem s (affA u) :=
        rrX_tcb hN hT hcT v n huT (Kx := 3520#u64) (by simp) (by simp) (fun _ => by simp)
      rw [ea, rrX_cpu] at haff
      refine ⟨?_, (P.homeOf (Locks := Locks) (off := 3376#u64) huT haff (by simp) (by simp) (by simp)
          (by simp [GateField]) (by simp [TimerField]) (by simp [GField])).1,
        (P.homeOf (Locks := Locks) (off := 3592#u64) huT haff (by simp) (by simp) (by simp) (by simp [GateField])
          (by simp [TimerField]) (by simp [GField])).1⟩
      rw [stA_eq]
      exact (P.homeOf (Locks := Locks) (off := 3328#u64) huT haff (by simp) (by simp) (by simp)
        (by simp [GateField]) (by simp [TimerField]) (by simp [GField])).1
    uS := fun u hu hu0 haff hst hsc => by
      have huT := uI u hu hu0
      have ea : L.mem (rrX (L := L) s v n) (affA u) = L.mem s (affA u) :=
        rrX_tcb hN hT hcT v n huT (Kx := 3520#u64) (by simp) (by simp) (fun _ => by simp)
      rw [ea, rrX_cpu] at haff
      have est : L.mem (rrX (L := L) s v n) (stA u) = L.mem s (stA u) :=
        rrX_tcb hN hT hcT v n huT (Kx := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val])
          (fun _ => by rw [st_val]; omega)
      have esc : L.mem (rrX (L := L) s v n) (scA u) = L.mem s (scA u) :=
        rrX_tcb hN hT hcT v n huT (Kx := 3464#u64) (by simp) (by simp) (fun _ => by simp)
      rw [est] at hst
      rw [esc] at hsc ⊢
      have hcS : L.mem s (scA u) ∈ Scs := (hX0.bound u huT hsc).1
      have hact : L.mem s (scA u) ∈ Ac :=
        hB.sact u huT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hst)))))) hsc
      have hWF := (hS.all _ hcS).1 ((hS.act _ hcS).1 hact)
      have hcore : L.mem s (scCoreA (L.mem s (scA u))) = L.cpu s := by rw [P.affSc u huT hsc, haff]
      exact rdHead_rrX hN hc hcT hcC v n (bxi_headOut P.bxi hcS) ((P.scacc (Locks := Locks) hcS hcore).head hWF) }

/-! ## A run declining at the entry is accepted at no alternative -/

/-- **Checks passing at an alternative's dispatch state pass at the entry's.** -/
theorem rr_chk_back {R : U64 → Prop} {X y : S} {a : A} {t rptr ep u usc : U64}
    (D : RrDR (L := L) R X t rptr ep) (G1 : Ag st R X y)
    (C : RRChecksG st ar fl4_abi.consts.fault.VMFault y a t rptr ep u usc) :
    RRChecksG st ar fl4_abi.consts.fault.VMFault X a t rptr ep u usc := by
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

/-- The state after the prefix is `rrX`. -/
theorem rr_pre_eq (hA : P0.ArchTotal ar) (hN : NodePlaced st T s (L.cpu s)) {a : A} {v : U64} {s2 : S} {a1 : A}
    (eu : sched.update_timestamp st ar (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v) a = ok (s2, a1)) :
    ∃ n, s2 = rrX (L := L) s v n := by
  have hN1 : NodePlaced st T (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)
      (L.cpu (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)) := by
    rw [LawfulStore.cpu_wr]; exact hN.wr
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok ar hN1 hn] at eu
  exact ⟨n, (Prod.mk.inj (ok_inj_ff eu)).1.symm⟩

/-- The current SC's head refill is readable at the state after the prefix. -/
theorem rr_suf (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (v n : U64) :
    RdHead (L := L) (IoRS (st := st) K Locks s) (rrX (L := L) s v n) (L.cscW (rrX (L := L) s v n)) := by
  have hcC : L.cpu s ∈ Cs := by obtain ⟨⟨Qs, Rq, hq⟩, -, -, -, -⟩ := P.bxi; exact hq.cur
  rw [rrX_csc P.np P.tA P.cT v n]
  exact rdHead_rrX P.np P.tA P.cT hcC v n (bxi_headOut P.bxi P.cscS) (P.cscacc.head P.cscwf)

set_option maxHeartbeats 1000000 in
/-- **A run that declines at `s` is accepted at no alternative state.** -/
theorem rr_alt_not_acc (hA : P0.ArchTotal ar) {rptr ep : U64}
    (E : VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s)
    {x : S} (G : Ag st (IoRS (st := st) K Locks s) s x) {a : A} {r : Bool × S × A} {z : S} {b : A}
    (h : syscall.handle_reply_recv_vm_local st ar s a (rptr, ep) = ok r) (hr : r.1 ≠ true)
    (h' : syscall.handle_reply_recv_vm_local st ar x a (rptr, ep) = ok (true, z, b)) : False := by
  have Q := E.1
  have P := Q.base
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have rT := (P.nd (Locks := Locks) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME])
    (by simp [layout.node.CUR_TIME])).1
  have rN := (P.nd (Locks := Locks) layout.node.CONSUMED (by simp [layout.node.CONSUMED])
    (by simp [layout.node.CONSUMED])).1
  have hcur : L.curW x = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  unfold syscall.handle_reply_recv_vm_local at h h'
  rw [cur_thread_ok] at h h'
  simp only [bind_ok] at h h'
  rw [if_neg vm_nd_ne] at h h'
  rw [hcur] at h'
  -- `FLAGS`
  have rfl' := (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    (by simp [TimerField])).1
  have efl : obj.Tcb.flags st (L.curW s) x = obj.Tcb.flags st (L.curW s) s :=
    ro_congr G (fun m z => obj.Tcb.flags m (L.curW s) z) (fun _ => rfl)
      (obj.Tcb.flags.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) (L.curW s) s rfl')
      (obj.Tcb.flags.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) (L.curW s) x rfl')
  rw [efl] at h'
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  rw [ei] at h'
  simp only [bind_ok] at h'
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  rw [ei1] at h'
  simp only [bind_ok] at h'
  by_cases hf : (i1 != 0#u64) = true
  · rw [if_pos hf] at h'; exact Bool.false_ne_true (congrArg Prod.fst (ok_inj_ff h'))
  rw [if_neg hf] at h h'
  -- `NEXT_IP`
  have rni := (P.reg (Locks := Locks) (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])).1
  have eni : obj.Tcb.reg st (L.curW s) x layout.reg.NEXT_IP = obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP :=
    ro_congr G (fun m z => obj.Tcb.reg m (L.curW s) z layout.reg.NEXT_IP) (fun _ => rfl)
      (obj.Tcb.reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) (L.curW s) s _ rni)
      (obj.Tcb.reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) (L.curW s) x _ rni)
  rw [eni] at h'
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
  rw [enx] at h'
  simp only [bind_ok] at h'
  obtain ⟨v, ev, h⟩ := bind_eq_ok h
  rw [ev] at h'
  simp only [bind_ok] at h'
  -- the `FAULT_IP` write and `update_timestamp`
  rw [set_reg_ok'] at h h'
  simp only [bind_ok] at h h'
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  obtain ⟨⟨x2, a1'⟩, eu', h'⟩ := bind_eq_ok h'
  simp only [uncurry_apply_pair] at h h'
  obtain ⟨k, hk, ek⟩ := fip_eq (L := L) P.tA
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := by
    rw [ek]; exact field_aligned P.tA (by omega) (by omega)
  have G0 := G.wr (fun _ hb => hb.1) (a := regA (L.curW s) layout.reg.FAULT_IP) (v := v) aF
  obtain ⟨ea, G1⟩ := vm_ag_upd (fun _ hb => hb.1) G0 (by rw [ctA_wr]; exact rT) (by rw [cnA_wr]; exact rN) eu eu'
  rw [ea] at h'
  obtain ⟨n, hn2⟩ := rr_pre_eq hA P.np eu
  subst hn2
  have D := rr_dr Q E.2.1 E.2.2.1 v n
  -- `cur_sc`, `consumed`, `sufficient`
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨csc', ecsc', h'⟩ := bind_eq_ok h'
  obtain ⟨u, eu1, h⟩ := bind_eq_ok h
  obtain ⟨u', eu1', h'⟩ := bind_eq_ok h'
  obtain ⟨bb, ebb, h⟩ := bind_eq_ok h
  obtain ⟨bb', ebb', h'⟩ := bind_eq_ok h'
  have nS := D.nd layout.node.CUR_SC (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have nN := D.nd layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have ecs : sched.cur_sc st x2 = sched.cur_sc st (rrX (L := L) s v n) :=
    ro_congr G1 (fun m z => sched.cur_sc m z) (fun _ => rfl)
      (sched.cur_sc.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) _ nS)
      (sched.cur_sc.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x2
        (by rw [G1.node]; exact nS))
  have ecn : sched.consumed st x2 = sched.consumed st (rrX (L := L) s v n) :=
    ro_congr G1 (fun m z => sched.consumed m z) (fun _ => rfl)
      (sched.consumed.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) _ nN)
      (sched.consumed.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x2
        (by rw [G1.node]; exact nN))
  rw [ecs, ecsc] at ecsc'
  rw [ecn, eu1] at eu1'
  have e1 : csc' = csc := (ok_inj_ff ecsc').symm
  have e2 : u' = u := (ok_inj_ff eu1').symm
  rw [e1, e2] at ebb'
  have hcs : csc = L.cscW (rrX (L := L) s v n) := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecsc; exact (ok_inj_ff ecsc).symm
  rw [hcs, suff_congr G1 a1 (rr_suf P v n), ← hcs, ebb] at ebb'
  have e3 : bb' = bb := (ok_inj_ff ebb').symm
  rw [e3] at h'
  by_cases hb : bb = true
  swap
  · rw [if_neg hb] at h'; exact Bool.false_ne_true (congrArg Prod.fst (ok_inj_ff h'))
  rw [if_pos hb] at h h'
  have hF : fastpath_vm.reply_recv_vm_found st ar (rrX (L := L) s v n) a1 (L.curW s) rptr ep = ok r := h
  have hF' : fastpath_vm.reply_recv_vm_found st ar x2 a1 (L.curW s) rptr ep = ok (true, z, b) := h'
  obtain ⟨u0, usc0, C', -⟩ := reply_recv_vm_found_acc st ar hF'
  rw [rr_found_chk (rr_chk_back D G1 C')] at hF
  exact hr (rrTail_fst hF)

/-! ## Declined runs on guarded stores -/

/-- The receiver's `STATE` / `FAULT_TYPE` words when it is homed on another core: the words outside
`IoRS s` a declining run may read. -/
def RrRep (st : machine.Store S) [L : LawfulStore st] (rptr : U64) (s : S) (b : U64) : Prop :=
  L.mem s (rTcbA rptr) ≠ 0#u64 ∧ L.mem s (affA (L.mem s (rTcbA rptr))) ≠ L.cpu s ∧
    (b = stA (L.mem s (rTcbA rptr)) ∨ b = core.num.U64.wrapping_add (L.mem s (rTcbA rptr)) 3376#u64)

theorem RrRep.aligned {rptr : U64} (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hrR : rptr ∈ Rp)
    {b : U64} (h : RrRep st rptr s b) : Aligned b := by
  obtain ⟨h0, -, hb⟩ := h
  have huT := (rr_uX P hrR 0#u64 0#u64).2 h0
  rcases hb with rfl | rfl
  · rw [stA_eq]; exact field_aligned (P.tp _ huT) (by simp) (by simp)
  · exact field_aligned (P.tp _ huT) (by simp) (by simp)

/-- **A run declining at an alternative `x` runs the same on `PathObl.guard st R'' (IoDS s)`**, `R''`
holding `IoRS s` and `RrRep`. -/
theorem rr_dec_tr (hA : P0.ArchTotal ar) {rptr ep : U64}
    (E : VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s)
    {x : S} (G : Ag st (IoRS (st := st) K Locks s) s x) {a : A} {R'' : U64 → Prop}
    (hRR : ∀ b, IoRS (st := st) K Locks s b → R'' b) (hrep : ∀ b, RrRep st rptr s b → R'' b)
    {r' : Bool × S × A} (h' : syscall.handle_reply_recv_vm_local st ar x a (rptr, ep) = ok r') (hn : r'.1 ≠ true) :
    syscall.handle_reply_recv_vm_local (PathObl.guard st R'' (IoDS (st := st) s)) ar x a (rptr, ep) = ok r' := by
  have Q := E.1
  have P := Q.base
  have hN := P.np
  have hT := P.tp
  have hcT := P.cT
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have rT := (P.nd (Locks := Locks) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME])
    (by simp [layout.node.CUR_TIME])).1
  have rN := (P.nd (Locks := Locks) layout.node.CONSUMED (by simp [layout.node.CONSUMED])
    (by simp [layout.node.CONSUMED])).1
  have hcur : L.curW x = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  obtain ⟨k, hk, ek⟩ := fip_eq (L := L) P.tA
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := by
    rw [ek]; exact field_aligned P.tA (by omega) (by omega)
  refine rr_local_guard_dec (gS := PathObl.guard st R'' (IoDS (st := st) s))
    (by rw [G.node]; exact hRR _ nC)
    (by rw [hcur]; exact hRR _ (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp)
      (by simp [GateField]) (by simp [TimerField])).1)
    (by rw [hcur]; exact hRR _ (P.reg (Locks := Locks) (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])).1)
    (by rw [hcur]; exact Or.inl rfl)
    ⟨by show R'' (L.nodeAt x (L.cpu x) layout.node.CUR_TIME); rw [G.node]; exact hRR _ rT,
      by show IoDS (st := st) s (L.nodeAt x (L.cpu x) layout.node.CUR_TIME); rw [G.node]; exact Or.inr (Or.inl rfl),
      by show R'' (L.nodeAt x (L.cpu x) layout.node.CONSUMED); rw [G.node]; exact hRR _ rN,
      by show IoDS (st := st) s (L.nodeAt x (L.cpu x) layout.node.CONSUMED); rw [G.node]; exact Or.inr (Or.inr rfl)⟩
    ?_ h' hn
  intro v X2 a2 eu'
  rw [hcur] at eu' ⊢
  obtain ⟨⟨n, a3⟩, hn3, -⟩ := spec_ex_fd (hA.now a)
  have hN1 : NodePlaced st T (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)
      (L.cpu (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)) := by
    rw [LawfulStore.cpu_wr]; exact hN.wr
  have eu := update_timestamp_ok ar hN1 hn3
  have G0 := G.wr (fun _ hb => hb.1) (a := regA (L.curW s) layout.reg.FAULT_IP) (v := v) aF
  obtain ⟨-, G1⟩ := vm_ag_upd (fun _ hb => hb.1) G0 (by rw [ctA_wr]; exact rT) (by rw [cnA_wr]; exact rN) eu eu'
  replace G1 : Ag st (IoRS (st := st) K Locks s) (rrX (L := L) s v n) X2 := G1
  have D := rr_dr Q E.2.1 E.2.2.1 v n
  have nd1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R'' (L.nodeAt X2 (L.cpu X2) o) := fun o ho h8 => by
    rw [G1.node]; exact hRR _ (D.nd o ho h8)
  have ecsc : L.cscW X2 = L.cscW (rrX (L := L) s v n) := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [G1.node]; exact G1.m _ (D.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
  have hs := G1.rdHead (rr_suf (Locks := Locks) P v n)
  rw [← ecsc] at hs
  obtain ⟨eRt, hRtT⟩ := rr_uX P E.2.1 v n
  refine ⟨nd1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]),
    nd1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]), ?_, D.alt G1 hRR, ?_⟩
  · unfold RdHead at hs ⊢
    exact ⟨hRR _ hs.1, hRR _ hs.2.1, hRR _ hs.2.2⟩
  · intro u hu hu0 haff
    rw [G1.m _ D.rRt, eRt] at hu
    subst hu
    have huT := hRtT hu0
    have gA := (D.uG _ eRt hu0).2.1
    have ea : L.mem (rrX (L := L) s v n) (affA (L.mem s (rTcbA rptr))) = L.mem s (affA (L.mem s (rTcbA rptr))) :=
      rrX_tcb hN hT hcT v n huT (Kx := 3520#u64) (by simp) (by simp) (fun _ => by simp)
    rw [G1.m _ gA, G1.c, ea, rrX_cpu] at haff
    exact ⟨hrep _ ⟨hu0, haff, Or.inl rfl⟩, hrep _ ⟨hu0, haff, Or.inr rfl⟩⟩

/-- **A declined run at an alternative on any store reading as `st` and writing `IoDS s` as `st`.** -/
theorem rr_dec_top (hA : P0.ArchTotal ar) {rptr ep : U64} (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    {gS : machine.Store S} [GRd gS st (fun _ => True)] [GWr gS st (IoDS (st := st) s)]
    {x : S} (G : Ag st (IoRS (st := st) K Locks s) s x) {a : A}
    {r' : Bool × S × A} (h' : syscall.handle_reply_recv_vm_local st ar x a (rptr, ep) = ok r') (hn : r'.1 ≠ true) :
    syscall.handle_reply_recv_vm_local gS ar x a (rptr, ep) = ok r' := by
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW x = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  exact rr_local_guard_dec (gS := gS) trivial trivial trivial (by rw [hcur]; exact Or.inl rfl)
    ⟨trivial, by show IoDS (st := st) s (L.nodeAt x (L.cpu x) layout.node.CUR_TIME); rw [G.node]; exact Or.inr (Or.inl rfl),
      trivial, by show IoDS (st := st) s (L.nodeAt x (L.cpu x) layout.node.CONSUMED); rw [G.node]; exact Or.inr (Or.inr rfl)⟩
    (fun _ X2 _ _ => ⟨trivial, trivial, rdHead_top X2 _, RrDR.top X2 _ rptr ep, fun _ _ _ _ => ⟨trivial, trivial⟩⟩)
    h' hn

/-- **`PathObl.dec_alt`** for the VM ReplyRecv local path. -/
theorem rr_dec_alt (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K) {rptr ep : U64}
    (E : VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s)
    {a : A} {r r' : Bool × S × A} {s' : S}
    (h : syscall.handle_reply_recv_vm_local st ar s a (rptr, ep) = ok r) (hr : r.1 ≠ true)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    (h' : syscall.handle_reply_recv_vm_local st ar s' a (rptr, ep) = ok r') :
    r'.1 ≠ true ∧
      syscall.handle_reply_recv_vm_local (PathObl.guard st (fun _ => True) (IoDS (st := st) s)) ar s' a (rptr, ep) = ok r' ∧
      syscall.handle_reply_recv_vm_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s' a (rptr, ep) = ok r' := by
  have P := E.1.base
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have hn : r'.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r'
    intro hb
    change b = true at hb
    subst hb
    exact rr_alt_not_acc hA E G h hr h'
  refine ⟨hn, rr_dec_top (gS := PathObl.guard st (fun _ => True) (IoDS (st := st) s)) hA P G h' hn, ?_⟩
  have iR : GRd (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
      (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) st (fun _ => True) :=
    { read := fun _ _ => rfl, read_pair := fun _ _ _ => rfl, ks_base := rfl, cur_cpu := rfl, frame_masks := rfl }
  have iW : GWr (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
      (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) st (IoDS (st := st) s) :=
    { write := fun {b} hb y v => by
        obtain ⟨ha, hs⟩ := P.dsSafe hb
        rw [L.write_eq]
        exact mguard_write (L.write_eq y b v) (stepOK_safe (m0 := m0) hK hLA ha hs)
      ks_base := rfl, cur_cpu := rfl, frame_masks := rfl }
  exact rr_dec_top hA P G h' hn

end

end Fl4Proofs.P2.PathObl

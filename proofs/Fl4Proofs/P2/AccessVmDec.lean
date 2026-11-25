/-
# P2: the VM-fault local path's declines (line p2e, VM paths)

`PathObl.dec_alt` for `syscall.handle_vm_fault_local`, with the read set `IoRS K Locks s` and the decline
set `IoDS s` (`P2/AccessIoOwn.lean`: the words `update_timestamp` writes, and the current thread's
`FAULT_IP`, which this path does not write), and the guarded declined runs `PathSide` / `ReadOnce` use.

* `faultTail3_fst`, `faultTailG_fst`: the fast path's tail, when it returns, accepts;
* `vm_here_guard`: `schedulable_here to` on a store answering as `st` on `R`, `to`'s words after
  `AFFINITY` only when `to` is homed here (it answers `false` right after `AFFINITY` otherwise);
* `VmDest`, `VmFDec`: the words a declining fast path reads at its state `X`;
  `vm_fault_guard_dec`, `vm_local_guard_dec`: **a declined run on `st` runs the same on any store answering
  as `st` on those words** (and writing the prefix words as `st`);
* `VmDF`, `vm_dfOf`: the read facts at the state after the entry's `update_timestamp`, from `VmFPre`;
  `VmDF.alt`, `vmFDec_of`: moved to an alternative's prefix state (`Ag` on `IoRS s`);
* `vm_ag_upd`: `update_timestamp` keeps `Ag`;
* `vm_chk_back`: checks passing at an alternative pass at the entry; **`vm_alt_not_acc`**: a run that
  declines at `s` is accepted at no alternative;
* **`vm_dec_tr`**: a declined run at an alternative on `PathObl.guard st R'' (IoDS s)`, `R''` holding `IoRS s` and
  the handler's `REPLY_OBJ` word when the handler is homed on another core (`VmRep`);
* `vm_fault_dec_m`, `vm_dec_m`: a declined run on any store reading as `st` and writing the prefix words as
  `st`; `VmBase.dsSafe`: `IoDS` words are aligned safe words;
* **`vm_dec_alt`**: `PathObl.dec_alt`.

Premises: `VmFPre`'s (`P2/AccessVmAcc.lean`), `RegionOK` / `IoLayA` [J] (`vm_dec_alt`), and
* `VmGlue` [P]: fl4-sync's `local_vm_fault` (`crates/fl4-sync/src/lib.rs`) calls the body only after
  `lock_object` succeeded on the endpoint of the current thread's fault-handler cap (it returns `false`
  otherwise); the body reads that cap again after `update_timestamp`, which writes only two node words.

The handler's `REPLY_OBJ` is home-owned (`OwnMap.tcbOwner`), and the fast path reads it before
`schedulable_here` checks the handler's `AFFINITY`: for a handler homed elsewhere that read is racy, which
is why `vm_dec_tr` needs `VmRep` (p2sl found the same in `fastpath::fault`; a kernel reorder, checking
`schedulable_here` right after reading the head, would remove it).
-/
import Fl4Proofs.P2.AccessVmAcc
import Fl4Proofs.P2.AccessIoDec2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout fld own GateField TimerField GField RegionOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}

/-! ## The tail accepts -/

theorem faultTail3_fst {A : Type} (m : machine.Store S) (ar : machine.Arch A) {s14 : S} {a : A} {d : U64}
    {r : Bool × S × A} (h : faultTail3 m ar s14 a d = ok r) : r.1 = true := by
  unfold faultTail3 at h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨s18, a18⟩, -, h⟩ := bind_eq_ok h
  simp only [uncurry_apply_pair] at h
  rw [← ok_inj_ff h]

theorem faultTailG_fst {A : Type} (m : machine.Store S) (ar : machine.Arch A) {s : S} {a : A} {t : obj.Tcb}
    {f : error.Fault} {ty ptr badge d r0 : U64} {r : Bool × S × A}
    (h : faultTailG m ar s a t f ty ptr badge d r0 = ok r) : r.1 = true := by
  rw [faultTailG_split] at h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  exact faultTail3_fst m ar h

/-! ## The words a declining fast path reads -/

/-- The handler's words a declining fast path reads (`REPLY_OBJ`, `AFFINITY`; the rest only when it is
homed here). -/
structure VmDest (R : U64 → Prop) (X : S) (d : U64) : Prop where
  rp : R (replyA d)
  af : R (affA d)
  rest : L.mem X (affA d) = L.cpu X →
    R (core.num.U64.wrapping_add d 3432#u64) ∧ R (scA d) ∧ R (inqA d) ∧ R (prioA d)

/-- **The words a declining fast path reads** at its state `X` (current thread `t`). -/
structure VmFDec (R : U64 → Prop) (X : S) (t : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)
  bm : RdBitmap (L := L) R X
  tm : L.mem X (tmA (L := L) X) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64)
  rh : L.mem X (rhA (L := L) X) ≠ 0#u64 → R (scA (L.mem X (rhA (L := L) X))) ∧
    RdHead (L := L) R X (L.mem X (scA (L.mem X (rhA (L := L) X))))
  fh : ∀ sl, obj.Tcb.slot t layout.tcb.SLOT_FAULT_HANDLER = ok sl → R sl ∧ R (core.num.U64.wrapping_add sl 8#u64)
  ep : ∀ sl ptr b x y g gr, obj.Tcb.slot t layout.tcb.SLOT_FAULT_HANDLER = ok sl →
    obj.Slot.cap st sl X = ok (capability.Cap.Endpoint ptr b x y g gr) →
    R (epTSA ptr) ∧ R (epHeadA ptr) ∧
      (obj.Ep.state st ptr X = ok obj.EP_RECV → ∀ d, obj.Ep.head st ptr X = ok d → VmDest (L := L) R X d)

section gen
variable {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]

/-- **`schedulable_here to`, `to`'s words after `AFFINITY` only when homed here.** -/
theorem vm_here_guard (s : S) (t : obj.Tcb)
    (hct : R (ctA (L := L) s)) (htm : R (tmA (L := L) s)) (hrh : R (rhA (L := L) s))
    (htd : L.mem s (tmA (L := L) s) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64))
    (hrs : L.mem s (rhA (L := L) s) ≠ 0#u64 → R (scA (L.mem s (rhA (L := L) s))) ∧
      RdHead (L := L) R s (L.mem s (scA (L.mem s (rhA (L := L) s)))))
    (hdt : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hcd : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (haf : R (affA t))
    (hrest : L.mem s (affA t) = L.cpu s →
      R (core.num.U64.wrapping_add t 3432#u64) ∧ R (scA t) ∧ R (inqA t)) :
    fastpath.schedulable_here gS s t = fastpath.schedulable_here st s t := by
  by_cases ha : L.mem s (affA t) = L.cpu s
  · obtain ⟨h1, h2, h3⟩ := hrest ha
    exact fastpath.schedulable_here.guard (gS := gS) s t hct htm hrh htd hrs hdt hcd haf h1 h2 h3
  · unfold fastpath.schedulable_here
    simp only [gst_cur_cpu, L.cur_cpu_eq, bind_ok]
    rw [sched.cur_time.guard (gS := gS) s hct, obj.node_get.guard (gS := gS) s _ _ htm,
      obj.node_get.guard (gS := gS) s _ _ hrh, sched.is_cur_domain_expired.guard (gS := gS) (st := st) s,
      sched.domain_time.guard (gS := gS) s hdt, obj.Tcb.affinity.guard (gS := gS) t s haf, aff_ok]
    rw [node_get_ok s _ layout.node.TIMER_MIN, node_get_ok s _ layout.node.RELEASE_HEAD]
    simp only [bind_ok, is_null_ok, ha, ↓reduceIte]
    by_cases h0 : L.mem s (tmA (L := L) s) = 0#u64
    · simp only [h0, decide_true, ↓reduceIte]
      by_cases h1 : L.mem s (rhA (L := L) s) = 0#u64
      · simp only [h1, decide_true, ↓reduceIte]
      · obtain ⟨hs1, hs2⟩ := hrs h1
        rw [obj.Tcb.sc.guard (gS := gS) _ s hs1, tcb_sc_ok s (L.mem s (rhA (L := L) s))]
        simp only [bind_ok]
        rw [sporadic.ready.guard (gS := gS) s _ hs2 hct]
    · rw [obj.Tcb.timer_deadline.guard (gS := gS) _ s (htd h0)]
      by_cases h1 : L.mem s (rhA (L := L) s) = 0#u64
      · simp only [h1, decide_true, ↓reduceIte]
      · obtain ⟨hs1, hs2⟩ := hrs h1
        rw [obj.Tcb.sc.guard (gS := gS) _ s hs1, tcb_sc_ok s (L.mem s (rhA (L := L) s))]
        simp only [bind_ok]
        rw [sporadic.ready.guard (gS := gS) s _ hs2 hct]

variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **A declined fast path on `gS`** (`R` holding `VmFDec`). -/
theorem vm_fault_guard_dec {X : S} {a : A} {t : obj.Tcb} {f : error.Fault} {r : Bool × S × A}
    (D : VmFDec (L := L) R X t) (h : fastpath_vm.vm_fault st ar X a t f = ok r) (hn : r.1 ≠ true) :
    fastpath_vm.vm_fault gS ar X a t f = ok r := by
  change fastFaultG st ar X a t f fl4_abi.consts.fault.VMFault = ok r at h
  show fastFaultG gS ar X a t f fl4_abi.consts.fault.VMFault = ok r
  unfold fastFaultG at h ⊢
  revert h
  rw [sched.action.guard (gS := gS) X (D.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  refine tr_bind_same (fun sl hsl => ?_)
  rw [obj.Slot.cap.guard (gS := gS) sl X (D.fh sl hsl).1 (D.fh sl hsl).2]
  refine tr_bind_same (fun c hc => ?_)
  cases c
  case Endpoint ptr badge x y g gr =>
    obtain ⟨hs, hh, hd⟩ := D.ep sl ptr badge x y g gr hsl hc
    refine tr_ite (fun _ => ?_) (fun _ => tr_ite (fun _ => ?_) (fun _ h' => h'))
    all_goals
      rw [obj.Ep.state.guard (gS := gS) ptr X hs]
      refine tr_bind_same (fun i1 ei1 => ?_)
      refine tr_ite (fun _ h' => h') (fun hne => ?_)
      have e1 : i1 = obj.EP_RECV := Classical.not_not.mp (fun h => hne (bne_iff_ne.mpr h))
      rw [obj.Ep.head.guard (gS := gS) ptr X hh]
      refine tr_bind_same (fun d ed => ?_)
      have Dd := hd (by rw [ei1, e1]) d ed
      rw [obj.Tcb.reply_obj.guard (gS := gS) d X Dd.rp]
      refine tr_bind_same (fun i3 _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [vm_here_guard (gS := gS) X d (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
        (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
        (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
        D.tm D.rh D.dt D.cd Dd.af (fun h => ⟨(Dd.rest h).1, (Dd.rest h).2.1, (Dd.rest h).2.2.1⟩)]
      refine tr_bind_same (fun b hb => ?_)
      refine tr_ite (fun hbt => ?_) (fun _ h' => h')
      have HF := here_facts (L := L) (show fastpath.schedulable_here st X d = ok true by rw [hb, hbt])
      rw [sched.cur_domain.guard (gS := gS) X D.cd]
      refine tr_bind_same (fun i4 _ => ?_)
      rw [obj.Tcb.prio.guard (gS := gS) d X (Dd.rest HF.aff).2.2.2]
      refine tr_bind_same (fun i5 _ => ?_)
      rw [sched.is_highest_prio.guard (gS := gS) X _ _ D.bm]
      refine tr_bind_same (fun b1 _ => ?_)
      exact tr_ite (fun _ hk => absurd (faultTailG_fst st ar
        (hk : faultTailG st ar X a t f fl4_abi.consts.fault.VMFault ptr badge d i3 = ok r)) hn) (fun _ h' => h')
  all_goals exact fun h' => h'

/-- **A declined VM-fault local path on `gS`**: the prefix's node words, then `VmFDec` at the state after
`update_timestamp`. -/
theorem vm_local_guard_dec {X : S} {a : A} {addr code : U64} {r : Bool × S × A}
    (hct : R (ctA (L := L) X)) (hwct : W (ctA (L := L) X)) (hcn : R (cnA (L := L) X)) (hwcn : W (cnA (L := L) X))
    (hmid : ∀ X1 a1, sched.update_timestamp st ar X a = ok (X1, a1) →
      R (L.nodeAt X1 (L.cpu X1) layout.node.CUR_SC) ∧ R (L.nodeAt X1 (L.cpu X1) layout.node.CONSUMED) ∧
      R (L.nodeAt X1 (L.cpu X1) layout.node.CUR_THREAD) ∧ RdHead (L := L) R X1 (L.cscW X1) ∧
      VmFDec (L := L) R X1 (L.curW X1))
    (h : syscall.handle_vm_fault_local st ar X a addr code = ok r) (hn : r.1 ≠ true) :
    syscall.handle_vm_fault_local gS ar X a addr code = ok r := by
  unfold syscall.handle_vm_fault_local at h ⊢
  revert h
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [sched.update_timestamp.guard (gS := gS) ar X a hct hwct hcn hwcn]
  refine tr_bind_same (fun y eu => ?_)
  obtain ⟨X1, a1⟩ := y
  simp only [uncurry_apply_pair]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hmid X1 a1 eu
  rw [sched.cur_sc.guard (gS := gS) X1 h1]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.consumed.guard (gS := gS) X1 h2]
  refine tr_bind_same (fun u _ => ?_)
  have ec : csc = L.cscW X1 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecsc; exact (ok_inj_ff ecsc).symm
  rw [ec, sporadic.sufficient.guard (gS := gS) ar X1 a1 (L.cscW X1) u h4]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h' => h')
  rw [sched.cur_thread.guard (gS := gS) X1 h3, cur_thread_ok]
  simp only [bind_ok]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_bind_same (fun f _ => ?_)
  exact fun h' => vm_fault_guard_dec h5 h' hn

end gen

/-! ## The glue's lock, and the entry facts after the prefix -/

/-- **`VmGlue`** [P] (module docstring): the body runs only with the endpoint of the current thread's
fault-handler cap locked, stated for the cap the body reads after its `update_timestamp`. -/
def VmGlue {A : Type} (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A)
    (Locks : S → U64 → Prop) (s : S) : Prop :=
  ∀ a s1 a1 sl ptr badge x y g gr, sched.update_timestamp st ar s a = ok (s1, a1) →
    obj.Tcb.slot (L.curW s1) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
    obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x y g gr) → Locks s ptr

/-- An endpoint of P1's heap is placed. -/
theorem vm_epP {Ω Sg Rp Scs Nt Ac : Set U64} {Z : U64 → Nat} {s1 : S} {ptr : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hpH : H ptr = some .ep) : EpPlaced T ptr := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  obtain ⟨E, EQ, hW⟩ := hSQ.eps
  obtain ⟨w1, -, -, -, -, w6⟩ := hW
  exact (w1 ptr ((w6.2.2.1 ptr).2 (Or.inl hpH))).1

/-- The head of an endpoint in the receive state is a TCB of `T`. -/
theorem vm_headT {Ω Sg Rp Scs Nt Ac : Set U64} {Z : U64 → Nat} {s1 : S} {ptr : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hpH : H ptr = some .ep)
    (hst : L.epState s1 ptr = obj.EP_RECV) : L.mem s1 (epHeadA ptr) ∈ T := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  obtain ⟨E, EQ, hW⟩ := hSQ.eps
  obtain ⟨w1, -, -, -, -, w6⟩ := hW
  have hpE : ptr ∈ E := (w6.2.2.1 ptr).2 (Or.inl hpH)
  obtain ⟨-, -, hQ⟩ := w1 ptr hpE
  have hst2 : L.epState s1 ptr = 2#u64 := by rw [hst, ep_recv_val']
  cases hl : EQ ptr with
  | nil =>
    have h1 := (w6.2.2.2.2.2 ptr hpE hl).1 hpH
    rw [hst2] at h1; exact absurd h1 (by decide)
  | cons y0 rest =>
    rw [hl] at hQ
    have h1 := hQ.head
    simp only [LawfulStore.epQ, List.headD_cons] at h1
    have e : L.mem s1 (epHeadA ptr) = y0 := h1
    rw [e]
    exact hQ.mem y0 List.mem_cons_self

/-- **The read facts at the state `s1` after the entry's `update_timestamp`**, read set `IoRS K Locks s`. -/
structure VmDF (st : machine.Store S) [L : LawfulStore st] (K : KLayout) (T : Set U64)
    (Locks : S → U64 → Prop) (s s1 : S) : Prop where
  k : L.ksb s1 = L.ksb s
  c : L.cpu s1 = L.cpu s
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → IoRS (st := st) K Locks s (L.nodeAt s1 (L.cpu s1) o)
  ksw : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 →
    IoRS (st := st) K Locks s (core.num.U64.wrapping_add (L.ksb s1) o)
  cur : L.curW s1 = L.curW s
  sl : ∀ sl, obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
    IoRS (st := st) K Locks s sl ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add sl 8#u64)
  ep : ∀ sl ptr badge x y g gr, obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
    obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x y g gr) →
    IoRS (st := st) K Locks s (epTSA ptr) ∧ IoRS (st := st) K Locks s (epHeadA ptr) ∧
      (L.epState s1 ptr = obj.EP_RECV → L.mem s1 (epHeadA ptr) ∈ T)
  gate : ∀ d ∈ T, ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 → GateField off.val →
    IoRS (st := st) K Locks s (fld d off)
  home : ∀ d ∈ T, L.mem s1 (affA d) = L.cpu s1 → ∀ off : U64, 192 ≤ off.val → off.val < 4096 →
    off.val % 8 = 0 → ¬ GateField off.val → ¬ TimerField off.val → ¬ GField off.val →
    IoRS (st := st) K Locks s (fld d off)
  td : L.mem s1 (tmA (L := L) s1) ≠ 0#u64 →
    IoRS (st := st) K Locks s (core.num.U64.wrapping_add (L.mem s1 (tmA (L := L) s1)) 3528#u64)
  rs : L.mem s1 (rhA (L := L) s1) ≠ 0#u64 → IoRS (st := st) K Locks s (scA (L.mem s1 (rhA (L := L) s1))) ∧
    RdHead (L := L) (IoRS (st := st) K Locks s) s1 (L.mem s1 (scA (L.mem s1 (rhA (L := L) s1))))
  suf : RdHead (L := L) (IoRS (st := st) K Locks s) s1 (L.cscW s1)

/-- **`VmDF` from the entry facts.** -/
theorem vm_dfOf {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s) (hlkE : VmGlue st ar Locks s)
    {a : A} {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar s a = ok (s1, a1)) :
    VmDF st K T Locks s s1 := by
  have B := P.base
  have hN := B.np
  have hT := B.tp
  have HY := P.hyp a s1 a1 eu
  have hlk := fun sl ptr badge x y g gr => hlkE a s1 a1 sl ptr badge x y g gr eu
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok ar hN hn] at eu
  have eS := (Prod.mk.inj (ok_inj_ff eu)).1
  subst eS
  have etm : L.mem (utW (L := L) s n) (tmA (L := L) (utW (L := L) s n)) = L.mem s (tmA (L := L) s) := by
    show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.TIMER_MIN) = _
    rw [ut_nodeAt]
    exact ut_node hN n (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
  have erh : L.mem (utW (L := L) s n) (rhA (L := L) (utW (L := L) s n)) = L.mem s (rhA (L := L) s) := by
    show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.RELEASE_HEAD) = _
    rw [ut_nodeAt]
    exact ut_node hN n (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
  refine
    { k := utW_ksb s n
      c := utW_cpu s n
      nd := fun o ho h8 => (nd_at (fun o ho h8 => B.nd (Locks := Locks) o ho h8) (utW_ksb s n) (utW_cpu s n) o ho h8).1
      ksw := fun o ho h8 => by rw [utW_ksb]; exact B.ksw ho h8
      cur := ut_cur hN n
      sl := fun sl hsl => B.tslot B.cT hsl (by simp [layout.tcb.SLOT_FAULT_HANDLER])
      ep := ?_
      gate := fun d hd off h1 h2 h8 hg => B.gate hd h1 h2 h8 hg
      home := ?_
      td := ?_
      rs := ?_
      suf := ?_ }
  · intro sl ptr badge x y g gr hsl hcap
    have hsl' : obj.Tcb.slot (L.curW (utW (L := L) s n)) layout.tcb.SLOT_FAULT_HANDLER = ok sl := by
      rw [ut_cur hN n]; exact hsl
    have hl := hlk sl ptr badge x y g gr hsl' hcap
    have hpH : H ptr = some .ep := by
      have h1 := HY.cap
      rw [hsl', WP.spec_ok, hcap, WP.spec_ok] at h1
      exact h1.1 ptr badge x y g gr rfl
    have hK := P.hEp ptr hpH
    have hEP := vm_epP HY.bxi hpH
    have h1 := epTSA_val hEP
    have h2 := epHeadA_val (ep := ptr)
    have := hEP.fits
    have := hEP.align
    exact ⟨(B.ep hK (b := epTSA ptr) ⟨by omega, by omega⟩ (by unfold Aligned; omega) hl).1,
      (B.ep hK (b := epHeadA ptr) ⟨by omega, by omega⟩ (by unfold Aligned; omega) hl).1,
      fun hst => vm_headT HY.bxi hpH hst⟩
  · intro d hd haff off h1 h2 h8 hg htm hG
    have e : L.mem (utW (L := L) s n) (affA d) = L.mem s (affA d) :=
      ut_tcb hN hT n hd (Kx := 3520#u64) (by simp) (by simp)
    rw [e, utW_cpu] at haff
    exact (B.homeOf hd haff h1 h2 h8 hg htm hG).1
  · intro h0
    rw [etm] at h0 ⊢
    exact B.td h0
  · intro h0
    rw [erh] at h0 ⊢
    obtain ⟨hrT, hscS, -⟩ := bxi_rh B.bxi h0
    have esc : L.mem (utW (L := L) s n) (scA (L.mem s (rhA (L := L) s))) =
        L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      ut_tcb hN hT n hrT (Kx := 3464#u64) (by simp) (by simp)
    rw [esc]
    obtain ⟨h1, h2⟩ := B.rs h0
    exact ⟨h1, rdHead_ut B.bxi n hscS h2⟩
  · rw [ut_csc hN n]
    exact rdHead_ut B.bxi n B.cscS (B.cscacc.head B.cscwf)

/-! ## Moving facts and results between states equal on the read set -/

/-- A read-only computation answers the same at two states equal on `R`, given it reads `R` only at
both (its guard lemma at each state). -/
theorem ro_congr {α : Type} {R : U64 → Prop} {x y : S} (h : Ag st R x y) (F : machine.Store S → S → Result α)
    (hF : ∀ z, F (PathObl.guard st R (fun _ => True)) z = F (cst (S := S) (fun a => (PathObl.guard st R (fun _ => True)).read z a)
      (fun a => (PathObl.guard st R (fun _ => True)).read_pair z a) (st.ks_base z) (st.cur_cpu z)) x)
    (gx : F (PathObl.guard st R (fun _ => True)) x = F st x) (gy : F (PathObl.guard st R (fun _ => True)) y = F st y) :
    F st y = F st x := by
  rw [← gx, ← gy, hF y, hF x, ag_cst h]

/-- **`update_timestamp` keeps `Ag`.** -/
theorem vm_ag_upd {A : Type} {ar : machine.Arch A} {R : U64 → Prop} {x y x1 y1 : S} {a a1 a1' : A}
    (hR : ∀ b, R b → Aligned b) (G : Ag st R x y) (rT : R (ctA (L := L) x)) (rN : R (cnA (L := L) x))
    (eu : sched.update_timestamp st ar x a = ok (x1, a1)) (eu' : sched.update_timestamp st ar y a = ok (y1, a1')) :
    a1' = a1 ∧ Ag st R x1 y1 := by
  obtain ⟨now, hn, e1⟩ := upd_eq eu
  obtain ⟨now', hn', e2⟩ := upd_eq eu'
  rw [hn] at hn'
  have en : now' = now := (Prod.mk.inj (ok_inj_ff hn')).1.symm
  have ea : a1' = a1 := (Prod.mk.inj (ok_inj_ff hn')).2.symm
  have eT : ctA (L := L) y = ctA (L := L) x := G.node _
  have eN : cnA (L := L) y = cnA (L := L) x := G.node _
  rw [en, eT, eN] at e2
  have G2 := G.wr hR (a := ctA (L := L) x) (v := now) (hR _ rT)
  rw [G2.m _ rN, G.m _ rT] at e2
  refine ⟨ea, ?_⟩
  rw [e1, e2]
  exact G2.wr hR (hR _ rN)

/-- The facts of `VmDF` that do not name the handler, at an alternative's prefix state. -/
theorem VmDF.alt {s1 x1 : S} {R'' : U64 → Prop} (D : VmDF st K T Locks s s1)
    (G1 : Ag st (IoRS (st := st) K Locks s) s1 x1) (hRR : ∀ b, IoRS (st := st) K Locks s b → R'' b) :
    (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R'' (L.nodeAt x1 (L.cpu x1) o)) ∧
    R'' (core.num.U64.wrapping_add (L.ksb x1) layout.ks.DOMAIN_TIME) ∧
    R'' (core.num.U64.wrapping_add (L.ksb x1) layout.ks.CUR_DOMAIN) ∧
    RdBitmap (L := L) R'' x1 ∧
    (L.mem x1 (tmA (L := L) x1) ≠ 0#u64 → R'' (core.num.U64.wrapping_add (L.mem x1 (tmA (L := L) x1)) 3528#u64)) ∧
    (L.mem x1 (rhA (L := L) x1) ≠ 0#u64 → R'' (scA (L.mem x1 (rhA (L := L) x1))) ∧
      RdHead (L := L) R'' x1 (L.mem x1 (scA (L.mem x1 (rhA (L := L) x1))))) := by
  have nd1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R'' (L.nodeAt x1 (L.cpu x1) o) := fun o ho h8 => by
    rw [G1.node]; exact hRR _ (D.nd o ho h8)
  have etm : L.mem x1 (tmA (L := L) x1) = L.mem s1 (tmA (L := L) s1) := by
    show L.mem x1 (L.nodeAt x1 (L.cpu x1) layout.node.TIMER_MIN) = L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN)
    rw [G1.node]; exact G1.m _ (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
  have erh : L.mem x1 (rhA (L := L) x1) = L.mem s1 (rhA (L := L) s1) := by
    show L.mem x1 (L.nodeAt x1 (L.cpu x1) layout.node.RELEASE_HEAD) =
      L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.RELEASE_HEAD)
    rw [G1.node]; exact G1.m _ (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  refine ⟨nd1, ?_, ?_, ⟨nd1 l1Off (by rw [l1Off_val]; omega) (by rw [l1Off_val]),
    fun inv hinv => nd1 _ (by simp only [w64_val]; omega) (by simp only [w64_val]; omega)⟩, ?_, ?_⟩
  · rw [G1.k]; exact hRR _ (D.ksw _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))
  · rw [G1.k]; exact hRR _ (D.ksw _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN]))
  · intro h0
    rw [etm] at h0 ⊢
    exact hRR _ (D.td h0)
  · intro h0
    rw [erh] at h0 ⊢
    obtain ⟨h1, h2⟩ := D.rs h0
    rw [G1.m _ h1]
    have h3 := G1.rdHead h2
    refine ⟨hRR _ h1, ?_⟩
    unfold RdHead at h3 ⊢
    exact ⟨hRR _ h3.1, hRR _ h3.2.1, hRR _ h3.2.2⟩

/-- **`VmFDec` at an alternative's prefix state**, `R''` holding `IoRS s` and the handler's `REPLY_OBJ`
when it is homed elsewhere (`hrep`). -/
theorem vmFDec_of {s1 x1 : S} {R'' : U64 → Prop} (D : VmDF st K T Locks s s1)
    (G1 : Ag st (IoRS (st := st) K Locks s) s1 x1) (hRR : ∀ b, IoRS (st := st) K Locks s b → R'' b)
    (hrep : ∀ sl ptr badge x y g gr, obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
      obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x y g gr) → L.epState s1 ptr = obj.EP_RECV →
      L.mem s1 (affA (L.mem s1 (epHeadA ptr))) ≠ L.cpu s1 → R'' (replyA (L.mem s1 (epHeadA ptr)))) :
    VmFDec (L := L) R'' x1 (L.curW s) := by
  obtain ⟨nd1, dt1, cd1, bm1, tm1, rh1⟩ := D.alt G1 hRR
  refine ⟨nd1, dt1, cd1, bm1, tm1, rh1, fun sl hsl => ⟨hRR _ (D.sl sl hsl).1, hRR _ (D.sl sl hsl).2⟩, ?_⟩
  intro sl ptr b x y g gr hsl hcap
  obtain ⟨r0, r8⟩ := D.sl sl hsl
  rw [cap_congr_ag G1 r0 r8] at hcap
  obtain ⟨rts, rhd, hHT⟩ := D.ep sl ptr b x y g gr hsl hcap
  refine ⟨hRR _ rts, hRR _ rhd, fun hst d hd => ?_⟩
  have hst1 : L.epState s1 ptr = obj.EP_RECV := by
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) x1 ptr)] at hst
    rw [← ok_inj_ff hst]
    unfold LawfulStore.epState
    rw [G1.m (epTSA ptr) rts]
  have hdd : d = L.mem s1 (epHeadA ptr) := by
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) x1 ptr)] at hd
    rw [← ok_inj_ff hd]; exact G1.m (epHeadA ptr) rhd
  have hdT : d ∈ T := by rw [hdd]; exact hHT hst1
  have rA : IoRS (st := st) K Locks s (affA d) :=
    D.gate d hdT 3520#u64 (by simp) (by simp) (by simp) (by simp [GateField])
  have eA : L.mem x1 (affA d) = L.mem s1 (affA d) := G1.m _ rA
  refine ⟨?_, hRR _ rA, fun hl => ?_⟩
  · by_cases hl : L.mem s1 (affA d) = L.cpu s1
    · exact hRR _ (D.home d hdT hl 3360#u64 (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField]))
    · rw [hdd] at hl ⊢; exact hrep sl ptr b x y g gr hsl hcap hst1 hl
  · have hl1 : L.mem s1 (affA d) = L.cpu s1 := by rw [← eA, ← G1.c]; exact hl
    exact ⟨hRR _ (D.gate d hdT 3432#u64 (by simp) (by simp) (by simp) (by simp [GateField])),
      hRR _ (D.gate d hdT 3464#u64 (by simp) (by simp) (by simp) (by simp [GateField])),
      hRR _ (D.home d hdT hl1 3592#u64 (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField])),
      hRR _ (D.gate d hdT 3448#u64 (by simp) (by simp) (by simp) (by simp [GateField]))⟩

/-! ## A run declining at the entry is accepted at no alternative -/

/-- **Checks passing at an alternative's prefix state pass at the entry's.** -/
theorem vm_chk_back {s1 x1 : S} (D : VmDF st K T Locks s s1)
    (G1 : Ag st (IoRS (st := st) K Locks s) s1 x1) {ptr badge dest r : U64}
    (C : FaultChecks st x1 (L.curW s) ptr badge dest r) : FaultChecks st s1 (L.curW s) ptr badge dest r := by
  obtain ⟨hA, ⟨sl, x, y, g, gr, hS, hcap, hg⟩, hep, hh, hrep, hr0, hhe, ⟨d, p, hd, hp, hhi⟩⟩ := C
  obtain ⟨r0, r8⟩ := D.sl sl hS
  rw [cap_congr_ag G1 r0 r8] at hcap
  obtain ⟨rts, rhd, hHT⟩ := D.ep sl ptr badge x y g gr hS hcap
  have eep : obj.Ep.state st ptr x1 = obj.Ep.state st ptr s1 := by
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) x1 ptr), eq_of_spec_fd (obj.Ep.state.spec (L := L) s1 ptr)]
    unfold LawfulStore.epState
    rw [G1.m (epTSA ptr) rts]
  rw [eep] at hep
  have hst : L.epState s1 ptr = obj.EP_RECV := by
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s1 ptr)] at hep; exact ok_inj_ff hep
  have ehd : obj.Ep.head st ptr x1 = obj.Ep.head st ptr s1 := by
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) x1 ptr), eq_of_spec_fd (obj.Ep.head.spec' (L := L) s1 ptr)]
    exact congrArg ok (G1.m (epHeadA ptr) rhd)
  rw [ehd] at hh
  have hdd : dest = L.mem s1 (epHeadA ptr) := by
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) s1 ptr)] at hh; exact (ok_inj_ff hh).symm
  have hdT : dest ∈ T := by rw [hdd]; exact hHT hst
  have rA : IoRS (st := st) K Locks s (affA dest) :=
    D.gate dest hdT 3520#u64 (by simp) (by simp) (by simp) (by simp [GateField])
  have eA : L.mem x1 (affA dest) = L.mem s1 (affA dest) := G1.m _ rA
  have HF := here_facts (L := L) hhe
  have haf : L.mem s1 (affA dest) = L.cpu s1 := by rw [← eA, ← G1.c]; exact HF.aff
  have rR : IoRS (st := st) K Locks s (replyA dest) :=
    D.home dest hdT haf 3360#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
      (by simp [GField])
  have erp : obj.Tcb.reply_obj st dest x1 = obj.Tcb.reply_obj st dest s1 := by
    rw [eq_of_spec_fd (obj.Tcb.reply_obj.spec (L := L) x1 dest),
      eq_of_spec_fd (obj.Tcb.reply_obj.spec (L := L) s1 dest)]
    exact congrArg ok (G1.m _ rR)
  rw [erp] at hrep
  -- `schedulable_here`, `cur_domain`, `prio`, `is_highest_prio`
  obtain ⟨nd1, dt1, cd1, bm1, tm1, rh1⟩ := D.alt G1 (fun b hb => hb)
  have rD : IoRS (st := st) K Locks s (core.num.U64.wrapping_add dest 3432#u64) :=
    D.gate dest hdT 3432#u64 (by simp) (by simp) (by simp) (by simp [GateField])
  have rS : IoRS (st := st) K Locks s (scA dest) :=
    D.gate dest hdT 3464#u64 (by simp) (by simp) (by simp) (by simp [GateField])
  have rQ : IoRS (st := st) K Locks s (inqA dest) :=
    D.home dest hdT haf 3592#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
      (by simp [GField])
  have rP : IoRS (st := st) K Locks s (prioA dest) :=
    D.gate dest hdT 3448#u64 (by simp) (by simp) (by simp) (by simp [GateField])
  have rCD : IoRS (st := st) K Locks s (core.num.U64.wrapping_add (L.ksb s1) layout.ks.CUR_DOMAIN) :=
    D.ksw _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  have bm0 : RdBitmap (L := L) (IoRS (st := st) K Locks s) s1 :=
    ⟨D.nd l1Off (by rw [l1Off_val]; omega) (by rw [l1Off_val]),
      fun inv hinv => D.nd _ (by simp only [w64_val]; omega) (by simp only [w64_val]; omega)⟩
  have g1 : fastpath.schedulable_here (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) s1 dest =
      fastpath.schedulable_here st s1 dest :=
    fastpath.schedulable_here.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) s1 dest
      (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])) D.td D.rs
      (D.ksw _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])) rCD rA rD rS rQ
  have g2 : fastpath.schedulable_here (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x1 dest =
      fastpath.schedulable_here st x1 dest :=
    fastpath.schedulable_here.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x1 dest
      (nd1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (nd1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (nd1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])) tm1 rh1 dt1 cd1 rA rD rS rQ
  have ehere : fastpath.schedulable_here st x1 dest = fastpath.schedulable_here st s1 dest :=
    ro_congr G1 (fun m z => fastpath.schedulable_here m z dest) (fun _ => rfl) g1 g2
  rw [ehere] at hhe
  have ecd : sched.cur_domain st x1 = sched.cur_domain st s1 := by
    rw [cur_domain_ok, cur_domain_ok, G1.k]
    exact congrArg ok (G1.m _ rCD)
  rw [ecd] at hd
  have epr : obj.Tcb.prio st dest x1 = obj.Tcb.prio st dest s1 := by
    rw [eq_of_spec_fd (obj.Tcb.prio.spec (L := L) x1 dest), eq_of_spec_fd (obj.Tcb.prio.spec (L := L) s1 dest)]
    exact congrArg ok (G1.m _ rP)
  rw [epr] at hp
  have h1 : sched.is_highest_prio (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) s1 d p =
      sched.is_highest_prio st s1 d p := sched.is_highest_prio.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) s1 d p bm0
  have h2 : sched.is_highest_prio (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x1 d p =
      sched.is_highest_prio st x1 d p := sched.is_highest_prio.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x1 d p bm1
  have ehi : sched.is_highest_prio st x1 d p = sched.is_highest_prio st s1 d p :=
    ro_congr G1 (fun m z => sched.is_highest_prio m z d p) (fun _ => rfl) h1 h2
  rw [ehi] at hhi
  have hact : sched.action st s1 = ok sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) _)] at hA ⊢
    rw [← ok_inj_ff hA]
    unfold LawfulStore.actionW
    rw [G1.node, G1.m _ (D.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
  exact ⟨hact, ⟨sl, x, y, g, gr, hS, hcap, hg⟩, hep, hh, hrep, hr0, hhe, ⟨d, p, hd, hp, hhi⟩⟩

theorem vm_nd_ne : ¬ (layout.NUM_DOMAINS != 1#u64) = true := by
  simp [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]

set_option maxHeartbeats 1000000 in
/-- **A run that declines at `s` is accepted at no alternative state.** -/
theorem vm_alt_not_acc {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s) (hlkE : VmGlue st ar Locks s)
    {x : S} (G : Ag st (IoRS (st := st) K Locks s) s x) {a : A} {addr code : U64} {r : Bool × S × A}
    {z : S} {b : A} (h : syscall.handle_vm_fault_local st ar s a addr code = ok r) (hr : r.1 ≠ true)
    (h' : syscall.handle_vm_fault_local st ar x a addr code = ok (true, z, b)) : False := by
  have B := P.base
  unfold syscall.handle_vm_fault_local at h h'
  rw [if_neg vm_nd_ne] at h h'
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  obtain ⟨⟨x1, a1'⟩, eu', h'⟩ := bind_eq_ok h'
  simp only [uncurry_apply_pair] at h h'
  have rT := (B.nd (Locks := Locks) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
  have rN := (B.nd (Locks := Locks) layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
  obtain ⟨ea, G1⟩ := vm_ag_upd (fun _ hb => hb.1) G rT rN eu eu'
  rw [ea] at h'
  have D := vm_dfOf hA P hlkE eu
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨csc', ecsc', h'⟩ := bind_eq_ok h'
  obtain ⟨u, eu1, h⟩ := bind_eq_ok h
  obtain ⟨u', eu1', h'⟩ := bind_eq_ok h'
  obtain ⟨bb, ebb, h⟩ := bind_eq_ok h
  obtain ⟨bb', ebb', h'⟩ := bind_eq_ok h'
  have nS := D.nd layout.node.CUR_SC (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have nC := D.nd layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have nT := D.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have nS' : IoRS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CUR_SC) := by rw [G1.node]; exact nS
  have nC' : IoRS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CONSUMED) := by rw [G1.node]; exact nC
  have gs1 : sched.cur_sc (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) s1 = sched.cur_sc st s1 :=
    sched.cur_sc.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) s1 nS
  have gs2 : sched.cur_sc (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x1 = sched.cur_sc st x1 :=
    sched.cur_sc.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x1 nS'
  have gc1 : sched.consumed (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) s1 = sched.consumed st s1 :=
    sched.consumed.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) s1 nC
  have gc2 : sched.consumed (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x1 = sched.consumed st x1 :=
    sched.consumed.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x1 nC'
  have ecs : sched.cur_sc st x1 = sched.cur_sc st s1 :=
    ro_congr G1 (fun m z => sched.cur_sc m z) (fun _ => rfl) gs1 gs2
  have ecn : sched.consumed st x1 = sched.consumed st s1 :=
    ro_congr G1 (fun m z => sched.consumed m z) (fun _ => rfl) gc1 gc2
  rw [ecs, ecsc] at ecsc'
  rw [ecn, eu1] at eu1'
  have e1 : csc' = csc := (ok_inj_ff ecsc').symm
  have e2 : u' = u := (ok_inj_ff eu1').symm
  rw [e1, e2] at ebb'
  have hcs : csc = L.cscW s1 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s1)] at ecsc; exact (ok_inj_ff ecsc).symm
  have esuf : sporadic.sufficient st ar x1 a1 csc u = sporadic.sufficient st ar s1 a1 csc u := by
    rw [hcs]
    have q1 : sporadic.sufficient (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) ar s1 a1 (L.cscW s1) u =
        sporadic.sufficient st ar s1 a1 (L.cscW s1) u := sporadic.sufficient.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) ar s1 a1 (L.cscW s1) u D.suf
    have q2 : sporadic.sufficient (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) ar x1 a1 (L.cscW s1) u =
        sporadic.sufficient st ar x1 a1 (L.cscW s1) u :=
      sporadic.sufficient.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) ar x1 a1 (L.cscW s1) u (G1.rdHead D.suf)
    exact ro_congr G1 (fun m z => sporadic.sufficient m ar z a1 (L.cscW s1) u) (fun _ => rfl) q1 q2
  rw [esuf, ebb] at ebb'
  have e3 : bb' = bb := (ok_inj_ff ebb').symm
  rw [e3] at h'
  by_cases hb : bb = true
  swap
  · rw [if_neg hb] at h'; exact Bool.false_ne_true (congrArg Prod.fst (ok_inj_ff h'))
  rw [if_pos hb] at h h'
  rw [cur_thread_ok] at h h'
  simp only [bind_ok] at h h'
  have ecur1 : L.curW x1 = L.curW s1 := by
    unfold LawfulStore.curW; rw [G1.node]; exact G1.m _ nT
  rw [ecur1, D.cur] at h'
  rw [D.cur] at h
  obtain ⟨j1, ej1, h'⟩ := bind_eq_ok h'
  obtain ⟨j2, ej2, h'⟩ := bind_eq_ok h'
  obtain ⟨f, ef, h'⟩ := bind_eq_ok h'
  rw [ej1] at h
  simp only [bind_ok] at h
  rw [ej2] at h
  simp only [bind_ok] at h
  rw [ef] at h
  simp only [bind_ok] at h
  obtain ⟨ptr, badge, dest, rr, C', -⟩ := vm_fault_acc st ar h'
  have C1 := vm_chk_back D G1 C'
  have h2 : faultTailG st ar s1 a1 (L.curW s) f fl4_abi.consts.fault.VMFault ptr badge dest rr = ok r := by
    rw [← fastFaultG_checks st ar C1]; exact h
  exact hr (faultTailG_fst st ar h2)

/-! ## A declined run at an alternative, on a guarded store -/

/-- **A run declining at an alternative `x` runs the same on `PathObl.guard st R'' (IoDS s)`**, `R''` holding
`IoRS s` and, when the handler is homed elsewhere, its `REPLY_OBJ` word (`hrep`). -/
theorem vm_dec_tr {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s) (hlkE : VmGlue st ar Locks s)
    {x : S} (G : Ag st (IoRS (st := st) K Locks s) s x) {a : A} {addr code : U64} {R'' : U64 → Prop}
    (hRR : ∀ b, IoRS (st := st) K Locks s b → R'' b)
    (hrep : ∀ s1 a1 sl ptr badge x y g gr, sched.update_timestamp st ar s a = ok (s1, a1) →
      obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
      obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x y g gr) → L.epState s1 ptr = obj.EP_RECV →
      L.mem s1 (affA (L.mem s1 (epHeadA ptr))) ≠ L.cpu s1 → R'' (replyA (L.mem s1 (epHeadA ptr))))
    {r' : Bool × S × A} (h' : syscall.handle_vm_fault_local st ar x a addr code = ok r') (hn : r'.1 ≠ true) :
    syscall.handle_vm_fault_local (PathObl.guard st R'' (IoDS (st := st) s)) ar x a addr code = ok r' := by
  have B := P.base
  have rT := (B.nd (Locks := Locks) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
  have rN := (B.nd (Locks := Locks) layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
  obtain ⟨⟨n, a2⟩, hn2, -⟩ := spec_ex_fd (hA.now a)
  obtain ⟨⟨s1, a3⟩, eu⟩ : ∃ y, sched.update_timestamp st ar s a = ok y := ⟨_, update_timestamp_ok ar B.np hn2⟩
  have D := vm_dfOf hA P hlkE eu
  have hct : R'' (ctA (L := L) x) := by
    show R'' (L.nodeAt x (L.cpu x) layout.node.CUR_TIME); rw [G.node]; exact hRR _ rT
  have hcn : R'' (cnA (L := L) x) := by
    show R'' (L.nodeAt x (L.cpu x) layout.node.CONSUMED); rw [G.node]; exact hRR _ rN
  have wct : IoDS (st := st) s (ctA (L := L) x) := by
    show IoDS (st := st) s (L.nodeAt x (L.cpu x) layout.node.CUR_TIME); rw [G.node]; exact Or.inr (Or.inl rfl)
  have wcn : IoDS (st := st) s (cnA (L := L) x) := by
    show IoDS (st := st) s (L.nodeAt x (L.cpu x) layout.node.CONSUMED); rw [G.node]; exact Or.inr (Or.inr rfl)
  refine vm_local_guard_dec (gS := PathObl.guard st R'' (IoDS (st := st) s)) hct wct hcn wcn ?_ h' hn
  intro x1 a1 eu'
  obtain ⟨-, G1⟩ := vm_ag_upd (fun _ hb => hb.1) G rT rN eu eu'
  have nd1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R'' (L.nodeAt x1 (L.cpu x1) o) := fun o ho h8 => by
    rw [G1.node]; exact hRR _ (D.nd o ho h8)
  have ecur1 : L.curW x1 = L.curW s := by
    have e : L.curW x1 = L.curW s1 := by
      unfold LawfulStore.curW; rw [G1.node]
      exact G1.m _ (D.nd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]))
    rw [e]; exact D.cur
  have ecsc : L.cscW x1 = L.cscW s1 := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [G1.node]; exact G1.m _ (D.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
  have hs := G1.rdHead D.suf
  rw [← ecsc] at hs
  refine ⟨nd1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]),
    nd1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
    nd1 _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]), ?_, ?_⟩
  · unfold RdHead at hs ⊢
    exact ⟨hRR _ hs.1, hRR _ hs.2.1, hRR _ hs.2.2⟩
  · rw [ecur1]
    exact vmFDec_of D G1 hRR (fun sl ptr badge x y g gr hsl hcap hst hne =>
      hrep s1 a3 sl ptr badge x y g gr eu hsl hcap hst hne)

/-! ## A declined run on other stores -/

section dm
variable {m : machine.Store S}

set_option maxHeartbeats 4000000 in
/-- **A declined fast path on `m`** (reading as `st`). -/
theorem vm_fault_dec_m (h : RdEq st m) {A : Type} {ar : machine.Arch A} {x1 : S} {a1 : A} {t : obj.Tcb}
    {f : error.Fault} {r : Bool × S × A} (hn : r.1 ≠ true) :
    fastpath_vm.vm_fault st ar x1 a1 t f = ok r → fastpath_vm.vm_fault m ar x1 a1 t f = ok r := by
  show fastFaultG st ar x1 a1 t f fl4_abi.consts.fault.VMFault = ok r →
    fastFaultG m ar x1 a1 t f fl4_abi.consts.fault.VMFault = ok r
  unfold fastFaultG
  rw [h.ro x1 (fun n => sched.action n x1) (fun _ => rfl)]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  refine tr_bind_same (fun sl hsl => ?_)
  rw [h.ro x1 (fun n => obj.Slot.cap n sl x1) (fun _ => rfl)]
  refine tr_bind_same (fun c hc => ?_)
  cases c
  case Endpoint ptr badge x y g gr =>
    refine tr_ite (fun _ => ?_) (fun _ => tr_ite (fun _ => ?_) (fun _ h' => h'))
    all_goals
      rw [h.ro x1 (fun n => obj.Ep.state n ptr x1) (fun _ => rfl)]
      refine tr_bind_same (fun _ _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [h.ro x1 (fun n => obj.Ep.head n ptr x1) (fun _ => rfl)]
      refine tr_bind_same (fun d _ => ?_)
      rw [h.ro x1 (fun n => obj.Tcb.reply_obj n d x1) (fun _ => rfl)]
      refine tr_bind_same (fun i3 _ => ?_)
      refine tr_ite (fun _ h' => h') (fun _ => ?_)
      rw [h.ro x1 (fun n => fastpath.schedulable_here n x1 d) (fun _ => rfl)]
      refine tr_bind_same (fun _ _ => ?_)
      refine tr_ite (fun _ => ?_) (fun _ h' => h')
      rw [h.ro x1 (fun n => sched.cur_domain n x1) (fun _ => rfl)]
      refine tr_bind_same (fun i4 _ => ?_)
      rw [h.ro x1 (fun n => obj.Tcb.prio n d x1) (fun _ => rfl)]
      refine tr_bind_same (fun i5 _ => ?_)
      rw [h.ro x1 (fun n => sched.is_highest_prio n x1 i4 i5) (fun _ => rfl)]
      refine tr_bind_same (fun _ _ => ?_)
      exact tr_ite (fun _ hk => absurd (faultTailG_fst st ar
        (hk : faultTailG st ar x1 a1 t f fl4_abi.consts.fault.VMFault ptr badge d i3 = ok r)) hn) (fun _ h' => h')
  all_goals exact fun h' => h'

/-- **A declined VM-fault local path on `m`** (reading as `st`, writing the prefix words as `st`). -/
theorem vm_dec_m (h : RdEq st m) {A : Type} {ar : machine.Arch A} {x : S} {a : A} {addr code : U64}
    {r : Bool × S × A} (hP : PreOK st m x (L.curW x))
    (hr : syscall.handle_vm_fault_local st ar x a addr code = ok r) (hn : r.1 ≠ true) :
    syscall.handle_vm_fault_local m ar x a addr code = ok r := by
  unfold syscall.handle_vm_fault_local at hr ⊢
  revert hr
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [upd_m h hP rfl rfl]
  refine tr_bind_same (fun y _ => ?_)
  obtain ⟨x1, a1⟩ := y
  simp only [uncurry_apply_pair]
  rw [h.ro x1 (fun n => sched.cur_sc n x1) (fun _ => rfl)]
  refine tr_bind_same (fun csc _ => ?_)
  rw [h.ro x1 (fun n => sched.consumed n x1) (fun _ => rfl)]
  refine tr_bind_same (fun u _ => ?_)
  rw [h.ro x1 (fun n => sporadic.sufficient n ar x1 a1 csc u) (fun _ => rfl)]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h' => h')
  rw [h.ro x1 (fun n => sched.cur_thread n x1) (fun _ => rfl)]
  refine tr_bind_same (fun t _ => ?_)
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_bind_same (fun f _ => ?_)
  exact vm_fault_dec_m h hn

end dm

/-- The declined run's possible writes are aligned safe words. -/
theorem VmBase.dsSafe (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {b : U64} (hb : IoDS (st := st) s b) :
    Aligned b ∧ SafeW K b := by
  rcases hb with rfl | rfl | rfl
  · obtain ⟨k, hk, e⟩ := regA_eq P.tA (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    have hk' : k.val = 392 := by rw [hk]; simp [layout.reg.FAULT_IP]
    have ht := P.hT _ P.cT
    rw [e]
    refine ⟨field_aligned P.tA (by omega) (by omega), Or.inr (Or.inl ⟨_, k.val, ht,
      P.lay.io.tcbw _ ht k (by omega) (by omega), by omega, tcb_wadd_val P.tA (by omega),
      by omega, by omega, by omega, by omega, by omega, by omega⟩)⟩
  · exact ⟨nodeAt_aligned P.np (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]),
      Or.inl ⟨_, P.lay.io.node _ _ (P.inNode _ (by simp [layout.node.CUR_TIME]))⟩⟩
  · exact ⟨nodeAt_aligned P.np (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
      Or.inl ⟨_, P.lay.io.node _ _ (P.inNode _ (by simp [layout.node.CONSUMED]))⟩⟩

/-- **`PathObl.dec_alt`** for the VM-fault local path. -/
theorem vm_dec_alt {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K)
    (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s) (hlkE : VmGlue st ar Locks s)
    {addr code : U64} {a : A} {r r' : Bool × S × A} {s' : S}
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok r) (hr : r.1 ≠ true)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    (h' : syscall.handle_vm_fault_local st ar s' a addr code = ok r') :
    r'.1 ≠ true ∧
      syscall.handle_vm_fault_local (PathObl.guard st (fun _ => True) (IoDS (st := st) s)) ar s' a addr code = ok r' ∧
      syscall.handle_vm_fault_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s' a addr code = ok r' := by
  have B := P.base
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (B.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hpre : ∀ b, (b = regA (L.curW s') layout.reg.FAULT_IP ∨
      b = L.nodeAt s' (L.cpu s') layout.node.CUR_TIME ∨ b = L.nodeAt s' (L.cpu s') layout.node.CONSUMED) →
      IoDS (st := st) s b := by
    intro b hb
    rw [hcur, G.node, G.node] at hb
    exact hb
  have hn : r'.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r'
    intro hb
    change b = true at hb
    subst hb
    exact vm_alt_not_acc hA P hlkE G h hr h'
  refine ⟨hn, ?_, ?_⟩
  · exact vm_dec_m ⟨fun _ _ => guard_read trivial, fun _ _ => guard_read_pair trivial trivial,
      fun _ => rfl, fun _ => rfl⟩ (fun y b v hb _ _ => guard_write (hpre b hb)) h' hn
  · have hR : RdEq st (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) :=
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
    have hW : PreOK st (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) s' (L.curW s') := by
      intro y b v hb _ _
      obtain ⟨ha, hs⟩ := B.dsSafe (hpre b hb)
      rw [L.write_eq]
      exact mguard_write (L.write_eq y b v) (stepOK_safe (m0 := m0) hK hLA ha hs)
    exact vm_dec_m hR hW h' hn

/-! ## The handler's `REPLY_OBJ` when it is homed elsewhere -/

/-- The handler's `REPLY_OBJ` word, when the handler is homed on another core: the one word outside
`IoRS s` a declining run may read (`s`, `a` the entry). -/
def VmRep {A : Type} (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (s : S) (a : A)
    (b : U64) : Prop :=
  ∃ s1 a1 sl ptr badge x y g gr, sched.update_timestamp st ar s a = ok (s1, a1) ∧
    obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl ∧
    obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x y g gr) ∧ L.epState s1 ptr = obj.EP_RECV ∧
    L.mem s1 (affA (L.mem s1 (epHeadA ptr))) ≠ L.cpu s1 ∧ b = replyA (L.mem s1 (epHeadA ptr))

theorem VmRep.aligned {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s) (hlkE : VmGlue st ar Locks s) {a : A} {b : U64}
    (h : VmRep st ar s a b) : Aligned b := by
  obtain ⟨s1, a1, sl, ptr, badge, x, y, g, gr, eu, hsl, hcap, hst, -, rfl⟩ := h
  have D := vm_dfOf hA P hlkE eu
  have hdT := (D.ep sl ptr badge x y g gr hsl hcap).2.2 hst
  exact field_aligned (P.base.tp _ hdT) (by simp) (by simp)

end

end Fl4Proofs.P2.PathObl

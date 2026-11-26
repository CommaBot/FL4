/-
# P2 (line stpost, generation 12): `dec_alt` and `read_aligned` of the frame-cap invocation path (`InvDecW`, `InvRaW`)

`syscall.handle_invocation_local` declines (returns `false`) before its prefix (domains, trap flag, syscall number,
label) or after it (`sched.action`, `yield_to`, `sporadic.sufficient`, `schedulable_here`, `Plan.still_holds`):
the prefix is the I/O port path's (`FAULT_IP`, `CUR_TIME`, `CONSUMED`), the checks are the I/O port path's minus
`extra_caps` / `invocation_ok`, plus the plan re-check `still_holds`. So the I/O port's `dec_alt` (P2/AccessIoDecl,
AccessIoDec2, AccessIoDecA) carries over, with `still_holds` answered alike at the alternative state because the
words it reads (`SeenW p`) are in the read set.

* `invTail`, `handle_invocation_local_eq` (the path after the syscall-number check);
* `invTail_dec_m`, `handle_inv_dec_m`: a run declining on `st` declines the same way on a store `m` reading as
  `st` and writing the prefix words as `st` (`RdEq`, `PreOK`; `still_holds` is read-only);
* `invTail_inv`, `handle_inv_inv`, `invTail_true`: an accepted run's checks, and acceptance from the checks;
* `still_holds_st`: `still_holds` answers alike at two states agreeing on the seen words;
* `inv_alt_not_acc`: a run that declines at `s` is accepted at no alternative `s'`;
* **`inv_dec_alt`** (`PathObl.dec_alt` for one entry) and **`invDecW_of`** (the named premise `InvDecW` of
  `inv_localPath`, discharged);
* `invTail.guardD`, **`inv_ra_dec`** (`PathSide.read_aligned` of a declining entry: the I/O port's `io_alt_midD`
  gives the words the checks read, `still_holds_guard` the seen words) and **`invRaW_of`** (`InvRaW` discharged);
* `InvSeenRS` [J], **`inv_pathsKD`** / **`inv_pathsKD_startAt`**: `inv_pathsK` with `hdec` and `hra` replaced by
  `hSeen : InvSeenRS` (`RegionOK` / `IoLayA` from `SlJAt`).

Premises of `invDecW_of`: `hA` (P0 Arch totality), and at each `Pre` state [J] `hK : RegionOK K`,
[J] `hLA : IoLayA K`, `hPE` (`Pre` gives `IoPre`) and [J] **`hSeen`**: at a `Pre` state every word `still_holds` reads is in `IoRS` (the plan's seen
words are words of its locked slots: cap words of a Frame slot and CDT links, `lock <slot>` by `OwnMap` rule 2,
held by the glue). `invRaW_of`: `hA`, `hPE`, `hSeen`. No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvLP
import Fl4Proofs.P2.AccessIoRa
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField)

section tail
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {m : machine.Store S}

/-- The frame-cap invocation local path after the syscall-number check. -/
def invTail {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : obj.Tcb)
    (info : msginfo.MessageInfo) (p : localinv.Plan) : Result (Bool × S × A) := do
  let b ← localinv.is_local_label info.label
  if b
  then
    let next ← obj.Tcb.reg m t s layout.reg.NEXT_IP
    let i2 ← lift (core.num.U64.wrapping_sub next 2#u64)
    let s1 ← obj.Tcb.set_reg m t s layout.reg.FAULT_IP i2
    let (s2, a1) ← sched.update_timestamp m ar s1 a
    let csc ← sched.cur_sc m s2
    let i3 ← sched.action m s2
    if i3 != sched.ACTION_RESUME_CURRENT
    then ok (false, s2, a1)
    else
      let i4 ← obj.Tcb.yield_to m t s2
      if i4 != 0#u64
      then ok (false, s2, a1)
      else
        let i5 ← sched.consumed m s2
        let b1 ← sporadic.sufficient m ar s2 a1 csc i5
        if b1
        then
          let b2 ← fastpath.schedulable_here m s2 t
          if b2
          then
            let b3 ← localinv.Plan.still_holds m p s2
            if b3
            then
              let buf ← msg.lookup_ipc_buffer m s2 false t
              let length ←
                if info.length > msg.N_MSG_REGISTERS
                then
                  if buf = 0#u64
                  then ok msg.N_MSG_REGISTERS
                  else ok info.length
                else ok info.length
              let cap ← obj.Slot.cap m p.slot s2
              let (r, s3, a2) ←
                syscall.decode_invocation m ar s2 a1 info.label length p.slot cap true true true false buf p.extra
              let (s4, a3, r1) ←
                match r with
                | core.result.Result.Ok _ =>
                  do
                  let i6 ← obj.Tcb.state m t s3
                  let t1 ←
                    if i6 = sched.TS_RESTART
                    then
                      do
                      let s5 ← msg.reply_success_empty m s3 t
                      sched.set_thread_state m s5 t sched.TS_RUNNING
                    else ok s3
                  ok (t1, a2, core.result.Result.Ok ())
                | core.result.Result.Err e =>
                  do
                  let (t1, r2) ←
                    match e with
                    | error.Exc.Fault _ => ok (s3, core.result.Result.Ok ())
                    | error.Exc.Lookup _ => ok (s3, core.result.Result.Ok ())
                    | error.Exc.Sys e1 =>
                      do
                      let s5 ← syscall.reply_error m s3 t e1
                      ok (s5, core.result.Result.Ok ())
                    | error.Exc.Preempted => ok (s3, r)
                  ok (t1, a2, r2)
              let (_, s5, a4) ← syscall.after_invocation m ar s4 a3 r1
              let (s6, a5) ← syscall.finish m ar s5 a4
              ok (true, s6, a5)
            else ok (false, s2, a1)
          else ok (false, s2, a1)
        else ok (false, s2, a1)
  else ok (false, s, a)

theorem handle_invocation_local_eq {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (number : I64) (p : localinv.Plan) :
    syscall.handle_invocation_local m ar s a number p = (do
      let t ← sched.cur_thread m s
      let info ← msg.msg_info m s t
      if layout.NUM_DOMAINS != 1#u64
      then ok (false, s, a)
      else
        let i ← obj.Tcb.flags m t s
        let i1 ← lift (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS)
        if i1 != 0#u64
        then ok (false, s, a)
        else
          if number != fl4_abi.syscall.SysCall
          then ok (false, s, a)
          else invTail m ar s a t info p) := rfl

set_option maxHeartbeats 1000000 in
/-- **A declined tail on `m`.** -/
theorem invTail_dec_m (h : RdEq st m) {A : Type} {ar : machine.Arch A} {x : S} {a : A} {t : U64}
    {info : msginfo.MessageInfo} {p : localinv.Plan} {r : Bool × S × A} (hP : PreOK st m x t)
    (ht : invTail st ar x a t info p = ok r) (hn : r.1 ≠ true) : invTail m ar x a t info p = ok r := by
  unfold invTail at ht ⊢
  revert ht
  refine tr_bind_same (fun b _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [h.ro x (fun n => obj.Tcb.reg n t x layout.reg.NEXT_IP) (fun _ => rfl)]
  refine tr_bind_same (fun nx _ => ?_)
  simp only [lift, bind_ok]
  have es : obj.Tcb.set_reg m t x layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) =
      obj.Tcb.set_reg st t x layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) := by
    unfold obj.Tcb.set_reg
    simp only [lift, bind_ok]
    exact hP x _ _ (Or.inl rfl) rfl rfl
  rw [es]
  refine tr_bind_same (fun s1 es1 => ?_)
  rw [set_reg_ok'] at es1
  have k1 : L.ksb s1 = L.ksb x := by rw [← ok_inj_ff es1, L.ksb_wr]
  have c1 : L.cpu s1 = L.cpu x := by rw [← ok_inj_ff es1, L.cpu_wr]
  rw [upd_m h hP k1 c1]
  refine tr_bind_same (fun q _ => ?_)
  obtain ⟨s2, a1⟩ := q
  simp only [uncurry_apply_pair]
  rw [h.ro s2 (fun n => sched.cur_sc n s2) (fun _ => rfl)]
  refine tr_bind_same (fun csc _ => ?_)
  rw [h.ro s2 (fun n => sched.action n s2) (fun _ => rfl)]
  refine tr_bind_same (fun i3 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [h.ro s2 (fun n => obj.Tcb.yield_to n t s2) (fun _ => rfl)]
  refine tr_bind_same (fun i4 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [h.ro s2 (fun n => sched.consumed n s2) (fun _ => rfl)]
  refine tr_bind_same (fun i5 _ => ?_)
  rw [h.ro s2 (fun n => sporadic.sufficient n ar s2 a1 csc i5) (fun _ => rfl)]
  refine tr_bind_same (fun b1 _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [h.ro s2 (fun n => fastpath.schedulable_here n s2 t) (fun _ => rfl)]
  refine tr_bind_same (fun b2 _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [h.ro s2 (fun n => localinv.Plan.still_holds n p s2) (fun _ => rfl)]
  refine tr_bind_same (fun b3 _ => ?_)
  refine tr_ite (fun _ hk => ?_) (fun _ h => h)
  exfalso
  obtain ⟨_, -, hk⟩ := bind_eq_ok hk
  obtain ⟨_, -, hk⟩ := bind_eq_ok hk
  obtain ⟨_, -, hk⟩ := bind_eq_ok hk
  obtain ⟨_, -, hk⟩ := bind_eq_ok hk
  obtain ⟨_, -, hk⟩ := bind_eq_ok hk
  obtain ⟨_, -, hk⟩ := bind_eq_ok hk
  obtain ⟨_, -, hk⟩ := bind_eq_ok hk
  exact hn (by rw [← ok_inj_ff hk])

/-- **A declined frame-cap invocation run on `m`.** -/
theorem handle_inv_dec_m (h : RdEq st m) {A : Type} {ar : machine.Arch A} {x : S} {a : A} {number : I64}
    {p : localinv.Plan} {r : Bool × S × A} (hP : PreOK st m x (L.curW x))
    (hr : syscall.handle_invocation_local st ar x a number p = ok r) (hn : r.1 ≠ true) :
    syscall.handle_invocation_local m ar x a number p = ok r := by
  rw [handle_invocation_local_eq] at hr ⊢
  revert hr
  rw [h.ro x (fun n => sched.cur_thread n x) (fun _ => rfl), cur_thread_ok]
  simp only [bind_ok]
  rw [h.ro x (fun n => msg.msg_info n x (L.curW x)) (fun _ => rfl)]
  refine tr_bind_same (fun info _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [h.ro x (fun n => obj.Tcb.flags n (L.curW x) x) (fun _ => rfl)]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  exact tr_ite (fun _ h => h) (fun _ ht => invTail_dec_m h hP ht hn)

set_option maxHeartbeats 1000000 in
/-- **An accepted tail's checks.** -/
theorem invTail_inv {A : Type} {ar : machine.Arch A} {s s' : S} {a a' : A} {t : U64} {info : msginfo.MessageInfo}
    {p : localinv.Plan} (h : invTail st ar s a t info p = ok (true, s', a')) :
    ∃ nx s1 s2 a1, localinv.is_local_label info.label = ok true ∧
      obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx ∧
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 ∧
      sched.update_timestamp st ar s1 a = ok (s2, a1) ∧
      sched.action st s2 = ok sched.ACTION_RESUME_CURRENT ∧ obj.Tcb.yield_to st t s2 = ok 0#u64 ∧
      sporadic.sufficient st ar s2 a1 (L.cscW s2) (L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED)) = ok true ∧
      fastpath.schedulable_here st s2 t = ok true ∧
      localinv.Plan.still_holds st p s2 = ok true := by
  unfold invTail at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok h
  cases b
  · rw [if_neg Bool.false_ne_true] at h; have e := ok_inj_ff h; simp at e
  rw [if_pos rfl] at h
  obtain ⟨nx, hnx, h⟩ := bind_eq_ok h
  simp only [lift, bind_ok] at h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2, a1⟩, hu, h⟩ := bind_eq_ok h
  simp only [uncurry_apply_pair] at h
  rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2)] at h; simp only [bind_ok] at h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  by_cases c3 : (i3 != sched.ACTION_RESUME_CURRENT) = true
  · rw [if_pos c3] at h; have e := ok_inj_ff h; simp at e
  rw [if_neg c3] at h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  by_cases c4 : (i4 != 0#u64) = true
  · rw [if_pos c4] at h; have e := ok_inj_ff h; simp at e
  rw [if_neg c4] at h
  rw [io_consumed_ok s2] at h; simp only [bind_ok] at h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
  cases b1
  · rw [if_neg Bool.false_ne_true] at h; have e := ok_inj_ff h; simp at e
  rw [if_pos rfl] at h
  obtain ⟨b2, hb2, h⟩ := bind_eq_ok h
  cases b2
  · rw [if_neg Bool.false_ne_true] at h; have e := ok_inj_ff h; simp at e
  rw [if_pos rfl] at h
  obtain ⟨b3, hb3, h⟩ := bind_eq_ok h
  cases b3
  · rw [if_neg Bool.false_ne_true] at h; have e := ok_inj_ff h; simp at e
  simp only [bne_iff_ne, ne_eq, not_not] at c3 c4
  subst c3 c4
  exact ⟨nx, s1, s2, a1, hb, hnx, hs1, hu, hi3, hi4, hb1, hb2, hb3⟩

/-- An accepted run reaches the tail. -/
theorem handle_inv_inv {A : Type} {ar : machine.Arch A} {s s' : S} {a a' : A} {number : I64} {p : localinv.Plan}
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    ∃ info, msg.msg_info st s (L.curW s) = ok info ∧
      (L.mem s (core.num.U64.wrapping_add (L.curW s) 3456#u64) &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ∧
      number = fl4_abi.syscall.SysCall ∧
      invTail st ar s a (L.curW s) info p = ok (true, s', a') := by
  rw [handle_invocation_local_eq, cur_thread_ok] at h
  simp only [bind_ok] at h
  obtain ⟨info, hi, h⟩ := bind_eq_ok h
  by_cases c0 : (layout.NUM_DOMAINS != 1#u64) = true
  · rw [if_pos c0] at h; have e := ok_inj_ff h; simp at e
  rw [if_neg c0] at h
  rw [flags_ok s (L.curW s)] at h
  simp only [bind_ok, lift] at h
  by_cases c1 : (L.mem s (core.num.U64.wrapping_add (L.curW s) 3456#u64) &&&
      fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; have e := ok_inj_ff h; simp at e
  rw [if_neg c1] at h
  simp only [bne_iff_ne, ne_eq, not_not] at c1
  by_cases c2 : (number != fl4_abi.syscall.SysCall) = true
  · rw [if_pos c2] at h; have e := ok_inj_ff h; simp at e
  rw [if_neg c2] at h
  simp only [bne_iff_ne, ne_eq, not_not] at c2
  exact ⟨info, hi, c1, c2, h⟩

set_option maxHeartbeats 1000000 in
/-- **All checks passing, a run that returns is accepted.** -/
theorem invTail_true {A : Type} {ar : machine.Arch A} {s s1 s2 : S} {a a1 : A} {t nx : U64}
    {info : msginfo.MessageInfo} {p : localinv.Plan} {r : Bool × S × A}
    (hb : localinv.is_local_label info.label = ok true)
    (hnx : obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx)
    (hs1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1)
    (hu : sched.update_timestamp st ar s1 a = ok (s2, a1))
    (hac : sched.action st s2 = ok sched.ACTION_RESUME_CURRENT) (hy : obj.Tcb.yield_to st t s2 = ok 0#u64)
    (hsf : sporadic.sufficient st ar s2 a1 (L.cscW s2) (L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED)) = ok true)
    (hh : fastpath.schedulable_here st s2 t = ok true)
    (hsh : localinv.Plan.still_holds st p s2 = ok true)
    (h : invTail st ar s a t info p = ok r) : r.1 = true := by
  have c0 : ∀ v : U64, ¬ ((v != v) = true) := fun v => by simp
  unfold invTail at h
  rw [hb] at h; simp only [bind_ok] at h
  simp only [if_true, ↓reduceIte] at h
  rw [hnx] at h; simp only [bind_ok, lift] at h
  rw [hs1] at h; simp only [bind_ok] at h
  rw [hu] at h; simp only [bind_ok, uncurry_apply_pair] at h
  rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2)] at h; simp only [bind_ok] at h
  rw [hac] at h; simp only [bind_ok] at h
  rw [if_neg (c0 _), hy] at h; simp only [bind_ok] at h
  rw [if_neg (c0 _)] at h
  rw [io_consumed_ok] at h; simp only [bind_ok] at h
  unfold LawfulStore.cscW at hsf
  rw [hsf] at h; simp only [bind_ok] at h
  simp only [if_true, ↓reduceIte] at h
  rw [hh] at h; simp only [bind_ok] at h
  simp only [if_true, ↓reduceIte] at h
  rw [hsh] at h; simp only [bind_ok] at h
  simp only [if_true, ↓reduceIte] at h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]

/-- **`still_holds` answers alike at two states agreeing on the seen words.** -/
theorem still_holds_st (p : localinv.Plan) {x y : S} (h : ∀ w, SeenW p w → L.mem x w = L.mem y w) :
    localinv.Plan.still_holds st p x = localinv.Plan.still_holds st p y := by
  have hb : (fun i1 => localinv.Plan.still_holds_loop.body st p x i1) =
      (fun i1 => localinv.Plan.still_holds_loop.body st p y i1) := by
    funext i
    unfold localinv.Plan.still_holds_loop.body
    by_cases h1 : i < p.nseen
    · by_cases h2 : i < localinv.MAX_LOCKS
      · have hM : localinv.MAX_LOCKS.val = 4 := by unfold localinv.MAX_LOCKS; rfl
        have h2v : i.val < localinv.MAX_LOCKS.val := h2
        have hl : i.val < p.seen.val.length := by rw [p.seen.property]; simp only [hM] at h2v; simpa using h2v
        obtain ⟨⟨a0, v0⟩, hq, -⟩ := spec_ex_fd (Aeneas.Std.Array.index_usize_spec p.seen i hl)
        simp only [h1, h2, if_true, hq, bind_ok, bind_tc_ok]
        try simp only [uncurry_apply_pair]
        try dsimp only
        rw [L.read_eq, L.read_eq, h a0 ⟨i, (a0, v0), h1, h2, hq, rfl⟩]
      · simp only [h1, h2, if_true, if_false]
    · simp only [h1, if_false]
  unfold localinv.Plan.still_holds localinv.Plan.still_holds_loop
  rw [hb]

end tail

section alt
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s' : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}

set_option maxHeartbeats 1000000 in
/-- **A frame-cap invocation run that declines at `s` is accepted at no alternative state** (`hSeen` [J]: the
words `still_holds` reads are in the read set). -/
theorem inv_alt_not_acc {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64}
    {p : localinv.Plan} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {r : Bool × S × A} {z : S} {b : A} (h : syscall.handle_invocation_local st ar s a number p = ok r)
    (hr : r.1 ≠ true) (h' : syscall.handle_invocation_local st ar s' a number p = ok (true, z, b)) : False := by
  have hRa : ∀ b, IoRS (st := st) K Locks s b → Aligned b := fun _ h => h.1
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  obtain ⟨info, emi', hfl', hnum, ht'⟩ := handle_inv_inv h'
  rw [hcur] at emi' hfl' ht'
  have eflg : L.mem s' (core.num.U64.wrapping_add (L.curW s) 3456#u64) =
      L.mem s (core.num.U64.wrapping_add (L.curW s) 3456#u64) :=
    G.m _ (P.home (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  rw [eflg] at hfl'
  have rg : ∀ q : U64, q.val < 384 → L.mem s' (regA (L.curW s) q) = L.mem s (regA (L.curW s) q) := fun q hq =>
    G.m _ (P.reg hq).1
  have emi : msg.msg_info st s (L.curW s) = ok info := by
    unfold msg.msg_info at emi' ⊢
    rw [reg_ok] at emi' ⊢
    rw [rg _ (by simp [layout.reg.MSG_INFO])] at emi'
    exact emi'
  -- the run at `s` reaches the tail
  have ht : invTail st ar s a (L.curW s) info p = ok r := by
    rw [handle_invocation_local_eq, cur_thread_ok] at h
    simp only [bind_ok] at h
    rw [emi] at h; simp only [bind_ok] at h
    rw [if_neg (by simp [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]), flags_ok] at h
    simp only [bind_ok, lift] at h
    rw [hfl', if_neg (by simp)] at h
    rw [if_neg (by rw [hnum]; simp)] at h
    exact h
  obtain ⟨nx, s1', s2', a1, hb, hnx', hs1', hu', hact', hy', hsuf', hh', hsh'⟩ := invTail_inv ht'
  -- the prefix at `s`
  have ev : nx = L.mem s (regA (L.curW s) layout.reg.NEXT_IP) := by
    rw [reg_ok] at hnx'; rw [← ok_inj_ff hnx']; exact rg _ (by simp [layout.reg.NEXT_IP])
  have hnx : obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx := by rw [reg_ok, ev]
  have hfr : (layout.reg.FAULT_IP).val < 384 := by simp [layout.reg.FAULT_IP]
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := hRa _ (P.reg (Locks := Locks) hfr).1
  have aT : Aligned (ctA (L := L) s) := nodeAt_aligned P.np (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have aN : Aligned (cnA (L := L) s) := nodeAt_aligned P.np (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have hs1 : obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) =
      ok (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) := set_reg_ok' _ _ _ _
  rw [set_reg_ok'] at hs1'
  have es1' := (ok_inj_ff hs1').symm
  have G1 := G.wr hRa (a := regA (L.curW s) layout.reg.FAULT_IP) (v := core.num.U64.wrapping_sub nx 2#u64) aF
  rw [← es1'] at G1
  obtain ⟨now, hnow, es2'⟩ := upd_eq hu'
  have hu := upd_fwd (st := st) (s := L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) hnow
  have eT : ctA (L := L) s1' = ctA (L := L) s := by
    show L.nodeAt _ _ _ = L.nodeAt _ _ _
    rw [es1', nd_wr, G.node]
  have eN : cnA (L := L) s1' = cnA (L := L) s := by
    show L.nodeAt _ _ _ = L.nodeAt _ _ _
    rw [es1', nd_wr, G.node]
  have eT1 : ctA (L := L) (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) =
      ctA (L := L) s := nd_wr _ _ _ _
  have eN1 : cnA (L := L) (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) =
      cnA (L := L) s := nd_wr _ _ _ _
  rw [eT, eN] at es2'
  rw [eT1, eN1] at hu
  have rT := (P.nd (Locks := Locks) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
  have rN := (P.nd (Locks := Locks) layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
  have G2 := (G1.wr hRa (a := ctA (L := L) s) (v := now) aT)
  have e1 : L.mem s1' (ctA (L := L) s) = L.mem (L.wr s (regA (L.curW s) layout.reg.FAULT_IP)
      (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s) := G1.m _ rT
  have e2 := G2.m _ rN
  rw [e1, e2] at es2'
  have G3 := G2.wr hRa (a := cnA (L := L) s) (v := core.num.U64.wrapping_add (L.mem (L.wr (L.wr s
    (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s) now) (cnA (L := L) s))
    (core.num.U64.wrapping_sub now (L.mem (L.wr s (regA (L.curW s) layout.reg.FAULT_IP)
      (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s)))) aN
  rw [← es2'] at G3
  rw [es1'] at es2'
  obtain ⟨s2, hs2⟩ : ∃ s2, L.wr (L.wr (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64))
    (ctA (L := L) s) now) (cnA (L := L) s) (core.num.U64.wrapping_add (L.mem (L.wr (L.wr s
    (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s) now) (cnA (L := L) s))
    (core.num.U64.wrapping_sub now (L.mem (L.wr s (regA (L.curW s) layout.reg.FAULT_IP)
      (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s)))) = s2 := ⟨_, rfl⟩
  rw [hs2] at hu G3
  have w := prefix_writes ar hA P.tp P.np P.cT hs1 hu
  have Hf := here_facts hh'
  have rsc : IoRS (st := st) K Locks s (scA (L.curW s)) :=
    P.gate (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have e3 : L.mem s2 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (hRa _ rsc) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s :=
    (P.hcsc (by rw [← e3, ← G3.m _ rsc]; exact Hf.sc)).symm
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  have M2 := io_hmid' (a := a) ar hA hq.tcbs (hq.nodes _ hq.cur) hq.cur hq.curT
    (P.mid (Locks := Locks) (P.ioWr (Locks := Locks)) hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2) (hd hX.cur)
    (fun h0 => ⟨(bxi_rh P.bxi h0).1, hd (bxi_rh P.bxi h0).2.1⟩) info nx _ s2 a1 emi hnx hs1 hu
  -- the checks at `s2`
  have nA := (P.nd (Locks := Locks) layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
  have nS := (P.nd (Locks := Locks) layout.node.CUR_SC (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
  have nM := (P.nd (Locks := Locks) layout.node.TIMER_MIN (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1
  have nR := (P.nd (Locks := Locks) layout.node.RELEASE_HEAD (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).1
  have nd2 : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by rw [w.2.1, nodeAt_of_ksb w.1]
  have hact : sched.action st s2 = ok sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) _)] at hact' ⊢
    rw [← ok_inj_ff hact']
    unfold LawfulStore.actionW
    rw [G3.node, G3.m _ (by rw [nd2]; exact nA)]
  have hy : obj.Tcb.yield_to st (L.curW s) s2 = ok 0#u64 := by
    rw [eq_ok_of_spec (obj.Tcb.yield_to.spec (L := L) _ _)] at hy' ⊢
    rw [← ok_inj_ff hy']; exact congrArg ok (G3.m _ M2.yld).symm
  have hh : fastpath.schedulable_here st s2 (L.curW s) = ok true := by
    rw [← hh']
    exact (here_congr G3 (by show IoRS _ _ _ (L.nodeAt _ _ _); rw [nd2]; exact rT)
      (by show IoRS _ _ _ (L.nodeAt _ _ _); rw [nd2]; exact nM)
      (by show IoRS _ _ _ (L.nodeAt _ _ _); rw [nd2]; exact nR) M2.td M2.rs M2.dt M2.cd M2.af M2.dom M2.iok.1.sc
      M2.iok.1.inq).symm
  have hsf : sporadic.sufficient st ar s2 a1 (L.cscW s2) (L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED)) = ok true := by
    have ec : L.cscW s2' = L.cscW s2 := by
      unfold LawfulStore.cscW LawfulStore.nodeA
      rw [G3.node]; exact G3.m _ (by rw [nd2]; exact nS)
    have en : L.mem s2' (L.nodeAt s2' (L.cpu s2') layout.node.CONSUMED) =
        L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) := by
      rw [G3.node]; exact G3.m _ (by rw [nd2]; exact rN)
    rw [ec, en] at hsuf'
    rw [← hsuf']
    exact (suff_congr G3 a1 M2.rh).symm
  -- the plan re-check: its words are in the read set
  have hsh : localinv.Plan.still_holds st p s2 = ok true := by
    rw [← hsh']
    exact still_holds_st p (fun w hw => (G3.m w (hSeen w hw)).symm)
  exact hr (invTail_true hb hnx hs1 hu hact hy hsf hh hsh ht)

/-- **`PathObl.dec_alt`** for the frame-cap invocation path at one entry. -/
theorem inv_dec_alt {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K)
    {number : I64} {p : localinv.Plan} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ x, SeenW p x → IoRS (st := st) K Locks s x) {a : A} {r r' : Bool × S × A}
    (h : syscall.handle_invocation_local st ar s a number p = ok r) (hr : r.1 ≠ true)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    (h' : syscall.handle_invocation_local st ar s' a number p = ok r') :
    r'.1 ≠ true ∧
      syscall.handle_invocation_local (guard st (fun _ => True) (IoDS (st := st) s)) ar s' a number p = ok r' ∧
      syscall.handle_invocation_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s' a number p = ok r' := by
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
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
    exact inv_alt_not_acc hA P hSeen Al h hr h'
  refine ⟨hn, ?_, ?_⟩
  · refine handle_inv_dec_m ⟨fun _ _ => guard_read trivial, fun _ _ => guard_read_pair trivial trivial,
      fun _ => rfl, fun _ => rfl⟩ (fun y b v hb _ _ => guard_write (hpre b hb)) h' hn
  · have hR : RdEq st (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) :=
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
    have hW : PreOK st (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) s' (L.curW s') := by
      intro y b v hb _ _
      obtain ⟨ha, hs⟩ := IoDS.safe P (hpre b hb)
      rw [L.write_eq]
      exact mguard_write (L.write_eq y b v) (stepOK_safe (m0 := m0) hK hLA ha hs)
    exact handle_inv_dec_m hR hW h' hn

/-- (stpost gen 12) **The named premise `InvDecW` of `inv_localPath`, discharged**: from `hA`, and at every `Pre`
state [J] `hK` (`RegionOK K`), [J] `hLA` (`IoLayA K`), `hPE` (`IoPre`) and [J] `hSeen` (the words `still_holds`
reads are in `IoRS`). At `Pre := SlJAt K ∧ _`, `hK` / `hLA` are `SlJAt.regionOK` / `SlJAt.ioLayA`. -/
theorem invDecW_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {P : S → Prop} (hK : ∀ s, P s → RegionOK K) (hLA : ∀ s, P s → IoLayA K)
    (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x) :
    InvDecW st ar number p K Locks m0 P :=
  fun s a _ hE h hn _ _ Al h' => inv_dec_alt hA (hK s hE) (hLA s hE) (hPE s hE) (hSeen s hE) h hn Al h'

end alt

/-! ## `read_aligned` of declining entries (`InvRaW`) -/

section ra
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

/-- **A declining frame-cap invocation tail on the guarded store** (the I/O port's `ioTail.guardD` without the
CSpace walk; `still_holds` answers alike on `gS`, `hsh`). -/
theorem invTail.guardD {A : Type} (ar : machine.Arch A) {s : S} {a : A} {t : U64}
    {info : msginfo.MessageInfo} {p : localinv.Plan} {r : Bool × S × A}
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hnx : R (regA t layout.reg.NEXT_IP)) (hfi : W (regA t layout.reg.FAULT_IP))
    (hmid : ∀ nx s1 s2 a1, obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) →
      ∃ C sl, IoMidD (L := L) R s s2 t C sl)
    (hsh : ∀ x, localinv.Plan.still_holds gS p x = localinv.Plan.still_holds st p x)
    (hr : r.1 ≠ true)
    (h : invTail st ar s a t info p = ok r) :
    invTail gS ar s a t info p = ok r := by
  unfold invTail at h ⊢
  revert h
  refine tr_bind_same (fun b _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  refine tr_bind (fun x hx _ => by rw [obj.Tcb.reg.guard t s _ hnx]; exact hx) (fun nx enx => ?_)
  simp only [lift, bind_ok]
  refine tr_bind (fun x hx _ => by rw [obj.Tcb.set_reg.guard t s _ _ hfi]; exact hx) (fun s1 es1 => ?_)
  have e1 : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have k1 : L.ksb s1 = L.ksb s := by rw [e1, L.ksb_wr]
  have c1 : L.cpu s1 = L.cpu s := by rw [e1, LawfulStore.cpu_wr]
  refine tr_bind (fun x hx _ => by
      rw [sched.update_timestamp.guard ar s1 a (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2]; exact hx)
    (fun x eu => ?_)
  obtain ⟨s2, a1⟩ := x
  simp only [uncurry_apply_pair]
  obtain ⟨C, sl, M⟩ := hmid nx s1 s2 a1 enx es1 eu
  have nd2 := nd_at hNd M.k M.c
  have Mc := M.cur
  subst Mc
  rw [sched.cur_sc.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.action.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1]
  refine tr_bind_same (fun i3 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.yield_to.guard (gS := gS) (L.curW s2) s2 M.yld]
  refine tr_bind_same (fun i4 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [sched.consumed.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1]
  refine tr_bind_same (fun i5 _ => ?_)
  have ecsc' : csc = L.cscW s2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2)] at ecsc; exact (ok_inj_ff ecsc).symm
  subst ecsc'
  rw [sporadic.sufficient.guard (gS := gS) ar s2 a1 _ i5 M.rh]
  refine tr_bind_same (fun b1 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [fastpath.schedulable_here.guard (gS := gS) s2 (L.curW s2) (nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
    (nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1 (nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).1
    M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
  refine tr_bind_same (fun b2 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [hsh s2]
  refine tr_bind_same (fun b3 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => ?_) (fun _ h => h)
  -- all checks passed: a run that returns is accepted
  exfalso
  apply hr
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]

end ra

section ra2
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s' : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}

/-- **`PathSide.read_aligned` from a declining entry** of the frame-cap invocation path: a run that declines at
`s` runs at every alternative `s'` on the store guarded to aligned reads as on `st` (`hSeen` [J]). -/
theorem inv_ra_dec {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {r0 r : Bool × S × A} (h0 : syscall.handle_invocation_local st ar s a number p = ok r0)
    (hr0 : r0.1 ≠ true) (h : syscall.handle_invocation_local st ar s' a number p = ok r) :
    syscall.handle_invocation_local (guard st (fun b => Aligned b) (fun _ => True)) ar s' a number p = ok r := by
  have hr : r.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r
    intro hb
    change b = true at hb
    subst hb
    exact inv_alt_not_acc hA P hSeen Al h0 hr0 h
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      Aligned (L.nodeAt s' (L.cpu s') o) ∧ True := fun o h1 h2 =>
    ⟨by rw [G.node]; exact nodeAt_aligned P.np h1 h2, trivial⟩
  rw [handle_invocation_local_eq] at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := guard st (fun b => Aligned b) (fun _ => True)) s'
    (hNd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [hcur, msg.msg_info.guard (gS := guard st (fun b => Aligned b) (fun _ => True)) s' _
    (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1.1]
  refine tr_bind_same (fun info _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard (gS := guard st (fun b => Aligned b) (fun _ => True)) (L.curW s) s'
    (field_aligned P.tA (K := 3456#u64) (by decide) (by decide))]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ ht => ?_)
  exact invTail.guardD (gS := guard st (fun b => Aligned b) (fun _ => True)) ar hNd
    (P.reg (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1.1 trivial
    (fun nx s1 s2 a1 _ e1 e2 => io_alt_midD (nx := nx) hA P Al e1 e2)
    (fun x => still_holds_guard p x (fun w hw => (hSeen w hw).1)) hr ht

/-- (stpost gen 12) **The named premise `InvRaW` of `inv_localPath`, discharged**: from `hA`, and at every `Pre`
state `hPE` (`IoPre`) and [J] `hSeen`. -/
theorem invRaW_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x) :
    InvRaW st ar number p K Locks m0 P :=
  fun s _ _ _ _ hE Al h0 hr0 h => inv_ra_dec hA (hPE s hE) (hSeen s hE) Al h0 hr0 h

end ra2

/-! ## The path with `dec_alt` / `read_aligned` discharged -/

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- [J] **The plan's seen words are readable** at the path's `Pre` (layout `K`, memory `m`): every word
`still_holds` reads is in `IoRS`. (They are the cap words and CDT links of the plan's locked slots: rule 2 of
`OwnMap.own` gives them to `lock <slot>`, or to the gate for a cap word of a non-Null/Frame slot.) -/
def InvSeenRS (st : machine.Store S) [L : LawfulStore st] (Locks : S → U64 → Prop) (p : localinv.Plan)
    (Q : KLayout → (U64 → U64) → S → Prop) : Prop :=
  ∀ K m s, SlJAt (L := L) K s → Q K m s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x

/-- (stpost gen 12) **`inv_pathsK` with `dec_alt` and `read_aligned` discharged** (`invDecW_of`, `invRaW_of`):
the premises `hdec` [W] and `hra` [W] are replaced by `hSeen : InvSeenRS` [J]; `RegionOK K` and
`IoLayA K` come from `SlJAt K` (`SlJAt.regionOK`, `SlJAt.ioLayA`).
Other premises as `inv_pathsK`. -/
noncomputable def inv_pathsKD (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hacc : ∀ K m, InvAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hSeen : InvSeenRS st Locks p Q)
    (hmv : ∀ K m, InvMoveW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∀ K m, ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (fun s => SlJAt (L := L) K s ∧ Q K m s) (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m)
        (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ Q K m s)) :
    E2E.Paths Unit :=
  inv_pathsK ar hA number p hm Q hPE hacc
    (fun K m => invDecW_of hA (fun _ h => h.1.regionOK) (fun _ h => h.1.ioLayA)
      (fun s h => hPE K m s h.1 h.2) (fun s h => hSeen K m s h.1 h.2)) hmv
    (fun K m => invRaW_of hA (fun s h => hPE K m s h.1 h.2) (fun s h => hSeen K m s h.1 h.2)) huf hpz

/-- (stpost gen 12) **`StartAt` of `inv_pathsKD` at a chain state** (as `inv_pathsK_startAt`). -/
theorem inv_pathsKD_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hacc : ∀ K m, InvAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hSeen : InvSeenRS st Locks p Q)
    (hmv : ∀ K m, InvMoveW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∀ K m, ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (fun s => SlJAt (L := L) K s ∧ Q K m s) (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m)
        (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {A3 : Type} {Rc : S → A3 → Fl4Spec.State Unit → Prop}
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), Rc σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : Rc σ a3 τ) (a : A) (hq : Q K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (inv_pathsKD ar hA number p hm Q hPE hacc hSeen hmv huf hpz () K m hK hU) c hs μ
      ((inv_pathsKD ar hA number p hm Q hPE hacc hSeen hmv huf hpz () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨h7 σ a3 τ hR, hq⟩, hc, hl, hμ, rfl⟩

end paths

end Fl4Proofs.P2.PathObl

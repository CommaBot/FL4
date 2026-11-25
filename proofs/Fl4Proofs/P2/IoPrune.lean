/-
# P2: the I/O port body pruned to its I/O port arm (line hpzf)

`IsProg (ioBody S number) p ∧ NoZero p` is false (`handoff/hpz.md`): on an arbitrary store
`handle_invocation`'s re-read of `CUR_THREAD` after the prefix writes can name another thread, whose
CSpace holds any cap, so `decode_invocation` reaches every arm (`zero`, `clear_free`, `vcpu_sync`).
The bridge needs the program premise only on stores narrowing the path's lawful store and from the
entry states and their alternatives (`PathBridge`, `IsProgOn`). There the re-read agrees, and the body is
`ioBodyP`, the same body with `decode_invocation` cut to its I/O port arm:

* `decIo` / `hinvIo` / `ioTailP` / `ioBodyP`: the extracted text of `decode_invocation` /
  `handle_invocation` / `ioTail` (`AccessIoPath`) / `handle_ioport_local` with the one call replaced
  (every non-I/O-port cap is `fail`); generic in the Store and Arch instances, so a tree of `ioBodyP` is
  a tree of a body with no `zero` / `clear_free` / `vcpu_sync` / `vcpu_release` in its call closure
  (checked by script over `Funs.lean`: 402 functions, of which 385 are in the closure of the five other
  local paths and 17 are the I/O port path's own);
* `hinv_eq`: on any store, `handle_invocation` is `hinvIo` when the re-read thread is `t` and the cap
  `t`'s lookup finds is an I/O port cap; `ioTail_eq`: `ioTail` is `ioTailP` when, after the prefix's
  writes, the re-read thread is the entry's (a passing `invocation_ok` at the same state and thread gives
  the cap, `inv_true_m`: two runs of the same `Result` term on the same store and state agree);
* `Nar` transfers (`cur_thread_nar`, `set_reg_nar`, `update_timestamp_nar`): on a store narrowing `st`
  these steps answer as on `st` or fail;
* `io_prune`: on every store narrowing `st`, from every entry state (`IoPre`) and every alternative of
  one, `handle_ioport_local` is `ioBodyP` (the prefix writes `FAULT_IP`, `CUR_TIME`, `CONSUMED`, none of
  them `CUR_THREAD`: `prefix_writes`, `pre_node`; at an alternative, `CUR_THREAD` is in `IoRS`);
* `io_isProgOn`: hence `IsProg (ioBodyP S number) p` gives the relativised premise of `E2E.LocalPath`.

Premises: `hA` (Arch totality), `hPE` (`Pre` gives `IoPre`). None new.
-/
import Fl4Proofs.P2.AccessIoMv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK)

/-! ## The pruned body -/

section defs
variable {S : Type}

/-- `decode_invocation` with its I/O port arm only (`decode_inv_ioport_eq`); every other cap fails. -/
def decIo {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (lbl length : U64)
    (_slot : obj.Slot) (cap : capability.Cap) (_block call _cd _fp : Bool) (buf : U64)
    (_extra : Array obj.Slot 3#usize) : Result ((core.result.Result Unit error.Exc) × S × A) :=
  match cap with
  | .IoPort first last x =>
    Std.bind (sched.cur_thread m s) (fun _ => ioport.decode m ar s a lbl length (.IoPort first last x) call buf)
  | _ => fail .panic

/-- `syscall.handle_invocation`, `decode_invocation` replaced by `decIo` (text otherwise as extracted). -/
def hinvIo {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (is_call : Bool)
    (blocking : Bool) (can_donate : Bool) (first_phase : Bool) (cptr : U64) :
    Result ((core.result.Result Unit error.Exc) × S × A) := do
  let t ← sched.cur_thread m s
  let info ← msg.msg_info m s t
  let r ← cspace.lookup_slot m s t cptr
  match r with
  | core.result.Result.Ok r1 =>
    let cap ← obj.Slot.cap m r1.slot s
    let buf ← msg.lookup_ipc_buffer m s false t
    let r2 ← ipc.lookup_extra_caps m s t buf info
    match r2 with
    | core.result.Result.Ok e =>
      let length ←
        if info.length > msg.N_MSG_REGISTERS
        then if buf = 0#u64
             then ok msg.N_MSG_REGISTERS
             else ok info.length
        else ok info.length
      let (r3, s1, a1) ←
        decIo m ar s a info.label length r1.slot cap blocking is_call can_donate first_phase buf e
      match r3 with
      | core.result.Result.Ok _ =>
        let i ← obj.Tcb.state m t s1
        if i = sched.TS_RESTART
        then
          let s2 ←
            if is_call
            then msg.reply_success_empty m s1 t
            else ok s1
          let s3 ← sched.set_thread_state m s2 t sched.TS_RUNNING
          ok (core.result.Result.Ok (), s3, a1)
        else ok (core.result.Result.Ok (), s1, a1)
      | core.result.Result.Err e1 =>
        match e1 with
        | error.Exc.Fault _ => ok (core.result.Result.Ok (), s1, a1)
        | error.Exc.Lookup _ => ok (core.result.Result.Ok (), s1, a1)
        | error.Exc.Sys e2 =>
          if is_call
          then
            let s2 ← syscall.reply_error m s1 t e2
            ok (core.result.Result.Ok (), s2, a1)
          else ok (core.result.Result.Ok (), s1, a1)
        | error.Exc.Preempted => ok (r3, s1, a1)
    | core.result.Result.Err f =>
      if blocking
      then
        let (s1, a1) ← faults.handle_fault m ar s a t f
        ok (core.result.Result.Ok (), s1, a1)
      else ok (core.result.Result.Ok (), s, a)
  | core.result.Result.Err lf =>
    if blocking
    then
      let (s1, a1) ← faults.handle_fault m ar s a t (error.Fault.Cap cptr false lf)
      ok (core.result.Result.Ok (), s1, a1)
    else ok (core.result.Result.Ok (), s, a)

/-- `ioTail` (`AccessIoPath`), `handle_invocation` replaced by `hinvIo`. -/
def ioTailP {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : obj.Tcb)
    (info : msginfo.MessageInfo) (number : I64) : Result (Bool × S × A) := do
  let b ← ioport.is_port_label info.label
  if b
  then
    let next ← obj.Tcb.reg m t s layout.reg.NEXT_IP
    let i2 ← lift (core.num.U64.wrapping_sub next 2#u64)
    let s1 ← obj.Tcb.set_reg m t s layout.reg.FAULT_IP i2
    let (s2, a1) ← sched.update_timestamp m ar s1 a
    let cptr ← obj.Tcb.reg m t s2 layout.reg.CAP
    let csc ← sched.cur_sc m s2
    let i3 ← sched.action m s2
    if i3 != sched.ACTION_RESUME_CURRENT
    then ok (false, s2, a1)
    else
      let i4 ← obj.Tcb.yield_to m t s2
      if i4 != 0#u64
      then ok (false, s2, a1)
      else
        if info.extra_caps != 0#u64
        then ok (false, s2, a1)
        else
          let b1 ← ioport.invocation_ok m s2 t cptr info
          if b1
          then
            let i5 ← sched.consumed m s2
            let b2 ← sporadic.sufficient m ar s2 a1 csc i5
            if b2
            then
              let b3 ← fastpath.schedulable_here m s2 t
              if b3
              then
                let (r, s3, a2) ←
                  hinvIo m ar s2 a1 (number = fl4_abi.syscall.SysCall) true
                    (number = fl4_abi.syscall.SysCall) false cptr
                let (_, s4, a3) ← syscall.after_invocation m ar s3 a2 r
                let (s5, a4) ← syscall.finish m ar s4 a3
                ok (true, s5, a4)
              else ok (false, s2, a1)
            else ok (false, s2, a1)
          else ok (false, s2, a1)
  else ok (false, s, a)

/-- **The pruned I/O port body** (`handle_ioport_local_eq` with `ioTailP`), generic in the Arch instance
as `E2E.LocalPath.F`. -/
def ioBodyP (S : Type) (number : I64) : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A →
    Result (Bool × S × A) :=
  fun ar m s a => do
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
        then
          if number != fl4_abi.syscall.SysSend
          then ok (false, s, a)
          else ioTailP m ar s a t info number
        else ioTailP m ar s a t info number

end defs

/-! ## Equal where the cap is an I/O port cap -/

section eqs
variable {S : Type}

/-- `inv_true` (`AccessIoInv`) on any store: a passing `invocation_ok` found an I/O port cap. -/
theorem inv_true_m {m : machine.Store S} {s : S} {t cptr : U64} {info : msginfo.MessageInfo}
    (h : ioport.invocation_ok m s t cptr info = ok true) :
    ∃ r1 f l x, cspace.lookup_slot m s t cptr = ok (.Ok r1) ∧ obj.Slot.cap m r1.slot s = ok (.IoPort f l x) := by
  unfold ioport.invocation_ok at h
  obtain ⟨size, -, h⟩ := bind_eq_ok h
  by_cases hz : size = 0#u64
  · rw [if_pos hz] at h; cases ok_inj_ff h
  rw [if_neg hz] at h
  obtain ⟨res, hres, h⟩ := bind_eq_ok h
  cases res with
  | Err e => cases ok_inj_ff h
  | Ok r1 =>
    dsimp only at h
    split at h
    · cases ok_inj_ff h
    obtain ⟨c, hc, h⟩ := bind_eq_ok h
    cases c <;> try cases ok_inj_ff h
    rename_i f l x
    exact ⟨r1, f, l, x, hres, hc⟩

/-- **`handle_invocation` is `hinvIo`** when the re-read thread is `t` and `t`'s lookup finds an I/O port
cap (on any store). -/
theorem hinv_eq {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (call blk cd fp : Bool) (cptr t : U64)
    (hct : ∀ t', sched.cur_thread m s = ok t' → t' = t)
    (hio : ∀ r1, cspace.lookup_slot m s t cptr = ok (.Ok r1) → ∀ c, obj.Slot.cap m r1.slot s = ok c →
      ∃ f l x, c = .IoPort f l x) :
    syscall.handle_invocation m ar s a call blk cd fp cptr = hinvIo m ar s a call blk cd fp cptr := by
  unfold syscall.handle_invocation hinvIo
  refine bind_guard_congr rfl fun t' ht' => ?_
  obtain rfl := hct t' ht'
  refine bind_guard_congr rfl fun info _ => ?_
  refine bind_guard_congr rfl fun r hr => ?_
  rcases r with r1 | lf
  · refine bind_guard_congr rfl fun c hc => ?_
    obtain ⟨f, l, x, rfl⟩ := hio r1 hr c hc
    rfl
  · rfl

/-- **`ioTail` is `ioTailP`** when, after the prefix's writes, the re-read thread is `t` (on any store). -/
theorem ioTail_eq {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (info : msginfo.MessageInfo) (number : I64)
    (hC : ∀ i2 s1 s2 a1, obj.Tcb.set_reg m t s layout.reg.FAULT_IP i2 = ok s1 →
      sched.update_timestamp m ar s1 a = ok (s2, a1) → ∀ t', sched.cur_thread m s2 = ok t' → t' = t) :
    ioTail m ar s a t info number = ioTailP m ar s a t info number := by
  unfold ioTail ioTailP
  refine bind_guard_congr rfl fun b _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  refine bind_guard_congr rfl fun next _ => ?_
  refine bind_guard_congr rfl fun i2 _ => ?_
  refine bind_guard_congr rfl fun s1 hs1 => ?_
  refine bind_guard_congr rfl fun ⟨s2, a1⟩ hu => ?_
  refine bind_guard_congr rfl fun cptr _ => ?_
  refine bind_guard_congr rfl fun csc _ => ?_
  refine bind_guard_congr rfl fun i3 _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  refine bind_guard_congr rfl fun i4 _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  refine bind_guard_congr rfl fun b1 hb1 => ?_
  refine ite_congr rfl (fun hb => ?_) (fun _ => rfl)
  refine bind_guard_congr rfl fun i5 _ => ?_
  refine bind_guard_congr rfl fun b2 _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  refine bind_guard_congr rfl fun b3 _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  have hb1' : ioport.invocation_ok m s2 t cptr info = ok true := by rw [hb1, hb]
  obtain ⟨r0, f, l, x, hr0, hc0⟩ := inv_true_m hb1'
  rw [hinv_eq m ar s2 a1 _ _ _ _ cptr t (hC i2 s1 s2 a1 hs1 hu) (fun r1 hr1 c hc => by
    rw [hr0] at hr1
    cases ok_inj_ff hr1
    rw [hc0] at hc
    cases ok_inj_ff hc
    exact ⟨f, l, x, rfl⟩)]

end eqs

/-! ## Steps on a narrowing store -/

section nar
variable {S : Type} {st m : machine.Store S}

theorem Narrow.ksb' (N : Narrow st m) (s : S) : Nar (m.ks_base s) (st.ks_base s) := by
  rw [N.ksb]; exact .refl _

theorem Narrow.cpu' (N : Narrow st m) (s : S) : Nar (m.cur_cpu s) (st.cur_cpu s) := by
  rw [N.cpu]; exact .refl _

theorem Nar.ite2 {T : Type} {c : Prop} [Decidable c] {x' x y' y : Result T} (h1 : c → Nar x' x)
    (h2 : ¬ c → Nar y' y) : Nar (if c then x' else y') (if c then x else y) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact h1 h
  · rw [if_neg h, if_neg h]; exact h2 h

/-- Walks two copies of one extracted body, on a narrowing store and on `st`. -/
macro "nar_walk" N:term : tactic => `(tactic| repeat' (first
  | exact Nar.refl _
  | exact ($N).read _ _
  | exact ($N).write _ _ _
  | exact Narrow.ksb' $N _
  | exact Narrow.cpu' $N _
  | (refine Nar.bind ?_ (fun ⟨_, _⟩ _ => ?_); simp only [Aeneas.Std.uncurry_apply_pair])
  | (refine Nar.bind ?_ (fun _ _ => ?_))
  | (refine Nar.ite2 (fun _ => ?_) (fun _ => ?_))))

theorem cur_thread_nar (N : Narrow st m) (s : S) : Nar (sched.cur_thread m s) (sched.cur_thread st s) := by
  unfold sched.cur_thread obj.node_get obj.node_base
  nar_walk N

theorem set_reg_nar (N : Narrow st m) (t : U64) (s : S) (r v : U64) :
    Nar (obj.Tcb.set_reg m t s r v) (obj.Tcb.set_reg st t s r v) := by
  unfold obj.Tcb.set_reg
  nar_walk N

theorem update_timestamp_nar {A : Type} (N : Narrow st m) (ar : machine.Arch A) (s : S) (a : A) :
    Nar (sched.update_timestamp m ar s a) (sched.update_timestamp st ar s a) := by
  unfold sched.update_timestamp sched.cur_time sched.consumed sched.set_consumed sched.domain_time
    obj.node_get obj.node_set obj.node_base obj.ks_set obj.ks_get
  nar_walk N

end nar

/-! ## The pruning on the bridge's stores and states -/

section prune
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **The I/O port body is `ioBodyP`** on every store narrowing `st`, from every entry state and every
alternative of one. -/
theorem io_prune (hA : P0.ArchTotal ar) {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {m : machine.Store S} (N : Narrow st m)
    {s' : S} (hG : AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s')
    (a : A) (number : I64) :
    syscall.handle_ioport_local m ar s' a number = ioBodyP S number ar m s' a := by
  obtain ⟨s, hE, Al⟩ := hG
  have P := hPE s hE
  have hk : L.ksb s' = L.ksb s := Al.ksb
  have hc : L.cpu s' = L.cpu s := Al.cpu
  have hct : layout.node.CUR_THREAD.val < 4288 ∧ layout.node.CUR_THREAD.val % 8 = 0 := by
    simp [layout.node.CUR_THREAD]
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW
    rw [hc, nodeAt_of_ksb hk]
    exact Al.read _ (P.nd (Locks := Locks) _ hct.1 hct.2).1
  have eb : L.nodeBase s' (L.cpu s') = L.nodeBase s (L.cpu s) := by
    simp only [LawfulStore.nodeBase, hk, hc]
  have hN : NodePlaced st T s' (L.cpu s') :=
    ⟨by rw [eb]; exact P.np.align, by rw [eb]; exact P.np.fits, by rw [eb]; exact P.np.disj⟩
  have hcT : L.curW s' ∈ T := hcur ▸ P.cT
  rw [handle_ioport_local_eq]
  unfold ioBodyP
  refine bind_guard_congr rfl fun t ht => ?_
  have et : t = L.curW s' := by
    have := (cur_thread_nar N s').ok_eq ht
    rw [cur_thread_ok] at this
    exact (ok_inj_ff this).symm
  subst et
  have key : ioTail m ar s' a (L.curW s') = ioTailP m ar s' a (L.curW s') := by
    funext info number
    refine ioTail_eq m ar s' a _ info number fun i2 s1 s2 a1 hs1 hu t' ht' => ?_
    have es1 := (set_reg_nar N _ s' _ i2).ok_eq hs1
    have eu := (update_timestamp_nar N ar s1 a).ok_eq hu
    have w := prefix_writes ar hA P.tp hN hcT es1 eu
    have e2 := pre_node (o := layout.node.CUR_THREAD) w P.tp hN hcT hct.1 hct.2
      (by simp [layout.node.CUR_THREAD, layout.node.CUR_TIME]) (by simp [layout.node.CUR_THREAD, layout.node.CONSUMED])
    have := (cur_thread_nar N s2).ok_eq ht'
    rw [cur_thread_ok] at this
    rw [← ok_inj_ff this]
    unfold LawfulStore.curW
    rw [w.2.1, nodeAt_of_ksb w.1]
    exact e2
  refine bind_guard_congr rfl fun info _ => ?_
  rw [key]

/-- **The relativised program premise of the I/O port path** from a tree of the pruned body. -/
theorem io_isProgOn (hA : P0.ArchTotal ar) {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {number : I64} {p : SProg Bool}
    (hp : IsProg (ioBodyP S number) p) :
    IsProgOn (fun m s a => syscall.handle_ioport_local m ar s a number) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) p :=
  fun m N s' hG a => by
    show syscall.handle_ioport_local m ar s' a number = _
    exact (io_prune (Locks := Locks) hA hPE N hG a number).trans (congrFun (congrFun (hp A ar m) s') a)

end prune

end Fl4Proofs.P2.PathObl

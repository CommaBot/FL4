/-
# P2 (line p2sl): declined runs of `handle_syscall_local` on other stores

A run of the syscall entry beside the gate that declines (`false`: the trap
arm's or the ReplyRecv arm's checks fail, or the head refill is not
sufficient) writes only the prefix words (`FAULT_IP` of the current thread,
the node's `CUR_TIME` and `CONSUMED`): every `false` exit of `fastpath.fault`
and `fastpath.reply_recv_found` is `ok (false, s, a)` after reads only.

* `SlRdEq st m`: `m` reads as `st`; `tr_bind_ro`: a read-only callee (one that
  only reads, at one state: proved by `rfl` against the constant-read store
  `slCst`) answers the same on `m`;
* `SlPreOK st m x t`: `m` writes the prefix words of `x` as `st`;
  `sl_upd_m`: `update_timestamp` on `m`;
* `fault_dec_m`, `rr_dec_m`, **`sl_dec_m`**: a run that declines on `st`
  declines the same way on `m`;
* `sl_dec_mguard`: on `mguard` for `StepOK` of `OwnMap` (the prefix words are
  aligned and decide no owner, `NonDec`); `sl_dec_guard`: on the store
  guarded to writes of the prefix words `SlDS`.

Premises: none beyond `PreAcc`'s (the prefix words, `NonDec` for `mguard`).
-/
import Fl4Proofs.P2.MoveSyscall
import Fl4Proofs.P2.AccessCSpace
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {m : machine.Store S}

/-- A store whose reads are constants (the state is ignored). -/
def slCst (rd : U64 → Result U64) (rp : U64 → Result (U64 × U64)) (ks cp : Result U64) : machine.Store S where
  frame_masks := fun _ => fail .panic
  read := fun _ a => rd a
  read_pair := fun _ a => rp a
  write := fun _ _ _ => fail .panic
  zero := fun _ _ _ => fail .panic
  clear_free := fun _ _ _ => fail .panic
  ks_base := fun _ => ks
  cur_cpu := fun _ => cp
  fetch_and := fun _ _ _ => fail .panic

/-- `m` reads as `st`. -/
structure SlRdEq (st m : machine.Store S) : Prop where
  rd : ∀ x a, m.read x a = st.read x a
  rp : ∀ x a, m.read_pair x a = st.read_pair x a
  ks : ∀ x, m.ks_base x = st.ks_base x
  cp : ∀ x, m.cur_cpu x = st.cur_cpu x

theorem SlRdEq.ro {α : Type} (h : SlRdEq st m) (x : S) (F : machine.Store S → Result α)
    (hF : ∀ n : machine.Store S, F n = F (slCst (S := S) (fun a => n.read x a) (fun a => n.read_pair x a)
      (n.ks_base x) (n.cur_cpu x))) : F m = F st := by
  have e1 : (fun a => m.read x a) = fun a => st.read x a := funext (h.rd x)
  have e2 : (fun a => m.read_pair x a) = fun a => st.read_pair x a := funext (h.rp x)
  rw [hF m, hF st, e1, e2, h.ks, h.cp]

/-- Transfer along a read-only callee. -/
theorem tr_bind_ro (h : SlRdEq st m) (x : S) {α β : Type} {F : machine.Store S → Result α}
    {k k' : α → Result β} {y : β}
    (hF : ∀ n : machine.Store S, F n = F (slCst (S := S) (fun a => n.read x a) (fun a => n.read_pair x a)
      (n.ks_base x) (n.cur_cpu x)))
    (h2 : ∀ v, F st = ok v → k v = ok y → k' v = ok y) :
    Std.bind (F st) k = ok y → Std.bind (F m) k' = ok y := by
  rw [h.ro x F hF]; exact tr_bind_same h2

/-- `m` writes the prefix words of `x` (at states with `x`'s core and kernel
base) as `st`. -/
def SlPreOK (st m : machine.Store S) [L : LawfulStore st] (x : S) (t : U64) : Prop :=
  ∀ y b v, (b = regA t layout.reg.FAULT_IP ∨ b = L.nodeAt x (L.cpu x) layout.node.CUR_TIME ∨
    b = L.nodeAt x (L.cpu x) layout.node.CONSUMED) → L.ksb y = L.ksb x → L.cpu y = L.cpu x →
    m.write y b v = st.write y b v

theorem sl_node_base_ok (y : S) (c : U64) :
    obj.node_base st y c = ok (core.num.U64.wrapping_add (core.num.U64.wrapping_add (L.ksb y) 13568#u64)
      (core.num.U64.wrapping_mul c 4288#u64)) := by
  unfold obj.node_base
  rw [L.ks_base_eq, eq_ok_of_spec Fl4Proofs.P0.Consts.layout.ks.NODES.spec,
    eq_ok_of_spec Fl4Proofs.P0.Consts.layout.node.SIZE.spec]
  simp only [bind_ok, lift]

theorem sl_node_set_m (h : SlRdEq st m) {x y : S} {t o v : U64} (hP : SlPreOK st m x t)
    (ho : o = layout.node.CUR_TIME ∨ o = layout.node.CONSUMED) (k : L.ksb y = L.ksb x) (c : L.cpu y = L.cpu x) :
    obj.node_set m y (L.cpu y) o v = ok (L.wr y (L.nodeAt y (L.cpu y) o) v) := by
  unfold obj.node_set
  rw [h.ro y (fun n => obj.node_base n y (L.cpu y)) (fun _ => rfl), sl_node_base_ok]
  simp only [bind_ok, lift]
  have e : L.nodeAt y (L.cpu y) o = L.nodeAt x (L.cpu x) o := by rw [c, nodeAt_of_ksb k]
  rw [show core.num.U64.wrapping_add (core.num.U64.wrapping_add (core.num.U64.wrapping_add (L.ksb y) 13568#u64)
      (core.num.U64.wrapping_mul (L.cpu y) 4288#u64)) o = L.nodeAt y (L.cpu y) o from rfl]
  rw [hP y _ v (by rcases ho with rfl | rfl <;> rw [e] <;> simp) k c, L.write_eq]

theorem sl_upd_m (h : SlRdEq st m) {A : Type} {ar : machine.Arch A} {x y : S} {t : U64} {a : A}
    (hP : SlPreOK st m x t) (k : L.ksb y = L.ksb x) (c : L.cpu y = L.cpu x) :
    sched.update_timestamp m ar y a = sched.update_timestamp st ar y a := by
  unfold sched.update_timestamp
  rw [h.ro y (fun n => sched.cur_time n y) (fun _ => rfl)]
  refine congrArg (Std.bind _) (funext fun prev => ?_)
  refine congrArg (Std.bind _) (funext fun na => ?_)
  obtain ⟨now, a1⟩ := na
  rw [h.cp, L.cur_cpu_eq]
  simp only [bind_ok, uncurry_apply_pair, lift]
  rw [sl_node_set_m h hP (Or.inl rfl) k c, eq_ok_of_spec (obj.node_set.spec (L := L) y _ _ _)]
  simp only [bind_ok, lift]
  have k1 : L.ksb (L.wr y (L.nodeAt y (L.cpu y) layout.node.CUR_TIME) now) = L.ksb x := by rw [L.ksb_wr, k]
  have c1 : L.cpu (L.wr y (L.nodeAt y (L.cpu y) layout.node.CUR_TIME) now) = L.cpu x := by rw [L.cpu_wr, c]
  rw [h.ro _ (fun n => sched.consumed n _) (fun _ => rfl)]
  refine congrArg (Std.bind _) (funext fun u => ?_)
  unfold sched.set_consumed
  rw [h.cp, L.cur_cpu_eq]
  simp only [bind_ok]
  rw [sl_node_set_m h hP (Or.inr rfl) k1 c1, eq_ok_of_spec (obj.node_set.spec (L := L) _ _ _ _)]
  simp only [bind_ok]
  have hd : ¬ (layout.NUM_DOMAINS > 1#u64) := by simp [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [if_neg hd, if_neg hd]

variable {A : Type} {ar : machine.Arch A}

open Lean Meta Elab Tactic in
/-- `tr_ro h x` on a goal `bind e k = ok y → bind e' k' = ok y`: `tr_bind_ro`
with the callee `F` abstracted from `e` over the store of `h : SlRdEq st m`
(higher-order unification cannot find `F` from `F st`). -/
elab "tr_ro " h:term:max x:term:max : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let .forallE _ lhs _ _ := tgt | throwError "tr_ro: not an implication"
  let some (_, l, _) := lhs.eq? | throwError "tr_ro: not an equation"
  let args := l.getAppArgs
  unless args.size ≥ 2 do throwError "tr_ro: no bind"
  let e := args[args.size - 2]!
  let hE ← Term.elabTerm h none
  let hT ← whnfR (← instantiateMVars (← inferType hE))
  let stE := hT.getAppArgs[1]!
  let body ← kabstract e stE
  unless body.hasLooseBVars do throwError "tr_ro: the callee does not use the store"
  let F := Expr.lam `n (← inferType stE) body .default
  let Fs ← Term.exprToSyntax F
  evalTactic (← `(tactic| refine tr_bind_ro (F := $Fs) $h $x ?_ (fun _ _ => ?_)))

/-- The checks of a fast path, transferred to `m` (reads only); what is left
is the accepting write part. -/
macro "dec_walk" h:ident x:ident : tactic => `(tactic|
  repeat' (first
    | (with_reducible exact fun h' => h')
    | (refine tr_ite (fun _ => ?_) (fun _ => ?_))
    | (tr_ro $h $x
       · exact fun _ => rfl)
    | (refine tr_bind_same (fun _ _ => ?_))))

/-- An accepting write part ends `true`. -/
macro "acc_true" hk:ident : tactic => `(tactic| (
  have h' := spec_of_eq_fd $hk
  clear $hk
  revert h'
  repeat' (first
    | (with_reducible_and_instances refine spec_bind_imp (fun _ => ?_)
       try simp only [uncurry_eta_fd])
    | (with_reducible_and_instances refine spec_bind_imp' (fun _ => ?_)
       try simp only [uncurry_eta_fd])
    | (with_reducible refine spec_ite_imp (fun _ => ?_) (fun _ => ?_))
    | split
    | (refine spec_bind_imp (fun _ => ?_)
       try simp only [uncurry_eta_fd]))
  all_goals intro h'
  all_goals rw [WP.spec_ok] at h'
  all_goals first
    | (rw [← h'])
    | simp at h'))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **A declined trap arm on `m`.** -/
theorem fault_dec_m (h : SlRdEq st m) {x : S} {a : A} {t n : U64} {r : Bool × S × A}
    (ht : fastpath.fault st ar x a t n = ok r) (hn : r.1 ≠ true) :
    fastpath.fault m ar x a t n = ok r := by
  unfold fastpath.fault at ht ⊢
  revert ht
  refine tr_bind_ro (F := fun n => sched.action n x) h x ?_ (fun _ _ => ?_)
  · exact fun _ => rfl
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  refine tr_bind_same (fun s1 _ => ?_)
  refine tr_bind_ro (F := fun n => obj.Slot.cap n s1 x) h x ?_ (fun c _ => ?_)
  · exact fun _ => rfl
  cases c <;> (try dsimp only) <;> try (with_reducible exact fun h' => h')
  all_goals dec_walk h x
  all_goals (intro hk; exfalso; apply hn)
  all_goals acc_true hk

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **A declined ReplyRecv arm on `m`.** -/
theorem rr_dec_m (h : SlRdEq st m) {x : S} {a : A} {t rp ep : U64} {r : Bool × S × A}
    (ht : fastpath.reply_recv_found st ar x a t rp ep = ok r) (hn : r.1 ≠ true) :
    fastpath.reply_recv_found m ar x a t rp ep = ok r := by
  unfold fastpath.reply_recv_found at ht ⊢
  revert ht
  dec_walk h x
  all_goals (intro hk; exfalso; apply hn)
  all_goals acc_true hk

set_option maxHeartbeats 4000000 in
/-- The prefix and the arms of a declined run on `m`. -/
theorem sl_arm_dec_m (h : SlRdEq st m) {x : S} {a : A} {n : I64} {rp ep : U64} {r : Bool × S × A}
    (hP : SlPreOK st m x (L.curW x)) (i1 : U64) :
    (do
      let next ← obj.Tcb.reg st (L.curW x) x layout.reg.NEXT_IP
      let i2 ← lift (core.num.U64.wrapping_sub next 2#u64)
      let s1 ← obj.Tcb.set_reg st (L.curW x) x layout.reg.FAULT_IP i2
      let (s2, a1) ← sched.update_timestamp st ar s1 a
      let csc ← sched.cur_sc st s2
      let i3 ← sched.consumed st s2
      let b ← sporadic.sufficient st ar s2 a1 csc i3
      if b then
        if i1 != 0#u64 then do
          let i4 ← lift (IScalar.hcast .U64 n)
          fastpath.fault st ar s2 a1 (L.curW x) i4
        else fastpath.reply_recv_found st ar s2 a1 (L.curW x) rp ep
      else ok (false, s2, a1)) = ok r → r.1 ≠ true →
    (do
      let next ← obj.Tcb.reg m (L.curW x) x layout.reg.NEXT_IP
      let i2 ← lift (core.num.U64.wrapping_sub next 2#u64)
      let s1 ← obj.Tcb.set_reg m (L.curW x) x layout.reg.FAULT_IP i2
      let (s2, a1) ← sched.update_timestamp m ar s1 a
      let csc ← sched.cur_sc m s2
      let i3 ← sched.consumed m s2
      let b ← sporadic.sufficient m ar s2 a1 csc i3
      if b then
        if i1 != 0#u64 then do
          let i4 ← lift (IScalar.hcast .U64 n)
          fastpath.fault m ar s2 a1 (L.curW x) i4
        else fastpath.reply_recv_found m ar s2 a1 (L.curW x) rp ep
      else ok (false, s2, a1)) = ok r := by
  intro hr hn
  revert hr
  rw [h.ro x (fun n => obj.Tcb.reg n (L.curW x) x layout.reg.NEXT_IP) (fun _ => rfl)]
  refine tr_bind_same (fun nx _ => ?_)
  simp only [lift, bind_ok]
  have es : obj.Tcb.set_reg m (L.curW x) x layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) =
      obj.Tcb.set_reg st (L.curW x) x layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) := by
    unfold obj.Tcb.set_reg
    simp only [lift, bind_ok]
    exact hP x _ _ (Or.inl rfl) rfl rfl
  rw [es]
  refine tr_bind_same (fun s1 es1 => ?_)
  rw [set_reg_ok'] at es1
  have k1 : L.ksb s1 = L.ksb x := by rw [← ok_inj_ff es1, L.ksb_wr]
  have c1 : L.cpu s1 = L.cpu x := by rw [← ok_inj_ff es1, L.cpu_wr]
  rw [sl_upd_m h hP k1 c1]
  refine tr_bind_same (fun q _ => ?_)
  obtain ⟨s2, a1⟩ := q
  simp only [uncurry_apply_pair]
  rw [h.ro s2 (fun n => sched.cur_sc n s2) (fun _ => rfl)]
  refine tr_bind_same (fun csc _ => ?_)
  rw [h.ro s2 (fun n => sched.consumed n s2) (fun _ => rfl)]
  refine tr_bind_same (fun i3 _ => ?_)
  rw [h.ro s2 (fun n => sporadic.sufficient n ar s2 a1 csc i3) (fun _ => rfl)]
  refine tr_bind_same (fun b _ => ?_)
  refine tr_ite (fun _ => tr_ite (fun _ ht => fault_dec_m h ht hn)
    (fun _ ht => rr_dec_m h ht hn)) (fun _ h' => h')

set_option maxHeartbeats 4000000 in
/-- **A declined run of the syscall entry on `m`.** -/
theorem sl_dec_m (h : SlRdEq st m) {x : S} {a : A} {n : I64} {found : U64 × U64} {r : Bool × S × A}
    (hP : SlPreOK st m x (L.curW x))
    (hr : syscall.handle_syscall_local st ar x a n found = ok r) (hn : r.1 ≠ true) :
    syscall.handle_syscall_local m ar x a n found = ok r := by
  obtain ⟨rp, ep⟩ := found
  unfold syscall.handle_syscall_local at hr ⊢
  revert hr
  rw [h.ro x (fun n => sched.cur_thread n x) (fun _ => rfl), cur_thread_ok]
  simp only [bind_ok]
  rw [h.ro x (fun n => obj.Tcb.flags n (L.curW x) x) (fun _ => rfl)]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  refine tr_ite (fun _ ht => sl_arm_dec_m h hP i1 ht hn) (fun _ => ?_)
  exact tr_ite (fun _ h' => h') (fun _ ht => sl_arm_dec_m h hP i1 ht hn)

/-! ## The two stores -/

/-- The prefix words of the entry state `s`. -/
def SlDS (s : S) (b : U64) : Prop :=
  b = regA (L.curW s) layout.reg.FAULT_IP ∨ b = L.nodeAt s (L.cpu s) layout.node.CUR_TIME ∨
    b = L.nodeAt s (L.cpu s) layout.node.CONSUMED

theorem slRdEq_guard (W : U64 → Prop) : SlRdEq st (guard st (fun _ => True) W) where
  rd _ _ := guard_read trivial
  rp _ _ := guard_read_pair trivial trivial
  ks _ := rfl
  cp _ := rfl

theorem slRdEq_mguard (Q : S → S → Prop) : SlRdEq st (mguard st Q) where
  rd _ _ := rfl
  rp _ _ := rfl
  ks _ := rfl
  cp _ := rfl

theorem slDS_node {s y : S} {o : U64} (k : L.ksb y = L.ksb s) (c : L.cpu y = L.cpu s) :
    L.nodeAt y (L.cpu y) o = L.nodeAt s (L.cpu s) o := by
  rw [c, nodeAt_of_ksb k]

/-- **A declined run on the store guarded to the prefix words** (`dec` at the
entry state). -/
theorem sl_dec_guard {s : S} {a : A} {n : I64} {found : U64 × U64} {r : Bool × S × A}
    (hr : syscall.handle_syscall_local st ar s a n found = ok r) (hn : r.1 ≠ true) :
    syscall.handle_syscall_local (guard st (fun _ => True) (SlDS (L := L) s)) ar s a n found = ok r :=
  sl_dec_m (slRdEq_guard _) (fun _ _ _ hb _ _ => guard_write hb) hr hn

/-- **A declined run on `mguard`** for `StepOK` of `OwnMap`: the prefix words
are aligned and decide no owner (`PreAcc` with the write set `NonDec K`). -/
theorem sl_dec_mguard {K : KLayout} (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K) {lk : U64 → Prop} {mm : U64 → U64}
    {s : S} {a : A} {n : I64} {found : U64 × U64} {r : Bool × S × A}
    (hpre : PreAcc (L := L) (fun _ => True) (NonDec K) s)
    (hr : syscall.handle_syscall_local st ar s a n found = ok r) (hn : r.1 ≠ true) :
    syscall.handle_syscall_local
        (mguard st fun x y => StepOK (own K) (cls K) (ko K mm) (· ∈ K.user) (L.cpu s) lk (L.mem x) (L.mem y))
        ar s a n found = ok r := by
  refine sl_dec_m (slRdEq_mguard _) (fun y b v hb _ _ => ?_) hr hn
  have hnd : NonDec K b := by
    rcases hb with rfl | rfl | rfl
    · exact hpre.fi
    · exact (hpre.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2
    · exact (hpre.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2
  rw [mguard_write (L.write_eq y b v) (stepOK_nondec hK hU hnd.1 hnd.2), L.write_eq]

/-- `PreAcc` moves to a state with the same core, kernel base and current
thread. -/
theorem PreAcc.transport {K : KLayout} {s s' : S} (hk : L.ksb s' = L.ksb s) (hc : L.cpu s' = L.cpu s)
    (hcur : L.curW s' = L.curW s) (hpre : PreAcc (L := L) (fun _ => True) (NonDec K) s) :
    PreAcc (L := L) (fun _ => True) (NonDec K) s' where
  nd o h1 h2 := by rw [slDS_node hk hc]; exact hpre.nd o h1 h2
  fl := trivial
  nx := trivial
  fi := by rw [hcur]; exact hpre.fi

/-- **A run declining at a state `s'` with the entry's core, kernel base and
current thread** (an alternative of the entry `s`, `Alt`, whose `ReadSet`
holds the node's `CUR_THREAD`): it runs the same on the store guarded to the
entry's prefix words and on `mguard` at the entry's core (`dec_alt` once the
run at `s'` is known to decline). -/
theorem sl_dec_at {K : KLayout} (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K) {lk : U64 → Prop} {mm : U64 → U64}
    {s s' : S} {a : A} {n : I64} {found : U64 × U64} {r : Bool × S × A}
    (hk : L.ksb s' = L.ksb s) (hc : L.cpu s' = L.cpu s) (hcur : L.curW s' = L.curW s)
    (hpre : PreAcc (L := L) (fun _ => True) (NonDec K) s)
    (hr : syscall.handle_syscall_local st ar s' a n found = ok r) (hn : r.1 ≠ true) :
    syscall.handle_syscall_local (guard st (fun _ => True) (SlDS (L := L) s)) ar s' a n found = ok r ∧
    syscall.handle_syscall_local
        (mguard st fun x y => StepOK (own K) (cls K) (ko K mm) (· ∈ K.user) (L.cpu s) lk (L.mem x) (L.mem y))
        ar s' a n found = ok r := by
  refine ⟨sl_dec_m (slRdEq_guard _) (fun _ b _ hb _ _ => guard_write ?_) hr hn, ?_⟩
  · show SlDS (L := L) s b
    unfold SlDS
    rw [← hcur, ← slDS_node (o := layout.node.CUR_TIME) hk hc, ← slDS_node (o := layout.node.CONSUMED) hk hc]
    exact hb
  · have := sl_dec_mguard (lk := lk) (mm := mm) hK hU (PreAcc.transport hk hc hcur hpre) hr hn
    rwa [hc] at this

set_option maxHeartbeats 4000000 in
/-- **`PathObl.move` of the syscall entry beside the gate**, every run: a
declined run by `sl_dec_mguard`, an accepted run by `move_trap` / `move_rr`
(their premises, each under its arm's flag test). -/
theorem syscall.handle_syscall_local.move {K : KLayout} (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {lk : U64 → Prop} {mm : U64 → U64}
    {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap}
    {Z : U64 → Nat} (hA : P0.ArchTotal ar) {s : S} {a : A} {n : I64} {found : U64 × U64}
    {p : SProg Bool}
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p)
    (hm : ∀ d, K.heap d = some .tcb → mm (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hpre : PreAcc (L := L) (fun _ => True) (NonDec K) s)
    (hI : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X)
    (hAs : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → AsidOff (L := L) Ω Sg X)
    (hSt : K.heap (L.curW s) = some .tcb ∧ Safe0 (L.cpu s) lk (L.mem s) (L.curW s))
    -- the trap arm
    (hrecv : SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (stA dest) = sched.TS_BLOCKED_ON_RECV)
    (hF : SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) →
      FaultEntAt (L := L) T Cs Ω U Sg Rp X (L.curW s))
    (hy0f : SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (yieldA dest) = 0#u64)
    (hTm : SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → TimerOK st T Cs X)
    (hRWf : SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r →
        FltAcc (L := L) Z (fun _ => True) (NonDec K) X (L.curW s) ptr dest r)
    (hSd : SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r →
        K.heap dest = some .tcb ∧ Safe0 (L.cpu s) lk (L.mem s) dest)
    -- the ReplyRecv arm
    (hPl : ¬ SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
      RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X (L.curW s) found.1 found.2 u usc)
    (hrz : ¬ SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) →
      L.mem X (rNextA found.1) &&& ~~~1#u64 = 0#u64 ∧ L.mem X (rPrevA found.1) &&& ~~~1#u64 = 0#u64)
    (hy0r : ¬ SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc → L.mem X (yieldA u) = 0#u64)
    (hRWr : ¬ SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
      RrAcc (L := L) Z (fun _ => True) (NonDec K) X (L.curW s) found.1 found.2 u usc)
    (hSu : ¬ SlTrap st s → ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
        K.heap u = some .tcb ∧ Safe0 (L.cpu s) lk (L.mem s) u)
    (hlk : ¬ SlTrap st s → lk found.2)
    {r : Bool × S × A} (h : syscall.handle_syscall_local st ar s a n found = ok r) :
    syscall.handle_syscall_local
        (mguard st fun x y => StepOK (own K) (cls K) (ko K mm) (· ∈ K.user) (L.cpu s) lk (L.mem x) (L.mem y))
        ar s a n found = ok r := by
  obtain ⟨b, s', a'⟩ := r
  by_cases hb : b = true
  · subst hb
    by_cases hS : SlTrap st s
    · exact syscall.handle_syscall_local.move_trap ar hK hU hA hFp hm hS hT hN hcT hpre hI hAs
        (hrecv hS) (hF hS) (hy0f hS) (hTm hS) (hRWf hS) hSt (hSd hS) h
    · exact syscall.handle_syscall_local.move_rr ar hK hU hA hFp hm hS hT hN hcT hpre hI hAs
        (hPl hS) (hrz hS) (hy0r hS) (hRWr hS) hSt (hSu hS) (hlk hS) h
  · exact sl_dec_mguard hK hU hpre h hb

end

end Fl4Proofs.P2.PathObl

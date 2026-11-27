/-
# P2: a declined I/O port run on other stores (line p2io)

* `RdEq st m`: `m` reads as `st`; `RdEq.ro`: a read-only callee answers the same;
* `node_set_m`, `upd_m`: the prefix's writes on `m`, given `m` writes the prefix
  words as `st` (`PreOK`);
* `ioTail_dec_m`, `handle_dec_m`: a run that declines on `st` declines the
  same way on `m`.

Premises: none.
-/
import Fl4Proofs.P2.AccessIoAlt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {m : machine.Store S}

/-- `m` reads as `st`. -/
structure RdEq (st m : machine.Store S) : Prop where
  rd : ∀ x a, m.read x a = st.read x a
  rp : ∀ x a, m.read_pair x a = st.read_pair x a
  ks : ∀ x, m.ks_base x = st.ks_base x
  cp : ∀ x, m.cur_cpu x = st.cur_cpu x

theorem RdEq.cstE (h : RdEq st m) (x : S) :
    cst (S := S) (fun a => m.read x a) (fun a => m.read_pair x a) (m.ks_base x) (m.cur_cpu x) =
      cst (fun a => st.read x a) (fun a => st.read_pair x a) (st.ks_base x) (st.cur_cpu x) := by
  have e1 : (fun a => m.read x a) = fun a => st.read x a := funext (h.rd x)
  have e2 : (fun a => m.read_pair x a) = fun a => st.read_pair x a := funext (h.rp x)
  rw [e1, e2, h.ks, h.cp]

theorem RdEq.ro {α : Type} (h : RdEq st m) (x : S) (F : machine.Store S → Result α)
    (hF : ∀ n : machine.Store S, F n = F (cst (S := S) (fun a => n.read x a) (fun a => n.read_pair x a)
      (n.ks_base x) (n.cur_cpu x))) : F m = F st := by
  rw [hF m, hF st, h.cstE x]

/-- `m` writes the prefix words of `x` (at states on the same core) as `st`. -/
def PreOK (st m : machine.Store S) [L : LawfulStore st] (x : S) (t : U64) : Prop :=
  ∀ y b v, (b = regA t layout.reg.FAULT_IP ∨ b = L.nodeAt x (L.cpu x) layout.node.CUR_TIME ∨
    b = L.nodeAt x (L.cpu x) layout.node.CONSUMED) → L.ksb y = L.ksb x → L.cpu y = L.cpu x →
    m.write y b v = st.write y b v

theorem node_base_ok (y : S) (c : U64) :
    obj.node_base st y c = ok (core.num.U64.wrapping_add (core.num.U64.wrapping_add (L.ksb y) 13568#u64)
      (core.num.U64.wrapping_mul c 4288#u64)) := by
  unfold obj.node_base
  rw [L.ks_base_eq, eq_ok_of_spec Fl4Proofs.P0.Consts.layout.ks.NODES.spec,
    eq_ok_of_spec Fl4Proofs.P0.Consts.layout.node.SIZE.spec]
  simp only [bind_ok, lift]

theorem node_set_m (h : RdEq st m) {x y : S} {t o v : U64} (hP : PreOK st m x t)
    (ho : o = layout.node.CUR_TIME ∨ o = layout.node.CONSUMED) (k : L.ksb y = L.ksb x) (c : L.cpu y = L.cpu x) :
    obj.node_set m y (L.cpu y) o v = ok (L.wr y (L.nodeAt y (L.cpu y) o) v) := by
  unfold obj.node_set
  rw [h.ro y (fun n => obj.node_base n y (L.cpu y)) (fun _ => rfl), node_base_ok]
  simp only [bind_ok, lift]
  have e : L.nodeAt y (L.cpu y) o = L.nodeAt x (L.cpu x) o := by rw [c, nodeAt_of_ksb k]
  rw [show core.num.U64.wrapping_add (core.num.U64.wrapping_add (core.num.U64.wrapping_add (L.ksb y) 13568#u64)
      (core.num.U64.wrapping_mul (L.cpu y) 4288#u64)) o = L.nodeAt y (L.cpu y) o from rfl]
  rw [hP y _ v (by rcases ho with rfl | rfl <;> rw [e] <;> simp) k c, L.write_eq]

theorem upd_m (h : RdEq st m) {A : Type} {ar : machine.Arch A} {x y : S} {t : U64} {a : A} (hP : PreOK st m x t)
    (k : L.ksb y = L.ksb x) (c : L.cpu y = L.cpu x) :
    sched.update_timestamp m ar y a = sched.update_timestamp st ar y a := by
  unfold sched.update_timestamp
  rw [h.ro y (fun n => sched.cur_time n y) (fun _ => rfl)]
  refine congrArg (Std.bind _) (funext fun prev => ?_)
  refine congrArg (Std.bind _) (funext fun na => ?_)
  obtain ⟨now, a1⟩ := na
  rw [h.cp, L.cur_cpu_eq]
  simp only [bind_ok, uncurry_apply_pair, lift]
  rw [node_set_m h hP (Or.inl rfl) k c, eq_ok_of_spec (obj.node_set.spec (L := L) y _ _ _)]
  simp only [bind_ok, lift]
  have k1 : L.ksb (L.wr y (L.nodeAt y (L.cpu y) layout.node.CUR_TIME) now) = L.ksb x := by rw [L.ksb_wr, k]
  have c1 : L.cpu (L.wr y (L.nodeAt y (L.cpu y) layout.node.CUR_TIME) now) = L.cpu x := by rw [L.cpu_wr, c]
  rw [h.ro _ (fun n => sched.consumed n _) (fun _ => rfl)]
  refine congrArg (Std.bind _) (funext fun u => ?_)
  unfold sched.set_consumed
  rw [h.cp, L.cur_cpu_eq]
  simp only [bind_ok]
  rw [node_set_m h hP (Or.inr rfl) k1 c1, eq_ok_of_spec (obj.node_set.spec (L := L) _ _ _ _)]
  simp only [bind_ok]
  have hd : ¬ (layout.NUM_DOMAINS > 1#u64) := by simp [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [if_neg hd, if_neg hd]

set_option maxHeartbeats 1000000 in
/-- **A declined tail on `m`.** -/
theorem ioTail_dec_m (h : RdEq st m) {A : Type} {ar : machine.Arch A} {x : S} {a : A} {t : U64}
    {info : msginfo.MessageInfo} {number : I64} {r : Bool × S × A} (hP : PreOK st m x t)
    (ht : ioTail st ar x a t info number = ok r) (hn : r.1 ≠ true) : ioTail m ar x a t info number = ok r := by
  unfold ioTail at ht ⊢
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
  rw [h.ro s2 (fun n => obj.Tcb.reg n t s2 layout.reg.CAP) (fun _ => rfl)]
  refine tr_bind_same (fun cptr _ => ?_)
  rw [h.ro s2 (fun n => sched.cur_sc n s2) (fun _ => rfl)]
  refine tr_bind_same (fun csc _ => ?_)
  rw [h.ro s2 (fun n => sched.action n s2) (fun _ => rfl)]
  refine tr_bind_same (fun i3 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [h.ro s2 (fun n => obj.Tcb.yield_to n t s2) (fun _ => rfl)]
  refine tr_bind_same (fun i4 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [h.ro s2 (fun n => ioport.invocation_ok n s2 t cptr info) (fun _ => rfl)]
  refine tr_bind_same (fun b1 _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [h.ro s2 (fun n => sched.consumed n s2) (fun _ => rfl)]
  refine tr_bind_same (fun i5 _ => ?_)
  rw [h.ro s2 (fun n => sporadic.sufficient n ar s2 a1 csc i5) (fun _ => rfl)]
  refine tr_bind_same (fun b2 _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [h.ro s2 (fun n => fastpath.schedulable_here n s2 t) (fun _ => rfl)]
  refine tr_bind_same (fun b3 _ => ?_)
  refine tr_ite (fun _ hk => ?_) (fun _ h => h)
  exfalso
  obtain ⟨_, -, hk⟩ := bind_eq_ok hk
  obtain ⟨_, -, hk⟩ := bind_eq_ok hk
  obtain ⟨_, -, hk⟩ := bind_eq_ok hk
  exact hn (by rw [← ok_inj_ff hk])

/-- **A declined run on `m`.** -/
theorem handle_dec_m (h : RdEq st m) {A : Type} {ar : machine.Arch A} {x : S} {a : A} {number : I64}
    {r : Bool × S × A} (hP : PreOK st m x (L.curW x))
    (hr : syscall.handle_ioport_local st ar x a number = ok r) (hn : r.1 ≠ true) :
    syscall.handle_ioport_local m ar x a number = ok r := by
  rw [handle_ioport_local_eq] at hr ⊢
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
  refine tr_ite (fun _ => tr_ite (fun _ h => h) (fun _ ht => ioTail_dec_m h hP ht hn)) (fun _ ht => ioTail_dec_m h hP ht hn)

end

end Fl4Proofs.P2.PathObl

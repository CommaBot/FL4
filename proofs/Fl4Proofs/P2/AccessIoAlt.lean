/-
# P2: the I/O port path's declines (line p2io)

`PathObl.dec_alt` for `syscall.handle_ioport_local`: a run that declines at the
entry `s` declines from every alternative state, writing only `IoDS`.

* `Ag`: two states with the same core and kernel base and equal on a set;
  `cst`: reads as constants; `here_congr`, `suff_congr`, `lib_congr`: the path's read-only
  checks give the same answer at `Ag` states (they read inside the set, by
  their guard lemmas);
* `slot_back`: at an alternative state, a slot holding a CNode or I/O port cap
  held the same cap at `s` (a Null / Frame slot only changes to Null / Frame);
  `rab_loop_back`, `lookup_back`, `inv_back`: a passing `invocation_ok` passes at `s`;
* `upd_eq`: `update_timestamp` on one domain; `ioTail_true`: all checks passing,
  a run that returns is accepted;
* `io_dec_alt_acc`: a declined run's alternative is not accepted;
* `ioTail_dec`, `handle_dec`: a declined run on another store instance;
  `io_dec_guard`, `io_dec_mguard`: `guard` (writes `IoDS`) and `mguard`.

Premises: those of `IoPre`, `RegionOK` / `IoLayA` [J].
-/
import Fl4Proofs.P2.AccessIoStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region tcbOwner TcbSlot NullOrFrame slotOwner RegionOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop} {x y z : S}

/-- Same core, same kernel base, equal on `R`. -/
structure Ag (st : machine.Store S) [L : LawfulStore st] (R : U64 → Prop) (x y : S) : Prop where
  k : L.ksb y = L.ksb x
  c : L.cpu y = L.cpu x
  m : ∀ b, R b → L.mem y b = L.mem x b

/-- A store whose reads are constants. -/
def cst (rd : U64 → Result U64) (rp : U64 → Result (U64 × U64)) (ks cp : Result U64) : machine.Store S where
  frame_masks := fun _ => fail .panic
  read := fun _ a => rd a
  read_pair := fun _ a => rp a
  write := fun _ _ _ => fail .panic
  zero := fun _ _ _ => fail .panic
  clear_free := fun _ _ _ => fail .panic
  ks_base := fun _ => ks
  cur_cpu := fun _ => cp

open Classical in
theorem ag_cst (h : Ag st R x y) :
    cst (S := S) (fun a => (guard st R W).read x a) (fun a => (guard st R W).read_pair x a) (st.ks_base x) (st.cur_cpu x) =
      cst (fun a => (guard st R W).read y a) (fun a => (guard st R W).read_pair y a) (st.ks_base y) (st.cur_cpu y) := by
  have e1 : (fun a => (guard st R W).read x a) = fun a => (guard st R W).read y a := by
    funext a
    by_cases ha : R a
    · rw [guard_read ha, guard_read ha, L.read_eq, L.read_eq, h.m a ha]
    · rw [guard_read_out ha, guard_read_out ha]
  have e2 : (fun a => (guard st R W).read_pair x a) = fun a => (guard st R W).read_pair y a := by
    funext a
    by_cases ha : R a ∧ R (core.num.U64.wrapping_add a 8#u64)
    · rw [guard_read_pair ha.1 ha.2, guard_read_pair ha.1 ha.2, L.read_pair_eq, L.read_pair_eq, h.m _ ha.1, h.m _ ha.2]
    · show (if R a ∧ R (core.num.U64.wrapping_add a 8#u64) then st.read_pair x a else fail .panic) =
        (if R a ∧ R (core.num.U64.wrapping_add a 8#u64) then st.read_pair y a else fail .panic)
      rw [if_neg ha, if_neg ha]
  rw [e1, e2, L.ks_base_eq, L.ks_base_eq, L.cur_cpu_eq, L.cur_cpu_eq, h.k, h.c]

theorem here_ag (h : Ag st R x y) (t : U64) :
    fastpath.schedulable_here (guard st R W) x t = fastpath.schedulable_here (guard st R W) y t := by
  have e1 : ∀ z : S, fastpath.schedulable_here (guard st R W) z t =
      fastpath.schedulable_here (cst (S := S) (fun a => (guard st R W).read z a) (fun a => (guard st R W).read_pair z a)
        (st.ks_base z) (st.cur_cpu z)) z t := fun z => rfl
  rw [e1 x, e1 y, ag_cst h]; rfl

theorem suff_ag {A : Type} {ar : machine.Arch A} (h : Ag st R x y) (a : A) (sc u : U64) :
    sporadic.sufficient (guard st R W) ar x a sc u = sporadic.sufficient (guard st R W) ar y a sc u := by
  have e1 : ∀ z : S, sporadic.sufficient (guard st R W) ar z a sc u =
      sporadic.sufficient (cst (S := S) (fun a => (guard st R W).read z a) (fun a => (guard st R W).read_pair z a)
        (st.ks_base z) (st.cur_cpu z)) ar z a sc u := fun z => rfl
  rw [e1 x, e1 y, ag_cst h]; rfl

theorem lib_ag (h : Ag st R x y) (rcv : Bool) (t : U64) :
    msg.lookup_ipc_buffer (guard st R W) x rcv t = msg.lookup_ipc_buffer (guard st R W) y rcv t := by
  have e1 : ∀ z : S, msg.lookup_ipc_buffer (guard st R W) z rcv t =
      msg.lookup_ipc_buffer (cst (S := S) (fun a => (guard st R W).read z a) (fun a => (guard st R W).read_pair z a)
        (st.ks_base z) (st.cur_cpu z)) z rcv t := fun z => rfl
  rw [e1 x, e1 y, ag_cst h]; rfl

theorem Ag.node (h : Ag st R x y) (o : U64) : L.nodeAt y (L.cpu y) o = L.nodeAt x (L.cpu x) o := by
  rw [h.c, nodeAt_of_ksb h.k]

theorem Ag.rdHead (h : Ag st R x y) {sc : U64} (hs : RdHead (L := L) R x sc) : RdHead (L := L) R y sc := by
  unfold RdHead LawfulStore.rhead at hs ⊢
  rw [h.m _ hs.1]; exact hs

/-- The check `schedulable_here` at `Ag` states. -/
theorem here_congr (h : Ag st R x y) {t : U64}
    (hct : R (ctA (L := L) x)) (htm : R (tmA (L := L) x)) (hrh : R (rhA (L := L) x))
    (htd : L.mem x (tmA (L := L) x) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem x (tmA (L := L) x)) 3528#u64))
    (hrs : L.mem x (rhA (L := L) x) ≠ 0#u64 → R (scA (L.mem x (rhA (L := L) x))) ∧
      RdHead (L := L) R x (L.mem x (scA (L.mem x (rhA (L := L) x)))))
    (hdt : R (core.num.U64.wrapping_add (L.ksb x) layout.ks.DOMAIN_TIME))
    (hcd : R (core.num.U64.wrapping_add (L.ksb x) layout.ks.CUR_DOMAIN))
    (haf : R (affA t)) (hdo : R (core.num.U64.wrapping_add t 3432#u64)) (hsc : R (scA t)) (hiq : R (inqA t)) :
    fastpath.schedulable_here st y t = fastpath.schedulable_here st x t := by
  have e1 : L.mem y (tmA (L := L) y) = L.mem x (tmA (L := L) x) := by
    show L.mem y (L.nodeAt y (L.cpu y) _) = _
    rw [h.node]; exact h.m _ htm
  have e2 : L.mem y (rhA (L := L) y) = L.mem x (rhA (L := L) x) := by
    show L.mem y (L.nodeAt y (L.cpu y) _) = _
    rw [h.node]; exact h.m _ hrh
  have gx := fastpath.schedulable_here.guard (gS := PathObl.guard st R (fun _ => True)) x t hct htm hrh htd hrs hdt hcd haf hdo hsc hiq
  have gy := fastpath.schedulable_here.guard (gS := PathObl.guard st R (fun _ => True)) y t
    (by show R (L.nodeAt y (L.cpu y) _); rw [h.node]; exact hct)
    (by show R (L.nodeAt y (L.cpu y) _); rw [h.node]; exact htm)
    (by show R (L.nodeAt y (L.cpu y) _); rw [h.node]; exact hrh)
    (by rw [e1]; exact htd)
    (by
      rw [e2]; intro h0
      obtain ⟨r1, r2⟩ := hrs h0
      rw [h.m _ r1]; exact ⟨r1, h.rdHead r2⟩)
    (by rw [h.k]; exact hdt) (by rw [h.k]; exact hcd) haf hdo hsc hiq
  rw [← gy, ← gx, here_ag h]

theorem suff_congr {A : Type} {ar : machine.Arch A} (h : Ag st R x y) (a : A) {sc u : U64}
    (hs : RdHead (L := L) R x sc) : sporadic.sufficient st ar y a sc u = sporadic.sufficient st ar x a sc u := by
  have gx := sporadic.sufficient.guard (gS := PathObl.guard st R (fun _ => True)) ar x a sc u hs
  have gy := sporadic.sufficient.guard (gS := PathObl.guard st R (fun _ => True)) ar y a sc u (h.rdHead hs)
  rw [← gy, ← gx, suff_ag h]

theorem lib_congr (h : Ag st R x y) {rcv : Bool} {t sl : U64} (hsl : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok sl)
    (hI : R (core.num.U64.wrapping_add t 3512#u64)) (hR0 : R sl) (hR8 : R (core.num.U64.wrapping_add sl 8#u64)) :
    msg.lookup_ipc_buffer st y rcv t = msg.lookup_ipc_buffer st x rcv t := by
  have gx := msg.lookup_ipc_buffer.guard (gS := PathObl.guard st R (fun _ => True)) (st := st) x rcv t hsl hI hR0 hR8
  have gy := msg.lookup_ipc_buffer.guard (gS := PathObl.guard st R (fun _ => True)) (st := st) y rcv t hsl hI hR0 hR8
  rw [← gy, ← gx, lib_ag h]

theorem cap_congr (h : Ag st R x y) {sl : U64} (h0 : R sl) (h8 : R (core.num.U64.wrapping_add sl 8#u64)) :
    obj.Slot.cap st sl y = obj.Slot.cap st sl x := by
  unfold obj.Slot.cap
  rw [L.read_pair_eq, L.read_pair_eq, h.m _ h0, h.m _ h8]

theorem Ag.wr (hR : ∀ b, R b → Aligned b) (h : Ag st R x y) {a v : U64} (ha : Aligned a) :
    Ag st R (L.wr x a v) (L.wr y a v) := by
  refine ⟨by rw [L.ksb_wr, L.ksb_wr]; exact h.k, by rw [L.cpu_wr, L.cpu_wr]; exact h.c, fun b hb => ?_⟩
  rw [L.mem_wr _ _ _ _ ha (hR b hb), L.mem_wr _ _ _ _ ha (hR b hb), h.m b hb]

/-! ## The walk, backwards -/

/-- A CNode or I/O port cap in a slot of `C` at `s'` was there at `s`. -/
def CapBack (s s' : S) (C : U64 → U64 → Prop) : Prop :=
  ∀ p r m y c, C p r → cspace.mask r = ok m → obj.Slot.cap st (cnSlot p (y &&& m)) s' = ok c →
    ((∃ p' r' gs' g', c = .CNode p' r' gs' g') ∨ ∃ f l z, c = .IoPort f l z) →
    obj.Slot.cap st (cnSlot p (y &&& m)) s = ok c

/-- One step on a CNode cap: the slots' caps that decide it are the same. -/
theorem rab_body_back {s s' : S} {cptr n fuel p r gs g m : U64}
    {w : ControlFlow (capability.Cap × U64 × U64) (core.result.Result cspace.Resolved error.LookupFault)}
    (hm : cspace.mask r = ok m)
    (hR : ∀ z c, obj.Slot.cap st (cnSlot p (z &&& m)) s' = ok c →
      ((∃ p' r' gs' g', c = .CNode p' r' gs' g') ∨
        ∃ bl, w = ControlFlow.done (core.result.Result.Ok { slot := cnSlot p (z &&& m), bits_left := bl })) →
      obj.Slot.cap st (cnSlot p (z &&& m)) s = ok c)
    (h : cspace.resolve_address_bits_loop.body st s' cptr (.CNode p r gs g) n fuel = ok w) :
    cspace.resolve_address_bits_loop.body st s cptr (.CNode p r gs g) n fuel = ok w := by
  unfold cspace.resolve_address_bits_loop.body at h ⊢
  simp only [obj.Slot.index, lift, bind_ok, hm] at h ⊢
  revert h
  repeat' (first
    | (exact fun h => h)
    | (with_reducible refine tr_ite (fun _ => ?_) (fun _ => ?_))
    | (with_reducible_and_instances refine tr_bind_same (fun _ _ => ?_)))
  all_goals
    with_reducible_and_instances refine tr_bind (fun c hc hk => ?_) (fun _ _ hk => hk)
    exact hR _ c hc (by
      cases c <;>
        first
        | exact Or.inl ⟨_, _, _, _, rfl⟩
        | exact Or.inr ⟨_, (ok_inj_ff hk).symm⟩)

theorem rab_loop_back {s s' : S} {cptr : U64} {C : U64 → U64 → Prop} {xr : cspace.Resolved}
    (hb : CapBack (st := st) s s' C) (hx : ∃ f l z, obj.Slot.cap st xr.slot s' = ok (.IoPort f l z))
    (hcl : WalkCl (st := st) s C) :
    ∀ (N : Nat) (cap : capability.Cap) (n fuel : U64),
      fuel.val < N → (∀ p r gs g, cap = .CNode p r gs g → C p r) →
      cspace.resolve_address_bits_loop st cap s' cptr n fuel = ok (.Ok xr) →
      cspace.resolve_address_bits_loop st cap s cptr n fuel = ok (.Ok xr) := by
  intro N
  induction N with
  | zero => intro _ _ _ hf; omega
  | succ N ih =>
    intro cap n fuel hf hc h
    rw [rabLoop_unfold] at h ⊢
    obtain ⟨w, hw, hk⟩ := bind_eq_ok h
    by_cases hcn : ∃ p r gs g, cap = .CNode p r gs g
    · obtain ⟨p, r, gs, g, rfl⟩ := hcn
      obtain ⟨m, hm, -⟩ := spec_ex_fd (P0.cspace.mask.p0 r)
      have hw' : cspace.resolve_address_bits_loop.body st s cptr (.CNode p r gs g) n fuel = ok w := by
        refine rab_body_back hm (fun z c hc' hb' => ?_) hw
        rcases hb' with ⟨p', r', gs', g', rfl⟩ | ⟨bl, rfl⟩
        · exact hb p r m z _ (hc _ _ _ _ rfl) hm hc' (Or.inl ⟨_, _, _, _, rfl⟩)
        · have e := ok_inj_ff hk
          injection e with e
          subst e
          obtain ⟨f, l, v, hv⟩ := hx
          have e2 : c = .IoPort f l v := ok_inj_ff (hc'.symm.trans hv)
          exact hb p r m z _ (hc _ _ _ _ rfl) hm hc' (Or.inr ⟨_, _, _, e2⟩)
      rw [hw']; simp only [bind_ok]
      cases w with
      | done z => exact hk
      | cont v =>
        obtain ⟨m', z, hm', hoff, hlt⟩ := rab_body_cont2 st hw'
        rw [hm] at hm'; cases ok_inj_ff hm'
        exact ih v.1 v.2.1 v.2.2 (by omega)
          (fun p' r' gs' g' e => hcl p r m z p' r' gs' g' (hc _ _ _ _ rfl) hm (e ▸ hoff)) hk
    · have eb : cspace.resolve_address_bits_loop.body st s cptr cap n fuel =
          cspace.resolve_address_bits_loop.body st s' cptr cap n fuel := by
        cases cap <;> first | rfl | exact absurd ⟨_, _, _, _, rfl⟩ hcn
      rw [eb, hw]
      simp only [bind_ok]
      cases w with
      | done z => exact hk
      | cont v =>
        exfalso
        (cases cap <;> (try simp [cspace.resolve_address_bits_loop.body] at hw)) <;>
          exact hcn ⟨_, _, _, _, rfl⟩

theorem lookup_back {s s' : S} {t cptr sl : U64} {C : U64 → U64 → Prop} {xr : cspace.Resolved}
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl)
    (e0 : obj.Slot.cap st sl s' = obj.Slot.cap st sl s)
    (hb : CapBack (st := st) s s' C) (hx : ∃ f l z, obj.Slot.cap st xr.slot s' = ok (.IoPort f l z))
    (hcl : WalkCl (st := st) s C) (hroot : ∀ p r gs g, obj.Slot.cap st sl s = ok (.CNode p r gs g) → C p r)
    (h : cspace.lookup_slot st s' t cptr = ok (.Ok xr)) : cspace.lookup_slot st s t cptr = ok (.Ok xr) := by
  unfold cspace.lookup_slot at h ⊢
  rw [hsl] at h ⊢; simp only [bind_ok] at h ⊢
  rw [e0] at h
  obtain ⟨root, er, h⟩ := bind_eq_ok h
  rw [er]; simp only [bind_ok]
  exact rab_loop_back hb hx hcl 66 root _ 65#u64 (by simp) (fun p r gs g e => hroot p r gs g (e ▸ er)) h

/-- A passing `invocation_ok` passes at the state the walk and the reads agree with. -/
theorem inv_back {s s' : S} {t cptr sl : U64} {info : msginfo.MessageInfo} {C : U64 → U64 → Prop}
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl)
    (e0 : obj.Slot.cap st sl s' = obj.Slot.cap st sl s)
    (hb : CapBack (st := st) s s' C)
    (hx : ∀ x f l z, cspace.lookup_slot st s t cptr = ok (.Ok x) → obj.Slot.cap st x.slot s' = ok (.IoPort f l z) →
      obj.Slot.cap st x.slot s = ok (.IoPort f l z))
    (hcl : WalkCl (st := st) s C) (hroot : ∀ p r gs g, obj.Slot.cap st sl s = ok (.CNode p r gs g) → C p r)
    (hbuf : msg.lookup_ipc_buffer st s' false t = msg.lookup_ipc_buffer st s false t)
    (hr10 : L.mem s' (regA t layout.reg.R10) = L.mem s (regA t layout.reg.R10))
    (h : ioport.invocation_ok st s' t cptr info = ok true) : ioport.invocation_ok st s t cptr info = ok true := by
  obtain ⟨r1, f, l, z, -, -, -, -, -, hl, hc, -⟩ := inv_true h
  have hl2 := lookup_back hsl e0 hb ⟨f, l, z, hc⟩ hcl hroot hl
  have hc2 := hx r1 f l z hl2 hc
  have n0 := zero_lt_nmr
  have earg : ∀ bf, msg.syscall_arg st s' t bf 0#u64 = msg.syscall_arg st s t bf 0#u64 := by
    intro bf
    unfold msg.syscall_arg
    rw [if_pos n0, if_pos n0, msg_register_zero]
    simp only [bind_ok]
    rw [reg_ok, reg_ok, hr10]
  unfold ioport.invocation_ok at h ⊢
  revert h
  refine tr_bind_same (fun size _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_bind (fun res hres _ => by rw [hl] at hres; rw [hl2]; exact hres) (fun res hres => ?_)
  rw [hl] at hres
  cases ok_inj_ff hres
  dsimp only
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_bind (fun c hc' _ => by rw [hc] at hc'; rw [hc2]; exact hc') (fun c hc' => ?_)
  rw [hc] at hc'
  cases ok_inj_ff hc'
  dsimp only
  rw [hbuf]
  simp only [earg]
  exact fun h => h

/-! ## The prefix -/

/-- `update_timestamp` with one domain. -/
theorem upd_eq {A : Type} {ar : machine.Arch A} {s s' : S} {a a' : A} (h : sched.update_timestamp st ar s a = ok (s', a')) :
    ∃ now, ar.now a = ok (now, a') ∧
      s' = L.wr (L.wr s (ctA (L := L) s) now) (cnA (L := L) s)
        (core.num.U64.wrapping_add (L.mem (L.wr s (ctA (L := L) s) now) (cnA (L := L) s))
          (core.num.U64.wrapping_sub now (L.mem s (ctA (L := L) s)))) := by
  unfold sched.update_timestamp at h
  rw [cur_time_ok] at h
  simp only [bind_ok] at h
  obtain ⟨⟨now, a1⟩, hn, h⟩ := bind_eq_ok h
  simp only [uncurry_apply_pair, L.cur_cpu_eq, bind_ok, lift] at h
  rw [eq_ok_of_spec (obj.node_set.spec (L := L) s _ _ _)] at h
  simp only [bind_ok] at h
  rw [io_consumed_ok] at h
  simp only [bind_ok] at h
  unfold sched.set_consumed at h
  simp only [L.cur_cpu_eq, bind_ok] at h
  rw [eq_ok_of_spec (obj.node_set.spec (L := L) _ _ _ _)] at h
  simp only [bind_ok] at h
  have hd : ¬ (layout.NUM_DOMAINS > 1#u64) := by simp [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [if_neg hd] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, rfl⟩ := e
  refine ⟨now, hn, ?_⟩
  rw [← e1]
  simp only [nd_wr]

theorem upd_fwd {A : Type} {ar : machine.Arch A} {s : S} {a a' : A} {now : U64} (h : ar.now a = ok (now, a')) :
    sched.update_timestamp st ar s a = ok (L.wr (L.wr s (ctA (L := L) s) now) (cnA (L := L) s)
        (core.num.U64.wrapping_add (L.mem (L.wr s (ctA (L := L) s) now) (cnA (L := L) s))
          (core.num.U64.wrapping_sub now (L.mem s (ctA (L := L) s)))), a') := by
  unfold sched.update_timestamp
  rw [cur_time_ok]
  simp only [bind_ok]
  rw [h]
  simp only [bind_ok, uncurry_apply_pair, L.cur_cpu_eq, lift]
  rw [eq_ok_of_spec (obj.node_set.spec (L := L) s _ _ _)]
  simp only [bind_ok]
  rw [io_consumed_ok]
  simp only [bind_ok]
  unfold sched.set_consumed
  simp only [L.cur_cpu_eq, bind_ok]
  rw [eq_ok_of_spec (obj.node_set.spec (L := L) _ _ _ _)]
  simp only [bind_ok]
  have hd : ¬ (layout.NUM_DOMAINS > 1#u64) := by simp [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  rw [if_neg hd]
  simp only [nd_wr]

set_option maxHeartbeats 1000000 in
/-- **All checks passing, a run that returns is accepted.** -/
theorem ioTail_true {A : Type} {ar : machine.Arch A} {s s1 s2 : S} {a a1 : A} {t nx : U64}
    {info : msginfo.MessageInfo} {number : I64} {r : Bool × S × A} (hb : ioport.is_port_label info.label = ok true)
    (hnx : obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx)
    (hs1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1)
    (hu : sched.update_timestamp st ar s1 a = ok (s2, a1))
    (hac : sched.action st s2 = ok sched.ACTION_RESUME_CURRENT) (hy : obj.Tcb.yield_to st t s2 = ok 0#u64)
    (hx : info.extra_caps = 0#u64)
    (hi : ioport.invocation_ok st s2 t (L.mem s2 (regA t layout.reg.CAP)) info = ok true)
    (hsf : sporadic.sufficient st ar s2 a1 (L.cscW s2) (L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED)) = ok true)
    (hh : fastpath.schedulable_here st s2 t = ok true)
    (h : ioTail st ar s a t info number = ok r) : r.1 = true := by
  have c0 : ∀ v : U64, ¬ ((v != v) = true) := fun v => by simp
  unfold ioTail at h
  rw [hb] at h; simp only [bind_ok] at h
  simp only [if_true, ↓reduceIte] at h
  rw [hnx] at h; simp only [bind_ok, lift] at h
  rw [hs1] at h; simp only [bind_ok] at h
  rw [hu] at h; simp only [bind_ok, uncurry_apply_pair] at h
  rw [reg_ok] at h; simp only [bind_ok] at h
  rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2)] at h; simp only [bind_ok] at h
  rw [hac] at h; simp only [bind_ok] at h
  rw [if_neg (c0 _), hy] at h; simp only [bind_ok] at h
  rw [if_neg (c0 _), hx] at h
  rw [if_neg (c0 _), hi] at h; simp only [bind_ok] at h
  simp only [if_true, ↓reduceIte] at h
  rw [io_consumed_ok] at h; simp only [bind_ok] at h
  unfold LawfulStore.cscW at hsf
  rw [hsf] at h; simp only [bind_ok] at h
  simp only [if_true, ↓reduceIte] at h
  rw [hh] at h; simp only [bind_ok] at h
  simp only [if_true, ↓reduceIte] at h
  obtain ⟨⟨r1, s3, a2⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨r2, s4, a3⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨s5, a4⟩, -, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]

end

end Fl4Proofs.P2.PathObl

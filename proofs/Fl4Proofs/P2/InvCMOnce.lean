/-
# P2 (line slhuf, gen 10): the Copy / Mint path's program premise (`IsProgOn`, `NoZero`, `ReadOnce`)

On top of hpzg gen 6's pruned body (`P2/InvProgSrc.lean`: `decCNG`, the CNode arm of `decode_invocation`, which
covers every `cnode.decode` label, Copy and Mint among them; trees `R.invBodyG`, `P2/ProgGenCd*.lean`):

* `IsProgOn` / `NoZero`: hpzg's `inv_isProgOn` (side condition `hSC : InvSlotCN` [J], the plan's slot holds a
  CNode cap: a Copy / Mint invocation is on a CNode cap as a Delete one is, so no other side condition is
  needed) and `inv_noZero`; `IsProgOn` carried to `InvCMRS`'s alternatives by `IsProgOn.mono` / `altOf_cm_io`.
  `InvRoW` (declining entries): hpzg's `invRoW_of` (`hSeen` [J]).
* `InvCMRoAccW` (accepting entries) in three steps:
  - `invCMRoAccW_of_ent`: at an alternative from the entry (`SlOnceL.once_agree`: the accepted run on
    `guard st (InvCMRS s) (InvCMWS s)` (`hacc`) reads the same words with the same values at `s` and `s'`);
  - **`invCM_entOnce`**: at the entry, the walk of `R.invBodyG` (current thread, `MSG_INFO`, flags, the label
    check, `NEXT_IP`, the `FAULT_IP` write, `update_timestamp`, `cur_sc`, `action`, `yield_to`, `consumed`,
    `sufficient`, `schedulable_here`, `still_holds`, the IPC buffer lookup, the length, the invoked slot's cap):
    every read is an `IoRS s` word (no user word), so nothing racy, the touched set stays empty, and `Once`
    reduces to `Once` of the decode onward (`invCMRest`) from the post-check state;
  - the decode onward is the premise **`InvCMDecOnceW`** [W]: `decCNG` → `cnode.decode` → `decode_copy` →
    `copied_cap` (user reads `buf + 40`, Mint also `buf + 48`), `invPostG` (`reply_error`: user read `buf + 56`
    after writes of the error MRs, at most up to `buf + 40`), `after_invocation`, `finish`.
* **`inv_pathsKCM2`** (and `_startAt`): `inv_pathsKCM` with `hpz` discharged up to `InvCMDecOnceW`, and `hdec` /
  `hra` from stpost's `invDecW_of` / `invRaW_of` (as `inv_pathsKD`).

Why the decode onward is left: its walk needs a guard lemma for each call of the Copy / Mint decode block
(`lookup_target_slot`, `ensure_empty_slot`, `lookup_source_slot`, `derive_cap`, `insert_with_cap`,
`reply_error`; none exists on this base), the same lemmas `InvCMBlkW` needs (`P2/InvCM.lean`); with them the walk is
`once_gstep` per call plus the three user reads.

Premises (tagged in their docstrings): `InvCMDecOnceW` [W]; passed through: `hSC` [J], `hSeen` [J], `hps` [J],
`hacc` [W] (`invCMAccW_of` ← `InvCMBlkW` [W]), `hmv` [W], `huf` [J], `hm` [P].
-/
import Fl4Proofs.P2.InvCM
import Fl4Proofs.P2.InvLPG
import Fl4Proofs.P2.IoOnce
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-! ## The premises -/

section prem
variable {S : Type}

/-- The tree of the frame-cap invocation body from the decode on (the continuation of the invoked slot's cap read
in `R.invTailG`). -/
noncomputable def invCMRest (t : U64) (info : msginfo.MessageInfo) (p : localinv.Plan) (buf length : U64)
    (cap : capability.Cap) : SProg Bool :=
  (R.decCNG info.label length p.slot cap true true true false buf p.extra).sbind fun r =>
    (R.invPostG t r).sbind fun r1 =>
      (R.syscall.after_invocation r1).sbind fun _ =>
        R.syscall.finish.sbind fun _ => SProg.ret true


end prem

section prem2
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- [W] **`ReadOnce` of an accepted Copy / Mint run at its entry**, of the tree `q`. -/
def InvCMRoEntW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64)
    (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop) (q : SProg Bool) (P : S → Prop) : Prop :=
  ∀ s (a : A) r, P s → (∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)) →
    interp st ar q s a = ok r → Once st ar (InvCMRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ q s a

/-- [W] **`Once` of an accepted Copy / Mint run from the decode on**: at an accepted entry `s`, after the prefix
and the checks (`InvChk`), the IPC buffer lookup (`buf`) and the invoked slot's cap read (`cap`), the tree
`invCMRest` (`decCNG` → `cnode.decode` → `decode_copy` → `copied_cap`, reading the caller's buffer words
`buf + 40` / `buf + 48`; `invPostG` (`reply_error`: `buf + 56`); `after_invocation`; `finish`) reads each racy
word (a user word, or a kernel word outside `IoRS s` not written before) once, from the empty touched set and
any written-word set. -/
def InvCMDecOnceW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64)
    (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap (r' : Bool × S × A), P s →
    (∃ s' a', syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) →
    msg.msg_info st s (L.curW s) = ok info → InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf → obj.Slot.cap st p.slot s2 = ok cap →
    interp st ar (invCMRest (L.curW s) info p buf length cap) s2 a1 = ok r' →
    ∀ Wd, Once st ar (InvCMRS (st := st) K Locks s) (· ∈ K.user) Wd ∅ (invCMRest (L.curW s) info p buf length cap)
      s2 a1

end prem2

/-! ## From the entry to the alternatives -/

section agree
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A} {number : I64} {p : localinv.Plan}

/-- **`InvCMRoAccW` from `ReadOnce` at the entry** (`once_agree` over the accepted run on the guarded store). -/
theorem invCMRoAccW_of_ent {P : S → Prop} {q : SProg Bool} (hm : E2E.MasksWr st)
    (hacc : InvCMAccW st ar number p K Locks P)
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (InvCMRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q) (hz : NoZero q)
    (hent : InvCMRoEntW st ar number p K Locks q P) :
    InvCMRoAccW st ar number p K Locks m0 q P := by
  intro s s' a r hE hac Al _
  obtain ⟨s1, a1, h0⟩ := hac
  have hg := hacc s a s1 a1 hE h0
  rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
  have h0' : interp st ar q s a = ok (true, s1, a1) := by
    rw [← inv_hp hp (Narrow.self st) (AltOf.pre hE) a]; exact h0
  exact once_agree hm (fun w hw => hw.1) (fun w hw => hw.1) q hz s s' a _ ∅ ∅ Al.ksb Al.cpu Al.masks Al.read hg
    (hent s a _ hE ⟨s1, a1, h0⟩ h0')

end agree

/-! ## The walk at the entry -/

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- **The post-prefix facts of an accepted run** (`InvMid` for `IoRS s`), as in `inv_acc_gen`. -/
theorem invCM_hmid (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {s s' : S} {a a' : A}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    ∀ info nx s1 s2 a1, msg.msg_info st s (L.curW s) = ok info →
      obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) →
      InvMid (L := L) (IoRS (st := st) K Locks s) s s2 (L.curW s) := by
  obtain ⟨info, -, -, -, ht⟩ := handle_inv_inv h
  obtain ⟨nx0, s10, s20, a10, -, -, es10, eu0, -, -, -, hh0, -⟩ := invTail_inv ht
  have hsc2 := (here_facts hh0).sc
  have w := prefix_writes ar hA P.tp P.np P.cT es10 eu0
  have e1 : L.mem s20 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (field_aligned P.tA (by simp) (by simp)) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s := (P.hcsc (by rw [← e1]; exact hsc2)).symm
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  intro info nx s1 s2 a1 emi enx es1 eu
  have M2 := io_hmid' (a := a) ar hA hq.tcbs (hq.nodes _ hq.cur) hq.cur hq.curT
    (P.mid (Locks := Locks) (P.ioWr (Locks := Locks)) hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2) (hd hX.cur)
    (fun h0 => ⟨(bxi_rh P.bxi h0).1, hd (bxi_rh P.bxi h0).2.1⟩) info nx _ s2 a1 emi enx es1 eu
  exact ⟨M2.k, M2.c, M2.cur, M2.yld, M2.rh, M2.td, M2.rs, M2.dt, M2.cd, M2.af, M2.dom, M2.iok.1.sc, M2.iok.1.inq,
    M2.iok.1.ib, M2.iok.1.bs⟩

set_option maxHeartbeats 8000000 in
/-- **`ReadOnce` of an accepted run at its entry, up to the decode** (module docstring): the walk of
`R.invBodyG` from the entry; `hdo` [W] for the decode onward, `hSeen` [J], `hps` [J]. -/
theorem invCM_entOnce (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hdo : InvCMDecOnceW st ar number p K Locks P) :
    InvCMRoEntW st ar number p K Locks (R.invBodyG number p) P := by
  intro s a r hE hac h
  obtain ⟨sA, aA, h0⟩ := hac
  have P := hPE s hE
  have hR0 : ∀ q, IoRS (st := st) K Locks s q → InvCMRS (st := st) K Locks s q ∧ q ∉ K.user :=
    fun q hq => ⟨ioRS_cm hq, hq.2.1⟩
  have hW0 : ∀ q, IoRS (st := st) K Locks s q → q ∉ K.user := fun q hq => hq.2.1
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  unfold R.invBodyG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the current thread
  refine once_gstep hR0 hW0 (R.sched.cur_thread_nz) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) s nC]
    exact h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  rw [cur_thread_ok] at et
  have et' : t = L.curW s := (ok_inj_ff et).symm
  subst et'
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `MSG_INFO`
  refine once_gstep hR0 hW0 (R.msg.msg_info_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd2 _ => ?_)
  · rw [R.msg.msg_info_eq] at h1 ⊢
    rw [msg.msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) s _
      (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1]
    exact h1
  replace h := hk
  rw [R.msg.msg_info_eq] at h1
  obtain ⟨info, emi, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the flags
  refine once_gstep hR0 hW0 (R.obj.Tcb.flags_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd3 _ => ?_)
  · rw [R.obj.Tcb.flags_eq] at h1 ⊢
    rw [obj.Tcb.flags.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ s
      (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.flags_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  -- the tail
  unfold R.invTailG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun b _ h => ?_)
  cases b
  · rw [if_neg Bool.false_ne_true]; simp only [Once]
  rw [if_pos rfl] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `NEXT_IP`
  refine once_gstep hR0 hW0 (R.obj.Tcb.reg_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd4 _ => ?_)
  · rw [R.obj.Tcb.reg_eq] at h1 ⊢
    rw [obj.Tcb.reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ s _
      (P.reg (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.reg_eq] at h1
  obtain ⟨nx, enx, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the `FAULT_IP` write
  refine once_gstep hR0 hW0 (R.obj.Tcb.set_reg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd5 _ => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ s
      _ _ (P.reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x1, es1, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have ex1 : x1 = L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have hNx1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) o) := fun o h1 h2 => by
    rw [ex1, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]; exact (P.nd (Locks := Locks) o h1 h2).1
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `update_timestamp`
  have hct : IoRS (st := st) K Locks s (ctA (L := L) x1) := by
    show IoRS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CUR_TIME)
    exact hNx1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have hcn : IoRS (st := st) K Locks s (cnA (L := L) x1) := by
    show IoRS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CONSUMED)
    exact hNx1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  refine once_gstep hR0 hW0 (R.sched.update_timestamp_nz) h (fun r h1 => ?_) (fun r h1 hk Wd6 _ => ?_)
  · rw [R.sched.update_timestamp_eq] at h1 ⊢
    rw [sched.update_timestamp.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      ar x1 a hct hct hcn hcn]
    exact h1
  replace h := hk
  rw [R.sched.update_timestamp_eq] at h1
  obtain ⟨⟨x2, a1⟩, eu, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have M := invCM_hmid (Locks := Locks) hA P h0 info nx x1 x2 a1 emi enx es1 eu
  have nd2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (L.nodeAt x2 (L.cpu x2) o) := fun o h1 h2 => by
    rw [M.c, nodeAt_of_ksb M.k]; exact (P.nd (Locks := Locks) o h1 h2).1
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `cur_sc`
  refine once_gstep hR0 hW0 (R.sched.cur_sc_nz) h (fun r h1 => ?_) (fun r h1 hk Wd7 _ => ?_)
  · rw [R.sched.cur_sc_eq] at h1 ⊢
    rw [sched.cur_sc.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x2
      (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
    exact h1
  replace h := hk
  rw [R.sched.cur_sc_eq] at h1
  obtain ⟨csc, ecs, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have ec : csc = L.cscW x2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecs; exact (ok_inj_ff ecs).symm
  subst ec
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `action`
  refine once_gstep hR0 hW0 (R.sched.action_nz) h (fun r h1 => ?_) (fun r h1 hk Wd8 _ => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x2
      (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨i3, ei3, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun hi3 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `yield_to`
  refine once_gstep hR0 hW0 (R.obj.Tcb.yield_to_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd9 _ => ?_)
  · rw [R.obj.Tcb.yield_to_eq] at h1 ⊢
    rw [obj.Tcb.yield_to.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ x2
      M.yld]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.yield_to_eq] at h1
  obtain ⟨i4, ei4, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun hi4 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `consumed`, `sufficient`
  refine once_gstep hR0 hW0 (R.sched.consumed_nz) h (fun r h1 => ?_) (fun r h1 hk Wd10 _ => ?_)
  · rw [R.sched.consumed_eq] at h1 ⊢
    rw [sched.consumed.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x2
      (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    exact h1
  replace h := hk
  rw [R.sched.consumed_eq] at h1
  obtain ⟨i5, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.sporadic.sufficient_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd11 _ => ?_)
  · rw [R.sporadic.sufficient_eq] at h1 ⊢
    rw [sporadic.sufficient.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      ar x2 a1 _ i5 M.rh]
    exact h1
  replace h := hk
  rw [R.sporadic.sufficient_eq] at h1
  obtain ⟨b1, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ h => ?_) (fun _ _ => by simp only [Once])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `schedulable_here`
  have htm : IoRS (st := st) K Locks s (tmA (L := L) x2) := by
    show IoRS (st := st) K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.TIMER_MIN)
    exact nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have hrh : IoRS (st := st) K Locks s (rhA (L := L) x2) := by
    show IoRS (st := st) K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.RELEASE_HEAD)
    exact nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have hct2 : IoRS (st := st) K Locks s (ctA (L := L) x2) := by
    show IoRS (st := st) K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.CUR_TIME)
    exact nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  refine once_gstep hR0 hW0 (R.fastpath.schedulable_here_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd12 _ => ?_)
  · rw [R.fastpath.schedulable_here_eq] at h1 ⊢
    rw [fastpath.schedulable_here.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s)
      (IoRS (st := st) K Locks s)) x2 _ hct2 htm hrh M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
    exact h1
  replace h := hk
  rw [R.fastpath.schedulable_here_eq] at h1
  obtain ⟨b2, eb2, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun hb2 h => ?_) (fun _ _ => by simp only [Once])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `still_holds`
  refine once_gstep hR0 hW0 (R.localinv.Plan.still_holds_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd13 _ => ?_)
  · rw [R.localinv.Plan.still_holds_eq] at h1 ⊢
    rw [still_holds_guard p x2 (fun w hw => hSeen s hE w hw)]
    exact h1
  replace h := hk
  rw [R.localinv.Plan.still_holds_eq] at h1
  obtain ⟨b3, eb3, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun hb3 h => ?_) (fun _ _ => by simp only [Once])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the IPC buffer
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
  refine once_gstep hR0 hW0 (R.msg.lookup_ipc_buffer_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd14 _ => ?_)
  · rw [R.msg.lookup_ipc_buffer_eq] at h1 ⊢
    rw [msg.lookup_ipc_buffer.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      x2 false (L.curW s) hbsl M.ib (M.bs _ hbsl).1 (M.bs _ hbsl).2]
    exact h1
  replace h := hk
  rw [R.msg.lookup_ipc_buffer_eq] at h1
  obtain ⟨buf, ebuf, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  -- the length
  simp only [SProg.blk, ite_ret, SProg.sbind] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the invoked slot's cap
  refine once_gstep hR0 hW0 (R.obj.Slot.cap_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd15 _ => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      p.slot x2 (hps s hE).1 (hps s hE).2]
    exact h1
  rw [R.obj.Slot.cap_eq] at h1
  obtain ⟨cap, ecap, rfl⟩ := bind_shape h1
  have hR := hk
  dsimp only at hR ⊢
  -- the decode onward
  simp only [bne_iff_ne, ne_eq, not_not] at hi3 hi4
  rw [hi3] at ei3
  rw [hi4] at ei4
  rw [hb2] at eb2
  rw [hb3] at eb3
  exact hdo s a info nx x1 x2 a1 buf _ cap _ hE ⟨sA, aA, h0⟩ emi ⟨enx, es1, eu, ei3, ei4, eb2, eb3⟩ ebuf ecap hR Wd15

end walk

/-! ## The program premise and the path -/

section path
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type}

/-- **The program premise of `inv_localPathCM`** for the tree `R.invBodyG number p`: `IsProgOn` (hpzg's
`inv_isProgOn`, [J] `hSC`), `NoZero`, `InvRoW` (hpzg's `invRoW_of`, [J] `hSeen`), `InvCMRoAccW`
(`invCMRoAccW_of_ent` + `invCM_entOnce`: `hacc` [W], [J] `hps`, [W] `hdo`). -/
theorem inv_hpzCM {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) {number : I64}
    {p : localinv.Plan} {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSC : InvSlotCN st K p P)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hacc : InvCMAccW st ar number p K Locks P) (hdo : InvCMDecOnceW st ar number p K Locks P) :
    ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m0 q P ∧ InvCMRoAccW st ar number p K Locks m0 q P := by
  have hp := inv_isProgOn (Locks := Locks) (m0 := m0) hA hPE hSC (inv_isProg S number p)
  exact ⟨R.invBodyG number p, hp, inv_noZero number p, invRoW_of hA hPE hSeen hp (inv_noZero number p),
    invCMRoAccW_of_ent hm hacc (hp.mono fun _ hy => altOf_cm_io hy) (inv_noZero number p)
      (invCM_entOnce hA hPE hSeen hps hdo)⟩

/-- (slhuf gen 10) **The Copy / Mint local path at chain states, program premise discharged**: `inv_pathsKCM` with
`hpz` from `inv_hpzCM` and `hdec` / `hra` from `invDecW_of` / `invRaW_of`. Premises: `hA`, `hm` [P], `Q`, `hPE`,
`hacc` [W] (`invCMAccW_of` ← `InvCMBlkW` [W]), `hSeen` [J] (`InvSeenRS`), `hps` [J], `hmv` [W], `huf` [J], `hSC`
[J] (`InvSlotCNK`), `hdo` [W] (`InvCMDecOnceW`). -/
noncomputable def inv_pathsKCM2 (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hacc : ∀ K m, InvCMAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hSeen : InvSeenRS st Locks p Q)
    (hps : ∀ K m s, SlJAt (L := L) K s → Q K m s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hmv : ∀ K m, InvMoveW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hSC : InvSlotCNK st p Q)
    (hdo : ∀ K m, InvCMDecOnceW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s)) :
    E2E.Paths Unit :=
  inv_pathsKCM ar hA number p hm Q hPE hacc
    (fun K m => invDecW_of hA (fun _ h => h.1.regionOK) (fun _ h => h.1.ioLayA)
      (fun s h => hPE K m s h.1 h.2) (fun s h => hSeen K m s h.1 h.2)) hmv
    (fun K m => invRaW_of hA (fun s h => hPE K m s h.1 h.2) (fun s h => hSeen K m s h.1 h.2)) huf
    (fun K m => inv_hpzCM hA hm (fun s h => hPE K m s h.1 h.2) (hSC K m) (fun s h => hSeen K m s h.1 h.2)
      (fun s h => hps K m s h.1 h.2) (hacc K m) (hdo K m))

/-- (slhuf gen 10) **`StartAt` of `inv_pathsKCM2` at a chain state** (as `inv_pathsK_startAt`). -/
theorem inv_pathsKCM2_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hacc : ∀ K m, InvCMAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hSeen : InvSeenRS st Locks p Q)
    (hps : ∀ K m s, SlJAt (L := L) K s → Q K m s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hmv : ∀ K m, InvMoveW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hSC : InvSlotCNK st p Q)
    (hdo : ∀ K m, InvCMDecOnceW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {A3 : Type} {Rc : S → A3 → Fl4Spec.State Unit → Prop}
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), Rc σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : Rc σ a3 τ) (a : A) (hq : Q K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (inv_pathsKCM2 ar hA number p hm Q hPE hacc hSeen hps hmv huf hSC hdo () K m hK hU) c hs μ
      ((inv_pathsKCM2 ar hA number p hm Q hPE hacc hSeen hps hmv huf hSC hdo () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨h7 σ a3 τ hR, hq⟩, hc, hl, hμ, rfl⟩

end path

end Fl4Proofs.P2.PathObl

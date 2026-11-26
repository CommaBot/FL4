/-
# P2: `ReadOnce` of the VM ReplyRecv tree, proved by walking it (line hpzg, gen 5)

`rr_localPathG` / `rr_localPathJG` (`P2/ProgGenLvLP.lean`) left `hro` [W]: at an entry where the reply's receiver
`u` (its `TCB` word) is homed on another core (`RrRep`), the runs of `R.syscall.handle_reply_recv_vm_local (rptr, ep)`
from the alternatives read each racy word once. The two racy words are `u`'s `STATE` and `FAULT_TYPE` (outside
`IoRS s`: home-owned on another core; `rr_dec_tr`'s `hrep`). Walk (`P2/OnceTree.lean`, as `P2/VmOnce.lean`):

* the prefix (`cur_thread`, flags, `NEXT_IP`, the `FAULT_IP` write, `update_timestamp`, `cur_sc`, `consumed`,
  `sufficient`) and the fast path up to `Reply.tcb` on `guard (IoRS s) (IoRS s)` (`rr_mid`: `rr_dec_tr`'s facts at
  the state after the prefix: `RrDR (IoRS s)`, the receiver word and its `AFFINITY` as at `s`);
* **one** read of `u.STATE` (nothing touched before), **one** read of `u.FAULT_TYPE` (another word: offsets 3328 /
  3376), then `Reply.next` / `next_is_head` / `u.SC` on `IoRS s`, and `schedulable_here u` answers `false` (`u`'s
  `AFFINITY`, in `IoRS s`, is not this core): the run ends with `false`, reading neither word again.

* `rr_mid`, `rr_once_alt`: an alternative's run is `Once` (no acceptance assumption needed);
* **`rr_hro`** / **`rr_hroJ`**: the `hro` premises of `rr_localPathG` / `rr_localPathJG`;
* **`rr_localPathG2`** / **`rr_localPathJG2`**: the VM ReplyRecv local path with `IsProg`, `NoZero` and `ReadOnce`
  all discharged. Premises: `rr_localPath`'s / `rr_localPathJ`'s minus `hpz`.
-/
import Fl4Proofs.P2.ProgGenLvLP
import Fl4Proofs.P2.VmOnce
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout fld own GateField TimerField GField RegionOK oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **The facts at the state after the prefix** of an alternative's run (`rr_dec_tr`'s, for `IoRS s`). -/
theorem rr_mid (hA : P0.ArchTotal ar) {rptr ep : U64}
    (E : VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s)
    {x : S} (G : Ag st (IoRS (st := st) K Locks s) s x) {a : A} {v : U64} {X2 : S} {a2 : A}
    (eu' : sched.update_timestamp st ar (L.wr x (regA (L.curW s) layout.reg.FAULT_IP) v) a = ok (X2, a2)) :
    (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → IoRS (st := st) K Locks s (L.nodeAt X2 (L.cpu X2) o)) ∧
      RdHead (L := L) (IoRS (st := st) K Locks s) X2 (L.cscW X2) ∧
      RrDR (L := L) (IoRS (st := st) K Locks s) X2 (L.curW s) rptr ep ∧
      L.mem X2 (rTcbA rptr) = L.mem s (rTcbA rptr) ∧ L.cpu X2 = L.cpu s ∧
      (L.mem s (rTcbA rptr) ≠ 0#u64 →
        L.mem X2 (affA (L.mem s (rTcbA rptr))) = L.mem s (affA (L.mem s (rTcbA rptr)))) := by
  have Q := E.1
  have P := Q.base
  have hN := P.np
  have hT := P.tp
  have hcT := P.cT
  have rT := (P.nd (Locks := Locks) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME])
    (by simp [layout.node.CUR_TIME])).1
  have rN := (P.nd (Locks := Locks) layout.node.CONSUMED (by simp [layout.node.CONSUMED])
    (by simp [layout.node.CONSUMED])).1
  obtain ⟨k, hk, ek⟩ := fip_eqV (L := L) P.tA
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := by
    rw [ek]; exact field_aligned P.tA (by omega) (by omega)
  obtain ⟨⟨n, a3⟩, hn3, -⟩ := spec_ex_fd (hA.now a)
  have hN1 : NodePlaced st T (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)
      (L.cpu (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)) := by
    rw [LawfulStore.cpu_wr]; exact hN.wr
  have eu := update_timestamp_ok ar hN1 hn3
  have G0 := G.wr (fun _ hb => hb.1) (a := regA (L.curW s) layout.reg.FAULT_IP) (v := v) aF
  obtain ⟨-, G1⟩ := vm_ag_upd (fun _ hb => hb.1) G0 (by rw [ctA_wr]; exact rT) (by rw [cnA_wr]; exact rN) eu eu'
  replace G1 : Ag st (IoRS (st := st) K Locks s) (rrX (L := L) s v n) X2 := G1
  have D := rr_dr Q E.2.1 E.2.2.1 v n
  have ecsc : L.cscW X2 = L.cscW (rrX (L := L) s v n) := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [G1.node]; exact G1.m _ (D.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
  have hs := G1.rdHead (rr_suf (Locks := Locks) P v n)
  rw [← ecsc] at hs
  obtain ⟨eRt, hRtT⟩ := rr_uX P E.2.1 v n
  refine ⟨fun o ho h8 => by rw [G1.node]; exact D.nd o ho h8, hs, D.alt G1 (fun _ hb => hb),
    by rw [G1.m _ D.rRt, eRt], by rw [G1.c, rrX_cpu], fun hu0 => ?_⟩
  have huT := hRtT hu0
  have gA := (D.uG _ eRt hu0).2.1
  have ea : L.mem (rrX (L := L) s v n) (affA (L.mem s (rTcbA rptr))) = L.mem s (affA (L.mem s (rTcbA rptr))) :=
    rrX_tcb hN hT hcT v n huT (Kx := 3520#u64) (by simp) (by simp) (fun _ => by simp)
  rw [G1.m _ gA, ea]

/-- `u.FAULT_TYPE` and `u.STATE` are different words. -/
theorem ft_ne_st (u : U64) :
    core.num.U64.wrapping_add u 3376#u64 ≠ core.num.U64.wrapping_add u layout.tcb.STATE := by
  intro e
  have e' := congrArg UScalar.val e
  have hb : u.val < 2 ^ 64 := by scalar_tac
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, UScalar.size, st_val] at e' <;> omega

set_option maxHeartbeats 4000000 in
/-- **An alternative's run of the VM ReplyRecv tree reads each racy word once** when the receiver is homed on
another core (module docstring). -/
theorem rr_once_alt (hA : P0.ArchTotal ar) {rptr ep : U64}
    (E : VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s) {b0 : U64} (hrem : RrRep st rptr s b0)
    {x : S} (G : Ag st (IoRS (st := st) K Locks s) s x) {a : A} {r' : Bool × S × A}
    (h' : interp st ar (R.syscall.handle_reply_recv_vm_local (rptr, ep)) x a = ok r') :
    Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_reply_recv_vm_local (rptr, ep)) x a := by
  obtain ⟨hu0, haffs, -⟩ := hrem
  have hU : ∀ q, IoRS (st := st) K Locks s q → q ∉ K.user := fun q hq => hq.2.1
  have hR0 : ∀ q, IoRS (st := st) K Locks s q → IoRS (st := st) K Locks s q ∧ q ∉ K.user :=
    fun q hq => ⟨hq, hq.2.1⟩
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
  have hct : IoRS (st := st) K Locks s (ctA (L := L) x) := by
    show IoRS (st := st) K Locks s (L.nodeAt x (L.cpu x) layout.node.CUR_TIME); rw [G.node]; exact rT
  have hcn : IoRS (st := st) K Locks s (cnA (L := L) x) := by
    show IoRS (st := st) K Locks s (L.nodeAt x (L.cpu x) layout.node.CONSUMED); rw [G.node]; exact rN
  have rF := (P.reg (Locks := Locks) (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])).1
  have rNI := (P.reg (Locks := Locks) (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])).1
  have rFl := (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    (by simp [TimerField])).1
  unfold R.syscall.handle_reply_recv_vm_local at h' ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h' ⊢
  -- cur_thread
  refine once_step hR0 hU (R.sched.cur_thread_nz) h' (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x
      (by rw [G.node]; exact nC)]
    exact h1
  replace h2 := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  rw [cur_thread_ok] at et
  have et' : t = L.curW s := by rw [← hcur]; exact (ok_inj_ff et).symm
  subst et'
  by_cases hd : (layout.NUM_DOMAINS != 1#u64) = true
  · rw [if_pos hd]; simp only [Once]
  rw [if_neg hd] at h2 ⊢
  -- flags
  refine once_step hR0 hU (R.obj.Tcb.flags_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Tcb.flags_eq] at h1 ⊢
    rw [obj.Tcb.flags.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      (L.curW s) x rFl]
    exact h1
  replace h2 := hk
  rw [R.obj.Tcb.flags_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  try simp only [SProg.sbind] at h2 ⊢
  split
  · simp only [Once]
  rename_i hi
  rw [if_neg hi] at h2
  -- `NEXT_IP`
  refine once_step hR0 hU (R.obj.Tcb.reg_nz _ _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Tcb.reg_eq] at h1 ⊢
    rw [obj.Tcb.reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      (L.curW s) x _ rNI]
    exact h1
  replace h2 := hk
  rw [R.obj.Tcb.reg_eq] at h1
  obtain ⟨nx, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  try simp only [SProg.sbind] at h2 ⊢
  -- the `FAULT_IP` write
  refine once_step hR0 hU (R.obj.Tcb.set_reg_nz _ _ _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      (L.curW s) x _ _ rF]
    exact h1
  replace h2 := hk
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x1, ex1, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  rw [set_reg_ok'] at ex1
  obtain rfl := ok_inj_ff ex1
  -- update_timestamp
  refine once_step hR0 hU (R.sched.update_timestamp_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.update_timestamp_eq] at h1 ⊢
    rw [sched.update_timestamp.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s)
      (IoRS (st := st) K Locks s)) ar _ a (by rw [ctA_wr]; exact hct) (by rw [ctA_wr]; exact hct)
      (by rw [cnA_wr]; exact hcn) (by rw [cnA_wr]; exact hcn)]
    exact h1
  replace h2 := hk
  rw [R.sched.update_timestamp_eq] at h1
  obtain ⟨⟨X2, a2⟩, eu', rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  obtain ⟨nd2, hs2, D, eRt, ecpu, eaff⟩ := rr_mid hA E G eu'
  -- cur_sc
  refine once_step hR0 hU (R.sched.cur_sc_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.cur_sc_eq] at h1 ⊢
    rw [sched.cur_sc.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) X2
      (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
    exact h1
  replace h2 := hk
  rw [R.sched.cur_sc_eq] at h1
  obtain ⟨csc, ecs, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  have ec : csc = L.cscW X2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecs; exact (ok_inj_ff ecs).symm
  subst ec
  -- consumed
  refine once_step hR0 hU (R.sched.consumed_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.consumed_eq] at h1 ⊢
    rw [sched.consumed.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) X2
      (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    exact h1
  replace h2 := hk
  rw [R.sched.consumed_eq] at h1
  obtain ⟨cu, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  -- sufficient
  refine once_step hR0 hU (R.sporadic.sufficient_nz _ _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sporadic.sufficient_eq] at h1 ⊢
    rw [sporadic.sufficient.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      ar X2 a2 (L.cscW X2) cu hs2]
    exact h1
  replace h2 := hk
  rw [R.sporadic.sufficient_eq] at h1
  obtain ⟨⟨b, a3⟩, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  all_goals (first
    | (rw [if_neg Bool.false_ne_true]; simp only [Once]; done)
    | (rw [if_pos rfl] at h2 ⊢))
  -- the fast path
  unfold R.fastpath_vm.reply_recv_vm_found at h2 ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h2 ⊢
  -- action
  refine once_step hR0 hU (R.sched.action_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) X2
      (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h2 := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨ia, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  by_cases hia : (ia != sched.ACTION_RESUME_CURRENT) = true
  · rw [if_pos hia]; simp only [Once]
  rw [if_neg hia] at h2 ⊢
  -- is_schedulable
  refine once_step hR0 hU (R.sched.is_schedulable_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.is_schedulable_eq] at h1 ⊢
    rw [is_sched_guardC (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) X2
      (L.curW s) D.tSt D.tSc D.tMx D.tIq]
    exact h1
  replace h2 := hk
  rw [R.sched.is_schedulable_eq] at h1
  obtain ⟨bs, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  by_cases hbs : bs = true
  swap
  · rw [if_neg hbs]; simp only [Once]
  rw [if_pos hbs] at h2 ⊢
  -- msg_info
  refine once_step hR0 hU (R.msg.msg_info_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.msg.msg_info_eq] at h1 ⊢
    rw [msg.msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) X2
      (L.curW s) D.tMi]
    exact h1
  replace h2 := hk
  rw [R.msg.msg_info_eq] at h1
  obtain ⟨info, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  by_cases hx1 : (info.extra_caps != 0#u64) = true
  · rw [if_pos hx1]; simp only [Once]
  rw [if_neg hx1] at h2 ⊢
  by_cases hx2 : (info.label != 0#u64) = true
  · rw [if_pos hx2]; simp only [Once]
  rw [if_neg hx2] at h2 ⊢
  -- the receiver
  refine once_step hR0 hU (R.obj.Reply.tcb_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Reply.tcb_eq] at h1 ⊢
    rw [obj.Reply.tcb.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      rptr X2 D.rRt]
    exact h1
  replace h2 := hk
  rw [R.obj.Reply.tcb_eq] at h1
  obtain ⟨u, eu, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  have hu : L.mem X2 (rTcbA rptr) = u := by
    rw [eq_of_spec_fd (obj.Reply.tcb.blk (L := L) X2 rptr)] at eu; exact ok_inj_ff eu
  have hus : L.mem s (rTcbA rptr) = u := by rw [← eRt]; exact hu
  have hu0' : u ≠ 0#u64 := by rw [← hus]; exact hu0
  have haffX : L.mem X2 (affA u) ≠ L.cpu X2 := by
    rw [← hus, eaff hu0, ecpu]; exact haffs
  obtain ⟨gSc, gAf, -, -⟩ := D.uG u hu hu0'
  -- `is_null`
  refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
    (fun r h1 hk Wd _ => ?_)
  replace h2 := hk
  obtain ⟨b1, x2, a4⟩ := r
  obtain ⟨eb1, e1, e2⟩ := interp_liftR_ok h1
  dsimp only at e1 e2 eb1
  subst x2 a4
  try dsimp only at h2 ⊢
  rw [is_null_ok] at eb1
  obtain rfl := ok_inj_ff eb1
  have hb1 : ¬ (decide (u = 0#u64) = true) := by simpa using hu0'
  rw [if_neg hb1] at h2 ⊢
  -- the first racy read: `u.STATE`
  unfold R.obj.Tcb.state at h2 ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.read] at h2 ⊢
  simp only [interp] at h2
  obtain ⟨v0, hv0, h2⟩ := bok.mp h2
  simp only [Once]
  refine ⟨fun _ => Set.notMem_empty _, fun v hv => ?_⟩
  rw [hv0] at hv
  obtain rfl := ok_inj_ff hv
  try dsimp only at h2 ⊢
  by_cases hst : (v0 != sched.TS_BLOCKED_ON_REPLY) = true
  · rw [if_pos hst]; simp only [Once]
  rw [if_neg hst] at h2 ⊢
  -- the second racy read: `u.FAULT_TYPE`
  unfold R.obj.Tcb.fault_type at h2 ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc] at h2 ⊢
  refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
    (fun r h1 hk Wd _ => ?_)
  replace h2 := hk
  obtain ⟨fi, x2, a4⟩ := r
  obtain ⟨efi, e1, e2⟩ := interp_liftR_ok h1
  dsimp only at e1 e2 efi
  subst x2 a4
  rw [eq_ok_of_spec Fl4Proofs.P0.Consts.layout.tcb.FAULT_TYPE.spec] at efi
  obtain rfl := ok_inj_ff efi
  try dsimp only at h2 ⊢
  simp only [SProg.sbind, SProg.read] at h2 ⊢
  simp only [interp] at h2
  obtain ⟨v1, hv1, h2⟩ := bok.mp h2
  simp only [Once]
  refine ⟨fun _ hq => ?_, fun v hv => ?_⟩
  · unfold E2E.tch at hq
    split_ifs at hq
    · rcases hq with hq | hq
      · exact ft_ne_st u hq
      · exact hq
    · exact hq
  rw [hv1] at hv
  obtain rfl := ok_inj_ff hv
  try dsimp only at h2 ⊢
  by_cases hft : (v1 != fl4_abi.consts.fault.VMFault) = true
  · rw [if_pos hft]; simp only [Once]
  rw [if_neg hft] at h2 ⊢
  -- `Reply.next`
  refine once_step hR0 hU (R.obj.Reply.next_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Reply.next_eq] at h1 ⊢
    rw [obj.Reply.next.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      X2 rptr D.rNx]
    exact h1
  replace h2 := hk
  rw [R.obj.Reply.next_eq] at h1
  obtain ⟨i4, -, rfl⟩ := bind_shape h1
  try dsimp only at h2 ⊢
  by_cases h4 : (i4 != 0#u64) = true
  on_goal 2 => rw [if_neg h4] at h2 ⊢
  on_goal 1 =>
    rw [if_pos h4] at h2 ⊢
    refine once_step hR0 hU (R.obj.Reply.next_is_head_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [R.obj.Reply.next_is_head_eq] at h1 ⊢
      rw [obj.Reply.next_is_head.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s)
        (IoRS (st := st) K Locks s)) X2 rptr D.rNx]
      exact h1
    replace h2 := hk
    rw [R.obj.Reply.next_is_head_eq] at h1
    obtain ⟨b2, -, rfl⟩ := bind_shape h1
    try dsimp only at h2 ⊢
    by_cases hb2 : b2 = true
    · rw [if_pos hb2]; simp only [Once]
    rw [if_neg hb2] at h2 ⊢
  all_goals
    refine once_step hR0 hU (R.obj.Tcb.sc_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [R.obj.Tcb.sc_eq] at h1 ⊢
      rw [obj.Tcb.sc.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
        u X2 gSc]
      exact h1
    replace h2 := hk
    rw [R.obj.Tcb.sc_eq] at h1
    obtain ⟨usc, -, rfl⟩ := bind_shape h1
    try dsimp only at h2 ⊢
    refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
      (fun r h1 hk Wd _ => ?_)
    replace h2 := hk
    obtain ⟨b3, x2, a4⟩ := r
    obtain ⟨-, e1, e2⟩ := interp_liftR_ok h1
    dsimp only at e1 e2
    subst x2 a4
    try dsimp only at h2 ⊢
    by_cases hb3 : b3 = true
    · rw [if_pos hb3]; simp only [Once]
    rw [if_neg hb3] at h2 ⊢
    -- `schedulable_here u` answers `false`
    refine once_step hR0 hU (R.fastpath.schedulable_here_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
    · rw [R.fastpath.schedulable_here_eq] at h1 ⊢
      rw [vm_here_guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) X2 u
        (nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
        (nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
        (nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
        D.tm D.rh D.dt D.cd gAf (fun hl => absurd hl haffX)]
      exact h1
    replace h2 := hk
    rw [R.fastpath.schedulable_here_eq] at h1
    obtain ⟨bh, ebh, rfl⟩ := bind_shape h1
    have hfalse : bh = false := by
      cases bh
      · rfl
      · exact absurd (here_facts (L := L) ebh).aff haffX
    subst hfalse
    try dsimp only at h2 ⊢
    rw [if_neg Bool.false_ne_true]
    simp only [Once]

/-- **`hro` of `rr_localPathG` holds** (the premise as stated there). -/
theorem rr_hro (hA : P0.ArchTotal ar) {rptr ep : U64} :
    ∀ s s' a r, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s → (∃ b, RrRep st rptr s b) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar (R.syscall.handle_reply_recv_vm_local (rptr, ep)) s' a = ok r →
      Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_reply_recv_vm_local (rptr, ep))
        s' a :=
  fun _ _ _ _ hE ⟨_, hb⟩ Al h => rr_once_alt hA hE hb ⟨Al.ksb, Al.cpu, Al.read⟩ h

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Scs Nt Ac : Set U64} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`hro` of `rr_localPathJG` holds** (the premise as stated there). -/
theorem rr_hroJ (hA : P0.ArchTotal ar) {rptr ep : U64} :
    ∀ s s' a r, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s → (∃ b, RrRep st rptr s b) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar (R.syscall.handle_reply_recv_vm_local (rptr, ep)) s' a = ok r →
      Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_reply_recv_vm_local (rptr, ep))
        s' a :=
  fun _ _ _ _ hE ⟨_, hb⟩ Al h => rr_once_alt hA (VmRRPreJ.pre hE) hb ⟨Al.ksb, Al.cpu, Al.read⟩ h

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} (ar : machine.Arch A)

/-- **The VM ReplyRecv local path with `IsProg`, `NoZero` and `ReadOnce` discharged** (module docstring):
`rr_localPathG` with `hro := rr_hro`. Premises: `hA`, `hK` [J], `hU` [J], `hLA` [J], `hm` [P], `hmA` [J], `huf` [J],
and `VmRRPre`'s fields. -/
noncomputable def rr_localPathG2 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {rptr ep : U64} (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s → b ∈ K.user → Aligned b →
      VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  rr_localPathG ar hA hK hU hLA hm hmA huf (rr_hro hA)

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Scs Nt Ac : Set U64} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} (ar : machine.Arch A)

/-- **`rr_localPathJ` with `IsProg`, `NoZero` and `ReadOnce` discharged** (module docstring): `rr_localPathJG`
with `hro := rr_hroJ`. Premises: `hA`, `hK` [J], `hU` [J], `hLA` [J], `hm` [P], `hmA` [J], `hufR` [J], and
`VmRRPreJ`'s fields. -/
noncomputable def rr_localPathJG2 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {rptr ep : U64} (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hufR : ∀ s b v, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s → b ∈ K.user → Aligned b →
      ((K.heap ep = some .ep →
          VmRPre st ar K T Cs Ω K.heap Sg (Heap.replies K.heap) Scs Nt Z Ac Locks (L.wr s b v) rptr ep) ∧
        RdTab (L := L) (IoRS (st := st) K Locks (L.wr s b v)) (L.wr s b v)) ∧
      Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  rr_localPathJG ar hA hK hU hLA hm hmA hufR (rr_hroJ hA)

end

end Fl4Proofs.P2.PathObl

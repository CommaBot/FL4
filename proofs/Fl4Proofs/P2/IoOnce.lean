/-
# P2: `ReadOnce` of the I/O port tree, proved by walking it (line hpzg, gen 3)

`io_localPathG` (`P2/ProgGenIoLP.lean`) left one premise, `hro` [W]: at an alternative `s'` of an entry `s` that
declines, the run of `R.ioBodyG number` reads each racy word once. Shown here by walking the tree
(`P2/OnceTree.lean`, `P2/OnceWalk.lean`):

* the prefix (`cur_thread`, `msg_info`, the flags, `NEXT_IP`, the `FAULT_IP` write, `update_timestamp`, `CAP`,
  `cur_sc`, `action`, `yield_to`) reads and writes words of `IoRS s` only (guarded steps);
* `ioport.invocation_ok` then reads the CTable root slot (in `IoRS s`) and walks the CSpace (`io_inv_once`,
  `P2/IoOnceC.lean`): every CNode-valued slot is in `IoRS s` (`slot_back`, `IoPre.slot`), so it is not racy; the
  first other slot read is the walk's last read and the run then ends (`bits_left ≠ 0`, `false`); a found slot
  (`bits_left = 0`) is read once, and unless it holds an I/O port cap (then it is in `IoRS s`) the run ends;
* after a passing check the run reads `CONSUMED`, the current SC's head refill and `schedulable_here`'s words, all
  in `IoRS s` (`IoMidR`, `P2/IoOnceB.lean`); since the alternative declines (`io_alt_not_acc`), it ends there.

So at most one racy pair (one slot's two words) is read, once.

* `io_tail_once` / `io_body_once`: the walk of `R.ioTailP` / `R.ioBodyG`;
* `io_hro`: **the `hro` premise of `io_localPathG` holds** (for any `Pre` giving `IoPre`);
* `io_localPathG2`: the I/O port local path with `IsProg`, `NoZero` and `ReadOnce` all discharged;
* `io_pathsKG2` / `io_pathsKG2_startAt`: SlJStLocTop's `io_pathsK` with its program premise family `hpz` fully
  discharged (`ProgGenWire`'s `io_pathsKG` with `hro := io_hro`).

Premises of `io_localPathG2`: `io_localPath`'s minus `hpz`: `hA` (Arch totality), `hK` [J], `hU` [J], `hLA` [J],
`hm` [P], `hPE` (`Pre` gives `IoPre`), `hmA` [J], `huf` [J]. Of `io_pathsKG2`: `io_pathsK`'s minus `hpz`.
-/
import Fl4Proofs.P2.IoOnceC
import Fl4Proofs.P2.ProgGenWire
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld oAFFINITY GateField TimerField)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section help
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {Rd User : U64 → Prop}

/-- An `if` on a pure condition at the top of the walked tree. -/
theorem once_ite0 {X : Type} {c : Prop} [Decidable c] {p q : SProg X} {Wd T : Set U64}
    {s : S} {a : A} {r' : X × S × A} (h : interp st ar (if c then p else q) s a = ok r')
    (hp : c → interp st ar p s a = ok r' → Once st ar Rd User Wd T p s a)
    (hq : ¬ c → interp st ar q s a = ok r' → Once st ar Rd User Wd T q s a) :
    Once st ar Rd User Wd T (if c then p else q) s a := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢; exact hp hc h
  · rw [if_neg hc] at h ⊢; exact hq hc h

theorem interp_ret_fst {X : Type} {x : X} {s : S} {a : A} {r : X × S × A}
    (h : interp st ar (SProg.ret x) s a = ok r) : r.1 = x := by
  rw [interp_ret'] at h; rw [← ok_inj_ff h]

end help

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 8000000 in
/-- **The walk of `R.ioTailP`** at a declining alternative (module docstring). -/
theorem io_tail_once (hA : P0.ArchTotal ar) {s s' : S} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {info : msginfo.MessageInfo} {number : I64} {a : A} {r' : Bool × S × A} {Wd : Set U64}
    (h : interp st ar (R.ioTailP (L.curW s) info number) s' a = ok r') (hn : r'.1 ≠ true) :
    Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) Wd ∅ (R.ioTailP (L.curW s) info number) s' a := by
  have hR0 : ∀ q, IoRS (st := st) K Locks s q → IoRS (st := st) K Locks s q ∧ q ∉ K.user :=
    fun q hq => ⟨hq, hq.2.1⟩
  have hW0 : ∀ q, IoRS (st := st) K Locks s q → q ∉ K.user := fun q hq => hq.2.1
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have hNd' : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (L.nodeAt s' (L.cpu s') o) := fun o h1 h2 => by
    rw [G.node]; exact (P.nd (Locks := Locks) o h1 h2).1
  unfold R.ioTailP at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun b _ h => ?_)
  cases b
  · rw [if_neg Bool.false_ne_true]; simp only [Once]
  rw [if_pos rfl] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- NEXT_IP
  refine once_gstep hR0 hW0 (R.obj.Tcb.reg_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.obj.Tcb.reg_eq] at h1 ⊢
    rw [obj.Tcb.reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ s' _
      (P.reg (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.reg_eq] at h1
  obtain ⟨nx, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the `FAULT_IP` write
  refine once_gstep hR0 hW0 (R.obj.Tcb.set_reg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd2 _ => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ s'
      _ _ (P.reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x1, es1, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have ex1 : x1 = L.wr s' (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have hNx1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) o) := fun o h1 h2 => by
    rw [ex1, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]; exact hNd' o h1 h2
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `update_timestamp`
  have hct : IoRS (st := st) K Locks s (ctA (L := L) x1) := by
    show IoRS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CUR_TIME)
    exact hNx1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have hcn : IoRS (st := st) K Locks s (cnA (L := L) x1) := by
    show IoRS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) layout.node.CONSUMED)
    exact hNx1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  refine once_gstep hR0 hW0 (R.sched.update_timestamp_nz) h (fun r h1 => ?_) (fun r h1 hk Wd3 _ => ?_)
  · rw [R.sched.update_timestamp_eq] at h1 ⊢
    rw [sched.update_timestamp.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      ar x1 a hct hct hcn hcn]
    exact h1
  replace h := hk
  rw [R.sched.update_timestamp_eq] at h1
  obtain ⟨⟨x2, a1⟩, eu, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  obtain ⟨C, sl, M⟩ := io_alt_midR (Locks := Locks) hA P Al es1 eu
  have nd2 := M.nd
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `CAP`
  refine once_gstep hR0 hW0 (R.obj.Tcb.reg_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd4 _ => ?_)
  · rw [R.obj.Tcb.reg_eq] at h1 ⊢
    rw [obj.Tcb.reg.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ x2 _
      M.cap]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.reg_eq] at h1
  obtain ⟨cptr, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `cur_sc`
  refine once_gstep hR0 hW0 (R.sched.cur_sc_nz) h (fun r h1 => ?_) (fun r h1 hk Wd5 _ => ?_)
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
  refine once_gstep hR0 hW0 (R.sched.action_nz) h (fun r h1 => ?_) (fun r h1 hk Wd6 _ => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x2
      (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨i3, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `yield_to`
  refine once_gstep hR0 hW0 (R.obj.Tcb.yield_to_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd7 _ => ?_)
  · rw [R.obj.Tcb.yield_to_eq] at h1 ⊢
    rw [obj.Tcb.yield_to.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ x2
      M.yld]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.yield_to_eq] at h1
  obtain ⟨i4, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the check and the rest
  refine io_inv_once M hW0 h (fun _ _ => by simp only [Bool.false_eq_true, ↓reduceIte, Once]) (fun Wd8 h => ?_)
  simp only [↓reduceIte] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.sched.consumed_nz) h (fun r h1 => ?_) (fun r h1 hk Wd9 _ => ?_)
  · rw [R.sched.consumed_eq] at h1 ⊢
    rw [sched.consumed.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x2
      (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    exact h1
  replace h := hk
  rw [R.sched.consumed_eq] at h1
  obtain ⟨i5, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.sporadic.sufficient_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd10 _ => ?_)
  · rw [R.sporadic.sufficient_eq] at h1 ⊢
    rw [sporadic.sufficient.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      ar x2 a1 _ i5 M.rh]
    exact h1
  replace h := hk
  rw [R.sporadic.sufficient_eq] at h1
  obtain ⟨b2, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ h => ?_) (fun _ _ => by simp only [Once])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  have htm : IoRS (st := st) K Locks s (tmA (L := L) x2) := by
    show IoRS (st := st) K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.TIMER_MIN)
    exact nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have hrh : IoRS (st := st) K Locks s (rhA (L := L) x2) := by
    show IoRS (st := st) K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.RELEASE_HEAD)
    exact nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have hct2 : IoRS (st := st) K Locks s (ctA (L := L) x2) := by
    show IoRS (st := st) K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.CUR_TIME)
    exact nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  refine once_gstep hR0 hW0 (R.fastpath.schedulable_here_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd11 _ => ?_)
  · rw [R.fastpath.schedulable_here_eq] at h1 ⊢
    rw [fastpath.schedulable_here.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s)
      (IoRS (st := st) K Locks s)) x2 _ hct2 htm hrh M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
    exact h1
  replace h := hk
  rw [R.fastpath.schedulable_here_eq] at h1
  obtain ⟨b3, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ h => ?_) (fun _ _ => by simp only [Once])
  -- an accepted run: excluded
  exfalso
  apply hn
  try simp only [SProg.sbind_assoc, SProg.sbind] at h
  exact interp_true_of (fun _ _ _ _ h => interp_true_of (fun _ _ _ _ h => interp_true_of
    (fun _ _ _ _ h => interp_ret_fst h) h) h) h

set_option maxHeartbeats 4000000 in
/-- **The walk of `R.ioBodyG`** at a declining alternative (module docstring). -/
theorem io_body_once (hA : P0.ArchTotal ar) {s s' : S} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {number : I64} {a : A} {r' : Bool × S × A}
    (h : interp st ar (R.ioBodyG number) s' a = ok r') (hn : r'.1 ≠ true) :
    Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.ioBodyG number) s' a := by
  have hR0 : ∀ q, IoRS (st := st) K Locks s q → IoRS (st := st) K Locks s q ∧ q ∉ K.user :=
    fun q hq => ⟨hq, hq.2.1⟩
  have hW0 : ∀ q, IoRS (st := st) K Locks s q → q ∉ K.user := fun q hq => hq.2.1
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  unfold R.ioBodyG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.sched.cur_thread_nz) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) s'
      (by rw [G.node]; exact nC)]
    exact h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  rw [cur_thread_ok] at et
  have et' : t = L.curW s := by rw [← hcur]; exact (ok_inj_ff et).symm
  subst et'
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.msg.msg_info_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd2 _ => ?_)
  · rw [R.msg.msg_info_eq] at h1 ⊢
    rw [msg.msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) s' _
      (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1]
    exact h1
  replace h := hk
  rw [R.msg.msg_info_eq] at h1
  obtain ⟨info, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.obj.Tcb.flags_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd3 _ => ?_)
  · rw [R.obj.Tcb.flags_eq] at h1 ⊢
    rw [obj.Tcb.flags.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) _ s'
      (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.flags_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  refine once_ite0 h (fun _ h => ?_) (fun _ h => io_tail_once hA P Al h hn)
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => io_tail_once hA P Al h hn)

/-- **`hro` of `io_localPathG` holds** (module docstring): at an alternative of a declining entry, the run of
`R.ioBodyG number` reads each racy word once. -/
theorem io_hro (hA : P0.ArchTotal ar) {number : I64} {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    ∀ s s' a r, P s → (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar (R.ioBodyG number) s' a = ok r →
      Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.ioBodyG number) s' a := by
  intro s s' a r hE hna Al h
  have P0' := hPE s hE
  obtain ⟨⟨b0, z0, c0⟩, h0⟩ := io_total (st := st) hA number s a
  have hr0 : b0 ≠ true := fun e => hna ⟨z0, c0, by rw [h0, e]⟩
  have hh : syscall.handle_ioport_local st ar s' a number = ok r := by
    exact (io_isProgOn (Locks := Locks) (m0 := m0) hA hPE (io_isProg S number) st (Narrow.self st) s' ⟨s, hE, Al⟩
      a).trans h
  have hn : r.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r
    intro e
    change b = true at e
    subst e
    exact io_alt_not_acc hA P0' Al h0 hr0 hh
  exact io_body_once hA P0' Al h hn

/-- **The I/O port local path with `IsProg`, `NoZero` and `ReadOnce` discharged** (module docstring). -/
noncomputable def io_localPathG2 (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hU : E2E.UserOK K) (hLA : IoLayA K) {number : I64} (hm : E2E.MasksWr st)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hmA : ∀ s, P s → ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  io_localPathG (Locks := Locks) ar hA hK hU hLA (number := number) hm hPE hmA huf (io_hro hA hPE)

end

/-! ## The top-level I/O port path member, program premise family discharged -/

section io
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- **`io_pathsK` with `hpz` fully discharged** (module docstring). -/
noncomputable def io_pathsKG2 (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hmA : ∀ K m s, SlJAt (L := L) K s → Q K m s → ∀ d, K.heap d = some .tcb →
      m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  io_pathsKG (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number hm Q hPE hmA huf
    (fun K m => io_hro (Locks := Locks) (m0 := m) hA (P := fun s => SlJAt (L := L) K s ∧ Q K m s)
      (fun s h => hPE K m s h.1 h.2))

/-- **`StartAt` for `io_pathsKG2`** at a layout `K` from `SlJAt K σ ∧ Q K m σ`. -/
theorem io_pathsKG2_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hmA : ∀ K m s, SlJAt (L := L) K s → Q K m s → ∀ d, K.heap d = some .tcb →
      m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hQ : Q K m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (io_pathsKG2 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number hm Q hPE hmA huf
        () K m hK hU) c hs μ
      ((io_pathsKG2 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number hm Q hPE hmA huf
        () K m hK hU).body σ a) :=
  io_pathsKG_startAt ar hA number hm Q hPE hmA huf _ K m hK hU a hJ hQ hc hl hμ

end io

end Fl4Proofs.P2.PathObl

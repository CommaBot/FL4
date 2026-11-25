/-
# P2: `ReadOnce` of the VM-fault tree, proved by walking it (line hpzg)

`vm_localPathG` (`P2/ProgGenVmLP.lean`) left one premise, `hro` [W]: at an entry whose fault handler is homed
on another core, the runs of the tree `R.syscall.handle_vm_fault_local addr code` from the alternatives read
each racy word once. With the tree concrete, this is a fact about its text, shown here by walking it
(`P2/OnceTree.lean`):

* `vm_once_alt`: a declined run of the tree at an alternative `x` of the entry `s` (`Ag` on `IoRS s`) is
  `Once`. Either the handler's `REPLY_OBJ` word is in `IoRS s` whenever the run could read it, and the whole
  run is guarded (`vm_dec_tr` with `R'' = IoRS s`, `once_of_guardG`); or the entry's handler `d` is homed on
  another core with `REPLY_OBJ` outside `IoRS s`, and the walk shows the run's reads: the prefix
  (`update_timestamp`, `cur_sc`, `consumed`, `sufficient`, `cur_thread`) and the fast path up to `Ep.head` on
  `IoRS s`, then **one** read of `d`'s `REPLY_OBJ` (the only racy read; nothing was touched before it), then
  either `false` or `schedulable_here d` on `IoRS s`, which answers `false` (`d`'s `AFFINITY`, in `IoRS s`,
  is not this core), and the run ends. So no word is read twice racily: `hro` holds.
* `vm_readOnceG`: `ReadOnce` of the tree (`vm_readOnce` with the `hro` case by `vm_once_alt`);
* `vm_localPathG2`: the VM-fault local path with `IsProg` / `NoZero` / `ReadOnce` all discharged.

Premises of `vm_localPathG2`: `vm_localPath`'s minus `hpz`: `hA` (Arch totality), `hK` [J], `hU` [J],
`hLA` [J], `hm` [P], `hmA` [J], `huf` [J], and `VmPre`'s fields.
-/
import Fl4Proofs.P2.ProgGenVmLP
import Fl4Proofs.P2.OnceTree
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout fld own GateField TimerField GField RegionOK oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section help
variable {S A : Type} {ar : machine.Arch A}

theorem bind_shape {T U : Type} {m : Result T} {g : T → U} {y : U} (h : (m >>= fun r => ok (g r)) = ok y) :
    ∃ v, m = ok v ∧ g v = y := by
  obtain ⟨v, hv, e⟩ := bind_eq_ok' h
  exact ⟨v, hv, ok_inj_ff e⟩

theorem interp_liftR_ok {X : Type} {m : machine.Store S} {e : Result X} {s : S} {a : A} {r : X × S × A}
    (h : interp m ar (SProg.liftR e) s a = ok r) : e = ok r.1 ∧ r.2.1 = s ∧ r.2.2 = a := by
  unfold SProg.liftR at h
  split_ifs at h with h1 h2
  · rw [interp_ret'] at h
    have e := ok_inj_ff h
    subst e
    exact ⟨h1.choose_spec, rfl, rfl⟩
  · rw [interp_err'] at h; exact absurd h fail_not_ok
  · rw [interp_err'] at h; exact absurd h fail_not_ok

end help

/-- Walks a `NoZero` goal of a generated subtree (as the generated `_nz` proofs). -/
macro "nz_walk" : tactic => `(tactic| (
  try simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret]
  repeat' (first
    | (with_reducible apply NoZero.sbind)
    | (with_reducible apply NoZero.blk)
    | (with_reducible apply NoZero.ite')
    | (with_reducible exact NoZero.liftR _)
    | (with_reducible exact NoZero.read _)
    | (with_reducible exact NoZero.readPair _)
    | (with_reducible exact NoZero.write _ _)
    | (with_reducible exact NoZero.ksBase)
    | (with_reducible exact NoZero.curCpu)
    | (with_reducible exact NoZero.frameMasks)
    | (intro; try dsimp only)
    | (simp only [reif_nz])
    | split
    | (exact trivial)
    | (dsimp only))))

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **A declined run of the VM-fault tree at an alternative reads each racy word once** (module docstring). -/
theorem vm_once_alt (hA : P0.ArchTotal ar) (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s)
    (hlkE : VmGlue st ar Locks s) {x : S} (G : Ag st (IoRS (st := st) K Locks s) s x) {a : A}
    {addr code : U64} {r' : Bool × S × A}
    (h' : interp st ar (R.syscall.handle_vm_fault_local addr code) x a = ok r') (hn : r'.1 ≠ true) :
    Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_vm_fault_local addr code) x a := by
  have hU : ∀ q, IoRS (st := st) K Locks s q → q ∉ K.user := fun q hq => hq.2.1
  have hR0 : ∀ q, IoRS (st := st) K Locks s q → IoRS (st := st) K Locks s q ∧ q ∉ K.user :=
    fun q hq => ⟨hq, hq.2.1⟩
  have hx : syscall.handle_vm_fault_local st ar x a addr code = ok r' := by
    rw [R.syscall.handle_vm_fault_local_eq, bind_proj3] at h'; exact h'
  by_cases hrepA : ∀ s1 a1 sl ptr badge x' y g gr, sched.update_timestamp st ar s a = ok (s1, a1) →
      obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
      obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr) → L.epState s1 ptr = obj.EP_RECV →
      L.mem s1 (affA (L.mem s1 (epHeadA ptr))) ≠ L.cpu s1 →
      IoRS (st := st) K Locks s (replyA (L.mem s1 (epHeadA ptr)))
  · -- the whole run is guarded
    have hg := vm_dec_tr hA P hlkE G (R'' := IoRS (st := st) K Locks s) (fun b hb => hb) hrepA hx hn
    have hg' : interp (PathObl.guard st (IoRS (st := st) K Locks s) (IoDS (st := st) s)) ar
        (R.syscall.handle_vm_fault_local addr code) x a = ok r' := by
      rw [R.syscall.handle_vm_fault_local_eq, bind_proj3]; exact hg
    exact once_of_guardG hU _ (R.syscall.handle_vm_fault_local_nz addr code) ∅ ∅ x a r' hg'
  -- a handler homed elsewhere, its `REPLY_OBJ` outside `IoRS s`: walk the tree
  push_neg at hrepA
  obtain ⟨s1, a1e, sl, ptr, badge, x', y, g, gr, eu, hsl, hcap, hst, hne, -⟩ := hrepA
  have B := P.base
  have rT := (B.nd (Locks := Locks) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME])
    (by simp [layout.node.CUR_TIME])).1
  have rN := (B.nd (Locks := Locks) layout.node.CONSUMED (by simp [layout.node.CONSUMED])
    (by simp [layout.node.CONSUMED])).1
  have D := vm_dfOf hA P hlkE eu
  have hct : IoRS (st := st) K Locks s (ctA (L := L) x) := by
    show IoRS (st := st) K Locks s (L.nodeAt x (L.cpu x) layout.node.CUR_TIME); rw [G.node]; exact rT
  have hcn : IoRS (st := st) K Locks s (cnA (L := L) x) := by
    show IoRS (st := st) K Locks s (L.nodeAt x (L.cpu x) layout.node.CONSUMED); rw [G.node]; exact rN
  -- the tree
  unfold R.syscall.handle_vm_fault_local at h' ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h' ⊢
  by_cases hd : (layout.NUM_DOMAINS != 1#u64) = true
  · rw [if_pos hd]; simp only [Once]
  rw [if_neg hd] at h' ⊢
  -- update_timestamp
  refine once_step hR0 hU (R.sched.update_timestamp_nz) h' (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.update_timestamp_eq] at h1 ⊢
    rw [sched.update_timestamp.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s)
      (IoRS (st := st) K Locks s)) ar x a hct hct hcn hcn]
    exact h1
  replace h2 := hk
  rw [R.sched.update_timestamp_eq] at h1
  obtain ⟨⟨x1, a1⟩, eu', rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  obtain ⟨-, G1⟩ := vm_ag_upd (fun _ hb => hb.1) G rT rN eu eu'
  obtain ⟨nd1, dt1, cd1, bm1, tm1, rh1⟩ := D.alt G1 (fun b hb => hb)
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
  -- cur_sc
  refine once_step hR0 hU (R.sched.cur_sc_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.cur_sc_eq] at h1 ⊢
    rw [sched.cur_sc.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x1
      (nd1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
    exact h1
  replace h2 := hk
  rw [R.sched.cur_sc_eq] at h1
  obtain ⟨csc, ecs, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  have ec : csc = L.cscW x1 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecs; exact (ok_inj_ff ecs).symm
  subst ec
  -- consumed
  refine once_step hR0 hU (R.sched.consumed_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.consumed_eq] at h1 ⊢
    rw [sched.consumed.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x1
      (nd1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    exact h1
  replace h2 := hk
  rw [R.sched.consumed_eq] at h1
  obtain ⟨u, -, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  -- sufficient
  refine once_step hR0 hU (R.sporadic.sufficient_nz _ _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sporadic.sufficient_eq] at h1 ⊢
    rw [sporadic.sufficient.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      ar x1 a1 (L.cscW x1) u hs]
    exact h1
  replace h2 := hk
  rw [R.sporadic.sufficient_eq] at h1
  obtain ⟨⟨b, a2⟩, -, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  all_goals (first
    | (rw [if_neg Bool.false_ne_true]; simp only [Once]; done)
    | (rw [if_pos rfl] at h2 ⊢))
  -- cur_thread
  refine once_step hR0 hU (R.sched.cur_thread_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x1
      (nd1 _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]))]
    exact h1
  replace h2 := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  rw [cur_thread_ok] at et
  have et' : t = L.curW s := by rw [← ecur1]; exact (ok_inj_ff et).symm
  subst et'
  -- the two pure steps and `vm_fault`'s fault value
  refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
    (fun r h1 hk Wd _ => ?_)
  replace h2 := hk
  obtain ⟨i1, x2, a3⟩ := r
  obtain ⟨-, e1, e2⟩ := interp_liftR_ok h1
  dsimp only at e1 e2
  subst x2 a3
  dsimp only at h2 ⊢
  simp only [SProg.sbind] at h2 ⊢
  refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
    (fun r h1 hk Wd _ => ?_)
  replace h2 := hk
  obtain ⟨f, x2, a3⟩ := r
  obtain ⟨-, e1, e2⟩ := interp_liftR_ok h1
  dsimp only at e1 e2
  subst x2 a3
  dsimp only at h2 ⊢
  -- the fast path
  unfold R.fastpath_vm.vm_fault at h2 ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h2 ⊢
  refine once_step hR0 hU (R.sched.action_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s)) x1
      (nd1 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h2 := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  split
  · simp only [Once]
  rename_i hi
  rw [if_neg hi] at h2
  refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
    (fun r h1 hk Wd _ => ?_)
  replace h2 := hk
  obtain ⟨sl', x2, a3⟩ := r
  obtain ⟨esl, e1, e2⟩ := interp_liftR_ok h1
  dsimp only at e1 e2
  subst x2 a3
  dsimp only at h2 ⊢ esl
  rw [hsl] at esl
  have e := ok_inj_ff esl
  subst e
  obtain ⟨r0, r8⟩ := D.sl sl hsl
  refine once_step hR0 hU (R.obj.Slot.cap_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
      sl x1 r0 r8]
    exact h1
  replace h2 := hk
  rw [R.obj.Slot.cap_eq] at h1
  obtain ⟨c, ec, rfl⟩ := bind_shape h1
  rw [cap_congr_ag G1 r0 r8, hcap] at ec
  have e := ok_inj_ff ec
  subst e
  dsimp only at h2 ⊢
  obtain ⟨rts, rhd, hHT⟩ := D.ep sl ptr badge x' y g gr hsl hcap
  -- `grant`, else `grant_reply`, leads to the same walk
  cases g
  rw [if_neg Bool.false_ne_true] at h2 ⊢
  cases gr
  · rw [if_neg Bool.false_ne_true]; simp only [Once]
  rw [if_pos rfl] at h2 ⊢
  rotate_left
  rw [if_pos rfl] at h2 ⊢
  all_goals
      refine once_step hR0 hU (R.obj.Ep.state_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
      · rw [R.obj.Ep.state_eq] at h1 ⊢
        rw [obj.Ep.state.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
          ptr x1 rts]
        exact h1
      replace h2 := hk
      rw [R.obj.Ep.state_eq] at h1
      obtain ⟨i1, -, rfl⟩ := bind_shape h1
      dsimp only at h2 ⊢
      split
      · simp only [Once]
      rename_i hi1
      rw [if_neg hi1] at h2
      refine once_step hR0 hU (R.obj.Ep.head_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
      · rw [R.obj.Ep.head_eq] at h1 ⊢
        rw [obj.Ep.head.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoRS (st := st) K Locks s))
          ptr x1 rhd]
        exact h1
      replace h2 := hk
      rw [R.obj.Ep.head_eq] at h1
      obtain ⟨d, ed, rfl⟩ := bind_shape h1
      dsimp only at h2 ⊢
      have hdd : d = L.mem s1 (epHeadA ptr) := by
        rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) x1 ptr)] at ed
        rw [← ok_inj_ff ed]; exact G1.m (epHeadA ptr) rhd
      have hdT : d ∈ T := by rw [hdd]; exact hHT hst
      have rA : IoRS (st := st) K Locks s (affA d) :=
        D.gate d hdT 3520#u64 (by simp) (by simp) (by simp) (by simp [GateField])
      have hrem : L.mem x1 (affA d) ≠ L.cpu x1 := by
        rw [G1.m _ rA, G1.c, hdd]; exact hne
      -- the reply word: its one read
      unfold R.obj.Tcb.reply_obj at h2 ⊢
      simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc] at h2 ⊢
      refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
        (fun r h1 hk Wd _ => ?_)
      replace h2 := hk
      obtain ⟨o, x2, a3⟩ := r
      obtain ⟨-, e1, e2⟩ := interp_liftR_ok h1
      dsimp only at e1 e2
      subst x2 a3
      dsimp only at h2 ⊢
      simp only [SProg.sbind, SProg.read] at h2 ⊢
      simp only [interp] at h2
      obtain ⟨v0, hv0, h2⟩ := bok.mp h2
      refine once_rd_first hR0 hU _ _ (fun v => by nz_walk) Wd ∅ x1 a1 (Set.notMem_empty _) (fun v hv => ?_)
      rw [hv0] at hv
      have e := ok_inj_ff hv
      subst e
      split
      · exact ⟨_, interp_ret' _ _ _ _ _⟩
      rename_i hz0
      rw [if_neg hz0] at h2
      -- `schedulable_here d` answers `false`
      rw [interp_sbind] at h2 ⊢
      obtain ⟨⟨bh, x3, a4⟩, hh, h3⟩ := bind_eq_ok' h2
      have hh' := hh
      rw [R.fastpath.schedulable_here_eq] at hh'
      obtain ⟨bh', ebh, ebh2⟩ := bind_shape hh'
      cases ebh2
      have hfalse : bh = false := by
        cases bh
        · rfl
        · exact absurd (here_facts (L := L) ebh).aff hrem
      subst hfalse
      rw [R.fastpath.schedulable_here_eq, vm_here_guard (gS := PathObl.guard st (IoRS (st := st) K Locks s)
          (IoRS (st := st) K Locks s)) x1 d
          (nd1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
          (nd1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
          (nd1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
          tm1 rh1 dt1 cd1 rA (fun hl => absurd hl hrem), ebh]
      refine ⟨(false, x1, a1), ?_⟩
      first
        | rfl
        | simp only [bind_tc_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, interp_ret']

/-- **`hro` of `vm_localPathG` holds** (the premise as stated there): at an alternative, a run of the tree
reads each racy word once. If the entry declines, so does the alternative (`vm_dec_alt`) and `vm_once_alt`
applies; if it accepts, the alternative's run is the entry's guarded run (`vm_readOnce`'s accepted case). -/
theorem vm_hro (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K) {addr code : U64}
    (hm : E2E.MasksWr st) :
    ∀ s s' a r, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → (∃ b, VmRep st ar s a b) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar (R.syscall.handle_vm_fault_local addr code) s' a = ok r →
      Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_vm_fault_local addr code) s' a := by
  intro s s' a r hE _ Al h
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_vm_fault_local mm ar x a addr code = interp mm ar (R.syscall.handle_vm_fault_local addr code) x a :=
    fun mm x a => congrFun (congrFun (vm_isProg S addr code A ar mm) x) a
  obtain ⟨⟨b0, z0, c0⟩, h0⟩ := vm_total (st := st) hA addr code s a
  cases b0
  · have h' : syscall.handle_vm_fault_local st ar s' a addr code = ok r := by rw [hp]; exact h
    have hn := (vm_dec_alt (m0 := m0) hA hK hLA hE.1 hE.2.1 h0 Bool.false_ne_true Al h').1
    exact vm_once_alt hA hE.1 hE.2.1 ⟨Al.ksb, Al.cpu, Al.read⟩ h hn
  · have hacc := vm_acc (Locks := Locks) hA hE.1 hE.2.2 h0
    rw [hp] at hacc
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) _ (vm_noZero addr code) s s' a true
      z0 c0 Al.ksb Al.cpu Al.masks Al.read hacc
    exact once_of_guard (fun q hq => hq.2.1) _ (vm_noZero addr code) ∅ ∅ s' a _ hg'

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} (ar : machine.Arch A)

/-- **The VM-fault local path with `IsProg`, `NoZero` and `ReadOnce` discharged** (module docstring):
`vm_localPathG` with `hro := vm_hro`. -/
noncomputable def vm_localPathG2 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {addr code : U64} (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → b ∈ K.user → Aligned b →
      VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  vm_localPathG ar hA hK hU hLA (addr := addr) (code := code) hm hmA huf (vm_hro hA hK hLA hm)

end

end Fl4Proofs.P2.PathObl

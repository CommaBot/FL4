/-
# P2 (2): write footprints of the page-fault local paths (line p2io)

Footprint lemmas have the shape `∀ w, ¬ Foot s w → read s' w = read s w`
(`P1.WritesIn st s s' Foot`: also the kernel base and the core index are
unchanged), with `Foot s` a predicate on (aligned) words computed from the
entry state `s`, the entry's inputs and the typed-heap sets of the P1
invariants (`T` the TCBs, `Scs` the SCs and `Z` their sizes).

DESIGN.md §7, "What a local path may write, its footprint", made concrete:

* `FootVmCore T Scs Z s`: this core's node state (the 4288 bytes of node
  `L.cpu s`); the TCB objects (4 KiB) of the threads on this core
  (`FootVmTcb`: the current thread, or a TCB of `T` whose `affinity` is this
  core); the SC objects of this core (`FootVmSc`: the current SC, or one
  bound to, or yielded to by, a thread on this core). None of these paths
  writes an IPC buffer (the VM-fault message is four message registers), so
  the buffers are left out.
* `FootVmLocked T s ep r`: the objects the path locks (fl4-sync
  `local_vm_fault` / `local_syscall`): the endpoint `ep` (16 bytes), the reply
  object `r` (32 bytes), and the queue links (`EP_NEXT`, `EP_PREV`) of the
  threads queued on `ep` (`QueueRel` at `s`).

Results here (P2 (2a), the write footprint):

* `vm_local_foot`: `handle_vm_fault_local`, accepted or declined, writes only
  `FootVm T Scs Z s ep r`, with `ep`, `r` the endpoint and reply object
  fl4-sync's `local_vm_fault` locked (`hLk`: the fast path's endpoint and its
  handler's reply object are those). Inputs: `BXI` at `s`, and after the
  entry's `update_timestamp` the facts P1's fast-path analysis takes there
  (`VmFootHyps`, what P3's `JAtZ.vmFaultOK` supplies);
* `rr_vm_local_foot`: `handle_reply_recv_vm_local`, accepted or declined,
  writes only `FootVm T Scs Z s ep rptr` for `found = (rptr, ep)`. Inputs:
  `BXI` at `s`; fl4-sync's check under the lock that the reply has no
  neighbours on a call stack (`hnb`: otherwise `reply_remove` writes the
  neighbours, unlocked); after the prefix, `BXI`, P1's ring-sum bound `RRSum`
  (P1 takes it as `RRSumAt` [J] at its top) and m68's placement `RRPl`
  (`rrPl_ofG`);
* the declines alone: `vm_local_decline_foot` (only the node's timestamp
  words), `rr_vm_local_decline_foot` (and the current thread's `FAULT_IP`);
* tools: `switch_to_foot` / `activate_foot` (the fast paths' tail writes only a
  given `B` holding this core's node, the switched-to thread, the current SC,
  its SC and the SC it yields to), `FootVm.of_agree` (the footprint reads few
  words, so it moves across the prefix), `ObjsOK.one` (P1's object facts for
  one SC, to reuse P1 lemmas stated over an object set with a single SC).

Premises: none.
-/
import Fl4Proofs.P1.FastLocalDecline
import Fl4Proofs.P1.FastIoLocal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! ## The footprint -/

/-- A thread on this core at `s`: the current thread, or a TCB of `T` whose
`affinity` is this core. -/
def FootVmTcb (T : Set U64) (s : S) (y : U64) : Prop :=
  y ∈ T ∧ (y = L.curW s ∨ L.mem s (affA y) = L.cpu s)

/-- An SC of this core at `s`: the current SC, or the SC a thread on this
core is bound to or yields to. -/
def FootVmSc (T Scs : Set U64) (s : S) (c : U64) : Prop :=
  c ∈ Scs ∧ (c = L.cscW s ∨ ∃ y, FootVmTcb (L := L) T s y ∧ (c = L.mem s (scA y) ∨ c = L.mem s (yieldA y)))

/-- This core's words at `s`: its node, the TCBs of its threads, its SCs. -/
def FootVmCore (T Scs : Set U64) (Z : U64 → Nat) (s : S) (b : U64) : Prop :=
  (∃ o : U64, o.val < 4288 ∧ b = L.nodeAt s (L.cpu s) o) ∨
  (∃ y K : U64, FootVmTcb (L := L) T s y ∧ K.val < 4096 ∧ b = core.num.U64.wrapping_add y K) ∨
  (∃ c, FootVmSc (L := L) T Scs s c ∧ InSC c (Z c) b)

/-- The words of the object of `n` bytes at `o`. -/
def InObj (o : U64) (n : Nat) (b : U64) : Prop := o.val ≤ b.val ∧ b.val < o.val + n

/-- The queue links of the threads queued on endpoint `ep` at `s`. -/
def FootVmEpQ (T : Set U64) (s : S) (ep b : U64) : Prop :=
  ∃ l, QueueRel (L.mem s) T .Ep (L.epQ s ep) l ∧ ∃ y ∈ l, b = nextA .Ep y ∨ b = prevA .Ep y

/-- The locked objects: the endpoint `ep`, the reply object `r`, and the
queue links of the threads queued on `ep`. -/
def FootVmLocked (T : Set U64) (s : S) (ep r b : U64) : Prop :=
  InObj ep 16 b ∨ InObj r 32 b ∨ FootVmEpQ (L := L) T s ep b

/-- **The write footprint of the page-fault local paths** at entry state `s`,
with `ep` and `r` the endpoint and reply object locked. -/
def FootVm (T Scs : Set U64) (Z : U64 → Nat) (s : S) (ep r b : U64) : Prop :=
  FootVmCore (L := L) T Scs Z s b ∨ FootVmLocked (L := L) T s ep r b

theorem FootVmCore.foot {T Scs : Set U64} {Z : U64 → Nat} {s : S} {ep r b : U64}
    (h : FootVmCore (L := L) T Scs Z s b) : FootVm (L := L) T Scs Z s ep r b := Or.inl h

/-! ## Words of the footprint -/

theorem footVm_node {T Scs : Set U64} {Z : U64 → Nat} {s : S} {o : U64} (ho : o.val < 4288) :
    FootVmCore (L := L) T Scs Z s (L.nodeAt s (L.cpu s) o) := Or.inl ⟨o, ho, rfl⟩

theorem footVm_tcb {T Scs : Set U64} {Z : U64 → Nat} {s : S} {y K : U64} (hy : FootVmTcb (L := L) T s y)
    (hK : K.val < 4096) : FootVmCore (L := L) T Scs Z s (core.num.U64.wrapping_add y K) :=
  Or.inr (Or.inl ⟨y, K, hy, hK, rfl⟩)

theorem footVm_cur {T Scs : Set U64} {Z : U64 → Nat} {s : S} {K : U64} (hc : L.curW s ∈ T)
    (hK : K.val < 4096) : FootVmCore (L := L) T Scs Z s (core.num.U64.wrapping_add (L.curW s) K) :=
  footVm_tcb ⟨hc, Or.inl rfl⟩ hK

/-- `update_timestamp`'s two words. -/
theorem utW_writes {T : Set U64} {s : S} (hN : NodePlaced st T s (L.cpu s)) (n : U64) :
    WritesIn st s (utW (L := L) s n) (fun b => b = ctA (L := L) s ∨ b = cnA (L := L) s) := by
  obtain ⟨hct, hcn, -⟩ := ct_cn hN
  refine ⟨by unfold utW; simp, by unfold utW; simp, fun b hb hn => ?_⟩
  unfold utW
  rw [mem_wr_ne' hcn hb (fun e => hn (Or.inr e.symm)), mem_wr_ne' hct hb (fun e => hn (Or.inl e.symm))]

/-- `update_timestamp`'s two words are node words. -/
theorem utW_foot {T Scs : Set U64} {Z : U64 → Nat} {s : S} (hN : NodePlaced st T s (L.cpu s)) (n : U64) :
    WritesIn st s (utW (L := L) s n) (FootVmCore (L := L) T Scs Z s) :=
  (utW_writes hN n).mono fun b hb => by
    rcases hb with rfl | rfl
    · exact footVm_node (by simp [layout.node.CUR_TIME])
    · exact footVm_node (by simp [layout.node.CONSUMED])

/-- The syscall prefix `LocalPre` (the current thread's `FAULT_IP`, then one
`update_timestamp`) writes only this core's words. -/
theorem localPre_foot {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {T Scs : Set U64}
    {Z : U64 → Nat} {s s' : S} {a a' : A} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (hcT : L.curW s ∈ T) (h : LocalPre (st := st) ar s a (s', a')) :
    WritesIn st s s' (FootVmCore (L := L) T Scs Z s) := by
  obtain ⟨t, nx, s1, et, -, es1, eu⟩ := h
  rw [cur_thread_ok] at et
  obtain rfl := ok_inj_ff et
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s (L.curW s) layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
    (hT _ hcT) (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨K, hK, e1⟩ := hW1
  have hK' : K.val = 392 := by rw [hK]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (core.num.U64.wrapping_add (L.curW s) K) := field_aligned (hT _ hcT) (by omega) (by omega)
  obtain ⟨⟨n, a1⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  rw [update_timestamp_ok ar hN1 hn] at eu
  obtain ⟨rfl, -⟩ := Prod.mk.inj (ok_inj_ff eu)
  have w1 : WritesIn st s s1 (FootVmCore (L := L) T Scs Z s) := by
    rw [e1]; exact (writesIn_wr aF).mono fun b e => by rw [e]; exact footVm_cur hcT (by omega)
  have ec : ctA (L := L) s1 = ctA (L := L) s := by rw [e1, ctA_wr]
  have en : cnA (L := L) s1 = cnA (L := L) s := by rw [e1, cnA_wr]
  refine (w1.trans (utW_writes hN1 n)).mono fun b hb => hb.elim id fun hb => ?_
  rw [ec, en] at hb
  rcases hb with rfl | rfl
  · exact footVm_node (by simp [layout.node.CUR_TIME])
  · exact footVm_node (by simp [layout.node.CONSUMED])

/-! ## The fast paths' tail -/

theorem wi_wr {s0 s : S} {B : U64 → Prop} {a v : U64} (h : WritesIn st s0 s B) (ha : Aligned a) (hb : B a) :
    WritesIn st s0 (L.wr s a v) B :=
  (h.trans (writesIn_wr ha)).mono fun b hb' => hb'.elim id fun e => by rw [e]; exact hb

/-- The words of the SC `c` (aligned). -/
def SCW (Z : U64 → Nat) (c : U64) : Set U64 := {b | Aligned b ∧ InSC c (Z c) b}

section tail
variable {A : Type _} {ar : machine.Arch A} {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

theorem sc_word_in {s : S} {c o : U64} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) (ho : o.val < 128)
    (h8 : o.val % 8 = 0) : core.num.U64.wrapping_add c o ∈ SCW Z c := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨c8, c128, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz ho
  exact ⟨by unfold Aligned; rw [hv]; omega, by rw [hv]; omega, by rw [hv]; omega⟩

/-- **`ObjsOK` for one SC**: the global object facts restricted to the SC `c`
(its words the only objects; no reply objects or notifications). -/
theorem ObjsOK.one {s s' : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c : U64} (hc : c ∈ Scs) :
    ObjsOK st (SCW Z c) (SCW Z c) ∅ {c} ∅ Z s' where
  rp := fun r hr => absurd hr (by simp)
  sc := fun c' hc' => by rw [Set.mem_singleton_iff] at hc'; subst hc'; exact hO.sc _ hc
  rpW := fun r hr => absurd hr (by simp)
  scW := fun c' hc' b hb hin => by rw [Set.mem_singleton_iff] at hc'; subst hc'; exact ⟨hb, hin⟩
  fixW := fun c' hc' => by
    rw [Set.mem_singleton_iff] at hc'; subst hc'
    exact ⟨sc_word_in hO hc (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB]),
      sc_word_in hO hc (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])⟩
  scDisj := fun c1 h1 c2 h2 hne => by
    rw [Set.mem_singleton_iff] at h1 h2; subst h1 h2; exact absurd rfl hne
  rpSc := fun r hr => absurd hr (by simp)
  repW := fun c' hc' => by
    rw [Set.mem_singleton_iff] at hc'; subst hc'
    exact sc_word_in hO hc (by simp [layout.sc.REPLY]) (by simp [layout.sc.REPLY])
  ntW := fun n hn => absurd hn (by simp)
  ntRp := fun n hn => absurd hn (by simp)
  ntSc := fun n hn => absurd hn (by simp)
  ntAl := fun n hn => absurd hn (by simp)
  ntP := fun n hn => absurd hn (by simp)
  ntB := fun n hn => absurd hn (by simp)
  ntORp := fun n hn => absurd hn (by simp)
  ntOSc := fun n hn => absurd hn (by simp)
  snW := fun c' hc' => by
    rw [Set.mem_singleton_iff] at hc'; subst hc'
    exact sc_word_in hO hc (by simp [layout.sc.NTFN]) (by simp [layout.sc.NTFN])
  syW := fun c' hc' => by
    rw [Set.mem_singleton_iff] at hc'; subst hc'
    exact sc_word_in hO hc (by simp [layout.sc.YIELD_FROM]) (by simp [layout.sc.YIELD_FROM])
  mxW := fun c' hc' => by
    rw [Set.mem_singleton_iff] at hc'; subst hc'
    exact sc_word_in hO hc (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])
  nt0 := fun n hn => absurd hn (by simp)
  rp0 := fun r hr => absurd hr (by simp)

/-- **`activate_thread` of the current thread `d` writes only `B`**, for any
`B` holding this core's node words, `d`'s TCB words and the SC `d` yields to. -/
theorem activate_foot (hA : P0.ArchTotal ar) (X : S) (a : A) {d : U64} {B : U64 → Prop}
    (P : TailPld (L := L) T Cs Ω X d) (hO : ObjsOK st Ω Sg Rp Scs Nt Z X) (hcur : L.curW X = d)
    (hyt : L.mem X (yieldA d) ≠ 0#u64 → L.mem X (yieldA d) ∈ Scs)
    (hBn : ∀ o : U64, o.val < 4288 → B (L.nodeAt X (L.cpu X) o))
    (hBd : ∀ K : U64, K.val < 4096 → B (core.num.U64.wrapping_add d K))
    (hBy : L.mem X (yieldA d) ≠ 0#u64 → ∀ b, InSC (L.mem X (yieldA d)) (Z (L.mem X (yieldA d))) b → B b) :
    sched.activate_thread st ar X a ⦃ r => WritesIn st X r.1 B ⦄ := by
  have hd' := P.hT d P.hd
  unfold sched.activate_thread
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have ect' : ct = d := by rw [ect]; exact hcur
  subst ect'
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => WritesIn st X r.1 B) ?_ ?_
  · split
    · rename_i hi
      have hi0 : L.mem X (yieldA ct) ≠ 0#u64 := by rw [← ei]; simpa using hi
      have hiS := hyt hi0
      have hΩd : ∀ b ∈ SCW Z (L.mem X (yieldA ct)), b.val < ct.val ∨ ct.val + 2 ^ 12 ≤ b.val := fun b hb =>
        (P.hΩ b (hO.scW _ hiS b hb.1 hb.2)).2.1 ct P.hd
      refine WP.spec_mono (schedcontext.complete_yield_to.ywN (Ω := SCW Z (L.mem X (yieldA ct)))
        (Sg := SCW Z (L.mem X (yieldA ct))) (Rp := ∅) (Scs := {L.mem X (yieldA ct)}) (Nt := ∅) (Z := Z)
        hA X a ct hd' (ObjsOK.one hO hiS) (fun b hb => hb) (fun b hb => hb.1) hΩd
        (fun _ => Set.mem_singleton _)) ?_
      rintro ⟨s1, a1⟩ w
      refine w.mono fun b hb => ?_
      rcases hb with (hm | ⟨K, hK, -, rfl⟩) | rfl
      · exact hBy hi0 b hm.2
      · exact hBd K (by omega)
      · exact hBd 3472#u64 (by simp)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rintro ⟨s1, a1⟩ w1
  try simp only [WP.uncurry'_pair]
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · step with obj.Tcb.reg.spec as ⟨pc, _⟩
    refine WP.spec_bind (obj.Tcb.set_reg.wrK s1 ct layout.reg.NEXT_IP pc hd' (by simp [layout.reg.NEXT_IP])) ?_
    rintro s2 ⟨K, hK, e2⟩
    subst e2
    have hK' : K.val < 4096 := by rw [hK]; simp [layout.reg.NEXT_IP]
    have kA : Aligned (core.num.U64.wrapping_add ct K) := field_aligned hd' hK' (by rw [hK]; try omega)
    have sA : Aligned (stA ct) := by rw [stA_eq]; exact field_aligned hd' (by simp) (by simp)
    have w2 := wi_wr (v := pc) w1 kA (hBd K hK')
    have w3 := wi_wr (v := sched.TS_RUNNING) w2 sA (by rw [stA_eq]; exact hBd _ (by simp))
    refine WP.spec_bind (set_thread_state_act _ ct sched.TS_RUNNING) fun s4 e4 => ?_
    simp only [WP.spec_ok]
    rcases e4 with rfl | rfl
    · exact w3
    · have eA : actA (L := L) (L.wr s1 (core.num.U64.wrapping_add ct K) pc) =
          L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION := by
        have k1 : L.ksb s1 = L.ksb X := w1.1
        have c1 : L.cpu s1 = L.cpu X := w1.2.1
        unfold actA
        rw [LawfulStore.cpu_wr, c1, nodeAt_of_ksb (show L.ksb (L.wr s1 (core.num.U64.wrapping_add ct K) pc) = L.ksb X by
          rw [L.ksb_wr, k1])]
      rw [eA]
      exact wi_wr w3 (nodeAt_aligned P.hN (by rw [act_val]; omega) (by rw [act_val]))
        (hBn _ (by rw [act_val]; omega))
  · exact (WP.spec_ok _).2 w1

/-- **The fast paths' tail `fastpath.switch_to Y a d` writes only `B`**, for
any `B` holding this core's node words, `d`'s TCB words, the current SC, `d`'s
SC and the SC `d` yields to (hypotheses of `switch_to_nvm`). -/
theorem switch_to_foot (hA : P0.ArchTotal ar) (Y : S) (a : A) {d : U64} {zc zt : Nat} {B : U64 → Prop}
    (P : TailPld (L := L) T Cs Ω Y d) (hO : ObjsOK st Ω Sg Rp Scs Nt Z Y) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hc : SCq st Y Ω (L.cscW Y) zc)
    (ht : L.mem Y (scA d) ≠ L.cscW Y → SCin st Y Ω (L.mem Y (scA d)) zt ∧
      ∀ b, InSC (L.mem Y (scA d)) zt b → Outside b (L.cscW Y) zc)
    (hyt : L.mem Y (yieldA d) ≠ 0#u64 → L.mem Y (yieldA d) ∈ Scs)
    (hBn : ∀ o : U64, o.val < 4288 → B (L.nodeAt Y (L.cpu Y) o))
    (hBd : ∀ K : U64, K.val < 4096 → B (core.num.U64.wrapping_add d K))
    (hBc : ∀ b, InSC (L.cscW Y) zc b → B b)
    (hBt : L.mem Y (scA d) ≠ L.cscW Y → ∀ b, InSC (L.mem Y (scA d)) zt b → B b)
    (hBy : L.mem Y (yieldA d) ≠ 0#u64 → ∀ b, InSC (L.mem Y (yieldA d)) (Z (L.mem Y (yieldA d))) b → B b) :
    fastpath.switch_to st ar Y a d ⦃ r => WritesIn st Y r.1 B ⦄ := by
  have hd' := P.hT d P.hd
  unfold fastpath.switch_to
  refine WP.spec_bind (vspace.set_vm_root.same hA Y a d) ?_
  rintro ⟨Y1, a1⟩ e1
  simp only at e1; subst Y1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (sched.set_cur_thread.spec Y d) fun s2 e2 => ?_
  subst e2
  refine WP.spec_bind (sched.set_action.spec _ sched.ACTION_RESUME_CURRENT) fun s3 e3 => ?_
  subst e3
  simp only [nodeAt_wr, LawfulStore.cpu_wr]
  have cA := P.curAl
  have aA : Aligned (L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION) :=
    nodeAt_aligned P.hN (by rw [act_val]; omega) (by rw [act_val])
  have nAC : L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION ≠ L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD := by
    apply ne_of_valne
    rw [nodeAt_val P.hN (by rw [act_val]; omega), nodeAt_val P.hN (by rw [curth_val]; omega), act_val, curth_val]
    omega
  generalize hX : L.wr (L.wr Y (L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD) d)
    (L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION) sched.ACTION_RESUME_CURRENT = X
  have kX : L.ksb X = L.ksb Y := by rw [← hX, L.ksb_wr, L.ksb_wr]
  have cX : L.cpu X = L.cpu Y := by rw [← hX, LawfulStore.cpu_wr, LawfulStore.cpu_wr]
  have PX := P.ksb kX cX
  have wYX : WritesIn st Y X B := by
    rw [← hX]
    exact wi_wr (wi_wr (WritesIn.refl _ _) cA (hBn _ (by rw [curth_val]; omega))) aA
      (hBn _ (by rw [act_val]; omega))
  have hBX : ∀ o : U64, o.val < 4288 → B (L.nodeAt X (L.cpu X) o) := by
    intro o ho; rw [cX, nodeAt_of_ksb kX]; exact hBn o ho
  -- X agrees with Y on every word but the two node words
  have ag : ∀ b, Aligned b → b ≠ L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD →
      b ≠ L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION → L.mem X b = L.mem Y b := by
    intro b hb h1 h2
    rw [← hX, mem_wr_ne' aA hb (Ne.symm h2), mem_wr_ne' cA hb (Ne.symm h1)]
  have agΩ : ∀ b ∈ Ω, L.mem X b = L.mem Y b := fun b hb => ag b (P.hΩ b hb).1
    (fun e => out_ne_node (P.hΩ b hb) P.hcC P.hN (by rw [curth_val]; omega) (by rw [e]))
    (fun e => out_ne_node (P.hΩ b hb) P.hcC P.hN (by rw [act_val]; omega) (by rw [e]))
  have agT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem X (core.num.U64.wrapping_add d K) = L.mem Y (core.num.U64.wrapping_add d K) := fun K hK h8 =>
    ag _ (P.tcbAl hK h8) (fun e => node_ne_field P.hN (by rw [curth_val]; omega) P.hd hd' hK e.symm)
      (fun e => node_ne_field P.hN (by rw [act_val]; omega) P.hd hd' hK e.symm)
  have csA : Aligned (L.nodeAt Y (L.cpu Y) layout.node.CUR_SC) :=
    nodeAt_aligned P.hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ecs : L.mem X (L.nodeA X layout.node.CUR_SC) = L.cscW Y := by
    unfold LawfulStore.nodeA LawfulStore.cscW LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX]
    have v24 := nodeAt_val P.hN (off := layout.node.CUR_SC) (by simp [layout.node.CUR_SC])
    have v0 := nodeAt_val P.hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD])
    have v16 := nodeAt_val P.hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
    refine ag _ csA ?_ ?_ <;> apply ne_of_valne
    · rw [v24, v0]; simp [layout.node.CUR_SC, layout.node.CUR_THREAD]
    · rw [v24, v16]; simp [layout.node.CUR_SC, layout.node.SCHED_ACTION]
  have hcur : L.mem X (L.nodeA X layout.node.CUR_THREAD) = d := by
    unfold LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX, ← hX, mem_wr_ne' aA cA nAC, L.mem_wr_same cA]
  have esc : L.mem X (scA d) = L.mem Y (scA d) := by rw [scA_eq]; exact agT _ (by simp) (by simp)
  have est : L.mem X (stA d) = L.mem Y (stA d) := by rw [stA_eq]; exact agT _ (by simp) (by simp)
  have eyt : L.mem X (yieldA d) = L.mem Y (yieldA d) := agT 3472#u64 (by simp) (by simp)
  have hcX : SCq st X Ω (L.mem X (L.nodeA X layout.node.CUR_SC)) zc := by
    rw [ecs]
    refine ⟨fun hm => ?_, hc.2.1, hc.2.2⟩
    have em : L.rmax X (L.cscW Y) = L.rmax Y (L.cscW Y) :=
      agΩ _ (hc.2.1 _ hc.2.2.2.2 hc.2.2.2.1)
    exact (hc.1 (em ▸ hm)).agree fun b hb hin => agΩ b (hc.2.1 b hb hin)
  have htX : L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD))) ≠ L.mem X (L.nodeA X layout.node.CUR_SC) →
      SCin st X Ω (L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD)))) zt ∧
      ∀ b, InSC (L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD)))) zt b →
        Outside b (L.mem X (L.nodeA X layout.node.CUR_SC)) zc := by
    rw [hcur, esc, ecs]
    intro hne
    obtain ⟨h1, h2⟩ := ht hne
    exact ⟨h1.agree agΩ, h2⟩
  have fN : ∀ o : U64, LowFree o.val → FreeCd (L := L) X Ω (L.nodeA X o) ∧ B (L.nodeA X o) :=
    fun o ho => ⟨Or.inr ⟨o, ho, rfl⟩, hBX o (by simp only [LowFree] at ho; omega)⟩
  have hBtX : L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD))) ≠ L.mem X (L.nodeA X layout.node.CUR_SC) →
      ∀ b, InSC (L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD)))) zt b → B b := by
    rw [hcur, esc, ecs]; exact hBt
  refine WP.spec_bind (sched.switch_sched_context.fp hA X a1 (zt := zt) (zc := zc)
    (B := fun b => FreeCd (L := L) X Ω b ∧ B b)
    PX.hcC PX.hN PX.hΩ hcX htX (fN _ (by simp [layout.node.REPROGRAM, LowFree]))
    (fN _ (by simp [layout.node.CONSUMED, LowFree])) (fN _ (by simp [layout.node.CUR_SC, LowFree]))
    (fun hne b hb h => ⟨Or.inl ((htX hne).1.2 b hb h.inSC), hBtX hne b h.inSC⟩)
    (fun b hb h => by
      rcases h with h | rfl
      · exact ⟨Or.inl (hcX.2.1 b hb h.inSC), hBc b (ecs ▸ h.inSC)⟩
      · refine ⟨Or.inl (hcX.2.1 _ hb hcX.2.2.1.1), ?_⟩
        have h1 := hcX.2.2.1.1
        rw [ecs] at h1 ⊢
        exact hBc _ h1)) ?_
  rintro ⟨s4, a2⟩ ⟨w4, -⟩
  try simp only [WP.uncurry'_pair]
  have P4 := PX.ksb w4.1 w4.2.1
  have fN4 : ∀ o : U64, LowFree o.val → FreeCd (L := L) X Ω (L.nodeAt s4 (L.cpu s4) o) ∧
      B (L.nodeAt s4 (L.cpu s4) o) := fun o ho =>
    ⟨Or.inr ⟨o, ho, by rw [w4.2.1, nodeAt_of_ksb w4.1]⟩,
      by rw [w4.2.1, nodeAt_of_ksb w4.1]; exact hBX o (by simp only [LowFree] at ho; omega)⟩
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => WritesIn st X r.1 (fun b => FreeCd (L := L) X Ω b ∧ B b)) ?_ ?_
  · split
    · refine WP.spec_bind (sched.set_next_interrupt.fp hA s4 a2 (B := fun b => FreeCd (L := L) X Ω b ∧ B b) P4.hN
        (fN4 _ (by simp [layout.node.ARMED, LowFree]))) ?_
      rintro ⟨s6, a4⟩ w6
      try simp only [WP.uncurry'_pair]
      refine WP.spec_bind (obj.node_set.spec s6 c _ _) fun s7 e7 => ?_
      subst e7
      simp only [WP.spec_ok]
      have w7 : WritesIn st s6 (L.wr s6 (L.nodeAt s6 c layout.node.REPROGRAM) 0#u64)
          (fun b => FreeCd (L := L) X Ω b ∧ B b) := by
        rw [ec, nodeAt_of_ksb w6.1]
        exact (writesIn_wr (nodeAt_aligned P4.hN (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]))).mono fun b e => by
            rw [e]; exact fN4 _ (by simp [layout.node.REPROGRAM, LowFree])
      exact ((w4.trans w6).trans w7).mono fun b hb => by
        rcases hb with (h | h) | h <;> exact h
    · exact (WP.spec_ok _).2 w4
  rintro ⟨s5, a3⟩ w5
  try simp only [WP.uncurry'_pair]
  have P5 := PX.ksb w5.1 w5.2.1
  refine WP.spec_bind (smp.send_pending.fp hA s5 a3 (B := fun b => FreeCd (L := L) X Ω b ∧ B b) P5.hN
    ⟨Or.inr ⟨layout.node.IPI_PENDING, by simp [layout.node.IPI_PENDING, LowFree],
      by rw [w5.2.1, nodeAt_of_ksb w5.1]⟩,
      by rw [w5.2.1, nodeAt_of_ksb w5.1]; exact hBX _ (by simp [layout.node.IPI_PENDING])⟩) ?_
  rintro ⟨s6, a4⟩ w6'
  try simp only [WP.uncurry'_pair]
  have w6B : WritesIn st X s6 (fun b => FreeCd (L := L) X Ω b ∧ B b) :=
    (w5.trans w6').mono fun b hb => hb.elim id id
  have w6 : WritesIn st X s6 (FreeCd (L := L) X Ω) := w6B.mono fun _ hb => hb.1
  have P6 := PX.ksb w6.1 w6.2.1
  have kT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s6 (core.num.U64.wrapping_add d K) = L.mem X (core.num.U64.wrapping_add d K) := fun K hK h8 =>
    w6.mem_eq (PX.tcbAl hK h8) (PX.tcb_nfree hK)
  have ey6 : L.mem s6 (yieldA d) = L.mem Y (yieldA d) := by
    rw [show yieldA d = core.num.U64.wrapping_add d 3472#u64 from rfl, kT _ (by simp) (by simp)]
    rw [show core.num.U64.wrapping_add d 3472#u64 = yieldA d from rfl, eyt]
  refine WP.spec_mono (activate_foot hA s6 a4 P6 (ObjsOK.any hO) (B := B) ?_ (by rw [ey6]; exact hyt) ?_ hBd
    (by rw [ey6]; exact hBy)) fun r w => (wYX.trans (w6B.trans w)).mono fun b hb => ?_
  · show L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.CUR_THREAD) = d
    rw [w6.2.1, nodeAt_of_ksb w6.1, w6.mem_eq PX.curAl PX.cur_nfree]; exact hcur
  · intro o ho; rw [w6.2.1, nodeAt_of_ksb w6.1]; exact hBX o ho
  · rcases hb with h | (h | h)
    · exact h
    · exact h.2
    · exact h

end tail

/-! ## The declined page-fault entries -/

section
variable {A : Type _} {ar : machine.Arch A}

/-- **A declined `handle_vm_fault_local` writes only this core's node**
(its `update_timestamp`), so only `FootVm`. -/
theorem vm_local_decline_foot {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {addr code ep r : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (false, s', a')) :
    WritesIn st s s' (FootVm (L := L) T Scs Z s ep r) := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hSQ.cur
  have e := vm_local_decline ar h
  obtain ⟨⟨n, a1⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok ar hN hn] at e
  obtain ⟨rfl, -⟩ := Prod.mk.inj (ok_inj_ff e)
  exact (utW_foot hN n).mono fun _ hb => hb.foot

/-- **A declined `handle_reply_recv_vm_local` writes only this core's words**
(the current thread's `FAULT_IP` and the node's timestamp words). -/
theorem rr_vm_local_decline_foot {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {found : U64 × U64} {ep r : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (h : syscall.handle_reply_recv_vm_local st ar s a found = ok (false, s', a')) :
    WritesIn st s s' (FootVm (L := L) T Scs Z s ep r) := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hSQ.cur
  rcases rr_vm_local_decline ar h with ⟨rfl, -⟩ | ⟨hP, -⟩
  · exact WritesIn.refl _ _
  · exact (localPre_foot hA hSQ.tcbs hN hSQ.curT hP).mono fun _ hb => hb.foot

end

/-! ## Moving the footprint across writes it does not read -/

theorem qrel_agree {m m' : U64 → U64} {T : Set U64} {l : tcbqueue.Link} {q : tcbqueue.Queue} {xs : List U64}
    (h : QueueRel m T l q xs)
    (hl : ∀ x ∈ xs, m' (prevA l x) = m (prevA l x) ∧ m' (nextA l x) = m (nextA l x)) : QueueRel m' T l q xs :=
  ⟨h.nodup, h.mem, h.head, h.last, Seg.congr hl h.seg⟩

/-- **The footprint depends on few words**: two states with the same kernel
base and core that agree on the current thread and SC words, the TCBs'
affinity, SC, yield and endpoint-link words, and the endpoint's queue, have
the same footprint. -/
theorem FootVm.of_agree {T Scs : Set U64} {Z : U64 → Nat} {s s' : S} {ep r b : U64}
    (hk : L.ksb s' = L.ksb s) (hc : L.cpu s' = L.cpu s)
    (hcur : L.curW s' = L.curW s) (hcsc : L.cscW s' = L.cscW s)
    (hy : ∀ y ∈ T, ∀ K : U64, (K.val = 3520 ∨ K.val = 3464 ∨ K.val = 3472 ∨ K.val = 3496 ∨ K.val = 3504) →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (he : L.epQ s' ep = L.epQ s ep)
    (h : FootVm (L := L) T Scs Z s' ep r b) : FootVm (L := L) T Scs Z s ep r b := by
  have hTc : ∀ y, FootVmTcb (L := L) T s' y → FootVmTcb (L := L) T s y := by
    rintro y ⟨hyT, e | e⟩
    · exact ⟨hyT, Or.inl (e.trans hcur)⟩
    · refine ⟨hyT, Or.inr ?_⟩
      have := hy y hyT 3520#u64 (Or.inl (by simp))
      rw [← hc, ← e]; exact this.symm
  have hSc : ∀ c, FootVmSc (L := L) T Scs s' c → FootVmSc (L := L) T Scs s c := by
    rintro c ⟨hcS, e | ⟨y, hyc, e | e⟩⟩
    · exact ⟨hcS, Or.inl (e.trans hcsc)⟩
    · refine ⟨hcS, Or.inr ⟨y, hTc y hyc, Or.inl ?_⟩⟩
      rw [e]; exact hy y hyc.1 3464#u64 (Or.inr (Or.inl (by simp)))
    · refine ⟨hcS, Or.inr ⟨y, hTc y hyc, Or.inr ?_⟩⟩
      rw [e]; exact hy y hyc.1 3472#u64 (Or.inr (Or.inr (Or.inl (by simp))))
  rcases h with (⟨o, ho, rfl⟩ | ⟨y, K, hyc, hK, rfl⟩ | ⟨c, hcs, hin⟩) | (h | h | ⟨l, hq, y, hyl, e⟩)
  · rw [hc, nodeAt_of_ksb hk]; exact (footVm_node ho).foot
  · exact (footVm_tcb (hTc y hyc) hK).foot
  · exact Or.inl (Or.inr (Or.inr ⟨c, hSc c hcs, hin⟩))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ⟨l, ?_, y, hyl, e⟩))
    rw [he] at hq
    refine qrel_agree hq fun x hx => ⟨?_, ?_⟩
    · exact (hy x (hq.mem x hx) 3504#u64 (Or.inr (Or.inr (Or.inr (Or.inr (by simp)))))).symm
    · exact (hy x (hq.mem x hx) 3496#u64 (Or.inr (Or.inr (Or.inr (Or.inl (by simp)))))).symm

/-- The footprint after an `update_timestamp` is the one before. -/
theorem FootVm.of_utW {T Scs : Set U64} {Z : U64 → Nat} {s : S} {n ep r b : U64} (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s))
    (hep : ep.val + 16 ≤ L.nodeBase s (L.cpu s) ∨ L.nodeBase s (L.cpu s) + 4288 ≤ ep.val)
    (hepf : ep.val + 16 ≤ 2 ^ 64) (hepa : ep.val % 8 = 0)
    (h : FootVm (L := L) T Scs Z (utW (L := L) s n) ep r b) : FootVm (L := L) T Scs Z s ep r b := by
  have w := utW_writes hN n
  have vT := nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
  have vN := nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
  have nNode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 → o.val ≠ 40 →
      L.mem (utW (L := L) s n) (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h48 h40
    have vo := nodeAt_val hN ho
    refine w.mem_eq (nodeAt_aligned hN ho h8) ?_
    rintro (e | e) <;> (have e' := congrArg UScalar.val e; (try unfold ctA at e'); (try unfold cnA at e'); rw [vo] at e')
    · rw [vT] at e'; simp [layout.node.CUR_TIME] at e'; omega
    · rw [vN] at e'; simp [layout.node.CONSUMED] at e'; omega
  have nOut : ∀ x : U64, Aligned x → (x.val < L.nodeBase s (L.cpu s) ∨ L.nodeBase s (L.cpu s) + 4288 ≤ x.val) →
      L.mem (utW (L := L) s n) x = L.mem s x := by
    intro x hx hout
    refine w.mem_eq hx ?_
    rintro (e | e) <;> (have e' := congrArg UScalar.val e; (try unfold ctA at e'); (try unfold cnA at e'))
    · rw [vT] at e'; simp [layout.node.CUR_TIME] at e'; omega
    · rw [vN] at e'; simp [layout.node.CONSUMED] at e'; omega
  have kk : L.ksb (utW (L := L) s n) = L.ksb s := w.1
  have cc : L.cpu (utW (L := L) s n) = L.cpu s := w.2.1
  refine FootVm.of_agree kk cc ?_ ?_ ?_ ?_ h
  · show L.mem _ (L.nodeAt _ _ _) = _
    rw [cc, nodeAt_of_ksb kk]
    exact nNode _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  · show L.mem _ (L.nodeA _ _) = L.mem _ (L.nodeA _ _)
    unfold LawfulStore.nodeA
    rw [cc, nodeAt_of_ksb kk]
    exact nNode _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  · intro y hy K hK
    have hya := hT y hy
    have hK' : K.val < 4096 := by omega
    refine nOut _ (field_aligned hya hK' (by omega)) ?_
    rw [field_val hya hK']; have := hN.disj y hy; omega
  · have ha : L.mem (utW (L := L) s n) (epHeadA ep) = L.mem s (epHeadA ep) :=
      nOut _ (by unfold Aligned; rw [epHeadA_val]; exact hepa) (by rw [epHeadA_val]; omega)
    have ht : L.mem (utW (L := L) s n) (epTSA ep) = L.mem s (epTSA ep) :=
      nOut _ (by unfold Aligned; rw [epTSA_val' hepf]; omega) (by rw [epTSA_val' hepf]; omega)
    unfold LawfulStore.epQ; rw [ha, ht]

/-! ## The VM fault message: registers only -/

section msgs
variable {A : Type _} {ar : machine.Arch A}

theorem set_mr_reg {T : Set U64} {s0 s : S} {y buf i v : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hi : i.val < 4)
    (h : WritesIn st s0 s (XferRegW T ∅)) :
    msg.set_mr st s y buf i v ⦃ r => WritesIn st s0 r.2 (XferRegW T ∅) ⦄ := by
  unfold msg.set_mr
  split
  · refine WP.spec_bind (msg.msg_register.lt i) fun r hr => ?_
    refine WP.spec_bind (set_reg_rgU (U := ∅) (v := v) hT hy hr h) fun s1 h1 => ?_
    try simp only [lift, bind_ok]
    exact (WP.spec_ok _).2 h1
  · rename_i hne
    exfalso; apply hne
    simp only [msg.N_MSG_REGISTERS]; scalar_tac

/-- **The VM fault message writes only the receiver's registers** (four
`set_mr` below `N_MSG_REGISTERS`). -/
theorem set_mrs_fault_vm_reg {T : Set U64} {s : S} {a : A} {snd rcv buf : U64} (hT : TcbPlaced T) (hr : rcv ∈ T)
    (hty : L.mem s (faultA snd) = fl4_abi.consts.fault.VMFault) :
    faults.set_mrs_fault st ar s a snd rcv buf ⦃ r => WritesIn st s r.2 (XferRegW T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.set_mrs_fault
  rw [fault_type_ok, hty]; simp only [bind_ok]
  refine WP.spec_bind (P0.obj.Tcb.fault_w0.p0 st snd s hS) fun w0 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w1.p0 st snd s hS) fun w1 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w2.p0 st snd s hS) fun w2 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s _ hS) fun pc _ => ?_
  simp only [vm_ne_cap, vm_ne_us, vm_ne_ue, vm_ne_to, vm_ne_dbg, if_false, if_true, eq_self_iff_true, ↓reduceIte]
  refine WP.spec_bind (set_mr_reg (v := pc) (buf := buf) (i := 0#u64) hT hr (by simp)
    (WritesIn.refl s (XferRegW T ∅))) ?_
  rintro ⟨x1, s1⟩ h1
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  try dsimp only
  refine WP.spec_bind (set_mr_reg (v := w0) (i := 1#u64) hT hr (by simp) h1) ?_
  rintro ⟨x2, s2⟩ h2
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  try dsimp only
  refine WP.spec_bind (set_mr_reg (v := w2) (i := 2#u64) hT hr (by simp) h2) ?_
  rintro ⟨x3, s3⟩ h3
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  try dsimp only
  exact set_mr_reg (v := w1) (i := 3#u64) hT hr (by simp) h3

end msgs

/-- The fast dequeue's writes (`epFast`). -/
theorem epFast_writes {s : S} {ptr dest : U64} (hh : Aligned (epHeadA ptr)) (htl : Aligned (epTSA ptr))
    (hn : Aligned (nextA .Ep dest)) (hp : Aligned (prevA .Ep dest))
    (haf : (L.epQ s ptr).end ≠ dest → Aligned (prevA .Ep (L.mem s (nextA .Ep dest)))) :
    WritesIn st s (epFast (L := L) s ptr dest) (fun b => b = epHeadA ptr ∨ b = epTSA ptr ∨ b = nextA .Ep dest ∨
      b = prevA .Ep dest ∨ ((L.epQ s ptr).end ≠ dest ∧ b = prevA .Ep (L.mem s (nextA .Ep dest)))) := by
  refine ⟨?_, ?_, fun b hb hnb => ?_⟩
  · unfold epFast epW; dsimp only; split <;> simp
  · unfold epFast epW; dsimp only; split <;> simp
  · exact epFast_mem hb ⟨hh, fun e => hnb (Or.inl e.symm)⟩ ⟨htl, fun e => hnb (Or.inr (Or.inl e.symm))⟩
      ⟨hn, fun e => hnb (Or.inr (Or.inr (Or.inl e.symm)))⟩ ⟨hp, fun e => hnb (Or.inr (Or.inr (Or.inr (Or.inl e.symm))))⟩
      (fun hne => ⟨haf hne, fun e => hnb (Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, e.symm⟩))))⟩)

theorem wt {s₁ s₂ s₃ : S} {B : U64 → Prop} (h₁ : WritesIn st s₁ s₂ B) (h₂ : WritesIn st s₂ s₃ B) :
    WritesIn st s₁ s₃ B := (h₁.trans h₂).mono fun _ hb => hb.elim id id

/-! ## The accepted VM fault -/

section acc
variable {A : Type _} {ar : machine.Arch A}

/-- The facts the VM-fault fast path's P1 analysis takes at the state where
it is entered (after the entry's `update_timestamp`): `vmFault_of`'s
hypotheses (P3 `JAtZ.vmFaultOK` supplies them: `bxiU`, `curNb`, `fhTyped`,
`bufU_out`, `bufOK`, `asidOffU`). -/
structure VmFootHyps (T Cs Ω U Sg Rp Scs Nt Ac : Set U64) (H : Heap) (Z : U64 → Nat) (s : S) : Prop where
  bxi : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s
  nb : ¬ Blocked (L.mem s (stA (L.curW s)))
  cap : obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄
  user : ∀ b ∈ U, OutsideObjs st T Cs s b ∧ b ∉ Ω
  buf : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄
  asid : AsidOff (L := L) Ω Sg s

set_option maxHeartbeats 4000000 in
/-- **An accepted VM-fault fast run writes only `FootVm` of its entry
state** (`s` here is the state `fastpath_vm.vm_fault` is entered at). -/
theorem vm_tail_foot (hA : P0.ArchTotal ar) {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {s : S} {a : A} {t : obj.Tcb} {w0 w1 w2 : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t = L.curW s)
    (hsf : faults.set_fault st s t (error.Fault.VmFault w0 w1 (w2 != 0#u64)) =
      ok (sfG (L := L) s t fl4_abi.consts.fault.VMFault w0 w1 (if (w2 != 0#u64) then 1#u64 else 0#u64)))
    {ptr badge dest r : U64} {rest : List U64} {sF : S} {aF : A}
    (hc : FaultChecks st s t ptr badge dest r)
    (hrecv : L.mem s (stA dest) = sched.TS_BLOCKED_ON_RECV) (hr : r ∈ Rp)
    (E : FaultEnt (L := L) T Cs Ω U s t ptr dest r rest)
    (hfast : faultTailG st ar s a t (error.Fault.VmFault w0 w1 (w2 != 0#u64)) fl4_abi.consts.fault.VMFault ptr badge
      dest r = ok (true, sF, aF)) :
    WritesIn st s sF (FootVm (L := L) T Scs Z s ptr r) := by
  obtain ⟨⟨Q, R, hSQ⟩, hB, hX, hSg, hS⟩ := hI
  have hX0 : ScExtra0 st T Cs Scs Nt s := hX.2.2.toScExtra0
  have hO := hX.1
  rw [faultTailG_eq st ar a t _ _ ptr badge dest r hsf] at hfast
  have hf0 := hfast
  unfold faultTail2G at hfast
  obtain ⟨rb, hbuf, h1⟩ := bind_eq_ok hfast
  obtain ⟨⟨sent, S6⟩, hmrs, h2⟩ := bind_eq_ok h1
  try simp only [uncurry_apply_pair] at h2
  obtain ⟨mi, hmi, h3⟩ := bind_eq_ok h2
  obtain ⟨S7, hS7, h4⟩ := bind_eq_ok h3
  obtain ⟨S8, hS8, -⟩ := bind_eq_ok h4
  rw [faultTail2G_eq ar _ a t _ dest r badge hbuf hmrs hmi hS7 hS8, faultTail3_eq] at hf0
  obtain ⟨s15, h15, hfin⟩ := bind_eq_ok hf0
  obtain ⟨-, -, K⟩ := faultReads_ofG ar (Or.inr rfl) E hbuf hmrs hS7 hS8
  have HF := here_facts (L := L) hc.here
  have hT := E.hT
  have hdT : dest ∈ T := E.hq.mem dest (by simp)
  have hd' := hT dest hdT
  have htT : t ∈ T := E.ht
  have ht' := hT t htT
  have hN := E.hN
  have hcC := E.hcC
  have hΩ := E.hΩ
  have hE := E.hE
  -- the footprint and its words
  generalize hG : FootVm (L := L) T Scs Z s ptr r = G
  have Gt : ∀ K : U64, K.val < 4096 → G (core.num.U64.wrapping_add t K) := fun K hK => by
    rw [← hG]; exact (footVm_tcb ⟨htT, Or.inl ht⟩ hK).foot
  have Gd : ∀ K : U64, K.val < 4096 → G (core.num.U64.wrapping_add dest K) := fun K hK => by
    rw [← hG]; exact (footVm_tcb ⟨hdT, Or.inr HF.aff⟩ hK).foot
  have Gn : ∀ o : U64, o.val < 4288 → G (L.nodeAt s (L.cpu s) o) := fun o ho => by
    rw [← hG]; exact (footVm_node ho).foot
  have Gsc : ∀ c b, FootVmSc (L := L) T Scs s c → InSC c (Z c) b → G b := fun c b hc' hb => by
    rw [← hG]; exact Or.inl (Or.inr (Or.inr ⟨c, hc', hb⟩))
  have Gep : ∀ b, InObj ptr 16 b → G b := fun b hb => by rw [← hG]; exact Or.inr (Or.inl hb)
  have Grp : ∀ b, InObj r 32 b → G b := fun b hb => by rw [← hG]; exact Or.inr (Or.inr (Or.inl hb))
  have Gq : ∀ y ∈ dest :: rest, G (prevA .Ep y) := fun y hy => by
    rw [← hG]; exact Or.inr (Or.inr (Or.inr ⟨dest :: rest, E.hq, y, hy, Or.inr rfl⟩))
  -- (1) `set_fault`: four words of `t`
  have tout : ∀ y ∈ T, y ≠ t → ∀ Kx : U64, Kx.val < 4096 →
      (core.num.U64.wrapping_add y Kx).val < t.val ∨ t.val + 4096 ≤ (core.num.U64.wrapping_add y Kx).val := by
    intro y hy hne Kx hKx
    have hya := hT y hy
    have hv : y.val ≠ t.val := fun e => hne (UScalar.eq_of_val_eq e)
    rw [field_val hya hKx]; have := hya.align; have := ht'.align; omega
  have sfo : ∀ x : U64, Aligned x → (x.val < t.val ∨ t.val + 4096 ≤ x.val) →
      L.mem (sfG (L := L) s t fl4_abi.consts.fault.VMFault w0 w1 (if (w2 != 0#u64) then 1#u64 else 0#u64)) x =
        L.mem s x := by
    intro x hx ho
    have ne : ∀ Kx : U64, Kx.val < 4096 → core.num.U64.wrapping_add t Kx ≠ x := fun Kx hKx e => by
      have := congrArg UScalar.val e; rw [field_val ht' hKx] at this; omega
    exact sfG_mem hx ⟨field_aligned ht' (K := 3376#u64) (by simp) (by simp), ne 3376#u64 (by simp)⟩
      ⟨field_aligned ht' (by simp) (by simp), ne _ (by simp)⟩ ⟨field_aligned ht' (by simp) (by simp), ne _ (by simp)⟩
      ⟨field_aligned ht' (by simp) (by simp), ne _ (by simp)⟩
  have hEo : ∀ o : U64, o.val < 16 → o.val % 8 = 0 → ptr.val + o.val < t.val ∨ t.val + 4096 ≤ ptr.val + o.val := by
    intro o ho _; have := hE.disj t htT; omega
  have eQ2 : L.epQ (sfG (L := L) s t fl4_abi.consts.fault.VMFault w0 w1 (if (w2 != 0#u64) then 1#u64 else 0#u64))
      ptr = L.epQ s ptr := by
    have h0 := sfo (epHeadA ptr) (by unfold Aligned; rw [epHeadA_val]; exact hE.align)
      (by rw [epHeadA_val]; have := hEo 0#u64 (by simp) (by simp); simpa using this)
    have h8 := sfo (epTSA ptr) (by unfold Aligned; rw [epTSA_val hE]; have := hE.align; omega)
      (by rw [epTSA_val hE]; have := hEo 8#u64 (by simp) (by simp); simpa using this)
    unfold LawfulStore.epQ; rw [h0, h8]
  have eN2 : L.mem (sfG (L := L) s t fl4_abi.consts.fault.VMFault w0 w1 (if (w2 != 0#u64) then 1#u64 else 0#u64))
      (nextA .Ep dest) = L.mem s (nextA .Ep dest) := by
    rw [nextA_eq']
    exact sfo _ (field_aligned hd' (by simp [nextOff]) (by simp [nextOff]))
      (tout dest hdT E.hdt _ (by simp [nextOff]))
  have fT2 : L.mem (sfG (L := L) s t fl4_abi.consts.fault.VMFault w0 w1 (if (w2 != 0#u64) then 1#u64 else 0#u64))
      (faultA t) = fl4_abi.consts.fault.VMFault := by
    have fA : Aligned (faultA t) := field_aligned ht' (K := 3376#u64) (by simp) (by simp)
    have ne : ∀ Kx : U64, Kx.val < 4096 → Kx.val ≠ 3376 → core.num.U64.wrapping_add t Kx ≠ faultA t :=
      fun Kx hKx hne => field_ne ht' ht' hKx (K2 := 3376#u64) (by simp) (fun _ => by simpa using hne)
    unfold sfG
    rw [mem_wr_ne' (field_aligned ht' (by simp) (by simp)) fA (ne _ (by simp) (by simp)),
      mem_wr_ne' (field_aligned ht' (by simp) (by simp)) fA (ne _ (by simp) (by simp)),
      mem_wr_ne' (field_aligned ht' (by simp) (by simp)) fA (ne _ (by simp) (by simp)), L.mem_wr_same fA]
  generalize hs2 : sfG (L := L) s t fl4_abi.consts.fault.VMFault w0 w1
    (if (w2 != 0#u64) then 1#u64 else 0#u64) = s2 at hbuf hmrs eQ2 eN2 fT2
  have w1' : WritesIn st s s2 G := by
    rw [← hs2]; unfold sfG
    exact wi_wr (wi_wr (wi_wr (wi_wr (WritesIn.refl _ _) (field_aligned ht' (K := 3376#u64) (by simp) (by simp))
      (Gt 3376#u64 (by simp)))
      (field_aligned ht' (by simp) (by simp)) (Gt _ (by simp)))
      (field_aligned ht' (by simp) (by simp)) (Gt _ (by simp)))
      (field_aligned ht' (by simp) (by simp)) (Gt _ (by simp))
  -- (2) the dequeue: the endpoint, the handler's links, its successor's `EP_PREV`
  have haf : (L.epQ s2 ptr).end ≠ dest → L.mem s2 (nextA .Ep dest) ∈ dest :: rest := by
    intro hne
    rw [eQ2] at hne; rw [eN2]
    have hl := E.hq.last
    have hsg := E.hq.seg
    cases rest with
    | nil => exact absurd (by rw [hl]; rfl) hne
    | cons y ys =>
      simp only [Seg_cons] at hsg
      rw [hsg.2.1]; simp
  have hafT : (L.epQ s2 ptr).end ≠ dest → L.mem s2 (nextA .Ep dest) ∈ T := fun h => E.hq.mem _ (haf h)
  have w5 : WritesIn st s2 (epFast (L := L) s2 ptr dest) G := by
    refine (epFast_writes (by unfold Aligned; rw [epHeadA_val]; exact hE.align)
      (by unfold Aligned; rw [epTSA_val hE]; have := hE.align; omega)
      (by rw [nextA_eq']; exact field_aligned hd' (by simp [nextOff]) (by simp [nextOff]))
      (by rw [prevA_eq']; exact field_aligned hd' (by simp [prevOff]) (by simp [prevOff]))
      (fun h => by rw [prevA_eq']; exact field_aligned (hT _ (hafT h)) (by simp [prevOff]) (by simp [prevOff]))).mono
      fun b hb => ?_
    rcases hb with rfl | rfl | rfl | rfl | ⟨hne, rfl⟩
    · exact Gep _ ⟨by rw [epHeadA_val], by rw [epHeadA_val]; omega⟩
    · exact Gep _ ⟨by rw [epTSA_val hE]; omega, by rw [epTSA_val hE]; omega⟩
    · rw [nextA_eq']; exact Gd _ (by simp [nextOff])
    · exact Gq dest (by simp)
    · exact Gq _ (haf hne)
  -- (3) the message, its info word, the badge: the handler's registers
  have hT1 : TcbPlaced ({dest} : Set U64) := fun y hy => by rw [Set.mem_singleton_iff] at hy; subst hy; exact hd'
  have fT5 : L.mem (epFast (L := L) s2 ptr dest) (faultA t) = fl4_abi.consts.fault.VMFault := by
    have fA : Aligned (faultA t) := field_aligned ht' (K := 3376#u64) (by simp) (by simp)
    have nL : ∀ y ∈ T, ∀ Kx : U64, Kx.val < 4096 → Kx.val ≠ 3376 → core.num.U64.wrapping_add y Kx ≠ faultA t :=
      fun y hy Kx hKx hne => field_ne (hT y hy) ht' hKx (K2 := 3376#u64) (by simp) (fun _ => by simpa using hne)
    rw [← fT2]
    refine (epFast_writes (s := s2) (ptr := ptr) (dest := dest)
      (by unfold Aligned; rw [epHeadA_val]; exact hE.align)
      (by unfold Aligned; rw [epTSA_val hE]; have := hE.align; omega)
      (by rw [nextA_eq']; exact field_aligned hd' (by simp [nextOff]) (by simp [nextOff]))
      (by rw [prevA_eq']; exact field_aligned hd' (by simp [prevOff]) (by simp [prevOff]))
      (fun h => by rw [prevA_eq']; exact field_aligned (hT _ (hafT h)) (by simp [prevOff]) (by simp [prevOff]))).mem_eq
      fA ?_
    have vF : (faultA t).val = t.val + 3376 := field_val ht' (K := 3376#u64) (by simp)
    rintro (e | e | e | e | ⟨hne, e⟩)
    · have := congrArg UScalar.val e; rw [epHeadA_val, vF] at this; have := hE.disj t htT; omega
    · have := congrArg UScalar.val e; rw [epTSA_val hE, vF] at this; have := hE.disj t htT; omega
    · rw [nextA_eq'] at e; exact nL dest hdT _ (by simp [nextOff]) (by simp [nextOff]) e.symm
    · rw [prevA_eq'] at e; exact nL dest hdT _ (by simp [prevOff]) (by simp [prevOff]) e.symm
    · rw [prevA_eq'] at e; exact nL _ (hafT hne) _ (by simp [prevOff]) (by simp [prevOff]) e.symm
  have w6 : WritesIn st (epFast (L := L) s2 ptr dest) S6 (XferRegW {dest} ∅) := by
    have := set_mrs_fault_vm_reg (ar := ar) (a := a) (buf := rb) hT1 (Set.mem_singleton dest) fT5
    rw [hmrs, WP.spec_ok] at this; exact this
  have w7 : WritesIn st (epFast (L := L) s2 ptr dest) S7 (XferRegW {dest} ∅) := by
    have := set_msg_info_rgU (mi := mi) hT1 (Set.mem_singleton dest) w6
    rw [hS7, WP.spec_ok] at this; exact this
  have w8 : WritesIn st (epFast (L := L) s2 ptr dest) S8 G := by
    have := set_reg_rgU (r := layout.reg.BADGE) (v := badge) hT1 (Set.mem_singleton dest)
      (by simp [layout.reg.BADGE, layout.reg.RDI]) w7
    rw [hS8, WP.spec_ok] at this
    refine this.mono fun b hb => ?_
    rcases hb with ⟨y, hy, Kx, -, h2, -, rfl⟩ | hb
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact Gd Kx (by omega)
    · exact absurd hb (by simp)
  -- (4) the reply's TCB word, the two states, `t`'s reply word
  have rA : Aligned (rTcbA r) := by unfold Aligned; rw [rTcbA_val0]; have := (hO.rp r hr).1; omega
  have Gr : G (rTcbA r) := Grp _ ⟨by rw [rTcbA_val0], by rw [rTcbA_val0]; omega⟩
  have sdA : Aligned (stA dest) := by rw [stA_eq]; exact field_aligned hd' (by simp) (by simp)
  have Gsd : G (stA dest) := by rw [stA_eq]; exact Gd _ (by simp)
  have w14 : WritesIn st S8 (fS14 (L := L) S8 t dest r) G := by
    unfold fS14 fS13 fS10
    exact wi_wr (wi_wr (wi_wr (wi_wr (wi_wr (wi_wr (WritesIn.refl _ _) rA Gr) sdA Gsd) rA Gr)
      (by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp)) (by rw [stA_eq]; exact Gt _ (by simp)))
      (field_aligned ht' (K := 3360#u64) (by simp) (by simp)) (Gt 3360#u64 (by simp))) sdA Gsd
  -- the handler's SC: active (blocked on receive), well formed
  have hdsc : L.mem s (scA dest) ∈ Scs := (hX0.bound dest hdT HF.sc).1
  obtain ⟨hPl, hZ7⟩ := hO.sc _ hdsc
  have scW : ∀ b, Aligned b → InSC (L.mem s (scA dest)) (Z (L.mem s (scA dest))) b → b ∈ Ω :=
    fun b hb h => hS.sub _ ((hS.all _ hdsc).2.2 b hb h)
  have spWF : L.mem s (sporA (L.mem s (scA dest))) ≠ 0#u64 →
      RefillsWF st s (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    fun h => (hS.all _ hdsc).1 ((hS.act _ hdsc).1 (hS.spor _ hdsc h))
  have hact : L.mem s (scA dest) ∈ Ac :=
    hB.sact dest hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hrecv)))))))) HF.sc
  have hWs : RefillsWF st s (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    (hS.all _ hdsc).1 ((hS.act _ hdsc).1 hact)
  have nrt : ∀ c ∈ Scs, ∀ b, InSC c (Z c) b → b ≠ rTcbA r := fun c hc' b hin e => by
    have := hO.rpSc r hr _ hc'; subst e; unfold InSC at hin; rw [rTcbA_val0] at hin; omega
  have hU := usOff_of E K scW (hS.sub _ (hS.spSg _ hdsc)) spWF (hO.rpSc r hr _ hdsc) hZ7 hPl.fits
  have w15 := unblock_sporadic_fr hU h15
  have esc14 : L.mem (fS14 (L := L) S8 t dest r) (scA dest) = L.mem s (scA dest) :=
    K.tcb dest hdT 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hW14 : RefillsWF st (fS14 (L := L) S8 t dest r) (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    hWs.agree fun b hb hin => K.omg b (scW b hb hin) (nrt _ hdsc b hin)
  have hW15 : RefillsWF st s15 (L.mem s (scA dest)) (Z (L.mem s (scA dest))) := by
    have := unblock_sporadic_wf hU (by rw [esc14]; exact hW14) h15
    rw [esc14] at this; exact this
  rw [esc14] at w15
  have K15 := finKeep15 hT hN hcC hΩ K scW w15
  -- the handler `Running` at `s15`
  have sA : Aligned (stA dest) := by rw [stA_eq]; exact field_aligned hd' (by simp) (by simp)
  have st14 : L.mem (fS14 (L := L) S8 t dest r) (stA dest) = sched.TS_RUNNING := by
    unfold fS14; exact L.mem_wr_same sA
  have st15 : L.mem s15 (stA dest) = sched.TS_RUNNING := by
    rw [w15.mem_eq sA ?_]; exact st14
    rintro (hin | e)
    · exact out_ne_field (hΩ _ (scW _ sA hin.inSC)) hdT hd' (K := 3328#u64) (by simp) (by rw [stA_eq])
    · have eR : L.nodeA (fS14 (L := L) S8 t dest r) layout.node.REPROGRAM =
          L.nodeAt s (L.cpu s) layout.node.REPROGRAM := by
        unfold LawfulStore.nodeA; rw [K.cpu, nodeAt_of_ksb K.ksb]
      rw [eR, stA_eq] at e
      exact node_ne_field hN (by simp [layout.node.REPROGRAM]) hdT hd' (by simp) e.symm
  -- the fast end: the handler's links cleared, then `switch_to`
  try unfold fastFin at hfin
  rw [obj.Tcb.set_sched_next.ok] at hfin; simp only [bind_ok] at hfin
  rw [obj.Tcb.set_sched_prev.ok] at hfin; simp only [bind_ok] at hfin
  obtain ⟨⟨x1, x2⟩, hsw, hx⟩ := bind_eq_ok hfin
  have hx' := ok_inj_ff hx
  simp only [Prod.mk.injEq, true_and] at hx'
  obtain ⟨rfl, rfl⟩ := hx'
  generalize hY : L.wr (L.wr s15 (nextA .Sched dest) 0#u64) (prevA .Sched dest) 0#u64 = Y at hsw
  have nA : Aligned (nextA .Sched dest) := by unfold nextA nextOff; exact field_aligned hd' (by simp) (by simp)
  have pA : Aligned (prevA .Sched dest) := by unfold prevA prevOff; exact field_aligned hd' (by simp) (by simp)
  have kY : L.ksb Y = L.ksb s := by rw [← hY, L.ksb_wr, L.ksb_wr, K15.ksb]
  have cY : L.cpu Y = L.cpu s := by rw [← hY, LawfulStore.cpu_wr, LawfulStore.cpu_wr, K15.cpu]
  have agY : ∀ b, Aligned b → b ≠ nextA .Sched dest → b ≠ prevA .Sched dest → L.mem Y b = L.mem s15 b := by
    intro b hb h1 h2
    rw [← hY, mem_wr_ne' pA hb (Ne.symm h2), mem_wr_ne' nA hb (Ne.symm h1)]
  have lkΩ : ∀ b ∈ Ω, b ≠ nextA .Sched dest ∧ b ≠ prevA .Sched dest := fun b hb =>
    ⟨fun e => out_ne_field (hΩ b hb) hdT hd' (K := 3480#u64) (by simp) (by rw [e]; rfl),
     fun e => out_ne_field (hΩ b hb) hdT hd' (K := 3488#u64) (by simp) (by rw [e]; rfl)⟩
  have lkT : ∀ K : U64, K.val < 4096 → K.val ≠ 3480 → K.val ≠ 3488 →
      core.num.U64.wrapping_add dest K ≠ nextA .Sched dest ∧ core.num.U64.wrapping_add dest K ≠ prevA .Sched dest :=
    fun K hK h1 h2 => ⟨field_ne hd' hd' hK (K2 := 3480#u64) (by simp) (fun _ => by simpa using h1),
      field_ne hd' hd' hK (K2 := 3488#u64) (by simp) (fun _ => by simpa using h2)⟩
  have agΩ : ∀ b ∈ Ω, L.mem Y b = L.mem s15 b := fun b hb => agY b (hΩ b hb).1 (lkΩ b hb).1 (lkΩ b hb).2
  have agT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3480 → K.val ≠ 3488 →
      L.mem Y (core.num.U64.wrapping_add dest K) = L.mem s15 (core.num.U64.wrapping_add dest K) :=
    fun K hK h8 h1 h2 => agY _ (field_aligned hd' hK h8) (lkT K hK h1 h2).1 (lkT K hK h1 h2).2
  -- the placement, the handler's words and the two SCs at `Y`
  have P : TailPld (L := L) T Cs Ω Y dest :=
    (⟨hT, hdT, hN, hcC, hΩ⟩ : TailPld (L := L) T Cs Ω s dest).ksb kY cY
  have escY : L.mem Y (scA dest) = L.mem s (scA dest) := by
    rw [scA_eq, agT _ (by simp) (by simp) (by simp) (by simp)]
    exact K15.tcb dest hdT 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have stY : L.mem Y (stA dest) = sched.TS_RUNNING := by
    rw [stA_eq, agT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact st15
  have eyY : L.mem Y (yieldA dest) = L.mem s (yieldA dest) := by
    rw [show yieldA dest = core.num.U64.wrapping_add dest 3472#u64 from rfl, agT _ (by simp) (by simp) (by simp)
      (by simp)]
    exact K15.tcb dest hdT 3472#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have csA : Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_SC) :=
    nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ecY : L.cscW Y = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [cY, nodeAt_of_ksb kY]
    rw [agY _ csA (fun e => node_ne_field hN (by simp [layout.node.CUR_SC]) hdT hd' (K := 3480#u64) (by simp) e)
      (fun e => node_ne_field hN (by simp [layout.node.CUR_SC]) hdT hd' (K := 3488#u64) (by simp) e)]
    exact K15.node _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  have hWY : RefillsWF st Y (L.mem s (scA dest)) (Z (L.mem s (scA dest))) :=
    hW15.agree fun b hb hin => agΩ b (scW b hb hin)
  have hcs : L.cscW s ∈ Scs := hX0.cur
  have hcq0 : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
    exact ⟨(hS.all _ hcs).1, fun b hb hi => hS.sub _ ((hS.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
  have hcY : SCq st Y Ω (L.cscW Y) (Z (L.cscW Y)) := by
    rw [ecY]
    refine ⟨fun hm => ?_, hcq0.2.1, hcq0.2.2⟩
    by_cases hcd : L.cscW s = L.mem s (scA dest)
    · rw [hcd]; exact hWY
    · have agC : ∀ b, Aligned b → InSC (L.cscW s) (Z (L.cscW s)) b → L.mem Y b = L.mem s b := by
        intro b hb hin
        have hbΩ := hcq0.2.1 b hb hin
        rw [agΩ b hbΩ]
        refine K15.omg b hbΩ (nrt _ hcs b hin) fun hR => ?_
        have := hO.scDisj _ hcs _ hdsc hcd
        unfold InSC at hin; unfold InRing at hR; omega
      have em : L.rmax Y (L.cscW s) = L.rmax s (L.cscW s) := by
        obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
        exact agC _ a1 ⟨a2, a3⟩
      exact (hcq0.1 (em ▸ hm)).agree agC
  have htY : L.mem Y (scA dest) ≠ L.cscW Y → SCin st Y Ω (L.mem Y (scA dest)) (Z (L.mem Y (scA dest))) ∧
      ∀ b, InSC (L.mem Y (scA dest)) (Z (L.mem Y (scA dest))) b → Outside b (L.cscW Y) (Z (L.cscW Y)) := by
    rw [escY, ecY]
    intro hne
    refine ⟨⟨hWY, scW⟩, fun b hin => ?_⟩
    have := hO.scDisj _ hdsc _ hcs hne
    unfold InSC at hin; unfold Outside; omega
  have hyY : L.mem Y (yieldA dest) ≠ 0#u64 → L.mem Y (yieldA dest) ∈ Scs := by
    rw [eyY]; exact hX0.yt.2.1 dest hdT
  -- (5) `unblock_sporadic`, the handler's links, `switch_to`
  have hdF : FootVmTcb (L := L) T s dest := ⟨hdT, Or.inr HF.aff⟩
  have w15' : WritesIn st (fS14 (L := L) S8 t dest r) s15 G := w15.mono fun b hb => by
    rcases hb with hin | e
    · exact Gsc _ b ⟨hdsc, Or.inr ⟨dest, hdF, Or.inl rfl⟩⟩ hin.inSC
    · have eR : L.nodeA (fS14 (L := L) S8 t dest r) layout.node.REPROGRAM =
          L.nodeAt s (L.cpu s) layout.node.REPROGRAM := by
        unfold LawfulStore.nodeA; rw [K.cpu, nodeAt_of_ksb K.ksb]
      rw [e, eR]; exact Gn _ (by simp [layout.node.REPROGRAM])
  have wY : WritesIn st s15 Y G := by
    rw [← hY]
    exact wi_wr (wi_wr (WritesIn.refl _ _) nA (by unfold nextA nextOff; exact Gd _ (by simp)))
      pA (by unfold prevA prevOff; exact Gd _ (by simp))
  have wF := switch_to_foot hA Y a P (ObjsOK.any hO) hS.sub hcY htY hyY (B := G)
    (fun o ho => by rw [cY, nodeAt_of_ksb kY]; exact Gn o ho) Gd
    (fun b hb => by rw [ecY] at hb; exact Gsc _ b ⟨hcs, Or.inl rfl⟩ hb)
    (fun _ b hb => by rw [escY] at hb; exact Gsc _ b ⟨hdsc, Or.inr ⟨dest, hdF, Or.inl rfl⟩⟩ hb)
    (fun hne b hb => by
      rw [eyY] at hne hb
      exact Gsc _ b ⟨hX0.yt.2.1 dest hdT hne, Or.inr ⟨dest, hdF, Or.inr rfl⟩⟩ hb)
  rw [hsw, WP.spec_ok] at wF
  exact wt w1' (wt w5 (wt w8 (wt w14 (wt w15' (wt wY wF)))))

end acc

/-! ## The VM-fault entry beside the gate -/

section top
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **P2 (2a) for `handle_vm_fault_local`**: the local VM-fault entry, accepted
or declined, writes only `FootVm` of its entry state `s`, with `ep` and `r`
the endpoint and reply object fl4-sync's `local_vm_fault` locked (`hLk`: the
fast path's endpoint and its handler's reply object are those). Inputs: `BXI`
at `s`, and at the state after the entry's `update_timestamp` the facts the
P1 analysis of the fast path takes (`VmFootHyps`, what P3's
`JAtZ.vmFaultOK` supplies there). -/
theorem vm_local_foot (hA : P0.ArchTotal ar) {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {s s' : S} {a a' : A} {addr code ep r : U64} {ok' : Bool}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hE : ∀ s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) →
      VmFootHyps (L := L) T Cs Ω U Sg Rp Scs Nt Ac H Z s1)
    (hLk : ∀ s1 a1 ptr badge dest r', sched.update_timestamp st ar s a = ok (s1, a1) →
      FaultChecks st s1 (L.curW s1) ptr badge dest r' → ptr = ep ∧ r' = r)
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (ok', s', a')) :
    WritesIn st s s' (FootVm (L := L) T Scs Z s ep r) := by
  cases ok'
  · exact vm_local_decline_foot hA hI h
  have hN : NodePlaced st T s (L.cpu s) := by
    obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI; exact hSQ.nodes _ hSQ.cur
  have hT : TcbPlaced T := by obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI; exact hSQ.tcbs
  unfold syscall.handle_vm_fault_local at h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨s1, a1⟩, e1, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  obtain ⟨i2, -, h⟩ := bind_eq_ok h
  obtain ⟨f, ef, h⟩ := bind_eq_ok h
  have hf : f = error.Fault.VmFault addr code (i2 != 0#u64) := by
    unfold vspace.vm_fault at ef; exact (ok_inj_ff ef).symm
  subst hf
  have HY := hE s1 a1 e1
  have ht : t = L.curW s1 := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  obtain ⟨ptr, badge, dest, r', hc, hfast⟩ := vm_fault_acc st ar h
  obtain ⟨rfl, rfl⟩ := hLk s1 a1 ptr badge dest r' e1 (by rw [← ht]; exact hc)
  have hF := faultEntAt_ofT HY.bxi et HY.nb HY.cap HY.user HY.buf HY.asid
  obtain ⟨hr, rest, E⟩ := hF.2 ptr badge dest r' hc
  have hrecv := faultRecv_ofT HY.bxi et HY.cap hc
  have w := vm_tail_foot hA HY.bxi ht (set_fault_vm (L := L) s1 t addr code (i2 != 0#u64)) hc hrecv hr E hfast
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok ar hN hn] at e1
  obtain ⟨rfl, -⟩ := Prod.mk.inj (ok_inj_ff e1)
  have wu := utW_writes hN n
  have hEN := E.hEN.1 _ E.hcC
  have eB : L.nodeBase (utW (L := L) s n) (L.cpu (utW (L := L) s n)) = L.nodeBase s (L.cpu s) := by
    simp only [LawfulStore.nodeBase, wu.1, wu.2.1]
  rw [eB] at hEN
  exact wt ((utW_foot hN n).mono fun _ hb => hb.foot)
    (w.mono fun _ hb => FootVm.of_utW hT hN hEN E.hE.fits E.hE.align hb)

end top


/-! ## The accepted VM-fault ReplyRecv -/

theorem tcb_range {y b : U64} (hy : TcbAddr y) (h1 : y.val ≤ b.val) (h2 : b.val < y.val + 4096) :
    ∃ K : U64, K.val < 4096 ∧ b = core.num.U64.wrapping_add y K := by
  have hm : b.val - y.val < 2 ^ 64 := by omega
  refine ⟨⟨BitVec.ofNat 64 (b.val - y.val)⟩, ?_, ?_⟩
  · show (BitVec.ofNat 64 (b.val - y.val)).toNat < 4096
    simp [Nat.mod_eq_of_lt hm]; omega
  · apply UScalar.eq_of_val_eq
    rw [tcb_wadd_val hy (by show (BitVec.ofNat 64 (b.val - y.val)).toNat < 4096; simp [Nat.mod_eq_of_lt hm]; omega)]
    show _ = y.val + (BitVec.ofNat 64 (b.val - y.val)).toNat
    simp [Nat.mod_eq_of_lt hm]; omega

section rr
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 8000000 in
/-- **An accepted VM-fault ReplyRecv fast run writes only `FootVm` of its
dispatch state `X0`**, the reply object `rptr` having no neighbours on a call
stack (`hnb`: fl4-sync `local_syscall` checks it with `rptr` locked). Inputs:
`BXI` and m68's placement `RRPl` at `X0`, m68's ring-sum bound for the
receiver's SC (`hsum`, P1 `RRSum`). -/
theorem rr_tail_foot (hA : P0.ArchTotal ar) {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {X0 sF : S} {a aF : A} {t rptr ep u usc : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X0)
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hC : RRChecksG st ar fl4_abi.consts.fault.VMFault X0 a t rptr ep u usc)
    (hsum : L.mem X0 (sporA usc) ≠ 0#u64 → L.amtSum X0 usc < 2 ^ 64)
    (hnb : L.mem X0 (rPrevA rptr) = 0#u64 ∧ L.mem X0 (rNextA rptr) = 0#u64)
    (h : rrTail st ar X0 a t rptr ep u usc = ok (true, sF, aF)) :
    WritesIn st X0 sF (FootVm (L := L) T Scs Z X0 ep rptr) := by
  unfold rrTail at h
  obtain ⟨X1, e1, h⟩ := bind_eq_ok h
  obtain ⟨⟨X2, a1⟩, e2, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨b9, e3s, h⟩ := bind_eq_ok h
  obtain ⟨X3, e3, h⟩ := bind_eq_ok h
  obtain ⟨⟨restart, X4, a2⟩, e4, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨X5, e5, h⟩ := bind_eq_ok h
  have R3 := rr_r3G ar P hC hsum e1 e2 e3s e3
  obtain ⟨ha1, w1, -, w23, -⟩ := rr_x3G ar P hC hsum e1 e2 e3s e3
  subst ha1
  obtain ⟨hrs, hX4, -⟩ := hfr_vm st ar R3.ft3 e4
  subst hrs
  simp only [↓reduceIte] at h
  obtain ⟨X6, e6, h⟩ := bind_eq_ok h
  obtain ⟨X7, e7, h⟩ := bind_eq_ok h
  obtain ⟨X8, e8, h⟩ := bind_eq_ok h
  obtain ⟨X9, e9, h⟩ := bind_eq_ok h
  obtain ⟨X10, e10, h⟩ := bind_eq_ok h
  obtain ⟨X11, e11, h⟩ := bind_eq_ok h
  obtain ⟨X12, e12, h⟩ := bind_eq_ok h
  obtain ⟨X13, e13, h⟩ := bind_eq_ok h
  obtain ⟨X14, e14, h⟩ := bind_eq_ok h
  obtain ⟨X15, e15, h⟩ := bind_eq_ok h
  obtain ⟨⟨x1, x2⟩, hsw, hx⟩ := bind_eq_ok h
  have hx' := ok_inj_ff hx
  simp only [Prod.mk.injEq, true_and] at hx'
  obtain ⟨rfl, rfl⟩ := hx'
  obtain ⟨-, -, K8, -⟩ := rr_x8G ar P hC hsum e1 e2 e3s e3 e4 e5 e6 e7 e8
  obtain ⟨-, -, -, -, -, hW3, -⟩ := rr_x3G ar P hC hsum e1 e2 e3s e3
  obtain ⟨om38, su8⟩ := rr_om38 ar P K8.ksb K8.cpu e4 e5 e6 e7 e8
  obtain ⟨k15, c15, m15⟩ := rr_m15 P e9 e10 e11 e12 e13 e14 e15
  obtain ⟨-, -, hX, -, hS0⟩ := hI
  have hX0 : ScExtra0 st T Cs Scs Nt X0 := hX.2.2.toScExtra0
  have hO := P.hO
  have hT := P.hT
  have hu' := hT u P.hu
  have ht' := hT t P.ht
  have ua := hu'.align; have ta := ht'.align
  have hut : u.val ≠ t.val := fun e => P.hut (UScalar.eq_of_val_eq e)
  have hrΩ := P.hSg.sub _ P.rtS
  -- Ω words pass `m15`'s side conditions
  have m15Ω : ∀ b ∈ Ω, b ≠ rTcbA rptr → L.mem X15 b = L.mem X8 b := fun b hb hne =>
    m15 b (P.hΩ b hb).1 ((P.hΩ b hb).2.1 t P.ht) (P.hEΩ b hb) (fun e => hne (UScalar.eq_of_val_eq e))
  -- u's words too
  have m15u : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem X15 (core.num.U64.wrapping_add u K) = L.mem X8 (core.num.U64.wrapping_add u K) := by
    intro K hK h8
    have v := tcbw_val hT P.hu hK
    have hed := P.hE.disj u P.hu
    have hro := (P.hΩ _ hrΩ).2.1 u P.hu
    exact m15 _ (field_aligned hu' hK h8) (by rw [v]; omega) (by rw [v]; omega) (by rw [v]; omega)
  have kX : L.ksb X15 = L.ksb X0 := k15.trans K8.ksb
  have cX : L.cpu X15 = L.cpu X0 := c15.trans K8.cpu
  -- SC facts
  have nrp : ∀ c ∈ Scs, ∀ b, InSC c (Z c) b → ¬ RpLW Rp b ∧ b ≠ rTcbA rptr := by
    intro c hc b hin
    unfold InSC at hin
    refine ⟨?_, fun e => ?_⟩
    · rintro ⟨r', hr', rfl | rfl⟩
      · have := hO.rpSc r' hr' _ hc; rw [rPrevA_val (hO.rp r' hr')] at hin; omega
      · have := hO.rpSc r' hr' _ hc; rw [rNextA_val (hO.rp r' hr')] at hin; omega
    · have := hO.rpSc rptr P.hrR _ hc; rw [e, rTcbA_val0] at hin; omega
  have scWu : ∀ b, Aligned b → InSC usc (Z usc) b → b ∈ Ω := fun b hb h => P.hSg.sub _ (P.scSg b hb h)
  have hWX : RefillsWF st X15 usc (Z usc) := hW3.agree fun b hb hin => by
    rw [m15Ω b (scWu b hb hin) (nrp _ P.hcS b hin).2, om38 b (scWu b hb hin)]
  have hcs : L.cscW X0 ∈ Scs := hX0.cur
  have hcq0 : SCq st X0 Ω (L.cscW X0) (Z (L.cscW X0)) := by
    obtain ⟨hP', hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP' hz
    have hv := sc_word_val hP' hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
    exact ⟨(hS0.all _ hcs).1, fun b hb hi => hS0.sub _ ((hS0.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
  have csA : Aligned (L.nodeAt X0 (L.cpu X0) layout.node.CUR_SC) :=
    nodeAt_aligned P.hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ecX : L.cscW X15 = L.cscW X0 := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX]
    have v := nodeAt_val P.hN (off := layout.node.CUR_SC) (by simp [layout.node.CUR_SC])
    have hnt := P.hN.disj t P.ht
    have hne := P.hEN.1 _ P.hcC
    have hro := (P.hΩ _ hrΩ).2.2 _ P.hcC
    have c24 : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]
    rw [m15 _ csA (by rw [v]; omega) (by rw [v]; omega) (by rw [v]; omega)]
    exact K8.node _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  have escX : L.mem X15 (scA u) = usc := by
    rw [scA_eq, m15u _ (by simp) (by simp)]
    rw [K8.tcb u P.hu 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), ← scA_eq]
    exact P.husc
  have stX : L.mem X15 (stA u) = sched.TS_RESTART := by
    rw [stA_eq, m15u _ (by simp) (by simp), ← stA_eq]; exact su8
  have eyX : L.mem X15 (yieldA u) = L.mem X0 (yieldA u) := by
    rw [show yieldA u = core.num.U64.wrapping_add u 3472#u64 from rfl, m15u _ (by simp) (by simp)]
    exact K8.tcb u P.hu 3472#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have hcX : SCq st X15 Ω (L.cscW X15) (Z (L.cscW X15)) := by
    rw [ecX]
    refine ⟨fun hm => ?_, hcq0.2.1, hcq0.2.2⟩
    by_cases hcd : L.cscW X0 = usc
    · rw [hcd]; exact hWX
    · have agC : ∀ b, Aligned b → InSC (L.cscW X0) (Z (L.cscW X0)) b → L.mem X15 b = L.mem X0 b := by
        intro b hb hin
        have hbΩ := hcq0.2.1 b hb hin
        obtain ⟨n1, n2⟩ := nrp _ hcs b hin
        rw [m15Ω b hbΩ n2]
        refine K8.omg b ⟨hbΩ, n1⟩ n2 fun hR => ?_
        have := hO.scDisj _ hcs _ P.hcS hcd
        unfold InSC at hin; unfold InRing at hR; omega
      have em : L.rmax X15 (L.cscW X0) = L.rmax X0 (L.cscW X0) := by
        obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
        exact agC _ a1 ⟨a2, a3⟩
      exact (hcq0.1 (em ▸ hm)).agree agC
  have htX : L.mem X15 (scA u) ≠ L.cscW X15 → SCin st X15 Ω (L.mem X15 (scA u)) (Z (L.mem X15 (scA u))) ∧
      ∀ b, InSC (L.mem X15 (scA u)) (Z (L.mem X15 (scA u))) b → Outside b (L.cscW X15) (Z (L.cscW X15)) := by
    rw [escX, ecX]
    intro hne
    refine ⟨⟨hWX, scWu⟩, fun b hin => ?_⟩
    have := hO.scDisj _ P.hcS _ hcs hne
    unfold InSC at hin; unfold Outside; omega
  have hyX : L.mem X15 (yieldA u) ≠ 0#u64 → L.mem X15 (yieldA u) ∈ Scs := by
    rw [eyX]; exact hX0.yt.2.1 u P.hu
  have PX : TailPld (L := L) T Cs Ω X15 u :=
    (⟨hT, P.hu, P.hN, P.hcC, P.hΩ⟩ : TailPld (L := L) T Cs Ω X0 u).ksb kX cX
  -- the footprint and its words
  generalize hG : FootVm (L := L) T Scs Z X0 ep rptr = G
  have HF := here_facts (L := L) (by obtain ⟨b, eb, hb⟩ := hC.here; rw [eb, hb])
  have huF : FootVmTcb (L := L) T X0 u := ⟨P.hu, Or.inr HF.aff⟩
  have Gt : ∀ K : U64, K.val < 4096 → G (core.num.U64.wrapping_add t K) := fun K hK => by
    rw [← hG]; exact (footVm_tcb ⟨P.ht, Or.inl P.hcur.symm⟩ hK).foot
  have Gu : ∀ K : U64, K.val < 4096 → G (core.num.U64.wrapping_add u K) := fun K hK => by
    rw [← hG]; exact (footVm_tcb huF hK).foot
  have Gn : ∀ o : U64, o.val < 4288 → G (L.nodeAt X0 (L.cpu X0) o) := fun o ho => by
    rw [← hG]; exact (footVm_node ho).foot
  have Gsc : ∀ c b, FootVmSc (L := L) T Scs X0 c → InSC c (Z c) b → G b := fun c b hc' hb => by
    rw [← hG]; exact Or.inl (Or.inr (Or.inr ⟨c, hc', hb⟩))
  have Gep : ∀ b, InObj ep 16 b → G b := fun b hb => by rw [← hG]; exact Or.inr (Or.inl hb)
  have Grp : ∀ b, InObj rptr 32 b → G b := fun b hb => by rw [← hG]; exact Or.inr (Or.inr (Or.inl hb))
  have hrp := P.hO.rp rptr P.hrR
  have GrT : G (rTcbA rptr) := Grp _ ⟨by rw [rTcbA_val0], by rw [rTcbA_val0]; omega⟩
  have Gst : G (stA t) := by rw [stA_eq]; exact Gt _ (by simp)
  have Gsu : G (stA u) := by rw [stA_eq]; exact Gu _ (by simp)
  have uscF : FootVmSc (L := L) T Scs X0 usc := ⟨P.hcS, Or.inr ⟨u, huF, Or.inl P.husc.symm⟩⟩
  -- X0 → X1: t's state
  have w01 : WritesIn st X0 X1 G := by rw [w1]; exact wi_wr (WritesIn.refl _ _) (P.aS P.ht) Gst
  -- X1 → X2: the reply unlink, the reply having no neighbours
  have aNx : Aligned (rNextA rptr) := (P.rpA rptr P.hrR).2
  have aPv : Aligned (rPrevA rptr) := (P.rpA rptr P.hrR).1
  have ntS : ∀ b ∈ Ω, b ≠ stA t := fun b hb => by rw [stA_eq]; exact P.omg_tcb hb P.ht (by decide)
  have mNx : L.mem X1 (rNextA rptr) = 0#u64 := by
    rw [w1, mem_wr_ne' (P.aS P.ht) aNx (Ne.symm (ntS _ (P.hSg.sub _ (P.hO.nextW P.hrR))))]; exact hnb.2
  have mPv : L.mem X1 (rPrevA rptr) = 0#u64 := by
    rw [w1, mem_wr_ne' (P.aS P.ht) aPv (Ne.symm (ntS _ (P.hSg.sub _ (P.hO.prevW P.hrR))))]; exact hnb.1
  have hrΩ := P.hSg.sub _ P.rtS
  have aR : Aligned (rTcbA rptr) := (P.hΩ _ hrΩ).1
  have hRT : rTcbA rptr ≠ stA u := by rw [stA_eq]; exact P.omg_tcb hrΩ P.hu (by decide)
  have hcur1 : ∀ X, WritesIn st X1 X (fun b => RpLW {rptr} b ∨ b = rTcbA rptr ∨ b = stA u) → L.curW X ≠ u := by
    intro X wX
    have aC : Aligned (L.nodeAt X0 (L.cpu X0) layout.node.CUR_THREAD) :=
      nodeAt_aligned P.hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
    have k1 : L.ksb X1 = L.ksb X0 := by rw [w1, L.ksb_wr]
    have c1 : L.cpu X1 = L.cpu X0 := by rw [w1, L.cpu_wr]
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD) ≠ u
    rw [wX.2.1, c1, nodeAt_of_ksb (wX.1.trans k1)]
    rw [wX.2.2 _ aC ?_]
    · have nC : stA t ≠ L.nodeAt X0 (L.cpu X0) layout.node.CUR_THREAD := by
        rw [stA_eq]; exact P.tcb_node P.ht (by decide) (by simp [layout.node.CUR_THREAD])
      rw [w1, mem_wr_ne' (P.aS P.ht) aC nC]
      have := P.hcur; unfold LawfulStore.curW at this; rw [this]; exact Ne.symm P.hut
    rintro (⟨r', hr', hh⟩ | hh | hh)
    · rw [Set.mem_singleton_iff] at hr'; rw [hr'] at hh
      exact P.omg_node (P.hSg.sub _ (P.rpS _ ⟨_, P.hrR, hh⟩)) (by simp [layout.node.CUR_THREAD]) rfl
    · exact P.omg_node hrΩ (by simp [layout.node.CUR_THREAD]) hh.symm
    · rw [stA_eq] at hh; exact P.tcb_node P.hu (by decide) (by simp [layout.node.CUR_THREAD]) hh.symm
  have hn1 : (∃ i, obj.Reply.next st rptr X1 = ok i ∧ ¬ (i != 0#u64) = true) ∨
      (∃ i, obj.Reply.next st rptr X1 = ok i ∧ (i != 0#u64) = true ∧
        ∃ b, obj.Reply.next_is_head st rptr X1 = ok b ∧ ¬ b = true) :=
    Or.inl ⟨_, eq_of_spec_fd (obj.Reply.next.spec (L := L) X1 rptr), by rw [mNx]; simp⟩
  obtain ⟨-, w12', -⟩ := rr_remove_foot (Rp := {rptr}) ar hn1 (fun h0 => absurd (by rw [mNx]; simp) h0)
    (fun h0 => absurd (by rw [mPv]; simp) h0)
    (fun r' hr' => by rw [Set.mem_singleton_iff] at hr'; subst hr'; exact ⟨aPv, aNx⟩)
    (Set.mem_singleton rptr) aR (P.aS P.hu) hRT hcur1 e2
  have w12 : WritesIn st X1 X2 G := w12'.mono fun b hb => by
    rcases hb with ⟨r', hr', e | e⟩ | e | e
    · rw [Set.mem_singleton_iff] at hr'; subst hr' e
      exact Grp _ ⟨by rw [rPrevA_val hrp]; omega, by rw [rPrevA_val hrp]; omega⟩
    · rw [Set.mem_singleton_iff] at hr'; subst hr' e
      exact Grp _ ⟨by rw [rNextA_val hrp]; omega, by rw [rNextA_val hrp]; omega⟩
    · rw [e]; exact GrT
    · rw [e]; exact Gsu
  -- X2 → X3: u's SC, the core's REPROGRAM
  have w23' : WritesIn st X2 X3 G := w23.mono fun b hb => by
    rcases hb with hin | e
    · exact Gsc usc b uscF hin.inSC
    · rw [e]; exact Gn _ (by simp [layout.node.REPROGRAM])
  -- X3 → X5: the fault reply writes nothing, then u's fault type
  have e5' := e5
  rw [hX4] at e5'
  have x5 : X5 = L.wr X3 (faultA u) fl4_abi.consts.fault.NullFault := by
    unfold faults.clear_fault at e5'
    have := obj.Tcb.set_fault_type.spec (L := L) X3 u fl4_abi.consts.fault.NullFault
    rw [e5', WP.spec_ok] at this; exact this
  have hu' := P.hT u P.hu
  have w35 : WritesIn st X3 X5 G := by
    rw [x5]; exact wi_wr (WritesIn.refl _ _) (field_aligned hu' (K := 3376#u64) (by simp) (by simp))
      (Gu 3376#u64 (by simp))
  -- X5 → X8: u's state, the action, t's state
  have x6 : X6 = L.wr X5 (stA u) sched.TS_RESTART := by
    have := obj.Tcb.set_state.spec (L := L) X5 u sched.TS_RESTART; rw [e6, WP.spec_ok] at this; exact this
  have x7 : X7 = L.wr X6 (L.nodeAt X6 (L.cpu X6) layout.node.SCHED_ACTION) u := by
    rw [set_action_ok] at e7; exact (ok_inj_ff e7).symm
  have x8 : X8 = L.wr X7 (stA t) sched.TS_RUNNING := by
    have := obj.Tcb.set_state.spec (L := L) X7 t sched.TS_RUNNING; rw [e8, WP.spec_ok] at this; exact this
  have w05 := wt w01 (wt w12 (wt w23' w35))
  have w06 : WritesIn st X0 X6 G := by rw [x6]; exact wi_wr w05 (P.aS P.hu) Gsu
  have w07 : WritesIn st X0 X7 G := by
    rw [x7, w06.2.1, nodeAt_of_ksb w06.1]
    exact wi_wr w06 (nodeAt_aligned P.hN (by rw [act_val]; omega) (by rw [act_val]))
      (Gn _ (by rw [act_val]; omega))
  have w08 : WritesIn st X0 X8 G := by rw [x8]; exact wi_wr w07 (P.aS P.ht) Gst
  -- X8 → X15: t blocked on the endpoint
  have ht' := P.hT t P.ht
  have w815 : WritesIn st X8 X15 G := by
    refine ⟨k15, c15, fun b hb hn => ?_⟩
    refine m15 b hb ?_ ?_ ?_
    · by_contra hc
      have h1 : t.val ≤ b.val := by omega
      have h2 : b.val < t.val + 4096 := by omega
      obtain ⟨K, hK, rfl⟩ := tcb_range (b := b) ht' h1 h2
      exact hn (Gt K hK)
    · by_contra hc
      have := P.hE.align
      have hb8 : b.val % 8 = 0 := hb
      exact hn (Gep b ⟨by omega, by omega⟩)
    · intro e; exact hn (by rw [UScalar.eq_of_val_eq e]; exact GrT)
  -- X15 → sF: `switch_to u`
  have wF := switch_to_foot hA X15 a2 PX (ObjsOK.any hO) P.hSg.sub hcX htX hyX (B := G)
    (fun o ho => by rw [cX, nodeAt_of_ksb kX]; exact Gn o ho) Gu
    (fun b hb => by rw [ecX] at hb; exact Gsc _ b ⟨hcs, Or.inl rfl⟩ hb)
    (fun _ b hb => by rw [escX] at hb; exact Gsc _ b uscF hb)
    (fun hne b hb => by
      rw [eyX] at hne hb
      exact Gsc _ b ⟨hX0.yt.2.1 u P.hu hne, Or.inr ⟨u, huF, Or.inr rfl⟩⟩ hb)
  rw [hsw, WP.spec_ok] at wF
  exact wt w08 (wt w815 wF)

end rr


/-- The footprint after a write of a TCB register word is the one before. -/
theorem FootVm.of_reg {T Scs : Set U64} {Z : U64 → Nat} {s : S} {y K v ep r b : U64} (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s)) (hy : y ∈ T) (hK : K.val < 3328) (hK8 : K.val % 8 = 0)
    (hE : EpPlaced T ep)
    (h : FootVm (L := L) T Scs Z (L.wr s (core.num.U64.wrapping_add y K) v) ep r b) :
    FootVm (L := L) T Scs Z s ep r b := by
  have hya := hT y hy
  have aW : Aligned (core.num.U64.wrapping_add y K) := field_aligned hya (by omega) hK8
  have vW := field_val hya (K := K) (by omega)
  have nN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s (core.num.U64.wrapping_add y K) v) (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o ho h8 => mem_wr_ne' aW (nodeAt_aligned hN ho h8)
      (fun e => node_ne_field hN ho hy hya (by omega) e.symm)
  refine FootVm.of_agree (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) ?_ ?_ ?_ ?_ h
  · show L.mem _ (L.nodeAt _ _ _) = _
    rw [L.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
    exact nN _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  · show L.mem _ (L.nodeA _ _) = L.mem _ (L.nodeA _ _)
    unfold LawfulStore.nodeA
    rw [L.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
    exact nN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  · intro y' hy' K' hK'
    have hy'a := hT y' hy'
    exact mem_wr_ne' aW (field_aligned hy'a (by omega) (by omega))
      (tcbw_ne hya hy'a (by omega) (by omega) (Or.inr (by omega)))
  · have hd := hE.disj y hy
    have ha : L.mem (L.wr s (core.num.U64.wrapping_add y K) v) (epHeadA ep) = L.mem s (epHeadA ep) :=
      mem_wr_ne' aW (by unfold Aligned; rw [epHeadA_val]; exact hE.align)
        (fun e => by have := congrArg UScalar.val e; rw [epHeadA_val, vW] at this; omega)
    have ht : L.mem (L.wr s (core.num.U64.wrapping_add y K) v) (epTSA ep) = L.mem s (epTSA ep) :=
      mem_wr_ne' aW (by unfold Aligned; rw [epTSA_val hE]; have := hE.align; omega)
        (fun e => by have := congrArg UScalar.val e; rw [epTSA_val hE, vW] at this; omega)
    unfold LawfulStore.epQ; rw [ha, ht]

section rrtop
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **P2 (2a) for `handle_reply_recv_vm_local`**: the local VM-fault
ReplyRecv entry, accepted or declined, writes only `FootVm` of its entry
state `s`, with `found = (rptr, ep)` the reply object and endpoint fl4-sync's
`local_syscall` locked. Inputs: `BXI` at `s`; fl4-sync's check under the
lock that the reply has no neighbours on a call stack (`hnb`); and at the
dispatch state after the prefix (`LocalPre`), `BXI`, m68's ring-sum bound
`RRSum` (P1's `RRSumAt` [J] at the top) and m68's placement `RRPl` (what P1
`rrPl_ofG` gives there). -/
theorem rr_vm_local_foot (hA : P0.ArchTotal ar) {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap}
    {Z : U64 → Nat} {s s' : S} {a a' : A} {rptr ep : U64} {ok' : Bool}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hD : ∀ s2 a2, LocalPre (st := st) ar s a (s2, a2) → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧
      RRSum (L := L) Scs s2 ∧ ∀ u usc, RRChecksG st ar fl4_abi.consts.fault.VMFault s2 a2 (L.curW s) rptr ep u usc →
        RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z s2 (L.curW s) rptr ep u usc)
    (hnb : L.mem s (rPrevA rptr) = 0#u64 ∧ L.mem s (rNextA rptr) = 0#u64)
    (h : syscall.handle_reply_recv_vm_local st ar s a (rptr, ep) = ok (ok', s', a')) :
    WritesIn st s s' (FootVm (L := L) T Scs Z s ep rptr) := by
  cases ok'
  · exact rr_vm_local_decline_foot hA hI h
  have hN : NodePlaced st T s (L.cpu s) := by
    obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI; exact hSQ.nodes _ hSQ.cur
  have hT : TcbPlaced T := by obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI; exact hSQ.tcbs
  have hcT : L.curW s ∈ T := by obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI; exact hSQ.curT
  unfold syscall.handle_reply_recv_vm_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨csc, -, h⟩ := bind_eq_ok h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  try dsimp only at h
  have ht : t = L.curW s := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  subst ht
  have hpre : LocalPre (st := st) ar s a (s2, a1) := ⟨_, nx, s1, et, enx, es1, eu⟩
  obtain ⟨hI2, hS2, hP2⟩ := hD s2 a1 hpre
  obtain ⟨u, usc, hC, hfast⟩ := reply_recv_vm_found_acc st ar h
  have P := hP2 u usc hC
  -- the prefix: `FAULT_IP`, then the timestamp
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s (L.curW s) layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
    (hT _ hcT) (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨K, hK, e1⟩ := hW1
  have hK' : K.val = 392 := by rw [hK]; simp [layout.reg.FAULT_IP]
  obtain ⟨⟨n, a3⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  rw [update_timestamp_ok ar hN1 hn] at eu
  obtain ⟨rfl, -⟩ := Prod.mk.inj (ok_inj_ff eu)
  have wpre : WritesIn st s (utW (L := L) s1 n) (FootVmCore (L := L) T Scs Z s) :=
    localPre_foot hA hT hN hcT hpre
  -- the reply's link words at the dispatch state are those at `s`
  have wsm : WritesIn st s (utW (L := L) s1 n) (fun b => b = core.num.U64.wrapping_add (L.curW s) K ∨
      b = ctA (L := L) s1 ∨ b = cnA (L := L) s1) := by
    have w1 : WritesIn st s s1 (· = core.num.U64.wrapping_add (L.curW s) K) := by
      rw [e1]; exact writesIn_wr (field_aligned (hT _ hcT) (by omega) (by omega))
    exact (w1.trans (utW_writes hN1 n)).mono fun b hb => by
      rcases hb with h1 | h2 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
  have keepΩ : ∀ x ∈ Ω, L.mem (utW (L := L) s1 n) x = L.mem s x := by
    intro x hx
    have hO := P.hΩ x hx
    refine wsm.mem_eq hO.1 ?_
    have hcpu : L.cpu (utW (L := L) s1 n) ∈ Cs := P.hcC
    have eC : L.cpu (utW (L := L) s1 n) = L.cpu s1 := wsm.2.1.trans (by rw [e1, LawfulStore.cpu_wr])
    have eB : L.nodeBase (utW (L := L) s1 n) (L.cpu s1) = L.nodeBase s1 (L.cpu s1) := by
      simp only [LawfulStore.nodeBase]; rw [(utW_writes hN1 n).1]
    have hc1 := hO.2.2 _ hcpu
    rw [eC, eB] at hc1
    rintro (e | e | e)
    · have := hO.2.1 _ hcT; rw [e, field_val (hT _ hcT) (by omega)] at this; omega
    · have := nodeAt_val hN1 (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
      have e' := congrArg UScalar.val e; unfold ctA at e'; rw [this] at e'
      simp [layout.node.CUR_TIME] at e'; omega
    · have := nodeAt_val hN1 (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
      have e' := congrArg UScalar.val e; unfold cnA at e'; rw [this] at e'
      simp [layout.node.CONSUMED] at e'; omega
  have hnb2 : L.mem (utW (L := L) s1 n) (rPrevA rptr) = 0#u64 ∧ L.mem (utW (L := L) s1 n) (rNextA rptr) = 0#u64 :=
    ⟨by rw [keepΩ _ (P.hSg.sub _ (P.hO.prevW P.hrR))]; exact hnb.1,
     by rw [keepΩ _ (P.hSg.sub _ (P.hO.nextW P.hrR))]; exact hnb.2⟩
  have w := rr_tail_foot hA hI2 P hC (hS2 usc P.hcS) hnb2 hfast
  -- the footprint at the dispatch state is the one at `s`
  have hk1 : L.ksb s1 = L.ksb s := by rw [e1, L.ksb_wr]
  have hc1 : L.cpu s1 = L.cpu s := by rw [e1, LawfulStore.cpu_wr]
  have hEN := P.hEN.1 _ P.hcC
  have eB2 : L.nodeBase (utW (L := L) s1 n) (L.cpu (utW (L := L) s1 n)) = L.nodeBase s1 (L.cpu s1) := by
    simp only [LawfulStore.nodeBase, (utW_writes hN1 n).1, (utW_writes hN1 n).2.1]
  rw [eB2] at hEN
  refine wt (wpre.mono fun _ hb => hb.foot) (w.mono fun b hb => ?_)
  have h1 := FootVm.of_utW hT hN1 hEN P.hE.fits P.hE.align hb
  rw [e1] at h1
  exact FootVm.of_reg hT hN hcT (by omega) (by omega) P.hE h1

end rrtop

end

end Fl4Proofs.P2

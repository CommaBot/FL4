/-
P3 (p3J gen 26): **the pieces of `syscall.finish`'s footprint at the P1/P2 level** (for `FinFootJ`, P3JMcFin).

* **`IdlK Cs s0 s`**: the key-space base kept and every core's node identity words (`IDLE_THREAD` at 8, `IDLE_SC`
  at 32) of `s0` kept. FL4 writes these two words only in `create_idle_thread` (crates/fl4-core/src/boot.rs
  l.695/699); here that is proved for `timer::fire`, without P2's `FCtx` (which asks every core's idle thread in
  `T`, false for the multicore projection's foreign cores):
  `idlK_footN` (any `FootN` step: its `IdW` excludes `IdN`), `FFoot.idl` (any `FFoot` step: `IdW` plus donation
  words, which are TCB / SC words), and **`vcpu.report.idlF` / `notification.send_signal.idlF` /
  `timer.fire_loop.idlF` / `timer.fire.idlF`**: P2's VCPU-word walk of `fire` (VcpuExitV, vk's `FKI` walk with
  `Kp = Il = Ks = ∅`) re-run with the frame `IdlK` in place of `VcpuWK` (text copy; the four `FootN` frames
  take the node placement of their start state).
* **`TWS Scs Z y s0`**: `activate_thread`'s words, sharper than P2's `TW`: `TW`'s first kind
  (`OutsideObjs ∧ NoHdr`: "any word outside the TCBs and nodes") is in fact only SC words — the `CONSUMED`
  and `YIELD_FROM` words `complete_yield_to` writes (`set_consumed` writes message register 0, a CPU register:
  no IPC-buffer word is written). So `TWS` = words of an SC of `Scs`, `y`'s register words, `y`'s
  `YIELD_TO` and `STATE`, and the executing core's `SCHED_ACTION`. `tws_sc`, `tws_reg`,
  `schedcontext.update_consumed.tws`, `schedcontext.set_consumed.tws`, `schedcontext.cancel_yield_to.tws`,
  `schedcontext.complete_yield_to.tws`, **`sched.activate_thread.tws`** (copies of P2/EntryTail's `.tw`
  lemmas with `TWS`).

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P2.VcpuExitV
import Fl4Proofs.P2.VcpuExitI
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64}

/-! ## The node identity words kept -/

/-- **Every core's `IDLE_THREAD` / `IDLE_SC` node word of `s0` kept** (module docstring). -/
def IdlK (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (s0 s : S) : Prop :=
  L.ksb s = L.ksb s0 ∧ ∀ c ∈ Cs, ∀ o : U64, (o.val = 8 ∨ o.val = 32) →
    L.mem s (L.nodeAt s0 c o) = L.mem s0 (L.nodeAt s0 c o)

theorem IdlK.refl (s : S) : IdlK st Cs s s := ⟨rfl, fun _ _ _ _ => rfl⟩

theorem IdlK.trans' {s0 s1 s2 : S} (h1 : IdlK st Cs s0 s1) (h2 : IdlK st Cs s1 s2) : IdlK st Cs s0 s2 :=
  ⟨h2.1.trans h1.1, fun c hc o ho => by
    have e := h2.2 c hc o ho
    rw [nodeAt_of_ksb h1.1] at e
    exact e.trans (h1.2 c hc o ho)⟩

theorem idOff_idl {cur nd : Prop} {o : Nat} (ho : o = 8 ∨ o = 32) : IdOff cur nd o :=
  ho.elim Or.inl fun h => Or.inr (Or.inl h)

/-- A `FootN` step keeps the node identity words. -/
theorem idlK_footN {Kp : Set U64} {Nd : Prop} {s s' : S} (NP : ∀ c ∈ Cs, NodePlaced st T s c)
    (f : FootN st Kp Nd T Cs Sg Scs Z Es s s') : IdlK st Cs s s' :=
  ⟨f.1, fun c hc o ho => f.idKeep (nodeAt_aligned (NP c hc) (by omega) (by omega))
    (Or.inl ⟨c, hc, o, idOff_idl ho, rfl⟩)⟩

/-- An `FFoot` step keeps the node identity words. -/
theorem FFoot.idl {Kp Il Ks : Set U64} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {s s' : S} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (f : FFoot st Kp Il Ks T Cs Sg Scs Z Es U s s') : IdlK st Cs s s' := by
  refine ⟨f.1, fun c hc o ho => ?_⟩
  have hN := hq.nodes c hc
  have ho' : o.val < 4288 := by omega
  refine f.mem_eq (nodeAt_aligned hN ho' (by omega)) ?_
  rintro (⟨-, hn⟩ | ⟨z, hzT, -, -, e | e⟩ | ⟨k, hk, -, e⟩)
  · exact hn (Or.inl ⟨c, hc, o, idOff_idl ho, rfl⟩)
  · rw [scA_eq] at e
    exact node_ne_field hN ho' hzT (hq.tcbs z hzT) (by simp) e
  · rw [affA_eq] at e
    exact node_ne_field hN ho' hzT (hq.tcbs z hzT) (by simp) e
  · obtain ⟨-, ⟨a2, i2⟩⟩ := sclink_in hO hk
    exact out_ne_node (hq.omega _ (hO.scW _ hk _ a2 i2)) hc hN ho' (congrArg UScalar.val e)

/-! ## `fire` keeps the node identity words (P2 VcpuExitV's walk, frame `IdlK`) -/

/-- `vcpu.report` of a `TS_RUNNING_VM` thread keeps every node identity word (`RepW` is
an `FFoot`; `set_thread_state` a `FootN ∅ True` step). -/
theorem vcpu.report.idlF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t badge : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hvm : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (hc : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) = 0#u64)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true t ⦃ b => BufOK U b ⦄) :
    vcpu.report st ar s a t badge ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      L.mem s' (stA t) = sched.TS_RUNNING ∧ IdlK st Cs s s' ⦄ := by
  have h0 := h
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -⟩ := h0
  refine WP.spec_mono (WP.spec_and (vcpu.report.xf hA s a t badge h ht hvm hc hU hbuf)
    (vcpu.report.blk hA s a t badge h ht hvm hc hU hbuf)) ?_
  rintro s' ⟨⟨s1, h1, st1, w1, e⟩, hb', st'⟩
  have V1 : IdlK st Cs s s1 :=
    FFoot.idl hq hX.1 (RepW.ff (Kp := (∅ : Set U64)) (Il := (∅ : Set U64)) (Ks := (∅ : Set U64)) (Es := ∅)
      (U := U) hq hX.1 ht hU w1)
  obtain ⟨⟨Q1, R1, hq1⟩, -, -, -, -⟩ := h1
  have F2 := sched.set_thread_state.kwNP (Kp := (∅ : Set U64)) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := ∅) s1 t sched.TS_RUNNING hq.tcbs hq1.nodes hq1.cur ht (Set.notMem_empty t)
  rw [e, WP.spec_ok] at F2
  exact ⟨hb', st', V1.trans' (idlK_footN hq1.nodes F2)⟩

/-- **`send_signal` keeps every node identity word** (vk's `send_signal.fk` with no
protected threads). -/
theorem notification.send_signal.idlF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt)
    (hH : H n = some .ntfn) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    :
    notification.send_signal st ar s a n badge ⦃ s' _ => IdlK st Cs s s' ⦄ := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hNb := hX.2.2.ntb
  have hT := h0.tcbs
  have hb0 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩
  have saK : notification.set_active st s n badge ⦃ s' => IdlK st Cs s s' ⦄ :=
    WP.spec_mono (notification.set_active.fn (Kp := (∅ : Set U64)) (Nd := True) s n badge h0 hX hSg hn hH)
      fun s' f => idlK_footN h0.nodes f
  unfold notification.send_signal
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  refine sig_if _ _ _ _ (fun hidl => ?_) (fun hnidl => ?_)
  · -- an idle notification
    step with obj.Ntfn.bound_tcb.val as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    have OLD : (do
        let s1 ← notification.set_active st s n badge
        if b = true then ok (s1, a)
        else do
          let i2 ← obj.Tcb.state st i s1
          if i2 = sched.TS_RUNNING_VM then notification.kick_guest st ar s1 a i else ok (s1, a))
        ⦃ s' _ => IdlK st Cs s s' ⦄ := by
      refine WP.spec_bind saK fun s1 k1 => ?_
      refine sig_if _ _ _ _ (fun _ => (WP.spec_ok _).2 k1) (fun _ => ?_)
      step with obj.Tcb.state.spec
      refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => (WP.spec_ok _).2 k1)
      refine WP.spec_mono (notification.kick_guest.same hA s1 a i) fun r hr => ?_
      obtain ⟨s', a'⟩ := r
      simp only at hr
      subst hr
      exact k1
    by_cases hb : b = true
    · rw [if_pos hb, if_pos hb]
      refine WP.spec_bind saK fun s1 k1 => ?_
      rw [if_pos hb]
      exact (WP.spec_ok _).2 k1
    rw [if_neg hb]
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    have hiT : i ∈ T := by
      rcases hNb n hn with e | e
      · rw [← ei] at e; exact absurd e hi0
      · rw [← ei] at e; exact e
    have hta := hT i hiT
    step with obj.Tcb.state.spec as ⟨i1, ei1⟩
    refine sig_if _ _ _ _ (fun hrecv => ?_) (fun hnrecv => ?_)
    · have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_RECV := by rw [← ei1, hrecv]
      have hbl : Blocked (L.mem s (stA i)) := by rw [hst]; exact Or.inr (Or.inl rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hiT (not_runnable_of_blocked hbl)
      refine WP.spec_bind (WP.spec_and (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub)
        (ipc.cancel_ipc.kwNR (Kp := (∅ : Set U64)) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z) s a i h0
          hiT hX hSg.sub hst (fun h0' => (hX.2.1.recv i hiT hst h0').1) (Set.notMem_empty _))) ?_
      rintro ⟨s1, a1⟩ ⟨⟨h1, hB1, hX1, nb1, nr1, -, k1, -⟩, F1⟩
      try simp only [WP.uncurry'_pair]
      have hS1 := hS.keepT hX k1
      have hSg1 : SgOK st Ω Sg s1 := ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb,
        fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩
      have K1 : IdlK st Cs s s1 := idlK_footN h0.nodes F1
      have dq1 : (L.mem s1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k1.inqf hiT]; exact dq
      have dr1 : (L.mem s1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k1.inqf hiT]; exact dr
      have da1 : L.actionW s1 ≠ i := by
        rcases k1.act with e | e
        · rw [e]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      refine WP.spec_bind (WP.spec_and (sts_all s1 i _ Q R h1 hB1 hX1 hS1 hSg1 hiT not_blocked_running running_ne
        (Or.inr nb1) (hX1.noref hta nr1 (fun e => nb1 (by rw [e]; exact Or.inr (Or.inl rfl))))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
        (sched.set_thread_state.kwNP (Sg := Sg) (Kp := (∅ : Set U64)) (Nd := True) (Scs := Scs) (Z := Z)
          (Es := ∅) s1 i _ hT h1.nodes h1.cur hiT (Set.notMem_empty _))) ?_
      rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩, F2⟩
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr
      have K2 : IdlK st Cs s1 s2 := idlK_footN h1.nodes F2
      have K02 := K1.trans' K2
      have dq2 : (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hiT]; exact dq1
      have dr2 : (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hiT]; exact dr1
      have da2 : L.actionW s2 ≠ i := by
        rcases k2.act with e | e
        · rw [e]; exact da1
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      refine WP.spec_mono (signal_tail.ff (Kp := (∅ : Set U64)) (Il := (∅ : Set U64)) (Ks := (∅ : Set U64))
        (Es := ∅) (U := ∅) hA s2 a1 i n badge Q R h2' hB2 hX2 hS2 hSg2 hiT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← k1.idleW, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb)
        (Set.notMem_empty _) (Set.notMem_empty _) (fun k hk => absurd hk (Set.notMem_empty k)) (fun k hk => absurd hk (Set.notMem_empty k))
        (fun _ => Set.notMem_empty _)) ?_
      rintro ⟨s', a'⟩ ⟨-, F'⟩
      exact K02.trans' (FFoot.idl h2' hX2.1 F')
    · -- not receiving: the `RunningVM` completion, else active (and kicked)
      rw [if_neg hb]
      refine sig_if _ _ _ _ (fun hvm => ?_) (fun _ => OLD)
      refine WP.spec_bind (WP.spec_and (vcpu.signal_completes.blk s i) (vcpu.signal_completes.aff s i)) ?_
      rintro b1 ⟨hb1, ha1⟩
      refine sig_if _ _ _ _ (fun hb1t => ?_) (fun _ => OLD)
      have hvmS : L.mem s (stA i) = sched.TS_RUNNING_VM := by rw [← ei1]; exact hvm
      refine WP.spec_bind (WP.spec_and (vcpu.report.idlF hA s a i badge hb0 hiT hvmS (hb1 hb1t) hU (hbuf i hiT)) (vcpu.report.stk hA s a i badge hb0 hiT hvmS (hb1 hb1t) hU (hbuf i hiT))) ?_
      rintro s1 ⟨⟨h1, st1, K1⟩, -, hc1⟩
      have h1' := h1
      obtain ⟨⟨Q1, R1, q1⟩, -, hX1, -, -⟩ := h1'
      refine WP.spec_mono (signal_vm.ff (Kp := (∅ : Set U64)) (Il := (∅ : Set U64)) (Ks := (∅ : Set U64))
        (Es := ∅) (U := ∅) hA s1 a i n h1 hiT hn st1 (Set.notMem_empty _) (Set.notMem_empty _)
        (fun k hk => absurd hk (Set.notMem_empty k)) (fun k hk => absurd hk (Set.notMem_empty k)) (fun _ => Set.notMem_empty _)) ?_
      rintro ⟨s', a'⟩ ⟨-, F'⟩
      exact K1.trans' (FFoot.idl q1 hX1.1 F')
  · split
    · -- a waiting notification
      rename_i hwait
      have hst1 : L.epState s n = 1#u64 := by rw [← hv, hwait]; unfold obj.NTFN_WAITING; rfl
      obtain ⟨hdT, hbe, hds⟩ := ntfn_head h0 hH hst1
      step with notification.get_queue.spec as ⟨q, eq⟩
      subst eq
      set hd := (L.epQ s n).head with hhd
      have hta := hT hd hdT
      have hbl : Blocked (L.mem s (stA hd)) := by rw [hds]; exact Or.inr (Or.inr rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hdT (not_runnable_of_blocked hbl)
      obtain ⟨E, EQ, hEW⟩ := h0.eps
      obtain ⟨he', hmem⟩ := hEW.2.2.2.2.1 hd hdT (by simp) hbl
      obtain ⟨hE, hEN, hq⟩ := hEW.1 _ he'
      have hHe : L.mem s (blockA hd) ∈ EH H := (hEW.2.2.2.2.2.2.2.1 _).1 he'
      have hEΩ := hEW.2.2.1 _ he'
      rw [hbe] at hE hEN hq hHe hEΩ hmem
      have hinv := notification.ntfn_dequeue.inv s hd Q R h0 hdT (by simp) hbl
      rw [hbe] at hinv
      refine WP.spec_bind (WP.spec_and hinv (notification.ntfn_dequeue.foot s n hd _ hT hE hq hmem)) ?_
      rintro s1 ⟨⟨h1, f1, o1, n1, k1, -, nc1⟩, w1⟩
      have F1 : FootN st (∅ : Set U64) True T Cs Sg Scs Z (EH H) s s1 :=
        FootN.of' w1 (fun b _ hb => EpFoot.kwN hT h0.nodes hq.mem hHe hE hEN hEΩ (hdrΩ_of hX hSg.sub) hb)
          (AcK.of_eq (EpFoot.act hT h0.nodes h0.cur hq.mem hE hEN w1))
      have K1 : IdlK st Cs s s1 := idlK_footN h0.nodes F1
      have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
        fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
      obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
      have st1 : L.mem s1 (stA hd) = sched.TS_BLOCKED_ON_NTFN := by
        rw [stA_eq, f1 hd hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
      have iq1 : L.mem s1 (inqA hd) = L.mem s (inqA hd) := by
        rw [inqA_eq]; exact f1 hd hdT _ (by simp) (by simp) (by simp) (by simp)
      obtain ⟨-, -, r3, -, r6⟩ := ts_vals
      refine WP.spec_bind (WP.spec_and (sts_all s1 hd _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_running running_ne
        (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
          (by rw [st1, r3, r6]; decide))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
        (sched.set_thread_state.kwNP (Sg := Sg) (Kp := (∅ : Set U64)) (Nd := True) (Scs := Scs) (Z := Z)
          (Es := ∅) s1 hd _ hT h1.nodes h1.cur hdT (Set.notMem_empty _))) ?_
      rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩, F2⟩
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
      have K2 : IdlK st Cs s1 s2 := idlK_footN h1.nodes F2
      have K02 := K1.trans' K2
      have dq2 : (L.mem s2 (inqA hd) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dq
      have dr2 : (L.mem s2 (inqA hd) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dr
      have da2 : L.actionW s2 ≠ hd := by
        rcases k2.act with e | e
        · rw [e, ea1]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hdT)
      refine WP.spec_mono (signal_tail.ff (Kp := (∅ : Set U64)) (Il := (∅ : Set U64)) (Ks := (∅ : Set U64))
        (Es := ∅) (U := ∅) hA s2 a hd n badge Q R h2' hB2 hX2 hS2 hSg2 hdT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← ei1, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb)
        (Set.notMem_empty _) (Set.notMem_empty _) (fun k hk => absurd hk (Set.notMem_empty k)) (fun k hk => absurd hk (Set.notMem_empty k))
        (fun _ => Set.notMem_empty _)) ?_
      rintro ⟨s', a'⟩ ⟨-, F'⟩
      exact K02.trans' (FFoot.idl h2' hX2.1 F')
    · -- an active notification
      step with obj.Ntfn.badge.val as ⟨i, ei⟩
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_bind (obj.Ntfn.set_badge.wr s n _) fun s1 e1 => ?_
      subst e1
      exact (WP.spec_ok _).2 (idlK_footN h0.nodes (ntfn_bd.fn (Kp := (∅ : Set U64)) (Nd := True) (Sg := Sg)
        (Scs := Scs) (Z := Z) (Es := ∅) n _ h0.nodes h0.cur hX.1 hn (h0.omega _ (hSg.sub _ (hX.1.ntB n hn).1))))

theorem timer.fire_loop.idlF {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => IdlK st Cs s s' ⦄ := by
  obtain ⟨IKr, IKs, IKp⟩ := IK T Cs Ω H Sg Rp Scs Nt Z Ac U
  unfold timer.fire_loop
  refine WP.spec_mono (P₀ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
    FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ IdlK st Cs s r.1) ?_
      fun r hr => by obtain ⟨s', a'⟩ := r; exact hr.2.2.2
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ FootDU st T Cs Sg Scs Z (EH H) U s x.1 ∧
      IbFr (L := L) T s x.1 ∧ IdlK st Cs s x.1)
  · rintro ⟨s1, a1, i1⟩ ⟨h1, F1, f1, K1⟩
    simp only at h1 F1 f1 K1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_get.spec as ⟨t, et⟩
      step with obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 ⟨h1, F1, f1, K1⟩
      rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      have hI1 := h1
      obtain ⟨⟨Q1, R1, h1q⟩, -, hX1, -, -⟩ := h1
      have hTm1 := hX1.2.2.tm
      have htT : t ∈ T := by
        have := hTm1.min _ h1q.cur
        rw [← ec] at this; rw [← et] at this
        rcases this with e | e
        · exact absurd e ht0
        · exact e
      step with obj.Tcb.timer_deadline.val as ⟨d, ed⟩
      split
      · exact (WP.spec_ok _).2 ⟨hI1, F1, f1, K1⟩
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (WP.spec_and (timer.remove.tf (s0 := s1) s1 t (TF.start hI1) htT) (IKr s1 t hI1 htT)) ?_
      rintro s2 ⟨⟨h2, f2, -, -, w2⟩, g2⟩
      have F2 : FootDU st T Cs Sg Scs Z (EH H) U s s2 := F1.trans (FootD.u (Foot.d (f2.mono (Set.empty_subset _))))
      have f12 := f1.trans g2
      have N2 : FootN st (∅ : Set U64) True T Cs Sg Scs Z ∅ s1 s2 :=
        TW.fn h1q.tcbs h1q.nodes h1q.cur w2
      have K2 : IdlK st Cs s s2 := K1.trans' (idlK_footN h1q.nodes N2)
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
          FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ IdlK st Cs s r.1) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hb2 := hBA.of_fr f12
          exact WP.spec_mono (WP.spec_and (WP.spec_and
            (notification.send_signal.tinvF hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2)
            (IKs s2 a1 n bd h2 hn (hNt n hn) hb2))
            (notification.send_signal.idlF hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2)) fun r hr => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr
            exact ⟨hr.1.1.1, F2.trans hr.1.1.2.1, f12.trans hr.1.2, K2.trans' hr.2⟩
        · exact (WP.spec_ok _).2 ⟨h2, F2, f12, K2⟩
      rintro ⟨s3, a3⟩ ⟨h3, F3, f3, K3⟩
      simp only at h3 F3 f3 K3
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3', ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have hc3 := h3.1.choose_spec.choose_spec.cur
      have h3' := h3
      obtain ⟨⟨Q3, R3, q3⟩, -, hX3, -, -⟩ := h3'
      have N4 : FootN st (∅ : Set U64) True T Cs Sg Scs Z ∅ s3
          (L.wr s3 (L.nodeAt s3 (L.cpu s3) layout.node.REPROGRAM) 1#u64) :=
        footN_node q3.nodes q3.cur (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)
          (idOff_ge (by rw [rp]; omega)) q3.cur (by rw [rp]; omega)
      exact ⟨reprogram.tinv h3, F3.trans (FootD.u (Foot.d (foot_node (h3.1.choose_spec.choose_spec.nodes _ hc3) hc3
        (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)))), f3.trans (IKp s3 1#u64 h3),
        K3.trans' (idlK_footN q3.nodes N4), by omega⟩
    · exact (WP.spec_ok _).2 ⟨h1, F1, f1, K1⟩
  · exact ⟨h, FootD.u (Foot.d (Foot.refl _)), IbFr.refl s, IdlK.refl s⟩

/-- **`timer::fire` keeps every node identity word.** -/
theorem timer.fire.idlF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    timer.fire st ar s a ⦃ s' _ => IdlK st Cs s s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.idlF hA IK hNt s a now 0#u64 h hBA

/-! ## `activate_thread`'s sharper words -/

/-- `set_consumed`'s words: an SC word of `Scs`, or a register word of `y`. -/
def TWSr (Scs : Set U64) (Z : U64 → Nat) (y : U64) (b : U64) : Prop :=
  (∃ c ∈ Scs, InSC c (Z c) b) ∨
  (∃ K : U64, 256 ≤ K.val ∧ K.val < 3328 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add y K)

/-- **`activate_thread`'s words** (module docstring). -/
def TWS (st : machine.Store S) [L : LawfulStore st] (Scs : Set U64) (Z : U64 → Nat) (y : U64) (s0 : S)
    (b : U64) : Prop :=
  TWSr Scs Z y b ∨ b = yieldA y ∨ b = stA y ∨ b = L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION

theorem TWS.ksb {y : U64} {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : TWS st Scs Z y s1 b) : TWS st Scs Z y s0 b := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, hc, nodeAt_of_ksb hk])))

theorem TWS.trans {y : U64} {s0 s1 s2 : S} (h1 : WritesIn st s0 s1 (TWS st Scs Z y s0))
    (h2 : WritesIn st s1 s2 (TWS st Scs Z y s1)) : WritesIn st s0 s2 (TWS st Scs Z y s0) :=
  (h1.trans h2).mono fun _ hb => hb.elim id (TWS.ksb h1.1 h1.2.1)

theorem TWSr.tws {y : U64} {s0 s1 : S} (h : WritesIn st s0 s1 (TWSr Scs Z y)) :
    WritesIn st s0 s1 (TWS st Scs Z y s0) := h.mono fun _ hb => Or.inl hb

theorem tws_sc {s : S} {i o y : U64} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hi : i ∈ Scs) (ho : o.val < 128)
    (h8 : o.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add i o) ∧ TWSr Scs Z y (core.num.U64.wrapping_add i o) := by
  obtain ⟨hP, hz⟩ := hO.sc i hi
  obtain ⟨c8, c128, cfit⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz ho
  have ha : Aligned (core.num.U64.wrapping_add i o) := by unfold Aligned; rw [hv]; omega
  exact ⟨ha, Or.inl ⟨i, hi, by rw [hv]; omega, by rw [hv]; omega⟩⟩

theorem tws_reg {s : S} {y r v : U64} (hy : TcbAddr y) (hr : r.val < 384) :
    obj.Tcb.set_reg st y s r v ⦃ s' => WritesIn st s s' (TWSr Scs Z y) ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.wrK s y r v hy hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    exact (writesIn_wr (field_aligned hy (by omega) (by omega))).mono fun b e =>
      Or.inr ⟨K, by omega, by omega, by omega, e⟩

variable {A : Type _} {ar : machine.Arch A}

theorem schedcontext.update_consumed.tws (hA : P0.ArchTotal ar) {s : S} {a : A} {c y : U64}
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) :
    schedcontext.update_consumed st ar s a c ⦃ r => WritesIn st s r.2 (TWSr Scs Z y) ⦄ := by
  obtain ⟨ha, hw⟩ := tws_sc (y := y) (o := layout.sc.CONSUMED) hO hc (by simp [layout.sc.CONSUMED])
    (by simp [layout.sc.CONSUMED])
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec as ⟨x, _hx⟩
  split
  · step as ⟨z, _hz⟩
    refine WP.spec_bind (obj.Sc.set_consumed.spec' s c z) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact hw)
  · refine WP.spec_bind (obj.Sc.set_consumed.spec' s c 0#u64) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact hw)

theorem schedcontext.set_consumed.tws (hA : P0.ArchTotal ar) (s : S) (a : A) (c y : U64) (wm : Bool)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hya : TcbAddr y) (hc : c ∈ Scs) :
    schedcontext.set_consumed st ar s a c y wm ⦃ s' => WritesIn st s s' (TWSr Scs Z y) ⦄ := by
  unfold schedcontext.set_consumed
  refine WP.spec_bind (schedcontext.update_consumed.tws (y := y) hA hO hc) ?_
  rintro ⟨x, s1⟩ w1
  simp only at w1
  try simp only [WP.uncurry'_pair]
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s1 true y L.total) fun buf _ => ?_
    refine WP.spec_bind (tws_reg (Scs := Scs) (Z := Z) (s := s1) (r := layout.reg.BADGE) (v := 0#u64) hya
      (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s2 w2 => ?_
    unfold msg.set_mr
    simp only [show (0#u64 < msg.N_MSG_REGISTERS) = True from by simp [msg.N_MSG_REGISTERS], if_true]
    simp only [msg.msg_register, if_true, Aeneas.Std.bind_ok]
    refine WP.spec_bind (Pₘ := fun r : U64 × S => WritesIn st s2 r.2 (TWSr Scs Z y)) ?_ ?_
    · refine WP.spec_bind (tws_reg (Scs := Scs) (Z := Z) (s := s2) (r := layout.reg.R10) hya
        (by simp [layout.reg.R10])) fun s3 hh => ?_
      simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok]; exact hh
    rintro ⟨len, s3⟩ w3
    simp only at w3
    try simp only [WP.uncurry'_pair]
    unfold msginfo.MessageInfo.new msg.set_msg_info
    simp only [Aeneas.Std.bind_ok]
    refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun wd _ => ?_
    exact WP.spec_mono (tws_reg (Scs := Scs) (Z := Z) (s := s3) (r := layout.reg.MSG_INFO) hya
      (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => w1.trans1 (w2.trans1 (w3.trans1 w4))
  · exact (WP.spec_ok _).2 w1

theorem schedcontext.cancel_yield_to.tws (s : S) (y : U64)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hya : TcbAddr y)
    (hyt : L.mem s (yieldA y) ≠ 0#u64 → L.mem s (yieldA y) ∈ Scs) :
    schedcontext.cancel_yield_to st s y ⦃ s' => WritesIn st s s' (TWS st Scs Z y s) ⦄ := by
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, _⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact hyt (by rw [← ei]; simpa using hi)
    obtain ⟨ha1, hw1⟩ := tws_sc (y := y) (o := layout.sc.YIELD_FROM) hO hiS (by simp [layout.sc.YIELD_FROM])
      (by simp [layout.sc.YIELD_FROM])
    step with obj.Sc.set_yield_from.spec as ⟨s1, e1⟩
    subst e1
    step with obj.Tcb.set_yield_to.spec as ⟨s2, e2⟩
    subst e2
    have w1 : WritesIn st s (L.wr s (scYieldFromA i) 0#u64) (TWS st Scs Z y s) :=
      (writesIn_wr ha1).mono fun b e => Or.inl (by rw [e]; exact hw1)
    have w2 : WritesIn st (L.wr s (scYieldFromA i) 0#u64)
        (L.wr (L.wr s (scYieldFromA i) 0#u64) (yieldA y) 0#u64) (TWS st Scs Z y s) :=
      (writesIn_wr (field_aligned (K := 3472#u64) hya (by simp) (by simp))).mono fun b e => Or.inr (Or.inl e)
    exact (w1.trans w2).mono fun _ hb => hb.elim id id
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

theorem schedcontext.complete_yield_to.tws (hA : P0.ArchTotal ar) (s : S) (a : A) (y : U64)
    (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hy : y ∈ T)
    (hT : TcbPlaced T) (hyt : L.mem s (yieldA y) ≠ 0#u64 → L.mem s (yieldA y) ∈ Scs) :
    schedcontext.complete_yield_to st ar s a y ⦃ r => WritesIn st s r.1 (TWS st Scs Z y s) ⦄ := by
  have hya := hT y hy
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact hyt (by rw [← ei]; simpa using hi)
    refine WP.spec_bind (schedcontext.set_consumed.tws hA s a i y true hO hya hiS) fun s1 w1 => ?_
    have ya : Aligned (yieldA y) := field_aligned (K := 3472#u64) hya (by simp) (by simp)
    have ey : L.mem s1 (yieldA y) = L.mem s (yieldA y) := by
      refine w1.mem_eq ya ?_
      rintro (⟨c, hc, hin⟩ | ⟨K, h1, h2, -, e⟩)
      · exact out_ne_field (K := 3472#u64) (hΩ _ (hO.scW c hc _ ya hin)) hy hya (by simp) rfl
      · have k3 : (3472#u64 : U64).val = 3472 := by simp
        exact field_ne (K1 := 3472#u64) hya hya (by simp) (by omega) (fun _ => by omega) e
    refine WP.spec_bind (schedcontext.cancel_yield_to.tws s1 y (ObjsOK.anyT hO) hya (by rw [ey]; exact hyt))
      fun s2 w2 => ?_
    exact (WP.spec_ok _).2 (TWS.trans (TWSr.tws w1) w2)
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`activate_thread` is a `TWS` step** of the current thread (module docstring). -/
theorem sched.activate_thread.tws (hA : P0.ArchTotal ar) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.activate_thread st ar s a ⦃ r => WritesIn st s r.1 (TWS st Scs Z (L.curW s) s) ⦄ := by
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -⟩ := h
  have hT := hq.tcbs
  have hcT : L.curW s ∈ T := hq.curT
  have hN := hq.nodes _ hq.cur
  unfold sched.activate_thread
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have ect' : ct = L.curW s := ect
  subst ect'
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => WritesIn st s r.1 (TWS st Scs Z (L.curW s) s)) ?_ ?_
  · split
    · exact schedcontext.complete_yield_to.tws hA s a _ hq.omega hX.1 hcT hT (hX.2.2.yt.2.1 _ hcT)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rintro ⟨s1, a1⟩ w1
  try simp only [WP.uncurry'_pair]
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · step with obj.Tcb.reg.spec as ⟨pc⟩
    refine WP.spec_bind (tws_reg (Scs := Scs) (Z := Z) (s := s1) (r := layout.reg.NEXT_IP) (v := pc)
      (hT _ hcT) (by simp [layout.reg.NEXT_IP])) fun s2 w2 => ?_
    have w12 : WritesIn st s s2 (TWS st Scs Z (L.curW s) s) := TWS.trans w1 (TWSr.tws w2)
    have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [w12.2.1]; exact hN.ksb w12.1
    refine WP.spec_bind (sched.set_thread_state.w2 s2 (L.curW s) sched.TS_RUNNING hT hN2 hcT)
      fun s3 hw3 => ?_
    exact (WP.spec_ok _).2 (TWS.trans w12 (hw3.1.mono fun b hb =>
      hb.elim (fun e => Or.inr (Or.inr (Or.inl e))) (fun e => Or.inr (Or.inr (Or.inr e)))))
  · exact (WP.spec_ok _).2 w1

end

end Fl4Proofs.P2.Stall

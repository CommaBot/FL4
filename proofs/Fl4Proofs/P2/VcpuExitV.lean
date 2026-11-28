/-
# P2 (vexit gen 3): the VCPU words through the serial VM exit (`hPF` discharged)

`syscall.handle_vcpu_exit.entryB` (P1/VcpuExitBuf) takes `hPF` [P]: after
`finish_old`, a `TS_RUNNING_VM` current thread's bound VCPU `PENDING` word is a
user word (`PendAt`). Here every TCB's VCPU word (offset 3664; written only by
`vcpu::detach` and `X86VCPUSetTCB`) is kept through the whole run
(`VcpuWK`), so `PendAt` after `finish_old` follows from `VcpuZ` at the entry
(every TCB's VCPU word zero, vent; P3 `JExt.vw`): vacuously.

The frame is vk's `PrW` exclusion (P2/FootN: under `Nd`, every `FootN … True`,
`SFootN` and `FFoot` footprint keeps the VCPU words), used here with **no
protected threads** (`Kp = Il = Ks = ∅`), so no multi-core context (`FCtx`,
`AllCores`) is needed:

* helpers: `vcpuWK_footN`, `vcpuWK_sfootN`, `vcpuWK_footB0` (node-word
  footprints, `update_timestamp`), `vcpuWK_node`, `vcpuWK_vck` (`vcpu::check`'s
  `VckW`: registers 256..3328, the state word, the action word);
* `vcpu.report.vc`, `notification.send_signal.vc`, `timer.fire_loop.vc`,
  `timer.fire.vc`: vk's `FKI` walk of `fire` (`send_signal.fk`,
  `fire_loop.fki`) redone with `Kp = Il = Ks = ∅` and the frame `VcpuWK`;
* `sched.schedule.vc` (`schedule.sN` over `Kp = ∅` + `fire.vc`),
  `syscall.finish_old.vc` (+ `activate_thread`'s `TW`, `vcpuWK_of_tw`; the
  current thread stays a TCB);
* `sched.check_budget.vc` (`check_budget.allGN` over `Kp = ∅`, `Nd`), with the
  timeout fault's frame in the pinned premise **`TmoIbV`** [P] (`TmoIb` plus
  the VCPU words: a timeout fault IPC writes no VCPU word);
* `interrupt.handle_interrupt.vcx` (signal: `send_signal.vc`; timer: node
  words; IPI: `reschedule_required.kwN`);
* `vexit_checkV`, `vexit_pre.ibv`, `vexit_irq.ibv`, `vexit_pf` (the `hPF`
  triple from `VcpuZ`), `tmoIb_tk`.

**`syscall.handle_vcpu_exit.entryV`** (and `vcpu_exit_local.entryV`,
`vm_timer_local.entryV`): `entryB` with `hPd` and `hPF` replaced by
`hz : VcpuZ T s` at the entry. Named premises: `hBA` [P] (`BufAt` at the
entry), `htk` [P] (with `TmoIbV` in place of `TmoIb`), `hI` [P] (IRQ slots).
-/
import Fl4Proofs.P2.EntryVent
import Fl4Proofs.P1.VcpuExitBuf
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64}

/-! ## Frames keeping every TCB's VCPU word -/

theorem vcpuWK_footN {Kp : Set U64} {s s' : S} (hT : TcbPlaced T)
    (f : FootN st Kp True T Cs Sg Scs Z Es s s') : VcpuWK st T s s' := fun y hy =>
  f.idKeep (field_aligned (hT y hy) (by simp) (by simp))
    (Or.inr (Or.inr ⟨trivial, Or.inr (Or.inr ⟨y, hy, hT y hy, rfl⟩)⟩))

theorem vcpuWK_sfootN {Kp : Set U64} {s s' : S} (hT : TcbPlaced T)
    (F : SFootN st Kp T Cs Sg Scs Z H s s') : VcpuWK st T s s' := fun y hy =>
  F.mem_eq (field_aligned (hT y hy) (by simp) (by simp))
    (fun hb => hb.2.2 (Or.inr ⟨trivial, Or.inr (Or.inr ⟨y, hy, hT y hy, rfl⟩)⟩))

/-! ## `fire` keeps the VCPU words (vk's `FKI` walk, no protected threads) -/

/-- `vcpu.report` of a `TS_RUNNING_VM` thread keeps every VCPU word (`RepW` is
an `FFoot`; `set_thread_state` a `FootN ∅ True` step). -/
theorem vcpu.report.vc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t badge : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hvm : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (hc : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) = 0#u64)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true t ⦃ b => BufOK U b ⦄) :
    vcpu.report st ar s a t badge ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      L.mem s' (stA t) = sched.TS_RUNNING ∧ VcpuWK st T s s' ⦄ := by
  have h0 := h
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -⟩ := h0
  refine WP.spec_mono (WP.spec_and (vcpu.report.xf hA s a t badge h ht hvm hc hU hbuf)
    (vcpu.report.blk hA s a t badge h ht hvm hc hU hbuf)) ?_
  rintro s' ⟨⟨s1, h1, st1, w1, e⟩, hb', st'⟩
  have V1 : VcpuWK st T s s1 :=
    FFoot.vc hq hX.1 (RepW.ff (Kp := (∅ : Set U64)) (Il := (∅ : Set U64)) (Ks := (∅ : Set U64)) (Es := ∅)
      (U := U) hq hX.1 ht hU w1)
  obtain ⟨⟨Q1, R1, hq1⟩, -, -, -, -⟩ := h1
  have F2 := sched.set_thread_state.kwNP (Kp := (∅ : Set U64)) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z)
    (Es := ∅) s1 t sched.TS_RUNNING hq.tcbs hq1.nodes hq1.cur ht (Set.notMem_empty t)
  rw [e, WP.spec_ok] at F2
  exact ⟨hb', st', V1.trans' (vcpuWK_footN hq.tcbs F2)⟩

/-- **`send_signal` keeps every VCPU word** (vk's `send_signal.fk` with no
protected threads). -/
theorem notification.send_signal.vc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt)
    (hH : H n = some .ntfn) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    :
    notification.send_signal st ar s a n badge ⦃ s' _ => VcpuWK st T s s' ⦄ := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hNb := hX.2.2.ntb
  have hT := h0.tcbs
  have hb0 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩
  have saK : notification.set_active st s n badge ⦃ s' => VcpuWK st T s s' ⦄ :=
    WP.spec_mono (notification.set_active.fn (Kp := (∅ : Set U64)) (Nd := True) s n badge h0 hX hSg hn hH)
      fun s' f => vcpuWK_footN hT f
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
        ⦃ s' _ => VcpuWK st T s s' ⦄ := by
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
      have K1 : VcpuWK st T s s1 := vcpuWK_footN hT F1
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
      have K2 : VcpuWK st T s1 s2 := vcpuWK_footN hT F2
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
      exact K02.trans' (FFoot.vc h2' hX2.1 F')
    · -- not receiving: the `RunningVM` completion, else active (and kicked)
      rw [if_neg hb]
      refine sig_if _ _ _ _ (fun hvm => ?_) (fun _ => OLD)
      refine WP.spec_bind (WP.spec_and (vcpu.signal_completes.blk s i) (vcpu.signal_completes.aff s i)) ?_
      rintro b1 ⟨hb1, ha1⟩
      refine sig_if _ _ _ _ (fun hb1t => ?_) (fun _ => OLD)
      have hvmS : L.mem s (stA i) = sched.TS_RUNNING_VM := by rw [← ei1]; exact hvm
      refine WP.spec_bind (WP.spec_and (vcpu.report.vc hA s a i badge hb0 hiT hvmS (hb1 hb1t) hU (hbuf i hiT)) (vcpu.report.stk hA s a i badge hb0 hiT hvmS (hb1 hb1t) hU (hbuf i hiT))) ?_
      rintro s1 ⟨⟨h1, st1, K1⟩, -, hc1⟩
      have h1' := h1
      obtain ⟨⟨Q1, R1, q1⟩, -, hX1, -, -⟩ := h1'
      refine WP.spec_mono (signal_vm.ff (Kp := (∅ : Set U64)) (Il := (∅ : Set U64)) (Ks := (∅ : Set U64))
        (Es := ∅) (U := ∅) hA s1 a i n h1 hiT hn st1 (Set.notMem_empty _) (Set.notMem_empty _)
        (fun k hk => absurd hk (Set.notMem_empty k)) (fun k hk => absurd hk (Set.notMem_empty k)) (fun _ => Set.notMem_empty _)) ?_
      rintro ⟨s', a'⟩ ⟨-, F'⟩
      exact K1.trans' (FFoot.vc q1 hX1.1 F')
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
      have K1 : VcpuWK st T s s1 := vcpuWK_footN hT F1
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
      have K2 : VcpuWK st T s1 s2 := vcpuWK_footN hT F2
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
      exact K02.trans' (FFoot.vc h2' hX2.1 F')
    · -- an active notification
      step with obj.Ntfn.badge.val as ⟨i, ei⟩
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_bind (obj.Ntfn.set_badge.wr s n _) fun s1 e1 => ?_
      subst e1
      exact (WP.spec_ok _).2 (vcpuWK_footN hT (ntfn_bd.fn (Kp := (∅ : Set U64)) (Nd := True) (Sg := Sg)
        (Scs := Scs) (Z := Z) (Es := ∅) n _ h0.nodes h0.cur hX.1 hn (h0.omega _ (hSg.sub _ (hX.1.ntB n hn).1))))

theorem timer.fire_loop.vc {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => VcpuWK st T s s' ⦄ := by
  obtain ⟨IKr, IKs, IKp⟩ := IK T Cs Ω H Sg Rp Scs Nt Z Ac U
  unfold timer.fire_loop
  refine WP.spec_mono (P₀ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
    FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ VcpuWK st T s r.1) ?_
      fun r hr => by obtain ⟨s', a'⟩ := r; exact hr.2.2.2
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ FootDU st T Cs Sg Scs Z (EH H) U s x.1 ∧
      IbFr (L := L) T s x.1 ∧ VcpuWK st T s x.1)
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
      have K2 : VcpuWK st T s s2 := K1.trans' (vcpuWK_footN h1q.tcbs N2)
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
          FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ VcpuWK st T s r.1) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hb2 := hBA.of_fr f12
          exact WP.spec_mono (WP.spec_and (WP.spec_and
            (notification.send_signal.tinvF hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2)
            (IKs s2 a1 n bd h2 hn (hNt n hn) hb2))
            (notification.send_signal.vc hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2)) fun r hr => by
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
        K3.trans' (vcpuWK_footN q3.tcbs N4), by omega⟩
    · exact (WP.spec_ok _).2 ⟨h1, F1, f1, K1⟩
  · exact ⟨h, FootD.u (Foot.d (Foot.refl _)), IbFr.refl s, fun _ _ => rfl⟩

/-- **`timer::fire` keeps every VCPU word.** -/
theorem timer.fire.vc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    timer.fire st ar s a ⦃ s' _ => VcpuWK st T s s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.vc hA IK hNt s a now 0#u64 h hBA

/-- **`schedule` keeps every VCPU word** (from `BlkOK` alone): `fire` by
`timer.fire.vc`, the rest an `SFootN` over no protected thread. -/
theorem sched.schedule.vc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    sched.schedule st ar s a ⦃ s' _ => VcpuWK st T s s' ⦄ := by
  have hT : TcbPlaced T := h.1.choose_spec.choose_spec.tcbs
  refine WP.spec_mono (sched.schedule.sN (Kp := (∅ : Set U64)) hA IK hNt s a h hBA fun _ _ =>
    ⟨fun y hy => absurd hy (Set.notMem_empty y), fun _ => Set.notMem_empty _,
      fun hk => absurd hk (Set.notMem_empty _)⟩) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨rf, hrf, -, F⟩ := hh
  have k0 := timer.fire.vc hA IK hNt s a h hBA
  rw [hrf] at k0
  have V1 : VcpuWK st T s rf.1 := (WP.spec_ok rf).1 k0
  exact V1.trans' (vcpuWK_sfootN hT F)

/-- **`finish_old` keeps every VCPU word**, and the current thread stays a TCB. -/
theorem syscall.finish_old.vc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    syscall.finish_old st ar s a ⦃ s' _ => VcpuWK st T s s' ∧ L.curW s' ∈ T ⦄ := by
  unfold syscall.finish_old
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  refine WP.spec_bind (WP.spec_and
    (Fl4Proofs.P1.sched.schedule.entry hA (ibKeep_holds hA) hNt s a Q R h0 hB hS hX hSg hBA)
    (sched.schedule.vc hA (ibKeep_holds hA) hNt s a ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ hBA)) ?_
  rintro ⟨s1, a1⟩ ⟨E1, V1⟩
  have hq1 := E1.1.choose_spec.choose_spec
  exact WP.spec_mono (Fl4Proofs.P2.Stall.sched.activate_thread.tw hA s1 a1 (EntryInv.bxi E1).blk)
    fun r hr => by
      obtain ⟨s', a'⟩ := r
      have fr := TW.frames hq1 hq1.curT hr.1
      show VcpuWK st T s s' ∧ L.curW s' ∈ T
      exact ⟨V1.trans' (vcpuWK_of_tw hq1.tcbs hq1.curT (hq1.nodes _ hq1.cur) hr.1),
        by rw [fr.2.1]; exact hq1.curT⟩

/-! ## The budget check and the interrupt -/

/-! ## The serial VM exit -/

end

end Fl4Proofs.P2.Stall

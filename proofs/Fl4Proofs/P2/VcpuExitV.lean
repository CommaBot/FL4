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

/-- A node-words-only step (`FootB` over empty object sets) keeps every VCPU word. -/
theorem vcpuWK_footB0 {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInv st T Cs Ω H s Q R) (f : FootB st ∅ Cs ∅ ∅ Z ∅ s s') : VcpuWK st T s s' :=
  fun y hy => footB0_fld hq hy (K := 3664#u64) (by simp) (by simp) f

/-- A write of a current-node word keeps every VCPU word. -/
theorem vcpuWK_node {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInv st T Cs Ω H s Q R) {o v : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (h88 : o.val ≠ 88) : VcpuWK st T s (L.wr s (L.nodeAt s (L.cpu s) o) v) :=
  vcpuWK_footB0 hq (footB_node (T := ∅) (Sg := ∅) (Scs := ∅) (Z := fun _ => 0) (Es := ∅)
    (nodePlaced0 (hq.nodes _ hq.cur)) hq.cur ho h8 h88)

/-- `vcpu::check`'s words (`VckW`) are no VCPU word. -/
theorem vcpuWK_vck {y : U64} {s s' : S} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hy : y ∈ T) (w : WritesIn st s s' (VckW st T Cs Scs y s)) :
    VcpuWK st T s s' := by
  obtain ⟨-, -, -, -, fld, -⟩ := VckW.frames hq hy w
  exact fun t ht => fld t ht _ (by simp) (by simp) (fun _ => Or.inr (by simp))

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

/-- **[P] The timeout fault of a budget check from `s0` keeps the
buffer-lookup words and every TCB's VCPU word** (and the invariants), at the
states `TmoGB` names (`TmoIb` with the VCPU words). -/
def TmoIbV (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (s0 : S) : Prop :=
  ∀ (s : S) (a : A) (f : error.Fault) (Q : U64 → U64 → List U64) (R : U64 → List U64),
    SchedQueuesInv st T Cs Ω H s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s → SgOK st Ω Sg s →
    SCsOK st T Ω Sg Scs Z Ac s → WritesIn st s0 s (ChgW st Scs Z s0) → CurOK st T s →
    faults.handle_timeout st ar s a (L.curW s) f ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      IbFr (L := L) T s s' ∧ VcpuWK st T s s' ⦄

theorem TmoIbV.ib {A : Type _} {ar : machine.Arch A} {s0 : S} (hT : TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    TmoIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0 :=
  fun s a f Q R h hB hX hSg hS w hc => WP.spec_mono (hT s a f Q R h hB hX hSg hS w hc) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨hr.1, hr.2.1⟩

theorem TmoIbV.kc {A : Type _} {ar : machine.Arch A} {s0 : S} (hT : TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0)
    (sA : S) : TmoKC st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0 (fun s' => VcpuWK st T sA s') :=
  fun s a f Q R h hB hX hSg hS w hc hG => WP.spec_mono (hT s a f Q R h hB hX hSg hS w hc) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨hr.1, hG.trans' hr.2.2⟩

/-- **`check_budget` from an `EntryInv` state keeps every VCPU word**, when
its timeout fault does (`TmoIbV` at its start): `check_budget.allGN` over no
protected thread, in no-donation mode. -/
theorem sched.check_budget.vc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (htmo : TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.check_budget st ar s a ⦃ r s' _ => VcpuWK st T s s' ⦄ := by
  have hT : TcbPlaced T := h.1.choose_spec.choose_spec.tcbs
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, -, hcA, hna, hcsc⟩ := h
  refine WP.spec_mono (Fl4Proofs.P1.sched.check_budget.allGN (Kp := (∅ : Set U64)) (Nd := True) hA s a Q R h0
    hB hX hS.sg hS hcsc hna hcA (G := fun s' => VcpuWK st T s s')
    (fun _ _ g f => g.trans' (vcpuWK_footN hT f))
    (fun _ _ => ⟨fun _ => Set.notMem_empty _, Set.notMem_empty _⟩) (fun _ _ => rfl) (htmo.kc s)) ?_
  rintro ⟨r, s', a'⟩ ⟨⟨-, g1⟩, -⟩
  exact g1

/-- **`handle_interrupt` keeps every VCPU word** (as
`interrupt.handle_interrupt.ibx`). -/
theorem interrupt.handle_interrupt.vcx {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (irq : U64)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hirq : IrqNtAt st Nt s) (hBA : BufAt st T Cs H Sg Scs Z U s) :
    interrupt.handle_interrupt st ar s a irq ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      VcpuWK st T s s' ⦄ := by
  have hST : P0.StoreTotal st := L.total
  have hq := h.1.choose_spec.choose_spec
  unfold interrupt.handle_interrupt
  step with layout.irq.MAX.spec as ⟨mx, emx⟩
  split
  · refine WP.spec_bind (hA.mask_irq a irq true) fun a1 _ => ?_
    refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
    exact (WP.spec_ok _).2 ⟨h, fun _ _ => rfl⟩
  step with P0.interrupt.irq_state.p0 st s irq hST as ⟨v⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ VcpuWK st T s r.1) ?_ ?_
  · split
    · rename_i hle _
      step with interrupt.irq_slot.val as ⟨sl, esl⟩
      subst esl
      have hirq' : irq.val < 128 := by
        have : mx.val = 127 := by rw [emx]; simp [layout.irq.MAX]
        simp at hle; omega
      refine WP.spec_bind (hirq irq hirq') fun c hc => ?_
      refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
        VcpuWK st T s r.1) ?_ ?_
      · split
        all_goals try exact (WP.spec_ok _).2 ⟨h, fun _ _ => rfl⟩
        rename_i ptr badge b x
        split
        · have hn := hc ptr badge b x rfl
          exact WP.spec_mono (WP.spec_and
            (notification.send_signal.tinv hA s a ptr badge h.blk hn (hNt ptr hn) hBA.1 hBA.2)
            (notification.send_signal.vc hA s a ptr badge h.blk hn (hNt ptr hn) hBA.1 hBA.2))
            fun r hr => by
              obtain ⟨s', a'⟩ := r
              simp only [WP.uncurry'_pair] at hr ⊢
              exact ⟨BlkOK.bxi hr.1, hr.2⟩
        · exact (WP.spec_ok _).2 ⟨h, fun _ _ => rfl⟩
      · rintro ⟨s3, a2⟩ h3
        try simp only [WP.uncurry'_pair]
        refine WP.spec_bind (hA.mask_irq a2 irq true) fun a3 _ => ?_
        exact (WP.spec_ok _).2 h3
    split
    · step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_set.spec as ⟨s2, e2⟩
      subst ec e2
      obtain ⟨⟨k2, -, -⟩, -, -⟩ := nodew_bxc (o := layout.node.REPROGRAM) (v := 1#u64) h
        (by simp [layout.node.REPROGRAM, LowFree]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      have i2 := vcpuWK_node (T := T) hq (o := layout.node.REPROGRAM) (v := 1#u64)
        (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      have i3 := vcpuWK_node (T := T) k2.1.choose_spec.choose_spec (o := layout.node.ARMED) (v := 0#u64)
        (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])
      step with obj.node_set.spec as ⟨s3, e3⟩
      subst e3
      have k3 := nodew_bxc (o := layout.node.ARMED) (v := 0#u64) k2
        (by simp [layout.node.ARMED, LowFree]) (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])
      have k3' := k3.1.1
      have i23 := i2.trans' i3
      simp only [LawfulStore.cpu_wr, nodeAt_wr] at k3' i23 ⊢
      exact ⟨k3', i23⟩
    split
    · unfold smp.handle_ipi
      step with layout.irq.RESCHEDULE_IPI.spec as ⟨ri, eri⟩
      split
      · obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
        refine WP.spec_bind (WP.spec_and (Fl4Proofs.P1.sched.reschedule_required.sch s Q R h0 hB hSg)
          (Fl4Proofs.P1.sched.reschedule_required.kwN (Kp := (∅ : Set U64)) (Nd := True) (Sg := Sg) (Scs := Scs)
            (Z := Z) (Es := EH H) s h0 (fun _ => Set.notMem_empty _))) fun s1 hh => ?_
        obtain ⟨⟨⟨hi, hB1, f1⟩, -, -, -⟩, k1⟩ := hh
        exact (WP.spec_ok _).2 ⟨⟨hi, hB1, hX.fr f1, hSg.fr f1, hS.fr f1⟩, vcpuWK_footN h0.tcbs k1⟩
      · exact (WP.spec_ok _).2 ⟨h, fun _ _ => rfl⟩
    · refine WP.spec_bind (Pₘ := fun _ : A => True) ?_ fun t _ => (WP.spec_ok _).2 ⟨h, fun _ _ => rfl⟩
      split
      · exact WP.spec_mono (hA.mask_irq a irq true) fun _ _ => trivial
      · exact (WP.spec_ok _).2 trivial
  · rintro ⟨s1, a1⟩ h1
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (hA.ack_irq a1 irq) fun a2 _ => ?_
    exact (WP.spec_ok _).2 h1

/-! ## The serial VM exit -/

/-- **`PendAt` holds vacuously when every TCB's VCPU word is zero** and the
current thread is a TCB. -/
theorem pendAt_of_vcpuZ {s : S} (hz : VcpuZ st T s) (hc : L.curW s ∈ T) : PendAt st U s :=
  fun _ hw => absurd (hz _ hc) hw

/-- `vcpu.check` of the current thread keeps `EntryInv`, the buffer lookups
and every VCPU word. -/
theorem vexit_checkV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hV : VmPl st T Cs H Sg Scs Z U s) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      IbFr (L := L) T s s' ∧ VcpuWK st T s s' ⦄ := by
  have hq := h.1.choose_spec.choose_spec
  have hcT : L.curW s ∈ T := hq.curT
  by_cases hv : L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM
  · obtain ⟨hBA, hpw⟩ := hV hv
    refine WP.spec_mono (Fl4Proofs.P1.vcpu.check.vck hA hNt s a h hBA.1 (hBA.2 _ hcT) hpw) ?_
    rintro ⟨s', a'⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    exact ⟨hh.1, VckW.ibFr hq hcT hh.2.1, vcpuWK_vck hq hcT hh.2.1⟩
  · rw [check_of_ne ar s a _ hv, WP.spec_ok]
    exact ⟨h, IbFr.refl s, fun _ _ => rfl⟩

/-- **The prefix of `handle_vcpu_exit` keeps the invariants, the buffer
lookups and every VCPU word** (`vexit_pre.ib` with `TmoIbV`). -/
theorem vexit_pre.ibv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hPd : PendAt st U s)
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄) :
    vexit_pre st ar s a stalled ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ∧
      VcpuWK st T s s' ⦄ := by
  unfold vexit_pre
  cases stalled with
  | true => exact (WP.spec_ok _).2 ⟨EntryInv.bxi h, IbFr.refl s, fun _ _ => rfl⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hq := h.1.choose_spec.choose_spec
    refine WP.spec_bind (WP.spec_and (WP.spec_and (Fl4Proofs.P1.sched.update_timestamp.bxc hA s a (EntryInv.bxi h))
      (Fl4Proofs.P2.Stall.sched.update_timestamp.kwB (T := ∅) (Sg := ∅) (Scs := ∅) (Es := ∅)
        (Z := fun _ => 0) hA s a (nodePlaced0 (hq.nodes _ hq.cur)) hq.cur)) (htk rfl)) ?_
    rintro ⟨s1, a1⟩ ⟨⟨⟨⟨hb1, c1, k1⟩, n1, f1⟩, F1⟩, T1⟩
    have E1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := EntryInv.of_step h hb1.blk c1 n1.2.2 (Or.inl n1.1) f1
    have I1 : IbFr (L := L) T s s1 := ibFr_footB0 hq F1
    have W1 : VcpuWK st T s s1 := vcpuWK_footB0 hq F1
    have hcur : L.curW s1 = L.curW s := k1.1
    have hcT : L.curW s ∈ T := hq.curT
    have V1 : VmPl st T Cs H Sg Scs Z U s1 := fun hv => by
      rw [hcur] at hv ⊢
      have est : L.mem s1 (stA (L.curW s)) = L.mem s (stA (L.curW s)) :=
        footB0_fld hq hcT (by simp [layout.tcb.STATE]) (by simp [layout.tcb.STATE]) F1
      have evc : L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64) =
          L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
        footB0_fld hq hcT (by simp) (by simp) F1
      refine ⟨hBA.of_fr I1, fun hw => ?_⟩
      rw [evc] at hw ⊢
      exact hPd (est ▸ hv) hw
    show (do
      let ct ← sched.cur_thread st s1
      let (s3, a3) ← vcpu.check st ar s1 a1 ct
      let (_, s4, a4) ← sched.check_budget st ar s3 a3
      ok (s4, a4)) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ∧ VcpuWK st T s s' ⦄
    rw [cur_thread_ok]; simp only [bind_ok]
    refine WP.spec_bind (WP.spec_and (vexit_checkV hA hNt s1 a1 E1 V1) T1) ?_
    rintro ⟨s2, a2⟩ ⟨⟨E2, I2, W2⟩, T2⟩
    refine WP.spec_bind (WP.spec_and (Fl4Proofs.P1.sched.check_budget.ibx hA s2 a2 E2 T2.ib)
      (sched.check_budget.vc hA s2 a2 E2 T2)) ?_
    rintro ⟨r, s3, a3⟩ ⟨⟨h3, I3⟩, W3⟩
    exact (WP.spec_ok _).2 ⟨h3, (I1.trans I2).trans I3, (W1.trans' W2).trans' W3⟩

/-- **`handle_vcpu_exit` up to `finish` keeps the invariants, the buffer
lookups and every VCPU word.** -/
theorem vexit_irq.ibv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq : U64) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hPd : PendAt st U s)
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄)
    (hI : vexit_pre st ar s a stalled ⦃ s1 _ => (irq != syscall.NO_IRQ) = true → IrqNtAt st Nt s1 ⦄) :
    vexit_irq st ar s a irq stalled ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ∧
      VcpuWK st T s s' ⦄ := by
  unfold vexit_irq
  refine WP.spec_bind (WP.spec_and (vexit_pre.ibv hA hNt s a stalled h hBA hPd htk) hI) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, I1, W1⟩, i1⟩
  try simp only [WP.uncurry'_pair] at h1 I1 W1 i1 ⊢
  split
  · rename_i hirq
    exact WP.spec_mono (WP.spec_and
      (Fl4Proofs.P1.interrupt.handle_interrupt.ibx hA hNt s1 a1 irq h1 (i1 hirq) (hBA.of_fr I1))
      (interrupt.handle_interrupt.vcx hA hNt s1 a1 irq h1 (i1 hirq) (hBA.of_fr I1)))
      fun r hr => by
        obtain ⟨s', a'⟩ := r
        simp only [WP.uncurry'_pair] at hr ⊢
        exact ⟨hr.1.1, I1.trans hr.1.2, W1.trans' hr.2.2⟩
  · exact (WP.spec_ok _).2 ⟨h1, I1, W1⟩

/-- **`hPF` of `entryB` from `VcpuZ` at the entry**: the VCPU words are kept
through `vexit_irq` and `finish_old`, so `PendAt` holds vacuously there. -/
theorem vexit_pf {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq : U64) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hz : VcpuZ st T s)
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄)
    (hI : vexit_pre st ar s a stalled ⦃ s1 _ => (irq != syscall.NO_IRQ) = true → IrqNtAt st Nt s1 ⦄) :
    vexit_irq st ar s a irq stalled ⦃ s2 a2 =>
      syscall.finish_old st ar s2 a2 ⦃ s3 _ => PendAt st U s3 ⦄ ⦄ := by
  have hPd : PendAt st U s := pendAt_of_vcpuZ hz h.1.choose_spec.choose_spec.curT
  refine WP.spec_mono (vexit_irq.ibv hA hNt s a irq stalled h hBA hPd htk hI) fun r hr => ?_
  obtain ⟨s2, a2⟩ := r
  try simp only [WP.uncurry'_pair] at hr ⊢
  obtain ⟨h2, I2, W2⟩ := hr
  refine WP.spec_mono (syscall.finish_old.vc hA hNt s2 a2 h2 (hBA.of_fr I2)) fun r3 hr3 => ?_
  obtain ⟨s3, a3⟩ := r3
  try simp only [WP.uncurry'_pair] at hr3 ⊢
  exact pendAt_of_vcpuZ (fun t ht => (hr3.1 t ht).trans ((W2 t ht).trans (hz t ht))) hr3.2

/-- `htk` with `TmoIbV` gives `entryB`'s `htk` (`TmoIb`). -/
theorem tmoIb_tk {A : Type _} {ar : machine.Arch A} {s : S} {a : A} {stalled : Bool}
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄) :
    stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄ := fun e =>
  WP.spec_mono (htk e) fun r hr => by
    obtain ⟨s1, a1⟩ := r
    try simp only [WP.uncurry'_pair] at hr ⊢
    exact WP.spec_mono hr fun r2 hr2 => by
      obtain ⟨s2, a2⟩ := r2
      try simp only [WP.uncurry'_pair] at hr2 ⊢
      exact hr2.ib

/-- **(vexit gen 3) The serial VM exit `handle_vcpu_exit` keeps `EntryInv`,
`hPd` and `hPF` discharged** (module docstring): from `EntryInv`, `BufAt`
(`hBA` [P]) and `VcpuZ` (`hz`) at the entry. Named premises: `hBA` [P],
`htk` [P] (`TmoIbV`), `hI` [P]. -/
theorem syscall.handle_vcpu_exit.entryV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq : U64) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hz : VcpuZ st T s)
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄)
    (hI : vexit_pre st ar s a stalled ⦃ s1 _ => (irq != syscall.NO_IRQ) = true → IrqNtAt st Nt s1 ⦄) :
    syscall.handle_vcpu_exit st ar s a irq stalled ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  Fl4Proofs.P1.syscall.handle_vcpu_exit.entryB hA hNt s a irq stalled h hBA
    (pendAt_of_vcpuZ hz h.1.choose_spec.choose_spec.curT) (tmoIb_tk htk) hI
    (vexit_pf hA hNt s a irq stalled h hBA hz htk hI)

/-- The no-IRQ `hI` from `vexit_pre.ibv`. -/
theorem vexit_noIrq {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hz : VcpuZ st T s)
    (htk : sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄) :
    vexit_pre st ar s a false ⦃ s1 _ => (syscall.NO_IRQ != syscall.NO_IRQ) = true → IrqNtAt st Nt s1 ⦄ :=
  WP.spec_mono (vexit_pre.ibv hA hNt s a false h hBA (pendAt_of_vcpuZ hz h.1.choose_spec.choose_spec.curT)
    fun _ => htk) fun r _ => by obtain ⟨s', a'⟩ := r; simp

/-- **The x86 local VM exit (no IRQ) keeps `EntryInv`** (`entryV`; no `hI`). -/
theorem vcpu_exit_local.entryV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (v n : U64) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hz : VcpuZ st T s)
    (htk : sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄) :
    localvm.handle_vcpu_exit_local st ar s a v n ⦃ r => r.1 = true →
      EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ :=
  Fl4Proofs.P1.vcpu_exit_local.entryB hA hNt s a v n h hBA
    (pendAt_of_vcpuZ hz h.1.choose_spec.choose_spec.curT) (tmoIb_tk (stalled := false) (fun _ => htk) rfl)
    (vexit_pf hA hNt s a syscall.NO_IRQ false h hBA hz (fun _ => htk) (vexit_noIrq hA hNt s a h hBA hz htk))

/-- **The x86 local VM timer exit keeps `EntryInv`** (`entryV`). -/
theorem vm_timer_local.entryV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq n : U64) (p : localtimer.TimerIrqPlan) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hz : VcpuZ st T s)
    (htk : sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄)
    (hI : vexit_pre st ar s a false ⦃ s1 _ => (irq != syscall.NO_IRQ) = true → IrqNtAt st Nt s1 ⦄) :
    localvm.handle_vm_timer_irq_local st ar s a irq p n ⦃ r => r.1 = true →
      EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ :=
  Fl4Proofs.P1.vm_timer_local.entryB hA hNt s a irq n p h hBA
    (pendAt_of_vcpuZ hz h.1.choose_spec.choose_spec.curT) (tmoIb_tk (stalled := false) (fun _ => htk) rfl) hI
    (vexit_pf hA hNt s a irq false h hBA hz (fun _ => htk) hI)

end

end Fl4Proofs.P2.Stall

/-
P1 (aarch64, gen 36): **the idle thread's `SC` field along the Zombie loop's steps** — the fact an SC cap inside a
covered slot needs (a64.md §39, route (b)).

An SC cap's finalisation (objects.rs `finalise_cap_object`, SchedContext arm → `unbind_all_tcbs`) needs, at the
round's state, "the SC's `TCB` word is not the idle thread" (`FinPl`'s SC clause, `ScPlAt`). Other covered slots'
finalisers write SC `TCB` words: the thread finaliser's `unbind_tcb` (to 0) and the reply finaliser's `reply_pop`
→ `schedcontext::donate` (ipc.rs:184–199, schedcontext.rs:65–79: `from.set_sc(0)`, `sc.set_tcb(to)`,
`to.set_sc(sc)`). Route (b): at every `BlkOK` state, `TSc` (an SC's `TCB` word `t ≠ 0` has `scA t = c`,
QueueObjs) turns "`scTcbA p = I`" into "`scA I = p`"; so it suffices that the idle thread's `SC` field `scA I`
keeps one ghost value `Is` along the loop and that the covered SC caps name SCs `≠ Is`. This module proves, per
step of the loop, the frame of that one word:

* **`ScK T s s'`** (every thread's `SC` field kept) with `ScK.of_w`, `sck_wr_out`, `sck_wr_fld`;
* the VCPU walks with `ScK`: `smp.remote_tcb_stall.sck`, **`vcpu.complete_run.sck`**, **`vcpu.unbind.sck`**,
  **`vcpu.detach.sck`**, **`vcpu.finalise.sck`** (gen 32's `.ubV` texts with `ScK` carried);
* per finaliser, "`scA u` kept or cleared" (`CurR`'s third field) — enough, because `BoundInv.idle`
  (`scA (idle) ≠ 0`) holds again at the round's end state: `fin_ntfn.si` (QueueFinCur's `CurF` chain),
  `fin_reply.si` (`reply_remove.curR` with `u` the idle thread: the replier is blocked on the reply, the idle thread
  is not, `BoundInv.idleNB`), the SC finaliser by QueueFinThr's `fin_sc.curR`, **`fin_thread.siV`** (stall,
  `detach.sck`, QueueFinThr7's `finThrRest.curR`), the endpoint by QueueCaiFr's `CaiFr.sc`;
* cap-slot writes (`W7.CapW` words are no TCB field at offset 3464: `capw_ne_sc`, `scK_cw`) and the preemption
  point (`sched.preemption_point.si`);
* the SC finaliser's idle word and `OSKeep`: **`fin_sc.idl`** (QueueFinSc's `fin_sc.blk` walk with
  `schedcontext.unbind_reply.idl`), `osk_sc`;
* **`siL`** (leaves), **`siZT`** (gen 35's `ZT` caps), **`siSc`** (SC caps).

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueZombieT
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local macro "sko" : tactic => `(tactic| first | omega | (simp; done) | (simp; omega) | (simp at *; omega) | simp_all)

/-! ## Every thread's `SC` field kept -/

/-- Every thread's `SC` field (TCB + 3464, `scA`) kept. -/
def ScK (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  ∀ z ∈ T, L.mem s' (scA z) = L.mem s (scA z)

theorem ScK.refl (s : S) : ScK st T s s := fun _ _ => rfl

theorem ScK.trans {s1 s2 s3 : S} (h1 : ScK st T s1 s2) (h2 : ScK st T s2 s3) : ScK st T s1 s3 :=
  fun z hz => (h2 z hz).trans (h1 z hz)

theorem ScK.of_w {s s' : S} {F : U64 → Prop} (hT : TcbPlaced T) (hw : WritesIn st s s' F)
    (hF : ∀ z ∈ T, ¬ F (scA z)) : ScK st T s s' :=
  fun z hz => hw.mem_eq (by rw [scA_eq]; exact field_aligned (hT z hz) (by simp) (by simp)) (hF z hz)

/-- A write of a word outside the TCBs and nodes. -/
theorem sck_wr_out {s0 s : S} {b v : U64} (hT : TcbPlaced T) (ho : OutsideObjs st T Cs s0 b) :
    ScK st T s (L.wr s b v) :=
  ScK.of_w hT (writesIn_wr ho.1) fun z hz e =>
    out_ne_field ho hz (hT z hz) (K := 3464#u64) (by simp) (by rw [← e]; rfl)

/-- A write of a TCB field other than 3464. -/
theorem sck_wr_fld {s : S} {y K v : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK : K.val < 4096) (h8 : K.val % 8 = 0)
    (hne : K.val ≠ 3464) : ScK st T s (L.wr s (core.num.U64.wrapping_add y K) v) :=
  ScK.of_w hT (writesIn_wr (field_aligned (hT y hy) hK h8)) fun z hz e =>
    field_ne (hT z hz) (hT y hy) (K1 := 3464#u64) (by simp) hK (fun _ h => hne (by simp at h; omega))
      (by rw [← scA_eq]; exact e)

/-! ## The SC finaliser keeps the idle word -/

theorem schedcontext.unbind_reply.idl (s : S) (c : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ≠ 0#u64 → c ∈ Scs) :
    schedcontext.unbind_reply st s c ⦃ s' => L.idleW s' = L.idleW s ⦄ := by
  unfold schedcontext.unbind_reply
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 rfl
  rename_i hb
  have hcS : c ∈ Scs := hc (fun e => hb (by rw [eb, e]; rfl))
  refine WP.spec_bind (obj.Sc.reply.val s c) fun i ei => ?_
  split
  · rename_i hi
    have hiR : i ∈ Rp := by rw [ei]; exact h.2.2.1.2.1.screp c hcS (by rw [← ei]; simpa using hi)
    refine WP.spec_bind (obj.Reply.set_next.val0 s i 0#u64) fun s1 e1 => ?_
    rw [zero_link] at e1
    subst e1
    obtain ⟨h1, -⟩ := rnext_zero_all h hiR
    refine WP.spec_mono (obj.Sc.set_reply.spec _ c 0#u64) fun s2 e2 => ?_
    subst e2
    have hO := h.2.2.1.1
    have hsub := h.2.2.2.2.sub
    exact (idleW_wr_out h1.1.choose_spec.choose_spec (hsub _ (hO.repW c hcS))).trans
      (idleW_wr_out h.1.choose_spec.choose_spec (hsub _ (hO.nextW hiR)))
  · exact (WP.spec_ok _).2 rfl

/-- **The SC finaliser keeps the idle-thread word** (QueueFinSc's `fin_sc.blk` walk). -/
theorem fin_sc.idl {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p x : U64)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) :
    objects.finalise_cap_object st ar s a (.SchedContext p x) fin ⦃ r => L.idleW r.2.1 = L.idleW s ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 rfl
  refine WP.spec_bind (schedcontext.unbind_all_tcbs.blk hA s a p h hp hp0 hna hidle) ?_
  rintro ⟨s1, a1⟩ ⟨h1, -, -, i1, -, -⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (WP.spec_and (schedcontext.unbind_ntfn.blk s1 p h1 fun _ => hp)
    (schedcontext.unbind_ntfn.idl s1 p h1 fun _ => hp)) fun s2 ⟨⟨h2, _⟩, i2⟩ => ?_
  refine WP.spec_bind (WP.spec_and (schedcontext.unbind_reply.blk s2 p p h2 (fun _ => hp) hp)
    (schedcontext.unbind_reply.idl s2 p h2 (fun _ => hp))) fun s3 ⟨⟨h3, _⟩, i3⟩ => ?_
  have i13 : L.idleW s3 = L.idleW s := i3.trans (i2.trans i1)
  refine WP.spec_bind (obj.Sc.yield_from.val s3 p) fun yf eyf => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
    L.idleW r.1 = L.idleW s) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, i13⟩
    · have hy : yf ≠ 0#u64 → yf ∈ T := fun hy0 => by
        rw [eyf]; exact h3.2.2.1.2.2.yt.2.2 p hp (by rw [← eyf]; exact hy0)
      refine WP.spec_mono (schedcontext.complete_yield_to.blk hA s3 a1 yf h3 hy) ?_
      rintro ⟨s4, a4⟩ ⟨h4, -, n4⟩
      exact ⟨h4, n4.2.1.trans i13⟩
  rintro ⟨s4, a2⟩ ⟨h4, i4⟩
  try simp only [WP.uncurry'_pair]
  have q4 := h4.1.choose_spec.choose_spec
  have hO4 := h4.2.2.1.1
  have hsub4 := h4.2.2.2.2.sub
  refine WP.spec_bind (obj.Sc.set_refill_max.spec s4 p 0#u64) fun s5 e5 => ?_
  subst e5
  have q5 := (omega_wr (v := 0#u64) q4 (hsub4 _ (hO4.mxW p hp))).1
  refine WP.spec_bind (obj.Sc.set_sporadic.wr _ p 0#u64) fun s6 e6 => ?_
  subst e6
  exact (WP.spec_ok _).2 (((idleW_wr_out q5 (spor_omega hO4 hp)).trans
    (idleW_wr_out q4 (hsub4 _ (hO4.mxW p hp)))).trans i4)

/-! ## The notification and reply finalisers: the `SC` field of a thread -/

/-- **The notification finaliser keeps every thread's `SC` field** (QueueFinCur's `CurF` chain). -/
theorem fin_ntfn.si {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (n b0 : U64) (b1 b2 : Bool) (fin : Bool)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hH : H n = some .ntfn) {u : U64} (hu : u ∈ T) :
    objects.finalise_cap_object st ar s a (.Notification n b0 b1 b2) fin ⦃ r =>
      L.mem r.2.1 (scA u) = L.mem s (scA u) ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · refine WP.spec_bind (WP.spec_and (schedcontext.maybe_unbind_ntfn.blk s n h hn)
      (schedcontext.maybe_unbind_ntfn.cura s n h hn)) fun s1 ⟨⟨h1, _⟩, c1⟩ => ?_
    refine WP.spec_bind (WP.spec_and (notification.unbind_maybe_notification.blkF s1 n h1 hn)
      (notification.unbind_maybe_notification.cura s1 n h1 hn)) fun s2 ⟨⟨h2, _⟩, c2⟩ => ?_
    refine WP.spec_bind (notification.cancel_all_signals.curF s2 n h2 hH) fun s3 ⟨c3, _⟩ => ?_
    exact (WP.spec_ok _).2 ((c3.2.2.1 u hu).trans ((c1.trans c2).1.2.2.1 u hu))
  · exact (WP.spec_ok _).2 rfl

/-- **The reply finaliser keeps the idle thread's `SC` field or clears it** (QueueFinCur's `finGap_reply` frame
with `u` the idle thread: the replier is blocked on the reply, the idle thread is not). -/
theorem fin_reply.si {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (x : Bool) (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Rp)
    (hRV : RunVcpuInv st T s) :
    objects.finalise_cap_object st ar s a (.Reply p x) fin ⦃ r =>
      L.mem r.2.1 (scA (L.idleW s)) = L.mem s (scA (L.idleW s)) ∨ L.mem r.2.1 (scA (L.idleW s)) = 0#u64 ⦄ := by
  have hiT : L.idleW s ∈ T := h.1.choose_spec.choose_spec.idleT
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 (Or.inl rfl)
  refine WP.spec_bind (obj.Reply.tcb.blk s p) fun i ei => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (Or.inl rfl)
  rename_i hbn
  have hi0 : i ≠ 0#u64 := fun e => hbn (by rw [eb, e]; rfl)
  have hX := h.2.2.1
  obtain ⟨-, hiT', -, -⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
  rw [← ei] at hiT'
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · rename_i hv
    have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_REPLY := by rw [← ev, hv]
    have hne : i ≠ L.idleW s := fun e => h.2.1.idleNB (by rw [← e, hst]; exact Or.inr rfl)
    refine WP.spec_bind (ipc.reply_remove.curR hA s a p i _ h hp hiT' ei.symm hst hiT hne
      (hRV.zero hiT' fun e => not_runnable_reply (by rw [← hst, e]; exact Or.inr (Or.inr rfl)))) ?_
    rintro ⟨s1, a1⟩ c1
    exact (WP.spec_ok _).2 c1.2.2.1
  split
  · obtain ⟨⟨Q, R, h0⟩, hB, -, hS, hSg⟩ := h
    refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h0 hiT' hB hX hSg.sub) ?_
    rintro ⟨s1, a1⟩ ⟨-, -, -, -, -, -, k1, -⟩
    exact (WP.spec_ok _).2 (Or.inl (k1.scf hiT))
  · exact (WP.spec_ok _).2 (Or.inl rfl)

/-! ## The VCPU walks with `ScK` -/

namespace W7
namespace R
namespace ST

local notation "wa" => core.num.U64.wrapping_add

variable {A : Type _} {ar : machine.Arch A} {P3Ok : S → Prop} {U : Set U64}

/-- The stall keeps every TCB field. -/
theorem smp.remote_tcb_stall.sck (hA : P0.ArchTotal ar) {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (a : A) (y : U64) : smp.remote_tcb_stall st ar s a y ⦃ s' _ => ScK st T s s' ⦄ := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := hb1.blk
  refine WP.spec_mono (smp.remote_tcb_stall.all hA s a y h0 hB hX hS hSg) ?_
  rintro ⟨s', a'⟩ ⟨-, -, -, -, -, -, -, -, -, k, -⟩
  exact fun z hz => by rw [scA_eq]; exact k z hz _ (by simp) (by simp)

section walk
variable {OS Vc Ub : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`complete_run` keeps every thread's `SC` field** (gen 32's `complete_run.ubV` text). -/
theorem vcpu.complete_run.sck (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A)
    (y stop m1 m2 m3 : U64) (hy : y ∈ T) (hvm : L.mem s (stA y) = sched.TS_RUNNING_VM) :
    vcpu.complete_run st ar s a y stop m1 m2 m3 ⦃ s' _ => ScK st T s s' ⦄ := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  have q := hb1.1.choose_spec.choose_spec
  have hT := q.tcbs
  have hta := hT y hy
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  have hU := hv.usr
  have hal : ∀ b ∈ Ub, Aligned b := fun b hb => (hU b hb).out.1
  unfold vcpu.complete_run
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq]
  by_cases hv0 : L.mem s (core.num.U64.wrapping_add y 3672#u64) = 0#u64
  · rw [if_pos hv0]; exact (WP.spec_ok _).2 (ScK.refl s)
  rw [if_neg hv0]
  have hvc : L.mem s (wa y 3672#u64) ∈ Vc := (hv.run y hy).resolve_left hv0
  have hbuf : RunBuf st Ub s y := hv.buf y hy hv0
  refine WP.spec_bind (hA.vcpu_flush_state _ _ _) fun a1 _ => ?_
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (· ∈ Ub)) ?_ fun s2 w2 => ?_
  · split
    · have hs : obj.Tcb.slot y layout.tcb.SLOT_BUFFER = ok (sbWordA y) := by
        simp [obj.Tcb.slot, lift, sbWordA]
      rw [hs, bind_ok]
      refine WP.spec_bind (spec_eq' (P0.obj.Slot.cap.p0 st (sbWordA y) s L.total)) fun c hc0 => ?_
      obtain ⟨hc, -⟩ := hc0
      cases c
      all_goals try exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      rename_i ptr size rights dev c1 c2 c3 c4
      refine WP.spec_bind (spec_eq' (P0.capability.FrameSize.bits.p0 size)) fun bits ⟨hbits, _⟩ => ?_
      have h63 : (bits &&& 63#u64).val < 64 := by
        rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by simp)
      refine WP.spec_bind (spec_eq' (P0.one_shift_positive _ h63)) fun sz ⟨hsz, _⟩ => ?_
      by_cases hd : dev = true
      · rw [if_pos hd]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      rw [if_neg hd]
      split
      · rename_i hrw
        split
        · rename_i ho
          split
          · rename_i hlt
            have hlt' : (L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3672#u64))
                vcpu.RUN_OFFSET)).val < sz.val := hlt
            step as ⟨i7, hi7⟩
            split
            · rename_i hge
              have hge' : 1024 ≤ i7.val := by scalar_tac
              have hF := hbuf ptr size rights dev c1 c2 c3 c4 bits sz hc (by simpa using hd) hrw hbits hsz
                ho hlt' (by unfold runOffA runVcpuA; omega)
              exact vcpu.read_state_to_frame.fw hA s a1 _ _ _ hF hal
            · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
          · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
        · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  have K2 : ScK st T s s2 := ScK.of_w hT w2 fun z hz hb =>
    (out_ne_field (hU _ hb).out hz (hT z hz) (K := 3464#u64) (by simp)) rfl
  obtain ⟨F2, B2, S2⟩ := UbF.usr h hU w2
  have hw : VcWords Ω Sg (L.mem s (core.num.U64.wrapping_add y 3672#u64)) := hW _ hvc
  have hx := hw vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
  have K3 := sck_wr_out (s := s2) (v := 0#u64) hT (q.omega _ hx.2.1)
  obtain ⟨F3, B3, S3⟩ := UbF.omega (v := 0#u64) F2.cur hx.1 hx.2.1 hx.2.2
  have K4 := sck_wr_fld (st := st) (s := L.wr s2 (wa (L.mem s (wa y 3672#u64)) vcpu.RUN_CALLER) 0#u64) (v := 0#u64)
    (K := 3672#u64) hT hy (by simp) (by simp) (by simp)
  obtain ⟨F4, B4, S4, rv4⟩ := UbF.rv0w F3.cur hy
  refine vck_regs _ y stop m1 m2 m3 hta fun s10 w10 => ?_
  have K10 := ScK.of_w hT w10 fun z hz hb => by
    obtain ⟨K, h1, h2, h3, e⟩ := hb
    exact field_ne (hT z hz) (hT y hy) (K1 := 3464#u64) (K2 := K) (by simp) (by omega)
      (fun _ h => by simp at h; omega) (by rw [← scA_eq]; exact e)
  obtain ⟨F10, B10, S10⟩ := UbF.regs F4.cur hy w10
  have F := ((F2.trans F3).trans F4).trans F10
  have st10 : L.mem s10 (stA y) = sched.TS_RUNNING_VM := by
    rw [(((S2.trans S3).trans S4).trans S10) y hy]; exact hvm
  obtain ⟨_, _, _, q10⟩ := Cur0.q F.cur
  refine WP.spec_bind (sts_fine s10 y sched.TS_RUNNING (q10.nodes _ q10.cur) (q10.tcbs y hy)) fun s11 w11 => ?_
  have K11 : ScK st T s10 s11 := ScK.of_w hT w11 fun z hz hb => by
    rcases hb with e | e
    · exact field_ne (hT z hz) (hT y hy) (K1 := 3464#u64) (K2 := 3328#u64) (by simp) (by simp)
        (fun _ => by first | decide | simp | omega) (by rw [← scA_eq, ← stA_eq]; exact e)
    · exact node_ne_field (o := layout.node.SCHED_ACTION) (q10.nodes _ q10.cur) (by first | (rw [act_val]; omega) | decide | (simp [layout.node.SCHED_ACTION]; done)) hz (hT z hz)
        (K := 3464#u64) (by simp) (by rw [← scA_eq]; exact e.symm)
  exact vck_vm_tail hA s11 a1 y (K2.trans (K3.trans (K4.trans (K10.trans K11))))

set_option maxHeartbeats 4000000 in
/-- **`vcpu::unbind` keeps every thread's `SC` field** (gen 32's `unbind.ubV` text). -/
theorem vcpu.unbind.sck (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (v : U64)
    (hvV : v ∈ Vc) :
    vcpu.unbind st ar s a v ⦃ s' _ => ScK st T s s' ⦄ := by
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  have V0 := hv.obj v hvV
  obtain ⟨_, _, _, q0⟩ := Cur0.q h
  have hT := q0.tcbs
  unfold vcpu.unbind vcpu.set_bound
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec, eq_of_spec_fd P0.Consts.layout.tcb.VCPU.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq]
  refine WP.spec_bind (Pₘ := fun r : S × A => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s r.1 ∧ BndK st T s r.1 ∧
    ScK st T s r.1 ∧ DS st T OS Vc s r.1) ?_ ?_
  · split
    · rename_i hne
      have hc0 : L.mem s (core.num.U64.wrapping_add v vcpu.RUN_CALLER) ≠ 0#u64 := by simpa using hne
      have hcT := V0.2.2.resolve_left hc0
      refine WP.spec_bind (WP.spec_and (WP.spec_and (smp.remote_tcb_stall.ub hA h a _)
        (smp.remote_tcb_stall.ds hA hO hV hW h a _)) (smp.remote_tcb_stall.sck hA h a _)) ?_
      rintro ⟨s2, a2⟩ ⟨⟨⟨F2, B2, -⟩, D2⟩, K2⟩
      try simp only [uncurry_apply_pair, WP.uncurry'_pair]
      step with obj.Tcb.state.spec as ⟨i1, ei1⟩
      split
      · rename_i hvm
        refine WP.spec_mono (WP.spec_and (vcpu.complete_run.ubV hA hO hV F2.cur (hv.keepZ D2.2) a2 _ _ _ _ _ hcT
          (by rw [← ei1]; exact hvm)) (vcpu.complete_run.sck hA hO hV F2.cur (hv.keepZ D2.2) a2 _ _ _ _ _ hcT
          (by rw [← ei1]; exact hvm))) ?_
        rintro ⟨s3, a3⟩ ⟨⟨F3, B3, D3⟩, K3⟩
        exact ⟨F2.trans F3, B2.trans B3, ScK.trans K2 K3, DS.trans D2 D3⟩
      · have hx := V0.1 vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
        obtain ⟨F3, B3, -⟩ := UbF.omega (v := 0#u64) F2.cur hx.1 hx.2.1 hx.2.2
        obtain ⟨_, _, _, q2⟩ := Cur0.q F2.cur
        have D3 := DS.vc0 (o := vcpu.RUN_CALLER) hO hV q2 hW hvV (by simp [vcpu.RUN_CALLER])
          (by simp [vcpu.RUN_CALLER])
        have K3 := sck_wr_out (s := s2) (v := 0#u64) hT (q0.omega _ hx.2.1)
        obtain ⟨F4, B4, -, -⟩ := UbF.rv0w F3.cur hcT
        obtain ⟨_, _, _, q3⟩ := Cur0.q F3.cur
        have D4 := DS.lnk0 (K := 3672#u64) hO hV q3 hW hcT (Or.inr (by simp))
        have K4 := sck_wr_fld (st := st) (s := L.wr s2 (wa v vcpu.RUN_CALLER) 0#u64) (v := 0#u64) (K := 3672#u64) hT hcT
          (by simp) (by simp) (by simp)
        exact (WP.spec_ok _).2 ⟨(F2.trans F3).trans F4, (B2.trans B3).trans B4, K2.trans (K3.trans K4),
          D2.trans (D3.trans D4)⟩
    · exact (WP.spec_ok _).2 ⟨UbF.refl h, BndK.refl s, ScK.refl s, DS.refl s⟩
  rintro ⟨s1, a1⟩ ⟨F1, B1, K1, D1⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  have V1 := (hv.keepZ D1.2).obj v hvV
  split
  · exact (WP.spec_ok _).2 K1
  rename_i ht0
  have htT := V1.2.1.resolve_left ht0
  refine WP.spec_bind (WP.spec_and (WP.spec_and (smp.remote_tcb_stall.ub hA F1.cur a1 _)
    (smp.remote_tcb_stall.ds hA hO hV hW F1.cur a1 _)) (smp.remote_tcb_stall.sck hA F1.cur a1 _)) ?_
  rintro ⟨s2, a2⟩ ⟨⟨⟨F2, -, -⟩, D2⟩, K2⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  refine WP.spec_bind (hA.vcpu_flush a2 v) fun a3 _ => ?_
  have hx0 := V1.1 vcpu.TCB (by simp [vcpu.TCB]) (by simp [vcpu.TCB])
  have hx8 := V1.1 vcpu.OWNER_CPU (by simp [vcpu.OWNER_CPU]) (by simp [vcpu.OWNER_CPU])
  have K3 := sck_wr_out (s := s2) (v := 0#u64) hT (q0.omega _ hx0.2.1)
  have K4 := sck_wr_out (s := L.wr s2 (wa v vcpu.TCB) 0#u64) (v := 0#u64) hT (q0.omega _ hx8.2.1)
  obtain ⟨F3, -, -⟩ := UbF.omega (v := 0#u64) F2.cur hx0.1 hx0.2.1 hx0.2.2
  obtain ⟨F4, -, -⟩ := UbF.omega (v := 0#u64) F3.cur hx8.1 hx8.2.1 hx8.2.2
  have K5 := sck_wr_fld (st := st) (s := L.wr (L.wr s2 (wa v vcpu.TCB) 0#u64) (wa v vcpu.OWNER_CPU) 0#u64) (v := 0#u64)
    (K := 3664#u64) hT htT (by simp) (by simp) (by simp)
  obtain ⟨F5, -⟩ := UbF.bnd0 (v := 0#u64) F4.cur htT
  obtain ⟨Ac5, hb5⟩ := F5.cur.bxi
  have hT5 := hb5.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st _ _ _ L.total) fun old _ => ?_
  refine WP.spec_bind (P0.regs.sanitise.p0 _ _) fun i4 _ => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.regW _ (hT5 _ htT) (by simp [layout.reg.SPSR_EL1]) (WritesIn.refl _ _))
    fun s6 w6 => ?_
  have K6 := ScK.of_w hT w6 fun z hz hb => by
    obtain ⟨K, h1, h2, h3, e⟩ := hb
    exact field_ne (hT z hz) (hT _ htT) (K1 := 3464#u64) (K2 := K) (by simp) (by omega)
      (fun _ h => by simp at h; omega) (by rw [← scA_eq]; exact e)
  exact vck_vm_tail hA s6 a3 _ (K1.trans (K2.trans (K3.trans (K4.trans (K5.trans K6)))))

set_option maxHeartbeats 2000000 in
/-- **`vcpu::detach` keeps every thread's `SC` field** (gen 32's `detach.ubV` text). -/
theorem vcpu.detach.sck (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (p : U64)
    (hp : p ∈ T) :
    vcpu.detach st ar s a p ⦃ s' _ => ScK st T s s' ⦄ := by
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  obtain ⟨_, _, _, q⟩ := Cur0.q h
  have hT := q.tcbs
  unfold vcpu.detach
  refine WP.spec_bind (Pₘ := fun r : S × A => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s r.1 ∧ BndK st T s r.1 ∧
    L.mem r.1 (runVcpuA p) = 0#u64 ∧ ScK st T s r.1 ∧ DS st T OS Vc s r.1) ?_ ?_
  · unfold vcpu.cancel_run
    rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
    simp only [lift, bind_ok, L.read_eq, L.write_eq]
    split
    · rename_i hne
      have hv' : L.mem s (runVcpuA p) ≠ 0#u64 := by simpa [runVcpuA] using hne
      have hvc : L.mem s (runVcpuA p) ∈ Vc := (hv.run p hp).resolve_left hv'
      have hx := hW _ hvc vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
      obtain ⟨F1, B1, -⟩ := UbF.omega (v := 0#u64) h hx.1 hx.2.1 hx.2.2
      have D1 := DS.vc0 (o := vcpu.RUN_CALLER) hO hV q hW hvc (by simp [vcpu.RUN_CALLER])
        (by simp [vcpu.RUN_CALLER])
      have K1 := sck_wr_out (s := s) (v := 0#u64) hT (q.omega _ hx.2.1)
      obtain ⟨F2, B2, -, e2⟩ := UbF.rv0w F1.cur hp
      obtain ⟨_, _, _, q1⟩ := Cur0.q F1.cur
      have D2 := DS.lnk0 (K := 3672#u64) hO hV q1 hW hp (Or.inr (by simp))
      have K2 := sck_wr_fld (st := st) (s := L.wr s (wa (L.mem s (runVcpuA p)) vcpu.RUN_CALLER) 0#u64) (v := 0#u64)
        (K := 3672#u64) hT hp (by simp) (by simp) (by simp)
      exact (WP.spec_ok _).2 ⟨F1.trans F2, B1.trans B2, e2, K1.trans K2, D1.trans D2⟩
    · rename_i heq
      exact (WP.spec_ok _).2 ⟨UbF.refl h, BndK.refl s, UScalar.eq_of_val_eq (by simpa [runVcpuA] using heq),
        ScK.refl s, DS.refl s⟩
  rintro ⟨s1, a1⟩ ⟨F1, B1, rv1, K1, D1⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  have hv1 := hv.keepZ D1.2
  step with vcpu.bound.spec as ⟨v, ev⟩
  split
  · rename_i hne
    have hv0 : v ≠ 0#u64 := by simpa using hne
    have hvV : v ∈ Vc := by
      rcases hv1.bnd p hp with e | e
      · exact absurd (ev.trans e) hv0
      · rw [ev]; exact e
    refine WP.spec_mono (vcpu.unbind.sck hA hO hV F1.cur hv1 a1 v hvV) ?_
    rintro ⟨s2, a2⟩ K2
    exact K1.trans K2
  · exact (WP.spec_ok _).2 K1

/-- **`vcpu::finalise` keeps every thread's `SC` field.** -/
theorem vcpu.finalise.sck (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (v : U64)
    (hvV : v ∈ Vc) :
    vcpu.finalise st ar s a v ⦃ s' _ => ScK st T s s' ⦄ := by
  unfold vcpu.finalise
  refine WP.spec_bind (vcpu.unbind.sck hP hO hV h hv a v hvV) ?_
  rintro ⟨s1, a1⟩ K1
  try simp only [WP.uncurry'_pair, uncurry_apply_pair] at K1 ⊢
  refine WP.spec_bind (hP.vcpu_flush_spec a1 v) fun a2 _ => ?_
  exact (WP.spec_ok _).2 K1

set_option maxHeartbeats 2000000 in
/-- **The thread finaliser keeps the `SC` field of a thread `u` or clears it** (any finality, a bound VCPU or a
run in flight included): the stall and `detach` keep it, then QueueFinThr7's `finThrRest.curR`. -/
theorem fin_thread.siV (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (p : U64)
    (fin : Bool) (hp : p ∈ T) (hid : p ≠ L.idleW s) {u : U64} (hu : u ∈ T) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r =>
      L.mem r.2.1 (scA u) = L.mem s (scA u) ∨ L.mem r.2.1 (scA u) = 0#u64 ⦄ := by
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  cases fin
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · rename_i hf; exact absurd hf (by simp)
    · exact (WP.spec_ok _).2 (Or.inl rfl)
  rw [fin_thread_split]
  refine WP.spec_bind (WP.spec_and (WP.spec_and (smp.remote_tcb_stall.ub hA h a p)
    (smp.remote_tcb_stall.ds hA hO hV hW h a p)) (smp.remote_tcb_stall.sck hA h a p)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨F1, -, -⟩, D1⟩, K1⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  refine WP.spec_bind (WP.spec_and (vcpu.detach.ubV hA hO hV F1.cur (hv.keepZ D1.2) a1 p hp)
    (vcpu.detach.sck hA hO hV F1.cur (hv.keepZ D1.2) a1 p hp)) ?_
  rintro ⟨s2, a2⟩ ⟨⟨F2, rv2, D2⟩, K2⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  have F12 := F1.trans F2
  obtain ⟨Ac2, hb2⟩ := F12.cur.bxi
  have hna : L.actionW s2 ≠ p := F12.cur.na p hp
  have hidle : L.idleW s2 ≠ p := by rw [F12.idle]; exact Ne.symm hid
  have e12 : L.mem s2 (scA u) = L.mem s (scA u) := (K2 u hu).trans (K1 u hu)
  refine WP.spec_mono (finThrRest.curR hA s2 a2 p u hb2.blk hp hna hidle hu rv2) fun r hr => ?_
  rcases hr.2.2.1 with e | e
  · exact Or.inl (e.trans e12)
  · exact Or.inr e

end walk

/-! ## Cap-slot writes and the preemption point -/

/-- A `W7.CapW` word is no thread's `SC` field. -/
theorem capw_ne_sc {s : S} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) {b z : U64} (hb : W7.CapW T Ω Sg b) (hz : z ∈ T) : b ≠ scA z := by
  intro e
  rcases hb with ⟨t, ht, K, hK, e'⟩ | ⟨hΩ, -⟩
  · rw [e'] at e
    exact field_ne (q.tcbs t ht) (q.tcbs z hz) (K1 := K) (K2 := 3464#u64) (by omega) (by simp)
      (fun _ h => by simp at h; omega) (by rw [e, scA_eq])
  · rw [e] at hΩ
    exact (out_ne_field (q.omega _ hΩ) hz (q.tcbs z hz) (K := 3464#u64) (by simp)) rfl

/-- **A `W7.CapW` footprint keeps every thread's `SC` field.** -/
theorem scK_cw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' (W7.CapW T Ω Sg)) : ScK st T s s' :=
  ScK.of_w q.tcbs hw fun z hz hb => capw_ne_sc q hb hz rfl

section si
variable {OS Vc Ub : Set U64}

theorem JV.sik_cw {s0 s s' : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hw : WritesIn st s s' (W7.CapW T Ω Sg)) : ScK st T s s' := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  exact scK_cw hb.1.choose_spec.choose_spec hw

set_option maxHeartbeats 2000000 in
/-- **The preemption point keeps every TCB field**, so every thread's `SC` field. -/
theorem sched.preemption_point.si (hP : P0.ArchTotal ar) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) :
    sched.preemption_point st ar s a ⦃ r => ScK st T s r.2.1 ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hN := q.nodes _ q.cur
  obtain ⟨hwa, hΩ, -⟩ := ks_work_units hb.blk
  have ho := q.omega _ hΩ
  have hT := q.tcbs
  refine WP.spec_mono (sched.preemption_point.pp (Ac := Ac') hP s a hb.blk) ?_
  rintro r ⟨-, w⟩
  intro y hy
  rw [scA_eq]
  refine w.2.2 _ (field_aligned (hT _ hy) (by simp) (by simp)) fun hp => ?_
  rcases hp with e | e | e
  · exact out_ne_field (K := 3464#u64) ho hy (hT _ hy) (by simp) (congrArg UScalar.val e)
  · exact node_ne_field (K := 3464#u64) (o := layout.node.CUR_TIME) hN (by simp [layout.node.CUR_TIME]) hy
      (hT _ hy) (by simp) (by unfold LawfulStore.nodeA at e; exact e.symm)
  · exact node_ne_field (K := 3464#u64) (o := layout.node.CONSUMED) hN (by simp [layout.node.CONSUMED]) hy
      (hT _ hy) (by simp) (by unfold LawfulStore.nodeA at e; exact e.symm)

/-! ## Per finaliser: the idle thread's `SC` field kept or cleared -/

/-- "The `SC` field of `u` kept or cleared" from `s` to `s'`. -/
def SIK (st : machine.Store S) [L : LawfulStore st] (u : U64) (s s' : S) : Prop :=
  L.mem s' (scA u) = L.mem s (scA u) ∨ L.mem s' (scA u) = 0#u64

set_option maxHeartbeats 2000000 in
/-- **A leaf cap's finalisation keeps the idle thread's `SC` field or clears it.** -/
theorem siL (hP : P0.ArchTotal ar) {s0 s : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64}
    (hx : x ∈ OS) {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c) (hk : ZL c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => SIK st (L.idleW s) s r.2.1 ⦄ := by
  rcases hk with ht | he
  · rw [finalise_cap.triv ar s a ht fin]; exact (WP.spec_ok _).2 (Or.inl rfl)
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  obtain ⟨Ac', hb⟩ := h.1.parts
  have hiT : L.idleW s ∈ T := hb.1.choose_spec.choose_spec.idleT
  rcases he with ⟨p, b0, b1, b2, b3, b4, rfl⟩ | ⟨n, b0, b1, b2, rfl⟩ | ⟨p, g, rfl⟩
  · have hH : H p = some .ep := hty.1.1.1 p b0 b1 b2 b3 b4 rfl
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_endpoint.fr (ar := ar) s a p b0 b1 b2 b3 b4 fin hb.blk hH) fun r hr =>
      Or.inl (hr.2.2.2.2.1.sc _ hiT)
  · obtain ⟨hn, hH⟩ := hty.1.1.2.1 n b0 b1 b2 rfl
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_ntfn.si (ar := ar) s a n b0 b1 b2 fin hb.blk hn hH hiT) fun r hr => Or.inl hr
  · have hp : p ∈ Rp := hty.1.1.2.2 p g rfl
    rw [fin_cap_eq_obj (by simp)]
    exact fin_reply.si hP s a p g fin hb.blk hp h.1.1.2

set_option maxHeartbeats 4000000 in
/-- **A `ZT` cap's finalisation keeps the idle thread's `SC` field or clears it.** -/
theorem siZT (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {D : Set U64} {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64} (hx : x ∈ OS)
    {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c) (hX : ZT Vc D (L.idleW s) c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => SIK st (L.idleW s) s r.2.1 ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have hiT : L.idleW s ∈ T := hb.1.choose_spec.choose_spec.idleT
  rcases hX with hz | ⟨p, rfl, hid, -⟩ | ⟨v, rfl, hvV⟩
  · rcases hz with hl | ⟨p, r, g, b, rfl, -⟩ | ⟨p, t, n, rfl, -⟩
    · exact siL hP h hx hc hl a fin
    · exact WP.spec_mono (fin_cnode.z ar s a p r g b fin) fun x hr => Or.inl (by rw [hr.1])
    · rw [fin_zombie.z]; exact (WP.spec_ok _).2 (Or.inl rfl)
  · have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
    have hp : p ∈ T := hty.1.2.2.2.2.2 p rfl
    rw [fin_cap_eq_obj (by simp)]
    exact fin_thread.siV hP hO hV h.1.1.1 h.2 a p fin hp hid hiT
  · rw [fin_cap_eq_obj (by simp)]
    cases fin
    · unfold objects.finalise_cap_object
      dsimp only
      split
      · rename_i hf; exact absurd hf (by simp)
      · exact (WP.spec_ok _).2 (Or.inl rfl)
    · unfold objects.finalise_cap_object
      dsimp only
      split
      · refine WP.spec_bind (vcpu.finalise.sck hP hO hV h.1.1.1 h.2 a v hvV) ?_
        rintro ⟨s1, a1⟩ K1
        try simp only [WP.uncurry'_pair, uncurry_apply_pair] at K1 ⊢
        exact (WP.spec_ok _).2 (Or.inl (K1 _ hiT))
      · rename_i hf; exact absurd rfl hf

/-! ## SC caps -/

/-- An SC cap's case at a state (`FinPl`'s SC clause), from the idle thread's `SC` field `Is` (`TSc`). -/
theorem scpl_of {s0 s : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x p b Is : U64}
    (hc : obj.Slot.cap st x s = ok (.SchedContext p b)) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64) (hpI : p ≠ Is)
    (hIs : L.mem s (scA (L.idleW s)) = Is) : ScPlAt st Scs x s := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have hX := hb.blk.2.2.1
  intro c hc'
  rw [hc] at hc'
  obtain rfl := okinj hc'
  refine ⟨⟨p, b, rfl⟩, And.intro (fun _ e => ?_) (fun p' b' e => ?_)⟩
  · cases e
  simp only [capability.Cap.SchedContext.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  refine ⟨hp, hp0, fun h0 ei => hpI ?_⟩
  have := hX.2.2.tsc p hp hp0 h0
  rw [← ei, hIs] at this
  exact this.symm

theorem osk_sc (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64} (a : A) (fin : Bool) (hk : ScPlAt st Scs x s)
    {p b : U64} (hc : obj.Slot.cap st x s = ok (.SchedContext p b)) :
    objects.finalise_cap st ar s a (.SchedContext p b) fin false ⦃ r => OSKeep st OS s r.2.1 ∧
      L.idleW r.2.1 = L.idleW s ∧ SIK st (L.idleW s) s r.2.1 ⦄ := by
  obtain ⟨-, hpl⟩ := hk _ hc
  obtain ⟨hpS, hp0, hid⟩ := hpl.2 p b rfl
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hsub : ∀ b ∈ Sg, b ∈ Ω := by obtain ⟨-, -, -, -, hSg⟩ := hb.blk; exact hSg.sub
  have hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p) := fun h0 =>
    h.1.1.1.na _ (hb.2.2.1.2.2.yt.1 p hpS h0)
  have hiT : L.idleW s ∈ T := q.idleT
  rw [fin_cap_eq_obj (by simp)]
  refine WP.spec_mono (WP.spec_and (WP.spec_and (K7.fin_sc.blk (ar := ar) hP s a p b fin hb.blk hpS hp0 hna hid)
    (fin_sc.idl hP s a p b fin hb.blk hpS hp0 hna hid))
    (fin_sc.curR hP s a p b (L.idleW s) fin hb.blk hpS hp0 hna hid hiT)) ?_
  rintro r ⟨⟨⟨_, _, _, f⟩, i⟩, c⟩
  exact ⟨OSKeep.of_kw7 hO q hsub hA (fun e he => absurd he (Set.notMem_empty e)) f, i, c.2.2.1⟩

end si

end ST
end R
end W7

end

end Fl4ProofsA64.P1

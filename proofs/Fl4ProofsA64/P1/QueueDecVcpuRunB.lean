/-
P1 (aarch64): **`ARMVCPURun`** over the corrected placements, and the VCPU family's `DecGap` with every label proved.

* `sched.set_thread_state.vm_cur0`: the current thread made `TS_RUNNING_VM` (runnable, not blocked) keeps `Cur0`.
* **`vcpu.check.ub`**: `vcpu::check` of any thread from a `Cur0` state (QueueUnbindB's steps; the bound
  notification's idle write as VcpuCheckInv's `ntfn_idle_all`; the completion `vcpu.complete_run.ub`, its run VCPU
  and run frame from [P] `VcPl` at that state).
* **`vcpu.decode_run.dec`**: the checks, the stall of the bound TCB, `OWNER_CPU := me`, `write_state_from_frame`
  (QueueDecVcpuStA `vcpu.write_state_from_frame.vcj`), `RUN_CALLER := ct`, `RUN_OFFSET`, `RUN_OUT_MASK` (words of
  `Ω \ Sg`, [P] `VcpuW`), `RUN_VCPU(ct) := vc` (`Cur0.vfC`), `set_stage2_root` (no store write),
  `set_thread_state ct TS_RUNNING_VM`, `vcpu.check ct`.
* **`decGap_vcpuD`**: the VCPU family's `DecGap`, all eight labels proved.

Named premises: those used ([P] `VcpuW`, [P] `VcpuStA`, [P] `VcpuObjA`, [P] `VcPl` through `B.DelPlace`) and
the heap's notification typing `∀ n ∈ Nt, H n = some .ntfn` (as `vcpu.check.vck`'s `hNt`, assumed by every entry
top's `GF`). No new premise.
-/
import Fl4ProofsA64.P1.QueueDecVcpuB
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-- `Cur0` keeps the current thread. -/
theorem Cur0.curEq {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : L.curW s = L.curW s0 :=
  h.2.choose_spec.2.1

/-- **The current thread made `TS_RUNNING_VM`** keeps `Cur0` (its state not blocked before). -/
theorem sched.set_thread_state.vm_cur0 {s0 s : S} {t : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (ht : L.curW s = t) :
    sched.set_thread_state st s t sched.TS_RUNNING_VM ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  subst ht
  obtain ⟨Ac1, hb1⟩ := h.bxi
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := hb1.blk
  have hct : L.curW s ∈ T := h0.curT
  have hnb := h.nb
  have rvm : Runnable sched.TS_RUNNING_VM := Or.inr (Or.inr rfl)
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ L.curW s :=
    hX.noref (h0.tcbs _ hct) (fun e => hnb (Or.inr e)) (fun e => hnb (Or.inl (Or.inr (Or.inl e))))
  refine WP.spec_mono (WP.spec_and (sts_all s _ _ Q R h0 hB hX hS hSg hct (runnable_ok rvm).1
    ⟨runnable_ne_reply rvm, runnable_ne_recv rvm⟩ (Or.inr fun hb => hnb (Or.inl hb)) hnoref
    ⟨fun _ _ _ _ _ => rvm, fun _ _ _ => rvm, fun _ => rvm⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s _ _ h0 hct)) ?_
  rintro s' ⟨⟨h1, hB1, hX1, hS1, hSg1, e1, k⟩, f1⟩
  have hb2 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac1 s' := ⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hS1, hSg1⟩
  exact Cur0.mk h (BlkOK.bxi hb2) k.curW k.cscW (Or.inl (k.scf hct)) k.act
    (Or.inr (by rw [e1]; exact nbr_runnable rvm)) (Foot.cur0w f1 (Set.empty_subset _))

set_option maxHeartbeats 4000000 in
/-- **`vcpu::check` of any thread** from a `Cur0` state (module docstring). -/
theorem vcpu.check.ub (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {s0 s : S}
    (Pl : VcPl st T Cs Ω H Sg Rp Scs Nt Z s0) (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (a : A) (y : U64)
    (hy : y ∈ T) :
    vcpu.check st ar s a y ⦃ s' _ => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ := hb1.blk
  have hT := hq.tcbs
  have hta := hT y hy
  have hN := hq.nodes _ hq.cur
  have hct : L.curW s ∈ T := hq.curT
  unfold vcpu.check
  step with obj.Tcb.state.spec as ⟨i, ei⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hvm0
  have hvm : L.mem s (stA y) = sched.TS_RUNNING_VM := by
    rw [← ei]; by_contra hne; exact hvm0 (bne_iff_ne.mpr hne)
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
  simp only [lift, bind_ok, L.read_eq]
  by_cases hv0 : L.mem s (core.num.U64.wrapping_add y 3672#u64) = 0#u64
  · rw [if_pos hv0]
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st _ s _ L.total) fun ip _ => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.regW s hta (by simp [layout.reg.FAULT_IP]) (WritesIn.refl _ _))
      fun s1 w1 => ?_
    obtain ⟨F1, -, S1⟩ := UbF.regs h hy w1
    refine WP.spec_bind (sched.set_thread_state.running_ub F1.cur hy (by rw [S1 y hy]; exact hvm)
      (F1.rv0 y hy hv0)) fun s2 hh => ?_
    exact (WP.spec_ok _).2 hh.1.cur
  rw [if_neg hv0]
  refine WP.spec_bind (obj.Tcb.bound_ntfn.val s _) fun n en => ?_
  split
  · rename_i hn
    refine WP.spec_bind (obj.Ntfn.state.spec s n) fun i3 ei3 => ?_
    split
    · rename_i hact0
      have hn0 : n ≠ 0#u64 := by simpa using hn
      have hact : L.epState s n = obj.NTFN_ACTIVE := by rw [← ei3]; exact hact0
      have hnN : n ∈ Nt := by rw [en]; exact hX.2.2.bnd _ hy (by rw [← en]; exact hn0)
      have hnH := hNt n hnN
      obtain ⟨E, EQ, hEW⟩ := hq.eps
      have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hnH)
      obtain ⟨hE, hEN, -⟩ := hEW.1 n he
      have hTS := epTSA_val hE
      have a2 : Aligned (epTSA n) := (ep_aligned hE).2
      refine WP.spec_bind (obj.Ntfn.badge.any s n) fun bd _ => ?_
      refine WP.spec_bind (obj.Ntfn.set_state.val s n _) fun s1 e1 => ?_
      subst e1
      obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, -, -, -, -⟩ :=
        ntfn_idle_all hq hB hX hS hSg hnH (by rw [hact, ntfn_active_val])
      have hout : OutsideObjs st T Cs s (epTSA n) := by
        refine ⟨a2, fun t ht => ?_, fun c hc => ?_⟩
        · have := hE.disj t ht; rw [hTS]; omega
        · have := hEN.1 c hc; rw [hTS]; omega
      have hw := writesIn_wr (st := st) (s := s)
        (v := (L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) a2
      obtain ⟨an, ecs⟩ := ani_of_wi hw hN hq.cur hT fun b e => Or.inl (by rw [e]; exact hout)
      have c1 : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0
          (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64))) :=
        Cur0.mk h (BlkOK.bxi ⟨⟨Q, R, h2⟩, hB2, hX2, hS2, hSg2⟩) an.2.2 ecs
          (Or.inl (by rw [scA_eq]; exact f2 _ hct _ (by simp) (by simp) (by simp) (by simp)))
          (Or.inl an.1) (Or.inl (by rw [stA_eq]; exact f2 _ hct _ (by simp) (by simp) (by simp) (by simp)))
          (hw.mono fun b e => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inr hnH, Or.inr e⟩)))))
      obtain ⟨Ac2, hb2⟩ := c1.bxi
      have st1 : L.mem (L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)))
          (stA y) = sched.TS_RUNNING_VM := by
        rw [stA_eq, f2 _ hy _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hvm
      exact WP.spec_mono (vcpu.complete_run.ub hA c1 a y _ _ _ _ hy st1 (fun h0 => Pl.rcv Ac2 _ y c1.fr hb2 hy h0)
        (fun b hb => hb) (Pl.rbuf Ac2 _ y c1.fr hb2 hy)) fun r hr => by
          obtain ⟨s', a'⟩ := r; exact hr.1.cur
    · exact (WP.spec_ok _).2 h
  · exact (WP.spec_ok _).2 h

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errS" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [bind_ok, bind_tc_ok, lift, error.illegal, error.truncated, error.range, error.invalid_arg,
      error.invalid_cap]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option hygiene false in
/-- A total step whose value is not needed. -/
local macro "tbS" : tactic => `(tactic| (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun _ _ => ?_))

set_option hygiene false in
/-- `decode_run`'s tail from the stall of the bound TCB (both branches of the VGIC check). -/
local macro "runT" : tactic => `(tactic| (
  refine WP.spec_bind (smp.remote_tcb_stall.ub hA c0 a _) ?_
  rintro ⟨s2, a1⟩ ⟨F2, -, -⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  step with LawfulStore.cur_cpu_spec as ⟨cc, ecc⟩
  try simp only [lift, bind_ok, L.read_eq]
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun a2 _ => ?_
  try simp only [lift, bind_ok, L.write_eq]
  have hx8 := hw vcpu.OWNER_CPU (by simp [vcpu.OWNER_CPU]) (by simp [vcpu.OWNER_CPU])
  obtain ⟨F3, -, -⟩ := UbF.omega (v := core.num.U64.wrapping_add cc 1#u64) F2.cur hx8.1 hx8.2.1 hx8.2.2
  refine WP.spec_bind (vcpu.write_state_from_frame.vcj hA D.user hw _ _ _ _ ⟨F3.cur, (vU _ F3.cur).2.1⟩)
    fun s4 J4 => ?_
  try simp only [lift, bind_ok, L.write_eq]
  have hx24 := hw vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
  have hx32 := hw vcpu.RUN_OFFSET (by simp [vcpu.RUN_OFFSET]) (by simp [vcpu.RUN_OFFSET])
  have hx40 := hw vcpu.RUN_OUT_MASK (by simp [vcpu.RUN_OUT_MASK]) (by simp [vcpu.RUN_OUT_MASK])
  obtain ⟨F5, -, -⟩ := UbF.omega (v := L.curW s) J4.1 hx24.1 hx24.2.1 hx24.2.2
  obtain ⟨F6, -, -⟩ := UbF.omega (v := off) F5.cur hx32.1 hx32.2.1 hx32.2.2
  obtain ⟨F7, -, -⟩ := UbF.omega (v := outm) F6.cur hx40.1 hx40.2.1 hx40.2.2
  obtain ⟨c8, -, -, -⟩ := Cur0.vfC (K := 3672#u64) (v := vc) F7.cur hct (Or.inr (by simp))
  refine WP.spec_bind (set_stage2_root_same hA _ a2 _) ?_
  rintro ⟨s9, a3⟩ e9
  try simp only [uncurry_apply_pair, WP.uncurry'_pair] at e9 ⊢
  subst e9
  refine WP.spec_bind (sched.set_thread_state.vm_cur0 c8 (Cur0.curEq c8)) fun s10 c10 => ?_
  refine WP.spec_bind (vcpu.check.ub hA hNt Pl c10 a3 _ hct) ?_
  rintro ⟨s11, a4⟩ c11
  exact (WP.spec_ok _).2 c11.post))

set_option maxHeartbeats 8000000 in
/-- **`ARMVCPURun`** keeps the invariants (module docstring). -/
theorem vcpu.decode_run.dec (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {s : S} {vc : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Vcpu vc) extra) (Pl : VcPl st T Cs Ω H Sg Rp Scs Nt Z s)
    (hV : ∀ (Ac' : Set U64) (s' : S), Fr0 st T Cs Ω H Sg Scs Z s s' → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' →
      VcObj st T Ω Sg s' vc) (a : A) (len : U64) (call : Bool) (buf : U64) :
    vcpu.decode_run st ar s a vc len call buf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have c0 : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s := (Stalled.refl0 D).cur0 D
  have vU : ∀ s' : S, Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s' → VcObj st T Ω Sg s' vc := fun s' h' => by
    obtain ⟨Ac', hb'⟩ := h'.bxi; exact hV Ac' s' h'.fr hb'
  have hw : VcWords Ω Sg vc := (vU s c0).1
  unfold vcpu.decode_run
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
  refine spec_ite (fun _ => ?_) (fun _ => by errS)
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun off _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun inm _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun outm _ => ?_
  tbS
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  rw [show obj.Tcb.slot (L.curW s) layout.tcb.SLOT_BUFFER = ok (sbWordA (L.curW s)) by
    simp [obj.Tcb.slot, lift, sbWordA], bind_ok]
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st _ s hS) fun c _ => ?_
  cases c
  all_goals try errS
  rename_i ptr fsz rights dev x1 x2 x3 x4
  try dsimp only
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  refine WP.spec_bind (P0.capability.FrameSize.bits.p0 fsz) fun bits _ => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun size1 _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  refine spec_ite (fun _ => by errS) (fun hlt => ?_)
  step as ⟨i8, _⟩
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  try simp only [lift, bind_ok, L.read_eq]
  refine spec_ite (fun _ => by errS) (fun ht0 => ?_)
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  refine spec_ite (fun _ => by errS) (fun _ => ?_)
  have hvT : L.mem s (core.num.U64.wrapping_add vc vcpu.TCB) ∈ T := (vU s c0).2.1.resolve_left ht0
  refine WP.spec_bind (P0.vcpu.num_lrs.p0 ar a hA) fun lrs hl => ?_
  refine WP.spec_bind (hA.vcpu_gic_version a) fun i12 _ => ?_
  tbS
  tbS
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => ?_) (fun _ => by runT)
  refine WP.spec_bind (P0.vcpu.validate_vgic_lrs.p0 st s _ lrs _ hS (by omega)) fun b1 _ => ?_
  refine spec_ite (fun _ => by runT) (fun _ => by errS)

/-- **InvGaps' `vcpu`, every label proved** ([P] `VcpuW`, [P] `VcpuStA`, [P] `VcpuObjA`, `B.DelPlace`'s [P] `vc`,
the heap's notification typing). -/
theorem decGap_vcpuD (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {V : U64 → Prop}
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (W : VcpuW st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pl : VcpuStA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (VO : VcpuObjA st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Pd : W7.R.A5.B.DelPlace st T Cs Ω H Sg Rp Scs Nt Z V P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vcpu :=
  decGap_vcpuC hA E ⟨fun Ac s a vc len call buf extra hE D => vcpu.decode_run.dec hA hNt D (Pd s hE).vc
    (fun Ac' s' f b => VO Ac Ac' s s' vc extra hE D f b) a len call buf⟩ W Pl VO Pd

end

end Fl4ProofsA64.P1

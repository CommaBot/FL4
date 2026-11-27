/-
P3x for virtualization (line virt, gen 16, item 2b): **WriteMSR end to end on the extracted decode** —
`decode_wrmsr_eq` (P3/VirtMsrDec: `vcpu.decode … X86VCPUWriteMSR` = stall, current thread, backend, the two
arguments, `wrmsrTail`) composed with the premise-free tails of P3/VirtReplyKeep across the stall prefix.

* `resched_arch`, `remote_tcb_stall_cap`, **`stall_cap`**: `vcpu.stall` keeps `CapAgree` (under `CapKeepStall`).
* `agreeA_of_writes`: a footprint missing the VCPU object's words keeps its aligned words (`AgreeAtA`).
* **`decode_wrmsr_gen`**: from a `ReplyPl` state where a relation `R` (closed under `AgreeAtA`, kept by an MSR
  store) holds, FL4's whole WriteMSR decode returns; its post names the stall's outcome `(s1, a1)` (a write of at
  most `IPI_PENDING`), the backend word `i`, the two arguments `f`, `value` exactly as the decode reads them, and
  — on the backend `amd = (i = 2)` — gen 15's `TailPost` (`checkMsrWrite` verdict, reply, relation to
  `vs.set k (.msr f) value`, or the related error with the state after the stall).
* **`decode_wrmsr_vmx`** / **`decode_wrmsr_svm`**: the two backends (`VcpuRelVmx` / `VcpuRelSvm`).

Named premises: `CapAgree ar a` [P] (gen 11, at the decode's entry state, unchanged); **`CapKeepStall ar`** [P]
(new): the two arch operations of the stall (`vcpu_barrier`, `remote_stall`) keep `CapAgree`. Justification: the
capability words are read-only VMX capability MSRs of the CPU (`IA32_VMX_*`), which an IPI / ordering barrier does
not change; FL4's `Arch` implementations read them from a boot-time copy. Not false on reachable states.
`P0.ArchTotal ar` (standard totality). State facts (no premise): `ReplyPl` (derived from `JAtZ` + `JVm`,
`JAtZ.replyPl`). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtReplyKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtMsrE2E
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtMsrDec Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtReplyKeep

noncomputable section

section
variable {A : Type} (ar : machine.Arch A)

/-- **`CapKeepStall` [P]** (module docstring): the stall's arch operations keep the capability agreement. -/
def CapKeepStall : Prop :=
  (∀ a, CapAgree ar a → ar.vcpu_barrier a ⦃ a' => CapAgree ar a' ⦄) ∧
    (∀ a c, CapAgree ar a → ar.remote_stall a c ⦃ a' => CapAgree ar a' ⦄)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

theorem resched_arch (s : S) (a : A) (cpu : U64) : smp.remote_reschedule st ar s a cpu ⦃ r => r.2 = a ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold smp.remote_reschedule
  step*
  all_goals first | rfl | simp_all

theorem remote_tcb_stall_cap (hK : CapKeepStall ar) (s : S) {a : A} (h : CapAgree ar a) (t : obj.Tcb) :
    smp.remote_tcb_stall st ar s a t ⦃ r => CapAgree ar r.2 ⦄ := by
  unfold smp.remote_tcb_stall
  refine WP.spec_bind (P1.obj.Tcb.affinity.spec s t) fun cpu _ => ?_
  rw [L.cur_cpu_eq, bind_ok]
  split
  · refine WP.spec_bind (P1.obj.node_get.spec s _ _) fun i1 _ => ?_
    split
    · refine WP.spec_bind (hK.2 a cpu h) fun a1 h1 => ?_
      exact WP.spec_mono (resched_arch s a1 cpu) fun r e => e ▸ h1
    · exact (WP.spec_ok _).2 h
  · exact (WP.spec_ok _).2 h

/-- **The stall keeps `CapAgree`** (premise `CapKeepStall` [P]). -/
theorem stall_cap (hK : CapKeepStall ar) {a : A} (h : CapAgree ar a) (s : S) (v : U64) :
    vcpu.stall st ar s a v ⦃ r => CapAgree ar r.2 ⦄ := by
  unfold vcpu.stall
  refine WP.spec_bind (hK.1 a h) fun a1 h1 => ?_
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun t _ => ?_
  refine WP.spec_bind (P1.obj.Tcb.is_null.spec t) fun b _ => ?_
  split
  · exact (WP.spec_ok _).2 h1
  · exact remote_tcb_stall_cap hK s h1 _

/-- A footprint missing the VCPU object's aligned words keeps them. -/
theorem agreeA_of_writes {v : U64} {s s' : S} (hv : VFits v) {W : U64 → Prop} (h : P1.WritesIn st s s' W)
    (hW : ∀ o : Word, o.toNat < 32768 → ¬ W ⟨v.bv + o⟩) : AgreeAtA (memW st s) (memW st s') v.bv := by
  intro o h1 _
  have ho : o.toNat < 32768 := by
    have : VcpuLay.SIZE.toNat = 32768 := rfl
    rw [BitVec.lt_def, this] at h1; exact h1
  have hal : P1.Aligned (⟨v.bv + o⟩ : U64) := by
    unfold P1.Aligned; rw [vo_val hv ho]; have := hv.1; omega
  unfold memW
  rw [h.2.2 _ hal (hW o ho)]

theorem arg_ok (s : S) (t buf : U64) (c : Prop) [Decidable c] (i : U64) :
    ∃ f, (if c then msg.syscall_arg st s t buf i else ok 0#u64) = ok f := by
  split
  · obtain ⟨f, hf, -⟩ := spec_ex (P0.msg.syscall_arg.p0 st s t buf i L.total); exact ⟨f, hf⟩
  · exact ⟨_, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **WriteMSR end to end, general relation** (module docstring). -/
theorem decode_wrmsr_gen (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) {a : A} (hc : CapAgree ar a) {s : S}
    {v : U64} (P : ReplyPl st v s) (length : U64) (call : Bool) (buf : U64) (ex : Aeneas.Std.Array obj.Slot 3#usize)
    (hlen : ¬ length < 2#u64) (amd : Bool) (R : (Word → Word) → Word → VcpuState → Prop) (k : VirtKind)
    (vs : VcpuState) (hR0 : R (memW st s) v.bv vs)
    (hR : ∀ mem, R mem v.bv vs → ∀ (f value : U64) o, msrOff amd f.bv = some o → ∀ mem',
      WrAt mem mem' v.bv o value.bv → R mem' v.bv (vs.set k (.msr f.bv) value.bv))
    (hRc : ∀ vs' mem mem', AgreeAtA mem mem' v.bv → R mem v.bv vs' → R mem' v.bv vs') :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteMSR length v call buf ex ⦃ r =>
      ∃ s1 a1 i f value, vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ar.virtualization a1 = ok i ∧
        (if length > 0#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 0#u64 else ok 0#u64) = ok f ∧
        (if length > 1#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 1#u64 else ok 0#u64) = ok value ∧
        (decide (i = 2#u64) = amd → TailPost R k st s1 v f value vs r) ⦄ := by
  rw [decode_wrmsr_eq hA s a length v call buf ex hlen]
  obtain ⟨⟨s1, a1⟩, hp, hW, hc1⟩ := spec_ex (spec_and2 (vcpu_stall_w hA s a v P.ipiA_al) (stall_cap hK hc s v))
  rw [hp, bind_tc_ok]
  dsimp only at hW hc1 ⊢
  have P1' : ReplyPl st v s1 := P.of_writes hW fun e => P.ipi_ne_cur e.symm
  obtain ⟨ct, hct, hcte⟩ := spec_ex (P1.sched.cur_thread.spec (L := L) s1)
  have hcte' : ct = L.mem s1 (curA st s1) := hcte
  subst hcte'
  rw [hct]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨i, hi, -⟩ := spec_ex (hA.virtualization a1)
  rw [hi]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨f, hf⟩ := arg_ok (st := st) s1 (L.mem s1 (curA st s1)) buf (length > 0#u64) 0#u64
  rw [hf]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨value, hval⟩ := arg_ok (st := st) s1 (L.mem s1 (curA st s1)) buf (length > 1#u64) 1#u64
  rw [hval]; simp only [bind_ok, bind_tc_ok]
  have hR1 : R (memW st s1) v.bv vs :=
    hRc vs _ _ (agreeA_of_writes P.fit hW fun o ho e => P.vo_ne_node ho (by simp [layout.node.IPI_PENDING]) e)
      hR0
  by_cases hb : decide (i = 2#u64) = amd
  · rw [hb]
    exact WP.spec_mono (wrmsrTail_genA hc1 P1' f value amd call R k vs (hR _ hR1 f value)
      (fun mem mem' h r => hRc _ mem mem' h r)) fun r hr => ⟨s1, a1, i, f, value, rfl, hW, hi, hf, hval, fun _ => hr⟩
  · exact WP.spec_mono (wrmsrTail_genA hc1 P1' f value _ call (fun _ _ _ => True) k vs
      (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)) fun r _ =>
        ⟨s1, a1, i, f, value, rfl, hW, hi, hf, hval, fun h => absurd h hb⟩

/-- **WriteMSR end to end, VMX** (premises `CapAgree` [P], `CapKeepStall` [P]; state fact `ReplyPl`). -/
theorem decode_wrmsr_vmx (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) {a : A} (hc : CapAgree ar a) {s : S}
    {v : U64} (P : ReplyPl st v s) (length : U64) (call : Bool) (buf : U64) (ex : Aeneas.Std.Array obj.Slot 3#usize)
    (hlen : ¬ length < 2#u64) {vs : VcpuState} (h : VcpuRelVmx (memW st s) v.bv vs) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteMSR length v call buf ex ⦃ r =>
      ∃ s1 a1 i f value, vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ar.virtualization a1 = ok i ∧
        (if length > 0#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 0#u64 else ok 0#u64) = ok f ∧
        (if length > 1#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 1#u64 else ok 0#u64) = ok value ∧
        (decide (i = 2#u64) = false → TailPost VcpuRelVmx .vmx st s1 v f value vs r) ⦄ :=
  decode_wrmsr_gen hA hK hc P length call buf ex hlen false VcpuRelVmx .vmx vs h
    (fun _ h' _ _ _ ho _ hw => msrStore_vmx h' ho hw) (fun _ _ _ hag h' => VcpuRelVmx.congrA hag h')

/-- **WriteMSR end to end, SVM** (premises `CapAgree` [P], `CapKeepStall` [P]; state fact `ReplyPl`). -/
theorem decode_wrmsr_svm (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) {a : A} (hc : CapAgree ar a) {s : S}
    {v : U64} (P : ReplyPl st v s) (length : U64) (call : Bool) (buf : U64) (ex : Aeneas.Std.Array obj.Slot 3#usize)
    (hlen : ¬ length < 2#u64) {vs : VcpuState} (h : VcpuRelSvm (memW st s) v.bv vs) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteMSR length v call buf ex ⦃ r =>
      ∃ s1 a1 i f value, vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ar.virtualization a1 = ok i ∧
        (if length > 0#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 0#u64 else ok 0#u64) = ok f ∧
        (if length > 1#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 1#u64 else ok 0#u64) = ok value ∧
        (decide (i = 2#u64) = true → TailPost VcpuRelSvm .svm st s1 v f value vs r) ⦄ :=
  decode_wrmsr_gen hA hK hc P length call buf ex hlen true VcpuRelSvm .svm vs h
    (fun _ h' _ _ _ ho _ hw => msrStore_svm h' ho hw) (fun _ _ _ hag h' => VcpuRelSvm.congrA hag h')

end

end
end Fl4Proofs.P3.VirtMsrE2E

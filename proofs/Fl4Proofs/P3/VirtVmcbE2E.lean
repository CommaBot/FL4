/-
P3x for virtualization (line virt, gen 17, item 1): **WriteVMCB end to end on the extracted decode** — FL4's `old`
word (`oldF`, P3/VirtVmcbTail) identified with the spec's `old` (`decodeVcpuInvocation`'s WriteVMCB arm), then
gen 16's `decode_wrvmcb_eq` (P3/VirtVmcbDec) composed with `wrvmcbTail_svm` (P3/VirtVmcbTail) across the stall
prefix, as `decode_wrmsr_gen` (P3/VirtMsrE2E) does for WriteMSR.

* `specOld vs f`: the spec's `old` (`if f < svmEnd ∧ f &&& 7 = 0 then vs.get virtKind (.vmcb f) else 0`, on SVM).
* `sanitizeVmcb_congr`: `sanitizeVmcb` reads `old` only outside the rule's mask. `writeRule_rax` (RAX's rule has the
  full mask), `writable_readable` (every writable word is readable and not `hiddenRead`, by FL4's 50 arms).
* **`sanitize_old_eq`**: from `VcpuRelSvm (memW st s) v vs`, `sanitizeVmcb f (oldF …) value` =
  `sanitizeVmcb f (specOld vs f) value` for every `f` (no condition): off the table both reject; off RAX the
  relation's `vmcb` clause gives the word; at RAX the full mask makes `old` irrelevant (FL4 reads the VMCB copy,
  the spec GPR 0, and they may differ inside the kernel — the result does not).
* `VmcbPost.congr_old`: the post only reads `old` through `sanitizeVmcb`.
* **`decode_wrvmcb_gen`**: from a `ReplyPl` state with the VCPU related on SVM, FL4's whole WriteVMCB decode returns;
  its post names the stall's outcome `(s1, a1)` (a write of at most `IPI_PENDING`), the backend word `i`, the two
  arguments `f`, `value` exactly as decoded, and on SVM (`i = 2`) `VmcbPost` against the **spec's** `old`
  (`specOld vs f`): verdict = the spec's `sanitizeVmcb`, on `ok val` the VCPU relates to `vs.set .svm (.vmcb f) val`,
  on `error e'` the related error with the state after the stall; on VMX (`i ≠ 2`) the state after the stall.

Named premises: `CapAgree ar a` [P] (gen 11, unchanged), `CapKeepStall ar` [P] (gen 16, unchanged);
`P0.ArchTotal ar` (standard totality). State fact (no premise): `ReplyPl`. New file only; no existing statement
changed.
-/
import Fl4Proofs.P3.VirtVmcbTail
import Fl4Proofs.P3.VirtMsrE2E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVmcbE2E
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanSvm
open Fl4Proofs.P3.VirtVcpuRel Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtVmcbStore Fl4Proofs.P3.VirtReplyKeep Fl4Proofs.P3.VirtVmcbDec
open Fl4Proofs.P3.VirtVmcbTail Fl4Proofs.P3.VirtMsrE2E

noncomputable section

/-- The spec's `old` word of WriteVMCB on SVM (`decodeVcpuInvocation`, module docstring). -/
def specOld (vs : VcpuState) (f : Word) : Word :=
  if f < Svm.svmEnd ∧ f &&& 7 = 0 then vs.get .svm (.vmcb f) else 0

theorem sanitizeVmcb_congr {f o1 o2 x : Word}
    (h : ∀ r, Svm.writeRule f = some r → o1 &&& ~~~r.mask = o2 &&& ~~~r.mask) :
    sanitizeVmcb f o1 x = sanitizeVmcb f o2 x := by
  unfold sanitizeVmcb
  rcases hw : Svm.writeRule f with _ | r
  · rfl
  · simp only [h r hw]

theorem writeRule_rax : Svm.writeRule Svm.rax = some ⟨~~~0, 0, false⟩ := by
  unfold Svm.writeRule
  rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_pos] <;>
    decide

theorem writable_readable {f : Word} (hf : Svm.writable f = true) :
    Svm.readable f = true ∧ Svm.hiddenRead f = false := by
  have hm := writeRule_mem hf
  simp only [svmTab, List.mem_cons, List.not_mem_nil, or_false] at hm
  repeat (rcases hm with rfl | hm; · exact ⟨by decide, by decide⟩)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

theorem and7_of {f : U64} (h : f.bv.toNat % 8 = 0) : f &&& 7#u64 = 0#u64 := by
  have e : (f &&& 7#u64).val = f.val % 8 := by simp; exact Nat.and_two_pow_sub_one_eq_mod f.val 3
  apply UScalar.eq_of_val_eq
  rw [e]; exact h

theorem oldF_writable (s : S) (v f : U64) (hf : Svm.writable f.bv = true) :
    oldF st s v f = L.mem s (core.num.U64.wrapping_add v f) := by
  obtain ⟨fa, fl⟩ := svm_writable_nat hf
  have h1 : f < 1768#u64 := by
    rw [UScalar.lt_equiv]; show f.bv.toNat < 1768; exact fl
  unfold oldF
  rw [if_pos h1, if_pos (and7_of fa)]

/-- **FL4's `old` and the spec's `old` give the same `sanitizeVmcb` verdict** (module docstring). -/
theorem sanitize_old_eq {s : S} {v : U64} {vs : VcpuState} (h : VcpuRelSvm (memW st s) v.bv vs) (f value : U64) :
    sanitizeVmcb f.bv (oldF st s v f).bv value.bv = sanitizeVmcb f.bv (specOld vs f.bv) value.bv := by
  by_cases hw : Svm.writable f.bv = true
  · obtain ⟨hr, hh⟩ := writable_readable hw
    have hc : f.bv < Svm.svmEnd ∧ f.bv &&& 7 = 0 := by
      simp only [Svm.readable, Bool.and_eq_true, decide_eq_true_eq] at hr
      exact ⟨hr.2, hr.1⟩
    unfold specOld
    rw [if_pos hc, oldF_writable s v f hw]
    by_cases hx : f.bv = Svm.rax
    · refine sanitizeVmcb_congr fun r e => ?_
      rw [hx, writeRule_rax] at e
      cases e
      simp
    · have e1 : (L.mem s (core.num.U64.wrapping_add v f)).bv = memW st s (v.bv + f.bv) := by
        unfold memW
        congr 2
      have hc' : VField.canon .svm (.vmcb f.bv) = .vmcb f.bv := by simp [VField.canon, hx]
      rw [e1, ← h.vmcb _ hr hh hx]
      unfold VcpuState.get
      rw [hc']
  · refine sanitizeVmcb_congr fun r e => ?_
    exact absurd (by unfold Svm.writable; rw [e]; rfl) hw

theorem VmcbPost.congr_old {s1 : S} {v f value o1 o2 : U64} {vs : VcpuState}
    {r : (core.result.Result Unit error.Exc) × S × A}
    (e : sanitizeVmcb f.bv o1.bv value.bv = sanitizeVmcb f.bv o2.bv value.bv)
    (h : VmcbPost st s1 v f value o1 vs r) : VmcbPost st s1 v f value o2 vs r := by
  unfold VmcbPost at h ⊢
  rw [← e]; exact h

theorem illegal_ok : ∃ e, error.illegal Unit = ok e := by
  unfold error.illegal; exact ⟨_, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **WriteVMCB end to end** (module docstring; premises `CapAgree` [P], `CapKeepStall` [P]; state fact
`ReplyPl`). -/
theorem decode_wrvmcb_gen (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) {a : A} (hc : CapAgree ar a) {s : S}
    {v : U64} (P : ReplyPl st v s) (length : U64) (call : Bool) (buf : U64) (ex : Aeneas.Std.Array obj.Slot 3#usize)
    (hlen : ¬ length < 2#u64) {vs : VcpuState} (h : VcpuRelSvm (memW st s) v.bv vs) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteVMCB length v call buf ex ⦃ r =>
      ∃ s1 a1 i f value, vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ar.virtualization a1 = ok i ∧
        (if length > 0#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 0#u64 else ok 0#u64) = ok f ∧
        (if length > 1#u64 then msg.syscall_arg st s1 (L.mem s1 (curA st s1)) buf 1#u64 else ok 0#u64) = ok value ∧
        (i = 2#u64 → VmcbPost st s1 v f value ⟨specOld vs f.bv⟩ vs r) ∧
        (i ≠ 2#u64 → r.2.1 = s1) ⦄ := by
  rw [decode_wrvmcb_eq s a length v call buf ex hlen]
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
  have h1 : VcpuRelSvm (memW st s1) v.bv vs :=
    VcpuRelSvm.congrA (agreeA_of_writes P.fit hW fun o ho e => P.vo_ne_node ho (by simp [layout.node.IPI_PENDING]) e)
      h
  by_cases hb : i = 2#u64
  · rw [if_pos hb]
    exact WP.spec_mono (wrvmcbTail_svm hc1 P1' f value call h1) fun r hr =>
      ⟨s1, a1, i, f, value, rfl, hW, hi, hf, hval,
        fun _ => VmcbPost.congr_old (o2 := ⟨specOld vs f.bv⟩) (sanitize_old_eq h1 f value) hr,
        fun hn => absurd hb hn⟩
  · rw [if_neg hb]
    obtain ⟨e, he⟩ := illegal_ok
    rw [he, bind_ok]
    exact (WP.spec_ok _).2 ⟨s1, a1, i, f, value, rfl, hW, hi, hf, hval, fun h2 => absurd h2 hb, fun _ => rfl⟩

end

end
end Fl4Proofs.P3.VirtVmcbE2E

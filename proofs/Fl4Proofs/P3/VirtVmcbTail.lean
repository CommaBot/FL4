/-
P3x for virtualization (line virt, gen 16, item 4b): **WriteVMCB's tail on the extracted decode** — `wrvmcbTail`
(P3/VirtVmcbDec, the arm `decode_wrvmcb_eq` exposes) from a related SVM VCPU: gen 12's verdict
(`sanitize_vmcb_rel`, P3/VirtSanSvm), gen 15's store sequence (`vmcbStore_svm`, P3/VirtVmcbStore) and this gen's
premise-free reply frame (`reply_keepsA`, P3/VirtReplyKeep) composed.

* `oldF st s v f`: the word FL4 reads as `old` (`v + f` when `f < svm::END` and `f & 7 = 0`, else 0); `old_eq`.
* `VmcbPost`: on `sanitizeVmcb f old value = ok val` FL4 answers `Ok` and the VCPU relates to
  `vs.set .svm (.vmcb f) val`; on `error e'` FL4 answers the related error with the state unchanged.
* **`wrvmcbTail_svm`**: `CapAgree` [P], `ReplyPl st v s1` (state fact), `VcpuRelSvm (memW st s1) v vs` ⇒ `VmcbPost`.

Not here: identifying FL4's `oldF` with the spec's `old` (`st.get virtKind (.vmcb f)` when `f < svmEnd`, aligned):
off RAX the relation's `vmcb` clause gives it for readable, unhidden words; RAX's rule has the full mask, so the
result is independent of `old` there. Named premise: `CapAgree ar a` [P] (unchanged). New file only.
-/
import Fl4Proofs.P3.VirtVmcbDec
import Fl4Proofs.P3.VirtVmcbStore
import Fl4Proofs.P3.VirtReplyKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVmcbTail
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanSvm
open Fl4Proofs.P3.VirtVcpuRel Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtVmcbStore Fl4Proofs.P3.VirtReplyKeep Fl4Proofs.P3.VirtVmcbDec

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- The word FL4's WriteVMCB reads as `old` (module docstring). -/
def oldF (st : machine.Store S) [L : P1.LawfulStore st] (s : S) (v f : U64) : U64 :=
  if f < 1768#u64 then (if f &&& 7#u64 = 0#u64 then L.mem s (core.num.U64.wrapping_add v f) else 0#u64) else 0#u64

theorem old_eq (s : S) (v f : U64) :
    (if f < 1768#u64 then
      (do
        let i2 ← lift (f &&& 7#u64)
        if i2 = 0#u64 then vcpu.get st s v f else ok 0#u64)
    else ok 0#u64) = ok (oldF st s v f) := by
  unfold oldF vcpu.get
  by_cases h1 : f < 1768#u64
  · by_cases h2 : f &&& 7#u64 = 0#u64
    · simp [h1, h2, lift, L.read_eq]
    · simp [h1, h2, lift]
  · simp [h1]

/-- The post of WriteVMCB's tail against `sanitizeVmcb` (module docstring). -/
def VmcbPost (st : machine.Store S) [L : P1.LawfulStore st] (s1 : S) (v f value old : U64) (vs : VcpuState)
    (r : (core.result.Result Unit error.Exc) × S × A) : Prop :=
  (∃ val, sanitizeVmcb f.bv old.bv value.bv = .ok val ∧ r.1 = .Ok () ∧
      VcpuRelSvm (memW st r.2.1) v.bv (vs.set .svm (.vmcb f.bv) val)) ∨
    (∃ e e', sanitizeVmcb f.bv old.bv value.bv = .error e' ∧ SysErrRel e e' ∧ r.1 = .Err e ∧ r.2.1 = s1)

theorem writable_of_ok {f old value val : Word} (h : sanitizeVmcb f old value = .ok val) :
    Svm.writable f = true := by
  unfold sanitizeVmcb at h
  unfold Svm.writable
  rcases hw : Svm.writeRule f with _ | r
  · rw [hw] at h; cases h
  · rfl

theorem RAX_eq : vcpu.svm.RAX = ok 1528#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.RAX.spec

theorem regs_bv : (vcpu.REGS).bv = VcpuLay.REGS := by unfold vcpu.REGS VcpuLay.REGS; decide
theorem svmcpu_nat : (vcpu.SVM_CPU).bv.toNat = 20536 := by unfold vcpu.SVM_CPU; decide

set_option maxHeartbeats 4000000 in
/-- **WriteVMCB's tail on SVM** (module docstring; premise `CapAgree` [P]; state fact `ReplyPl`). -/
theorem wrvmcbTail_svm {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (P : ReplyPl st v s1) (f value : U64)
    (call : Bool) {vs : VcpuState} (h : VcpuRelSvm (memW st s1) v.bv vs) :
    wrvmcbTail st ar s1 a1 v f value call ⦃ r => VmcbPost st s1 v f value (oldF st s1 v f) vs r ⦄ := by
  unfold wrvmcbTail
  rw [END_eq, bind_ok, old_eq, bind_ok]
  obtain ⟨r, hr, hrel⟩ := sanitize_vmcb_rel hc f (oldF st s1 v f) value
  rw [hr, bind_ok]
  cases r with
  | Err e =>
    rcases hs : sanitizeVmcb f.bv (oldF st s1 v f).bv value.bv with e' | val'
    · rw [hs] at hrel
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      exact Or.inr ⟨e, e', hs, hrel, rfl, rfl⟩
    · rw [hs] at hrel; exact hrel.elim
  | Ok val =>
    rcases hs : sanitizeVmcb f.bv (oldF st s1 v f).bv value.bv with e' | val'
    · rw [hs] at hrel; exact hrel.elim
    have hvv : val.bv = val' := by rw [hs] at hrel; exact hrel
    have hwf := writable_of_ok hs
    obtain ⟨fa, fl⟩ := svm_writable_nat hwf
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    -- the word
    refine WP.spec_bind (vset_eq s1 v f val) fun s2 e2 => ?_
    subst e2
    have hx1 : (core.num.U64.wrapping_add v f).bv = v.bv + f.bv := wadd_bv v f
    have w1 := memW_wr (st := st) P.fit (o := f.bv) (by omega) fa hx1 s1 val
    have P2 := P.wr (o := f.bv) (by omega) fa _ hx1 val
    -- `SVM_CPU := 0` for the paging words
    refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun b _ => ?_
    have hx2 : (core.num.U64.wrapping_add v vcpu.SVM_CPU).bv = v.bv + (vcpu.SVM_CPU).bv := wadd_bv v _
    have hs2 : (vcpu.SVM_CPU).bv.toNat < 32768 := by rw [svmcpu_nat]; omega
    have ha2 : (vcpu.SVM_CPU).bv.toNat % 8 = 0 := by rw [svmcpu_nat]
    refine WP.spec_bind (Pₘ := fun s3 => ReplyPl st v s3 ∧
        (memW st s3 = memW st (L.wr s1 (core.num.U64.wrapping_add v f) val) ∨
          ∃ o : Word, o.toNat = 20536 ∧ WrAt (memW st (L.wr s1 (core.num.U64.wrapping_add v f) val)) (memW st s3)
            v.bv o (0#u64).bv)) ?_ fun s3 h3 => ?_
    · split
      · exact WP.spec_mono (vset_eq _ v vcpu.SVM_CPU 0#u64) fun s3 e3 => by
          subst e3
          exact ⟨P2.wr hs2 ha2 _ hx2 _, Or.inr ⟨_, svmcpu_nat, memW_wr (st := st) P.fit hs2 ha2 hx2 _ _⟩⟩
      · exact (WP.spec_ok _).2 ⟨P2, Or.inl rfl⟩
    -- RAX's `REGS` copy
    rw [RAX_eq, bind_ok]
    have hx3 : (core.num.U64.wrapping_add v vcpu.REGS).bv = v.bv + VcpuLay.REGS := by rw [wadd_bv, regs_bv]
    have hs3 : VcpuLay.REGS.toNat < 32768 := by decide
    have ha3 : VcpuLay.REGS.toNat % 8 = 0 := by decide
    have hraxf : f = 1528#u64 ↔ f.bv = Svm.rax := by
      constructor
      · rintro rfl; decide
      · intro e; apply UScalar.eq_of_val_eq
        have := congrArg BitVec.toNat e
        rw [rax_nat] at this; exact this
    refine WP.spec_bind (Pₘ := fun s4 => ReplyPl st v s4 ∧
        (f.bv = Svm.rax → WrAt (memW st s3) (memW st s4) v.bv VcpuLay.REGS val.bv) ∧
        (f.bv ≠ Svm.rax → memW st s4 = memW st s3)) ?_ fun s4 h4 => ?_
    · split
      · rename_i hf
        exact WP.spec_mono (vset_eq _ v vcpu.REGS val) fun s4 e4 => by
          subst e4
          exact ⟨h3.1.wr hs3 ha3 _ hx3 _, fun _ => memW_wr (st := st) P.fit hs3 ha3 hx3 _ _,
            fun hn => absurd (hraxf.1 hf) hn⟩
      · rename_i hf
        exact (WP.spec_ok _).2 ⟨h3.1, fun e => absurd (hraxf.2 e) hf, fun _ => rfl⟩
    -- the reply
    refine WP.spec_bind (reply_keepsA h4.1 call val) fun s5 hag => (WP.spec_ok _).2 (Or.inl ⟨val', hs, rfl, ?_⟩)
    rw [← hvv]
    refine VcpuRelSvm.congrA hag (vmcbStore_svm h hwf w1 ?_ ⟨h4.2.1, h4.2.2⟩)
    rcases h3.2 with e | ⟨o, ho, hw⟩
    · exact Or.inl e
    · exact Or.inr ⟨o, ho, hw⟩

end

end
end Fl4Proofs.P3.VirtVmcbTail

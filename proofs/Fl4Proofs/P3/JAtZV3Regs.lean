/-
P3 (line mmuAD, gen 32): **X86VCPUWriteRegisters end to end at `JAtZV3`** — the extracted `vcpu.decode` at label
`X86VCPUWriteRegisters` (vcpu.rs l. 861-877: `stall`, `cur_thread`, `virtualization`, `syscall_arg` 0/1, the label
and length checks, the Aeneas loop `decode_loop0` storing `syscall_arg(i)` at `REGS + 8 i` for `i < 15`, on SVM the
copy of `REGS` into the VMCB RAX word, then the caller's `TS_RESTART`), paired with the extended spec's
`decodeVcpuInvocation` (`.writeRegisters v (fun i => args[i])`) and `performVcpuInvocation (.writeRegisters v vals)`
(`vcpuUpdate v (setGprs vals)`, reply `[]`).

* **`gprPre vals vs k`**: the spec VCPU after FL4's first `k` loop rounds (`vsSetGpr` of GPRs `0..k-1`);
  **`gprPre_15`** = `vs.setGprs vals` (gen 31's `vsSetGpr_fold`).
* **`RBKeep ct buf s0 s1`**: the current thread's register words and the IPC-buffer words of MRs 0..14 are those of
  `s0` — so `msg.syscall_arg` reads the same values (P3's `syscall_arg_keep`); **`RBKeep.wr`**: kept across a store
  inside a VCPU of `V` (the TCB is apart from every VCPU by the layout `vap`; the buffer words by `BufOut`).
* **`JAtZV3.wrLoop`**: the extracted `decode_loop0` from round `k` at a `JAtZV3` state paired with `gprPre k`
  ends at a `JAtZV3` state paired with `vs.setGprs vals` (gen 31's `JAtZV3.gprWr` per round), `RBKeep` kept.
* Spec side: **`zv_label_wregs`**, **`zv_decode_wregs`**, **`zv_perform_wregs`**.
* **`JAtZV3.writeRegsJ`**: `vcpu.decode … X86VCPUWriteRegisters len p call buf ex` at a `JAtZV3` state, `p ∈ V` a spec
  VCPU, `len ≥ 15`: the post names `ct` and the 15 words `vals` FL4 read (`syscall_arg ct buf i` at the entry state);
  FL4 returns `Ok ()`; for every spec argument list agreeing with them the spec decoder returns
  `.writeRegisters p (vals)`; `performVcpuInvocation` has exactly one outcome `([], σ')`, `JAtZV3` holds at FL4's
  state just before the caller's `set_thread_state ct TS_RESTART` and `σ'`, and FL4's final state is that call's
  result (l4v `handle_invocation`'s restart tail on `[]`, left to the caller). Both backends: the SVM RAX copy is
  gen 31's `JAtZV3.raxWr` (the relation does not read the VMCB RAX word), so no platform premise is needed.

Scope hypothesis (not a premise about the world): **`BufOut V buf`** — when `buf ≠ 0`, the IPC-buffer words of MRs
4..14 (`fl4BufA buf (i + 1)`) are aligned and outside every VCPU of `V` (the caller's buffer is a user frame: seL4's
IPC buffer is 512-byte aligned in a frame cap's page, VCPUs are kernel objects; the caller gets it from
`lookup_ipc_buffer`). ARKeep (`stall`) and `P0.ArchTotal arI` (`virtualization` returns) as elsewhere.
No named premise; no existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3Vmcs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## The spec VCPU after `k` rounds -/

section
open Fl4Spec

/-- The spec VCPU after FL4's first `k` rounds (module docstring). -/
def gprPre (vals : Fin 15 → Word) (vs : VcpuState) : Nat → VcpuState
  | 0 => vs
  | n + 1 => if h : n < 15 then vsSetGpr ⟨n, h⟩ (vals ⟨n, h⟩) (gprPre vals vs n) else gprPre vals vs n

theorem gprPre_succ (vals : Fin 15 → Word) (vs : VcpuState) {n : Nat} (h : n < 15) :
    gprPre vals vs (n + 1) = vsSetGpr ⟨n, h⟩ (vals ⟨n, h⟩) (gprPre vals vs n) := by
  simp only [gprPre, dif_pos h]

theorem gprPre_15 (vals : Fin 15 → Word) (vs : VcpuState) : gprPre vals vs 15 = vs.setGprs vals := by
  rw [← vsSetGpr_fold]
  rfl

theorem zv_updK_updK (σ : State Unit) (p : ObjRef) (o o' : KernelObject) :
    Notif.updK (Notif.updK σ p o) p o' = Notif.updK σ p o' := by
  unfold Notif.updK
  simp only [Function.update_idem]

theorem zv_updK_self {σ : State Unit} {p : ObjRef} {o : KernelObject} (h : σ.kheap p = some o) :
    Notif.updK σ p o = σ := by
  unfold Notif.updK
  rw [← h, Function.update_eq_self]

theorem zv_label_wregs : vcpuLabelOf (81 : Data) = some .writeRegisters := by decide

theorem zv_decode_wregs {args : List Data} {v : ObjRef} {ec : List (Cap × CslotPtr)} (hl : 15 ≤ args.length) :
    decodeVcpuInvocation (Z := Unit) 81 args v ec =
      NonDetE.returnOk (.writeRegisters v fun i => args.getD i.val 0) := by
  have hn : ¬ args.length < 15 := by omega
  simp only [decodeVcpuInvocation, zv_label_wregs, hn, ↓reduceIte] <;> rfl

theorem zv_perform_wregs {σ : State Unit} {v : ObjRef} {vs : VcpuState}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (vals : Fin 15 → Word) :
    performVcpuInvocation (Z := Unit) (.writeRegisters v vals) σ =
      ({([], Notif.updK σ v (.archObj (.vcpu (vs.setGprs vals))))}, False) := by
  show ((vcpuUpdate (Z := Unit) v (VcpuState.setGprs vals)) >>= fun _ =>
    (pure [] : SMonad Unit (List Data))) σ = _
  rw [Notif.nd_bind_one (zv_vcpuUpdate_eq hk _)]
  rfl

end

/-! ## The argument words -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **Scope**: the IPC-buffer words of MRs 0..14 are aligned and outside every VCPU of `V` (module docstring). -/
def BufOut (V : Set U64) (buf : U64) : Prop :=
  buf ≠ 0#u64 → ∀ j : U64, j.val < 15 →
    P1.Aligned (Endp.fl4BufA buf (core.num.U64.wrapping_add j 1#u64)) ∧
    ∀ u ∈ V, (Endp.fl4BufA buf (core.num.U64.wrapping_add j 1#u64)).val < u.val ∨
      u.val + 32768 ≤ (Endp.fl4BufA buf (core.num.U64.wrapping_add j 1#u64)).val

/-- The words `syscall_arg ct buf i` (`i < 15`) reads are those of `s0` (module docstring). -/
def RBKeep (ct buf : U64) (s0 s1 : S) : Prop :=
  (∀ g : Fl4Spec.Register, L.mem s1 (Endp.regA ct (Endp.regIdx g)) = L.mem s0 (Endp.regA ct (Endp.regIdx g))) ∧
  (buf ≠ 0#u64 → ∀ j : U64, j.val < 15 → L.mem s1 (Endp.fl4BufA buf (core.num.U64.wrapping_add j 1#u64)) =
    L.mem s0 (Endp.fl4BufA buf (core.num.U64.wrapping_add j 1#u64)))

theorem RBKeep.refl (ct buf : U64) (s0 : S) : RBKeep (L := L) ct buf s0 s0 := ⟨fun _ => rfl, fun _ _ _ => rfl⟩

/-- **`RBKeep` across a store inside a VCPU of `V`** (module docstring). -/
theorem RBKeep.wr {ct buf : U64} {s0 s1 : S} (h : RBKeep (L := L) ct buf s0 s1) {th : TypedHeap} {U : Set U64}
    (Ly : JVLay V th U) (hct : P1.TcbAddr ct) (hth : th ct = some .tcb) (hb : BufOut V buf) {p w : U64}
    (hp : p ∈ V) (hal : P1.Aligned w) (g1 : p.val ≤ w.val) (g2 : w.val < p.val + 32768) (x : U64) :
    RBKeep (L := L) ct buf s0 (L.wr s1 w x) := by
  have hd := Ly.vap p hp ct .tcb hth
  rw [show objSize ObjKind.tcb = 4096 from rfl] at hd
  refine ⟨fun g => ?_, fun h0 j hj => ?_⟩
  · have hi := Endp.regIdx_lt g
    obtain ⟨ha, -⟩ := Endp.regA_tf hct hi
    have hv := Endp.regA_val hct hi
    rw [L.mem_wr_ne hal ha (by rw [hv]; omega)]
    exact h.1 g
  · obtain ⟨ha, hout⟩ := hb h0 j hj
    have ho := hout p hp
    rw [L.mem_wr_ne hal ha (by omega)]
    exact h.2 h0 j hj

theorem RBKeep.arg {ct buf : U64} {s0 s1 : S} (h : RBKeep (L := L) ct buf s0 s1) (i : U64) (hi : i.val < 15) :
    msg.syscall_arg st s1 ct buf i = msg.syscall_arg st s0 ct buf i :=
  syscall_arg_keep h.1 fun h0 => h.2 h0 i hi

/-! ## The loop -/

theorem zv_u64_ofNat {k : U64} (h : k.val < 15) : (⟨BitVec.ofNat 64 k.val⟩ : U64) = k :=
  UScalar.eq_of_val_eq (by
    show (BitVec.ofNat 64 k.val).toNat = k.val
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))

set_option maxHeartbeats 8000000 in
/-- **FL4's WriteRegisters loop at `JAtZV3`, paired with the spec's GPR updates** (module docstring). -/
theorem JAtZV3.wrLoop {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {ct buf : U64} (hct : P1.TcbAddr ct)
    (hth : Z.th ct = some .tcb) (hb : BufOut V buf) (s0 : S) (vals : Fin 15 → U64)
    (hvals : ∀ i : Fin 15, msg.syscall_arg st s0 ct buf ⟨BitVec.ofNat 64 i.val⟩ = ok (vals i))
    (k : U64) (hk15 : k.val ≤ 15) (s1 : S)
    (J1 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a
      (Notif.updK σ p.bv (.archObj (.vcpu (gprPre (fun i => (vals i).bv) vs k.val)))))
    (hK1 : RBKeep (L := L) ct buf s0 s1) :
    vcpu.decode_loop0 st s1 p buf ct k ⦃ s2 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s2 a
      (Notif.updK σ p.bv (.archObj (.vcpu (vs.setGprs fun i => (vals i).bv)))) ∧ RBKeep (L := L) ct buf s0 s2 ⦄ := by
  unfold vcpu.decode_loop0
  apply loop.spec_decr_nat (measure := fun y : S × U64 => 15 - y.2.val)
    (inv := fun y => y.2.val ≤ 15 ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D y.1 a
      (Notif.updK σ p.bv (.archObj (.vcpu (gprPre (fun i => (vals i).bv) vs y.2.val)))) ∧
      RBKeep (L := L) ct buf s0 y.1)
  · rintro ⟨s2, j⟩ ⟨hj, J2, K2⟩
    try simp only at hj J2 K2
    unfold vcpu.decode_loop0.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < 15 := by scalar_tac
      have hrd : msg.syscall_arg st s2 ct buf j = ok (vals ⟨j.val, hlt'⟩) := by
        rw [K2.arg j hlt']
        have := hvals ⟨j.val, hlt'⟩
        rwa [zv_u64_ofNat hlt'] at this
      rw [hrd, bind_ok]
      step as ⟨i1, hi1⟩
      simp only [vcpu.REGS]
      step as ⟨i2, hi2⟩
      simp only [vcpu.set, lift, bind_ok]
      refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s3 e3 => ?_
      subst e3
      step as ⟨j1, hj1⟩
      have Ly := J2.z2.zv.base.jvLay J2.z2.zv.vm
      have hf := Ly.vfit p hp
      have hwv : (core.num.U64.wrapping_add p i2).val = p.val + 20736 + 8 * j.val := by
        have h2 := hf.2
        have hs : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
        have : i2.val = 20736 + j.val * 8 := by
          first | omega | (simp at hi2; omega) | (simp at hi1; omega) | (simp at hi2 hi1; omega)
        rw [core.num.U64.wrapping_add_val_eq, hs, this, Nat.mod_eq_of_lt (by omega)]; omega
      have hal : P1.Aligned (core.num.U64.wrapping_add p i2) := by
        show (core.num.U64.wrapping_add p i2).val % 8 = 0
        have : p.val % 32768 = 0 := hf.1
        rw [hwv]; omega
      have hk2 : (Notif.updK σ p.bv (.archObj (.vcpu (gprPre (fun i => (vals i).bv) vs j.val)))).kheap p.bv =
          some (.archObj (.vcpu (gprPre (fun i => (vals i).bv) vs j.val))) := by simp [Notif.updK]
      have J3 := J2.gprWr hp ⟨j.val, hlt'⟩ hwv (vals ⟨j.val, hlt'⟩) hk2
      rw [zv_updK_updK, ← gprPre_succ (fun i => (vals i).bv) vs hlt'] at J3
      have hj1' : j1.val = j.val + 1 := by first | omega | (simp at hj1; omega)
      try dsimp only
      refine ⟨by omega, ?_, K2.wr Ly hct hth hb hp hal (by rw [hwv]; omega)
        (by rw [hwv]; omega) _, by omega⟩
      rw [hj1']; exact J3
    · rename_i hge
      have h15 : j.val = 15 := by
        have : ¬ j.val < 15 := by intro h; apply hge; scalar_tac
        omega
      rw [h15, gprPre_15] at J2
      exact (WP.spec_ok _).2 ⟨J2, K2⟩
  · exact ⟨hk15, J1, hK1⟩

/-! ## The invocation -/

theorem zv_wregs_bv : fl4_abi.label.X86VCPUWriteRegisters.bv = (81 : Fl4Spec.Data) := by
  unfold fl4_abi.label.X86VCPUWriteRegisters; rfl

theorem zv_RAX_eq : vcpu.svm.RAX = ok 1528#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.RAX.spec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUWriteRegisters at `JAtZV3`, paired with the spec's decode and perform** (module docstring). -/
theorem JAtZV3.writeRegsJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hAT : P0.ArchTotal arI) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 15 ≤ len.val) (call : Bool) {buf : U64}
    (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteRegisters len p call buf ex ⦃ r =>
      ∃ (ct : U64) (vals : Fin 15 → U64), sched.cur_thread st s = ok ct ∧
      (∀ i : Fin 15, msg.syscall_arg st s ct buf ⟨BitVec.ofNat 64 i.val⟩ = ok (vals i)) ∧ r.1 = .Ok () ∧
      (∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), args.length = len.val →
        (∀ i : Fin 15, args.getD i.val 0 = (vals i).bv) →
        Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUWriteRegisters.bv args p.bv ec =
          Fl4Spec.NonDetE.returnOk (.writeRegisters p.bv fun i => (vals i).bv)) ∧
      ∃ (s3 : S) (σ' : Fl4Spec.State Unit),
        Fl4Spec.performVcpuInvocation (Z := Unit) (.writeRegisters p.bv fun i => (vals i).bv) σ =
          ({([], σ')}, False) ∧
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s3 r.2.2 σ' ∧
        sched.set_thread_state st s3 ct sched.TS_RESTART = ok r.2.1 ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, ect⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  have hctT : ct ∈ Z.T := by rw [ect, hc.cur]; exact hc.curT
  have hctA : P1.TcbAddr ct := hc.tcbs ct hctT
  have hcth : Z.th ct = some .tcb := B.thTcb hctT
  rw [hct, bind_ok]
  obtain ⟨i, hi, -⟩ := P1.spec_ex_fd (hAT.virtualization_spec a1)
  rw [hi, bind_ok]
  have g0 : len > 0#u64 := by scalar_tac
  have g1 : len > 1#u64 := by scalar_tac
  have g2 : ¬ len < 15#u64 := by scalar_tac
  obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
  obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
  rw [if_pos g0, hf, bind_ok, if_pos g1, hx, bind_ok]
  have n73 : ¬ fl4_abi.label.X86VCPUWriteRegisters = fl4_abi.label.X86VCPUSetTCB :=
    zv_lbl_ne (by simp [fl4_abi.label.X86VCPUWriteRegisters, fl4_abi.label.X86VCPUSetTCB])
  rw [if_neg n73]
  simp only [eq_self_iff_true, ↓reduceIte, if_neg g2]
  -- the 15 argument words at the entry state
  have hv : ∀ j : Fin 15, ∃ y, msg.syscall_arg st s ct buf ⟨BitVec.ofNat 64 j.val⟩ = ok y := fun j => by
    obtain ⟨y, hy, -⟩ := P1.spec_ex_fd
      (P0.msg.syscall_arg.p0 st s ct buf ⟨BitVec.ofNat 64 j.val⟩ (P1.LawfulStore.total (st := st)))
    exact ⟨y, hy⟩
  choose vals hvals using hv
  have J0 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a1
      (Notif.updK σ p.bv (.archObj (.vcpu (gprPre (fun i => (vals i).bv) vs (0#u64 : U64).val)))) := by
    rw [show (0#u64 : U64).val = 0 from rfl, show gprPre (fun i => (vals i).bv) vs 0 = vs from rfl, zv_updK_self hk]
    exact J1
  refine WP.spec_bind (JAtZV3.wrLoop (L := L) (arI := arI) (X := X) (AR := AR) (H := H) (Cs := Cs) (Ac := Ac)
    (Lst := Lst) (D := D) (a := a1) hp hk hctA hcth hb s vals hvals 0#u64 (by simp) s J0 (RBKeep.refl ct buf s)) ?_
  rintro s2 ⟨J2, -⟩
  have hk2 : (Notif.updK σ p.bv (.archObj (.vcpu (vs.setGprs fun i => (vals i).bv)))).kheap p.bv =
      some (.archObj (.vcpu (vs.setGprs fun i => (vals i).bv))) := by simp [Notif.updK]
  refine WP.spec_bind (Pₘ := fun s3 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s3 a1
    (Notif.updK σ p.bv (.archObj (.vcpu (vs.setGprs fun i => (vals i).bv))))) ?_ ?_
  · split
    · simp only [vcpu.get, lift, bind_ok]
      refine WP.spec_bind (P1.LawfulStore.read_spec s2 _) fun v _ => ?_
      rw [zv_RAX_eq, bind_ok]
      simp only [vcpu.set, lift, bind_ok]
      refine WP.spec_mono (P1.LawfulStore.write_spec _ _ _) fun s3 e3 => ?_
      rw [e3]
      have hf := (J2.z2.zv.base.jvLay J2.z2.zv.vm).vfit p hp
      have h2 := hf.2
      have hs : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
      exact J2.raxWr hp (by
        have : (1528#u64 : U64).val = 1528 := rfl
        rw [core.num.U64.wrapping_add_val_eq, hs, this, Nat.mod_eq_of_lt (by omega)]) v
    · exact (WP.spec_ok _).2 J2
  · intro s3 J3
    obtain ⟨s4, h4, -⟩ := P1.spec_ex_fd
      (P0.sched.set_thread_state.p0 st s3 ct sched.TS_RESTART (P1.LawfulStore.total (st := st)))
    rw [h4, bind_ok]
    refine (WP.spec_ok _).2 ⟨ct, vals, rfl, hvals, rfl, fun args ec hl hargs => ?_,
      s3, _, zv_perform_wregs hk _, J3, h4⟩
    rw [zv_wregs_bv, zv_decode_wregs (by omega),
      show (fun i : Fin 15 => args.getD i.val 0) = (fun i => (vals i).bv) from funext hargs]

end

end

end Fl4Proofs.P3

/-
P3 (line mmuAD, gen 39): **X86VCPUEnableIOPort end to end at `JAtZV3`** — the extracted `vcpu.decode` at label
`X86VCPUEnableIOPort` (vcpu.rs l. 1007-1062 on VMX, `len ≥ 2`: `low = f & 0xffff`, `high = value & 0xffff`,
`low > high` → `InvalidArgument 0`; `ex[0]` null → `TruncatedMessage`; `ex[0]`'s cap not `IoPort` → `IllegalOperation`;
`IoPort first last prior` with `low < first` or `high > last` → `InvalidArgument 0`; else the walk of the VCPU list
(l. 1035-1045: `prior = 0` stalls and revokes nothing), `ex[0].set_cap(IoPort first last v)` (l. 1046),
`ports(s, v, low, high, false)` and `set_thread_state(ct, TS_RESTART)`) paired with the extended spec's
`decodeVcpuInvocation` (`.enableIoPort v (f &&& 0xffff) (x &&& 0xffff) (.ioPortCap first last) slot`, the same four
errors in the same order) and `performVcpuInvocationF (.enableIoPort …)` (`ioPortRevoke`, which does nothing:
`ioPortOwner = none`, decision Q2; then `vcpuUpdate v (setPorts lo hi false)`, reply `[]`), in `VDecPostC` form,
tail (a).

* Spec side: `zv_decode_eio_inv`, `zv_decode_eio_nil`, `zv_decode_eio_ill`, `zv_decode_eio_rng`, `zv_decode_eio_ok`,
  `zv_perform_eio`; `zv_absIo_ne`, `zv_sw16` (`setWidth 64 (ofNat 16 q) = q` below `2^16`).
* `zv_walk0`: the VCPU-list walk `decode_loop3` with `prior = 0` returns its state unchanged (each step reads the
  `NEXT` word only; `fuel` bounds it).
* **`JAtZV3.enableIoPortJ`**: the label at `JAtZV3`, VMX, `len ≥ 2`, under the scope **`IoFresh b c`** (gen 37:
  the cap's owner word is 0) and **the slot scope** `b = false → ex[0] = cslotAddr (pc, idx)` for a CNode `pc` of
  `Z.th` (the front end's extra-cap lookup, P3/JAtZV3EioFront), and `Canonical p` (the invoked cap's decoded
  pointer). The `set_cap` step is P3/JAtZV3SlotIo's `JAtZV3.ioOwnJ`, the bitmap step P3/JAtZV3VDio's `portsLoopJ`
  with `d = false`.

No named premise beyond those of `disableIoPortJ` ([P] `ZvVirtAgree arI`, `ARKeep arI AR`). No existing statement
changed.
-/
import Fl4Proofs.P3.JAtZV3SlotIo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## The spec side -/

section
open Fl4Spec

theorem zv_decode_eio_inv (hvk : virtKind ≠ .svm) {args : List Data} (hl : 2 ≤ args.length) {f x : Word}
    (h0 : args.getD 0 0 = f) (h1 : args.getD 1 0 = x) (hgt : f &&& 0xffff > x &&& 0xffff) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 79 args v ec = NonDetE.throwError (.invalidArgument 0) := by
  have hn : ¬ args.length < 2 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_eio]
  simp only [hvk, hn, h0, h1, hgt, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem zv_decode_eio_nil (hvk : virtKind ≠ .svm) {args : List Data} (hl : 2 ≤ args.length) {f x : Word}
    (h0 : args.getD 0 0 = f) (h1 : args.getD 1 0 = x) (hgt : ¬ f &&& 0xffff > x &&& 0xffff) (v : ObjRef) :
    decodeVcpuInvocation (Z := Unit) 79 args v [] = NonDetE.throwError .truncatedMessage := by
  have hn : ¬ args.length < 2 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_eio]
  simp only [hvk, hn, h0, h1, hgt, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem zv_decode_eio_ill (hvk : virtKind ≠ .svm) {args : List Data} (hl : 2 ≤ args.length) {f x : Word}
    (h0 : args.getD 0 0 = f) (h1 : args.getD 1 0 = x) (hgt : ¬ f &&& 0xffff > x &&& 0xffff) (v : ObjRef)
    {cr : Cap} (hcr : ∀ a b, cr ≠ .archObjectCap (.ioPortCap a b)) (cp : CslotPtr) (rest : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 79 args v ((cr, cp) :: rest) = NonDetE.throwError .illegalOperation := by
  have hn : ¬ args.length < 2 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_eio]
  simp only [hvk, hn, h0, h1, hgt, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem zv_decode_eio_rng (hvk : virtKind ≠ .svm) {args : List Data} (hl : 2 ≤ args.length) {f x : Word}
    (h0 : args.getD 0 0 = f) (h1 : args.getD 1 0 = x) (hgt : ¬ f &&& 0xffff > x &&& 0xffff) (v : ObjRef)
    (fs ls : BitVec 16) (cp : CslotPtr) (rest : List (Cap × CslotPtr))
    (hr : f &&& 0xffff < BitVec.setWidth 64 fs ∨ x &&& 0xffff > BitVec.setWidth 64 ls) :
    decodeVcpuInvocation (Z := Unit) 79 args v ((.archObjectCap (.ioPortCap fs ls), cp) :: rest) =
      NonDetE.throwError (.invalidArgument 0) := by
  have hn : ¬ args.length < 2 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_eio]
  simp only [hvk, hn, h0, h1, hgt, hr, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem zv_decode_eio_ok (hvk : virtKind ≠ .svm) {args : List Data} (hl : 2 ≤ args.length) {f x : Word}
    (h0 : args.getD 0 0 = f) (h1 : args.getD 1 0 = x) (hgt : ¬ f &&& 0xffff > x &&& 0xffff) (v : ObjRef)
    (fs ls : BitVec 16) (cp : CslotPtr) (rest : List (Cap × CslotPtr))
    (hr : ¬ (f &&& 0xffff < BitVec.setWidth 64 fs ∨ x &&& 0xffff > BitVec.setWidth 64 ls)) :
    decodeVcpuInvocation (Z := Unit) 79 args v ((.archObjectCap (.ioPortCap fs ls), cp) :: rest) =
      NonDetE.returnOk (.enableIoPort v (f &&& 0xffff) (x &&& 0xffff) (.ioPortCap fs ls) cp) := by
  have hn : ¬ args.length < 2 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_eio]
  simp only [hvk, hn, h0, h1, hgt, hr, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem zv_perform_eio {σ : State Unit} {v : ObjRef} {vs : VcpuState}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (lo hi : Word) (c : ArchCap) (sl : CslotPtr) :
    performVcpuInvocationF (Z := Unit) (.enableIoPort v lo hi c sl) σ =
      ({([], Notif.updK σ v (.archObj (.vcpu (vs.setPorts lo hi false))))}, False) := by
  have hr : ioPortRevoke (Z := Unit) c σ = ({((), σ)}, False) := by
    cases c <;> rfl
  show ((ioPortRevoke (Z := Unit) c) >>= fun _ => (vcpuUpdate (Z := Unit) v (VcpuState.setPorts lo hi false)) >>=
    fun _ => (pure [] : SMonad Unit (List Data))) σ = _
  rw [Notif.nd_bind_one hr, Notif.nd_bind_one (zv_vcpuUpdate_eq hk _)]
  rfl

end

theorem zv_absIo_ne {c : capability.Cap} (h : ∀ f l q, c ≠ .IoPort f l q) (a b : BitVec 16) :
    absCap c ≠ .archObjectCap (.ioPortCap a b) := by
  intro e
  cases c <;> simp [absCap] at e
  all_goals exact h _ _ _ rfl

theorem zv_sw16 {q : U64} (h : q.val < 2 ^ 16) : BitVec.setWidth 64 (BitVec.ofNat 16 q.val) = q.bv := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UScalar.bv_toNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## The VCPU-list walk without a prior owner -/

theorem zv_walk0 {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {arI : machine.Arch A}
    (s : S) (a : A) (first last old fuel : U64) :
    vcpu.decode_loop3 st arI s a first last 0#u64 old fuel ⦃ r => r = (s, a) ⦄ := by
  unfold vcpu.decode_loop3
  apply loop.spec_decr_nat (measure := fun y : S × A × U64 × U64 => y.2.2.2.val)
    (inv := fun y => y.1 = s ∧ y.2.1 = a)
  · rintro ⟨s2, a2, o, fu⟩ ⟨e1, e2⟩
    simp only at e1 e2 ⊢
    subst e1
    subst e2
    unfold vcpu.decode_loop3.body
    split
    · rename_i hne
      split
      · rename_i hfu
        have ho : ¬ o = 0#u64 := by simpa using hne
        step as ⟨fu1, hfu1⟩
        rw [if_neg ho, bind_ok]
        try dsimp only
        unfold vcpu.get
        simp only [lift, bind_ok]
        refine WP.spec_bind (P1.LawfulStore.read_spec s2 _) fun o1 _ => ?_
        rw [WP.spec_ok]
        refine ⟨rfl, rfl, ?_⟩
        show fu1.val < fu.val
        scalar_tac
      · rw [WP.spec_ok]
    · rw [WP.spec_ok]
  · exact ⟨rfl, rfl⟩

/-! ## The invocation -/

section
open Classical Fl4Proofs.P3.Vs
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 16000000 in
/-- **X86VCPUEnableIOPort at `JAtZV3`, VMX, `len ≥ 2`** (module docstring). -/
theorem JAtZV3.enableIoPortJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind ≠ .svm) {p : U64} (hp : p ∈ V) (hcan : Canonical p)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 2 ≤ len.val)
    (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hio : IoFresh b c)
    (hsc : b = false → ∃ pc r idx, Z.th pc = some (.cnode r) ∧ idx.length = r ∧ sl = cslotAddr (pc.bv, idx)) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUEnableIOPort len p call buf ex ⦃ rr =>
      VDecPostC (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUEnableIOPort len p call buf b c rr ⦄ := by
  have g0 : len > 0#u64 := by scalar_tac
  have g1 : len > 1#u64 := by scalar_tac
  have g2 : ¬ len < 2#u64 := by scalar_tac
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  have h2 : ¬ i = 2#u64 := fun e => hvk (hi2.1 e)
  rw [hi, bind_ok]
  obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
  obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
  rw [if_pos g0, hf, bind_ok, if_pos g1, hx, bind_ok]
  have nSetTCB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUSetTCB])
  have nWriteRegisters := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteRegisters])
  have nFlushTLB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUFlushTLB])
  have nReadVMCS := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUReadVMCS])
  have nWriteVMCS := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteVMCS])
  have nReadVMCB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUReadVMCB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUReadVMCB])
  have nWriteVMCB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteVMCB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteVMCB])
  have nReadMSR := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUReadMSR
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUReadMSR])
  have nWriteMSR := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteMSR
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteMSR])
  simp only [if_neg nSetTCB, if_neg nWriteRegisters, if_neg nFlushTLB, if_neg nReadVMCS, if_neg nWriteVMCS,
    if_neg nReadVMCB, if_neg nWriteVMCB, if_neg nReadMSR, if_neg nWriteMSR, ↓reduceIte,
    if_neg h2, if_neg g2, lift, bind_ok, not_true_eq_false, decide_false]
  have hf0 : ∀ args : List Fl4Spec.Data, VArgs st s ct buf len args → args.getD 0 0 = f.bv :=
    fun args hA => hA.a0 (by omega) hf
  have hx1 : ∀ args : List Fl4Spec.Data, VArgs st s ct buf len args → args.getD 1 0 = x.bv :=
    fun args hA => hA.a1 (by omega) hx
  by_cases hlh : (f &&& 65535#u64) > (x &&& 65535#u64)
  · have hgt : f.bv &&& 0xffff > x.bv &&& 0xffff := by
      rw [← zv_mask_bv, ← zv_mask_bv]; exact (Sched.gt_bv _ _).1 hlh
    simp only [if_pos hlh, error.invalid_arg, bind_ok, WP.spec_ok]
    exact ⟨ct, hct, fun args ec hA _ => Or.inl ⟨_, .invalidArgument 0, rfl, rfl, by
      rw [zv_eio_bv, zv_decode_eio_inv hvk (by rw [hA.1]; exact hlen) (hf0 args hA) (hx1 args hA) hgt],
      rfl, J1⟩⟩
  have hle : ¬ f.bv &&& 0xffff > x.bv &&& 0xffff := by
    rw [← zv_mask_bv, ← zv_mask_bv]; exact fun h => hlh ((Sched.gt_bv _ _).2 h)
  have hlo : (f &&& 65535#u64).val ≤ (x &&& 65535#u64).val := by
    have := fun h => hlh ((gt_iff_lt).2 h); scalar_tac
  rw [if_neg hlh, hsl, bind_ok, hbn, bind_ok]
  cases b with
  | true =>
    rw [if_pos rfl]
    simp only [error.truncated, bind_ok, WP.spec_ok]
    exact ⟨ct, hct, fun args ec hA hC => Or.inl ⟨_, .truncatedMessage, rfl, trivial, by
      rw [hC.1 rfl, zv_eio_bv, zv_decode_eio_nil hvk (by rw [hA.1]; exact hlen) (hf0 args hA) (hx1 args hA) hle],
      rfl, J1⟩⟩
  | false =>
    rw [if_neg Bool.false_ne_true, hc rfl, bind_ok]
    have ILL : (∀ f' l' q, c ≠ .IoPort f' l' q) →
        (do
          let r ← error.illegal Unit
          ok (r, s, a1)) ⦃ rr => VDecPostC (L := L) arI V X AR Z H Cs Ac Lst D s σ
            fl4_abi.label.X86VCPUEnableIOPort len p call buf false c rr ⦄ := by
      intro hni
      simp only [error.illegal, bind_ok, WP.spec_ok]
      refine ⟨ct, hct, fun args ec hA hC => Or.inl ⟨_, .illegalOperation, rfl, trivial, ?_, rfl, J1⟩⟩
      obtain ⟨cp, rest, hec⟩ := hC.2 rfl
      rw [hec, zv_eio_bv, zv_decode_eio_ill hvk (by rw [hA.1]; exact hlen) (hf0 args hA) (hx1 args hA) hle p.bv
        (zv_absIo_ne hni) cp rest]
    cases c
    case IoPort first last prior =>
      dsimp only
      have hpr : prior = 0#u64 := hio rfl first last prior rfl
      subst hpr
      obtain ⟨pc, r, idx, hpc, hidx, hsle⟩ := hsc rfl
      subst hsle
      have hcx : capV (L.mem s) (cslotAddr (pc.bv, idx)) = .IoPort first last 0#u64 := by
        have h' := hc rfl
        rw [slot_cap_eq] at h'
        exact capV_of_capAt h'
      have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
      have hwf : first.val < 2 ^ 16 ∧ last.val < 2 ^ 16 ∧ first.val ≤ last.val := by
        obtain ⟨c0, a0, hc0, hr0, -⟩ := B.xtop.rel.2.1.1.abs_cap hA
        have e := capV_of_capAt hc0
        rw [hcx] at e
        subst e
        exact hr0.1
      have hfs : BitVec.setWidth 64 (BitVec.ofNat 16 first.val) = first.bv := zv_sw16 hwf.1
      have hls : BitVec.setWidth 64 (BitVec.ofNat 16 last.val) = last.bv := zv_sw16 hwf.2.1
      have habs : absCap (.IoPort first last 0#u64) =
          .archObjectCap (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val)) := rfl
      by_cases hl1 : (f &&& 65535#u64) < first
      · rw [if_pos hl1]
        simp only [error.invalid_arg, bind_ok, WP.spec_ok]
        refine ⟨ct, hct, fun args ec hA' hC => Or.inl ⟨_, .invalidArgument 0, rfl, rfl, ?_, rfl, J1⟩⟩
        obtain ⟨cp, rest, hec⟩ := hC.2 rfl
        rw [hec, habs, zv_eio_bv, zv_decode_eio_rng hvk (by rw [hA'.1]; exact hlen) (hf0 args hA') (hx1 args hA') hle
          p.bv _ _ cp rest (Or.inl (by rw [hfs, ← zv_mask_bv]; exact (Sched.lt_bv _ _).1 hl1))]
      rw [if_neg hl1]
      by_cases hl2 : (x &&& 65535#u64) > last
      · rw [if_pos hl2]
        simp only [error.invalid_arg, bind_ok, WP.spec_ok]
        refine ⟨ct, hct, fun args ec hA' hC => Or.inl ⟨_, .invalidArgument 0, rfl, rfl, ?_, rfl, J1⟩⟩
        obtain ⟨cp, rest, hec⟩ := hC.2 rfl
        rw [hec, habs, zv_eio_bv, zv_decode_eio_rng hvk (by rw [hA'.1]; exact hlen) (hf0 args hA') (hx1 args hA') hle
          p.bv _ _ cp rest (Or.inr (by rw [hls, ← zv_mask_bv]; exact (Sched.gt_bv _ _).1 hl2))]
      rw [if_neg hl2]
      have hr : ¬ (f.bv &&& 0xffff < BitVec.setWidth 64 (BitVec.ofNat 16 first.val) ∨
          x.bv &&& 0xffff > BitVec.setWidth 64 (BitVec.ofNat 16 last.val)) := by
        rw [hfs, hls, ← zv_mask_bv, ← zv_mask_bv]
        rintro (h | h)
        · exact hl1 ((Sched.lt_bv _ _).2 h)
        · exact hl2 ((Sched.gt_bv _ _).2 h)
      obtain ⟨old, hold, -⟩ := P1.spec_ex_fd
        (P0.obj.ks_get.p0 st s layout.ks.VCPU_HEAD (P1.LawfulStore.total (st := st)))
      rw [hold, bind_ok]
      refine WP.spec_bind (zv_walk0 (arI := arI) s a1 first last old layout.WALK_FUEL) ?_
      rintro r3 rfl
      show (do
        let s4 ← ok (cslotAddr (pc.bv, idx))
        let s5 ← obj.Slot.set_cap st s4 s (capability.Cap.IoPort first last p)
        let s6 ← vcpu.ports st s5 p (f &&& 65535#u64) (x &&& 65535#u64) false
        let s7 ← sched.set_thread_state st s6 ct sched.TS_RESTART
        ok (core.result.Result.Ok (), s7, a1)) ⦃ rr => VDecPostC (L := L) arI V X AR Z H Cs Ac Lst D s σ
          fl4_abi.label.X86VCPUEnableIOPort len p call buf false (.IoPort first last 0#u64) rr ⦄
      rw [bind_ok]
      refine WP.spec_bind (J1.ioOwnJ hpc hidx hcx hp hcan) ?_
      rintro s5 ⟨J5, -, -⟩
      unfold vcpu.ports
      have J5' : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s5 a1
          (Notif.updK σ p.bv (.archObj (.vcpu (vsIoLt vs (f &&& 65535#u64).val (f &&& 65535#u64).val false)))) := by
        rw [vsIoLt_self, v3_updK_self hk]; exact J5
      refine WP.spec_bind (J5'.portsLoopJ hvk hp (zv_mask_lt x) false hk _ s5 (f &&& 65535#u64) le_rfl
        (by omega)) fun s6 J6 => ?_
      obtain ⟨s7, h7, -⟩ := P1.spec_ex_fd
        (P0.sched.set_thread_state.p0 st s6 ct sched.TS_RESTART (P1.LawfulStore.total (st := st)))
      rw [h7, bind_ok, WP.spec_ok]
      have eP : vsIoLt vs (f &&& 65535#u64).val ((x &&& 65535#u64).val + 1) false =
          vs.setPorts (f.bv &&& 0xffff) (x.bv &&& 0xffff) false :=
        vsIoLt_setPorts vs false (by rw [← zv_mask_bv, UScalar.bv_toNat]) (by rw [← zv_mask_bv, UScalar.bv_toNat])
      rw [eP] at J6
      refine ⟨ct, hct, fun args ec hA' hC => ?_⟩
      obtain ⟨cp, rest, hec⟩ := hC.2 rfl
      exact Or.inr ⟨.enableIoPort p.bv (f.bv &&& 0xffff) (x.bv &&& 0xffff)
        (.ioPortCap (BitVec.ofNat 16 first.val) (BitVec.ofNat 16 last.val)) cp, [], s6, _, Ac, Lst, rfl,
        by rw [hec, habs, zv_eio_bv, zv_decode_eio_ok hvk (by rw [hA'.1]; exact hlen) (hf0 args hA') (hx1 args hA')
          hle p.bv _ _ cp rest hr],
        zv_perform_eio hk _ _ _ _, J6, Or.inl ⟨rfl, h7⟩⟩
    all_goals (dsimp only; exact ILL (fun f' l' q e => by cases e))

end

end

end Fl4Proofs.P3

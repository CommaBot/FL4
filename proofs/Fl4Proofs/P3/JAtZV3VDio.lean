/-
P3 (line mmuAD, gen 38): **X86VCPUDisableIOPort end to end at `JAtZV3`** — the extracted `vcpu.decode` at label
`X86VCPUDisableIOPort` (vcpu.rs l. 1007-1062 on VMX, `len ≥ 2`: `low = f & 0xffff`, `high = value & 0xffff`,
`low > high` → `InvalidArgument 0`, else `ports(s, v, low, high, true)` (l. 755-764: for every port of `low..high`
the bit `port & 63` of the word `IO + 8 · (port >> 6)` set) and `set_thread_state(ct, TS_RESTART)`) paired with the
extended spec's `decodeVcpuInvocation` (`.disableIoPort v (f &&& 0xffff) (x &&& 0xffff)` / `invalidArgument 0`) and
`performVcpuInvocationF (.disableIoPort v lo hi)` (`vcpuUpdate v (setPorts lo hi true)`, reply `[]`), in
`VDecPost` form (`P3/JAtZV3VDec`), tail (a).

* `zv_ioBit_dec`, `zv_ioOff_nat`: the relation's bitmap test is the word's bit `P % 64`; the word's offset.
* **`zv_ioStore_vmx`**: a store into the bitmap word of port `Q` that sets bit `Q % 64` to `d` and keeps the
  other bits keeps `VcpuRelVmx` with `ioDenied Q := d` (every other place of the relation lies below `IO`).
* **`JAtZV3.ioWr`**: that store paired with the spec VCPU update keeps `JAtZV3` (gen 30's `vcpuStep`).
* `vsIoLt vs lo n d` (the bitmap with `lo ≤ P < n` set to `d`), `vsIoLt_self`, `vsIoLt_setPorts`.
* **`JAtZV3.portsLoopJ`**: FL4's `vcpu.ports_loop` from port `q` (`lo ≤ q ≤ high + 1`, `high < 2^16`) refines
  the spec bitmap update `lo ≤ P ≤ high` (loop invariant: `JAtZV3` at `vsIoLt vs lo q d`).
* Spec side: `zv_decode_dio_inv`, `zv_decode_dio_ok`, `zv_perform_dio`.
* **`JAtZV3.disableIoPortJ`**: the label at `JAtZV3`, VMX, `len ≥ 2`. **`vcpuNyp_dio`**: `VcpuNyp3`'s
  `disableIoPort` field, proved.

Premises: [P] `ZvVirtAgree arI`, `ARKeep arI AR` (existing). No new premise; no existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VDisp3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## The bitmap word -/

section
open Fl4Spec

theorem zv_ioBit_dec (x : Word) (P : BitVec 16) :
    decide (x &&& vcpuIoBit P ≠ 0) = x.getLsbD (P.toNat % 64) := by
  have hk : P.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  have e : vcpuIoBit P = BitVec.twoPow 64 (P.toNat % 64) := rfl
  rw [e, BitVec.and_twoPow]
  have h0 : BitVec.twoPow 64 (P.toNat % 64) ≠ 0 := by
    intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)] at this
    simp at this
  by_cases hb : x.getLsbD (P.toNat % 64) = true
  · rw [if_pos hb, hb]; exact decide_eq_true h0
  · rw [if_neg hb]; simp only [ne_eq, not_true_eq_false, decide_false]; exact (Bool.of_not_eq_true hb).symm

theorem zv_ioOff_nat (P : BitVec 16) : (vcpuIoOff P).toNat = 24576 + 8 * (P.toNat / 64) := by
  have hp : P.toNat < 65536 := P.isLt
  simp [vcpuIoOff, VcpuLay.IO, BitVec.toNat_add, BitVec.toNat_mul]
  omega

set_option maxHeartbeats 4000000 in
/-- **A store into port `Q`'s bitmap word keeps the VMX relation** with `ioDenied Q := d` (module docstring). -/
theorem zv_ioStore_vmx {mem mem' : Word → Word} {v : Word} {vs : VcpuState} {Q : BitVec 16} {d : Bool} {w : Word}
    (h : VcpuRelVmx mem v vs) (hw : VirtMsrStore.WrAt mem mem' v (vcpuIoOff Q) w)
    (hb : ∀ j, w.getLsbD j = if j = Q.toNat % 64 then d else (mem (v + vcpuIoOff Q)).getLsbD j)
    (g : BitVec 16 → Bool) (hg : ∀ P, g P = if P = Q then d else vs.ioDenied P) :
    VcpuRelVmx mem' v { vs with ioDenied := g } := by
  have hQ := VirtMsrStore.ioOff_nat Q
  have hk : ∀ off : Word, off.toNat < 24576 → off.toNat % 8 = 0 → mem' (v + off) = mem (v + off) :=
    fun off h1 h2 => hw.keep (by omega) h2 (by omega)
  refine ⟨⟨?_, ?_, ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩, fun f hf => ?_, fun m i hi => ?_, ?_, fun P => ?_⟩
  · rw [hk VcpuLay.TCB (by decide) (by decide)]; exact h.tcb
  · rw [hk VcpuLay.VALID (by decide) (by decide)]; exact h.valid
  · rw [hk VcpuLay.PENDING (by decide) (by decide)]; exact h.pending
  · have e := VirtMsrStore.exitOff_nat i
    rw [hk (exitOff i) (by omega) (by omega)]; exact h.mrs i
  · have e := VirtMsrStore.gprOff_nat i
    rw [hk (gprOff i) (by omega) (by omega)]; exact h.gpr i
  · rw [hk VcpuLay.XCR0 (by decide) (by decide)]; exact h.xcr0
  · rw [hk VcpuLay.VM_IBPB_DEFER (by decide) (by decide)]; exact h.ibpb
  · have := VirtMsrStore.vmcsOff_nat f
    rw [hk (vmcsOff f) (by omega) this.2]; exact h.vmcs f hf
  · obtain ⟨-, h1, h2, h3, -⟩ := VirtMsrStore.msrOff_cases (VirtMsrStore.msrOff_of_slot hi)
    have := h3 rfl
    rw [hk (VcpuLay.MSRS + i * 8) (by omega) h2]; exact h.msr m i hi
  · rw [hk VcpuLay.CR2 (by decide) (by decide)]; exact h.cr2
  · show g P = _
    rw [hg P]
    have hP := VirtMsrStore.ioOff_nat P
    have nP := zv_ioOff_nat P
    have nQ := zv_ioOff_nat Q
    by_cases hs : P.toNat / 64 = Q.toNat / 64
    · have eo : vcpuIoOff P = vcpuIoOff Q := BitVec.eq_of_toNat_eq (by rw [nP, nQ, hs])
      rw [eo, hw.1, zv_ioBit_dec, hb]
      by_cases hpq : P = Q
      · subst hpq; rw [if_pos rfl, if_pos rfl]
      · have hm : P.toNat % 64 ≠ Q.toNat % 64 := fun e => hpq (BitVec.eq_of_toNat_eq (by omega))
        rw [if_neg hpq, if_neg hm, h.io P, eo, zv_ioBit_dec]
    · have hne : (vcpuIoOff P).toNat ≠ (vcpuIoOff Q).toNat := by rw [nP, nQ]; omega
      rw [hw.keep hP.2.1 hP.2.2 hne, if_neg (fun e => hs (by rw [e]))]
      exact h.io P

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **FL4's store into port `Q`'s bitmap word, paired with the spec's `ioDenied Q := d`** (module docstring). -/
theorem JAtZV3.ioWr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hvk : Fl4Spec.virtKind ≠ .svm)
    {p : U64} (hp : p ∈ V) {Q : BitVec 16} {x : U64} (hx : x.bv = p.bv + Fl4Spec.vcpuIoOff Q) {d : Bool}
    (w : U64) (hb : ∀ j, w.bv.getLsbD j = if j = Q.toNat % 64 then d else (L.mem s x).bv.getLsbD j)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs)))
    (g : BitVec 16 → Bool) (hg : ∀ P, g P = if P = Q then d else vs.ioDenied P) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s x w) a
      (Notif.updK σ p.bv (.archObj (.vcpu { vs with ioDenied := g }))) := by
  have hfv := (J.z2.zv.base.jvLay J.z2.zv.vm).vfit p hp
  have hv : VFits p := ⟨hfv.1, hfv.2⟩
  have hQ := VirtMsrStore.ioOff_nat Q
  have h1 : (Fl4Spec.vcpuIoOff Q).toNat < 32768 := hQ.2.1
  have h2 : (Fl4Spec.vcpuIoOff Q).toNat % 8 = 0 := hQ.2.2
  have ex : x = ⟨p.bv + Fl4Spec.vcpuIoOff Q⟩ := by
    rcases x with ⟨b⟩; exact congrArg (fun b => (⟨b⟩ : U64)) hx
  have hxv : x.val = p.val + (Fl4Spec.vcpuIoOff Q).toNat := by rw [ex, VirtInitWalk.vo_val hv h1]
  have hal : P1.Aligned x := by unfold P1.Aligned; rw [hxv]; have := hv.1; omega
  obtain ⟨w1, w2⟩ := VirtMsrStore.memW_wr (st := st) hv h1 h2 hx s w
  have hW : VirtMsrStore.WrAt (vmemW (L.mem s)) (vmemW (L.mem (L.wr s x w))) p.bv (Fl4Spec.vcpuIoOff Q) w.bv := by
    refine ⟨?_, fun off g1 g2 hne => ?_⟩
    · rw [v3_vmemW_al hv h1 h2]; exact w1
    · rw [v3_vmemW_al hv g1 g2, v3_vmemW_al hv g1 g2]; exact w2 off g1 g2 hne
  have hold : vmemW (L.mem s) (p.bv + Fl4Spec.vcpuIoOff Q) = (L.mem s x).bv := by
    rw [v3_vmemW_al hv h1 h2, ← ex]
  have R0 := J.vr p hp vs hk
  have hR : Fl4Spec.VcpuRel Fl4Spec.virtKind (vmemW (L.mem (L.wr s x w))) p.bv { vs with ioDenied := g } := by
    revert R0
    rcases hvk' : Fl4Spec.virtKind with _ | _ | _ | _
    · intro R0; exact (show False from R0).elim
    · intro R0
      exact zv_ioStore_vmx R0 hW (fun j => by rw [hb j, hold]) g hg
    · exact absurd hvk' hvk
    · intro R0; exact (show False from R0).elim
  exact J.vcpuStep hp hal (by rw [hxv]; omega) (by rw [hxv]; omega)
    ⟨by rw [hxv]; omega, by rw [hxv]; omega, by rw [hxv]; omega⟩ w hk _ rfl hR

end

/-! ## The ports loop -/

/-- The I/O bitmap with the ports `lo ≤ P < n` set to `d` (module docstring). -/
def vsIoLt (vs : Fl4Spec.VcpuState) (lo n : Nat) (d : Bool) : Fl4Spec.VcpuState :=
  { vs with ioDenied := fun P => if lo ≤ P.toNat ∧ P.toNat < n then d else vs.ioDenied P }

theorem vsIoLt_self (vs : Fl4Spec.VcpuState) (lo : Nat) (d : Bool) : vsIoLt vs lo lo d = vs := by
  unfold vsIoLt
  have : (fun P : BitVec 16 => if lo ≤ P.toNat ∧ P.toNat < lo then d else vs.ioDenied P) = vs.ioDenied := by
    funext P; rw [if_neg (by omega)]
  rw [this]

theorem vsIoLt_setPorts (vs : Fl4Spec.VcpuState) {lo n : Nat} {lo' hi' : Fl4Spec.Word} (d : Bool)
    (h1 : lo = lo'.toNat) (h2 : n = hi'.toNat + 1) : vsIoLt vs lo n d = vs.setPorts lo' hi' d := by
  unfold vsIoLt Fl4Spec.VcpuState.setPorts
  subst h1 h2
  congr 1
  funext P
  by_cases hc : lo'.toNat ≤ P.toNat ∧ P.toNat ≤ hi'.toNat
  · rw [if_pos hc, if_pos (by omega)]
  · rw [if_neg hc, if_neg (by omega)]

section
open Classical Fl4Proofs.P3.Vs
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem zv_and63 (q : U64) : (q &&& 63#u64).val = q.val % 64 := by
  rw [UScalar.val_and, show (63#u64 : U64).val = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

set_option maxHeartbeats 16000000 in
/-- **FL4's `ports_loop` against the spec's bitmap update** (module docstring). -/
theorem JAtZV3.portsLoopJ (hvk : Fl4Spec.virtKind ≠ .svm) {p : U64} (hp : p ∈ V) {high : U64}
    (hh : high.val < 65536) (d : Bool) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (lo : Nat) (s1 : S) (port : U64)
    (h1 : lo ≤ port.val) (h2 : port.val ≤ high.val + 1)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a
      (Notif.updK σ p.bv (.archObj (.vcpu (vsIoLt vs lo port.val d))))) :
    vcpu.ports_loop st s1 p high d port ⦃ s' =>
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s' a
        (Notif.updK σ p.bv (.archObj (.vcpu (vsIoLt vs lo (high.val + 1) d)))) ⦄ := by
  unfold vcpu.ports_loop
  apply loop.spec_decr_nat (measure := fun y : S × U64 => 65536 - y.2.val)
    (inv := fun y => lo ≤ y.2.val ∧ y.2.val ≤ high.val + 1 ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D y.1 a
        (Notif.updK σ p.bv (.archObj (.vcpu (vsIoLt vs lo y.2.val d)))))
  · rintro ⟨s2, q⟩ ⟨g1, g2, J2⟩
    simp only at g1 g2 J2 ⊢
    unfold vcpu.ports_loop.body
    by_cases c1 : q ≤ high
    swap
    · rw [if_neg c1, WP.spec_ok]
      have : q.val = high.val + 1 := by
        have : high.val < q.val := by scalar_tac
        omega
      rw [← this]; exact J2
    rw [if_pos c1]
    have hq1 : q.val ≤ high.val := by scalar_tac
    have c2 : q < 65536#u64 := by scalar_tac
    rw [if_pos c2]
    simp only [lift, bind_ok]
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    have hi1' : i1.val = q.val / 64 := by
      have : i1.val = q.val >>> 6 := by simpa using hi1
      rw [this, Nat.shiftRight_eq_div_pow]
    have hk8 : i2.val = 8 * (q.val / 64) := by rw [hi2, hi1']; ring
    step as ⟨bit, hb1, hb2⟩
    refine WP.spec_bind (P1.LawfulStore.read_spec s2 _) fun old hold => ?_
    -- the spec port and the address
    have hQv : (q.bv.setWidth 16).toNat = q.val := by
      rw [BitVec.toNat_setWidth, UScalar.bv_toNat]; omega
    have hx : (core.num.U64.wrapping_add (core.num.U64.wrapping_add p vcpu.IO) i2).bv =
        p.bv + Fl4Spec.vcpuIoOff (q.bv.setWidth 16) := by
      rw [core.num.U64.wrapping_add_bv_eq, core.num.U64.wrapping_add_bv_eq, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [zv_ioOff_nat, hQv, BitVec.toNat_add, UScalar.bv_toNat, UScalar.bv_toNat, hk8]
      have : vcpu.IO.val = 24576 := by unfold vcpu.IO; rfl
      rw [this]; omega
    have hk3 : (q &&& 63#u64).val < 64 := by rw [zv_and63]; omega
    have hk2 : (Notif.updK σ p.bv (.archObj (.vcpu (vsIoLt vs lo q.val d)))).kheap p.bv =
        some (.archObj (.vcpu (vsIoLt vs lo q.val d))) := by simp
    have hg : ∀ P : BitVec 16, (vsIoLt vs lo (q.val + 1) d).ioDenied P =
        if P = q.bv.setWidth 16 then d else (vsIoLt vs lo q.val d).ioDenied P := by
      intro P
      show (if lo ≤ P.toNat ∧ P.toNat < q.val + 1 then d else vs.ioDenied P) =
        if P = q.bv.setWidth 16 then d else (if lo ≤ P.toNat ∧ P.toNat < q.val then d else vs.ioDenied P)
      by_cases e : P.toNat = q.val
      · have eP : P = q.bv.setWidth 16 := BitVec.eq_of_toNat_eq (by rw [e, hQv])
        rw [if_pos (by omega), if_pos eP]
      · have eP : P ≠ q.bv.setWidth 16 := fun e' => e (by rw [e', hQv])
        rw [if_neg eP]
        by_cases c : lo ≤ P.toNat ∧ P.toNat < q.val
        · rw [if_pos (by omega), if_pos c]
        · rw [if_neg (by omega), if_neg c]
    split
    · rename_i hd
      refine WP.spec_bind (P1.LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
      subst e3
      step as ⟨q1, hq1v⟩
      have hb : ∀ j, (old ||| bit).bv.getLsbD j = if j = (q.bv.setWidth 16).toNat % 64 then d
          else (L.mem s2 (core.num.U64.wrapping_add (core.num.U64.wrapping_add p vcpu.IO) i2)).bv.getLsbD j := by
        intro j
        rw [P1.bit_or_shl old bit (old ||| bit) (q &&& 63#u64) hk3 hb2
          (by first | rfl | simp [U64.bv, UScalar.bv_or]), zv_and63, hQv, ← hold, hd]
        by_cases e : j = q.val % 64
        · rw [if_pos e, e]; simp
        · rw [if_neg e]; simp [e]
      have J3 := J2.ioWr hvk hp hx (old ||| bit) hb hk2 _ hg
      rw [Vs.updK_updK] at J3
      try rw [WP.spec_ok]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show lo ≤ q1.val; omega
      · show q1.val ≤ high.val + 1; omega
      · show JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D _ a
          (Notif.updK σ p.bv (.archObj (.vcpu (vsIoLt vs lo q1.val d))))
        rw [hq1v]; exact J3
      · show 65536 - q1.val < 65536 - q.val; omega
    · rename_i hd
      refine WP.spec_bind (P1.LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
      subst e3
      step as ⟨q1, hq1v⟩
      have hd' : d = false := by simpa using hd
      have hb : ∀ j, (old &&& ~~~bit).bv.getLsbD j = if j = (q.bv.setWidth 16).toNat % 64 then d
          else (L.mem s2 (core.num.U64.wrapping_add (core.num.U64.wrapping_add p vcpu.IO) i2)).bv.getLsbD j := by
        intro j
        rw [P1.bit_and_not_shl old bit (old &&& ~~~bit) (q &&& 63#u64) hk3 hb2
          (by first | rfl | simp [U64.bv, UScalar.bv_and, UScalar.bv_not]),
          zv_and63, hQv, ← hold, hd']
        by_cases e : j = q.val % 64
        · rw [if_pos e, e]; simp
        · rw [if_neg e]; simp [e]
      have J3 := J2.ioWr hvk hp hx (old &&& ~~~bit) hb hk2 _ hg
      rw [Vs.updK_updK] at J3
      try rw [WP.spec_ok]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show lo ≤ q1.val; omega
      · show q1.val ≤ high.val + 1; omega
      · show JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D _ a
          (Notif.updK σ p.bv (.archObj (.vcpu (vsIoLt vs lo q1.val d))))
        rw [hq1v]; exact J3
      · show 65536 - q1.val < 65536 - q.val; omega
  · exact ⟨h1, h2, J⟩

end

/-! ## The spec side -/

section
open Fl4Spec

theorem zv_decode_dio_inv (hvk : virtKind ≠ .svm) {args : List Data} (hl : 2 ≤ args.length) {f x : Word}
    (h0 : args.getD 0 0 = f) (h1 : args.getD 1 0 = x) (hgt : f &&& 0xffff > x &&& 0xffff) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 80 args v ec = NonDetE.throwError (.invalidArgument 0) := by
  have hn : ¬ args.length < 2 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_dio]
  simp only [hvk, hn, h0, h1, hgt, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem zv_decode_dio_ok (hvk : virtKind ≠ .svm) {args : List Data} (hl : 2 ≤ args.length) {f x : Word}
    (h0 : args.getD 0 0 = f) (h1 : args.getD 1 0 = x) (hgt : ¬ f &&& 0xffff > x &&& 0xffff) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 80 args v ec =
      NonDetE.returnOk (.disableIoPort v (f &&& 0xffff) (x &&& 0xffff)) := by
  have hn : ¬ args.length < 2 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_dio]
  simp only [hvk, hn, h0, h1, hgt, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem zv_perform_dio {σ : State Unit} {v : ObjRef} {vs : VcpuState}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (lo hi : Word) :
    performVcpuInvocationF (Z := Unit) (.disableIoPort v lo hi) σ =
      ({([], Notif.updK σ v (.archObj (.vcpu (vs.setPorts lo hi true))))}, False) := by
  show ((vcpuUpdate (Z := Unit) v (VcpuState.setPorts lo hi true)) >>= fun _ =>
    (pure [] : SMonad Unit (List Data))) σ = _
  rw [Notif.nd_bind_one (zv_vcpuUpdate_eq hk _)]
  rfl

end

/-! ## The invocation -/

section
open Classical Fl4Proofs.P3.Vs
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem zv_mask_bv (f : U64) : (f &&& 65535#u64).bv = (f.bv : Fl4Spec.Word) &&& (0xffff : Fl4Spec.Word) := by rw [UScalar.bv_and]; rfl

theorem zv_mask_lt (f : U64) : (f &&& 65535#u64).val < 65536 := by
  rw [UScalar.val_and]
  have := @Nat.and_le_right f.val 65535
  have e : (65535#u64 : U64).val = 65535 := rfl
  rw [e]; omega

set_option maxHeartbeats 16000000 in
/-- **X86VCPUDisableIOPort at `JAtZV3`, VMX, `len ≥ 2`** (module docstring). -/
theorem JAtZV3.disableIoPortJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind ≠ .svm) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 2 ≤ len.val) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUDisableIOPort len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUDisableIOPort len p call buf b c r ⦄ := by
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
  have nSetTCB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUSetTCB])
  have nWriteRegisters := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteRegisters])
  have nFlushTLB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUFlushTLB])
  have nReadVMCS := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUReadVMCS])
  have nWriteVMCS := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteVMCS])
  have nReadVMCB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUReadVMCB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUReadVMCB])
  have nWriteVMCB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteVMCB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteVMCB])
  have nReadMSR := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUReadMSR
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUReadMSR])
  have nWriteMSR := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteMSR
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteMSR])
  have nEnableIOPort := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUEnableIOPort
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUEnableIOPort])
  simp only [if_neg nSetTCB, if_neg nWriteRegisters, if_neg nFlushTLB, if_neg nReadVMCS, if_neg nWriteVMCS,
    if_neg nReadVMCB, if_neg nWriteVMCB, if_neg nReadMSR, if_neg nWriteMSR, if_neg nEnableIOPort,
    eq_self_iff_true, ↓reduceIte, if_neg h2, if_neg g2, lift, bind_ok, nEnableIOPort, not_false_eq_true,
    decide_true]
  have hf0 : ∀ args : List Fl4Spec.Data, VArgs st s ct buf len args → args.getD 0 0 = f.bv :=
    fun args hA => hA.a0 (by omega) hf
  have hx1 : ∀ args : List Fl4Spec.Data, VArgs st s ct buf len args → args.getD 1 0 = x.bv :=
    fun args hA => hA.a1 (by omega) hx
  by_cases hlh : (f &&& 65535#u64) > (x &&& 65535#u64)
  · have hgt : f.bv &&& 0xffff > x.bv &&& 0xffff := by
      rw [← zv_mask_bv, ← zv_mask_bv]; exact (Sched.gt_bv _ _).1 hlh
    simp only [if_pos hlh, error.invalid_arg, bind_ok, WP.spec_ok]
    exact ⟨ct, hct, fun args ec hA _ => Or.inl ⟨_, .invalidArgument 0, rfl, rfl, by
      rw [zv_dio_bv, zv_decode_dio_inv hvk (by rw [hA.1]; exact hlen) (hf0 args hA) (hx1 args hA) hgt],
      rfl, J1⟩⟩
  · have hle : ¬ f.bv &&& 0xffff > x.bv &&& 0xffff := by
      rw [← zv_mask_bv, ← zv_mask_bv]; exact fun h => hlh ((Sched.gt_bv _ _).2 h)
    rw [if_neg hlh]
    unfold vcpu.ports
    have hlo : (f &&& 65535#u64).val ≤ (x &&& 65535#u64).val := by
      have := fun h => hlh ((gt_iff_lt).2 h); scalar_tac
    have J1' : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a1
        (Notif.updK σ p.bv (.archObj (.vcpu (vsIoLt vs (f &&& 65535#u64).val (f &&& 65535#u64).val true)))) := by
      rw [vsIoLt_self, v3_updK_self hk]; exact J1
    refine WP.spec_bind (J1'.portsLoopJ hvk hp (zv_mask_lt x) true hk _ s (f &&& 65535#u64) le_rfl
      (by omega)) fun s6 J6 => ?_
    obtain ⟨s7, h7, -⟩ := P1.spec_ex_fd
      (P0.sched.set_thread_state.p0 st s6 ct sched.TS_RESTART (P1.LawfulStore.total (st := st)))
    rw [h7, bind_ok, WP.spec_ok]
    have eP : vsIoLt vs (f &&& 65535#u64).val ((x &&& 65535#u64).val + 1) true =
        vs.setPorts (f.bv &&& 0xffff) (x.bv &&& 0xffff) true :=
      vsIoLt_setPorts vs true (by rw [← zv_mask_bv, UScalar.bv_toNat]) (by rw [← zv_mask_bv, UScalar.bv_toNat])
    rw [eP] at J6
    exact ⟨ct, hct, fun args ec hA _ => Or.inr ⟨.disableIoPort p.bv (f.bv &&& 0xffff) (x.bv &&& 0xffff), [], s6, _,
      Ac, Lst, rfl,
      by rw [zv_dio_bv, zv_decode_dio_ok hvk (by rw [hA.1]; exact hlen) (hf0 args hA) (hx1 args hA) hle],
      zv_perform_dio hk _ _, J6, Or.inl ⟨rfl, h7⟩⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **`VcpuNyp3`'s `disableIoPort` field, proved** (module docstring). -/
theorem vcpuNyp_dio {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} :
    VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUDisableIOPort (fun _ _ => True)
      (Fl4Spec.virtKind ≠ .svm) 2 := by
  intro hK _ hVA _ _ V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c hv hl J hp hk _ _
  exact WP.spec_mono (J.disableIoPortJ hK hVA hv hp hk hl call buf ex b c) fun r h => h.toC

end

end

end Fl4Proofs.P3

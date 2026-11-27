/-
P3 (line mmuAD, gen 38): **X86VCPUReadVMCB end to end at `JAtZV3`** — the extracted `vcpu.decode` at label
`X86VCPUReadVMCB` (vcpu.rs l. 935-977, the read side on SVM, `len ≥ 2`: `f & 7 != 0 || f >= END || value == 0 ||
value > 64 || value > (END - f) / 8` → `InvalidArgument 0`; with `call`, `lookup_ipc_buffer(true, ct)` and for
`i < value` the word at `off = f + 8 i` — 0 when `vmcb_hidden(off)`, the `REGS` word for `off = RAX`, else
`get(v, off)` — stored by `set_mr(ct, b, i, ·)`, then `BADGE := 0` and the message info of the count; always
`TS_RUNNING`) paired with the extended spec's `decodeVcpuInvocation` (`.readVmcb v f x` / `invalidArgument 0`) and
`performVcpuInvocationF (.readVmcb v f x)` (the `x` words `if Svm.hiddenRead o then 0 else vs.get virtKind (.vmcb o)`),
in `VDecPost` form (`P3/JAtZV3VDec`), tail (c).

* **`zv_vmcb_hidden`**: FL4's `vmcb_hidden` is `Svm.hiddenRead` (the same eleven offsets 0x040 0x048 0x058 0x098
  0x0a0 0x0b0 0x0c0 0x0e0 0x0f0 0x0f8 0x108).
* `rvW vs f i` (the spec's word `i`), `rvWs vs f n` (FL4's words, as `U64`); `zv_rvmcb_cond` (the spec's
  `invalidArgument` test on FL4's naturals).
* **`JAtZV3.rvmcbLoop`**: FL4's `decode_loop1` from word 0 is `vcpuReplyWsLoop` over `rvWs` — every word FL4 reads
  after earlier `set_mr`s is still the spec's (loop invariant: `JAtZV3` at the spec state after the words so far,
  gen 34's `setMrJ3`, the VCPU untouched there by `jMrSt_other`; the SVM relation `VcpuRelSvm.vmcb` / `.gpr 0`).
* Spec side: `zv_decode_rvmcb_inv`, `zv_decode_rvmcb_ok`, `zv_perform_rvmcb`.
* **`JAtZV3.readVmcbJ`**: the label at `JAtZV3`, SVM, `len ≥ 2`; FL4's store is unchanged up to the reply, `JAtZV3`
  holds there (`s' = s`), FL4's final state is `vcpuReplyWs s ct call (rvWs …)`. **`vcpuNyp_rvmcb`**: `VcpuNyp3`'s
  `readVmcb` field, proved.

Premises: [P] `ZvVirtAgree arI`, `ARKeep arI AR` (existing). No new premise; no existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VRvmcs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## `vmcb_hidden` -/

theorem zv_vmcb_hidden (o : U64) : vcpu.vmcb_hidden o = ok (Fl4Spec.Svm.hiddenRead o.bv) := by
  unfold vcpu.vmcb_hidden
  split
  all_goals first
    | (congr 1; done)
    | (congr 1; decide)
    | (congr 1
       symm
       by_contra hc
       have hc' : Fl4Spec.Svm.hiddenRead o.bv = true := by simpa using hc
       simp only [Fl4Spec.Svm.hiddenRead, Fl4Spec.Svm.hidden, Fl4Spec.Svm.hostCache, Bool.or_eq_true,
         decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc'
       rcases hc' with e | e | e | e | e | e | e | e | e | e | e
       all_goals first
         | exact absurd (VirtSanEq.u64_ext (y := 64#uscalar) e) (by assumption)
         | exact absurd (VirtSanEq.u64_ext (y := 72#uscalar) e) (by assumption)
         | exact absurd (VirtSanEq.u64_ext (y := 88#uscalar) e) (by assumption)
         | exact absurd (VirtSanEq.u64_ext (y := 152#uscalar) e) (by assumption)
         | exact absurd (VirtSanEq.u64_ext (y := 160#uscalar) e) (by assumption)
         | exact absurd (VirtSanEq.u64_ext (y := 176#uscalar) e) (by assumption)
         | exact absurd (VirtSanEq.u64_ext (y := 192#uscalar) e) (by assumption)
         | exact absurd (VirtSanEq.u64_ext (y := 224#uscalar) e) (by assumption)
         | exact absurd (VirtSanEq.u64_ext (y := 240#uscalar) e) (by assumption)
         | exact absurd (VirtSanEq.u64_ext (y := 248#uscalar) e) (by assumption)
         | exact absurd (VirtSanEq.u64_ext (y := 264#uscalar) e) (by assumption))

/-! ## The words -/

/-- The spec's ReadVMCB word `i` from `f` (module docstring). -/
def rvW (vs : Fl4Spec.VcpuState) (f : Fl4Spec.Word) (i : Nat) : Fl4Spec.Word :=
  if Fl4Spec.Svm.hiddenRead (f + BitVec.ofNat 64 (i * 8)) then 0
  else vs.get Fl4Spec.virtKind (.vmcb (f + BitVec.ofNat 64 (i * 8)))

/-- The `n` words as FL4 words (module docstring). -/
def rvWs (vs : Fl4Spec.VcpuState) (f : Fl4Spec.Word) (n : Nat) : List U64 :=
  (List.range n).map fun i => (⟨rvW vs f i⟩ : U64)

theorem rvWs_length (vs : Fl4Spec.VcpuState) (f : Fl4Spec.Word) (n : Nat) : (rvWs vs f n).length = n := by
  simp [rvWs]

theorem rvWs_bv (vs : Fl4Spec.VcpuState) (f : Fl4Spec.Word) (n : Nat) :
    (rvWs vs f n).map (·.bv) = (List.range n).map (rvW vs f) := by
  simp only [rvWs, List.map_map]; rfl

theorem rvWs_get (vs : Fl4Spec.VcpuState) (f : Fl4Spec.Word) {n i : Nat} (hi : i < n) :
    (rvWs vs f n)[i]'(by rw [rvWs_length]; exact hi) = ⟨rvW vs f i⟩ := by
  simp [rvWs]

theorem rvWs_take_succ (vs : Fl4Spec.VcpuState) (f : Fl4Spec.Word) {n i : Nat} (hi : i < n) :
    ((rvWs vs f n).take (i + 1)).map (·.bv) = ((rvWs vs f n).take i).map (·.bv) ++ [rvW vs f i] := by
  rw [List.take_succ, List.map_append]
  congr 1
  rw [List.getElem?_eq_getElem (by rw [rvWs_length]; exact hi), rvWs_get vs f hi]
  rfl

theorem vcpuReplyWsLoop_nil {S : Type} (st : machine.Store S) (ct b : U64) (s : S) (i n : U64) :
    vcpuReplyWsLoop st ct b s [] i n = ok (s, n) := rfl

theorem vcpuReplyWsLoop_cons {S : Type} (st : machine.Store S) (ct b : U64) (s : S) (w : U64) (ws : List U64)
    (i n : U64) :
    vcpuReplyWsLoop st ct b s (w :: ws) i n = (do
      let (n1, s1) ← msg.set_mr st s ct b i w
      let i2 ← i + 1#u64
      vcpuReplyWsLoop st ct b s1 ws i2 n1) := rfl

/-! ## The spec side -/

section
open Fl4Spec

theorem zv_decode_rvmcb_inv (hvk : virtKind = .svm) {args : List Data} (hl : 2 ≤ args.length) {f x : Word}
    (h0 : args.getD 0 0 = f) (h1 : args.getD 1 0 = x)
    (hc : f &&& 7 ≠ 0 ∨ f ≥ Svm.svmEnd ∨ x = 0 ∨ x > 64 ∨ x > (Svm.svmEnd - f) / 8) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 77 args v ec = NonDetE.throwError (.invalidArgument 0) := by
  have hn : ¬ args.length < 2 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_rvmcb]
  simp only [hvk, hn, h0, h1, hc, decide_true, not_true_eq_false, ↓reduceIte]

theorem zv_decode_rvmcb_ok (hvk : virtKind = .svm) {args : List Data} (hl : 2 ≤ args.length) {f x : Word}
    (h0 : args.getD 0 0 = f) (h1 : args.getD 1 0 = x)
    (hc : ¬ (f &&& 7 ≠ 0 ∨ f ≥ Svm.svmEnd ∨ x = 0 ∨ x > 64 ∨ x > (Svm.svmEnd - f) / 8)) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 77 args v ec = NonDetE.returnOk (.readVmcb v f x) := by
  have hn : ¬ args.length < 2 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_rvmcb]
  simp only [hvk, hn, h0, h1, hc, decide_true, not_true_eq_false, ↓reduceIte]

theorem zv_perform_rvmcb {σ : State Unit} {v : ObjRef} {vs : VcpuState}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (f n : Word) :
    performVcpuInvocationF (Z := Unit) (.readVmcb v f n) σ =
      ({((List.range n.toNat).map (rvW vs f), σ)}, False) := by
  show ((getVcpu (Z := Unit) v) >>= fun st => (pure ((List.range n.toNat).map fun i =>
    let o := f + BitVec.ofNat 64 (i * 8)
    if Svm.hiddenRead o then 0 else st.get virtKind (.vmcb o)) : SMonad Unit (List Data))) σ = _
  rw [Notif.nd_bind_one (zv_getVcpu_eq hk)]
  rfl

/-- The spec's `invalidArgument` test on FL4's naturals (module docstring). -/
theorem zv_rvmcb_cond (f x : U64) :
    (f.bv &&& 7 ≠ 0 ∨ f.bv ≥ Svm.svmEnd ∨ x.bv = 0 ∨ x.bv > 64 ∨ x.bv > (Svm.svmEnd - f.bv) / 8) ↔
      (f.val % 8 ≠ 0 ∨ 1768 ≤ f.val ∨ x.val = 0 ∨ 64 < x.val ∨ (1768 - f.val) / 8 < x.val) := by
  have hE : Svm.svmEnd.toNat = 1768 := by decide
  have hf : f.bv.toNat = f.val := rfl
  have hx : x.bv.toNat = x.val := rfl
  have hfl : f.val < 2 ^ 64 := f.hBounds
  have e1 : (f.bv &&& 7 = 0) ↔ f.val % 8 = 0 := by
    rw [BitVec.toNat_eq, BitVec.toNat_and, hf, show (7 : Word).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]; rfl
  have e2 : f.bv ≥ Svm.svmEnd ↔ 1768 ≤ f.val := by
    rw [ge_iff_le, BitVec.le_def, hE, hf]
  have e3 : x.bv = 0 ↔ x.val = 0 := by rw [BitVec.toNat_eq, hx]; rfl
  have e4 : x.bv > 64 ↔ 64 < x.val := by rw [gt_iff_lt, BitVec.lt_def, hx]; rfl
  by_cases hlt : f.val < 1768
  · have e5 : x.bv > (Svm.svmEnd - f.bv) / 8 ↔ (1768 - f.val) / 8 < x.val := by
      rw [gt_iff_lt, BitVec.lt_def, hx, BitVec.toNat_udiv, BitVec.toNat_sub, hE, hf]
      have : (2 ^ 64 - f.val + 1768) % 2 ^ 64 = 1768 - f.val := by omega
      rw [this]; rfl
    rw [e2, e3, e4, e5, ne_eq, e1]
  · constructor
    · intro _; exact Or.inr (Or.inl (by omega))
    · intro _; exact Or.inr (Or.inl (e2.2 (by omega)))

end

/-! ## The loop -/

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 16000000 in
/-- **FL4's word: the spec's word**, at a state where the VCPU relates to `vs` (module docstring). -/
theorem zv_rvmcb_word (hvk : Fl4Spec.virtKind = .svm) {p : U64} (hv : VFits p) {vs : Fl4Spec.VcpuState}
    {s1 : S} (R : Fl4Spec.VcpuRelSvm (vmemW (L.mem s1)) p.bv vs) {f i : U64} (hf8 : f.val % 8 = 0)
    (hfi : f.val + 8 * i.val < 1768) :
    (if Fl4Spec.Svm.hiddenRead (core.num.U64.wrapping_add f (core.num.U64.wrapping_mul i 8#u64)).bv then ok 0#u64
      else do
        let i2 ← vcpu.svm.RAX
        if core.num.U64.wrapping_add f (core.num.U64.wrapping_mul i 8#u64) = i2
        then vcpu.get st s1 p vcpu.REGS
        else vcpu.get st s1 p (core.num.U64.wrapping_add f (core.num.U64.wrapping_mul i 8#u64)))
      ⦃ val => val.bv = rvW vs f.bv i.val ⦄ := by
  set o := core.num.U64.wrapping_add f (core.num.U64.wrapping_mul i 8#u64) with ho
  have hov : o.val = f.val + i.val * 8 := by
    rw [ho]
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    omega
  have hob : o.bv = f.bv + BitVec.ofNat 64 (i.val * 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    show o.val = _
    rw [hov, show f.bv.toNat = f.val from rfl, Nat.mod_eq_of_lt (a := i.val * 8) (by omega)]
    omega
  have hW : rvW vs f.bv i.val = if Fl4Spec.Svm.hiddenRead o.bv then 0 else vs.get Fl4Spec.virtKind (.vmcb o.bv) := by
    rw [hob]; rfl
  rw [hW]
  by_cases hh : Fl4Spec.Svm.hiddenRead o.bv = true
  · rw [if_pos hh, if_pos hh, WP.spec_ok]; rfl
  · rw [if_neg hh, if_neg hh, VirtVmcbTail.RAX_eq, bind_ok]
    have hl : (o.bv).toNat < 32768 := by show o.val < _; omega
    have h8 : (o.bv).toNat % 8 = 0 := by show o.val % 8 = 0; omega
    by_cases hr : o = 1528#u64
    · rw [if_pos hr]
      unfold vcpu.get
      simp only [lift, bind_ok]
      refine WP.spec_mono (P1.LawfulStore.read_spec s1 _) fun w hw => ?_
      subst hw
      have hrax : o.bv = Fl4Spec.Svm.rax := by rw [hr]; rfl
      have hc : vs.get Fl4Spec.virtKind (.vmcb o.bv) = vs.fields (.gpr 0) := by
        unfold Fl4Spec.VcpuState.get
        dsimp only [Fl4Spec.VField.canon]
        rw [if_pos ⟨hvk, hrax⟩]
      rw [hc, R.gpr 0]
      have hg : Fl4Spec.gprOff 0 = Fl4Spec.VcpuLay.REGS := by unfold Fl4Spec.gprOff; simp
      have ea : core.num.U64.wrapping_add p vcpu.REGS = ⟨p.bv + Fl4Spec.VcpuLay.REGS⟩ :=
        VirtSanEq.u64_ext (by rw [core.num.U64.wrapping_add_bv_eq, VirtVmcbTail.regs_bv])
      rw [hg, v3_vmemW_al hv (by simp [Fl4Spec.VcpuLay.REGS]) (by simp [Fl4Spec.VcpuLay.REGS]), ea]
    · rw [if_neg hr]
      unfold vcpu.get
      simp only [lift, bind_ok]
      refine WP.spec_mono (P1.LawfulStore.read_spec s1 _) fun w hw => ?_
      subst hw
      have hrax : o.bv ≠ Fl4Spec.Svm.rax := fun e => hr (VirtSanEq.u64_ext (by rw [e]; rfl))
      have hc : vs.get Fl4Spec.virtKind (.vmcb o.bv) = vs.fields (.vmcb o.bv) := by
        unfold Fl4Spec.VcpuState.get
        dsimp only [Fl4Spec.VField.canon]
        rw [if_neg (fun h : Fl4Spec.virtKind = .svm ∧ o.bv = Fl4Spec.Svm.rax => hrax h.2)]
      have hrd : Fl4Spec.Svm.readable o.bv = true := by
        unfold Fl4Spec.Svm.readable
        have a1 : o.bv &&& 7 = 0 := by
          rw [BitVec.toNat_eq, BitVec.toNat_and, show (7 : Fl4Spec.Word).toNat = 2 ^ 3 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod]
          show o.val % 8 = 0; omega
        have a2 : o.bv < Fl4Spec.Svm.svmEnd := by
          rw [BitVec.lt_def, show Fl4Spec.Svm.svmEnd.toNat = 1768 by decide]; show o.val < 1768; omega
        simp only [a1, a2, decide_true, Bool.and_self]
      have ea : core.num.U64.wrapping_add p o = ⟨p.bv + o.bv⟩ :=
        VirtSanEq.u64_ext (by rw [core.num.U64.wrapping_add_bv_eq])
      rw [hc, R.vmcb o.bv hrd (by simpa using hh) hrax, v3_vmemW_al hv hl h8, ea]

set_option maxHeartbeats 16000000 in
/-- **FL4's `decode_loop1` is `vcpuReplyWsLoop` over the spec's words** (module docstring). -/
theorem JAtZV3.rvmcbLoop (hvk : Fl4Spec.virtKind = .svm) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {ct : U64} (hct : ct ∈ Z.T) {x0 : Fl4Spec.Tcb}
    (hkx : σ.kheap ct.bv = some (.tcb x0)) {pb : Option Fl4Spec.ObjRef}
    (hq : ∀ q, pb = some q → Endp.ipcBufOf true x0 = some q) {b : U64} (hb : JBufR Z.B b pb) {f value : U64}
    (hf8 : f.val % 8 = 0) (hfv : f.val + 8 * value.val ≤ 1768) (hv64 : value.val ≤ 64)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) :
    vcpu.decode_loop1 st s p ct f value b 0#u64 0#u64 ⦃ r =>
      vcpuReplyWsLoop st ct b s (rvWs vs f.bv value.val) 0#u64 0#u64 = ok r ⦄ := by
  have hfv' := (J.z2.zv.base.jvLay J.z2.zv.vm).vfit p hp
  have hv : VFits p := ⟨hfv'.1, hfv'.2⟩
  have hpc : p.bv ≠ ct.bv := by
    intro e; rw [e, hkx] at hk; simp at hk
  have hwl : (rvWs vs f.bv value.val).length = value.val := rvWs_length _ _ _
  unfold vcpu.decode_loop1
  apply loop.spec_decr_nat (measure := fun y : S × U64 × U64 => value.val - y.2.1.val)
    (inv := fun y => y.2.1.val ≤ value.val ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D y.1 a
        (jMrSt σ ct.bv x0 pb (((rvWs vs f.bv value.val).take y.2.1.val).map (·.bv))) ∧
      vcpuReplyWsLoop st ct b s (rvWs vs f.bv value.val) 0#u64 0#u64 = vcpuReplyWsLoop st ct b y.1 ((rvWs vs f.bv value.val).drop y.2.1.val) y.2.1 y.2.2)
  · rintro ⟨s1, i, n⟩ ⟨g1, J1, hE⟩
    simp only at g1 J1 hE ⊢
    unfold vcpu.decode_loop1.body
    by_cases hlt : i < value
    swap
    · rw [if_neg hlt, WP.spec_ok]
      have hvi : value.val ≤ i.val := by scalar_tac
      have : i.val = value.val := by omega
      show vcpuReplyWsLoop st ct b s (rvWs vs f.bv value.val) 0#u64 0#u64 = ok (s1, n)
      rw [hE, this, List.drop_eq_nil_of_le (le_of_eq hwl), vcpuReplyWsLoop_nil]
    rw [if_pos hlt]
    have hil : i.val < value.val := by scalar_tac
    simp only [lift, bind_ok]
    rw [zv_vmcb_hidden, bind_ok]
    have hk1 : (jMrSt σ ct.bv x0 pb (((rvWs vs f.bv value.val).take i.val).map (·.bv))).kheap p.bv = some (.archObj (.vcpu vs)) := by
      rw [jMrSt_other _ _ _ _ _ hpc, hk]
    have R : Fl4Spec.VcpuRelSvm (vmemW (L.mem s1)) p.bv vs := by
      have := J1.vr p hp vs hk1; rw [hvk] at this; exact this
    refine WP.spec_bind (zv_rvmcb_word hvk hv R hf8 (by omega)) fun val hval => ?_
    have hms : (((rvWs vs f.bv value.val).take i.val).map (·.bv)).length = i.val := by simp [hwl]; omega
    obtain ⟨r, hr, -⟩ := P1.spec_ex_fd (P0.msg.set_mr.p0 st s1 ct b i val (P1.LawfulStore.total (st := st)))
    have hJ := setMrJ3 J1 hct hq hb i (by rw [hms]) (by rw [hms]; omega) val
    rw [hr, WP.spec_ok] at hJ
    refine WP.spec_bind (Pₘ := fun r' => r' = r) (by rw [hr]; exact (WP.spec_ok _).2 rfl) ?_
    rintro ⟨n1, s2⟩ e
    subst e
    try simp only [uncurry_apply_pair]
    obtain ⟨i2, h2e, h2v⟩ := P1.spec_ex_fd (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h2e, bind_ok]
    try rw [WP.spec_ok]
    have hi2 : i2.val = i.val + 1 := by simpa using h2v
    have hw : (rvWs vs f.bv value.val)[i.val]'(by rw [hwl]; exact hil) = val := by
      rw [rvWs_get _ _ hil]; exact VirtSanEq.u64_ext hval.symm
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show i2.val ≤ value.val; omega
    · simp only at hJ
      rw [hi2, rvWs_take_succ _ _ hil]
      have e2 : mrUpd (((rvWs vs f.bv value.val).take i.val).map (·.bv)) i.val val.bv = ((rvWs vs f.bv value.val).take i.val).map (·.bv) ++ [val.bv] := by
        unfold mrUpd; rw [if_neg (by omega)]
      rw [e2] at hJ
      rw [← hval]; exact hJ
    · show vcpuReplyWsLoop st ct b s (rvWs vs f.bv value.val) 0#u64 0#u64 =
        vcpuReplyWsLoop st ct b s2 ((rvWs vs f.bv value.val).drop i2.val) i2 n1
      rw [hE, hi2, List.drop_eq_getElem_cons (by rw [hwl]; exact hil), hw, vcpuReplyWsLoop_cons, hr, bind_ok]
      show (do
          let i2' ← i + 1#u64
          vcpuReplyWsLoop st ct b s2 ((rvWs vs f.bv value.val).drop (i.val + 1)) i2' n1) =
        vcpuReplyWsLoop st ct b s2 ((rvWs vs f.bv value.val).drop (i.val + 1)) i2 n1
      rw [h2e, bind_ok]
    · show value.val - i2.val < value.val - i.val; omega
  · refine ⟨Nat.zero_le _, ?_, rfl⟩
    show JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ ct.bv x0 pb (((rvWs vs f.bv value.val).take 0).map (·.bv)))
    rw [List.take_zero, List.map_nil, jMrSt_nil hkx]
    exact J

end

/-! ## The invocation -/

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 16000000 in
/-- **X86VCPUReadVMCB at `JAtZV3`, SVM, `len ≥ 2`** (module docstring). -/
theorem JAtZV3.readVmcbJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind = .svm) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 2 ≤ len.val) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUReadVMCB len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUReadVMCB len p call buf b c r ⦄ := by
  have g0 : len > 0#u64 := by scalar_tac
  have g1 : len > 1#u64 := by scalar_tac
  have g2 : ¬ len < 2#u64 := by scalar_tac
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
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  have h2 : i = 2#u64 := hi2.2 hvk
  rw [hi, bind_ok]
  obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
  obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
  rw [if_pos g0, hf, bind_ok, if_pos g1, hx, bind_ok]
  have n73 := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUSetTCB])
  have n81 := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUWriteRegisters])
  have n76 := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUFlushTLB])
  have n74 := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUReadVMCS])
  have n75 := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUWriteVMCS])
  have n78 := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUWriteVMCB
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUWriteVMCB])
  simp only [if_neg n73, if_neg n81, if_neg n76, if_neg n74, if_neg n75, eq_self_iff_true, ↓reduceIte,
    if_pos h2, if_neg g2, if_neg n78, lift, bind_ok, VirtSanEq.ite_bne, VirtInitWalk.END_eq]
  have hf0 : ∀ args : List Fl4Spec.Data, VArgs st s ct buf len args → args.getD 0 0 = f.bv :=
    fun args hA => hA.a0 (by omega) hf
  have hx1 : ∀ args : List Fl4Spec.Data, VArgs st s ct buf len args → args.getD 1 0 = x.bv :=
    fun args hA => hA.a1 (by omega) hx
  -- the four `invalid_arg` checks
  have hand : (f &&& 7#u64).bv = (0#u64 : U64).bv ↔ f.val % 8 = 0 := by
    rw [UScalar.bv_and, BitVec.toNat_eq, BitVec.toNat_and, show (7#u64 : U64).bv.toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]; rfl
  have herr : (f.val % 8 ≠ 0 ∨ 1768 ≤ f.val ∨ x.val = 0 ∨ 64 < x.val ∨ (1768 - f.val) / 8 < x.val) →
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUReadVMCB len p call buf b c
        (.Err (.Sys (.InvalidArgument 0#u64)), s, a1) := fun hC =>
    ⟨ct, hct, fun args ec hA _ => Or.inl ⟨_, .invalidArgument 0, rfl, rfl, by
      rw [zv_rvmcb_bv, zv_decode_rvmcb_inv hvk (by rw [hA.1]; exact hlen) (hf0 args hA) (hx1 args hA)
        ((zv_rvmcb_cond f x).2 hC)], rfl, J1⟩⟩
  by_cases c1 : f.val % 8 = 0
  swap
  · rw [if_neg (fun h => c1 (hand.1 h))]
    simp only [error.invalid_arg, bind_ok, WP.spec_ok]
    exact herr (Or.inl c1)
  rw [if_pos (hand.2 c1)]
  by_cases c2 : 1768 ≤ f.val
  · rw [if_pos (show f >= 1768#u64 by scalar_tac)]
    simp only [error.invalid_arg, bind_ok, WP.spec_ok]
    exact herr (Or.inr (Or.inl c2))
  rw [if_neg (show ¬ f >= 1768#u64 by scalar_tac)]
  by_cases c3 : x.val = 0
  · rw [if_pos (show x = 0#u64 by scalar_tac)]
    simp only [error.invalid_arg, bind_ok, WP.spec_ok]
    exact herr (Or.inr (Or.inr (Or.inl c3)))
  rw [if_neg (show ¬ x = 0#u64 by scalar_tac)]
  by_cases c4 : 64 < x.val
  · rw [if_pos (show x > 64#u64 by scalar_tac)]
    simp only [error.invalid_arg, bind_ok, WP.spec_ok]
    exact herr (Or.inr (Or.inr (Or.inr (Or.inl c4))))
  rw [if_neg (show ¬ x > 64#u64 by scalar_tac)]
  obtain ⟨i3, h3e, h3v⟩ := P1.spec_ex_fd (U64.sub_spec (x := 1768#u64) (y := f) (by scalar_tac))
  rw [h3e, bind_ok]
  obtain ⟨i4, h4e, h4v⟩ := P1.spec_ex_fd (U64.div_spec (x := i3) (y := 8#u64) (by scalar_tac))
  rw [h4e, bind_ok]
  have hi4 : i4.val = (1768 - f.val) / 8 := by
    have a : i3.val = 1768 - f.val := by have := h3v; simp at this; omega
    have b' : i4.val = i3.val / 8 := by have := h4v; simp at this; omega
    rw [b', a]
  by_cases c5 : (1768 - f.val) / 8 < x.val
  · rw [if_pos (show x > i4 by scalar_tac)]
    simp only [error.invalid_arg, bind_ok, WP.spec_ok]
    exact herr (Or.inr (Or.inr (Or.inr (Or.inr c5))))
  rw [if_neg (show ¬ x > i4 by scalar_tac)]
  -- the words
  have hC : ¬ (f.bv &&& 7 ≠ 0 ∨ f.bv ≥ Fl4Spec.Svm.svmEnd ∨ x.bv = 0 ∨ x.bv > 64 ∨
      x.bv > (Fl4Spec.Svm.svmEnd - f.bv) / 8) := fun h => by
    rcases (zv_rvmcb_cond f x).1 h with h | h | h | h | h <;> omega
  have hx8 : f.val + 8 * x.val ≤ 1768 := by omega
  have hP : Fl4Spec.performVcpuInvocationF (Z := Unit) (.readVmcb p.bv f.bv x.bv) σ =
      ({((rvWs vs f.bv x.val).map (·.bv), σ)}, False) := by
    rw [zv_perform_rvmcb hk, rvWs_bv]; rfl
  cases call with
  | false =>
    rw [if_neg (by simp)]
    obtain ⟨s2, h2s, -⟩ := P1.spec_ex_fd
      (P0.sched.set_thread_state.p0 st s ct sched.TS_RUNNING (P1.LawfulStore.total (st := st)))
    rw [h2s, bind_ok, WP.spec_ok]
    refine ⟨ct, hct, fun args ec hA _ => Or.inr ⟨.readVmcb p.bv f.bv x.bv, _, s, σ, Ac, Lst, rfl, ?_, hP, J1,
      Or.inr (Or.inr ⟨rvWs vs f.bv x.val, rfl, ?_⟩)⟩⟩
    · rw [zv_rvmcb_bv, zv_decode_rvmcb_ok hvk (by rw [hA.1]; exact hlen) (hf0 args hA) (hx1 args hA) hC]
    · unfold vcpuReplyWs; rw [if_neg (by simp)]; exact h2s
  | true =>
    rw [if_pos rfl]
    have hcth : Z.th ct = some .tcb := B.thTcb hctT
    obtain ⟨x0, hkx, hwr⟩ := B.buf ct hctT
    have hBC := bufCover_of_frameCover (T := Z.T) B.bok B.fcov
    obtain ⟨bw, hbw, -⟩ := P1.spec_ex_fd (P0.msg.lookup_ipc_buffer.p0 st s true ct (P1.LawfulStore.total (st := st)))
    have hb0 := Endp.lookup_buf_full s σ B.xtop.rel.2.1.1 B.xtop.rel.2.1.2.1 hcth hkx B.bok true
    rw [hbw, WP.spec_ok] at hb0
    have hb : JBufR Z.B bw (Endp.ipcBufOf true x0) := by
      obtain ⟨hrw0, hrwp⟩ := hb0
      cases hrb : Endp.ipcBufOf true x0 with
      | none => exact hrw0.2 hrb
      | some rp =>
        have hrwv : bw.bv = rp := hrwp hwr rp hrb
        exact ⟨(fun e => by have := hrw0.1 e; rw [hrb] at this; cases this),
          hBC ct hctT x0 true rp hkx hrb bw hrwv, hrwv⟩
    rw [hbw, bind_ok]
    refine WP.spec_bind (J1.rvmcbLoop hvk hp hk hctT hkx (fun q h => h) hb c1 hx8 (by omega)) ?_
    rintro ⟨s2, n⟩ hL
    try simp only [uncurry_apply_pair]
    obtain ⟨s3, h3s, -⟩ := P1.spec_ex_fd
      (P0.obj.Tcb.set_reg.p0 st ct s2 layout.reg.BADGE 0#u64 (P1.LawfulStore.total (st := st)))
    rw [h3s, bind_ok]
    obtain ⟨mi, hmi, -⟩ := P1.spec_ex_fd (P0.msginfo.MessageInfo.new.p0 0#u64 0#u64 0#u64 n)
    rw [hmi, bind_ok]
    obtain ⟨s4, h4s, -⟩ := P1.spec_ex_fd
      (P0.msg.set_msg_info.p0 st s3 ct mi (P1.LawfulStore.total (st := st)))
    rw [h4s, bind_ok]
    obtain ⟨s5, h5s, -⟩ := P1.spec_ex_fd
      (P0.sched.set_thread_state.p0 st s4 ct sched.TS_RUNNING (P1.LawfulStore.total (st := st)))
    rw [h5s, bind_ok, WP.spec_ok]
    refine ⟨ct, hct, fun args ec hA _ => Or.inr ⟨.readVmcb p.bv f.bv x.bv, _, s, σ, Ac, Lst, rfl, ?_, hP, J1,
      Or.inr (Or.inr ⟨rvWs vs f.bv x.val, rfl, ?_⟩)⟩⟩
    · rw [zv_rvmcb_bv, zv_decode_rvmcb_ok hvk (by rw [hA.1]; exact hlen) (hf0 args hA) (hx1 args hA) hC]
    · show vcpuReplyWs st s ct true (rvWs vs f.bv x.val) = ok s5
      unfold vcpuReplyWs
      rw [if_pos rfl, hbw, bind_ok, hL, bind_ok]
      show (do
          let s3 ← obj.Tcb.set_reg st ct s2 layout.reg.BADGE 0#u64
          let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
          let s4 ← msg.set_msg_info st s3 ct mi
          sched.set_thread_state st s4 ct sched.TS_RUNNING) = ok s5
      rw [h3s, bind_ok, hmi, bind_ok, h4s, bind_ok, h5s]

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **`VcpuNyp3`'s `readVmcb` field, proved** (module docstring). -/
theorem vcpuNyp_rvmcb {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} :
    VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUReadVMCB (fun _ _ => True)
      (Fl4Spec.virtKind = .svm) 2 := by
  intro hK _ hVA _ _ V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c hv hl J hp hk _ _
  exact WP.spec_mono (J.readVmcbJ hK hVA hv hp hk hl call buf ex b c) fun r h => h.toC

end

end

end Fl4Proofs.P3

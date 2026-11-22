/-
P3 (DESIGN.md §9): **`ReplyHypMX.fail` for the composite relation**: FL4's
error reply (`reply_error`: the badge register, `error_mrs`, the debug word
of `KERNEL_INVOCATION_REPORT_ERROR_IPC`, the message info) against the
spec's `fl4ReplyFromKernelError true` (Ext/ReplyError), keeping `RX`
(ReplyTopX.lean).

* `BufPlaced` (BufPlaced.lean): the named placement of the IPC-buffer words
  `B` the reply writes.
* `bufw_top`, `bufw_inv`: a write to a buffer word keeps `TopSR` and `RInv`,
  with the spec's store to the matching user word.
-/
import Fl4Proofs.P3.ReplyTopX
import Fl4Proofs.P3.BufPlaced
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- The notification footprint's TCB words lie in the TCB. -/
theorem nfoot_tcb_range {t a : U64} (ht : TcbAddr t)
    (h : a = Notif.tStA t ∨ a = Notif.tBlockA t ∨ a = Notif.badgeRegA t ∨ a = prioA t ∨ a = nextA .Ep t ∨ a = prevA .Ep t) :
    t.val ≤ a.val ∧ a.val < t.val + 4096 := by
  have hb := Endp.regA_val ht (Endp.regIdx_lt Fl4Spec.badge_register)
  have hbi := Endp.regIdx_lt Fl4Spec.badge_register
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Endp.val_st ht]; omega
  · rw [Endp.val_blk ht]; omega
  · rw [Endp.badgeRegA_eq_regA, hb]; omega
  · rw [Endp.val_prio ht]; omega
  · rw [Endp.val_next ht]; omega
  · rw [Endp.val_prev ht]; omega

set_option maxHeartbeats 4000000 in
/-- **A write to an IPC-buffer word** for the composite relation, with the
spec's store to the matching user word. -/
theorem bufw_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hBP : BufPlaced (L := L) N C B c s σ) {wp : U64 × Fl4Spec.Word} (hw : wp ∈ B) (v : U64) :
    VsRel P (L.mem (L.wr s wp.1 v)) (L.ksb (L.wr s wp.1 v))
        (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv)) ∧
      (PtRel L4 L3 L2 L1 (L.mem s) σ →
        PtRel L4 L3 L2 L1 (L.mem (L.wr s wp.1 v)) (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv))) ∧
      TopSR st th P L4 L3 L2 L1 N T C E R B c AR (L.wr s wp.1 v) a
        (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv)) ∧
      L.ksb (L.wr s wp.1 v) = L.ksb s ∧
      ∀ b, Aligned b → VObj th P L4 L3 L2 L1 (L.ksb s) b → L.mem (L.wr s wp.1 v) b = L.mem s b := by
  obtain ⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩ := hS
  obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
  have hN := hc.node
  have hal : Aligned wp.1 := (hP.ep.balign wp hw).1
  set σ1 := Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv) with hσ1
  have hO1 : OObj st N T C E R B c s σ wp.1 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩))))))
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
  have hfar := hBP.far wp hw
  have hksb : L.ksb (L.wr s wp.1 v) = L.ksb s := L.ksb_wr _ _ _
  have hmem : ∀ b, Aligned b → b.val ≠ wp.1.val → L.mem (L.wr s wp.1 v) b = L.mem s b :=
    fun b hb h => L.mem_wr_ne hal hb (Ne.symm h)
  have hmV : ∀ b, Aligned b → VObj th P L4 L3 L2 L1 (L.ksb s) b → L.mem (L.wr s wp.1 v) b = L.mem s b :=
    fun b hb hv => hmem b hb (fun e => hP.disj _ hO1 (UScalar.eq_of_val_eq e ▸ hv))
  have hmK : ∀ b : U64, Aligned b → (L.ksb s).val ≤ b.val → b.val < (L.ksb s).val + 13568 →
      L.mem (L.wr s wp.1 v) b = L.mem s b :=
    fun b hb h1 h2 => hmem b hb (fun e => by rw [e] at h1 h2; omega)
  have hVs : VsRel P (L.mem (L.wr s wp.1 v)) (L.ksb (L.wr s wp.1 v)) σ1 := by
    rw [hksb]
    exact hR.frame (fun b hb => hmV b (VsWrite.aligned hP.vs hb) (vsWrite_vobj hP.vs hb)) rfl (fun _ _ => rfl)
  have hPt' : PtRel L4 L3 L2 L1 (L.mem s) σ → PtRel L4 L3 L2 L1 (L.mem (L.wr s wp.1 v)) σ1 := fun hPt => by
    refine hPt.frame (fun b hb => hmV b (PtWAll.aligned hP.pt hb) ?_) (fun _ _ => rfl)
    obtain ⟨q, hq, i, hi, rfl⟩ := hb
    exact table_vobj hP.pt hq hi _
  -- the scheduler relation: the word is far from what it reads
  have hS1 : Sched.SchedRel st N T C c (L.wr s wp.1 v) σ := by
    refine hSch.wr_far hal ⟨by simp only [LawfulStore.nodeBase] at hfar ⊢; exact hfar,
      fun t ht => by
        have := hP.ep.bt wp hw t ht; have := (hc.tcbs t ht).align; have := (hP.ep.balign wp hw).1; omega,
      fun sc hsc x n hk => hBP.sc wp hw sc hsc x n hk⟩ v
  have hS' : Sched.SchedRel st N T C c (L.wr s wp.1 v) σ1 :=
    hS1.spec_congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hEp' := hEp.upd_buf hP.ep hw v (fun b hb h => hmem b hb h) (Notif.rd_wr_eq hal)
  have hNt' : Notif.NtfnStateRel N T (L.mem (L.wr s wp.1 v)) σ1 := by
    refine hNt.frame hSch.placed (fun b hb hf => hmem b hb ?_) ⟨fun _ _ h => h, fun _ x h => ⟨x, h, rfl, rfl, rfl⟩⟩
    rcases hf with ⟨n, hn, h1, h2⟩ | ⟨t, ht, ht'⟩
    · have := hBP.ntfn wp hw n hn; omega
    · have := nfoot_tcb_range (hSch.placed.tcb t ht) ht'
      have := hP.ep.bt wp hw t ht; omega
  have hKr' : KRootRel (L.mem (L.wr s wp.1 v)) (L.ksb (L.wr s wp.1 v)) σ1 := by
    refine ⟨?_, ?_⟩
    · have hKr := hKr.1
      unfold KRootW globCr3 at hKr ⊢
      have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
        unfold layout.ks.KERNEL_ROOT
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      rw [hksb, hmK _ (by unfold Aligned; rw [hkv]; omega) (by rw [hkv]; omega) (by rw [hkv]; omega)]
      exact hKr
    · rw [hksb]
      have hfv := feat_val hkf
      exact HugeRel.frame hKr.2 (hmK _ (by unfold Aligned; rw [hfv]; omega) (by rw [hfv]; omega) (by rw [hfv]; omega)) rfl
  refine ⟨hVs, hPt', ⟨⟨hS', hEp', hNt', ?_, ?_, hKr', hAr⟩, ?_⟩, hksb, hmV⟩
  · rw [hksb]; exact IrqRel.ksFrame hIrq hkf hka (fun b hb h1 h2 _ => hmK b hb h1 h2) rfl rfl
  · rw [hksb]; exact IoRel.ksFrame hIo hkf hka (fun b hb h1 h2 _ => hmK b hb h1 h2) rfl
  · refine ⟨hP.ep, by rw [hksb]; exact hP.vs, hP.pt, hP.pl, fun y hy => ?_, fun y h1 h2 => ?_, hP.po, hP.ps,
      by rw [hksb]; exact hP.pv, by rw [hksb]; exact hP.vo, by rw [hksb]; exact hP.sd, by rw [hksb]; exact hP.tko⟩
    · rw [hksb]
      exact hP.disj y (OObj.of_kh hksb (fun q z n hq => hq) hy)
    · have : L.nodeBase (L.wr s wp.1 v) c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hksb]
      rw [this] at h1 h2; exact hP.nodeE y h1 h2

/-- **A write to an IPC-buffer word keeps `RInv`.** -/
theorem bufw_inv {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a σ)
    (hBP : BufPlaced (L := L) N C B c s σ) {wp : U64 × Fl4Spec.Word} (hw : wp ∈ B) (v : U64) :
    RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G (L.wr s wp.1 v) a
      (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv)) := by
  obtain ⟨hCR, hFI, hMO, hDom, hS, hR, hPt, hPI, hCur⟩ := hI
  obtain ⟨hR', hPt', hS', hksb, hmV⟩ := bufw_top s a σ hS hR hBP hw v
  have hal : Aligned wp.1 := (hS.2.ep.balign wp hw).1
  have hO1 : OObj st N T C E R B c s σ wp.1 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩))))))
  have hSS : SlotsSame th (L.mem s) (L.mem (L.wr s wp.1 v)) := by
    refine slotsSame_wr hS.2.pl s v hal (fun x hx ⟨h1, h2⟩ => ?_)
    exact hS.2.disj _ hO1 (vobj_of_slot hS.2.pl P L4 L3 L2 L1 (L.ksb s) hx h1 h2)
  have hK0 : KFoot σ (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv)) :=
    ⟨rfl, rfl, fun o h => absurd rfl h, rfl⟩
  have hSt : StateRel th (L.mem (L.wr s wp.1 v))
      (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv)) :=
    (⟨hCR.1.cnode, hCR.1.tcb⟩ : StateRel th (L.mem s)
      (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv))).of_caps (fun y hy => hSS.capAt hy)
  obtain ⟨hCR', hFI', hMO'⟩ := cspace_step hCR hFI hMO hSS hK0 hSt
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hS.2.vs.ksb_fit; omega
  have hka := hS.2.vs.ksb_al
  have hfar := hBP.far wp hw
  have hDom' : DomRel (L.mem (L.wr s wp.1 v)) (L.ksb s)
      (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv)) :=
    hDom.of_same (domSame_low hkf hka fun b hb h1 h2 =>
      L.mem_wr_ne hal hb (fun e => by
        have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
        rw [← e] at h1 h2; omega)) rfl rfl
  refine ⟨hCR', hFI', by rw [hksb]; exact hMO', by rw [hksb]; exact hDom', hS', hR', hPt' hPt, ?_,
    CurOK.of_same hCur hSS rfl⟩
  intro q hq lo hl
  have hw' : VsWrite P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
  rw [hmV _ (hw'.aligned hS.2.vs) (vsWrite_vobj hS.2.vs hw')]
  exact hPI q hq lo hl

/-! ### The message registers -/

/-- The spec's state after `set_mrs t buf ms` from `σ0`. -/
def MrS (σ0 : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) :
    Option Fl4Spec.ObjRef → List Fl4Spec.Word → Fl4Spec.State Unit
  | some p, ms => Endp.mrState σ0 t x p ms
  | none, ms => Endp.mrStateN σ0 t x ms

theorem MrS_kheap_t (σ0 : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (buf : Option Fl4Spec.ObjRef)
    (ms : List Fl4Spec.Word) :
    (MrS σ0 t x buf ms).kheap t = some (.tcb (Endp.withRegs x (Endp.mrRegs x.tcbArch.tcbContext.userRegs ms))) := by
  cases buf <;> simp [MrS, Endp.mrState, Endp.mrStateN, Endp.setUm]

theorem MrS_kheap_ne (σ0 : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (buf : Option Fl4Spec.ObjRef)
    (ms : List Fl4Spec.Word) {q : Fl4Spec.ObjRef} (hq : q ≠ t) : (MrS σ0 t x buf ms).kheap q = σ0.kheap q := by
  cases buf <;> simp [MrS, Endp.mrState, Endp.mrStateN, Endp.setUm, hq]

theorem MrS_cur (σ0 : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (buf : Option Fl4Spec.ObjRef)
    (ms : List Fl4Spec.Word) : (MrS σ0 t x buf ms).curThread = σ0.curThread := by
  cases buf <;> rfl

/-- The SC objects of `MrS` are `σ0`'s (the TCB at `t` is one). -/
theorem MrS_sc {σ0 : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb} (hk : σ0.kheap t = some (.tcb x))
    (buf : Option Fl4Spec.ObjRef) (ms : List Fl4Spec.Word) :
    ∀ q y n, (MrS σ0 t x buf ms).kheap q = some (.schedContext y n) → σ0.kheap q = some (.schedContext y n) := by
  intro q y n hq
  by_cases e : q = t
  · subst e; rw [MrS_kheap_t] at hq; cases hq
  · rwa [MrS_kheap_ne _ _ _ _ _ e] at hq

/-- The length `set_mrs` returns, as FL4 counts. -/
def mrLen (buf : Option Fl4Spec.ObjRef) (n : Nat) : Nat :=
  match buf with
  | some _ => n
  | none => min 4 n

set_option maxHeartbeats 4000000 in
/-- **`set_mr` of the next message word keeps `RInv`**, the spec's `set_mrs`
state growing by the word. -/
theorem setmr_inv {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (σ0 : Fl4Spec.State Unit)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ0.curThread) {x0 : Fl4Spec.Tcb}
    (hk0 : σ0.kheap ct.bv = some (.tcb x0))
    (buf : Option Fl4Spec.ObjRef) (w : U64) (hw0 : w = 0#u64 ↔ buf = none)
    (hbm : ∀ p, buf = some p → Endp.BufMap B w p)
    (s : S) (a : A) (ms : List Fl4Spec.Word)
    (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 buf ms))
    (hBP : BufPlaced (L := L) N C B c s σ0) (i : U64) (hi : i.val = ms.length) (hi' : ms.length < 120)
    (v : U64) :
    msg.set_mr st s ct w i v ⦃ r => r.1.val = mrLen buf (ms.length + 1) ∧
      RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G r.2 a (MrS σ0 ct.bv x0 buf (ms ++ [v.bv])) ∧
      L.ksb r.2 = L.ksb s ∧ L.cpu r.2 = L.cpu s ⦄ := by
  have hkx := MrS_kheap_t σ0 ct.bv x0 buf ms
  have hcurM : ct.bv = (MrS σ0 ct.bv x0 buf ms).curThread := by rw [MrS_cur]; exact hcur
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  unfold msg.set_mr
  by_cases h4 : i < msg.N_MSG_REGISTERS
  · have hi4 : i.val < 4 := by have := (gt_iff_val).1 h4; omega
    simp only [h4, ↓reduceIte]
    refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
    rintro r rfl
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct _ v) ?_
    rintro s1 rfl
    simp only [lift, bind_ok, WP.spec_ok]
    have hI1 := regw_inv s a _ hI ct htcb hcurM hkx (Endp.mrIdx i.val) v
    refine ⟨?_, ?_, L.ksb_wr _ _ _, L.cpu_wr _ _ _⟩
    · have : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      rw [this, hi]; cases buf <;> simp [mrLen] <;> omega
    · cases buf with
      | none =>
        have e := Endp.mrStateN_snoc_lt σ0 ct.bv x0 ms v.bv i.val hi (by omega)
        simp only [MrS] at hI1 ⊢; rw [← e]; exact hI1
      | some p =>
        have e := Endp.mrState_snoc_lt σ0 ct.bv x0 p ms v.bv i.val hi (by omega)
        simp only [MrS] at hI1 ⊢; rw [← e]; exact hI1
  · have hi4 : 4 ≤ i.val := by
      have : ¬ i.val < 4 := fun h => h4 ((gt_iff_val).2 (by rw [hN]; exact h)); omega
    rw [if_neg h4]
    cases buf with
    | none =>
      have hw : w = 0#u64 := hw0.2 rfl
      simp only [hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨by rw [hN]; simp [mrLen]; omega, ?_, by first | rfl | trivial, by first | rfl | trivial⟩
      simp only [MrS] at hI ⊢
      rw [Endp.mrStateN_append_ge _ _ _ _ _ (by omega)]; exact hI
    | some p =>
      have hw : w ≠ 0#u64 := fun h => by cases hw0.1 h
      have hb : (w != 0#u64) = true := by simp [hw]
      simp only [hb, ↓reduceIte]
      unfold lift
      apply Endp.ok_bind_spec
      refine WP.spec_bind (Endp.msg.buf_set.spec s w _ v) ?_
      rintro s1 rfl
      have hiv : (core.num.U64.wrapping_add i 1#u64).val = ms.length + 1 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have hwB := hbm p rfl (core.num.U64.wrapping_add i 1#u64) (by omega)
      have hBP' : BufPlaced (L := L) N C B c s (MrS σ0 ct.bv x0 (some p) ms) :=
        hBP.mono rfl (MrS_sc hk0 _ _)
      have hI1 := bufw_inv s a _ hI hBP' hwB v
      simp only [lift, bind_ok, WP.spec_ok]
      refine ⟨by rw [hiv]; simp [mrLen], ?_, L.ksb_wr _ _ _, L.cpu_wr _ _ _⟩
      simp only [hiv] at hI1
      simp only [MrS] at hI1 ⊢
      rw [← Endp.mrState_snoc_ge _ _ _ _ _ _ (by omega) hi']
      exact hI1

/-! ### The error message -/

theorem ofNat_val (x : U64) : BitVec.ofNat 64 x.val = x.bv := BitVec.eq_of_toNat_eq (by simp)

section ErrMrs
variable {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (σ0 : Fl4Spec.State Unit)
  (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ0.curThread) {x0 : Fl4Spec.Tcb}
  (hk0 : σ0.kheap ct.bv = some (.tcb x0))
  (buf : Option Fl4Spec.ObjRef) (w : U64) (hw0 : w = 0#u64 ↔ buf = none)
  (hbm : ∀ p, buf = some p → Endp.BufMap B w p) (a : A)

include htcb hcur hk0 hw0 hbm in
set_option maxHeartbeats 4000000 in
/-- **`set_mrs_lookup_failure_at` from MR 1** keeps `RInv`: the words of
`msg_from_lookup_failure` (a guard found within its size). -/
theorem setmrs_lf_inv (s : S) (ms : List Fl4Spec.Word) (hms : ms.length = 1)
    (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 buf ms))
    (hBP : BufPlaced (L := L) N C B c s σ0) (lf : error.LookupFault) (lf' : Fl4Spec.LookupFailure)
    (hlf : LookupFaultRel lf lf')
    (hG : ∀ g l gs, lf = .GuardMismatch g l gs → g.val < 2 ^ gs.val) :
    faults.set_mrs_lookup_failure_at st s ct w lf 1#u64 ⦃ r =>
      r.1.val = mrLen buf (ms ++ Fl4Spec.msgFromLookupFailure lf').length ∧
      RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G r.2 a
        (MrS σ0 ct.bv x0 buf (ms ++ Fl4Spec.msgFromLookupFailure lf')) ∧ L.ksb r.2 = L.ksb s ∧ L.cpu r.2 = L.cpu s ⦄ := by
  have step := fun (s1 : S) (ms1 : List Fl4Spec.Word) (hI1 : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s1 a
      (MrS σ0 ct.bv x0 buf ms1)) (hB1 : BufPlaced (L := L) N C B c s1 σ0) (i : U64) (hi : i.val = ms1.length)
      (hi' : ms1.length < 120) (v : U64) =>
    setmr_inv (L := L) σ0 ct htcb hcur hk0 buf w hw0 hbm s1 a ms1 hI1 hB1 i hi hi' v
  unfold faults.set_mrs_lookup_failure_at faults.set_mrs_lookup_failure
  cases lf with
  | InvalidRoot =>
    cases lf' <;> (try simp only [LookupFaultRel] at hlf)
    simp only [error.LookupFault.type_code, bind_ok]
    refine WP.spec_bind (step s ms hI hBP 1#u64 (by rw [hms]; rfl) (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨h1, h2, h3, h4⟩
    show (ok (i1, s1) : Result (U64 × S)) ⦃ _ ⦄
    rw [WP.spec_ok]
    have hl : ms ++ Fl4Spec.msgFromLookupFailure .invalidRoot = ms ++ [(fl4_abi.consts.lookup.InvalidRoot).bv] := by
      simp [Fl4Spec.msgFromLookupFailure, fl4_abi.consts.lookup.InvalidRoot]
    rw [hl]
    exact ⟨by rw [h1]; simp, h2, h3, h4⟩
  | MissingCapability bl =>
    cases lf' <;> (try simp only [LookupFaultRel] at hlf)
    rename_i n
    simp only [error.LookupFault.type_code, bind_ok]
    refine WP.spec_bind (step s ms hI hBP 1#u64 (by rw [hms]; rfl) (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨-, h2, h3, h4⟩
    simp only [lift, bind_ok]
    have e2 : (core.num.U64.wrapping_add (1#u64 : U64) 1#u64).val = (ms ++ [(fl4_abi.consts.lookup.MissingCapability).bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_mono (step s1 _ h2 (hBP.mono h3 fun _ _ _ h => h) _ e2 (by simp [hms]) bl) ?_
    rintro ⟨i2, s2⟩ ⟨g1, g2, g3, g4⟩
    have hl : ms ++ Fl4Spec.msgFromLookupFailure (.missingCapability n) =
        ms ++ [(fl4_abi.consts.lookup.MissingCapability).bv] ++ [bl.bv] := by
      simp [Fl4Spec.msgFromLookupFailure, hlf, fl4_abi.consts.lookup.MissingCapability]
    rw [hl]
    exact ⟨by rw [g1]; simp, g2, g3.trans h3, g4.trans h4⟩
  | DepthMismatch found left =>
    cases lf' <;> (try simp only [LookupFaultRel] at hlf)
    rename_i n m
    simp only [error.LookupFault.type_code, bind_ok]
    refine WP.spec_bind (step s ms hI hBP 1#u64 (by rw [hms]; rfl) (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨-, h2, h3, h4⟩
    simp only [lift, bind_ok]
    have e2 : (core.num.U64.wrapping_add (1#u64 : U64) 1#u64).val = (ms ++ [(fl4_abi.consts.lookup.DepthMismatch).bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_bind (step s1 _ h2 (hBP.mono h3 fun _ _ _ h => h) _ e2 (by simp [hms]) left) ?_
    rintro ⟨i2, s2⟩ ⟨-, g2, g3, g4⟩
    have e3 : (core.num.U64.wrapping_add (1#u64 : U64) 2#u64).val =
        (ms ++ [(fl4_abi.consts.lookup.DepthMismatch).bv] ++ [left.bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_mono (step s2 _ g2 (hBP.mono (g3.trans h3) fun _ _ _ h => h) _ e3 (by simp [hms]) found) ?_
    rintro ⟨i3, s3⟩ ⟨k1, k2, k3, k4⟩
    have hl : ms ++ Fl4Spec.msgFromLookupFailure (.depthMismatch n m) =
        ms ++ [(fl4_abi.consts.lookup.DepthMismatch).bv] ++ [left.bv] ++ [found.bv] := by
      simp [Fl4Spec.msgFromLookupFailure, hlf.1, hlf.2, fl4_abi.consts.lookup.DepthMismatch]
    rw [hl]
    exact ⟨by rw [k1]; simp, k2, k3.trans (g3.trans h3), k4.trans (g4.trans h4)⟩
  | GuardMismatch g left gs =>
    cases lf' <;> (try simp only [LookupFaultRel] at hlf)
    rename_i n gl
    have hg := hG g left gs rfl
    simp only [error.LookupFault.type_code, bind_ok]
    refine WP.spec_bind (step s ms hI hBP 1#u64 (by rw [hms]; rfl) (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨-, h2, h3, h4⟩
    simp only [lift, bind_ok]
    have e2 : (core.num.U64.wrapping_add (1#u64 : U64) 1#u64).val = (ms ++ [(fl4_abi.consts.lookup.GuardMismatch).bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_bind (step s1 _ h2 (hBP.mono h3 fun _ _ _ h => h) _ e2 (by simp [hms]) left) ?_
    rintro ⟨i2, s2⟩ ⟨-, g2, g3, g4⟩
    have e3 : (core.num.U64.wrapping_add (1#u64 : U64) 2#u64).val =
        (ms ++ [(fl4_abi.consts.lookup.GuardMismatch).bv] ++ [left.bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_bind (step s2 _ g2 (hBP.mono (g3.trans h3) fun _ _ _ h => h) _ e3 (by simp [hms]) g) ?_
    rintro ⟨i3, s3⟩ ⟨-, k2, k3, k4⟩
    have e4 : (core.num.U64.wrapping_add (1#u64 : U64) 3#u64).val =
        (ms ++ [(fl4_abi.consts.lookup.GuardMismatch).bv] ++ [left.bv] ++ [g.bv]).length := by
      simp [hms, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    refine WP.spec_mono (step s3 _ k2 (hBP.mono (k3.trans (g3.trans h3)) fun _ _ _ h => h) _ e4 (by simp [hms]) gs) ?_
    rintro ⟨i4, s4⟩ ⟨j1, j2, j3, j4⟩
    have hgb : Fl4Spec.ofBl gl = g.bv := by
      rw [hlf.2.1, ofBl_bitsOf_eq, Nat.mod_eq_of_lt hg]; exact BitVec.eq_of_toNat_eq (by simp)
    have hgl : gl.length = gs.val := by rw [hlf.2.1, length_bitsOf]
    have hl : ms ++ Fl4Spec.msgFromLookupFailure (.guardMismatch n gl) =
        ms ++ [(fl4_abi.consts.lookup.GuardMismatch).bv] ++ [left.bv] ++ [g.bv] ++ [gs.bv] := by
      simp only [Fl4Spec.msgFromLookupFailure, hgb, hgl, hlf.1, List.append_assoc, List.cons_append,
        List.nil_append, fl4_abi.consts.lookup.GuardMismatch, ofNat_val]
      rfl
    rw [hl]
    exact ⟨by rw [j1]; simp, j2, j3.trans (k3.trans (g3.trans h3)), j4.trans (k4.trans (g4.trans h4))⟩

include htcb hcur hk0 hw0 hbm in
set_option maxHeartbeats 8000000 in
/-- **`error_mrs` keeps `RInv`**: the words of `msg_from_syscall_error`. -/
theorem error_mrs_inv (s : S)
    (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 buf []))
    (hBP : BufPlaced (L := L) N C B c s σ0) (e : error.SysError) (e' : Fl4Spec.SyscallError)
    (he : ErrRel (.Sys e) e')
    (hG : ∀ src g l gs, e = .FailedLookup src (.GuardMismatch g l gs) → g.val < 2 ^ gs.val) :
    syscall.error_mrs st s ct w e ⦃ r =>
      r.1.val = mrLen buf (Fl4Spec.msgFromSyscallError e').2.length ∧
      RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G r.2 a
        (MrS σ0 ct.bv x0 buf (Fl4Spec.msgFromSyscallError e').2) ∧ L.ksb r.2 = L.ksb s ∧ L.cpu r.2 = L.cpu s ⦄ := by
  have step := fun (s1 : S) (ms1 : List Fl4Spec.Word) (hI1 : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s1 a
      (MrS σ0 ct.bv x0 buf ms1)) (hB1 : BufPlaced (L := L) N C B c s1 σ0) (i : U64) (hi : i.val = ms1.length)
      (hi' : ms1.length < 120) (v : U64) =>
    setmr_inv (L := L) σ0 ct htcb hcur hk0 buf w hw0 hbm s1 a ms1 hI1 hB1 i hi hi' v
  have one : ∀ (v : U64) (ms : List Fl4Spec.Word), ms = [v.bv] →
      msg.set_mr st s ct w 0#u64 v ⦃ r => r.1.val = mrLen buf ms.length ∧
        RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G r.2 a (MrS σ0 ct.bv x0 buf ms) ∧ L.ksb r.2 = L.ksb s ∧ L.cpu r.2 = L.cpu s ⦄ := by
    rintro v ms rfl
    refine WP.spec_mono (step s [] hI hBP 0#u64 rfl (by simp) v) ?_
    rintro r ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  unfold syscall.error_mrs
  rcases he with h | ⟨n, he, rfl⟩
  swap
  · cases he
    exact one n _ (by simp [Fl4Spec.msgFromSyscallError, ofNat_val])
  cases e <;> cases e' <;> simp only [SysErrRel] at h
  case InvalidArgument.invalidArgument arg n =>
    exact one arg _ (by simp [Fl4Spec.msgFromSyscallError, h, ofNat_val])
  case IllegalOperation.illegalOperation =>
    rw [WP.spec_ok]; exact ⟨by cases buf <;> simp [Fl4Spec.msgFromSyscallError, mrLen], hI, rfl, rfl⟩
  case AlignmentError.alignmentError =>
    rw [WP.spec_ok]; exact ⟨by cases buf <;> simp [Fl4Spec.msgFromSyscallError, mrLen], hI, rfl, rfl⟩
  case TruncatedMessage.truncatedMessage =>
    rw [WP.spec_ok]; exact ⟨by cases buf <;> simp [Fl4Spec.msgFromSyscallError, mrLen], hI, rfl, rfl⟩
  case DeleteFirst.deleteFirst =>
    rw [WP.spec_ok]; exact ⟨by cases buf <;> simp [Fl4Spec.msgFromSyscallError, mrLen], hI, rfl, rfl⟩
  case RevokeFirst.revokeFirst =>
    rw [WP.spec_ok]; exact ⟨by cases buf <;> simp [Fl4Spec.msgFromSyscallError, mrLen], hI, rfl, rfl⟩
  case NotEnoughMemory.notEnoughMemory b b' =>
    exact one b _ (by simp [Fl4Spec.msgFromSyscallError, h])
  case RangeError.rangeError mn mx mn' mx' =>
    refine WP.spec_bind (step s [] hI hBP 0#u64 rfl (by simp) mn) ?_
    rintro ⟨i1, s1⟩ ⟨-, h2, h3, h4⟩
    refine WP.spec_mono (step s1 _ h2 (hBP.mono h3 fun _ _ _ h => h) 1#u64 (by simp) (by simp) mx) ?_
    rintro r ⟨g1, g2, g3, g4⟩
    have hl : (Fl4Spec.msgFromSyscallError (.rangeError mn' mx')).2 = [] ++ [mn.bv] ++ [mx.bv] := by
      simp [Fl4Spec.msgFromSyscallError, h.1, h.2]
    rw [hl]
    exact ⟨by rw [g1]; simp, g2, g3.trans h3, g4.trans h4⟩
  case FailedLookup.failedLookup src lf src' lf' =>
    obtain ⟨rfl, hlf⟩ := h
    have hG' : ∀ g l gs, lf = .GuardMismatch g l gs → g.val < 2 ^ gs.val := fun g l gs e =>
      hG _ g l gs (by rw [e])
    have core : ∀ v : U64, v.bv = (if src' then 1 else 0) →
        (do
          let (_, s1) ← msg.set_mr st s ct w 0#u64 v
          faults.set_mrs_lookup_failure_at st s1 ct w lf 1#u64) ⦃ r =>
        r.1.val = mrLen buf (Fl4Spec.msgFromSyscallError (.failedLookup src' lf')).2.length ∧
        RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G r.2 a
          (MrS σ0 ct.bv x0 buf (Fl4Spec.msgFromSyscallError (.failedLookup src' lf')).2) ∧ L.ksb r.2 = L.ksb s ∧ L.cpu r.2 = L.cpu s ⦄ := by
      intro v hv
      refine WP.spec_bind (step s [] hI hBP 0#u64 rfl (by simp) v) ?_
      rintro ⟨i1, s1⟩ ⟨-, h2, h3, h4⟩
      have hl : (Fl4Spec.msgFromSyscallError (.failedLookup src' lf')).2 =
          ([] ++ [v.bv]) ++ Fl4Spec.msgFromLookupFailure lf' := by
        simp [Fl4Spec.msgFromSyscallError, hv]
      rw [hl]
      refine WP.spec_mono (setmrs_lf_inv (L := L) σ0 ct htcb hcur hk0 buf w hw0 hbm a s1 _ (by simp) h2
        (hBP.mono h3 fun _ _ _ h => h) lf lf' hlf hG') ?_
      rintro r ⟨g1, g2, g3, g4⟩
      exact ⟨g1, g2, g3.trans h3, g4.trans h4⟩
    cases src'
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact core 0#u64 (by simp)
    · simp only [↓reduceIte]
      exact core 1#u64 (by simp)

end ErrMrs

/-! ### The spec's error reply -/

/-- The spec's state after `fl4ReplyFromKernelError true t (label, ms)`. -/
def replyErrState (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (label : Fl4Spec.Data)
    (ms : List Fl4Spec.Word) : Fl4Spec.State Unit :=
  let xA := Notif.setReg x Fl4Spec.badge_register 0
  let xM := Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs ms)
  match Endp.ipcBufOf true x with
  | some p =>
    let σM := MrS (Notif.updK σ t (.tcb xA)) t xA (some p) ms
    let σD := Endp.setUm σM (Endp.storeMem σM.machineState.underlyingMemory (Endp.bufAddr p 7)
      (Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) &&& ~~~255))
    Notif.updK σD t (.tcb (Notif.setReg xM Fl4Spec.msg_info_register
      (Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen (some p) ms.length) + 1, 0, 0, label⟩)))
  | none =>
    Notif.updK (MrS (Notif.updK σ t (.tcb xA)) t xA none ms) t (.tcb (Notif.setReg xM Fl4Spec.msg_info_register
      (Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen none ms.length), 0, 0, label⟩)))

theorem notDataPage_tcb (y : Fl4Spec.Tcb) : ∀ sz, (Fl4Spec.KernelObject.tcb y) ≠ .archObj (.dataPage false sz) :=
  fun _ h => by cases h

set_option maxHeartbeats 4000000 in
/-- **The spec's error reply with the debug option** has one outcome,
`replyErrState`. -/
theorem fl4ReplyErr_eq {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (label : Fl4Spec.Data) (ms : List Fl4Spec.Word) (hlen : ms.length ≤ 6)
    (hfr : ∀ p, Endp.ipcBufOf true x = some p →
      ∀ k, k < 128 → (Endp.bufAddr p k).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p k) σ) :
    Fl4Spec.fl4ReplyFromKernelError (Z := Unit) true t (label, ms) σ =
      ({((), replyErrState σ t x label ms)}, False) := by
  set xA := Notif.setReg x Fl4Spec.badge_register 0
  have hkA : (Notif.updK σ t (.tcb xA)).kheap t = some (.tcb xA) := by simp
  have hkM : ∀ buf, (MrS (Notif.updK σ t (.tcb xA)) t xA buf ms).kheap t =
      some (.tcb (Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs ms))) := fun buf =>
    MrS_kheap_t _ _ _ _ _
  unfold Fl4Spec.fl4ReplyFromKernelError
  simp only [↓reduceIte]
  rw [Notif.nd_pure_bind']
  dsimp only
  rw [nd_bind_one (Endp.lookupIpcBuffer_eq hk true), nd_bind_one (Notif.asUser_setRegister_eq _ _ hk)]
  unfold replyErrState
  cases hb : Endp.ipcBufOf true x with
  | none =>
    rw [nd_bind_one (Endp.setMrs_eqN hkA ms)]
    dsimp only
    unfold Fl4Spec.setMessageInfo
    have h' : (Endp.mrStateN (Notif.updK σ t (.tcb xA)) t xA ms).kheap t =
        some (.tcb (Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs ms))) := hkM none
    rw [Notif.asUser_setRegister_eq _ _ h']
    rfl
  | some p =>
    have hfp := hfr p hb
    rw [nd_bind_one (Endp.setMrs_eq hkA p ms (fun q hq => by
      have hq1 : q.1 < 128 := by
        have := (List.of_mem_zip hq).1
        simp only [List.mem_range'] at this; omega
      exact ⟨(hfp q.1 hq1).1, Endp.inUserFrame_updK hk (notDataPage_tcb x) _ (hfp q.1 hq1).2⟩))]
    dsimp only
    set σM := MrS (Notif.updK σ t (.tcb xA)) t xA (some p) ms
    have hufM : Fl4Spec.inUserFrame (Endp.bufAddr p 7) σM :=
      (Endp.inUserFrame_setUm _ _ _).2 (Endp.inUserFrame_updK hkA (notDataPage_tcb _) _
        (Endp.inUserFrame_updK hk (notDataPage_tcb x) _ (hfp 7 (by omega)).2))
    have hlen' : min ms.length Fl4Spec.msgMaxLength = ms.length := by
      unfold Fl4Spec.msgMaxLength; omega
    have hd : Fl4Spec.debugMessageStart + 1 = 7 := rfl
    rw [hd]
    change (Fl4Spec.loadWordOffs p 7 >>= _) σM = _
    rw [nd_bind_one (Endp.loadWordOffs_eq σM p 7 (hfp 7 (by omega)).1),
      nd_bind_one (Endp.storeWordOffs_eq σM p 7 _ (hfp 7 (by omega)).1 hufM)]
    unfold Fl4Spec.setMessageInfo
    change Fl4Spec.asUser t _ (Endp.setUm σM (Endp.storeMem σM.machineState.underlyingMemory (Endp.bufAddr p 7)
      (Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) &&& ~~~255))) = _
    have hkD : (Endp.setUm σM (Endp.storeMem σM.machineState.underlyingMemory (Endp.bufAddr p 7)
        (Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) &&& ~~~255))).kheap t =
        some (.tcb (Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs ms))) := hkM (some p)
    rw [Notif.asUser_setRegister_eq _ _ hkD, hlen']
    rfl

/-! ### The error reply -/

theorem msgErr_len (e' : Fl4Spec.SyscallError) : (Fl4Spec.msgFromSyscallError e').2.length ≤ 5 := by
  cases e' with
  | failedLookup s lf => cases lf <;> simp [Fl4Spec.msgFromSyscallError, Fl4Spec.msgFromLookupFailure]
  | _ => simp [Fl4Spec.msgFromSyscallError]

/-- FL4's error code is the spec's label. -/
theorem code_label {e : error.SysError} {e' : Fl4Spec.SyscallError} (he : ErrRel (.Sys e) e') :
    error.SysError.code e ⦃ c => c.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits = (Fl4Spec.msgFromSyscallError e').1 ⦄ := by
  rcases he with h | ⟨n, he, rfl⟩
  · cases e <;> cases e' <;> simp only [SysErrRel] at h <;>
      simp only [error.SysError.code, WP.spec_ok, Fl4Spec.msgFromSyscallError, fl4_abi.consts.error.InvalidArgument,
        fl4_abi.consts.error.IllegalOperation, fl4_abi.consts.error.RangeError, fl4_abi.consts.error.AlignmentError,
        fl4_abi.consts.error.FailedLookup, fl4_abi.consts.error.TruncatedMessage, fl4_abi.consts.error.DeleteFirst,
        fl4_abi.consts.error.RevokeFirst, fl4_abi.consts.error.NotEnoughMemory] <;> decide
  · cases he
    simp only [error.SysError.code, WP.spec_ok, Fl4Spec.msgFromSyscallError, fl4_abi.consts.error.InvalidCapability]
    decide

set_option maxHeartbeats 16000000 in
/-- **FL4's `reply_error` keeps `RInv`**, against the spec's error reply with
the debug option (`replyErrState`). -/
theorem reply_error_inv {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (ct : U64) (s1 : S) (a1 : A)
    (σ' : Fl4Spec.State Unit) (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s1 a1 σ')
    (htcb : th ct = some .tcb) (hcur : ct.bv = σ'.curThread) {x : Fl4Spec.Tcb}
    (hk : σ'.kheap ct.bv = some (.tcb x)) (hBP0 : BufPlaced (L := L) N C B c s1 σ')
    (hLB0 : msg.lookup_ipc_buffer st s1 true ct ⦃ w => (w = 0#u64 ↔ Endp.ipcBufOf true x = none) ∧
        ∀ p, Endp.ipcBufOf true x = some p → Endp.BufMap B w p ∧
          ∀ k, k < 128 → Fl4Spec.inUserFrame (Endp.bufAddr p k) σ' ⦄)
    (e : error.SysError) (e' : Fl4Spec.SyscallError) (he : ErrRel (.Sys e) e')
    (hG : ∀ src g l gs, e = .FailedLookup src (.GuardMismatch g l gs) → g.val < 2 ^ gs.val) :
    syscall.reply_error st s1 ct e ⦃ s2 =>
      RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s2 a1
        (replyErrState σ' ct.bv x (Fl4Spec.msgFromSyscallError e').1 (Fl4Spec.msgFromSyscallError e').2) ∧
      L.ksb s2 = L.ksb s1 ∧ L.cpu s2 = L.cpu s1 ⦄ := by
  have hmsl : (Fl4Spec.msgFromSyscallError e').2.length ≤ 5 := msgErr_len e'
  have hflag : fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC = true := by
    unfold fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC; rfl
  have hdm : syscall.DEBUG_MESSAGE_START + 1#u64 = ok 7#u64 := by
    unfold syscall.DEBUG_MESSAGE_START; rfl
  set xA := Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv with hxA
  set σA := Notif.updK σ' ct.bv (.tcb xA) with hσA
  have hkA : σA.kheap ct.bv = some (.tcb xA) := by simp [σA]
  have hcurA : ct.bv = σA.curThread := hcur
  have hBPA : ∀ s, L.ksb s = L.ksb s1 → BufPlaced (L := L) N C B c s σA := fun s h =>
    hBP0.mono h (fun q y n hq => by
      by_cases e : q = ct.bv
      · subst e; rw [hkA] at hq; cases hq
      · simpa [σA, e] using hq)
  unfold syscall.reply_error
  refine WP.spec_bind hLB0 ?_
  rintro w ⟨hw0, hwp⟩
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s1 ct layout.reg.BADGE 0#u64) ?_
  rintro s2 rfl
  have hI1 := regw_inv s1 a1 σ' hI ct htcb hcur hk Fl4Spec.badge_register 0#u64
  rw [Endp.regIdx_badge] at hI1
  have hksb2 : L.ksb (L.wr s1 (Endp.regA ct layout.reg.BADGE) 0#u64) = L.ksb s1 := L.ksb_wr _ _ _
  have hcpu2 : L.cpu (L.wr s1 (Endp.regA ct layout.reg.BADGE) 0#u64) = L.cpu s1 := L.cpu_wr _ _ _
  cases hb : Endp.ipcBufOf true x with
  | none =>
    have hMS : MrS σA ct.bv xA none [] = σA := Endp.mrStateN_nil hkA
    replace hI1 : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G (L.wr s1 (Endp.regA ct layout.reg.BADGE) 0#u64) a1 (MrS σA ct.bv xA none []) := by
      rw [hMS]; exact hI1
    refine WP.spec_bind (error_mrs_inv σA ct htcb hcurA hkA none w (hw0.trans (by rw [hb]))
      (fun p h => by cases h) a1 _ hI1 (hBPA _ hksb2) e e' he hG) ?_
    rintro ⟨len, s3⟩ ⟨hlen, hI3, hk3, hc3⟩
    have hw : w = 0#u64 := hw0.2 hb
    simp only [hflag, hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine WP.spec_bind (code_label he) ?_
    rintro cd hcd
    unfold msginfo.MessageInfo.new
    simp only [bind_ok]
    have hl128 : len.val < 128 := by rw [hlen]; simp only [mrLen]; omega
    refine WP.spec_mono (Endp.set_msg_info_spec _ ct cd len hl128) ?_
    rintro s4 ⟨v, rfl, hv⟩
    rw [← Endp.regIdx_msgInfo]
    have hkM := MrS_kheap_t σA ct.bv xA none (Fl4Spec.msgFromSyscallError e').2
    have hI4 := regw_inv _ a1 _ hI3 ct htcb (by rw [MrS_cur]; exact hcurA) hkM Fl4Spec.msg_info_register v
    refine ⟨?_, by rw [L.ksb_wr, hk3, hksb2], by rw [L.cpu_wr, hc3, hcpu2]⟩
    have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen none (Fl4Spec.msgFromSyscallError e').2.length),
        0, 0, (Fl4Spec.msgFromSyscallError e').1⟩ := by
      rw [hv, hcd]; congr 2
      apply BitVec.eq_of_toNat_eq; simp only [Fl4Spec.natToLen, BitVec.toNat_ofNat, UScalar.bv_toNat, hlen, mrLen]; omega
    unfold replyErrState
    simp only [hb]
    rw [← hvd]; exact hI4
  | some p =>
    obtain ⟨hbm, hfr⟩ := hwp p hb
    have hMS : MrS σA ct.bv xA (some p) [] = σA := Endp.mrState_nil hkA p
    replace hI1 : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G (L.wr s1 (Endp.regA ct layout.reg.BADGE) 0#u64) a1 (MrS σA ct.bv xA (some p) []) := by
      rw [hMS]; exact hI1
    have hw : w ≠ 0#u64 := fun h => by rw [hb] at hw0; cases hw0.1 h
    refine WP.spec_bind (error_mrs_inv σA ct htcb hcurA hkA (some p) w (by rw [← hb]; exact hw0)
      (fun q h => by cases h; exact hbm) a1 _ hI1 (hBPA _ hksb2) e e' he hG) ?_
    rintro ⟨len, s3⟩ ⟨hlen, hI3, hk3, hc3⟩
    have hbw : (w != 0#u64) = true := by simp [hw]
    simp only [hflag, hbw, ↓reduceIte, hdm, bind_ok]
    have hdbg : (do
        let w_1 ← msg.buf_get st s3 w 7#u64
        let i1 ← lift (~~~255#u64)
        let i2 ← lift (w_1 &&& i1)
        let s4 ← msg.buf_set st s3 w 7#u64 i2
        let len2 ← lift (core.num.U64.wrapping_add len 1#u64)
        ok (s4, len2)) ⦃ r => r = (L.wr s3 (Endp.fl4BufA w 7#u64) (L.mem s3 (Endp.fl4BufA w 7#u64) &&& ~~~255#u64),
          core.num.U64.wrapping_add len 1#u64) ⦄ := by
      refine WP.spec_bind (Endp.msg.buf_get.spec s3 w 7#u64) ?_
      rintro dv rfl
      simp only [lift, bind_ok]
      refine WP.spec_bind (Endp.msg.buf_set.spec s3 w 7#u64 _) ?_
      rintro s4 rfl
      simp only [bind_ok, WP.spec_ok]
    refine WP.spec_bind hdbg ?_
    rintro r rfl
    have hpair := hbm 7#u64 (by decide)
    set σM := MrS σA ct.bv xA (some p) (Fl4Spec.msgFromSyscallError e').2
    have hdv : (L.mem s3 (Endp.fl4BufA w 7#u64)).bv = Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) :=
      hI3.2.2.2.2.1.1.2.1.buf _ hpair
    have hval : (L.mem s3 (Endp.fl4BufA w 7#u64) &&& ~~~255#u64).bv =
        Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) &&& ~~~(255 : Fl4Spec.Word) := by
      rw [UScalar.bv_and]; exact congrArg₂ (· &&& ·) hdv rfl
    have hI4 : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G
        (L.wr s3 (Endp.fl4BufA w 7#u64) (L.mem s3 (Endp.fl4BufA w 7#u64) &&& ~~~255#u64)) a1
        (Endp.setUm σM (Endp.storeMem σM.machineState.underlyingMemory (Endp.bufAddr p 7)
          (Endp.loadWordAt σM.machineState.underlyingMemory (Endp.bufAddr p 7) &&& ~~~(255 : Fl4Spec.Word)))) := by
      rw [← hval]
      exact bufw_inv s3 a1 σM hI3 ((hBPA s3 (hk3.trans hksb2)).mono rfl (MrS_sc hkA _ _)) hpair
        (L.mem s3 (Endp.fl4BufA w 7#u64) &&& ~~~255#u64)
    refine WP.spec_bind (code_label he) ?_
    rintro cd hcd
    unfold msginfo.MessageInfo.new
    simp only [bind_ok]
    have hl128 : (core.num.U64.wrapping_add len 1#u64).val < 128 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hlen, mrLen]; omega
    refine WP.spec_mono (Endp.set_msg_info_spec _ ct cd _ hl128) ?_
    rintro s5 ⟨v, rfl, hv⟩
    rw [← Endp.regIdx_msgInfo]
    have hkD := MrS_kheap_t σA ct.bv xA (some p) (Fl4Spec.msgFromSyscallError e').2
    have hI5 := regw_inv _ a1 _ hI4 ct htcb (by show ct.bv = σM.curThread; rw [MrS_cur]; exact hcurA) hkD
      Fl4Spec.msg_info_register v
    refine ⟨?_, by rw [L.ksb_wr, L.ksb_wr, hk3, hksb2], by rw [L.cpu_wr, L.cpu_wr, hc3, hcpu2]⟩
    have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen (some p)
        (Fl4Spec.msgFromSyscallError e').2.length) + 1, 0, 0, (Fl4Spec.msgFromSyscallError e').1⟩ := by
      rw [hv, hcd]; congr 2
      apply BitVec.eq_of_toNat_eq
      simp [Fl4Spec.natToLen, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hlen, mrLen]
    unfold replyErrState
    simp only [hb]
    rw [← hvd]; exact hI5

theorem replyErrState_cur (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (label : Fl4Spec.Data)
    (ms : List Fl4Spec.Word) : (replyErrState σ t x label ms).curThread = σ.curThread := by
  unfold replyErrState; split <;> rfl

/-- The caller's IPC buffer as the error reply reads it (a hypothesis on the
joint invariant, the CSpace's IPC-buffer cap): no buffer, or a mapped one
whose words are user-frame words. -/
def BufLookupHyp {A : Type} (L4 L3 L2 L1 N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64)
    (AR : A → Fl4Spec.Cr3 → Prop) (ct : U64) : Prop :=
  ∀ s a σ x, RX (L := L) L4 L3 L2 L1 N T C E R B c AR ct s a σ → σ.kheap ct.bv = some (.tcb x) →
    msg.lookup_ipc_buffer st s true ct ⦃ w => (w = 0#u64 ↔ Endp.ipcBufOf true x = none) ∧
      ∀ p, Endp.ipcBufOf true x = some p → Endp.BufMap B w p ∧
        ∀ k, k < 128 → Fl4Spec.inUserFrame (Endp.bufAddr p k) σ ⦄

set_option maxHeartbeats 4000000 in
/-- **`ReplyHypMX.fail` for `RX`**, with the debug option: from the caller's
buffer (`BufLookupHyp`), the buffer words' placement (`BufPlaced`) and a
guard found within its size. -/
theorem replyHypMX_fail {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (ct : U64) (is_call : Bool)
    (hBP : ∀ s a σ, RX (L := L) L4 L3 L2 L1 N T C E R B c AR ct s a σ → BufPlaced (L := L) N C B c s σ)
    (hLB : BufLookupHyp (L := L) L4 L3 L2 L1 N T C E R B c AR ct)
    (hG : ∀ (e : error.SysError) src g l gs, e = .FailedLookup src (.GuardMismatch g l gs) → g.val < 2 ^ gs.val)
    (s1 : S) (a1 : A) (σ' : Fl4Spec.State Unit) (e : error.SysError) (e' : Fl4Spec.SyscallError)
    (hX : RX (L := L) L4 L3 L2 L1 N T C E R B c AR ct s1 a1 σ') (he : ErrRel (.Sys e) e') :
    ((if is_call then do
        let s2 ← syscall.reply_error st s1 ct e
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)
      else ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s1, a1)) :
      Result ((core.result.Result Unit error.Exc) × S × A)) ⦃ res =>
      res.1 = .Ok () ∧ ∃ z ∈ ((Fl4Spec.NonDet.when is_call <|
        Fl4Spec.fl4ReplyFromKernelError true ct.bv (Fl4Spec.msgFromSyscallError e')) σ').1,
        RelTopM (L := L) res.2.1 z.2 ∧ RX (L := L) L4 L3 L2 L1 N T C E R B c AR ct res.2.1 res.2.2 z.2 ⦄ := by
  cases is_call
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨trivial, ((), σ'), ?_, hX.relTop, hX⟩
    rw [Endp.nd_when_false (by simp)]; exact Set.mem_singleton _
  simp only [↓reduceIte]
  have hBP0 := hBP s1 a1 σ' hX
  have hLB0 := hLB s1 a1 σ'
  obtain ⟨th, P, G, hI, htcb, hcur, hact⟩ := hX
  obtain ⟨x, hk, -⟩ := hI.1.1.tcb ct htcb
  have hLB1 := hLB0 x ⟨th, P, G, hI, htcb, hcur, hact⟩ hk
  obtain ⟨w, -, hw0, hwp⟩ := spec_exists hLB1
  have hfr : ∀ p, Endp.ipcBufOf true x = some p →
      ∀ k, k < 128 → (Endp.bufAddr p k).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p k) σ' :=
    fun p hp k hk' => ⟨Endp.bufAddr_aligned hI.2.2.2.2.1.2.ep (hwp p hp).1 k, (hwp p hp).2 k hk'⟩
  refine WP.spec_bind (reply_error_inv ct s1 a1 σ' hI htcb hcur hk hBP0 hLB1 e e' he (hG e)) ?_
  rintro s2 ⟨hI2, hksb, hcpu⟩
  simp only [WP.spec_ok]
  refine ⟨trivial, ((), replyErrState σ' ct.bv x (Fl4Spec.msgFromSyscallError e').1
    (Fl4Spec.msgFromSyscallError e').2), ?_, hI2.relTop, th, P, G, hI2, htcb, by rw [replyErrState_cur]; exact hcur,
    by rw [hcpu, Sched.nodeAt_ksb hksb]; exact hact⟩
  unfold Fl4Spec.NonDet.when
  simp only [↓reduceIte]
  rw [fl4ReplyErr_eq hk _ _ (by have := msgErr_len e'; omega) hfr]
  exact Set.mem_singleton _

/-- **`ReplyHypMX` for `RX`**, with the debug option. -/
theorem replyHypMX_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (ct : U64) (is_call : Bool)
    (hBP : ∀ s a σ, RX (L := L) L4 L3 L2 L1 N T C E R B c AR ct s a σ → BufPlaced (L := L) N C B c s σ)
    (hLB : BufLookupHyp (L := L) L4 L3 L2 L1 N T C E R B c AR ct)
    (hG : ∀ (e : error.SysError) src g l gs, e = .FailedLookup src (.GuardMismatch g l gs) → g.val < 2 ^ gs.val) :
    ReplyHypMX (L := L) (RX (L := L) L4 L3 L2 L1 N T C E R B c AR ct) true ct is_call :=
  ⟨fun s1 a1 σ' _ hX => replyHypMX_succ ct is_call s1 a1 σ' hX,
   fun s1 a1 σ' e e' _ hX he => replyHypMX_fail ct is_call hBP hLB hG s1 a1 σ' e e' hX he⟩

end

end

end Fl4Proofs.P3.Vs

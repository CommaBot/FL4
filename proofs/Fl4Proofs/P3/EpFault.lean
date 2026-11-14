/-
P3 (DESIGN.md §9), endpoints: fault messages (l4v `do_fault_transfer`,
FL4 `ipc::do_fault_transfer` / `faults::set_mrs_fault`).

`set_mr_rel`: FL4's `set_mr` of word `i = |ms|` refines appending the word to
the message `ms` that l4v `set_mrs` writes (`mrState`), on a receiver with a
mapped IPC buffer.
-/
import Fl4Proofs.P3.EpMrs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

theorem setReg_withRegs (x : Fl4Spec.Tcb) (R : Fl4Spec.Register → Fl4Spec.Word) (r : Fl4Spec.Register)
    (v : Fl4Spec.Word) : setReg (withRegs x R) r v = withRegs x (Function.update R r v) := rfl

theorem mrState_snoc_lt (σ : Fl4Spec.State Unit) (rcv : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (p : Fl4Spec.ObjRef)
    (ms : List Fl4Spec.Word) (v : Fl4Spec.Word) (k : Nat) (hk : k = ms.length) (h : ms.length < 4) :
    updK (mrState σ rcv x p ms) rcv
      (.tcb (setReg (withRegs x (mrRegs x.tcbArch.tcbContext.userRegs ms)) (mrIdx k) v)) =
    mrState σ rcv x p (ms ++ [v]) := by
  subst hk
  unfold mrState
  rw [mrPairs_snoc_lt _ _ h, mrRegs_snoc_lt _ _ _ h, setReg_withRegs]
  simp only [updK, setUm, Function.update_idem]

theorem mrState_snoc_ge (σ : Fl4Spec.State Unit) (rcv : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (p : Fl4Spec.ObjRef)
    (ms : List Fl4Spec.Word) (v : Fl4Spec.Word) (h : 4 ≤ ms.length) (h' : ms.length < 120) :
    setUm (mrState σ rcv x p ms) (storeMem (mrState σ rcv x p ms).machineState.underlyingMemory
      (bufAddr p (ms.length + 1)) v) = mrState σ rcv x p (ms ++ [v]) := by
  unfold mrState
  rw [mrPairs_snoc_ge _ _ h h', mrRegs_snoc_ge _ _ _ h, mrMem_snoc, setUm_um, setUm_setUm]

section Spec
open Fl4Spec

theorem mrState_nil {σ : State Unit} {rcv : ObjRef} {x : Tcb} (hk : σ.kheap rcv = some (.tcb x)) (p : ObjRef) :
    mrState σ rcv x p [] = σ := by
  have h1 : mrRegs x.tcbArch.tcbContext.userRegs [] = x.tcbArch.tcbContext.userRegs := by
    funext reg; simp [mrRegs]
  have h2 : withRegs x x.tcbArch.tcbContext.userRegs = x := rfl
  unfold mrState
  rw [h1, h2, updK_self hk]
  rfl

/-- The fault message of a cap fault (l4v `make_fault_msg`). -/
def capFaultMsg (pc : Word) (c : ObjRef) (rp : Bool) (lf : LookupFailure) : List Word :=
  pc :: c :: (if rp then 1 else 0) :: msgFromLookupFailure lf

theorem makeFaultMsg_cap {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (c : ObjRef) (rp : Bool) (lf : LookupFailure) :
    makeFaultMsg (Z := Unit) (.capFault c rp lf) t σ =
      ({((1, capFaultMsg (x.tcbArch.tcbContext.userRegs .faultIP) c rp lf), σ)}, False) := by
  rw [makeFaultMsg]
  rw [show getRestartPC = getRegister .faultIP from rfl, nd_bind_one (asUser_getRegister_eq hk .faultIP)]
  rfl

/-- **`do_fault_transfer` into a receiver with an IPC buffer**, given the
fault message. -/
theorem doFaultTransfer_eq {σ : State Unit} {snd rcv : ObjRef} {xs xr : Tcb}
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) {f : Fault}
    (hf : xs.tcbFault = some f) {label : Data} {ms : List Word}
    (hmsg : makeFaultMsg (Z := Unit) f snd σ = ({((label, ms), σ)}, False)) (p : ObjRef)
    (hal : ∀ q ∈ mrPairs ms, (bufAddr p q.1).toNat % 8 = 0 ∧ inUserFrame (bufAddr p q.1) σ) (badge : Data) :
    doFaultTransfer (Z := Unit) badge snd rcv (some p) σ =
      ({((), updK (mrState σ rcv xr p ms) rcv (.tcb (setReg (setReg
        (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms)) msg_info_register
        (messageInfoToData ⟨natToLen (min ms.length msgMaxLength), 0, 0, label⟩)) badge_register badge)))}, False) := by
  unfold doFaultTransfer
  rw [nd_bind_one (threadGet_eq _ hks), hf]
  dsimp only
  rw [nd_pure_bind', nd_bind_one hmsg]
  dsimp only
  rw [nd_bind_one (setMrs_eq hkr p ms hal)]
  have hkm : (mrState σ rcv xr p ms).kheap rcv = some (.tcb (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms))) := by
    simp [mrState, setUm]
  unfold setMessageInfo
  rw [nd_bind_one (asUser_setRegister_eq _ _ hkm), asUser_setRegister_eq (x := setReg
    (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms)) msg_info_register
    (messageInfoToData ⟨natToLen (min ms.length msgMaxLength), 0, 0, label⟩)) _ _
    (by simp only [updK_kheap, Function.update_self])]
  simp only [updK, Function.update_idem]

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **`set_mr`** of the next message word. -/
theorem set_mr_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (σ0 : Fl4Spec.State Unit)
    {rcv : U64} (hr : rcv ∈ T) {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap rcv.bv = some (.tcb x0))
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p)
    (ms : List Fl4Spec.Word) (hR : EpStateRel T E R B (L.mem s) (mrState σ0 rcv.bv x0 p ms))
    (hSR : SR s (mrState σ0 rcv.bv x0 p ms)) (i : U64) (hi : i.val = ms.length) (hi' : i.val < 120) (v : U64) :
    msg.set_mr st s rcv rw i v ⦃ r => r.1.val = i.val + 1 ∧
      EpStateRel T E R B (L.mem r.2) (mrState σ0 rcv.bv x0 p (ms ++ [v.bv])) ∧
      SR r.2 (mrState σ0 rcv.bv x0 p (ms ++ [v.bv])) ∧
      Agree (L.mem s) (L.mem r.2) (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ⦄ := by
  have hra := hP.tcb rcv hr
  have hks : (mrState σ0 rcv.bv x0 p ms).kheap rcv.bv =
      some (.tcb (withRegs x0 (mrRegs x0.tcbArch.tcbContext.userRegs ms))) := by
    simp [mrState, setUm]
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  unfold msg.set_mr
  by_cases h4 : i < msg.N_MSG_REGISTERS
  · have hi4 : i.val < 4 := by have := (gt_iff_val).1 h4; omega
    simp only [h4, ↓reduceIte]
    refine WP.spec_bind (msg_register_spec i hi4) ?_
    rintro r rfl
    step as ⟨s1, hs1⟩
    subst hs1
    obtain ⟨hR1, hW1, hS1⟩ := write_reg_rel hP s _ hR hr hks (mrIdx i.val) v
    rw [mrState_snoc_lt _ _ _ _ _ _ i.val hi (by omega)] at hR1 hS1
    unfold lift
    apply ok_bind_spec
    simp only [WP.spec_ok]
    have ha := a_reg hra (mrIdx i.val)
    refine ⟨?_, hR1, hH.stable _ _ _ _ hSR hW1 hS1, ?_⟩
    · simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · exact fun b hb hn => agree_wr (L := L) (s := s) (v := v) ha.1 b hb (fun h => hn.1 ⟨_, h⟩)
  · have hi4 : 4 ≤ i.val := by have : ¬ i.val < 4 := fun h => h4 ((gt_iff_val).2 (by rw [hN]; exact h)); omega
    have hb : (rw != 0#u64) = true := by simp [hrw0]
    rw [if_neg h4]
    simp only [hb, ↓reduceIte]
    unfold lift
    apply ok_bind_spec
    step as ⟨s1, hs1⟩
    subst hs1
    have hiv : (core.num.U64.wrapping_add i 1#u64).val = ms.length + 1 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have hw := hmr (core.num.U64.wrapping_add i 1#u64) (by omega)
    have hal := (hP.balign _ hw).1
    have hag := agree_wr (L := L) (s := s) (v := v) hal
    have hR1 := hR.upd_buf hP hw v hag (rd_wr_eq hal)
    simp only [hiv] at hR1
    rw [mrState_snoc_ge _ _ _ _ _ _ (by omega) (by omega)] at hR1
    have hW : WritesIn st s (L.wr s (fl4BufA rw (core.num.U64.wrapping_add i 1#u64)) v) (EWrite T E R B) :=
      (writesIn_wr hal).mono fun b hb => Or.inr (Or.inr (Or.inr ⟨_, hw, hb⟩))
    have hS1 := hH.stable _ _ _ _ hSR hW (EpStep.setUm' _ (storeMem (mrState σ0 rcv.bv x0 p ms).machineState.underlyingMemory
      (bufAddr p (ms.length + 1)) v.bv))
    rw [mrState_snoc_ge _ _ _ _ _ _ (by omega) (by omega)] at hS1
    refine ⟨by omega, hR1, hS1, fun b hb hn => hag b hb (fun h => hn.2 ⟨_, hw, UScalar.eq_of_val_eq h⟩)⟩

/-- The invariant of a message being written: related to `mrState` of the
words written so far, `SR`, and nothing changed but the receiver's
registers and buffer words. -/
def MrInv (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) (s0 : S)
    (σ0 : Fl4Spec.State Unit) (rcv : U64) (x0 : Fl4Spec.Tcb) (p : Fl4Spec.ObjRef) (s : S) (ms : List Fl4Spec.Word) :
    Prop :=
  EpStateRel T E R B (L.mem s) (mrState σ0 rcv.bv x0 p ms) ∧ SR s (mrState σ0 rcv.bv x0 p ms) ∧
    Agree (L.mem s0) (L.mem s) (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b)

theorem set_mr_inv (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    {rcv : U64} (hr : rcv ∈ T) {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap rcv.bv = some (.tcb x0))
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p) {s : S} {ms : List Fl4Spec.Word}
    (hI : MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s ms) (i : U64) (hi : i.val = ms.length) (hi' : i.val < 120)
    (v : U64) :
    msg.set_mr st s rcv rw i v ⦃ r => r.1.val = i.val + 1 ∧
      MrInv (L := L) T E R B SR s0 σ0 rcv x0 p r.2 (ms ++ [v.bv]) ⦄ :=
  WP.spec_mono (set_mr_rel hH hP s σ0 hr hk0 hrw0 hmr ms hI.1 hI.2.1 i hi hi' v) fun _ ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2, h3, fun b hb hn => (h4 b hb hn).trans (hI.2.2 b hb hn)⟩

end

/-- The words FL4 sends for a lookup failure (faults.rs
`set_mrs_lookup_failure`). -/
def fl4LfMsg : error.LookupFault → List U64
  | .InvalidRoot => [1#u64]
  | .MissingCapability bl => [2#u64, bl]
  | .DepthMismatch bf bl => [3#u64, bl, bf]
  | .GuardMismatch g bl gs => [4#u64, bl, g, gs]

theorem bv_ofNat_val (x : U64) {n : Nat} (h : x.val = n) : x.bv = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  show x.val = n % 2 ^ 64
  rw [← h, Nat.mod_eq_of_lt (by have := x.hBounds; simpa [U64.size_def, U64.numBits] using this)]

/-- `LookupFault::decode` of related words gives the spec's message. -/
theorem decode_rel {lt l0 l1 : U64} {lf : Fl4Spec.LookupFailure} (h : LfRel lt l0 l1 lf) :
    error.LookupFault.decode lt l0 l1 ⦃ v => (fl4LfMsg v).map UScalar.bv = Fl4Spec.msgFromLookupFailure lf ⦄ := by
  unfold error.LookupFault.decode
  cases lf with
  | invalidRoot =>
    have : lt = 1#u64 := h
    subst this
    simp only [show (1#u64 : U64) ≠ 2#u64 by decide, show (1#u64 : U64) ≠ 3#u64 by decide,
      show (1#u64 : U64) ≠ 4#u64 by decide, ↓reduceIte, WP.spec_ok]
    rfl
  | missingCapability n =>
    obtain ⟨rfl, h0⟩ := h
    simp only [↓reduceIte, WP.spec_ok, fl4LfMsg, List.map_cons, List.map_nil, Fl4Spec.msgFromLookupFailure]
    simp only [List.cons.injEq, and_true]
    exact ⟨rfl, bv_ofNat_val l0 h0⟩
  | depthMismatch bl bf =>
    obtain ⟨rfl, h0, h1⟩ := h
    simp only [show (3#u64 : U64) ≠ 2#u64 by decide, ↓reduceIte, WP.spec_ok, fl4LfMsg, List.map_cons, List.map_nil,
      Fl4Spec.msgFromLookupFailure]
    simp only [List.cons.injEq, and_true]
    exact ⟨rfl, bv_ofNat_val l1 h1, bv_ofNat_val l0 h0⟩
  | guardMismatch bl g =>
    obtain ⟨rfl, h0, h1, h2⟩ := h
    simp only [show (4#u64 : U64) ≠ 2#u64 by decide, show (4#u64 : U64) ≠ 3#u64 by decide, ↓reduceIte]
    step as ⟨i, hi, hi'⟩
    unfold lift
    apply ok_bind_spec
    simp only [WP.spec_ok, fl4LfMsg, List.map_cons, List.map_nil, Fl4Spec.msgFromLookupFailure, List.cons.injEq,
      and_true]
    refine ⟨rfl, bv_ofNat_val i (by rw [hi]; exact h1), h0, bv_ofNat_val _ ?_⟩
    show (l1 &&& 255#u64).bv.toNat = _
    rw [UScalar.bv_and, BitVec.toNat_and, show (UScalar.bv (255#u64 : U64)).toNat = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    exact h2

theorem wadd_val (x : U64) (k : Nat) (hk : x.val + k < 2 ^ 64) (K : U64) (hK : K.val = k) :
    (core.num.U64.wrapping_add x K).val = x.val + k := by
  rw [core.num.U64.wrapping_add_val_eq, hK]; simp [U64.size_def, U64.numBits]; omega

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **`set_mrs_lookup_failure`**: the lookup-failure words, appended. -/
theorem set_mrs_lookup_failure_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S}
    {σ0 : Fl4Spec.State Unit} {rcv : U64} (hr : rcv ∈ T) {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap rcv.bv = some (.tcb x0))
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p) {s : S} {ms : List Fl4Spec.Word}
    (hI : MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s ms) (off : U64) (hoff : off.val = ms.length)
    (hlen : ms.length + 4 ≤ 120) (lfv : error.LookupFault) :
    faults.set_mrs_lookup_failure st s rcv rw lfv off ⦃ r => r.1.val = ms.length + (fl4LfMsg lfv).length ∧
      MrInv (L := L) T E R B SR s0 σ0 rcv x0 p r.2 (ms ++ ((fl4LfMsg lfv).map UScalar.bv : List Fl4Spec.Word)) ⦄ := by
  have hset := fun {s : S} {ms : List Fl4Spec.Word} (h : MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s ms) =>
    set_mr_inv (L := L) hH hP hr hk0 hrw0 hmr h
  unfold faults.set_mrs_lookup_failure error.LookupFault.type_code
  have hc : ∀ (c : U64), c.val = 1 ∨ c.val = 2 ∨ c.val = 3 ∨ c.val = 4 → True := fun _ _ => trivial
  cases lfv with
  | InvalidRoot =>
    dsimp only
    apply ok_bind_spec
    refine WP.spec_bind (hset hI off hoff (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨h1, h2⟩
    show (ok (i1, s1)) ⦃ _ ⦄
    simp only [WP.spec_ok]
    refine ⟨by simp only at h1; rw [h1, hoff]; rfl, ?_⟩
    simpa [fl4LfMsg, fl4_abi.consts.lookup.InvalidRoot] using h2
  | MissingCapability bl =>
    dsimp only
    apply ok_bind_spec
    refine WP.spec_bind (hset hI off hoff (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨h1, h2⟩
    unfold lift
    apply ok_bind_spec
    refine WP.spec_mono (hset h2 (core.num.U64.wrapping_add off 1#u64)
      (by rw [wadd_val off 1 (by omega) _ rfl]; simp; omega) (by rw [wadd_val off 1 (by omega) _ rfl]; omega) bl) ?_
    rintro ⟨i2, s2⟩ ⟨g1, g2⟩
    refine ⟨by simp only at g1 ⊢; rw [g1, wadd_val off 1 (by omega) _ rfl, hoff]; rfl, ?_⟩
    simpa [fl4LfMsg, fl4_abi.consts.lookup.MissingCapability] using g2
  | DepthMismatch bf bl =>
    dsimp only
    apply ok_bind_spec
    refine WP.spec_bind (hset hI off hoff (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨h1, h2⟩
    unfold lift
    apply ok_bind_spec
    refine WP.spec_bind (hset h2 (core.num.U64.wrapping_add off 1#u64)
      (by rw [wadd_val off 1 (by omega) _ rfl]; simp; omega) (by rw [wadd_val off 1 (by omega) _ rfl]; omega) bl) ?_
    rintro ⟨i2, s2⟩ ⟨g1, g2⟩
    apply ok_bind_spec
    refine WP.spec_mono (hset g2 (core.num.U64.wrapping_add off 2#u64)
      (by rw [wadd_val off 2 (by omega) _ rfl]; simp; omega) (by rw [wadd_val off 2 (by omega) _ rfl]; omega) bf) ?_
    rintro ⟨i3, s3⟩ ⟨k1, k2⟩
    refine ⟨by simp only at k1 ⊢; rw [k1, wadd_val off 2 (by omega) _ rfl, hoff]; rfl, ?_⟩
    simpa [fl4LfMsg, fl4_abi.consts.lookup.DepthMismatch] using k2
  | GuardMismatch g bl gs =>
    dsimp only
    apply ok_bind_spec
    refine WP.spec_bind (hset hI off hoff (by omega) _) ?_
    rintro ⟨i1, s1⟩ ⟨h1, h2⟩
    unfold lift
    apply ok_bind_spec
    refine WP.spec_bind (hset h2 (core.num.U64.wrapping_add off 1#u64)
      (by rw [wadd_val off 1 (by omega) _ rfl]; simp; omega) (by rw [wadd_val off 1 (by omega) _ rfl]; omega) bl) ?_
    rintro ⟨i2, s2⟩ ⟨g1, g2⟩
    apply ok_bind_spec
    refine WP.spec_bind (hset g2 (core.num.U64.wrapping_add off 2#u64)
      (by rw [wadd_val off 2 (by omega) _ rfl]; simp; omega) (by rw [wadd_val off 2 (by omega) _ rfl]; omega) g) ?_
    rintro ⟨i3, s3⟩ ⟨k1, k2⟩
    apply ok_bind_spec
    refine WP.spec_mono (hset k2 (core.num.U64.wrapping_add off 3#u64)
      (by rw [wadd_val off 3 (by omega) _ rfl]; simp; omega) (by rw [wadd_val off 3 (by omega) _ rfl]; omega) gs) ?_
    rintro ⟨i4, s4⟩ ⟨l1, l2⟩
    refine ⟨by simp only at l1 ⊢; rw [l1, wadd_val off 3 (by omega) _ rfl, hoff]; rfl, ?_⟩
    simpa [fl4LfMsg, fl4_abi.consts.lookup.GuardMismatch] using l2

theorem mrInv_init (hR : EpStateRel T E R B (L.mem s0) σ0) (hSR : SR s0 σ0) {rcv : U64} {x0 : Fl4Spec.Tcb}
    (hk0 : σ0.kheap rcv.bv = some (.tcb x0)) (p : Fl4Spec.ObjRef) :
    MrInv (L := L) T E R B SR s0 σ0 rcv x0 p s0 [] := by
  unfold MrInv; rw [mrState_nil hk0]; exact ⟨hR, hSR, Agree.rfl'⟩

/-- The sender's TCB words do not change while the message is written. -/
theorem snd_word_eq {s0 s : S} (hP : EPlaced T E R B) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T)
    (hne : snd ≠ rcv) (hA : Agree (L.mem s0) (L.mem s) (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b)) {a : U64}
    (ha : Aligned a ∧ TF snd a) : L.mem s a = L.mem s0 a := by
  refine hA a ha.1 ⟨?_, ?_⟩
  · rintro ⟨r', hr'⟩
    have := tcb_disj hP hr hs hne; have := ha.2.range
    rw [regA_val (hP.tcb rcv hr) (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
  · rintro ⟨wp, hw, he⟩
    have := hP.bt wp hw snd hs; have := ha.2.range; have := congrArg UScalar.val he; omega

/-- **`set_mrs_fault` of a cap fault** into a receiver with a mapped IPC
buffer. -/
theorem set_mrs_fault_cap {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {c : Fl4Spec.ObjRef} {rp : Bool} {lf : Fl4Spec.LookupFailure} (hf : xs.tcbFault = some (.capFault c rp lf))
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p) :
    faults.set_mrs_fault st ar s a snd rcv rw ⦃ r =>
      r.1.val = (capFaultMsg (xs.tcbArch.tcbContext.userRegs .faultIP) c rp lf).length ∧
      MrInv (L := L) T E R B SR s σ rcv xr p r.2 (capFaultMsg (xs.tcbArch.tcbContext.userRegs .faultIP) c rp lf) ⦄ := by
  have hsa := hP.tcb snd hs
  have hxs := hR.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0, hw1, hlf⟩ := hfr
  have hset := fun {s' : S} {ms : List Fl4Spec.Word} (h : MrInv (L := L) T E R B SR s σ rcv xr p s' ms) =>
    set_mr_inv (L := L) hH hP hr hkr hrw0 hmr h
  have hpc : (L.mem s (regA snd layout.reg.FAULT_IP)).bv = xs.tcbArch.tcbContext.userRegs .faultIP := by
    rw [show layout.reg.FAULT_IP = regIdx .faultIP by unfold layout.reg.FAULT_IP; rfl]; exact hxs.regs _
  unfold faults.set_mrs_fault
  step as ⟨ty, hty'⟩
  step as ⟨w0, hw0'⟩
  step as ⟨w1, hw1'⟩
  step as ⟨w2, hw2'⟩
  step as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, if_pos (by unfold fl4_abi.consts.fault.CapFault; rfl)]
  refine WP.spec_bind (hset (mrInv_init hR hSR hkr p) 0#u64 rfl (by decide) _) ?_
  rintro ⟨_, s1⟩ ⟨-, hI1⟩
  refine WP.spec_bind (hset hI1 1#u64 rfl (by decide) _) ?_
  rintro ⟨_, s2⟩ ⟨-, hI2⟩
  refine WP.spec_bind (hset hI2 2#u64 rfl (by decide) _) ?_
  rintro ⟨_, s3⟩ ⟨-, hI3⟩
  unfold faults.lookup_failure
  step as ⟨lt, hlt⟩
  step as ⟨l0, hl0⟩
  step as ⟨l1, hl1⟩
  rw [snd_word_eq hP hs hr hne hI3.2.2 (a_lf hsa)] at hlt
  rw [snd_word_eq hP hs hr hne hI3.2.2 (a_lf0 hsa)] at hl0
  rw [snd_word_eq hP hs hr hne hI3.2.2 (a_lf1 hsa)] at hl1
  subst hlt hl0 hl1
  refine WP.spec_bind (decode_rel hlf) ?_
  rintro lfv hlfv
  refine WP.spec_mono (set_mrs_lookup_failure_rel (L := L) hH hP hr hkr hrw0 hmr hI3 3#u64 rfl (by simp) lfv) ?_
  rintro ⟨n, s4⟩ ⟨hn, hI4⟩
  have hlist : [(L.mem s (regA snd layout.reg.FAULT_IP)).bv, (L.mem s (tFw0A snd)).bv, (L.mem s (tFw1A snd)).bv] ++
      ((fl4LfMsg lfv).map UScalar.bv : List Fl4Spec.Word) =
      capFaultMsg (xs.tcbArch.tcbContext.userRegs .faultIP) c rp lf := by
    rw [hlfv, hpc, hw0, hw1]
    unfold capFaultMsg
    cases rp <;> rfl
  rw [List.nil_append, List.singleton_append, List.cons_append, List.singleton_append] at hI4
  refine ⟨?_, ?_⟩
  · simp only at hn
    rw [hn, ← hlist]
    have := congrArg List.length hlfv
    simp only [List.length_map] at this
    simp [this]; omega
  · rw [← hlist]
    simpa using hI4

theorem msgFromLookupFailure_len (lf : Fl4Spec.LookupFailure) : (Fl4Spec.msgFromLookupFailure lf).length ≤ 4 := by
  cases lf <;> simp [Fl4Spec.msgFromLookupFailure]

/-- The buffer words of a mapped buffer are aligned. -/
theorem bufAddr_aligned (hP : EPlaced T E R B) {w : U64} {p : Fl4Spec.ObjRef} (hm : BufMap B w p) (k : Nat) :
    (bufAddr p k).toNat % 8 = 0 := by
  have hp0 := (hP.balign _ (hm 0#u64 (by decide))).2
  simp only [bufAddr, show (0#u64 : U64).val = 0 from rfl, Nat.zero_mul, BitVec.add_zero] at hp0
  unfold bufAddr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [Fl4Spec.wordSize]; omega

/-- **`do_fault_transfer`** into a receiver with a mapped IPC buffer, given
that `set_mrs_fault` writes the l4v fault message `ms` and that the fault
type word is the l4v label. -/
theorem do_fault_transfer_full {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {f : Fl4Spec.Fault} (hf : xs.tcbFault = some f) {label : Fl4Spec.Data} {ms : List Fl4Spec.Word}
    (hmsg : Fl4Spec.makeFaultMsg (Z := Unit) f snd.bv σ = ({((label, ms), σ)}, False)) (hlen : ms.length < 120)
    {lab : U64} (hty : L.mem s (tFaultA snd) = lab)
    (hlab : lab.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits = label)
    {rw : U64} {p : Fl4Spec.ObjRef} (hmr : BufMap B rw p)
    (hu : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr p k) σ) (badge : U64)
    (hset : faults.set_mrs_fault st ar s a snd rcv rw ⦃ r => r.1.val = ms.length ∧
      MrInv (L := L) T E R B SR s σ rcv xr p r.2 ms ⦄) :
    ipc.do_fault_transfer st ar s a badge snd rcv rw ⦃ s' => ∃ σ',
      Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv (some p) σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      (∀ q, q ≠ rcv.bv → σ'.kheap q = σ.kheap q) ∧
      ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄ := by
  have hsa := hP.tcb snd hs
  have hal : ∀ q ∈ mrPairs ms, (bufAddr p q.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (bufAddr p q.1) σ := by
    intro q hq
    have := (List.of_mem_zip hq).1
    simp at this
    exact ⟨bufAddr_aligned hP hmr _, hu _ (by omega)⟩
  have hspec := doFaultTransfer_eq hks hkr hf hmsg p hal badge.bv
  unfold ipc.do_fault_transfer
  refine WP.spec_bind hset ?_
  rintro ⟨sent, s1⟩ ⟨hn, hR1, hS1, hA1⟩
  simp only at hn hR1 hS1 hA1
  step as ⟨ft, hft⟩
  rw [snd_word_eq hP hs hr hne hA1 (a_fault hsa), hty] at hft
  subst hft
  unfold msginfo.MessageInfo.new
  apply ok_bind_spec
  refine WP.spec_bind (set_msg_info_spec (L := L) s1 rcv ft sent (by omega)) ?_
  rintro s2 ⟨v, hs2, hv⟩
  step as ⟨s3, hs3⟩
  subst hs2 hs3
  have hkm : (mrState σ rcv.bv xr p ms).kheap rcv.bv =
      some (.tcb (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms))) := by simp [mrState, setUm]
  obtain ⟨hR2, hW2, hS2⟩ := write_reg_rel hP s1 _ hR1 hr hkm Fl4Spec.msg_info_register v
  rw [regIdx_msgInfo] at hR2 hW2
  obtain ⟨hR3, hW3, hS3⟩ := write_reg_rel hP _ _ hR2 hr (by simp only [updK_kheap, Function.update_self]; exact rfl)
    Fl4Spec.badge_register badge
  rw [regIdx_badge] at hR3 hW3
  have hvx : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (min ms.length Fl4Spec.msgMaxLength), 0, 0, label⟩ := by
    rw [hv, hlab, bv_ofNat_val sent hn, Nat.min_eq_left (by unfold Fl4Spec.msgMaxLength; omega)]; rfl
  have hfin : updK (updK (mrState σ rcv.bv xr p ms) rcv.bv (.tcb (setReg (withRegs xr
      (mrRegs xr.tcbArch.tcbContext.userRegs ms)) Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (setReg (setReg (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms)) Fl4Spec.msg_info_register v.bv)
        Fl4Spec.badge_register badge.bv)) =
      updK (mrState σ rcv.bv xr p ms) rcv.bv (.tcb (setReg (setReg
        (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms)) Fl4Spec.msg_info_register
        (Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (min ms.length Fl4Spec.msgMaxLength), 0, 0, label⟩))
        Fl4Spec.badge_register badge.bv)) := by
    simp only [updK, Function.update_idem]; rw [hvx]
  rw [hfin] at hR3
  have hS := hH.stable _ _ _ _ (hH.stable _ _ _ _ hS1 hW2 hS2) hW3 hS3
  rw [hfin] at hS
  have hra := hP.tcb rcv hr
  have a1 := a_reg hra Fl4Spec.msg_info_register
  have a2 := a_reg hra Fl4Spec.badge_register
  rw [regIdx_msgInfo] at a1
  rw [regIdx_badge] at a2
  have hAg : Agree (L.mem s) (L.mem (L.wr (L.wr s1 (regA rcv layout.reg.MSG_INFO) v) (regA rcv layout.reg.BADGE)
      badge)) (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) := by
    intro b hb hn
    rw [agree_wr (L := L) (s := L.wr s1 (regA rcv layout.reg.MSG_INFO) v) (v := badge) a2.1 b hb
        (fun h => hn.1 ⟨_, by rw [regIdx_badge]; exact h⟩),
      agree_wr (L := L) (s := s1) (v := v) a1.1 b hb (fun h => hn.1 ⟨_, by rw [regIdx_msgInfo]; exact h⟩)]
    exact hA1 b hb hn
  refine ⟨_, hspec, hR3, hS, hAg, fun q hq => ?_, setReg (setReg (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms))
    Fl4Spec.msg_info_register (Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (min ms.length Fl4Spec.msgMaxLength), 0, 0,
      label⟩)) Fl4Spec.badge_register badge.bv, by simp only [updK_kheap, Function.update_self], rfl⟩
  simp [mrState, setUm, hq]

/-- `do_fault_transfer_full` without the frame. -/
theorem do_fault_transfer_gen {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {f : Fl4Spec.Fault} (hf : xs.tcbFault = some f) {label : Fl4Spec.Data} {ms : List Fl4Spec.Word}
    (hmsg : Fl4Spec.makeFaultMsg (Z := Unit) f snd.bv σ = ({((label, ms), σ)}, False)) (hlen : ms.length < 120)
    {lab : U64} (hty : L.mem s (tFaultA snd) = lab)
    (hlab : lab.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits = label)
    {rw : U64} {p : Fl4Spec.ObjRef} (hmr : BufMap B rw p)
    (hu : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr p k) σ) (badge : U64)
    (hset : faults.set_mrs_fault st ar s a snd rcv rw ⦃ r => r.1.val = ms.length ∧
      MrInv (L := L) T E R B SR s σ rcv xr p r.2 ms ⦄) :
    ipc.do_fault_transfer st ar s a badge snd rcv rw ⦃ s' => ∃ σ',
      Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv (some p) σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ⦄ :=
  WP.spec_mono (do_fault_transfer_full hH hP s a σ hR hs hr hne hks hkr hf hmsg hlen hty hlab hmr hu badge hset)
    fun _ ⟨σ', h1, h2, h3, _⟩ => ⟨σ', h1, h2, h3⟩

/-- **`do_fault_transfer` of a cap fault** into a receiver with a mapped IPC
buffer refines l4v `do_fault_transfer`. -/
theorem do_fault_transfer_cap {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {c : Fl4Spec.ObjRef} {rp : Bool} {lf : Fl4Spec.LookupFailure} (hf : xs.tcbFault = some (.capFault c rp lf))
    {rw : U64} {p : Fl4Spec.ObjRef} (hrw0 : rw ≠ 0#u64) (hmr : BufMap B rw p)
    (hu : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr p k) σ) (badge : U64) :
    ipc.do_fault_transfer st ar s a badge snd rcv rw ⦃ s' => ∃ σ',
      Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv (some p) σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ⦄ := by
  have hfr := (hR.at_tcb hs hks).faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  have hlen : (capFaultMsg (xs.tcbArch.tcbContext.userRegs .faultIP) c rp lf).length < 120 := by
    have := msgFromLookupFailure_len lf; simp [capFaultMsg]; omega
  exact do_fault_transfer_gen hH hP s a σ hR hs hr hne hks hkr hf (makeFaultMsg_cap hks c rp lf) hlen hfr.1
    (by rw [mask52]; decide) hmr hu badge
    (set_mrs_fault_cap (ar := ar) hH hP s a σ hR hSR hs hr hne hks hkr hf hrw0 hmr)

end

end

end Fl4Proofs.P3.Endp

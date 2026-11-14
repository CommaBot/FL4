/-
P3 (DESIGN.md §9), endpoints: fault messages into a receiver **without an
IPC buffer** (l4v `set_mrs rcv None`: the first four words go to the message
registers, the rest are dropped, and the length is `min 4 len`; FL4
`msg::set_mr` returns `N_MSG_REGISTERS` past the registers, since 866cdae).

`mrStateN` is the state after l4v `set_mrs rcv None ms`; `MrInvN` the
invariant of the message being written. The fault messages are those of
`EpFault`, `EpFaultUs` and `EpFaultMore`.
-/
import Fl4Proofs.P3.EpComb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The state after `set_mrs rcv None ms`. -/
def mrStateN (σ : State Unit) (rcv : ObjRef) (x : Tcb) (ms : List Word) : State Unit :=
  updK σ rcv (.tcb (withRegs x (mrRegs x.tcbArch.tcbContext.userRegs ms)))

theorem setMrs_eqN {σ : State Unit} {rcv : ObjRef} {x : Tcb} (hk : σ.kheap rcv = some (.tcb x))
    (ms : List Word) :
    setMrs (Z := Unit) rcv none ms σ = ({(natToLen (min 4 ms.length), mrStateN σ rcv x ms)}, False) := by
  unfold setMrs
  rw [nd_bind_one (getTcb_eq hk), nd_pure_bind', nd_pure_bind']
  erw [nd_bind_one (setObject_eq (o' := .tcb (withRegs x (mrRegs x.tcbArch.tcbContext.userRegs ms))) hk rfl)]
  rw [nd_pure_bind']
  rfl

theorem mrStateN_nil {σ : State Unit} {rcv : ObjRef} {x : Tcb} (hk : σ.kheap rcv = some (.tcb x)) :
    mrStateN σ rcv x [] = σ := by
  have h1 : mrRegs x.tcbArch.tcbContext.userRegs [] = x.tcbArch.tcbContext.userRegs := by
    funext reg; simp [mrRegs]
  have h2 : withRegs x x.tcbArch.tcbContext.userRegs = x := rfl
  unfold mrStateN
  rw [h1, h2, updK_self hk]

theorem mrRegs_append_ge (ctx : Register → Word) (ms : List Word) (h : 4 ≤ ms.length) :
    ∀ ys : List Word, mrRegs ctx (ms ++ ys) = mrRegs ctx ms := by
  intro ys
  induction ys using List.reverseRecOn with
  | nil => simp
  | append_singleton ys y ih =>
    rw [← List.append_assoc, mrRegs_snoc_ge _ _ _ (by simp; omega), ih]

theorem mrStateN_append_ge (σ : State Unit) (rcv : ObjRef) (x : Tcb) (ms ys : List Word) (h : 4 ≤ ms.length) :
    mrStateN σ rcv x (ms ++ ys) = mrStateN σ rcv x ms := by
  unfold mrStateN; rw [mrRegs_append_ge _ _ h]

theorem mrStateN_snoc_lt (σ : State Unit) (rcv : ObjRef) (x : Tcb) (ms : List Word) (v : Word) (k : Nat)
    (hk : k = ms.length) (h : ms.length < 4) :
    updK (mrStateN σ rcv x ms) rcv
      (.tcb (setReg (withRegs x (mrRegs x.tcbArch.tcbContext.userRegs ms)) (mrIdx k) v)) =
    mrStateN σ rcv x (ms ++ [v]) := by
  subst hk
  unfold mrStateN
  rw [mrRegs_snoc_lt _ _ _ h, setReg_withRegs]
  simp only [updK, Function.update_idem]

/-- **`do_fault_transfer` into a receiver without an IPC buffer**, given the
fault message. -/
theorem doFaultTransfer_eqN {σ : State Unit} {snd rcv : ObjRef} {xs xr : Tcb}
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) {f : Fault}
    (hf : xs.tcbFault = some f) {label : Data} {ms : List Word}
    (hmsg : makeFaultMsg (Z := Unit) f snd σ = ({((label, ms), σ)}, False)) (badge : Data) :
    doFaultTransfer (Z := Unit) badge snd rcv none σ =
      ({((), updK (mrStateN σ rcv xr ms) rcv (.tcb (setReg (setReg
        (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms)) msg_info_register
        (messageInfoToData ⟨natToLen (min 4 ms.length), 0, 0, label⟩)) badge_register badge)))}, False) := by
  unfold doFaultTransfer
  rw [nd_bind_one (threadGet_eq _ hks), hf]
  dsimp only
  rw [nd_pure_bind', nd_bind_one hmsg]
  dsimp only
  rw [nd_bind_one (setMrs_eqN hkr ms)]
  have hkm : (mrStateN σ rcv xr ms).kheap rcv = some (.tcb (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms))) := by
    simp [mrStateN]
  unfold setMessageInfo
  rw [nd_bind_one (asUser_setRegister_eq _ _ hkm), asUser_setRegister_eq (x := setReg
    (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms)) msg_info_register
    (messageInfoToData ⟨natToLen (min 4 ms.length), 0, 0, label⟩)) _ _
    (by simp only [updK_kheap, Function.update_self])]
  simp only [updK, Function.update_idem]

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- The invariant of a message being written to a receiver without a
buffer. -/
def MrInvN (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) (s0 : S)
    (σ0 : Fl4Spec.State Unit) (rcv : U64) (x0 : Fl4Spec.Tcb) (s : S) (ms : List Fl4Spec.Word) : Prop :=
  EpStateRel T E R B (L.mem s) (mrStateN σ0 rcv.bv x0 ms) ∧ SR s (mrStateN σ0 rcv.bv x0 ms) ∧
    Agree (L.mem s0) (L.mem s) (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b)

theorem mrInvN_init {s0 : S} {σ0 : Fl4Spec.State Unit} (hR : EpStateRel T E R B (L.mem s0) σ0) (hSR : SR s0 σ0)
    {rcv : U64} {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap rcv.bv = some (.tcb x0)) :
    MrInvN (L := L) T E R B SR s0 σ0 rcv x0 s0 [] := by
  unfold MrInvN; rw [mrStateN_nil hk0]; exact ⟨hR, hSR, Agree.rfl'⟩

theorem mrInvN_append_ge {s0 : S} {σ0 : Fl4Spec.State Unit} {rcv : U64} {x0 : Fl4Spec.Tcb} {s : S}
    {ms : List Fl4Spec.Word} (hI : MrInvN (L := L) T E R B SR s0 σ0 rcv x0 s ms) (h : 4 ≤ ms.length)
    (ys : List Fl4Spec.Word) : MrInvN (L := L) T E R B SR s0 σ0 rcv x0 s (ms ++ ys) := by
  unfold MrInvN at hI ⊢; rw [mrStateN_append_ge _ _ _ _ _ h]; exact hI

/-- Writing message register `k < 4` of the receiver. -/
theorem set_reg_mr_invN (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    {rcv : U64} (hr : rcv ∈ T) {x0 : Fl4Spec.Tcb} {s : S} {ms : List Fl4Spec.Word}
    (hI : MrInvN (L := L) T E R B SR s0 σ0 rcv x0 s ms) (k : Nat) (hk : k = ms.length) (hk4 : k < 4) (v : U64) :
    obj.Tcb.set_reg st rcv s (regIdx (mrIdx k)) v ⦃ s1 => MrInvN (L := L) T E R B SR s0 σ0 rcv x0 s1 (ms ++ [v.bv]) ⦄ := by
  have hra := hP.tcb rcv hr
  have hks : (mrStateN σ0 rcv.bv x0 ms).kheap rcv.bv =
      some (.tcb (withRegs x0 (mrRegs x0.tcbArch.tcbContext.userRegs ms))) := by
    simp [mrStateN]
  refine WP.spec_mono (obj.Tcb.set_reg.spec s rcv _ v) ?_
  rintro s1 rfl
  obtain ⟨hR1, hW1, hS1⟩ := write_reg_rel hP s _ hI.1 hr hks (mrIdx k) v
  rw [mrStateN_snoc_lt _ _ _ _ _ k hk (by omega)] at hR1 hS1
  have ha := a_reg hra (mrIdx k)
  exact ⟨hR1, hH.stable _ _ _ _ hI.2.1 hW1 hS1, fun b hb hn =>
    (agree_wr (L := L) (s := s) (v := v) ha.1 b hb (fun h => hn.1 ⟨_, h⟩)).trans (hI.2.2 b hb hn)⟩

/-- **`set_mr`** of the next message word, without a buffer. -/
theorem set_mr_invN (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    {rcv : U64} (hr : rcv ∈ T) {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap rcv.bv = some (.tcb x0)) {s : S}
    {ms : List Fl4Spec.Word} (hI : MrInvN (L := L) T E R B SR s0 σ0 rcv x0 s ms) (i : U64) (hi : i.val = ms.length)
    (hi' : i.val < 120) (v : U64) :
    msg.set_mr st s rcv 0#u64 i v ⦃ r => r.1.val = min (i.val + 1) 4 ∧
      MrInvN (L := L) T E R B SR s0 σ0 rcv x0 r.2 (ms ++ [v.bv]) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  unfold msg.set_mr
  by_cases h4 : i < msg.N_MSG_REGISTERS
  · have hi4 : i.val < 4 := by have := (gt_iff_val).1 h4; omega
    simp only [h4, ↓reduceIte]
    refine WP.spec_bind (msg_register_spec i hi4) ?_
    rintro r rfl
    refine WP.spec_bind (set_reg_mr_invN (L := L) hH hP hr hI i.val hi hi4 v) ?_
    rintro s1 hI1
    unfold lift
    apply ok_bind_spec
    simp only [WP.spec_ok]
    refine ⟨?_, hI1⟩
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] <;> omega
  · have hi4 : 4 ≤ i.val := by
      have : ¬ i.val < 4 := fun h => h4 ((gt_iff_val).2 (by rw [hN]; exact h)); omega
    rw [if_neg h4]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨by rw [hN]; omega, mrInvN_append_ge hI (by omega) _⟩

/-- **`set_mrs_lookup_failure`**: the lookup-failure words, appended. -/
theorem set_mrs_lookup_failure_relN (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S}
    {σ0 : Fl4Spec.State Unit} {rcv : U64} (hr : rcv ∈ T) {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap rcv.bv = some (.tcb x0))
    {s : S} {ms : List Fl4Spec.Word}
    (hI : MrInvN (L := L) T E R B SR s0 σ0 rcv x0 s ms) (off : U64) (hoff : off.val = ms.length)
    (hlen : ms.length + 4 ≤ 120) (lfv : error.LookupFault) :
    faults.set_mrs_lookup_failure st s rcv 0#u64 lfv off ⦃ r => r.1.val = min (ms.length + (fl4LfMsg lfv).length) 4 ∧
      MrInvN (L := L) T E R B SR s0 σ0 rcv x0 r.2 (ms ++ ((fl4LfMsg lfv).map UScalar.bv : List Fl4Spec.Word)) ⦄ := by
  have hset := fun {s : S} {ms : List Fl4Spec.Word} (h : MrInvN (L := L) T E R B SR s0 σ0 rcv x0 s ms) =>
    set_mr_invN (L := L) hH hP hr hk0 h
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
    refine ⟨by simp only at h1; rw [h1, hoff]; simp only [fl4LfMsg, List.length_cons, List.length_nil], ?_⟩
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
    refine ⟨by simp only at g1 ⊢; rw [g1, wadd_val off 1 (by omega) _ rfl, hoff]; simp only [fl4LfMsg, List.length_cons, List.length_nil], ?_⟩
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
    refine ⟨by simp only at k1 ⊢; rw [k1, wadd_val off 2 (by omega) _ rfl, hoff]; simp only [fl4LfMsg, List.length_cons, List.length_nil], ?_⟩
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
    refine ⟨by simp only at l1 ⊢; rw [l1, wadd_val off 3 (by omega) _ rfl, hoff]; simp only [fl4LfMsg, List.length_cons, List.length_nil], ?_⟩
    simpa [fl4LfMsg, fl4_abi.consts.lookup.GuardMismatch] using l2

/-- **`set_mrs_fault` of a cap fault** into a receiver with a mapped IPC
buffer. -/
theorem set_mrs_fault_capN {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {c : Fl4Spec.ObjRef} {rp : Bool} {lf : Fl4Spec.LookupFailure} (hf : xs.tcbFault = some (.capFault c rp lf))
    :
    faults.set_mrs_fault st ar s a snd rcv 0#u64 ⦃ r =>
      r.1.val = min (capFaultMsg (xs.tcbArch.tcbContext.userRegs .faultIP) c rp lf).length 4 ∧
      MrInvN (L := L) T E R B SR s σ rcv xr r.2 (capFaultMsg (xs.tcbArch.tcbContext.userRegs .faultIP) c rp lf) ⦄ := by
  have hsa := hP.tcb snd hs
  have hxs := hR.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0, hw1, hlf⟩ := hfr
  have hset := fun {s' : S} {ms : List Fl4Spec.Word} (h : MrInvN (L := L) T E R B SR s σ rcv xr s' ms) =>
    set_mr_invN (L := L) hH hP hr hkr h
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
  refine WP.spec_bind (hset (mrInvN_init hR hSR hkr) 0#u64 rfl (by decide) _) ?_
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
  refine WP.spec_mono (set_mrs_lookup_failure_relN (L := L) hH hP hr hkr hI3 3#u64 rfl (by simp) lfv) ?_
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
    simp [this] <;> omega
  · rw [← hlist]
    simpa using hI4


/-- The first loop of `copy_mrs_fault`, without a buffer. -/
theorem copy_mrs_fault_loop0_relN (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s0 : S)
    (σ0 : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s0) σ0) (hSR : SR s0 σ0)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {x0 : Fl4Spec.Tcb}
    (hk0 : σ0.kheap rcv.bv = some (.tcb x0)) {regs : Fl4Spec.Register → Fl4Spec.Word}
    (hreg : ∀ r, (L.mem s0 (regA snd (regIdx r))).bv = regs r)
    {sl : Slice U64} {rl : List Fl4Spec.Register} (hsl : sl.val = rl.map regIdx) (hn : rl.length ≤ 120) :
    faults.copy_mrs_fault_loop0 st s0 snd rcv sl 0#usize ⦃ r =>
      r.2.val = min rl.length 4 ∧
      MrInvN (L := L) T E R B SR s0 σ0 rcv x0 r.1 ((rl.take r.2.val).map regs) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  have hlen := slice_len_val hsl
  unfold faults.copy_mrs_fault_loop0
  apply loop.spec_decr_nat (measure := fun x => 4 - x.2.val)
    (inv := fun x => x.2.val ≤ min rl.length 4 ∧
      MrInvN (L := L) T E R B SR s0 σ0 rcv x0 x.1 ((rl.take x.2.val).map regs))
  · rintro ⟨s', i⟩ ⟨hi4, hI⟩
    unfold faults.copy_mrs_fault_loop0.body
    simp only at hi4 hI ⊢
    by_cases h1 : i < Slice.len sl
    · have hin : i.val < rl.length := by have := us_lt_iff.1 h1; omega
      simp only [h1, ↓reduceIte]
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = i.val := by rw [hi2]; exact cast_us i (by omega)
      by_cases h2 : i2 < msg.N_MSG_REGISTERS
      · have hi : i.val < 4 := by have := (gt_iff_val).1 h2; omega
        simp only [h2, ↓reduceIte]
        step as ⟨r, hr'⟩
        step as ⟨v, hv⟩
        step as ⟨i4, hi4'⟩
        have hi4v : i4.val = i.val := by rw [hi4']; exact cast_us i (by omega)
        refine WP.spec_bind (msg_register_spec i4 (by omega)) ?_
        rintro r5 rfl
        have hlen' : ((rl.take i.val).map regs).length = i.val := by simp; omega
        refine WP.spec_bind (set_reg_mr_invN (L := L) hH hP hr hI i4.val (by omega) (by omega) v) ?_
        rintro s1 hI1
        step as ⟨i6, hi6⟩
        have hi6v : i6.val = i.val + 1 := by simpa using hi6
        have hvb : v.bv = regs rl[i.val] := by
          rw [hv, hr', getElem_regs hsl, snd_word_eq hP hs hr hne hI.2.2 (a_reg (hP.tcb snd hs) _), hreg]
        refine ⟨by omega, ?_, by omega⟩
        rw [hi6v, take_succ_map regs rl i.val hin, ← hvb]
        exact hI1
      · simp only [h2, ↓reduceIte, WP.spec_ok]
        have hi : i.val = 4 := by
          have h2' : ¬ i.val < 4 := fun h => h2 ((gt_iff_val).2 (by rw [hN]; omega))
          omega
        exact ⟨by omega, hI⟩
    · simp only [h1, ↓reduceIte, WP.spec_ok]
      have : ¬ i.val < rl.length := fun h => h1 (us_lt_iff.2 (by omega))
      exact ⟨by omega, hI⟩
  · refine ⟨by simp, ?_⟩
    have := mrInvN_init (L := L) (SR := SR) (B := B) hR hSR hk0
    simpa using this

/-- **`copy_mrs_fault`** without a buffer: the first four words. -/
theorem copy_mrs_fault_relN (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S)
    (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xr : Fl4Spec.Tcb}
    (hkr : σ.kheap rcv.bv = some (.tcb xr)) {regs : Fl4Spec.Register → Fl4Spec.Word}
    (hreg : ∀ r, (L.mem s (regA snd (regIdx r))).bv = regs r)
    {sl : Slice U64} {rl : List Fl4Spec.Register} (hsl : sl.val = rl.map regIdx) (hn : rl.length ≤ 120) :
    faults.copy_mrs_fault st s snd rcv sl 0#u64 ⦃ s2 =>
      MrInvN (L := L) T E R B SR s σ rcv xr s2 (rl.map regs) ⦄ := by
  unfold faults.copy_mrs_fault
  refine WP.spec_bind (copy_mrs_fault_loop0_relN (L := L) hH hP s σ hR hSR hs hr hne hkr hreg hsl hn) ?_
  rintro ⟨s1, i⟩ ⟨hi, hI⟩
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  show (ok s1) ⦃ _ ⦄
  simp only [WP.spec_ok]
  simp only at hi hI
  by_cases hn4 : rl.length ≤ 4
  · rw [hi, Nat.min_eq_left hn4, List.take_of_length_le (le_refl _)] at hI; exact hI
  · rw [hi, Nat.min_eq_right (by omega)] at hI
    have : rl.map regs = (rl.take 4).map regs ++ (rl.drop 4).map regs := by
      rw [← List.map_append, List.take_append_drop]
    rw [this]
    exact mrInvN_append_ge hI (by simp; omega) _

/-- **`set_mrs_fault` of an unknown-syscall fault**, without a buffer. -/
theorem set_mrs_fault_unknownN {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {n : Fl4Spec.Word} (hf : xs.tcbFault = some (.unknownSyscallException n)) :
    faults.set_mrs_fault st ar s a snd rcv 0#u64 ⦃ r =>
      r.1.val = min (usMsg xs.tcbArch.tcbContext.userRegs n).length 4 ∧
      MrInvN (L := L) T E R B SR s σ rcv xr r.2 (usMsg xs.tcbArch.tcbContext.userRegs n) ⦄ := by
  have hxs := hR.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  unfold faults.set_mrs_fault
  step as ⟨ty, hty'⟩
  step as ⟨w0, hw0'⟩
  step as ⟨w1, hw1'⟩
  step as ⟨w2, hw2'⟩
  step as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.UnknownSyscall; rfl))]
  unfold lift
  apply ok_bind_spec
  refine WP.spec_bind (copy_mrs_fault_relN (L := L) hH hP s σ hR hSR hs hr hne hkr (fun r => hxs.regs r)
    syscall_slice_val (by decide)) ?_
  rintro s2 hI2
  refine WP.spec_mono (set_mr_invN (L := L) hH hP hr hkr hI2 18#u64 (by simp [syscall_len]) (by decide)
    (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s3⟩ ⟨hk, hI3⟩
  rw [hw0] at hI3
  exact ⟨by rw [usMsg_length]; simpa using hk, hI3⟩

/-- **`set_mrs_fault` of a user exception**, without a buffer. -/
theorem set_mrs_fault_userN {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {e c : Fl4Spec.Word} (hf : xs.tcbFault = some (.userException e c)) :
    faults.set_mrs_fault st ar s a snd rcv 0#u64 ⦃ r =>
      r.1.val = min (ueMsg xs.tcbArch.tcbContext.userRegs e c).length 4 ∧
      MrInvN (L := L) T E R B SR s σ rcv xr r.2 (ueMsg xs.tcbArch.tcbContext.userRegs e c) ⦄ := by
  have hxs := hR.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0, hw1⟩ := hfr
  unfold faults.set_mrs_fault
  step as ⟨ty, hty'⟩
  step as ⟨w0, hw0'⟩
  step as ⟨w1, hw1'⟩
  step as ⟨w2, hw2'⟩
  step as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.UserException; rfl))]
  unfold lift
  apply ok_bind_spec
  refine WP.spec_bind (copy_mrs_fault_relN (L := L) hH hP s σ hR hSR hs hr hne hkr (fun r => hxs.regs r)
    exc_slice_val (by decide)) ?_
  rintro s2 hI2
  refine WP.spec_bind (set_mr_invN (L := L) hH hP hr hkr hI2 3#u64 (by simp [Fl4Spec.exceptionMessage])
    (by decide) (L.mem s (tFw0A snd))) ?_
  rintro ⟨k3, s3⟩ ⟨-, hI3⟩
  refine WP.spec_mono (set_mr_invN (L := L) hH hP hr hkr hI3 4#u64 (by simp [Fl4Spec.exceptionMessage])
    (by decide) (L.mem s (tFw1A snd))) ?_
  rintro ⟨k4, s4⟩ ⟨hk4, hI4⟩
  rw [hw0, hw1, List.append_assoc] at hI4
  exact ⟨by rw [ueMsg_length]; simpa using hk4, hI4⟩

/-- **`set_mrs_fault` of a timeout fault** of a sender without a
scheduling context, without a buffer. -/
theorem set_mrs_fault_timeoutN {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {b : Fl4Spec.Word} (hf : xs.tcbFault = some (.timeout b)) (hsc : L.mem s (scA snd) = 0#u64) :
    faults.set_mrs_fault st ar s a snd rcv 0#u64 ⦃ r =>
      r.1.val = min [b].length 4 ∧ MrInvN (L := L) T E R B SR s σ rcv xr r.2 [b] ⦄ := by
  have hxs := hR.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0⟩ := hfr
  unfold faults.set_mrs_fault
  step as ⟨ty, hty'⟩
  step as ⟨w0, hw0'⟩
  step as ⟨w1, hw1'⟩
  step as ⟨w2, hw2'⟩
  step as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.Timeout; rfl))]
  step with obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  unfold obj.Sc.is_null
  apply ok_bind_spec
  simp only [hsc, decide_true, ↓reduceIte]
  refine WP.spec_mono (set_mr_invN (L := L) hH hP hr hkr (mrInvN_init hR hSR hkr) 0#u64 rfl
    (by decide) (L.mem s (tFw0A snd))) ?_
  rintro ⟨k, s1⟩ ⟨hk, hI⟩
  rw [hw0, List.nil_append] at hI
  exact ⟨by simpa using hk, hI⟩

/-- **`set_mrs_fault` of a VM fault**, without a buffer. -/
theorem set_mrs_fault_vmN {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {va : Fl4Spec.VSpaceRef} {d : List Fl4Spec.Word} (hf : xs.tcbFault = some (.archFault (.vmFault va d))) :
    faults.set_mrs_fault st ar s a snd rcv 0#u64 ⦃ r =>
      r.1.val = min (vmMsg (xs.tcbArch.tcbContext.userRegs .faultIP) va d).length 4 ∧
      MrInvN (L := L) T E R B SR s σ rcv xr r.2 (vmMsg (xs.tcbArch.tcbContext.userRegs .faultIP) va d) ⦄ := by
  have hxs := hR.at_tcb hs hks
  have hfr := hxs.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  obtain ⟨hty, hw0, hd⟩ := hfr
  have hset := fun {s' : S} {ms : List Fl4Spec.Word} (h : MrInvN (L := L) T E R B SR s σ rcv xr s' ms) =>
    set_mr_invN (L := L) hH hP hr hkr h
  have hpc : (L.mem s (regA snd layout.reg.FAULT_IP)).bv = xs.tcbArch.tcbContext.userRegs .faultIP := by
    rw [show layout.reg.FAULT_IP = regIdx .faultIP by unfold layout.reg.FAULT_IP; rfl]; exact hxs.regs _
  unfold faults.set_mrs_fault
  step as ⟨ty, hty'⟩
  step as ⟨w0, hw0'⟩
  step as ⟨w1, hw1'⟩
  step as ⟨w2, hw2'⟩
  step as ⟨pc, hpc'⟩
  subst hty' hw0' hw1' hw2' hpc'
  rw [hty, ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.CapFault; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.UserException; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.Timeout; decide),
    ite_eq_right_of_eq_false _ _ (by unfold fl4_abi.consts.fault.DebugException; decide),
    ite_eq_left_of_eq_true _ _ (eq_true (by unfold fl4_abi.consts.fault.VMFault; rfl))]
  refine WP.spec_bind (hset (mrInvN_init hR hSR hkr) 0#u64 rfl (by decide) _) ?_
  rintro ⟨_, s1⟩ ⟨-, hI1⟩
  refine WP.spec_bind (hset hI1 1#u64 rfl (by decide) _) ?_
  rintro ⟨_, s2⟩ ⟨-, hI2⟩
  refine WP.spec_bind (hset hI2 2#u64 rfl (by decide) _) ?_
  rintro ⟨_, s3⟩ ⟨-, hI3⟩
  refine WP.spec_mono (hset hI3 3#u64 rfl (by decide) _) ?_
  rintro ⟨k, s4⟩ ⟨hk, hI4⟩
  have hl : [(L.mem s (regA snd layout.reg.FAULT_IP)).bv] ++ [(L.mem s (tFw0A snd)).bv] ++
      [(L.mem s (tFw2A snd)).bv] ++ [(L.mem s (tFw1A snd)).bv] =
      vmMsg (xs.tcbArch.tcbContext.userRegs .faultIP) va d := by
    rw [hpc, hw0, hd]; rfl
  rw [List.nil_append, hl] at hI4
  exact ⟨by rw [← hl]; simpa using hk, hI4⟩

/-- **`do_fault_transfer` into a receiver without an IPC buffer**, given
that `set_mrs_fault` writes the l4v message `ms` (returning `min |ms| 4`)
and that the fault type word is the l4v label. -/
theorem do_fault_transfer_fullN {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {f : Fl4Spec.Fault} (hf : xs.tcbFault = some f) {label : Fl4Spec.Data} {ms : List Fl4Spec.Word}
    (hmsg : Fl4Spec.makeFaultMsg (Z := Unit) f snd.bv σ = ({((label, ms), σ)}, False))
    {lab : U64} (hty : L.mem s (tFaultA snd) = lab)
    (hlab : lab.bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits = label) (badge : U64)
    (hset : faults.set_mrs_fault st ar s a snd rcv 0#u64 ⦃ r => r.1.val = min ms.length 4 ∧
      MrInvN (L := L) T E R B SR s σ rcv xr r.2 ms ⦄) :
    ipc.do_fault_transfer st ar s a badge snd rcv 0#u64 ⦃ s' => ∃ σ',
      Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv none σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      (∀ q, q ≠ rcv.bv → σ'.kheap q = σ.kheap q) ∧
      ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄ := by
  have hsa := hP.tcb snd hs
  have hspec := doFaultTransfer_eqN hks hkr hf hmsg badge.bv
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
  have hkm : (mrStateN σ rcv.bv xr ms).kheap rcv.bv =
      some (.tcb (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms))) := by simp [mrStateN]
  obtain ⟨hR2, hW2, hS2⟩ := write_reg_rel hP s1 _ hR1 hr hkm Fl4Spec.msg_info_register v
  rw [regIdx_msgInfo] at hR2 hW2
  obtain ⟨hR3, hW3, hS3⟩ := write_reg_rel hP _ _ hR2 hr (by simp only [updK_kheap, Function.update_self]; exact rfl)
    Fl4Spec.badge_register badge
  rw [regIdx_badge] at hR3 hW3
  have hvx : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (min 4 ms.length), 0, 0, label⟩ := by
    rw [hv, hlab, bv_ofNat_val sent hn, Nat.min_comm]; rfl
  have hfin : updK (updK (mrStateN σ rcv.bv xr ms) rcv.bv (.tcb (setReg (withRegs xr
      (mrRegs xr.tcbArch.tcbContext.userRegs ms)) Fl4Spec.msg_info_register v.bv))) rcv.bv
      (.tcb (setReg (setReg (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms)) Fl4Spec.msg_info_register v.bv)
        Fl4Spec.badge_register badge.bv)) =
      updK (mrStateN σ rcv.bv xr ms) rcv.bv (.tcb (setReg (setReg
        (withRegs xr (mrRegs xr.tcbArch.tcbContext.userRegs ms)) Fl4Spec.msg_info_register
        (Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (min 4 ms.length), 0, 0, label⟩))
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
    Fl4Spec.msg_info_register (Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (min 4 ms.length), 0, 0,
      label⟩)) Fl4Spec.badge_register badge.bv, by simp only [updK_kheap, Function.update_self], rfl⟩
  simp [mrStateN, hq]

/-- **`do_fault_transfer`** of any fault but a timeout with a scheduling
context, into a receiver without an IPC buffer, refines l4v
`do_fault_transfer rcv None`. -/
theorem do_fault_transfer_relN {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {f : Fl4Spec.Fault} (hf : xs.tcbFault = some f) (hok : FaultOK (L := L) s snd xs f) (badge : U64) :
    ipc.do_fault_transfer st ar s a badge snd rcv 0#u64 ⦃ s' => ∃ σ',
      Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv none σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      (∀ q, q ≠ rcv.bv → σ'.kheap q = σ.kheap q) ∧
      ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄ := by
  have hfr := (hR.at_tcb hs hks).faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  cases f with
  | capFault c rp lf =>
    exact do_fault_transfer_fullN hH hP s a σ hs hr hne hks hkr hf (makeFaultMsg_cap hks c rp lf) hfr.1
      (by rw [mask52]; decide) badge (set_mrs_fault_capN (ar := ar) hH hP s a σ hR hSR hs hr hne hks hkr hf)
  | unknownSyscallException n =>
    exact do_fault_transfer_fullN hH hP s a σ hs hr hne hks hkr hf (makeFaultMsg_unknown hks n) hfr.1
      (by rw [mask52]; decide) badge (set_mrs_fault_unknownN (ar := ar) hH hP s a σ hR hSR hs hr hne hks hkr hf)
  | userException e c =>
    exact do_fault_transfer_fullN hH hP s a σ hs hr hne hks hkr hf (makeFaultMsg_user hks e c) hfr.1
      (by rw [mask52]; decide) badge (set_mrs_fault_userN (ar := ar) hH hP s a σ hR hSR hs hr hne hks hkr hf)
  | timeout b =>
    exact do_fault_transfer_fullN hH hP s a σ hs hr hne hks hkr hf (makeFaultMsg_timeout hks hok.1 b) hfr.1
      (by rw [mask52]; decide) badge (set_mrs_fault_timeoutN (ar := ar) hH hP s a σ hR hSR hs hr hks hkr hf hok.2)
  | archFault af =>
    cases af with
    | vmFault va d =>
      exact do_fault_transfer_fullN hH hP s a σ hs hr hne hks hkr hf (makeFaultMsg_vm hks va d) hfr.1
        (by rw [mask52]; decide) badge (set_mrs_fault_vmN (ar := ar) hH hP s a σ hR hSR hs hr hks hkr hf)

/-- **`do_ipc_transfer` of a faulted sender** into a receiver without an
IPC buffer refines l4v `do_ipc_transfer`. -/
theorem do_ipc_transfer_faultN {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR)
    (hBf : EpBufHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {f : Fl4Spec.Fault} (hf : xs.tcbFault = some f) (hok : FaultOK (L := L) s snd xs f)
    (hrb : ipcBufOf true xr = none) (ep badge : U64) (grant : Bool) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      EpStateRel T E R B (L.mem s') σ' ∧ SR s' σ' ∧
      Agree (L.mem s) (L.mem s') (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b) ∧
      (∀ q, q ≠ rcv.bv → σ'.kheap q = σ.kheap q) ∧
      ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄ := by
  have hxs := hR.at_tcb hs hks
  have hspec : Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
      Fl4Spec.doFaultTransfer (Z := Unit) badge.bv snd.bv rcv.bv none σ := by
    unfold Fl4Spec.doIpcTransfer
    rw [nd_bind_one (lookupIpcBuffer_eq hkr true), hrb, nd_bind_one (threadGet_eq _ hks), hf]
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (hBf.lookup s σ rcv xr true hR hSR hr hkr) ?_
  rintro rw hrw
  obtain rfl : rw = 0#u64 := hrw.2 hrb
  step as ⟨ft, hft⟩
  have hft0 : ¬ ft = fl4_abi.consts.fault.NullFault := by
    intro h
    have : L.mem s (tFaultA snd) = 0#u64 := by rw [← hft, h]; unfold fl4_abi.consts.fault.NullFault; rfl
    rw [hxs.fault0.1 this] at hf; cases hf
  simp only [hft0, ↓reduceIte]
  refine WP.spec_mono (do_fault_transfer_relN hH hP s a σ hR hSR hs hr hne hks hkr hf hok badge) ?_
  rintro s' ⟨σ', h1, h2⟩
  exact ⟨σ', hspec.trans h1, h2⟩

end

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **`do_ipc_transfer` of a faulted sender**, no receive buffer, against
the combined relation. -/
theorem do_ipc_transfer_fault_combN (hC : CombHyps st N T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hP : CPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ)
    (hSR : SR s σ) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {f : Fl4Spec.Fault} (hf : xs.tcbFault = some f) (hok : FaultOK (L := L) s snd xs f)
    (hrb : ipcBufOf true xr = none) (ep badge : U64) (grant : Bool) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      CombRel N T E R B (L.mem s') σ' ∧ SR s' σ' ⦄ := by
  refine WP.spec_mono (do_ipc_transfer_faultN (ar := ar) hC.epHyps hBf hP.e s a σ hRC.2 hSR hs hr hne hks hkr hf
    hok hrb ep badge grant) ?_
  rintro s' ⟨σ', h1, h2, h3, h4, h5, x', h6, h7⟩
  exact ⟨σ', h1, ⟨ntfn_lift_rcv hP hRC.1 h2 hr h4 h5 hkr h6 h7, h2⟩, h3⟩

end

end

end Fl4Proofs.P3.Endp

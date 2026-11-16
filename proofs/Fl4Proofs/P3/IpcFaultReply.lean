/-
P3 (DESIGN.md §9), IPC: **the fault reply of `do_reply_transfer`**
(`handle_fault_reply`, `clear_fault`, `set_thread_state`) against l4v's
(`handle_fault_reply`, the fault cleared, `set_thread_state`):
`fault_reply_top`, which is `ReplyHyps.faultReply`.

* `sanitise_eq`: FL4's `regs::sanitise` of a register is l4v's
  `sanitise_register` (the flags by `flags_sanitise`).
* `cmfr_loop0`, `cmfr_loop1`, `cmfr_top`: `copy_mrs_fault_reply` over a
  register list sets the receiver's registers to the sanitised words of
  l4v's `get_mrs` (`specMrs`, `getMrs_eq`): message registers 0..3, then
  buffer words 5.., to the shorter of the list and the message length.
* `handle_fault_reply_rel`: by the fault's kind (`FaultRel`): a cap fault
  or a VM fault restarts; an unknown syscall, a user exception or a timeout
  copies `SYSCALL_MESSAGE`, `EXCEPTION_MESSAGE` or `TIMEOUT_REPLY_MESSAGE`
  (l4v's `syscallMessage`, `exceptionMessage`, `timeoutMessage`) and
  restarts on label 0.
-/
import Fl4Proofs.P3.IpcReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- The TCB `x` with the registers `rs` set to the sanitised `vs` (pairwise,
to the shorter list). -/
def sanRegs (x : Tcb) : List Register → List Word → Tcb
  | r :: rs, v :: vs => sanRegs (setReg x r (sanitiseRegister false r v)) rs vs
  | _, _ => x

/-- The user context `uc` with the registers `rs` set to the sanitised `vs`. -/
def ucSan (uc : UserContext) : List Register → List Word → UserContext
  | r :: rs, v :: vs => ucSan (setRegUc uc r (sanitiseRegister false r v)) rs vs
  | _, _ => uc

theorem zipSan_uc (uc : UserContext) : ∀ (rs : List Register) (vs : List Word),
    NonDet.zipWithMx (fun r v => setRegister r (sanitiseRegister false r v)) rs vs uc =
      ({((), ucSan uc rs vs)}, False)
  | r :: rs, v :: vs => by
    show (NonDet.bind (setRegister r _) fun _ => _) uc = _
    rw [show NonDet.bind (setRegister r (sanitiseRegister false r v)) (fun _ =>
        NonDet.zipWithMx (fun r v => setRegister r (sanitiseRegister false r v)) rs vs) =
        (setRegister r (sanitiseRegister false r v) >>= fun _ =>
        NonDet.zipWithMx (fun r v => setRegister r (sanitiseRegister false r v)) rs vs) from rfl]
    rw [nd_bind_one (show setRegister r (sanitiseRegister false r v) uc =
      ({((), setRegUc uc r (sanitiseRegister false r v))}, False) from rfl), zipSan_uc _ rs vs]
    rfl
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem sanRegs_eq : ∀ (x : Tcb) (rs : List Register) (vs : List Word),
    ({ x with tcbArch := archTcbContextSet (ucSan (archTcbContextGet x.tcbArch) rs vs) x.tcbArch } : Tcb) =
      sanRegs x rs vs
  | x, r :: rs, v :: vs => by
    rw [sanRegs, ← sanRegs_eq _ rs vs]; rfl
  | x, [], _ => rfl
  | x, _ :: _, [] => rfl

/-- `as_user` of a computation with one outcome. -/
theorem asUser_det {α : Type} {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    {f : UserMonad α} {a : α} {uc' : UserContext}
    (hf : f (archTcbContextGet x.tcbArch) = ({(a, uc')}, False)) :
    asUser (Z := Unit) t f σ =
      ({(a, updK σ t (.tcb { x with tcbArch := archTcbContextSet uc' x.tcbArch }))}, False) := by
  unfold asUser
  show (NonDet.getsThe _ >>= _) σ = _
  rw [nd_bind_one (getTcb_eq hk)]
  show ((pure _ : NonDet (State Unit) UserContext) >>= _) σ = _
  rw [nd_pure_bind']
  show (NonDet.selectF _ >>= _) σ = _
  rw [nd_bind_one (show NonDet.selectF (σ := State Unit) (f (archTcbContextGet x.tcbArch)) σ =
      (({((a, uc'), σ)}), False) by
    rw [hf]; simp only [NonDet.selectF]
    ext ⟨a', b⟩ <;> simp)]
  show ((pure _ : NonDet (State Unit) Tcb) >>= _) σ = _
  rw [nd_pure_bind']
  exact (nd_bind_one (setObject_eq (o' := KernelObject.tcb { x with tcbArch := archTcbContextSet uc' x.tcbArch })
    hk rfl) _).trans rfl

theorem asUser_zipSan {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (rs : List Register) (vs : List Word) :
    asUser (Z := Unit) t (NonDet.zipWithMx (fun r v => setRegister r (sanitiseRegister false r v)) rs vs) σ =
      ({((), updK σ t (.tcb (sanRegs x rs vs)))}, False) := by
  rw [asUser_det hk (zipSan_uc _ rs vs), sanRegs_eq]

theorem sanRegs_snoc : ∀ (x : Tcb) (rs : List Register) (vs : List Word), rs.length = vs.length →
    ∀ r v, sanRegs x (rs ++ [r]) (vs ++ [v]) = setReg (sanRegs x rs vs) r (sanitiseRegister false r v)
  | x, [], [], _, r, v => rfl
  | x, r' :: rs, v' :: vs, h, r, v => by
    simp only [List.cons_append, sanRegs]
    exact sanRegs_snoc _ rs vs (by simpa using h) r v
  | _, [], _ :: _, h, _, _ => by simp at h
  | _, _ :: _, [], h, _, _ => by simp at h

theorem sanRegs_take : ∀ (x : Tcb) (rs : List Register) (vs : List Word) (k : Nat),
    min rs.length vs.length ≤ k → sanRegs x (rs.take k) (vs.take k) = sanRegs x rs vs
  | x, [], _, k, _ => by simp [sanRegs]
  | x, _ :: _, [], k, _ => by cases k <;> simp [sanRegs]
  | x, r :: rs, v :: vs, 0, h => by simp at h
  | x, r :: rs, v :: vs, k + 1, h => by
    simp only [List.take_succ_cons, sanRegs]
    exact sanRegs_take _ rs vs k (by simp at h; omega)

/-- l4v `get_mrs`' result: the message registers, then the buffer words
5..120, the first `len`. -/
def specMrs (regs : Register → Word) (sbo : Option ObjRef) (um : Word → Word8) (len : Nat) : List Word :=
  ((msg_registers.map regs) ++ (match sbo with
    | none => []
    | some sb => (List.range' 5 116).map fun k => loadWordAt um (bufAddr sb k))).take len

theorem getMrs_eq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (sbo : Option ObjRef) (hal : ∀ sb, sbo = some sb → ∀ k, k < 128 → (bufAddr sb k).toNat % 8 = 0)
    (mi : MessageInfo) :
    getMrs (Z := Unit) t sbo mi σ =
      ({(specMrs x.tcbArch.tcbContext.userRegs sbo σ.machineState.underlyingMemory (unat mi.miLength), σ)},
        False) := by
  unfold getMrs
  rw [nd_bind_one (threadGet_eq _ hk), nd_pure_bind']
  cases sbo with
  | none => dsimp only; rw [nd_pure_bind', nd_pure_apply']; rfl
  | some sb =>
    dsimp only
    rw [nd_bind_one (Fl4Proofs.P3.Ipc.mapM_load sb _ σ fun k hk' => hal sb rfl k (by
      simp [msg_registers, msgRegisters, msgMaxLength] at hk'; omega))]
    rw [nd_pure_apply']; rfl

theorem specMrs_lo (regs : Register → Word) (sbo : Option ObjRef) (um : Word → Word8) (len i : Nat) (hi : i < 4)
    (hil : i < len) : i < (specMrs regs sbo um len).length ∧ (specMrs regs sbo um len)[i]! = regs (mrIdx i) := by
  have hl : i < ((msg_registers.map regs) ++ (match sbo with
      | none => []
      | some sb => (List.range' 5 116).map fun k => loadWordAt um (bufAddr sb k))).length := by
    simp [msg_registers, msgRegisters]; omega
  have hlt : i < (specMrs regs sbo um len).length := by
    unfold specMrs; rw [List.length_take]; omega
  refine ⟨hlt, ?_⟩
  rw [getElem!_pos _ i hlt]
  unfold specMrs mrIdx
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp [List.getElem_append_left, msg_registers, msgRegisters]

theorem specMrs_hi (regs : Register → Word) (sb : ObjRef) (um : Word → Word8) (len i : Nat) (hi : 4 ≤ i)
    (hil : i < len) (h120 : i < 120) : i < (specMrs regs (some sb) um len).length ∧
      (specMrs regs (some sb) um len)[i]! = loadWordAt um (bufAddr sb (i + 1)) := by
  have hlt : i < (specMrs regs (some sb) um len).length := by
    unfold specMrs; rw [List.length_take]; simp [msg_registers, msgRegisters]; omega
  refine ⟨hlt, ?_⟩
  rw [getElem!_pos _ i hlt]
  unfold specMrs
  simp only [List.getElem_take, List.getElem_append, msg_registers, msgRegisters, List.length_map,
    List.length_cons, List.length_nil]
  rw [dif_neg (by omega)]
  simp only [List.getElem_map, List.getElem_range']
  congr 2
  omega

theorem specMrs_len_le (regs : Register → Word) (sbo : Option ObjRef) (um : Word → Word8) (len : Nat) :
    (specMrs regs sbo um len).length ≤ len := by
  unfold specMrs; rw [List.length_take]; omega

theorem specMrs_len_none (regs : Register → Word) (um : Word → Word8) (len : Nat) :
    (specMrs regs none um len).length ≤ 4 := by
  unfold specMrs; rw [List.length_take]; simp [msg_registers, msgRegisters]

theorem sanRegs_fields : ∀ (x : Tcb) (rs : List Register) (vs : List Word),
    (sanRegs x rs vs).tcbState = x.tcbState ∧ (sanRegs x rs vs).tcbFault = x.tcbFault
  | x, r :: rs, v :: vs => sanRegs_fields (setReg x r (sanitiseRegister false r v)) rs vs
  | x, [], _ => ⟨rfl, rfl⟩
  | x, _ :: _, [] => ⟨rfl, rfl⟩

theorem hfr_regs_eq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (lst : List Register) (label : Data) (msg : List Data) :
    (do
      let tt ← archGetSanitiseRegisterInfo (Z := Unit) t
      asUser t <| NonDet.zipWithMx (fun r v => setRegister r <| sanitiseRegister tt r v) lst msg
      return decide (label = 0)) σ =
      ({(decide (label = 0), updK σ t (.tcb (sanRegs x lst msg)))}, False) := by
  rw [nd_bind_one (show archGetSanitiseRegisterInfo (Z := Unit) t σ = ({(false, σ)}, False) from rfl),
    nd_bind_one (asUser_zipSan hk lst msg)]
  rfl

end Spec

theorem flags_sanitise (v : BitVec 64) :
    ((((v ||| 2#64) &&& ~~~40#64) ||| 512#64) &&& ~~~256#64) &&& 4095#64 =
      (v ||| Fl4Spec.sanitiseOrFlags) &&& Fl4Spec.sanitiseAndFlags := by
  unfold Fl4Spec.sanitiseOrFlags Fl4Spec.sanitiseAndFlags Fl4Spec.mask
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
  interval_cases i <;> simp

/-- **FL4's `regs::sanitise` is l4v's `sanitise_register`.** -/
theorem sanitise_eq (r : Fl4Spec.Register) (v : U64) : ∃ w : U64, regs.sanitise (regIdx r) v = ok w ∧
    w.bv = Fl4Spec.sanitiseRegister false r v.bv := by
  have e1 : (140737488355327 : BitVec 64).toNat = 140737488355327 := rfl
  have e2 : (18446603336221196288 : BitVec 64).toNat = 18446603336221196288 := rfl
  have g1 : v > 140737488355327#u64 ↔ v.bv > 140737488355327 := by
    rw [GT.gt, GT.gt, BitVec.lt_def, e1, UScalar.bv_toNat]; scalar_tac
  have g2 : v < 18446603336221196288#u64 ↔ v.bv < 18446603336221196288 := by
    rw [BitVec.lt_def, e2, UScalar.bv_toNat]; scalar_tac
  unfold regs.sanitise
  simp only [layout.reg.FS_BASE, layout.reg.GS_BASE, layout.reg.FAULT_IP, layout.reg.NEXT_IP, layout.reg.FLAGS,
    u64_eq_iff]
  unfold Fl4Spec.sanitiseRegister
  cases r
  all_goals simp only [regIdx, show (0#u64 : U64).val = 0 from rfl, show (1#u64 : U64).val = 1 from rfl, show (2#u64 : U64).val = 2 from rfl, show (3#u64 : U64).val = 3 from rfl, show (4#u64 : U64).val = 4 from rfl, show (5#u64 : U64).val = 5 from rfl, show (6#u64 : U64).val = 6 from rfl, show (7#u64 : U64).val = 7 from rfl, show (8#u64 : U64).val = 8 from rfl, show (9#u64 : U64).val = 9 from rfl, show (10#u64 : U64).val = 10 from rfl, show (11#u64 : U64).val = 11 from rfl, show (12#u64 : U64).val = 12 from rfl, show (13#u64 : U64).val = 13 from rfl, show (14#u64 : U64).val = 14 from rfl, show (15#u64 : U64).val = 15 from rfl, show (16#u64 : U64).val = 16 from rfl, show (17#u64 : U64).val = 17 from rfl, show (18#u64 : U64).val = 18 from rfl, show (19#u64 : U64).val = 19 from rfl, show (20#u64 : U64).val = 20 from rfl, show (21#u64 : U64).val = 21 from rfl, show (22#u64 : U64).val = 22 from rfl, show (23#u64 : U64).val = 23 from rfl,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq, or_true, or_false, false_or, true_or, bind_ok]
  case flags =>
    obtain ⟨c1, h1, rfl⟩ := spec_exists Fl4Proofs.P0.Consts.regs.FLAGS_HIGH.spec
    obtain ⟨c2, h2, rfl⟩ := spec_exists Fl4Proofs.P0.Consts.regs.FLAGS_LOW.spec
    obtain ⟨c3, h3, rfl⟩ := spec_exists Fl4Proofs.P0.Consts.regs.FLAGS_IF.spec
    obtain ⟨c4, h4, rfl⟩ := spec_exists Fl4Proofs.P0.Consts.regs.FLAGS_TF.spec
    obtain ⟨c5, h5, rfl⟩ := spec_exists Fl4Proofs.P0.Consts.regs.FLAGS_MASK.spec
    rw [h1, h2, h3, h4, h5]
    simp only [lift, bind_ok]
    refine ⟨_, rfl, ?_⟩
    simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not]
    exact flags_sanitise v.bv
  all_goals first
    | exact ⟨v, rfl, rfl⟩
    | (simp only [← g1, ← g2]
       by_cases h1 : v > 140737488355327#u64 <;> by_cases h2 : v < 18446603336221196288#u64 <;>
         simp only [h1, h2, and_self, and_true, and_false, ↓reduceIte, bind_ok] <;> exact ⟨_, rfl, rfl⟩)


theorem timeout_slice_val :
    (Array.to_slice faults.TIMEOUT_REPLY_MESSAGE).val = Fl4Spec.timeoutMessage.map regIdx := by
  unfold faults.TIMEOUT_REPLY_MESSAGE layout.reg.RAX layout.reg.RBX layout.reg.RCX layout.reg.RDX layout.reg.RSI
    layout.reg.RDI layout.reg.RBP layout.reg.R8 layout.reg.R9 layout.reg.R10 layout.reg.R11 layout.reg.R12
    layout.reg.R13 layout.reg.R14 layout.reg.R15 layout.reg.FAULT_IP layout.reg.RSP layout.reg.FLAGS
    layout.reg.TLS_BASE layout.reg.FS_BASE
  rfl

section Loops
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

variable (T E R B SR) in
/-- The fault-reply copy's invariant: the receiver's registers `rs` set to
the sanitised `vs`. -/
def RgInv (s0 : S) (σ0 : Fl4Spec.State Unit) (rcv : U64) (x0 : Fl4Spec.Tcb) (s : S)
    (rs : List Fl4Spec.Register) (vs : List Fl4Spec.Word) : Prop :=
  EpStateRel T E R B (L.mem s) (updK σ0 rcv.bv (.tcb (sanRegs x0 rs vs))) ∧
    SR s (updK σ0 rcv.bv (.tcb (sanRegs x0 rs vs))) ∧ Agree (L.mem s0) (L.mem s) (fun b => ¬ RcvReg rcv b)

theorem rgInv_init {s0 : S} {σ0 : Fl4Spec.State Unit} (hR : EpStateRel T E R B (L.mem s0) σ0) (hSR : SR s0 σ0)
    {rcv : U64} {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap rcv.bv = some (.tcb x0)) :
    RgInv (L := L) T E R B SR s0 σ0 rcv x0 s0 [] [] := by
  unfold RgInv; rw [show sanRegs x0 [] [] = x0 from rfl, updK_self hk0]; exact ⟨hR, hSR, Agree.rfl'⟩

/-- Writing the next sanitised register of the receiver. -/
theorem set_reg_rg_inv (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    {rcv : U64} (hr : rcv ∈ T) {x0 : Fl4Spec.Tcb} {s : S} {rs : List Fl4Spec.Register} {vs : List Fl4Spec.Word}
    (hI : RgInv (L := L) T E R B SR s0 σ0 rcv x0 s rs vs) (hl : rs.length = vs.length) (r : Fl4Spec.Register)
    (v : Fl4Spec.Word) (w : U64) (hw : w.bv = Fl4Spec.sanitiseRegister false r v) :
    obj.Tcb.set_reg st rcv s (regIdx r) w ⦃ s1 => RgInv (L := L) T E R B SR s0 σ0 rcv x0 s1 (rs ++ [r]) (vs ++ [v]) ⦄ := by
  have hra := hP.tcb rcv hr
  have hks : (updK σ0 rcv.bv (.tcb (sanRegs x0 rs vs))).kheap rcv.bv = some (.tcb (sanRegs x0 rs vs)) := by simp
  refine WP.spec_mono (obj.Tcb.set_reg.spec s rcv _ w) ?_
  rintro s1 rfl
  obtain ⟨hR1, hW1, hS1⟩ := write_reg_rel hP s _ hI.1 hr hks r w
  have e : updK (updK σ0 rcv.bv (.tcb (sanRegs x0 rs vs))) rcv.bv (.tcb (setReg (sanRegs x0 rs vs) r w.bv)) =
      updK σ0 rcv.bv (.tcb (sanRegs x0 (rs ++ [r]) (vs ++ [v]))) := by
    rw [sanRegs_snoc x0 rs vs hl r v, ← hw]; simp only [updK, Function.update_idem]
  rw [e] at hR1 hS1
  have ha := a_reg hra r
  exact ⟨hR1, hH.stable _ _ _ _ hI.2.1 hW1 hS1, fun b hb hn =>
    (agree_wr (L := L) (s := s) (v := w) ha.1 b hb (fun h => hn ⟨_, h⟩)).trans (hI.2.2 b hb hn)⟩

/-- A receiver register word is no other TCB's field nor a buffer word, so
the sender's words survive the copy. -/
theorem snd_reg_keep (hP : EPlaced T E R B) {s0 s : S} {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T)
    (hne : snd ≠ rcv) (hA : Agree (L.mem s0) (L.mem s) (fun b => ¬ RcvReg rcv b)) (r : Fl4Spec.Register) :
    L.mem s (regA snd (regIdx r)) = L.mem s0 (regA snd (regIdx r)) := by
  have ha := a_reg (hP.tcb snd hs) r
  refine hA _ ha.1 ?_
  rintro ⟨r', hr'⟩
  have := tcb_disj hP hr hs (Ne.symm hne).symm; have := ha.2.range
  rw [regA_val (hP.tcb rcv hr) (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega

theorem buf_keep (hP : EPlaced T E R B) {s0 s : S} {rcv : U64} (hr : rcv ∈ T)
    (hA : Agree (L.mem s0) (L.mem s) (fun b => ¬ RcvReg rcv b)) {wp : U64 × Fl4Spec.Word} (hw : wp ∈ B) :
    L.mem s wp.1 = L.mem s0 wp.1 := by
  refine hA _ (hP.balign _ hw).1 ?_
  rintro ⟨r', hr'⟩
  have := hP.bt wp hw rcv hr
  rw [regA_val (hP.tcb rcv hr) (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega

set_option maxHeartbeats 4000000 in
/-- **The first loop of `copy_mrs_fault_reply`**: the sender's message
registers 0..3 into the receiver's registers `Lr`, sanitised. -/
theorem cmfr_loop0 (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {x0 : Fl4Spec.Tcb}
    {regs : Fl4Spec.Register → Fl4Spec.Word} (hreg : ∀ r, (L.mem s0 (regA snd (regIdx r))).bv = regs r)
    {sl : Slice U64} {Lr : List Fl4Spec.Register} (hsl : sl.val = Lr.map regIdx) (hLr : Lr.length < 32)
    (n : Usize) (hn : n.val ≤ Lr.length) {V : List Fl4Spec.Word}
    (hV : ∀ i (h : i < min n.val 4), i < V.length ∧ V[i]! = regs (mrIdx i)) (s1 : S)
    (hI : RgInv (L := L) T E R B SR s0 σ0 rcv x0 s1 [] []) :
    faults.copy_mrs_fault_reply_loop0 st s1 snd rcv sl n 0#usize ⦃ r => r.2.val = min n.val 4 ∧
      RgInv (L := L) T E R B SR s0 σ0 rcv x0 r.1 (Lr.take r.2.val) (V.take r.2.val) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  have hlen : (Slice.len sl).val = Lr.length := by simp [Slice.len, hsl]
  unfold faults.copy_mrs_fault_reply_loop0
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.val)
    (inv := fun x => x.2.val ≤ min n.val 4 ∧
      RgInv (L := L) T E R B SR s0 σ0 rcv x0 x.1 (Lr.take x.2.val) (V.take x.2.val))
  · rintro ⟨s', i⟩ ⟨hi4, hI'⟩
    unfold faults.copy_mrs_fault_reply_loop0.body
    simp only at hi4 hI' ⊢
    by_cases hcn : i < n
    swap
    · rw [if_neg hcn, WP.spec_ok]
      have : i.val = min n.val 4 := by have := us_lt_iff.not.1 hcn; omega
      exact ⟨this, this ▸ hI'⟩
    rw [if_pos hcn]
    have hin : i.val < n.val := us_lt_iff.1 hcn
    have h1 : i < Slice.len sl := us_lt_iff.2 (by omega)
    rw [if_pos h1]
    simp only [lift, bind_ok]
    by_cases h2 : (UScalar.cast .U64 i : U64) < msg.N_MSG_REGISTERS
    swap
    · rw [if_neg h2, WP.spec_ok]
      have : i.val = min n.val 4 := by
        have h2' : ¬ i.val < 4 := fun h => h2 ((gt_iff_val).2 (by rw [hN, cast_us i (by omega)]; omega))
        omega
      exact ⟨this, this ▸ hI'⟩
    rw [if_pos h2]
    have hi4' : i.val < 4 := by have := (gt_iff_val).1 h2; rw [hN, cast_us i (by omega)] at this; omega
    have hiL : i.val < Lr.length := by omega
    have hidx : Slice.index_usize sl i = ok (regIdx Lr[i.val]) := by
      unfold Slice.index_usize
      have : sl[i]? = some (regIdx Lr[i.val]) := by
        simp [Slice.getElem?_Usize_eq, hsl, List.getElem?_map, List.getElem?_eq_getElem hiL]
      rw [this]
    rw [hidx]
    simp only [bind_ok]
    refine WP.spec_bind (msg_register_spec (UScalar.cast .U64 i) (by rw [cast_us i (by omega)]; exact hi4')) ?_
    rintro r5 rfl
    rw [cast_us i (by omega)]
    refine WP.spec_bind (obj.Tcb.reg.spec s' snd _) ?_
    rintro v rfl
    obtain ⟨w, hw, hwv⟩ := sanitise_eq Lr[i.val] (L.mem s' (regA snd (regIdx (mrIdx i.val))))
    rw [hw]
    simp only [bind_ok]
    have hvv : (L.mem s' (regA snd (regIdx (mrIdx i.val)))).bv = V[i.val]! := by
      rw [snd_reg_keep hP hs hr hne hI'.2.2, hreg, (hV i.val (by omega)).2]
    rw [hvv] at hwv
    have hl : (Lr.take i.val).length = (V.take i.val).length := by
      simp [List.length_take]; have := (hV i.val (by omega)).1; omega
    refine WP.spec_bind (set_reg_rg_inv hH hP hr hI' hl Lr[i.val] V[i.val]! w hwv) ?_
    rintro s2 hI2
    obtain ⟨i6, h6e, h6v⟩ := spec_exists (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [h6e, bind_ok, WP.spec_ok]
    have hi6 : i6.val = i.val + 1 := by simpa using h6v
    refine ⟨⟨by show i6.val ≤ min n.val 4; rw [hi6]; exact Nat.le_min.2 ⟨by omega, by omega⟩, ?_⟩,
      by show n.val - i6.val < n.val - i.val; omega⟩
    show RgInv (L := L) T E R B SR s0 σ0 rcv x0 s2 (Lr.take i6.val) (V.take i6.val)
    have hVl := (hV i.val (by omega)).1
    rw [hi6, List.take_succ, List.take_succ, List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hVl]
    simp only [Option.toList_some]
    rw [← getElem!_pos V i.val hVl]
    exact hI2
  · exact ⟨by simp, by simpa using hI⟩

set_option maxHeartbeats 4000000 in
/-- **The second loop of `copy_mrs_fault_reply`**: buffer words `i + 1`
into the receiver's registers `Lr`, sanitised. -/
theorem cmfr_loop1 (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    (hR0 : EpStateRel T E R B (L.mem s0) σ0) {rcv : U64} (hr : rcv ∈ T) {x0 : Fl4Spec.Tcb}
    {sw : U64} {sp : Fl4Spec.Word} (hms : BufMap B sw sp)
    {sl : Slice U64} {Lr : List Fl4Spec.Register} (hsl : sl.val = Lr.map regIdx) (hLr : Lr.length < 32)
    (n : Usize) (hn : n.val ≤ Lr.length) (hn120 : n.val ≤ 120) {V : List Fl4Spec.Word}
    (hV : ∀ i, 4 ≤ i → i < n.val → i < V.length ∧
      V[i]! = loadWordAt σ0.machineState.underlyingMemory (bufAddr sp (i + 1)))
    (s1 : S) (i0 : Usize) (hi0 : 4 ≤ i0.val) (hi0n : i0.val ≤ n.val)
    (hI : RgInv (L := L) T E R B SR s0 σ0 rcv x0 s1 (Lr.take i0.val) (V.take i0.val)) :
    faults.copy_mrs_fault_reply_loop1 st s1 rcv sl n i0 sw ⦃ s2 =>
      RgInv (L := L) T E R B SR s0 σ0 rcv x0 s2 (Lr.take n.val) (V.take n.val) ⦄ := by
  have hlen : (Slice.len sl).val = Lr.length := by simp [Slice.len, hsl]
  unfold faults.copy_mrs_fault_reply_loop1
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.val)
    (inv := fun x => 4 ≤ x.2.val ∧ x.2.val ≤ n.val ∧
      RgInv (L := L) T E R B SR s0 σ0 rcv x0 x.1 (Lr.take x.2.val) (V.take x.2.val))
  · rintro ⟨s', i⟩ ⟨hi4, hin', hI'⟩
    unfold faults.copy_mrs_fault_reply_loop1.body
    simp only at hi4 hin' hI' ⊢
    by_cases hcn : i < n
    swap
    · rw [if_neg hcn, WP.spec_ok]
      have : i.val = n.val := by have := us_lt_iff.not.1 hcn; omega
      exact this ▸ hI'
    rw [if_pos hcn]
    have hin : i.val < n.val := us_lt_iff.1 hcn
    have h1 : i < Slice.len sl := us_lt_iff.2 (by omega)
    rw [if_pos h1]
    have hiL : i.val < Lr.length := by omega
    have hidx : Slice.index_usize sl i = ok (regIdx Lr[i.val]) := by
      unfold Slice.index_usize
      have : sl[i]? = some (regIdx Lr[i.val]) := by
        simp [Slice.getElem?_Usize_eq, hsl, List.getElem?_map, List.getElem?_eq_getElem hiL]
      rw [this]
    rw [hidx]
    simp only [lift, bind_ok]
    set k := core.num.U64.wrapping_add (UScalar.cast .U64 i) 1#u64 with hk
    have hkv : k.val = i.val + 1 := by
      rw [hk]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, cast_us i (by omega)]; omega
    refine WP.spec_bind (msg.buf_get.spec s' sw k) ?_
    rintro v rfl
    have hw := hms k (by omega)
    have hvv : (L.mem s' (fl4BufA sw k)).bv = V[i.val]! := by
      rw [buf_keep hP hr hI'.2.2 hw, hR0.buf _ hw, (hV i.val hi4 hin).2, hkv]
    obtain ⟨w, hw', hwv⟩ := sanitise_eq Lr[i.val] (L.mem s' (fl4BufA sw k))
    rw [hw']
    simp only [bind_ok]
    rw [hvv] at hwv
    have hl : (Lr.take i.val).length = (V.take i.val).length := by
      simp [List.length_take]; have := (hV i.val hi4 hin).1; omega
    refine WP.spec_bind (set_reg_rg_inv hH hP hr hI' hl Lr[i.val] V[i.val]! w hwv) ?_
    rintro s2 hI2
    obtain ⟨i5, h5e, h5v⟩ := spec_exists (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [h5e, bind_ok, WP.spec_ok]
    have hi5 : i5.val = i.val + 1 := by simpa using h5v
    refine ⟨⟨by show 4 ≤ i5.val; omega, by show i5.val ≤ n.val; omega, ?_⟩,
      by show n.val - i5.val < n.val - i.val; omega⟩
    show RgInv (L := L) T E R B SR s0 σ0 rcv x0 s2 (Lr.take i5.val) (V.take i5.val)
    have hVl := (hV i.val hi4 hin).1
    rw [hi5, List.take_succ, List.take_succ, List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hVl]
    simp only [Option.toList_some]
    rw [← getElem!_pos V i.val hVl]
    exact hI2
  · exact ⟨hi0, hi0n, hI⟩

set_option maxHeartbeats 4000000 in
/-- **`copy_mrs_fault_reply`** over a register list `Lr`: the receiver's
registers `Lr` set to the sanitised `get_mrs` words of the sender. -/
theorem cmfr_top (hH : EpHyps st T E R B SR) (hBf : EpBufHyps st T E R B SR) (hBm : EpBufMapHyps st T E R B SR)
    (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {sl : Slice U64} {Lr : List Fl4Spec.Register} (hsl : sl.val = Lr.map regIdx) (hLr : Lr.length < 32)
    (len : U64) (hlen : len.val ≤ 120) :
    faults.copy_mrs_fault_reply st s snd rcv sl len ⦃ s' => RgInv (L := L) T E R B SR s σ rcv xr s' Lr
      (specMrs xs.tcbArch.tcbContext.userRegs (ipcBufOf false xs) σ.machineState.underlyingMemory len.val) ⦄ := by
  set V := specMrs xs.tcbArch.tcbContext.userRegs (ipcBufOf false xs) σ.machineState.underlyingMemory len.val
    with hVdef
  have hxs := hR.at_tcb hs hks
  have hreg : ∀ r, (L.mem s (regA snd (regIdx r))).bv = xs.tcbArch.tcbContext.userRegs r := fun r => hxs.regs r
  have hslen : (Slice.len sl).val = Lr.length := by simp [Slice.len, hsl]
  unfold faults.copy_mrs_fault_reply
  simp only [lift, bind_ok]
  obtain ⟨n, hn, hnv⟩ : ∃ n : Usize, (if len < UScalar.cast .U64 (Slice.len sl) then ok (UScalar.cast .Usize len)
      else ok (Slice.len sl) : Result Usize) = ok n ∧ n.val = min len.val Lr.length := by
    have hc : (UScalar.cast .U64 (Slice.len sl) : U64).val = Lr.length := by
      rw [cast_us _ (by omega), hslen]
    by_cases h : len < UScalar.cast .U64 (Slice.len sl)
    · refine ⟨_, if_pos h, ?_⟩
      have := (gt_iff_val).1 h; rw [hc] at this
      rw [UScalar.cast_val_eq]
      rw [Nat.mod_eq_of_lt (by rw [UScalarTy.Usize_numBits_eq]; rcases System.Platform.numBits_eq with e | e <;>
        rw [e] <;> omega)]
      omega
    · refine ⟨_, if_neg h, ?_⟩
      have : ¬ len.val < Lr.length := fun h' => h ((gt_iff_val).2 (by rw [hc]; exact h'))
      rw [hslen]; omega
  rw [hn]
  simp only [bind_ok]
  refine WP.spec_bind (cmfr_loop0 (L := L) hH hP hs hr hne hreg hsl hLr n (by omega)
    (fun i hi => specMrs_lo xs.tcbArch.tcbContext.userRegs (ipcBufOf false xs) σ.machineState.underlyingMemory
      len.val i (by omega) (by omega)) s (rgInv_init hR hSR hkr)) ?_
  rintro ⟨s1, i2⟩ ⟨hi2, hI1⟩
  show (if i2 < n then _ else _) ⦃ _ ⦄
  have h2a : i2.val ≤ 4 := by rw [hi2]; exact Nat.min_le_right _ _
  have h2b : i2.val ≤ n.val := by rw [hi2]; exact Nat.min_le_left _ _
  have h2c : i2.val = n.val ∨ i2.val = 4 := by rw [hi2]; exact min_choice _ _
  have hna : n.val ≤ len.val := by rw [hnv]; exact Nat.min_le_left _ _
  have hnb : n.val ≤ Lr.length := by rw [hnv]; exact Nat.min_le_right _ _
  have hnc : n.val = len.val ∨ n.val = Lr.length := by rw [hnv]; exact min_choice _ _
  have hVl : V.length ≤ len.val := specMrs_len_le _ _ _ _
  have mle : ∀ k, (Lr.length ≤ k ∨ V.length ≤ k) → min Lr.length V.length ≤ k := fun k h => by
    rcases h with h | h
    · exact (Nat.min_le_left _ _).trans h
    · exact (Nat.min_le_right _ _).trans h
  have fin : ∀ s' k, min Lr.length V.length ≤ k →
      RgInv (L := L) T E R B SR s σ rcv xr s' (Lr.take k) (V.take k) →
      RgInv (L := L) T E R B SR s σ rcv xr s' Lr V := by
    intro s' k hk h
    unfold RgInv at h ⊢; rw [sanRegs_take xr Lr V k hk] at h; exact h
  by_cases hlt : i2 < n
  swap
  · rw [if_neg hlt, WP.spec_ok]
    refine fin s1 i2.val (mle _ ?_) hI1
    have := us_lt_iff.not.1 hlt
    omega
  rw [if_pos hlt]
  have hi2n : i2.val < n.val := us_lt_iff.1 hlt
  have hi24 : i2.val = 4 := by omega
  have hk1 : (updK σ rcv.bv (.tcb (sanRegs xr (Lr.take i2.val) (V.take i2.val)))).kheap snd.bv = some (.tcb xs) := by
    simp [show snd.bv ≠ rcv.bv from fun e => hne (eq_of_bv e), hks]
  refine WP.spec_bind (lookup_send_buf hBf hBm s1 _ hI1.1 hI1.2.1 hs hk1) ?_
  rintro sw hsw
  rcases hsw with ⟨hnone, rfl⟩ | ⟨sp, hsp, hsw0, hms⟩
  · rw [if_neg (by simp), WP.spec_ok]
    refine fin s1 i2.val (mle _ ?_) hI1
    have : V.length ≤ 4 := by rw [hVdef, hnone]; exact specMrs_len_none _ _ _
    omega
  · rw [if_pos (by simp [hsw0])]
    refine WP.spec_mono (cmfr_loop1 (L := L) hH hP hR hr hms hsl hLr n (by omega) (by omega) (V := V)
      (fun i h4 hin => by
        rw [hVdef, hsp]; exact specMrs_hi xs.tcbArch.tcbContext.userRegs sp σ.machineState.underlyingMemory len.val i h4
          (by omega) (by omega)) s1 i2
      (by omega) (by omega) hI1) ?_
    intro s2 hI2
    exact fin s2 n.val (mle _ (by omega)) hI2

set_option maxHeartbeats 8000000 in
/-- **`handle_fault_reply` refines l4v `handle_fault_reply`**, the message
info, buffer and words of the replier `snd` (`get_mrs`) given. -/
theorem handle_fault_reply_rel {A : Type} {ar : machine.Arch A} (hH : EpHyps st T E R B SR)
    (hBf : EpBufHyps st T E R B SR) (hBm : EpBufMapHyps st T E R B SR) (hP : EPlaced T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ)
    {rcv snd : U64} (hr : rcv ∈ T) (hs : snd ∈ T) (hne : snd ≠ rcv) {xr xs : Fl4Spec.Tcb}
    (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hks : σ.kheap snd.bv = some (.tcb xs))
    {f : Fl4Spec.Fault} (hf : xr.tcbFault = some f) :
    faults.handle_fault_reply st ar s a rcv snd ⦃ res => res.2.2 = a ∧ ∃ σ',
      Fl4Spec.handleFaultReply (Z := Unit) f rcv.bv
        (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miLabel
        (specMrs xs.tcbArch.tcbContext.userRegs (ipcBufOf false xs) σ.machineState.underlyingMemory
          (Fl4Spec.unat (Fl4Spec.dataToMessageInfo
            (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miLength)) σ = ({(res.1, σ')}, False) ∧
      EpStateRel T E R B (L.mem res.2.1) σ' ∧ SR res.2.1 σ' ∧
      Agree (L.mem s) (L.mem res.2.1) (fun b => ¬ RcvReg rcv b) ∧
      (∀ p, p ≠ rcv.bv → σ'.kheap p = σ.kheap p) ∧
      ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ∧ x'.tcbFault = xr.tcbFault ⦄ := by
  have hxs := hR.at_tcb hs hks
  have hxr := hR.at_tcb hr hkr
  have hwmi : (L.mem s (regA snd layout.reg.MSG_INFO)).bv = xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  set w := xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register with hwdef
  set V := specMrs xs.tcbArch.tcbContext.userRegs (ipcBufOf false xs) σ.machineState.underlyingMemory
    (Fl4Spec.unat (Fl4Spec.dataToMessageInfo w).miLength) with hVdef
  have hfr := hxr.faultR
  unfold FaultRel at hfr
  rw [hf] at hfr
  have keep : ∀ p, p ≠ rcv.bv → (updK σ rcv.bv (.tcb (sanRegs xr [] []))).kheap p = σ.kheap p := fun p hp => by
    simp [hp]
  unfold faults.handle_fault_reply
  refine WP.spec_bind (msg_info_spec (L := L) s snd) ?_
  rintro tag ⟨hlab, hlen, -, hle⟩
  rw [hwmi] at hlab hlen
  have hlab0 : decide (tag.label = 0#u64) = decide ((Fl4Spec.dataToMessageInfo w).miLabel = 0) := by
    refine decide_eq_decide.2 ⟨fun h => ?_, fun h => ?_⟩
    · show (w >>> 12) &&& Fl4Spec.mask Fl4Spec.msgLabelBits = 0
      rw [label_mask, ← hlab, h]; rfl
    · apply UScalar.eq_of_val_eq
      have : tag.label.bv = 0 := by rw [hlab]; rw [← label_mask w]; exact h
      show tag.label.bv.toNat = _; rw [this]; rfl
  have hlv : tag.length.val = Fl4Spec.unat (Fl4Spec.dataToMessageInfo w).miLength := by
    show tag.length.bv.toNat = _; rw [hlen]
  step with Fl4Proofs.P3.Endp.obj.Tcb.fault_type.spec as ⟨ty, hty⟩
  have regs_case : ∀ (sl : Slice U64) (lst : List Fl4Spec.Register), sl.val = lst.map regIdx → lst.length < 32 →
      (Fl4Spec.handleFaultReply (Z := Unit) f rcv.bv (Fl4Spec.dataToMessageInfo w).miLabel V σ =
        ({(decide ((Fl4Spec.dataToMessageInfo w).miLabel = 0), updK σ rcv.bv (.tcb (sanRegs xr lst V)))}, False)) →
      (do
        let s2 ← faults.copy_mrs_fault_reply st s snd rcv sl tag.length
        ok (decide (tag.label = 0#u64), s2, a)) ⦃ res => res.2.2 = a ∧ ∃ σ',
        Fl4Spec.handleFaultReply (Z := Unit) f rcv.bv (Fl4Spec.dataToMessageInfo w).miLabel V σ =
          ({(res.1, σ')}, False) ∧
        EpStateRel T E R B (L.mem res.2.1) σ' ∧ SR res.2.1 σ' ∧
        Agree (L.mem s) (L.mem res.2.1) (fun b => ¬ RcvReg rcv b) ∧
        (∀ p, p ≠ rcv.bv → σ'.kheap p = σ.kheap p) ∧
        ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ∧ x'.tcbFault = xr.tcbFault ⦄ := by
    intro sl lst hsl hl hspec
    refine WP.spec_bind (cmfr_top (L := L) hH hBf hBm hP s σ hR hSR hs hr hne hks hkr hsl hl tag.length hle) ?_
    intro s2 hI
    rw [hlv] at hI
    refine (WP.spec_ok _).2 ⟨rfl, _, by rw [hspec, hlab0], hI.1, hI.2.1, hI.2.2, fun p hp => by simp [hp],
      sanRegs xr lst V, by simp only [updK_kheap, Function.update_self]; rfl, (sanRegs_fields _ _ _).1,
      (sanRegs_fields _ _ _).2⟩
  cases f with
  | capFault c rp lf =>
    obtain ⟨h1, -⟩ := hfr
    rw [hty, h1, if_pos (by unfold fl4_abi.consts.fault.CapFault; rfl), WP.spec_ok]
    exact ⟨rfl, σ, rfl, hR, hSR, Agree.rfl', fun _ _ => rfl, xr, hkr, rfl, rfl⟩
  | unknownSyscallException n =>
    obtain ⟨h1, -⟩ := hfr
    rw [hty, h1, if_neg (by unfold fl4_abi.consts.fault.CapFault; decide),
      if_pos (by unfold fl4_abi.consts.fault.UnknownSyscall; rfl)]
    simp only [lift, bind_ok]
    exact regs_case _ _ Fl4Proofs.P3.Endp.syscall_slice_val (by decide) (hfr_regs_eq hkr _ _ _)
  | userException e c =>
    obtain ⟨h1, -⟩ := hfr
    rw [hty, h1, if_neg (by unfold fl4_abi.consts.fault.CapFault; decide),
      if_neg (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
      if_pos (by unfold fl4_abi.consts.fault.UserException; rfl)]
    simp only [lift, bind_ok]
    exact regs_case _ _ Fl4Proofs.P3.Endp.exc_slice_val (by decide) (hfr_regs_eq hkr _ _ _)
  | timeout b =>
    obtain ⟨h1, -⟩ := hfr
    rw [hty, h1, if_neg (by unfold fl4_abi.consts.fault.CapFault; decide),
      if_neg (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
      if_neg (by unfold fl4_abi.consts.fault.UserException; decide),
      if_pos (by unfold fl4_abi.consts.fault.Timeout; rfl)]
    simp only [lift, bind_ok]
    exact regs_case _ _ timeout_slice_val (by decide) (hfr_regs_eq hkr _ _ _)
  | archFault af =>
    cases af with
    | vmFault ad d =>
      obtain ⟨h1, -⟩ := hfr
      rw [hty, h1, if_neg (by unfold fl4_abi.consts.fault.CapFault; decide),
        if_neg (by unfold fl4_abi.consts.fault.UnknownSyscall; decide),
        if_neg (by unfold fl4_abi.consts.fault.UserException; decide),
        if_neg (by unfold fl4_abi.consts.fault.Timeout; decide),
        if_neg (by unfold fl4_abi.consts.fault.DebugException; decide), WP.spec_ok]
      exact ⟨rfl, σ, rfl, hR, hSR, Agree.rfl', fun _ _ => rfl, xr, hkr, rfl, rfl⟩

end Loops


section Top
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T C E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 8000000 in
/-- **The fault reply of `do_reply_transfer`** on `IRel` (`ReplyHyps.faultReply`):
`handle_fault_reply` (`handle_fault_reply_rel`), `clear_fault`
(`fault_clear_ipc`, `fault_clear_top`) and the receiver's new state. -/
theorem fault_reply_top (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) :
    ∀ s (a : A) σ (t snd : U64) (x : Fl4Spec.Tcb) (f : Fl4Spec.Fault), IRel st N T C E R B c s σ →
    t ∈ T → snd ∈ T → t ≠ snd → σ.kheap t.bv = some (.tcb x) → x.tcbFault = some f → x.tcbState = .inactive →
    fl4FaultReply st ar s a t snd ⦃ res => ∃ z ∈ (specFaultReply snd.bv t.bv f σ).1,
      IRel st N T C E R B c res.1 z.2 ⦄ := by
  intro s a σ t snd x f hX ht hs hts hkt hf hst
  obtain ⟨hIR, hSRT⟩ := hX
  have hSB := IpcRel.toSRN hIR hSRT
  have hEH := hH.epHyps hP0
  obtain ⟨xs, hks, -⟩ := hIR.tcb snd hs
  -- the spec's reads of the replier
  have hal : ∀ sb, ipcBufOf false xs = some sb → ∀ k, k < 128 → (bufAddr sb k).toNat % 8 = 0 := by
    intro sb hsb k hk
    obtain ⟨w, -, -, hmb⟩ := spec_exists (hBm.lookupMap s σ snd xs false sb hIR.toE hSRT hs hks hsb)
    have hv : (⟨BitVec.ofNat 64 k⟩ : U64).val = k := by
      show (BitVec.ofNat 64 k).toNat = k; simp; omega
    have h := (hP0.e.balign _ (hmb ⟨BitVec.ofNat 64 k⟩ (by rw [hv]; omega))).2
    rw [hv] at h; exact h
  have hpre : ∀ (P : Unit × Fl4Spec.State Unit → Prop) (rst : Bool) (σ1 : Fl4Spec.State Unit),
      Fl4Spec.handleFaultReply (Z := Unit) f t.bv
        (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miLabel
        (specMrs xs.tcbArch.tcbContext.userRegs (ipcBufOf false xs) σ.machineState.underlyingMemory
          (Fl4Spec.unat (Fl4Spec.dataToMessageInfo
            (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miLength)) σ = ({(rst, σ1)}, False) →
      ∀ z, z ∈ ((Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) t.bv >>= fun _ =>
        Fl4Spec.setThreadState (Z := Unit) t.bv (if rst then .restart else .inactive)) σ1).1 →
      z ∈ (specFaultReply snd.bv t.bv f σ).1 := by
    intro P rst σ1 h1 z hz
    unfold specFaultReply
    rw [nd_bind_one (getMessageInfo_eq hks), nd_bind_one (lookupIpcBuffer_eq hks false),
      nd_bind_one (getMrs_eq hks _ hal _), nd_bind_one h1]
    exact hz
  unfold fl4FaultReply
  refine WP.spec_bind (handle_fault_reply_rel (L := L) (ar := ar) hEH hBf.srs hBm.srs hP0.e s a σ hIR.toE hSB.1 ht
    hs (Ne.symm hts) hkt hks hf) ?_
  rintro ⟨rst, s4, a3⟩ ⟨-, σ4, hhf, hE4, hS4, hA4, hk4, x4, hkx4, hx4s, hx4f⟩
  have hN4 := ntfn_lift_rcv hP0.toC hIR.toN hE4 ht (hA4.mono fun _ h => h.1) hk4 hkt hkx4 hx4s
  have hIR4 : IpcRel N T E R B (L.mem s4) σ4 := IpcRel.of hN4 hE4 hS4.2.all
  have hSRT4 := hS4.1
  unfold faults.clear_fault
  step with Fl4Proofs.P1.obj.Tcb.set_fault_type.spec as ⟨s5, hs5⟩
  have e5 : s5 = L.wr s4 (tFaultA t) 0#u64 := by rw [hs5]; unfold fl4_abi.consts.fault.NullFault; rfl
  subst e5
  have hIR5 := fault_clear_ipc hP0 hIR4 ht hkx4
  have hSRT5 := fault_clear_top hSRT4 ht hkx4
  set x5 : Fl4Spec.Tcb := { x4 with tcbFault := none } with hx5
  have hkx5 : (updK σ4 t.bv (.tcb x5)).kheap t.bv = some (.tcb x5) := by simp
  obtain ⟨x5', hk5', hTR5⟩ := hIR5.tcb t ht
  rw [hkx5] at hk5'; cases hk5'
  have hst5 : x5.tcbState = .inactive := by rw [hx5]; exact hx4s.trans hst
  have hq := IpcRel.not_ep_queued hIR5 (t := t) (by rw [hTR5.st, hst5]; decide)
  have hsteps := IpcSchedHyps.stepsG (A := A) hH hBf hBm hP0
  have fin : ∀ (ts : Fl4Spec.ThreadState) (code : U64), tsCode ts < 3 → code.val = tsCode ts →
      ts = (if rst then .restart else .inactive) →
      (do let s6 ← sched.set_thread_state st (L.wr s4 (tFaultA t) 0#u64) t code; ok (s6, a3)) ⦃ res =>
        ∃ z ∈ (specFaultReply snd.bv t.bv f σ).1, IRel st N T C E R B c res.1 z.2 ⦄ := by
    intro ts code hts hcode hts'
    refine WP.spec_bind (hsteps.sts hP0.e _ _ hIR5.toE (IpcRel.toSRN hIR5 hSRT5) ht hkx5 hq
      (show tsCode x5.tcbState ≠ 6 by rw [hst5]; decide) ts hts code hcode) ?_
    rintro s6 ⟨hE6, hS6⟩
    apply (WP.spec_ok _).2
    refine ⟨((), _), hpre (fun _ => True) rst σ4 hhf _ ?_, IpcRel.ofSRN hE6 hS6⟩
    rw [nd_bind_one (Notif.threadSet_eq _ hkx4), ← hts', Notif.setThreadState_eq _ hkx5]
    rfl
  cases rst
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact fin .inactive sched.TS_INACTIVE (by decide) (by unfold sched.TS_INACTIVE; rfl) rfl
  · simp only [↓reduceIte]
    exact fin .restart sched.TS_RESTART (by decide) (by unfold sched.TS_RESTART; rfl) rfl

set_option maxHeartbeats 4000000 in
/-- **The grant transfer of `do_reply_transfer`** (`ReplyHyps.grantXfer`):
`do_ipc_transfer_grant` with no endpoint (FL4's endpoint 0, which no
valid cap names). -/
theorem grant_xfer_top (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B) :
    ∀ s (a : A) σ (snd rcv : U64) (xs xr : Fl4Spec.Tcb) (rp : Fl4Spec.ObjRef),
    IRel st N T C E R B c s σ → snd ∈ T → rcv ∈ T → snd ≠ rcv → σ.kheap snd.bv = some (.tcb xs) →
    σ.kheap rcv.bv = some (.tcb xr) → xs.tcbFault = none → ipcBufOf true xr = some rp →
    ipc.do_ipc_transfer st ar s a snd 0#u64 0#u64 true rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv none 0 true rcv.bv σ = ({((), σ')}, False) ∧
      IRel st N T C E R B c s' σ' ∧ ∃ x', σ'.kheap rcv.bv = some (.tcb x') ∧ x'.tcbState = xr.tcbState ⦄ := by
  intro s a σ snd rcv xs xr rp hX hs hr hne hks hkr hf hrb
  obtain ⟨hIR, hSRT⟩ := hX
  refine WP.spec_mono (do_ipc_transfer_grant hH hBf hBm hP0 hP0.e s a σ hIR.toE (IpcRel.toSRN hIR hSRT) hs hr hne
    hks hkr hf hrb 0#u64 0#u64 true none (Or.inr ⟨rfl, rfl⟩)) ?_
  rintro s' ⟨σ', hsp, hE, hS, -, -, x', hx', hxs⟩
  exact ⟨σ', hsp, IpcRel.ofSRN hE hS, x', hx', hxs⟩

/-- **`ReplyHyps` from its three remaining steps**: `faultReply` is
`fault_reply_top` and `grantXfer` is `grant_xfer_top`. -/
theorem ReplyHyps.of (hH : IpcSchedHyps st ar N T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBf : EpBufHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hBm : EpBufMapHyps st T E R B (SRT st N T C E R B c (SRE st N T C E R B c)))
    (hP0 : IPlaced N T E R B)
    (hrem : ∀ s (a : A) σ (r t : U64) (x : Fl4Spec.Tcb), IRel st N T C E R B c s σ → r ∈ R → t ∈ T →
      σ.kheap t.bv = some (.tcb x) → x.tcbState = .blockedOnReply r.bv →
      ipc.reply_remove st ar s a r t ⦃ res => res.2 = a ∧ ∃ σ' x',
        Fl4Spec.replyRemove (Z := Unit) t.bv r.bv σ = ({((), σ')}, False) ∧ IRel st N T C E R B c res.1 σ' ∧
        σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive ∧ x'.tcbFault = x.tcbFault ∧
        ∀ p y, p ≠ t.bv → σ.kheap p = some (.tcb y) → ∃ y', σ'.kheap p = some (.tcb y') ∧
          y'.tcbFault = y.tcbFault ∧ y'.tcbState = y.tcbState ⦄)
    (hunb : ∀ s σ (t : U64) (x : Fl4Spec.Tcb) (k : S → Result (S × A)) (P : S × A → Prop),
      IRel st N T C E R B c s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
      (∀ s' σ', (Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext t.bv >>=
          Fl4Spec.ifSporadicCurScTestRefillUnblockCheck) σ = ({((), σ')}, False) → IRel st N T C E R B c s' σ' →
        (∀ p y, σ.kheap p = some (.tcb y) → σ'.kheap p = some (.tcb y)) → k s' ⦃ P ⦄) →
      (do
        let i2 ← obj.Tcb.sc st t s
        let b1 ← sporadic.sc_sporadic st s i2
        let s2 ←
          if b1
          then
            do
            let i3 ← obj.Sc.cpu st i2 s
            let i4 ← obj.node_get st s i3 layout.node.CUR_SC
            if i2 != i4
            then sporadic.unblock_check st s i2
            else ok s
          else ok s
        k s2) ⦃ P ⦄)
    (htmo : ∀ s (a : A) σ (t sc ft : U64) (fault : Option Fl4Spec.Fault) (y : Fl4Spec.SchedContext) (n : Nat),
      IRel st N T C E R B c s σ → t ∈ T → sc ∈ C → σ.kheap sc.bv = some (.schedContext y n) →
      ∀ x : Fl4Spec.Tcb, σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true →
      x.tcbSchedContext = some sc.bv → (ft = 0#u64 ↔ fault = none) → (ft = 5#u64 ↔ ∃ b, fault = some (.timeout b)) →
      fl4ReplyTmo st ar t ft sc s a ⦃ res => ∃ z ∈ (specReplyTmo t.bv fault y sc.bv σ).1,
        IRel st N T C E R B c res.1 z.2 ⦄) :
    ReplyHyps st ar N T C E R B c :=
  ⟨hrem, hunb, fault_reply_top hH hBf hBm hP0, grant_xfer_top hH hBf hBm hP0, htmo⟩

end Top

end

end Fl4Proofs.P3.Endp

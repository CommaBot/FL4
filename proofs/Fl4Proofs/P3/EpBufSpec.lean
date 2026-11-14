/-
P3 (DESIGN.md §9), endpoints: the spec's IPC-buffer words, computed.

`loadWordOffs_eq`, `storeWordOffs_eq`: on an aligned word (and, for the
store, a word of a user data frame, `inUserFrame`) the spec's buffer
accessors have one outcome; `copyMrs_bufs`: l4v `copy_mrs` with both IPC
buffers copies the registers and then the buffer words `5 .. n`
(`copyBufMem`).
-/
import Fl4Proofs.P3.EpBytes
import Fl4Proofs.P3.EpXferSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

variable {Z : Type}

theorem assert_true' {σ' : Type} {P : Prop} (h : P) (s : σ') : NonDet.assert P s = ({((), s)}, False) := by
  simp [NonDet.assert, h]

/-- The state with user memory `um`. -/
def setUm (σ : State Z) (um : Word → Word8) : State Z :=
  { σ with machineState := { σ.machineState with underlyingMemory := um } }

theorem aligned_mask {a : Word} (h : a.toNat % 8 = 0) : a &&& mask 3 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (mask 3 : Word).toNat = 2 ^ 3 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]
  simpa using h

theorem selectF_one {σ' α : Type} (a : α) (s : σ') :
    NonDet.selectF (σ := σ') (({a} : Set α), False) s = ({(a, s)}, False) := by
  unfold NonDet.selectF
  ext ⟨x, y⟩ <;> simp [and_comm]

theorem loadWord_eq (ms : MachineState) (a : Word) (h : a.toNat % 8 = 0) :
    loadWord a ms = ({(loadWordAt ms.underlyingMemory a, ms)}, False) := by
  unfold loadWord
  rw [nd_gets_bind, nd_bind_one (assert_true' (aligned_mask h) ms), nd_pure_apply']
  rfl

theorem loadWordOffs_eq (σ : State Z) (p : ObjRef) (x : Nat) (h : (p + BitVec.ofNat 64 (x * wordSize)).toNat % 8 = 0) :
    loadWordOffs (Z := Z) p x σ =
      ({(loadWordAt σ.machineState.underlyingMemory (p + BitVec.ofNat 64 (x * wordSize)), σ)}, False) := by
  unfold loadWordOffs doMachineOp
  rw [nd_gets_bind, loadWord_eq _ _ h, nd_bind_one (selectF_one _ σ)]
  dsimp only
  rw [nd_bind_one (show NonDet.modify (fun state : State Z => { state with machineState := σ.machineState }) σ =
    ({((), σ)}, False) from rfl)]
  rfl

theorem modify_eq {σ' : Type} (f : σ' → σ') (s : σ') : NonDet.modify f s = ({((), f s)}, False) := rfl

theorem storeWord_eq (ms : MachineState) (a w : Word) (h : a.toNat % 8 = 0) :
    storeWord a w ms = ({((), { ms with underlyingMemory := storeMem ms.underlyingMemory a w })}, False) := by
  unfold storeWord
  rw [nd_bind_one (assert_true' (aligned_mask h) ms)]
  rfl

theorem storeWordOffs_eq (σ : State Z) (p : ObjRef) (x : Nat) (v : Word)
    (h : (p + BitVec.ofNat 64 (x * wordSize)).toNat % 8 = 0) (hu : inUserFrame (p + BitVec.ofNat 64 (x * wordSize)) σ) :
    storeWordOffs (Z := Z) p x v σ =
      ({((), setUm σ (storeMem σ.machineState.underlyingMemory (p + BitVec.ofNat 64 (x * wordSize)) v))}, False) := by
  unfold storeWordOffs doMachineOp
  rw [nd_bind_one (show (NonDet.get : NonDet (State Z) (State Z)) σ = ({(σ, σ)}, False) from rfl),
    nd_bind_one (assert_true' hu σ), nd_gets_bind, storeWord_eq _ _ _ h, nd_bind_one (selectF_one _ σ)]
  dsimp only
  rw [nd_bind_one (modify_eq _ _)]
  rfl

/-- Word `x` of the buffer at `p`. -/
def bufAddr (p : Word) (x : Nat) : Word := p + BitVec.ofNat 64 (x * wordSize)

/-- User memory after copying the buffer words `xs` from `sb` to `rb`. -/
def copyBufMem (um : Word → Word8) (sb rb : Word) : List Nat → (Word → Word8)
  | [] => um
  | x :: xs => copyBufMem (storeMem um (bufAddr rb x) (loadWordAt um (bufAddr sb x))) sb rb xs

/-- The buffer words `copy_mrs` copies. -/
def bufIdx (n : LengthType) : List Nat :=
  List.range' (msg_registers.length + 1) (unat n + 1 - (msg_registers.length + 1))

theorem inUserFrame_setUm (σ : State Z) (um : Word → Word8) (a : Word) :
    inUserFrame a (setUm σ um) ↔ inUserFrame a σ := Iff.rfl

theorem setUm_setUm (σ : State Z) (a b : Word → Word8) : setUm (setUm σ a) b = setUm σ b := rfl

theorem setUm_um (σ : State Z) (a : Word → Word8) : (setUm σ a).machineState.underlyingMemory = a := rfl

theorem mapM_copy (sb rb : Word) : ∀ (xs : List Nat) (σ : State Z),
    (∀ x ∈ xs, (bufAddr sb x).toNat % 8 = 0 ∧ (bufAddr rb x).toNat % 8 = 0 ∧ inUserFrame (bufAddr rb x) σ) →
    NonDet.mapM (fun x => do
        let v ← loadWordOffs (Z := Z) sb x
        storeWordOffs rb x v) xs σ =
      ({(xs.map fun _ => (), setUm σ (copyBufMem σ.machineState.underlyingMemory sb rb xs))}, False)
  | [], σ, _ => by
    show (pure [] : NonDet (State Z) (List Unit)) σ = _
    rw [nd_pure_apply']; rfl
  | x :: xs, σ, h => by
    obtain ⟨h1, h2, h3⟩ := h x (by simp)
    unfold NonDet.mapM
    rw [nd_bind_one' (show (do
        let v ← loadWordOffs (Z := Z) sb x
        storeWordOffs rb x v) σ = ({((), setUm σ (storeMem σ.machineState.underlyingMemory (bufAddr rb x)
          (loadWordAt σ.machineState.underlyingMemory (bufAddr sb x))))}, False) by
      rw [nd_bind_one (loadWordOffs_eq σ sb x h1)]
      exact storeWordOffs_eq σ rb x _ h2 h3)]
    rw [nd_bind_one' (mapM_copy sb rb xs _ fun y hy => by
      obtain ⟨g1, g2, g3⟩ := h y (by simp [hy])
      exact ⟨g1, g2, (inUserFrame_setUm _ _ _).2 g3⟩)]
    rfl

/-- A user frame stays one when a kernel object is replaced by one of the
same kind (here: anything that is not a data page). -/
theorem inUserFrame_updK {σ : State Z} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (ho : ∀ sz, o ≠ .archObj (.dataPage false sz)) (a : Word) (h : inUserFrame a σ) : inUserFrame a (updK σ p o') := by
  obtain ⟨sz, hsz⟩ := h
  refine ⟨sz, ?_⟩
  have hne : (a &&& ~~~(mask (pageBitsForSize sz))) ≠ p := by
    intro e; rw [e, hk] at hsz; cases hsz; exact ho sz rfl
  simp [updK, hne, hsz]

/-- **`copy_mrs` with both IPC buffers.** -/
theorem copyMrs_bufs {σ : State Z} {snd rcv : ObjRef} {xs xr : Tcb} (hne : snd ≠ rcv)
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) (sb rb : ObjRef) (n : LengthType)
    (h : ∀ x ∈ bufIdx n, (bufAddr sb x).toNat % 8 = 0 ∧ (bufAddr rb x).toNat % 8 = 0 ∧ inUserFrame (bufAddr rb x) σ) :
    copyMrs (Z := Z) snd (some sb) rcv (some rb) n σ =
      ({(min n (natToLen ((msg_registers.take (unat n)).length + ((bufIdx n).map fun _ => ()).length)),
        setUm (updK σ rcv (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (msg_registers.take (unat n)))))
          (copyBufMem σ.machineState.underlyingMemory sb rb (bufIdx n)))}, False) := by
  unfold copyMrs
  rw [nd_pure_bind', nd_bind_one (copy_regs_eq hne hks hkr _)]
  dsimp only
  rw [show List.range' (msg_registers.length + 1) (unat n + 1 - (msg_registers.length + 1)) = bufIdx n from rfl]
  rw [nd_bind_one (mapM_copy sb rb (bufIdx n) (updK σ rcv (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
      (msg_registers.take (unat n))))) (fun x hx => by
    obtain ⟨g1, g2, g3⟩ := h x hx
    exact ⟨g1, g2, inUserFrame_updK hkr (fun _ h => by cases h) _ g3⟩))]
  rfl

theorem copyMrs_noSendBuf {σ : State Z} {snd rcv : ObjRef} {xs xr : Tcb} (hne : snd ≠ rcv)
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) (rbuf : Option ObjRef)
    (n : LengthType) :
    copyMrs (Z := Z) snd none rcv rbuf n σ =
      ({(min n (natToLen ((msg_registers.take (unat n)).length + ([] : List Word).length)),
        updK σ rcv (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (msg_registers.take (unat n)))))}, False) := by
  unfold copyMrs
  rw [nd_pure_bind', nd_bind_one (copy_regs_eq hne hks hkr _)]
  cases rbuf <;> (dsimp only; rw [nd_pure_bind']; rfl)

end

section
variable {σ : State Unit}

theorem transferCaps_recvBuf (mi : MessageInfo) (ep : Option ObjRef) (rcv rb : ObjRef) {sl : List CslotPtr}
    (hs : getReceiveSlots (Z := Unit) rcv (some rb) σ = ({(sl, σ)}, False)) :
    transferCaps (Z := Unit) mi [] ep rcv (some rb) σ = ({(⟨mi.miLength, 0, 0, mi.miLabel⟩, σ)}, False) := by
  unfold transferCaps
  rw [nd_bind_one hs, nd_pure_bind']
  rfl

/-- **`do_ipc_transfer` with a receive buffer** (sender without fault, no
extra caps), given the outcome of `copy_mrs` and of the receive-slot
lookup (whose result is not used without caps). -/
theorem doIpcTransfer_recvBuf {snd rcv : ObjRef} {xs xr : Tcb}
    (hks : σ.kheap snd = some (.tcb xs)) (hkr : σ.kheap rcv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rb : ObjRef} (hrb : ipcBufOf true xr = some rb) (ep : Option ObjRef) (badge : Badge) (grant : Bool)
    (hcaps : grant = false ∨ ipcBufOf false xs = none ∨
      unat (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miExtraCaps = 0)
    {mrs : LengthType} {σc : State Unit} {xc : Tcb}
    (hcopy : copyMrs (Z := Unit) snd (ipcBufOf false xs) rcv (some rb)
      (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLength σ = ({(mrs, σc)}, False))
    (hkc : σc.kheap rcv = some (.tcb xc)) {sl : List CslotPtr}
    (hsl : getReceiveSlots (Z := Unit) rcv (some rb) σc = ({(sl, σc)}, False)) :
    doIpcTransfer (Z := Unit) snd ep badge grant rcv σ =
      ({((), updK σc rcv (.tcb (setReg (setReg xc msg_info_register (messageInfoToData
        ⟨mrs, 0, 0, (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLabel⟩))
        badge_register badge)))}, False) := by
  unfold doIpcTransfer
  rw [nd_bind_one (lookupIpcBuffer_eq hkr true), hrb, nd_bind_one (threadGet_eq _ hks), hf]
  dsimp only
  rw [nd_bind_one (lookupIpcBuffer_eq hks false)]
  unfold doNormalTransfer
  rw [nd_bind_one (getMessageInfo_eq hks)]
  have hlk : grant = true → NonDetE.catch (lookupExtraCaps (Z := Unit) snd (ipcBufOf false xs)
      (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register))) (fun _ => pure []) σ =
      ({([], σ)}, False) := by
    intro hg
    refine catch_lookupExtraCaps_nil ?_
    rcases hcaps with h | h | h
    · rw [hg] at h; cases h
    · exact Or.inl h
    · exact Or.inr h
  cases grant <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    first | rw [nd_bind_one (hlk rfl)] | rw [nd_pure_bind']
  all_goals
    rw [nd_bind_one hcopy, nd_bind_one (transferCaps_recvBuf _ _ _ _ hsl)]
    unfold setMessageInfo
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkc)]
    rw [asUser_setRegister_eq (x := setReg xc msg_info_register (messageInfoToData
        ⟨mrs, 0, 0, (dataToMessageInfo (xs.tcbArch.tcbContext.userRegs msg_info_register)).miLabel⟩)) _ _
        (by simp only [updK_kheap, Function.update_self])]
    simp only [updK, Function.update_idem]

end

end Fl4Proofs.P3.Endp

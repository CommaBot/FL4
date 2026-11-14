/-
P3 (DESIGN.md §9), endpoints: writing a message into a receiver's message
registers and IPC buffer (l4v `set_mrs`, FL4 `set_mr` one word at a time).

`mrRegs ctx ms` is the receiver's register file after the message `ms`
(l4v `set_mrs`'s `new_regs`), `mrPairs ms` the buffer words it stores
(`zipWithM_x store_word_offs [5 ..] (drop 4 ms)`). `setMrs_eq`: on a
receiver with IPC buffer `p` (aligned, in user frames) `set_mrs` has one
outcome, `mrState`. `mrRegs_snoc` / `mrPairs_snoc`: appending one word
changes one register (first four words) or stores one buffer word.
-/
import Fl4Proofs.P3.TcbRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

/-- The receiver's registers after the message `ms` (l4v `set_mrs`). -/
def mrRegs (ctx : Register → Word) (ms : List Word) : Register → Word := fun reg =>
  if reg ∈ msg_registers.take ms.length then the ms[theIndex msg_registers reg]? else ctx reg

/-- The buffer words `set_mrs` stores. -/
def mrPairs (ms : List Word) : List (Nat × Word) := (List.range' 5 116).zip (ms.drop 4)

/-- User memory after storing `ps` into the buffer at `p`. -/
def mrMem (um : Word → Word8) (p : Word) : List (Nat × Word) → (Word → Word8)
  | [] => um
  | (x, v) :: ps => mrMem (storeMem um (bufAddr p x) v) p ps

/-- The receiver TCB with the registers `regs`. -/
def withRegs (x : Tcb) (regs : Register → Word) : Tcb :=
  { x with tcbArch := archTcbSetRegisters regs x.tcbArch }

/-- The state after `set_mrs rcv (Some p) ms`. -/
def mrState (σ : State Unit) (rcv : ObjRef) (x : Tcb) (p : ObjRef) (ms : List Word) : State Unit :=
  setUm (updK σ rcv (.tcb (withRegs x (mrRegs x.tcbArch.tcbContext.userRegs ms))))
    (mrMem σ.machineState.underlyingMemory p (mrPairs ms))

theorem theIndex_mr : ∀ j, j < 4 → theIndex msg_registers (mrIdx j) = j := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem mr_cases (reg : Register) : (∃ j, j < 4 ∧ reg = mrIdx j) ∨ reg ∉ msg_registers := by
  cases reg
  all_goals first
    | (right; decide)
    | (left; exact ⟨0, by omega, rfl⟩)
    | (left; exact ⟨1, by omega, rfl⟩)
    | (left; exact ⟨2, by omega, rfl⟩)
    | (left; exact ⟨3, by omega, rfl⟩)

theorem mrIdx_mem_take {j k : Nat} (hj : j < 4) : mrIdx j ∈ msg_registers.take k ↔ j < k := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with rfl | rfl | rfl | rfl | hk <;>
  first | decide | (rw [List.take_of_length_le (by simp [msg_registers, msgRegisters]; omega)]; simp [mrIdx,
    msg_registers, msgRegisters]; omega)

theorem mrRegs_mr (ctx : Register → Word) (ms : List Word) {j : Nat} (hj : j < 4) :
    mrRegs ctx ms (mrIdx j) = if j < ms.length then ms.getD j 0 else ctx (mrIdx j) := by
  unfold mrRegs
  rw [theIndex_mr j hj]
  by_cases h : j < ms.length
  · rw [if_pos ((mrIdx_mem_take hj).2 h), if_pos h, List.getElem?_eq_getElem h]
    simp [the, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · rw [if_neg (fun h' => h ((mrIdx_mem_take hj).1 h')), if_neg h]

theorem mrRegs_other (ctx : Register → Word) (ms : List Word) {reg : Register} (h : reg ∉ msg_registers) :
    mrRegs ctx ms reg = ctx reg := by
  unfold mrRegs
  rw [if_neg (fun h' => h (List.mem_of_mem_take h'))]

/-- Appending a word to a message of fewer than four words: one more
register. -/
theorem mrRegs_snoc_lt (ctx : Register → Word) (ms : List Word) (v : Word) (h : ms.length < 4) :
    mrRegs ctx (ms ++ [v]) = Function.update (mrRegs ctx ms) (mrIdx ms.length) v := by
  funext reg
  rcases mr_cases reg with ⟨j, hj, rfl⟩ | hr
  · rw [mrRegs_mr _ _ hj]
    by_cases e : j = ms.length
    · subst e; simp
    · rw [Function.update_of_ne (fun h' => e (by
          have := congrArg (theIndex msg_registers) h'; rwa [theIndex_mr _ hj, theIndex_mr _ h] at this)),
        mrRegs_mr _ _ hj]
      simp only [List.length_append, List.length_singleton]
      by_cases hl : j < ms.length
      · rw [if_pos (by omega), if_pos hl, List.getD_append _ _ _ _ hl]
      · rw [if_neg (by omega), if_neg hl]
  · rw [mrRegs_other _ _ hr, Function.update_of_ne (fun h' => hr (by rw [h']; exact mrIdx_mem _)), mrRegs_other _ _ hr]

/-- Appending a word to a message of at least four words: the registers
stay. -/
theorem mrRegs_snoc_ge (ctx : Register → Word) (ms : List Word) (v : Word) (h : 4 ≤ ms.length) :
    mrRegs ctx (ms ++ [v]) = mrRegs ctx ms := by
  funext reg
  rcases mr_cases reg with ⟨j, hj, rfl⟩ | hr
  · rw [mrRegs_mr _ _ hj, mrRegs_mr _ _ hj, List.getD_append _ _ _ _ (by omega)]
    simp only [List.length_append, List.length_singleton]
    rw [if_pos (by omega), if_pos (by omega)]
  · rw [mrRegs_other _ _ hr, mrRegs_other _ _ hr]

theorem mrPairs_snoc_lt (ms : List Word) (v : Word) (h : ms.length < 4) : mrPairs (ms ++ [v]) = mrPairs ms := by
  unfold mrPairs
  rw [List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by omega)]

theorem zip_range'_snoc {α : Type} (v : α) : ∀ (l : List α) (a n : Nat), l.length < n →
    (List.range' a n).zip (l ++ [v]) = (List.range' a n).zip l ++ [(a + l.length, v)]
  | [], a, n, h => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [List.range'_succ]
  | x :: l, a, n, h => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [List.range'_succ, List.cons_append, List.zip_cons_cons, List.length_cons]
    rw [zip_range'_snoc v l (a + 1) k (by simp at h; omega)]
    simp; omega

theorem mrPairs_snoc_ge (ms : List Word) (v : Word) (h : 4 ≤ ms.length) (h' : ms.length < 120) :
    mrPairs (ms ++ [v]) = mrPairs ms ++ [(ms.length + 1, v)] := by
  unfold mrPairs
  rw [List.drop_append_of_le_length h, zip_range'_snoc v _ 5 116 (by simp; omega)]
  simp; omega

theorem mrMem_snoc (um : Word → Word8) (p : Word) :
    ∀ (ps : List (Nat × Word)) (x : Nat) (v : Word), mrMem um p (ps ++ [(x, v)]) = storeMem (mrMem um p ps) (bufAddr p x) v
  | [], x, v => rfl
  | (y, w) :: ps, x, v => mrMem_snoc _ p ps x v

theorem zipWithMx_store (p : ObjRef) : ∀ (xs : List Nat) (ys : List Word) (σ : State Unit),
    (∀ q ∈ xs.zip ys, (bufAddr p q.1).toNat % 8 = 0 ∧ inUserFrame (bufAddr p q.1) σ) →
    NonDet.zipWithMx (fun x v => storeWordOffs (Z := Unit) p x v) xs ys σ =
      ({((), setUm σ (mrMem σ.machineState.underlyingMemory p (xs.zip ys)))}, False)
  | [], _, σ, _ => by
    show (pure () : NonDet (State Unit) Unit) σ = _
    rw [nd_pure_apply']; rfl
  | _ :: _, [], σ, _ => by
    show (pure () : NonDet (State Unit) Unit) σ = _
    rw [nd_pure_apply']; rfl
  | x :: xs, y :: ys, σ, h => by
    obtain ⟨h1, h2⟩ := h (x, y) (by simp)
    unfold NonDet.zipWithMx
    rw [nd_bind_one' (storeWordOffs_eq σ p x y h1 h2)]
    rw [zipWithMx_store p xs ys _ fun q hq => by
      obtain ⟨g1, g2⟩ := h q (by simp [hq]); exact ⟨g1, (inUserFrame_setUm _ _ _).2 g2⟩]
    rfl

/-- **`set_mrs` with an IPC buffer.** -/
theorem setMrs_eq {σ : State Unit} {rcv : ObjRef} {x : Tcb} (hk : σ.kheap rcv = some (.tcb x)) (p : ObjRef)
    (ms : List Word) (hal : ∀ q ∈ mrPairs ms, (bufAddr p q.1).toNat % 8 = 0 ∧ inUserFrame (bufAddr p q.1) σ) :
    setMrs (Z := Unit) rcv (some p) ms σ = ({(natToLen (min ms.length msgMaxLength), mrState σ rcv x p ms)}, False) := by
  unfold setMrs
  rw [nd_bind_one (getTcb_eq hk), nd_pure_bind', nd_pure_bind',
    ]
  erw [nd_bind_one (setObject_eq (o' := .tcb (withRegs x (mrRegs x.tcbArch.tcbContext.userRegs ms))) hk rfl)]
  rw [nd_pure_bind']
  dsimp only
  rw [nd_bind_one (zipWithMx_store p _ _ _ (fun q hq => by
    obtain ⟨g1, g2⟩ := hal q hq
    exact ⟨g1, inUserFrame_updK hk (fun _ h => by cases h) _ g2⟩))]
  rfl

end

end Fl4Proofs.P3.Endp

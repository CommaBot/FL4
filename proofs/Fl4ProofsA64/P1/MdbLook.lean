/-
P1 (aarch64, gen 51): **the lookups land in `OS`; CNode Copy / Mint / Move / Mutate through `cnode.decode` and
`decode_invocation` with the MDB facts, without `∈ OS` hypotheses on lookup results**.

* **`lookup_src_in`** / **`lookup_piv_in`**: `lookup_source_slot` / `lookup_pivot_slot` (cspace.rs:113–123, all three
  are `lookup_slot_for_cnode_op`) from a `RootOK` root return a slot of `OS` — gen 30's target lemma generalised in
  place (`lookup_op_in`, QueueSlotTyDec; `lookup_tgt_in` its instance).
* **`lookup_slotO`**: `cspace.lookup_slot` of a thread whose CSpace-root slot (`SLOT_CTABLE` = 0, the thread
  address itself) is in `OS` returns a slot of `OS` (`resolve_in` from `RootOK.of_slot`).
* **`ipc.lookup_extra_caps.inOS`**: every non-null extra-cap slot `lookup_extra_caps` (ipc.rs:28–44) returns for
  such a thread is in `OS` (the loop over `lookup_slot`). With [J] `SlotTyEntT`'s `cover` (every TCB of `T` in
  `OS`) this holds for the current thread at every `EntAt` state: the extra slots handed to a decode are `OS`
  slots by the kernel's own lookup.
* **`cnode.decode.copy_mdbS`**: `cnode.decode` at `CNodeCopy` / `CNodeMint` / `CNodeMove` / `CNodeMutate` of a `RootOK` invoked cap keeps `MdbS`.
  The destination is `lookup_target_slot`'s (in `OS`, `lookup_tgt_in`), canonical by `OSOK.canon` under `WinOK`
  (MdbWin); the source lookup's root is the cap of the non-null first extra slot (in `OS`), so `lookup_src_in`
  discharges gen 50's source hypothesis (`cnode.decode_copy.mdbSX`, MdbCopyD).
* **`syscall.decode_invocation.copy_mdbS`**: the same at `decode_invocation` for a CNode cap read from an `OS` slot.

Case hypotheses (input facts of the decode, as gen 30's `del_ty` takes `slot ∈ OS`): the invoked slot in `OS`
and the extra slots `0` or in `OS` (the latter discharged by `ipc.lookup_extra_caps.inOS` where the extras are
looked up). No named premise.

(gen 60) `cnode.decode.copyG` / `syscall.decode_invocation.cnodeG`: the decode-level traversal and the
`decode_invocation` dispatch for any invariant `P` (the target lookup's results satisfying some `Dq`); `copy_mdbS`
and its `decode_invocation` form are their `MdbS` instances.
-/
import Fl4ProofsA64.P1.MdbCopyD
import Fl4ProofsA64.P1.MdbWin
import Fl4ProofsA64.P1.QueueSlotTyDec
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

/-- **The source lookup returns a slot of `OS`** from a `RootOK` root. -/
theorem lookup_src_in {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (c : capability.Cap) (hc : RootOK OS c)
    (i d : U64) : cspace.lookup_source_slot st s c i d ⦃ r => ∀ x, r = .Ok x → x ∈ OS ⦄ :=
  lookup_op_in hT true c hc i d

/-- **The pivot lookup returns a slot of `OS`** from a `RootOK` root. -/
theorem lookup_piv_in {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (c : capability.Cap) (hc : RootOK OS c)
    (i d : U64) : cspace.lookup_pivot_slot st s c i d ⦃ r => ∀ x, r = .Ok x → x ∈ OS ⦄ :=
  lookup_op_in hT true c hc i d

/-- **A thread's lookup returns a slot of `OS`** when its CSpace-root slot is in `OS`. -/
theorem lookup_slotO {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) {t : U64} (ht : t ∈ OS) (cptr : U64) :
    cspace.lookup_slot st s t cptr ⦃ r => ∀ x, r = .Ok x → x.slot ∈ OS ⦄ := by
  unfold cspace.lookup_slot
  rw [tcb_slot_ctable, bind_ok, capA_eq, bind_ok]
  exact resolve_in hT _ (RootOK.of_slot hT ht (capA_eq s t)) cptr _

theorem cast_us3 (i : U64) (hi : i.val < 3) : (UScalar.cast .Usize i).val = i.val := by
  have : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with e | e <;> simp [e]
  simp only [UScalar.cast_val_eq, UScalar.size, UScalarTy.numBits]
  exact Nat.mod_eq_of_lt (by omega)

theorem spec_ex {α : Type _} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) : ∃ v, m = ok v ∧ P v :=
  spec_exists_u h

set_option maxHeartbeats 1000000 in
/-- **The extra-cap slots are `OS` slots** (or `0`) when the thread's CSpace-root slot is in `OS`. -/
theorem ipc.lookup_extra_caps.inOS {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) {t : U64} (ht : t ∈ OS)
    (buf : U64) (info : msginfo.MessageInfo) :
    ipc.lookup_extra_caps st s t buf info ⦃ r => ∀ e, r = .Ok e → ∀ x ∈ e.val, x ≠ 0#u64 → x ∈ OS ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h0 : ∀ x ∈ ipc.NO_EXTRA_CAPS.val, x = 0#u64 ∨ x ∈ OS := by
    intro x hx; left
    simp [ipc.NO_EXTRA_CAPS, Aeneas.Std.Array.make] at hx
    first | exact hx | (rcases hx with h | h | h <;> exact h)
  unfold ipc.lookup_extra_caps
  split
  · rw [WP.spec_ok]; intro e he x hx hx0; cases he; exact (h0 x hx).resolve_left hx0
  unfold ipc.lookup_extra_caps_loop
  refine WP.spec_mono (loop.spec_decr_nat (fun x => 3 - x.2.val)
    (fun x => ∀ y ∈ x.1.val, y = 0#u64 ∨ y ∈ OS)
    (fun r => ∀ e, r = .Ok e → ∀ y ∈ e.val, y = 0#u64 ∨ y ∈ OS) _ _ (fun x hx => ?_) h0)
    fun r hr e he y hy hy0 => (hr e he y hy).resolve_left hy0
  obtain ⟨arr, i⟩ := x
  dsimp only at hx ⊢
  unfold ipc.lookup_extra_caps_loop.body
  by_cases hin : i < info.extra_caps
  · by_cases hi3 : i < 3#u64
    · have hi3' : i.val < 3 := by scalar_tac
      simp only [hin, hi3, ↓reduceIte, lift, bind_ok]
      obtain ⟨b1, hb1, -⟩ := spec_ex msg.BUF_CAPS.spec
      rw [hb1, bind_ok]
      refine WP.spec_bind (P0.msg.buf_get.p0 st s buf _ hS) fun w _ => ?_
      refine WP.spec_bind (lookup_slotO hT ht w) fun r hr => ?_
      cases r with
      | Ok r1 =>
        simp only []
        obtain ⟨a', ha', ha'v⟩ := spec_ex (Aeneas.Std.Array.update_spec arr (UScalar.cast .Usize i) r1.slot
          (by have hl : arr.val.length = 3 := by simp
              rw [cast_us3 i hi3']; simp [Aeneas.Std.Array.length, hl]; omega))
        rw [ha']
        simp only [bind_ok]
        obtain ⟨i4, h4e, h4v⟩ := spec_ex (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
        rw [h4e, bind_ok, WP.spec_ok]
        have hi4 : i4.val = i.val + 1 := by simpa using h4v
        subst ha'v
        refine ⟨fun y hy => ?_, by rw [hi4]; omega⟩
        rw [Aeneas.Std.Array.set_val_eq] at hy
        rcases List.mem_or_eq_of_mem_set hy with h | h
        · exact hx y h
        · exact Or.inr (h ▸ hr r1 rfl)
      | Err lf =>
        simp only [WP.spec_ok]
        intro ex hex; cases hex
    · simp only [hin, hi3, ↓reduceIte, WP.spec_ok]
      intro ex hex; cases hex; exact hx
  · simp only [hin, ↓reduceIte, WP.spec_ok]
    intro ex hex; cases hex; exact hx

set_option hygiene false in
/-- An error leaf of the decode: the start state, `MdbS` held. -/
local macro "mleaf" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 hm
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     first | exact (WP.spec_ok _).2 hm | exact hm))

theorem lbl_cm (lbl : U64) (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨
    lbl = fl4_abi.label.CNodeMove ∨ lbl = fl4_abi.label.CNodeMutate) :
    lbl ≥ fl4_abi.label.CNodeCopy ∧ lbl ≤ fl4_abi.label.CNodeMutate := by
  rcases hl with rfl | rfl | rfl | rfl <;>
    (first | decide | (simp only [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeMint, fl4_abi.label.CNodeMove, fl4_abi.label.CNodeMutate]; decide) | simp [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeMint, fl4_abi.label.CNodeMove, fl4_abi.label.CNodeMutate])

set_option maxHeartbeats 2000000 in
/-- (gen 60) **`cnode.decode` at CNode Copy / Mint / Move / Mutate, for an invariant `P`** (gen 51's
`copy_mdbS` traversal, abstracted): the target lookup's results satisfy `Dq`, and `decode_copy` keeps `P` from the
start state for every `Dq` destination. -/
theorem cnode.decode.copyG {A : Type _} {ar : machine.Arch A} {s : S} {P : S → Prop} (hm : P s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (c : capability.Cap) {Dq : U64 → Prop}
    (hlk : ∀ i d : U64, cspace.lookup_target_slot st s c i d ⦃ r => ∀ x, r = .Ok x → Dq x ⦄)
    (hin : ∀ dest, Dq dest → cnode.decode_copy st s lbl len buf extra dest ⦃ r => P r.2 ⦄) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => P s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨hl1, hl2⟩ := lbl_cm lbl hl
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · mleaf
  split
  · mleaf
  split
  · mleaf
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
  refine WP.spec_bind (hlk idx dep) fun r hr => ?_
  rcases r with v | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    mleaf
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  try rw [if_pos hl1, if_pos hl2]
  refine WP.spec_bind (hin v (hr v rfl)) fun r2 h2 => ?_
  rcases r2 with ⟨r1, s1⟩
  exact (WP.spec_ok _).2 h2

/-- **`cnode.decode` at CNode Copy / Mint / Move / Mutate keeps `MdbS`** (module docstring). -/
theorem cnode.decode.copy_mdbS {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : MdbS st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => MdbS st OS s' ⦄ :=
  cnode.decode.copyG hm a hl c (lookup_tgt_in hT c hc) fun _ hv =>
    cnode.decode_copy.mdbSX hO q hm hl hv (hO.canon hW hv) fun sl hsl hs0 i d =>
      lookup_src_in hT _ (RootOK.of_slot hT (hx sl hsl hs0) (capA_eq s sl)) i d

set_option maxHeartbeats 1000000 in
/-- (gen 60) **A CNode invocation at `decode_invocation`, for an invariant `P`**: `cnode.decode` of the invoked cap
keeps `P` (gen 51's `copy_mdbS` dispatch, abstracted). -/
theorem syscall.decode_invocation.cnodeG {A : Type _} {ar : machine.Arch A} {s : S} {P : S → Prop} (hm : P s)
    (a : A) {lbl : U64} (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (hf : capFam cap = .cnode)
    (hdec : cnode.decode st ar s a lbl len cap buf extra ⦃ r s' _ => P s' ⦄) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ => P s' ⦄ := by
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 hm
  · exact hdec

/-- **CNode Copy / Mint / Move / Mutate at `decode_invocation`** of a CNode cap read from an `OS` slot keep `MdbS`. -/
theorem syscall.decode_invocation.copy_mdbS {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    (hW : WinOK T Ω) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : MdbS st OS s)
    (a : A) {lbl : U64} (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ => MdbS st OS s' ⦄ :=
  syscall.decode_invocation.cnodeG hm a len slot cap blk call don fp buf extra hf
    (cnode.decode.copy_mdbS hO hW q hT hm a hl cap (RootOK.of_slot hT hslot hcap) hx)

end ST
end R
end W7

end

end Fl4ProofsA64.P1

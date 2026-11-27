/-
# P2 (line p3mc, gen 33): a concrete store — `LawfulStore`, `PlainStore` and `StoreExt` hold of one model

The joint-satisfiability item `hB` (handoff §36c, §38) needs a concrete `machine.Store S`. None existed in the tree
(every P1 / P2 / P3 theorem is generic over `[LawfulStore st]`). This module gives one:

* **`BS`**: a word memory `U64 → U64` that is 0 at every unaligned address, a kernel-state base and a CPU number
  (a subtype, so that two states with the same aligned words are equal);
* **`bst : machine.Store BS`**: every operation total; `read` / `read_pair` read the map, `write` updates an
  aligned word (an unaligned write is a no-op), `zero` / `clear_free` clear the aligned words of `[a, a + n)`,
  `frame_masks` is `(0, 0)`;
* **`bsL : LawfulStore bst`**, **`bsP : PlainStore bst`**, **`bs_ext : StoreExt bst`** (the gen-32 conditional
  `locPlat_archT` asks `StoreExt st`: this discharges it for `bst`);
* **`BS.of m kb c`**: the state with aligned words `m`, base `kb` and CPU `c` (`BS.of_mem`), to build boot states.

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P1.FastDecline
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P1

/-- A store state: aligned words (0 at every unaligned address), the kernel-state base, the CPU. -/
def BS : Type := { p : (U64 → U64) × U64 × U64 // ∀ a : U64, ¬ Aligned a → p.1 a = 0#u64 }

/-- The word map. -/
def BS.m (s : BS) : U64 → U64 := s.1.1

/-- The kernel-state base. -/
def BS.kb (s : BS) : U64 := s.1.2.1

/-- The CPU. -/
def BS.cpu (s : BS) : U64 := s.1.2.2

/-- Write an aligned word (an unaligned address leaves the state). -/
def BS.wr (s : BS) (a v : U64) : BS :=
  ⟨(fun b => if Aligned a ∧ a = b then v else s.m b, s.kb, s.cpu), fun b hb => by
    show (if Aligned a ∧ a = b then v else s.m b) = 0#u64
    rw [if_neg (fun (h : Aligned a ∧ a = b) => hb (h.2 ▸ h.1))]; exact s.2 b hb⟩

/-- Clear the aligned words of `[a, a + n)`. -/
def BS.zr (s : BS) (a n : U64) : BS :=
  ⟨(fun b => if Aligned b ∧ a.val ≤ b.val ∧ b.val < a.val + n.val then 0#u64 else s.m b, s.kb, s.cpu),
    fun b hb => by
      show (if Aligned b ∧ a.val ≤ b.val ∧ b.val < a.val + n.val then 0#u64 else s.m b) = 0#u64
      rw [if_neg (fun h => hb h.1)]; exact s.2 b hb⟩

/-- **The concrete store** (module docstring). -/
def bst : machine.Store BS where
  frame_masks _ := ok (0#u64, 0#u64)
  read s a := ok (s.m a)
  read_pair s a := ok (s.m a, s.m (core.num.U64.wrapping_add a 8#u64))
  write s a v := ok (s.wr a v)
  zero s a n := ok (s.zr a n)
  clear_free s a n := ok (s.zr a n)
  ks_base s := ok s.kb
  cur_cpu s := ok s.cpu

/-- **`bst` is lawful.** -/
instance bsL : LawfulStore bst where
  frame_masks_total s := by show (ok (0#u64, 0#u64) : Result (U64 × U64)) ⦃ _ => True ⦄; simp
  mem := BS.m
  wr := BS.wr
  zr := BS.zr
  ksb := BS.kb
  cpu := BS.cpu
  read_eq _ _ := rfl
  read_pair_eq _ _ := rfl
  write_eq _ _ _ := rfl
  zero_eq _ _ _ := rfl
  clear_free_eq _ _ _ := rfl
  ks_base_eq _ := rfl
  cur_cpu_eq _ := rfl
  mem_wr s a v b ha _ := by
    show (if Aligned a ∧ a = b then v else s.m b) = _
    by_cases h : a = b
    · rw [if_pos ⟨ha, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  mem_zr s a n b _ _ _ hb := by
    show (if Aligned b ∧ a.val ≤ b.val ∧ b.val < a.val + n.val then 0#u64 else s.m b) = _
    by_cases h : a.val ≤ b.val ∧ b.val < a.val + n.val
    · rw [if_pos ⟨hb, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  ksb_wr _ _ _ := rfl
  cpu_wr _ _ _ := rfl
  ksb_zr _ _ _ := rfl
  cpu_zr _ _ _ := rfl

/-- **`bst` is plain** (`frame_masks = (0, 0)`). -/
instance bsP : PlainStore bst := ⟨fun _ => rfl⟩

/-- **`bst` is extensional** (P1's `StoreExt`): equal aligned words, base and CPU give the same state. -/
theorem bs_ext : StoreExt bst := by
  intro s s' hm hk hc
  apply Subtype.ext
  obtain ⟨⟨m, k, c⟩, hz⟩ := s
  obtain ⟨⟨m', k', c'⟩, hz'⟩ := s'
  have hmm : m = m' := by
    funext x
    by_cases hx : Aligned x
    · exact hm x hx
    · exact (hz x hx).trans (hz' x hx).symm
  change k = k' at hk
  change c = c' at hc
  subst hmm hk hc
  rfl

/-- The state with aligned words `m`, base `kb` and CPU `c`. -/
def BS.of (m : U64 → U64) (kb c : U64) : BS :=
  ⟨(fun a => if Aligned a then m a else 0#u64, kb, c), fun a ha => by
    show (if Aligned a then m a else 0#u64) = 0#u64
    rw [if_neg ha]⟩

theorem BS.of_mem (m : U64 → U64) (kb c : U64) {a : U64} (ha : Aligned a) : bsL.mem (BS.of m kb c) a = m a := by
  show (if Aligned a then m a else 0#u64) = m a
  rw [if_pos ha]

theorem BS.of_ksb (m : U64 → U64) (kb c : U64) : bsL.ksb (BS.of m kb c) = kb := rfl

theorem BS.of_cpu (m : U64 → U64) (kb c : U64) : bsL.cpu (BS.of m kb c) = c := rfl

end Fl4Proofs.P2.BootSt

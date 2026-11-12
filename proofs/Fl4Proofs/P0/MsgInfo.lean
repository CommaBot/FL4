/-
P0 for `fl4_core::msginfo`: decoding and encoding message info words never
fail (no overflow, no out-of-range shift), and decoding clamps the length.
-/
import Fl4Core.Funs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P0

open fl4_core

@[step]
theorem from_word_spec (w : U64) :
    msginfo.MessageInfo.from_word w ⦃ m => m.length.val ≤ 127 ⦄ := by
  unfold msginfo.MessageInfo.from_word
  step*

theorem from_word_clamped_spec (w : U64) :
    msginfo.MessageInfo.from_word_clamped w ⦃ m => m.length.val ≤ 120 ⦄ := by
  unfold msginfo.MessageInfo.from_word_clamped
  step*
  all_goals simp_all [fl4_abi.consts.MSG_MAX_LENGTH]

theorem to_word_spec (m : msginfo.MessageInfo) :
    msginfo.MessageInfo.to_word m ⦃ _ => True ⦄ := by
  unfold msginfo.MessageInfo.to_word
  step*

end Fl4Proofs.P0

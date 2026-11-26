/-
# P2 (line pte, generation 14): two leaf accesses of `decode_page_map` on another store (second `blk` piece)

`blk` (`PmBlkUW2`) asks that the accepted PageMap run's decode give on the guarded store what it gives on `st`.
`decode_page_map` (x86_64 `vspace.rs` l. 551) for a small, non-device, non-EPT frame cap reads the current thread,
its message registers 0–2 (`syscall_arg`), `extra[0]`'s cap, then `check_vspace` (the ASID table), the small-page
walk `page_entry_slot … Small`, the frame masks (`frame_address`), the NX feature word (`make_user_page`), writes the
caller's thread state (`set_thread_state … RESTART`), the invoked slot's cap words (`set_cap`) and the leaf
(`write_mapping`: one read and one write of the leaf, then Arch invalidations, which touch no store word).

* **`vspace.frame_address.guardK`**: `frame_address` on a store with `st`'s frame masks is `st`'s;
* **`vspace.write_mapping.guard`**: `write_mapping` on a store reading and writing the leaf as `st` is `st`'s;
Not here yet (gen 14 finding, see WS/handoff/pte.md): the congruence of the whole `decode_page_map` run. `simp` does
not reduce the size match's tuple bind `let (fs, b) ← match f.size with …` (a matcher on `(Small, false)` stays
stuck and simp does not rewrite inside it), so the run must be stepped with concrete intermediate results (as
P3/VsFrameMapRel's `map_tail` does with `ok_bind_spec`), not rewritten as a whole.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmRoot
import Fl4Proofs.P2.InvPmWalk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl

noncomputable section

section congr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {gS : machine.Store S}
variable {A : Type} (ar : machine.Arch A)

/-- **`frame_address` reads only the frame masks.** -/
theorem vspace.frame_address.guardK [GK gS st] (x : S) (a : A) (f : vspace.FrameCap) :
    vspace.frame_address gS ar x a f = vspace.frame_address st ar x a f := by
  unfold vspace.frame_address
  rw [gst_frame_masks]

/-- **`write_mapping` reads and writes only the leaf** (the Arch invalidations touch no store word). -/
theorem vspace.write_mapping.guard {R W : U64 → Prop} [GRd gS st R] [GWr gS st W] (x : S) (a : A)
    (slot e asid va : U64) (d : Bool) (hr : R slot) (hw : W slot) :
    vspace.write_mapping gS ar x a slot e asid va d = vspace.write_mapping st ar x a slot e asid va d := by
  unfold vspace.write_mapping
  rw [gst_read hr, gst_write hw]

end congr

end
end Fl4Proofs.P2.E2EP

/-
# P2 (line pte, generation 15): the PageMap decode on two stores (`blk`, first part)

`decode_page_map` (x86_64 `vspace.rs` l. 551) for a small, non-EPT frame cap, at the decode state `x`, on two stores
that answer its accesses alike:

* **`dpm_congr`**: the whole run is the same on `m1` and `m2` when the current thread, the three message arguments,
  `extra[0]`'s cap (a mapped PML4 cap), `check_vspace` of it, the small-page walk (answering the leaf `e`), the
  frame masks (`frame_address`), the NX / huge-page feature word (`make_user_page`, `huge_pages`), the caller's
  `set_thread_state`, the invoked slot's `set_cap` and the leaf's `write_mapping` agree. Closed-term rewriting
  only (no stepping), so it holds for every outcome, error arms included.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmDecRd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl

noncomputable section

section congr
variable {S : Type} {A : Type} (ar : machine.Arch A)

/-- **`decode_page_map` on two stores answering its accesses alike** (module docstring). -/
theorem dpm_congr (m1 m2 : machine.Store S) {x : S} {a : A} {length buf : U64} {slot : obj.Slot}
    {ex : Array obj.Slot 3#usize} {fp rt asid va : U64} {mp : Bool} {t x0 root rasid v0 v1 v2 e : U64}
    (hc1 : sched.cur_thread m1 x = ok t) (hc2 : sched.cur_thread m2 x = ok t)
    (hx0 : vspace.extra ex 0#usize = ok (some x0))
    (ha0 : msg.syscall_arg m1 x t buf 0#u64 = ok v0) (hb0 : msg.syscall_arg m2 x t buf 0#u64 = ok v0)
    (ha1 : msg.syscall_arg m1 x t buf 1#u64 = ok v1) (hb1 : msg.syscall_arg m2 x t buf 1#u64 = ok v1)
    (ha2 : msg.syscall_arg m1 x t buf 2#u64 = ok v2) (hb2 : msg.syscall_arg m2 x t buf 2#u64 = ok v2)
    (hk1 : obj.Slot.cap m1 x0 x = ok (.Pml4 root true rasid)) (hk2 : obj.Slot.cap m2 x0 x = ok (.Pml4 root true rasid))
    (hcv : vspace.check_vspace m1 x (.Pml4 root true rasid) = vspace.check_vspace m2 x (.Pml4 root true rasid))
    (hp1 : vspace.page_entry_slot m1 x root v0 .Small = ok (.Ok e))
    (hp2 : vspace.page_entry_slot m2 x root v0 .Small = ok (.Ok e))
    (hfa : ∀ f, vspace.frame_address m1 ar x a f = vspace.frame_address m2 ar x a f)
    (hmu : ∀ p at0 r l, vspace.make_user_page m1 x p at0 r l = vspace.make_user_page m2 x p at0 r l)
    (hhp : vspace.huge_pages m1 x = vspace.huge_pages m2 x)
    (hst : sched.set_thread_state m1 x t sched.TS_RESTART = sched.set_thread_state m2 x t sched.TS_RESTART)
    (hsc : ∀ y c, obj.Slot.set_cap m1 slot y c = obj.Slot.set_cap m2 slot y c)
    (hwm : ∀ y a' as' va' d, vspace.write_mapping m1 ar y a' e as' va' d = vspace.write_mapping m2 ar y a' e as' va' d) :
    vspace.decode_page_map m1 ar x a length slot
        { ptr := fp, size := .Small, rights := rt, is_device := false, mapped := mp, is_ept := false, asid,
          vaddr := va } buf ex =
      vspace.decode_page_map m2 ar x a length slot
        { ptr := fp, size := .Small, rights := rt, is_device := false, mapped := mp, is_ept := false, asid,
          vaddr := va } buf ex := by
  unfold vspace.decode_page_map
  simp only [hc1, hc2, hx0, ha0, hb0, ha1, hb1, ha2, hb2, hk1, hk2, hcv, hp1, hp2, hfa, hmu, hhp, hst, hsc, hwm,
    bind_ok, vspace.mapped_root, uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte,
    core.result.Result.Insts.CoreOpsTry.branch]

end congr

end
end Fl4Proofs.P2.E2EP

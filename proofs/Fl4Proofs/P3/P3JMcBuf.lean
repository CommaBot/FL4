/-
P3 (p3J gen 22): **no IPC buffer on a `CKI` run** — the fact the `UserW` half of the `…FootW` premises needs.

P1's footprints (`Cur0W = KW ∨ DbgW ∨ CapW ∨ UserW`) put a message transfer's IPC-buffer words in `UserW`
(`XferFoot`'s `U`), and P1's `UserOK` (which the transfer lemmas ask of `U`) places those words outside every TCB,
node, `Ω` word and endpoint / notification head, i.e. outside every object of `H` (`HKind` has no frame kind): so
"the receiver's IPC-buffer frame is an `H` object" is not merely missing from `JAtZ`, it is excluded by P1's own
side condition, and `ProjW` can never cover a buffer write. What makes the `…FootW` premises true on the runs they
are used on is instead that FL4 writes no buffer there:

* **`kw_of_cki`**: at a `JAtZ` state whose spec state is `CKI`, every typed-heap slot's FL4 cap abstracts to a `KW`
  cap (`StateRel` / `absCap`, as P3JMcUt's `no_untyped_of_cki`).
* **`lookup_ipc_buffer_cki`**: so FL4's `lookup_ipc_buffer` of every TCB of the typed heap is `0` (its buffer slot
  holds no `Frame` cap: `absCap` of a frame cap is an arch cap, not `KW`), for the sender and the receiver side.
  With a zero buffer FL4's transfer writes no buffer word (`msg::buf_set` is guarded by `buf != 0`), so the
  transfer's `U` can be taken empty and `UserW` drops out of the footprint of every entry of a `RunCK` run.

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcUt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- **Every typed-heap slot's cap abstracts to a `KW` cap at a `CKI` state** (module docstring). -/
theorem kw_of_cki {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) {x : U64} (hx : IsSlot Z.th x) : SInvCk.KW (absCap (capV (L.mem s) x)) := by
  have hR : StateRel Z.th (L.mem s) σ := J.xtop.rel.2.1.1
  obtain ⟨q, i, hsa, rfl⟩ := hx
  rcases hsa with ⟨r, hq, hi⟩ | ⟨hq, hi⟩
  · obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode q r hq
    obtain ⟨c, ac, hca, hac, hrel⟩ := hs (bitsOf i r) (length_bitsOf i r)
    have e1 : slotAddr q.bv (Fl4Spec.ofBl (bitsOf i r)) = slotOf q i := by
      rw [slotAddr_ofBl, blVal_bitsOf, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hi]
    rw [e1, capAt_capV] at hca
    have ec := ok_inj_ff hca
    subst ec
    have hco : capOpt (σ.kheap q.bv) (bitsOf i r) = some ac := by
      simp only [capOpt, hk, if_pos hwf]; exact hac
    rw [hrel.2]; exact hC _ _ _ hco
  · obtain ⟨tcb, hk, hs⟩ := hR.tcb q hq
    obtain ⟨c, ac, hca, hac, hrel⟩ := hs i hi
    have e1 : slotAddr q.bv (BitVec.ofNat 64 i) = slotOf q i := rfl
    rw [e1, capAt_capV] at hca
    have ec := ok_inj_ff hca
    subst ec
    have hco : capOpt (σ.kheap q.bv) (Fl4Spec.tcbCnodeIndex i) = some ac := by
      simp only [capOpt, hk]; exact hac
    rw [hrel.2]; exact hC _ _ _ hco

/-- **FL4's IPC-buffer lookup is `0` for every TCB of the typed heap at a `CKI` state** (module docstring). -/
theorem lookup_ipc_buffer_cki {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) {t : U64} (ht : Z.th t = some .tcb) (rcv : Bool) :
    msg.lookup_ipc_buffer st s rcv t = ok 0#u64 := by
  have hR : StateRel Z.th (L.mem s) σ := J.xtop.rel.2.1.1
  obtain ⟨x, c, hkx, hc, hca⟩ := hR.bufCap ht
  have hco : capOpt (σ.kheap t.bv) (Fl4Spec.tcbCnodeIndex 2) = some x.tcbIpcframe := by
    simp only [capOpt, hkx]; exact Endp.tcbCnodeMap_two x
  have hk := hC _ _ _ hco
  rw [← hca.2] at hk
  obtain ⟨w, hw, -⟩ := spec_exists (Endp.obj.Tcb.ipc_buffer.spec' (L := L) s t)
  unfold msg.lookup_ipc_buffer
  rw [hw, bind_ok, Endp.tcb_slot_buffer, bind_ok, slot_cap_eq, hc, bind_ok]
  cases c <;> first | rfl | exact (by simp [absCap, SInvCk.KW] at hk)

end

end Fl4Proofs.P3.Mc

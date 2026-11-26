/-
# P2 (line invj, generation 4): the entry facts of the CNodeDelete **PTE arm**

The no-PTE arm's canonical `Q` is `InvQF` = `InvQ ∧ InvLk`, with `InvArm`'s `p.n ≤ p.pte`. The PTE arm swaps that
clause for `p.pte < p.n`:

* `InvArmP` (label `CNodeDelete`, `p.pte < p.n`), `InvQP` (`InvQ` with `InvArmP`), `InvQFP` (`InvQP ∧ InvLk`);
* **`del_coreP`**: from `InvQFP` at the entry, stpost's `del_core` facts (the invoked CNode cap, the target, the
  walk, the locks on the target and its links, the seen words) for a **mapped** frame cap, plus the PTE branch:
  ASID ≠ 0, `small_page_entry = some e`, `e ≠ 0`, and `e` locked (the plan's `locks[pte]`, `plan_with_delP`).

No named premise. No existing statement changes.
-/
import Fl4Proofs.P2.InvDelPte
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}

variable (st) in
/-- **The PTE arm**: at the entry the current thread's label is `CNodeDelete` and the plan took a PTE lock. -/
def InvArmP (p : localinv.Plan) (s : S) : Prop :=
  ∀ t info, sched.cur_thread st s = ok t → msg.msg_info st s t = ok info →
    info.label = fl4_abi.label.CNodeDelete ∧ p.pte.val < p.n.val

variable (st) in
/-- `InvQ` with the PTE arm. -/
def InvQP (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayout)
    (m : U64 → U64) (s : S) : Prop :=
  IoQ st Cs Ω Sg Ac K m s ∧ InvPlanD st p s ∧ InvArmP st p s ∧
    ∀ (i : Nat) (x : U64), i < p.n.val → p.locks.val[i]? = some x → Locks s x

variable (st) in
/-- **The canonical `Q` of the PTE arm**: `InvQP ∧ InvLk`. -/
def InvQFP (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayout)
    (m : U64 → U64) (s : S) : Prop :=
  InvQP st Cs Ω Sg Ac Locks p K m s ∧ InvLk st p s

/-- (invj gen 4) **The PTE arm's facts at the entry from `InvQFP`** (module docstring). -/
theorem del_coreP (hq : InvQFP st Cs Ω Sg Ac Locks p K μ s) :
    ∃ (cp cr cg cgb dest fp rt asid va e : U64) (C : U64 → U64 → Prop),
      obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb) ∧ p.slot ∈ K.slots ∧
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA (L.curW s) layout.reg.R10))
        (L.mem s (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) ∧
      obj.Slot.cap st dest s = ok (.Frame fp .Small rt false true false asid va) ∧
      C cp cr ∧ WalkCl (st := st) s C ∧
      (∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots ∧
        OutsideObjs st K.heap.tcbs Cs s (cnSlot p (y &&& m)) ∧
        OutsideObjs st K.heap.tcbs Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)) ∧
      dest ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s dest ∧
      (dest ≠ 0#u64 → Locks s dest) ∧
      (L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
        Locks s (L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV))) ∧
      (∀ nx, obj.Slot.next st dest s = ok nx → nx ≠ 0#u64 → Locks s nx) ∧
      (∀ x, SeenW p x → DelW dest x) ∧
      asid ≠ 0#u64 ∧ localinv.small_page_entry st s asid va = ok (some e) ∧ e ≠ 0#u64 ∧ Locks s e := by
  obtain ⟨⟨⟨PE, -⟩, ⟨t, info, ex, et, ei, hpw⟩, harm, hlk⟩, ⟨x, hx, hxs⟩⟩ := hq
  have ht : t = L.curW s := ok_inj_ff (et.symm.trans (cur_thread_ok s))
  subst ht
  obtain ⟨hlbl, hpt⟩ := harm _ _ (cur_thread_ok s) ei
  rw [hlbl] at hpw
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, hcap, htg, hdc, hHd, hHp, hHn, hSn, -⟩ :=
    plan_with_delF hpw
  obtain ⟨cp', cr', cg', cgb', dest', fp', rt', asid', va', mp', hcap', htg', hdc', hP⟩ := plan_with_delP hpw
  obtain ⟨hmp, hA, e, he, he0, hle⟩ := hP hpt
  rw [hcap] at hcap'
  have e1 := ok_inj_ff hcap'
  simp only [capability.Cap.CNode.injEq] at e1
  obtain ⟨c1, c2, c3, c4⟩ := e1
  rw [← c1, ← c2, ← c3, ← c4, htg] at htg'
  have e2 := ok_inj_ff htg'
  simp only [core.result.Result.Ok.injEq] at e2
  rw [← e2, hdc] at hdc'
  have e3 := ok_inj_ff hdc'
  simp only [capability.Cap.Frame.injEq, true_and] at e3
  obtain ⟨-, -, f3, f4, f5⟩ := e3
  rw [← f4, ← f5] at he
  rw [← f4] at hA
  rw [← f3] at hmp
  subst hmp
  obtain ⟨C, hroot, hcl, hC⟩ := PE.walk
  obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hx
  rw [hxs] at hs0
  have hCc : C cp cr := hcl q0 r0 m0 y0 cp cr cg cgb hq0 hm0 (by rw [← hs0]; exact hcap)
  obtain ⟨q1, r1, m1, y1, hq1, hm1, hs1⟩ :=
    lts_cn (fun p r gs g e => by cases e; exact hCc) hcl htg
  have hD := hC q1 r1 m1 y1 hq1 hm1
  rw [← hs1] at hD
  have held : ∀ y, PHeld p y → Locks s y := fun y ⟨j, hj, hy⟩ => hlk j y hj hy
  refine ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, e, C, hcap, ?_, htg, hdc, hCc, hcl, hC, hD.1, hD.2.1,
    fun hd => held _ (hHd hd), fun hd => held _ (hHp hd), fun nx e hne => held _ (hHn nx e hne), ?_,
    hA, he, he0, hlk _ e hpt hle⟩
  · rw [hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).1
  · intro w ⟨i, q, hi, hiM, hidx, hq⟩
    have hM : localinv.MAX_LOCKS.val = 4 := maxLocks_val
    have hiv : i.val < 4 := by have : i.val < localinv.MAX_LOCKS.val := hiM; omega
    have hlen : p.seen.val.length = 4 := by have hp := p.seen.property; simpa using hp
    have hl : i.val < p.seen.length := by simp only [Aeneas.Std.Array.length]; omega
    rw [eq_of_spec_fd (Aeneas.Std.Array.index_usize_spec p.seen i hl)] at hidx
    have e := ok_inj_ff hidx
    subst e hq
    exact hSn i.val (by omega) hi

end ent

end Fl4Proofs.P2.PathObl

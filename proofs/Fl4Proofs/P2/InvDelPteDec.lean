/-
# P2 (line invj, generation 4): the Delete decode block of the **PTE arm**: `KeepSX` with the leaf

stpost's `cnDel_keep` / `invRep_ok_keep` / `decDel_keep` (P2/InvBlkFin.lean) for a mapped frame cap with a non-zero
ASID whose `unmap_page` at the decode state is `unmapLeaf` at the planned leaf `e` (`hu`, from `unmap_pte`):
the decode then `invRep` write `IoTW t`, capability-slot words and `e` (`KeepSX … X` with `X e`), and reply `Ok ()`.

* `SlotOKX.notT`; **`cnDelP_keep`**, `invRep_ok_keepX`, **`decDelP_keep`**.

No named premise. No existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

section keepX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {X : U64 → Prop}

/-- A slot word is no `IoTW t` word (`SlotOK.tf`). -/
theorem SlotOKX.notT {s0 : S} {t b : U64} (F : SchedOK (L := L) s0 t) (O : SlotOKX (L := L) K X s0 t) (hs : SlotWX K X b) :
    ¬ IoTW t b := by
  rintro (⟨r, hr, e⟩ | e)
  · obtain ⟨k, hk, ek⟩ := regA_eq F.tcb hr
    rw [ek] at e; subst e
    exact O.tf k (by omega) (by omega) hs
  · subst e
    exact O.tf _ (by rw [st_val]; omega) (by rw [st_val]; omega) hs



end keepX

section dec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {X : U64 → Prop}

/-- **`invRep` of `Ok`** from a `KeepS` state where `t` is current: `reply_success_empty` and `set_thread_state
RUNNING` when `t` is `RESTART`; result `Ok ()`. -/
theorem invRep_ok_keepX {s0 x : S} {t : U64} {a : A} {z : S × A × core.result.Result Unit error.Exc}
    (F : SchedOK (L := L) s0 t) (O : SlotOKX (L := L) K X s0 t) (hk : KeepSX st K X s0 t x)
    (h : invRep st t x a (.Ok ()) = ok z) : z.2.2 = .Ok () ∧ KeepSX st K X s0 t z.1 := by
  have Fx := hk.sched F O
  unfold invRep at h
  obtain ⟨i6, -, h⟩ := bind_eq_ok h
  obtain ⟨t1, et1, h⟩ := bind_eq_ok h
  cases ok_inj_ff h
  refine ⟨rfl, ?_⟩
  by_cases hi : i6 = sched.TS_RESTART
  · rw [if_pos hi] at et1
    obtain ⟨s5, es5, et1⟩ := bind_eq_ok et1
    have k5 : KeepA (L := L) x t s5 := by
      unfold msg.reply_success_empty at es5
      rw [set_reg_ok'] at es5; simp only [bind_ok] at es5
      obtain ⟨mi, -, es5⟩ := bind_eq_ok es5
      unfold msg.set_msg_info at es5
      obtain ⟨w, -, es5⟩ := bind_eq_ok es5
      rw [set_reg_ok'] at es5
      cases ok_inj_ff es5
      exact ((KeepA.refl hk.2.1 hk.2.2).wr_reg Fx rB384).wr_reg Fx rM384
    exact hk.keepA (k5.sts Fx (Or.inr rfl) et1)
  · rw [if_neg hi] at et1
    cases ok_inj_ff et1
    exact hk

/-- **The Delete decode writes `IoTW t` and slot words only** (from the decode state `x`, where `t` is current,
schedulable, the action `RESUME_CURRENT`), returning `Ok ()`: `set_thread_state RESTART`, then the frame's
deletion. -/
theorem cnDelP_keep {x : S} {a : A} {t length buf cp cr cg cgb dest fp rt asid va e : U64}
    {ex : Aeneas.Std.Array obj.Slot 3#usize}
    (F : SchedOK (L := L) x t) (O : SlotOKX (L := L) K X x t) (ha : L.actionW x = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING)
    (hL : Slot8 K) (hlen : ¬ length < 2#u64)
    (hlk : cspace.lookup_target_slot st x (.CNode cp cr cg cgb) (L.mem x (regA t layout.reg.R10))
      (L.mem x (regA t layout.reg.R8)) = ok (.Ok dest))
    (hd : dest ∈ K.slots) (hc : obj.Slot.cap st dest x = ok (.Frame fp .Small rt false true false asid va))
    (hA : asid ≠ 0#u64)
    (hu : ∀ x3, sched.set_thread_state st x t sched.TS_RESTART = ok x3 → ∀ a' : A,
      vspace.unmap_page st ar x3 a' .Small asid va fp = unmapLeaf st ar x3 a' e asid va fp)
    (hXe : X e) (hes : ¬ SlotW K e) (heA : Aligned e)
    (hp : L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots)
    (hn : ∀ nx, obj.Slot.next st dest x = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
    {y : core.result.Result Unit error.Exc × S × A}
    (h : cnode.decode st ar x a fl4_abi.label.CNodeDelete length (.CNode cp cr cg cgb) buf ex = ok y) :
    y.1 = .Ok () ∧ KeepSX st K X x t y.2.1 := by
  unfold cnode.decode at h
  rw [if_neg lblD1, if_neg lblD2, if_neg hlen, cur_thread_ok, F.cur] at h
  simp only [bind_ok] at h
  rw [sarg0_reg, sarg1_reg, reg_ok, reg_ok] at h
  simp only [bind_ok] at h
  rw [hlk] at h
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lblD3, lblD4, ↓reduceIte] at h
  obtain ⟨s3, hs3, h⟩ := bind_eq_ok h
  have K3 : KeepA (L := L) x t s3 := (KeepA.refl ha hr).sts F (Or.inl rfl) hs3
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s3 b = L.mem x b := fun b hs hb =>
    K3.mem hb (O.notT F (Or.inl hs))
  have hc3 : obj.Slot.cap st dest s3 = ok (.Frame fp .Small rt false true false asid va) := by
    rw [cap_agree hL hd ag]; exact hc
  have ep : L.mem s3 (core.num.U64.wrapping_add dest layout.cte.PREV) =
      L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) :=
    ag _ (slotW_of hL hd (by simp [layout.cte.PREV])) (slot_al hL hd (by simp [layout.cte.PREV])
      (by simp [layout.cte.PREV]))
  have hlnk : ∀ x1 a1, vspace.unmap_page st ar s3 a .Small asid va fp = ok (x1, a1) →
      (L.mem x1 (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
        L.mem x1 (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots) ∧
      (∀ nx, obj.Slot.next st dest x1 = ok nx → nx ≠ 0#u64 → nx ∈ K.slots) := by
    intro x1 a1 hu1
    rw [hu s3 hs3 a] at hu1
    have ag1 : ∀ b, SlotW K b → Aligned b → L.mem x1 b = L.mem x b := by
      intro b hs hb
      rcases unmapLeaf_st ar hu1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ag b hs hb
      · rw [L.mem_wr_ne heA hb (fun hv => hes ((UScalar.eq_of_val_eq hv) ▸ hs))]
        exact ag b hs hb
    have ep1 : L.mem x1 (core.num.U64.wrapping_add dest layout.cte.PREV) =
        L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) :=
      ag1 _ (slotW_of hL hd (by simp [layout.cte.PREV])) (slot_al hL hd (by simp [layout.cte.PREV])
        (by simp [layout.cte.PREV]))
    exact ⟨by rw [ep1]; exact hp, fun nx e' => hn nx (by rw [← next_agree hL hd ag1]; exact e')⟩
  obtain ⟨hy1, x1, a1, hu1, wd⟩ := del_frame_pte ar hL hd hc3 hA hlnk h
  have k3 : KeepSX st K X x t s3 := KeepSX.of_keepA K3
  have k1 : KeepSX st K X x t x1 := by
    rw [hu s3 hs3 a] at hu1
    rcases unmapLeaf_st ar hu1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact k3
    · exact k3.slots F O ((writesIn_wr heA).mono fun b hb => by subst hb; exact Or.inr hXe)
  exact ⟨hy1, k1.slots F O (wd.mono fun b hb => Or.inl hb)⟩

/-- **The decode block's footprint**: from the decode state `x`, the Delete decode then `invRep` write `IoTW t`
and slot words only, and the reply is `Ok ()`. -/
theorem decDelP_keep {x : S} {a : A} {t length buf cp cr cg cgb dest fp rt asid va slot e : U64}
    {ex : Aeneas.Std.Array obj.Slot 3#usize}
    (F : SchedOK (L := L) x t) (O : SlotOKX (L := L) K X x t) (ha : L.actionW x = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING)
    (hL : Slot8 K) (hlen : ¬ length < 2#u64)
    (hlk : cspace.lookup_target_slot st x (.CNode cp cr cg cgb) (L.mem x (regA t layout.reg.R10))
      (L.mem x (regA t layout.reg.R8)) = ok (.Ok dest))
    (hd : dest ∈ K.slots) (hc : obj.Slot.cap st dest x = ok (.Frame fp .Small rt false true false asid va))
    (hA : asid ≠ 0#u64)
    (hu : ∀ x3, sched.set_thread_state st x t sched.TS_RESTART = ok x3 → ∀ a' : A,
      vspace.unmap_page st ar x3 a' .Small asid va fp = unmapLeaf st ar x3 a' e asid va fp)
    (hXe : X e) (hes : ¬ SlotW K e) (heA : Aligned e)
    (hp : L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem x (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots)
    (hn : ∀ nx, obj.Slot.next st dest x = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
    {y : core.result.Result Unit error.Exc × S × A} {z : S × A × core.result.Result Unit error.Exc}
    (hy : syscall.decode_invocation st ar x a fl4_abi.label.CNodeDelete length slot (.CNode cp cr cg cgb)
      true true true false buf ex = ok y)
    (hz : invRep st t y.2.1 y.2.2 y.1 = ok z) : z.2.2 = .Ok () ∧ KeepSX st K X x t z.1 := by
  rw [decode_cnode_eq] at hy
  obtain ⟨hy1, k1⟩ := cnDelP_keep ar F O ha hr hL hlen hlk hd hc hA hu hXe hes heA hp hn hy
  rw [hy1] at hz
  exact invRep_ok_keepX F O k1 hz

end dec

end Fl4Proofs.P2.PathObl

/-
P1: **retype of TCBs keeps the invariants** (`RetypeP1Step` for `n = 1`),
and so retype of every kind (`retypeP1Step`).  The region's objects are
dropped, the creation's writes agree off the debug lists over the dropped
heap (`agreeD_of_writes`), the new TCBs are placed by the window with their
fields from `F` zero but the initialised ones (`addOKT_window`), and the
debug links name null, kept or new TCBs (`DbgLinksOK.tzT`); then
`BlkOK.agreeAddTcb`.
-/
import Fl4Proofs.P1.QueueRetypeP1
import Fl4Proofs.P1.QueueHeapAddTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {Cs : Set U64}

/-- **The new TCBs' placement**, from the window. -/
theorem addOKT_window {lo hi A k w us : Nat} {s s' : S}
    (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hbits : ∀ kd, newKind 1 us = some kd → 2 ^ kd.bits ≤ k)
    (hnode : RegionOffNodes st Cs s lo hi) (hwin : WinInit st s' lo hi A k w 1 us) (hwp : WinPlaced A k w 1 us)
    (hks : L.ksb s' = L.ksb s) :
    AddOKT st (H.drop (RegionD H lo hi)) (NewAt A k w) Cs s' := by
  have hk1 : newKind 1 us = some .tcb := by simp [newKind]
  have hb : 4096 ≤ k := hbits .tcb hk1
  obtain ⟨hal, hfit, hA0, -⟩ := hwp
  obtain ⟨hA, hk⟩ := hal .tcb hk1
  rw [show (HKind.tcb).bits = 12 from rfl] at hA hk
  have pos : ∀ {q : U64}, NewAt A k w q → ∃ j, j < w ∧ q.val = A + j * k ∧ (j + 1) * k ≤ w * k := by
    rintro q ⟨j, hj, hq⟩; exact ⟨j, hj, hq, Nat.mul_le_mul_right _ hj⟩
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hks]
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq p kp hp => ?_,
    fun q q' hq hq' hne => ?_, fun q hq c hc => ?_, fun q hq => ?_, fun q hq K h1 h2 h8 n1 n2 n3 => ?_⟩
  · obtain ⟨j, hj, hv, hjk⟩ := pos hq
    unfold Heap.drop
    by_cases hD : RegionD H lo hi q
    · simp [hD]
    · simp only [hD, if_false]
      cases hH : H q with
      | none => rfl
      | some kq =>
        exfalso; apply hD
        simp only [RegionD, hH, Option.elim, MeetsR]
        have := Nat.one_le_two_pow (n := kq.bits)
        rw [Nat.add_mul, Nat.one_mul] at hjk; omega
  · obtain ⟨j, -, hv, -⟩ := pos hq
    rw [hv, Nat.add_mod, Nat.mul_mod, hk, hA]; simp
  · obtain ⟨j, -, hv, hjk⟩ := pos hq
    rw [Nat.add_mul, Nat.one_mul] at hjk; omega
  · obtain ⟨j, -, hv, -⟩ := pos hq
    intro e; rw [e] at hv; simp at hv; omega
  · obtain ⟨j, -, hv, hjk⟩ := pos hq
    obtain ⟨hD, hp'⟩ := Heap.drop_eq_some.1 hp
    rw [Nat.add_mul, Nat.one_mul] at hjk
    simp only [RegionD, hp', Option.elim, MeetsR, not_not] at hD
    omega
  · obtain ⟨j, hj, hv, -⟩ := pos hq
    obtain ⟨j', hj', hv', -⟩ := pos hq'
    have hjj : j ≠ j' := fun e => hne (UScalar.eq_of_val_eq (by rw [hv, hv', e]))
    rcases Nat.lt_or_gt_of_ne hjj with h | h
    · have : (j + 1) * k ≤ j' * k := Nat.mul_le_mul_right _ h
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    · have : (j' + 1) * k ≤ j * k := Nat.mul_le_mul_right _ h
      rw [Nat.add_mul, Nat.one_mul] at this; omega
  · obtain ⟨j, -, hv, hjk⟩ := pos hq
    rw [Nat.add_mul, Nat.one_mul] at hjk
    rw [hnb]; rcases hnode.1 c hc with h | h <;> omega
  · obtain ⟨j, -, hv, hjk⟩ := pos hq
    rw [Nat.add_mul, Nat.one_mul] at hjk
    rw [hks]; rcases hnode.2 with h | h <;> omega
  · obtain ⟨j0, hj0, hv, hjk⟩ := pos hq
    rw [Nat.add_mul, Nat.one_mul] at hjk
    have hq4 : q.val % 2 ^ 12 = 0 := by rw [hv, Nat.add_mod, Nat.mul_mod, hk, hA]; simp
    have hbv : (core.num.U64.wrapping_add q K).val = q.val + K.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rcases hwin (by rw [hk1]; rfl) (fun z e => by rw [hk1] at e; cases e) _ (by unfold Aligned; rw [hbv]; omega) (by rw [hbv]; omega)
        (by rw [hbv]; omega) with h | ⟨-, j, hj, K', ⟨hK', hK4⟩, he⟩
    · exact h
    · exfalso
      rw [hbv] at he
      rcases Nat.lt_trichotomy j j0 with hl | rfl | hl
      · have : (j + 1) * k ≤ j0 * k := Nat.mul_le_mul_right _ hl
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      · omega
      · have : (j0 + 1) * k ≤ j * k := Nat.mul_le_mul_right _ hl
        rw [Nat.add_mul, Nat.one_mul] at this; omega

/-- The debug links after a TCB retype are typed over the dropped heap with the new TCBs. -/
theorem DbgLinksOK.tzT {lo hi A k w : Nat} {s s' : S} (P : DropOK st H (RegionD H lo hi) Cs s)
    (AT : AddOKT st (H.drop (RegionD H lo hi)) (NewAt A k w) Cs s')
    (h : DbgLinksOK st H Cs s' lo hi A k w 1) :
    DbgTz st ((H.drop (RegionD H lo hi)).add (NewAt A k w) .tcb).tcbs Cs s' := by
  have cv : ∀ x, NewTcbRef H lo hi A k w 1 x → Tz ((H.drop (RegionD H lo hi)).add (NewAt A k w) .tcb).tcbs x := by
    rintro x (h0 | ⟨hx, hD⟩ | ⟨-, hn⟩)
    · exact Or.inl h0
    · exact Or.inr (AT.up (Heap.mem_tcbs_drop.2 ⟨hx, hD⟩))
    · exact Or.inr (AT.tcbs_add.2 (Or.inr hn))
  have ref : ∀ y ∈ ((H.drop (RegionD H lo hi)).add (NewAt A k w) .tcb).tcbs,
      NewTcbRef H lo hi A k w 1 y ∧ y ≠ 0#u64 := fun y hy => by
    rcases AT.tcbs_add.1 hy with hy | hn
    · obtain ⟨h1, h2⟩ := Heap.mem_tcbs_drop.1 hy
      exact ⟨Or.inr (Or.inl ⟨h1, h2⟩), P.ne0 (by rw [show H y = some .tcb from h1]; simp)⟩
    · exact ⟨Or.inr (Or.inr ⟨rfl, hn⟩), AT.nz y hn⟩
  exact ⟨fun y hy => cv _ (h.1 y (ref y hy).1 (ref y hy).2).1, fun y hy => cv _ (h.1 y (ref y hy).1 (ref y hy).2).2,
    fun c hc => cv _ (h.2 c hc)⟩

set_option maxHeartbeats 8000000 in
/-- **`RetypeP1Step` for TCBs.** -/
theorem retypeP1Step_tcb {s s' : S} {Ac : Set U64} {lo hi A k w us : Nat} :
    RetypeP1Step st s s' H Cs Ac lo hi A k w 1 us := by
  classical
  intro hb hlo hhi hbits P hnode hw hwin hdbg hwp h0Cs
  have hb0 := hb.drop P
  have G := agreeD_of_writes hb0 hw.al (fun b hb' => retype_write_cls P hnode hb'.1 hb'.2)
  have hk1 : newKind 1 us = some .tcb := by simp [newKind]
  have AT := addOKT_window (H := H) hlo hhi hbits hnode hwin hwp G.ksb
  have hB := BlkOK.agreeAddTcb P.heap.drop hb0 G AT h0Cs (hdbg.tzT P AT)
  rw [← retypeHeap_some hk1] at hB
  have heq : ∀ q, retypeHeap H lo hi A k w 1 us q =
      if NewAt A k w q ∧ (newKind 1 us).isSome then newKind 1 us else H.drop (RegionD H lo hi) q := fun q => by
    unfold retypeHeap; rfl
  have inR : ∀ q, NewAt A k w q → lo ≤ q.val ∧ q.val + 8 ≤ hi := by
    rintro q ⟨j, hj, hq⟩
    have := hbits .tcb hk1
    rw [show (HKind.tcb).bits = 12 from rfl] at this
    have : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have notNew : ∀ q kd, H q = some kd → ¬ MeetsR lo hi q.val (q.val + 2 ^ kd.bits) →
      ¬ (NewAt A k w q ∧ (newKind 1 us).isSome) := fun q kd hq hm ⟨hN, _⟩ => by
    have := inR q hN; apply hm; unfold MeetsR; have := Nat.one_le_two_pow (n := kd.bits); omega
  have rD : ∀ q kd, H q = some kd → (RegionD H lo hi q ↔ MeetsR lo hi q.val (q.val + 2 ^ kd.bits)) :=
    fun q kd hq => by simp only [RegionD, hq, Option.elim]
  have h00 := hb0.1.choose_spec.choose_spec
  have hcur := h00.cur
  have ea : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW; exact G.cur hcur (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
  have ei : L.idleW s' = L.idleW s := by
    unfold LawfulStore.idleW; exact G.cur hcur (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)
  refine ⟨retypeHeap H lo hi A k w 1 us, Ac, hB, fun q kd hq hm => ?_, fun q kd hq => ?_,
    fun q hq kd hk => ?_, fun q he hd => ?_⟩
  · rw [heq, if_neg (notNew q kd hq hm), Heap.drop_of_not (fun h => hm ((rD q kd hq).1 h)), hq]
  · rw [heq] at hq
    by_cases hc : NewAt A k w q ∧ (newKind 1 us).isSome
    · rw [if_pos hc] at hq; exact Or.inr ⟨hc.1, hq⟩
    · rw [if_neg hc] at hq
      obtain ⟨hD, hq'⟩ := Heap.drop_eq_some.1 hq
      exact Or.inl ⟨hq', fun h => hD ((rD q kd hq').2 h)⟩
  · rw [heq, if_pos (show NewAt A k w q ∧ (newKind 1 us).isSome from ⟨hq, by rw [hk]; rfl⟩), hk]
  · by_cases hnone : H q = none
    · exact DeadQ.of_none (he.trans hnone)
    by_cases hc : NewAt A k w q ∧ (newKind 1 us).isSome
    · have hq' : retypeHeap H lo hi A k w 1 us q = some .tcb := by rw [heq, if_pos hc, hk1]
      have nT : q ∉ (H.drop (RegionD H lo hi)).tcbs := fun h => AT.notN h hc.1
      unfold DeadQ
      rw [hq']
      refine ⟨fun _ => ⟨?_, AT.zSc hc.1, AT.zBnd hc.1, ?_, ?_⟩, (fun h => by cases h), (fun h => by cases h),
        (fun h => by cases h), (fun z h => by cases h)⟩
      · rw [AT.zSt hc.1]; unfold sched.TS_INACTIVE; rfl
      · rw [ea]
        rcases h00.action with e | e | e
        · rw [e]; exact AT.nz q hc.1
        · rw [e]; intro e'; have := AT.align q hc.1; rw [e'] at this; simp at this
        · exact fun e' => nT (e' ▸ e)
      · rw [ei]; exact fun e' => nT (e' ▸ h00.idleT)
    · have h1 : retypeHeap H lo hi A k w 1 us q = H.drop (RegionD H lo hi) q := by rw [heq, if_neg hc]
      have h2 : H.drop (RegionD H lo hi) q = H q := h1.symm.trans he
      have hd1 : DeadQ st (H.drop (RegionD H lo hi)) s q := DeadQ.heq h2 hd
      have hO := hb0.2.2.1.1
      refine DeadQ.heq h1 (hd1.keepw (fun hq => ⟨?_, ?_, ?_⟩) ?_ ?_ (fun hq => ?_) (fun hq => ?_) (fun hq => ?_)
        (fun z hq => ?_))
      · rw [stA_eq]; exact G.fld q hq _ (by simp) (by simp) (by simp) (by simp) (by simp)
      · rw [scA_eq]; exact G.fld q hq _ (by simp) (by simp) (by simp) (by simp) (by simp)
      · unfold boundA; exact G.fld q hq _ (by simp) (by simp) (by simp) (by simp) (by simp)
      · exact ea
      · exact ei
      · unfold LawfulStore.epState; rw [(G.epw q hq).2]
      · exact ⟨G.sig _ (hO.ntB q hq).2, G.sig _ (hO.ntW q hq)⟩
      · exact G.sig _ (hO.tcbW hq)
      · exact ⟨G.sig _ (hO.fixW q ⟨z, hq⟩).1, G.sig _ (hO.repW q ⟨z, hq⟩), G.sig _ (hO.snW q ⟨z, hq⟩)⟩

/-- The families are all done. -/
theorem retypeFams : RetypeFams st := ⟨fun _ _ _ _ _ _ _ _ _ _ _ => retypeP1Step_tcb⟩

/-- **P1's half of retype, for every kind.** -/
theorem retypeP1Step {s s' : S} {Ac : Set U64} {lo hi A k w n us : Nat} :
    RetypeP1Step st s s' H Cs Ac lo hi A k w n us :=
  retypeP1Step_of retypeFams

end

end Fl4Proofs.P1

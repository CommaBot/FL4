/-
P1: **retype keeps the invariants** (`RetypeP1Step`), by family.  The
region's objects are dropped at the start (`BlkOK.drop`); the creation's
writes are cap-slot words (of the dropped heap, or untracked if they were in
dropped objects, `capw_drop`), the region's words (untracked) and the debug
lists (`blk_of_writesD`, the links typed by `DbgLinksOK`); then the new
objects are added (`BlkOK.add*`, their placement `AddOK` from the window and
`WinInit`).
-/
import Fl4Proofs.P1.QueueHeapDbg
import Fl4Proofs.P1.QueueHeapAddO
import Fl4Proofs.P1.QueueHeapAddSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {Cs : Set U64}

/-- A retype's write over the dropped heap: a cap-slot, untracked or debug-list word. -/
theorem retype_write_cls {lo hi : Nat} {s : S} (P : DropOK st H (RegionD H lo hi) Cs s)
    (hnode : RegionOffNodes st Cs s lo hi) {b : U64} (ha : Aligned b)
    (hb : CapW (Heap.tcbs H) (Heap.omega H) (Heap.frame H) b ∨ (lo ≤ b.val ∧ b.val < hi) ∨
      DbgW st (Heap.tcbs H) Cs s b) :
    CapW (H.drop (RegionD H lo hi)).tcbs (H.drop (RegionD H lo hi)).omega (H.drop (RegionD H lo hi)).frame b ∨
      Untracked st (H.drop (RegionD H lo hi)).tcbs Cs (H.drop (RegionD H lo hi))
        (H.drop (RegionD H lo hi)).frame s b ∨
      DbgW st (H.drop (RegionD H lo hi)).tcbs Cs s b := by
  rcases hb with hc | ⟨h1, h2⟩ | (⟨y, hy, e⟩ | hn)
  · rcases capw_drop P rfl ha hc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inl (untracked_of_noKept P.heap ha (noKept_of_region h1 h2) fun c hc => ?_))
    rcases hnode.1 c hc with h | h <;> omega
  · by_cases hD : RegionD H lo hi y
    · have hfit := P.heap.fits y .tcb hy
      have hal := P.heap.align y .tcb hy
      have hya : TcbAddr y := ⟨fun h0 => P.ne0 (by rw [show H y = some .tcb from hy]; simp)
        (UScalar.eq_of_val_eq (by simpa using h0)), hal, hfit⟩
      have hin : ∀ K : U64, K.val < 4096 → InObj y .tcb (core.num.U64.wrapping_add y K) := fun K hK => by
        have := field_val hya hK; unfold InObj; rw [this, show (HKind.tcb).bits = 12 from rfl]; omega
      refine Or.inr (Or.inl (untracked_of_dropped P rfl hy hD ha ?_))
      rcases e with e | e <;> rw [e]
      · exact hin 3576#u64 (by simp)
      · exact hin 3584#u64 (by simp)
    · exact Or.inr (Or.inr (Or.inl ⟨y, Heap.mem_tcbs_drop.2 ⟨hy, hD⟩, e⟩))
  · exact Or.inr (Or.inr (Or.inr hn))

/-- The debug links after a retype without new TCBs are typed over the dropped heap. -/
theorem DbgLinksOK.tz {lo hi A k w n : Nat} {s s' : S} (P : DropOK st H (RegionD H lo hi) Cs s) (hn : n ≠ 1)
    (h : DbgLinksOK st H Cs s' lo hi A k w n) : DbgTz st (H.drop (RegionD H lo hi)).tcbs Cs s' := by
  have cv : ∀ x, NewTcbRef H lo hi A k w n x → Tz (H.drop (RegionD H lo hi)).tcbs x := by
    rintro x (h0 | ⟨hx, hD⟩ | ⟨h1, -⟩)
    · exact Or.inl h0
    · exact Or.inr (Heap.mem_tcbs_drop.2 ⟨hx, hD⟩)
    · exact absurd h1 hn
  have ref : ∀ y ∈ (H.drop (RegionD H lo hi)).tcbs, NewTcbRef H lo hi A k w n y ∧ y ≠ 0#u64 := fun y hy => by
    obtain ⟨h1, h2⟩ := Heap.mem_tcbs_drop.1 hy
    exact ⟨Or.inr (Or.inl ⟨h1, h2⟩), P.ne0 (by rw [show H y = some .tcb from h1]; simp)⟩
  exact ⟨fun y hy => cv _ (h.1 y (ref y hy).1 (ref y hy).2).1, fun y hy => cv _ (h.1 y (ref y hy).1 (ref y hy).2).2,
    fun c hc => cv _ (h.2 c hc)⟩

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {Cs : Set U64}

theorem HeapOK.drop {D : U64 → Prop} (hH : HeapOK H) : HeapOK (H.drop D) := by
  refine ⟨fun p k h => hH.align p k (Heap.drop_eq_some.1 h).2, fun p k h => hH.fits p k (Heap.drop_eq_some.1 h).2,
    fun p k h => hH.lt64 p k (Heap.drop_eq_some.1 h).2, fun p z h => hH.scmin p z (Heap.drop_eq_some.1 h).2,
    fun p k q k' h1 h2 hne => hH.disj p k q k' (Heap.drop_eq_some.1 h1).2 (Heap.drop_eq_some.1 h2).2 hne⟩

theorem DeadQ.heq {H1 H2 : Heap} {s : S} {q : U64} (e : H2 q = H1 q) (h : DeadQ st H1 s q) : DeadQ st H2 s q := by
  unfold DeadQ at *; rw [e]; exact h

/-- **The creation's writes over the dropped heap** (no new TCBs): `BlkOK` and
the frames off the debug lists. -/
theorem retype_writes {lo hi A k w n : Nat} {s s' : S} {Ac : Set U64} (hn1 : n ≠ 1)
    (hb : BlkOK st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits Ac s)
    (P : DropOK st H (RegionD H lo hi) Cs s) (hnode : RegionOffNodes st Cs s lo hi)
    (hw : WritesIn st s s' (fun b => CapW (Heap.tcbs H) (Heap.omega H) (Heap.frame H) b ∨ (lo ≤ b.val ∧ b.val < hi) ∨
      DbgW st (Heap.tcbs H) Cs s b))
    (hdbg : DbgLinksOK st H Cs s' lo hi A k w n) :
    BlkOK st (H.drop (RegionD H lo hi)).tcbs Cs (H.drop (RegionD H lo hi)).omega (H.drop (RegionD H lo hi))
      (H.drop (RegionD H lo hi)).frame (H.drop (RegionD H lo hi)).replies (H.drop (RegionD H lo hi)).scs
      (H.drop (RegionD H lo hi)).ntfns (H.drop (RegionD H lo hi)).scBits Ac s' ∧
    AgreeD st (H.drop (RegionD H lo hi)).tcbs Cs (H.drop (RegionD H lo hi)) (H.drop (RegionD H lo hi)).frame s s' := by
  have hb1 := hb.drop P
  have hB : ∀ b, (Aligned b ∧ (CapW (Heap.tcbs H) (Heap.omega H) (Heap.frame H) b ∨ (lo ≤ b.val ∧ b.val < hi) ∨
      DbgW st (Heap.tcbs H) Cs s b)) → _ := fun b hb' => retype_write_cls P hnode hb'.1 hb'.2
  exact ⟨blk_of_writesD hb1 hw.al hB (hdbg.tz P hn1), agreeD_of_writes hb1 hw.al hB⟩

/-- **The new objects' placement** (no zero words), from the window. -/
theorem addOKP_window {lo hi A k w n us : Nat} {s s' : S} {kd : HKind} (hkd : newKind n us = some kd)
    (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hbits : ∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ k)
    (hnode : RegionOffNodes st Cs s lo hi) (hwp : WinPlaced A k w n us)
    (hks : L.ksb s' = L.ksb s) :
    AddOKP st (H.drop (RegionD H lo hi)) (NewAt A k w) kd Cs s' := by
  have hb := hbits kd hkd
  obtain ⟨hal, hfit, hA0, -⟩ := hwp
  obtain ⟨hA, hk⟩ := hal kd hkd
  have hp1 : 1 ≤ 2 ^ kd.bits := Nat.one_le_two_pow
  have pos : ∀ {q : U64}, NewAt A k w q → ∃ j, j < w ∧ q.val = A + j * k ∧ (j + 1) * k ≤ w * k := by
    rintro q ⟨j, hj, hq⟩; exact ⟨j, hj, hq, Nat.mul_le_mul_right _ hj⟩
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hks]
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq p kp hp => ?_,
    fun q q' hq hq' hne => ?_, fun q hq c hc => ?_, fun q hq => ?_⟩
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

/-- **The new objects' placement and zero words**, from the window (a
tracked kind). -/
theorem addOK_window {lo hi A k w n us : Nat} {s s' : S} {kd : HKind} (hkd : newKind n us = some kd) (hn1 : n ≠ 1)
    (hno : ∀ z, kd ≠ .other z)
    (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hbits : ∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ k)
    (hnode : RegionOffNodes st Cs s lo hi) (hwin : WinInit st s' lo hi A k w n us) (hwp : WinPlaced A k w n us)
    (hks : L.ksb s' = L.ksb s) :
    AddOK st (H.drop (RegionD H lo hi)) (NewAt A k w) kd Cs s' := by
  refine ⟨addOKP_window hkd hlo hhi hbits hnode hwp hks, fun q hq b ha h1 h2 => ?_⟩
  obtain ⟨j, hj, hv⟩ := hq
  have hjk : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at hjk
  have hb := hbits kd hkd
  rcases hwin (by rw [hkd]; rfl) (fun z e => hno z (by rw [hkd] at e; cases e; rfl)) b ha (by omega) (by omega)
    with h | ⟨h, -⟩
  · exact h
  · exact absurd h hn1

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- The heap after a retype: the dropped heap with the new objects. -/
noncomputable def retypeHeap (H : Heap) (lo hi A k w n us : Nat) : Heap := fun q => by
  classical exact if NewAt A k w q ∧ (newKind n us).isSome then newKind n us else H.drop (RegionD H lo hi) q

theorem retypeHeap_some {H : Heap} {lo hi A k w n us : Nat} {kd : HKind} (hkd : newKind n us = some kd) :
    retypeHeap H lo hi A k w n us = (H.drop (RegionD H lo hi)).add (NewAt A k w) kd := by
  funext q; unfold retypeHeap Heap.add
  by_cases hq : NewAt A k w q <;> simp [hq, hkd]

theorem retypeHeap_none {H : Heap} {lo hi A k w n us : Nat} (hkd : newKind n us = none) :
    retypeHeap H lo hi A k w n us = H.drop (RegionD H lo hi) := by
  funext q; unfold retypeHeap
  by_cases hq : NewAt A k w q <;> simp [hq, hkd]

/-- The TCB family (`n = 1`), done apart (`retypeFams`, QueueRetypeTcb). -/
structure RetypeFams (st : machine.Store S) [L : LawfulStore st] : Prop where
  tcb : ∀ (s s' : S) (H : Heap) (Cs Ac : Set U64) (lo hi A k w us : Nat), RetypeP1Step st s s' H Cs Ac lo hi A k w 1 us

theorem newKind_cases {n us : Nat} (h1 : n ≠ 1) :
    newKind n us = none ∨ newKind n us = some .ep ∨ newKind n us = some .ntfn ∨ newKind n us = some .reply ∨
      (∃ z, newKind n us = some (.other z) ∧ 5 ≤ z) ∨ (n = 5 ∧ newKind n us = some (.sc us)) := by
  unfold newKind
  simp only [h1, if_false]
  split_ifs <;> simp_all

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem DeadQ.of_none {H : Heap} {s : S} {q : U64} (h : H q = none) : DeadQ st H s q := by
  unfold DeadQ; rw [h]
  exact ⟨(fun e => by cases e), (fun e => by cases e), (fun e => by cases e), (fun e => by cases e),
    (fun z e => by cases e)⟩

set_option maxHeartbeats 8000000 in
/-- **`RetypeP1Step` for the families with no new TCB**: endpoints,
notifications, replies, CNodes and SCs (zero forms; the new SCs leave the
active set), and the kinds with no heap object. -/
theorem retypeP1Step_base {s s' : S} {H : Heap} {Cs Ac : Set U64} {lo hi A k w n us : Nat}
    (hn : n ≠ 1) : RetypeP1Step st s s' H Cs Ac lo hi A k w n us := by
  classical
  intro hb hlo hhi hbits P hnode hw hwin hdbg hwp h0Cs
  obtain ⟨hb1, G⟩ := retype_writes hn hb P hnode hw hdbg
  have hus7 : ∀ z, newKind n us = some (.sc z) → 7 ≤ z := fun z hz => by
    rcases newKind_cases (us := us) hn with h | h | h | h | ⟨z', h, -⟩ | ⟨h5, h⟩ <;> rw [h] at hz <;> cases hz
    exact hwp.2.2.2 h5
  have hH1 : HeapOK (H.drop (RegionD H lo hi)) := P.heap.drop
  have hB : ∃ Ac', BlkOK st (retypeHeap H lo hi A k w n us).tcbs Cs (retypeHeap H lo hi A k w n us).omega
      (retypeHeap H lo hi A k w n us) (retypeHeap H lo hi A k w n us).frame (retypeHeap H lo hi A k w n us).replies
      (retypeHeap H lo hi A k w n us).scs (retypeHeap H lo hi A k w n us).ntfns
      (retypeHeap H lo hi A k w n us).scBits Ac' s' := by
    rcases newKind_cases hn with hk | hk | hk | hk | ⟨z, hk, -⟩ | ⟨h5, hk⟩
    · rw [retypeHeap_none hk]; exact ⟨_, hb1⟩
    · rw [retypeHeap_some hk]
      exact ⟨_, BlkOK.addEp (addOK_window hk hn (by simp) hlo hhi hbits hnode hwin hwp G.ksb) hH1 hb1⟩
    · rw [retypeHeap_some hk]
      exact ⟨_, BlkOK.addNtfn (addOK_window hk hn (by simp) hlo hhi hbits hnode hwin hwp G.ksb) hH1 hb1⟩
    · rw [retypeHeap_some hk]
      exact ⟨_, BlkOK.addReply (addOK_window hk hn (by simp) hlo hhi hbits hnode hwin hwp G.ksb) hH1 hb1⟩
    · rw [retypeHeap_some hk]
      exact ⟨_, BlkOK.addOther (addOKP_window hk hlo hhi hbits hnode hwp G.ksb) hH1 hb1⟩
    · rw [retypeHeap_some hk]
      exact ⟨_, BlkOK.addSc (addOK_window hk hn (by simp) hlo hhi hbits hnode hwin hwp G.ksb) hH1 (hus7 us hk) h0Cs hb1⟩
  have heq : ∀ q, retypeHeap H lo hi A k w n us q =
      if NewAt A k w q ∧ (newKind n us).isSome then newKind n us else H.drop (RegionD H lo hi) q := fun q => by
    unfold retypeHeap; rfl
  have inR : ∀ q, NewAt A k w q → (newKind n us).isSome → lo ≤ q.val ∧ q.val + 8 ≤ hi := by
    rintro q ⟨j, hj, hq⟩ hs
    obtain ⟨kd, hkd⟩ := Option.isSome_iff_exists.1 hs
    have := hbits kd hkd
    have h8 : 8 ≤ 2 ^ kd.bits := by
      rcases newKind_cases hn with h | h | h | h | ⟨z, h, hz⟩ | ⟨-, h⟩ <;> rw [h] at hkd <;> cases hkd <;> simp [HKind.bits]
      · exact le_trans (by decide) (Nat.pow_le_pow_right (by decide) (by omega : 3 ≤ z))
      · exact le_trans (by decide) (Nat.pow_le_pow_right (by decide) (by have := hus7 us h; omega : 3 ≤ us))
    have : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have notNew : ∀ q kd, H q = some kd → ¬ MeetsR lo hi q.val (q.val + 2 ^ kd.bits) →
      ¬ (NewAt A k w q ∧ (newKind n us).isSome) := fun q kd hq hm ⟨hN, hs⟩ => by
    have := inR q hN hs; apply hm; unfold MeetsR; have := Nat.one_le_two_pow (n := kd.bits); omega
  have rD : ∀ q kd, H q = some kd → (RegionD H lo hi q ↔ MeetsR lo hi q.val (q.val + 2 ^ kd.bits)) :=
    fun q kd hq => by simp only [RegionD, hq, Option.elim]
  obtain ⟨Ac', hB⟩ := hB
  refine ⟨retypeHeap H lo hi A k w n us, Ac', hB, fun q kd hq hm => ?_, fun q kd hq => ?_,
    fun q hq kd hk => ?_, fun q he hd => ?_⟩
  · rw [heq, if_neg (notNew q kd hq hm), Heap.drop_of_not (fun h => hm ((rD q kd hq).1 h)), hq]
  · rw [heq] at hq
    by_cases hc : NewAt A k w q ∧ (newKind n us).isSome
    · rw [if_pos hc] at hq; exact Or.inr ⟨hc.1, hq⟩
    · rw [if_neg hc] at hq
      obtain ⟨hD, hq'⟩ := Heap.drop_eq_some.1 hq
      exact Or.inl ⟨hq', fun h => hD ((rD q kd hq').2 h)⟩
  · rw [heq, if_pos (show NewAt A k w q ∧ (newKind n us).isSome from ⟨hq, by rw [hk]; rfl⟩), hk]
  · by_cases hnone : H q = none
    · exact DeadQ.of_none (he.trans hnone)
    by_cases hc : NewAt A k w q ∧ (newKind n us).isSome
    · obtain ⟨kd, hkd⟩ := Option.isSome_iff_exists.1 hc.2
      have hq' : retypeHeap H lo hi A k w n us q = some kd := by rw [heq, if_pos hc, hkd]
      by_cases ho : ∃ z, kd = .other z
      · obtain ⟨z, rfl⟩ := ho
        unfold DeadQ; rw [hq']
        exact ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h), (fun h => by cases h),
          (fun z h => by cases h)⟩
      have Aw := addOK_window (H := H) hkd hn (fun z e => ho ⟨z, e⟩) hlo hhi hbits hnode hwin hwp G.ksb
      have z := Aw.zero q hc.1
      have al := Aw.align q hc.1
      have fi := Aw.fits q hc.1
      have hkk : kd = .ep ∨ kd = .ntfn ∨ kd = .reply ∨ (kd = .sc us ∧ 7 ≤ us) := by
        rcases newKind_cases hn with h | h | h | h | ⟨z', h, -⟩ | ⟨-, h⟩ <;> rw [h] at hkd <;> cases hkd <;> simp
        · exact absurd ⟨z', rfl⟩ ho
        · exact hus7 us h
      have zw : ∀ o : U64, o.val < 2 ^ kd.bits → o.val % 8 = 0 →
          L.mem s' (core.num.U64.wrapping_add q o) = 0#u64 := fun o ho h8 => by
        have h16 : 8 ∣ 2 ^ kd.bits := by
          rcases hkk with rfl | rfl | rfl | ⟨rfl, h7⟩
          any_goals decide
          · exact Nat.pow_dvd_pow 2 (by omega : 3 ≤ us)
        have hq8 : q.val % 8 = 0 := by have := Nat.mod_mod_of_dvd q.val h16; omega
        have hv : (core.num.U64.wrapping_add q o).val = q.val + o.val := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        exact z _ (by unfold Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)
      unfold DeadQ
      rw [hq']
      rcases hkk with rfl | rfl | rfl | ⟨rfl, h7⟩
      · refine ⟨(fun h => by cases h), (fun _ => ?_), (fun h => by cases h), (fun h => by cases h), (fun z h => by cases h)⟩
        unfold LawfulStore.epState epTSA
        rw [zw _ (by simp [layout.ep.TAIL_STATE, HKind.bits]) (by simp [layout.ep.TAIL_STATE])]; rfl
      · refine ⟨(fun h => by cases h), (fun h => by cases h), (fun _ => ⟨?_, ?_, ?_⟩), (fun h => by cases h),
          (fun z h => by cases h)⟩
        · unfold LawfulStore.epState epTSA
          rw [zw _ (by simp [layout.ep.TAIL_STATE, HKind.bits]) (by simp [layout.ep.TAIL_STATE])]; decide
        · unfold ntfnBtA; exact zw _ (by simp [layout.ntfn.BOUND_TCB, HKind.bits]) (by simp [layout.ntfn.BOUND_TCB])
        · unfold ntfnScA; exact zw _ (by simp [layout.ntfn.SC, HKind.bits]) (by simp [layout.ntfn.SC])
      · refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h), (fun _ => ?_), (fun z h => by cases h)⟩
        unfold rTcbA; exact zw _ (by simp [layout.reply.TCB, HKind.bits]) (by simp [layout.reply.TCB])
      · have h128 : 128 ≤ 2 ^ (HKind.sc us).bits := le_trans (by decide) (Nat.pow_le_pow_right (by decide) h7)
        refine ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h), (fun h => by cases h),
          (fun z' _ => ⟨?_, ?_, ?_⟩)⟩
        · unfold scTcbA; exact zw _ (lt_of_lt_of_le (by simp [layout.sc.TCB]) h128) (by simp [layout.sc.TCB])
        · unfold scReplyA; exact zw _ (lt_of_lt_of_le (by simp [layout.sc.REPLY]) h128) (by simp [layout.sc.REPLY])
        · unfold scNtfnA; exact zw _ (lt_of_lt_of_le (by simp [layout.sc.NTFN]) h128) (by simp [layout.sc.NTFN])
    · have h1 : retypeHeap H lo hi A k w n us q = H.drop (RegionD H lo hi) q := by rw [heq, if_neg hc]
      have h2 : H.drop (RegionD H lo hi) q = H q := h1.symm.trans he
      have hd1 : DeadQ st (H.drop (RegionD H lo hi)) s q := DeadQ.heq h2 hd
      obtain ⟨kq, hkq⟩ := Option.ne_none_iff_exists'.1 hnone
      have hq1 : H.drop (RegionD H lo hi) q = some kq := h2.trans hkq
      have hb0 := hb.drop P
      have hO := hb0.2.2.1.1
      have hcur := hb0.1.choose_spec.choose_spec.cur
      refine DeadQ.heq h1 (hd1.keepw (fun hq => ⟨?_, ?_, ?_⟩) ?_ ?_ (fun hq => ?_) (fun hq => ?_) (fun hq => ?_)
        (fun z hq => ?_))
      · rw [stA_eq]; exact G.fld q hq _ (by simp) (by simp) (by simp) (by simp) (by simp)
      · rw [scA_eq]; exact G.fld q hq _ (by simp) (by simp) (by simp) (by simp) (by simp)
      · unfold boundA; exact G.fld q hq _ (by simp) (by simp) (by simp) (by simp) (by simp)
      · unfold LawfulStore.actionW; exact G.cur hcur (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
      · unfold LawfulStore.idleW; exact G.cur hcur (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)
      · unfold LawfulStore.epState; rw [(G.epw q hq).2]
      · exact ⟨G.sig _ (hO.ntB q hq).2, G.sig _ (hO.ntW q hq)⟩
      · exact G.sig _ (hO.tcbW hq)
      · exact ⟨G.sig _ (hO.fixW q ⟨z, hq⟩).1, G.sig _ (hO.repW q ⟨z, hq⟩), G.sig _ (hO.snW q ⟨z, hq⟩)⟩



/-- **`RetypeP1Step` for every kind**, from the TCB family (`RetypeFams`;
`retypeP1Step` in QueueRetypeTcb discharges it). -/
theorem retypeP1Step_of (F : RetypeFams st) {s s' : S} {H : Heap} {Cs Ac : Set U64} {lo hi A k w n us : Nat} :
    RetypeP1Step st s s' H Cs Ac lo hi A k w n us := by
  by_cases h1 : n = 1
  · subst h1; exact F.tcb s s' H Cs Ac lo hi A k w us
  exact retypeP1Step_base h1

end

end Fl4Proofs.P1

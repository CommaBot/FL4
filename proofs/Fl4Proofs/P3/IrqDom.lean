/-
P3 (DESIGN.md §9), interrupts: **the IRQ handler decode keeps the domain
schedule's words** (`DK4`, DomKeep), for its `DomFrame`.

* `empty_frame_of_links`, `DK4.of_foot` (P1's `Foot` with `KW` apart,
  `KWApart`), `delete_one_dk4`: the deletion of a null or notification cap
  (P1's `fin_cap_ntfn.slots`, `empty_slot_frame`).
* `irq_handler_dk4`: `decode_irq_handler` at every label. `Ack` restarts the
  caller (`sts_dk4`) and masks; `Set`/`Clear` also delete the IRQ slot's cap
  (`delete_one_dk4`: P1's footprint of a notification's finalisation, from
  P1's invariant at the restarted state, `IrqDelP1`) and `Set` inserts the
  new cap (`insert_frame`); the other paths fail with the state unchanged.
-/
import Fl4Proofs.P3.DomKeep
import Fl4Proofs.P3.EmptyFrame
import Fl4Proofs.P3.DelOne
import Fl4Proofs.P3.MdbRename
import Fl4Proofs.P3.Delete
import Fl4Proofs.P1.QueueFinCap
import Fl4Proofs.P3.IrqDecode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {th : TypedHeap} {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {ar : machine.Arch A}

/-! ## `cdt::empty_slot` and `cdt::delete_one` -/

/-- `empty_slot` of a slot of the MDB (any cap; nothing for the null cap). -/
theorem empty_frame_of_links (hP : Placed th) (s : S) (a : A) {G : MdbGhost} (hM : MdbLinks th (L.mem s) G)
    {xs : U64} (hx : IsSlot th xs) :
    cdt.empty_slot st ar s a xs .Null ⦃ r => SlotFrame (L := L) th s r.1 ⦄ := by
  by_cases hcn : capV (L.mem s) xs = .Null
  · rw [empty_slot_null (arI := ar) s a xs (by rw [capAt_capV, hcn]) _, WP.spec_ok]
    exact SlotFrame.refl s
  have hxm : xs ∈ G.chains.flatten := (hM.members _).2 ⟨hx, _, capAt_capV _ _, hcn⟩
  have hslot : ∀ y ∈ G.chains.flatten, IsSlot th y := fun y hy => ((hM.members y).1 hy).1
  refine empty_slot_frame hP s a xs hx _ (capAt_capV _ _) hcn ?_ ?_
  · by_cases h0 : prevOf (L.mem s) xs = 0#u64
    · exact Or.inl h0
    · exact Or.inr (hslot _ (hM.prev_link hxm h0).1)
  · rcases hM.next_mem hxm with h | ⟨h1, -⟩
    · exact Or.inl h
    · exact Or.inr (hslot _ h1)

end

/-! ## P1's footprints -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- P1's `KW`'s aligned words apart from the first 256 bytes of the
kernel-global area (as TcbHypsX's `KWDom`; P1's `KWLow`). -/
def KWApart (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64) (s : S) : Prop :=
  ∀ b, P1.Aligned b → P1.KW st T Cs Sg Scs Z Es s b → b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ b.val

/-- **A P1 `Foot` step keeps the domain schedule's words.** -/
theorem DK4.of_foot {T Cs Sg Scs Es : Set U64} {Z : U64 → Nat} {s s' : S}
    (hf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (ha : (L.ksb s).val % 8 = 0)
    (hK : KWApart (L := L) T Cs Sg Scs Z Es s) (h : P1.Foot st T Cs Sg Scs Z Es s s') : DK4 (L := L) s s' := by
  have hal : ∀ o ∈ domOffs0, P1.Aligned (core.num.U64.wrapping_add (L.ksb s) o) := fun o ho => by
    have hv := dw_val hf ho
    have := domOffs0_lt ho
    unfold P1.Aligned; rw [hv]; omega
  refine ⟨h.1, fun o ho => h.mem_eq (hal o ho) fun hk => ?_⟩
  have hv := dw_val hf ho
  have := (domOffs0_lt ho).1
  rcases hK _ (hal o ho) hk with e | e <;> rw [hv] at e <;> omega

end

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] (arI : machine.Arch A)

/-- **`cdt::delete_one` of a null or notification cap keeps the domain
schedule's words**: the finalisation by P1's `fin_cap_ntfn.slots` (a `Foot`,
from P1's invariant over sets whose `KW` lies apart, `KWApart`), the
emptying by `empty_frame_of_links` (the MDB from `FinObjHyp`'s `DState`). -/
theorem delete_one_dk4 (th : TypedHeap) (hP : Placed th) (hO : FinObjHyp (L := L) arI th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) (hD : KsbOK (L := L) th s)
    (hk : capV (L.mem s) (cslotAddr sl) = .Null ∨
      ∃ p b w r, capV (L.mem s) (cslotAddr sl) = .Notification p b w r)
    (hP1 : ∀ p b w r, capV (L.mem s) (cslotAddr sl) = .Notification p b w r →
      ∃ (T Cs Ω : Set U64) (H : P1.Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64),
        P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧ p ∈ Nt ∧ H p = some .ntfn ∧
        KWApart (L := L) T Cs Sg Scs Z (P1.EH H) s) :
    cdt.delete_one st arI s a (cslotAddr sl) ⦃ r => DK4 (L := L) s r.1 ⦄ := by
  unfold cdt.delete_one
  rw [slot_cap_eq, capAt_capV]
  simp only [bind_ok, cap_is_null_eq]
  rcases hk with hk | ⟨p, b, w, r, hk⟩
  · rw [hk]; simp only [isNullB, ↓reduceIte, WP.spec_ok]; exact DK4.refl s
  rw [hk]
  have hcn : capability.Cap.Notification p b w r ≠ .Null := by simp
  simp only [isNullB_false hcn, Bool.false_eq_true, ↓reduceIte]
  have hc : capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r) := by rw [capAt_capV, hk]
  obtain ⟨bf, hbf, hbf2, -⟩ := finalHyp_full th hP s σ G sl _ hDS hA hc hcn
  rw [hbf2 (Or.inl ⟨trivial, rfl⟩)] at hbf
  rw [is_final_with_cap_eq _ _ _ hc, hbf]; simp only [bind_ok]
  obtain ⟨T, Cs, Ω, H, Sg, Rp, Scs, Nt, Z, Ac, hB, hpN, hH, hKW⟩ := hP1 p b w r hk
  rw [← finalise_cap_ntfn arI s a p b w r _ false]
  have hO' := hO s a σ G sl _ hDS hA hc trivial
  refine WP.spec_bind (WP.spec_and (P1.fin_cap_ntfn.slots (ar := arI) s a p b w r _ false hB hpN hH) hO') ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨-, -, hfoot, -⟩, hO1⟩
  simp only [uncurry_apply_pair]
  obtain ⟨-, -, -, σ1, G1, -, hDS1, -, -, -⟩ := hO1
  have h1 : DK4 (L := L) s s1 := DK4.of_foot hD.fits hD.align hKW hfoot
  have hD1 : KsbOK (L := L) th s1 := hD.same hfoot.1
  exact WP.spec_mono (empty_frame_of_links (ar := arI) hP s1 a1 hDS1.1.2.2.1 hA.isSlot) fun r hr =>
    h1.trans (DK4.of_slotFrame hD1 hr)

end




section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **P1's invariant for deleting IRQ `irq`'s handler cap** (for the P1
side): at the caller's restart, a notification cap in the IRQ slot names a
notification of P1's sets, which satisfy `BlkOK` with `KW` apart from the
domain schedule. -/
def IrqDelP1 (s : S) (ct irq : U64) : Prop :=
  ∀ s2, sched.set_thread_state st s ct sched.TS_RESTART = ok s2 →
    ∀ p b w r, capV (L.mem s2) (nodeA (L.ksb s) irq) = .Notification p b w r →
      ∃ (T Cs Ω : Set U64) (H : P1.Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64),
        P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧ p ∈ Nt ∧ H p = some .ntfn ∧
        KWApart (L := L) T Cs Sg Scs Z (P1.EH H) s2

/-- The restart of the caller, with the relation and `DState` carried. -/
theorem restart_dk4 (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hDS : DState (L := L) th s σ G) (ct : U64) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (hD : DomPlaced (L := L) th s) :
    ∃ s2, sched.set_thread_state st s ct sched.TS_RESTART = ok s2 ∧ DK4 (L := L) s s2 ∧
      L.ksb s2 = L.ksb s ∧ L.cpu s2 = L.cpu s ∧ SlotsSame th (L.mem s) (L.mem s2) ∧
      ∃ σ1, DState (L := L) th s2 σ1 G := by
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hDl, hFI⟩ := hDS
  have hts := WP.spec_and (WP.spec_and (set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact)
    (sts_dk4 hP hD htcb sched.TS_RESTART)) (set_thread_state_cases s ct sched.TS_RESTART)
  obtain ⟨s2, hs2, ⟨hS, hdk⟩, hcs⟩ := spec_exists hts
  have hcpu : L.cpu s2 = L.cpu s := by rcases hcs with rfl | rfl <;> simp
  obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
  rw [← hcur] at hk
  obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, -, -⟩ := restart_rel hR hV hM hC hS hk .restart
  exact ⟨s2, hs2, hdk, hdk.1, hcpu, hS, σ1, ⟨hR1, hV1, hM1, hC1, MdbInv.of_same hM hI hS⟩, hDl.of_same hS,
    hFI.of_same hM hS (ksub_of_eq (setThreadState_nks _ _) hst)⟩

/-- **`decode_irq_handler` keeps the domain schedule's words**, every label. -/
theorem irq_handler_dk4 (th : TypedHeap) (hP : Placed th)
    (hO : FinObjHyp (L := L) arI th) (hPD : PostDelHyp (L := L) arI th) (hK : NtfnKeepHyp (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hL : IntLayout th (L.ksb s)) (lbl : U64)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (irq : U64) (hirq : irq.val < 128) (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : lbl.val = 35 → ExtraSRel th (L.mem s) x0 cps) (hxn : lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq)
    (hD : DomPlaced (L := L) th s) (hP1 : IrqDelP1 (L := L) s ct irq) :
    interrupt.decode_irq_handler st arI s ar lbl irq extra ⦃ res => DK4 (L := L) s res.2.1 ⦄ := by
  obtain ⟨s2, hs2, hdk2, hkb2, hcpu2, hS2, σ1, hDS1⟩ := restart_dk4 th hP s σ G hDS ct hcur htcb hact hD
  have hA : AbsSlot th ((nodeA (L.ksb s) irq).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node irq hirq)⟩
  have hns : IsSlot th (nodeA (L.ksb s) irq) := by have := hA.isSlot; rwa [cslotAddr_nil] at this
  have hok2 : IrqSlotOK (L.mem s2) (nodeA (L.ksb s) irq) := by unfold IrqSlotOK; rw [hS2.capV hns]; exact hok
  have hD2 : KsbOK (L := L) th s2 := hD.toK.same hkb2
  -- the deletion of the IRQ slot's cap, from the restarted state
  have hdel : ∀ a2 : A, cdt.delete_one st arI s2 a2 (nodeA (L.ksb s) irq) ⦃ r =>
      DK4 (L := L) s r.1 ∧ ∃ σ' G', DState (L := L) th r.1 σ' G' ∧
        ∀ y, IsSlot th y → y ≠ nodeA (L.ksb s) irq → capV (L.mem r.1) y = capV (L.mem s2) y ⦄ := by
    intro a2
    have hok3 : capV (L.mem s2) (cslotAddr ((nodeA (L.ksb s) irq).bv, [])) = .Null ∨
        ∃ p b w r, capV (L.mem s2) (cslotAddr ((nodeA (L.ksb s) irq).bv, [])) = .Notification p b w r := by
      have h := hok2; unfold IrqSlotOK at h; simpa only [cslotAddr_nil] using h
    have h1 := delete_one_dk4 arI th hP hO s2 a2 σ1 G hDS1 hA hD2 hok3
      (fun p b w r e => hP1 s2 hs2 p b w r (by simpa only [cslotAddr_nil] using e))
    have h2 := delete_one_keep arI th hP (finalHyp_full th hP) hO hPD hK s2 a2 σ1 G hDS1 hA hok3
    rw [cslotAddr_nil] at h1 h2
    refine WP.spec_mono (WP.spec_and h1 h2) ?_
    rintro r ⟨hr1, ⟨σ', G', -, hDS', -⟩, -, hoth⟩
    exact ⟨hdk2.trans hr1, σ', G', hDS', hoth⟩
  unfold interrupt.decode_irq_handler
  rw [hct]; simp only [bind_ok]
  by_cases h34 : lbl = fl4_abi.label.IRQAckIRQ
  · simp only [h34, ↓reduceIte, hs2, bind_ok]
    obtain ⟨a', ha'⟩ := hmask ar irq false
    rw [ha']; simp only [bind_ok, WP.spec_ok]
    exact hdk2
  simp only [h34, ↓reduceIte]
  by_cases h35 : lbl = fl4_abi.label.IRQSetIRQHandler
  · have h35v : lbl.val = 35 := by subst h35; simp [fl4_abi.label.IRQSetIRQHandler]
    simp only [h35, ↓reduceIte, hx0, is_null_eq]
    rcases hex h35v with ⟨rfl, -⟩ | ⟨hx0n, ps, rs, idxs, rest, hps, hls, hxe, -⟩
    · simp only [decide_true, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
      exact DK4.refl s
    simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, capAt_capV, bind_ok]
    generalize hcx : capV (L.mem s) x0 = c
    by_cases hgood : ∃ p b r, c = .Notification p b true r
    · obtain ⟨p, b, r, rfl⟩ := hgood
      simp only [↓reduceIte, hs2, bind_ok, irq_slot_eq, hkb2]
      refine WP.spec_bind (hdel ar) ?_
      rintro ⟨s3, a3⟩ ⟨hdk3, σ2, G2, hDS3, hoth⟩
      simp only [uncurry_apply_pair]
      have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
      have hxs : IsSlot th x0 := by rw [hxe]; exact hAs.isSlot
      have hsrc3 : capAt (L.mem s3) x0 = ok (.Notification p b true r) := by
        rw [capAt_capV, hoth x0 hxs (hxn h35v), hS2.capV hxs, hcx]
      have hM3 := hDS3.1.2.2.1
      have hnx : nextOf (L.mem s3) x0 = 0#u64 ∨ IsSlot th (nextOf (L.mem s3) x0) := by
        have hsm : x0 ∈ G2.chains.flatten := (hM3.members _).2 ⟨hxs, _, hsrc3, by simp⟩
        rcases hM3.next_mem hsm with h | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr ((hM3.members _).1 h).1
      have hD3 : KsbOK (L := L) th s3 := hD.toK.same hdk3.1
      refine WP.spec_bind (insert_frame hP s3 (.Notification p b true r) x0 _ hxs hns _ hsrc3 hnx) fun s4 h4 => ?_
      exact (WP.spec_ok _).2 (hdk3.trans (DK4.of_slotFrame hD3 h4))
    · cases c <;> simp only [error.invalid_cap, bind_ok, WP.spec_ok]
      all_goals first
        | exact DK4.refl s
        | (rename_i p b w r
           cases w
           · simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
             exact DK4.refl s
           · exact absurd ⟨p, b, r, rfl⟩ hgood)
  simp only [h35, ↓reduceIte]
  by_cases h36 : lbl = fl4_abi.label.IRQClearIRQHandler
  · simp only [h36, ↓reduceIte, hs2, bind_ok, irq_slot_eq, hkb2]
    refine WP.spec_bind (hdel ar) ?_
    rintro ⟨s3, a3⟩ ⟨hdk3, -⟩
    exact (WP.spec_ok _).2 hdk3
  simp only [h36, ↓reduceIte, error.illegal, bind_ok, WP.spec_ok]
  exact DK4.refl s

end

end

end Fl4Proofs.P3

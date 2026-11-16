/-
P3: **retype's post to P1's `RetypeP1Step`** — the bridge.

* `slotSpan_wd`: an aligned word within a slot is one of its four words.
* `retFrame_writesIn`: `RetFrame`'s creation frame is P1's write frame
  (`CapW`, the window, `DbgW`), given the typed heap's slots as `CapW`
  words (`SlotCapW`), the debug-list head word a node's and the old head a
  TCB.
* `creation_step`: P1's `RetypeP1Step` applied to the creation (from the
  reset's state, or the restart's), the window `[A, A + win * k)` its region.
* `JCovD.retype_post`: `JCovD` and `BlkOK` across a whole retype from
  `RetPostN` (the window's objects dead by `retype_window_dead`), given P1's
  restart and reset (`hstep`: `BlkOK` over a heap `H1` of `H`'s objects with
  the dead kept dead) and `RetypeP1Step`.
-/
import Fl4Proofs.P3.ScPlaceRet
import Fl4Proofs.P3.ScInstFoot
import Fl4Proofs.P3.UntypedPml4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **An aligned word within a slot is one of its four words.** -/
theorem slotSpan_wd {th : TypedHeap} (hP : Placed th) {b : U64} (hb : P1.Aligned b) (h : SlotSpan th b) :
    SlotWd th b := by
  obtain ⟨a, ha, h1, h2⟩ := h
  have hal := ha.align hP
  have hb8 : b.val % 8 = 0 := hb
  have hd : b.val - a.val = 0 ∨ b.val - a.val = 8 ∨ b.val - a.val = 16 ∨ b.val - a.val = 24 := by omega
  have mk : ∀ k : U64, Off k → k.val = b.val - a.val → SlotWd th b := fun k hk hkv =>
    ⟨a, ha, k, hk, UScalar.eq_of_val_eq (by rw [slot_word_val hP ha hk]; omega)⟩
  rcases hd with e | e | e | e
  · exact mk 0#u64 (Or.inl rfl) (by rw [e]; rfl)
  · exact mk 8#u64 (Or.inr (Or.inl rfl)) (by rw [e]; rfl)
  · exact mk 16#u64 (Or.inr (Or.inr (Or.inl rfl))) (by rw [e]; rfl)
  · exact mk 24#u64 (Or.inr (Or.inr (Or.inr rfl))) (by rw [e]; rfl)

/-- **`RetFrame`'s creation frame is P1's write frame**: slot words are
`CapW` words (`SlotCapW`), the new TCBs' creation words and a PML4's window
lie in the window `[A, A + win * k)`, and the debug-list head word and the
old head's `debug_prev` word are `DbgW` words. -/
theorem retFrame_writesIn {thR : TypedHeap} {sR s' : S} {A k win : Nat} {DW h0 : U64} {T pml4 : Prop}
    {T1 Ω1 Sg1 Cs : Set U64}
    (hW : WFrame (L := L) sR s' (fun v => ((T ∧ TcbLoopW thR A win DW h0 v) ∨ SlotSpan thR v) ∨
      (pml4 ∧ A ≤ v.val ∧ v.val < A + win * k)))
    (hP : Placed thR) (hSC : SlotCapW thR T1 Ω1 Sg1)
    (hDW : ∃ c ∈ Cs, DW = L.nodeAt sR c layout.node.DEBUG_TCBS) (hh0 : h0 ≠ 0#u64 → h0 ∈ T1)
    (hk : T → k = 4096) (hfit : A + win * k ≤ 2 ^ 64) :
    WritesIn st sR s' (fun b => CapW T1 Ω1 Sg1 b ∨ (A ≤ b.val ∧ b.val < A + win * k) ∨ DbgW st T1 Cs sR b) := by
  refine ⟨hW.1, hW.2.1, fun b hb hn => hW.2.2 b hb (fun hF => hn ?_)⟩
  have hslot : SlotSpan thR b → CapW T1 Ω1 Sg1 b := fun h => hSC b (slotSpan_wd hP hb h)
  rcases hF with (⟨hT, hL⟩ | hs) | ⟨-, hw⟩
  · rcases hL with hs | ⟨j, hj, hI⟩ | e | ⟨hne, he⟩
    · exact Or.inl (hslot hs)
    · right; left
      have hk' := hk hT; subst hk'
      have hjv : (⟨BitVec.ofNat 64 (A + j * 4096)⟩ : U64).val = A + j * 4096 := by
        have : j * 4096 < win * 4096 := Nat.mul_lt_mul_of_pos_right hj (by omega)
        show (BitVec.ofNat 64 (A + j * 4096)).toNat = _; simp; omega
      obtain ⟨h1, h2, -⟩ := hI
      rw [hjv] at h1 h2
      have : (j + 1) * 4096 ≤ win * 4096 := Nat.mul_le_mul_right _ hj
      constructor <;> omega
    · obtain ⟨c, hc, e'⟩ := hDW
      exact Or.inr (Or.inr (Or.inr ⟨c, hc, e.trans e'⟩))
    · refine Or.inr (Or.inr (Or.inl ⟨h0, hh0 hne, Or.inr ?_⟩))
      apply UScalar.eq_of_val_eq
      unfold dpA
      rw [core.num.U64.wrapping_add_val_eq]
      simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
      have := b.hBounds; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits] at this
      omega
  · exact Or.inl (hslot hs)
  · exact Or.inr (Or.inl hw)

/-- A dead object of an absent address. -/
theorem DeadP.none {H : Heap} {s : S} {q : U64} (h : H q = none) : DeadP (L := L) H s q := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun z e => ?_⟩ <;> rw [h] at e <;> cases e

/-- **P1's `RetypeP1Step` on the creation** (module docstring). -/
theorem creation_step {sR s' : S} {H1 : Heap} {Cs Ac : Set U64} {thR : TypedHeap} {A k win n us : Nat}
    {T pml4 : Prop} (hCR : RetypeP1Step st sR s' H1 Cs Ac A (A + win * k) A k win n us)
    (hb : BlkOK st (Heap.tcbs H1) Cs (Heap.omega H1) H1 (Heap.frame H1) (Heap.replies H1) (Heap.scs H1)
      (Heap.ntfns H1) (Heap.scBits H1) Ac sR)
    (hbits : ∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ k)
    (hdrop : DropOK st H1 (RegionD H1 A (A + win * k)) Cs sR) (hnode : RegionOffNodes st Cs sR A (A + win * k))
    (hdbg : DbgLinksOK st H1 Cs s' A (A + win * k) A k win n)
    (hW : WFrame (L := L) sR s' (fun v => ((T ∧ TcbLoopW thR A win (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)
      (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan thR v) ∨
      (pml4 ∧ A ≤ v.val ∧ v.val < A + win * k)))
    (hP : Placed thR) (hSC : SlotCapW thR (Heap.tcbs H1) (Heap.omega H1) (Heap.frame H1)) (h0Cs : 0#u64 ∈ Cs)
    (hh0 : L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
      L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS) ∈ Heap.tcbs H1)
    (hk : T → k = 4096) (hfit : A + win * k ≤ 2 ^ 64)
    (hWZ : (newKind n us).isSome → WinZero (L.mem s') A k win (n = 1)) (hn1 : n = 1 → k = 4096) :
    ∃ (H' : Heap) (Ac' : Set U64),
      BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H') (Heap.ntfns H')
        (Heap.scBits H') Ac' s' ∧
      (∀ q kd, H1 q = some kd → ¬ MeetsR A (A + win * k) q.val (q.val + 2 ^ kd.bits) → H' q = some kd) ∧
      (∀ q kd, H' q = some kd → (H1 q = some kd ∧ ¬ MeetsR A (A + win * k) q.val (q.val + 2 ^ kd.bits)) ∨
        (NewAt A k win q ∧ newKind n us = some kd)) ∧
      (∀ q, NewAt A k win q → ∀ kd, newKind n us = some kd → H' q = some kd) ∧
      (∀ q, H' q = H1 q → DeadQ st H1 sR q → DeadQ st H' s' q) :=
  hCR hb le_rfl le_rfl hbits hdrop hnode (retFrame_writesIn hW hP hSC ⟨0#u64, h0Cs, rfl⟩ hh0 hk hfit)
    (fun hs => winInit_of_winZero (hWZ hs) hn1 hfit hs) hdbg

/-- **`JCovD` and `BlkOK` across a whole retype** (module docstring). -/
theorem JCovD.retype_post {th : TypedHeap} {H : Heap} {G : MdbGhost} {D Cs : Set U64} {s : S}
    {σ : Fl4Spec.State Unit} {A' : Type} {arI : machine.Arch A'} {ar : A'}
    {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {sl : Fl4Spec.CslotPtr} {rs : Bool} {pb rb : Fl4Spec.ObjRef}
    {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A'}
    (hJ : JCovD (L := L) th H G D Cs s) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    (hRP : RetPostN (L := L) th (L.mem s) G σ arI ar s bitsApi (L.ksb s) (.retype sl rs pb rb t us slots dev) res)
    (hok : res.1 = .Ok ())
    (hCR : ∀ (s1 s2 : S) (H1 : Heap) (Cs1 Ac1 : Set U64) (lo hi A k w n us : Nat),
      RetypeP1Step st s1 s2 H1 Cs1 Ac1 lo hi A k w n us)
    (n : Nat) (hnt : n = 1 ↔ t = .tcbObject) (hn1 : n = 1 → 2 ^ bitsApi t us = 4096)
    (hnK : (newKind n us).isSome → t ≠ .untyped ∧ t ≠ .archObject .pml4Obj ∧ dev = false)
    (hbits : ∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ 2 ^ bitsApi t us)
    (hfit : rb.toNat + slots.length * 2 ^ bitsApi t us ≤ 2 ^ 64)
    (hstep' : ∀ (ct : U64) (s0 sR : S) (thR : TypedHeap),
      sched.cur_thread st s = ok ct → sched.set_thread_state st s ct sched.TS_RESTART = ok s0 →
      ((sR = s0 ∧ thR = th) ∨ ∃ a1, untyped.reset_untyped st arI s0 ar (cslotAddr sl) = ok (.Ok (), sR, a1)) →
      (∀ a, IsSlot thR a → IsSlot th a) →
      ∃ (H1 : Heap) (Ac1 : Set U64), BlkOK st (Heap.tcbs H1) Cs (Heap.omega H1) H1 (Heap.frame H1) (Heap.replies H1)
          (Heap.scs H1) (Heap.ntfns H1) (Heap.scBits H1) Ac1 sR ∧
        Placed thR ∧ SlotCapW thR (Heap.tcbs H1) (Heap.omega H1) (Heap.frame H1) ∧ 0#u64 ∈ Cs ∧
        (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
          L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS) ∈ Heap.tcbs H1) ∧
        ¬ (rb.toNat ≤ (L.curW sR).val ∧ (L.curW sR).val < rb.toNat + slots.length * 2 ^ bitsApi t us) ∧
        DropOK st H1 (RegionD H1 rb.toNat (rb.toNat + slots.length * 2 ^ bitsApi t us)) Cs sR ∧
        RegionOffNodes st Cs sR rb.toNat (rb.toNat + slots.length * 2 ^ bitsApi t us) ∧
        DbgLinksOK st H1 Cs res.2.1 rb.toNat (rb.toNat + slots.length * 2 ^ bitsApi t us) rb.toNat
          (2 ^ bitsApi t us) slots.length n ∧
        (∀ q kd, H1 q = some kd → H q = some kd) ∧
        (∀ q, H1 q = H q → DeadP (L := L) H s q → DeadQ st H1 sR q)) :
    ∃ th' G' A k w dslot cj, RetExp th th' (L.mem s) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr sl) ∧
      ∃ (H' : Heap) (Ac' : Set U64),
        BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H')
          (Heap.ntfns H') (Heap.scBits H') Ac' res.2.1 ∧
        JCovD (L := L) th' H' G' {q | q ∈ D ∧ ¬ NewQ A k w cj q} Cs res.2.1 := by
  obtain ⟨-, -, -, -, -, G', th', -, -, -, -, -, -, -, -, -, -, -, hks, A, k, w, dslot, cj, hE,
    ⟨ct, s0, hct, hs0, hbr⟩, hut⟩ := hRP
  rcases hbr with ⟨e, -⟩ | ⟨-, ⟨eA, ek, ew, -⟩, sR, thR, lo, hi, hor', -, -, -, hsl, -, -, hW, hWZ, -⟩
  · rw [hok] at e; cases e
  have hor : (sR = s0 ∧ thR = th) ∨ ∃ a1, untyped.reset_untyped st arI s0 ar (cslotAddr sl) = ok (.Ok (), sR, a1) :=
    hor'.elim (fun ⟨a, b, _, _⟩ => Or.inl ⟨a, b⟩) (fun ⟨a1, _, _, _, _, h, _⟩ => Or.inr ⟨a1, h⟩)
  obtain ⟨H1, Ac1, hb1, hPR, hSC, h0Cs, hh0, -, hdrop, hnode, hdbg, hsub, hdk⟩ := hstep' ct s0 sR thR hct hs0 hor hsl
  subst eA ek ew
  have hwd := (retype_window_dead hJ hU hI hE).1
  have hnewQ : ∀ q, NewAt rb.toNat (2 ^ bitsApi t us) slots.length q → (newKind n us).isSome →
      NewQ rb.toNat (2 ^ bitsApi t us) slots.length cj q := by
    rintro q ⟨j, hj, hq⟩ hs
    refine ⟨j, hj, hq, ?_⟩
    cases hu : isUt (cj j)
    · rfl
    · exact absurd (hut hok j hj hu) (hnK hs).1
  obtain ⟨H', Ac', hb', -, hshape, -, hdead'⟩ := creation_step (hCR _ _ _ _ _ _ _ _ _ _ n us) hb1
    hbits hdrop hnode hdbg hW hPR hSC h0Cs hh0
    (fun hT => hn1 (hnt.2 hT)) hfit
    (fun hs w hw h1 h2 => ((hWZ ⟨(hnK hs).2.2, (hnK hs).2.1⟩) w hw h1 h2).imp id (fun ⟨hT, hj⟩ => ⟨hnt.2 hT, hj⟩))
    (fun h => hn1 h)
  refine ⟨th', G', _, _, _, dslot, cj, hE, H', Ac', hb', hJ.retype hE (fun q kd hq => ?_) (fun q hqD hnq e hd => ?_) hks⟩
  · rcases hshape q kd hq with ⟨h1, hm⟩ | ⟨hna, hk⟩
    · refine Or.inl ⟨hsub q kd h1, ?_⟩
      rintro ⟨j, hj, hv, -⟩
      apply hm
      unfold MeetsR
      have h1' : (j + 1) * 2 ^ bitsApi t us ≤ slots.length * 2 ^ bitsApi t us := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at h1'
      have := Nat.one_le_two_pow (n := kd.bits)
      have := Nat.one_le_two_pow (n := bitsApi t us)
      omega
    · exact Or.inr ⟨hnewQ q hna (by rw [hk]; rfl), hbits kd hk⟩
  · cases hHq : H q with
    | none => exact DeadP.none (e.trans hHq)
    | some kd =>
      have hq' : H' q = some kd := e.trans hHq
      rcases hshape q kd hq' with ⟨h1, -⟩ | ⟨hna, hk⟩
      · exact hdead' q (hq'.trans h1.symm) (hdk q (h1.trans hHq.symm) hd)
      · exact absurd (hnewQ q hna (by rw [hk]; rfl)) hnq

/-- **P1's `ResetP1Step` on a reset's outcome** (the reset equation that
`RetFrame` exposes): `BlkOK` over `H` with the untyped region's objects
dropped, the dead kept dead; the heap after has only `H`'s objects. -/
theorem reset_step {A' : Type} {arI : machine.Arch A'} (hRS : ResetP1Step st arI) {H : Heap} {Cs Ac : Set U64}
    {s0 : S} {ar : A'} {x p sb fi : U64} {dev : Bool}
    {r : core.result.Result Unit error.Exc × S × A'}
    (hb : BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac s0)
    (hcap : obj.Slot.cap st x s0 = ok (.Untyped p sb fi dev))
    (hx : CapSlotW (Heap.tcbs H) (Heap.omega H) (Heap.frame H) x)
    (hpal : p.val % 2 ^ sb.val = 0) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (hdrop : DropOK st H (RegionD H p.val (p.val + 2 ^ sb.val)) Cs s0)
    (hnode : RegionOffNodes st Cs s0 p.val (p.val + 2 ^ sb.val)) (hfi : UtSize fi sb)
    (heq : untyped.reset_untyped st arI s0 ar x = ok r) :
    ∃ (H1 : Heap) (Ac1 : Set U64),
      BlkOK st (Heap.tcbs H1) Cs (Heap.omega H1) H1 (Heap.frame H1) (Heap.replies H1) (Heap.scs H1)
        (Heap.ntfns H1) (Heap.scBits H1) Ac1 r.2.1 ∧
      (∀ q kd, H1 q = some kd → H q = some kd) ∧
      (∀ q, H1 q = H q → DeadQ st H s0 q → DeadQ st H1 r.2.1 q) := by
  obtain ⟨r', hr', H1, Ac1, hb1, hsh, hdk, -⟩ := spec_exists (hRS H Cs Ac s0 ar x p sb fi dev hb hcap hx hpal hfit hdrop hnode hfi)
  rw [heq] at hr'; cases eq_of_ok_eq hr'
  refine ⟨H1, Ac1, hb1, fun q kd hq => ?_, hdk⟩
  rw [hsh q] at hq
  split_ifs at hq with h
  exact hq

end

end

end Fl4Proofs.P3.Sched

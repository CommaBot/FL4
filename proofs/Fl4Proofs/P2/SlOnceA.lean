/-
# P2 (line slhuf, gen 7): `Once` at an alternative when the decided thread is homed elsewhere — trap arm

When the trap arm's receiver `d` (the handler endpoint's head) is homed on another core, its `REPLY_OBJ`
is outside the read set and an alternative's run is not the entry's. The walk (as `VmOnce`'s case B):
the prefix (`sl_pre_once`) and the fast path up to `Ep.head` on `SlRS s ∧ NU K`, then **one** read of `d`'s
`REPLY_OBJ` (nothing touched before it), then `schedulable_here d` on `SlRS s ∧ NU K`, which answers
`false` (`d`'s `AFFINITY`, a read-set word, is not this core), and the run ends.

* `RdHead.meet`, `RdBitmap.meet`, `FltDecT.meet`, `RrDecT.meet`, `FltDec.toT`: read facts for two sets
  give them for the meet.
* `sl_alt_pre`: an alternative's prefix state agrees with one of the entry's on `SlRS s` (`lp_alt`).
* **`fault_away_once`**: `Once` of the trap fast path at a state where the head's `AFFINITY` is a guard word
  and not this core.
* **`sl_once_trap_away`**: `Once` of the entry's tree at every alternative, trap arm, decided thread homed
  elsewhere.

No premises beyond the entry facts (`SlOF`).
-/
import Fl4Proofs.P2.SlOnceP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once)

section meet
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R1 R2 : U64 → Prop}

theorem RdHead.meet {X : S} {sc : obj.Sc} (h1 : RdHead (L := L) R1 X sc) (h2 : RdHead (L := L) R2 X sc) :
    RdHead (L := L) (fun q => R1 q ∧ R2 q) X sc :=
  ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2.1⟩, ⟨h1.2.2, h2.2.2⟩⟩

theorem RdBitmap.meet {X : S} (h1 : RdBitmap (L := L) R1 X) (h2 : RdBitmap (L := L) R2 X) :
    RdBitmap (L := L) (fun q => R1 q ∧ R2 q) X :=
  ⟨⟨h1.1, h2.1⟩, fun i hi => ⟨h1.2 i hi, h2.2 i hi⟩⟩

theorem FltDecT.meet {X : S} {t : U64} (D1 : FltDecT (L := L) R1 X t) (D2 : FltDecT (L := L) R2 X t) :
    FltDecT (L := L) (fun q => R1 q ∧ R2 q) X t :=
  ⟨fun o h1 h2 => ⟨D1.nd o h1 h2, D2.nd o h1 h2⟩, ⟨D1.dt, D2.dt⟩, ⟨D1.cd, D2.cd⟩, RdBitmap.meet D1.bm D2.bm,
    fun h => ⟨D1.tm h, D2.tm h⟩, fun h => ⟨⟨(D1.rh h).1, (D2.rh h).1⟩, RdHead.meet (D1.rh h).2 (D2.rh h).2⟩,
    ⟨⟨D1.fh.1, D2.fh.1⟩, ⟨D1.fh.2, D2.fh.2⟩⟩,
    fun ptr b x y g gr hc => ⟨⟨(D1.ep ptr b x y g gr hc).1, (D2.ep ptr b x y g gr hc).1⟩,
      ⟨(D1.ep ptr b x y g gr hc).2, (D2.ep ptr b x y g gr hc).2⟩⟩⟩

theorem RrDecT.meet {X : S} {t rptr ep : U64} (D1 : RrDecT (L := L) R1 X t rptr ep)
    (D2 : RrDecT (L := L) R2 X t rptr ep) : RrDecT (L := L) (fun q => R1 q ∧ R2 q) X t rptr ep :=
  ⟨fun o h1 h2 => ⟨D1.nd o h1 h2, D2.nd o h1 h2⟩, ⟨D1.dt, D2.dt⟩, ⟨D1.cd, D2.cd⟩, RdBitmap.meet D1.bm D2.bm,
    fun h => ⟨D1.tm h, D2.tm h⟩, fun h => ⟨⟨(D1.rh h).1, (D2.rh h).1⟩, RdHead.meet (D1.rh h).2 (D2.rh h).2⟩,
    ⟨D1.tSt, D2.tSt⟩, ⟨D1.tSc, D2.tSc⟩, ⟨D1.tMx, D2.tMx⟩, ⟨D1.tIq, D2.tIq⟩, ⟨D1.tMi, D2.tMi⟩,
    ⟨D1.tBn, D2.tBn⟩, ⟨D1.tPr, D2.tPr⟩,
    fun n h1 h2 => ⟨⟨(D1.ntf n h1 h2).1, (D2.ntf n h1 h2).1⟩, ⟨(D1.ntf n h1 h2).2, (D2.ntf n h1 h2).2⟩⟩,
    ⟨D1.rRt, D2.rRt⟩, ⟨D1.rNx, D2.rNx⟩, ⟨D1.eTS, D2.eTS⟩⟩

theorem FltDec.toT {R : U64 → Prop} {X : S} {t : U64} (D : FltDec (L := L) R X t) : FltDecT (L := L) R X t :=
  ⟨D.nd, D.dt, D.cd, D.bm, D.tm, D.rh, D.fh, fun ptr b x y g gr hc =>
    ⟨(D.ep ptr b x y g gr hc).1, (D.ep ptr b x y g gr hc).2.1⟩⟩

theorem RrDec.toT {R : U64 → Prop} {X : S} {t rptr ep : U64} (D : RrDec (L := L) R X t rptr ep) :
    RrDecT (L := L) R X t rptr ep :=
  ⟨D.nd, D.dt, D.cd, D.bm, D.tm, D.rh, D.tSt, D.tSc, D.tMx, D.tIq, D.tMi, D.tBn, D.tPr, D.ntf, D.rRt, D.rNx, D.eTS⟩

end meet

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A} {Rd User : U64 → Prop}

set_option maxHeartbeats 4000000 in
/-- **The trap fast path makes one racy read when the head is homed elsewhere** (module docstring). -/
theorem fault_away_once {R0 : U64 → Prop} (hR0 : ∀ q, R0 q → Rd q ∧ ¬ User q) {X : S} {a : A} {t n' : U64}
    (D : FltDecT (L := L) R0 X t)
    (hd : ∀ ptr b x y g gr, obj.Slot.cap st (slotIdx t layout.tcb.SLOT_FAULT_HANDLER) X =
        ok (capability.Cap.Endpoint ptr b x y g gr) → L.epState X ptr = obj.EP_RECV →
      R0 (affA (L.mem X (epHeadA ptr))) ∧ L.mem X (affA (L.mem X (epHeadA ptr))) ≠ L.cpu X)
    {r' : Bool × S × A} (h : interp st ar (R.fastpath.fault t n') X a = ok r') (Wd : Set U64) :
    Once st ar Rd User Wd ∅ (R.fastpath.fault t n') X a := by
  have hW0 : ∀ q, (fun _ => False) q → ¬ User q := fun _ h => h.elim
  unfold R.fastpath.fault at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h ⊢
  refine once_step (W0 := fun _ => False) hR0 hW0 (R.sched.action_nz) h (fun r h1 => ?_)
    (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st R0 (fun _ => False)) X
      (D.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h2 := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  split
  · simp only [Once]
  rename_i hi
  rw [if_neg hi] at h2
  refine once_step (W0 := fun _ => False) hR0 hW0 (NoZero.liftR _) h2
    (fun r h1 => by rw [interp_liftR_store _ st]; exact h1) (fun r h1 hk Wd _ => ?_)
  replace h2 := hk
  obtain ⟨sl', x2, a3⟩ := r
  obtain ⟨esl, e1, e2⟩ := interp_liftR_ok h1
  dsimp only at e1 e2
  subst x2 a3
  dsimp only at h2 ⊢ esl
  rw [tcb_slot_val] at esl
  have e := ok_inj_ff esl
  subst e
  refine once_step (W0 := fun _ => False) hR0 hW0 (R.obj.Slot.cap_nz _) h2 (fun r h1 => ?_)
    (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := PathObl.guard st R0 (fun _ => False)) _ X D.fh.1 D.fh.2]
    exact h1
  replace h2 := hk
  rw [R.obj.Slot.cap_eq] at h1
  obtain ⟨c, ec, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  cases c
  all_goals try (simp only [Once]; done)
  rename_i ptr badge x' y g gr
  obtain ⟨rts, rhd⟩ := D.ep ptr badge x' y g gr ec
  cases g
  rw [if_neg Bool.false_ne_true] at h2 ⊢
  cases gr
  · rw [if_neg Bool.false_ne_true]; simp only [Once]
  rw [if_pos rfl] at h2 ⊢
  rotate_left
  rw [if_pos rfl] at h2 ⊢
  all_goals
      refine once_step (W0 := fun _ => False) hR0 hW0 (R.obj.Ep.state_nz _) h2 (fun r h1 => ?_)
        (fun r h1 hk Wd _ => ?_)
      · rw [R.obj.Ep.state_eq] at h1 ⊢
        rw [obj.Ep.state.guard (gS := PathObl.guard st R0 (fun _ => False)) ptr X rts]
        exact h1
      replace h2 := hk
      rw [R.obj.Ep.state_eq] at h1
      obtain ⟨i1, ei1, rfl⟩ := bind_shape h1
      dsimp only at h2 ⊢
      split
      · simp only [Once]
      rename_i hi1
      rw [if_neg hi1] at h2
      have hst : L.epState X ptr = obj.EP_RECV := by
        rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) X ptr)] at ei1
        have e := ok_inj_ff ei1
        simp only [bne_iff_ne, ne_eq, not_not] at hi1
        rw [e, hi1]
      obtain ⟨rA, hrem⟩ := hd ptr badge x' y _ _ ec hst
      refine once_step (W0 := fun _ => False) hR0 hW0 (R.obj.Ep.head_nz _) h2 (fun r h1 => ?_)
        (fun r h1 hk Wd _ => ?_)
      · rw [R.obj.Ep.head_eq] at h1 ⊢
        rw [obj.Ep.head.guard (gS := PathObl.guard st R0 (fun _ => False)) ptr X rhd]
        exact h1
      replace h2 := hk
      rw [R.obj.Ep.head_eq] at h1
      obtain ⟨d, ed, rfl⟩ := bind_shape h1
      dsimp only at h2 ⊢
      have hdd : d = L.mem X (epHeadA ptr) := by
        rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) X ptr)] at ed
        exact (ok_inj_ff ed).symm
      subst hdd
      -- the reply word: its one read
      unfold R.obj.Tcb.reply_obj at h2 ⊢
      simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc] at h2 ⊢
      refine once_step (W0 := fun _ => False) hR0 hW0 (NoZero.liftR _) h2
        (fun r h1 => by rw [interp_liftR_store _ st]; exact h1) (fun r h1 hk Wd _ => ?_)
      replace h2 := hk
      obtain ⟨o, x2, a3⟩ := r
      obtain ⟨-, e1, e2⟩ := interp_liftR_ok h1
      dsimp only at e1 e2
      subst x2 a3
      dsimp only at h2 ⊢
      simp only [SProg.sbind, SProg.read] at h2 ⊢
      simp only [interp] at h2
      obtain ⟨v0, hv0, h2⟩ := bok.mp h2
      refine once_rd_first (W0 := fun _ => False) hR0 hW0 _ _ (fun v => by nz_walk) Wd ∅ X a
        (Set.notMem_empty _) (fun v hv => ?_)
      rw [hv0] at hv
      have e := ok_inj_ff hv
      subst e
      split
      · exact ⟨_, interp_ret' _ _ _ _ _⟩
      rename_i hz0
      rw [if_neg hz0] at h2
      rw [interp_sbind] at h2 ⊢
      obtain ⟨⟨bh, x3, a4⟩, hh, h3⟩ := bind_eq_ok' h2
      have hh' := hh
      rw [R.fastpath.schedulable_here_eq] at hh'
      obtain ⟨bh', ebh, ebh2⟩ := bind_shape hh'
      cases ebh2
      have hfalse : bh = false := by
        cases bh
        · rfl
        · exact absurd (here_facts (L := L) ebh).aff hrem
      subst hfalse
      rw [R.fastpath.schedulable_here_eq, vm_here_guard (gS := PathObl.guard st R0 (fun _ => False)) X _
          (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
          (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
          (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
          D.tm D.rh D.dt D.cd rA (fun hl => absurd hl hrem), ebh]
      refine ⟨(false, X, a), ?_⟩
      first
        | rfl
        | simp only [bind_tc_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, interp_ret']

end

section alt
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {Cs Ω Sg Ac : Set U64}

/-- The read set without user words. -/
abbrev SlRN (K : KLayout) (Locks : S → U64 → Prop) (s : S) (q : U64) : Prop :=
  SlRS (st := st) K Locks s q ∧ NU K q

/-- **An alternative's prefix state agrees with an entry's prefix state on `SlRS s`** (`lp_alt`). -/
theorem sl_alt_pre (hA : P0.ArchTotal ar) {s s' : S} {a : A}
    (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {X' : S} {a1' : A} (LP' : LocalPre (st := st) ar s' a (X', a1')) :
    ∃ X, LocalPre (st := st) ar s a (X, a1') ∧
      (∀ b, SlRS (st := st) K Locks s b → L.mem X' b = L.mem X b) ∧ L.ksb X' = L.ksb X ∧ L.cpu X' = L.cpu X := by
  have E := F.E
  have hcur := sl_alt_cur F.P.preG Al
  have hN' : NodePlaced st K.heap.tcbs s' (L.cpu s') := by rw [Al.cpu]; exact NodePlaced.of_ksb Al.ksb E.hN
  have hc' : L.curW s' ∈ K.heap.tcbs := by rw [hcur]; exact E.hcT
  have hct : SlRS (st := st) K Locks s (ctA (L := L) s) :=
    (F.P.preG.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
  have hcn : SlRS (st := st) K Locks s (cnA (L := L) s) :=
    (F.P.preG.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
  obtain ⟨X, LP, hag⟩ := lp_alt ar hA (fun b hb => hb.1) E.hT E.hN E.hcT Al.ksb Al.cpu hcur Al.read
    F.P.preG.nx hct hcn LP'
  obtain ⟨hkX, hcX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  obtain ⟨hkX', hcX', -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT hN' hc' LP'
  exact ⟨X, LP, hag, by rw [hkX', hkX, Al.ksb], by rw [hcX', hcX, Al.cpu]⟩

/-- The prefix facts at an alternative, on `SlRN s` / `NU K`. -/
theorem sl_alt_preDec {s s' : S} (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s') :
    PreDec (L := L) (SlRN (st := st) K Locks s) (NU K) s' := by
  have E := F.E
  have hX := F.B.regionOKX
  have hcur := sl_alt_cur F.P.preG Al
  refine ⟨fun o h1 h2 => by rw [slDS_node Al.ksb Al.cpu]; exact ⟨(F.P.preG.nd o h1 h2).1, F.B.nuNode E.hN h1 h2⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · show NU K (L.nodeAt s' (L.cpu s') layout.node.CUR_TIME)
    rw [slDS_node Al.ksb Al.cpu]
    exact F.B.nuNode E.hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  · show NU K (L.nodeAt s' (L.cpu s') layout.node.CONSUMED)
    rw [slDS_node Al.ksb Al.cpu]
    exact F.B.nuNode E.hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  · rw [hcur]; exact ⟨F.P.preG.fl, nu_tcb hX E.hSt.1 (o := 3456#u64) (by simp) (by simp) (by simp)⟩
  · rw [hcur]; exact ⟨F.P.preG.nx, nuReg hX E.hSt.1 (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])⟩
  · rw [hcur]; exact nuReg hX E.hSt.1 (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])

/-- The current SC's head refill at an alternative's prefix state, on `SlRN s`. -/
theorem sl_alt_hhd (hA : P0.ArchTotal ar) {s s' : S} {a : A}
    (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s') :
    ∀ X' a1 csc, LocalPre (st := st) ar s' a (X', a1) → sched.cur_sc st X' = ok csc →
      RdHead (L := L) (SlRN (st := st) K Locks s) X' csc := by
  intro X' a1' csc LP' ecsc
  have E := F.E
  have hX := F.B.regionOKX
  obtain ⟨X, LP, hag, hk, hc⟩ := sl_alt_pre ar hA F Al LP'
  obtain ⟨hkX, hcX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have rcs : SlRS (st := st) K Locks s (L.nodeA X layout.node.CUR_SC) := by
    unfold LawfulStore.nodeA; rw [hcX, nodeAt_of_ksb hkX]
    exact (F.P.preG.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
  have en : L.nodeA X' layout.node.CUR_SC = L.nodeA X layout.node.CUR_SC := by
    unfold LawfulStore.nodeA; exact slDS_node hk hc
  have ecsc' : sched.cur_sc st X = ok csc := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X')] at ecsc
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X), ← hag _ rcs, ← en]
    exact ecsc
  have h1 := F.P.hhd a X a1' csc LP ecsc'
  have e : csc = L.cscW s := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at ecsc'
    rw [← ok_inj_ff ecsc']; exact ecs
  have h2 : RdHead (L := L) (NU K) X csc := by
    rw [e]; exact rdHead_hereN ar hA hX E F.Hh LP F.Hh.cs
  exact RdHead.congr (fun b hb => hag b hb.1) (RdHead.meet h1 h2)

set_option maxHeartbeats 4000000 in
/-- **`Once` at an alternative, trap arm, decided thread homed elsewhere** (module docstring). -/
theorem sl_once_trap_away (hA : P0.ArchTotal ar) {s s' : S} {a : A} {rp ep : U64}
    (F : SlOF (st := st) ar K Locks m0 n (rp, ep) Cs Ω Sg Ac s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    (hS : SlTrap st s) (hh : L.mem s (affA (slThr st rp s)) ≠ L.cpu s)
    {r' : Bool × S × A} (h : interp st ar (R.syscall.handle_syscall_local n (rp, ep)) s' a = ok r') :
    Once st ar (SlRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_syscall_local n (rp, ep)) s' a := by
  have E := F.E
  have B := F.B
  have hX := B.regionOKX
  have I := F.I
  have hcur := sl_alt_cur F.P.preG Al
  have hTr := slTrap_alt F.P.preG.fl Al hcur
  have hN' : NodePlaced st K.heap.tcbs s' (L.cpu s') := by rw [Al.cpu]; exact NodePlaced.of_ksb Al.ksb E.hN
  have hc' : L.curW s' ∈ K.heap.tcbs := by rw [hcur]; exact E.hcT
  refine sl_pre_once (R0 := SlRN (st := st) K Locks s) (W0 := NU K) (fun q hq => ⟨hq.1, hq.2.2⟩)
    (fun q hq => hq.2) hA E.hT hN' hc' (sl_alt_preDec ar F Al) (sl_alt_hhd ar hA F Al) h ?_
    (fun hS' => absurd (hTr.2 hS) hS')
  intro _ X' a1' a2 n' LP' h' Wd
  obtain ⟨X, LP, hag, hk, hc⟩ := sl_alt_pre ar hA F Al LP'
  have hag' : ∀ b, SlRN (st := st) K Locks s b → L.mem X' b = L.mem X b := fun b hb => hag b hb.1
  have DT : FltDecT (L := L) (SlRN (st := st) K Locks s) X' (L.curW s) :=
    FltDecT.congr hk hc hag' (FltDecT.meet (F.D.fT hS a X a1' LP) (FltDec.toT (fltDec_nu ar hA B E LP)))
  rw [hcur] at h' ⊢
  refine fault_away_once (fun q hq => ⟨hq.1, hq.2.2⟩) DT ?_ h' Wd
  intro ptr bb x y g gr hcp hst'
  have DT0 := F.D.fT hS a X a1' LP
  have hc0 : obj.Slot.cap st (fhA (L := L) s) X = ok (capability.Cap.Endpoint ptr bb x y g gr) :=
    (cap_congr (hag _ DT0.fh.1) (hag _ DT0.fh.2)).symm.trans hcp
  have ets : L.mem X' (epTSA ptr) = L.mem X (epTSA ptr) := hag _ (DT0.ep ptr bb x y g gr hc0).1
  have hst : obj.Ep.state st ptr X = ok obj.EP_RECV := by
    rw [← ep_state_congr (st := st) ets, eq_of_spec_fd (obj.Ep.state.spec (L := L) X' ptr), hst']
  have lv := slLive_trap ar hA E.hT E.hN E.hcT I hS LP hc0 hst
  have af := I.af lv
  have e1 := slThr_hd_trap ar hA E.hT E.hN E.hcT I hS LP hc0
  have eh : L.mem X' (epHeadA ptr) = slThr st rp s := by
    rw [hag _ (DT0.ep ptr bb x y g gr hc0).2, e1]
  rw [eh]
  obtain ⟨-, hcX0, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  refine ⟨⟨af.1, nu_tcb hX (F.N.hthr lv) (o := 3520#u64) (by simp) (by simp) (by simp)⟩, fun e => hh ?_⟩
  rw [← lp_mem ar hA E.hT E.hN E.hcT LP af.1.1 af.2, ← hag _ af.1, e, hc, hcX0]

end alt

end Fl4Proofs.P2.PathObl

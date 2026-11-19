/-
P3 (DESIGN.md §9), CSpace: **the reply's, the thread's and the IRQ
handler's finalisations at `WJL`** (XTopJointWJLFin's `JFinAtL`, the kinds
left there).

* `jFinAtL_reply`: XTopJointDelR's `jFinAt_reply` at `WJL`
  (`JAtZ.finReplyJD` from the dead set grown by the TCB zombies' TCBs, its
  `reply_remove` case by `JAtZ.replyRemoveJD` at that set; P1's
  `fin_reply.dbgKeep`, its caller-core premise by `JAtZ.rmCore`).
* `jFinAtL_thread`: XTopJointDelR's `jFinAt_thread` at `WJL`
  (`JAtZ.finThreadJL` from the grown dead set): the debug lists lose exactly
  the thread (`JAtZ.dbgWF_thread`), so `LiveJ` after by `LiveJ.of_sameDbg`
  (every debug-list member after one before: `dbgNth_mem_wf`,
  `dbgNth_getElem_wf`) and `RzJ` at the zombie remainder (the thread dead,
  off the list).
-/
import Fl4Proofs.P3.XTopJointWJLFin
import Fl4Proofs.P3.XTopJointFinThreadU
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **A final reply cap's finalisation at `WJL`** (module docstring). -/
theorem jFinAtL_reply [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) : JFinAtL (L := L) arI AR th RpK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ⟨p, g, hce⟩ hfin
  subst hce hth
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .reply := (hJ.typed _ hA.isSlot).2.2 p g hcv
  have hpR : p ∈ (Z.mv G V).R := J.hset.2.2 p hHp
  have hrH : p ∈ P1.Heap.replies H := J.zH.2.2.1 p hpR
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  have hdc : ∀ t ∈ P1.Heap.tcbs H, headBit (L.mem s (rNextA p)) = true →
      L.mem s (P1.affA t) = L.mem s (P1.scCoreA (L.mem s (rNextA p) &&& ~~~1#u64)) := fun t ht =>
    J.rmCore hpR (by rw [J.tcbs_eq.1]; exact ht)
  rw [decide_eq_true hfin] at hpp ⊢
  refine WP.spec_mono (WP.spec_and (WP.spec_and
    (J0.finReplyJD hT (fun r t x hr ht hk hst => WP.spec_mono (J0.replyRemoveJD hT hr ht hk hst)
      fun res ⟨h1, σ', V', Ac', Lst', D', e, J', hSS, hks, hD, _⟩ => by
        subst hD; exact ⟨h1, σ', V', Ac', Lst', e, J', hSS, hks⟩) hpR)
    (P1.fin_cap_reply.dead (ar := arI) hT s a p g false J.blk hHp))
    (P1.fin_reply.dbgKeep (ar := arI) hT s a p g true false J.blk hrH hdc)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨e1, e2, σ1, V1, Ac1, Lst1, hmem1, J1, hSS1, hks1⟩, d1⟩, hK⟩
  simp only at e1 e2 hmem1 J1 hSS1 hks1 d1 hK
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  subst e2
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h),
      fun h => (by rw [hHp] at h; cases h), fun _ => d1, fun z h => (by rw [hHp] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Reply p g := by
    rw [hSS1.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS1 hDS1 hK
  have hn : ∀ q, ¬ RefsObj q (capV (L.mem s1) (cslotAddr sl)) := fun q h => by rw [hcv1] at h; exact h
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨⟨V1, Ac1, Lst1, _, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns, SpecGlob.fin hmem1 hsg, hpp _ _ hmem1 hp0⟩,
      hL1, hDW1, hN1⟩,
    fun _ => rdLO_noRef arI J1 hL1 (JAtZ.reply_ready arI J1 hA.isSlot hcv1 hdp) hn,
    fun _ _ _ _ q h => by rw [hcv1] at h; cases h⟩

/-- `dbgNth` one step further, from the end. -/
theorem dbgNth_succ' (m : U64 → U64) (n : Nat) (h : U64) :
    dbgNth m (n + 1) h = (if dbgNth m n h = 0#u64 then 0#u64 else m (P1.dnA (dbgNth m n h))) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    by_cases h0 : h = 0#u64
    · subst h0; simp [dbgNth]
    · rw [show dbgNth m (n + 1 + 1) h = dbgNth m (n + 1) (m (P1.dnA h)) by simp [dbgNth, h0], ih,
        show dbgNth m (n + 1) h = dbgNth m n (m (P1.dnA h)) by simp [dbgNth, h0]]

/-- **A debug-list walk stays on the list** (`DbgWFL`). -/
theorem dbgNth_mem_wf {T Cs : Set U64} {m hd : U64 → U64} {lst : U64 → List U64}
    (hW : DbgWFL T Cs m hd lst) {c : U64} (hc : c ∈ Cs) (n : Nat) :
    dbgNth m n (m (hd c)) = 0#u64 ∨ dbgNth m n (m (hd c)) ∈ lst c := by
  induction n with
  | zero =>
    show m (hd c) = 0#u64 ∨ m (hd c) ∈ lst c
    rw [hW.head c hc]
    cases lst c with
    | nil => exact Or.inl rfl
    | cons a r => exact Or.inr (by simp)
  | succ n ih =>
    rw [dbgNth_succ']
    split
    · exact Or.inl rfl
    · rename_i h0
      rw [hW.next c hc _ (ih.resolve_left h0)]
      exact nextIn_mem _ _

theorem nextIn_getElem {l : List U64} (hnd : l.Nodup) {i : Nat} (hi : i + 1 < l.length) :
    nextIn l (l[i]'(by omega)) = l[i + 1] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a r ih =>
    obtain ⟨ha, hr⟩ := List.nodup_cons.1 hnd
    cases i with
    | zero =>
      cases r with
      | nil => simp at hi
      | cons b r' => simp [nextIn]
    | succ j =>
      have hj : j + 1 < r.length := by simp at hi; omega
      have hne : a ≠ r[j] := fun e => ha (by rw [e]; exact List.getElem_mem _)
      simp only [List.getElem_cons_succ, nextIn, if_neg hne]
      exact ih hr hj

theorem headD_getElem0 (l : List U64) (hi : 0 < l.length) : l.headD 0#u64 = l[0] := by
  cases l with
  | nil => simp at hi
  | cons a r => rfl

/-- **A debug-list walk visits the list in order** (`DbgWFL`). -/
theorem dbgNth_getElem_wf {T Cs : Set U64} {m hd : U64 → U64} {lst : U64 → List U64}
    (hW : DbgWFL T Cs m hd lst) {c : U64} (hc : c ∈ Cs) :
    ∀ i (hi : i < (lst c).length), dbgNth m i (m (hd c)) = (lst c)[i] := by
  intro i
  induction i with
  | zero =>
    intro hi
    show m (hd c) = _
    rw [hW.head c hc]
    exact headD_getElem0 _ hi
  | succ i ih =>
    intro hi
    have hi' : i < (lst c).length := by omega
    rw [dbgNth_succ', ih hi']
    have hz : (lst c)[i] ≠ 0#u64 := fun e => hW.zero c hc (by rw [← e]; exact List.getElem_mem hi')
    rw [if_neg hz, hW.next c hc _ (List.getElem_mem hi')]
    exact nextIn_getElem (hW.nodup c hc) hi

/-- **`LiveJ.of_sameZ` with the debug list shrunk** (module docstring): every
debug-list member after one before. -/
theorem LiveJ.of_sameDbg {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s s' : S}
    {σ σ' : Fl4Spec.State Unit} (hL : LiveJ (L := L) th H G s σ) (hSS : SlotsSame th (L.mem s) (L.mem s'))
    (hmem : ∀ y ∈ G.chains.flatten, IsSlot th y) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hdbg : ∀ n, dbgNth (L.mem s') n (dbgHead (L := L) s') ≠ 0#u64 → ∃ k,
      dbgNth (L.mem s') n (dbgHead (L := L) s') = dbgNth (L.mem s) k (dbgHead (L := L) s) ∧
      dbgNth (L.mem s) k (dbgHead (L := L) s) ≠ 0#u64)
    (hdead : ∀ p ∈ ZTcb (L := L) th s, DeadP (L := L) H s' p) :
    LiveJ (L := L) th H G s' σ' := by
  have hU : ∀ y, IsSlot th y → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := fun y hy hu => by
    unfold InUse at hu ⊢
    rw [hSS.capV hy, horig] at hu
    exact hu
  refine ⟨fun q i hqi hu => ?_, fun n hn => ?_, fun y hy p zt n hz i hpi hni hu => ?_,
    fun y hy p zt n hz hzt => ?_⟩
  · obtain ⟨y, hy, hr⟩ := hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hu)
    exact ⟨y, hy, by rw [hSS.capV (hmem y hy)]; exact hr⟩
  · obtain ⟨k, hk, hk0⟩ := hdbg n hn
    obtain ⟨y, hy, hr⟩ := hL.dbg k hk0
    exact ⟨y, hy, by rw [hSS.capV (hmem y hy), hk]; exact hr⟩
  · exact hL.zslots y hy p zt n (by rw [← hSS.capV hy]; exact hz) i hpi hni (hU _ ⟨p, i, hpi, rfl⟩ hu)
  · exact hdead p ⟨y, hy, zt, n, by rw [← hSS.capV hy]; exact hz, hzt⟩

set_option maxHeartbeats 4000000 in
/-- **A final thread cap's finalisation at `WJL`** (module docstring). -/
theorem jFinAtL_thread (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hF : JThreadFinHypsU (L := L) arI AR th) : JFinAtL (L := L) arI AR th TcbK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ⟨p, hce⟩ hfin
  subst hce hth
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩ := hW
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  have hthp : Z.th p = some .tcb := hDS.1.2.1.abs hA hc
  have hpT : p ∈ Z.T := J.thT p hthp
  have hpH : H p = some .tcb := J.zH.1 p hpT
  have hv0 := hF.obj (Z.mv G V) H Cs Ac Lst D s a σ rfl J _ p hA.isSlot hcv
  have hidle : L.idleW s ≠ p := by
    intro e
    obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hA
    rw [hc] at hc0; cases eq_of_ok_eq hc0
    rw [hca0.abs] at hg0
    have ha0 := (getCap_set_iff σ sl.1 sl.2 _).1 (congrArg Prod.fst hg0)
    apply hsg.idle sl.1 sl.2 _ ha0 (by simp [IsPageCap, absCap])
    rw [JAtZ.idleThread_eq arI J, e]; simp [absCap, Fl4Spec.objRefs]
  have hna : L.actionW s ≠ p := J.action_ne_of_noSwitch hpT hns
  have hp00 : p ≠ 0#u64 := fun e => by rw [e, J.kern.h0] at hpH; cases hpH
  have c0 : 0#u64 ∈ Cs := J.kern.cs0
  have hnd := hDW.nodup 0#u64 c0
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  rw [decide_eq_true hfin] at hpp ⊢
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and
    (J0.finThreadJL hT hK hF.ticks hL hpT hv0 hna hidle)
    (P1.fin_cap_thread.dead (ar := arI) hT s a p false J.blk hpH hna hidle hv0))
    (P1.fin_cap_thread.slots (ar := arI) hT s a p true false J.blk hpH hna hidle hv0))
    (J.finThreadDbgPre hT hpH hna hidle hv0)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨⟨σ1, hm1, V1, Ac1, Lst1, J1⟩, d1, d2, d3, d4, d5, d6⟩, e, -, f, hW1⟩, s5, hpre⟩
  simp only [ite_true, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_of_capw J.xtop.rel.1 (J.slotCapW (tLowSlots_all _)) hW1
  have hks1 : L.ksb s1 = L.ksb s := f.1
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun _ => ⟨d1, d2, d3, Ne.symm d4, Ne.symm d5, d6⟩, fun h => (by rw [hpH] at h; cases h),
      fun h => (by rw [hpH] at h; cases h), fun h => (by rw [hpH] at h; cases h),
      fun z h => (by rw [hpH] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Thread p := by
    rw [hSS1.capV hA.isSlot, hcv]
  have hm1' : ((absCap (capability.Cap.Zombie p capability.ZOMBIE_TCB 6#u64), absCap capability.Cap.Null), σ1) ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Thread p)) true σ).1 := by
    rw [absCap_zombieTcb]; exact hm1
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  have horig : σ1.isOriginalCap = σ.isOriginalCap :=
    orig_eq_of_slots hDS.1.2.2.2.1 hDS1.1.2.2.2.1 J.kern.orig J1.kern.orig hSS1
  have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hDS.1.2.2.1.members y).1 hy).1
  have hDW1 := J.dbgWF_thread J1 rfl rfl hDW hpH hpre
  have hW1m : ∀ n, dbgNth (L.mem s1) n (dbgHead (L := L) s1) = 0#u64 ∨
      dbgNth (L.mem s1) n (dbgHead (L := L) s1) ∈ (lst 0#u64).erase p := fun n =>
    dbgNth_mem_wf hDW1 c0 n
  have hdbg : ∀ n, dbgNth (L.mem s1) n (dbgHead (L := L) s1) ≠ 0#u64 → ∃ k,
      dbgNth (L.mem s1) n (dbgHead (L := L) s1) = dbgNth (L.mem s) k (dbgHead (L := L) s) ∧
      dbgNth (L.mem s) k (dbgHead (L := L) s) ≠ 0#u64 := by
    intro n hn
    have hy := ((List.Nodup.mem_erase_iff hnd).1 ((hW1m n).resolve_left hn)).2
    obtain ⟨k, hk, ek⟩ := List.mem_iff_getElem.1 hy
    have e2 : dbgNth (L.mem s) k (dbgHead (L := L) s) = (lst 0#u64)[k] := dbgNth_getElem_wf hDW c0 k hk
    exact ⟨k, by rw [e2, ek], by rw [e2, ek]; exact hn⟩
  have hL1 : LiveJ (L := L) Z.th H G s1 σ1 :=
    hL.of_sameDbg hSS1 hmem horig hdbg (fun q hq => J1.jcov.dead q (Or.inr hq))
  have hN1 : NullOrig Z.th (L.mem s1) σ1 := hN.of_same (fun y hy => hSS1.capV hy) horig
  refine ⟨rfl, trivial, trivial, σ1, G, hm1', hDS1, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨⟨V1, Ac1, Lst1, _, J1, hks1.trans hkb, ak_finaliseCap_ns hm1' hns, SpecGlob.fin hm1' hsg, hpp _ _ hm1' hp0⟩,
      hL1, ⟨_, hDW1⟩, hN1⟩, fun hrm => ?_, fun _ _ _ _ q hq => ?_⟩
  · exfalso
    rcases hrm with e | ⟨p', zt, n, e, hn⟩
    · cases e
    · cases e
      rcases hn with hn | ⟨hn, -⟩ <;> exact absurd hn (by decide)
  · have e : p = q := by rw [hcv1] at hq; cases hq; rfl
    subst e
    refine ⟨hdp, fun n hn => ?_⟩
    rcases hW1m n with h | h
    · exact hp00 (hn.symm.trans h)
    · rw [hn] at h
      exact ((List.Nodup.mem_erase_iff hnd).1 h).1 rfl

end

end

end Fl4Proofs.P3

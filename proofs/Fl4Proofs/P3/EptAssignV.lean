/-
P3 (line mmuAD, gen 42b7): **the ASID-pool assign of an EPT root at `VmEptState`** — the second half of gen 42b5's
route (b) (P3/EptAssignJ has the first: `JAtZB.eptAssignX`, `XTopAt` after the assign), by gen 42b6's 4-step plan.

* Spec: **`AssignFE.ofTcb`** / **`KFoot.ofTcb`**: `AssignFE` / `KFoot` from the decode's entry state `σ` move to the
  restart state `σ1` (`σ1` differs from `σ` only at the current thread's TCB; the ASID table and the CDT kept).
  **`eptAssign_size`**: the objects' sizes kept (the one rewritten arch object is the pool).
* **`Vs.VsNamed.ofEptAssignF`** (the new `VsNamed` lemma of 42b6's plan): `VsNamed` across the nested assign — the
  invoked slot's `Ept` cap (no VSpace key) rewritten, every other slot kept (`SlotFoot`), the ASID table and every
  set table / pool other than the written pool kept in the spec (`AssignFE`), and every changed pool word guest-tagged
  (`r ||| 1`): a tagged entry is no walk step (`VsPath.pool` needs the tag clear, `wstep5`), so walks are only
  removed (VsNamedOps' `VsNamed.shrink`; the tables by `esame_of_kheap`, unmapped tables empty by `unEmpty_keep`).
* **`VmEptState.eptAssign`**: from `VmEptState V X XL` at an `Entered` spec state, the invoked ASID-pool cap in a
  slot, its first extra cap the unmapped level-0 `Ept ptr1` of a CNode slot: FL4's `vspace.decode` at
  `X86ASIDPoolAssign` ends in an error related to the spec decoder's with the states unchanged, or `Ok ()` with the
  spec decoder's outcome `.poolAssign asid ptr (pc, idx)` (no failure), the single outcome `σ'` of restart + perform
  (`EptAssignSpec`), and **`VmEptState V X XL` at FL4's state after and `σ'`** (some `Lst'`). Steps:
  1. `VmEptState.restart` (P3/EptSetRoot) to the restart states `s1`, `σ1`;
  2. FL4's writes from `s1` pinned as in P3/XTopJointVsMap's `JAtZ.vsPostJ` (the TCB state words and the action word by
     `XTopAt` at both states and the spec keeping the TCBs' states and the action; the other slots by `SlotFoot`);
  3. the base by P3/JAtZBRecap's **`JAtZB.vsStepJXB`** (the spec step `VsSFr` by P3/EptAssignJ's `vsSFr_eptAssign`,
     the cap `Ept r 0 false → Ept r 0 true asid 0` of the same shape and object key, not untyped; `VsSlotsW` after:
     an `Ept` cap is `VCapOK`-trivial; `VsNamed` after by `VsNamed.ofEptAssignF`);
  4. `VcpuCore` by P3/EptStep1's **`VcpuCore.ofWE`** (gen 42b7: `VcpuCore.ofW` generalised in place to slot caps
     rewritten into `Ept` caps of the same shape; the writes miss the VCPUs and the list head: `JAtZB.vsW_apart` /
     `vsW_head`, `slotWd_vcpu` / `slotWd_head`; the TCB VCPU words: `TopPlaced.disj`, `slotWd_tcb`), `JExtEpt`
     after (`ptr1 ∈ X` from the old cap), `EptCore` by P3/EptAssign's `EptCore.assignE` at `s1`, `σ1`.
* **`eptAssign_decode_vmEpt`**: the same with the extended decoder `specDecV` (`fl4DecodeInvocationV`) on the
  ASID-pool cap and its extra caps (P3/EptAssignJ's `decV_asidPoolEpt`): error ↔ the extended decoder's error;
  success: `DecOut` of `.ept (.poolAssign …)`, `EptAssignSpec`, `VmEptState` after.

No named premise; the spec is not touched. No `sorry`; only the three standard axioms.
-/
import Fl4Proofs.P3.EptAssignJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Spec side: from the decode's entry state to the restart state -/

section Spec
open Fl4Spec Fl4Proofs.P3.Vs

/-- `AssignFE` at the restart state: only the current thread's TCB differs (module docstring). -/
theorem AssignFE.ofTcb {m : U64 → U64} {x q0 : U64} {σ σ1 σ' : State Unit} {ct : ObjRef} {y y1 : Tcb}
    (hA : AssignFE m x q0 σ σ') (hk : ∀ o, o ≠ ct → σ1.kheap o = σ.kheap o)
    (hct : σ.kheap ct = some (.tcb y)) (hct1 : σ1.kheap ct = some (.tcb y1))
    (har : σ1.archState = σ.archState) : AssignFE m x q0 σ1 σ' := by
  obtain ⟨asid, pool, hi, lo, f, hcv, hhi, htab, hlo, has, has20, ha0, hkp, hkp', hAK, htab'⟩ := hA
  have hpc : pool.bv ≠ ct := fun e => by rw [e, hct] at hkp; cases hkp
  refine ⟨asid, pool, hi, lo, f, hcv, hhi, by rw [har]; exact htab, hlo, has, has20, ha0, by rw [hk _ hpc]; exact hkp,
    hkp', ?_, by rw [har]; exact htab'⟩
  rintro q ⟨ao, hq⟩ hne
  have hqc : q.bv ≠ ct := fun e => by rw [e, hct1] at hq; cases hq
  rw [hk _ hqc] at hq ⊢
  exact hAK q ⟨ao, hq⟩ hne

/-- `KFoot` at the restart state. -/
theorem KFoot.ofTcb {σ σ1 σ' : State Unit} {ct : ObjRef} {y y1 : Tcb} (hK : KFoot σ σ')
    (hk : ∀ o, o ≠ ct → σ1.kheap o = σ.kheap o)
    (hct : σ.kheap ct = some (.tcb y)) (hct1 : σ1.kheap ct = some (.tcb y1))
    (hcdt : σ'.cdt = σ1.cdt) (horig : σ'.isOriginalCap = σ1.isOriginalCap) (hcur : σ'.curThread = σ1.curThread) :
    KFoot σ1 σ' := by
  refine ⟨hcdt, horig, fun o hne => ?_, hcur⟩
  by_cases e : o = ct
  · subst e
    refine Or.inr (Or.inr ⟨y1, ?_⟩)
    by_cases e2 : σ'.kheap o = σ.kheap o
    · exact ⟨_, hct1, by rw [e2]; exact hct⟩
    · rcases hK.2.2.1 o e2 with ⟨a0, a1, h0, -⟩ | ⟨r, cs, cs', h0, -, -⟩ | ⟨t, t', -, h1⟩
      · rw [hct] at h0; cases h0
      · rw [hct] at h0; cases h0
      · exact ⟨_, hct1, h1⟩
  · rw [hk o e] at hne ⊢
    exact hK.2.2.1 o hne

/-- The objects' sizes across the nested assign (the one rewritten arch object is the pool). -/
theorem eptAssign_size {m : U64 → U64} {x q0 : U64} {σ σ' : State Unit} (hA : AssignFE m x q0 σ σ') (hK : KFoot σ σ')
    (o : ObjRef) (ko' : KernelObject) (h' : σ'.kheap o = some ko') :
    ∃ ko, σ.kheap o = some ko ∧ objBits ko' = objBits ko := by
  obtain ⟨asid, pool, hi, lo, f, -, -, -, -, -, -, -, hkp, hkp', hAK, -⟩ := hA
  by_cases e : σ'.kheap o = σ.kheap o
  · exact ⟨ko', by rw [← e]; exact h', rfl⟩
  rcases hK.2.2.1 o e with ⟨a0, a1, h0, h1⟩ | ⟨r, cs, cs', h0, -, h1⟩ | ⟨t, t', h0, h1⟩
  · by_cases hop : o = pool.bv
    · subst hop
      rw [hkp'] at h'; cases h'
      exact ⟨_, hkp, rfl⟩
    · exact absurd (hAK ⟨o⟩ ⟨a0, h0⟩ (fun h => hop (by rw [← h]))) e
  · rw [h1] at h'; cases h'; exact ⟨_, h0, rfl⟩
  · rw [h1] at h'; cases h'; exact ⟨_, h0, rfl⟩

end Spec

/-! ## `VsNamed` across the nested assign -/

namespace Vs
open Fl4Proofs.P1

section
variable {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {m m' : U64 → U64} {ksb : U64} {σ σ' : Fl4Spec.State Unit}

/-- A table of level `1 … 4` is not an ASID pool. -/
theorem ne_pool_of_lvl (hPt : PtRel L4 L3 L2 L1 m σ) {k : Nat} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) {q : U64}
    (hq : q ∈ lvlSet P L4 L3 L2 L1 k) {pool : U64} {f : BitVec 9 → Option Fl4Spec.ObjRef}
    (hp : σ.kheap pool.bv = some (.archObj (.asidPool f))) : q ≠ pool := by
  intro e
  subst e
  obtain rfl | rfl | rfl | rfl : k = 4 ∨ k = 3 ∨ k = 2 ∨ k = 1 := by omega
  · obtain ⟨g, hg, -⟩ := hPt.l4 q hq; rw [hg] at hp; cases hp
  · obtain ⟨g, hg, -⟩ := hPt.l3 q hq; rw [hg] at hp; cases hp
  · obtain ⟨g, hg, -⟩ := hPt.l2 q hq; rw [hg] at hp; cases hp
  · obtain ⟨g, hg, -⟩ := hPt.l1 q hq; rw [hg] at hp; cases hp

/-- A guest-tagged pool word is no walk step. -/
theorem wstep5_tagged {w : U64} (h : w &&& 1#u64 ≠ 0#u64) : wstep 5 w = none := by
  cases e : wstep 5 w with
  | none => rfl
  | some q => exact absurd (wstep5.1 e).1.2 h

/-- **`VsNamed` across the ASID-pool assign of an EPT root** (module docstring). -/
theorem VsNamed.ofEptAssignF (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
    (hR' : VsRel P m' ksb σ') (hPt' : PtRel L4 L3 L2 L1 m' σ')
    {x : U64} {r a0 v0 : U64} (hc : capV m x = .Ept r 0#u64 false a0 v0) (hSF : SlotFoot th m m' x)
    (hA : AssignFE m' x r σ σ')
    (hAW : ∀ q ∈ P, ∀ i : U64, i.val < 512 → m' (peA q i) ≠ m (peA q i) → m' (peA q i) &&& 1#u64 ≠ 0#u64) :
    VsNamed th m' ksb := by
  obtain ⟨asid, pool, hi, lo, f, hcv, -, -, -, -, -, -, hkp, -, hAK, htab'⟩ := hA
  have hWt : TblSame ksb m m' := tbl_same_of_asid hR hR' htab'
  -- the set tables other than the pool keep their spec objects
  have hko : ∀ q, (q ∈ P ∨ q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) → q ≠ pool → σ'.kheap q.bv = σ.kheap q.bv :=
    fun q hq hne => hAK q (arch_of_set hR hPt hq) hne
  refine hN.shrink (fun y hy hk => ?_) (fun hi' hh => Or.inl (hWt hi' hh)) (fun k p a v i hp h2 h5 hi' => ?_)
    (fun y hy hu k q hkey i hi' => ?_) (fun y hy q b hb hi' hib => ?_)
  · by_cases e : y = x
    · subst e
      rw [hc, hcv] at hk
      exact absurd hk (by simp [VKey])
    · exact capV_of_foot hSF y hy e
  · have hm := hp.mem hR hPt hPI
    by_cases e5 : k = 5
    · subst e5
      by_cases e : m' (peA p i) = m (peA p i)
      · exact Or.inl (by rw [e])
      · exact Or.inr (wstep5_tagged (hAW p hm i (by simpa [bnd] using hi') e))
    · have hpp : p ≠ pool := ne_pool_of_lvl hPt (by omega) (by omega) hm hkp
      exact Or.inl (esame_of_kheap hPt hPt' (by omega) (by omega) hm (hko p (lvl_mem hm) hpp) hi').2
  · have hq := hS.need hy (vneed_of_un hu hkey)
    have hk14 := un_lvl hu hkey
    exact unEmpty_keep hPt hPt' hN hS (X := (· = pool))
      (fun q hq' hx => hko q (Or.inr hq') hx) y hy hu k q hkey (ne_pool_of_lvl hPt hk14.1 hk14.2 hq hkp) i hi'
  · have hcw := hS y hy
    rw [hb] at hcw
    simp only [VCapW, VCapOK] at hcw
    rw [hWt _ (by omega)]
    exact hN.poolT y hy q b hb hi' hib

end

end Vs

/-! ## The step at `VmEptState` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
  Fl4Proofs.P1

set_option maxHeartbeats 4000000 in
/-- **The ASID-pool assign of an unmapped EPT root at `VmEptState`** (module docstring). -/
theorem VmEptState.eptAssign (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (ptr base : U64) {slot : U64} (hsl : IsSlot Z.th slot) (hcap : capAt (L.mem s) slot = ok (.AsidPool ptr base))
    (length : U64) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hex : vspace.extra ex 0#usize = ok (some (cslotAddr (pc.bv, idx))))
    {ptr1 asid0 va0 : U64} (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Ept ptr1 0#u64 false asid0 va0)) :
    vspace.decode st arI s a fl4_abi.label.X86ASIDPoolAssign length slot (.AsidPool ptr base) call buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodeEptAsidPoolAssign (Z := Unit) ptr.bv base.bv (pc.bv, idx)) σ =
          ({(.error e', σ)}, False) ∧
        res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧
        ¬ (ExceptT.run (Fl4Spec.decodeEptAsidPoolAssign (Z := Unit) ptr.bv base.bv (pc.bv, idx)) σ).2 ∧
        ∃ asid σ', (.ok (.poolAssign asid ptr.bv (pc.bv, idx)), σ) ∈
          (ExceptT.run (Fl4Spec.decodeEptAsidPoolAssign (Z := Unit) ptr.bv base.bv (pc.bv, idx)) σ).1 ∧
          EptAssignSpec σ asid ptr.bv (pc.bv, idx) σ' ∧
          ∃ Lst' : U64 → List U64, VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst' D res.2.1 res.2.2 σ') ⦄ := by
  have B := J.1.1
  have Cv := J.1.2
  have C := J.2
  refine WP.spec_mono (JAtZB.eptAssignX arI B C hni ptr base hsl hcap length call buf ex hpc hidx hex hcx) ?_
  rintro ⟨res1, s', a'⟩ (⟨e, e', h1, he, hdec, h2, h2a⟩ |
    ⟨h1, hnf, asid, σ', hmem, hAS, hX', hW0, hSF, hK, hAW, hFE⟩)
  · exact Or.inl ⟨e, e', h1, he, hdec, h2, h2a⟩
  refine Or.inr ⟨h1, hnf, asid, σ', hmem, hAS, ?_⟩
  simp only at hX' hW0 hSF hAW hFE ⊢
  set x := cslotAddr (pc.bv, idx) with hxdef
  -- 1. the restart
  obtain ⟨s1, σ1, Lst1, hs1, hst1, J1⟩ := VmEptState.restart (arI := arI) J hni
  have B1 := J1.1.1
  have Cv1 := J1.1.2
  have C1 := J1.2
  have hct := P1.cur_thread_ok (L := L) s
  obtain ⟨hcur, xct, hkt, -⟩ := B.curRunnable hni hct
  have htcb : Z.th (L.curW s) = some .tcb := (B.xtop.curTcb hcur).1
  have e1 : σ1 = stsAct (updK σ (L.curW s).bv (.tcb { xct with tcbState := .restart })) (L.curW s).bv := by
    have hst := hst1
    rw [hcur, Notif.setThreadState_eq .restart hkt] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  have hk1 : ∀ o, o ≠ (L.curW s).bv → σ1.kheap o = σ.kheap o := by
    intro o ho; rw [e1, stsAct_kheap]; simp [updK, ho]
  have hct1 : σ1.kheap (L.curW s).bv = some (.tcb { xct with tcbState := .restart }) := by
    rw [e1, stsAct_kheap]; simp [updK]
  have har1 : σ1.archState = σ.archState := by rw [e1]; unfold stsAct; split <;> rfl
  -- the spec's step after the restart
  have hX := B.xtop
  obtain ⟨hS, hR, hPt, hPI, -⟩ := hX.fin
  obtain ⟨-, hCR, -, -, -, -, -⟩ := hX.rel
  obtain ⟨hSt, -, -, -, -⟩ := hCR
  have hw := B.vsc slot hsl
  rw [capV_of_capAt hcap] at hw
  simp only [VCapW, VCapOK] at hw
  obtain ⟨cs, hkc, hwf, hslc⟩ := hSt.cnode pc r hpc
  have hcs : cs idx = some (.archObjectCap (.eptCap ptr1.bv 0 none)) := by
    obtain ⟨c, ac, hc, hac, hca⟩ := hslc idx hidx
    have : c = .Ept ptr1 0#u64 false asid0 va0 := by
      have h2 : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok c := hc
      rw [hcx] at h2; exact (by simpa using h2 : capability.Cap.Ept ptr1 0#u64 false asid0 va0 = c).symm
    subst this
    rw [hac, ← hca.2]; rfl
  obtain ⟨fp, hkf, -⟩ := hR.pool ptr hw.1.1
  have hpct : pc.bv ≠ (L.curW s).bv := kheap_ne hkc hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hptct : ptr.bv ≠ (L.curW s).bv := kheap_ne hkf hkt (fun _ h1 h2 => by subst h1; cases h2)
  have F : VsSFr σ1 σ' :=
    vsSFr_eptAssign hst1 hAS (by rw [hk1 _ hpct]; exact hkc) hwf hidx hcs (by rw [hk1 _ hptct]; exact hkf)
  have hFE1 : AssignFE (L.mem s') x ptr1 σ1 σ' := AssignFE.ofTcb hFE hk1 hkt hct1 har1
  have hK1 : KFoot σ1 σ' := KFoot.ofTcb hK hk1 hkt hct1 F.cdt F.orig F.ct
  -- 2. FL4's writes after the restart (`JAtZ.vsPostJ`'s pins)
  have hP := B.xtop.rel.1
  have hact := B.kern.act
  have hF2 : Frame2 (L := L) s s1 (P1.stA (L.curW s)) (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    have h := set_thread_state_frame (L := L) s (L.curW s) sched.TS_RESTART (stA_al hP htcb) hact.1
    rw [hs1, WP.spec_ok] at h; exact h
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := set_thread_state_slots (L := L) Z.th hP s (L.curW s) sched.TS_RESTART htcb hact
    rw [hs1, WP.spec_ok] at h; exact h
  have hkc1 : L.ksb s1 = L.ksb s ∧ L.cpu s1 = L.cpu s := by
    have h := set_thread_state_cases (L := L) s (L.curW s) sched.TS_RESTART
    rw [hs1, WP.spec_ok] at h
    rcases h with rfl | rfl <;> simp
  have hks' : L.ksb s' = L.ksb s := hW0.1
  have pinS : ∀ t, Z.th t = some .tcb → L.mem s' (P1.stA t) = L.mem s1 (P1.stA t) := by
    intro t ht
    have htT := B.thT t ht
    obtain ⟨y1, hy1, hR1⟩ := B1.xtop.ipc.tcb t htT
    obtain ⟨y, hky, hRy⟩ := hX'.ipc.tcb t htT
    obtain ⟨y', hy', hc⟩ := F.tcbF hy1
    rw [hky] at hy'; cases hy'
    have h1 : (L.mem s' (tStA t)).val = (L.mem s1 (tStA t)).val := by rw [hRy.st, hR1.st, hc.st]
    rw [stA_tStA]; exact UScalar.eq_of_val_eq h1
  have pinA : L.mem s' (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) =
      L.mem s1 (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    have a1 := B1.xtop.fin.1.1.1.act
    have a2 := hX'.fin.1.1.1.act
    rw [F.act] at a2
    have e := Sched.ActRel.det a2 a1
    obtain ⟨Q, R, hc, -⟩ := B.xtop.fin.1.1.1.lists
    unfold nodeW at e
    rw [P1.nodeAt_of_ksb hks', P1.nodeAt_of_ksb hkc1.1, ← hc.cur] at e
    exact e
  have hSlot : ∀ y, IsSlot Z.th y → L.mem s' (wordOf y 16#u64) = L.mem s1 (wordOf y 16#u64) ∧
      L.mem s' (wordOf y 24#u64) = L.mem s1 (wordOf y 24#u64) ∧
      (y ≠ x → L.mem s' y = L.mem s1 y ∧ L.mem s' (wordOf y 8#u64) = L.mem s1 (wordOf y 8#u64)) := by
    intro y hy
    obtain ⟨a0, a8, a16, a24⟩ := hSS1 y hy
    obtain ⟨b16, b24, bx⟩ := hSF y hy
    exact ⟨by rw [b16, a16], by rw [b24, a24], fun hne => ⟨by rw [(bx hne).1, a0], by rw [(bx hne).2, a8]⟩⟩
  have hW : P1.WritesIn st s1 s' (VsXW Z (L.ksb s1) x) := by
    refine ⟨hks'.trans hkc1.1.symm, hW0.2.1.trans hkc1.2.symm, fun b hb hn => ?_⟩
    have hslw : ∀ y, IsSlot Z.th y → ∀ k : U64, Off k → b = wordOf y k → L.mem s' b = L.mem s1 b := by
      intro y hy k hk e
      subst e
      obtain ⟨h16, h24, hne⟩ := hSlot y hy
      rcases hk with rfl | rfl | rfl | rfl
      · by_cases ex : y = x
        · exact (hn (Or.inr (Or.inl (by rw [wordOf_zero, ex])))).elim
        · rw [wordOf_zero]; exact (hne ex).1
      · by_cases ex : y = x
        · exact (hn (Or.inr (Or.inr (by rw [ex])))).elim
        · exact (hne ex).2
      · exact h16
      · exact h24
    by_cases hb0 : VsFootW st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 s b
    · rcases hb0 with ⟨y, hy, e | e⟩ | ⟨y, k, hy, hk, e⟩ | hpt | hvw | ⟨t, ht, e⟩ | e
      · exact hslw y hy 0#u64 (Or.inl rfl) (by rw [wordOf_zero]; exact e)
      · exact hslw y hy 8#u64 (Or.inr (Or.inl rfl)) e
      · exact hslw y hy k hk e
      · exact (hn (Or.inl (Or.inl hpt))).elim
      · exact (hn (Or.inl (Or.inr (by rw [hkc1.1]; exact hvw)))).elim
      · subst e; exact pinS t ht
      · subst e; exact pinA
    · have e0 : L.mem s' b = L.mem s b := hW0.2.2 b hb hb0
      have e1 : L.mem s1 b = L.mem s b := hF2 b hb (fun e => hb0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨L.curW s, htcb, UScalar.eq_of_val_eq e⟩)))))) (fun e => hb0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (UScalar.eq_of_val_eq e)))))))
      rw [e0, e1]
  -- the invoked slot's cap
  have hcv0 : capV (L.mem s) x = .Ept ptr1 0#u64 false asid0 va0 := capV_of_capAt hcx
  have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hxs : IsSlot Z.th x := hA.isSlot
  have hcv1 : capV (L.mem s1) x = .Ept ptr1 0#u64 false asid0 va0 := by rw [hSS1.capV hxs]; exact hcv0
  have hcvN : ∃ a1, capV (L.mem s') x = .Ept ptr1 0#u64 true a1 0#u64 ∧ a1 ≠ 0#u64 := by
    obtain ⟨a1, -, -, -, -, h, -, -, -, -, -, h0, -⟩ := hFE; exact ⟨a1, h, h0⟩
  obtain ⟨a1, hcvN, ha1⟩ := hcvN
  have hLk := vsLike_eptAssign ptr1 a1 asid0 va0
  have hcap' : ∀ y, IsSlot Z.th y → y ≠ x → capV (L.mem s') y = capV (L.mem s1) y := by
    intro y hy hne
    obtain ⟨-, -, h⟩ := hSlot y hy
    unfold capV; rw [(h hne).1, (h hne).2]
  have hSF1 : SlotFoot Z.th (L.mem s1) (L.mem s') x := fun y hy =>
    ⟨(hSlot y hy).1, (hSlot y hy).2.1, fun hne => (hSlot y hy).2.2 hne⟩
  have Ap : VsApart (L := L) Z H Cs s1 := ⟨fun q z hq hqC => absurd (B1.hscC q z hq) hqC⟩
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s') := by
    intro y hy
    by_cases e : y = x
    · rw [e, hcvN]; trivial
    · rw [hcap' y hy e]; exact B1.vsc y hy
  -- `VsNamed` after (from `J`'s, at `s`)
  have hvn : Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s') := fun hvx => by
    have hR' : Vs.VsRel Z.P (L.mem s') (L.ksb s) σ' := by rw [← hks']; exact hX'.fin.2.1
    rw [hks']
    exact (B.carry.vsNamed hvx).ofEptAssignF B.vsc hR hPt hPI hR' hX'.fin.2.2.1 hcv0 hSF hFE
      fun q hq i hi hne => by rw [hAW _ (Or.inr ⟨q, hq, i, hi, rfl⟩) hne]; exact or1_and1_ne ptr1
  -- 3. the base
  have B' : JAtZB (L := L) arI AR Z H Cs Ac Lst1 D s' a' σ' :=
    B1.vsStepJXB Ap hpc hidx (TabsArch.empty σ1) (L3' := Z.L3) (L2' := Z.L2) (L1' := Z.L1) hX' F
      (hW.mono fun _ h => Or.inl h) hcap' (by rw [hcv1, hcvN]; exact hLk.1.1) (by rw [hcv1, hcvN]; exact hLk.1.2.1)
      (by rw [hcv1]; rfl) (fun y hy => ⟨(hSlot y hy).1, (hSlot y hy).2.1⟩) hvc
      ⟨subset_rfl, subset_rfl, subset_rfl⟩ hvn
  -- 4. `VcpuCore` and `EptCore`
  have sw : ∀ b, (b = x ∨ b = wordOf x 8#u64) → SlotWd Z.th b := by
    rintro b (rfl | rfl)
    · exact ⟨x, hxs, 0#u64, Or.inl rfl, by rw [wordOf_zero]⟩
    · exact ⟨x, hxs, 8#u64, Or.inr (Or.inl rfl), rfl⟩
  obtain ⟨_, pool, _, _, f, -, -, -, -, -, -, -, hkp1, hkp1', hAK1, -⟩ := id hFE1
  have nV : ∀ u ∈ V, ∀ b, VsXW Z (L.ksb s1) x b → b.val < u.val ∨ u.val + 32768 ≤ b.val := by
    intro u hu b hb
    rcases hb with hb | hb
    · obtain ⟨vx, hvx⟩ := Cv1.vm.spec u hu
      have := B1.vsW_apart (t := u) (n := 32768) (fun o ko hk hne => Cv1.vm.sep u hu o ko hk hne) (Cv1.vm.ks u hu)
        (fun q hq e => by
          obtain ⟨ao, hk, -, -, hnv⟩ := B1.vsFrSpec hq
          rw [e, hvx] at hk; cases hk; exact hnv vx rfl) hb
      omega
    · exact B1.slotWd_vcpu Cv1.vm (sw b hb) u hu
  have nX : ∀ b, VsXW Z (L.ksb s1) x b → ∀ t ∈ X, b.val < t.val ∨ t.val + 4096 ≤ b.val := by
    intro b hb t ht
    rcases hb with hb | hb
    · obtain ⟨es, hxe, -⟩ := C1.rel.obj t ht
      have := B1.vsW_apart (t := t) (n := 4096) (fun o ko hk hne => C1.sep t ht o ko hk hne) (C1.ks t ht)
        (fun q hq e => by
          obtain ⟨ao, hk, -, hne, -⟩ := B1.vsFrSpec hq
          rw [e, hxe] at hk; cases hk; exact hne _ es rfl) hb
      omega
    · exact JAtZB.slotWd_ept B1 C1 b (sw b hb) t ht
  have hv : VKeep (L := L) Z.th s1 s' := by
    intro t ht
    have htT := B1.thT t ht
    obtain ⟨Q, R0, hcq, -⟩ := B1.xtop.fin.1.1.1.lists
    have hT := hcq.tcbs
    have ev := tVcpuA_val hT htT
    refine hW.mem_eq (tVcpuA_aligned hT htT) fun hb => ?_
    rcases hb with hb | hb
    · have hP1 := B1.xtop.fin.1.2
      have hO : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s1 σ1 (tVcpuA t) :=
        Or.inr (Or.inr (Or.inl ⟨t, htT, by omega, by omega⟩))
      have hvo : VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s1) (tVcpuA t) := by
        rcases hb with ⟨q, hq, i, hi, e⟩ | h
        · rw [e]; exact table_vobj hP1.pt hq hi _
        · exact vsWrite_vobj hP1.vs h
      exact hP1.disj _ hO hvo
    · exact B1.slotWd_tcb (sw _ hb) ht (by omega) (by omega) rfl
  have hvk : ∀ u ∈ V, σ'.kheap u.bv = σ1.kheap u.bv := fun u hu => by
    obtain ⟨vx, hvx⟩ := Cv1.vm.spec u hu
    have hne : u ≠ pool := fun e => by subst e; rw [hkp1] at hvx; cases hvx
    exact hAK1 u ⟨_, hvx⟩ hne
  have hrv : ∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ1.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM := fun o x' ho hx => by
    rcases F.kh o with e | ⟨a0, a1, -, h1, -⟩ | ⟨r', cs0, cs1, -, h1⟩ | ⟨y0, y1, h0, h1, hco⟩
    · exact ⟨x', by rw [← e]; exact ho, hx⟩
    · rw [h1] at ho; cases ho
    · rw [h1] at ho; cases ho
    · rw [h1] at ho; cases ho; exact ⟨y0, h0, by rw [← hco.1]; exact hx⟩
  have hnv : ∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ1.kheap p = some (.archObj (.vcpu vs)) := fun p vs hp =>
    archKept_of hAK1 hK1 (fun e => by subst e; rw [hkp1'] at hp; cases hp) hp
  have hcs' : ∀ y, IsSlot Z.th y → capV (L.mem s') y = capV (L.mem s1) y ∨
      (shape (capV (L.mem s') y) = shape (capV (L.mem s1) y) ∧
        ∃ (p l : U64) (mm : Bool) (a v : U64), capV (L.mem s') y = .Ept p l mm a v) := by
    intro y hy
    by_cases e : y = x
    · right; rw [e]
      exact ⟨by rw [hcvN, hcv1]; exact hLk.1.1, _, _, _, _, _, hcvN⟩
    · exact Or.inl (hcap' y hy e)
  have Cv' : VcpuCore (L := L) V Z H s' σ' :=
    Cv1.ofWE B1 B' hW hcs' nV (fun b hb => by
      rcases hb with hb | hb
      · exact B1.vsW_head hb
      · exact B1.slotWd_head (sw b hb)) hv hvk (eptAssign_size hFE1 hK1) hrv hnv
  have hev : ptr1.val % 2 = 0 := by
    have h := C1.exte.cap _ hxs
    rw [hcv1] at h
    have hp := (C1.rel.place ptr1 h).1
    omega
  have hX'E : JExtEpt (L := L) X Z.th s' := ⟨fun y hy => by
    by_cases e : y = x
    · rw [e, hcvN]
      have h := C1.exte.cap x hxs
      rw [hcv1] at h
      exact h
    · rw [hcap' y hy e]; exact C1.exte.cap y hy, ⟨fun y hy p l a v hc => by
    by_cases e : y = x
    · rw [e, hcvN] at hc
      obtain ⟨-, -, -, -, rfl⟩ := capability.Cap.Ept.inj hc
      exact lt_of_eq_of_lt (rfl : (0#u64 : U64).val = 0) (by norm_num)
    · rw [hcap' y hy e] at hc; exact C1.exte.vtop.1 y hy p l a v hc, fun y hy p sz r d a v hc => by
    by_cases e : y = x
    · rw [e, hcvN] at hc; cases hc
    · rw [hcap' y hy e] at hc; exact C1.exte.vtop.2 y hy p sz r d a v hc⟩, fun y hy p l a v hc => by
    by_cases e : y = x
    · rw [e, hcvN] at hc
      obtain ⟨-, -, -, rfl, -⟩ := capability.Cap.Ept.inj hc
      exact ha1
    · rw [hcap' y hy e] at hc; exact C1.exte.anz y hy p l a v hc⟩
  have C' : EptCore (L := L) X XL Z.th s' σ' := C1.assignE hxs hcv1 hev hW nX hSF1 hFE1 hK1 hX'E
  exact ⟨Lst1, ⟨B', Cv'⟩, C'⟩

set_option maxHeartbeats 4000000 in
/-- **The extended decoder and FL4's `vspace.decode` at `X86ASIDPoolAssign` with an unmapped EPT root, at
`VmEptState`** (module docstring; P3/EptAssignJ's `decV_asidPoolEpt` + `VmEptState.eptAssign`). -/
theorem eptAssign_decode_vmEpt (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (ptr base : U64) {slot : U64} (hsl : IsSlot Z.th slot) (hcap : capAt (L.mem s) slot = ok (.AsidPool ptr base))
    (length : U64) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hex : vspace.extra ex 0#usize = ok (some (cslotAddr (pc.bv, idx))))
    {ptr1 asid0 va0 : U64} (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Ept ptr1 0#u64 false asid0 va0))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign)
    (fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    vspace.decode st arI s a fl4_abi.label.X86ASIDPoolAssign length slot (.AsidPool ptr base) call buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧
        (specDecV fp slbl args ci sl (.AsidPool ptr base)
          ((absCap (.Ept ptr1 0#u64 false asid0 va0), (pc.bv, idx)) :: rest) buffer).run σ =
          ({(.error e', σ)}, False) ∧
        res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ asid σ',
        DecOut (specDecV fp slbl args ci sl (.AsidPool ptr base)
          ((absCap (.Ept ptr1 0#u64 false asid0 va0), (pc.bv, idx)) :: rest) buffer) σ
          (.ept (.poolAssign asid ptr.bv (pc.bv, idx))) ∧
        EptAssignSpec σ asid ptr.bv (pc.bv, idx) σ' ∧
        ∃ Lst' : U64 → List U64, VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst' D res.2.1 res.2.2 σ') ⦄ := by
  have hd : specDecV fp slbl args ci sl (.AsidPool ptr base)
      ((absCap (.Ept ptr1 0#u64 false asid0 va0), (pc.bv, idx)) :: rest) buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4InvocationV.ept
        (Fl4Spec.decodeEptAsidPoolAssign ptr.bv base.bv (pc.bv, idx)) :=
    decV_asidPoolEpt hl fp args ci sl ptr1.bv (pc.bv, idx) rest buffer
  rw [hd]
  refine WP.spec_mono (VmEptState.eptAssign J hni ptr base hsl hcap length call buf ex hpc hidx hex hcx) ?_
  rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, hnf, asid, σ', hmem, hAS, hJ⟩)
  · exact Or.inl ⟨e, e', h1, he, run_liftME_err hdec, h2, h2a⟩
  · exact Or.inr ⟨h1, asid, σ', DecOut.liftME ⟨hmem, hnf⟩, hAS, hJ⟩
end

end

end Fl4Proofs.P3

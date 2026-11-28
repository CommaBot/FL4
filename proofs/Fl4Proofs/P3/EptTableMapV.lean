/-
P3 (line mmuAD, gen 42b11): **the EPT table map at `VmEptState`** — FL4's `ept::decode` map arm (crates/fl4-core/src/
ept.rs l. 294-310: the caller's restart, `s.write(e, paddr(ptr) | 7)`, `set_cap` of the mapped cap) against the
extended spec's `decodeEptInvocation` then `setThreadState cur Restart` and `performEptInvocation (.tableMap …)`
(Fl4Spec/Ext/VirtEptInv l. 160-173, l. 221-223: `storeGuestEntry tbl i (encode (.table (addrFromPPtr ptr)))`, then
`setCap (eptCap ptr level (some (asid, gpa)))`), modelled on the EPT pool-assign stack (P3/EptAssignRel, EptAssignJ,
EptAssignV).

* Spec: **`performTableMap_eq`** (the perform's single outcome: the guest-table object `t` with the entry written,
  then the CNode slot), `EptTableMapSpec` (restart, then perform), `vsSFr_setCnodeSlot` / `keepC_setCnodeSlot` /
  `cnK_setCnodeSlot` (one CNode slot rewritten is a `VsSFr` / `KeepC` / `CnK` step), `GPath.ofArch` (walk paths kept
  by a step keeping the ASID table and every arch object, the restart), `tblEntry_ptr` (`ptrFromPAddr` of the table
  entry's address bits is `ptr` when `PaM ptr` holds).
* **Base half** (inside `VmEptState.tableMap`): after P3/EptSetRoot's `VmEptState.restart` (`s1`, `σ1`):
  1. FL4's entry word: P3/EptStep1's `JAtZB.eptWr` (σ unchanged);
  2. the spec's `storeGuestEntry`: P3/JAtZBVcpuX's **`XTopAt.archSpec`** (gen 42b11: `XTopAt.vcpuSpec` generalised in
     place to a guest-table object) and P3/JAtZBVcpu's `JAtZB.arFrS` with **`arFr_arch`** (`arFr_vcpu` generalised in
     place);
  3. the `set_cap` / `setCap` pair: `XTopAt.slotStep` (P3/XTopStep; `CRel` / `FinInv` / `MdbOKV` by P3/VsDecFrame's
     `crelM_after`, `StateRel` / `SlotsValid` by `set_cap_refines`, the new cap `VsLike` the old by P3/EptAssignJ's
     **`vsLike_ept`** (`vsLike_eptAssign` generalised in place)), then P3/JAtZBRecap's `JAtZB.vsStepJXB` (`VsNamed`
     after by `JAtZB.vsShr`: no slot changes its VSpace key, no arch object changes).
* `VcpuCore` by `VcpuCore.ofW` (the entry word: `EptCore.apartV`, `JAtZB.eptHead`, `JAtZB.oobjX`) then
  `VcpuCore.ofWE` (the slot words: `slotWd_vcpu` / `slotWd_head` / `slotWd_tcb`); **`EptCore` by P3/EptTableMap's
  `EptCore.tableMap`** at `s1`, `σ1` (its `htg` from `PaM ptr`, `hgk` from `gKey_idem`, its `CnK` from the spec's
  `setCap`; the decoded walk path moved to `σ1` by `GPath.ofArch`).
* **`VmEptState.tableMap`**: from `VmEptState` at an `Entered` spec state, the invoked unmapped `Ept ptr level` cap
  in a CNode slot, P3/EptMapDec's decode hypotheses (level 39 / 30 / 21, the map label, `len ≥ 2`, `ex[0]` non-null,
  the masked guest address below `2^47`) and `PaM ptr` (below): `ept.decode` returns `res`, and either both sides
  fail with related errors, FL4's state unchanged, or the spec decodes `.tableMap …` (single outcome), the restart +
  perform has the single outcome `σ'`, and `VmEptState` holds at FL4's state after and `σ'`.
* **`eptTableMap_decode_vmEpt`**: the same through `syscall.decode_invocation` and the extended decoder
  `fl4DecodeInvocationV` (P3/JAtZV3EptE's `zv_sysdec_ept` / `zv_decV_ept`), spec arguments by `VArgs`.

Gen 42b12: the former case hypotheses **`hpa : PaM ptr 4503599627366400`** (the new table's physical address 4 KiB
aligned and below `2^52`, so the entry FL4 writes names `ptr` again: `EptCore.tableMap`'s `htg`) and **`hlv`** (level
39 / 30 / 21) are dropped from both tops (statements changed in place): both come from the Architect's new field
`EptCore.tbl` through P3/EptStep1's `EptCore.capTbl` (the invoked cap's table is in `X` by `exte`, at the cap's level by
`capL`, with `XL ∈ {0, 39, 30, 21}` and `PaM`; level 0 is excluded by `h0`).

Gen 42b13 (the Architect's `hz0` decision (i)): both tops take `hxe : IsSlot Z.th (exAt ex 0)` (the extra cap is a
slot cap, so `JExtEpt.anz` gives the root's ASID nonzero, `MapDecOut`; `EptCore.tableMap` takes `ha1 : asid1 ≠ 0`
for the new mapped cap's `anz`); statements changed in place.

No named premise; the spec is not touched. No `sorry`; only the three standard axioms. New file; root import after
`P3.EptTableMap`.
-/
import Fl4Proofs.P3.EptTableMap
import Fl4Proofs.P3.EptAssignV
import Fl4Proofs.P3.JAtZV3SlotIo
import Fl4Proofs.P3.JAtZBVcpuX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Spec side -/

section Spec
open Fl4Spec Fl4Proofs.P3.Notif

/-- **The spec's perform of a table map** (`performEptInvocation (.tableMap …)`): the entry `i` of the guest table
`t` written with the table entry of `ptr`, then the CNode slot `(pc, idx)` set to the mapped cap. -/
theorem performTableMap_eq {σ : State Unit} {pc : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool}
    (hk : σ.kheap pc = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r)
    {t : ObjRef} {l : Nat} {es : BitVec 9 → Word} (ht : σ.kheap t = some (.archObj (.ept l es)))
    (ptr : ObjRef) (lv : Nat) (i : BitVec 9) (asid gpa : ObjRef) :
    performEptInvocation (Z := Unit) (.tableMap ptr lv (pc, idx) t i asid gpa) σ =
      ({((), setCnodeSlot (updK σ t (.archObj (.ept l (Function.update es i
          (GuestPte.encode virtKind (.table (addrFromPPtr ptr))))))) pc r cs idx
        (.archObjectCap (.eptCap ptr lv (some (asid, gpa)))))}, False) := by
  have htc : t ≠ pc := Endp.kheap_ne ht hk (fun _ h1 h2 => by subst h1; cases h2)
  have hs : storeGuestEntry (Z := Unit) t i (GuestPte.encode virtKind (.table (addrFromPPtr ptr))) σ =
      ({((), updK σ t (.archObj (.ept l (Function.update es i
        (GuestPte.encode virtKind (.table (addrFromPPtr ptr)))))))}, False) := by
    unfold storeGuestEntry
    rw [Notif.nd_bind_one (getEpt_eq ht)]
    exact setObject_eq ht rfl
  unfold performEptInvocation
  dsimp only
  rw [Notif.nd_bind_one hs]
  have hk' : (updK σ t (.archObj (.ept l (Function.update es i
      (GuestPte.encode virtKind (.table (addrFromPPtr ptr))))))).kheap pc = some (.cnode r cs) := by
    simp [updK, htc.symm, hk]
  exact setCap_cnode _ hk' hwf hidx

/-- The spec after the table map's decode: `set_thread_state cur Restart`, then the perform, with the single outcome
`σ'`. -/
def EptTableMapSpec (σ : State Unit) (ptr : ObjRef) (lv : Nat) (sl : CslotPtr) (t : ObjRef) (i : BitVec 9)
    (asid gpa : ObjRef) (σ' : State Unit) : Prop :=
  (setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
    performEptInvocation (.tableMap ptr lv sl t i asid gpa)) σ = ({((), σ')}, False)

/-- One CNode slot rewritten is a `VsSFr` step. -/
theorem vsSFr_setCnodeSlot {σ : State Unit} {pc : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool}
    (hk : σ.kheap pc = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r) (a : Cap) :
    VsSFr σ (setCnodeSlot σ pc r cs idx a) := by
  apply VsSFr.of_eq
  unfold setCnodeSlot
  refine vsF_upd hk ?_ ?_
  · simp [aType, hwf, wf_update _ hwf hidx]
  · rfl

/-- One CNode slot rewritten is a `KeepC` step. -/
theorem keepC_setCnodeSlot {σ : State Unit} {pc : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool}
    (hk : σ.kheap pc = some (.cnode r cs)) (a : Cap) : Ipc.KeepC σ (setCnodeSlot σ pc r cs idx a) := by
  intro q
  by_cases e : q = pc
  · subst e
    exact Or.inr ⟨r, cs, Function.update cs idx (some a), hk, by simp [setCnodeSlot]⟩
  · exact Or.inl (by simp [setCnodeSlot, e])

/-- One CNode slot rewritten by `setCap` is a `CnK` step. -/
theorem cnK_setCnodeSlot {σ : State Unit} {pc : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool}
    (hk : σ.kheap pc = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r) (a : Cap) :
    Ipc.CnK σ (setCnodeSlot σ pc r cs idx a) := by
  have h := Ipc.nkn_setCap a (pc, idx) σ ((), setCnodeSlot σ pc r cs idx a)
    (by rw [setCap_cnode a hk hwf hidx]; exact Set.mem_singleton _)
  exact h

end Spec

/-- **Walk paths across a step keeping the ASID table and every arch object** (the restart). -/
theorem GPath.ofArch {σ σ' : Fl4Spec.State Unit} (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hk : ∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = some (.archObj ao))
    {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex} {gpa : Fl4Spec.Word} {l : Nat} {u : Fl4Spec.ObjRef}
    (h : GPath σ hi lo gpa l u) : GPath σ' hi lo gpa l u := by
  induction h with
  | root hp h1 =>
    obtain ⟨p, f, h1', h2, h3⟩ := hp
    exact .root ⟨p, f, by rw [hat]; exact h1', hk _ _ h2, h3⟩ h1
  | step _ hkt hc hw ih => exact .step ih (hk _ _ hkt) hc hw

/-- **The table entry FL4 writes names `ptr` again** when `ptr`'s physical address is a 4 KiB-aligned address below
`2^52` (`PaM`; `EptCore.tableMap`'s `htg`). -/
theorem tblEntry_ptr {ptr : U64} (hpa : Vs.PaM ptr 4503599627366400#u64) :
    Fl4Spec.ptrFromPAddr (Fl4Spec.GuestPte.encode Fl4Spec.virtKind (.table (Fl4Spec.addrFromPPtr ptr.bv)) &&&
      Fl4Spec.guestPteAddress) = ptr.bv := by
  have e : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE).bv = ptr.bv - Fl4Spec.pptrBase := by
    rw [core.num.U64.wrapping_sub_bv_eq, pptrBase_bv]
  have hx : Fl4Spec.addrFromPPtr ptr.bv &&& Fl4Spec.guestPteAddress = Fl4Spec.addrFromPPtr ptr.bv := by
    have h := congrArg UScalar.bv hpa
    rw [UScalar.bv_and] at h
    have h2 : (ptr.bv - Fl4Spec.pptrBase) &&& Fl4Spec.guestPteAddress = ptr.bv - Fl4Spec.pptrBase := by
      rw [← e]; exact h
    exact h2
  show ((Fl4Spec.addrFromPPtr ptr.bv ||| 7) &&& Fl4Spec.guestPteAddress) + Fl4Spec.pptrBase = ptr.bv
  have h7 : ((7 : BitVec 64) &&& Fl4Spec.guestPteAddress) = 0 := by decide
  have hz0 : ∀ y : BitVec 64, y ||| 0 = y := fun y => by simp
  rw [BitVec.and_or_distrib_right, hx, h7, hz0]
  unfold Fl4Spec.addrFromPPtr
  exact BitVec.sub_add_cancel _ _

/-! ## The table map at `VmEptState` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
  Fl4Proofs.P1

set_option maxHeartbeats 4000000 in
/-- **The EPT table map at `VmEptState`** (module docstring). -/
theorem VmEptState.tableMap (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    {lbl len ptr level asid va : U64} (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Ept ptr level false asid va))
    (h0 : level ≠ 0#u64)
    (hu : lbl.val ≠ (Fl4Spec.eptTableLabels level.val).2) (hm : lbl.val = (Fl4Spec.eptTableLabels level.val).1)
    (hl : ¬ len.val < 2) (hz : exAt ex 0 ≠ 0#u64) (hxe : IsSlot Z.th (exAt ex 0)) {i : U64}
    (hsa : msg.syscall_arg st s (L.curW s) buf 0#u64 = ok i)
    (hg : ¬ (i.bv &&& ~~~((1#64 <<< level.val) - 1)) ≥ Fl4Spec.guestGpaLimit)
    (args : List Fl4Spec.Data) (ha0 : args.getD 0 0 = i.bv) (hn : ¬ args.length < 2)
    (sl0 : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    ∃ g : U64, g.bv = (i.bv &&& ~~~((1#64 <<< level.val) - 1)) ∧ g.val < 2 ^ 47 ∧
    ∃ res, ept.decode st arI s a lbl len (.Ept ptr level false asid va) (cslotAddr (pc.bv, idx)) buf ex = ok res ∧
      ((∃ e e', res = (.Err e, s, a) ∧ ErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodeEptInvocation (Z := Unit) lbl.bv args (pc.bv, idx) (.eptCap ptr.bv level.val none)
          ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest)) σ = ({(.error e', σ)}, False)) ∨
      (res.1 = .Ok () ∧ ∃ (t : Fl4Spec.ObjRef) (asid1 : Fl4Spec.ObjRef) (σ' : Fl4Spec.State Unit),
        ExceptT.run (Fl4Spec.decodeEptInvocation (Z := Unit) lbl.bv args (pc.bv, idx) (.eptCap ptr.bv level.val none)
          ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest)) σ =
          ({(.ok (.tableMap ptr.bv level.val (pc.bv, idx) t (Fl4Spec.guestIndex g.bv level.val) asid1 g.bv), σ)},
            False) ∧
        EptTableMapSpec σ ptr.bv level.val (pc.bv, idx) t (Fl4Spec.guestIndex g.bv level.val) asid1 g.bv σ' ∧
        ∃ Lst' : U64 → List U64, VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst' D res.2.1 res.2.2 σ')) := by
  have B := J.1.1
  have C := J.2
  -- gen 42b12: the level range and `PaM ptr` from `EptCore.tbl` (`capTbl`)
  have hxs0 : IsSlot Z.th (cslotAddr (pc.bv, idx)) :=
    AbsSlot.isSlot (⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩ : AbsSlot Z.th (pc.bv, idx))
  obtain ⟨-, hlv4, hpa⟩ := C.capTbl hxs0 (capV_of_capAt hcx)
  have hlv : level.val = 39 ∨ level.val = 30 ∨ level.val = 21 := by
    rcases hlv4 with h | h
    · exact absurd (UScalar.eq_of_val_eq (by rw [h]; rfl) : level = 0#u64) h0
    · exact h
  have hct := P1.cur_thread_ok (L := L) s
  obtain ⟨g, hgb, hgv, res, hdec, hout⟩ := C.mapDec (arI := arI) B.xtop.fin.2.1 a (cslotAddr (pc.bv, idx)) buf ex
    h0 hlv hu hm hl hz hxe hct hsa hg args ha0 hn (pc.bv, idx) sl0 rest
  refine ⟨g, hgb, hgv, res, hdec, ?_⟩
  rcases hout with ⟨e, e', hres, he, ho⟩ |
    ⟨t, asid1, ent, ht, hXt, ha20, hA1, -, -, -, -, hpath, -, ⟨es0, hk0, -⟩, ho, s2, hs2, hres⟩
  · exact Or.inl ⟨e, e', hres, he, ho⟩
  subst hres
  set x := cslotAddr (pc.bv, idx) with hxdef
  set gi := Fl4Spec.guestIndex g.bv level.val with hgi
  -- 1. the restart
  obtain ⟨s1, σ1, Lst1, hs1, hst1, J1⟩ := VmEptState.restart (arI := arI) J hni
  have e21 : s1 = s2 := ok_inj (hs1.symm.trans hs2)
  subst e21
  have B1 := J1.1.1
  have Cv1 := J1.1.2
  have C1 := J1.2
  obtain ⟨hcur, xct, hkt, -⟩ := B.curRunnable hni hct
  have e1 : σ1 = stsAct (updK σ (L.curW s).bv (.tcb { xct with tcbState := .restart })) (L.curW s).bv := by
    have hst := hst1
    rw [hcur, Notif.setThreadState_eq .restart hkt] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  have hk1 : ∀ o, o ≠ (L.curW s).bv → σ1.kheap o = σ.kheap o := by
    intro o ho; rw [e1, stsAct_kheap]; simp [updK, ho]
  have har1 : σ1.archState = σ.archState := by rw [e1]; unfold stsAct; split <;> rfl
  -- the objects
  have hP : Placed Z.th := B.xtop.rel.1
  have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hxs : IsSlot Z.th x := hA.isSlot
  have hcv0 : capV (L.mem s) x = .Ept ptr level false asid va := capV_of_capAt hcx
  obtain ⟨cs, hkc, hwf, -⟩ := B.xtop.rel.2.1.1.cnode pc r hpc
  have htct : t.bv ≠ (L.curW s).bv := kheap_ne hk0 hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hpct : pc.bv ≠ (L.curW s).bv := kheap_ne hkc hkt (fun _ h1 h2 => by subst h1; cases h2)
  have htpc : t.bv ≠ pc.bv := kheap_ne hk0 hkc (fun _ h1 h2 => by subst h1; cases h2)
  have hk01 : σ1.kheap t.bv = some (.archObj (.ept (XL t) es0)) := by rw [hk1 _ htct]; exact hk0
  have hkc1 : σ1.kheap pc.bv = some (.cnode r cs) := by rw [hk1 _ hpct]; exact hkc
  have hka1 : ∀ p ao, σ.kheap p = some (.archObj ao) → σ1.kheap p = some (.archObj ao) := by
    intro p ao hp
    have : p ≠ (L.curW s).bv := fun e => by rw [e, hkt] at hp; cases hp
    rw [hk1 _ this]; exact hp
  -- the spec states
  set E := Fl4Spec.GuestPte.encode Fl4Spec.virtKind (.table (Fl4Spec.addrFromPPtr ptr.bv)) with hE
  set σ2 := updK σ1 t.bv (.archObj (.ept (XL t) (Function.update es0 gi E))) with hσ2
  have hkc2 : σ2.kheap pc.bv = some (.cnode r cs) := by simp [hσ2, updK, htpc.symm, hkc1]
  have hk2t : σ2.kheap t.bv = some (.archObj (.ept (XL t) (Function.update es0 gi E))) := by simp [hσ2, updK]
  have hoth2 : ∀ q, q ≠ t.bv → σ2.kheap q = σ1.kheap q := fun q hq => by simp [hσ2, updK, hq]
  set nc : Fl4Spec.Cap := .archObjectCap (.eptCap ptr.bv level.val (some (asid1.bv, g.bv))) with hnc
  have hspec : EptTableMapSpec σ ptr.bv level.val (pc.bv, idx) t.bv gi asid1.bv g.bv
      (setCnodeSlot σ2 pc.bv r cs idx nc) := by
    unfold EptTableMapSpec
    rw [Notif.nd_bind_one hst1, performTableMap_eq hkc1 hwf hidx hk01] <;> rfl
  -- FL4's states
  have hcl := hcx
  rw [capAt_words] at hcl
  have hew0 := decode_encWf hcl
  have hcan : Canonical ptr := hew0.1
  have hl64 : level.val < 64 := hew0.2.1
  set v := core.num.U64.wrapping_sub ptr layout.PPTR_BASE ||| 7#u64 with hv
  set w := eptA t gi with hw
  have hpl := C1.rel.place t ht
  have ew : w.val = t.val + 8 * gi.toNat := eptA_val hpl.2 gi
  have hgi9 := gi.isLt
  have hal : P1.Aligned w := by unfold P1.Aligned; rw [ew]; omega
  -- 2. FL4's entry word, then the spec's `storeGuestEntry`
  obtain ⟨B2, hSS2⟩ := B1.eptWr C1 ht hal (by rw [ew]; omega) (by rw [ew]; omega) v
  set s2' := L.wr s1 w v with hs2'
  have hX2 : XTopAt (L := L) AR Z s2' a σ2 := B2.xtop.archSpec hk01 (Or.inr ⟨_, _, rfl⟩)
    (.ept (XL t) (Function.update es0 gi E)) rfl
  have B2' : JAtZB (L := L) arI AR Z H Cs Ac Lst1 D s2' a σ2 := B2.arFrS (arFr_arch hk01 (.ept (XL t) (Function.update es0 gi E)) rfl) hX2
  -- 3. the `set_cap` / `setCap` pair
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := set_thread_state_slots (L := L) Z.th hP s (L.curW s) sched.TS_RESTART (B.xtop.curTcb hcur).1
      B.kern.act
    rw [hs1, WP.spec_ok] at h; exact h
  have hcv1 : capV (L.mem s1) x = .Ept ptr level false asid va := by rw [hSS1.capV hxs]; exact hcv0
  have hcv2 : capV (L.mem s2') x = .Ept ptr level false asid va := by rw [hSS2.capV hxs]; exact hcv1
  have hcx2 : capAt (L.mem s2') x = ok (.Ept ptr level false asid va) := by rw [capAt_capV, hcv2]
  set c : capability.Cap := .Ept ptr level true asid1 g with hc
  have hew : EncWf c := ⟨hcan, hl64, ha20, by omega⟩
  have hca : CapRel c nc := ⟨trivial, rfl⟩
  obtain ⟨hSt2, hSV2, -, -, -⟩ := hX2.rel.2.1
  have hSC := set_cap_refines (L := L) Z.th s2' σ2 hSt2 hSV2 hP hpc hidx c nc hca trivial hew
  rw [set_cap_eq, WP.spec_ok] at hSC
  obtain ⟨σ3, hsc, hSt3, hSV3, -, -, -, -⟩ := hSC
  have hσ3 : σ3 = setCnodeSlot σ2 pc.bv r cs idx nc := by
    rw [setCap_cnode nc hkc2 hwf hidx] at hsc
    have := congrArg Prod.fst hsc
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst hσ3
  set s3 := wrCap (L := L) s2' x c with hs3
  have hF3 := set_cap_foot (L := L) hP hxs s2' c hew
  rw [set_cap_eq, WP.spec_ok] at hF3
  obtain ⟨hSF3, hcv3⟩ := hF3
  have hfx := hxs.fit hP
  have hal32 := hxs.align hP
  have hWF := set_cap_frame (L := L) s2' x c (by omega) (by omega)
  rw [set_cap_eq, WP.spec_ok] at hWF
  have h8 : (wordOf x 8#u64).val = x.val + 8 := wa8_val (by omega)
  have hW3 : P1.WritesIn st s2' s3 (fun b => b = x ∨ b = wordOf x 8#u64) := by
    refine ⟨hWF.1, hWF.2.1, fun b hb hn => hWF.2.2 b hb fun hr => hn (by
      obtain ⟨g1, g2⟩ := hr
      have hb8 : b.val % 8 = 0 := hb
      by_cases e : b.val = x.val
      · exact Or.inl (UScalar.eq_of_val_eq e)
      · exact Or.inr (UScalar.eq_of_val_eq (by rw [h8]; omega)))⟩
  have hks3 : L.ksb s3 = L.ksb s2' := hW3.1
  have hcap3 : ∀ y, IsSlot Z.th y → y ≠ x → capV (L.mem s3) y = capV (L.mem s2') y := fun y hy hne => by
    unfold capV; rw [((hSF3 y hy).2.2 hne).1, ((hSF3 y hy).2.2 hne).2]
  have hLk : VsLike (capV (L.mem s3) x) (capV (L.mem s2') x) := by
    rw [hcv3, hcv2]; exact vsLike_ept ptr level asid1 g asid va
  have hK3 : KFoot σ2 (setCnodeSlot σ2 pc.bv r cs idx nc) := KFoot.cnode hkc2 hwf idx nc
  obtain ⟨-, hCR2, hFI2, -, hMO2, -, -⟩ := hX2.rel
  obtain ⟨hCR3, hFI3, hMO3⟩ := crelM_after hCR2 hFI2 hMO2 hcx2 hSt3 hSV3 hSF3 (by rw [← hcv2]; exact hLk) hK3 rfl
  have hTS : ∀ t', Z.th t' = some .tcb → capAt (L.mem s3) (slotOf t' 1) = capAt (L.mem s2') (slotOf t' 1) := by
    intro t' ht'
    have hs : IsSlot Z.th (slotOf t' 1) := ⟨t', 1, Or.inr ⟨ht', by simp [tcbSlots]⟩, rfl⟩
    have he : cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 1) = slotOf t' 1 := by
      show slotAddr t'.bv (Fl4Spec.ofBl _) = _
      rw [slotAddr_ofBl, tcbCnodeIndex_blVal 1 (by decide)]
    have hne : slotOf t' 1 ≠ x := fun e => cnode_slot_ne_tcb hP hpc hidx ht' 1 (by decide) (by rw [he, e])
    rw [capAt_capV, capAt_capV, hcap3 _ hs hne]
  have hSW : ∀ b, (b = x ∨ b = wordOf x 8#u64) → SlotWd Z.th b := by
    rintro b (rfl | rfl)
    · exact ⟨x, hxs, 0#u64, Or.inl rfl, by rw [wordOf_zero]⟩
    · exact ⟨x, hxs, 8#u64, Or.inr (Or.inl rfl), rfl⟩
  have hX3 : XTopAt (L := L) AR { Z with G := Z.G } s3 a (setCnodeSlot σ2 pc.bv r cs idx nc) :=
    XTopAt.slotStep hX2 (hW3.mono hSW) (cnK_setCnodeSlot hkc2 hwf hidx nc) (keepC_setCnodeSlot hkc2 nc)
      hCR3 hFI3 hMO3 hTS
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s3) := fun y hy => by
    by_cases e : y = x
    · rw [e, hcv3]; trivial
    · rw [hcap3 y hy e]; exact B2'.vsc y hy
  have hvn : Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s3) (L.ksb s3) :=
    B2'.vsShr (G' := Z.G) hX3 hks3 (VsKeep.of_vk fun y hy => by
      by_cases e : y = x
      · rw [e, hcv3, hcv2]; exact ⟨rfl, rfl⟩
      · rw [hcap3 y hy e]; exact ⟨rfl, rfl⟩)
      (ArchShr.of_keep rfl fun q ao hq => by
        have hq' : q ≠ pc.bv := fun e => by rw [e, hkc2] at hq; cases hq
        simp [setCnodeSlot, hq'])
  have B' : JAtZB (L := L) arI AR Z H Cs Ac Lst1 D s3 a (setCnodeSlot σ2 pc.bv r cs idx nc) :=
    B2'.vsStepJXB ⟨B2'.scOut⟩ hpc hidx (TabsArch.empty σ2) (L3' := Z.L3) (L2' := Z.L2) (L1' := Z.L1) hX3
      (vsSFr_setCnodeSlot hkc2 hwf hidx nc) (hW3.mono fun b hb => Or.inl (Or.inr hb)) hcap3
      (by rw [hcv3, hcv2]; exact (vsLike_ept ptr level asid1 g asid va).1.1)
      (by rw [hcv3, hcv2]; exact (vsLike_ept ptr level asid1 g asid va).1.2.1)
      (by rw [hcv2]; rfl) (fun y hy => ⟨(hSF3 y hy).1, (hSF3 y hy).2.1⟩) hvc
      ⟨subset_rfl, subset_rfl, subset_rfl⟩ hvn
  -- 4. `VcpuCore`: the entry word, then the slot words
  have hw12 : P1.WritesIn st s1 s2' (· = w) := P1.writesIn_wr hal
  obtain ⟨Q, R0, hcq, -⟩ := B1.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  have nV1 : ∀ u ∈ V, ∀ b, b = w → b.val < u.val ∨ u.val + 32768 ≤ b.val := by
    intro u hu b hb
    subst hb
    rcases C1.apartV Cv1.vm t ht u hu with h | h <;> omega
  have hh1 : ∀ b, b = w → b ≠ P1.vHeadA st s1 := by
    intro b hb he
    subst hb
    have h2 : w.val = (P1.vHeadA st s1).val := by rw [he]
    rcases B1.eptHead C1 ht with h | h <;> omega
  have hv1 : VKeep (L := L) Z.th s1 s2' := by
    intro t' ht'
    have htT := B1.thT t' ht'
    have ev := tVcpuA_val hT htT
    refine hw12.mem_eq (tVcpuA_aligned hT htT) fun he => ?_
    have hO : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s1 σ1 (tVcpuA t') :=
      Or.inr (Or.inr (Or.inl ⟨t', htT, by omega, by omega⟩))
    have h2 : (tVcpuA t').val = w.val := by rw [he]
    rcases B1.oobjX C1 ht hO with h | h <;> omega
  have hvt : ∀ u ∈ V, u.bv ≠ t.bv := fun u hu e => by
    obtain ⟨vx, hvx⟩ := Cv1.vm.spec u hu
    rw [e, hk01] at hvx; cases hvx
  have Cv2 : VcpuCore (L := L) V Z H s2' σ2 :=
    Cv1.ofW B1 B2' hw12 hSS2 nV1 hh1 hv1 (fun u hu => hoth2 _ (hvt u hu))
      (fun o ko' ho => by
        by_cases e : o = t.bv
        · subst e; rw [hk2t] at ho; cases ho
          exact ⟨_, hk01, by rw [ept_bits, ept_bits]⟩
        · rw [hoth2 _ e] at ho; exact ⟨ko', ho, rfl⟩)
      (fun o x' ho hx => by
        have e : o ≠ t.bv := fun e => by rw [e, hk2t] at ho; cases ho
        rw [hoth2 _ e] at ho; exact ⟨x', ho, hx⟩)
      (fun p vs hp => by
        have e : p ≠ t.bv := fun e => by rw [e, hk2t] at hp; cases hp
        rw [hoth2 _ e] at hp; exact hp)
  have hothc : ∀ q, q ≠ pc.bv → (setCnodeSlot σ2 pc.bv r cs idx nc).kheap q = σ2.kheap q :=
    fun q hq => by simp [setCnodeSlot, hq]
  have hvpc : ∀ u ∈ V, u.bv ≠ pc.bv := fun u hu e => by
    obtain ⟨vx, hvx⟩ := Cv2.vm.spec u hu
    rw [e, hkc2] at hvx; cases hvx
  obtain ⟨Q2, R2, hcq2, -⟩ := B2'.xtop.fin.1.1.1.lists
  have hT2 := hcq2.tcbs
  have Cv' : VcpuCore (L := L) V Z H s3 (setCnodeSlot σ2 pc.bv r cs idx nc) :=
    Cv2.ofWE B2' B' hW3
      (fun y hy => by
        by_cases e : y = x
        · right; rw [e]
          exact ⟨by rw [hcv3, hcv2]; exact (vsLike_ept ptr level asid1 g asid va).1.1, _, _, _, _, _, hcv3⟩
        · exact Or.inl (hcap3 y hy e))
      (fun u hu b hb => B2'.slotWd_vcpu Cv2.vm (hSW b hb) u hu)
      (fun b hb => B2'.slotWd_head (hSW b hb))
      (fun t' ht' => by
        have htT := B2'.thT t' ht'
        have ev := tVcpuA_val hT2 htT
        exact hW3.mem_eq (tVcpuA_aligned hT2 htT) fun hb =>
          B2'.slotWd_tcb (hSW _ hb) ht' (by omega) (by omega) rfl)
      (fun u hu => hothc _ (hvpc u hu))
      (fun o ko' ho => by
        by_cases e : o = pc.bv
        · subst e
          simp only [setCnodeSlot, Function.update_self, Option.some.injEq] at ho
          subst ho
          exact ⟨_, hkc2, rfl⟩
        · rw [hothc _ e] at ho; exact ⟨ko', ho, rfl⟩)
      (fun o x' ho hx => by
        have e : o ≠ pc.bv := fun e => by subst e; simp [setCnodeSlot] at ho
        rw [hothc _ e] at ho; exact ⟨x', ho, hx⟩)
      (fun p vs hp => by
        have e : p ≠ pc.bv := fun e => by subst e; simp [setCnodeSlot] at hp
        rw [hothc _ e] at hp; exact hp)
  -- 5. `EptCore`
  have hW13 : P1.WritesIn st s1 s3 (fun b => b = w ∨ (b = x ∨ b = wordOf x 8#u64)) := hw12.trans hW3
  have hxa : ∀ b, (b = x ∨ b = wordOf x 8#u64) → ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val :=
    fun b hb => B1.slotWd_ept C1 b (hSW b hb)
  have hmw : L.mem s3 w = v := by
    rw [hW3.mem_eq hal (fun hb => by rcases hxa _ hb t ht with h | h <;> rw [ew] at h <;> omega)]
    rw [hs2', L.mem_wr s1 _ v _ hal hal, if_pos rfl]
  have hgk : gKey g.bv level.val = g.bv := by
    have e : g.bv = gKey i.bv level.val := hgb
    rw [e, gKey_idem _ hl64 le_rfl]
  have hp1 : GPath σ1 (Fl4Spec.asidHighBitsOf asid1.bv) (Fl4Spec.asidLowBitsOf asid1.bv) g.bv (XL t) t.bv := by
    rw [hXt]
    exact GPath.ofArch (by rw [har1]) hka1 hpath
  have C' : EptCore (L := L) X XL Z.th s3 (setCnodeSlot σ2 pc.bv r cs idx nc) :=
    C1.tableMap ht hxs hcv1 hXt hlv hgv hA1 hgk hp1 hk01 hW13
      (fun b hb => hb.elim Or.inl fun hb => Or.inr (hxa b hb))
      (by rw [hmw]; exact congrArg (· &&& ~~~(eptHw Fl4Spec.virtKind)) (tblEntry_bv Fl4Spec.virtKind ptr)) (tblEntry_ptr hpa) hk2t hoth2 rfl
      (cnK_setCnodeSlot hkc2 hwf hidx nc) hcv3
      (fun y hy hne => by rw [hcap3 y hy hne, hSS2.capV hy])
  exact Or.inr ⟨rfl, t.bv, asid1.bv, _, ho, hspec, Lst1, ⟨B', Cv'⟩, C'⟩

set_option maxHeartbeats 4000000 in
/-- **The extended decoder and FL4's `syscall.decode_invocation` on an unmapped EPT table cap with the map label, at
`VmEptState`** (module docstring; P3/JAtZV3EptE's `zv_sysdec_ept` / `zv_decV_ept` + `VmEptState.tableMap`). -/
theorem eptTableMap_decode_vmEpt (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    {lbl len ptr level asid va : U64} (block call cd fp : Bool) (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Ept ptr level false asid va))
    (h0 : level ≠ 0#u64)
    (hu : lbl.val ≠ (Fl4Spec.eptTableLabels level.val).2) (hm : lbl.val = (Fl4Spec.eptTableLabels level.val).1)
    (hl : ¬ len.val < 2) (hz : exAt ex 0 ≠ 0#u64) (hxe : IsSlot Z.th (exAt ex 0)) {i : U64}
    (hsa : msg.syscall_arg st s (L.curW s) buf 0#u64 = ok i)
    (hg : ¬ (i.bv &&& ~~~((1#64 <<< level.val) - 1)) ≥ Fl4Spec.guestGpaLimit)
    (args : List Fl4Spec.Data) (hA : VArgs st s (L.curW s) buf len args)
    (sl0 : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (fp' : Bool) (cref : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    ∃ res, syscall.decode_invocation st arI s a lbl len (cslotAddr (pc.bv, idx)) (.Ept ptr level false asid va)
        block call cd fp buf ex = ok res ∧
      ((∃ e e', res = (.Err e, s, a) ∧ ErrRel e e' ∧
        ExceptT.run (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp' lbl.bv args cref (pc.bv, idx)
          (absCap (.Ept ptr level false asid va)) ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest) buffer) σ =
          ({(.error e', σ)}, False)) ∨
      (res.1 = .Ok () ∧ ∃ (g : U64) (t asid1 : Fl4Spec.ObjRef) (σ' : Fl4Spec.State Unit),
        g.bv = (i.bv &&& ~~~((1#64 <<< level.val) - 1)) ∧ g.val < 2 ^ 47 ∧
        DecOut (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp' lbl.bv args cref (pc.bv, idx)
          (absCap (.Ept ptr level false asid va)) ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest) buffer) σ
          (.ept (.tableMap ptr.bv level.val (pc.bv, idx) t (Fl4Spec.guestIndex g.bv level.val) asid1 g.bv)) ∧
        EptTableMapSpec σ ptr.bv level.val (pc.bv, idx) t (Fl4Spec.guestIndex g.bv level.val) asid1 g.bv σ' ∧
        ∃ Lst' : U64 → List U64, VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst' D res.2.1 res.2.2 σ')) := by
  have hn : ¬ args.length < 2 := by rw [hA.1]; exact hl
  have ha0 : args.getD 0 0 = i.bv := hA.a0 (by omega) hsa
  obtain ⟨g, hgb, hgv, res, hdec, hout⟩ := VmEptState.tableMap J hni buf ex hpc hidx hcx h0 hu hm hl hz hxe
    hsa hg args ha0 hn sl0 rest
  have habs : absCap (.Ept ptr level false asid va) = .archObjectCap (.eptCap ptr.bv level.val none) := rfl
  refine ⟨res, by rw [zv_sysdec_ept]; exact hdec, ?_⟩
  rw [habs, zv_decV_ept]
  rcases hout with ⟨e, e', h1, he, ho⟩ | ⟨h1, t, asid1, σ', ho, hS, hJ⟩
  · exact Or.inl ⟨e, e', h1, he, run_liftME_err ho⟩
  · exact Or.inr ⟨h1, g, t, asid1, σ', hgb, hgv, DecOut.liftME (DecOut.of_eq ho), hS, hJ⟩

end

end

end Fl4Proofs.P3

/-
P3 (line mmuAD, gen 42b12): **the EPT frame map at `VmEptState`** — FL4's `ept::map_frame` past the guest-address
bound (crates/fl4-core/src/ept.rs l. 118-187: decode, the caller's restart, `set_cap` of `Frame { mapped, is_ept:
mapped, asid, vaddr }` into the invoked slot, `s.write(e, val)`) against the extended spec's `decodePageMapEpt`, then
`setThreadState cur Restart` and `performEptInvocation (.frameMap …)` (Fl4Spec/Ext/VirtEptInv l. 182-203, l. 224-226:
`setCap`, then `storeGuestEntry`), modelled on P3/EptTableMapV.

* Decode: P3/EptFrameMapDec's `EptCore.frameMapDec` (single spec outcome, `FrameDecOut`).
* **Base half** (inside `VmEptState.frameMap`): after P3/EptSetRoot's `VmEptState.restart` (`s1`, `σ1`):
  1. the `set_cap` / `setCap` pair: `set_cap_refines` (`StateRel` / `SlotsValid`; the new cap `CapRel` the spec's
     `newCap`, `CapValid` / `EncWf` from the old cap and the decode), P3/JAtZV3SlotIo's **`Vs.Recap.carryIo`** (the
     MDB links, CDT relation, `MdbInv`, `FinInv`: the frame cap's VT-x flag `vtF = mapped && is_ept` changes, so
     `MdbLike` does not hold, but `IoLike` — `MdbLike` without `vtF` — does), `MdbStep.recap` (`MdbOKV`; the new cap
     is `VCapOK`: `PaM` from the old cap, a nonzero ASID and `UserV gpa` when mapped), `XTopAt.slotStep`, then
     P3/JAtZBRecap's `JAtZB.vsStepJXB` (`VsNamed` after by `JAtZB.vsShr`: frame caps have no VSpace key);
  2. FL4's entry word: P3/EptStep1's `JAtZB.eptWr` (at the `EptCore` after step 1, P3/EptFrameMap's
     `EptCore.frameSlot`), then the spec's `storeGuestEntry`: `XTopAt.archSpec` + `JAtZB.arFrS` / `arFr_arch`.
* `VcpuCore` by **`VcpuCore.ofWG`** (P3/EptStep1, gen 42b12: `ofWE` generalised in place to any same-shape rewrite
  that is no VCPU / I/O-port cap) then `VcpuCore.ofW`; `EptCore` by P3/EptFrameMap's `EptCore.frameSlot` then
  `EptCore.frameEntry` (the decoded walk path moved to the state after the slot step by `GPath.ofArch`; the entry
  no walk step by `frame_nw`).
* **`VmEptState.frameMap`**: from `VmEptState` at an `Entered` spec state, the invoked unmapped `Frame` cap in a CNode
  slot and P3/EptFrameMapDec's decode hypotheses: `ept.map_frame` returns `res`, and either both sides fail with
  related errors, FL4's state unchanged, or the spec decodes `.frameMap nc …` (single outcome), the restart + perform
  has the single outcome `σ'`, and `VmEptState` holds at FL4's state after and `σ'`.

Gen 42b13 (the Architect's decision (i) on gen 42b12's case hypothesis `hz0`): `hz0` (ASID-0 pool entry not
guest-tagged) is dropped; the decoded ASID `asid1 ≠ 0`, which the native base needs for the new mapped frame cap
(`VCapOK`'s `m → a ≠ 0`, through `VsSlotsW`), comes from `JExtEpt.anz` (P3/VmState: a mapped `Ept` slot cap's ASID is
nonzero) at the root cap `ex[0]`, a slot by the new scope hypothesis `hxe : IsSlot Z.th (exAt ex 0)`
(`FrameDecOut`). Statement changed in place (`- hz0`, `+ hxe`). `ZvVirtAgree arI` [P] (gen-34 premise) as
hypothesis, as in `EptCore.frameMapDec`.

No named premise; the spec is not touched. No `sorry`; only the three standard axioms. New file; root import after
`P3.EptFrameMap`.
-/
import Fl4Proofs.P3.EptFrameMap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- A decoded frame table's level is not the root's. -/
theorem lkLvl_fbits_ne0 (sz : capability.FrameSize) : lkLvl (fbits sz).val ≠ 0 := by
  cases sz <;> simp [fbits, lkLvl]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
  Fl4Proofs.P1

set_option maxHeartbeats 4000000 in
/-- **The EPT frame map at `VmEptState`** (module docstring). -/
theorem VmEptState.frameMap (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hVA : ZvVirtAgree arI)
    {len ptr rights asid va : U64} {size : capability.FrameSize} {dev ep : Bool}
    (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : Z.th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame ptr size rights dev false ep asid va))
    (hrw : 1 ≤ rights.val ∧ rights.val ≤ 3)
    (hl : ¬ len.val < 3) (hz : exAt ex 0 ≠ 0#u64) (hxe : IsSlot Z.th (exAt ex 0)) {i mask attr : U64}
    (hsa : msg.syscall_arg st s (L.curW s) buf 0#u64 = ok i) (hsm : msg.syscall_arg st s (L.curW s) buf 1#u64 = ok mask)
    (hsr : msg.syscall_arg st s (L.curW s) buf 2#u64 = ok attr)
    (hg : ¬ (i.bv &&& ~~~(4095 : Fl4Spec.Word)) ≥ Fl4Spec.guestGpaLimit)
    (args : List Fl4Spec.Data) (ha0 : args.getD 0 0 = i.bv) (ha1 : args.getD 1 0 = mask.bv)
    (ha2 : args.getD 2 0 = attr.bv) (hn : ¬ args.length < 3)
    (sl0 : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    ∃ g : U64, g.bv = (i.bv &&& ~~~(4095 : Fl4Spec.Word)) ∧ g.val < 2 ^ 47 ∧
    ∃ res, ept.map_frame st arI s a len (.Frame ptr size rights dev false ep asid va) (cslotAddr (pc.bv, idx)) buf ex
        = ok res ∧
      ((∃ e e', res = (.Err e, s, a) ∧ ErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodePageMapEpt (Z := Unit) args (pc.bv, idx)
          (.pageCap dev ptr.bv (vmRightsOf rights) .vmNoMap (frameSizeOf size) none)
          ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest)) σ = ({(.error e', σ)}, False)) ∨
      (res.1 = .Ok () ∧ ∃ (nc : Fl4Spec.ArchCap) (t : Fl4Spec.ObjRef) (gi : BitVec 9) (E : Fl4Spec.Word)
          (σ' : Fl4Spec.State Unit),
        ExceptT.run (Fl4Spec.decodePageMapEpt (Z := Unit) args (pc.bv, idx)
          (.pageCap dev ptr.bv (vmRightsOf rights) .vmNoMap (frameSizeOf size) none)
          ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest)) σ =
          ({(.ok (.frameMap nc (pc.bv, idx) t gi E), σ)}, False) ∧
        EptFrameMapSpec σ nc (pc.bv, idx) t gi E σ' ∧
        ∃ Lst' : U64 → List U64, VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst' D res.2.1 res.2.2 σ')) := by
  have B := J.1.1
  have C := J.2
  have hct := P1.cur_thread_ok (L := L) s
  obtain ⟨g, hgb, hgv, res, hdec, hout⟩ := C.frameMapDec (arI := arI) B.xtop.fin.2.1 hVA a (cslotAddr (pc.bv, idx))
    buf ex hrw hl hz hxe hct hsa hsm hsr hg args ha0 ha1 ha2 hn (pc.bv, idx) sl0 rest
  refine ⟨g, hgb, hgv, res, hdec, ?_⟩
  rcases hout with ⟨e, e', hres, he, ho⟩ | ⟨t, asid1, m, ht, hXt, ha20, hA1, hnH, hpath, -, ⟨es0, hk0, -⟩, -, -, -, -,
    ho, s2, val, mp, a', v', hs2, hval, hT, hres⟩
  · exact Or.inl ⟨e, e', hres, he, ho⟩
  subst hres
  set x := cslotAddr (pc.bv, idx) with hxdef
  set gi := Fl4Spec.guestIndex g.bv (fbits size).val with hgi
  set E := specFrameEntry (vmRightsOf m) ptr.bv (frameSizeOf size = .x64LargePage) attr.bv with hE
  set nc : Fl4Spec.ArchCap := if E = 0 then .pageCap dev ptr.bv (vmRightsOf rights) .vmNoMap (frameSizeOf size) none
    else .pageCap dev ptr.bv (vmRightsOf rights) .vmEptMap (frameSizeOf size) (some (asid1.bv, g.bv)) with hnc_def
  -- 0. the decoded cap's fields
  have hTa : (mp = true ∧ a' = asid1 ∧ v' = g ∧ val ≠ 0#u64) ∨ (mp = false ∧ a' = 0#u64 ∧ v' = 0#u64 ∧ val = 0#u64) := by
    by_cases hv : (val != 0#u64) = true
    · rw [if_pos hv] at hT; cases hT
      exact Or.inl ⟨rfl, rfl, rfl, bne_iff_ne.mp hv⟩
    · rw [if_neg hv] at hT; cases hT
      exact Or.inr ⟨rfl, rfl, rfl, by by_contra h; exact hv (bne_iff_ne.mpr h)⟩
  have hanz : mp = true → a' ≠ 0#u64 := by
    intro hm
    rcases hTa with ⟨-, h2, -, -⟩ | ⟨h1, -, -, -⟩
    · rw [h2]; exact hA1
    · rw [h1] at hm; cases hm
  have hvu : mp = true → UserV v' := by
    intro hm
    rcases hTa with ⟨-, -, h3, -⟩ | ⟨h1, -, -, -⟩
    · rw [h3]; unfold UserV; omega
    · rw [h1] at hm; cases hm
  have hv47 : mp = true → mp = true → v'.val < 2 ^ 47 := by
    intro hm _
    rcases hTa with ⟨-, -, h3, -⟩ | ⟨h1, -, -, -⟩
    · rw [h3]; exact hgv
    · rw [h1] at hm; cases hm
  have ha'20 : a'.val < 2 ^ 20 := by
    rcases hTa with ⟨-, h2, -, -⟩ | ⟨-, h2, -, -⟩
    · rw [h2]; exact ha20
    · rw [h2]; decide
  have hv'48 : v'.val < 2 ^ 48 := by
    rcases hTa with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩
    · rw [h3]; omega
    · rw [h3]; decide
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
  have hcv0 : capV (L.mem s) x = .Frame ptr size rights dev false ep asid va := capV_of_capAt hcx
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
  -- 2. the `set_cap` / `setCap` pair
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) := by
    have h := set_thread_state_slots (L := L) Z.th hP s (L.curW s) sched.TS_RESTART (B.xtop.curTcb hcur).1
      B.kern.act
    rw [hs1, WP.spec_ok] at h; exact h
  have hcv1 : capV (L.mem s1) x = .Frame ptr size rights dev false ep asid va := by rw [hSS1.capV hxs]; exact hcv0
  have hcx1 : capAt (L.mem s1) x = ok (.Frame ptr size rights dev false ep asid va) := by rw [capAt_capV, hcv1]
  have hcl := hcx
  rw [capAt_words] at hcl
  have hew0 := decode_encWf hcl
  set c : capability.Cap := .Frame ptr size rights dev mp mp a' v' with hc
  have hew : EncWf c := ⟨hew0.1, hew0.2.1, ha'20, hv'48⟩
  have hnc : absCap c = .archObjectCap nc := by
    rcases hTa with ⟨h1, h2, h3, hv⟩ | ⟨h1, h2, h3, hv⟩
    · have hE0 : ¬ E = 0 := fun h => hv (P1.eq_of_bv (hval.trans (h.trans rfl)))
      rw [hc, h1, h2, h3, hnc_def, if_neg hE0] <;> rfl
    · have hE0 : E = 0 := hval.symm.trans ((congrArg UScalar.bv hv).trans rfl)
      rw [hc, h1, h2, h3, hnc_def, if_pos hE0] <;> rfl
  have hca : CapRel c (.archObjectCap nc) := ⟨hrw, hnc⟩
  obtain ⟨hSt1, hSV1, -, -, -⟩ := B1.xtop.rel.2.1
  have hcvd : CapValid Z.th c := by have h := hSV1.abs hA hcx1; exact h
  have hSC := set_cap_refines (L := L) Z.th s1 σ1 hSt1 hSV1 hP hpc hidx c (.archObjectCap nc) hca hcvd hew
  rw [set_cap_eq, WP.spec_ok] at hSC
  obtain ⟨σ2, hsc, hSt2, hSV2, -, -, -, -⟩ := hSC
  have hσ2 : σ2 = setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc) := by
    rw [setCap_cnode _ hkc1 hwf hidx] at hsc
    have := congrArg Prod.fst hsc
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
    exact this.symm
  subst hσ2
  set s2c := wrCap (L := L) s1 x c with hs2c
  have hF3 := set_cap_foot (L := L) hP hxs s1 c hew
  rw [set_cap_eq, WP.spec_ok] at hF3
  obtain ⟨hSF3, hcv3⟩ := hF3
  have hfx := hxs.fit hP
  have hal32 := hxs.align hP
  have hWF := set_cap_frame (L := L) s1 x c (by omega) (by omega)
  rw [set_cap_eq, WP.spec_ok] at hWF
  have h8 : (wordOf x 8#u64).val = x.val + 8 := wa8_val (by omega)
  have hW3 : P1.WritesIn st s1 s2c (fun b => b = x ∨ b = wordOf x 8#u64) := by
    refine ⟨hWF.1, hWF.2.1, fun b hb hn => hWF.2.2 b hb fun hr => hn (by
      obtain ⟨g1, g2⟩ := hr
      have hb8 : b.val % 8 = 0 := hb
      by_cases e : b.val = x.val
      · exact Or.inl (UScalar.eq_of_val_eq e)
      · exact Or.inr (UScalar.eq_of_val_eq (by rw [h8]; omega)))⟩
  have hks3 : L.ksb s2c = L.ksb s1 := hW3.1
  have hcap3 : ∀ y, IsSlot Z.th y → y ≠ x → capV (L.mem s2c) y = capV (L.mem s1) y := fun y hy hne => by
    unfold capV; rw [((hSF3 y hy).2.2 hne).1, ((hSF3 y hy).2.2 hne).2]
  have hLk : Vs.IoLike (capV (L.mem s2c) x) (capV (L.mem s1) x) := by
    rw [hcv3, hcv1]; exact ⟨rfl, rfl, rfl, trivial⟩
  have hsh : shape (capV (L.mem s2c) x) = shape (capV (L.mem s1) x) := hLk.1
  have hok : okey (capV (L.mem s2c) x) = okey (capV (L.mem s1) x) := hLk.2.1
  have hnu : isUt (capV (L.mem s1) x) = false := by rw [hcv1]; rfl
  have hK3 : KFoot σ1 (setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc)) := KFoot.cnode hkc1 hwf idx _
  obtain ⟨-, ⟨-, -, hM, hCd, hI⟩, hFI, -, hMO, -, -⟩ := B1.xtop.rel
  obtain ⟨hM', hCd', hI', hFI'⟩ := Vs.Recap.carryIo hM hCd hI hFI hSF3 hLk hK3
  have hvok : ∀ P L4 L3 L2 L1 : Set U64, VCapOK P L4 L3 L2 L1 (capV (L.mem s1) x) →
      VCapOK P L4 L3 L2 L1 (capV (L.mem s2c) x) := by
    intro P L4 L3 L2 L1 hv
    rw [hcv1] at hv
    obtain ⟨-, hpa, -⟩ := hv
    rw [hcv3]
    exact ⟨hanz, hpa, hvu⟩
  have hMO3 : MdbOKV (L.ksb s1) (L.mem s2c) Z.G :=
    (MdbStep.recap hM x (CapAlike.of_shape hsh hok fun h => by rw [hnu] at h; cases h) hvok
      (fun z hz hne => hcap3 z ((hM.members z).1 hz).1 hne)
      (fun z hz => by unfold revOf; rw [(hSF3 z ((hM.members z).1 hz).1).2.1])).okv hMO
  have hTS : ∀ t', Z.th t' = some .tcb → capAt (L.mem s2c) (slotOf t' 1) = capAt (L.mem s1) (slotOf t' 1) := by
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
  have hX3 : XTopAt (L := L) AR { Z with G := Z.G } s2c a (setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc)) :=
    XTopAt.slotStep B1.xtop (hW3.mono hSW) (cnK_setCnodeSlot hkc1 hwf hidx _) (keepC_setCnodeSlot hkc1 _)
      ⟨hSt2, hSV2, hM', hCd', hI'⟩ hFI' hMO3 hTS
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s2c) := fun y hy => by
    by_cases e : y = x
    · rw [e]
      have h0 := B1.vsc x hxs
      rw [hcv1] at h0
      have h1 : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 (capV (L.mem s1) x) := by rw [hcv1]; exact h0
      have h2 := hvok _ _ _ _ _ h1
      rw [hcv3] at h2 ⊢
      exact h2
    · rw [hcap3 y hy e]; exact B1.vsc y hy
  have hvn : Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s2c) (L.ksb s2c) :=
    B1.vsShr (G' := Z.G) hX3 hks3 (VsKeep.of_vk fun y hy => by
      by_cases e : y = x
      · rw [e, hcv3, hcv1]; exact ⟨rfl, rfl⟩
      · rw [hcap3 y hy e]; exact ⟨rfl, rfl⟩)
      (ArchShr.of_keep rfl fun q ao hq => by
        have hq' : q ≠ pc.bv := fun e => by rw [e, hkc1] at hq; cases hq
        simp [setCnodeSlot, hq'])
  have B2 : JAtZB (L := L) arI AR Z H Cs Ac Lst1 D s2c a (setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc)) :=
    B1.vsStepJXB ⟨B1.scOut⟩ hpc hidx (TabsArch.empty σ1) (L3' := Z.L3) (L2' := Z.L2) (L1' := Z.L1) hX3
      (vsSFr_setCnodeSlot hkc1 hwf hidx _) (hW3.mono fun b hb => Or.inl (Or.inr hb)) hcap3 hsh hok hnu
      (fun y hy => ⟨(hSF3 y hy).1, (hSF3 y hy).2.1⟩) hvc ⟨subset_rfl, subset_rfl, subset_rfl⟩ hvn
  -- `VcpuCore` after the slot step
  obtain ⟨Q1, R1, hcq1, -⟩ := B1.xtop.fin.1.1.1.lists
  have hT1 := hcq1.tcbs
  have hothc : ∀ q, q ≠ pc.bv → (setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc)).kheap q = σ1.kheap q :=
    fun q hq => by simp [setCnodeSlot, hq]
  have hvpc : ∀ u ∈ V, u.bv ≠ pc.bv := fun u hu e => by
    obtain ⟨vx, hvx⟩ := Cv1.vm.spec u hu
    rw [e, hkc1] at hvx; cases hvx
  have Cv2 : VcpuCore (L := L) V Z H s2c (setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc)) :=
    Cv1.ofWG B1 B2 hW3
      (fun y hy => by
        by_cases e : y = x
        · right
          rw [e, hcv3, hcv1]
          exact ⟨rfl, trivial, fun f l o h => by rw [hc] at h; cases h⟩
        · exact Or.inl (hcap3 y hy e))
      (fun u hu b hb => B1.slotWd_vcpu Cv1.vm (hSW b hb) u hu)
      (fun b hb => B1.slotWd_head (hSW b hb))
      (fun t' ht' => by
        have htT := B1.thT t' ht'
        have ev := tVcpuA_val hT1 htT
        exact hW3.mem_eq (tVcpuA_aligned hT1 htT) fun hb =>
          B1.slotWd_tcb (hSW _ hb) ht' (by omega) (by omega) rfl)
      (fun u hu => hothc _ (hvpc u hu))
      (fun o ko' ho => by
        by_cases e : o = pc.bv
        · subst e
          simp only [setCnodeSlot, Function.update_self, Option.some.injEq] at ho
          subst ho
          exact ⟨_, hkc1, rfl⟩
        · rw [hothc _ e] at ho; exact ⟨ko', ho, rfl⟩)
      (fun o x' ho hx => by
        have e : o ≠ pc.bv := fun e => by subst e; simp [setCnodeSlot] at ho
        rw [hothc _ e] at ho; exact ⟨x', ho, hx⟩)
      (fun p vs hp => by
        have e : p ≠ pc.bv := fun e => by subst e; simp [setCnodeSlot] at hp
        rw [hothc _ e] at hp; exact hp)
  -- `EptCore` after the slot step
  have hxa : ∀ b, (b = x ∨ b = wordOf x 8#u64) → ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val :=
    fun b hb => B1.slotWd_ept C1 b (hSW b hb)
  have C2 : EptCore (L := L) X XL Z.th s2c (setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc)) :=
    C1.frameSlot ht hW3 hxa hcv1 hcv3 hv47 hcap3 (cnK_setCnodeSlot hkc1 hwf hidx _)
  -- 3. FL4's entry word, then the spec's `storeGuestEntry`
  set w := eptA t gi with hw
  have hpl := C1.rel.place t ht
  have ew : w.val = t.val + 8 * gi.toNat := eptA_val hpl.2 gi
  have hgi9 := gi.isLt
  have hal : P1.Aligned w := by unfold P1.Aligned; rw [ew]; omega
  obtain ⟨B3, hSS3⟩ := B2.eptWr C2 ht hal (by rw [ew]; omega) (by rw [ew]; omega) val
  set s3 := L.wr s2c w val with hs3
  set σ3 := updK (setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc)) t.bv
    (.archObj (.ept (XL t) (Function.update es0 gi E))) with hσ3
  have hk2t : (setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc)).kheap t.bv = some (.archObj (.ept (XL t) es0)) := by
    rw [hothc _ htpc]; exact hk01
  have hX4 : XTopAt (L := L) AR Z s3 a σ3 := B3.xtop.archSpec hk2t (Or.inr ⟨_, _, rfl⟩)
    (.ept (XL t) (Function.update es0 gi E)) rfl
  have B4 : JAtZB (L := L) arI AR Z H Cs Ac Lst1 D s3 a σ3 :=
    B3.arFrS (arFr_arch hk2t (.ept (XL t) (Function.update es0 gi E)) rfl) hX4
  have hspec : EptFrameMapSpec σ nc (pc.bv, idx) t.bv gi E σ3 := by
    unfold EptFrameMapSpec
    rw [Notif.nd_bind_one hst1, performFrameMap_eq hkc1 hwf hidx hk01] <;> rfl
  -- `VcpuCore` after the entry word
  have hw23 : P1.WritesIn st s2c s3 (· = w) := P1.writesIn_wr hal
  obtain ⟨Q2, R2, hcq2, -⟩ := B2.xtop.fin.1.1.1.lists
  have hT2 := hcq2.tcbs
  have nV2 : ∀ u ∈ V, ∀ b, b = w → b.val < u.val ∨ u.val + 32768 ≤ b.val := by
    intro u hu b hb
    subst hb
    rcases C2.apartV Cv2.vm t ht u hu with h | h <;> omega
  have hh2 : ∀ b, b = w → b ≠ P1.vHeadA st s2c := by
    intro b hb he
    subst hb
    have h2 : w.val = (P1.vHeadA st s2c).val := by rw [he]
    rcases B2.eptHead C2 ht with h | h <;> omega
  have hv2 : VKeep (L := L) Z.th s2c s3 := by
    intro t' ht'
    have htT := B2.thT t' ht'
    have ev := tVcpuA_val hT2 htT
    refine hw23.mem_eq (tVcpuA_aligned hT2 htT) fun he => ?_
    have hO : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s2c (setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc))
        (tVcpuA t') :=
      Or.inr (Or.inr (Or.inl ⟨t', htT, by omega, by omega⟩))
    have h2 : (tVcpuA t').val = w.val := by rw [he]
    rcases B2.oobjX C2 ht hO with h | h <;> omega
  have hvt : ∀ u ∈ V, u.bv ≠ t.bv := fun u hu e => by
    obtain ⟨vx, hvx⟩ := Cv2.vm.spec u hu
    rw [e, hk2t] at hvx; cases hvx
  have hoth3 : ∀ q, q ≠ t.bv → σ3.kheap q = (setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc)).kheap q :=
    fun q hq => by simp [hσ3, updK, hq]
  have hk3t : σ3.kheap t.bv = some (.archObj (.ept (XL t) (Function.update es0 gi E))) := by simp [hσ3, updK]
  have Cv3 : VcpuCore (L := L) V Z H s3 σ3 :=
    Cv2.ofW B2 B4 hw23 hSS3 nV2 hh2 hv2 (fun u hu => hoth3 _ (hvt u hu))
      (fun o ko' ho => by
        by_cases e : o = t.bv
        · subst e; rw [hk3t] at ho; cases ho
          exact ⟨_, hk2t, by rw [ept_bits, ept_bits]⟩
        · rw [hoth3 _ e] at ho; exact ⟨ko', ho, rfl⟩)
      (fun o x' ho hx => by
        have e : o ≠ t.bv := fun e => by rw [e, hk3t] at ho; cases ho
        rw [hoth3 _ e] at ho; exact ⟨x', ho, hx⟩)
      (fun p vs hp => by
        have e : p ≠ t.bv := fun e => by rw [e, hk3t] at hp; cases hp
        rw [hoth3 _ e] at hp; exact hp)
  -- 4. `EptCore` after the entry word
  have hXt0 : XL t ≠ 0 := by rw [hXt]; exact lkLvl_fbits_ne0 size
  have hp2 : GPath (setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc)) (Fl4Spec.asidHighBitsOf asid1.bv)
      (Fl4Spec.asidLowBitsOf asid1.bv) g.bv (XL t) t.bv := by
    rw [hXt]
    refine GPath.ofArch (σ := σ1) (σ' := setCnodeSlot σ1 pc.bv r cs idx (.archObjectCap nc)) rfl (fun q ao hq => ?_) (GPath.ofArch (by rw [har1]) hka1 hpath)
    have hq' : q ≠ pc.bv := fun e => by rw [e, hkc1] at hq; cases hq
    rw [hothc _ hq']; exact hq
  have hnw : ¬ GWalkE (XL t) (Function.update es0 gi E) gi := by
    rw [hXt]; exact frame_nw hnH (vmRightsOf m) ptr.bv attr.bv es0 gi
  have hmw : L.mem s3 w = val := by rw [hs3, L.mem_wr s2c _ val _ hal hal, if_pos rfl]
  have hwd : EptWord Fl4Spec.virtKind (L.mem s3 w).bv E := by
    unfold EptWord; rw [hmw]; exact congrArg (· &&& ~~~(eptHw Fl4Spec.virtKind)) hval
  have C3 : EptCore (L := L) X XL Z.th s3 σ3 :=
    C2.frameEntry ht hXt0 hgv hp2 hk2t hnw hw23 hwd hk3t hoth3 rfl hSS3
  exact Or.inr ⟨rfl, nc, t.bv, gi, E, σ3, ho, hspec, Lst1, ⟨B4, Cv3⟩, C3⟩

end

end

end Fl4Proofs.P3

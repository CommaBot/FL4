/-
P3 (DESIGN.md §9), VSpace: **the decode of a mapped table cap whose table is
in no set** (toward removing XTopJointEntry's `JEntryGlob.vsTab`,
handoff/vsreach.md "vs17 HANDOFF" steps 2/3).

A detype may prune a mapped page table, directory or PDPT `q` from its set
while its cap still says mapped (handoff/vsreach.md). Its decode:

* `offFr_of`: at `TopSR`, `q`'s frame facts (4 KiB-aligned; no `OObj`, no
  `VObj`, no typed-heap word: XTopJointEntry's `JEntryAt.vsTyp`) give the
  off-set unmaps' `hoff`/`hnS`, VsOffTop's `hno`, and that `q`'s words are no
  pool or ASID word and no `OObj` word.
* `vs_x_afterTO`, `dom_of_footO`: VsTopX's `vs_x_afterT` and VsDomF's
  `dom_of_foot` for a footprint grown by `q`'s frame.
* `decode_invocation_page_tableXO` (and the PD/PDPT forms): every label of
  such a cap (VsDecFrame's `decode_invocation_page_tableX` with `Map` an error
  for a mapped cap and `Unmap` VsPtUnmapOff's `pt_unmap_rel_off`).
* `decode_invocation_page_table_offX` (and PD/PDPT): at `FinXR`, the post
  VsTopX's `VsJPostO` (XTopJointVsOff's `JAtZ.vsPostOffJ`).
-/
import Fl4Proofs.P3.VsThX
import Fl4Proofs.P3.VsOffTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}
  {A : Type} {AR : A → Fl4Spec.Cr3 → Prop}

/-- **A table frame outside the sets** (module docstring): from `q`'s frame
facts at `TopSR`, the off-set unmaps' `hoff` and `hnS`, VsOffTop's `hno`, and
`q`'s words no pool/ASID word and no `OObj` word. -/
theorem offFr_of {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) {q : U64} (hqa : q.val % 4096 = 0)
    (hfr : ∀ b : U64, q.val ≤ b.val → b.val < q.val + 4096 →
      ¬ OObj st N T C E R B c s σ b ∧ ¬ VObj th P L4 L3 L2 L1 (L.ksb s) b ∧
      ∀ p k, th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k)) :
    (∀ i : U64, i.val < 512 → ¬ PtWAll L4 L3 L2 L1 (peA q i) ∧ ¬ SlotW th (peA q i) ∧
      ¬ VsWrite P (L.ksb s) (peA q i) ∧ OutsideObjects th (peA q i)) ∧
    ¬ (q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) ∧
    (∀ i : U64, i.val < 512 → ¬ OObj st N T C E R B c s σ (peA q i)) ∧
    (∀ b, PtW {q} b → ¬ VsWrite P (L.ksb s) b) ∧ (∀ b, PtW {q} b → ¬ OObj st N T C E R B c s σ b) := by
  have hfit := tbl_fit hqa
  have hin : ∀ i : U64, i.val < 512 → q.val ≤ (peA q i).val ∧ (peA q i).val < q.val + 4096 := fun i hi => by
    rw [peA_val hfit hi]; omega
  have hA : ∀ i : U64, i.val < 512 → ¬ PtWAll L4 L3 L2 L1 (peA q i) ∧ ¬ SlotW th (peA q i) ∧
      ¬ VsWrite P (L.ksb s) (peA q i) ∧ OutsideObjects th (peA q i) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hin i hi
    obtain ⟨-, hnv, hno⟩ := hfr _ h1 h2
    refine ⟨?_, ?_, ?_, ?_, hno⟩
    · rintro ⟨p, hp, j, hj, e⟩
      apply hnv; rw [e]
      have hv := peA_val (tbl_fit (hS.2.pt p hp)) hj
      exact Or.inr (Or.inr (Or.inl ⟨p, Or.inr hp, by rw [hv]; omega, by rw [hv]; omega⟩))
    · rintro ⟨x, hx, e | e⟩
      · apply hnv; rw [e, ← wordOf_zero x]; exact vobj_slot hS.2.pl P L4 L3 L2 L1 _ hx (by decide)
      · apply hnv; rw [e]; exact vobj_slot hS.2.pl P L4 L3 L2 L1 _ hx (k := 8#u64) (by decide)
    · intro hv; apply hnv
      rcases hv with ⟨hi', hhi, e⟩ | ⟨p, hp, lo, hlo, e⟩
      · rw [e]; have hv := atA_val hS.2.vs.ksb_fit hhi
        exact Or.inr (Or.inr (Or.inr ⟨by rw [hv]; omega, by rw [hv]; omega⟩))
      · rw [e]; have hv := peA_val (hS.2.vs.pal p hp).2 hlo
        exact Or.inr (Or.inr (Or.inl ⟨p, Or.inl hp, by rw [hv]; omega, by rw [hv]; omega⟩))
    · show (peA q i).val % 8 = 0
      rw [peA_val hfit hi]; omega
  have hno : ∀ i : U64, i.val < 512 → ¬ OObj st N T C E R B c s σ (peA q i) := fun i hi =>
    (hfr _ (hin i hi).1 (hin i hi).2).1
  have hPq : ∀ b, PtW {q} b → ∃ i : U64, i.val < 512 ∧ b = peA q i := by
    rintro b ⟨p, hp, i, hi, rfl⟩
    rw [Set.mem_singleton_iff.1 hp]; exact ⟨i, hi, rfl⟩
  refine ⟨hA, fun hq => (hfr q le_rfl (by omega)).2.1
    (Or.inr (Or.inr (Or.inl ⟨q, Or.inr hq, le_rfl, by omega⟩))), hno, fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := hPq b hb; exact (hA i hi).2.2.1
  · obtain ⟨i, hi, rfl⟩ := hPq b hb; exact hno i hi

/-- **`FinXT` after an outcome** of a footprint `W` missing the pool words
(VsTopX's `vs_x_afterT`, any such `W`). -/
theorem vs_x_afterTO {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {W : U64 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hWV : ∀ b, W b → ¬ VsWrite P (L.ksb s) b)
    (hSR : FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s W s' a' σ')
    (hR' : VsRel P (L.mem s') (L.ksb s') σ') (hPt' : PtRel L4 L3 L2 L1 (L.mem s') σ')
    (hCR' : CRel th (L.mem s') σ' G) (hFI' : FinInv th (L.mem s') σ' G) (hMO' : MdbOKV (L.ksb s) (L.mem s') G)
    (hK : KFoot σ σ') :
    FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ s' a' σ' :=
  ⟨⟨hSR.1, hR', hPt', Vs.PoolsIn.of_writes hPI hSR.2 hS.2.vs hWV, CurOK.of_inv hCur hK hCR'.2.2.1 hMO'.2.2⟩,
    ⟨G, hCR', hFI', by rw [hSR.2.1]; exact hMO'⟩, hSR.2.1, KFoot.szKeep hK⟩

/-- **The domain-schedule words kept** by an outcome writing in `VsFootW` and
a frame with no `OObj` word (VsDomF's `dom_of_foot`). -/
theorem dom_of_footO {s s' : S} {a : A} {σ : Fl4Spec.State Unit}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) {q : U64}
    (hWO : ∀ b, PtW {q} b → ¬ OObj st N T C E R B c s σ b)
    (h : s' = s ∨ P1.WritesIn st s s' (fun b => VsFootW st th P L4 L3 L2 L1 s b ∨ PtW {q} b)) :
    L.ksb s' = L.ksb s ∧ ∀ o ∈ domOffs, L.mem s' (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) := by
  rcases h with rfl | hw
  · exact ⟨rfl, fun _ _ => rfl⟩
  · refine ⟨hw.1, fun o ho => hw.2.2 _ ?_ ?_⟩
    · have := hS.2.vs.ksb_fit
      exact ksW_al (by omega) hS.2.vs.ksb_al (domOffs_lt' ho).1 (domOffs_lt' ho).2
    · rintro (h | h)
      · exact dom_not_foot hS ho h
      · apply hWO _ h
        obtain ⟨ho1, -⟩ := domOffs_lt' ho
        have hfit := hS.2.vs.ksb_fit
        have hb : (ksW (L.ksb s) o).val = (L.ksb s).val + o.val := ksW_val (by omega)
        exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **A mapped PageTable cap whose table is in no set**, every label (VsDecFrame's
`decode_invocation_page_tableX` for `ptr ∉ L1`): `Map` errors (the cap is mapped),
`Unmap` is VsPtUnmapOff's `pt_unmap_rel_off` (FL4 zeroes `ptr`'s frame, the spec
empties its table), any other label l4v's `IllegalOperation`. -/
theorem decode_invocation_page_tableXO (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    {pc : U64} {r : Nat} {idx : List Bool} {ptr asid0 va0 : U64} {mp : Bool}
    (hXs : ∀ s' a' σ', SR s' a' σ' → VsRel P (L.mem s') (L.ksb s') σ' → PtRel L4 L3 L2 L1 (L.mem s') σ' →
      CRel th (L.mem s') σ' G → FinInv th (L.mem s') σ' G → MdbOKV (L.ksb s) (L.mem s') G → KFoot σ σ' →
      VsPostJ th (L.mem s) (L.mem s') (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) σ σ' →
      (∀ i : U64, i.val < 512 → L.mem s' (peA ptr i) = 0#u64) →
      σ'.kheap ptr.bv = some (.archObj (.pageTable fun _ => .invalidPTE)) →
      X s' a' σ')
    (hHU : VsPtUnmapHyps st A arI th P L4 L3 L2 L1 SR) (hS : SR s ar σ)
    (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageTableMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap)
    (hlU : lbl = fl4_abi.label.X86PageTableUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hpc : th pc = some (.cnode r)) (hidx : idx.length = r)
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr mp asid0 va0)) (hmp : mp = true)
    (hTy : ∃ f, σ.kheap ptr.bv = some (.archObj (.pageTable f))) (hqa : ptr.val % 4096 = 0)
    (hoff : ∀ i : U64, i.val < 512 → ¬ PtWAll L4 L3 L2 L1 (peA ptr i) ∧ ¬ SlotW th (peA ptr i) ∧
      ¬ VsWrite P (L.ksb s) (peA ptr i) ∧ OutsideObjects th (peA ptr i))
    (hnS : ¬ (ptr ∈ L4 ∨ ptr ∈ L3 ∨ ptr ∈ L2 ∨ ptr ∈ L1))
    (hoffSt : ∀ s1 s2 a1 σ1 σ2, SR s1 a1 σ1 → L.ksb s1 = L.ksb s → KFoot σ σ1 → P1.WritesIn st s1 s2 (PtW {ptr}) →
      (∃ f f', σ1.kheap ptr.bv = some (.archObj (.pageTable f)) ∧ σ2 = updK σ1 ptr.bv (.archObj (.pageTable f'))) →
      SR s2 a1 σ2)
    (hm0 : mp = true → asid0 ≠ 0#u64 ∧ va0.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
    (hmu : mp = true → Vs.UserV va0)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQX (L := L) arI Q X s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  have hCR0 := hCR
  obtain ⟨hSt, hSV, -, -, -⟩ := hCR0
  have hfe : EncWf (.PageTable ptr mp asid0 va0) := by
    have h := hcap; rw [capAt_words] at h; exact decode_encWf h
  obtain ⟨xct, hkt0, -⟩ := hSt.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hcur' : ct.bv = σ.curThread := hcur.symm
  have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
    rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
  have hAs : AbsSlot th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  unfold DecOKMQX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci (pc.bv, idx) (.PageTable ptr mp asid0 va0) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          (args.map UScalar.bv) ci (pc.bv, idx) (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))
          excaps)) := rfl
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  have hne : ¬ fl4_abi.label.X86PageTableMap = fl4_abi.label.X86PageTableUnmap := by
    unfold fl4_abi.label.X86PageTableMap fl4_abi.label.X86PageTableUnmap; decide
  by_cases hm : lbl = fl4_abi.label.X86PageTableMap
  · subst hm hmp
    have hl := hlM rfl
    unfold vspace.decode_table
    simp only [vspace.as_table, bind_ok, hne, ↓reduceIte]
    rcases hext with ⟨hex, rfl⟩ | ⟨x, vc, vc', xsl, rest, hex, -, -, rfl⟩
    · have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
          (.pageTableCap ptr.bv (some (asid0.bv, va0.bv))) []) σ =
          ({(.error .truncatedMessage, σ)}, False) := ptDecode_trunc hl _ _ _ _ _ (by simp) σ
      rw [hex]
      simp only [bind_ok, error.truncated, WP.spec_ok]
      exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
    · rw [hex]
      simp only [bind_ok]
      by_cases h2 : length >= 2#u64
      · rw [if_pos h2]
        have h2' : 2 ≤ args.length := by
          have : 2 ≤ length.val := by scalar_tac
          omega
        obtain ⟨a0, a1, ar', rfl⟩ : ∃ a0 a1 r', args = a0 :: a1 :: r' := by
          match args, h2' with
          | a0 :: a1 :: r', _ => exact ⟨_, _, _, rfl⟩
        have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl ((a0 :: a1 :: ar').map UScalar.bv) ci
            (pc.bv, idx) (.pageTableCap ptr.bv (some (asid0.bv, va0.bv))) ((vc', xsl) :: rest)) σ =
            ({(.error (.invalidCapability 0), σ)}, False) := ptDecode_mapped hl _ _ _ _ _ _ _ _ σ
        simp only [error.invalid_cap, bind_ok, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, _, htr, Or.inr ⟨0#u64, rfl, rfl⟩⟩) hX0
      · rw [if_neg h2]
        have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
            (.pageTableCap ptr.bv (some (asid0.bv, va0.bv))) ((vc', xsl) :: rest)) σ =
            ({(.error .truncatedMessage, σ)}, False) := ptDecode_trunc hl _ _ _ _ _ (by
              have : length.val < 2 := by scalar_tac
              simp only [List.length_map]; omega) σ
        simp only [error.truncated, bind_ok, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
  by_cases hu : lbl = fl4_abi.label.X86PageTableUnmap
  · subst hu
    have hl := hlU rfl
    have hfinR := fin_iff_of hP hCR hFI hAs hcap (Or.inl ⟨trivial, rfl⟩) rfl (by simp)
      (fun h => by
        have : Fl4Spec.GenObjRef.objRef ptr.bv ∈ Fl4Spec.genObjRefs (absCap (.PageTable ptr mp asid0 va0)) :=
          Set.mem_union_left _ (Set.mem_union_left _ ⟨ptr.bv, by simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef], rfl⟩)
        rw [h] at this; exact this)
    refine WP.spec_mono (pt_unmap_rel_off hHU s ar σ hP hVP hD hPP hPS (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩) (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, e⟩) hPI hSt hSV hR hPt hS ct hct hcur' hkt (hrun _ hkt) htcb
      hact hPO ptr asid0 va0 mp hTy hqa hoff hnS hoffSt hfe hm0 hmu hpc hidx hcap hl length buf (args.map UScalar.bv) ci
      extra excaps (is_final_eq s _) hfinR) ?_
    rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, iv, σ', hdec, hms, ⟨hSRq, hSt', hSV', hR', hPt'⟩, hF, hL, hK, hz⟩)
    · exact topMQX_err (⟨e, h1, h2, e', hdec, he⟩) (by rw [h2, h2a]; exact hX0)
    · obtain ⟨hz1, hz2⟩ := hz hmp
      exact ⟨topMX_of_lift2 ⟨iv, hdec, _, hst1, _, perf_tbl_mem blk call don hst1 (Or.inl hms),
        (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR' hPt' h3.1 h3.2.1 h3.2.2 hK
          ⟨hF, hL, Or.inl ⟨iv, Or.inr (Or.inl hms)⟩⟩ hz1 hz2⟩)
        (crelM_after hCR hFI hMO hcap hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
  obtain ⟨o1, o2⟩ := hlO hm hu
  unfold vspace.decode_table
  simp only [vspace.as_table, bind_ok, hm, hu, ↓reduceIte, error.illegal, WP.spec_ok]
  refine topMQX_err (⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩) hX0
  show ExceptT.run (Fl4Spec.decodePageTableInvocation (Z := Unit) slbl (args.map UScalar.bv) (pc.bv, idx)
    (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) excaps) σ = _
  unfold Fl4Spec.decodePageTableInvocation; dsimp only
  rw [if_neg o1, if_neg o2]; rfl

set_option maxHeartbeats 8000000 in
/-- **A mapped PageTable cap whose table is in no set, at `FinXR`** (VsThX's
`decode_invocation_page_table_thX` for `ptr ∉ L1`): `decode_invocation_page_tableXO`
at `FootSR TopSR` with the footprint grown by `ptr`'s frame (`offFr_of`,
VsOffTop's `offStable_footPT`), its domain frame (`dom_of_footO`) and empty
result; the post `VsJPostO`. -/
theorem decode_invocation_page_table_offX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageTableMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap)
    (hlU : lbl = fl4_abi.label.X86PageTableUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr true asid0 va0))
    (hm0 : true = true → asid0 ≠ 0#u64 ∧ va0.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
    (hmu : true = true → Vs.UserV va0)
    (hTy : ∃ f, σ.kheap ptr.bv = some (.archObj (.pageTable f))) (hqa : ptr.val % 4096 = 0)
    (hfr : ∀ b : U64, ptr.val ≤ b.val → b.val < ptr.val + 4096 →
      ¬ OObj st N T C E R B c s σ b ∧ ¬ VObj th P L4 L3 L2 L1 (L.ksb s) b ∧
      ∀ p k, th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hEA : EpSchedApart st T C E R B c s σ)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ a.val) :
    XCap (L := L) arI (fun s' a' σ' => FinXR (L := L) AR (xsetsOf th G P L4 L3 L2 L1 N T C E R B c) s' a' σ' ∧
      VsJPostO (L := L) th P L4 L3 L2 L1 G pc r idx (.PageTable ptr true asid0 va0) ptr s ar σ s' a' σ') s ar σ lbl
      length (cslotAddr (pc.bv, idx)) (.PageTable ptr true asid0 va0) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  obtain ⟨hoff, hnS, hno, hWV, hWO⟩ := offFr_of hS hqa hfr
  have hD := decode_invocation_page_tableXO arI th hS.2.pl s ar σ G hCR hFI hMO
    (SR := FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s
      (fun b => VsFootW0 st th L4 L3 L2 L1 s b ∨ PtW {ptr} b))
    (Q := fun s' => P1.WritesIn st s s' (fun b => VsFootW st th P L4 L3 L2 L1 s b ∨ PtW {ptr} b))
    (fun _ _ _ h => h.2.mono fun _ hb => hb.imp_left fun h => h.toW)
    (X := fun s' a' σ' => FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ s' a' σ' ∧
      VsJPostO (L := L) th P L4 L3 L2 L1 G pc r idx (.PageTable ptr true asid0 va0) ptr s ar σ s' a' σ')
    ⟨vs_x0T hS hR hPt hPI hCur hCR hFI hMO, Or.inl ⟨rfl, rfl, rfl⟩⟩
    (fun _ _ _ hSR hR' hPt' hCR' hFI' hMO' hK hJ hz1 hz2 =>
      ⟨vs_x_afterTO hS hPI hCur (fun b hb => hb.elim (foot0_not_vs hS) (hWV b)) hSR hR' hPt' hCR' hFI' hMO' hK,
        Or.inr ⟨hSR.2.mono fun _ hb => hb.imp_left fun h => h.toW, hpc, hidx, hcap, rfl, hJ, hCR', hFI', hMO',
          hz1, by simp only [TabEmptied, true_and]; first | exact hz2 | exact ⟨rfl, hz2⟩⟩⟩)
    ((vsPtUnmapHyps_top hA).foot (s0 := s) (fun _ h => Or.inl h) hS.2.pl) ⟨hS, P1.WritesIn.refl _ _⟩
    hS.2.vs hS.2.sd hS.2.pt hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact
    hrun args hlen hargs hpc hidx hcap rfl hTy hqa hoff hnS (offStable_footPT (fun b h => Or.inr h) hno) hm0 hmu
    extra excaps hext blk call don fp ci buffer
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  exact Or.inl (DecOKMX.toXD arI (DecOKMQX.toX arI hD fun _ _ _ h => h)
    ⟨WP.spec_mono hD fun res hr => dom_of_footO hS hWO hr.2, dk_spec_arch ⟨_, rfl⟩ hkt⟩
    (okAll_specDec_pageTable fp slbl (args.map UScalar.bv) ci (pc.bv, idx) ptr true asid0 va0 excaps buffer) hDR
    (fun _ _ _ hx hd => ⟨FinXT.toXR G hEA hdom hx.1 hd, hx.2⟩))

set_option maxHeartbeats 8000000 in
/-- **A mapped PageDirectory cap whose table is in no set**, every label (VsDecFrame's
`decode_invocation_page_directoryX` for `ptr ∉ L2`): `Map` errors (the cap is mapped),
`Unmap` is VsPdUnmapOff's `pd_unmap_rel_off` (FL4 zeroes `ptr`'s frame, the spec
empties its table), any other label l4v's `IllegalOperation`. -/
theorem decode_invocation_page_directoryXO (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    {pc : U64} {r : Nat} {idx : List Bool} {ptr asid0 va0 : U64} {mp : Bool}
    (hXs : ∀ s' a' σ', SR s' a' σ' → VsRel P (L.mem s') (L.ksb s') σ' → PtRel L4 L3 L2 L1 (L.mem s') σ' →
      CRel th (L.mem s') σ' G → FinInv th (L.mem s') σ' G → MdbOKV (L.ksb s) (L.mem s') G → KFoot σ σ' →
      VsPostJ th (L.mem s) (L.mem s') (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) σ σ' →
      (∀ i : U64, i.val < 512 → L.mem s' (peA ptr i) = 0#u64) →
      σ'.kheap ptr.bv = some (.archObj (.pageDirectory fun _ => .invalidPDE)) →
      X s' a' σ')
    (hHU : VsPdUnmapHyps st A arI th P L4 L3 L2 L1 SR) (hS : SR s ar σ)
    (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageDirectoryMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (hlU : lbl = fl4_abi.label.X86PageDirectoryUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hpc : th pc = some (.cnode r)) (hidx : idx.length = r)
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr mp asid0 va0)) (hmp : mp = true)
    (hTy : ∃ f, σ.kheap ptr.bv = some (.archObj (.pageDirectory f))) (hqa : ptr.val % 4096 = 0)
    (hoff : ∀ i : U64, i.val < 512 → ¬ PtWAll L4 L3 L2 L1 (peA ptr i) ∧ ¬ SlotW th (peA ptr i) ∧
      ¬ VsWrite P (L.ksb s) (peA ptr i) ∧ OutsideObjects th (peA ptr i))
    (hnS : ¬ (ptr ∈ L4 ∨ ptr ∈ L3 ∨ ptr ∈ L2 ∨ ptr ∈ L1))
    (hoffSt : ∀ s1 s2 a1 σ1 σ2, SR s1 a1 σ1 → L.ksb s1 = L.ksb s → KFoot σ σ1 → P1.WritesIn st s1 s2 (PtW {ptr}) →
      (∃ f f', σ1.kheap ptr.bv = some (.archObj (.pageDirectory f)) ∧ σ2 = updK σ1 ptr.bv (.archObj (.pageDirectory f'))) →
      SR s2 a1 σ2)
    (hm0 : mp = true → asid0 ≠ 0#u64)
    (hmu : mp = true → Vs.UserV va0)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQX (L := L) arI Q X s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  have hCR0 := hCR
  obtain ⟨hSt, hSV, -, -, -⟩ := hCR0
  have hfe : EncWf (.PageDirectory ptr mp asid0 va0) := by
    have h := hcap; rw [capAt_words] at h; exact decode_encWf h
  obtain ⟨xct, hkt0, -⟩ := hSt.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hcur' : ct.bv = σ.curThread := hcur.symm
  have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
    rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
  have hAs : AbsSlot th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  unfold DecOKMQX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci (pc.bv, idx) (.PageDirectory ptr mp asid0 va0) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          (args.map UScalar.bv) ci (pc.bv, idx) (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))
          excaps)) := rfl
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  have hne : ¬ fl4_abi.label.X86PageDirectoryMap = fl4_abi.label.X86PageDirectoryUnmap := by
    unfold fl4_abi.label.X86PageDirectoryMap fl4_abi.label.X86PageDirectoryUnmap; decide
  by_cases hm : lbl = fl4_abi.label.X86PageDirectoryMap
  · subst hm hmp
    have hl := hlM rfl
    unfold vspace.decode_table
    simp only [vspace.as_table, bind_ok, hne, ↓reduceIte]
    rcases hext with ⟨hex, rfl⟩ | ⟨x, vc, vc', xsl, rest, hex, -, -, rfl⟩
    · have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
          (.pageDirectoryCap ptr.bv (some (asid0.bv, va0.bv))) []) σ =
          ({(.error .truncatedMessage, σ)}, False) := pdDecode_trunc hl _ _ _ _ _ (by simp) σ
      rw [hex]
      simp only [bind_ok, error.truncated, WP.spec_ok]
      exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
    · rw [hex]
      simp only [bind_ok]
      by_cases h2 : length >= 2#u64
      · rw [if_pos h2]
        have h2' : 2 ≤ args.length := by
          have : 2 ≤ length.val := by scalar_tac
          omega
        obtain ⟨a0, a1, ar', rfl⟩ : ∃ a0 a1 r', args = a0 :: a1 :: r' := by
          match args, h2' with
          | a0 :: a1 :: r', _ => exact ⟨_, _, _, rfl⟩
        have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl ((a0 :: a1 :: ar').map UScalar.bv) ci
            (pc.bv, idx) (.pageDirectoryCap ptr.bv (some (asid0.bv, va0.bv))) ((vc', xsl) :: rest)) σ =
            ({(.error (.invalidCapability 0), σ)}, False) := pdDecode_mapped hl _ _ _ _ _ _ _ _ σ
        simp only [error.invalid_cap, bind_ok, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, _, htr, Or.inr ⟨0#u64, rfl, rfl⟩⟩) hX0
      · rw [if_neg h2]
        have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
            (.pageDirectoryCap ptr.bv (some (asid0.bv, va0.bv))) ((vc', xsl) :: rest)) σ =
            ({(.error .truncatedMessage, σ)}, False) := pdDecode_trunc hl _ _ _ _ _ (by
              have : length.val < 2 := by scalar_tac
              simp only [List.length_map]; omega) σ
        simp only [error.truncated, bind_ok, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
  by_cases hu : lbl = fl4_abi.label.X86PageDirectoryUnmap
  · subst hu
    have hl := hlU rfl
    have hfinR := fin_iff_of hP hCR hFI hAs hcap (Or.inl ⟨trivial, rfl⟩) rfl (by simp)
      (fun h => by
        have : Fl4Spec.GenObjRef.objRef ptr.bv ∈ Fl4Spec.genObjRefs (absCap (.PageDirectory ptr mp asid0 va0)) :=
          Set.mem_union_left _ (Set.mem_union_left _ ⟨ptr.bv, by simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef], rfl⟩)
        rw [h] at this; exact this)
    refine WP.spec_mono (pd_unmap_rel_off hHU s ar σ hP hVP hD hPP hPS (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inl hq), i, hi, e⟩) (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩) hPI hSt hSV hR hPt hS ct hct hcur' hkt (hrun _ hkt) htcb
      hact hPO ptr asid0 va0 mp hTy hqa hoff hnS hoffSt hfe hm0 hmu hpc hidx hcap hl length buf (args.map UScalar.bv) ci
      extra excaps (is_final_eq s _) hfinR) ?_
    rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, iv, σ', hdec, hms, ⟨hSRq, hSt', hSV', hR', hPt'⟩, hF, hL, hK, hz⟩)
    · exact topMQX_err (⟨e, h1, h2, e', hdec, he⟩) (by rw [h2, h2a]; exact hX0)
    · obtain ⟨hz1, hz2⟩ := hz hmp
      exact ⟨topMX_of_lift2 ⟨iv, hdec, _, hst1, _, perf_tbl_mem blk call don hst1 ((Or.inr ∘ Or.inl) hms),
        (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR' hPt' h3.1 h3.2.1 h3.2.2 hK
          ⟨hF, hL, Or.inl ⟨iv, Or.inr (Or.inr (Or.inl hms))⟩⟩ hz1 hz2⟩)
        (crelM_after hCR hFI hMO hcap hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
  obtain ⟨o1, o2⟩ := hlO hm hu
  unfold vspace.decode_table
  simp only [vspace.as_table, bind_ok, hm, hu, ↓reduceIte, error.illegal, WP.spec_ok]
  refine topMQX_err (⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩) hX0
  show ExceptT.run (Fl4Spec.decodePageDirectoryInvocation (Z := Unit) slbl (args.map UScalar.bv) (pc.bv, idx)
    (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) excaps) σ = _
  unfold Fl4Spec.decodePageDirectoryInvocation; dsimp only
  rw [if_neg o1, if_neg o2]; rfl

set_option maxHeartbeats 8000000 in
/-- **A mapped PageDirectory cap whose table is in no set, at `FinXR`** (VsThX's
`decode_invocation_page_directory_thX` for `ptr ∉ L2`): `decode_invocation_page_directoryXO`
at `FootSR TopSR` with the footprint grown by `ptr`'s frame (`offFr_of`,
VsOffTop's `offStable_footPD`), its domain frame (`dom_of_footO`) and empty
result; the post `VsJPostO`. -/
theorem decode_invocation_page_directory_offX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageDirectoryMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (hlU : lbl = fl4_abi.label.X86PageDirectoryUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr true asid0 va0))
    (hm0 : true = true → asid0 ≠ 0#u64)
    (hmu : true = true → Vs.UserV va0)
    (hTy : ∃ f, σ.kheap ptr.bv = some (.archObj (.pageDirectory f))) (hqa : ptr.val % 4096 = 0)
    (hfr : ∀ b : U64, ptr.val ≤ b.val → b.val < ptr.val + 4096 →
      ¬ OObj st N T C E R B c s σ b ∧ ¬ VObj th P L4 L3 L2 L1 (L.ksb s) b ∧
      ∀ p k, th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hEA : EpSchedApart st T C E R B c s σ)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ a.val) :
    XCap (L := L) arI (fun s' a' σ' => FinXR (L := L) AR (xsetsOf th G P L4 L3 L2 L1 N T C E R B c) s' a' σ' ∧
      VsJPostO (L := L) th P L4 L3 L2 L1 G pc r idx (.PageDirectory ptr true asid0 va0) ptr s ar σ s' a' σ') s ar σ lbl
      length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr true asid0 va0) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  obtain ⟨hoff, hnS, hno, hWV, hWO⟩ := offFr_of hS hqa hfr
  have hD := decode_invocation_page_directoryXO arI th hS.2.pl s ar σ G hCR hFI hMO
    (SR := FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s
      (fun b => VsFootW0 st th L4 L3 L2 L1 s b ∨ PtW {ptr} b))
    (Q := fun s' => P1.WritesIn st s s' (fun b => VsFootW st th P L4 L3 L2 L1 s b ∨ PtW {ptr} b))
    (fun _ _ _ h => h.2.mono fun _ hb => hb.imp_left fun h => h.toW)
    (X := fun s' a' σ' => FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ s' a' σ' ∧
      VsJPostO (L := L) th P L4 L3 L2 L1 G pc r idx (.PageDirectory ptr true asid0 va0) ptr s ar σ s' a' σ')
    ⟨vs_x0T hS hR hPt hPI hCur hCR hFI hMO, Or.inl ⟨rfl, rfl, rfl⟩⟩
    (fun _ _ _ hSR hR' hPt' hCR' hFI' hMO' hK hJ hz1 hz2 =>
      ⟨vs_x_afterTO hS hPI hCur (fun b hb => hb.elim (foot0_not_vs hS) (hWV b)) hSR hR' hPt' hCR' hFI' hMO' hK,
        Or.inr ⟨hSR.2.mono fun _ hb => hb.imp_left fun h => h.toW, hpc, hidx, hcap, rfl, hJ, hCR', hFI', hMO',
          hz1, by simp only [TabEmptied, true_and]; first | exact hz2 | exact ⟨rfl, hz2⟩⟩⟩)
    ((vsPdUnmapHyps_top hA).foot (s0 := s) (fun _ h => Or.inl h) hS.2.pl) ⟨hS, P1.WritesIn.refl _ _⟩
    hS.2.vs hS.2.sd hS.2.pt hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact
    hrun args hlen hargs hpc hidx hcap rfl hTy hqa hoff hnS (offStable_footPD (fun b h => Or.inr h) hno) hm0 hmu
    extra excaps hext blk call don fp ci buffer
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  exact Or.inl (DecOKMX.toXD arI (DecOKMQX.toX arI hD fun _ _ _ h => h)
    ⟨WP.spec_mono hD fun res hr => dom_of_footO hS hWO hr.2, dk_spec_arch ⟨_, rfl⟩ hkt⟩
    (okAll_specDec_pageDirectory fp slbl (args.map UScalar.bv) ci (pc.bv, idx) ptr true asid0 va0 excaps buffer) hDR
    (fun _ _ _ hx hd => ⟨FinXT.toXR G hEA hdom hx.1 hd, hx.2⟩))

set_option maxHeartbeats 8000000 in
/-- **A mapped Pdpt cap whose table is in no set**, every label (VsDecFrame's
`decode_invocation_pdptX` for `ptr ∉ L3`): `Map` errors (the cap is mapped),
`Unmap` is VsPdptUnmapOff's `pdpt_unmap_rel_off` (FL4 zeroes `ptr`'s frame, the spec
empties its table), any other label l4v's `IllegalOperation`. -/
theorem decode_invocation_pdptXO (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 : Set U64} {SR : S → A → Fl4Spec.State Unit → Prop}
    {Q : S → Prop} (hQ : ∀ s' a' σ', SR s' a' σ' → Q s')
    {X : S → A → Fl4Spec.State Unit → Prop} (hX0 : X s ar σ)
    {pc : U64} {r : Nat} {idx : List Bool} {ptr asid0 va0 : U64} {mp : Bool}
    (hXs : ∀ s' a' σ', SR s' a' σ' → VsRel P (L.mem s') (L.ksb s') σ' → PtRel L4 L3 L2 L1 (L.mem s') σ' →
      CRel th (L.mem s') σ' G → FinInv th (L.mem s') σ' G → MdbOKV (L.ksb s) (L.mem s') G → KFoot σ σ' →
      VsPostJ th (L.mem s) (L.mem s') (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) σ σ' →
      (∀ i : U64, i.val < 512 → L.mem s' (peA ptr i) = 0#u64) →
      σ'.kheap ptr.bv = some (.archObj (.pdPointerTable fun _ => .invalidPDPTE)) →
      X s' a' σ')
    (hHU : VsPdptUnmapHyps st A arI th P L4 L3 L2 L1 SR) (hS : SR s ar σ)
    (hVP : VsPlaced P (L.ksb s)) (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b) (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PDPTMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap)
    (hlU : lbl = fl4_abi.label.X86PDPTUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hpc : th pc = some (.cnode r)) (hidx : idx.length = r)
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr mp asid0 va0)) (hmp : mp = true)
    (hTy : ∃ f, σ.kheap ptr.bv = some (.archObj (.pdPointerTable f))) (hqa : ptr.val % 4096 = 0)
    (hoff : ∀ i : U64, i.val < 512 → ¬ PtWAll L4 L3 L2 L1 (peA ptr i) ∧ ¬ SlotW th (peA ptr i) ∧
      ¬ VsWrite P (L.ksb s) (peA ptr i) ∧ OutsideObjects th (peA ptr i))
    (hnS : ¬ (ptr ∈ L4 ∨ ptr ∈ L3 ∨ ptr ∈ L2 ∨ ptr ∈ L1))
    (hoffSt : ∀ s1 s2 a1 σ1 σ2, SR s1 a1 σ1 → L.ksb s1 = L.ksb s → KFoot σ σ1 → P1.WritesIn st s1 s2 (PtW {ptr}) →
      (∃ f f', σ1.kheap ptr.bv = some (.archObj (.pdPointerTable f)) ∧ σ2 = updK σ1 ptr.bv (.archObj (.pdPointerTable f'))) →
      SR s2 a1 σ2)
    (hm0 : mp = true → asid0 ≠ 0#u64)
    (hmu : mp = true → Vs.UserV va0)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKMQX (L := L) arI Q X s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer := by
  have hCR0 := hCR
  obtain ⟨hSt, hSV, -, -, -⟩ := hCR0
  have hfe : EncWf (.Pdpt ptr mp asid0 va0) := by
    have h := hcap; rw [capAt_words] at h; exact decode_encWf h
  obtain ⟨xct, hkt0, -⟩ := hSt.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hcur' : ct.bv = σ.curThread := hcur.symm
  have hst1 : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ =
      ({((), Notif.stsAct (Notif.updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv)}, False) := by
    rw [hcur]; exact Notif.setThreadState_eq .restart hkt0
  have hAs : AbsSlot th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  unfold DecOKMQX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci (pc.bv, idx) (.Pdpt ptr mp asid0 va0) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.spec (Fl4Spec.archDecodeInvocation (Z := Unit) slbl
          (args.map UScalar.bv) ci (pc.bv, idx) (.pdPointerTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))
          excaps)) := rfl
  rw [hspec]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  have hne : ¬ fl4_abi.label.X86PDPTMap = fl4_abi.label.X86PDPTUnmap := by
    unfold fl4_abi.label.X86PDPTMap fl4_abi.label.X86PDPTUnmap; decide
  by_cases hm : lbl = fl4_abi.label.X86PDPTMap
  · subst hm hmp
    have hl := hlM rfl
    unfold vspace.decode_table
    simp only [vspace.as_table, bind_ok, hne, ↓reduceIte]
    rcases hext with ⟨hex, rfl⟩ | ⟨x, vc, vc', xsl, rest, hex, -, -, rfl⟩
    · have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
          (.pdPointerTableCap ptr.bv (some (asid0.bv, va0.bv))) []) σ =
          ({(.error .truncatedMessage, σ)}, False) := pdptDecode_trunc hl _ _ _ _ _ (by simp) σ
      rw [hex]
      simp only [bind_ok, error.truncated, WP.spec_ok]
      exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
    · rw [hex]
      simp only [bind_ok]
      by_cases h2 : length >= 2#u64
      · rw [if_pos h2]
        have h2' : 2 ≤ args.length := by
          have : 2 ≤ length.val := by scalar_tac
          omega
        obtain ⟨a0, a1, ar', rfl⟩ : ∃ a0 a1 r', args = a0 :: a1 :: r' := by
          match args, h2' with
          | a0 :: a1 :: r', _ => exact ⟨_, _, _, rfl⟩
        have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl ((a0 :: a1 :: ar').map UScalar.bv) ci
            (pc.bv, idx) (.pdPointerTableCap ptr.bv (some (asid0.bv, va0.bv))) ((vc', xsl) :: rest)) σ =
            ({(.error (.invalidCapability 0), σ)}, False) := pdptDecode_mapped hl _ _ _ _ _ _ _ _ σ
        simp only [error.invalid_cap, bind_ok, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, _, htr, Or.inr ⟨0#u64, rfl, rfl⟩⟩) hX0
      · rw [if_neg h2]
        have htr : ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci (pc.bv, idx)
            (.pdPointerTableCap ptr.bv (some (asid0.bv, va0.bv))) ((vc', xsl) :: rest)) σ =
            ({(.error .truncatedMessage, σ)}, False) := pdptDecode_trunc hl _ _ _ _ _ (by
              have : length.val < 2 := by scalar_tac
              simp only [List.length_map]; omega) σ
        simp only [error.truncated, bind_ok, WP.spec_ok]
        exact topMQX_err (⟨_, rfl, rfl, .truncatedMessage, htr, Or.inl trivial⟩) hX0
  by_cases hu : lbl = fl4_abi.label.X86PDPTUnmap
  · subst hu
    have hl := hlU rfl
    have hfinR := fin_iff_of hP hCR hFI hAs hcap (Or.inl ⟨trivial, rfl⟩) rfl (by simp)
      (fun h => by
        have : Fl4Spec.GenObjRef.objRef ptr.bv ∈ Fl4Spec.genObjRefs (absCap (.Pdpt ptr mp asid0 va0)) :=
          Set.mem_union_left _ (Set.mem_union_left _ ⟨ptr.bv, by simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef], rfl⟩)
        rw [h] at this; exact this)
    refine WP.spec_mono (pdpt_unmap_rel_off hHU s ar σ hP hVP hD hPP hPS (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inl hq, i, hi, e⟩) (fun b ⟨q, hq, i, hi, e⟩ => hPV b ⟨q, Or.inr (Or.inl hq), i, hi, e⟩) hPI hSt hSV hR hPt hS ct hct hcur' hkt (hrun _ hkt) htcb
      hact hPO ptr asid0 va0 mp hTy hqa hoff hnS hoffSt hfe hm0 hmu hpc hidx hcap hl length buf (args.map UScalar.bv) ci
      extra excaps (is_final_eq s _) hfinR) ?_
    rintro res (⟨e, e', h1, he, hdec, h2, h2a⟩ | ⟨h1, iv, σ', hdec, hms, ⟨hSRq, hSt', hSV', hR', hPt'⟩, hF, hL, hK, hz⟩)
    · exact topMQX_err (⟨e, h1, h2, e', hdec, he⟩) (by rw [h2, h2a]; exact hX0)
    · obtain ⟨hz1, hz2⟩ := hz hmp
      exact ⟨topMX_of_lift2 ⟨iv, hdec, _, hst1, _, perf_tbl_mem blk call don hst1 ((Or.inr ∘ Or.inr) hms),
        (fun h3 => ⟨⟨th, G, Or.inl ⟨h1, [], rfl⟩, hP, h3⟩, hXs _ _ _ hSRq hR' hPt' h3.1 h3.2.1 h3.2.2 hK
          ⟨hF, hL, Or.inl ⟨iv, Or.inr (Or.inr (Or.inr hms))⟩⟩ hz1 hz2⟩)
        (crelM_after hCR hFI hMO hcap hSt' hSV' hF hL hK rfl)⟩, Or.inr (hQ _ _ _ hSRq)⟩
  obtain ⟨o1, o2⟩ := hlO hm hu
  unfold vspace.decode_table
  simp only [vspace.as_table, bind_ok, hm, hu, ↓reduceIte, error.illegal, WP.spec_ok]
  refine topMQX_err (⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩) hX0
  show ExceptT.run (Fl4Spec.decodePdptInvocation (Z := Unit) slbl (args.map UScalar.bv) (pc.bv, idx)
    (.pdPointerTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) excaps) σ = _
  unfold Fl4Spec.decodePdptInvocation; dsimp only
  rw [if_neg o1, if_neg o2]; rfl

set_option maxHeartbeats 8000000 in
/-- **A mapped Pdpt cap whose table is in no set, at `FinXR`** (VsThX's
`decode_invocation_pdpt_thX` for `ptr ∉ L3`): `decode_invocation_pdptXO`
at `FootSR TopSR` with the footprint grown by `ptr`'s frame (`offFr_of`,
VsOffTop's `offStable_footPDPT`), its domain frame (`dom_of_footO`) and empty
result; the post `VsJPostO`. -/
theorem decode_invocation_pdpt_offX (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s)) (hCur : CurOK st th s σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PDPTMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap)
    (hlU : lbl = fl4_abi.label.X86PDPTUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr true asid0 va0))
    (hm0 : true = true → asid0 ≠ 0#u64)
    (hmu : true = true → Vs.UserV va0)
    (hTy : ∃ f, σ.kheap ptr.bv = some (.archObj (.pdPointerTable f))) (hqa : ptr.val % 4096 = 0)
    (hfr : ∀ b : U64, ptr.val ≤ b.val → b.val < ptr.val + 4096 →
      ¬ OObj st N T C E R B c s σ b ∧ ¬ VObj th P L4 L3 L2 L1 (L.ksb s) b ∧
      ∀ p k, th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hEA : EpSchedApart st T C E R B c s σ)
    (hdom : ∀ a, IWords N T E R B a → a.val < (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ a.val) :
    XCap (L := L) arI (fun s' a' σ' => FinXR (L := L) AR (xsetsOf th G P L4 L3 L2 L1 N T C E R B c) s' a' σ' ∧
      VsJPostO (L := L) th P L4 L3 L2 L1 G pc r idx (.Pdpt ptr true asid0 va0) ptr s ar σ s' a' σ') s ar σ lbl
      length (cslotAddr (pc.bv, idx)) (.Pdpt ptr true asid0 va0) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := by
  obtain ⟨hoff, hnS, hno, hWV, hWO⟩ := offFr_of hS hqa hfr
  have hD := decode_invocation_pdptXO arI th hS.2.pl s ar σ G hCR hFI hMO
    (SR := FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s
      (fun b => VsFootW0 st th L4 L3 L2 L1 s b ∨ PtW {ptr} b))
    (Q := fun s' => P1.WritesIn st s s' (fun b => VsFootW st th P L4 L3 L2 L1 s b ∨ PtW {ptr} b))
    (fun _ _ _ h => h.2.mono fun _ hb => hb.imp_left fun h => h.toW)
    (X := fun s' a' σ' => FinXT (L := L) th P L4 L3 L2 L1 N T C E R B c AR (L.ksb s) σ s' a' σ' ∧
      VsJPostO (L := L) th P L4 L3 L2 L1 G pc r idx (.Pdpt ptr true asid0 va0) ptr s ar σ s' a' σ')
    ⟨vs_x0T hS hR hPt hPI hCur hCR hFI hMO, Or.inl ⟨rfl, rfl, rfl⟩⟩
    (fun _ _ _ hSR hR' hPt' hCR' hFI' hMO' hK hJ hz1 hz2 =>
      ⟨vs_x_afterTO hS hPI hCur (fun b hb => hb.elim (foot0_not_vs hS) (hWV b)) hSR hR' hPt' hCR' hFI' hMO' hK,
        Or.inr ⟨hSR.2.mono fun _ hb => hb.imp_left fun h => h.toW, hpc, hidx, hcap, rfl, hJ, hCR', hFI', hMO',
          hz1, by simp only [TabEmptied, true_and]; first | exact hz2 | exact ⟨rfl, hz2⟩⟩⟩)
    ((vsPdptUnmapHyps_top hA).foot (s0 := s) (fun _ h => Or.inl h) hS.2.pl) ⟨hS, P1.WritesIn.refl _ _⟩
    hS.2.vs hS.2.sd hS.2.pt hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact
    hrun args hlen hargs hpc hidx hcap rfl hTy hqa hoff hnS (offStable_footPDPT (fun b h => Or.inr h) hno) hm0 hmu
    extra excaps hext blk call don fp ci buffer
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  exact Or.inl (DecOKMX.toXD arI (DecOKMQX.toX arI hD fun _ _ _ h => h)
    ⟨WP.spec_mono hD fun res hr => dom_of_footO hS hWO hr.2, dk_spec_arch ⟨_, rfl⟩ hkt⟩
    (okAll_specDec_pdpt fp slbl (args.map UScalar.bv) ci (pc.bv, idx) ptr true asid0 va0 excaps buffer) hDR
    (fun _ _ _ hx hd => ⟨FinXT.toXR G hEA hdom hx.1 hd, hx.2⟩))

end

end

end Fl4Proofs.P3

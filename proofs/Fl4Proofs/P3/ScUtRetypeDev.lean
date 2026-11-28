/-
P3: **the retype from a device untyped** (losfair/FL4#34): `devRetype_holds`
proves `DevRetypeGap` (formerly a named premise [W]) for any `P3Ok` giving
`UtJoint`, so `utRetypeP3_of` needs it no more.

Since #34 a device untyped's pointer `paddr + PPTR_BASE` may lie in the
kernel image (physical [510, 512) GiB: the kernel-state block, the nodes, the
idle TCBs) or wrap to the lower half, so none of the RAM placement facts
(`UtCapP3`) hold of it. None is needed: FL4 retypes a device untyped only into
frames or untypeds (`decode`), whose creation writes nothing but caps
(`create_object_eq`), and resets it by rewriting its free index only
(`reset_untyped_dev`); the kernel never reads or writes through a device
pointer. So the creation writes only slot words (`create_dev_frame`), and P1's
`CreateOK` holds over `H` with an empty window (`createOK_dev`, by
`createOK_core` with no object: no drop, no new object, the window put at the
first node's base, outside every `H` object).
-/
import Fl4Proofs.P3.ScUtRetype
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

attribute [local step] set_cap_spec

/-- **`insert_new_cap` leaves the parent's next link at the new slot** (its
last write, `set_next`), whatever the words before. -/
theorem insert_new_next {th : TypedHeap} (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest) :
    cdt.insert_new_cap st s src dest c ⦃ s' => nextOf (L.mem s') src = dest ⦄ := by
  have key : ∀ s4 : S, obj.Slot.set_next st src s4 dest ⦃ s' => nextOf (L.mem s') src = dest ⦄ := by
    intro s4
    rw [set_next_eq, WP.spec_ok]
    show (⟨sextF (L.mem _ (wordOf src 24#u64)).bv⟩ : U64) = dest
    rw [P1.LawfulStore.mem_wr_val (slot_word_aligned hP hs off24) (slot_word_aligned hP hs off24), if_pos rfl]
    show (⟨sextF (setNextF _ dest.bv)⟩ : U64) = dest
    rw [sextF_setNextF, sextF_canonical _ (hd.canonical hP)]
  unfold cdt.insert_new_cap
  step; step; step; step
  simp only [obj.Slot.is_null, bind_ok]
  split
  · simp only [bind_ok]; exact key _
  · step
    exact key _

/-- **`create_new_objects` for a device untyped** (types 0, 9, 10, 11:
untypeds and frames, which `decode` alone allows of a device cap): each object
is only a cap (`create_object_eq`) inserted after the parent, so only slot
words of `th` are written: the parent's, the destination's and the parent's
old next slot's (null or a slot: the parent's next is the previous new slot
after each insertion, `insert_new_next`). -/
theorem create_dev_frame {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (hP : Placed th)
    (nt us : U64) (hn : nt.val = 0 ∨ (9 ≤ nt.val ∧ nt.val ≤ 11)) (hus : us.val < 64)
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (off win base src : U64) (hwin : off.val + win.val ≤ 2 ^ r) (hs : IsSlot th src) (s : S)
    (hnx : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src)) :
    objects.create_new_objects st arI s ar nt src dest off win base us true ⦃ res =>
      WFrame (L := L) s res.1 (SlotSpan th) ⦄ := by
  have hn14 : nt.val < 14 := by omega
  unfold objects.create_new_objects
  rw [object_size_eq nt us hn14 hus]
  simp only [bind_ok]
  let I : S → A' → Nat → Prop := fun s1 _ _ => WFrame (L := L) s s1 (SlotSpan th) ∧
    (nextOf (L.mem s1) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s1) src))
  refine WP.spec_mono (create_new_objects_loopG arI ar s nt src dest off win base us true _ 0#u64 I
    (fun s2 a2 _ i => I s2 a2 i)
    (fun s1 a1 _ _ hI => by rw [create_object_eq arI s1 a1 nt _ us true (by omega)]; exact (WP.spec_ok _).2 hI)
    ?_ ⟨WFrame.refl s _, hnx⟩) fun _ h => h.1
  rintro s1 a1 c i hit' ⟨hW, hx⟩
  have hi4 : (core.num.U64.wrapping_add off i).bv = BitVec.ofNat 64 (off.val + i.val) := by
    rw [bv_eq_ofNat]; congr 1
    have : off.val + i.val < 2 ^ 64 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show r ≤ 64 by omega); omega
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
  rw [hi4]
  have hds : IsSlot th (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val))) :=
    ⟨dest, off.val + i.val, Or.inl ⟨r, hdest, by omega⟩, rfl⟩
  refine WP.spec_mono (WP.spec_and (insert_new_frame hP s1 _ _ _ hs hds hx)
    (WP.spec_and (insert_new_cap_kc s1 _ _ _) (insert_new_next hP s1 _ _ _ hs hds))) fun s3 ⟨hfr, hk, hn3⟩ => ?_
  refine ⟨hW.trans ⟨hk.1, hk.2, fun w hw hnp => hfr w hw (fun a ha hin => by
    refine hnp ⟨a, ?_, hin.1, hin.2⟩
    rcases ha with e | e | ⟨h0, e⟩
    · rw [e]; exact hs
    · rw [e]; exact hds
    · rw [e]; exact hx.resolve_left h0)⟩, Or.inr (by rw [hn3]; exact hds)⟩

/-- **The creation from a device untyped, without a reset** (from `sR`, the
cap at `slot` a device untyped of some free index, its next link null or a
slot): `Ok`, and only slot words of `th` written (the untyped cap's free
index, `set_cap_frame`, then `create_dev_frame`). -/
theorem retype_dev_frame {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (hP : Placed th)
    (sR : S) (slot : U64) (hsl : IsSlot th slot) {ptr sb fi1 : U64}
    (hcR : capAt (L.mem sR) slot = ok (.Untyped ptr sb fi1 true))
    (hnxR : nextOf (L.mem sR) slot = 0#u64 ∨ IsSlot th (nextOf (L.mem sR) slot))
    (nt us : U64) (hn : nt.val = 0 ∨ (9 ≤ nt.val ∧ nt.val ≤ 11)) (hus : us.val < 64)
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (off win base : U64) (hwin : off.val + win.val ≤ 2 ^ r) :
    untyped.retype st arI sR ar slot false base nt us dest off win true ⦃ res =>
      res.1 = .Ok () ∧ WFrame (L := L) sR res.2.1 (SlotSpan th) ⦄ := by
  have hz : zOf nt.val us.val < 64 := by
    rcases hn with h | ⟨h1, h2⟩
    · rw [show zOf nt.val us.val = us.val by simp [zOf, h]]; exact hus
    · unfold zOf; split_ifs <;> omega
  obtain ⟨total, -, he⟩ := retype_noreset_eq arI sR ar slot base nt us dest off win true (by omega) hus hz
    ptr sb fi1 true hcR
  rw [he]
  have h24 := slot_word_val hP hsl off24
  have h0 := slot_word_aligned hP hsl off0
  rw [wordOf_zero] at h0
  have hfit := hsl.fit hP
  refine WP.spec_bind (set_cap_frame sR slot _ h0 (by omega)) fun s1 hW1 => ?_
  have hnx1 : nextOf (L.mem s1) slot = nextOf (L.mem sR) slot := by
    unfold nextOf
    rw [hW1.2.2 _ (slot_word_aligned hP hsl off24) (fun h => by
      have h2 := h.2; rw [h24] at h2; simp only [show (24#u64 : U64).val = 24 from rfl] at h2; omega)]
  refine WP.spec_bind (create_dev_frame arI ar th hP nt us hn hus hdest hr off win base slot hwin hsl s1
    (hnx1 ▸ hnxR)) ?_
  rintro ⟨s2, a2⟩ hW2
  exact (WP.spec_ok _).2 ⟨rfl, (hW1.mono fun w ⟨h1, h2⟩ => ⟨slot, hsl, h1, by omega⟩).trans hW2⟩

/-- **P1's `CreateOK` for a device creation** (`createOK_core` with an empty
window at the first node's base `ksb + 13568`: no `H` object meets it, as
none straddles a node; no object is dropped or made; the writes are slot
words, P1 cap-slot words off the debug links and the nodes). -/
theorem createOK_dev {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs : Set U64} {s0 sR s' : S}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slot : obj.Slot} {cap : capability.Cap}
    {th : TypedHeap} {G : MdbGhost} {D : Set U64} {σ : Fl4Spec.State Unit} {pp : U64} {rs : Nat} {idx : List Bool}
    (J : UtJoint (L := L) arI H Cs s0 slot cap extra th G D σ pp rs idx) (h0Cs : 0#u64 ∈ Cs)
    {Ac : Set U64}
    (hbR : BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac sR)
    (hkR : L.ksb sR = L.ksb s0) (hcwR : L.curW sR = L.curW s0) (hcsR : L.cscW sR = L.cscW s0)
    (hW : WFrame (L := L) sR s' (SlotSpan th)) :
    CreateOK st H Cs sR s' := by
  obtain ⟨Tr, C, hJP⟩ := J.jpl
  have hnb : ∀ c, L.nodeBase sR c = L.nodeBase s0 c := fun c => by simp [LawfulStore.nodeBase, hkR]
  have hks := J.ksbFit
  have hno : ∀ q k, H q = some k → ¬ RegionD H ((L.ksb s0).val + 13568) ((L.ksb s0).val + 13568 + 0 * 1) q := by
    intro q k hq hR
    unfold RegionD MeetsR at hR
    rw [hq] at hR
    simp only [Option.elim] at hR
    have := J.hnd q k hq 0#u64 h0Cs
    have e0 : (0#u64 : U64).val = 0 := rfl
    simp only [LawfulStore.nodeBase, e0, Nat.zero_mul, Nat.add_zero] at this
    omega
  refine createOK_core (T := False) (pml4 := False) (Z := False) (n := 0) (us := 0) J.placed J.heap
    (dropOK_none J.heap J.h0 hno (by simp [hcwR, J.curH]) (by rw [hcsR]; exact J.cscH))
    ⟨fun c hc => Or.inr (by simp only [LawfulStore.nodeBase, hkR] <;> omega), Or.inl (by rw [hkR] <;> omega)⟩
    hbR.2.2.1.2.2.tm (slotCapW_of_in J.placed J.heap (fun a ha => hJP.slot_in ha))
    (fun v hv => ?_) (hW.mono fun v h => Or.inl (Or.inr h)) (fun h => h.elim) (by simp [zOf]) (Nat.mod_one _)
    (by simp) (fun hs _ => by simp [newKind] at hs) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) h0Cs (by omega) (by omega)
  obtain ⟨o1, o2⟩ := slot_word_off hJP J.hnd hv
  exact ⟨o1, fun c hc => by rw [hnb]; exact o2 c hc⟩

set_option maxHeartbeats 1000000 in
/-- **The device retype holds** (was the named premise `DevRetypeGap` [W],
losfair/FL4#34): for any `P3Ok` giving the joint state (`UtOkRU`), P1's
`UtRetypeP3.run` conclusion for a device untyped: no `ResetOK` is asked, the
cap is at its slot after the restart (`UtJoint.restart`), and the retype is
`Ok` with `CreateOK` over `H` (`createOK_dev`) from the state after the
optional reset (`reset_untyped_dev_blk`: only the cap rewritten). -/
theorem devRetype_holds {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs U : Set U64}
    {P3Ok : S → U64 → capability.Cap → Aeneas.Std.Array obj.Slot 3#usize → Prop}
    (hOk : UtOkRU (L := L) arI H Cs P3Ok) (h0Cs : 0#u64 ∈ Cs) :
    DevRetypeGap (L := L) arI H Cs U P3Ok := by
  intro Ac s0 s a extra slot ptr sb fi reset aligned nt us dest off win hP3 hrs hDP hCSW hUA hC0
  obtain ⟨th, G, D, σ, pp, rs, idx, J, -⟩ := hOk _ _ _ _ _ hP3 hrs
  obtain ⟨-, hks, -, hcapS⟩ := J.restart hrs
  obtain ⟨-, Ac', hbx, hcw, hcs, -, -, -⟩ := hC0
  have hb : BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac' s := ⟨hbx.1, hbx.2.1, hbx.2.2.1, hbx.2.2.2.2, hbx.2.2.2.1⟩
  have hcapS' : obj.Slot.cap st slot s = ok (.Untyped ptr sb fi true) := by rw [slot_cap_eq]; exact hcapS
  refine ⟨fun _ h => absurd h (by simp), fun _ => hcapS', ?_⟩
  -- the decode's facts
  obtain ⟨x, hxe, hx0, idx', dep, val, hsz, -, hdst, hemp, hrsE, hal, hmem, hdev⟩ := hUA
  obtain ⟨hxs, c, a0, hc, hca, hcv⟩ := J.extraRel x hxe hx0
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [J.idxLen] using J.node)⟩
  have hcap0 : capAt (L.mem s0) (cslotAddr (pp.bv, idx)) = ok (.Untyped ptr sb fi true) := by
    rw [← J.slotEq]; exact J.capEq
  rw [J.slotEq] at hrsE
  obtain ⟨fiv, hfiv⟩ : ∃ fiv : U64, fiv = if reset then 0#u64 else fi := ⟨_, rfl⟩
  obtain ⟨t, r, hctx, -⟩ := retCtx_of_args J.rel J.valid J.placed J.links J.cdt J.mdb hAs hcap0 hc hca hcv hxs hsz
    hdst hemp hrsE hal hmem hdev fiv hfiv
  have hnt : nt.val = 0 ∨ (9 ≤ nt.val ∧ nt.val ≤ 11) := by
    rcases hdev rfl with h | h
    · rw [is_frame_type_eq] at h
      simp only [ok.injEq, decide_eq_true_eq] at h
      omega
    · left; rw [h] <;> first | rfl | simp [fl4_abi.consts.object.Untyped]
  have hus := hctx.size.1
  obtain ⟨hdest, hr64, -, -⟩ := hctx.cnode
  have hwin := hctx.window.2.2
  have hsl : IsSlot th slot := by rw [J.slotEq]; exact hAs.isSlot
  -- the invoked slot's next link: null or a slot, kept by the restart
  obtain ⟨-, hxm, -⟩ := J.slot_mem (by simp)
  have hnx0 : nextOf (L.mem s0) slot = 0#u64 ∨ IsSlot th (nextOf (L.mem s0) slot) := by
    rcases J.links.next_mem hxm with h | ⟨h1, -⟩
    · exact Or.inl h
    · exact Or.inr ((J.links.members _).1 h1).1
  obtain ⟨s2, hs2, hSS⟩ := spec_exists (set_thread_state_slots (L := L) th J.placed s0 (L.curW s0)
    sched.TS_RESTART J.curT J.act)
  rw [hrs] at hs2; cases eq_of_ok_eq hs2
  have hnxs : nextOf (L.mem s) slot = nextOf (L.mem s0) slot := by
    unfold nextOf; rw [(hSS slot hsl).2.2.2]
  have eH : ∀ b : Bool, utHeap H (b && !true) ptr sb = H := fun b => by cases b <;> simp [utHeap]
  -- the creation from the state after the optional reset
  have create : ∀ (sR : S) (fi1 : U64), capAt (L.mem sR) slot = ok (.Untyped ptr sb fi1 true) →
      (nextOf (L.mem sR) slot = 0#u64 ∨ IsSlot th (nextOf (L.mem sR) slot)) →
      BlkOK st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac' sR → L.ksb sR = L.ksb s0 → L.curW sR = L.curW s0 → L.cscW sR = L.cscW s0 →
      untyped.retype st arI sR a slot false aligned nt us dest off win true ⦃ r s' a' =>
        r = .Ok () ∧ CreateOK st H Cs sR s' ⦄ := by
    intro sR fi1 hcR hnxR hbR hkR hcwR hcsR
    refine WP.spec_mono (retype_dev_frame arI a th J.placed sR slot hsl hcR hnxR nt us hnt hus hdest hr64 off win
      aligned hwin) fun ⟨r0, s', a'⟩ ⟨h1, hW⟩ => ⟨h1, createOK_dev J h0Cs hbR hkR hcwR hcsR hW⟩
  cases reset
  · refine WP.spec_mono (create s fi hcapS (by rw [hnxs]; exact hnx0) hb hks hcw hcs) fun ⟨r0, s', a'⟩ ⟨h1, h2⟩ => ?_
    exact Or.inr ⟨h1, s, Or.inl ⟨rfl, rfl⟩, by rw [eH]; exact h2⟩
  · rw [retype_true_eq]
    obtain ⟨s1, h1, hb1, hK1, -⟩ := reset_untyped_dev_blk arI a hb hCSW hcapS'
    obtain ⟨s1', h1', hor⟩ := reset_untyped_dev arI s a slot ptr sb fi hCSW hcapS'
    rw [h1] at h1'
    simp only [ok.injEq, Prod.mk.injEq, true_and, and_true] at h1'
    subst h1'
    rw [h1]
    simp only [bind_ok]
    have hk1 : L.ksb s1 = L.ksb s0 := by
      rcases hor with rfl | e
      · exact hks
      · obtain ⟨v, hv, hP⟩ := spec_exists (set_cap_kc (L := L) slot s (.Untyped ptr sb 0#u64 true))
        rw [e] at hv; cases eq_of_ok_eq hv; exact hP.1.trans hks
    obtain ⟨fi1, hc1, hn1⟩ : ∃ fi1, capAt (L.mem s1) slot = ok (.Untyped ptr sb fi1 true) ∧
        nextOf (L.mem s1) slot = nextOf (L.mem s) slot := by
      rcases hor with rfl | e
      · exact ⟨fi, hcapS, rfl⟩
      · obtain ⟨v, hv, hP⟩ := spec_exists (set_cap_spec (L := L) slot s (.Untyped ptr sb 0#u64 true))
        rw [e] at hv; cases eq_of_ok_eq hv
        subst hP
        have h24 := slot_word_val J.placed hsl off24
        have h0 := slot_word_aligned J.placed hsl off0
        rw [wordOf_zero] at h0
        have hfit := hsl.fit J.placed
        have h8 : (core.num.U64.wrapping_add slot 8#u64).val = slot.val + 8 := wa8_val (by omega)
        have ha8 : P1.Aligned (core.num.U64.wrapping_add slot 8#u64) := by
          unfold P1.Aligned at h0 ⊢; rw [h8]; omega
        refine ⟨0#u64, capAt_wr2_self s slot _ ?_ h0 ha8 (by rw [h8]; omega), ?_⟩
        · have hc' := hcapS
          rw [capAt_words] at hc'
          have he : EncWf (.Untyped ptr sb fi true) := decode_encWf hc'
          exact ⟨he.1, he.2⟩
        · unfold nextOf
          rw [mem_wr2 _ _ _ _ _ _ h0 ha8 (slot_word_aligned J.placed hsl off24),
            if_neg (by rw [h8, h24]; simp), if_neg (by rw [h24]; simp)]
    refine WP.spec_mono (create s1 fi1 hc1 (by rw [hn1, hnxs]; exact hnx0) hb1 hk1 (hK1.1.trans hcw)
      (hK1.2.1.trans hcs)) fun ⟨r0, s', a'⟩ ⟨h2, h3⟩ => ?_
    exact Or.inr ⟨h2, s1, Or.inr ⟨trivial, a, rfl⟩, by rw [eH]; exact h3⟩

/-- **P1's `UtRetypeP3` with `UtP3Ok` as `P3Ok`** (`utRetypeP3_gen`, the
device retype by `devRetype_holds`). -/
theorem utRetypeP3_of [Fl4Proofs.P1.PlainStore st] {A' : Type} (arI : machine.Arch A') (hA : P0.ArchTotal arI) (H : Heap) (Cs U : Set U64)
    (Adm : PSets → Prop) (hAdm : ∀ H' : Heap, HeapOK H' → H' 0#u64 = none → Adm (PSets.ofHeap H'))
    (h0Cs : 0#u64 ∈ Cs) (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    /- [W-false] not true in reachable states (gap K10: the spec cannot preempt from every state; ∀ ksb); only the pre-J XTop reset path uses it; superseded by the J-level reset -/
    (hPPW : ∀ (th : TypedHeap) (s0 : S) (p sb k0 v0 : U64), PPHyp (L := L) arI th p sb (fun t => L.ksb t = k0 ∧
      L.mem t (L.nodeAt s0 0#u64 layout.node.DEBUG_TCBS) = v0))
    (hRU : RegionUnref (L := L) arI H Cs) (hDbg : UtDbgTcb (L := L) arI H Cs)
    (hVtx : UtVtx (L := L) arI H Cs U) :
    UtRetypeP3 st arI Adm H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits U
      (UtP3Ok (L := L) arI H Cs) :=
  utRetypeP3_gen arI hA H Cs U Adm hAdm h0Cs hrcb hppS hPPW _ (utOkRU_of hRU) hDbg hVtx
    (devRetype_holds (utOkRU_of hRU) h0Cs)

end

end

end Fl4Proofs.P3.Sched

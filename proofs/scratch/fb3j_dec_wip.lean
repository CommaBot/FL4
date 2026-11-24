/-
fb3j WIP (NOT BUILT, NOT IN THE ROOT): the FrameBatch decode walk of
`decode_invocation_pml4_fbJV` against SpecFbDec's `fbDecP` (XTopJointVsFb),
with the loop and tail stated as `fb_loopJ`. Built through the extra-cap
checks in fb3j-m10 (KENTRY-PLAN fb3j); paste into XTopJointVsFb in place of
the `fail` stub to continue. Known open points in this text: the `hq`
witness (`exact ⟨_, rfl, rfl⟩`, "Eq.refl has no explicit fields") and the
cost of the three `tail` uses (8M-heartbeat timeouts): see the handoff.
-/
set_option maxHeartbeats 4000000 in
/-- **The batch's loop and tail at `JAt`** (the decode's checks passed; module docstring): the
loop against `fbRun` from `σ`, moved to the spec's `Restart` by SpecFbRestart, the deferred
`invalidate_asid` against `flushAll`, the reply and `TS_RUNNING` by VsFbReply's `fbTail_inv`, `JAt`
after. OPEN. -/
theorem fb_loopJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hT : P0.ArchTotal arI)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (p asid : U64) (h0 : asid ≠ 0#u64) (length buf : U64) (blk call don : Bool)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hXO : ExtraOK Z.th (L.mem s) extra excaps) (hXN : ExtraNamed Z.th (L.mem s) extra)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok p.bv, σ)}, False))
    (b : Fl4Spec.Fl4FrameBatchInvocation)
    (hb : fbDecP p.bv asid.bv (args.map UScalar.bv) excaps = .ok b)
    (a0 : U64) (ha0 : args[0]? = some a0)
    (n words op depth mr cr attr : U64) (dd : Bool) (cnode dcnode : capability.Cap)
    (hop : op = a0 &&& vspace.frame_batch.OP) (hw : words.val = b.op.words)
    (hn : n = (⟨a0.bv >>> 8⟩ : U64) &&& 255#u64) (hdp : depth = (⟨a0.bv >>> 16⟩ : U64) &&& 127#u64)
    (hmr : mr = (⟨a0.bv >>> 24⟩ : U64) &&& 15#u64) (hcr : cr = (⟨a0.bv >>> 28⟩ : U64) &&& 15#u64)
    (hat : attr = (⟨a0.bv >>> 32⟩ : U64) &&& 31#u64)
    (hdd : ∃ d : U64, d = 1099511627776#u64 ∧ dd = (a0 &&& d != 0#u64))
    (hcn : ∃ x, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok cnode)
    (hdcn : dcnode = cnode ∨ ∃ x, vspace.extra extra 1#usize = ok (some x) ∧ capAt (L.mem s) x = ok dcnode) :
    (do
      let (s1, a1, done1, err, deferred) ←
        vspace.decode_frame_batch_loop st arI s ar buf ct n words p asid op depth mr cr attr dd cnode dcnode
          0#u64 false
      let a2 ← if deferred then arI.invalidate_asid a1 asid else ok a1
      let s2 ←
        if call
        then
          do
          let rbuf ← msg.lookup_ipc_buffer st s1 true ct
          let s3 ← obj.Tcb.set_reg st ct s1 layout.reg.BADGE 0#u64
          let (_, s4) ← msg.set_mr st s3 ct rbuf 0#u64 done1
          let (len, s5) ← msg.set_mr st s4 ct rbuf 1#u64 err
          let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 len
          msg.set_msg_info st s5 ct mi
        else ok s1
      let s3 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
      ok (core.result.Result.Ok (), s3, a2)) ⦃ res =>
      TopPostRMX (L := L) (JAt (L := L) arI AR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.frameBatch
            (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv) (.pml4Cap p.bv (some asid.bv)) excaps)))
        ct s res ⦄ := by
  fail "FB3 OPEN: the FrameBatch refinement (KENTRY-PLAN fb3j)"

/-- `isCnodeCap` of the abstraction of a native cap that is no CNode. -/
theorem fb_notCN {c : capability.Cap} (h : ∀ a b d e, c ≠ .CNode a b d e) : Fl4Spec.isCnodeCap (absCap c) = false := by
  cases c <;> first | rfl | exact absurd rfl (h _ _ _ _)

theorem fb_isCN {c : capability.Cap} (h : Fl4Spec.isCnodeCap (absCap c) = true) :
    ∃ a b d e, c = .CNode a b d e := by
  by_contra hn
  push_neg at hn
  rw [fb_notCN hn] at h
  exact absurd h (by decide)

set_option maxHeartbeats 8000000 in
/-- **The FrameBatch label on a PML4 cap at `JAt`** (module docstring): the decode's checks against
SpecFbDec's `fbDecP`, the loop and tail by `fb_loopJ`. -/
theorem decode_invocation_pml4_fbJV (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlb : lbl = fl4_abi.label.X86PML4FrameBatch)
    (hslb : Fl4Spec.dataToNat slbl = Fl4Spec.fl4FrameBatchLabel)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (p asid : U64) (mp : Bool) (h0 : mp = true → asid ≠ 0#u64) (length buf : U64) (blk call don fp : Bool)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Pml4 p mp asid))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hXO : ExtraOK Z.th (L.mem s) extra excaps) (hXN : ExtraNamed Z.th (L.mem s) extra)
    (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.Pml4 p mp asid) blk call don fp buf
      extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  have hR := hX.fin.2.1
  have hPl : Placed Z.th := J.xtop.rel.1
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hnf : lbl ≠ fl4_abi.label.X86PML4Flush := by
    intro h
    have h1 : fl4_abi.label.X86PML4FrameBatch.val = 90 := by simp [fl4_abi.label.X86PML4FrameBatch]
    have h2 : fl4_abi.label.X86PML4Flush.val = 46 := by simp [fl4_abi.label.X86PML4Flush]
    rw [← h, hlb] at h2; omega
  have hnF : ¬ Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel := by
    rw [hslb]; decide
  refine Or.inr ?_
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  rw [if_neg hnf, if_pos hlb]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci sl (.Pml4 p mp asid) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.frameBatch
          (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv)
            (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps)) := by
    show Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
      (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci sl
        (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps) = _
    unfold Fl4Spec.fl4ArchDecodeInvocation; dsimp only
    rw [if_neg hnF, if_pos hslb]
  rw [hspec]
  unfold vspace.decode_frame_batch
  rw [hct]; simp only [bind_ok]
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
    exact fb_err (L := L) (e := .Sys (.InvalidCapability 0#u64)) (e' := .invalidCapability 0) rfl (Or.inr ⟨0#u64, rfl, rfl⟩) hJ0
  simp only [↓reduceIte]
  have h0' := h0 rfl
  refine WP.spec_bind (check_vspace_fb s σ hR p asid h0') ?_
  rintro r (⟨rfl, hf⟩ | ⟨e, rfl, hdec⟩)
  swap
  · rw [fb_mapErr_err]
    simp only [bind_tc_ok, bind_ok, fb_branch_err, fb_fromResidual, WP.spec_ok]
    exact fb_err (L := L) (e := .Sys (.InvalidCapability 0#u64)) (e' := .invalidCapability 0) (hdec _ _)
      (Or.inr ⟨0#u64, rfl, rfl⟩) hJ0
  rw [fb_mapErr_ok]
  simp only [bind_tc_ok, bind_ok, fb_branch_ok]
  try simp only [WP.uncurry'_pair]
  try simp only [uncurry_apply_pair]
  try simp only [Aeneas.Std.uncurry]
  try dsimp only
  have hfd := decodeFrameBatch_run (args := args.map UScalar.bv) (ex := excaps) hf
  -- no header
  by_cases hl1 : length < 1#u64
  · simp only [hl1, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
    have h1 : (args.map UScalar.bv).length < 1 := by rw [List.length_map, ← hlen]; scalar_tac
    exact fb_err (L := L) (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) (by rw [hfd, fbDecP_short h1])
      (Or.inl trivial) hJ0
  simp only [hl1, ↓reduceIte]
  have h1 : ¬ (args.map UScalar.bv).length < 1 := by rw [List.length_map, ← hlen]; scalar_tac
  obtain ⟨a0, ha0⟩ : ∃ a0, args[0]? = some a0 := by
    cases h : args with
    | nil => rw [h] at h1; simp at h1
    | cons a r => exact ⟨a, rfl⟩
  have hhd : Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? = a0.bv := by
    rw [List.getElem?_map, ha0]; rfl
  rw [hargs 0#u64 a0 ha0]
  simp only [bind_ok, lift]
  rw [show vspace.frame_batch.COUNT_SHIFT = 8#u64 from (by unfold vspace.frame_batch.COUNT_SHIFT; rfl),
        show a0 >>> (8#u64 : U64) = ok ⟨a0.bv >>> 8⟩ from shr_u64_eq a0 8#u64 (by decide)]
  simp only [bind_ok, lift]
  rw [show vspace.frame_batch.DEPTH_SHIFT = 16#u64 from (by unfold vspace.frame_batch.DEPTH_SHIFT; rfl),
        show a0 >>> (16#u64 : U64) = ok ⟨a0.bv >>> 16⟩ from shr_u64_eq a0 16#u64 (by decide)]
  simp only [bind_ok, lift]
  refine WP.spec_bind (fb_words a0) ?_
  rintro words hw
  refine WP.spec_bind P0.Consts.vspace.frame_batch.DEFINED.spec ?_
  rintro i2 hi2
  try simp only [bind_ok, lift]
  have hdep : Fl4Spec.dataToNat ((a0.bv >>> 16) &&& 0x7f#64) =
      ((⟨a0.bv >>> 16⟩ : U64) &&& 127#u64).val := fb_and_val _ _
  have hnn : Fl4Spec.dataToNat ((a0.bv >>> 8) &&& 0xff#64) = ((⟨a0.bv >>> 8⟩ : U64) &&& 255#u64).val :=
    fb_and_val _ _
  have hIA : ∀ (hh : Fl4Spec.fbOpOf (Fl4Spec.dataToNat (a0.bv &&& 0x3#64)) = none ∨
      (a0.bv &&& ~~~Fl4Spec.fbDefined ≠ 0 ∨ Fl4Spec.dataToNat ((a0.bv >>> 16) &&& 0x7f#64) = 0 ∨
        Fl4Spec.dataToNat ((a0.bv >>> 16) &&& 0x7f#64) > 64)),
      TopPostRMX (L := L) (JAt (L := L) arI AR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.frameBatch
            (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv) (.pml4Cap p.bv (some asid.bv)) excaps)))
        ct s (.Err (.Sys (.InvalidArgument 0#u64)), s, ar) := fun hh =>
    fb_err (L := L) (e := .Sys (.InvalidArgument 0#u64)) (e' := .invalidArgument 0)
      (by rw [hfd, fbDecP_hdr h1 (by rw [hhd]; exact hh)]) (Or.inl rfl) hJ0
  -- reserved bits
  by_cases hd1 : ((a0 &&& ~~~i2) != 0#u64) = true
  · simp only [hd1, ↓reduceIte, error.invalid_arg, bind_ok, WP.spec_ok]
    exact hIA (Or.inr (Or.inl ((fb_defined' a0 i2 hi2).1 hd1)))
  simp only [hd1, Bool.false_eq_true, ↓reduceIte]
  have hd1' : ¬ a0.bv &&& ~~~Fl4Spec.fbDefined ≠ 0 := fun h => hd1 ((fb_defined' a0 i2 hi2).2 h)
  rcases hw with ⟨rfl, hnone⟩ | ⟨op', hop', hwv, hw0, hcpy⟩
  · simp only [eq_self_iff_true, ↓reduceIte, error.invalid_arg, bind_ok, WP.spec_ok]
    exact hIA (Or.inl hnone)
  simp only [hw0, ↓reduceIte]
  by_cases hd2 : (⟨a0.bv >>> 16⟩ : U64) &&& 127#u64 = 0#u64
  · simp only [hd2, ↓reduceIte, error.invalid_arg, bind_ok, WP.spec_ok]
    exact hIA (Or.inr (Or.inr (Or.inl (by rw [hdep, hd2]; rfl))))
  simp only [hd2, ↓reduceIte]
  by_cases hd3 : (⟨a0.bv >>> 16⟩ : U64) &&& 127#u64 > 64#u64
  · simp only [hd3, ↓reduceIte, error.invalid_arg, bind_ok, WP.spec_ok]
    exact hIA (Or.inr (Or.inr (Or.inr (by rw [hdep]; scalar_tac))))
  simp only [hd3, ↓reduceIte]
  have h2 : ¬ (Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? &&& ~~~Fl4Spec.fbDefined ≠ 0 ∨
      Fl4Spec.dataToNat ((Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? >>> 16) &&& 0x7f#64) = 0 ∨
      Fl4Spec.dataToNat ((Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? >>> 16) &&& 0x7f#64) > 64) := by
    rw [hhd, hdep]
    have : ((⟨a0.bv >>> 16⟩ : U64) &&& 127#u64).val ≠ 0 := fun h => hd2 (UScalar.eq_of_val_eq (by simpa using h))
    have : ¬ ((⟨a0.bv >>> 16⟩ : U64) &&& 127#u64).val > 64 := fun h => hd3 (by scalar_tac)
    tauto
  have hQ := fbDecP_some (p := p.bv) (asid := asid.bv) (ex := excaps) h1 (by rw [hhd]; exact hop') h2
  -- the entries' words
  have hwn : words.val * ((⟨a0.bv >>> 8⟩ : U64) &&& 255#u64).val ≤ 3 * 255 := by
    have : ((⟨a0.bv >>> 8⟩ : U64) &&& 255#u64).val ≤ 255 := by
      rw [UScalar.val_and]; exact Nat.le_trans Nat.and_le_right (by decide)
    have : words.val ≤ 3 := by rw [hwv]; cases op' <;> decide
    exact Nat.mul_le_mul (by assumption) (by assumption)
  step as ⟨i5, hi5⟩
  step as ⟨i6, hi6⟩
  by_cases hl2 : length < i6
  · simp only [hl2, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
    have h3 : (args.map UScalar.bv : List Fl4Spec.Data).length < 1 + op'.words *
        Fl4Spec.dataToNat ((Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? >>> 8) &&& 0xff#64) := by
      rw [List.length_map, hhd, hnn, ← hwv, ← hlen]; scalar_tac
    exact fb_err (L := L) (e := .Sys .TruncatedMessage) (e' := .truncatedMessage)
      (by rw [hfd, hQ]; unfold fbDecQ; rw [if_pos h3]) (Or.inl trivial) hJ0
  simp only [hl2, ↓reduceIte]
  have h3 : ¬ (args.map UScalar.bv : List Fl4Spec.Data).length < 1 + op'.words *
      Fl4Spec.dataToNat ((Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? >>> 8) &&& 0xff#64) := by
    rw [List.length_map, hhd, hnn, ← hwv, ← hlen]; scalar_tac
  -- extra cap 0: the lookup CNode
  obtain ⟨hXl, hXs, hXz⟩ := hXO
  rw [vsExtra_at extra 0#usize (by decide) _ (exAt_idx0 extra)]
  simp only [bind_ok]
  by_cases hx0 : exAt extra 0 = 0#u64
  · simp only [hx0, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
    have hl0 : excaps.length < 1 := by
      by_contra hn
      have := (srcOK_facts hPl (hXs 0 (by omega))).1
      exact this hx0
    exact fb_err (L := L) (e := .Sys .TruncatedMessage) (e' := .truncatedMessage)
      (by rw [hfd, hQ]; unfold fbDecQ; rw [if_neg h3, if_pos hl0]) (Or.inl trivial) hJ0
  simp only [hx0, ↓reduceIte]
  have hl0 : ¬ excaps.length < 1 := fun h => hx0 (hXz 0 (by omega) (by decide))
  obtain ⟨y0, rest, hy⟩ : ∃ y0 rest, excaps = y0 :: rest := by
    cases h : excaps with
    | nil => rw [h] at hl0; simp at hl0
    | cons a r => exact ⟨a, r, rfl⟩
  obtain ⟨-, -, -, cv, hcv, hy1, -, -, -⟩ := srcOK_facts hPl (hXs 0 (by omega))
  have hthe0 : (Fl4Spec.the excaps[0]?).1 = absCap cv := by subst hy; exact hy1
  rw [slot_cap_eq, hcv]
  simp only [bind_ok]
  cases cv
  case CNode cp cr cg cgs =>
    simp only [bind_ok, ↓reduceIte]
    have h5 : Fl4Spec.isCnodeCap (Fl4Spec.the excaps[0]?).1 = true := by rw [hthe0]; rfl
    have hcn : ∃ x, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok (.CNode cp cr cg cgs) :=
      ⟨exAt extra 0, by rw [vsExtra_at extra 0#usize (by decide) _ (exAt_idx0 extra), if_neg hx0], hcv⟩
    -- the tail of the decode, the loop: `fb_loopJ`
    have tail : ∀ (dcnode : capability.Cap)
        (h6 : Fl4Spec.isCnodeCap (if op' = .copyMap ∧ excaps.length > 1 then (Fl4Spec.the excaps[1]?).1
          else (Fl4Spec.the excaps[0]?).1) = true)
        (hdcn : dcnode = .CNode cp cr cg cgs ∨
          ∃ x, vspace.extra extra 1#usize = ok (some x) ∧ capAt (L.mem s) x = ok dcnode),
        (do
          let i7 ← a0 >>> vspace.frame_batch.MAP_RIGHTS_SHIFT
          let i9 ← a0 >>> vspace.frame_batch.CAP_RIGHTS_SHIFT
          let i11 ← a0 >>> vspace.frame_batch.ATTR_SHIFT
          let i13 ← vspace.frame_batch.DEFER_DELETE_FLUSH
          let (s1, a1, done1, err, deferred) ←
            vspace.decode_frame_batch_loop st arI s ar buf ct ((⟨a0.bv >>> 8⟩ : U64) &&& 255#u64) words p asid
              (a0 &&& vspace.frame_batch.OP) ((⟨a0.bv >>> 16⟩ : U64) &&& 127#u64) (i7 &&& 15#u64) (i9 &&& 15#u64)
              (i11 &&& 31#u64) (a0 &&& i13 != 0#u64) (.CNode cp cr cg cgs) dcnode 0#u64 false
          let a2 ← if deferred then arI.invalidate_asid a1 asid else ok a1
          let s2 ←
            if call
            then
              do
              let rbuf ← msg.lookup_ipc_buffer st s1 true ct
              let s3 ← obj.Tcb.set_reg st ct s1 layout.reg.BADGE 0#u64
              let (_, s4) ← msg.set_mr st s3 ct rbuf 0#u64 done1
              let (len, s5) ← msg.set_mr st s4 ct rbuf 1#u64 err
              let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 len
              msg.set_msg_info st s5 ct mi
            else ok s1
          let s3 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
          ok (core.result.Result.Ok (), s3, a2)) ⦃ res =>
          TopPostRMX (L := L) (JAt (L := L) arI AR) σ blk call don
            (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
              (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.frameBatch
                (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv) (.pml4Cap p.bv (some asid.bv)) excaps)))
            ct s res ⦄ := by
      intro dcnode h6 hdcn
      have hq : ∃ b, fbDecQ p.bv asid.bv (args.map UScalar.bv) excaps op' = .ok b ∧ b.op = op' := by
        unfold fbDecQ; rw [if_neg h3, if_neg hl0, if_pos h5, if_pos h6]; exact ⟨_, rfl, rfl⟩
      obtain ⟨b, hb', hbop⟩ := hq
      have hb : fbDecP p.bv asid.bv (args.map UScalar.bv) excaps = .ok b := hQ.trans hb'
      rw [show vspace.frame_batch.MAP_RIGHTS_SHIFT = 24#u64 from (by unfold vspace.frame_batch.MAP_RIGHTS_SHIFT; rfl),
        show a0 >>> (24#u64 : U64) = ok ⟨a0.bv >>> 24⟩ from shr_u64_eq a0 24#u64 (by decide)]
      simp only [bind_ok, lift]
      rw [show vspace.frame_batch.CAP_RIGHTS_SHIFT = 28#u64 from (by unfold vspace.frame_batch.CAP_RIGHTS_SHIFT; rfl),
        show a0 >>> (28#u64 : U64) = ok ⟨a0.bv >>> 28⟩ from shr_u64_eq a0 28#u64 (by decide)]
      simp only [bind_ok, lift]
      rw [show vspace.frame_batch.ATTR_SHIFT = 32#u64 from (by unfold vspace.frame_batch.ATTR_SHIFT; rfl),
        show a0 >>> (32#u64 : U64) = ok ⟨a0.bv >>> 32⟩ from shr_u64_eq a0 32#u64 (by decide)]
      simp only [bind_ok, lift]
      refine WP.spec_bind P0.Consts.vspace.frame_batch.DEFER_DELETE_FLUSH.spec ?_
      rintro i13 hi13
      exact fb_loopJ arI s ar σ J hni hA hT ct hct p asid h0' length buf blk call don args hlen hargs extra excaps
        ⟨hXl, hXs, hXz⟩ hXN hf b hb a0 ha0 _ words _ _ _ _ _ _ _ _ rfl (by rw [hbop]; exact hwv) rfl rfl rfl rfl
        ⟨i13, hi13, rfl⟩ hcn hdcn
    -- extra cap 1: the destination CNode of a copy
    rw [vsExtra_at extra 1#usize (by decide) _ (exAt_idx1 extra)]
    simp only [bind_ok]
    by_cases hx1 : exAt extra 1 = 0#u64
    · simp only [hx1, ↓reduceIte, bind_ok]
      have hl1 : ¬ excaps.length > 1 := fun h => (srcOK_facts hPl (hXs 1 h)).1 hx1
      refine tail _ (by rw [if_neg (show ¬ (op' = .copyMap ∧ excaps.length > 1) from fun h => hl1 h.2)]; exact h5)
        (Or.inl rfl)
    simp only [hx1, ↓reduceIte]
    have hl1 : excaps.length > 1 := by
      by_contra hn
      exact hx1 (hXz 1 (by omega) (by decide))
    by_cases hcm : op' = .copyMap
    swap
    · have hcm' : ¬ a0 &&& vspace.frame_batch.OP = vspace.frame_batch.COPY_MAP := fun h => hcm (hcpy.1 h)
      simp only [hcm', ↓reduceIte, bind_ok]
      exact tail _ (by rw [if_neg (show ¬ (op' = .copyMap ∧ excaps.length > 1) from fun h => hcm h.1)]; exact h5)
        (Or.inl rfl)
    have hcm' : a0 &&& vspace.frame_batch.OP = vspace.frame_batch.COPY_MAP := hcpy.2 hcm
    simp only [hcm', ↓reduceIte]
    obtain ⟨-, -, -, cv1, hcv1, hy11, -, -, -⟩ := srcOK_facts hPl (hXs 1 hl1)
    have hthe1 : (Fl4Spec.the excaps[1]?).1 = absCap cv1 := by
      rw [List.getElem?_eq_getElem hl1]; exact hy11
    rw [slot_cap_eq, hcv1]
    simp only [bind_ok]
    have hdx : ∃ x, vspace.extra extra 1#usize = ok (some x) ∧ capAt (L.mem s) x = ok cv1 :=
      ⟨exAt extra 1, by rw [vsExtra_at extra 1#usize (by decide) _ (exAt_idx1 extra), if_neg hx1], hcv1⟩
    cases cv1
    case CNode dp dr dg dgs =>
      simp only [bind_ok, ↓reduceIte]
      exact tail _ (by rw [if_pos (show op' = .copyMap ∧ excaps.length > 1 from ⟨hcm, hl1⟩), hthe1]; rfl)
        (Or.inr hdx)
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
      have h6 : ¬ Fl4Spec.isCnodeCap (if op' = .copyMap ∧ excaps.length > 1 then (Fl4Spec.the excaps[1]?).1
          else (Fl4Spec.the excaps[0]?).1) = true := by
        rw [if_pos (show op' = .copyMap ∧ excaps.length > 1 from ⟨hcm, hl1⟩), hthe1]
        intro h
        obtain ⟨_, _, _, _, he⟩ := fb_isCN h
        cases he
      have hE : ExceptT.run (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv)
          (.pml4Cap p.bv (some asid.bv)) excaps) σ = ({(.error (.invalidCapability 2), σ)}, False) := by
        rw [hfd, hQ]; unfold fbDecQ; rw [if_neg h3, if_neg hl0, if_pos h5, if_neg h6]
      exact fb_err (L := L) (e := .Sys (.InvalidCapability 2#u64)) hE (Or.inr ⟨2#u64, rfl, rfl⟩) hJ0
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
    have h5 : ¬ Fl4Spec.isCnodeCap (Fl4Spec.the excaps[0]?).1 = true := by
      rw [hthe0]
      intro h
      obtain ⟨_, _, _, _, he⟩ := fb_isCN h
      cases he
    have hE : ExceptT.run (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv)
        (.pml4Cap p.bv (some asid.bv)) excaps) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
      rw [hfd, hQ]; unfold fbDecQ; rw [if_neg h3, if_neg hl0, if_neg h5]
    exact fb_err (L := L) (e := .Sys (.InvalidCapability 1#u64)) hE (Or.inr ⟨1#u64, rfl, rfl⟩) hJ0


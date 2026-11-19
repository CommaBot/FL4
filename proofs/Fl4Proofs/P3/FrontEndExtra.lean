/-
P3 (issue #16, front end): **the invocation's extra caps and label at `J`**.

`handle_invocation` reads the message info (`msg_info`), the IPC buffer
(`lookup_ipc_buffer`) and the extra caps (`lookup_extra_caps`); the spec's
`handle_invocation` reads `getMessageInfo`, `lookupIpcBuffer` and
`lookupExtraCaps`. From `JAtZ` at entry (and the buffer facts of
`JEntryGlob`):

* `JAtZ.frontJ`: when both lookups succeed, FL4's extra-slot array and the
  spec's extra caps are related slot by slot (IpcGrant's `ExtraOK`, by
  `lookup_extra_top`), and the label words agree (`info.label.bv = mi.miLabel`).
* `ExtraOK.rel1`, `.rel2`, `.relS`, `.xc`: `ExtraOK` gives the decodes'
  extra-slot relations (`ExtraRel`, `ExtraRel2`, `ExtraSRel`, `XcRel`), so
  XTopJointEntry's paths no longer ask them.
-/
import Fl4Proofs.P3.XTopJointGrant
import Fl4Proofs.P3.TcbCtl
import Fl4Proofs.P3.IrqHandler
import Fl4Proofs.P3.CnodeRotate
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Conv
variable {th : TypedHeap} {m : U64 → U64} {e : Aeneas.Std.Array obj.Slot 3#usize}
  {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}

/-- A source slot of `ExtraOK`: a nonzero CNode slot holding a related cap. -/
theorem srcOK_facts (hP : Placed th) {x : U64} {y : Fl4Spec.Cap × Fl4Spec.CslotPtr} (h : SrcOK th m x y) :
    x ≠ 0#u64 ∧ IsSlot th x ∧ x = cslotAddr y.2 ∧ ∃ cv, capAt m x = ok cv ∧ y.1 = absCap cv ∧ CapRel cv y.1 ∧
      CapValid th cv ∧ ∃ ps, th ps = some (.cnode y.2.2.length) ∧ y.2.1 = ps.bv := by
  obtain ⟨ps, rs, idx, cv, hth, hl, hy2, hx, hc, hy1, hwf, -, hcv⟩ := h
  have hth' : th ps = some (.cnode y.2.2.length) := by
    rw [hy2]; show th ps = some (.cnode idx.length); rw [hl]; exact hth
  have hAs : AbsSlot th y.2 := ⟨ps, by rw [hy2], Or.inl hth'⟩
  have hxa : x = cslotAddr y.2 := by rw [hx, hy2]
  have hS : IsSlot th x := by rw [hxa]; exact hAs.isSlot
  exact ⟨hS.ne_zero hP, hS, hxa, cv, hc, hy1, ⟨hwf, hy1.symm⟩, hcv, ps, hth', by rw [hy2]⟩

theorem ExtraOK.rel1 (hP : Placed th) (h : ExtraOK th m e caps) :
    ExtraRel th m (exAt e 0) (caps.map Prod.fst) := by
  obtain ⟨-, hs, hz⟩ := h
  cases caps with
  | nil => exact Or.inl ⟨hz 0 (by simp) (by omega), rfl⟩
  | cons y rest =>
    obtain ⟨hne, hS, -, cv, hc, -, hcr, hcv, -⟩ := srcOK_facts hP (hs 0 (by simp))
    exact Or.inr ⟨hne, hS, cv, y.1, rest.map Prod.fst, hc, hcr, hcv, rfl⟩

theorem ExtraOK.rel2 (hP : Placed th) (h : ExtraOK th m e caps) :
    ExtraRel2 th m (exAt e 0) (exAt e 1) (caps.map Prod.fst) := by
  obtain ⟨-, hs, hz⟩ := h
  cases caps with
  | nil => exact Or.inl ⟨hz 0 (by simp) (by omega), rfl⟩
  | cons y rest =>
    obtain ⟨hne, hS, -, cv, hc, -, hcr, hcv, -⟩ := srcOK_facts hP (hs 0 (by simp))
    refine Or.inr ⟨hne, hS, cv, y.1, hc, hcr, hcv, ?_⟩
    cases rest with
    | nil => exact Or.inl ⟨hz 1 (by simp) (by omega), rfl⟩
    | cons y' rest' =>
      obtain ⟨hne', hS', -, cv', hc', -, hcr', hcv', -⟩ := srcOK_facts hP (hs 1 (by simp))
      exact Or.inr ⟨hne', hS', cv', y'.1, rest'.map Prod.fst, hc', hcr', hcv', rfl⟩

theorem ExtraOK.relS (hP : Placed th) (h : ExtraOK th m e caps) : ExtraSRel th m (exAt e 0) caps := by
  obtain ⟨-, hs, hz⟩ := h
  cases caps with
  | nil => exact Or.inl ⟨hz 0 (by simp) (by omega), rfl⟩
  | cons y rest =>
    have h0 := hs 0 (by simp)
    obtain ⟨hne, -, -, -⟩ := srcOK_facts hP h0
    obtain ⟨ps, rs, idx, cv, hth, hl, hy2, hx, hc, hy1, -⟩ := h0
    refine Or.inr ⟨hne, ps, rs, idx, rest, hth, hl, hx, ?_⟩
    obtain ⟨y1, y2⟩ := y
    simp only [List.getElem_cons_zero] at hy2 hy1
    rw [capV_of_capAt hc, ← hy1, ← hy2]

theorem ExtraOK.xc (hP : Placed th) (h : ExtraOK th m e caps) :
    XcRel th m (exAt e 0) (exAt e 1) (exAt e 2) caps := by
  obtain ⟨hl, hs, hz⟩ := h
  suffices H : ∀ i < 3, (exAt e i = 0#u64 ↔ caps.length ≤ i) ∧ ∀ y, caps[i]? = some y →
      exAt e i = cslotAddr y.2 ∧ y.1 = absCap (capV m (exAt e i)) ∧
        ∃ ps, th ps = some (.cnode y.2.2.length) ∧ y.2.1 = ps.bv by
    refine ⟨hl, fun i x hx => ?_⟩
    rcases i with _ | _ | _ | i
    all_goals simp at hx
    all_goals (subst hx; exact H _ (by omega))
  intro i hi
  by_cases hlt : i < caps.length
  · obtain ⟨hne, -, hxa, cv, hc, hy1, -, -, hps⟩ := srcOK_facts hP (hs i hlt)
    refine ⟨⟨fun h0 => absurd h0 hne, fun h => by omega⟩, fun y hy => ?_⟩
    rw [List.getElem?_eq_getElem hlt] at hy
    cases hy
    exact ⟨hxa, by rw [capV_of_capAt hc]; exact hy1, hps⟩
  · refine ⟨⟨fun _ => by omega, fun _ => hz i (by omega) hi⟩, fun y hy => ?_⟩
    rw [List.getElem?_eq_none (by omega)] at hy; cases hy

theorem exAt_idx0 (e : Aeneas.Std.Array obj.Slot 3#usize) : Aeneas.Std.Array.index_usize e 0#usize = ok (exAt e 0) := by
  rw [index_exAt e 0#usize (by simp)]; rfl

theorem exAt_idx1 (e : Aeneas.Std.Array obj.Slot 3#usize) : Aeneas.Std.Array.index_usize e 1#usize = ok (exAt e 1) := by
  rw [index_exAt e 1#usize (by simp)]; rfl

theorem exAt_idx2 (e : Aeneas.Std.Array obj.Slot 3#usize) : Aeneas.Std.Array.index_usize e 2#usize = ok (exAt e 2) := by
  rw [index_exAt e 2#usize (by simp)]; rfl

end Conv


/-! ## The argument words -/

section Args
open Fl4Spec

/-- The spec's argument word `i` (`fl4GetMr`, and `getMrs`' entry `i`):
message register `i`, then buffer word `i + 1` (0 with no buffer). -/
def specArg (regs : Register → Word) (sbo : Option ObjRef) (um : Word → Word8) (i : Nat) : Word :=
  if i < 4 then regs (mrIdx i) else match sbo with
    | none => 0
    | some sb => loadWordAt um (bufAddr sb (i + 1))

theorem msgReg_getElem (i : Nat) (hi : i < msg_registers.length) : msg_registers[i] = mrIdx i := by
  have : i < 4 := by simpa [msg_registers, msgRegisters] using hi
  unfold mrIdx
  interval_cases i <;> rfl

theorem fl4GetMr_eq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (sbo : Option ObjRef) (hal : ∀ sb, sbo = some sb → ∀ k, k < 128 → (bufAddr sb k).toNat % 8 = 0)
    (i : Nat) (hi : i < 127) :
    fl4GetMr (Z := Unit) t sbo i σ =
      ({(specArg x.tcbArch.tcbContext.userRegs sbo σ.machineState.underlyingMemory i, σ)}, False) := by
  unfold fl4GetMr
  rw [nd_bind_one (threadGet_eq _ hk)]
  try dsimp only
  by_cases h4 : i < msg_registers.length
  · rw [dif_pos h4, nd_pure_apply']
    have : i < 4 := by simpa [msg_registers, msgRegisters] using h4
    unfold specArg; rw [if_pos this, ← msgReg_getElem i h4]; rfl
  · rw [dif_neg h4]
    have : ¬ i < 4 := by simpa [msg_registers, msgRegisters] using h4
    unfold specArg; rw [if_neg this]
    cases sbo with
    | none => dsimp only; rw [nd_pure_apply']
    | some sb =>
      dsimp only
      exact loadWordOffs_eq σ sb (i + 1) (hal sb rfl (i + 1) (by omega))

theorem specMrs_length (regs : Register → Word) (sbo : Option ObjRef) (um : Word → Word8) (len : Nat) :
    (specMrs regs sbo um len).length = min len (match sbo with | none => 4 | some _ => 120) := by
  unfold specMrs
  cases sbo <;> simp [msg_registers, msgRegisters] <;> omega

theorem specMrs_get (regs : Register → Word) (sbo : Option ObjRef) (um : Word → Word8) (len i : Nat)
    (hl : len ≤ 120) (hi : i < (specMrs regs sbo um len).length) :
    (specMrs regs sbo um len)[i]! = specArg regs sbo um i := by
  have hil : i < len := lt_of_lt_of_le hi (specMrs_len_le _ _ _ _)
  unfold specArg
  by_cases h4 : i < 4
  · rw [if_pos h4]; exact (specMrs_lo regs sbo um len i h4 hil).2
  · rw [if_neg h4]
    cases sbo with
    | none => exact absurd (lt_of_lt_of_le hi (specMrs_len_none _ _ _)) h4
    | some sb => exact (specMrs_hi regs sb um len i (by omega) hil (by omega)).2

end Args

section ArgsJ
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem syscall_arg_rel {s : S} {B : Set (U64 × Fl4Spec.Word)} {um : Fl4Spec.Word → Fl4Spec.Word8}
    {regs : Fl4Spec.Register → Fl4Spec.Word} {ct buf : U64} {sbo : Option Fl4Spec.ObjRef}
    (hregs : ∀ r, (L.mem s (regA ct (regIdx r))).bv = regs r)
    (hbw : ∀ wp ∈ B, (L.mem s wp.1).bv = loadWordAt um wp.2)
    (hsb : buf = 0#u64 ↔ sbo = none) (hsm : ∀ sp, sbo = some sp → Endp.BufMap B buf sp)
    (i : U64) (hi : i.val < 127) :
    ∃ x, msg.syscall_arg st s ct buf i = ok x ∧ x.bv = specArg regs sbo um i.val := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by simp [msg.N_MSG_REGISTERS]
  unfold msg.syscall_arg
  by_cases h4 : i < msg.N_MSG_REGISTERS
  · have hi4' : i.val < msg.N_MSG_REGISTERS.val := by scalar_tac
    have hi4 : i.val < 4 := by omega
    rw [if_pos h4]
    obtain ⟨r, hr, hrv⟩ := spec_exists (msg_register_spec i hi4)
    rw [hr, bind_ok]
    obtain ⟨v, hv, hvv⟩ := spec_exists (Endp.obj.Tcb.reg.spec (L := L) s ct r)
    rw [hv]
    refine ⟨v, rfl, ?_⟩
    rw [hvv, hrv, hregs]
    unfold specArg; rw [if_pos hi4]
  · have hi4 : ¬ i.val < 4 := by
      intro h; apply h4; have : i.val < msg.N_MSG_REGISTERS.val := by omega
      scalar_tac
    rw [if_neg h4]
    by_cases h0 : buf = 0#u64
    · have hn := hsb.1 h0
      subst hn
      simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      refine ⟨0#u64, rfl, ?_⟩
      unfold specArg; rw [if_neg hi4]; rfl
    · obtain ⟨sb, hsbo⟩ : ∃ sb, sbo = some sb := by
        cases e : sbo with
        | none => exact absurd (hsb.2 e) h0
        | some sb => exact ⟨sb, rfl⟩
      subst hsbo
      have hb : (buf != 0#u64) = true := by simpa using h0
      rw [if_pos hb]
      simp only [lift, bind_ok]
      have hk : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      obtain ⟨v, hv, hvv⟩ := spec_exists (msg.buf_get.spec (L := L) s buf (core.num.U64.wrapping_add i 1#u64))
      rw [hv]
      refine ⟨v, rfl, ?_⟩
      have hwp := hsm sb rfl _ (by rw [hk]; omega : (core.num.U64.wrapping_add i 1#u64).val < 128)
      rw [hvv, hbw _ hwp]
      unfold specArg; rw [if_neg hi4]; dsimp only; rw [hk]

end ArgsJ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The front end at `J`**: the label words agree, and when both lookups
of the extra caps succeed, FL4's extra-slot array is the spec's extra caps
(`ExtraOK`). -/
theorem JAtZ.frontJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hOK : Endp.IpcBufCapOK σ) (hBC : Endp.BufCover Z.T Z.B σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {info : msginfo.MessageInfo} (hinfo : msg.msg_info st s ct = ok info)
    {mi : Fl4Spec.MessageInfo} (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    {buf : U64} (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    {buffer : Option Fl4Spec.ObjRef}
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    (hr2 : ipc.lookup_extra_caps st s ct buf info = ok r2)
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))}
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False)) :
    info.label.bv = mi.miLabel ∧
    ∀ e exs, r2 = .Ok e → er = .ok exs → ExtraOK Z.th (L.mem s) e exs := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hctT hks
  have hwmi : (L.mem s (regA ct layout.reg.MSG_INFO)).bv =
      xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  -- the spec's reads
  have hmi' : mi = Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register) := by
    have h := (congrArg Prod.fst (hmi.symm.trans (getMessageInfo_eq hks)))
    exact congrArg Prod.fst (Set.singleton_eq_singleton_iff.1 h)
  have hbuffer' : buffer = Endp.ipcBufOf false xs := by
    have h := (congrArg Prod.fst (hbuffer.symm.trans (lookupIpcBuffer_eq hks false)))
    exact congrArg Prod.fst (Set.singleton_eq_singleton_iff.1 h)
  subst hmi' hbuffer'
  -- FL4's reads
  have hm := Endp.msg_info_spec (L := L) s ct
  rw [hinfo, WP.spec_ok] at hm
  obtain ⟨hlab, -, hext, -⟩ := hm
  refine ⟨?_, ?_⟩
  · show info.label.bv = (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register >>> 12) &&&
      Fl4Spec.mask Fl4Spec.msgLabelBits
    rw [label_mask, hlab, hwmi]
  intro e exs h1 h2
  subst h1 h2
  have hb := lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 htcb hks hOK false
  rw [hbuf, WP.spec_ok] at hb
  obtain ⟨hsb, hsbp⟩ := hb
  obtain ⟨xs', hks', hws⟩ := J.buf ct hctT
  rw [hks] at hks'; cases hks'
  have hsm : ∀ sp, Endp.ipcBufOf false xs = some sp → Endp.BufMap Z.B buf sp :=
    fun sp h => hBC ct hctT xs false sp hks h buf (hsbp hws sp h)
  have hlk := Ipc.lookup_extra_top J.ip J.xtop.rel hI.1 htcb buf (Endp.ipcBufOf false xs)
    ⟨hsb.1, hsb.2⟩ hsm info (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register))
    (by show info.extra_caps.bv.toNat = _; rw [hext, hwmi])
    (by show info.extra_caps.bv.toNat ≤ 3; rw [hext, hwmi]; exact Endp.extra_le3 _)
  rw [hr2, WP.spec_ok] at hlk
  obtain ⟨caps, hc, hok⟩ := hlk
  have hc' := (Vs.catch_ok (h := fun _ => pure []) her).symm.trans hc
  have e2 : exs = caps := congrArg Prod.fst (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hc'))
  subst e2
  exact hok

set_option maxHeartbeats 4000000 in
/-- **The extra caps' lookups at `J`**: FL4's and the spec's both succeed, or
both fault with the same cap fault (`CapFaultCorr`, IpcGrant's
`lookup_extra_rel`). -/
theorem JAtZ.extraJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hOK : Endp.IpcBufCapOK σ) (hBC : Endp.BufCover Z.T Z.B σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {info : msginfo.MessageInfo} (hinfo : msg.msg_info st s ct = ok info)
    {mi : Fl4Spec.MessageInfo} (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    {buf : U64} (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    {buffer : Option Fl4Spec.ObjRef}
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    {r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault}
    (hr2 : ipc.lookup_extra_caps st s ct buf info = ok r2)
    {er : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))}
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(er, σ)}, False)) :
    (∃ e exs, r2 = .Ok e ∧ er = .ok exs) ∨ (∃ f f', r2 = .Err f ∧ er = .error f' ∧ Endp.CapFaultCorr f f') := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  have hxs := hI.1.toE.at_tcb hctT hks
  have hwmi : (L.mem s (regA ct layout.reg.MSG_INFO)).bv =
      xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  have hmi' : mi = Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register) := by
    have h := (congrArg Prod.fst (hmi.symm.trans (getMessageInfo_eq hks)))
    exact congrArg Prod.fst (Set.singleton_eq_singleton_iff.1 h)
  have hbuffer' : buffer = Endp.ipcBufOf false xs := by
    have h := (congrArg Prod.fst (hbuffer.symm.trans (lookupIpcBuffer_eq hks false)))
    exact congrArg Prod.fst (Set.singleton_eq_singleton_iff.1 h)
  subst hmi' hbuffer'
  have hm := Endp.msg_info_spec (L := L) s ct
  rw [hinfo, WP.spec_ok] at hm
  obtain ⟨-, -, hext, -⟩ := hm
  have hb := lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 htcb hks hOK false
  rw [hbuf, WP.spec_ok] at hb
  obtain ⟨hsb, hsbp⟩ := hb
  obtain ⟨xs', hks', hws⟩ := J.buf ct hctT
  rw [hks] at hks'; cases hks'
  have hsm : ∀ sp, Endp.ipcBufOf false xs = some sp → Endp.BufMap Z.B buf sp :=
    fun sp h => hBC ct hctT xs false sp hks h buf (hsbp hws sp h)
  have hlk := Ipc.lookup_extra_rel J.ip J.xtop.rel hI.1 htcb buf (Endp.ipcBufOf false xs)
    ⟨hsb.1, hsb.2⟩ hsm info (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register))
    (by show info.extra_caps.bv.toNat = _; rw [hext, hwmi])
    (by show info.extra_caps.bv.toNat ≤ 3; rw [hext, hwmi]; exact Endp.extra_le3 _)
  rw [hr2, WP.spec_ok] at hlk
  have huniq : ∀ {x y : Except Fl4Spec.Fault (List (Fl4Spec.Cap × Fl4Spec.CslotPtr))},
      ({(x, σ)} : Set _) = {(y, σ)} → x = y := fun h =>
    congrArg Prod.fst (Set.singleton_eq_singleton_iff.1 h)
  cases r2 with
  | Ok e =>
    obtain ⟨caps, hc, -⟩ := hlk
    exact Or.inl ⟨e, caps, rfl, huniq (congrArg Prod.fst (her.symm.trans hc))⟩
  | Err f =>
    obtain ⟨f', hc, hf⟩ := hlk
    exact Or.inr ⟨f, f', rfl, huniq (congrArg Prod.fst (her.symm.trans hc)), hf⟩


set_option maxHeartbeats 4000000 in
/-- **The argument words at `J`**: the spec's `getMrs` words are FL4's
`syscall_arg`s, as many as `msgLen`, and the first five arguments are
`fl4GetMr`'s (`ArgRel`, also past the message length). -/
theorem JAtZ.argsJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hOK : Endp.IpcBufCapOK σ) (hBC : Endp.BufCover Z.T Z.B σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {info : msginfo.MessageInfo} (hinfo : msg.msg_info st s ct = ok info)
    {mi : Fl4Spec.MessageInfo} (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    {buf : U64} (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    {buffer : Option Fl4Spec.ObjRef}
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    {argsU : List U64}
    (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(argsU.map UScalar.bv, σ)}, False)) :
    (msgLen info buf).val = argsU.length ∧
    (∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x) ∧
    ArgRel (st := st) s σ ct buf buffer 5 := by
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨htcb, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  have hR := hI.1.toE
  have hxs := hR.at_tcb hctT hks
  have hwmi : (L.mem s (regA ct layout.reg.MSG_INFO)).bv =
      xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register := by
    rw [← regIdx_msgInfo]; exact hxs.regs _
  have hmi' : mi = Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register) := by
    have h := (congrArg Prod.fst (hmi.symm.trans (getMessageInfo_eq hks)))
    exact congrArg Prod.fst (Set.singleton_eq_singleton_iff.1 h)
  have hbuffer' : buffer = Endp.ipcBufOf false xs := by
    have h := (congrArg Prod.fst (hbuffer.symm.trans (lookupIpcBuffer_eq hks false)))
    exact congrArg Prod.fst (Set.singleton_eq_singleton_iff.1 h)
  have hm := Endp.msg_info_spec (L := L) s ct
  rw [hinfo, WP.spec_ok] at hm
  obtain ⟨-, hlen, -, hle⟩ := hm
  have hb := lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 htcb hks hOK false
  rw [hbuf, WP.spec_ok] at hb
  obtain ⟨hsb, hsbp⟩ := hb
  obtain ⟨xs', hks', hws⟩ := J.buf ct hctT
  rw [hks] at hks'; cases hks'
  have hsm : ∀ sp, Endp.ipcBufOf false xs = some sp → Endp.BufMap Z.B buf sp :=
    fun sp h => hBC ct hctT xs false sp hks h buf (hsbp hws sp h)
  have hal : ∀ sb, Endp.ipcBufOf false xs = some sb → ∀ k, k < 128 → (bufAddr sb k).toNat % 8 = 0 := by
    intro sb hsb' k hk
    have hmb := hBC ct hctT xs false sb hks hsb' ⟨sb⟩ rfl
    have hv : (⟨BitVec.ofNat 64 k⟩ : U64).val = k := by
      show (BitVec.ofNat 64 k).toNat = k; simp; omega
    have h := (J.ip.e.balign _ (hmb ⟨BitVec.ofNat 64 k⟩ (by rw [hv]; omega))).2
    rw [hv] at h; exact h
  subst hmi' hbuffer'
  set regs := xs.tcbArch.tcbContext.userRegs
  set um := σ.machineState.underlyingMemory
  set len := Fl4Spec.unat (Fl4Spec.dataToMessageInfo (regs Fl4Spec.msg_info_register)).miLength with hlen'
  have hlv : info.length.val = len := by
    show info.length.bv.toNat = _; rw [hlen, hwmi]
  have hV : argsU.map UScalar.bv = specMrs regs (Endp.ipcBufOf false xs) um len := by
    have h := (congrArg Prod.fst (hmrs.symm.trans (getMrs_eq hks _ hal _)))
    exact congrArg Prod.fst (Set.singleton_eq_singleton_iff.1 h)
  have hL : argsU.length = (specMrs regs (Endp.ipcBufOf false xs) um len).length := by
    rw [← hV, List.length_map]
  have hreg : ∀ r, (L.mem s (regA ct (regIdx r))).bv = regs r := fun r => hxs.regs r
  have hrel := syscall_arg_rel (L := L) (s := s) (B := Z.B) (um := um) hreg (fun wp h => hR.buf wp h)
    (ct := ct) ⟨hsb.1, hsb.2⟩ hsm
  refine ⟨?_, fun i x hx => ?_, fun i hi => ?_⟩
  · rw [hL, specMrs_length]
    have hN : msg.N_MSG_REGISTERS.val = 4 := by simp [msg.N_MSG_REGISTERS]
    unfold msgLen
    by_cases hgt : info.length > msg.N_MSG_REGISTERS
    · have hgt0 : msg.N_MSG_REGISTERS.val < info.length.val := by scalar_tac
      have hgt' : 4 < info.length.val := by omega
      rw [if_pos hgt]
      by_cases h0 : buf = 0#u64
      · rw [if_pos h0, hN, (hsb.1 h0)]; (try simp only); omega
      · rw [if_neg h0]
        cases e : Endp.ipcBufOf false xs with
        | none => exact absurd (hsb.2 e) h0
        | some _ => (try simp only); omega
    · have hle' : info.length.val ≤ 4 := by
        have : ¬ msg.N_MSG_REGISTERS.val < info.length.val := fun h => hgt (by scalar_tac)
        omega
      rw [if_neg hgt]
      cases Endp.ipcBufOf false xs <;> (try simp only) <;> omega
  · have hlt : i.val < argsU.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hx; cases hx
    have hx' : argsU[i.val] = x := by rw [List.getElem?_eq_getElem hlt] at hx; cases hx; rfl
    have h120 : argsU.length ≤ 120 := by
      rw [hL]; exact le_trans (specMrs_len_le _ _ _ _) (by omega)
    obtain ⟨y, hy, hyv⟩ := hrel i (by omega)
    have hg := specMrs_get regs (Endp.ipcBufOf false xs) um len i.val (by omega) (by rw [← hL]; exact hlt)
    have hm : (argsU.map UScalar.bv)[i.val]! = x.bv := by
      rw [getElem!_pos _ i.val (by simpa using hlt)]; simp [hx']
    rw [hV] at hm
    rw [hy]; congr 1
    apply P1.eq_of_bv
    rw [hyv, ← hg, hm]
  · obtain ⟨y, hy, hyv⟩ := hrel i (by omega)
    refine ⟨y, hy, ?_⟩
    rw [fl4GetMr_eq hks _ hal i.val (by omega), hyv]

end

end

end Fl4Proofs.P3

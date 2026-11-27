/-
P3 (line mmuAD, gen 39): **the EnableIOPort scope `EioScope` from the syscall front end** (P3/JAtZV3VDisp5) — what
`vcpuDecodeJ5` / `vcpuInvJ5` ask beyond gen 38's scope comes from FL4's `handle_invocation`
(syscall.rs l. 170-197): the invoked cap is `slot.cap(s)` (`Cap::Vcpu { ptr }`, l. 153), `extra` is
`ipc::lookup_extra_caps` (ipc.rs l. 28-44, each entry `cspace::lookup_slot`'s slot).

* `JAtZB.curEq`, **`JAtZB.frontJ`**: P3/ScJoint's `JAtZ.curEq` and P3/FrontEndExtra's `JAtZ.frontJ` over `JAtZB`
  (statements and proofs verbatim, `J : JAtZ` read as `J : JAtZB`; neither reads `JAtZ.ext`); **`JAtZV3.frontJ`**:
  at `JAtZV3` (through `J.z2.zv.base`). When FL4's and the spec's extra-cap lookups both succeed, FL4's array and
  the spec's extra caps are related slot by slot (`ExtraOK`, IpcGrant), each source a CNode slot of `Z.th`.
* `capV_vcpu_canonical`: a slot whose cap is `Vcpu p` has `p` canonical (`decodeF` unpacks the pointer,
  `unpackF_canonical`).
* **`ExtraOK.eioSlot`**: under `ExtraOK`, a non-null `ex[0]` is `cslotAddr (pc, idx)` of a CNode `pc` of `th`;
  **`ExtraOK.eioScope`**: with the invoked slot's cap `Vcpu p`, `EioScope th ex p` holds;
  **`ExtraOK.vcaps`**: `ExtraOK` gives `VCaps` at `ex[0]`'s cap (the dispatcher's extra-cap agreement).

So the slot scope and canonicity are supplied by the front end's lookup relation. Still missing between this and
a syscall-level step at `JAtZV3` (not proved here): the `JAtZV3` invocation step itself (handle_invocation's
lookup of the invoked cap and its `ExtraOK` at a `JAtZV3` state needs `Endp.IpcBufCapOK σ` / `Endp.BufCover`, which
`JAtZB.frontJ` takes as hypotheses as `JAtZ.frontJ` does; the native entry derives them from `JEntryGlob`).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VDisp5
import Fl4Proofs.P3.FrontEndExtra
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem JAtZB.curEq {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) :
    σ.curThread = ct.bv ∧ ∃ x, σ.kheap ct.bv = some (.tcb x) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = Sched.nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  obtain ⟨-, x, hk⟩ := J.xtop.curTcb hcur
  exact ⟨hcur, x, hk⟩

set_option maxHeartbeats 4000000 in
theorem JAtZB.frontJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s ar σ)
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

/-- **`JAtZ.frontJ` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.frontJ {V X : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s ar σ)
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
    ∀ e exs, r2 = .Ok e → er = .ok exs → ExtraOK Z.th (L.mem s) e exs :=
  J.z2.zv.base.frontJ hOK hBC hct hinfo hmi hbuf hbuffer hr2 her

end

/-- A slot holding a VCPU cap names a canonical pointer (module docstring). -/
theorem capV_vcpu_canonical {m : U64 → U64} {y p : U64} (h : capV m y = .Vcpu p) : Canonical p := by
  unfold capV decodeF at h
  dsimp only at h
  split at h <;> first | (cases h; done) | skip
  all_goals (injection h with e; subst e; exact unpackF_canonical _)

section
variable {th : TypedHeap} {m : U64 → U64} {e : Aeneas.Std.Array obj.Slot 3#usize}
  {caps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}

theorem zv_ex0 {sl : obj.Slot} (hsl : Array.index_usize e 0#usize = ok sl) : sl = exAt e 0 := by
  rw [index_exAt e 0#usize (by decide)] at hsl
  exact (ok_inj hsl).symm

theorem zv_isnull {sl : obj.Slot} {b : Bool} (h : obj.Slot.is_null sl = ok b) : b = decide (sl = 0#u64) := by
  unfold obj.Slot.is_null at h
  exact (ok_inj h).symm

/-- **A non-null `ex[0]` is a CNode slot under `ExtraOK`** (module docstring). -/
theorem ExtraOK.eioSlot (hP : Placed th) (h : ExtraOK th m e caps) :
    ∀ sl, Array.index_usize e 0#usize = ok sl → obj.Slot.is_null sl = ok false →
      ∃ pc r idx, th pc = some (.cnode r) ∧ idx.length = r ∧ sl = cslotAddr (pc.bv, idx) := by
  intro sl hsl hbn
  have e0 := zv_ex0 hsl
  have hb := zv_isnull hbn
  rcases ExtraOK.relS hP h with ⟨hz, -⟩ | ⟨-, ps, rs, idxs, rest, hth, hl, hx, -⟩
  · rw [← e0] at hz
    rw [hz] at hb
    simp at hb
  · exact ⟨ps, rs, idxs, hth, hl, by rw [e0]; exact hx⟩

/-- **`EioScope` from the front end** (module docstring). -/
theorem ExtraOK.eioScope (hP : Placed th) (h : ExtraOK th m e caps) {y p : U64} (hv : capV m y = .Vcpu p) :
    EioScope th e p :=
  ⟨capV_vcpu_canonical hv, ExtraOK.eioSlot hP h⟩

/-- **`VCaps` at `ex[0]` from the front end** (module docstring). -/
theorem ExtraOK.vcaps (hP : Placed th) (h : ExtraOK th m e caps) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize e 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) : VCaps b (capV m sl) caps := by
  have e0 := zv_ex0 hsl
  have hb := zv_isnull hbn
  rcases ExtraOK.relS hP h with ⟨hz, hc⟩ | ⟨hnz, ps, rs, idxs, rest, -, -, -, hc⟩
  · rw [← e0] at hz
    refine ⟨fun _ => hc, fun hf => ?_⟩
    rw [hz] at hb
    rw [hf] at hb
    simp at hb
  · rw [← e0] at hnz hc
    refine ⟨fun ht => ?_, fun _ => ⟨(ps.bv, idxs), rest, hc⟩⟩
    rw [ht] at hb
    exact absurd (of_decide_eq_true hb.symm) hnz

end

end

end Fl4Proofs.P3

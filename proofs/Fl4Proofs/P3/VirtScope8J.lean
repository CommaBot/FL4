/-
P3x for virtualization (line virt, gen 8, item 1, joint half): **the joint front-end walk, exported, and the
narrowed route scope derived from U36I's own per-entry premise.**

U33's proof walks FL4's front end (message info, `lookup_slot`, IPC buffer, extra caps, message words) beside the
spec's and applies the per-slot path premise at the invoked slot; that walk sits inside
`handle_invocation_refinesMXPL` / `handle_invocation_entryJMUL` (P3JLook) and was not reusable. This module
restates it as lemmas about the **spec's decode points** (VirtR7e's `DecPt`):

* `run_lookupPart_ok`, `run_lookupPart_err1`, `run_lookupPart_err2` (the spec's `lookupPart` from single-outcome
  reads), **`decPt_joint`** (the walk: at a `JAtZ` state every spec decode point of `toBl cptr` is FL4's front end —
  `frontEx`, `lookup_slot_refines`, `StateRel.slot_cap`, `frontJ`, `extraJ`, `argsJ`: one message info, the
  looked-up slot with FL4's cap `c` there and `absCap c` the spec's, FL4's extra-slot array with `ExtraOK`, the
  argument words with `syscall_arg`, all at the decode state `σ` itself).
* **`offRoute6_of_path`**: `JPathAtMU30 … fp cptr` (U36I's per-entry path premise) at an `NR` state ⇒
  `OffRoute6 fp (toBl cptr.bv) σ`: at each on-route point the leaf (`JPathME` @88 / `JPathME6` @60 / the untyped
  `vtx` field) is `XCapP` against the ported decoder, and VirtAgreeDec's `agree_*` turn it into `ErrAgree`.
* **`offRouteS8_of_disp`**: `KDispHypsKVU32 … n c` at an `NR` dispatch state ⇒ `VirtScope8.OffRouteS8 c σ`
  (`inv` for Send / NBSend / Call at the cap register, `mid` for ReplyRecv / NBSendRecv / NBSendWait).

Named premises: `hvk : virtKind = .none` [S] (as gen 5–7); **`hvirt : ∀ a, arI.virtualization a = ok 0` [P]**
(gen 2's `hvirt`, used by `agree_untypedGate`; the FL4 backend reports no VT-x exactly when the spec's
`virtKind = none`). No [J]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtScope8
import Fl4Proofs.P3.VirtAgreeDec
import Fl4Proofs.P3.VirtExtTopU36
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The spec's `lookupPart` from single-outcome reads -/

theorem run_lookupPart_ok {th : Fl4Spec.ObjRef} {cptr : Fl4Spec.CapRef} {info : Fl4Spec.MessageInfo}
    {σ : Fl4Spec.State Unit} {cap : Fl4Spec.Cap} {slot : Fl4Spec.CslotPtr} {buffer : Option Fl4Spec.ObjRef}
    {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) th cptr).run σ = ({(.ok (cap, slot), σ)}, False))
    (hb : Fl4Spec.lookupIpcBuffer (Z := Unit) false th σ = ({(buffer, σ)}, False))
    (he : (Fl4Spec.lookupExtraCaps (Z := Unit) th buffer info).run σ = ({(.ok exs, σ)}, False)) :
    (VirtR7e.lookupPart th cptr info).run σ = ({(.ok (slot, cap, exs, buffer), σ)}, False) := by
  unfold VirtR7e.lookupPart Fl4Spec.capFaultOnFailure
  rw [run_bind_ok (run_handleE_ok hl)]
  simp only
  rw [run_bind_ok (run_liftE hb), run_bind_ok he]
  rfl

theorem run_lookupPart_err1 {th : Fl4Spec.ObjRef} {cptr : Fl4Spec.CapRef} {info : Fl4Spec.MessageInfo}
    {σ : Fl4Spec.State Unit} {lf : Fl4Spec.LookupFailure}
    (hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) th cptr).run σ = ({(.error lf, σ)}, False)) :
    (VirtR7e.lookupPart th cptr info).run σ =
      ({(.error (.capFault (Fl4Spec.ofBl cptr) false lf), σ)}, False) := by
  unfold VirtR7e.lookupPart
  have h2 : (Fl4Spec.capFaultOnFailure (Z := Unit) (Fl4Spec.ofBl cptr) false
      (Fl4Spec.lookupCapAndSlot (Z := Unit) th cptr)).run σ =
      ({(.error (.capFault (Fl4Spec.ofBl cptr) false lf), σ)}, False) := by
    unfold Fl4Spec.capFaultOnFailure
    rw [run_handleE_err hl]
    rfl
  exact run_bind_error h2 _

theorem run_lookupPart_err2 {th : Fl4Spec.ObjRef} {cptr : Fl4Spec.CapRef} {info : Fl4Spec.MessageInfo}
    {σ : Fl4Spec.State Unit} {cap : Fl4Spec.Cap} {slot : Fl4Spec.CslotPtr} {buffer : Option Fl4Spec.ObjRef}
    {f : Fl4Spec.Fault}
    (hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) th cptr).run σ = ({(.ok (cap, slot), σ)}, False))
    (hb : Fl4Spec.lookupIpcBuffer (Z := Unit) false th σ = ({(buffer, σ)}, False))
    (he : (Fl4Spec.lookupExtraCaps (Z := Unit) th buffer info).run σ = ({(.error f, σ)}, False)) :
    (VirtR7e.lookupPart th cptr info).run σ = ({(.error f, σ)}, False) := by
  unfold VirtR7e.lookupPart Fl4Spec.capFaultOnFailure
  rw [run_bind_ok (run_handleE_ok hl)]
  simp only
  rw [run_bind_ok (run_liftE hb), run_bind_error he]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The joint front-end walk at a spec decode point** (module docstring): every decode point of `toBl cptr` at a
`JAtZ` state is FL4's front end at the same state. -/
theorem decPt_joint {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (cptr : U64) {info : Fl4Spec.MessageInfo}
    {a0 : Fl4Spec.CslotPtr × Fl4Spec.Cap × List (Fl4Spec.Cap × Fl4Spec.CslotPtr) × Option Fl4Spec.ObjRef}
    {args : List Fl4Spec.Data} {u : Fl4Spec.State Unit}
    (hd : VirtR7e.DecPt (Fl4Spec.toBl cptr.bv) σ info a0 args u) :
    u = σ ∧ ∃ (info' : msginfo.MessageInfo) (buf : U64) (r2 : core.result.Result (Aeneas.Std.Array obj.Slot 3#usize) error.Fault)
      (e : Aeneas.Std.Array obj.Slot 3#usize) (argsU : List U64) (c : capability.Cap),
      msg.msg_info st s ct = ok info' ∧
      Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(info, σ)}, False) ∧
      msg.lookup_ipc_buffer st s false ct = ok buf ∧
      Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(a0.2.2.2, σ)}, False) ∧
      ipc.lookup_extra_caps st s ct buf info' = ok r2 ∧
      (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv a0.2.2.2 info).run σ = ({(.ok a0.2.2.1, σ)}, False) ∧
      Fl4Spec.getMrs (Z := Unit) ct.bv a0.2.2.2 info σ = ({(argsU.map UScalar.bv, σ)}, False) ∧
      args = argsU.map UScalar.bv ∧ r2 = .Ok e ∧
      (∃ p, a0.1.1 = p.bv ∧ Z.th p = some (.cnode a0.1.2.length)) ∧
      capAt (L.mem s) (cslotAddr a0.1) = ok c ∧
      Fl4Spec.getCap (Z := Unit) a0.1 σ = ({(absCap c, σ)}, False) ∧ a0.2.1 = absCap c ∧
      info'.label.bv = info.miLabel ∧ ExtraOK Z.th (L.mem s) e a0.2.2.1 ∧
      (msgLen info' buf).val = argsU.length ∧
      (∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x) := by
  obtain ⟨s1, t2, h1, ha, hu⟩ := hd
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨info', mi, buf, buffer, r2, er, argsU, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs⟩ :=
    JAtZ.frontEx arI J J.xferH.1 J.xferH.2.1 hct
  rw [hcur, hmi] at h1
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
  subst e1; subst s1
  rw [hcur] at ha hu
  have hX := J.xtop
  have htcb := (J.xtop.curTcb hcur).1
  obtain ⟨r, -, el, hel, -, hok⟩ := spec_exists
    (lookup_slot_refines (Z := Unit) Z.th s σ hX.rel.2.1.1 hX.rel.2.1.2.1 ct htcb cptr)
  cases el with
  | error lf =>
    have hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ =
        ({(.error lf, σ)}, False) := by
      unfold Fl4Spec.lookupCapAndSlot; exact run_bind_error (s := σ) hel _
    rw [run_lookupPart_err1 hl] at ha
    cases (Prod.mk.inj (Set.mem_singleton_iff.1 ha)).1
  | ok v =>
    obtain ⟨sl, rest⟩ := v
    obtain ⟨p, hp, hth, -⟩ := hok
    obtain ⟨c, ca, hc, hca, hget⟩ := hX.rel.2.1.1.slot_cap hp hth
    have hl : (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ =
        ({(.ok (ca, sl), σ)}, False) := by
      unfold Fl4Spec.lookupCapAndSlot
      rw [run_bind_ok hel]
      simp only
      rw [run_bind_ok (run_liftE hget)]
      rfl
    cases er with
    | error f =>
      rw [run_lookupPart_err2 hl hbuffer her] at ha
      cases (Prod.mk.inj (Set.mem_singleton_iff.1 ha)).1
    | ok exs =>
      rw [run_lookupPart_ok hl hbuffer her] at ha
      obtain ⟨ea, et⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 ha)
      cases ea
      subst t2
      rw [hmrs] at hu
      obtain ⟨eu1, eu2⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hu)
      subst eu1; subst eu2
      obtain ⟨e, he⟩ : ∃ e, r2 = .Ok e := by
        rcases J.extraJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her with ⟨e, exs', h1, -⟩ |
          ⟨f, f', -, h2, -⟩
        · exact ⟨e, h1⟩
        · cases h2
      obtain ⟨hLb, hXO⟩ := J.frontJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hr2 her
      obtain ⟨hLen, hArgs, -⟩ := J.argsJ J.xferH.1 J.xferH.2.1 hct hinfo hmi hbuf hbuffer hmrs
      have hca' : ca = absCap c := hca.abs
      subst hca'
      exact ⟨rfl, info', buf, r2, e, argsU, c, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs, rfl, he,
        ⟨p, hp, hth⟩, hc, hget, rfl, hLb, hXO e exs he rfl, hLen, hArgs⟩

set_option maxHeartbeats 8000000 in
/-- **U36I's per-entry path premise gives the route scope at its decode points** (module docstring). -/
theorem offRoute6_of_path (hvk : Fl4Spec.virtKind = .none) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hvirt : arI.virtualization a = ok 0#u64)
    (hnr : VirtR7e.NR σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {call bl don fp : Bool} {cptr : U64}
    (hP : JPathAtMU30 (L := L) arI AR Z H Cs D s a σ ct call bl don fp cptr) :
    VirtAgree.OffRoute6 fp (Fl4Spec.toBl cptr.bv) σ := by
  intro info a0 args u hd
  rcases a0 with ⟨sl, cap, exs, buffer⟩
  have hd' := hd
  obtain ⟨s1, t2, h1, ha, -⟩ := hd'
  obtain ⟨hu, info', buf, r2, e, argsU, c, hinfo, hmi, hbuf, hbuffer, hr2, her, hmrs, hargsE, he, hsl, hc, hget,
    hcap, hLb, hXO, hLen, hArgs⟩ := decPt_joint arI J hct cptr hd
  subst u
  dsimp only at hbuffer her hmrs hsl hc hget hcap hXO
  have hcur := (J.curEq hct).1
  rw [hcur, hmi] at h1
  obtain ⟨-, e2⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
  subst s1
  obtain ⟨-, hcv, hexv⟩ := VirtOffNv.okn_lookupPart hnr.1.1 σ.curThread (Fl4Spec.toBl cptr.bv) info σ rfl _ t2 ha
  dsimp only at hcv hexv
  subst hcap; subst hargsE
  have hnv0 : ∀ x ∈ exs.head?, ¬ Fl4Spec.IsVirtCap x.1 := fun x hx => hexv x (List.mem_of_mem_head? hx)
  have hex0 : ExtraSRel Z.th (L.mem s) (exAt e 0) exs := ExtraOK.relS J.xtop.rel.1 hXO
  have hlv : Fl4Spec.dataToNat info.miLabel = info'.label.val := by rw [← hLb, dataToNat_bv]
  show ¬ VirtOffNv.Route3 fp info.miLabel (argsU.map UScalar.bv) (absCap c) exs ∨
    VirtAgree.ErrAgree fp (Fl4Spec.toBl cptr.bv) info (sl, absCap c, exs, buffer) (argsU.map UScalar.bv) σ
  by_cases hR : VirtOffNv.Route3 fp info.miLabel (argsU.map UScalar.bv) (absCap c) exs
  swap
  · exact Or.inl hR
  right
  have hM := fun hN => hP info' info buf buffer r2 (.ok exs) argsU hinfo hmi hbuf hbuffer hr2 her hmrs sl c e exs
    hsl hc hget he rfl hN
  cases c with
  | Thread p =>
    obtain ⟨hfp, hl⟩ : ¬ fp ∧ Fl4Spec.dataToNat info.miLabel = Fl4Spec.fl4SetEptRootLabel := hR
    have hfp' : fp = false := by simpa using hfp
    subst hfp'
    have hlab : info'.label = fl4_abi.label.TCBSetEPTRoot := by
      rw [u64_val_eq, lbl_tcbSetEPTRoot_val, ← hlv, hl]; rfl
    have hV := (hM trivial : JPathMEU30 (L := L) arI AR Z H Cs D s a σ info'.label (msgLen info' buf) bl call don
      false buf e info.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct (.Thread p)) hlab
    rw [hlab] at hV
    have hcv' : capV (L.mem s) (cslotAddr sl) = .Thread p := by rw [capAt_capV] at hc; simpa using hc
    obtain ⟨q, hq1, hq2⟩ := hsl
    have hp : Z.th p = some .tcb := (slot_cap_wf J.xtop ⟨q, hq1, Or.inl hq2⟩ hcv').2
    exact errAgree_of rfl (agree_thread88 arI s a σ (msgLen info' buf) (cslotAddr sl) p bl call don buf e ct hct
      (J.stallT p (J.thT p hp)) Z.th (exAt e 0) (exAt_idx0 e) exs hex0 hnv0 info.miLabel hl _ _ sl buffer hV)
  | Frame p sz rt d m ie asid va =>
    have hl : Fl4Spec.dataToNat info.miLabel = Fl4Spec.fl4PageMapEptLabel := hR
    have hlab : info'.label = fl4_abi.label.X86PageMapEPT := by
      rw [u64_val_eq, show fl4_abi.label.X86PageMapEPT.val = 60 by simp [fl4_abi.label.X86PageMapEPT], ← hlv, hl]
      rfl
    have hN : Vs.NativeCap (.Frame p sz rt d m ie asid va) := by
      rintro ⟨rfl, rfl⟩
      exact hcv (by simp [absCap, Fl4Spec.IsVirtCap])
    have hV := (hM hN : JPathMEU30 (L := L) arI AR Z H Cs D s a σ info'.label (msgLen info' buf) bl call don
      fp buf e info.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct (.Frame p sz rt d m ie asid va))
      (Or.inr hlab)
    rw [hlab] at hV
    exact errAgree_of rfl (agree_frame60 arI s a σ (msgLen info' buf) (cslotAddr sl) p sz rt d m ie asid va bl call
      don fp buf e ct hct argsU hLen hArgs Z.th (exAt e 0) (exAt_idx0 e) exs hex0 hnv0 info.miLabel hl _ sl buffer
      hV)
  | Untyped p sb fi dev =>
    simp only [VirtOffNv.Route3, absCap] at hR
    obtain ⟨hg, h6, hne, hvtx, -⟩ := hR
    have hg' := hg
    rw [← hLb] at hg'
    have hlab : info'.label = fl4_abi.label.UntypedRetype := (genInvocationType_untyped_iff _).1 hg'
    simp only [List.length_map] at h6
    obtain ⟨nt, rest, hrest⟩ : ∃ nt rest, argsU = nt :: rest := by
      cases argsU with
      | nil => simp at h6
      | cons x r => exact ⟨x, r, rfl⟩
    have hnt : argsU.head? = some nt := by rw [hrest]; rfl
    have hvtx' : 14 ≤ nt.val ∧ nt.val ≤ 18 := by
      rw [hrest] at hvtx
      simpa [Fl4Spec.isVtxObjectTypeNum, dataToNat_bv] using hvtx
    have hx0n : exAt e 0 ≠ 0#u64 := by
      rcases hex0 with ⟨-, hnil⟩ | ⟨h0, -⟩
      · subst hnil; exact absurd rfl hne
      · exact h0
    have hV : JVtxScope (L := L) arI AR s a σ info'.label (msgLen info' buf) (.Untyped p sb fi dev) bl call don fp
        buf e info.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct := by
      have hM' := (hM trivial : JPathMEU30 (L := L) arI AR Z H Cs D s a σ info'.label (msgLen info' buf) bl call
        don fp buf e info.miLabel argsU (Fl4Spec.toBl cptr.bv) sl exs buffer ct (.Untyped p sb fi dev))
      cases dev with
      | false => exact (hM'.2 rfl).vtx nt hnt hvtx'.1 (by omega)
      | true => exact (hM'.1 rfl).vtx nt hnt hvtx'.1 (by omega)
    rw [hlab] at hV
    exact errAgree_of rfl (agree_untypedGate arI s a σ (msgLen info' buf) (cslotAddr sl) p sb fi dev bl call don fp
      buf e ct hct argsU hLen (by omega) hArgs Z.th (exAt e 0) (exAt_idx0 e) hx0n exs hex0 nt hnt hvtx'.1
      (by omega) hvirt hvk info.miLabel hg _ sl buffer hV)
  | _ => first
    | exact (hR : False).elim
    | exact absurd hR (by simp [VirtOffNv.Route3, absCap])
    | exact absurd hR (by unfold absCap; split <;> simp [VirtOffNv.Route3])

theorem regIdx_of_midSysR {n : I64} {c : Fl4Spec.Syscall} {rg : U64} {sr : Fl4Spec.Register} {cr : Bool}
    (h : MidSysR n c rg sr cr) : regIdx sr = rg ∧ VirtR7eK.sysReg c = some sr ∧ VirtScope8.sysFp c = true := by
  rcases h with ⟨-, rfl, rfl, rfl, -⟩ | ⟨-, rfl, rfl, rfl, -⟩ | ⟨-, rfl, rfl, rfl, -⟩
  · exact ⟨regIdx_reply, rfl, rfl⟩
  · exact ⟨regIdx_nbsendRecvDest, rfl, rfl⟩
  · exact ⟨regIdx_reply, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **U36I's dispatch premise gives the narrowed route scope at the dispatch state** (module docstring). -/
theorem offRouteS8_of_disp (hvk : Fl4Spec.virtKind = .none) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hvirt : arI.virtualization a = ok 0#u64)
    (hnr : VirtR7e.NR σ) {n : I64} {c : Fl4Spec.Syscall} (hn : NativeSys n c)
    (hK : KDispHypsKVU32 (L := L) arI AR Z H Cs D s a σ n c) : VirtScope8.OffRouteS8 c σ := by
  intro reg hreg cptr t' hm
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  obtain ⟨-, xs, hks⟩ := J.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hxs := (J.xtop.irelK J.ks J.buf).1.toE.at_tcb hctT hks
  have hk' : σ.kheap σ.curThread = some (.tcb xs) := by rw [hcur]; exact hks
  have hm' : cptr = Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs reg) ∧ t' = σ := by
    unfold Fl4Spec.getCapReg at hm
    obtain ⟨y, hy, hm⟩ := hm
    obtain rfl := Set.mem_singleton_iff.1 hy
    unfold Fl4Spec.NonDet.liftM at hm
    obtain ⟨z, hz, hm⟩ := hm
    rw [Endp.asUser_getRegister_eq hk'] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    exact Prod.mk.inj (Set.mem_singleton_iff.1 hm)
  obtain ⟨rfl, rfl⟩ := hm'
  have hregv : ∀ rg, regIdx reg = rg →
      Fl4Spec.dataToCptr (xs.tcbArch.tcbContext.userRegs reg) = Fl4Spec.toBl (L.mem s (regA ct rg)).bv := by
    intro rg h; rw [← h, hxs.regs]; rfl
  rcases hn with ⟨call, bl, don, hinv, hc⟩ | ⟨bl, cr, -, hc⟩ | ⟨-, hc⟩ | hmid
  · have hfp : VirtScope8.sysFp c = false ∧ reg = Fl4Spec.cap_register := by
      subst hc; unfold invSysOf at hreg ⊢
      cases call <;> cases bl <;> simp [VirtR7eK.sysReg, VirtScope8.sysFp] at hreg ⊢ <;> exact hreg.symm
    obtain ⟨hf, rfl⟩ := hfp
    rw [hf, hregv _ regIdx_cap]
    exact offRoute6_of_path arI hvk J hvirt hnr hct (hK.inv ct call bl don hct hinv).2
  · subst hc; exfalso
    cases bl <;> cases cr <;> simp [recvSysOf, VirtR7eK.sysReg] at hreg
  · subst hc; exfalso; simp [VirtR7eK.sysReg] at hreg
  · obtain ⟨rg, sr, cr, hmr⟩ := midSysR_of hmid
    obtain ⟨hidx, hsr, hf⟩ := regIdx_of_midSysR hmr
    rw [hsr] at hreg
    cases hreg
    rw [hf, hregv _ hidx]
    exact offRoute6_of_path arI hvk J hvirt hnr hct (hK.mid ct rg _ cr hct hmr).2

end

end

end Fl4Proofs.P3.SInvR.G5

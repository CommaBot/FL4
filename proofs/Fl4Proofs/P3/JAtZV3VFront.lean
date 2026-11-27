/-
P3 (line mmuAD, gen 40): **the V-side VCPU invocation step at `JAtZV3` from the syscall front end** — the decode
stage of FL4's `handle_invocation` (syscall.rs l. 170-205) for an invoked `Cap::Vcpu { ptr }` (l. 153), with every
input of gen 39's `JAtZV3.vcpuInvJ5` derived at `JAtZV3` from the front end's reads, except EnableIOPort's
`IoFresh` (kept, owner decision Q2).

* **`JAtZB.argsJ`**: P3/FrontEndExtra's `JAtZ.argsJ` over `JAtZB` (statement and proof verbatim, `J : JAtZ` read as
  `J : JAtZB`; it reads no `JAtZ.ext`; the source's `maxHeartbeats 4000000` kept).
* **`JAtZB.bWord`**: every tracked buffer word (`Z.B`) is 8-aligned (`IPlaced`'s `balign`) and off every VCPU of `V`
  (`JCarry.bufPg`: a word of a spec data page, apart from each VCPU by `JVm.sep`; as `JAtZB.jvLay`'s `uv`).
* **`JAtZV3.ipcBuf`**: `Endp.IpcBufCapOK σ` (`JAtZB.bok`) and `Endp.BufCover Z.T Z.B σ` (`bufCover_of_frameCover`
  with `JAtZB.fcov`) at `JAtZV3` — what the native entry takes from `JEntryGlob` (since gl15 from `JAtZ.xferH`), here
  from `JAtZV3`'s base, so `JAtZV3.frontJ` needs no hypothesis beyond the reads.
* **`JAtZV3.bufOut`**: FL4's sending buffer (`lookup_ipc_buffer … false ct`) satisfies `BufOut V buf` (its MR words
  are `Z.B` words by `BufCover`, then `bWord`).
* **`JAtZV3.vargs`**: the spec's `getMrs` words satisfy `VArgs` at FL4's `msgLen info buf` (`JAtZB.argsJ`).
* **`JAtZV3.vcpuCapV`**: a slot of `Z.th` holding `Vcpu p` has `p ∈ V` (`JExtV.cap`) and a spec VCPU at `p`
  (`JVm.spec`).
* `zv_ex0Cap` / `zv_ex0Null`: FL4's first extra slot `exAt e 0`, its null flag and its cap (`Null` for a null slot).
* **`VFrontPost`**: the decode stage's post with the spec's actual label (`mi.miLabel`), arguments (`getMrs`), extra
  caps (`lookupExtraCaps`) and buffer — for every first-phase flag, cap reference, slot, `onCore` / `remoteCur`
  oracles and block/call/donate flags: the extended decoder's error `(.error e', σ)` with FL4's `Err e`
  (`SysErrRel`, store and `JAtZV3` kept), or its success `(.ok (.vcpu inv), σ)`, the extended perform's single
  outcome `(.ok rep, σ')` and `JAtZV3` at FL4's `s'` / `σ'`, with `VDecTail` from `s'` to FL4's final state.
* **`JAtZV3.vcpuFrontJ`** — the top: from `JAtZV3`, FL4's `syscall.decode_invocation` on the front end's values
  (`info.label`, `msgLen info buf`, the invoked `Vcpu p` cap of an `IsSlot` slot, `buf`, the extra-slot array `e`
  of a successful `lookup_extra_caps`) satisfies `VFrontPost` at the spec's front-end values. Hypotheses: the
  front end's reads (FL4: `cur_thread`, `msg_info`, `lookup_ipc_buffer false`, `lookup_extra_caps = .Ok e`; spec:
  `getMessageInfo`, `lookupIpcBuffer false`, `lookupExtraCaps = .ok exs`, `getMrs`, each its single outcome as in
  HandleTopX's `handle_invocation_refinesMX`), the invoked slot (`IsSlot Z.th x`, `capV x = .Vcpu p`: what the
  lookup's `WalkRel` gives), and the scope **`IoFreshEx`** (EnableIOPort only: FL4's first extra slot, if not
  null, holds no IoPort cap with a non-zero owner word — `IoFresh`, Q2).

What is still missing between this and a whole `fl4HandleInvocationVF` step at `JAtZV3` (not proved here):
(1) the lookup-failure and extra-cap-failure arms with `blocking` (FL4 `handle_fault`, l. 175 / 185; no
`handle_fault` theorem at `JAtZV3`); (2) the reply of a decode error (`reply_error`, l. 197; spec
`fl4ReplyFromKernelError`) at `JAtZV3`; (3) the success tail: the spec runs `setThreadState thread .restart`
*before* the perform and `replyFromKernel (0, reply)` / `setThreadState .running` after it, FL4 replies inside the
decode (`VDecTail`) and then `set_thread_state TS_RUNNING` when the state is `TS_RESTART` (l. 199-204), while
`VFrontPost`'s perform runs from the decode's state `σ`: the commutation of `performVcpuInvocationF` with that
`setThreadState` (every VCPU invocation but SetTCB touches only the VCPU object; SetTCB's
`associateVcpuTcbF` writes the TCB's VCPU field, not its state) and the reply relation at `JAtZV3` are needed.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3EioFront
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}


set_option maxHeartbeats 4000000 in
/-- **`JAtZ.argsJ` over `JAtZB`** (verbatim; module docstring). P3/FrontEndExtra: **The argument words at `J`**: the spec's `getMrs` words are FL4's
`syscall_arg`s, as many as `msgLen`, and the first five arguments are
`fl4GetMr`'s (`ArgRel`, also past the message length). -/
theorem JAtZB.argsJ {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s ar σ)
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

/-- **The tracked buffer words: aligned, off every VCPU** (module docstring). -/
theorem JAtZB.bWord {V : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) {wp : U64 × Fl4Spec.Word}
    (hwp : wp ∈ Z.B) : P1.Aligned wp.1 ∧ ∀ v ∈ V, wp.1.val < v.val ∨ v.val + 32768 ≤ wp.1.val := by
  refine ⟨(J.ip.e.balign _ hwp).1, fun v hv => ?_⟩
  obtain ⟨q, vms, hq, g1, g2⟩ := J.carry.bufPg wp hwp
  obtain ⟨x, hx⟩ := Jv.spec v hv
  have hne : q ≠ v.bv := fun e => by rw [e, hx] at hq; cases hq
  rcases Jv.sep v hv q _ hq hne with e | e
  · left
    have eb : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := by
      simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
    rw [eb] at e; omega
  · right; omega

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **The IPC-buffer facts at `JAtZV3`** (module docstring). -/
theorem JAtZV3.ipcBuf (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) :
    Endp.IpcBufCapOK σ ∧ Endp.BufCover Z.T Z.B σ :=
  ⟨J.z2.zv.base.bok, bufCover_of_frameCover J.z2.zv.base.bok J.z2.zv.base.fcov⟩

/-- **The sending buffer's MR words are off every VCPU** (module docstring). -/
theorem JAtZV3.bufOut (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {buf : U64} (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf) : BufOut V buf := by
  have B := J.z2.zv.base
  obtain ⟨hcur, -⟩ := B.curEq hct
  obtain ⟨htcb, xs, hks⟩ := B.xtop.curTcb hcur
  have hctT : ct ∈ Z.T := TopSR.cur_mem B.xtop.fin.1 hcur.symm
  have hb := lookup_buf_full s σ B.xtop.rel.2.1.1 B.xtop.rel.2.1.2.1 htcb hks B.bok false
  rw [hbuf, WP.spec_ok] at hb
  obtain ⟨hsb, hsbp⟩ := hb
  obtain ⟨xs', hks', hws⟩ := B.buf ct hctT
  rw [hks] at hks'; cases hks'
  intro h0 j hj
  cases hq : Endp.ipcBufOf false xs with
  | none => exact absurd (hsb.2 hq) h0
  | some sp =>
    have hm : Endp.BufMap Z.B buf sp :=
      bufCover_of_frameCover B.bok B.fcov ct hctT xs false sp hks hq buf (hsbp hws sp hq)
    have hi : (core.num.U64.wrapping_add j 1#u64).val < 128 := by
      rw [core.num.U64.wrapping_add_val_eq]
      exact lt_of_le_of_lt (Nat.mod_le _ _) (by simp; omega)
    exact B.bWord J.z2.zv.vm (hm _ hi)

theorem zv_map_mk (args : List Fl4Spec.Data) : (args.map fun d => (⟨d⟩ : U64)).map UScalar.bv = args := by
  induction args with
  | nil => rfl
  | cons d t ih =>
    simp only [List.map_cons]
    rw [ih]

/-- **The spec's arguments against FL4's `syscall_arg` words** (module docstring). -/
theorem JAtZV3.vargs (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {info : msginfo.MessageInfo} (hinfo : msg.msg_info st s ct = ok info)
    {mi : Fl4Spec.MessageInfo} (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    {buf : U64} (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    {buffer : Option Fl4Spec.ObjRef}
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    {args : List Fl4Spec.Data} (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(args, σ)}, False)) :
    VArgs st s ct buf (msgLen info buf) args := by
  have hmrs' : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ =
      ({((args.map fun d => (⟨d⟩ : U64)).map UScalar.bv, σ)}, False) := by rw [zv_map_mk]; exact hmrs
  obtain ⟨hlen, hget, -⟩ := J.z2.zv.base.argsJ J.ipcBuf.1 J.ipcBuf.2 hct hinfo hmi hbuf hbuffer hmrs'
  rw [List.length_map] at hlen
  refine ⟨hlen.symm, fun i w hi hw => ?_⟩
  have hil : i < args.length := by omega
  have hiv : (⟨BitVec.ofNat 64 i⟩ : U64).val = i := by
    show (BitVec.ofNat 64 i).toNat = i
    have : (msgLen info buf).val < 2 ^ 64 := (msgLen info buf).hBounds
    simp; omega
  have h1 : (args.map fun d => (⟨d⟩ : U64))[(⟨BitVec.ofNat 64 i⟩ : U64).val]? = some ⟨args[i]⟩ := by
    rw [hiv, List.getElem?_map, List.getElem?_eq_getElem hil]; rfl
  have h2 := hget _ _ h1
  rw [hw] at h2
  have e := ok_inj h2
  subst e
  show args.getD i 0 = args[i]
  rw [List.getD_eq_getElem]

/-- **A VCPU cap of a slot names a VCPU of `V` with its spec object** (module docstring). -/
theorem JAtZV3.vcpuCapV (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {x p : U64}
    (hx : IsSlot Z.th x) (hc : capV (L.mem s) x = .Vcpu p) :
    p ∈ V ∧ ∃ vs, σ.kheap p.bv = some (.archObj (.vcpu vs)) := by
  have h := J.z2.zv.extv.cap x hx
  rw [hc] at h
  exact ⟨h, J.z2.zv.vm.spec p h⟩

end

theorem zv_ex0Idx (e : Aeneas.Std.Array obj.Slot 3#usize) : Array.index_usize e 0#usize = ok (exAt e 0) :=
  index_exAt e 0#usize (by decide)

theorem zv_ex0Null (sl : obj.Slot) : obj.Slot.is_null sl = ok (decide (sl = 0#u64)) := rfl


/-- **Scope (EnableIOPort, decision Q2)**: FL4's first extra slot, when not null, holds no IoPort cap with a
non-zero owner word (`IoFresh` at the front end's slot; module docstring). -/
def IoFreshEx (m : U64 → U64) (e : Aeneas.Std.Array obj.Slot 3#usize) : Prop :=
  exAt e 0 ≠ 0#u64 → ∀ f l q, capV m (exAt e 0) = .IoPort f l q → q = 0#u64

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **The decode stage's post at the spec's front-end values** (module docstring). -/
def VFrontPost (arI : machine.Arch A) (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap)
    (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (σ : Fl4Spec.State Unit) (ct : U64)
    (call : Bool) (lbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (p : U64)
    (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (r : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∀ (fp : Bool) (cref : Fl4Spec.CapRef) (slot : Fl4Spec.CslotPtr) (onCore remoteCur : Fl4Spec.ObjRef → Bool)
    (bl ca cd : Bool),
    (∃ e e', r.1 = .Err e ∧ SysErrRel e e' ∧
        ExceptT.run (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp lbl args cref slot
          (.archObjectCap (.vcpuCap p.bv)) ec buffer) σ = ({(.error e', σ)}, False) ∧
        r.2.1 = s ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s r.2.2 σ) ∨
      (∃ (inv : Fl4Spec.VcpuInvocation) (rep : List Fl4Spec.Data) (s' : S) (σ' : Fl4Spec.State Unit)
          (Ac' : Set U64) (Lst' : U64 → List U64), r.1 = .Ok () ∧
        ExceptT.run (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp lbl args cref slot
          (.archObjectCap (.vcpuCap p.bv)) ec buffer) σ = ({(.ok (.vcpu inv), σ)}, False) ∧
        ExceptT.run (Fl4Spec.fl4PerformInvocationVF (Z := Unit) onCore remoteCur bl ca cd (.vcpu inv)) σ =
          ({(.ok rep, σ')}, False) ∧
        JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D s' r.2.2 σ' ∧ VDecTail st ct call rep s' r.2.1)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **The V-side VCPU invocation step at `JAtZV3` from the syscall front end** (module docstring). -/
theorem JAtZV3.vcpuFrontJ (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {info : msginfo.MessageInfo} (hinfo : msg.msg_info st s ct = ok info)
    {mi : Fl4Spec.MessageInfo} (hmi : Fl4Spec.getMessageInfo (Z := Unit) ct.bv σ = ({(mi, σ)}, False))
    {buf : U64} (hbuf : msg.lookup_ipc_buffer st s false ct = ok buf)
    {buffer : Option Fl4Spec.ObjRef}
    (hbuffer : Fl4Spec.lookupIpcBuffer (Z := Unit) false ct.bv σ = ({(buffer, σ)}, False))
    {e : Aeneas.Std.Array obj.Slot 3#usize} (hr2 : ipc.lookup_extra_caps st s ct buf info = ok (.Ok e))
    {exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (her : (Fl4Spec.lookupExtraCaps (Z := Unit) ct.bv buffer mi).run σ = ({(.ok exs, σ)}, False))
    {args : List Fl4Spec.Data} (hmrs : Fl4Spec.getMrs (Z := Unit) ct.bv buffer mi σ = ({(args, σ)}, False))
    {x p : U64} (hx : IsSlot Z.th x) (hcx : capV (L.mem s) x = .Vcpu p)
    (slot : obj.Slot) (block call cd fp : Bool)
    (hIo : info.label = fl4_abi.label.X86VCPUEnableIOPort → IoFreshEx (L.mem s) e) :
    syscall.decode_invocation st arI s a info.label (msgLen info buf) slot (.Vcpu p) block call cd fp buf e ⦃ r =>
      VFrontPost (L := L) arI V X AR Z H Cs Ac Lst D s σ ct call mi.miLabel args p exs buffer r ⦄ := by
  have hP : Placed Z.th := J.z2.zv.base.xtop.rel.1
  obtain ⟨hLb, hXO⟩ := J.frontJ J.ipcBuf.1 J.ipcBuf.2 hct hinfo hmi hbuf hbuffer hr2 her
  have hX := hXO e exs rfl rfl
  obtain ⟨hp, vs, hk⟩ := J.vcpuCapV hx hcx
  have hsl := zv_ex0Idx e
  have hbn := zv_ex0Null (exAt e 0)
  have hc : decide (exAt e 0 = 0#u64) = false → obj.Slot.cap st (exAt e 0) s =
      ok (if exAt e 0 = 0#u64 then .Null else capV (L.mem s) (exAt e 0)) := by
    intro hb
    rw [if_neg (of_decide_eq_false hb), slot_cap_eq, capAt_capV]
  have hcv : exAt e 0 ≠ 0#u64 →
      (if exAt e 0 = 0#u64 then capability.Cap.Null else capV (L.mem s) (exAt e 0)) = capV (L.mem s) (exAt e 0) :=
    fun h => if_neg h
  have hct' : ∀ t, (if exAt e 0 = 0#u64 then capability.Cap.Null else capV (L.mem s) (exAt e 0)) = .Thread t →
      Z.th t = some .tcb := by
    intro t ht
    by_cases h0 : exAt e 0 = 0#u64
    · rw [if_pos h0] at ht; cases ht
    · obtain ⟨pc, r, idx, hth, hl, hxe⟩ := ExtraOK.eioSlot hP hX (exAt e 0) hsl (by rw [hbn, decide_eq_false h0])
      have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by rw [hl]; exact hth)⟩
      have hS : IsSlot Z.th (exAt e 0) := by rw [hxe]; exact hA.isSlot
      rw [hcv h0] at ht
      exact J.z2.zv.base.thrCap hS t ht
  have hIo' : info.label = fl4_abi.label.X86VCPUEnableIOPort →
      IoFresh (decide (exAt e 0 = 0#u64)) (if exAt e 0 = 0#u64 then .Null else capV (L.mem s) (exAt e 0)) := by
    intro hl hb f l q hq
    have hne : exAt e 0 ≠ 0#u64 := of_decide_eq_false hb
    rw [hcv hne] at hq
    exact hIo hl hne f l q hq
  have hEs : info.label = fl4_abi.label.X86VCPUEnableIOPort → EioScope Z.th e p :=
    fun _ => ExtraOK.eioScope hP hX hcx
  have hVC : VCaps (decide (exAt e 0 = 0#u64))
      (if exAt e 0 = 0#u64 then .Null else capV (L.mem s) (exAt e 0)) exs := by
    have h := ExtraOK.vcaps hP hX hsl hbn
    refine ⟨h.1, fun hb => ?_⟩
    rw [hcv (of_decide_eq_false hb)]; exact h.2 hb
  have hA := J.vargs hct hinfo hmi hbuf hbuffer hmrs
  refine WP.spec_mono (J.vcpuInvJ5 hK hSy hVA hCap hAT hp hk info.label (msgLen info buf) slot block call cd fp
    (J.bufOut hct hbuf) e hsl hbn hc hct' hIo' hEs) ?_
  rintro r ⟨ct', hct2, HH⟩
  rw [hct] at hct2
  have e1 := ok_inj hct2
  subst e1
  intro fp' cref slot' onCore remoteCur bl ca cd'
  rw [← hLb]
  exact HH args exs hA hVC fp' cref slot' buffer onCore remoteCur bl ca cd'

end

end

end Fl4Proofs.P3

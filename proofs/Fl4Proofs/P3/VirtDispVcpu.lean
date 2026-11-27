/-
P3x for virtualization (line virt, gen 20, item 1): **WriteMSR / WriteVMCB through FL4's invocation dispatcher**,
against the extended spec's dispatcher (`fl4DecodeInvocationV`, `fl4PerformInvocationV`, Ext/VirtDispatch), whose
VCPU arms are `decodeVcpuInvocation` and `performVcpuInvocation` (Ext/VirtVcpu).

FL4 side: `syscall::handle_invocation` (syscall.rs l. 171-215) reads the message info, looks the cap up, reads the
IPC buffer and the extra caps — all reads, the state is passed unchanged — and calls `syscall::decode_invocation`,
whose `Vcpu` arm is `vcpu::decode` (Funs.lean `syscall.decode_invocation`, `| capability.Cap.Vcpu ptr =>`).

* `decode_invocation_vcpu_eq`: the dispatcher on a `Vcpu v` cap is `vcpu.decode … v` (any phase, any label).
* `fl4DecodeInvocationV_vcpu`, `fl4PerformInvocationV_vcpu` (`rfl`): the spec dispatcher's VCPU arms;
  `mem_performV_vcpu`: an outcome of the extended perform on `.vcpu i` is an `ok` outcome of
  `performVcpuInvocation i`.
* `VRelAt.congrA`: `VRelAt` reads only aligned words of the VCPU object.
* **`wrmsr_disp`** (both backends), **`wrvmcb_disp`** (both backends: SVM by gen 18's `wrvmcb_sys`, VMX by gen 19's
  `wrvmcb_vmx`): FL4's `decode_invocation` on a `Vcpu v` cap with the WriteMSR / WriteVMCB label, from a `ReplyPl`
  state where `v` relates (`VRelAt`), the entry registers `regs` (`hregs`) and the length `len`: after the stall
  `s1` (writes ⊆ `IPI_PENDING`) either the spec dispatcher's decode has the single outcome
  `ok (.vcpu (.writeMsr v f value))` (resp. `.writeVmcb v f val`), FL4 answers `Ok` and every outcome of the
  spec dispatcher's perform is `ok` and relates at `v` to FL4's final state; or the spec decode's single outcome is
  `error e'` with the state unchanged, FL4 answers the related `Err e`, its state is `s1` and `v` still relates.
  Spec dispatcher arguments (`firstPhase`, cap index, slot, extra caps, buffer, `onCore`, flags) are arbitrary.
* `hinvTail`: `handle_invocation`'s tail after the decode (the `Ok` tail is HandleTop's `flTail`; `Sys` errors
  `reply_error` when called). **`handle_invocation_vcpu_eq`**: at the syscall entry state `s`, given the front end's
  reads (`cur_thread`, `msg_info`, `lookup_slot` with the cap `Vcpu v` at the slot, `lookup_ipc_buffer`,
  `lookup_extra_caps`), `handle_invocation` is `vcpu.decode` at `s` with `info.label`, `msgLen info buf`, the call
  flag, then `hinvTail`.
* **`wrmsr_hinv`**, **`wrvmcb_hinv`**: from the syscall entry: `handle_invocation`'s result is `hinvTail` of a decode
  result that satisfies `wrmsr_disp`'s (resp. `wrvmcb_disp`'s) post.

Not covered here (open, gen 20 handoff): the spec side of the tail (`fl4HandleInvocationV`'s restart / reply /
`Running` steps) and `VRelAt` across FL4's tail (the success tail is a no-op once the decode's own `vcpu.reply`
left the thread `Running`; the error reply writes the caller's IPC buffer, so it needs the buffer apart from the
VCPU — a placement fact of the VM-epoch relation).

Named premises: as gen 18/19 — `CapAgree ar a` [P], `CapKeepStall ar` [P], `VirtCodeAgree ar a` [P],
`VirtCodeKeepStall ar` [P]; `P0.ArchTotal ar` (totality). No new premise. The front-end reads of
`handle_invocation_vcpu_eq` are the statement's scope (explicit values, as HandleTop's `handle_invocation_refines`).
New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtWrVmcbVmx
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtDispVcpu
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanSvm
open Fl4Proofs.P3.VirtVcpuRel Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtVmcbStore Fl4Proofs.P3.VirtReplyKeep Fl4Proofs.P3.VirtVmcbDec
open Fl4Proofs.P3.VirtVmcbTail Fl4Proofs.P3.VirtMsrE2E Fl4Proofs.P3.VirtVmcbE2E Fl4Proofs.P3.VirtArgsSpec
open Fl4Proofs.P3.VirtWrSys Fl4Proofs.P3.VirtWrVmcbVmx

noncomputable section

/-! ## The two dispatchers' VCPU arms -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **FL4's dispatcher on a `Vcpu` cap is `vcpu::decode`** (any label, any phase). -/
theorem decode_invocation_vcpu_eq (s : S) (a : A) (lbl length slot : U64) (p : U64) (blk call don fp : Bool)
    (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) :
    syscall.decode_invocation st ar s a lbl length slot (.Vcpu p) blk call don fp buf extra =
      vcpu.decode st ar s a lbl length p call buf extra := by
  obtain ⟨ct, hct, -⟩ := spec_ex (P1.sched.cur_thread.spec (L := L) s)
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]

end

section
variable {Z : Type} [StateExt Z]

theorem fl4DecodeInvocationV_vcpu (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (slot : CslotPtr)
    (v : ObjRef) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    fl4DecodeInvocationV (Z := Z) fp label args ci slot (.archObjectCap (.vcpuCap v)) excaps buffer =
      NonDetE.liftME Fl4InvocationV.vcpu (decodeVcpuInvocation label args v excaps) := rfl

theorem fl4PerformInvocationV_vcpu (onCore : ObjRef → Bool) (b c d : Bool) (i : VcpuInvocation) :
    fl4PerformInvocationV (Z := Z) onCore b c d (.vcpu i) = NonDetE.liftE (performVcpuInvocation i) := rfl

/-- An outcome of the extended perform on a VCPU invocation is an `ok` outcome of `performVcpuInvocation`. -/
theorem mem_performV_vcpu {onCore : ObjRef → Bool} {b c d : Bool} {i : VcpuInvocation} {σ : State Z}
    {x : Except Unit (List Data) × State Z}
    (hx : x ∈ ((fl4PerformInvocationV (Z := Z) onCore b c d (.vcpu i)).run σ).1) :
    ∃ y ∈ (performVcpuInvocation (Z := Z) i σ).1, x = (.ok y.1, y.2) := by
  rw [fl4PerformInvocationV_vcpu] at hx
  unfold NonDetE.liftE at hx
  rw [ExceptT.run_lift] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact ⟨y, hy, Set.mem_singleton_iff.1 hxy⟩

/-- The spec dispatcher's decode on a VCPU cap whose VCPU decode returns `a`. -/
theorem decV_ok {fp : Bool} {label : Data} {args : List Data} {ci : CapRef} {slot : CslotPtr} {v : ObjRef}
    {excaps : List (Cap × CslotPtr)} {buffer : Option ObjRef} {σ : State Z} {a : VcpuInvocation}
    (h : ExceptT.run (decodeVcpuInvocation (Z := Z) label args v excaps) σ = ({(.ok a, σ)}, False)) :
    (fl4DecodeInvocationV (Z := Z) fp label args ci slot (.archObjectCap (.vcpuCap v)) excaps buffer).run σ =
      ({(.ok (.vcpu a), σ)}, False) := by
  rw [fl4DecodeInvocationV_vcpu]; exact run_liftME_ok h

/-- The spec dispatcher's decode on a VCPU cap whose VCPU decode throws `e`. -/
theorem decV_err {fp : Bool} {label : Data} {args : List Data} {ci : CapRef} {slot : CslotPtr} {v : ObjRef}
    {excaps : List (Cap × CslotPtr)} {buffer : Option ObjRef} {σ : State Z} {e : SyscallError}
    (h : ExceptT.run (decodeVcpuInvocation (Z := Z) label args v excaps) σ = ({(.error e, σ)}, False)) :
    (fl4DecodeInvocationV (Z := Z) fp label args ci slot (.archObjectCap (.vcpuCap v)) excaps buffer).run σ =
      ({(.error e, σ)}, False) := by
  rw [fl4DecodeInvocationV_vcpu]; exact run_liftME_err h

/-- `VRelAt` reads only aligned words of the VCPU object. -/
theorem VRelAt.congrA {mem mem' : Word → Word} {σ : State Z} {v : Word} (hm : AgreeAtA mem mem' v)
    (h : VRelAt mem σ v) : VRelAt mem' σ v := by
  obtain ⟨vs, hvs, hS, hV⟩ := h
  exact ⟨vs, hvs, fun e => VcpuRelSvm.congrA hm (hS e), fun e => VcpuRelVmx.congrA hm (hV e)⟩

end

/-! ## Through the dispatcher -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {Z : Type} [StateExt Z]

/-- The stall keeps `VRelAt` (its only write is `IPI_PENDING`, off the VCPU). -/
theorem vrel_stall {s s1 : S} {v : U64} (P : ReplyPl st v s) (hW : P1.WritesIn st s s1 (· = ipiA st s))
    {σ : State Z} (hR : VRelAt (memW st s) σ v.bv) : VRelAt (memW st s1) σ v.bv :=
  VRelAt.congrA (agreeA_of_writes P.fit hW fun o ho e => P.vo_ne_node ho (by simp [layout.node.IPI_PENDING]) e) hR

set_option maxHeartbeats 1000000 in
/-- **WriteMSR through FL4's dispatcher against the spec dispatcher** (module docstring; premises `CapAgree`,
`CapKeepStall`, `VirtCodeAgree`, `VirtCodeKeepStall`, all [P]). -/
theorem wrmsr_disp (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S} {v : U64} (P : ReplyPl st v s) {σ : State Z}
    (hR : VRelAt (memW st s) σ v.bv) (length slot : U64) (blk call don fp : Bool) (buf : U64)
    (ex : Aeneas.Std.Array obj.Slot 3#usize) (hlen : ¬ length < 2#u64) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : length.val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeMsr) (sfp : Bool) (ci : CapRef) (ssl : CslotPtr)
    (caps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (onCore : ObjRef → Bool) (sb sc sd : Bool) :
    syscall.decode_invocation st ar s a fl4_abi.label.X86VCPUWriteMSR length slot (.Vcpu v) blk call don fp buf ex
      ⦃ r => ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ f value : U64,
            (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ =
              ({(.ok (.vcpu (.writeMsr v.bv f.bv value.bv)), σ)}, False) ∧ r.1 = .Ok () ∧
            ∀ x ∈ ((fl4PerformInvocationV (Z := Z) onCore sb sc sd (.vcpu (.writeMsr v.bv f.bv value.bv))).run σ).1,
              (∃ rr, x.1 = .ok rr) ∧ VRelAt (memW st r.2.1) x.2 v.bv) ∨
          (∃ e e', (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ = ({(.error e', σ)}, False) ∧
            SysErrRel e e' ∧ r.1 = .Err e ∧ r.2.1 = s1 ∧ VRelAt (memW st s1) σ v.bv)) ⦄ := by
  rw [decode_invocation_vcpu_eq]
  refine WP.spec_mono (wrmsr_sys (Z := Z) (sbo := sbo) (um := um) hA hK hKv hc hk P hR length call buf ex hlen hregs hL hl caps) ?_
  rintro r ⟨s1, a1, f, value, hp, hW, hd | hd⟩
  · obtain ⟨hd, hr, hrel⟩ := hd
    refine ⟨s1, a1, hp, hW, Or.inl ⟨f, value, decV_ok (by rw [hd]; rfl), hr, fun x hx => ?_⟩⟩
    obtain ⟨y, hy, rfl⟩ := mem_performV_vcpu hx
    exact ⟨⟨y.1, rfl⟩, hrel y hy⟩
  · obtain ⟨e, e', hd, hE, hr, hs⟩ := hd
    exact ⟨s1, a1, hp, hW, Or.inr ⟨e, e', decV_err (by rw [hd]; rfl), hE, hr, hs, vrel_stall P hW hR⟩⟩

set_option maxHeartbeats 1000000 in
/-- **WriteVMCB through FL4's dispatcher against the spec dispatcher, both backends** (module docstring; premises
as `wrmsr_disp`). On VMX the spec throws `illegalOperation` and FL4 answers the related error. -/
theorem wrvmcb_disp (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S} {v : U64} (P : ReplyPl st v s) {σ : State Z}
    (hR : VRelAt (memW st s) σ v.bv) (length slot : U64) (blk call don fp : Bool) (buf : U64)
    (ex : Aeneas.Std.Array obj.Slot 3#usize) (hlen : ¬ length < 2#u64) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : length.val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeVmcb) (sfp : Bool) (ci : CapRef) (ssl : CslotPtr)
    (caps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (onCore : ObjRef → Bool) (sb sc sd : Bool) :
    syscall.decode_invocation st ar s a fl4_abi.label.X86VCPUWriteVMCB length slot (.Vcpu v) blk call don fp buf ex
      ⦃ r => ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ (f : U64) (val : Word),
            (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ =
              ({(.ok (.vcpu (.writeVmcb v.bv f.bv val)), σ)}, False) ∧ r.1 = .Ok () ∧
            ∀ x ∈ ((fl4PerformInvocationV (Z := Z) onCore sb sc sd (.vcpu (.writeVmcb v.bv f.bv val))).run σ).1,
              (∃ rr, x.1 = .ok rr) ∧ VRelAt (memW st r.2.1) x.2 v.bv) ∨
          (∃ e e', (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ = ({(.error e', σ)}, False) ∧
            SysErrRel e e' ∧ r.1 = .Err e ∧ r.2.1 = s1 ∧ VRelAt (memW st s1) σ v.bv)) ⦄ := by
  rw [decode_invocation_vcpu_eq]
  by_cases hsvm : virtKind = .svm
  · refine WP.spec_mono (wrvmcb_sys (Z := Z) (sbo := sbo) (um := um) hsvm hA hK hKv hc hk P hR length call buf ex hlen hregs hL hl caps) ?_
    rintro r ⟨s1, a1, f, value, hp, hW, hd | hd⟩
    · obtain ⟨val, hd, hr, hrel⟩ := hd
      refine ⟨s1, a1, hp, hW, Or.inl ⟨f, val, decV_ok (by rw [hd]; rfl), hr, fun x hx => ?_⟩⟩
      obtain ⟨y, hy, rfl⟩ := mem_performV_vcpu hx
      exact ⟨⟨y.1, rfl⟩, hrel y hy⟩
    · obtain ⟨e, e', hd, hE, hr, hs⟩ := hd
      exact ⟨s1, a1, hp, hW, Or.inr ⟨e, e', decV_err (by rw [hd]; rfl), hE, hr, hs, vrel_stall P hW hR⟩⟩
  · refine WP.spec_mono (wrvmcb_vmx (Z := Z) hsvm hA hKv hk P length call buf ex hlen hl
      (Endp.specMrs regs sbo um len) caps) ?_
    rintro r ⟨s1, a1, hp, hW, hd, e, hr, hE, hs, -⟩
    exact ⟨s1, a1, hp, hW, Or.inr ⟨e, .illegalOperation, decV_err (by rw [hd]; rfl), hE, hr, hs,
      vrel_stall P hW hR⟩⟩

end

/-! ## From the syscall entry (`handle_invocation`) -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- `handle_invocation`'s tail after the decode (syscall.rs l. 196-214, copied from the extracted body). -/
def hinvTail (st : machine.Store S) (t : U64) (is_call : Bool) (r3 : core.result.Result Unit error.Exc) (s1 : S)
    (a1 : A) : Result ((core.result.Result Unit error.Exc) × S × A) :=
  match r3 with
  | .Ok _ => flTail (st := st) t is_call s1 a1
  | .Err (.Fault _) => ok (.Ok (), s1, a1)
  | .Err (.Lookup _) => ok (.Ok (), s1, a1)
  | .Err (.Sys e2) =>
    if is_call then do
      let s2 ← syscall.reply_error st s1 t e2
      ok (.Ok (), s2, a1)
    else ok (.Ok (), s1, a1)
  | .Err .Preempted => ok (.Err .Preempted, s1, a1)

/-- `hinvTail` terminates (P0 totality of its reads and writes). -/
theorem hinvTail_total (t : U64) (is_call : Bool) (r3 : core.result.Result Unit error.Exc) (s1 : S) (a1 : A) :
    ∃ res, hinvTail st t is_call r3 s1 a1 = ok res := by
  have h : hinvTail st t is_call r3 s1 a1 ⦃ _ => True ⦄ := by
    unfold hinvTail
    cases r3 with
    | Ok u =>
      dsimp only
      unfold flTail
      refine WP.spec_bind (P0.obj.Tcb.state.p0 st t s1 L.total) fun i _ => ?_
      split
      · refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun s2 _ => ?_
        · split
          · exact WP.spec_mono (P0.msg.reply_success_empty.p0 st s1 t L.total) fun _ _ => trivial
          · exact (WP.spec_ok _).2 trivial
        · exact WP.spec_bind (P0.sched.set_thread_state.p0 st s2 t _ L.total) fun _ _ => (WP.spec_ok _).2 trivial
      · exact (WP.spec_ok _).2 trivial
    | Err e1 =>
      cases e1 with
      | Sys e2 =>
        dsimp only
        split
        · exact WP.spec_bind (P0.syscall.reply_error.p0 st s1 t e2 L.total) fun _ _ => (WP.spec_ok _).2 trivial
        · exact (WP.spec_ok _).2 trivial
      | _ => dsimp only; exact (WP.spec_ok _).2 trivial
  obtain ⟨x, hx, -⟩ := spec_ex h
  exact ⟨x, hx⟩

set_option maxHeartbeats 1000000 in
/-- **`handle_invocation` on a VCPU cap** (module docstring): at the syscall entry state, given the front end's
reads, the decode `vcpu.decode` runs at that same state, then `hinvTail`. -/
theorem handle_invocation_vcpu_eq (s : S) (a : A) (is_call blocking can_donate fp : Bool) (cptr : U64) {t : U64}
    (ht : sched.cur_thread st s = ok t) {info : msginfo.MessageInfo} (hinfo : msg.msg_info st s t = ok info)
    {r1 : cspace.Resolved} (hlk : cspace.lookup_slot st s t cptr = ok (.Ok r1)) {v : U64}
    (hcap : obj.Slot.cap st r1.slot s = ok (.Vcpu v)) {buf : U64}
    (hbuf : msg.lookup_ipc_buffer st s false t = ok buf) {e : Aeneas.Std.Array obj.Slot 3#usize}
    (hex : ipc.lookup_extra_caps st s t buf info = ok (.Ok e)) :
    syscall.handle_invocation st ar s a is_call blocking can_donate fp cptr =
      vcpu.decode st ar s a info.label (msgLen info buf) v is_call buf e >>= fun x =>
        hinvTail st t is_call x.1 x.2.1 x.2.2 := by
  unfold syscall.handle_invocation
  rw [ht]; simp only [bind_ok, hinfo, hlk, hcap, hbuf, hex]
  rw [msgLen_eq, bind_ok, decode_invocation_vcpu_eq]
  refine VirtMsrDec.bind_ext fun x => ?_
  obtain ⟨r3, s1, a1⟩ := x
  cases r3 with
  | Ok u => rfl
  | Err e1 => cases e1 <;> rfl

variable {Z : Type} [StateExt Z]

set_option maxHeartbeats 1000000 in
/-- **WriteMSR from the syscall entry** (module docstring; premises as `wrmsr_disp`): `handle_invocation`'s result
is `hinvTail` of a decode result satisfying `wrmsr_disp`'s post. -/
theorem wrmsr_hinv (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S} (is_call blocking can_donate fp : Bool) (cptr : U64)
    {t : U64} (ht : sched.cur_thread st s = ok t) {info : msginfo.MessageInfo}
    (hinfo : msg.msg_info st s t = ok info) (hlbl : info.label = fl4_abi.label.X86VCPUWriteMSR)
    {r1 : cspace.Resolved} (hlk : cspace.lookup_slot st s t cptr = ok (.Ok r1)) {v : U64}
    (hcap : obj.Slot.cap st r1.slot s = ok (.Vcpu v)) {buf : U64}
    (hbuf : msg.lookup_ipc_buffer st s false t = ok buf) {e : Aeneas.Std.Array obj.Slot 3#usize}
    (hex : ipc.lookup_extra_caps st s t buf info = ok (.Ok e)) (hlen : ¬ msgLen info buf < 2#u64)
    (P : ReplyPl st v s) {σ : State Z} (hR : VRelAt (memW st s) σ v.bv) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : (msgLen info buf).val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeMsr) (sfp : Bool) (ci : CapRef) (ssl : CslotPtr)
    (caps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (onCore : ObjRef → Bool) (sb sc sd : Bool) :
    syscall.handle_invocation st ar s a is_call blocking can_donate fp cptr ⦃ res =>
      ∃ (r3 : core.result.Result Unit error.Exc) (s2 : S) (a2 : A),
        vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteMSR (msgLen info buf) v is_call buf e = ok (r3, s2, a2) ∧
        hinvTail st t is_call r3 s2 a2 = ok res ∧
        ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ f value : U64,
            (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ =
              ({(.ok (.vcpu (.writeMsr v.bv f.bv value.bv)), σ)}, False) ∧ r3 = .Ok () ∧
            ∀ x ∈ ((fl4PerformInvocationV (Z := Z) onCore sb sc sd (.vcpu (.writeMsr v.bv f.bv value.bv))).run σ).1,
              (∃ rr, x.1 = .ok rr) ∧ VRelAt (memW st s2) x.2 v.bv) ∨
          (∃ e e', (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ = ({(.error e', σ)}, False) ∧
            SysErrRel e e' ∧ r3 = .Err e ∧ s2 = s1 ∧ VRelAt (memW st s1) σ v.bv)) ⦄ := by
  rw [handle_invocation_vcpu_eq (ar := ar) s a is_call blocking can_donate fp cptr ht hinfo hlk hcap hbuf hex, hlbl]
  have hD := wrmsr_disp (Z := Z) (sbo := sbo) (um := um) hA hK hKv hc hk P hR (msgLen info buf) r1.slot blocking is_call can_donate fp buf e
    hlen hregs hL hl sfp ci ssl caps buffer onCore sb sc sd
  rw [decode_invocation_vcpu_eq] at hD
  obtain ⟨⟨r3, s2, a2⟩, hd, hpost⟩ := spec_ex hD
  rw [hd, bind_tc_ok]
  obtain ⟨res, hres⟩ := hinvTail_total (st := st) t is_call r3 s2 a2
  dsimp only
  rw [hres]
  exact (WP.spec_ok _).2 ⟨r3, s2, a2, rfl, hres, hpost⟩

set_option maxHeartbeats 1000000 in
/-- **WriteVMCB from the syscall entry, both backends** (module docstring; premises as `wrmsr_disp`):
`handle_invocation`'s result is `hinvTail` of a decode result satisfying `wrvmcb_disp`'s post. -/
theorem wrvmcb_hinv (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S} (is_call blocking can_donate fp : Bool) (cptr : U64)
    {t : U64} (ht : sched.cur_thread st s = ok t) {info : msginfo.MessageInfo}
    (hinfo : msg.msg_info st s t = ok info) (hlbl : info.label = fl4_abi.label.X86VCPUWriteVMCB)
    {r1 : cspace.Resolved} (hlk : cspace.lookup_slot st s t cptr = ok (.Ok r1)) {v : U64}
    (hcap : obj.Slot.cap st r1.slot s = ok (.Vcpu v)) {buf : U64}
    (hbuf : msg.lookup_ipc_buffer st s false t = ok buf) {e : Aeneas.Std.Array obj.Slot 3#usize}
    (hex : ipc.lookup_extra_caps st s t buf info = ok (.Ok e)) (hlen : ¬ msgLen info buf < 2#u64)
    (P : ReplyPl st v s) {σ : State Z} (hR : VRelAt (memW st s) σ v.bv) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : (msgLen info buf).val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeVmcb) (sfp : Bool) (ci : CapRef) (ssl : CslotPtr)
    (caps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (onCore : ObjRef → Bool) (sb sc sd : Bool) :
    syscall.handle_invocation st ar s a is_call blocking can_donate fp cptr ⦃ res =>
      ∃ (r3 : core.result.Result Unit error.Exc) (s2 : S) (a2 : A),
        vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteVMCB (msgLen info buf) v is_call buf e = ok (r3, s2, a2) ∧
        hinvTail st t is_call r3 s2 a2 = ok res ∧
        ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ (f : U64) (val : Word),
            (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ =
              ({(.ok (.vcpu (.writeVmcb v.bv f.bv val)), σ)}, False) ∧ r3 = .Ok () ∧
            ∀ x ∈ ((fl4PerformInvocationV (Z := Z) onCore sb sc sd (.vcpu (.writeVmcb v.bv f.bv val))).run σ).1,
              (∃ rr, x.1 = .ok rr) ∧ VRelAt (memW st s2) x.2 v.bv) ∨
          (∃ e e', (fl4DecodeInvocationV (Z := Z) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ = ({(.error e', σ)}, False) ∧
            SysErrRel e e' ∧ r3 = .Err e ∧ s2 = s1 ∧ VRelAt (memW st s1) σ v.bv)) ⦄ := by
  rw [handle_invocation_vcpu_eq (ar := ar) s a is_call blocking can_donate fp cptr ht hinfo hlk hcap hbuf hex, hlbl]
  have hD := wrvmcb_disp (Z := Z) (sbo := sbo) (um := um) hA hK hKv hc hk P hR (msgLen info buf) r1.slot blocking is_call can_donate fp buf e
    hlen hregs hL hl sfp ci ssl caps buffer onCore sb sc sd
  rw [decode_invocation_vcpu_eq] at hD
  obtain ⟨⟨r3, s2, a2⟩, hd, hpost⟩ := spec_ex hD
  rw [hd, bind_tc_ok]
  obtain ⟨res, hres⟩ := hinvTail_total (st := st) t is_call r3 s2 a2
  dsimp only
  rw [hres]
  exact (WP.spec_ok _).2 ⟨r3, s2, a2, rfl, hres, hpost⟩

end

end
end Fl4Proofs.P3.VirtDispVcpu

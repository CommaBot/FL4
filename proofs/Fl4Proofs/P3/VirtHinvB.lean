/-
P3x for virtualization (line virt, gen 22, item 2): **the caller's IPC-buffer fact `hB` of VirtHinvV from the
relation facts the joint relation carries** (gen 21's [J] `hB` narrowed to state facts).

* **Finding**: `hB` (`msg.lookup_ipc_buffer st s true t ⦃ P1.BufOK U ⦄`) does **not** follow from the hypotheses of
  `wrmsr_hinvJ` / `wrvmcb_hinvJ` (`JKern`, `JVLay V th U`, `JVm`): none of them relates the current TCB's buffer slot
  or its spec object to `U`. Counter-model shape: `U = ∅` satisfies every `U`-clause of `JVLay` (`ua`, `usl`, `ut`,
  `uv` are all `∀ b ∈ U`), while `BufOK ∅ w` is false for every nonzero `w`; a thread whose buffer slot holds a
  writable non-device frame cap with a valid buffer address gets `w ≠ 0` from FL4's `lookup_ipc_buffer`. So the
  missing facts are: the state relation (`StateRel`, `SlotsValid`: the buffer slot's cap is the spec TCB's
  `tcbIpcframe`), the current TCB's spec object `x`, `IpcBufCapOK σ` (the spec buffer frame is a user frame and the
  buffer 1 KiB-aligned), the buffer-address word relation (`BufWordRel`'s `(mem (Endp.tIpcBufA t)).bv = x.tcbIpcBuffer`)
  and that `U` contains `x`'s receive-buffer words (`RcvBufW x`). `JAtZ` carries all of them (`xtop.rel`, `bok`,
  `buf`, and `U = BufU Z σ` by `JAtZ.jvLay`), which is how `JAtZ.bufOK` (BufAtJ) proves it; mmuAD's `JAtZV3` has the
  same JAtZ-shaped base. Without `JAtZV3` they cannot be produced from this line's bundles.
* **`bufOK_of_rel`**: BufAtJ's `JAtZ.bufOK` with `JAtZ` replaced by exactly those facts (any `U ⊇ RcvBufW x`).
* `hB_of_cur`: the same for the current thread (`cur_thread = curW`, `JKern.curT`).
* **`wrmsr_hinvJR`**, **`wrvmcb_hinvJR`**: VirtHinvV's `wrmsr_hinvJ` / `wrvmcb_hinvJ` with **`hB` [J] replaced by
  these state facts** (no [J] premise left on the buffer). They are not false on reachable states: at a `JAtZ`-shaped
  state they are fields of the relation with `U = BufU Z σ`, and `BufU`'s words are user-frame words, apart from
  every VCPU (`JVLay.uv`, gen 21's justification).

Other premises unchanged (`CapAgree` [P], `CapKeepStall` [P], `VirtCodeAgree` [P], `VirtCodeKeepStall` [P]). New file
only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtHinvV
import Fl4Proofs.P3.BufAtJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtHinvB
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanSvm
open Fl4Proofs.P3.VirtVcpuRel Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtVmcbStore Fl4Proofs.P3.VirtReplyKeep Fl4Proofs.P3.VirtVmcbDec
open Fl4Proofs.P3.VirtVmcbTail Fl4Proofs.P3.VirtMsrE2E Fl4Proofs.P3.VirtVmcbE2E Fl4Proofs.P3.VirtArgsSpec
open Fl4Proofs.P3.VirtWrSys Fl4Proofs.P3.VirtWrVmcbVmx Fl4Proofs.P3.VirtMsrDec Fl4Proofs.P3.VirtDispVcpu
open Fl4Proofs.P3.VirtVKeep Fl4Proofs.P3.VirtHinvV

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`JAtZ.bufOK` from the relation facts** (module docstring). -/
theorem bufOK_of_rel {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} (hR : StateRel th (L.mem s) σ)
    (hV : SlotsValid th (L.mem s)) {t : U64} (ht : th t = some .tcb) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (hok : Endp.IpcBufCapOK σ) (hws : (L.mem s (Endp.tIpcBufA t)).bv = x.tcbIpcBuffer)
    {U : Set U64} (hU : ∀ b, RcvBufW x b → b ∈ U) :
    msg.lookup_ipc_buffer st s true t ⦃ P1.BufOK U ⦄ := by
  refine WP.spec_mono (Endp.lookup_buf_full s σ hR hV ht hk hok true) ?_
  rintro w ⟨h0, hp⟩ hw0 i hi
  cases hb : Endp.ipcBufOf true x with
  | none => exact absurd (h0.2 hb) hw0
  | some p' =>
    have e := hp hws p' hb
    subst e
    exact hU _ ⟨_, hb, i, hi, rfl⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {AI : Type} {arI : machine.Arch AI}
variable {H : P1.Heap} {Cs D : Set U64} {th : TypedHeap} {σ : Fl4Spec.State Unit} {V U : Set U64}

/-- `bufOK_of_rel` for the current thread (`cur_thread` returns `curW`, a TCB by `JKern.curT`). -/
theorem hB_of_cur {s : S} (Kn : JKern (L := L) arI H Cs D th s σ) {t : U64} (ht : sched.cur_thread st s = ok t)
    (hRl : StateRel th (L.mem s) σ) (hSl : SlotsValid th (L.mem s)) (hok : Endp.IpcBufCapOK σ)
    {x : Fl4Spec.Tcb} (hx : σ.kheap (L.curW s).bv = some (.tcb x))
    (hws : (L.mem s (Endp.tIpcBufA (L.curW s))).bv = x.tcbIpcBuffer) (hU : ∀ b, RcvBufW x b → b ∈ U) :
    msg.lookup_ipc_buffer st s true t ⦃ P1.BufOK U ⦄ := by
  have e : t = L.curW s := by
    rw [P1.cur_thread_ok] at ht; exact (eq_of_ok_eq ht).symm
  subst e
  exact bufOK_of_rel hRl hSl Kn.curT hx hok hws hU

set_option maxHeartbeats 1000000 in
/-- **`wrmsr_hinvJ` with `hB` from the relation facts** (module docstring). -/
theorem wrmsr_hinvJR (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S}
    (Kn : JKern (L := L) arI H Cs D th s σ) (Ly : JVLay V th U) (Jv : JVm (L := L) V H s σ) {v : U64} (hvV : v ∈ V)
    (is_call blocking can_donate fp : Bool) (cptr : U64)
    {t : U64} (ht : sched.cur_thread st s = ok t) {info : msginfo.MessageInfo}
    (hinfo : msg.msg_info st s t = ok info) (hlbl : info.label = fl4_abi.label.X86VCPUWriteMSR)
    {r1 : cspace.Resolved} (hlk : cspace.lookup_slot st s t cptr = ok (.Ok r1))
    (hcap : obj.Slot.cap st r1.slot s = ok (.Vcpu v)) {buf : U64}
    (hbuf : msg.lookup_ipc_buffer st s false t = ok buf) {e : Aeneas.Std.Array obj.Slot 3#usize}
    (hex : ipc.lookup_extra_caps st s t buf info = ok (.Ok e)) (hlen : ¬ msgLen info buf < 2#u64)
    (hR : VRelAt (memW st s) σ v.bv) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : (msgLen info buf).val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeMsr) (sfp : Bool) (ci : CapRef) (ssl : CslotPtr)
    (caps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (onCore : ObjRef → Bool) (sb sc sd : Bool)
    (hRl : StateRel th (L.mem s) σ) (hSl : SlotsValid th (L.mem s)) (hok : Endp.IpcBufCapOK σ)
    {x : Fl4Spec.Tcb} (hx : σ.kheap (L.curW s).bv = some (.tcb x))
    (hws : (L.mem s (Endp.tIpcBufA (L.curW s))).bv = x.tcbIpcBuffer) (hU : ∀ b, RcvBufW x b → b ∈ U) :
    syscall.handle_invocation st ar s a is_call blocking can_donate fp cptr ⦃ res =>
      (∃ (r3 : core.result.Result Unit error.Exc) (s2 : S) (a2 : A),
        vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteMSR (msgLen info buf) v is_call buf e = ok (r3, s2, a2) ∧
        (r3 = .Ok () → res = (.Ok (), s2, a2))) ∧
      ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ f value : U64,
            (fl4DecodeInvocationV (Z := Unit) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ =
              ({(.ok (.vcpu (.writeMsr v.bv f.bv value.bv)), σ)}, False) ∧ res.1 = .Ok () ∧
            ∀ x ∈ ((fl4PerformInvocationV (Z := Unit) onCore sb sc sd (.vcpu (.writeMsr v.bv f.bv value.bv))).run σ).1,
              (∃ rr, x.1 = .ok rr) ∧ VRelAt (memW st res.2.1) x.2 v.bv) ∨
          (∃ e e', (fl4DecodeInvocationV (Z := Unit) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ = ({(.error e', σ)}, False) ∧
            SysErrRel e e' ∧ VRelAt (memW st res.2.1) σ v.bv)) ⦄ :=
  wrmsr_hinvJ hA hK hKv hc hk Kn Ly Jv hvV is_call blocking can_donate fp cptr ht hinfo hlbl hlk hcap hbuf hex
    hlen hR hregs hL hl sfp ci ssl caps buffer onCore sb sc sd (hB_of_cur Kn ht hRl hSl hok hx hws hU)

set_option maxHeartbeats 1000000 in
/-- **`wrvmcb_hinvJ` with `hB` from the relation facts** (module docstring). -/
theorem wrvmcb_hinvJR (hA : P0.ArchTotal ar) (hK : CapKeepStall ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S}
    (Kn : JKern (L := L) arI H Cs D th s σ) (Ly : JVLay V th U) (Jv : JVm (L := L) V H s σ) {v : U64} (hvV : v ∈ V)
    (is_call blocking can_donate fp : Bool) (cptr : U64)
    {t : U64} (ht : sched.cur_thread st s = ok t) {info : msginfo.MessageInfo}
    (hinfo : msg.msg_info st s t = ok info) (hlbl : info.label = fl4_abi.label.X86VCPUWriteVMCB)
    {r1 : cspace.Resolved} (hlk : cspace.lookup_slot st s t cptr = ok (.Ok r1))
    (hcap : obj.Slot.cap st r1.slot s = ok (.Vcpu v)) {buf : U64}
    (hbuf : msg.lookup_ipc_buffer st s false t = ok buf) {e : Aeneas.Std.Array obj.Slot 3#usize}
    (hex : ipc.lookup_extra_caps st s t buf info = ok (.Ok e)) (hlen : ¬ msgLen info buf < 2#u64)
    (hR : VRelAt (memW st s) σ v.bv) {regs : Register → Word}
    (hregs : ∀ r, (L.mem s (Endp.regA (L.mem s (curA st s)) (Endp.regIdx r))).bv = regs r)
    {sbo : Option ObjRef} {um : Word → Word8} {len : Nat} (hL : (msgLen info buf).val = len) {label : Data}
    (hl : vcpuLabelOf label = some .writeVmcb) (sfp : Bool) (ci : CapRef) (ssl : CslotPtr)
    (caps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (onCore : ObjRef → Bool) (sb sc sd : Bool)
    (hRl : StateRel th (L.mem s) σ) (hSl : SlotsValid th (L.mem s)) (hok : Endp.IpcBufCapOK σ)
    {x : Fl4Spec.Tcb} (hx : σ.kheap (L.curW s).bv = some (.tcb x))
    (hws : (L.mem s (Endp.tIpcBufA (L.curW s))).bv = x.tcbIpcBuffer) (hU : ∀ b, RcvBufW x b → b ∈ U) :
    syscall.handle_invocation st ar s a is_call blocking can_donate fp cptr ⦃ res =>
      (∃ (r3 : core.result.Result Unit error.Exc) (s2 : S) (a2 : A),
        vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteVMCB (msgLen info buf) v is_call buf e = ok (r3, s2, a2) ∧
        (r3 = .Ok () → res = (.Ok (), s2, a2))) ∧
      ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        ((∃ (f : U64) (val : Word),
            (fl4DecodeInvocationV (Z := Unit) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ =
              ({(.ok (.vcpu (.writeVmcb v.bv f.bv val)), σ)}, False) ∧ res.1 = .Ok () ∧
            ∀ x ∈ ((fl4PerformInvocationV (Z := Unit) onCore sb sc sd (.vcpu (.writeVmcb v.bv f.bv val))).run σ).1,
              (∃ rr, x.1 = .ok rr) ∧ VRelAt (memW st res.2.1) x.2 v.bv) ∨
          (∃ e e', (fl4DecodeInvocationV (Z := Unit) sfp label (Endp.specMrs regs sbo um len) ci ssl
                (.archObjectCap (.vcpuCap v.bv)) caps buffer).run σ = ({(.error e', σ)}, False) ∧
            SysErrRel e e' ∧ VRelAt (memW st res.2.1) σ v.bv)) ⦄ :=
  wrvmcb_hinvJ hA hK hKv hc hk Kn Ly Jv hvV is_call blocking can_donate fp cptr ht hinfo hlbl hlk hcap hbuf hex
    hlen hR hregs hL hl sfp ci ssl caps buffer onCore sb sc sd (hB_of_cur Kn ht hRl hSl hok hx hws hU)

end

end
end Fl4Proofs.P3.VirtHinvB

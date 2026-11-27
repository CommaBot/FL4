/-
P3 (line mmuAD, gen 35): **X86VCPUSetTCB end to end at `JAtZV3`**: the extracted `vcpu.decode` at label
`X86VCPUSetTCB` paired with the extended spec's `decodeVcpuInvocation` and FL4's perform
`performVcpuInvocationF (.setTcb v t)` = `associateVcpuTcbF v t` (Fl4Spec/Ext/VirtKernelF), with gen 34's
`JAtZV3.setTcbCoreF2` (no [J]) as the binding core.

* Spec side: `zv_label_stcb` (`vcpuLabelOf 73 = some .setTcb`), `zv_stcb_bv`, `zv_decode_stcb_nil` (no extra cap:
  `truncatedMessage`), `zv_decode_stcb_thr` (a thread cap first: `.setTcb v t`), `zv_decode_stcb_ill` (any other
  cap first: `illegalOperation`), `zv_perform_stcbF`.
* `StcbCaps b c ec`: how FL4's first extra-cap slot (null flag `b`, cap `c`) and the spec's extra caps `ec` agree
  (none ↔ `[]`; a thread cap ↔ the spec's `threadCap` of the same pointer; any other cap ↔ a non-thread cap) —
  the decode front end's slot/cap correspondence (`hexs`, not proved on this line), taken per spec argument list as
  gen 32's `writeVmcsJ` takes `args`.
* **`JAtZV3.setTcbJ`**: `vcpu.decode … X86VCPUSetTCB len p call buf ex` from `JAtZV3`, `p ∈ V`, the slot of
  `ex[0]` with its null flag and (when not null) its cap given, a thread cap naming a TCB of the typed heap (`hct`):
  the post names FL4's `cur_thread` `ct` and for every agreeing `ec` either an error (FL4 `Err e`, spec decoder
  throws `e'`, `SysErrRel e e'`, store unchanged, `JAtZV3`) or the binding: spec decoder returns `.setTcb p t`,
  `performVcpuInvocationF` has the one outcome `([], σ')`, `JAtZV3` at FL4's state before the caller's
  `set_thread_state ct TS_RESTART` and `σ'`, FL4's final state that call's result (as gen 32's `writeRegsJ`).

Premises: [P] `ZvVirtAgree arI`, `P0.ArchTotal arI`, `ARKeep arI AR` (as `setTcbCoreF2`). Scope: `hsl`/`hb`/`hc`,
`hct`, `StcbCaps`. No [J]; no existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3ReportJ3
import Fl4Proofs.P3.JAtZV3Regs
import Fl4Spec.Ext.VirtKernelF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Fl4Spec Classical

theorem zv_label_stcb : vcpuLabelOf (73 : Data) = some .setTcb := by decide

theorem zv_stcb_bv : fl4_abi.label.X86VCPUSetTCB.bv = (73 : Fl4Spec.Data) := by
  unfold fl4_abi.label.X86VCPUSetTCB; rfl

theorem zv_decode_stcb_nil (args : List Data) (v : ObjRef) :
    decodeVcpuInvocation (Z := Unit) 73 args v [] = NonDetE.throwError .truncatedMessage := by
  simp only [decodeVcpuInvocation, zv_label_stcb]

theorem zv_decode_stcb_thr (args : List Data) (v t : ObjRef) (cp : CslotPtr) (rest : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 73 args v ((.threadCap t, cp) :: rest) = NonDetE.returnOk (.setTcb v t) := by
  simp only [decodeVcpuInvocation, zv_label_stcb]

theorem zv_decode_stcb_ill (args : List Data) (v : ObjRef) {cr : Cap} (h : ∀ t, cr ≠ .threadCap t) (cp : CslotPtr)
    (rest : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 73 args v ((cr, cp) :: rest) = NonDetE.throwError .illegalOperation := by
  simp only [decodeVcpuInvocation, zv_label_stcb]

theorem zv_perform_stcbF {σ σ' : State Unit} {v t : ObjRef}
    (h : associateVcpuTcbF (Z := Unit) v t σ = ({((), σ')}, False)) :
    performVcpuInvocationF (Z := Unit) (.setTcb v t) σ = ({([], σ')}, False) := by
  show (associateVcpuTcbF (Z := Unit) v t >>= fun _ => (pure [] : SMonad Unit (List Data))) σ = _
  rw [Notif.nd_bind_one h]
  rfl

end

/-- **FL4's first extra-cap slot and the spec's extra caps agree** (module docstring). -/
def StcbCaps (b : Bool) (c : capability.Cap) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop :=
  (b = true → ec = []) ∧ (b = false → ∃ cr cp rest, ec = (cr, cp) :: rest ∧
    ((∃ t : U64, c = .Thread t ∧ cr = .threadCap t.bv) ∨ ((∀ t, c ≠ .Thread t) ∧ ∀ t, cr ≠ .threadCap t)))

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 16000000 in
/-- **gen 33's `setTcbCoreF` with the decode's continuation** (the caller's `set_thread_state ct TS_RESTART` and
the `Ok` result; proof copied, only its last step extended). -/
theorem JAtZV3.setTcbCoreK (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hR : ReportJ3All st arI V X AR Z H Cs D) {t v : U64} (ht : Z.th t = some .tcb) (hv : v ∈ V) (ct : U64) :
    (do
      let (s3, a2) ← smp.remote_tcb_stall st arI s a t
      let (s4, a3) ← vcpu.detach st arI s3 a2 t
      let i1 ← vcpu.get st s4 v vcpu.TCB
      let b1 ← obj.Tcb.is_null i1
      let (s5, a4) ← if b1 then ok (s4, a3) else vcpu.detach st arI s4 a3 i1
      let s6 ← vcpu.set st s5 v vcpu.TCB t
      let i2 ← layout.tcb.VCPU
      let i3 ← lift (core.num.U64.wrapping_add t i2)
      let s7 ← st.write s6 i3 v
      let s8 ← sched.set_thread_state st s7 ct sched.TS_RESTART
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s8, a4)) ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64)
        (Lst' : U64 → List U64) (s7 : S), r.1 = .Ok () ∧
        Fl4Spec.associateVcpuTcbF (Z := Unit) v.bv t.bv σ = ({((), σ')}, False) ∧
        JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D s7 r.2.2 σ' ∧
        sched.set_thread_state st s7 ct sched.TS_RESTART = ok r.2.1 ⦄ := by
  have Jz := J.z2.zv
  have B := Jz.base
  have P := B.jwPl Jz.vm
  have hS := B.xtop.fin.1.1.1
  have hv0 : v ≠ 0#u64 := Jz.extv.nz v hv
  have JWt : JW V Z.th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  refine WP.spec_bind (Sched.remote_tcb_stall_id (ar := arI) a hS (B.thT t ht)) ?_
  rintro ⟨s3, a2⟩ e
  try simp only [uncurry_apply_pair]
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  subst s3
  subst a2
  refine WP.spec_bind (J.detachF hK hR ht) ?_
  rintro ⟨s4, a3⟩ ⟨σ1, Ac1, Lst1, hD1, J1, DM1⟩
  try simp only [uncurry_apply_pair]
  obtain ⟨vs1, hk1, hb1⟩ := J1.z2.vb v hv
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s4 _) fun i1 ei1 => ?_
  have ei1' : i1 = L.mem s4 (vTcbA v) := ei1
  refine WP.spec_bind (P1.obj.Tcb.is_null.spec i1) fun b1 eb1 => ?_
  refine WP.spec_bind (Pₘ := fun r => ∃ (σ2 : Fl4Spec.State Unit) (Ac2 : Set U64) (Lst2 : U64 → List U64),
      Fl4Spec.associateVcpuTcbF (Z := Unit) v.bv t.bv σ =
        Fl4Spec.vcpuUpdate (Z := Unit) v.bv (fun x : Fl4Spec.VcpuState => { x with tcb := some t.bv }) σ2 ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac2 Lst2 D r.1 r.2 σ2 ∧ L.mem r.1 (tVcpuA t) = 0#u64 ∧
      L.mem r.1 (vTcbA v) = 0#u64) ?_ ?_
  · split
    · rename_i hb
      have hi0 : i1 = 0#u64 := by rw [eb1] at hb; simpa using hb
      have hm0 : L.mem s4 (vTcbA v) = 0#u64 := ei1'.symm.trans hi0
      have htc : Fl4Spec.VcpuState.tcb vs1 = none := by
        rcases hb1 with ⟨h, -⟩ | ⟨o, ho0, -, hm⟩
        · exact h
        · exact absurd (hm.symm.trans hm0) ho0
      refine (WP.spec_ok _).2 ⟨σ1, Ac1, Lst1, ?_, J1, DM1.w0, hm0⟩
      unfold Fl4Spec.associateVcpuTcbF
      rw [Notif.nd_bind_one hD1, Notif.nd_bind_one (zv_getVcpu_eq hk1), htc]
      try exact Notif.nd_pure_bind' _ _ _
    · rename_i hb
      have hi0 : i1 ≠ 0#u64 := by rw [eb1] at hb; simpa using hb
      obtain ⟨o, ho0, htc, hm⟩ : ∃ o : U64, o ≠ 0#u64 ∧ Fl4Spec.VcpuState.tcb vs1 = some o.bv ∧
          L.mem s4 (vTcbA v) = o := by
        rcases hb1 with ⟨-, h⟩ | h
        · exact absurd (ei1'.trans h) hi0
        · exact h
      have eio : o = i1 := (ei1'.trans hm).symm
      rw [eio] at ho0 htc hm
      obtain ⟨hto, hov⟩ := (J1.z2.zv.extv.back v hv).resolve_left (by rw [hm]; exact ho0)
      rw [hm] at hto hov
      have hne : t ≠ i1 := fun e => hv0 (by rw [← hov, ← e]; exact DM1.w0)
      refine WP.spec_mono (J1.detachF hK hR hto) ?_
      rintro ⟨s5, a4⟩ ⟨σ2, Ac2, Lst2, hD2, J2, DM2⟩
      refine ⟨σ2, Ac2, Lst2, ?_, J2, ?_, ?_⟩
      · unfold Fl4Spec.associateVcpuTcbF
        rw [Notif.nd_bind_one hD1, Notif.nd_bind_one (zv_getVcpu_eq hk1), htc]
        exact Notif.nd_bind_one hD2 _
      · rw [DM2.keep _ JWt (fun e => hne (tVcpuA_inj e)) (fun w hw _ => P.vb t ht w hw)]
        exact DM1.w0
      · exact DM2.b0 v hv hov
  rintro ⟨s5, a4⟩ ⟨σ2, Ac2, Lst2, hA2, J2, hw0, hb0⟩
  try simp only [uncurry_apply_pair]
  obtain ⟨vs2, hk2, -⟩ := J2.z2.vb v hv
  simp only [vcpu.set, lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec s5 _ _) fun s6 e6 => ?_
  subst e6
  step as ⟨o2, ho2⟩
  subst ho2
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s7 e7 => ?_
  obtain ⟨s8, h8, -⟩ := P1.spec_ex_fd
    (P0.sched.set_thread_state.p0 st s7 ct sched.TS_RESTART (P1.LawfulStore.total (st := st)))
  rw [h8, bind_ok, WP.spec_ok]
  refine ⟨_, Ac2, Lst2, s7, rfl, by rw [hA2]; exact zv_vcpuUpdate_eq hk2 _, ?_, h8⟩
  rw [e7]
  exact J2.bind ht hv hw0 hb0 hk2 { vs2 with tcb := some t.bv } rfl

set_option maxHeartbeats 16000000 in
/-- **X86VCPUSetTCB at `JAtZV3`, paired with the spec's decode and FL4's perform** (module docstring). -/
theorem JAtZV3.setTcbJ (hA : P0.ArchTotal arI) (hVA : ZvVirtAgree arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR) {p : U64} (hp : p ∈ V)
    (len : U64) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hb : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUSetTCB len p call buf ex ⦃ r => ∃ ct : U64,
      sched.cur_thread st s = ok ct ∧
      ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), StcbCaps b c ec →
        (∃ e e', r.1 = .Err e ∧ SysErrRel e e' ∧
          Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUSetTCB.bv args p.bv ec =
            Fl4Spec.NonDetE.throwError e' ∧
          r.2.1 = s ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s r.2.2 σ) ∨
        (∃ (t : U64) (s7 : S) (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64), r.1 = .Ok () ∧
          Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUSetTCB.bv args p.bv ec =
            Fl4Spec.NonDetE.returnOk (.setTcb p.bv t.bv) ∧
          Fl4Spec.performVcpuInvocationF (Z := Unit) (.setTcb p.bv t.bv) σ = ({([], σ')}, False) ∧
          JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D s7 r.2.2 σ' ∧
          sched.set_thread_state st s7 ct sched.TS_RESTART = ok r.2.1) ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct', -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct', bind_ok]
  obtain ⟨i, hi, -⟩ := P1.spec_ex_fd (hA.virtualization_spec a1)
  rw [hi, bind_ok]
  have hF : ∃ f, (if len > 0#u64 then msg.syscall_arg st s ct buf 0#u64 else ok 0#u64) = ok f := by
    split
    · obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨f, hf⟩
    · exact ⟨_, rfl⟩
  have hX : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  obtain ⟨f, hf⟩ := hF
  obtain ⟨x, hx⟩ := hX
  rw [hf, bind_ok, hx, bind_ok, if_pos trivial, hsl, bind_ok, hb, bind_ok]
  cases b with
  | true =>
    rw [if_pos rfl]
    simp only [error.truncated, bind_ok, WP.spec_ok]
    refine ⟨ct, rfl, fun args ec hE => Or.inl ⟨_, .truncatedMessage, rfl, trivial, ?_, by first | rfl | trivial, J1⟩⟩
    rw [hE.1 rfl, zv_stcb_bv, zv_decode_stcb_nil]
  | false =>
    rw [if_neg Bool.false_ne_true, hc rfl, bind_ok]
    -- an illegal cap: FL4 and the spec both refuse
    have ILL : (∀ t, c ≠ .Thread t) →
        (do
          let r ← error.illegal Unit
          ok (r, s, a1)) ⦃ r => ∃ ct' : U64, (ok ct : Result U64) = ok ct' ∧
          ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), StcbCaps false c ec →
            (∃ e e', r.1 = .Err e ∧ SysErrRel e e' ∧
              Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUSetTCB.bv args p.bv ec =
                Fl4Spec.NonDetE.throwError e' ∧
              r.2.1 = s ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s r.2.2 σ) ∨
            (∃ (t : U64) (s7 : S) (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
              r.1 = .Ok () ∧
              Fl4Spec.decodeVcpuInvocation (Z := Unit) fl4_abi.label.X86VCPUSetTCB.bv args p.bv ec =
                Fl4Spec.NonDetE.returnOk (.setTcb p.bv t.bv) ∧
              Fl4Spec.performVcpuInvocationF (Z := Unit) (.setTcb p.bv t.bv) σ = ({([], σ')}, False) ∧
              JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D s7 r.2.2 σ' ∧
              sched.set_thread_state st s7 ct' sched.TS_RESTART = ok r.2.1) ⦄ := by
      intro hnt
      simp only [error.illegal, bind_ok, WP.spec_ok]
      refine ⟨ct, rfl, fun args ec hE => Or.inl ⟨_, .illegalOperation, rfl, trivial, ?_, by first | rfl | trivial, J1⟩⟩
      obtain ⟨cr, cp, rest, hec, hrel⟩ := hE.2 rfl
      rcases hrel with ⟨t, e, -⟩ | ⟨-, hcr⟩
      · exact absurd e (hnt t)
      · rw [hec, zv_stcb_bv, zv_decode_stcb_ill args p.bv hcr]
    cases c
    case Thread ptr =>
      have hth := hct ptr rfl
      dsimp only
      refine WP.spec_mono (J1.setTcbCoreK hK (v3_reportJ3All hA hVA V X AR Z H Cs D) hth hp ct) ?_
      rintro r ⟨σ', Ac', Lst', s7, hr1, hD, J7, h8⟩
      refine ⟨ct, rfl, fun args ec hE => Or.inr ⟨ptr, s7, σ', Ac', Lst', hr1, ?_, zv_perform_stcbF hD, J7, h8⟩⟩
      obtain ⟨cr, cp, rest, hec, hrel⟩ := hE.2 rfl
      rcases hrel with ⟨t, e, hcr⟩ | ⟨hnt, -⟩
      · cases e
        rw [hec, hcr, zv_stcb_bv, zv_decode_stcb_thr]
      · exact absurd rfl (hnt ptr)
    all_goals (dsimp only; exact ILL (fun t e => by cases e))

end

end

end Fl4Proofs.P3

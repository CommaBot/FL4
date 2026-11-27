/-
P3 (line mmuAD, gen 34): **`ReportJ3`'s full-state, no-pending branch** (`JAtZV3.repBrC2` with a VCPU: `report_loop2`, `repTail` with `report_loop3`; `JAtZV3.repBrC1` without: zeros, `finish_notification`).

No named premise beyond [P] `ZvVirtAgree arI` (gen 32). No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3RepBr0
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **Branch: no pending exit, full-state caller, with a VCPU** (module docstring). -/
theorem JAtZV3.repBrC2 (hVA : ZvVirtAgree arI) (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {t : U64} (htT : t ∈ Z.T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrs : x.tcbState = .runningVM) {b : U64} (hb : JBufR Z.B b (Endp.ipcBufOf true x))
    (hal : ∀ ms : List Fl4Spec.Word, ∀ p, Endp.ipcBufOf true x = some p → ∀ q ∈ Endp.mrPairs ms,
      (Endp.bufAddr p q.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p q.1) σ)
    {v : U64} (hv0 : v ≠ 0#u64) (hvV : v ∈ V) {vs : Fl4Spec.VcpuState}
    (hkv : σ.kheap v.bv = some (.archObj (.vcpu vs))) (hvt' : v.bv ≠ t.bv)
    (hTV : Fl4Spec.tcbVcpuOf σ t.bv = some v.bv)
    {pending full : Bool} (hpend : pending = vs.exit.pending) (hp : pending = false) (hf : full = true)
    (hfull : full = Fl4Proofs.P3.repFull x) (badge : U64) :
    (do
      let saved ←
        if v != 0#u64
        then
          do
          let i ← vcpu.get st s v vcpu.VALID
          ok (i != 0#u64)
        else ok false
      let s1 ← vcpu.report_loop2 st s t v pending b saved 0#u64
      if v = 0#u64
      then
        vcpu.finish_notification st arI s1 a t b
          badge false
      else
        let i ← vcpu.get st s1 v vcpu.VALID
        if i = 0#u64
        then
          let i1 ← arI.virtualization a
          let ip ←
            if i1 = 2#u64
            then do
                 let i2 ← vcpu.svm.RIP
                 vcpu.get st s1 v i2
            else vcpu.read_vmcs st s1 v vcpu.vmx.GUEST_RIP
          let ctl ←
            if i1 = 2#u64
            then
              do
              let i2 ← vcpu.get st s1 v vcpu.svm.INTERCEPT_EXC
              i2 >>> 32#i32
            else
              vcpu.read_vmcs st s1 v
                vcpu.vmx.CONTROL_PRIMARY_PROCESSOR_CONTROLS
          let intr ←
            if i1 = 2#u64
            then vcpu.get st s1 v vcpu.svm.EVENT_INJ
            else
              vcpu.read_vmcs st s1 v
                vcpu.vmx.CONTROL_ENTRY_INTERRUPTION_INFO
          let (_, s2) ← msg.set_mr st s1 t b 0#u64 ip
          let (_, s3) ← msg.set_mr st s2 t b 1#u64 ctl
          let (_, s4) ← msg.set_mr st s3 t b 2#u64 intr
          let s5 ← vcpu.report_loop3 st s4 t v b 0#u64
          let i2 ← vcpu.get st s5 v vcpu.VALID
          let s6 ←
            if i2 = 0#u64
            then
              do
              let i3 ← arI.virtualization a
              let flags ←
                if i3 = 2#u64
                then
                  do
                  let i4 ← vcpu.svm.RFLAGS
                  vcpu.get st s5 v i4
                else vcpu.read_vmcs st s5 v vcpu.vmx.GUEST_RFLAGS
              let int ←
                if i3 = 2#u64
                then vcpu.get st s5 v vcpu.svm.INT_STATE
                else
                  vcpu.read_vmcs st s5 v
                    vcpu.vmx.GUEST_INTERRUPTABILITY
              let cr3 ←
                if i3 = 2#u64
                then
                  do
                  let i4 ← vcpu.svm.CR3
                  vcpu.get st s5 v i4
                else ok 0#u64
              let cr2 ←
                if i3 = 2#u64
                then
                  do
                  let i4 ← vcpu.svm.CR2
                  vcpu.get st s5 v i4
                else vcpu.get st s5 v vcpu.CR2
              let (_, s7) ← msg.set_mr st s5 t b 7#u64 flags
              let (_, s8) ← msg.set_mr st s7 t b 8#u64 int
              let (_, s9) ← msg.set_mr st s8 t b 9#u64 cr3
              let (_, s10) ← msg.set_mr st s9 t b 29#u64 cr2
              ok s10
            else ok s5
          if full
          then
            let i3 ← msg.syscall_arg st s6 t b 2#u64
            let descriptor ← lift (i3 &&& 4294967295#u64)
            let (_, s7) ← msg.set_mr st s6 t b 2#u64 descriptor
            if pending
            then
              let s8 ← vcpu.set st s7 v vcpu.PENDING 0#u64
              let s9 ←
                obj.Tcb.set_reg st t s8 layout.reg.MSG_INFO 1#u64
              let s10 ←
                obj.Tcb.set_reg st t s9 layout.reg.BADGE 0#u64
              let ip1 ← obj.Tcb.reg st t s10 layout.reg.NEXT_IP
              let s11 ←
                obj.Tcb.set_reg st t s10 layout.reg.FAULT_IP ip1
              sched.set_thread_state st s11 t sched.TS_RUNNING
            else
              let vectoring ←
                if saved
                then
                  do
                  let i4 ← 27#u64 * 8#u64
                  let i5 ← vcpu.EXIT + i4
                  let i6 ← vcpu.get st s7 v i5
                  let i7 ← 1#u64 <<< 31#i32
                  let i8 ← lift (i6 &&& i7)
                  ok (i8 != 0#u64)
                else ok false
              vcpu.finish_notification st arI s7 a t
                b badge vectoring
          else
            let s7 ← vcpu.set st s6 v vcpu.PENDING 0#u64
            let s8 ←
              obj.Tcb.set_reg st t s7 layout.reg.MSG_INFO 1#u64
            let s9 ←
              obj.Tcb.set_reg st t s8 layout.reg.BADGE 0#u64
            let ip1 ← obj.Tcb.reg st t s9 layout.reg.NEXT_IP
            let s10 ←
              obj.Tcb.set_reg st t s9 layout.reg.FAULT_IP ip1
            sched.set_thread_state st s10 t sched.TS_RUNNING
        else
          let s2 ←
            if i = 0#u64
            then
              do
              let i1 ← arI.virtualization a
              let flags ←
                if i1 = 2#u64
                then
                  do
                  let i2 ← vcpu.svm.RFLAGS
                  vcpu.get st s1 v i2
                else vcpu.read_vmcs st s1 v vcpu.vmx.GUEST_RFLAGS
              let int ←
                if i1 = 2#u64
                then vcpu.get st s1 v vcpu.svm.INT_STATE
                else
                  vcpu.read_vmcs st s1 v
                    vcpu.vmx.GUEST_INTERRUPTABILITY
              let cr3 ←
                if i1 = 2#u64
                then
                  do
                  let i2 ← vcpu.svm.CR3
                  vcpu.get st s1 v i2
                else ok 0#u64
              let cr2 ←
                if i1 = 2#u64
                then
                  do
                  let i2 ← vcpu.svm.CR2
                  vcpu.get st s1 v i2
                else vcpu.get st s1 v vcpu.CR2
              let (_, s3) ← msg.set_mr st s1 t b 7#u64 flags
              let (_, s4) ← msg.set_mr st s3 t b 8#u64 int
              let (_, s5) ← msg.set_mr st s4 t b 9#u64 cr3
              let (_, s6) ← msg.set_mr st s5 t b 29#u64 cr2
              ok s6
            else ok s1
          if full
          then
            let i1 ← msg.syscall_arg st s2 t b 2#u64
            let descriptor ← lift (i1 &&& 4294967295#u64)
            let (_, s3) ← msg.set_mr st s2 t b 2#u64 descriptor
            if pending
            then
              let s4 ← vcpu.set st s3 v vcpu.PENDING 0#u64
              let s5 ←
                obj.Tcb.set_reg st t s4 layout.reg.MSG_INFO 1#u64
              let s6 ←
                obj.Tcb.set_reg st t s5 layout.reg.BADGE 0#u64
              let ip ← obj.Tcb.reg st t s6 layout.reg.NEXT_IP
              let s7 ←
                obj.Tcb.set_reg st t s6 layout.reg.FAULT_IP ip
              sched.set_thread_state st s7 t sched.TS_RUNNING
            else
              let vectoring ←
                if saved
                then
                  do
                  let i2 ← 27#u64 * 8#u64
                  let i3 ← vcpu.EXIT + i2
                  let i4 ← vcpu.get st s3 v i3
                  let i5 ← 1#u64 <<< 31#i32
                  let i6 ← lift (i4 &&& i5)
                  ok (i6 != 0#u64)
                else ok false
              vcpu.finish_notification st arI s3 a t
                b badge vectoring
          else
            let s3 ← vcpu.set st s2 v vcpu.PENDING 0#u64
            let s4 ←
              obj.Tcb.set_reg st t s3 layout.reg.MSG_INFO 1#u64
            let s5 ←
              obj.Tcb.set_reg st t s4 layout.reg.BADGE 0#u64
            let ip ← obj.Tcb.reg st t s5 layout.reg.NEXT_IP
            let s6 ←
              obj.Tcb.set_reg st t s5 layout.reg.FAULT_IP ip
            sched.set_thread_state st s6 t sched.TS_RUNNING) ⦃ s' => ∃ (σr : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      Fl4Spec.vmReportF (Z := Unit) t.bv badge.bv σ = ({((), σr)}, False) ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σr ⦄ := by
  subst hp hf
  have hq : ∀ p, Endp.ipcBufOf true x = some p → Endp.ipcBufOf true x = some p := fun _ h => h
  have J0 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ t.bv x (Endp.ipcBufOf true x) []) := by
    rw [jMrSt_nil hk]; exact J
  have hne : (v != 0#u64) = true := by simp [hv0]
  refine WP.spec_bind (Pₘ := fun p => p = vs.exit.valid) (by
    rw [if_pos hne, v3_get_eq, bind_ok, WP.spec_ok]; exact J.rdValid hvV hkv) fun saved hsaved => ?_
  have J0' : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ t.bv x (Endp.ipcBufOf true x)
      ((List.range (0#u64 : U64).val).map (exitMrN (false || saved) vs))) := by
    simpa using J0
  refine WP.spec_bind (JAtZV3.repLoop2 htT hq hb (v := v) (pending := false) (saved := saved) (vs := vs)
    (fun _ => ⟨hvV, hkv, hvt'⟩) 0#u64 (by simp) s J0') fun s1 J1 => ?_
  refine v3_ite_spec (fun h => absurd h hv0) (fun _ => ?_)
  refine WP.spec_mono (J1.repTail hVA htT hq hb hrs hvV hkv hvt' false saved true hsaved (fun _ => rfl) badge
    (fun s4 => vcpu.report_loop3 st s4 t v b 0#u64) (fun s4 J4 => JAtZV3.repLoop3 htT hq hb hvV hkv hvt' _ 0#u64
      (by simp) s4 (by rw [v3_gpr0]; exact J4))) fun s' h' => ?_
  obtain ⟨Lst', J'⟩ := h'
  refine ⟨_, Lst', ?_, J'⟩
  rw [v3_vmReportF_some hk hTV hkv badge.bv (hal _), v3_repR_full x vs badge.bv hpend.symm hfull.symm, hsaved]
  rfl

set_option maxHeartbeats 4000000 in
/-- **Branch: no pending exit, full-state caller, without VCPU** (module docstring). -/
theorem JAtZV3.repBrC1 (hVA : ZvVirtAgree arI) (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ)
    {t : U64} (htT : t ∈ Z.T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrs : x.tcbState = .runningVM) {b : U64} (hb : JBufR Z.B b (Endp.ipcBufOf true x))
    (hal : ∀ ms : List Fl4Spec.Word, ∀ p, Endp.ipcBufOf true x = some p → ∀ q ∈ Endp.mrPairs ms,
      (Endp.bufAddr p q.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p q.1) σ)
    {v : U64} (hv0 : v = 0#u64) (hTV : Fl4Spec.tcbVcpuOf σ t.bv = none)
    {pending full : Bool} (hp : pending = false) (hf : full = true) (hfull : full = Fl4Proofs.P3.repFull x) (badge : U64) :
    (do
      let saved ←
        if v != 0#u64
        then
          do
          let i ← vcpu.get st s v vcpu.VALID
          ok (i != 0#u64)
        else ok false
      let s1 ← vcpu.report_loop2 st s t v pending b saved 0#u64
      if v = 0#u64
      then
        vcpu.finish_notification st arI s1 a t b
          badge false
      else
        let i ← vcpu.get st s1 v vcpu.VALID
        if i = 0#u64
        then
          let i1 ← arI.virtualization a
          let ip ←
            if i1 = 2#u64
            then do
                 let i2 ← vcpu.svm.RIP
                 vcpu.get st s1 v i2
            else vcpu.read_vmcs st s1 v vcpu.vmx.GUEST_RIP
          let ctl ←
            if i1 = 2#u64
            then
              do
              let i2 ← vcpu.get st s1 v vcpu.svm.INTERCEPT_EXC
              i2 >>> 32#i32
            else
              vcpu.read_vmcs st s1 v
                vcpu.vmx.CONTROL_PRIMARY_PROCESSOR_CONTROLS
          let intr ←
            if i1 = 2#u64
            then vcpu.get st s1 v vcpu.svm.EVENT_INJ
            else
              vcpu.read_vmcs st s1 v
                vcpu.vmx.CONTROL_ENTRY_INTERRUPTION_INFO
          let (_, s2) ← msg.set_mr st s1 t b 0#u64 ip
          let (_, s3) ← msg.set_mr st s2 t b 1#u64 ctl
          let (_, s4) ← msg.set_mr st s3 t b 2#u64 intr
          let s5 ← vcpu.report_loop3 st s4 t v b 0#u64
          let i2 ← vcpu.get st s5 v vcpu.VALID
          let s6 ←
            if i2 = 0#u64
            then
              do
              let i3 ← arI.virtualization a
              let flags ←
                if i3 = 2#u64
                then
                  do
                  let i4 ← vcpu.svm.RFLAGS
                  vcpu.get st s5 v i4
                else vcpu.read_vmcs st s5 v vcpu.vmx.GUEST_RFLAGS
              let int ←
                if i3 = 2#u64
                then vcpu.get st s5 v vcpu.svm.INT_STATE
                else
                  vcpu.read_vmcs st s5 v
                    vcpu.vmx.GUEST_INTERRUPTABILITY
              let cr3 ←
                if i3 = 2#u64
                then
                  do
                  let i4 ← vcpu.svm.CR3
                  vcpu.get st s5 v i4
                else ok 0#u64
              let cr2 ←
                if i3 = 2#u64
                then
                  do
                  let i4 ← vcpu.svm.CR2
                  vcpu.get st s5 v i4
                else vcpu.get st s5 v vcpu.CR2
              let (_, s7) ← msg.set_mr st s5 t b 7#u64 flags
              let (_, s8) ← msg.set_mr st s7 t b 8#u64 int
              let (_, s9) ← msg.set_mr st s8 t b 9#u64 cr3
              let (_, s10) ← msg.set_mr st s9 t b 29#u64 cr2
              ok s10
            else ok s5
          if full
          then
            let i3 ← msg.syscall_arg st s6 t b 2#u64
            let descriptor ← lift (i3 &&& 4294967295#u64)
            let (_, s7) ← msg.set_mr st s6 t b 2#u64 descriptor
            if pending
            then
              let s8 ← vcpu.set st s7 v vcpu.PENDING 0#u64
              let s9 ←
                obj.Tcb.set_reg st t s8 layout.reg.MSG_INFO 1#u64
              let s10 ←
                obj.Tcb.set_reg st t s9 layout.reg.BADGE 0#u64
              let ip1 ← obj.Tcb.reg st t s10 layout.reg.NEXT_IP
              let s11 ←
                obj.Tcb.set_reg st t s10 layout.reg.FAULT_IP ip1
              sched.set_thread_state st s11 t sched.TS_RUNNING
            else
              let vectoring ←
                if saved
                then
                  do
                  let i4 ← 27#u64 * 8#u64
                  let i5 ← vcpu.EXIT + i4
                  let i6 ← vcpu.get st s7 v i5
                  let i7 ← 1#u64 <<< 31#i32
                  let i8 ← lift (i6 &&& i7)
                  ok (i8 != 0#u64)
                else ok false
              vcpu.finish_notification st arI s7 a t
                b badge vectoring
          else
            let s7 ← vcpu.set st s6 v vcpu.PENDING 0#u64
            let s8 ←
              obj.Tcb.set_reg st t s7 layout.reg.MSG_INFO 1#u64
            let s9 ←
              obj.Tcb.set_reg st t s8 layout.reg.BADGE 0#u64
            let ip1 ← obj.Tcb.reg st t s9 layout.reg.NEXT_IP
            let s10 ←
              obj.Tcb.set_reg st t s9 layout.reg.FAULT_IP ip1
            sched.set_thread_state st s10 t sched.TS_RUNNING
        else
          let s2 ←
            if i = 0#u64
            then
              do
              let i1 ← arI.virtualization a
              let flags ←
                if i1 = 2#u64
                then
                  do
                  let i2 ← vcpu.svm.RFLAGS
                  vcpu.get st s1 v i2
                else vcpu.read_vmcs st s1 v vcpu.vmx.GUEST_RFLAGS
              let int ←
                if i1 = 2#u64
                then vcpu.get st s1 v vcpu.svm.INT_STATE
                else
                  vcpu.read_vmcs st s1 v
                    vcpu.vmx.GUEST_INTERRUPTABILITY
              let cr3 ←
                if i1 = 2#u64
                then
                  do
                  let i2 ← vcpu.svm.CR3
                  vcpu.get st s1 v i2
                else ok 0#u64
              let cr2 ←
                if i1 = 2#u64
                then
                  do
                  let i2 ← vcpu.svm.CR2
                  vcpu.get st s1 v i2
                else vcpu.get st s1 v vcpu.CR2
              let (_, s3) ← msg.set_mr st s1 t b 7#u64 flags
              let (_, s4) ← msg.set_mr st s3 t b 8#u64 int
              let (_, s5) ← msg.set_mr st s4 t b 9#u64 cr3
              let (_, s6) ← msg.set_mr st s5 t b 29#u64 cr2
              ok s6
            else ok s1
          if full
          then
            let i1 ← msg.syscall_arg st s2 t b 2#u64
            let descriptor ← lift (i1 &&& 4294967295#u64)
            let (_, s3) ← msg.set_mr st s2 t b 2#u64 descriptor
            if pending
            then
              let s4 ← vcpu.set st s3 v vcpu.PENDING 0#u64
              let s5 ←
                obj.Tcb.set_reg st t s4 layout.reg.MSG_INFO 1#u64
              let s6 ←
                obj.Tcb.set_reg st t s5 layout.reg.BADGE 0#u64
              let ip ← obj.Tcb.reg st t s6 layout.reg.NEXT_IP
              let s7 ←
                obj.Tcb.set_reg st t s6 layout.reg.FAULT_IP ip
              sched.set_thread_state st s7 t sched.TS_RUNNING
            else
              let vectoring ←
                if saved
                then
                  do
                  let i2 ← 27#u64 * 8#u64
                  let i3 ← vcpu.EXIT + i2
                  let i4 ← vcpu.get st s3 v i3
                  let i5 ← 1#u64 <<< 31#i32
                  let i6 ← lift (i4 &&& i5)
                  ok (i6 != 0#u64)
                else ok false
              vcpu.finish_notification st arI s3 a t
                b badge vectoring
          else
            let s3 ← vcpu.set st s2 v vcpu.PENDING 0#u64
            let s4 ←
              obj.Tcb.set_reg st t s3 layout.reg.MSG_INFO 1#u64
            let s5 ←
              obj.Tcb.set_reg st t s4 layout.reg.BADGE 0#u64
            let ip ← obj.Tcb.reg st t s5 layout.reg.NEXT_IP
            let s6 ←
              obj.Tcb.set_reg st t s5 layout.reg.FAULT_IP ip
            sched.set_thread_state st s6 t sched.TS_RUNNING) ⦃ s' => ∃ (σr : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      Fl4Spec.vmReportF (Z := Unit) t.bv badge.bv σ = ({((), σr)}, False) ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σr ⦄ := by
  subst hp hf
  have hq : ∀ p, Endp.ipcBufOf true x = some p → Endp.ipcBufOf true x = some p := fun _ h => h
  have J0 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ t.bv x (Endp.ipcBufOf true x) []) := by
    rw [jMrSt_nil hk]; exact J
  refine WP.spec_bind (Pₘ := fun p => p = false) (by
    rw [if_neg (by simp [hv0])]; exact (WP.spec_ok _).2 rfl) fun saved hsaved => ?_
  subst hsaved
  have J0' : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ t.bv x (Endp.ipcBufOf true x)
      ((List.range (0#u64 : U64).val).map (exitMrN (false || false) default))) := by
    simpa using J0
  refine WP.spec_bind (JAtZV3.repLoop2 htT hq hb (v := v) (pending := false) (saved := false) (vs := default)
    (fun h => absurd h (by simp)) 0#u64 (by simp) s J0') fun s1 J1 => ?_
  refine v3_ite_spec (fun _ => ?_) (fun h => absurd hv0 h)
  refine WP.spec_mono (J1.repFinN hVA htT hq hb hrs badge false) fun s' h' => ?_
  obtain ⟨Lst', J'⟩ := h'
  refine ⟨_, Lst', ?_, J'⟩
  rw [v3_vmReportF_none hk hTV badge.bv (hal _), v3_repR_noneFull x badge.bv hfull.symm]
  rfl


end

end

end Fl4Proofs.P3

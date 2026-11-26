/-
P3 (line mmuAD, gen 34): **the branch tail of `vcpu::report` after its first loop, at `JAtZV3`** (toward
`ReportJ3`, gen 33 plan step 6).

* `rpFullF` (MR2 masked to 32 bits when full, FL4 #85), `rpVecOf` (`finish_notification`'s vectoring flag: a saved
  exit whose MR27 has bit 31), `repEnd` (the spec state FL4 ends at: `PENDING` cleared, message info 1, badge 0 on a
  pending exit; `finish_notification`'s words, message info 0 and the badge otherwise).
* **`JAtZV3.repFull`**: the `if full …` block (FL4 text verbatim): the MR2 read-back (`v3_syscall_arg2`, the
  register relation), the mask, then `repFinP` or the vectoring read (`rdExit` of MR27) and `repFinN`.
* `rpEntF`, **`JAtZV3.repTail`**: from `let i ← get VALID` to the end (FL4 text verbatim, the GPR loop abstracted as
  `lp`, given by `repLoop1` / `repLoop3`): with a saved exit straight to `repFull`; without, the entry state
  (`rvIp`/`rvCtl`/`rvIntr`), MR0..2, the GPR loop, `repCr`, `repFull`.

Premise used: [P] `ZvVirtAgree arI` (gen 32). No new named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3RepVal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- MR2 masked to its low 32 bits when the caller is full-state (FL4 #85). -/
def rpFullF (full : Bool) (F : Nat → Fl4Spec.Word) : Nat → Fl4Spec.Word := fun k =>
  if full = true ∧ k = 2 then F 2 &&& 0xffffffff else F k

/-- `finish_notification`'s vectoring flag (FL4 #80). -/
def rpVecOf (saved : Bool) (vs : Fl4Spec.VcpuState) : Bool :=
  saved && decide (vs.exit.mrs 27 &&& (1 <<< 31) ≠ 0)

/-- The entry state over MR0..2. -/
def rpEntF (vs : Fl4Spec.VcpuState) (F : Nat → Fl4Spec.Word) : Nat → Fl4Spec.Word := fun k =>
  if k = 0 then vs.entryIp Fl4Spec.virtKind else if k = 1 then vs.entryCtl Fl4Spec.virtKind
  else if k = 2 then vs.entryIntr Fl4Spec.virtKind else F k

/-- The spec state FL4's report ends at (module docstring). -/
def repEnd (σ0 : Fl4Spec.State Unit) (t : U64) (x0 : Fl4Spec.Tcb) (pb : Option Fl4Spec.ObjRef) (v : U64)
    (vs : Fl4Spec.VcpuState) (pending saved full : Bool) (badge : U64) (F : Nat → Fl4Spec.Word) :
    Fl4Spec.State Unit :=
  if pending then
    repTail (Notif.updK (jMrSt σ0 t.bv x0 pb ((List.range 30).map (rpFullF full F))) v.bv (.archObj (.vcpu vs.reported)))
      t.bv (repX x0 ((List.range 30).map (rpFullF full F))) (1#u64 : U64).bv (0#u64 : U64).bv
  else
    repTail (jMrSt σ0 t.bv x0 pb ((List.range 30).map (repFinF (rpVecOf saved vs) (rpFullF full F)))) t.bv
      (repX x0 ((List.range 30).map (repFinF (rpVecOf saved vs) (rpFullF full F)))) (0#u64 : U64).bv badge.bv

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {a : A} {V X : Set U64}
variable {σ0 : Fl4Spec.State Unit} {x0 : Fl4Spec.Tcb} {pb : Option Fl4Spec.ObjRef} {vs : Fl4Spec.VcpuState}

set_option maxHeartbeats 16000000 in
/-- **The `if full …` block** (module docstring). -/
theorem JAtZV3.repFull (hVA : ZvVirtAgree arI) {t b v : U64} {F : Nat → Fl4Spec.Word} {s6 : S}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s6 a (jMrSt σ0 t.bv x0 pb ((List.range 30).map F)))
    (hr : t ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p) (hb : JBufR Z.B b pb)
    (hrs : x0.tcbState = .runningVM) (hv : v ∈ V) (hkv : σ0.kheap v.bv = some (.archObj (.vcpu vs)))
    (hvt : v.bv ≠ t.bv) (pending saved full : Bool) (hsaved : saved = vs.exit.valid)
    (hpf : pending = false → full = true) (badge : U64) :
    (do
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
          vcpu.finish_notification st arI s7 a t b
            badge vectoring
      else
        let s7 ← vcpu.set st s6 v vcpu.PENDING 0#u64
        let s8 ←
          obj.Tcb.set_reg st t s7 layout.reg.MSG_INFO 1#u64
        let s9 ←
          obj.Tcb.set_reg st t s8 layout.reg.BADGE 0#u64
        let ip1 ← obj.Tcb.reg st t s9 layout.reg.NEXT_IP
        let s10 ←
          obj.Tcb.set_reg st t s9 layout.reg.FAULT_IP ip1
        sched.set_thread_state st s10 t sched.TS_RUNNING) ⦃ s' => ∃ Lst' : U64 → List U64, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a
        (repEnd σ0 t x0 pb v vs pending saved full badge F) ⦄ := by
  have hk := v3_kv (ms := (List.range 30).map F) (x0 := x0) (pb := pb) hkv hvt
  have hkt := jMrSt_rcv σ0 t.bv x0 pb ((List.range 30).map F)
  have hE : vcpu.EXIT.val = 20992 := by unfold vcpu.EXIT; rfl
  cases full with
  | false =>
    have hp : pending = true := by
      cases pending
      · exact absurd (hpf rfl) (by simp)
      · rfl
    subst hp
    simp only [Bool.false_eq_true, ↓reduceIte]
    have e : (List.range 30).map (rpFullF false F) = (List.range 30).map F :=
      v3_map_congr 30 (fun k _ => by simp [rpFullF])
    simp only [repEnd, ↓reduceIte, e]
    exact J.repFinP hr hkt hrs hv hk
  | true =>
    simp only [↓reduceIte]
    refine WP.spec_bind (v3_syscall_arg2 s6 t b) fun i3 hi3 => ?_
    simp only [lift, bind_ok]
    have hv2 : i3.bv = F 2 := by
      rw [hi3]
      have B := J.z2.zv.base
      have h := ((B.xtop.irelK B.ks B.buf).1.toE.at_tcb hr hkt).regs (Endp.mrIdx 2)
      rw [h]
      show Endp.mrRegs x0.tcbArch.tcbContext.userRegs ((List.range 30).map F) (Endp.mrIdx 2) = F 2
      rw [Endp.mrRegs_mr _ _ (by omega : 2 < 4)]
      simp
    refine WP.spec_bind (setMrJ3F J hr hq hb 2#u64 2 (by simp) (by omega) (i3 &&& 4294967295#u64)) ?_
    rintro ⟨_, s7⟩ J7
    try simp only [uncurry_apply_pair]
    have hm : ((i3 &&& 4294967295#u64).bv : Fl4Spec.Word) = F 2 &&& (0xffffffff : Fl4Spec.Word) := by
      simp only [UScalar.bv_and, hv2]; rfl
    rw [v3_map_congr 30 (G := rpFullF true F) (fun k _ => by
      unfold rpFullF
      by_cases e2 : k = 2
      · subst e2; simp [hm]
      · simp [e2])] at J7
    have hk7 := v3_kv (ms := (List.range 30).map (rpFullF true F)) (x0 := x0) (pb := pb) hkv hvt
    cases pending with
    | true =>
      simp only [↓reduceIte]
      simp only [repEnd, ↓reduceIte]
      exact J7.repFinP hr (jMrSt_rcv _ _ _ _ _) hrs hv hk7
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [repEnd, Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_bind (Pₘ := fun vec => vec = rpVecOf saved vs) ?_ ?_
      · cases saved with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          simp [rpVecOf]
        | true =>
          simp only [↓reduceIte]
          step as ⟨i4, hi4⟩
          step as ⟨i5, hi5⟩
          rw [v3_get_eq, bind_ok, VirtSanEq.shl_i32 _ _ (by decide) (by decide), bind_ok]
          simp only [lift, bind_ok, WP.spec_ok]
          have hw := J7.rdExit hv hk7 i5 27 (by
            have : ((27 : Fin 30) : Nat) = 27 := rfl
            first | omega | (simp at hi4 hi5; omega) | (simp_all; omega))
          rw [v3_bne0]
          simp only [UScalar.bv_and, hw]
          have h1 : ((1#u64 : U64).bv <<< (31#i32 : I32).toNat : Fl4Spec.Word) = (1 : Fl4Spec.Word) <<< 31 := by
            decide
          first | rw [h1] | simp only [h1]
          simp [rpVecOf, ← hsaved]
      · intro vec hvec
        subst hvec
        exact J7.repFinN hVA hr hq hb hrs badge _

/-- The final MR function of the report's long branches (a saved exit keeps the loop's words). -/
def rpTailF (vs : Fl4Spec.VcpuState) (F0 : Nat → Fl4Spec.Word) : Nat → Fl4Spec.Word :=
  if vs.exit.valid then F0 else crF vs (gprOv vs (rpEntF vs F0) 15)

set_option maxHeartbeats 32000000 in
/-- **The tail of the report after its first loop, with a VCPU** (module docstring). -/
theorem JAtZV3.repTail (hVA : ZvVirtAgree arI) {t b v : U64} {F0 : Nat → Fl4Spec.Word} {s1 : S}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a (jMrSt σ0 t.bv x0 pb ((List.range 30).map F0)))
    (hr : t ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p) (hb : JBufR Z.B b pb)
    (hrs : x0.tcbState = .runningVM) (hv : v ∈ V) (hkv : σ0.kheap v.bv = some (.archObj (.vcpu vs)))
    (hvt : v.bv ≠ t.bv) (pending saved full : Bool) (hsaved : saved = vs.exit.valid)
    (hpf : pending = false → full = true) (badge : U64) (lp : S → Result S)
    (hlp : ∀ s4, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s4 a
        (jMrSt σ0 t.bv x0 pb ((List.range 30).map (rpEntF vs F0))) →
      lp s4 ⦃ s5 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s5 a
        (jMrSt σ0 t.bv x0 pb ((List.range 30).map (gprOv vs (rpEntF vs F0) 15))) ⦄) :
    (do
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
        let s5 ← lp s4
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
              then do
                   let i4 ← vcpu.svm.CR3
                   vcpu.get st s5 v i4
              else ok 0#u64
            let cr2 ←
              if i3 = 2#u64
              then do
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
            vcpu.finish_notification st arI s7 a t b
              badge vectoring
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
              then do
                   let i2 ← vcpu.svm.CR3
                   vcpu.get st s1 v i2
              else ok 0#u64
            let cr2 ←
              if i1 = 2#u64
              then do
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
            vcpu.finish_notification st arI s3 a t b
              badge vectoring
        else
          let s3 ← vcpu.set st s2 v vcpu.PENDING 0#u64
          let s4 ←
            obj.Tcb.set_reg st t s3 layout.reg.MSG_INFO 1#u64
          let s5 ←
            obj.Tcb.set_reg st t s4 layout.reg.BADGE 0#u64
          let ip ← obj.Tcb.reg st t s5 layout.reg.NEXT_IP
          let s6 ←
            obj.Tcb.set_reg st t s5 layout.reg.FAULT_IP ip
          sched.set_thread_state st s6 t sched.TS_RUNNING) ⦃ s' => ∃ Lst' : U64 → List U64, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a
        (repEnd σ0 t x0 pb v vs pending saved full badge (rpTailF vs F0)) ⦄ := by
  have hk := v3_kv (ms := (List.range 30).map F0) (x0 := x0) (pb := pb) hkv hvt
  rw [v3_get_eq, bind_ok]
  by_cases hval : vs.exit.valid = true
  · have hi0 : ¬ L.mem s1 (core.num.U64.wrapping_add v vcpu.VALID) = 0#u64 := fun h => by
      rw [(J.rdValid0 hv hk).1 h] at hval; cases hval
    rw [if_neg hi0, if_neg hi0, bind_ok]
    unfold rpTailF
    rw [if_pos hval]
    exact J.repFull hVA hr hq hb hrs hv hkv hvt pending saved full hsaved hpf badge
  · have hval' : vs.exit.valid = false := by simpa using hval
    have hi0 : L.mem s1 (core.num.U64.wrapping_add v vcpu.VALID) = 0#u64 := (J.rdValid0 hv hk).2 hval'
    rw [if_pos hi0]
    obtain ⟨i1, hvi, hi⟩ := hVA a
    refine WP.spec_bind (Pₘ := fun i => i = i1) (by rw [hvi, WP.spec_ok]) fun i1' hi1' => ?_
    subst hi1'
    refine WP.spec_bind (J.rvIp hv hk hi) fun ip hip => ?_
    refine WP.spec_bind (J.rvCtl hv hk hi) fun ctl hctl => ?_
    refine WP.spec_bind (J.rvIntr hv hk hi) fun intr hintr => ?_
    refine WP.spec_bind (setMrJ3F J hr hq hb 0#u64 0 (by simp) (by omega) ip) ?_
    rintro ⟨_, s2⟩ J2
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (setMrJ3F J2 hr hq hb 1#u64 1 (by simp) (by omega) ctl) ?_
    rintro ⟨_, s3⟩ J3
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (setMrJ3F J3 hr hq hb 2#u64 2 (by simp) (by omega) intr) ?_
    rintro ⟨_, s4⟩ J4
    try simp only [uncurry_apply_pair]
    rw [v3_map_congr 30 (G := rpEntF vs F0) (fun k _ => by
      unfold rpEntF
      simp only [hip, hctl, hintr]
      all_goals (by_cases e0 : k = 0 <;> by_cases e1 : k = 1 <;> by_cases e2 : k = 2 <;> simp_all))] at J4
    refine WP.spec_bind (hlp s4 J4) fun s5 J5 => ?_
    have hk5 := v3_kv (ms := (List.range 30).map (gprOv vs (rpEntF vs F0) 15)) (x0 := x0) (pb := pb) hkv hvt
    rw [v3_get_eq, bind_ok]
    have hi0' : L.mem s5 (core.num.U64.wrapping_add v vcpu.VALID) = 0#u64 := (J5.rdValid0 hv hk5).2 hval'
    rw [if_pos hi0']
    refine WP.spec_bind (J5.repCr hVA hr hq hb hv hkv hvt) fun s6 J6 => ?_
    unfold rpTailF
    rw [if_neg hval]
    exact J6.repFull hVA hr hq hb hrs hv hkv hvt pending saved full hsaved hpf badge

end

end

end Fl4Proofs.P3

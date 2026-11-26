/-
# P2 (line lvm, gen 7): **the acc walk of `local_vm_exit` with a pending exit** (`PENDING ≠ 0` at the entry)

`vexit_accG_p`: from a state with P1's invariant (`BXI`), an accepted run of `handle_vcpu_exit_local` whose VCPU
has a pending exit is the same run on any store `gS` answering as `st`

* the reads of `IrqRd` (the timer interrupt's read set), the two kernel-global words, and the writes of `IrqWr`
  other than the current thread's `STATE` (as `vexit_accG_np`);
* the words `U` the report writes besides the thread's registers (its IPC buffer, which P1's `BufOK U` places in
  `U`, and `v.PENDING`), read and written (`gU`); every aligned word of the VCPU `v` (`VW`) and its VMCS shadow
  (`vmcs_addr`), read;
* the report's last write, the current thread's `STATE := RUNNING`, at each state where it is still
  `RUNNING_VM` and homed here (`gSt`: `GWr` for `acc`, the per-write check for `move`).

The run (`vexit_split`, `vexitTail_split`, `vfinish_split`): the head's checks at `s`, `update_timestamp` to `s1`,
`vcpu.check` = `vcpu.report` (`vcpu.check_pend`; P1's `vcpu.report.xfV`: its writes are `RepW` words, then
`set_thread_state TS_RUNNING`, which writes only `STATE`, the thread staying schedulable: `schedule_tcb_sch`) to
`s2`, `check_budget` (sufficient: the SC's head words are kept, `suff_congr`), `schedule` (the quiet case at `s2`:
`rel_ag`, the deadline, the action kept: `schedule_resume`, `schedTail_fp`), `activate_thread` (no yield, now
`RUNNING`: `activate_id`), `vcpu.check` (no longer `RUNNING_VM`: `vcpu.check_nvm`). Each guarded call is the real
one at its state (`VexitAcc`): the report by gen 4's `vcpu.report.guardP` with gen 5's frame (`repFr_steps`) and
`repFr_finX`.

No named premises: every hypothesis is about `gS`'s read / write sets, P1's placement of the buffer and of
`v.PENDING` (`hU`, `hbuf`, as P1's `vcpu.check.vck`) or the entry state.
-/
import Fl4Proofs.P2.AccessLvmPx
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt VW RepG)

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac U : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 32000000 in
/-- **An accepted VM exit with a pending exit on the guarded store** (module docstring), with the report's words `U`
only written (`gU`) and `v.PENDING` read (`gRp`): `R` need not hold the IPC buffer's (user) words (line hpzg, gen 5,
for `ReadOnce` on a user-free read set). -/
theorem vexit_accG_pW {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {v n : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRd st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hRn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (hU : ∀ x ∈ U, UsrW st T Cs H Sg Scs Z s x) (hpU : core.num.U64.wrapping_add v vcpu.PENDING ∈ U)
    (hbuf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK U b ⦄)
    (gU : ∀ x ∈ U, W x) (gRp : R (core.num.U64.wrapping_add v vcpu.PENDING)) (gV : VW R v)
    (gM : ∀ f b, vcpu.vmcs_addr v f = ok b → R b)
    (gSt : ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RUNNING_VM → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hpd : vcpu.get st s v vcpu.PENDING ≠ ok 0#u64)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    localvm.handle_vcpu_exit_local gS ar s a v n = ok (true, s', a') := by
  have hRp : R (core.num.U64.wrapping_add v vcpu.PENDING) := gRp
  obtain ⟨i3, hstv, hv0, eb, en, ep, -, eok, esch, eq, et⟩ := vexit_split ar h
  have hi3 : i3 ≠ 0#u64 := fun e => hpd (by rw [ep, e])
  obtain ⟨haff, hy0, hsct, hcore⟩ := current_vm_ok_true eok
  obtain ⟨s1, a1, now, i2, s2, a2, x, s3, a3, eu, enow, ei2, eb4, eaq, evc, ecb, efin⟩ := vexitTail_split ar et
  obtain ⟨edue, erel⟩ := aq_true eaq
  obtain ⟨s4, a4, s5, a5, t, esc, eac, ett, evc5⟩ := vfinish_split ar efin
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  -- the current SC
  have hX := hI.2.2.1
  have hS := hI.2.2.2.2
  have hO := hX.1
  have hcs : L.cscW s ∈ Scs := hX.2.2.cur
  have hcq : SCq st s Ω (L.cscW s) (Z (L.cscW s)) := scq_of hO hS hcs
  have hact0 : L.actionW s = sched.ACTION_RESUME_CURRENT := sq_true eq
  have hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := hI.2.1.resume (hact0.trans resume_val)
  have hAc : L.cscW s ∈ Ac := by
    rw [← hsct]
    exact hI.2.1.sact _ hcT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hact0.trans resume_val, rfl⟩))))) hsc0
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := (hS.act _ hcs).1 hAc
  have hmaxΩ : maxA (L.cscW s) ∈ Ω := hcq.2.1 _ hcq.2.2.2.2 hcq.2.2.2.1
  -- `s → s1`: the timestamp update
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  have k1 : L.ksb s1 = L.ksb s := by rw [er, utW_ksb]
  have c1 : L.cpu s1 = L.cpu s := by rw [er, utW_cpu]
  have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
    fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
  have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c1, nodeAt_of_ksb k1]
  have hnode1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      L.mem s1 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48
    refine m1 _ (nodeAt_aligned hN ho h8) (fun e => ?_) (fun e => ?_)
    · have e' := congrArg UScalar.val e
      unfold ctA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CUR_TIME])] at e'
      simp [layout.node.CUR_TIME] at e'; omega
    · have e' := congrArg UScalar.val e
      unfold cnA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CONSUMED])] at e'
      simp [layout.node.CONSUMED] at e'; omega
  have htcb1 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8
    exact m1 _ (field_aligned (hT y hy) hK h8) (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CUR_TIME]))
      (tcb_node_ne hN hy (hT y hy) hK (by simp [layout.node.CONSUMED]))
  have hout1 : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b := fun b hb =>
    m1 b hb.1 (fun e => out_ne_node hb hcC hN (by simp [layout.node.CUR_TIME]) (congrArg UScalar.val e).symm)
      (fun e => out_ne_node hb hcC hN (by simp [layout.node.CONSUMED]) (congrArg UScalar.val e).symm)
  have agΩ1 : ∀ b ∈ Ω, L.mem s1 b = L.mem s b := fun b hb => hout1 b (h0.omega b hb)
  have agS1 : ∀ c ∈ Scs, ∀ b, Aligned b → InSC c (Z c) b → L.mem s1 b = L.mem s b := fun c hc b hb hin =>
    agΩ1 b ((scq_of hO hS hc).2.1 b hb hin)
  -- the quiet facts at `s1`
  have hB1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 :=
    (irq_quiet_schedule ar (a3 := a1) hA hI eq eu enow erel edue (WritesIn.refl s1 _)).1
  obtain ⟨hT1, hR1, hact1⟩ := irq_quiet_pre ar hA hI eq eu enow erel edue (WritesIn.refl s1 _)
  have hcur1 : L.curW s1 = L.curW s := by
    unfold LawfulStore.curW
    rw [e1N]
    exact hnode1 _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega)
  have hcs1 : L.cscW s1 = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  have hsc1 : L.mem s1 (scA (L.curW s)) = L.mem s (scA (L.curW s)) := by
    rw [scA_eq]; exact htcb1 hcT (by simp) (by simp)
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [c1]; exact hN.ksb k1
  have hcC1 : L.cpu s1 ∈ Cs := by rw [c1]; exact hcC
  -- `vcpu.check` at `s1` is the report
  have eb1 : vcpu.bound st s1 (L.curW s) = ok v := by
    rw [vcpu_bound_congr (htcb1 hcT (by simp) (by simp))]; exact eb
  have hv1 : L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64) = v := by
    have e := eb1
    rw [eq_of_spec_fd (vcpu.bound.spec (L := L) s1 _)] at e
    exact ok_inj_ff e
  have ep1 : vcpu.get st s1 v vcpu.PENDING = ok i3 := by
    rw [vcpu_get_congr (hout1 _ (hU _ hpU).out)]; exact ep
  have hst1 : L.mem s1 (stA (L.curW s)) = sched.TS_RUNNING_VM := by
    rw [stA_eq, htcb1 hcT (by simp) (by simp), ← stA_eq]; exact hstv
  have evc0 := evc
  rw [vcpu.check_pend ar s1 a1 (L.curW s) v hst1 eb1 hv0 ep1 hi3] at evc
  obtain ⟨r2, er2, eR2⟩ := bind_eq_ok evc
  obtain ⟨rfl, rfl⟩ : s2 = r2 ∧ a1 = a2 := by
    have e := ok_inj_ff eR2
    simp only [Prod.mk.injEq] at e
    exact ⟨e.1.symm, e.2⟩
  -- the report's writes (P1 `vcpu.report.xfV`)
  have hU1 : ∀ x ∈ U, UsrW st T Cs H Sg Scs Z s1 x := fun x hx => (hU x hx).ksb k1
  have ib1 : IbSame (L := L) s s1 (L.curW s) :=
    ⟨by unfold ibWordA; exact htcb1 hcT (by simp) (by simp),
      by rw [sbWordA_eq]; exact htcb1 hcT (by simp) (by simp),
      by rw [sbWordA8_eq]; exact htcb1 hcT (by simp) (by simp)⟩
  obtain ⟨b, eb0, hbOK⟩ := spec_ex_fd hbuf
  have eb1' : msg.lookup_ipc_buffer st s1 true (L.curW s) = ok b := (lookup_ipc_buffer_same ib1).trans eb0
  have hXf := vcpu.report.xfV (U := U) hA s1 a1 (L.curW s) 0#u64 (BXI.blk hB1) hcT hst1 hU1
    (by rw [eb1', WP.spec_ok]; exact hbOK) (fun _ _ => by rw [hv1]; exact hpU)
  rw [er2, WP.spec_ok] at hXf
  obtain ⟨s2', -, -, w12', est⟩ := hXf
  have aS : Aligned (stA (L.curW s)) := by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp)
  have h3328 : (3328#u64 : U64).val = 3328 := by simp
  have nB_node : ∀ o : U64, o.val < 4288 → ¬ (RepW (L.curW s) U (L.nodeAt s (L.cpu s) o) ∨
      L.nodeAt s (L.cpu s) o = stA (L.curW s)) := by
    rintro o ho ((⟨K, -, hK, -, e⟩ | hu) | e)
    · exact node_ne_field hN ho hcT ht' (by omega) e
    · exact out_ne_node (hU _ hu).out hcC hN ho rfl
    · rw [stA_eq] at e; exact node_ne_field hN ho hcT ht' (by simp) e
  have nB_fld : ∀ z ∈ T, ∀ K : U64, K.val < 4096 → (z = L.curW s → K.val < 256 ∨ 3328 < K.val) →
      ¬ (RepW (L.curW s) U (core.num.U64.wrapping_add z K) ∨
        core.num.U64.wrapping_add z K = stA (L.curW s)) := by
    rintro z hz K hK hne ((⟨K', h1, h2, -, e⟩ | hu) | e)
    · exact field_ne (hT z hz) ht' hK (by omega) (fun h => by have := hne h; omega) e
    · exact out_ne_field (hU _ hu).out hz (hT z hz) hK rfl
    · rw [stA_eq] at e
      exact field_ne (hT z hz) ht' hK (by simp) (fun h => by have := hne h; omega) e
  have nB_sc : ∀ c ∈ Scs, ∀ b, Aligned b → InSC c (Z c) b →
      ¬ (RepW (L.curW s) U b ∨ b = stA (L.curW s)) := by
    rintro c hc b hb hin ((⟨K, -, hK, -, rfl⟩ | hu) | rfl)
    · exact out_ne_field (h0.omega _ ((scq_of hO hS hc).2.1 _ hb hin)) hcT ht' (by omega) rfl
    · exact (hU _ hu).sc c hc hin
    · rw [stA_eq] at hb hin
      exact out_ne_field (h0.omega _ ((scq_of hO hS hc).2.1 _ hb hin)) hcT ht' (by simp) rfl
  have w12Y : WritesIn st s1 (L.wr s2' (stA (L.curW s)) sched.TS_RUNNING)
      (fun b => RepW (L.curW s) U b ∨ b = stA (L.curW s)) := w12'.trans (writesIn_wr aS)
  have tfY : ∀ z ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (z = L.curW s → K.val < 256 ∨ 3328 < K.val) →
      L.mem (L.wr s2' (stA (L.curW s)) sched.TS_RUNNING) (core.num.U64.wrapping_add z K) =
        L.mem s (core.num.U64.wrapping_add z K) := fun z hz K hK h8 hne =>
    (w12Y.mem_eq (field_aligned (hT z hz) hK h8) (nB_fld z hz K hK hne)).trans (htcb1 hz hK h8)
  have isY : sched.is_schedulable st (L.wr s2' (stA (L.curW s)) sched.TS_RUNNING) (L.curW s) = ok true := by
    have eS : L.mem (L.wr s2' (stA (L.curW s)) sched.TS_RUNNING) (stA (L.curW s)) = sched.TS_RUNNING := by
      rw [L.mem_wr _ _ _ _ aS aS, if_pos rfl]
    have eQ : L.mem (L.wr s2' (stA (L.curW s)) sched.TS_RUNNING) (inqA (L.curW s)) = L.mem s (inqA (L.curW s)) :=
      tfY _ hcT _ (by simp) (by simp) (fun _ => Or.inr (by simp))
    rw [is_schedulable_rel (s := s) ⟨fun _ => Or.inr (Or.inr hstv), fun _ => Or.inl eS⟩
      (tfY _ hcT _ (by simp) (by simp) (fun _ => Or.inr (by simp)))
      (fun _ => by
        rw [hsct]
        unfold LawfulStore.rmax
        exact (w12Y.mem_eq hcq.2.2.2.2 (nB_sc _ hcs _ hcq.2.2.2.2 hcq.2.2.2.1)).trans
          (agS1 _ hcs _ hcq.2.2.2.2 hcq.2.2.2.1)) (by rw [eQ])]
    exact esch
  have eS2 : s2 = L.wr s2' (stA (L.curW s)) sched.TS_RUNNING := by
    have e : sched.set_thread_state st s2' (L.curW s) sched.TS_RUNNING =
        ok (L.wr s2' (stA (L.curW s)) sched.TS_RUNNING) := by
      unfold sched.set_thread_state
      rw [PathObl.set_state_ok']
      simp only [bind_ok]
      exact schedule_tcb_sch _ _ isY
    rw [e] at est
    exact (ok_inj_ff est).symm
  have w12 : WritesIn st s1 s2 (fun b => RepW (L.curW s) U b ∨ b = stA (L.curW s)) := by rw [eS2]; exact w12Y
  have hst2 : L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [eS2, L.mem_wr _ _ _ _ aS aS, if_pos rfl]
  -- the frame at `s2`
  have k2 : L.ksb s2 = L.ksb s := w12.1.trans k1
  have c2 : L.cpu s2 = L.cpu s := w12.2.1.trans c1
  have e2N : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c2, nodeAt_of_ksb k2]
  have nd2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s2 (L.nodeAt s (L.cpu s) o) = L.mem s1 (L.nodeAt s (L.cpu s) o) := fun o ho h8 =>
    w12.mem_eq (nodeAt_aligned hN ho h8) (nB_node o ho)
  have tf2 : ∀ z ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (z = L.curW s → K.val < 256 ∨ 3328 < K.val) →
      L.mem s2 (core.num.U64.wrapping_add z K) = L.mem s (core.num.U64.wrapping_add z K) := fun z hz K hK h8 hne =>
    (w12.mem_eq (field_aligned (hT z hz) hK h8) (nB_fld z hz K hK hne)).trans (htcb1 hz hK h8)
  have sc2 : ∀ c ∈ Scs, ∀ b, Aligned b → InSC c (Z c) b → L.mem s2 b = L.mem s b := fun c hc b hb hin =>
    (w12.mem_eq hb (nB_sc c hc b hb hin)).trans (agS1 c hc b hb hin)
  have hnode2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      L.mem s2 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8 h40 h48 =>
    (nd2 o ho h8).trans (hnode1 o ho h8 h40 h48)
  have hcur2 : L.curW s2 = L.curW s := by
    unfold LawfulStore.curW
    rw [e2N]
    exact hnode2 _ (by rw [curth_val]; omega) (by rw [curth_val]) (by rw [curth_val]; omega)
      (by rw [curth_val]; omega)
  have hcs2 : L.cscW s2 = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [e2N]
    exact hnode2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  have sc2c : L.mem s2 (scA (L.curW s)) = L.cscW s := by
    rw [scA_eq, tf2 _ hcT _ (by simp) (by simp) (fun _ => Or.inr (by simp)), ← scA_eq]; exact hsct
  have scK2 : ∀ y ∈ T, L.mem s2 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact tf2 y hy _ (by simp) (by simp) (fun _ => Or.inr (by simp))
  have scK1 : ∀ y ∈ T, L.mem s1 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact htcb1 hy (by simp) (by simp)
  have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [c2]; exact hN.ksb k2
  have hcC2 : L.cpu s2 ∈ Cs := by rw [c2]; exact hcC
  -- the quiet facts at `s2`
  have tm1e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have tm2e : L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e2N]
    exact hnode2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have tmTs : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ∈ T := fun hne =>
    (tmin_facts (BXI.blk hI) hcC hne).1
  have hT2 : L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.TIMER_MIN) = 0#u64 ∨
      L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CUR_TIME) <
        L.mem s2 (tdA (L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.TIMER_MIN))) := by
    have eC : L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CUR_TIME) =
        L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_TIME) := by
      rw [e2N, e1N]; exact nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
    rw [tm2e, eC, ← tm1e]
    rcases hT1 with h1 | h1
    · exact Or.inl h1
    · by_cases h00 : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) = 0#u64
      · exact Or.inl h00
      · right
        have hq := tmTs (by rw [← tm1e]; exact h00)
        rw [← tm1e] at hq
        have e : L.mem s2 (tdA (L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN))) =
            L.mem s1 (tdA (L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN))) :=
          (tf2 _ hq _ (by simp) (by simp) (fun _ => Or.inr (by simp))).trans (htcb1 hq (by simp) (by simp)).symm
        rw [e]; exact h1
  have hR2 : RelNone st s2 := rel_ag hB1 (w12.1) (w12.2.1)
    (fun o ho h8 => by rw [e1N]; exact nd2 o ho h8)
    (fun y hy => (scK2 y hy).trans (scK1 y hy).symm)
    (fun c hc b hb hin => (sc2 c hc b hb hin).trans (agS1 c hc b hb hin).symm) hR1
  have hact2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    have e := hact1
    unfold LawfulStore.actionW at e ⊢
    rw [e1N] at e
    rw [e2N, nd2 _ (by rw [act_val]; omega) (by rw [act_val])]
    exact e
  -- `check_budget` at `s2`
  have ecs2 : sched.cur_sc st s2 = ok (L.cscW s) := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2)]; exact congrArg ok hcs2
  have ei2' : sched.consumed st s2 = ok i2 := by
    rw [lvm_consumed_ok, e2N, nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]), ← e1N,
      ← lvm_consumed_ok]
    exact ei2
  have hcq1 : SCq st s1 Ω (L.cscW s) (Z (L.cscW s)) := SCq.agree hcq agΩ1
  have hmx1 : L.rmax s1 (L.cscW s) ≠ 0#u64 := by
    unfold LawfulStore.rmax; rw [agΩ1 _ hmaxΩ]; exact hmx0
  have suf2 : sporadic.sufficient st ar s2 a1 (L.cscW s) i2 = ok true := by
    rw [suff_congr ar (X := s1) (sc_head_keep (hcq1.1 hmx1)
      (fun b hb hin => (sc2 _ hcs b hb hin).trans (agS1 _ hcs b hb hin).symm))]
    exact eb4
  have ecbr := ecb
  rw [check_budget_suf ar ecs2 ei2' suf2] at ecb
  obtain ⟨-, rfl, rfl⟩ : true = x ∧ s2 = s3 ∧ a1 = a3 := by
    have e := ok_inj_ff ecb
    simp only [Prod.mk.injEq] at e
    exact e
  -- `schedule` at `s2`: the quiet case
  have hsch : sched.schedule st ar s2 a1 = schedTail (st := st) ar s2 a1 := schedule_resume ar s2 a1 hT2 hR2 hact2
  have hfp := schedTail_fp ar hA s2 a1 (zc := Z (L.cscW s))
    (B := fun b => (∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add (L.curW s) K) ∧
      b ≠ L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    hcC2 hN2 hT (fun b hb => (h0.omega b hb).ksb k2)
    (by rw [hcur2]; exact hcT) (by rw [hcur2, hcs2]; exact sc2c)
    (by rw [hcs2]; exact scq_agree' hcq (fun b hb hin => sc2 _ hcs b hb hin))
    (fun o ho h8 hz => by
      rw [e2N]
      refine ⟨fun K hK => node_ne_field hN ho hcT ht' hK, fun e => hz ?_⟩
      have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by rw [curth_val]; omega), curth_val] at e'
      omega)
    (fun b hb hin => by
      rw [hcs2] at hin
      have ho := h0.omega b (hcq.2.1 b hb hin)
      exact ⟨fun K hK e => out_ne_field ho hcT ht' hK (congrArg UScalar.val e).symm,
        fun e => out_ne_node ho hcC hN (by rw [curth_val]; omega) (congrArg UScalar.val e).symm⟩)
  rw [← hsch, esc, WP.spec_ok] at hfp
  have w24 := hfp
  have k4 : L.ksb s4 = L.ksb s := w24.1.trans k2
  have c4 : L.cpu s4 = L.cpu s := w24.2.1.trans c2
  have e4N : ∀ o, L.nodeAt s4 (L.cpu s4) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c4, nodeAt_of_ksb k4]
  have hcur4 : L.curW s4 = L.curW s := by
    have h1 := hcur2
    unfold LawfulStore.curW at h1 ⊢
    rw [e2N] at h1
    rw [w24.2.1, nodeAt_of_ksb w24.1, e2N,
      w24.mem_eq (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) (fun hb => hb.2 rfl)]
    exact h1
  have tK4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s4 (core.num.U64.wrapping_add (L.curW s) K) = L.mem s2 (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K hK h8 => w24.mem_eq (field_aligned ht' hK h8) (fun hb => hb.1 K hK rfl)
  have hy4 : L.mem s4 (yieldA (L.curW s)) = 0#u64 := by
    unfold yieldA
    rw [tK4 _ (by simp) (by simp), tf2 _ hcT _ (by simp) (by simp) (fun _ => Or.inr (by simp))]
    exact hy0
  have hst4 : L.mem s4 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [stA_eq, tK4 _ (by simp) (by simp), ← stA_eq]; exact hst2
  have sc4 : L.mem s4 (scA (L.curW s)) = L.cscW s := by
    rw [scA_eq, tK4 _ (by simp) (by simp), ← scA_eq]; exact sc2c
  have hnr : L.mem s4 (stA (L.curW s)) ≠ sched.TS_RESTART := by
    rw [hst4]; simp [sched.TS_RUNNING, sched.TS_RESTART]
  have hnvm : L.mem s4 (stA (L.curW s)) ≠ sched.TS_RUNNING_VM := by
    rw [hst4]; simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]
  -- `activate_thread` changes nothing
  rw [activate_id ar s4 a4 (by rw [hcur4]; exact hy4) (by rw [hcur4]; exact hnr)] at eac
  obtain ⟨rfl, rfl⟩ : s4 = s5 ∧ a4 = a5 := by
    have e := ok_inj_ff eac
    simp only [Prod.mk.injEq] at e
    exact e
  -- the guarded store: what it admits
  have hok : IrqOk st s := ⟨haff, hsct, hcore⟩
  replace gRd := gRd hok
  replace gWr := gWr hok
  replace hD1 := hD1 hok
  replace hD2 := hD2 hok
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gRd _ (nodeAt_aligned hN h1 h2) (Or.inl ⟨o, h1, h2, rfl⟩)
  have nW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → W (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    gWr _ (nodeAt_aligned hN h1 h2) (Or.inl ⟨o, h1, h2, rfl⟩) (fun e => by
      rw [stA_eq] at e; exact node_ne_field hN h1 hcT ht' (by simp) e)
  have cR : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      K.val ≠ 3496 → K.val ≠ 3504 → R (core.num.U64.wrapping_add (L.curW s) K) := fun K h1 h2 h3 h4 h5 h6 =>
    gRd _ (field_aligned ht' h2 h3) (Or.inr (Or.inl ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩))
  have cW : ∀ K : U64, 256 ≤ K.val → K.val < 3328 → K.val % 8 = 0 → W (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K h1 h2 h3 =>
    gWr _ (field_aligned ht' (by omega) h3) (Or.inr (Or.inl ⟨K, h1, by omega, h3, rfl⟩)) (fun e => by
      rw [stA_eq] at e
      exact tcb_word_ne ht' ht' (by omega) (by simp) (fun _ h => by simp at h; omega) e)
  have rR : ∀ r : U64, r.val < 384 → R (regA (L.curW s) r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cR K (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have rW : ∀ r : U64, r.val < 384 → W (regA (L.curW s) r) := fun r hr => by
    obtain ⟨K, hK, e⟩ := regA_eq ht' hr
    rw [e]; exact cW K (by omega) (by omega) (by omega)
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha =>
    gRd _ ha (Or.inr (Or.inr (Or.inl hb)))
  have scNS : ∀ b, Aligned b → InSC (L.cscW s) (Z (L.cscW s)) b → b ≠ stA (L.curW s) := fun b ha hb e => by
    rw [stA_eq] at e
    exact out_ne_field (h0.omega b (hcq.2.1 b ha hb)) hcT ht' (by simp) (congrArg UScalar.val e).symm
  have hSc : ScAcc R W (L.cscW s) (Z (L.cscW s)) := ⟨fun b ha hb => scR b hb ha, fun b h1 h2 =>
    gWr _ h1 (Or.inr (Or.inr (Or.inl h2))) (scNS b h1 ⟨by have := h2.1; omega, h2.2⟩),
    gWr _ hcq.2.2.1.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (scNS _ hcq.2.2.1.2 hcq.2.2.1.1)⟩
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rIq : R (inqA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rYt : R (yieldA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rVc : R (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
    cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rBn : R (core.num.U64.wrapping_add (L.curW s) 3368#u64) :=
    cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  have rCore : R (scCoreA (L.cscW s)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    exact scR _ ⟨by unfold scCoreA; rw [hv]; omega, by unfold scCoreA; rw [hv, hcv]; omega⟩
      (by unfold Aligned scCoreA; rw [hv, hcv]; omega)
  have nrm : ∀ Y : S, (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R W Y := fun Y e => by
    unfold PathObl.NodeSt
    rw [e, e]
    exact ⟨nR _ (by rw [curth_val]; omega) (by rw [curth_val]), nR _ (by rw [act_val]; omega) (by rw [act_val]),
      nW _ (by rw [act_val]; omega) (by rw [act_val])⟩
  have ndR : ∀ (Y : S), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → ∀ o : U64, o.val < 4288 →
      o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) := fun Y e o h1 h2 => by rw [e]; exact nR o h1 h2
  have hdC : ∀ Y : S, (∀ b, Aligned b → InSC (L.cscW s) (Z (L.cscW s)) b → L.mem Y b = L.mem s b) →
      RdHead (L := L) R Y (L.cscW s) := fun Y ag =>
    hSc.head ((scq_agree' hcq ag).1 (by
      unfold LawfulStore.rmax; rw [ag _ hcq.2.2.2.2 hcq.2.2.2.1]; exact hmx0))
  -- the release head
  have hRH : ∀ Y : S, L.ksb Y = L.ksb s → L.cpu Y = L.cpu s →
      L.mem Y (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) →
      (∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y)) →
      (∀ c ∈ Scs, ∀ b, Aligned b → InSC c (Z c) b → L.mem Y b = L.mem s b) →
      L.mem Y (rhA (L := L) Y) ≠ 0#u64 → L.mem Y (rhA (L := L) Y) ∈ T ∧
      R (scA (L.mem Y (rhA (L := L) Y))) ∧
      SCq st Y Ω (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) (Z (L.mem Y (scA (L.mem Y (rhA (L := L) Y))))) ∧
      L.rmax Y (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) ≠ 0#u64 ∧
      (∀ b, InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) (Z (L.mem Y (scA (L.mem Y (rhA (L := L) Y))))) b →
        Aligned b → R b) ∧
      (L.mem Y (scA (L.mem Y (rhA (L := L) Y))) ≠ L.cscW s → ∀ b,
        InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) (Z (L.mem Y (scA (L.mem Y (rhA (L := L) Y))))) b →
        Outside b (L.cscW s) (Z (L.cscW s))) := by
    intro Y kY cY eh es ag
    have e0 : L.mem Y (rhA (L := L) Y) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
      show L.mem Y (L.nodeAt Y (L.cpu Y) _) = _
      rw [cY, nodeAt_of_ksb kY, eh]
    rw [e0]
    intro hne
    obtain ⟨r1, -, -, r4, r5⟩ := rel_facts hI hne
    rw [es _ r1]
    have hqr := scq_of hO hS r4
    refine ⟨r1, gRd _ ?_ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl rfl⟩)))),
      scq_agree' hqr (fun b hb hin => ag _ r4 b hb hin), ?_,
      fun b hb ha => gRd _ ha (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr hb⟩)))), fun hn b hb => ?_⟩
    · rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp)
    · unfold LawfulStore.rmax
      rw [ag _ r4 _ hqr.2.2.2.2 hqr.2.2.2.1]; exact r5
    · have := hO.scDisj _ r4 _ hcs hn
      unfold Outside; unfold InSC at hb; omega
  have rhd : ∀ Y : S, L.ksb Y = L.ksb s → L.cpu Y = L.cpu s →
      L.mem Y (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) →
      (∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y)) →
      (∀ c ∈ Scs, ∀ b, Aligned b → InSC c (Z c) b → L.mem Y b = L.mem s b) →
      L.mem Y (rhA (L := L) Y) ≠ 0#u64 → R (scA (L.mem Y (rhA (L := L) Y))) ∧
        RdHead (L := L) R Y (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) := by
    intro Y kY cY eh es ag hne
    obtain ⟨-, q2, q3, q4, q5, -⟩ := hRH Y kY cY eh es ag hne
    exact ⟨q2, PathObl.ScAcc.head (W := fun _ => True) ⟨fun b ha hb => q5 b hb ha, fun _ _ _ => trivial, trivial⟩ (q3.1 q4)⟩
  have rh1 : L.mem s1 (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) :=
    hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have rh2 : L.mem s2 (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) :=
    hnode2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  -- the earliest timer
  have tmT : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ∈ T ∧
      R (core.num.U64.wrapping_add (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) 3528#u64) := by
    intro hne
    have q1 := tmTs hne
    exact ⟨q1, gRd _ (field_aligned (hT _ q1) (by simp) (by simp))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl ⟨3528#u64, by simp, rfl⟩⟩)))))⟩
  have tm1 : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) ∈ T ∧
      R (tdA (L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN))) := fun hne => by
    rw [tm1e] at hne ⊢
    exact tmT hne
  have tm2 : L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.TIMER_MIN) ∈ T ∧
      R (tdA (L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.TIMER_MIN))) := fun hne => by
    rw [tm2e] at hne ⊢
    exact tmT hne
  -- the guarded report at `s1`
  have hsU : scA (L.curW s) ∉ U := fun hu => out_ne_field (hU _ hu).out hcT ht' (by simp) rfl
  have Rs := repFr_steps (Ω := Ω) (Rp := Rp) (Nt := Nt) (Ac := Ac) (s0 := s1) hcT hU1 hbOK
  have hfin := repFr_finX (T := T) (Cs := Cs) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt)
    (Z := Z) (Ac := Ac) (U := U) (gS := gS) ht' hsU (nrm s1 e1N)
    (fun X hX => gSt X hX.2.1 (by
      have e : L.mem X (affA (L.curW s)) = L.mem s1 (affA (L.curW s)) :=
        hX.2.2.mem_eq (field_aligned ht' (by simp) (by simp))
          (fun hr => nB_fld _ hcT _ (by simp) (fun _ => Or.inr (by simp)) (Or.inl hr))
      rw [e]
      have e' : L.mem s1 (affA (L.curW s)) = L.mem s (affA (L.curW s)) := htcb1 hcT (by simp) (by simp)
      rw [e']; exact haff))
    rSt rSc (by rw [hsc1, hsct]; exact rMx) rIq
  have hlb : msg.lookup_ipc_buffer gS s1 true (L.curW s) = msg.lookup_ipc_buffer st s1 true (L.curW s) := by
    have hsl : obj.Tcb.slot (L.curW s) layout.tcb.SLOT_BUFFER = ok (sbWordA (L.curW s)) := by
      unfold obj.Tcb.slot sbWordA; simp only [lift, bind_ok]
    refine PathObl.msg.lookup_ipc_buffer.guard s1 true (L.curW s) hsl
      (cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)) ?_ ?_
    · rw [sbWordA_eq]
      exact gRd _ (field_aligned ht' (by simp) (by simp))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨64#u64, by simp, by simp, by simp, rfl⟩)))))
    · rw [sbWordA8_eq]
      exact gRd _ (field_aligned ht' (by simp) (by simp))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨72#u64, by simp, by simp, by simp, rfl⟩)))))
  have G : RepG R W (L.curW s) v b :=
    { regR := rR
      regW := rW
      bufW := fun hb0 i hi => gU _ (hbOK hb0 i hi)
      vR := fun _ => gV
      vmcs := fun _ => gM
      pW := fun _ => gU _ hpU }
  have grep : vcpu.report gS ar s1 a1 (L.curW s) 0#u64 = vcpu.report st ar s1 a1 (L.curW s) 0#u64 :=
    PathObl.vcpu.report.guardP hA s1 a1 (L.curW s) 0#u64 v b Rs hfin ⟨BXI.blk hB1, hst1, WritesIn.refl _ _⟩
      rVc hv1 hlb eb1' (fun _ => hpU) G
  have gvc1 : vcpu.check gS ar s1 a1 (L.curW s) = vcpu.check st ar s1 a1 (L.curW s) :=
    vcpu.check.guard_pend ar s1 a1 (L.curW s) v rSt rVc hRp eb1 hv0 ep1 hi3 grep
  -- the guarded calls after the report
  have agC2 : ∀ b, Aligned b → InSC (L.cscW s) (Z (L.cscW s)) b → L.mem s2 b = L.mem s b := fun b hb hin =>
    sc2 _ hcs b hb hin
  have gcb : sched.check_budget gS ar s2 a1 = sched.check_budget st ar s2 a1 :=
    sched.check_budget.guard_suf ar s2 a1
      (ndR s2 e2N _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      (ndR s2 e2N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
      (fun sc e => by
        rw [ecs2] at e
        rw [← ok_inj_ff e]
        exact hdC s2 agC2)
      (fun sc c e1 e2 => by
        rw [ecs2] at e1
        rw [ei2'] at e2
        rw [← ok_inj_ff e1, ← ok_inj_ff e2]
        exact suf2)
  have hres := resume_hsw_hfr (gS := gS) ar hA s2 a1 (zc := Z (L.cscW s)) hcC2 hN2 hT
    (fun b hb => (h0.omega b hb).ksb k2) (by rw [hcur2]; exact hcT) (by rw [hcur2, hcs2]; exact sc2c)
    (by rw [hcs2]; exact scq_agree' hcq agC2)
    (by rw [hcs2]; unfold LawfulStore.rmax; rw [agC2 _ hcq.2.2.2.2 hcq.2.2.2.1]; exact hmx0)
    (fun o h1 h2 => by rw [e2N]; exact ⟨nR o h1 h2, nW o h1 h2⟩)
    (by rw [hcs2]; exact hSc) (by rw [hcur2]; exact rSc) (by rw [k2]; exact hD2)
    (fun hne => by
      obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hRH s2 k2 c2 rh2 scK2 sc2 hne
      exact ⟨_, q1, q2, q3, q4, q5, by rw [hcs2]; exact q6, fun e => by rw [e, hcs2]⟩)
    (fun hne => tm2 hne)
  have gsc : sched.schedule gS ar s2 a1 = sched.schedule st ar s2 a1 :=
    sched.schedule.guard_nodue ar s2 a1 (fun o h1 h2 => by rw [e2N]; exact ⟨nR o h1 h2, nW o h1 h2⟩)
      (fun hne => (tm2 hne).2) hT2 (fun hne => rhd s2 k2 c2 rh2 scK2 sc2 hne) hR2 hact2 hres.1 hres.2
  have gac : sched.activate_thread gS ar s4 a4 = sched.activate_thread st ar s4 a4 :=
    activate_thread.gw ar s4 a4 hcur4 ht' hy4 (nrm s4 e4N) rYt rSt (rR _ (by simp [layout.reg.FAULT_IP]))
      (rW _ (by simp [layout.reg.NEXT_IP])) (fun hr => absurd hr hnr) rSc (by rw [sc4]; exact rMx) rIq
  have gvc4 : vcpu.check gS ar s4 a4 (L.curW s) = vcpu.check st ar s4 a4 (L.curW s) :=
    vcpu.check.guard_nvm ar s4 a4 (L.curW s) rSt hnvm
  -- determinism of the real steps
  have dut : ∀ s1' a1', sched.update_timestamp st ar s a = ok (s1', a1') → s1' = s1 ∧ a1' = a1 := by
    intro s1' a1' e
    rw [eu] at e
    have e := ok_inj_ff e
    simp only [Prod.mk.injEq] at e
    exact ⟨e.1.symm, e.2.symm⟩
  have V : VexitAcc (gS := gS) (st := st) ar s a (L.curW s) (L.cscW s) (L.cpu s) :=
    { ut := PathObl.sched.update_timestamp.guard ar s a
        (nR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
        (nW _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
        (nR _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
        (nW _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
      now := fun s1' a1' e => by
        obtain ⟨rfl, rfl⟩ := dut s1' a1' e
        exact PathObl.sched.cur_time.guard s1' (ndR s1' e1N _ (by simp [layout.node.CUR_TIME])
          (by simp [layout.node.CUR_TIME]))
      cons := fun s1' a1' e => by
        obtain ⟨rfl, rfl⟩ := dut s1' a1' e
        exact PathObl.sched.consumed.guard s1' (ndR s1' e1N _ (by simp [layout.node.CONSUMED])
          (by simp [layout.node.CONSUMED]))
      suf := fun s1' a1' u e => by
        obtain ⟨rfl, rfl⟩ := dut s1' a1' e
        exact PathObl.sporadic.sufficient.guard ar s1' a1' (L.cscW s) u
          (hdC s1' (fun b hb hin => agS1 _ hcs b hb hin))
      aq := fun s1' a1' now' e => by
        obtain ⟨rfl, rfl⟩ := dut s1' a1' e
        have := localvm.awaken_quiet.guard (gS := gS) s1' now'
          (ndR s1' e1N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
          (fun hne => (tm1 hne).2)
          (ndR s1' e1N _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
          (fun hne => rhd s1' k1 c1 rh1 scK1 agS1 hne)
          (ndR s1' e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
        rwa [c1] at this
      chk := fun s1' a1' e => by
        obtain ⟨rfl, rfl⟩ := dut s1' a1' e
        exact gvc1
      cb := fun s1x a1x s2x a2x ex hcx => by
        obtain ⟨rfl, rfl⟩ := dut s1x a1x ex
        rw [evc0] at hcx
        have hcx := ok_inj_ff hcx
        simp only [Prod.mk.injEq] at hcx
        obtain ⟨rfl, rfl⟩ := hcx
        exact gcb
      fin := fun s1x a1x s2x a2x x' s3x a3x ex hcx e3 => by
        obtain ⟨rfl, rfl⟩ := dut s1x a1x ex
        rw [evc0] at hcx
        have hcx := ok_inj_ff hcx
        simp only [Prod.mk.injEq] at hcx
        obtain ⟨rfl, rfl⟩ := hcx
        rw [ecbr] at e3
        have e3 := ok_inj_ff e3
        simp only [Prod.mk.injEq] at e3
        obtain ⟨-, rfl, rfl⟩ := e3
        refine localvm.finish.guardP ar _ _ gsc fun s4' a4' e4 => ?_
        rw [esc] at e4
        have e4 := ok_inj_ff e4
        simp only [Prod.mk.injEq] at e4
        obtain ⟨rfl, rfl⟩ := e4
        refine ⟨gac, fun s5' a5' e5 => ?_⟩
        rw [activate_id ar s4 a4 (by rw [hcur4]; exact hy4) (by rw [hcur4]; exact hnr)] at e5
        have e5 := ok_inj_ff e5
        simp only [Prod.mk.injEq] at e5
        obtain ⟨rfl, rfl⟩ := e5
        refine ⟨ndR s4 e4N _ (by rw [curth_val]; omega) (by rw [curth_val]), fun t' et => ?_⟩
        rw [cur_thread_ok, hcur4] at et
        rw [← ok_inj_ff et]
        exact gvc4 }
  have hR : LvmRd st R s (L.curW s) (L.cscW s) :=
    { cur := nR _ (by rw [curth_val]; omega) (by rw [curth_val])
      curSc := nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      vcpu := rVc
      bntfn := rBn
      aff := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      yld := rYt
      sc := rSc
      scCore := rCore
      idle := nR _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
      dom := cR _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      curDom := hD1
      state := rSt
      maxA := by rw [hsct]; exact rMx
      inq := rIq
      act := nR _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      domTime := hD2
      ipi := nR _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]) }
  rw [vexit_acc ar s a v n (L.cscW s) (eq_of_spec_fd (sched.cur_sc.spec (L := L) s)) hR (fun _ => hRp) hRn V]
  exact h

/-- **An accepted VM exit with a pending exit on the guarded store** (module docstring): `vexit_accG_pW` with the
report's words `U` read and written. -/
theorem vexit_accG_p {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {v n : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRd st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hRn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (hU : ∀ x ∈ U, UsrW st T Cs H Sg Scs Z s x) (hpU : core.num.U64.wrapping_add v vcpu.PENDING ∈ U)
    (hbuf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK U b ⦄)
    (gU : ∀ x ∈ U, R x ∧ W x) (gV : VW R v) (gM : ∀ f b, vcpu.vmcs_addr v f = ok b → R b)
    (gSt : ∀ X, L.mem X (stA (L.curW s)) = sched.TS_RUNNING_VM → L.mem X (affA (L.curW s)) = L.cpu s →
      gS.write X (stA (L.curW s)) sched.TS_RUNNING = st.write X (stA (L.curW s)) sched.TS_RUNNING)
    (hpd : vcpu.get st s v vcpu.PENDING ≠ ok 0#u64)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    localvm.handle_vcpu_exit_local gS ar s a v n = ok (true, s', a') :=
  vexit_accG_pW ar hA hI gRd gWr hD1 hD2 hRn hU hpU hbuf (fun x hx => (gU x hx).2) (gU _ hpU).1 gV gM gSt hpd h

end main

end Fl4Proofs.P2

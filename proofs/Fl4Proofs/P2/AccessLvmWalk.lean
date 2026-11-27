/-
# P2 (line lvm, gen 6): **the acc walk of `local_vm_exit`, no pending exit** (`PENDING = 0` at the entry)

`vexit_accG_np`: from a state with P1's invariant (`BXI`), an accepted run of `handle_vcpu_exit_local` whose VCPU
has no pending exit is the same run on any store `gS` answering the reads of `IrqRd` (the timer interrupt's read
set: this core's node words, the current thread's words, the current SC, the release head and the earliest armed
thread), the two kernel-global words, the VCPU's `PENDING` and the bound notification's `TAIL_STATE` as `st`, and
the writes of `IrqWr` (other than the current thread's `STATE`, which this run does not write) as `st`
(`PathObl.GRd` / `PathObl.GWr`: `guard st R W` for `acc`, a checked store `gd` for `move`).

The run (`vexit_split`, `vexitTail_split`, `vfinish_split`): the head's checks at `s`, `update_timestamp` to `s1`,
`vcpu.check` of the current thread (nothing to report: `vcpu.check_np`, state unchanged), `check_budget` (sufficient:
`check_budget_suf`, unchanged), `schedule` (the quiet case: `irq_quiet_schedule` / `irq_quiet_pre` with no handler
writes, so `schedTail`), `activate_thread` (no yield, not restarting: `activate_id`), `vcpu.check` again (the VCPU
and notification words untouched by `schedTail`, `VFar`). Each guarded call is the real one at its state
(`VexitAcc`'s fields), and `vexit_acc` composes them; the walk is FootTimerIrqAcc's `irq_accG_quiet_walk` without
the interrupt handler.

`VFar` of the VCPU's `PENDING` word and of the bound notification's `TAIL_STATE` (outside every TCB, node and SC)
are hypotheses here, discharged from the layout in `AccessLvmOwn`.

No named premises.
-/
import Fl4Proofs.P2.AccessLvmSplit
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt)

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 32000000 in
/-- **An accepted VM exit with no pending exit on the guarded store** (module docstring). -/
theorem vexit_accG_np {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {v n : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (gRd : IrqOk st s → ∀ w, Aligned w → IrqRd st Z s w → R w)
    (gWr : IrqOk st s → ∀ w, Aligned w → IrqWr st Z s w → w ≠ stA (L.curW s) → W w)
    (hD1 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hD2 : IrqOk st s → R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME))
    (hRp : R (core.num.U64.wrapping_add v vcpu.PENDING))
    (hRn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (fP : VFar st T Cs Scs Z s (core.num.U64.wrapping_add v vcpu.PENDING))
    (fN : n ≠ 0#u64 → VFar st T Cs Scs Z s (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (hp0 : vcpu.get st s v vcpu.PENDING = ok 0#u64)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    localvm.handle_vcpu_exit_local gS ar s a v n = ok (true, s', a') := by
  obtain ⟨i3, hstv, hv0, eb, en, ep, hqf, eok, -, eq, et⟩ := vexit_split ar h
  rw [hp0] at ep
  have ei3 : i3 = 0#u64 := (ok_inj_ff ep).symm
  subst ei3
  have hnq := nq_true (hqf rfl)
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
  -- `vcpu.check` at `s1` reports nothing
  have eb1 : vcpu.bound st s1 (L.curW s) = ok v := by
    rw [vcpu_bound_congr (htcb1 hcT (by simp) (by simp))]; exact eb
  have en1 : obj.Tcb.bound_ntfn st (L.curW s) s1 = ok n := by
    rw [bound_ntfn_congr (by unfold boundA; exact htcb1 hcT (by simp) (by simp))]; exact en
  have ep1 : vcpu.get st s1 v vcpu.PENDING = ok 0#u64 := by
    rw [vcpu_get_congr (hout1 _ fP.1)]; exact hp0
  have hq1 : n ≠ 0#u64 → ∀ x, obj.Ntfn.state st n s1 = ok x → x ≠ obj.NTFN_ACTIVE := fun hn x ex =>
    hnq hn x (by rw [← ntfn_state_congr (hout1 _ (fN hn).1)]; exact ex)
  have evc1 := vcpu.check_np ar s1 a1 (L.curW s) v n eb1 hv0 ep1 en1 hq1
  rw [evc1] at evc
  obtain ⟨rfl, rfl⟩ : s1 = s2 ∧ a1 = a2 := by
    have e := ok_inj_ff evc
    simp only [Prod.mk.injEq] at e
    exact e
  -- `check_budget`
  have ecs1 : sched.cur_sc st s1 = ok (L.cscW s) := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s1)]
    congr 1
    show L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_SC) = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_SC)
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  have ecbr := ecb
  rw [check_budget_suf ar ecs1 ei2 eb4] at ecb
  obtain ⟨-, rfl, rfl⟩ : true = x ∧ s1 = s3 ∧ a1 = a3 := by
    have e := ok_inj_ff ecb
    simp only [Prod.mk.injEq] at e
    exact e
  -- `schedule`: the quiet case
  obtain ⟨-, hsch⟩ := irq_quiet_schedule ar (a3 := a1) hA hI eq eu enow erel edue (WritesIn.refl s1 _)
  obtain ⟨hT3, hR3, hact3⟩ := irq_quiet_pre ar hA hI eq eu enow erel edue (WritesIn.refl s1 _)
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
  have hfp := schedTail_fp ar hA s1 a1 (zc := Z (L.cscW s))
    (B := fun b => ((∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add (L.curW s) K) ∧
      b ≠ L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) ∧ b ≠ core.num.U64.wrapping_add v vcpu.PENDING ∧
      (n ≠ 0#u64 → b ≠ core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    hcC1 hN1 hT (fun b hb => (h0.omega b hb).ksb k1)
    (by rw [hcur1]; exact hcT) (by rw [hcur1, hsc1, hcs1]; exact hsct) (by rw [hcs1]; exact SCq.agree hcq agΩ1)
    (fun o ho h8 hz => by
      rw [e1N]
      refine ⟨⟨fun K hK => node_ne_field hN ho hcT ht' hK, fun e => hz ?_⟩,
        fun e => out_ne_node fP.1 hcC hN ho (congrArg UScalar.val e),
        fun hn e => out_ne_node (fN hn).1 hcC hN ho (congrArg UScalar.val e)⟩
      have e' := congrArg UScalar.val e
      rw [nodeAt_val hN ho, nodeAt_val hN (by rw [curth_val]; omega), curth_val] at e'
      omega)
    (fun b hb hin => by
      rw [hcs1] at hin
      have ho := h0.omega b (hcq.2.1 b hb hin)
      exact ⟨⟨fun K hK e => out_ne_field ho hcT ht' hK (congrArg UScalar.val e).symm,
        fun e => out_ne_node ho hcC hN (by rw [curth_val]; omega) (congrArg UScalar.val e).symm⟩,
        fun e => fP.2 _ hcs (e ▸ hin), fun hn e => (fN hn).2 _ hcs (e ▸ hin)⟩)
  rw [← hsch, esc, WP.spec_ok] at hfp
  have w14 := hfp
  have k4 : L.ksb s4 = L.ksb s := w14.1.trans k1
  have c4 : L.cpu s4 = L.cpu s := w14.2.1.trans c1
  have e4N : ∀ o, L.nodeAt s4 (L.cpu s4) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c4, nodeAt_of_ksb k4]
  have hcur4 : L.curW s4 = L.curW s := by
    have h1 := hcur1
    unfold LawfulStore.curW at h1 ⊢
    rw [e1N] at h1
    rw [w14.2.1, nodeAt_of_ksb w14.1, e1N,
      w14.mem_eq (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) (fun hb => hb.1.2 rfl)]
    exact h1
  have tK4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s4 (core.num.U64.wrapping_add (L.curW s) K) = L.mem s (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K hK h8 => (w14.mem_eq (field_aligned ht' hK h8) (fun hb => hb.1.1 K hK rfl)).trans (htcb1 hcT hK h8)
  have hy4 : L.mem s4 (yieldA (L.curW s)) = 0#u64 := by
    unfold yieldA
    rw [tK4 _ (by simp) (by simp)]
    exact hy0
  have hst4 : L.mem s4 (stA (L.curW s)) = L.mem s (stA (L.curW s)) := by
    rw [stA_eq, tK4 _ (by simp) (by simp)]
  have sc4 : L.mem s4 (scA (L.curW s)) = L.cscW s := by
    rw [scA_eq, tK4 _ (by simp) (by simp), ← scA_eq]; exact hsct
  have hN4 : NodePlaced st T s4 (L.cpu s4) := by rw [c4]; exact hN.ksb k4
  have hnr : L.mem s4 (stA (L.curW s)) ≠ sched.TS_RESTART := by
    rw [hst4, hstv]; simp [sched.TS_RUNNING_VM, sched.TS_RESTART]
  -- `activate_thread` changes nothing
  rw [activate_id ar s4 a4 (by rw [hcur4]; exact hy4) (by rw [hcur4]; exact hnr)] at eac
  obtain ⟨rfl, rfl⟩ : s4 = s5 ∧ a4 = a5 := by
    have e := ok_inj_ff eac
    simp only [Prod.mk.injEq] at e
    exact e
  rw [cur_thread_ok, hcur4] at ett
  have et' := ok_inj_ff ett
  subst et'
  -- `vcpu.check` at `s4`
  have eb4' : vcpu.bound st s4 (L.curW s) = ok v := by
    rw [vcpu_bound_congr (tK4 _ (by simp) (by simp))]; exact eb
  have en4 : obj.Tcb.bound_ntfn st (L.curW s) s4 = ok n := by
    rw [bound_ntfn_congr (by unfold boundA; exact tK4 _ (by simp) (by simp))]; exact en
  have pk4 : L.mem s4 (core.num.U64.wrapping_add v vcpu.PENDING) =
      L.mem s (core.num.U64.wrapping_add v vcpu.PENDING) :=
    (w14.mem_eq fP.1.1 (fun hb => hb.2.1 rfl)).trans (hout1 _ fP.1)
  have ep4 : vcpu.get st s4 v vcpu.PENDING = ok 0#u64 := by
    rw [vcpu_get_congr pk4]; exact hp0
  have nk4 : n ≠ 0#u64 → L.mem s4 (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) =
      L.mem s (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) := fun hn =>
    (w14.mem_eq (fN hn).1.1 (fun hb => hb.2.2 hn rfl)).trans (hout1 _ (fN hn).1)
  have hq4 : n ≠ 0#u64 → ∀ x, obj.Ntfn.state st n s4 = ok x → x ≠ obj.NTFN_ACTIVE := fun hn x ex =>
    hnq hn x (by rw [← ntfn_state_congr (nk4 hn)]; exact ex)
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
  have hdC : ∀ Y : S, (∀ b ∈ Ω, L.mem Y b = L.mem s b) → RdHead (L := L) R Y (L.cscW s) := fun Y ag =>
    hSc.head ((SCq.agree hcq ag).1 (by
      unfold LawfulStore.rmax; rw [ag _ hmaxΩ]; exact hmx0))
  -- the release head
  have hRH : ∀ Y : S, L.ksb Y = L.ksb s → L.cpu Y = L.cpu s →
      L.mem Y (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) →
      (∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y)) → (∀ b ∈ Ω, L.mem Y b = L.mem s b) →
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
    refine ⟨r1, gRd _ ?_ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl rfl⟩)))), SCq.agree hqr ag, ?_,
      fun b hb ha => gRd _ ha (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inr hb⟩)))), fun hn b hb => ?_⟩
    · rw [scA_eq]; exact field_aligned (hT _ r1) (by simp) (by simp)
    · unfold LawfulStore.rmax
      rw [ag _ (hqr.2.1 _ hqr.2.2.2.2 hqr.2.2.2.1)]; exact r5
    · have := hO.scDisj _ r4 _ hcs hn
      unfold Outside; unfold InSC at hb; omega
  have rhd : ∀ Y : S, L.ksb Y = L.ksb s → L.cpu Y = L.cpu s →
      L.mem Y (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) = L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) →
      (∀ y ∈ T, L.mem Y (scA y) = L.mem s (scA y)) → (∀ b ∈ Ω, L.mem Y b = L.mem s b) →
      L.mem Y (rhA (L := L) Y) ≠ 0#u64 → R (scA (L.mem Y (rhA (L := L) Y))) ∧
        RdHead (L := L) R Y (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) := by
    intro Y kY cY eh es ag hne
    obtain ⟨-, q2, q3, q4, q5, -⟩ := hRH Y kY cY eh es ag hne
    exact ⟨q2, PathObl.ScAcc.head (W := fun _ => True) ⟨fun b ha hb => q5 b hb ha, fun _ _ _ => trivial, trivial⟩ (q3.1 q4)⟩
  have scK1 : ∀ y ∈ T, L.mem s1 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact htcb1 hy (by simp) (by simp)
  have rh1 : L.mem s1 (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) :=
    hnode1 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  -- the earliest timer
  have tmT : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ∈ T ∧
      R (core.num.U64.wrapping_add (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) 3528#u64) := by
    intro hne
    have q1 := (tmin_facts (BXI.blk hI) hcC hne).1
    exact ⟨q1, gRd _ (field_aligned (hT _ q1) (by simp) (by simp))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, Or.inl ⟨3528#u64, by simp, rfl⟩⟩)))))⟩
  have tm1e : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have tm1 : L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN) ∈ T ∧
      R (tdA (L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN))) := fun hne => by
    rw [tm1e] at hne ⊢
    exact tmT hne
  -- the guarded calls
  have hres := resume_hsw_hfr (gS := gS) ar hA s1 a1 (zc := Z (L.cscW s)) hcC1 hN1 hT
    (fun b hb => (h0.omega b hb).ksb k1) (by rw [hcur1]; exact hcT) (by rw [hcur1, hsc1, hcs1]; exact hsct)
    (by rw [hcs1]; exact SCq.agree hcq agΩ1)
    (by rw [hcs1]; unfold LawfulStore.rmax; rw [agΩ1 _ hmaxΩ]; exact hmx0)
    (fun o h1 h2 => by rw [e1N]; exact ⟨nR o h1 h2, nW o h1 h2⟩)
    (by rw [hcs1]; exact hSc) (by rw [hcur1]; exact rSc) (by rw [k1]; exact hD2)
    (fun hne => by
      obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hRH s1 k1 c1 rh1 scK1 agΩ1 hne
      exact ⟨_, q1, q2, q3, q4, q5, by rw [hcs1]; exact q6, fun e => by rw [e, hcs1]⟩)
    (fun hne => tm1 hne)
  have gsc : sched.schedule gS ar s1 a1 = sched.schedule st ar s1 a1 :=
    sched.schedule.guard_nodue ar s1 a1 (fun o h1 h2 => by rw [e1N]; exact ⟨nR o h1 h2, nW o h1 h2⟩)
      (fun hne => (tm1 hne).2) hT3 (fun hne => rhd s1 k1 c1 rh1 scK1 agΩ1 hne) hR3 hact3 hres.1 hres.2
  have gac : sched.activate_thread gS ar s4 a4 = sched.activate_thread st ar s4 a4 :=
    activate_thread.gw ar s4 a4 hcur4 ht' hy4 (nrm s4 e4N) rYt rSt (rR _ (by simp [layout.reg.FAULT_IP]))
      (rW _ (by simp [layout.reg.NEXT_IP])) (fun hr => absurd hr hnr) rSc (by rw [sc4]; exact rMx) rIq
  have gvc4 : vcpu.check gS ar s4 a4 (L.curW s) = vcpu.check st ar s4 a4 (L.curW s) :=
    vcpu.check.guard_vmq ar s4 a4 (L.curW s) v n rSt rVc rBn hRp hRn eb4' hv0 ep4 en4 hq4
  have gvc1 : vcpu.check gS ar s1 a1 (L.curW s) = vcpu.check st ar s1 a1 (L.curW s) :=
    vcpu.check.guard_vmq ar s1 a1 (L.curW s) v n rSt rVc rBn hRp hRn eb1 hv0 ep1 en1 hq1
  have gcb : sched.check_budget gS ar s1 a1 = sched.check_budget st ar s1 a1 :=
    sched.check_budget.guard_suf ar s1 a1
      (ndR s1 e1N _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      (ndR s1 e1N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
      (fun sc e => by
        rw [ecs1] at e
        rw [← ok_inj_ff e]
        exact hdC s1 agΩ1)
      (fun sc c e1 e2 => by
        rw [ecs1] at e1
        rw [ei2] at e2
        rw [← ok_inj_ff e1, ← ok_inj_ff e2]
        exact eb4)
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
        exact PathObl.sporadic.sufficient.guard ar s1' a1' (L.cscW s) u (hdC s1' agΩ1)
      aq := fun s1' a1' now' e => by
        obtain ⟨rfl, rfl⟩ := dut s1' a1' e
        have := localvm.awaken_quiet.guard (gS := gS) s1' now'
          (ndR s1' e1N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
          (fun hne => (tm1 hne).2)
          (ndR s1' e1N _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
          (fun hne => rhd s1' k1 c1 rh1 scK1 agΩ1 hne)
          (ndR s1' e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
        rwa [c1] at this
      chk := fun s1' a1' e => by
        obtain ⟨rfl, rfl⟩ := dut s1' a1' e
        exact gvc1
      cb := fun s1' a1' s2' a2' e e2 => by
        obtain ⟨rfl, rfl⟩ := dut s1' a1' e
        rw [evc1] at e2
        have e2 := ok_inj_ff e2
        simp only [Prod.mk.injEq] at e2
        obtain ⟨rfl, rfl⟩ := e2
        exact gcb
      fin := fun s1' a1' s2' a2' x' s3' a3' e e2 e3 => by
        obtain ⟨rfl, rfl⟩ := dut s1' a1' e
        rw [evc1] at e2
        have e2 := ok_inj_ff e2
        simp only [Prod.mk.injEq] at e2
        obtain ⟨rfl, rfl⟩ := e2
        rw [ecbr] at e3
        have e3 := ok_inj_ff e3
        simp only [Prod.mk.injEq] at e3
        obtain ⟨-, rfl, rfl⟩ := e3
        refine localvm.finish.guardP ar s1' a1' gsc fun s4' a4' e4 => ?_
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

end main

end Fl4Proofs.P2

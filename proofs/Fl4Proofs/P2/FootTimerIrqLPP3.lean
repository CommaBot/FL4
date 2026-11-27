/-
# P2 (p2lf gen13): the timer interrupt local path with `hBA` proved from entry facts

* `fire_ibFr`: on a fire-case run, `update_timestamp` (this core's `CUR_TIME` / `CONSUMED`), `check_budget` (a
  sufficient budget: writes nothing, `check_budget_suf`) and the timer `handle_interrupt` (this core's
  `REPROGRAM` / `ARMED`, `handle_interrupt_timer_writes`) keep the buffer-lookup frame (P1 `IbFr`: `ksb` and the
  three `lookup_ipc_buffer` words of every TCB).
* `fire_bufAt3`: `BufAt` at the state after `handle_interrupt` from P1 `UserOK` and the IPC-buffer lookup fact at
  the entry state (`BufAt.of_user` at `s`, then `BufAt.of_fr` along `fire_ibFr`).
* `irq_localPathP3`: `irq_localPathP2` with `hBA` [P] replaced by the entry premise `hUB` [J] and `SlotLay` narrowed
  to `SlotLayV` (slot 1's two words, the only slot words the switch block reads).

Premises of `irq_localPathP3`: `hp` [P], `hz` [W], `hm` [P], `hro` [W], `IrqEnt`'s [J] parts, `hEU` [J], `hlk` [P],
`hPL` [P], `hOL` [J], `hSL` [J] (`SlotLayV`; from P3 by `slotLayV_of_JAtZ`, P2/FootTimerIrqSlotJ), plus

* `hUB` [J] (at every entry state: some user-word set `U` with P1 `UserOK st T Cs Ω H U s` and every TCB's
  `lookup_ipc_buffer` landing in `U` (`BufOK U`). Sources: P1 `EntryHyps0.blkU` (UserOK at every `BXI` state) with
  `XferHyps.buf` / `EntryHyps0.bufAt`; P3 `JAtZ.bufAtJ` (BufAt at a `JAtZ` state, `U = BufU Z σ`, for
  `T = Heap.tcbs H`).)
-/
import Fl4Proofs.P2.FootTimerIrqLPP2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section ba
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The fire-case prefix keeps the buffer-lookup frame** (module docstring). -/
theorem fire_ibFr (hA : P0.ArchTotal ar) {s s1 s2 s3 : S} {a a1 a2 a3 : A} {mx irq i2 : U64} {x : Bool}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (ei2 : sched.consumed st s1 = ok i2)
    (eb4 : sporadic.sufficient st ar s1 a1 (L.cscW s) i2 = ok true)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2))
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (ehi : interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3)) :
    IbFr (L := L) T s s3 := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
  simp only at er
  have k1 : L.ksb s1 = L.ksb s := by rw [er, utW_ksb]
  have c1 : L.cpu s1 = L.cpu s := by rw [er, utW_cpu]
  have m1 : ∀ b, Aligned b → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s → L.mem s1 b = L.mem s b :=
    fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [er]; exact utW_placed hN n1
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
  -- the IRQ's state word after the timestamp update
  have hirq : irq.val ≤ 127 := by
    rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
    have e := ok_inj_ff emx
    subst e
    scalar_tac
  obtain ⟨i, hi, hiv⟩ : ∃ i, interrupt.state_off irq = ok i ∧ i.val = 224 + 8 * irq.val := by
    unfold interrupt.state_off
    simp only [lift, bind_ok]
    rw [eq_of_spec_fd layout.ks.IRQ_STATE.spec]
    simp only [bind_ok]
    refine ⟨_, rfl, ?_⟩
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    try omega
  have hi' : i.val < 13568 := by omega
  have hi8 : i.val % 8 = 0 := by omega
  have eis1 : interrupt.irq_state st s1 irq = ok interrupt.IRQ_TIMER := by
    rw [← ei1]
    unfold interrupt.irq_state
    rw [hi]
    simp only [bind_ok]
    rw [eq_of_spec_fd (obj.ks_get.spec (L := L) s1 i), eq_of_spec_fd (obj.ks_get.spec (L := L) s i), k1,
      m1 _ (ks_aligned hN hi' hi8) (ks_ne_node hN hi' (by simp [layout.node.CUR_TIME]))
        (ks_ne_node hN hi' (by simp [layout.node.CONSUMED]))]
  -- `check_budget`
  have ecs1 : sched.cur_sc st s1 = ok (L.cscW s) := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s1)]
    congr 1
    show L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.CUR_SC) = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_SC)
    rw [e1N]
    exact hnode1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  rw [check_budget_suf ar ecs1 ei2 eb4] at ecb
  have e2 := ok_inj_ff ecb
  simp only [Prod.mk.injEq] at e2
  obtain ⟨-, e2s, e2a⟩ := e2
  subst e2s e2a
  -- `handle_interrupt`: `s1 → s3`
  obtain ⟨s2', eh2, eh3, -⟩ := handle_interrupt_timer ar emx hle eis1 ehi
  have w13 : WritesIn st s1 s3 (HW st s1) := handle_interrupt_timer_writes hN1 eh2 eh3
  have k3 : L.ksb s3 = L.ksb s := w13.1.trans k1
  have htcb3 : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      L.mem s3 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun hy hK h8 => (hw_tcb hT hN1 w13 hy hK h8).trans (htcb1 hy hK h8)
  refine ⟨k3, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · exact htcb3 (K := 3512#u64) hy (by simp) (by simp)
  · rw [sbWordA_eq]; exact htcb3 hy (by simp) (by simp)
  · rw [sbWordA8_eq]; exact htcb3 hy (by simp) (by simp)

/-- **`BufAt` after the timer handler of a fire-case run** (module docstring). -/
theorem fire_bufAt3 (hA : P0.ArchTotal ar) {s s1 s2 s3 : S} {a a1 a2 a3 : A} {mx irq i2 : U64} {x : Bool}
    {U : Set U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s)
    (hb : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (ei2 : sched.consumed st s1 = ok i2)
    (eb4 : sporadic.sufficient st ar s1 a1 (L.cscW s) i2 = ok true)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2))
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (ehi : interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3)) :
    BufAt st T Cs H Sg Scs Z U s3 :=
  (BufAt.of_user hU (BXI.blk hI) hb).of_fr (fire_ibFr ar hA hI eu ei2 eb4 ecb emx hle ei1 ehi)

/-- **`hBA` of `irq_acc_fire_wk2` / `irq_move_fire_wk2`** (the run form) from the entry facts. -/
theorem irq_bufAt_run (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    {U : Set U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s)
    (hb : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hq : IrqFire st ar s a) (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    ∀ s1 a1 x s2 a2 s3 a3, sched.update_timestamp st ar s a = ok (s1, a1) →
      sched.check_budget st ar s1 a1 = ok (x, s2, a2) → interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) →
      BufAt st T Cs H Sg Scs Z U s3 := by
  intro s1' a1' x' s2' a2' s3' a3' eu' ecb' ehi'
  obtain ⟨mx, now, i2, tip, x, s1, s2, s3, a1, a2, a3, emx, hle, ei1, -, -, -, -, eu, -, -, ei2, eb4, -, -, -,
    -⟩ := fire_eqs ar hA hq h
  rw [eu] at eu'
  have e1 := ok_inj_ff eu'
  simp only [Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  exact fire_bufAt3 ar hA hI hU hb eu ei2 eb4 ecb' emx hle ei1 ehi'

end ba

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- **The timer interrupt is a local path, `hBA` proved** (module docstring). -/
noncomputable def irq_localPathP3 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR K st lk))
    (hEU : ∀ s b v, IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ K.user → Aligned b →
      IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) (hOL : ObjLay K H Rp)
    (hUB : ∀ s, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s →
      ∃ U : Set U64, UserOK st T Cs Ω H U s ∧ ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hSL : ∀ s, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → SlotLayV K st T s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  irq_localPathW ar hA hK hUO hp hz hm hro hEU hlk
    (fun s a s1 a1 hE hf hw h => by
      obtain ⟨U, hU, hb⟩ := hUB s hE
      exact irq_acc_fire_wk2 ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth hOL hPL
        (irq_bufAt_run ar hA hE.ent.inv hU hb hf h) (hSL s hE) hf hw h)
    (fun s a s1 a1 hE hf hw h => by
      obtain ⟨U, hU, hb⟩ := hUB s hE
      exact irq_move_fire_wk2 ar hA hK hUO hp hE.k hE.ent.ly hE.ent.aff hE.ent.nth hOL hPL
        (irq_bufAt_run ar hA hE.ent.inv hU hb hf h) hf hw h)

end

end Fl4Proofs.P2

/-
# P2 (line lvm, gen 4): `vcpu.report` / `vcpu.check` on a guarded store (`PathObl.acc` of the VM exit's work)

`handle_vcpu_exit_local`'s tail (`AccessLvm.vexitTail`) runs `vcpu.check` of the current thread, which, for a
thread in `TS_RUNNING_VM` with a pending exit or an active bound notification, runs `vcpu.report` (461 lines of
extracted text, four loops, `finish_notification`). Here: on any store `gS` answering the listed reads (`R`) and
writes (`W`) as `st` (`GRd` / `GWr`), `report` and `check` equal the real ones.

* Stateless guards (`VW`: the VCPU's 0x8000 bytes are readable): `lv_get`, `lv_set`, `lv_vmcs`, the four loop
  bodies and loops (`lv_loop0` … `lv_loop3`).
* **`vcpu.report.guardP`** (in `AccessLvmRepR`): for any state predicate `P` that the report's four write kinds keep (P1's
  `RepSteps`, the buffer the one looked up) and at which the final `set_thread_state TS_RUNNING` is guarded
  (`hfin`), `report gS = report st`. The frame (`P`) is the caller's: `set_thread_state` reads the thread's SC's
  `REFILL_MAX`, a word whose address the report's writes must not change.
* **`vcpu.check.guardP`**: `check` of a `TS_RUNNING_VM` thread, from `report`'s and the notification words.

No named premises: every hypothesis is about the guarded store's read / write sets or the caller's `P`.
-/
import Fl4Proofs.P2.AccessLvm
import Fl4Proofs.P1.VcpuReport
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

/-- The words of the VCPU `v` (0x8000 bytes) are in `P`. -/
def VW (P : U64 → Prop) (v : U64) : Prop := ∀ o : U64, o.val < 32768 → P (core.num.U64.wrapping_add v o)

theorem lv_mulv {x y z : U64} (h : x * y = ok z) (hb : x.val * y.val ≤ U64.max) : z.val = x.val * y.val := by
  obtain ⟨w, hw, hwv⟩ := spec_ex_fd (U64.mul_spec (x := x) (y := y) hb)
  rw [hw] at h; cases ok_inj_ff h; exact hwv

theorem lv_addv {x y z : U64} (h : x + y = ok z) (hb : x.val + y.val ≤ U64.max) : z.val = x.val + y.val := by
  obtain ⟨w, hw, hwv⟩ := spec_ex_fd (U64.add_spec (x := x) (y := y) hb)
  rw [hw] at h; cases ok_inj_ff h; exact hwv

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [GRd gS st R] [GWr gS st W]

theorem lv_get {v : U64} (hV : VW R v) (s : S) (o : U64) (ho : o.val < 32768) :
    vcpu.get gS s v o = vcpu.get st s v o :=
  Fl4Proofs.P2.vcpu.get.guard s v o (hV o ho)

theorem lv_set (s : S) (v x : U64) (h : W (core.num.U64.wrapping_add v vcpu.PENDING)) :
    vcpu.set gS s v vcpu.PENDING x = vcpu.set st s v vcpu.PENDING x := by
  unfold vcpu.set
  simp only [lift, bind_ok]
  exact gst_write h

theorem lv_vmcs {v : U64} (h : ∀ f a, vcpu.vmcs_addr v f = ok a → R a) (s : S) (f : U64) :
    vcpu.read_vmcs gS s v f = vcpu.read_vmcs st s v f := by
  unfold vcpu.read_vmcs
  exact bind_guard_congr rfl fun a ha => gst_read (h f a ha)

/-- `report_loop0`'s body, for every state and index. -/
theorem lv_body0 {t v b : U64} {pending saved : Bool} (hV : pending = true ∨ saved = true → VW R v) (hWt : Regs W t) (hBW : BufW W b)
    (s : S) (i : U64) :
    vcpu.report_loop0.body gS t v pending b saved s i = vcpu.report_loop0.body st t v pending b saved s i := by
  unfold vcpu.report_loop0.body
  by_cases hi : i < vcpu.NUM_MRS
  · have hi' : i.val < 30 := by simpa using hi
    simp only [hi, ↓reduceIte]
    have gmr : ∀ (s' : S) (x : U64), msg.set_mr gS s' t b i x = msg.set_mr st s' t b i x :=
      fun s' x => msg.set_mr.guard s' t b i x (by omega) hWt hBW
    have hoff : ∀ i1 i2 : U64, i * 8#u64 = ok i1 → vcpu.EXIT + i1 = ok i2 → i2.val < 32768 := by
      intro i1 i2 h1 h2
      have e1 := lv_mulv h1 (by scalar_tac)
      have e2 := lv_addv h2 (by scalar_tac)
      scalar_tac
    cases pending <;> cases saved <;> simp only [Bool.false_eq_true, eq_self_iff_true, if_true, if_false, ↓reduceIte]
    · rw [gmr]
    all_goals
      refine bind_guard_congr rfl fun i1 h1 => bind_guard_congr rfl fun i2 h2 => ?_
      rw [lv_get (hV (by simp)) s i2 (hoff i1 i2 h1 h2)]
      refine bind_guard_congr rfl fun i3 _ => ?_
      rw [gmr]
  · simp only [hi, ↓reduceIte]

theorem lv_body2 {t v b : U64} {pending saved : Bool} (hV : pending = true ∨ saved = true → VW R v) (hWt : Regs W t) (hBW : BufW W b)
    (s : S) (i : U64) :
    vcpu.report_loop2.body gS t v pending b saved s i = vcpu.report_loop2.body st t v pending b saved s i := by
  unfold vcpu.report_loop2.body
  by_cases hi : i < vcpu.NUM_MRS
  · have hi' : i.val < 30 := by simpa using hi
    simp only [hi, ↓reduceIte]
    have gmr : ∀ (s' : S) (x : U64), msg.set_mr gS s' t b i x = msg.set_mr st s' t b i x :=
      fun s' x => msg.set_mr.guard s' t b i x (by omega) hWt hBW
    have hoff : ∀ i1 i2 : U64, i * 8#u64 = ok i1 → vcpu.EXIT + i1 = ok i2 → i2.val < 32768 := by
      intro i1 i2 h1 h2
      have e1 := lv_mulv h1 (by scalar_tac)
      have e2 := lv_addv h2 (by scalar_tac)
      scalar_tac
    cases pending <;> cases saved <;> simp only [Bool.false_eq_true, eq_self_iff_true, if_true, if_false, ↓reduceIte]
    · rw [gmr]
    all_goals
      refine bind_guard_congr rfl fun i1 h1 => bind_guard_congr rfl fun i2 h2 => ?_
      rw [lv_get (hV (by simp)) s i2 (hoff i1 i2 h1 h2)]
      refine bind_guard_congr rfl fun i3 _ => ?_
      rw [gmr]
  · simp only [hi, ↓reduceIte]

theorem lv_body1 {t v b : U64} (hV : VW R v) (hWt : Regs W t) (hBW : BufW W b) (s : S) (j : U64) :
    vcpu.report_loop1.body gS t v b s j = vcpu.report_loop1.body st t v b s j := by
  unfold vcpu.report_loop1.body
  by_cases hj : j < 15#u64
  · have hj' : j.val < 15 := by simpa using hj
    simp only [hj, ↓reduceIte]
    refine bind_guard_congr rfl fun i hi => bind_guard_congr rfl fun i1 h1 => bind_guard_congr rfl fun i2 h2 => ?_
    have e0 := lv_addv hi (by scalar_tac)
    have e1 := lv_mulv h1 (by scalar_tac)
    have e2 := lv_addv h2 (by scalar_tac)
    rw [lv_get hV s i2 (by scalar_tac)]
    refine bind_guard_congr rfl fun i3 _ => ?_
    rw [msg.set_mr.guard s t b i i3 (by scalar_tac) hWt hBW]
  · simp only [hj, ↓reduceIte]

theorem lv_body3 {t v b : U64} (hV : VW R v) (hWt : Regs W t) (hBW : BufW W b) (s : S) (j : U64) :
    vcpu.report_loop3.body gS t v b s j = vcpu.report_loop3.body st t v b s j := by
  unfold vcpu.report_loop3.body
  by_cases hj : j < 15#u64
  · have hj' : j.val < 15 := by simpa using hj
    simp only [hj, ↓reduceIte]
    refine bind_guard_congr rfl fun i hi => bind_guard_congr rfl fun i1 h1 => bind_guard_congr rfl fun i2 h2 => ?_
    have e0 := lv_addv hi (by scalar_tac)
    have e1 := lv_mulv h1 (by scalar_tac)
    have e2 := lv_addv h2 (by scalar_tac)
    rw [lv_get hV s i2 (by scalar_tac)]
    refine bind_guard_congr rfl fun i3 _ => ?_
    rw [msg.set_mr.guard s t b i i3 (by scalar_tac) hWt hBW]
  · simp only [hj, ↓reduceIte]

theorem lv_loop0 {t v b : U64} {pending saved : Bool} (hV : pending = true ∨ saved = true → VW R v) (hWt : Regs W t) (hBW : BufW W b)
    (s : S) (i : U64) :
    vcpu.report_loop0 gS s t v pending b saved i = vcpu.report_loop0 st s t v pending b saved i := by
  unfold vcpu.report_loop0
  congr 1; funext x; exact lv_body0 hV hWt hBW x.1 x.2

theorem lv_loop1 {t v b : U64} (hV : VW R v) (hWt : Regs W t) (hBW : BufW W b) (s : S) (j : U64) :
    vcpu.report_loop1 gS s t v b j = vcpu.report_loop1 st s t v b j := by
  unfold vcpu.report_loop1
  congr 1; funext x; exact lv_body1 hV hWt hBW x.1 x.2

theorem lv_loop2 {t v b : U64} {pending saved : Bool} (hV : pending = true ∨ saved = true → VW R v) (hWt : Regs W t) (hBW : BufW W b)
    (s : S) (i : U64) :
    vcpu.report_loop2 gS s t v pending b saved i = vcpu.report_loop2 st s t v pending b saved i := by
  unfold vcpu.report_loop2
  congr 1; funext x; exact lv_body2 hV hWt hBW x.1 x.2

theorem lv_loop3 {t v b : U64} (hV : VW R v) (hWt : Regs W t) (hBW : BufW W b) (s : S) (j : U64) :
    vcpu.report_loop3 gS s t v b j = vcpu.report_loop3 st s t v b j := by
  unfold vcpu.report_loop3
  congr 1; funext x; exact lv_body3 hV hWt hBW x.1 x.2

end


theorem lv_mul_ok {x y z : U64} (hb : x.val * y.val ≤ U64.max) (hz : z.val = x.val * y.val) : x * y = ok z := by
  obtain ⟨w, hw, hwv⟩ := spec_ex_fd (U64.mul_spec (x := x) (y := y) hb)
  rw [hw, UScalar.eq_of_val_eq (hwv.trans hz.symm)]

theorem lv_add_ok {x y z : U64} (hb : x.val + y.val ≤ U64.max) (hz : z.val = x.val + y.val) : x + y = ok z := by
  obtain ⟨w, hw, hwv⟩ := spec_ex_fd (U64.add_spec (x := x) (y := y) hb)
  rw [hw, UScalar.eq_of_val_eq (hwv.trans hz.symm)]

/-- The words `vcpu.report` of thread `t` with VCPU `v` and IPC buffer `b` reads and writes, besides the final
`set_thread_state`: `t`'s registers, `b`'s words, `v`'s words (read; its VMCS shadow through `vmcs_addr`) and
`v.PENDING` (written). -/
structure RepG (R W : U64 → Prop) (t v b : U64) : Prop where
  regR : Regs R t
  regW : Regs W t
  bufW : BufW W b
  vR : v ≠ 0#u64 → VW R v
  vmcs : v ≠ 0#u64 → ∀ f a, vcpu.vmcs_addr v f = ok a → R a
  pW : v ≠ 0#u64 → W (core.num.U64.wrapping_add v vcpu.PENDING)

section rep
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [GRd gS st R] [GWr gS st W]

theorem lv_ntfn_set_state (s : S) (n x : U64) (hr : R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (hw : W (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE)) :
    obj.Ntfn.set_state gS n s x = obj.Ntfn.set_state st n s x := by
  unfold obj.Ntfn.set_state
  unfold obj.Ntfn.tail
  rw [obj.Ntfn.tail_state.guard n s hr]
  refine bind_guard_congr rfl fun _ _ => ?_
  simp only [lift, bind_ok]
  rw [obj.Ntfn.set_tail_state.guard n s _ hw]

/-- **`vcpu.check` on a guarded store**: its own reads (the thread's state, VCPU and bound-notification words,
the VCPU's `PENDING`, the notification's state and badge) and the notification write are listed; each
`report` it runs (at the entry state, or after clearing the notification) is guarded (`hrep`, from
`vcpu.report.guardP`). -/
theorem vcpu.check.guardP {A : Type} (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (hst : R (stA t)) (hvw : R (core.num.U64.wrapping_add t 3664#u64))
    (hbn : R (core.num.U64.wrapping_add t 3368#u64))
    (hp : ∀ v, vcpu.bound st s t = ok v → v ≠ 0#u64 → R (core.num.U64.wrapping_add v vcpu.PENDING))
    (hn : ∀ n, obj.Tcb.bound_ntfn st t s = ok n → n ≠ 0#u64 →
      R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) ∧ R (core.num.U64.wrapping_add n layout.ntfn.BADGE) ∧
      W (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (hrep : ∀ s' badge, (s' = s ∨ ∃ n, obj.Tcb.bound_ntfn st t s = ok n ∧
        obj.Ntfn.set_state st n s obj.NTFN_IDLE = ok s') →
      vcpu.report gS ar s' a t badge = vcpu.report st ar s' a t badge) :
    vcpu.check gS ar s a t = vcpu.check st ar s a t := by
  have ntf : ∀ (v : U64), (do
      let i1 ← obj.Tcb.bound_ntfn gS t s
      if i1 != 0#u64 then
        let i2 ← obj.Ntfn.state gS i1 s
        if i2 = obj.NTFN_ACTIVE then
          let badge ← obj.Ntfn.badge gS i1 s
          let s1 ← obj.Ntfn.set_state gS i1 s obj.NTFN_IDLE
          let s2 ← vcpu.report gS ar s1 a t badge
          ok (s2, a)
        else if v = 0#u64 then
          let s1 ← vcpu.report gS ar s a t 0#u64
          ok (s1, a)
        else ok (s, a)
      else if v = 0#u64 then
        let s1 ← vcpu.report gS ar s a t 0#u64
        ok (s1, a)
      else ok (s, a) : Result (S × A)) = (do
      let i1 ← obj.Tcb.bound_ntfn st t s
      if i1 != 0#u64 then
        let i2 ← obj.Ntfn.state st i1 s
        if i2 = obj.NTFN_ACTIVE then
          let badge ← obj.Ntfn.badge st i1 s
          let s1 ← obj.Ntfn.set_state st i1 s obj.NTFN_IDLE
          let s2 ← vcpu.report st ar s1 a t badge
          ok (s2, a)
        else if v = 0#u64 then
          let s1 ← vcpu.report st ar s a t 0#u64
          ok (s1, a)
        else ok (s, a)
      else if v = 0#u64 then
        let s1 ← vcpu.report st ar s a t 0#u64
        ok (s1, a)
      else ok (s, a)) := by
    intro v
    have r0 := hrep s 0#u64 (Or.inl rfl)
    rw [obj.Tcb.bound_ntfn.guard _ s hbn]
    refine bind_guard_congr rfl fun n hn0 => ?_
    refine ite_congr rfl (fun h1 => ?_) (fun _ => by rw [r0])
    have hn1 := hn n hn0 (by simpa using h1)
    rw [obj.Ntfn.state.guard n s hn1.1]
    refine bind_guard_congr rfl fun i2 _ => ?_
    refine ite_congr rfl (fun _ => ?_) (fun _ => by rw [r0])
    rw [obj.Ntfn.badge.guard n s hn1.2.1]
    refine bind_guard_congr rfl fun bd _ => ?_
    rw [lv_ntfn_set_state s n _ hn1.1 hn1.2.2]
    refine bind_guard_congr rfl fun s1 hs1 => ?_
    rw [hrep s1 bd (Or.inr ⟨n, hn0, hs1⟩)]
  unfold vcpu.check
  rw [obj.Tcb.state.guard _ s hst]
  refine bind_guard_congr rfl fun i _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  rw [vcpu.bound.guardT s t hvw]
  refine bind_guard_congr rfl fun v hv => ?_
  refine ite_congr rfl (fun h0 => ?_) (fun _ => ntf v)
  rw [vcpu.get.guard s v _ (hp v hv (by simpa using h0))]
  refine bind_guard_congr rfl fun i1 _ => ?_
  refine ite_congr rfl (fun _ => by rw [hrep s 0#u64 (Or.inl rfl)]) (fun _ => ntf v)

end rep

end Fl4Proofs.P2.PathObl

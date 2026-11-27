/-
# P2 (line lvm, gen 4): **`acc` of `local_vm_exit`** (`handle_vcpu_exit_local` on a guarded store)

Gen 3 split the body into its checks (`vexitHead`, `vexit_acc_head`) and its work (`vexitTail`). Here the work:
`update_timestamp`, the budget and wake checks, `vcpu.check` (→ `vcpu.report`, gen 4's `AccessLvmRep*`),
`check_budget`, `localvm.finish`. `VexitAcc` lists, for each step, the guard fact at the state the real run
reaches there; **`vexit_acc`** composes them with the head into `PathObl.acc`'s equation for the whole body.
Each field is discharged by an existing guard lemma, given the read / write sets:

| field | discharged by |
|---|---|
| `ut` | `sched.update_timestamp.guard` (node `CUR_TIME` / `CONSUMED`, read and write) |
| `now`, `cons` | `sched.cur_time.guard`, `sched.consumed.guard` |
| `suf` | `sporadic.sufficient.guard` (`RdHead` of the current SC) |
| `aq` | `localvm.awaken_quiet.guard` (below: `timer_due.guard` + `release_due.guard`) |
| `chk` | `vcpu.check.guardP` + `vcpu.report.guardP` (the report's frame `P`, `RepG`) |
| `cb` | `sched.check_budget.guard_suf` |
| `fin` | `localvm.finish.guardP` (below; `sched.schedule`'s guard is its premise) |

No named premises: the fields are hypotheses about the guarded store only, discharged as listed.
-/
import Fl4Proofs.P2.AccessLvmRepR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- `awaken_quiet` reads the node's timer minimum and release head and their first entries. -/
theorem localvm.awaken_quiet.guard (s : S) (now : U64)
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      R (tdA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
    (h3 : R (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))
    (h4 : L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) ≠ 0#u64 →
      R (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) ∧
      PathObl.RdHead (L := L) R s (L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)))))
    (h5 : R (ctA (L := L) s)) :
    localvm.awaken_quiet gS s (L.cpu s) now = localvm.awaken_quiet st s (L.cpu s) now := by
  unfold localvm.awaken_quiet
  rw [timer_due.guard s now h1 h2]
  refine PathObl.bind_guard_congr rfl fun b _ => ?_
  split
  · rfl
  · rw [release_due.guard s h3 h4 h5]

/-- **`localvm.finish`** (`schedule`, `activate_thread`, `vcpu.check` of the new current thread), from the
guards of its steps at the states the real run reaches. -/
theorem localvm.finish.guardP {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hsch : sched.schedule gS ar s a = sched.schedule st ar s a)
    (hk : ∀ s1 a1, sched.schedule st ar s a = ok (s1, a1) →
      sched.activate_thread gS ar s1 a1 = sched.activate_thread st ar s1 a1 ∧
      ∀ s2 a2, sched.activate_thread st ar s1 a1 = ok (s2, a2) →
        R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) ∧
        ∀ t, sched.cur_thread st s2 = ok t → vcpu.check gS ar s2 a2 t = vcpu.check st ar s2 a2 t) :
    localvm.finish gS ar s a = localvm.finish st ar s a := by
  unfold localvm.finish
  rw [hsch]
  refine PathObl.bind_guard_congr rfl ?_
  rintro ⟨s1, a1⟩ h1
  obtain ⟨ha, hk2⟩ := hk s1 a1 h1
  try simp only [Aeneas.Std.uncurry_apply_pair]
  rw [ha]
  refine PathObl.bind_guard_congr rfl ?_
  rintro ⟨s2, a2⟩ h2
  obtain ⟨hc, hk3⟩ := hk2 s2 a2 h2
  try simp only [Aeneas.Std.uncurry_apply_pair]
  rw [PathObl.sched.cur_thread.guard s2 hc]
  exact PathObl.bind_guard_congr rfl fun t ht => hk3 t ht

/-- **The guard facts of `local_vm_exit`'s work** (module docstring), at the states the real run reaches from
`s`: current thread `ct`, current SC `csc`, core `cpu`. -/
structure VexitAcc {A : Type} (ar : machine.Arch A) (s : S) (a : A) (ct csc cpu : U64) : Prop where
  ut : sched.update_timestamp gS ar s a = sched.update_timestamp st ar s a
  now : ∀ s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) → sched.cur_time gS s1 = sched.cur_time st s1
  cons : ∀ s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) → sched.consumed gS s1 = sched.consumed st s1
  suf : ∀ s1 a1 u, sched.update_timestamp st ar s a = ok (s1, a1) →
    sporadic.sufficient gS ar s1 a1 csc u = sporadic.sufficient st ar s1 a1 csc u
  aq : ∀ s1 a1 now, sched.update_timestamp st ar s a = ok (s1, a1) →
    localvm.awaken_quiet gS s1 cpu now = localvm.awaken_quiet st s1 cpu now
  chk : ∀ s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) →
    vcpu.check gS ar s1 a1 ct = vcpu.check st ar s1 a1 ct
  cb : ∀ s1 a1 s2 a2, sched.update_timestamp st ar s a = ok (s1, a1) → vcpu.check st ar s1 a1 ct = ok (s2, a2) →
    sched.check_budget gS ar s2 a2 = sched.check_budget st ar s2 a2
  fin : ∀ s1 a1 s2 a2 x s3 a3, sched.update_timestamp st ar s a = ok (s1, a1) →
    vcpu.check st ar s1 a1 ct = ok (s2, a2) → sched.check_budget st ar s2 a2 = ok (x, s3, a3) →
    localvm.finish gS ar s3 a3 = localvm.finish st ar s3 a3

/-- `vexitTail` on the guarded store, from `VexitAcc`. -/
theorem vexitTail.guardP {A : Type} (ar : machine.Arch A) (s : S) (a : A) (ct csc cpu : U64)
    (V : VexitAcc (gS := gS) (st := st) ar s a ct csc cpu) :
    vexitTail gS ar s a ct csc cpu = vexitTail st ar s a ct csc cpu := by
  unfold vexitTail
  rw [V.ut]
  refine PathObl.bind_guard_congr rfl ?_
  rintro ⟨s1, a1⟩ h1
  try simp only [Aeneas.Std.uncurry_apply_pair]
  rw [V.now s1 a1 h1]
  refine PathObl.bind_guard_congr rfl fun now _ => ?_
  rw [V.cons s1 a1 h1]
  refine PathObl.bind_guard_congr rfl fun c _ => ?_
  rw [V.suf s1 a1 c h1]
  refine PathObl.bind_guard_congr rfl fun b4 _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  rw [V.aq s1 a1 now h1]
  refine PathObl.bind_guard_congr rfl fun b5 _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  rw [V.chk s1 a1 h1]
  refine PathObl.bind_guard_congr rfl ?_
  rintro ⟨s2, a2⟩ h2
  try simp only [Aeneas.Std.uncurry_apply_pair]
  rw [V.cb s1 a1 s2 a2 h1 h2]
  refine PathObl.bind_guard_congr rfl ?_
  rintro ⟨x, s3, a3⟩ h3
  try simp only [Aeneas.Std.uncurry_apply_pair]
  rw [V.fin s1 a1 s2 a2 x s3 a3 h1 h2 h3]

/-- **`PathObl.acc` of `local_vm_exit`** (`handle_vcpu_exit_local`): on any store answering the heads' reads
(`vexit_acc_head`'s hypotheses) and the work's steps (`VexitAcc`) as `st`, the body is the real one. -/
theorem vexit_acc {A : Type} (ar : machine.Arch A) (s : S) (a : A) (v n csc : U64)
    (hcsc : sched.cur_sc st s = ok csc) (hR : LvmRd st R s (L.curW s) csc)
    (hp : v ≠ 0#u64 → R (core.num.U64.wrapping_add v vcpu.PENDING))
    (hn : n ≠ 0#u64 → R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE))
    (V : VexitAcc (gS := gS) (st := st) ar s a (L.curW s) csc (L.cpu s)) :
    localvm.handle_vcpu_exit_local gS ar s a v n = localvm.handle_vcpu_exit_local st ar s a v n :=
  vexit_acc_head ar s a v n csc hcsc hR hp hn (vexitTail.guardP ar s a _ _ _ V)

end

end Fl4Proofs.P2

/-
P2 (p2j, stage 1 of modelling remote stalls; `P2/InvStall.lean` has the
write-up): **the store viewed at another core** and **`stallAt d`**.

* `atCpu st d`: the `Store` `st` with `cur_cpu` returning `d`, every other
  operation `st`'s (same carrier, same memory). `LawfulStore.atCpu L d`: its
  `LawfulStore` instance (`L`'s laws, `cpu := d`); `LawfulStore`'s existing
  laws are not touched. So every P1 lemma, stated for any
  `[LawfulStore st]`, applies to the view `(atCpu st d, L.atCpu d)`, with
  `L.cpu` read as `d`: P1's current-core invariants become `d`'s.
* `stallAt st ar d s a`: `smp.stall` then `smp.send_pending` on the view at
  `d` — what the target core `d` runs for `Arch::remote_stall(d)` on the
  issuer's behalf (fl4-kernel `service_remote`; `fl4-sim`'s `remote_stall`
  with `conc: None`). `stallAt.p0`: total.
* `stallPre.bxi`: the first half of `smp.stall` — `update_timestamp`,
  `check_budget` (**including the timeout-fault branch**: `charge_budget`'s
  `end_timeslice` → `handle_timeout`, under P1's `TmoK` premise) and
  `commit_time` — keeps P1's invariants (`BlkOK`) from `EntryInv`, for any
  `LawfulStore`; `stallPre_at.bxi` is the view at `d`.

**Not yet proved** (stage-1 blocker, reported to the lead):

1. The second half of `smp.stall` (`Running → Restart`, `enqueue`,
   `switch_to_idle_thread`, `CUR_SC := IDLE_SC`, `CONSUMED`, `REPROGRAM`,
   `SCHED_ACTION`) at the view: `CUR_SC := IDLE_SC` needs the node word
   `IDLE_SC` to be the idle thread's SC (active, disjoint from the other
   bound SCs). P1 never reads `IDLE_SC`: a new invariant ([J] boot sets
   `IDLE_SC = isc = SC(idle)`, `create_idle_thread`; no invocation reaches
   the idle thread's SC).
2. The issuer's invariant across `stallAt d`: P1's `EntryInv`/`BXI` hold only
   for the executing core's current-core clauses (`L.cpu`: `actionW`,
   `curW`, `idleW`, `cscW`, `BoundInv.resume`, `SCsOK.disj`, …). `stallPre.bxi`
   at the view needs `EntryInv` *at the view `d`* at stall time, i.e. `d`'s
   current-core clauses, which no P1 lemma maintains for a non-executing core
   (the same all-cores gap as `OwnJ` in `P2/InvAff.lean`); and back at the
   issuer's view, its own current-core clauses must survive the stall
   (`d`'s writes are `KW`-sized: `Foot` does not separate cores).

**The Arch-model change (stage 3, proposal; nothing changed here).** No
premise about `Arch.remote_stall` can give it a store effect: the extracted
`smp.remote_tcb_stall` calls `ar.remote_stall a cpu : Result A` and passes
`s` on unchanged, so the store effect must be in the extracted code. The
smallest change: move the call to the `Store` trait,
`Store::remote_stall(&mut self, cpu: u64)` (fl4-kernel: today's
`remote_call(CALL_STALL, …)`; fl4-sim: today's `remote_stall` body; the
`Arch` method goes), so the extraction has
`machine.Store.remote_stall : S → U64 → Result S` and `remote_tcb_stall`
threads the store. Then one [W] law, beside `LawfulStore` (a new class, its
laws untouched): `StallLaw st ar : ∀ s a d s', st.remote_stall s d = ok s' →
∃ a', stallAt st ar d s a = ok (s', a')` (the target's Arch effects, its
`set_vspace` and reschedule IPIs, are its own). P0 gets one totality
premise for it (`StoreTotal.remote_stall`). This changes fl4-core (one call
site, `smp.rs:52/63`) and re-extracts.

**What relies on the stall being a store no-op** (would change):

* P1, the source: `smp.remote_tcb_stall.spec` (QueueAppend: `s' = s` or the
  issuer's `IPI_PENDING`), and the lemmas built on it: `ipi_all`,
  `smp.remote_tcb_stall.all` (QueueIpc: invariants kept, every TCB word and
  every `Ω` word unchanged), `.tm` (TimerRBSig), `.bxi` (QueueDecSc),
  `.blkS` (QueueFinSc), `.cur0` (QueueFinIo), `.blk` (QueueFinal),
  `Stalled.stall` (QueueDecTcb2).
* Their users (uses / files): `.spec` 12/12 (QueueIpcFoot, TimerRBSig,
  QueueIpc, QueueDecSc, QueueSchedCtl, QueueFinSc, QueueFootD, QueueReplyKw,
  QueueFinal; P3 XTopJointSendDon, ScRestP1), `.all` 14/11 (QueueReplyPop,
  QueueIpc, QueueFinThr, QueueDecSc, QueueReply, QueueDead, QueueFinCur,
  QueueFinal, QueueDeadTd; P3 XTopJointSendDon, XTopJointDbgKeep), `.bxi`
  8/6 (QueueDecDom, QueueDecSc, QueueDecTcb2, QueueDecVcpu, QueueFinIo; P3
  ScRestP1), `.blk` 11/10 (QueueFinThr, QueueFinSc, QueueSchedCtl,
  QueueReplyKw, QueueFootD, QueueDead, QueueFinal, QueueDeadTd; P3 ScRestP1,
  XTopJointDbgKeep), `.blkS` 3/2, `.cur0` 3/2, `.tm` 1, `Stalled.stall` 1,
  `ipi_all` 2. These are the serial entries that stall: `donate`
  (`schedcontext.donate.ipc` assumes the donor unqueued *after* the stall —
  with the stall modelled the donor may be enqueued by it, and `dequeue`
  then really dequeues), `configure_flags`, `unbind_all_tcbs`, SC/TCB/
  domain/VCPU decode, Thread-cap finalisation, reply removal.
* Unaffected: P1 `stall_none` (LocalTimer: target on this core, no call),
  P3 `remote_tcb_stall_id` (ScConfig; 20 uses in 14 P3 files) and
  `vcpu_stall_id` (single core: every thread on the current core, so no
  call is made), `MK`/`MKD`/`AK.smp_remote_tcb_stall` (Arch keep: no Arch
  call left if it moves to `Store`). P3 keeps its one-core [P] premise (INV-
  PLAN E5/C1): the uniprocessor spec has no stall.
-/
import Fl4Proofs.P1.QueueBudgetG
import Fl4Proofs.P1.QueueSchedCtl
import Fl4Proofs.P1.QueueFire
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

/-- The `Store` `st` viewed from core `d`: `cur_cpu` returns `d`. -/
def atCpu {S : Type _} (st : machine.Store S) (d : U64) : machine.Store S :=
  { st with cur_cpu := fun _ => ok d }

/-- The view's `LawfulStore`: `L`'s memory and laws, the core `d`. -/
def _root_.Fl4Proofs.P1.LawfulStore.atCpu {S : Type _} {st : machine.Store S} (L : LawfulStore st) (d : U64) :
    LawfulStore (atCpu st d) where
  frame_masks_total := L.frame_masks_total
  mem := L.mem
  wr := L.wr
  zr := L.zr
  ksb := L.ksb
  cpu := fun _ => d
  read_eq := L.read_eq
  read_pair_eq := L.read_pair_eq
  write_eq := L.write_eq
  zero_eq := L.zero_eq
  clear_free_eq := L.clear_free_eq
  ks_base_eq := L.ks_base_eq
  cur_cpu_eq := fun _ => rfl
  fetch_and_eq := L.fetch_and_eq
  mem_wr := L.mem_wr
  mem_zr := L.mem_zr
  ksb_wr := L.ksb_wr
  cpu_wr := fun _ _ _ => rfl
  ksb_zr := L.ksb_zr
  cpu_zr := fun _ _ _ => rfl

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

@[simp] theorem atCpu_mem (d : U64) (s : S) (b : U64) : (L.atCpu d).mem s b = L.mem s b := rfl
@[simp] theorem atCpu_wr (d : U64) (s : S) (b v : U64) : (L.atCpu d).wr s b v = L.wr s b v := rfl
@[simp] theorem atCpu_ksb (d : U64) (s : S) : (L.atCpu d).ksb s = L.ksb s := rfl
@[simp] theorem atCpu_cpu (d : U64) (s : S) : (L.atCpu d).cpu s = d := rfl

/-- The view's node words are the store's. -/
@[simp] theorem atCpu_nodeAt (d : U64) (s : S) (c o : U64) :
    (L.atCpu d).nodeAt s c o = L.nodeAt s c o := rfl

/-- The view's current thread and SC are `d`'s. -/
theorem atCpu_curW (d : U64) (s : S) :
    (L.atCpu d).curW s = L.mem s (L.nodeAt s d layout.node.CUR_THREAD) := rfl
theorem atCpu_cscW (d : U64) (s : S) :
    (L.atCpu d).cscW s = L.mem s (L.nodeAt s d layout.node.CUR_SC) := rfl

end

/-- **`stallAt d`**: what core `d` runs for `Arch::remote_stall(d)`, on the
issuer's behalf: `smp::stall` then `smp::send_pending`, with `cur_cpu = d`. -/
def stallAt {S A : Type _} (st : machine.Store S) (ar : machine.Arch A) (d : U64) (s : S) (a : A) :
    Result (S × A) := do
  let (s1, a1) ← smp.stall (atCpu st d) ar s a
  smp.send_pending (atCpu st d) ar s1 a1

/-- `stallAt` is total. -/
theorem stallAt.p0 {S A : Type _} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
    (hA : P0.ArchTotal ar) (d : U64) (s : S) (a : A) : stallAt st ar d s a ⦃ _ => True ⦄ := by
  unfold stallAt
  refine WP.spec_bind (P0.smp.stall.p0 (atCpu st d) ar s a (@LawfulStore.total _ _ (L.atCpu d)) hA) ?_
  rintro ⟨s1, a1⟩ -
  exact P0.smp.send_pending.p0 (atCpu st d) ar s1 a1 (@LawfulStore.total _ _ (L.atCpu d)) hA

/-- The first half of `smp.stall`: `update_timestamp`, `check_budget`,
`commit_time`. -/
def stallPre {S A : Type _} (st : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) : Result (S × A) := do
  let (s1, a1) ← sched.update_timestamp st ar s a
  let (_, s2, a2) ← sched.check_budget st ar s1 a1
  let s3 ← sched.commit_time st ar s2 a2
  ok (s3, a2)

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs Ω : Set U64} {H : Heap}
variable {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {A : Type _} {ar : machine.Arch A}

/-- **The budget half of a stall keeps P1's invariants**, timeout faults
included: from `EntryInv` (the stalled core's, at its view), with P1's
timeout-fault premise `TmoK` (`tmoXG_holds` at `XG` states). -/
theorem stallPre.bxi (hA : P0.ArchTotal ar) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (htmo : ∀ s0 : S, TmoK st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    stallPre st ar s a ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold stallPre
  refine WP.spec_bind (sched.update_timestamp.entry hA s a h) ?_
  rintro ⟨s1, a1⟩ h1
  try simp only [WP.uncurry'_pair] at h1 ⊢
  obtain ⟨⟨⟨Q, R, q1⟩, hB1, hX1, hSg1, hS1⟩, -, hcA, hna, hcsc, -⟩ := h1
  refine WP.spec_bind (sched.check_budget.all hA s1 a1 Q R q1 hB1 hX1 hSg1 hS1 hcsc hna hcA (htmo s1)) ?_
  rintro ⟨r, s2, a2⟩ ⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hSg2, hS2⟩, -⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (sched.commit_time.blk hA a2 ⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩) ?_
  rintro s3 ⟨h3, -⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact h3

/-- `stallPre.bxi` at the view of core `d`: `EntryInv` with `d` as the
current core. -/
theorem stallPre_at.bxi (hA : P0.ArchTotal ar) (d : U64) (s : S) (a : A)
    (h : @EntryInv S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (htmo : ∀ s0 : S, @TmoK S (atCpu st d) (L.atCpu d) A ar T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    stallPre (atCpu st d) ar s a ⦃ s' _ => @BlkOK S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  stallPre.bxi (st := atCpu st d) (L := L.atCpu d) hA s a h htmo

end

end Fl4Proofs.P2.Stall

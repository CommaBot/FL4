/-
P2 (local-path ownership): the **core-placement invariants** the global
ownership map (`P2/OwnMap.lean`: a thread's words are its `AFFINITY` core's,
an SC's words its `CORE` core's) needs, which P1 does not state:

* (2) `AffSc`: a TCB-bound SC's `CORE` word is the thread's `AFFINITY`.
* (1) `CurAff`: every core's current thread has that core as its `AFFINITY`.
* (3) `CurScCore`: every core's `CUR_SC` has that core as its `CORE`.

**(2) and SC donation.** It holds in FL4, as in seL4 MCS: every write that
binds an SC to a thread or changes an SC's core moves the thread to the SC's
core (`smp::migrate_tcb`, seL4 `migrateTCB`), and `migrate_tcb` is the only
writer of `AFFINITY` (besides boot's idle threads, `create_idle_thread`, which
also sets the idle SC's `CORE` to the same core):

* `schedcontext::bind_tcb` (crates/fl4-core/src/schedcontext.rs:26–29;
  `SchedContext_Bind`, `TCB_Configure`/`SetSchedParams` via tcb.rs:164):
  `t.set_sc(sc); sc.set_tcb(t); migrate_tcb(t, sc.cpu())`.
* `schedcontext::donate` (schedcontext.rs:65–79), the one path of every
  donation: `send_ipc` to a passive receiver (endpoint.rs:108), `reply_push`
  on Call (ipc.rs:180), `reply_pop` handing the SC back (ipc.rs:195), and a
  passive waiter's bound notification (`maybe_donate_sched_context`,
  notification.rs:52): the donor loses the SC (`from.set_sc(0)`), and then
  `sc.set_tcb(to); to.set_sc(sc); migrate_tcb(to, sc.cpu())`. A passive
  server called by a client on another core therefore runs on the client's
  SC's core, with its `AFFINITY` moved there (DESIGN §8 "the server runs on
  the client's core"); when it replies the SC goes back to the caller and the
  server keeps no SC, so (2) says nothing about it.
* `invokeSchedControl_ConfigureFlags` (`configure_flags`,
  schedcontext.rs:315–317): `target.set_cpu(cpu)` then, for a bound thread,
  `migrate_tcb(thread, cpu)`.
* Unbinding (`unbind_tcb`, notification.rs:63, finalisation) only clears the
  link. The fast paths (fastpath.rs, fastpath_vm.rs) move no SC (they decline
  where `reply_pop` would move a donated SC) and require the woken thread's
  `AFFINITY` to be this core (`schedulable_here`).

So no reachable state has a bound SC on another core than its thread, and no
local path writes an SC owned by another core through a donated SC.

What is proved here: (2)'s update lemmas for the three kinds of writes
(`AffSc.of_x`/`AffScX.keep` for bind/donate, `AffSc.reconfigure` for
`configure_flags`, `ScExtra.sc_owner` supplying its uniqueness premises), and
that the extracted `smp.migrate_tcb` sets the affinity
(`smp.migrate_tcb.aff_val`) and re-establishes (2) for the migrated thread
(`smp.migrate_tcb.affSc`). (3) follows from (1), (2) and the current SC being
the current thread's (`CurScCore.of`, and at the current core from P1's
`EntryInv`: `EntryInv.cur_sc_core`).

**Premises** (`OwnJ`, all [J]): (1), (2), `CurScOf` and `curT` at every kernel
entry (`P2/InvKeep.lean` discharges them for declined local entries and
reduces accepted local paths to their footprint obligation).
Their preservation by every kernel entry is not proved here (the P1 entry
proofs carry no frame for `AFFINITY`/`CORE` to compose with). A further point
for (1) and `CurScOf` at *other* cores: `remote_tcb_stall` runs `smp::stall`
on the stalled core, which sets that core's `CUR_THREAD`/`CUR_SC` to its idle
thread and SC, but the extracted model's `Arch.remote_stall` returns only an
`Arch` value (no store effect; INV-PLAN E5/C1 take it as a no-op, [P] one
core). In the model, `configure_flags` moving a thread current on core `d`
to another core leaves `node[d].CUR_THREAD` naming it, so (1) at `d` holds
of the real machine but not of the store model until `remote_stall`'s store
effect is modelled.
-/
import Fl4Proofs.P2.InvImpl
import Fl4Proofs.P1.QueueIpc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- Core `c`'s `CUR_THREAD`. -/
def curTh (st : machine.Store S) [L : LawfulStore st] (s : S) (c : U64) : U64 :=
  L.mem s (L.nodeAt s c layout.node.CUR_THREAD)

/-- Core `c`'s `CUR_SC`. -/
def curSc (st : machine.Store S) [L : LawfulStore st] (s : S) (c : U64) : U64 :=
  L.mem s (L.nodeAt s c layout.node.CUR_SC)

/-- **(2)** A bound SC's `CORE` is its thread's `AFFINITY`. -/
def AffSc (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) : Prop :=
  ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)

/-- (2) except for the thread `x` (between the writes of a bind or donation). -/
def AffScX (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (x : U64) (s : S) : Prop :=
  ∀ t ∈ T, t ≠ x → L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)

/-- **(1)** Every core's current thread is on that core. -/
def CurAff (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (s : S) : Prop :=
  ∀ c ∈ Cs, L.mem s (affA (curTh st s c)) = c

/-- Every core's current thread has an SC, and it is that core's `CUR_SC`
(P1's `EntryInv` last clause and `BoundInv.resume`, at every core). -/
def CurScOf (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (s : S) : Prop :=
  ∀ c ∈ Cs, L.mem s (scA (curTh st s c)) ≠ 0#u64 ∧ curSc st s c = L.mem s (scA (curTh st s c))

/-- **(3)** Every core's current SC is on that core. -/
def CurScCore (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (s : S) : Prop :=
  ∀ c ∈ Cs, L.mem s (scCoreA (curSc st s c)) = c

/-- **[J] The core-placement premises at a kernel entry** (or between
entries): (2) `AffSc`, (1) `CurAff`, `CurScOf` and every core's current
thread a TCB. Why they hold (module
docstring): `AFFINITY` is written only by `migrate_tcb`, which every SC bind,
donation and core change runs towards the SC's core; `schedule()`, which ends
every serial entry, makes current only this core's threads (ready queues are
per affinity, `SchedQueuesInvX.inQ`; the idle thread's affinity is its core)
or keeps a current thread whose SC was neither moved nor taken (each path that
moves or takes it, `configure_flags`, `donate` from the current thread,
`unbind_tcb`, raises `reschedule_required`), then switches `CUR_SC` to its
SC; a remote stall leaves the stalled core on its idle thread and SC. Local
paths move no thread or SC between cores. -/
structure OwnJ (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s : S) : Prop where
  affSc : AffSc st T s
  curAff : CurAff st Cs s
  curScOf : CurScOf st Cs s
  /-- Every core's current thread is a TCB (P1's `SchedQueuesInvX.curT`, at every core). -/
  curT : ∀ c ∈ Cs, curTh st s c ∈ T

/-! ## (3) from (1), (2) -/

/-- **(3)** from (1), (2) and `CurScOf`. -/
theorem CurScCore.of {s : S} (hT : ∀ c ∈ Cs, curTh st s c ∈ T) (h2 : AffSc st T s) (h1 : CurAff st Cs s)
    (h3 : CurScOf st Cs s) : CurScCore st Cs s := fun c hc => by
  obtain ⟨h0, e⟩ := h3 c hc
  rw [e, h2 _ (hT c hc) h0, h1 c hc]

theorem OwnJ.curScCore {s : S} (h : OwnJ st T Cs s) : CurScCore st Cs s :=
  CurScCore.of h.curT h.affSc h.curAff h.curScOf

/-- **(3)** at the current core from P1's `EntryInv`, given (2) and (1) there,
when the current thread has an SC. -/
theorem EntryInv.cur_sc_core {s : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (h2 : AffSc st T s)
    (h1 : L.mem s (affA (L.curW s)) = L.cpu s) (h0 : L.mem s (scA (L.curW s)) ≠ 0#u64) :
    L.mem s (scCoreA (L.cscW s)) = L.cpu s := by
  obtain ⟨⟨Q, R, hq⟩, -, -, -, -, -, -, hc⟩ := h
  rw [hc h0, h2 (L.curW s) hq.curT h0, h1]

/-- The current thread has an SC when the action is resume (`BoundInv.resume`). -/
theorem EntryInv.cur_sc_ne0 {s : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ha : L.actionW s = 0#u64) : L.mem s (scA (L.curW s)) ≠ 0#u64 :=
  h.2.1.resume ha

/-! ## (2) under the writes that change it -/

theorem AffSc.x {s : S} {x : U64} (h : AffSc st T s) : AffScX st T x s := fun t ht _ => h t ht

/-- (2) from (2) except `x` and (2) for `x`: the end of a bind or donation to
`x` (`sc.set_tcb(x); x.set_sc(sc); migrate_tcb(x, sc.cpu())`). -/
theorem AffSc.of_x {s : S} {x : U64} (h : AffScX st T x s)
    (hx : x ∈ T → L.mem s (scA x) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA x))) = L.mem s (affA x)) :
    AffSc st T s := fun t ht h0 => by
  by_cases e : t = x
  · subst e; exact hx ht h0
  · exact h t ht e h0

/-- (2) except `x` is kept by writes that keep the other threads' `SC` and
`AFFINITY` and every SC's `CORE` (unbinding, clearing the donor's `SC`, the
queue and debug-list steps). -/
theorem AffScX.keep {s s' : S} {x : U64} (h : AffScX st T x s)
    (hty : ∀ t ∈ T, t ≠ x → L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Scs)
    (hsc : ∀ t ∈ T, t ≠ x → L.mem s' (scA t) = L.mem s (scA t))
    (haf : ∀ t ∈ T, t ≠ x → L.mem s' (affA t) = L.mem s (affA t))
    (hco : ∀ c ∈ Scs, L.mem s' (scCoreA c) = L.mem s (scCoreA c)) : AffScX st T x s' := by
  intro t ht hne h0
  rw [hsc t ht hne] at h0 ⊢
  rw [hco _ (hty t ht hne h0), haf t ht hne]
  exact h t ht hne h0

/-- (2) after clearing `x`'s `SC` (unbind, or the donor in `donate`). -/
theorem AffSc.unbind {s : S} {x : U64} (h : AffScX st T x s) (h0 : L.mem s (scA x) = 0#u64) : AffSc st T s :=
  AffSc.of_x h fun _ hn => absurd h0 hn

/-- The bound-SC facts of `ScExtra` that `configure_flags` needs: the only
thread bound to `target` is its `TCB`, which names it back. -/
theorem ScExtra.sc_owner {s : S} (hX : ScExtra st T Cs Scs Nt s) {target : U64} (hc : target ∈ Scs)
    (hc0 : target ≠ 0#u64) :
    (∀ y ∈ T, L.mem s (scA y) = target → y = L.mem s (scTcbA target)) ∧
      (L.mem s (scTcbA target) ≠ 0#u64 → L.mem s (scA (L.mem s (scTcbA target))) = target) := by
  refine ⟨fun y hy e => ?_, hX.tsc target hc hc0⟩
  have hb := (hX.bound y hy (by rw [e]; exact hc0)).2.1
  rw [e] at hb
  exact hb.symm

/-- **(2) under `configure_flags`**: `target`'s `CORE` becomes `cpu` and its
thread `th` (if any) is migrated to `cpu`; every other `SC`, `AFFINITY` and
`CORE` word is kept. The premises `huniq`/`hth` are `ScExtra.sc_owner`. -/
theorem AffSc.reconfigure {s s' : S} {target th cpu : U64} (h : AffSc st T s)
    (hT0 : ∀ y ∈ T, y ≠ 0#u64)
    (hty : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Scs)
    (huniq : ∀ y ∈ T, L.mem s (scA y) = target → y = th)
    (hth : th ≠ 0#u64 → L.mem s (scA th) = target)
    (hsc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t))
    (haf : ∀ t ∈ T, t ≠ th → L.mem s' (affA t) = L.mem s (affA t))
    (hco : ∀ c ∈ Scs, c ≠ target → L.mem s' (scCoreA c) = L.mem s (scCoreA c))
    (hct : L.mem s' (scCoreA target) = cpu) (hath : th ∈ T → L.mem s' (affA th) = cpu) :
    AffSc st T s' := by
  intro y hy h0
  rw [hsc y hy] at h0 ⊢
  by_cases e : L.mem s (scA y) = target
  · have hy' := huniq y hy e
    rw [e, hct, hy', hath (by rw [← hy']; exact hy)]
  · have hne : y ≠ th := fun hyt => e (by rw [hyt]; exact hth (by rw [← hyt]; exact hT0 y hy))
    rw [hco _ (hty y hy h0) e, haf y hy hne]
    exact h y hy h0

/-! ## `migrate_tcb` -/

/-- The extracted `smp.migrate_tcb t cpu` leaves `t`'s `AFFINITY` at `cpu`. -/
theorem smp.migrate_tcb.aff_val {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t cpu : U64) (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hD : DbgTz st T Cs s)
    (hc : L.mem s (affA t) ∈ Cs) (hcpu : cpu ∈ Cs) (ht : t ∈ T) :
    smp.migrate_tcb st ar s a t cpu ⦃ s' _ => L.mem s' (affA t) = cpu ⦄ := by
  have hta := hT t ht
  have haa : Aligned (affA t) := field_aligned (K := 3520#u64) hta (by simp) (by simp)
  unfold smp.migrate_tcb
  step with obj.Tcb.affinity.spec as ⟨af, haf⟩
  split
  · refine WP.spec_bind (objects.debug_remove.frame s t hT hN hD hc ht) fun s1 ⟨w1, D1⟩ => ?_
    refine WP.spec_bind (hA.fpu_flush _ _) fun a2 _ => ?_
    refine WP.spec_bind (hA.fpu_release _ _) fun a3 _ => ?_
    refine WP.spec_bind (obj.Tcb.set_affinity.wr s1 t cpu) fun s2 e2 => ?_
    subst e2
    have hN1 : ∀ c ∈ Cs, NodePlaced st T s1 c := fun c hc' => (hN c hc').ksb w1.1
    have hN2 : ∀ c ∈ Cs, NodePlaced st T (L.wr s1 (affA t) cpu) c := fun c hc' => (hN1 c hc').wr
    have D2 : DbgTz st T Cs (L.wr s1 (affA t) cpu) :=
      DbgTz.wr_out hT hN1 haa (notDbgW_field (K := 3520#u64) hT hN1 ht (by simp) (by simp)) D1
    have hc2 : L.mem (L.wr s1 (affA t) cpu) (affA t) ∈ Cs := by rw [L.mem_wr_same haa]; exact hcpu
    refine WP.spec_bind (objects.debug_append.frame _ t hT hN2 D2 hc2 ht) fun s3 ⟨w3, _⟩ => ?_
    refine (WP.spec_ok _).2 ?_
    try simp only [WP.uncurry'_pair]
    rw [w3.mem_eq haa (notDbgW_field (K := 3520#u64) hT hN2 ht (by simp) (by simp)), L.mem_wr_same haa]
  · rename_i hne
    try simp only [Aeneas.Std.bind_ok]
    refine (WP.spec_ok _).2 ?_
    try simp only [WP.uncurry'_pair]
    have e : af = cpu := UScalar.eq_of_val_eq (by simpa using hne)
    rw [← haf]; exact e

/-- **(2) after `migrate_tcb`**: if (2) holds except for `t`, and `t`'s SC
(if any) is on `cpu`, then after `smp.migrate_tcb t cpu` (2) holds. The bound
SCs' `CORE` words lie outside the TCBs and nodes. -/
theorem smp.migrate_tcb.affSc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t cpu : U64) (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hD : DbgTz st T Cs s)
    (hc : L.mem s (affA t) ∈ Cs) (hcpu : cpu ∈ Cs) (ht : t ∈ T) (hX : AffScX st T t s)
    (ht0 : L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = cpu)
    (hty : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → OutsideObjs st T Cs s (scCoreA (L.mem s (scA y)))) :
    smp.migrate_tcb st ar s a t cpu ⦃ s' _ => AffSc st T s' ⦄ := by
  have hta := hT t ht
  refine WP.spec_mono (WP.spec_and (smp.migrate_tcb.frame hA s a t cpu hT hN hD hc hcpu ht)
    (smp.migrate_tcb.aff_val hA s a t cpu hT hN hD hc hcpu ht)) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  obtain ⟨⟨w, -, -⟩, hv⟩ := hr
  have nA : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val ≠ 3576 ∧ K.val ≠ 3584) →
      (y = t → K.val ≠ 3520) →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8 hKd hne
    refine w.mem_eq (field_aligned (hT y hy) hK hK8) ?_
    rintro (e | e)
    · exact field_ne (K2 := 3520#u64) (hT y hy) hta hK (by simp) (fun h => by have := hne h; simpa using this) e
    · exact notDbgW_field hT hN hy hK hKd e
  have nC : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 →
      L.mem s' (scCoreA (L.mem s (scA y))) = L.mem s (scCoreA (L.mem s (scA y))) := by
    intro y hy h0
    have ho := hty y hy h0
    refine w.mem_eq ho.1 ?_
    rintro (e | e)
    · exact out_ne_field (K := 3520#u64) ho ht hta (by simp) (congrArg UScalar.val e).symm
    · exact notDbgW_out hT hN ho e
  have hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact nA y hy _ (by simp) (by simp) (by simp) (fun _ => by simp)
  have haf : ∀ y ∈ T, y ≠ t → L.mem s' (affA y) = L.mem s (affA y) := fun y hy hne =>
    nA y hy 3520#u64 (by simp) (by simp) (by simp) (fun h => absurd h hne)
  intro y hy h0
  rw [hsc y hy] at h0 ⊢
  rw [nC y hy h0]
  by_cases e : y = t
  · subst e; rw [hv]; exact ht0 h0
  · rw [haf y hy e]; exact hX y hy e h0

end

end Fl4Proofs.P1

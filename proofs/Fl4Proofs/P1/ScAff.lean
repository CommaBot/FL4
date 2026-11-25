/-
P1: a bound SC's `CORE` word is its thread's `AFFINITY` (`ScAff`), and its
step lemmas, stated over word frames so that every P1 path can use them.

fl4-core keeps it: the only writes of a TCB's nonzero `SC` field are
`schedcontext::bind_tcb` and `donate` (both followed by
`migrate_tcb(t, sc.cpu())`, schedcontext.rs:27–29, 77–78) and boot; the only
`CORE` write of a bound SC is `SchedControl` configure (`set_cpu`, then
`migrate_tcb` of the bound thread, schedcontext.rs:315–317); the only
`AFFINITY` writers are `migrate_tcb` (smp.rs:36) and boot (boot.rs:691/696).

Between those writes and the `migrate_tcb` P1 holds its invariants
(`donate_pair`'s state, `migrate_tail`'s and `cfD`'s inputs) while `ScAff`
fails for the one thread being moved: `ScAffX d` is `ScAff` off that thread,
`ScAff.pairX` / `ScAff.coreX` enter it and `ScAffX.restore` (the affinity
write) leaves it.
-/
import Fl4Proofs.P1.QueueSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Scs : Set U64}

/-- **A bound SC's `CORE` word is its thread's `AFFINITY`.** -/
def ScAff (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) : Prop :=
  ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)

/-- `ScAff` off the thread `d` (between the SC write that binds `d`, or the
`CORE` write of `d`'s SC, and the `migrate_tcb` of `d`). -/
def ScAffX (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (d : U64) (s : S) : Prop :=
  ∀ t ∈ T, t ≠ d → L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)

theorem ScAff.x {s : S} (h : ScAff st T s) (d : U64) : ScAffX st T d s := fun t ht _ => h t ht

theorem ScAffX.full {s : S} {d : U64} (h : ScAffX st T d s)
    (hd : d ∈ T → L.mem s (scA d) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA d))) = L.mem s (affA d)) :
    ScAff st T s := fun t ht h0 =>
  if e : t = d then by subst e; exact hd ht h0 else h t ht e h0

/-- `ScAff` under a frame of the TCBs' `SC` and `AFFINITY` fields and the
SCs' `CORE` words. -/
theorem ScAff.keep {s s' : S} (h : ScAff st T s)
    (hb : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Scs)
    (hsc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t))
    (hco : ∀ c ∈ Scs, L.mem s' (scCoreA c) = L.mem s (scCoreA c))
    (haf : ∀ t ∈ T, L.mem s' (affA t) = L.mem s (affA t)) : ScAff st T s' := fun t ht h0 => by
  rw [hsc t ht] at h0 ⊢
  rw [hco _ (hb t ht h0), haf t ht]
  exact h t ht h0

/-- `ScAffX` under the same frame (off `d`). -/
theorem ScAffX.keep {s s' : S} {d : U64} (h : ScAffX st T d s)
    (hb : ∀ t ∈ T, t ≠ d → L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Scs)
    (hsc : ∀ t ∈ T, t ≠ d → L.mem s' (scA t) = L.mem s (scA t))
    (hco : ∀ c ∈ Scs, L.mem s' (scCoreA c) = L.mem s (scCoreA c))
    (haf : ∀ t ∈ T, t ≠ d → L.mem s' (affA t) = L.mem s (affA t)) : ScAffX st T d s' := fun t ht hne h0 => by
  rw [hsc t ht hne] at h0 ⊢
  rw [hco _ (hb t ht hne h0), haf t ht hne]
  exact h t ht hne h0

/-- **Binding `d`** (`donate`/`bind_tcb`'s SC writes): the other threads keep
their `SC` fields, the `CORE` words and affinities are kept, so `ScAff` holds
off `d`. -/
theorem ScAff.pairX {s s' : S} {d : U64} (h : ScAff st T s)
    (hb : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Scs)
    (hsc : ∀ t ∈ T, t ≠ d → L.mem s' (scA t) = L.mem s (scA t))
    (hco : ∀ c ∈ Scs, L.mem s' (scCoreA c) = L.mem s (scCoreA c))
    (haf : ∀ t ∈ T, L.mem s' (affA t) = L.mem s (affA t)) : ScAffX st T d s' :=
  ScAffX.keep (h.x d) (fun t ht _ => hb t ht) hsc hco fun t ht _ => haf t ht

/-- **The `CORE` write of the SC `c` bound to `i`** (`SchedControl`
configure): no other thread holds `c`, so `ScAff` holds off `i`. -/
theorem ScAff.coreX {s s' : S} {c i : U64} (h : ScAff st T s)
    (hb : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Scs)
    (hu : ∀ t ∈ T, t ≠ i → L.mem s (scA t) ≠ c)
    (hsc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t))
    (hco : ∀ c' ∈ Scs, c' ≠ c → L.mem s' (scCoreA c') = L.mem s (scCoreA c'))
    (haf : ∀ t ∈ T, L.mem s' (affA t) = L.mem s (affA t)) : ScAffX st T i s' := fun t ht hne h0 => by
  rw [hsc t ht] at h0 ⊢
  rw [hco _ (hb t ht h0) (hu t ht hne), haf t ht]
  exact h t ht h0

/-- **`migrate_tcb`'s affinity write** (`d` to its SC's core) leaves `ScAffX`. -/
theorem ScAffX.restore {s s' : S} {d : U64} (h : ScAffX st T d s)
    (hb : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Scs)
    (hsc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t))
    (hco : ∀ c ∈ Scs, L.mem s' (scCoreA c) = L.mem s (scCoreA c))
    (haf : ∀ t ∈ T, t ≠ d → L.mem s' (affA t) = L.mem s (affA t))
    (hd : d ∈ T → L.mem s (scA d) ≠ 0#u64 → L.mem s' (affA d) = L.mem s (scCoreA (L.mem s (scA d)))) :
    ScAff st T s' := by
  refine ScAffX.full (ScAffX.keep h (fun t ht _ => hb t ht) (fun t ht _ => hsc t ht) hco haf) fun hdT h0 => ?_
  rw [hsc d hdT] at h0 ⊢
  rw [hco _ (hb d hdT h0), hd hdT h0]

/-- `ScAff` holds when no thread has an SC (the zeroed root thread at boot). -/
theorem ScAff.of_unbound {s : S} (h : ∀ t ∈ T, L.mem s (scA t) = 0#u64) : ScAff st T s :=
  fun t ht h0 => absurd (h t ht) h0

/-- **What P2 reads**: a thread with an SC runs on its SC's core. -/
theorem ScAff.core_eq {s : S} {t : U64} (h : ScAff st T s) (ht : t ∈ T) (h0 : L.mem s (scA t) ≠ 0#u64) :
    L.mem s (affA t) = L.mem s (scCoreA (L.mem s (scA t))) := (h t ht h0).symm

end

end Fl4Proofs.P1

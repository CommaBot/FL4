/-
P2 (DESIGN.md §9): transaction soundness, proved once for the runtime.

An abstract model of `fl4-store` (crates/fl4-store/src/tx.rs) and the serial
gate of `fl4-sync`: kernel entries on any number of cores run as
transactions whose steps interleave arbitrarily, or as serial entries.

* A kernel entry's body is a `Prog`: it reads memory (what it does next may
  depend on the values), writes memory and queues Arch effects.
* `begin` reads the version clock. A read of a word the transaction wrote
  returns the buffered value; any other read is valid if the word's stripe
  is unlocked and its version is no newer than the start clock, and dooms
  the transaction otherwise. A doomed transaction reads 0 and never commits.
* Commit locks the stripes it writes (one step per stripe, in any order and
  interleaved with everything else). With the locks held it advances the
  clock, checks the read set, writes the buffer out, publishes the new
  version and releases the locks. That last part is one step here: on
  hardware it runs while every stripe it writes is locked, so no other core
  can read or validate against those stripes in between (fl4-sim tests that
  the implementation keeps this promise, DESIGN.md §9 point (4)).
* A transaction that wrote nothing commits without checking its reads,
  as tx.rs does.
* A transaction may be doomed (an irrevocable operation, a full buffer) or
  given up at any step.
* A serial entry runs its body directly on memory while no transaction is
  active: the gate closes, waits for running transactions, and keeps new
  ones out.

The theorem (`sound`): in every reachable state, memory is what running
the updating entries (committed writers and serial entries) one after
another in commit order produces, each from the memory the previous one
left; every read-only transaction's effects are what its body produces on
one of the memories of that sequence (the one at its start); and the
Arch effects applied are exactly the committed entries' effects, in commit
order. So aborted transactions leave no trace, and each committed one saw
one consistent snapshot.
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.Basic

namespace Fl4Proofs.P2

abbrev Addr := Nat
abbrev Val := Nat
abbrev Mem := Addr → Val

/-- A kernel entry's body, as the runtime sees it. -/
inductive Prog (E : Type) where
  | done
  | read (a : Addr) (k : Val → Prog E)
  | write (a : Addr) (v : Val) (k : Prog E)
  | effect (e : E) (k : Prog E)

variable {E : Type}

/-- The serial semantics: run a body directly on memory. -/
def run : Prog E → Mem → List E → Mem × List E
  | .done, m, l => (m, l)
  | .read a k, m, l => run (k (m a)) m l
  | .write a v k, m, l => run k (Function.update m a v) l
  | .effect e k, m, l => run k m (l ++ [e])

/-- A write buffer, newest write first. -/
abbrev Buf := List (Addr × Val)

def lookup : Buf → Addr → Option Val
  | [], _ => none
  | (b, v) :: r, a => if b = a then some v else lookup r a

/-- Memory with the buffer written out. -/
def applyBuf : Buf → Mem → Mem
  | [], m => m
  | (b, v) :: r, m => Function.update (applyBuf r m) b v

theorem applyBuf_apply (wb : Buf) (m : Mem) (a : Addr) :
    applyBuf wb m a = (lookup wb a).getD (m a) := by
  induction wb with
  | nil => rfl
  | cons x r ih =>
    obtain ⟨b, v⟩ := x
    by_cases h : b = a
    · subst h; simp [applyBuf, lookup]
    · simp [applyBuf, lookup, h, Function.update, Ne.symm h, ih]

/-- `Exec m body p wb ef rd`: running `body` against memory `m`, with the
transaction's own writes visible to its later reads, reached `p`, having
buffered `wb`, queued the effects `ef` and read the addresses `rd` from
memory. -/
inductive Exec (m : Mem) (body : Prog E) : Prog E → Buf → List E → List Addr → Prop
  | start : Exec m body body [] [] []
  | readMem {a k wb ef rd} : Exec m body (.read a k) wb ef rd → lookup wb a = none →
      Exec m body (k (m a)) wb ef (a :: rd)
  | readBuf {a k wb ef rd v} : Exec m body (.read a k) wb ef rd → lookup wb a = some v →
      Exec m body (k v) wb ef rd
  | write {a v k wb ef rd} : Exec m body (.write a v k) wb ef rd →
      Exec m body k ((a, v) :: wb) ef rd
  | effect {e k wb ef rd} : Exec m body (.effect e k) wb ef rd →
      Exec m body k wb (ef ++ [e]) rd

/-- An execution depends on memory only at the addresses it read. -/
theorem Exec.congr {m m' : Mem} {body p : Prog E} {wb ef rd}
    (h : Exec m body p wb ef rd) (hm : ∀ a ∈ rd, m a = m' a) : Exec m' body p wb ef rd := by
  induction h with
  | start => exact .start
  | @readMem a k wb ef rd _ hl ih =>
    have ha : m a = m' a := hm a (by simp)
    rw [ha]
    exact .readMem (ih fun x hx => hm x (by simp [hx])) hl
  | readBuf _ hl ih => exact .readBuf (ih hm) hl
  | write _ ih => exact .write (ih hm)
  | effect _ ih => exact .effect (ih hm)

/-- Buffered execution agrees with the serial semantics. -/
theorem Exec.run_eq {m : Mem} {body p : Prog E} {wb ef rd}
    (h : Exec m body p wb ef rd) (l : List E) :
    run body m l = run p (applyBuf wb m) (l ++ ef) := by
  induction h with
  | start => simp [applyBuf]
  | readMem _ hl ih => rw [ih]; simp [run, applyBuf_apply, hl]
  | readBuf _ hl ih => rw [ih]; simp [run, applyBuf_apply, hl]
  | write _ ih => rw [ih]; simp [run, applyBuf]
  | effect _ ih => rw [ih]; simp [run]

/-- A completed execution: the serial run's result. -/
theorem Exec.run_done {m : Mem} {body : Prog E} {wb ef rd}
    (h : Exec m body .done wb ef rd) : run body m [] = (applyBuf wb m, ef) := by
  rw [h.run_eq]; simp [run]

/-- A transaction's state on its core. -/
structure Tx (E : Type) where
  body : Prog E
  prog : Prog E
  rv : Nat
  wb : Buf
  effs : List E
  rd : List Addr
  doomed : Bool

/-- What committed: a body that updated memory from `before` to `after`,
or a read-only one that ran on `m`; both queued `effs`. -/
inductive Event (E : Type) where
  | update (body : Prog E) (before after : Mem) (effs : List E)
  | observe (body : Prog E) (m : Mem) (effs : List E)

def Event.effs : Event E → List E
  | .update _ _ _ e => e
  | .observe _ _ e => e

/-- Commits, newest first: memory after them. -/
def histMem (m0 : Mem) : List (Event E) → Mem
  | [] => m0
  | .update _ _ a _ :: _ => a
  | .observe .. :: r => histMem m0 r

/-- Every memory of the sequence. -/
def histMems (m0 : Mem) : List (Event E) → List Mem
  | [] => [m0]
  | .update _ _ a _ :: r => a :: histMems m0 r
  | .observe .. :: r => histMems m0 r

/-- The effects applied, in commit order. -/
def histLog : List (Event E) → List E
  | [] => []
  | e :: r => histLog r ++ e.effs

/-- The history is serial: each update ran its body on the memory the
updates before it left, and each read-only body ran on one of those
memories and changed nothing. -/
inductive Serial (m0 : Mem) : List (Event E) → Prop
  | nil : Serial m0 []
  | update {evs b m' ef} : Serial m0 evs → run b (histMem m0 evs) [] = (m', ef) →
      Serial m0 (.update b (histMem m0 evs) m' ef :: evs)
  | observe {evs b m ef} : Serial m0 evs → m ∈ histMems m0 evs → run b m [] = (m, ef) →
      Serial m0 (.observe b m ef :: evs)

theorem histMem_mem (m0 : Mem) (evs : List (Event E)) : histMem m0 evs ∈ histMems m0 evs := by
  induction evs with
  | nil => simp [histMem, histMems]
  | cons e r ih => cases e <;> simp [histMem, histMems, ih]

/-- The machine: memory, the version table and its locks, the clock, each
core's transaction, the effects applied; and ghost state for the proof:
the memory at each clock value, and the history of commits. -/
structure St (E : Type) where
  mem : Mem
  ver : Nat → Nat
  owner : Nat → Option Nat
  clock : Nat
  txs : Nat → Option (Tx E)
  log : List E
  snap : Nat → Mem
  events : List (Event E)

def init (m0 : Mem) : St E :=
  { mem := m0, ver := fun _ => 0, owner := fun _ => none, clock := 0, txs := fun _ => none,
    log := [], snap := fun _ => m0, events := [] }

section
variable (stripe : Addr → Nat)

/-- The stripes a buffer writes. -/
def wstripes (wb : Buf) : List Nat := wb.map (fun x => stripe x.1)

/-- Locks held by core `c` released. -/
def release (owner : Nat → Option Nat) (c : Nat) : Nat → Option Nat :=
  fun s => if owner s = some c then none else owner s

/-- One step of core `c`. -/
inductive Step : St E → St E → Prop
  | begin {s c} (p : Prog E) : s.txs c = none →
      Step s { s with txs := Function.update s.txs c (some ⟨p, p, s.clock, [], [], [], false⟩) }
  | readDoomed {s c t a k} : s.txs c = some t → t.prog = .read a k → t.doomed = true →
      Step s { s with txs := Function.update s.txs c (some { t with prog := k 0 }) }
  | readBuf {s c t a k v} : s.txs c = some t → t.prog = .read a k → t.doomed = false →
      lookup t.wb a = some v →
      Step s { s with txs := Function.update s.txs c (some { t with prog := k v }) }
  | readMem {s c t a k} : s.txs c = some t → t.prog = .read a k → t.doomed = false →
      lookup t.wb a = none → s.ver (stripe a) ≤ t.rv → s.owner (stripe a) = none →
      Step s { s with txs := Function.update s.txs c (some { t with prog := k (s.mem a), rd := (a :: t.rd) }) }
  | readConflict {s c t a k} : s.txs c = some t → t.prog = .read a k → t.doomed = false →
      lookup t.wb a = none → ¬ (s.ver (stripe a) ≤ t.rv ∧ s.owner (stripe a) = none) →
      Step s { s with txs := Function.update s.txs c (some { t with prog := k 0, doomed := true }) }
  | write {s c t a v k} : s.txs c = some t → t.prog = .write a v k →
      Step s { s with txs := Function.update s.txs c (some (if t.doomed then { t with prog := k } else { t with prog := k, wb := (a, v) :: t.wb })) }
  | effect {s c t e k} : s.txs c = some t → t.prog = .effect e k →
      Step s { s with txs := Function.update s.txs c (some { t with prog := k, effs := t.effs ++ [e] }) }
  | doom {s c t} : s.txs c = some t →
      Step s { s with txs := Function.update s.txs c (some { t with doomed := true }) }
  | abort {s c t} : s.txs c = some t →
      Step s { s with txs := Function.update s.txs c none, owner := release s.owner c }
  | lock {s c t st} : s.txs c = some t → st ∈ wstripes stripe t.wb → s.owner st = none →
      Step s { s with owner := Function.update s.owner st (some c) }
  | commitReadOnly {s c t} : s.txs c = some t → t.prog = .done → t.doomed = false → t.wb = [] →
      Step s { s with
        txs := Function.update s.txs c none,
        log := s.log ++ t.effs,
        events := (Event.observe t.body (s.snap t.rv) t.effs :: s.events) }
  | commit {s c t} : s.txs c = some t → t.prog = .done → t.doomed = false → t.wb ≠ [] →
      (∀ st ∈ wstripes stripe t.wb, s.owner st = some c) →
      (∀ a ∈ t.rd, s.ver (stripe a) ≤ t.rv ∧ (s.owner (stripe a) = none ∨ s.owner (stripe a) = some c)) →
      Step s { s with
        mem := applyBuf t.wb s.mem,
        ver := fun x => if x ∈ wstripes stripe t.wb then s.clock + 1 else s.ver x,
        owner := release s.owner c,
        clock := s.clock + 1,
        txs := Function.update s.txs c none,
        log := s.log ++ t.effs,
        snap := Function.update s.snap (s.clock + 1) (applyBuf t.wb s.mem),
        events := (Event.update t.body s.mem (applyBuf t.wb s.mem) t.effs :: s.events) }
  | serial {s} (p : Prog E) : (∀ c, s.txs c = none) →
      Step s { s with
        mem := (run p s.mem []).1,
        log := s.log ++ (run p s.mem []).2,
        snap := fun _ => (run p s.mem []).1,
        events := (Event.update p s.mem (run p s.mem []).1 (run p s.mem []).2 :: s.events) }

/-- States reachable from `init m0`. -/
inductive Reachable (m0 : Mem) : St E → Prop
  | init : Reachable m0 (init m0)
  | step {s s'} : Reachable m0 s → Step stripe s s' → Reachable m0 s'

/-- The proof's invariant. -/
structure Inv (m0 : Mem) (s : St E) : Prop where
  serial : Serial m0 s.events
  mem : s.mem = histMem m0 s.events
  log : s.log = histLog s.events
  snap_now : s.snap s.clock = s.mem
  /-- A word whose stripe's version is at most `k` has not changed since
  clock value `k`. -/
  snap_ver : ∀ a k, s.ver (stripe a) ≤ k → k ≤ s.clock → s.snap k a = s.mem a
  snap_hist : ∀ k ≤ s.clock, s.snap k ∈ histMems m0 s.events
  /-- A live transaction has run its body, so far, on the memory at its
  start clock. -/
  tx : ∀ c t, s.txs c = some t → t.rv ≤ s.clock ∧
    (t.doomed = false → Exec (s.snap t.rv) t.body t.prog t.wb t.effs t.rd)

theorem inv_init (m0 : Mem) : Inv stripe m0 (init m0 : St E) := by
  refine ⟨.nil, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro a k _ _; rfl
  · intro k _; simp [init, histMems]
  · intro c t h; simp [init] at h

theorem lookup_none_of_not_mem {wb : Buf} {a : Addr}
    (h : stripe a ∉ wstripes stripe wb) : lookup wb a = none := by
  induction wb with
  | nil => rfl
  | cons x r ih =>
    obtain ⟨b, v⟩ := x
    simp only [wstripes, List.map_cons, List.mem_cons, not_or] at h
    have hb : b ≠ a := fun e => h.1 (by rw [e])
    simp [lookup, hb, ih h.2]

/-- Updating one core's transaction, given what is known about it. -/
theorem tx_update {m0 : Mem} {s : St E} (I : Inv stripe m0 s) {c : Nat} {t' : Tx E}
    (hrv : t'.rv ≤ s.clock)
    (hex : t'.doomed = false → Exec (s.snap t'.rv) t'.body t'.prog t'.wb t'.effs t'.rd) :
    ∀ c' t, Function.update s.txs c (some t') c' = some t → t.rv ≤ s.clock ∧
      (t.doomed = false → Exec (s.snap t.rv) t.body t.prog t.wb t.effs t.rd) := by
  intro c' t h
  by_cases hc : c' = c
  · subst hc; simp at h; subst h; exact ⟨hrv, hex⟩
  · rw [Function.update_of_ne hc] at h; exact I.tx c' t h

theorem tx_remove {m0 : Mem} {s : St E} (I : Inv stripe m0 s) (c : Nat) :
    ∀ c' t, Function.update s.txs c none c' = some t → t.rv ≤ s.clock ∧
      (t.doomed = false → Exec (s.snap t.rv) t.body t.prog t.wb t.effs t.rd) := by
  intro c' t h
  by_cases hc : c' = c
  · subst hc; simp at h
  · rw [Function.update_of_ne hc] at h; exact I.tx c' t h

theorem inv_step {m0 : Mem} {s s' : St E} (I : Inv stripe m0 s) (h : Step stripe s s') :
    Inv stripe m0 s' := by
  cases h with
  | begin p hc =>
    refine { I with tx := tx_update stripe I (by simp) (fun _ => .start) }
  | readDoomed ht hp hd =>
    refine { I with tx := tx_update stripe I (I.tx _ _ ht).1 (by simp [hd]) }
  | readBuf ht hp hd hl =>
    rename_i c t a k v
    have ⟨hrv, hex⟩ := I.tx _ _ ht
    refine { I with tx := tx_update stripe I hrv (fun _ => ?_) }
    have e := hex hd; rw [hp] at e
    exact .readBuf e hl
  | readMem ht hp hd hl hv ho =>
    rename_i c t a k
    have ⟨hrv, hex⟩ := I.tx _ _ ht
    refine { I with tx := tx_update stripe I hrv (fun _ => ?_) }
    have e := hex hd; rw [hp] at e
    have hs : s.snap t.rv a = s.mem a := I.snap_ver a t.rv hv hrv
    simpa [hs] using Exec.readMem e hl
  | readConflict ht hp hd hl hv =>
    refine { I with tx := tx_update stripe I (I.tx _ _ ht).1 (by simp) }
  | write ht hp =>
    rename_i c t a v k
    have ⟨hrv, hex⟩ := I.tx _ _ ht
    refine { I with tx := tx_update stripe I (by split <;> simpa) (fun hd' => ?_) }
    cases hd : t.doomed
    · have e := hex hd; rw [hp] at e
      simpa [hd] using Exec.write e
    · simp [hd] at hd'
  | effect ht hp =>
    have ⟨hrv, hex⟩ := I.tx _ _ ht
    refine { I with tx := tx_update stripe I hrv (fun hd => ?_) }
    have e := hex hd; rw [hp] at e
    exact Exec.effect e
  | doom ht =>
    refine { I with tx := tx_update stripe I (I.tx _ _ ht).1 (by simp) }
  | abort ht =>
    refine { I with tx := tx_remove stripe I _ }
  | lock ht hst ho =>
    exact { I with }
  | commitReadOnly ht hp hd hw =>
    rename_i c t
    have ⟨hrv, hex⟩ := I.tx _ _ ht
    have e := hex hd; rw [hp, hw] at e
    have hrun := e.run_done
    simp only [applyBuf] at hrun
    refine ⟨.observe I.serial (I.snap_hist _ hrv) hrun, ?_, ?_, I.snap_now, I.snap_ver,
      I.snap_hist, tx_remove stripe I _⟩
    · simp [histMem, I.mem]
    · simp [histLog, Event.effs, I.log]
  | commit ht hp hd hw hown hrd =>
    rename_i c t
    have ⟨hrv, hex⟩ := I.tx _ _ ht
    have e := hex hd; rw [hp] at e
    -- The words it read have not changed since its start.
    have hsame : ∀ a ∈ t.rd, s.snap t.rv a = s.mem a := fun a ha =>
      I.snap_ver a t.rv (hrd a ha).1 hrv
    have hrun := (e.congr hsame).run_done
    have hm := I.mem
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Serial m0 (.update t.body s.mem (applyBuf t.wb s.mem) t.effs :: s.events)
      rw [hm] at hrun ⊢; exact .update I.serial hrun
    · simp [histMem]
    · simp [histLog, Event.effs, I.log]
    · simp
    · intro a k hv hk
      simp only at hv hk ⊢
      by_cases hkc : k = s.clock + 1
      · subst hkc; simp
      · have hk' : k ≤ s.clock := by omega
        rw [Function.update_of_ne hkc]
        by_cases hs : stripe a ∈ wstripes stripe t.wb
        · simp [hs] at hv; omega
        · simp [hs] at hv
          rw [I.snap_ver a k hv hk', applyBuf_apply, lookup_none_of_not_mem stripe hs]; rfl
    · intro k hk
      simp only at hk ⊢
      by_cases hkc : k = s.clock + 1
      · subst hkc; simp [histMems]
      · rw [Function.update_of_ne hkc]
        have := I.snap_hist k (by omega)
        simp [histMems, this]
    · intro c' t' h'
      by_cases hc : c' = c
      · subst hc; simp at h'
      · simp only at h'
        rw [Function.update_of_ne hc] at h'
        have ⟨hrv', hex'⟩ := I.tx c' t' h'
        refine ⟨by simp only; omega, fun hd' => ?_⟩
        show Exec (Function.update s.snap (s.clock + 1) (applyBuf t.wb s.mem) t'.rv) _ _ _ _ _
        rw [Function.update_of_ne (by omega)]
        exact hex' hd'
  | serial p hnone =>
    refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · show Serial m0 (.update p s.mem (run p s.mem []).1 (run p s.mem []).2 :: s.events)
      have hm := I.mem
      rw [hm]; exact .update I.serial (by rfl)
    · simp [histMem]
    · simp [histLog, Event.effs, I.log]
    · intro a k _ _; rfl
    · intro k _; simp [histMems]
    · intro c t h; simp [hnone c] at h

theorem inv_reachable {m0 : Mem} {s : St E} (h : Reachable stripe m0 s) : Inv stripe m0 s := by
  induction h with
  | init => exact inv_init stripe m0
  | step _ hs ih => exact inv_step stripe ih hs

/-- P2: every reachable state is explained by a serial history of the
committed entries. -/
theorem sound {m0 : Mem} {s : St E} (h : Reachable stripe m0 s) :
    Serial m0 s.events ∧ s.mem = histMem m0 s.events ∧ s.log = histLog s.events :=
  let I := inv_reachable stripe h
  ⟨I.serial, I.mem, I.log⟩

/-- A live transaction that is not doomed has read exactly the memory at
its start: one consistent snapshot, which is one of the history's
memories. -/
theorem snapshot {m0 : Mem} {s : St E} (h : Reachable stripe m0 s) {c : Nat} {t : Tx E}
    (ht : s.txs c = some t) (hd : t.doomed = false) :
    ∃ m ∈ histMems m0 s.events, Exec m t.body t.prog t.wb t.effs t.rd :=
  let I := inv_reachable stripe h
  have ⟨hrv, hex⟩ := I.tx c t ht
  ⟨s.snap t.rv, I.snap_hist _ hrv, hex hd⟩

end
end Fl4Proofs.P2

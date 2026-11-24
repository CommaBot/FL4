/-
P2 part (3) (DESIGN.md §9 "From serial to concurrent", §7): **the serial gate
and local paths serialize**, at the abstract level, once for the runtime.

## The model

* Memory is a word map `A → V` (`LawfulStore`'s functional view `mem` is one).
* A kernel entry's body is a `Prog`: a tree of single-word reads (what it does
  next may depend on the value), single-word writes, and attempts to take a
  lock (`fl4_store::lock`, a CAS that never waits: the body continues with the
  outcome). Every `fl4-core` entry is generic over `Store`, whose only memory
  operations are word reads and writes, so its body is such a tree. Its
  sequential meaning is `Run` (a lock attempt may have either outcome:
  a failed one is a decline, which the general path then repeats).
* Cores step one at a time (interleaving). A **local path is not atomic**: each
  of its reads, writes and lock attempts is a step of its own, interleaved
  arbitrarily with every other core's steps (`Step.rd`, `Step.wr`, `Step.lock`).
* The gate (`fl4_sync::SerialGate`): a core arms its active flag (`arm`), then
  loads `closed` and either enters the local path on an open gate (`enter`) or
  backs off (`back`). A serial entry takes the ticket (`take`; an open gate
  becomes draining, i.e. `closed = 1`, before any scan), scans the active flags
  one core at a time (`scan d`, only when it finds `d`'s flag clear), and once
  every core has been seen clear sets `closed = 2` (`drain`). Its body then runs
  (`serial`) and the release keeps the gate closed for a successor or opens it.
  The body is one step: the theorem `no_overlap` shows no local path is in
  progress while the gate is closed, and holders exclude each other by the
  ticket, so nothing interleaves with a body anyway.
* Ownership (DESIGN §7 "What a local path may write"): `own m x` says who owns
  word `x` in memory `m`: a core (its node state, its threads and SCs, its
  timer tree's links), a lock (the locked object's words and the queue links of
  threads queued on it), or the gate (everything else: read-only beside the
  gate). It is a function of memory, as in the DESIGN (a thread's queue links
  belong to the endpoint it is blocked on). A local path on core `c` *holds*
  owner `core c` and every lock it took (`Held`).
* The ownership map is ghost state of the configuration (`Cfg.own`); a serial
  step may replace it (retype, delete, migration and binding change it), which
  is sound because no local path is in progress then (`no_overlap`).
* Speculative reads (`Prog.rds`): a read that needs no ownership (an unlocked
  CSpace walk that may meet a slot another core is writing, a plan read before
  its locks). It reads memory; the sequential meaning `Run` lets it return any
  value, so a path's log entry is explained for whatever it saw there; that
  this changes nothing a serial run could not do is the path's refinement
  obligation (`PathObl.lean`).
* `Allowed s c`: core `c`'s next local-path access is permitted: a read of
  a word it holds or the gate owns; a write of a word it holds, which changes
  the owner of any word only between owners it holds (e.g. blocking a thread
  on a locked endpoint moves its queue links from the core to the lock).

## The theorems

* `no_overlap`: in every reachable state, while the gate is closed no local
  path is in progress (the Dekker handshake, *proved* here in the interleaving
  model: either the local path sees the closing gate and backs off, or the
  holder sees its flag and waits).
* `serializable`: in every reachable state there is a memory `H` that running
  the completed entries one after another, from the initial memory, in the
  order they completed (serial entries in the order they ran under the gate,
  local paths in the order they finished) produces (`RunAll`), and the memory
  equals `H` on every word no in-progress local path has written.
* `serializable_quiescent`: with no local path in progress the memory is
  exactly that serial run. `serializable_reach`: the same for every execution,
  under the footprint premise below.
* `within_unchanged` / `within_frame`: a body whose every access lies in `F`
  (`Within F p`) has the denotational footprint properties (a) words outside
  `F` unchanged, (b) runs from states agreeing on `F` can end agreeing on `F`.
* `denotational_insufficient`: the converse fails, and matters: a body `p` with
  (a) and (b) for `F = {w}` (it reads `z` twice and writes `w` whether the two
  reads agree) and a body `q` writing only `z`, interleaved, end in a memory no
  serial order of the two produces. So (a)+(b) of the sequential meaning do
  not suffice for commutation: the per-path obligation must bound every
  *access* (reads included), which is what `Allowed` states.

## Premises (nothing else is assumed)

* `FootprintOK s0` [W] (only in `serializable_reach`; `serializable` and
  the others quantify over `GReach`, executions whose local steps are
  `Allowed`, and need no premise): every local-path access in every execution
  is `Allowed`. This is P2 obligation (2), footprint, in its trace form, for
  the ownership map the DESIGN's footprint list describes: each local path
  reads only words its core or its locks own or that change only under the
  gate, and writes only words its core or its locks own. Per-path proofs are
  other lines' work; `fl4-sim`'s footprint oracle checks the write half on
  every local path it runs (the read half, DESIGN §7 "every other kernel word
  it reads changes only under the gate", is not checked by the oracle).
* [P] Sequential consistency for the gate and lock words (`fl4-sync`,
  `fl4-store`, both in `TRUSTED`): the interleaving semantics is the
  processor's behaviour for this protocol. Concretely: the active-flag store
  and the `closed` store are SeqCst and each is followed (fence) by the load of
  the other's word, so the two-core Dekker handshake behaves as interleaved
  (x86 locked stores, AArch64 `dmb`); a lock CAS and the ticket fetch-add are
  atomic; `leave_local`'s release and the drain's acquire fence order a
  finished local path's writes before the serial entry, and lock
  release/acquire order a local path's writes before the next taker's. Data
  accesses of concurrently running local paths are race-free under
  `Allowed` (disjoint written words, gate-owned words only read), so by the
  DRF-SC guarantee of both memory models they behave as interleaved.
* Scope: kernel memory only. Arch effects (I/O ports, the timer's EOI) are not
  modelled; IPC buffers are user memory, where two cores' threads sharing a
  frame race as user code does (DESIGN §7), and are outside `own`'s domain.
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Lattice

namespace Fl4Proofs.P2.Serial

noncomputable section

/-! ## Bodies and their sequential meaning -/

/-- A kernel entry's body: single-word reads and writes, and lock attempts. -/
inductive Prog (A V L : Type) where
  | done
  | rd (a : A) (k : V → Prog A V L)
  | wr (a : A) (v : V) (k : Prog A V L)
  | lock (l : L) (k : Bool → Prog A V L)
  /-- A speculative read: of a word the path may not hold (an unlocked CSpace
  walk, a plan read before its locks). It reads memory like `rd`, but the
  sequential meaning lets it return any value. -/
  | rds (a : A) (k : V → Prog A V L)

variable {A V C L : Type} [DecidableEq A]

/-- The sequential meaning of a body: run alone on memory. A lock attempt may
succeed or fail (a failure is a decline). -/
inductive Run : Prog A V L → (A → V) → (A → V) → Prop
  | done (m : A → V) : Run .done m m
  | rd {a : A} {k : V → Prog A V L} {m m' : A → V} :
      Run (k (m a)) m m' → Run (.rd a k) m m'
  | wr {a : A} {v : V} {k : Prog A V L} {m m' : A → V} :
      Run k (Function.update m a v) m' → Run (.wr a v k) m m'
  | lock {l : L} {k : Bool → Prog A V L} {m m' : A → V} (b : Bool) :
      Run (k b) m m' → Run (.lock l k) m m'
  | rds {a : A} {k : V → Prog A V L} {m m' : A → V} (v : V) :
      Run (k v) m m' → Run (.rds a k) m m'

/-- Running a list of bodies one after another, each from the memory the
previous one left. -/
def RunAll : List (Prog A V L) → (A → V) → (A → V) → Prop
  | [], m, m' => m' = m
  | p :: l, m, m' => ∃ m1, Run p m m1 ∧ RunAll l m1 m'

theorem RunAll.snoc {l : List (Prog A V L)} {p : Prog A V L} {m m1 m2 : A → V}
    (h1 : RunAll l m m1) (h2 : Run p m1 m2) : RunAll (l ++ [p]) m m2 := by
  induction l generalizing m with
  | nil =>
    simp only [RunAll] at h1
    subst h1
    simp only [List.nil_append, RunAll]
    exact ⟨m2, h2, rfl⟩
  | cons q l ih =>
    simp only [RunAll] at h1
    obtain ⟨m', hq, hl⟩ := h1
    simp only [List.cons_append, RunAll]
    exact ⟨m', hq, ih hl⟩

/-! ## Ownership -/

/-- Who owns a word: a core, a lock, or the gate (written only under it). -/
inductive Owner (C L : Type) where
  | core (c : C)
  | lock (l : L)
  | gate

/-- Owners a local path on core `c` holds, given the lock table. -/
def Held (lk : L → Option C) (c : C) : Owner C L → Prop
  | .core d => d = c
  | .lock l => lk l = some c
  | .gate => False

theorem held_disj {lk : L → Option C} {c d : C} {o : Owner C L} (hcd : c ≠ d)
    (hc : Held lk c o) (hd : Held lk d o ∨ o = .gate) : False := by
  cases o with
  | core e =>
    have h1 : e = c := hc
    have h2 : e = d := by
      rcases hd with hd | hd
      · exact hd
      · cases hd
    exact hcd (h1.symm.trans h2)
  | lock l =>
    have h1 : lk l = some c := hc
    have h2 : lk l = some d := by
      rcases hd with hd | hd
      · exact hd
      · cases hd
    exact hcd (Option.some.inj (h1.symm.trans h2))
  | gate => exact hc

/-! ## Configurations and steps -/

/-- The gate's `closed` word: open (0), closing and draining (1), closed with
local paths excluded (2). -/
inductive Gate where
  | opn
  | draining
  | closed
  deriving DecidableEq

/-- What a core is doing. `arm`: active flag set, `closed` not yet loaded.
`loc p0 p W`: running the local path with body `p0`, `p` left to run, having
written the words `W` (ghost). `ser p`: holding the ticket with body `p`. -/
inductive Phase (A V L : Type) where
  | idle
  | arm (p : Prog A V L)
  | loc (p0 p : Prog A V L) (W : Set A)
  | ser (p : Prog A V L)

def Phase.IsLoc : Phase A V L → Prop
  | .loc .. => True
  | _ => False

/-- The active flag is set. -/
def Phase.Active : Phase A V L → Prop
  | .arm _ => True
  | .loc .. => True
  | _ => False

theorem Phase.idle_not_loc : ¬ (Phase.idle : Phase A V L).IsLoc := fun h => h
theorem Phase.arm_not_loc (p : Prog A V L) : ¬ (Phase.arm p).IsLoc := fun h => h
theorem Phase.ser_not_loc (p : Prog A V L) : ¬ (Phase.ser p).IsLoc := fun h => h

theorem Phase.active_of_isLoc {X : Phase A V L} (h : X.IsLoc) : X.Active := by
  cases X <;> first | exact h | trivial

structure Cfg (A V C L : Type) where
  mem : A → V
  gate : Gate
  holder : Option C
  /-- Cores the holder has seen with a clear active flag since it took the gate. -/
  seen : Set C
  lk : L → Option C
  ph : C → Phase A V L
  /-- The ownership map (ghost), replaced only by serial entries. -/
  own : (A → V) → A → Owner C L
  /-- Completed entries, in completion order (ghost). -/
  log : List (Prog A V L)

variable [DecidableEq C] [DecidableEq L]

/-- Release every lock core `c` holds. -/
def release (lk : L → Option C) (c : C) : L → Option C :=
  fun l => if lk l = some c then none else lk l

/-- One step of core `c`. -/
inductive Step (s : Cfg A V C L) (c : C) : Cfg A V C L → Prop
  /-- Set the active flag (SeqCst store, then fence). -/
  | arm (p : Prog A V L) : s.ph c = .idle →
      Step s c { s with ph := Function.update s.ph c (.arm p) }
  /-- Load `closed`: open, so the local path starts. -/
  | enter {p : Prog A V L} : s.ph c = .arm p → s.gate = .opn →
      Step s c { s with ph := Function.update s.ph c (.loc p p ∅) }
  /-- Load `closed`: not open, so clear the flag and back off. -/
  | back {p : Prog A V L} : s.ph c = .arm p → s.gate ≠ .opn →
      Step s c { s with ph := Function.update s.ph c .idle }
  | rd {p0 : Prog A V L} {a : A} {k : V → Prog A V L} {W : Set A} :
      s.ph c = .loc p0 (.rd a k) W →
      Step s c { s with ph := Function.update s.ph c (.loc p0 (k (s.mem a)) W) }
  /-- A speculative read: no ownership condition. -/
  | rds {p0 : Prog A V L} {a : A} {k : V → Prog A V L} {W : Set A} :
      s.ph c = .loc p0 (.rds a k) W →
      Step s c { s with ph := Function.update s.ph c (.loc p0 (k (s.mem a)) W) }
  | wr {p0 : Prog A V L} {a : A} {v : V} {k : Prog A V L} {W : Set A} :
      s.ph c = .loc p0 (.wr a v k) W →
      Step s c { s with mem := Function.update s.mem a v,
                        ph := Function.update s.ph c (.loc p0 k (insert a W)) }
  /-- A lock attempt: success only on a free lock; failure at any time. -/
  | lock {p0 : Prog A V L} {l : L} {k : Bool → Prog A V L} {W : Set A} (b : Bool) :
      s.ph c = .loc p0 (.lock l k) W → (b = true → s.lk l = none) →
      Step s c { s with lk := if b then Function.update s.lk l (some c) else s.lk,
                        ph := Function.update s.ph c (.loc p0 (k b) W) }
  /-- The local path ends: release its locks, clear the active flag. -/
  | leave {p0 : Prog A V L} {W : Set A} : s.ph c = .loc p0 .done W →
      Step s c { s with lk := release s.lk c, ph := Function.update s.ph c .idle,
                        log := s.log ++ [p0] }
  /-- Take the ticket; an open gate becomes draining (`closed = 1`). -/
  | take (p : Prog A V L) : s.ph c = .idle → s.holder = none →
      Step s c { s with holder := some c, seen := ∅, ph := Function.update s.ph c (.ser p),
                        gate := if s.gate = .opn then .draining else s.gate }
  /-- The holder reads core `d`'s active flag clear. -/
  | scan (d : C) : s.holder = some c → s.gate = .draining → ¬ (s.ph d).Active →
      Step s c { s with seen := insert d s.seen }
  /-- Every flag seen clear: `closed = 2`. -/
  | drain : s.holder = some c → s.gate = .draining → (∀ d, d ∈ s.seen) →
      Step s c { s with gate := .closed }
  /-- The serial body, then release (keeping the gate closed or opening it). -/
  | serial {p : Prog A V L} {m' : A → V} (keep : Bool) (own' : (A → V) → A → Owner C L) :
      s.holder = some c → s.gate = .closed → s.ph c = .ser p → Run p s.mem m' →
      Step s c { s with mem := m', holder := none, ph := Function.update s.ph c .idle,
                        gate := if keep then .closed else .opn, log := s.log ++ [p],
                        own := own' }

/-- Core `c` may read `x`: it holds `x`'s owner, or the gate owns `x`. -/
def Perm (s : Cfg A V C L) (c : C) (x : A) : Prop :=
  Held s.lk c (s.own s.mem x) ∨ s.own s.mem x = .gate

/-- Core `c`'s next local-path access respects ownership. -/
def Allowed (s : Cfg A V C L) (c : C) : Prop :=
  match s.ph c with
  | .loc _ (.rd a _) _ => Perm s c a
  | .loc _ (.wr a v _) _ =>
      Held s.lk c (s.own s.mem a) ∧
      ∀ x, s.own (Function.update s.mem a v) x ≠ s.own s.mem x →
        Held s.lk c (s.own s.mem x) ∧ Held s.lk c (s.own (Function.update s.mem a v) x)
  | _ => True

/-- Executions whose local-path accesses respect ownership. -/
inductive GReach (s0 : Cfg A V C L) : Cfg A V C L → Prop
  | refl : GReach s0 s0
  | step {s s' : Cfg A V C L} {c : C} :
      GReach s0 s → Allowed s c → Step s c s' → GReach s0 s'

/-- All executions. -/
inductive Reach (s0 : Cfg A V C L) : Cfg A V C L → Prop
  | refl : Reach s0 s0
  | step {s s' : Cfg A V C L} {c : C} : Reach s0 s → Step s c s' → Reach s0 s'

/-- No local path in progress. -/
def NoLoc (s : Cfg A V C L) : Prop := ∀ d, ¬ (s.ph d).IsLoc

/-- A start: nothing completed, no local path in progress. -/
def Init (s0 : Cfg A V C L) : Prop := s0.log = [] ∧ NoLoc s0

/-- **Footprint premise** [W]: every local-path access of every execution
respects ownership (P2 obligation (2) in trace form, per local path). -/
def FootprintOK (s0 : Cfg A V C L) : Prop :=
  ∀ s, GReach s0 s → ∀ c, Allowed s c

/-! ## The invariant -/

/-- `m` on `W`, `n` elsewhere. -/
def mix (W : Set A) (m n : A → V) : A → V :=
  fun x => @ite _ (x ∈ W) (Classical.propDecidable _) (m x) (n x)

theorem mix_mem {W : Set A} {m n : A → V} {x : A} (h : x ∈ W) : mix W m n x = m x := by
  show @ite _ (x ∈ W) (Classical.propDecidable _) (m x) (n x) = m x
  exact if_pos h

theorem mix_nmem {W : Set A} {m n : A → V} {x : A} (h : x ∉ W) : mix W m n x = n x := by
  show @ite _ (x ∈ W) (Classical.propDecidable _) (m x) (n x) = n x
  exact if_neg h

theorem mix_empty {m n : A → V} : mix ∅ m n = n := by
  funext x; exact mix_nmem (by simp)

theorem mix_upd {W : Set A} {m n : A → V} {a : A} {v : V} :
    Function.update (mix W m n) a v = mix (insert a W) (Function.update m a v) n := by
  funext x
  by_cases hx : x = a
  · subst hx
    rw [Function.update_self, mix_mem (Set.mem_insert x W), Function.update_self]
  · rw [Function.update_of_ne hx]
    by_cases hw : x ∈ W
    · rw [mix_mem hw, mix_mem (Set.mem_insert_of_mem a hw), Function.update_of_ne hx]
    · rw [mix_nmem hw, mix_nmem (fun h => (Set.mem_insert_iff.mp h).elim hx hw)]

/-- What is known of an in-progress local path on core `d` with body `p0`,
`p` left to run, having written `W`: it holds the owners of what it wrote, and
running `p` from any memory that agrees with the history `H` on what `d` may
read, with `d`'s writes so far in place, is a run of `p0` from that memory. -/
structure LocInv (s : Cfg A V C L) (H : A → V) (d : C)
    (p0 p : Prog A V L) (W : Set A) : Prop where
  held : ∀ x ∈ W, Held s.lk d (s.own s.mem x)
  sim : ∀ n n' : A → V, (∀ x, Perm s d x → n x = H x) →
    Run p (mix W s.mem n) n' → Run p0 n n'

/-- The invariant, with `H` the memory of the serial history. -/
structure InvH (m0 : A → V) (s : Cfg A V C L)
    (H : A → V) : Prop where
  hist : RunAll s.log m0 H
  clo : s.gate = .closed → NoLoc s
  drn : s.gate = .draining → ∀ d ∈ s.seen, ¬ (s.ph d).IsLoc
  agree : ∀ x, (∀ d p0 p W, s.ph d = .loc p0 p W → x ∉ W) → s.mem x = H x
  loc : ∀ d p0 p W, s.ph d = .loc p0 p W → LocInv s H d p0 p W


theorem LocInv.mono {s s' : Cfg A V C L} {H H' : A → V} {d : C} {p0 p : Prog A V L}
    {W : Set A} (I : LocInv s H d p0 p W)
    (hheld : ∀ x, Held s.lk d (s.own s.mem x) → Held s'.lk d (s'.own s'.mem x))
    (hperm : ∀ x, Perm s d x → Perm s' d x)
    (hH : ∀ x, Perm s d x → H' x = H x)
    (hmem : ∀ x ∈ W, s'.mem x = s.mem x) :
    LocInv s' H' d p0 p W where
  held x hx := hheld x (I.held x hx)
  sim n n' hn hr := by
    have he : mix W s'.mem n = mix W s.mem n := by
      funext x
      by_cases hx : x ∈ W
      · rw [mix_mem hx, mix_mem hx, hmem x hx]
      · rw [mix_nmem hx, mix_nmem hx]
    exact I.sim n n' (fun x hx => (hn x (hperm x hx)).trans (hH x hx)) (by rw [← he]; exact hr)

theorem upd_loc {f : C → Phase A V L} {c d : C} {X : Phase A V L} {p0 p : Prog A V L}
    {W : Set A} (h : Function.update f c X d = .loc p0 p W) :
    (d = c ∧ X = .loc p0 p W) ∨ (d ≠ c ∧ f d = .loc p0 p W) := by
  by_cases hdc : d = c
  · subst hdc; rw [Function.update_self] at h; exact Or.inl ⟨rfl, h⟩
  · rw [Function.update_of_ne hdc] at h; exact Or.inr ⟨hdc, h⟩

theorem upd_isLoc {f : C → Phase A V L} {c d : C} {X : Phase A V L} (hX : ¬ X.IsLoc)
    (h : (Function.update f c X d).IsLoc) : d ≠ c ∧ (f d).IsLoc := by
  by_cases hdc : d = c
  · subst hdc; rw [Function.update_self] at h; exact absurd h hX
  · rw [Function.update_of_ne hdc] at h; exact ⟨hdc, h⟩

theorem upd_nonloc {f : C → Phase A V L} {c : C} {X : Phase A V L} (hX : ¬ X.IsLoc)
    (hc : ¬ (f c).IsLoc) (d : C) (q0 q : Prog A V L) (U : Set A) :
    Function.update f c X d = .loc q0 q U ↔ f d = .loc q0 q U := by
  by_cases hdc : d = c
  · subst hdc
    rw [Function.update_self]
    constructor
    · intro h; exact absurd (by rw [h]; trivial) hX
    · intro h; exact absurd (by rw [h]; trivial) hc
  · rw [Function.update_of_ne hdc]

theorem gate_mono {s s' : Cfg A V C L}
    (hclo : s.gate = .closed → NoLoc s)
    (hdrn : s.gate = .draining → ∀ d ∈ s.seen, ¬ (s.ph d).IsLoc)
    (hg : s'.gate = s.gate) (hs : s'.seen = s.seen)
    (hl : ∀ d, (s'.ph d).IsLoc → (s.ph d).IsLoc) :
    (s'.gate = .closed → NoLoc s') ∧
      (s'.gate = .draining → ∀ d ∈ s'.seen, ¬ (s'.ph d).IsLoc) :=
  ⟨fun h d hd => hclo (hg.symm.trans h) d (hl d hd),
   fun h d hm hd => hdrn (hg.symm.trans h) d (by rw [← hs]; exact hm) (hl d hd)⟩

/-- Steps that change neither memory, locks nor log, nor which cores run
which local path. -/
theorem InvH.frame {m0 : A → V} {s s' : Cfg A V C L} {H : A → V} (I : InvH m0 s H)
    (hmem : s'.mem = s.mem) (hlk : s'.lk = s.lk) (hown : s'.own = s.own) (hlog : s'.log = s.log)
    (hl : ∀ d q0 q U, s'.ph d = .loc q0 q U → s.ph d = .loc q0 q U)
    (hl' : ∀ d q0 q U, s.ph d = .loc q0 q U → s'.ph d = .loc q0 q U)
    (hclo : s'.gate = .closed → NoLoc s')
    (hdrn : s'.gate = .draining → ∀ d ∈ s'.seen, ¬ (s'.ph d).IsLoc) :
    InvH m0 s' H where
  hist := by rw [hlog]; exact I.hist
  clo := hclo
  drn := hdrn
  agree x hx := by
    rw [hmem]; exact I.agree x (fun d q0 q U hd => hx d q0 q U (hl' d q0 q U hd))
  loc d q0 q U hd :=
    (I.loc d q0 q U (hl d q0 q U hd)).mono
      (fun x h => by rw [hlk, hmem, hown]; exact h)
      (fun x h => by unfold Perm; rw [hlk, hmem, hown]; exact h)
      (fun _ _ => rfl) (fun x _ => by rw [hmem])

/-- A step of core `c` inside its local path. -/
theorem InvH.locstep {m0 : A → V} {s s' : Cfg A V C L} {H : A → V} (I : InvH m0 s H)
    {c : C} {p0 p p' : Prog A V L} {W W' : Set A}
    (hc : s.ph c = .loc p0 p W)
    (hph : s'.ph = Function.update s.ph c (.loc p0 p' W'))
    (hlog : s'.log = s.log) (hgate : s'.gate = s.gate) (hseen : s'.seen = s.seen)
    (hWW : W ⊆ W')
    (hmem : ∀ x, x ∉ W' → s'.mem x = s.mem x)
    (hheld : ∀ d, d ≠ c → ∀ x, Held s.lk d (s.own s.mem x) → Held s'.lk d (s'.own s'.mem x))
    (hperm : ∀ d, d ≠ c → ∀ x, Perm s d x → Perm s' d x)
    (hmemd : ∀ d, d ≠ c → ∀ q0 q U, s.ph d = .loc q0 q U → ∀ x ∈ U, s'.mem x = s.mem x)
    (hcinv : LocInv s' H c p0 p' W') : InvH m0 s' H := by
  have hl : ∀ d, (s'.ph d).IsLoc → (s.ph d).IsLoc := by
    intro d hd
    by_cases hdc : d = c
    · subst hdc; rw [hc]; trivial
    · rw [hph, Function.update_of_ne hdc] at hd; exact hd
  have hg := gate_mono I.clo I.drn hgate hseen hl
  refine ⟨by rw [hlog]; exact I.hist, hg.1, hg.2, ?_, ?_⟩
  · intro x hx
    have hxW' : x ∉ W' := hx c p0 p' W' (by rw [hph, Function.update_self])
    rw [hmem x hxW']
    apply I.agree
    intro d q0 q U hd
    by_cases hdc : d = c
    · subst hdc; rw [hc] at hd; cases hd; exact fun h => hxW' (hWW h)
    · exact hx d q0 q U (by rw [hph, Function.update_of_ne hdc]; exact hd)
  · intro d q0 q U hd
    rw [hph] at hd
    rcases upd_loc hd with ⟨rfl, he⟩ | ⟨hdc, hd⟩
    · cases he; exact hcinv
    · exact (I.loc d q0 q U hd).mono (hheld d hdc) (hperm d hdc) (fun _ _ => rfl)
        (hmemd d hdc q0 q U hd)

theorem inv_rd {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {c : C}
    {p0 : Prog A V L} {a : A} {k : V → Prog A V L} {W : Set A}
    (hc : s.ph c = .loc p0 (.rd a k) W) (hp : Perm s c a) :
    InvH m0 { s with ph := Function.update s.ph c (.loc p0 (k (s.mem a)) W) } H := by
  have Ic := I.loc c p0 _ W hc
  have hma : ∀ n : A → V, (∀ x, Perm s c x → n x = H x) → mix W s.mem n a = s.mem a := by
    intro n hn
    by_cases haW : a ∈ W
    · exact mix_mem haW
    · rw [mix_nmem haW, hn a hp]
      symm; apply I.agree
      intro d q0 q U hd haU
      by_cases hdc : d = c
      · subst hdc; rw [hc] at hd; cases hd; exact haW haU
      · exact held_disj hdc ((I.loc d q0 q U hd).held a haU) hp
  exact I.locstep (p' := k (s.mem a)) (W' := W) hc rfl rfl rfl rfl (subset_refl _)
    (fun _ _ => rfl) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ => rfl)
    { held := Ic.held
      sim := fun n n' hn hr => Ic.sim n n' hn (Run.rd (by rw [hma n hn]; exact hr)) }

theorem inv_rds {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {c : C}
    {p0 : Prog A V L} {a : A} {k : V → Prog A V L} {W : Set A}
    (hc : s.ph c = .loc p0 (.rds a k) W) :
    InvH m0 { s with ph := Function.update s.ph c (.loc p0 (k (s.mem a)) W) } H := by
  have Ic := I.loc c p0 _ W hc
  exact I.locstep (p' := k (s.mem a)) (W' := W) hc rfl rfl rfl rfl (subset_refl _)
    (fun _ _ => rfl) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ => rfl)
    { held := Ic.held
      sim := fun n n' hn hr => Ic.sim n n' hn (Run.rds _ hr) }

theorem inv_wr {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {c : C}
    {p0 : Prog A V L} {a : A} {v : V} {k : Prog A V L} {W : Set A}
    (hc : s.ph c = .loc p0 (.wr a v k) W)
    (ha : Held s.lk c (s.own s.mem a))
    (hmv : ∀ x, s.own (Function.update s.mem a v) x ≠ s.own s.mem x →
        Held s.lk c (s.own s.mem x) ∧ Held s.lk c (s.own (Function.update s.mem a v) x)) :
    InvH m0 { s with mem := Function.update s.mem a v,
                         ph := Function.update s.ph c (.loc p0 k (insert a W)) } H := by
  have Ic := I.loc c p0 _ W hc
  have hsame : ∀ d, d ≠ c → ∀ x, (Held s.lk d (s.own s.mem x) ∨ s.own s.mem x = .gate) →
      s.own (Function.update s.mem a v) x = s.own s.mem x := by
    intro d hdc x h
    by_contra hne
    exact held_disj (Ne.symm hdc) (hmv x hne).1 h
  have hcpres : ∀ x, Held s.lk c (s.own s.mem x) →
      Held s.lk c (s.own (Function.update s.mem a v) x) := by
    intro x h
    by_cases he : s.own (Function.update s.mem a v) x = s.own s.mem x
    · rw [he]; exact h
    · exact (hmv x he).2
  refine I.locstep (p' := k) (W' := insert a W) hc rfl rfl rfl rfl (Set.subset_insert a W)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact Function.update_of_ne (fun h => hx (by rw [h]; exact Set.mem_insert a W)) _ _
  · intro d hdc x h
    show Held s.lk d (s.own (Function.update s.mem a v) x)
    rw [hsame d hdc x (Or.inl h)]; exact h
  · intro d hdc x h
    show Held s.lk d (s.own (Function.update s.mem a v) x) ∨
      s.own (Function.update s.mem a v) x = .gate
    rw [hsame d hdc x h]; exact h
  · intro d hdc q0 q U hd x hx
    have hxa : x ≠ a := by
      rintro rfl
      exact held_disj (Ne.symm hdc) ha (Or.inl ((I.loc d q0 q U hd).held x hx))
    exact Function.update_of_ne hxa _ _
  · refine { held := ?_, sim := ?_ }
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hcpres x ha
      · exact hcpres x (Ic.held x hx)
    · intro n n' hn hr
      refine Ic.sim n n' (fun x hx => hn x ?_) (Run.wr (by rw [mix_upd]; exact hr))
      show Held s.lk c (s.own (Function.update s.mem a v) x) ∨
        s.own (Function.update s.mem a v) x = .gate
      by_cases he : s.own (Function.update s.mem a v) x = s.own s.mem x
      · rw [he]; exact hx
      · exact Or.inl (hmv x he).2

theorem held_lock {lk : L → Option C} {l : L} {c d : C} {b : Bool}
    (hb : b = true → lk l = none) {o : Owner C L} (h : Held lk d o) :
    Held (if b then Function.update lk l (some c) else lk) d o := by
  cases b with
  | false => rw [if_neg (by decide)]; exact h
  | true =>
    rw [if_pos rfl]
    cases o with
    | core e => exact h
    | lock l' =>
      have h' : lk l' = some d := h
      by_cases hl : l' = l
      · subst hl; rw [hb rfl] at h'; cases h'
      · show Function.update lk l (some c) l' = some d
        rw [Function.update_of_ne hl]; exact h'
    | gate => exact h

theorem inv_lock {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {c : C}
    {p0 : Prog A V L} {l : L} {k : Bool → Prog A V L} {W : Set A}
    (hc : s.ph c = .loc p0 (.lock l k) W) (b : Bool) (hb : b = true → s.lk l = none) :
    InvH m0 { s with lk := if b then Function.update s.lk l (some c) else s.lk,
                         ph := Function.update s.ph c (.loc p0 (k b) W) } H := by
  have Ic := I.loc c p0 _ W hc
  exact I.locstep (p' := k b) (W' := W) hc rfl rfl rfl rfl (subset_refl _)
    (fun _ _ => rfl) (fun _ _ _ h => held_lock hb h)
    (fun _ _ _ h => Or.imp (held_lock hb) id h) (fun _ _ _ _ _ _ _ _ => rfl)
    { held := fun x hx => held_lock hb (Ic.held x hx)
      sim := fun n n' hn hr =>
        Ic.sim n n' (fun x hx => hn x (Or.imp (held_lock hb) id hx)) (Run.lock b hr) }

theorem held_release {lk : L → Option C} {c d : C} (hdc : d ≠ c) {o : Owner C L}
    (h : Held lk d o) : Held (release lk c) d o := by
  cases o with
  | core e => exact h
  | lock l =>
    have h' : lk l = some d := h
    show (if lk l = some c then none else lk l) = some d
    rw [if_neg (by rw [h']; exact fun e => hdc (Option.some.inj e))]; exact h'
  | gate => exact h

theorem inv_leave {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {c : C}
    {p0 : Prog A V L} {W : Set A} (hc : s.ph c = .loc p0 .done W) :
    InvH m0 { s with lk := release s.lk c, ph := Function.update s.ph c .idle,
                         log := s.log ++ [p0] } (mix W s.mem H) := by
  have Ic := I.loc c p0 _ W hc
  have hl : ∀ d, ((Function.update s.ph c Phase.idle) d).IsLoc → (s.ph d).IsLoc :=
    fun d hd => (upd_isLoc Phase.idle_not_loc hd).2
  refine ⟨RunAll.snoc I.hist (Ic.sim H _ (fun _ _ => rfl) (Run.done _)),
    fun h d hd => I.clo h d (hl d hd), fun h d hm hd => I.drn h d hm (hl d hd), ?_, ?_⟩
  · intro x hx
    show s.mem x = mix W s.mem H x
    by_cases hxW : x ∈ W
    · rw [mix_mem hxW]
    · rw [mix_nmem hxW]
      apply I.agree
      intro d q0 q U hd
      by_cases hdc : d = c
      · subst hdc; rw [hc] at hd; cases hd; exact hxW
      · exact hx d q0 q U (by
          show Function.update s.ph c .idle d = _
          rw [Function.update_of_ne hdc]; exact hd)
  · intro d q0 q U hd
    rcases upd_loc hd with ⟨_, he⟩ | ⟨hdc, hd⟩
    · cases he
    · exact (I.loc d q0 q U hd).mono (fun x h => held_release hdc h)
        (fun x h => Or.imp (held_release hdc) id h)
        (fun x hp => mix_nmem (fun hxW => held_disj (Ne.symm hdc) (Ic.held x hxW) hp))
        (fun _ _ => rfl)

theorem inv_phase {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {c : C}
    {X : Phase A V L} (hX : ¬ X.IsLoc) (hc : ¬ (s.ph c).IsLoc) :
    InvH m0 { s with ph := Function.update s.ph c X } H :=
  I.frame rfl rfl rfl rfl (fun d q0 q U h => (upd_nonloc hX hc d q0 q U).mp h)
    (fun d q0 q U h => (upd_nonloc hX hc d q0 q U).mpr h)
    (fun h d hd => I.clo h d (upd_isLoc hX hd).2)
    (fun h d hm hd => I.drn h d hm (upd_isLoc hX hd).2)

theorem inv_enter {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {c : C}
    {p : Prog A V L} (hc : s.ph c = .arm p) (hg : s.gate = .opn) :
    InvH m0 { s with ph := Function.update s.ph c (.loc p p ∅) } H := by
  have hnc : ∀ d q0 q U, s.ph d = .loc q0 q U → d ≠ c := by
    rintro d q0 q U hd rfl; rw [hc] at hd; cases hd
  refine ⟨I.hist, fun h => ?_, fun h => ?_, ?_, ?_⟩
  · have h' : s.gate = .closed := h
    rw [hg] at h'; cases h'
  · have h' : s.gate = .draining := h
    rw [hg] at h'; cases h'
  · intro x hx
    apply I.agree
    intro d q0 q U hd
    exact hx d q0 q U (by
      show Function.update s.ph c _ d = _
      rw [Function.update_of_ne (hnc d q0 q U hd)]; exact hd)
  · intro d q0 q U hd
    rcases upd_loc hd with ⟨rfl, he⟩ | ⟨hdc, hd⟩
    · cases he
      exact { held := fun x hx => absurd hx (by simp)
              sim := fun n n' _ hr => by rw [mix_empty] at hr; exact hr }
    · exact (I.loc d q0 q U hd).mono (fun _ h => h) (fun _ h => h) (fun _ _ => rfl)
        (fun _ _ => rfl)

theorem inv_take {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {c : C}
    (p : Prog A V L) (hc : s.ph c = .idle) :
    InvH m0 { s with holder := some c, seen := ∅, ph := Function.update s.ph c (.ser p),
                         gate := if s.gate = .opn then .draining else s.gate } H := by
  have hX : ¬ (Phase.ser p : Phase A V L).IsLoc := Phase.ser_not_loc p
  have hc' : ¬ (s.ph c).IsLoc := by rw [hc]; exact Phase.idle_not_loc
  refine I.frame rfl rfl rfl rfl (fun d q0 q U h => (upd_nonloc hX hc' d q0 q U).mp h)
    (fun d q0 q U h => (upd_nonloc hX hc' d q0 q U).mpr h) ?_ ?_
  · intro h d hd
    have h' : (if s.gate = .opn then Gate.draining else s.gate) = .closed := h
    by_cases hg : s.gate = .opn
    · rw [if_pos hg] at h'; cases h'
    · rw [if_neg hg] at h'; exact I.clo h' d (upd_isLoc hX hd).2
  · intro _ d hd
    have : d ∈ (∅ : Set C) := hd
    simp at this

theorem inv_scan {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H)
    (d : C) (hd : ¬ (s.ph d).Active) :
    InvH m0 { s with seen := insert d s.seen } H := by
  refine I.frame rfl rfl rfl rfl (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) I.clo ?_
  intro h e he hl
  rcases Set.mem_insert_iff.mp he with rfl | he
  · exact hd (Phase.active_of_isLoc hl)
  · exact I.drn h e he hl

theorem inv_drain {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H)
    (hg : s.gate = .draining) (hall : ∀ d, d ∈ s.seen) :
    InvH m0 { s with gate := .closed } H := by
  refine I.frame rfl rfl rfl rfl (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
    (fun _ d => I.drn hg d (hall d)) ?_
  intro h; cases h

theorem inv_serial {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {c : C}
    {p : Prog A V L} {m' : A → V} (keep : Bool) (own' : (A → V) → A → Owner C L)
    (hg : s.gate = .closed) (hr : Run p s.mem m') :
    InvH m0 { s with mem := m', holder := none, ph := Function.update s.ph c .idle,
                         gate := if keep then .closed else .opn, log := s.log ++ [p],
                         own := own' } m' := by
  have nl := I.clo hg
  have hmH : s.mem = H := by
    funext x
    exact I.agree x (fun d q0 q U hd => absurd (by rw [hd]; trivial) (nl d))
  have nl' : ∀ d, ¬ ((Function.update s.ph c Phase.idle) d).IsLoc :=
    fun d hd => nl d (upd_isLoc Phase.idle_not_loc hd).2
  refine ⟨RunAll.snoc I.hist (by rw [← hmH]; exact hr), fun _ => nl', fun _ d _ => nl' d,
    fun _ _ => rfl, ?_⟩
  intro d q0 q U hd
  have hd' : Function.update s.ph c Phase.idle d = .loc q0 q U := hd
  exact absurd (by rw [hd']; trivial) (nl' d)

theorem InvH.step {m0 : A → V} {s s' : Cfg A V C L} {H : A → V} {c : C}
    (I : InvH m0 s H) (hal : Allowed s c) (h : Step s c s') :
    ∃ H', InvH m0 s' H' := by
  cases h with
  | arm p hc => exact ⟨H, inv_phase I (Phase.arm_not_loc p) (by rw [hc]; exact Phase.idle_not_loc)⟩
  | enter hc hg => exact ⟨H, inv_enter I hc hg⟩
  | back hc _ => exact ⟨H, inv_phase I Phase.idle_not_loc (by rw [hc]; exact Phase.arm_not_loc _)⟩
  | rd hc =>
    simp only [Allowed, hc] at hal
    exact ⟨H, inv_rd I hc hal⟩
  | wr hc =>
    simp only [Allowed, hc] at hal
    exact ⟨H, inv_wr I hc hal.1 hal.2⟩
  | lock b hc hb => exact ⟨H, inv_lock I hc b hb⟩
  | rds hc => exact ⟨H, inv_rds I hc⟩
  | leave hc => exact ⟨_, inv_leave I hc⟩
  | take p hc _ => exact ⟨H, inv_take I p hc⟩
  | scan d _ _ hd => exact ⟨H, inv_scan I d hd⟩
  | drain _ hg hall => exact ⟨H, inv_drain I hg hall⟩
  | serial keep own' _ hg _ hr => exact ⟨_, inv_serial I keep own' hg hr⟩

theorem inv_init {s0 : Cfg A V C L} (h0 : Init s0) : InvH s0.mem s0 s0.mem where
  hist := by rw [h0.1]; rfl
  clo _ := h0.2
  drn _ d _ := h0.2 d
  agree _ _ := rfl
  loc d _ _ _ hd := absurd (by rw [hd]; trivial) (h0.2 d)

theorem greach_inv {s0 s : Cfg A V C L} (h0 : Init s0) (h : GReach s0 s) :
    ∃ H, InvH s0.mem s H := by
  induction h with
  | refl => exact ⟨_, inv_init h0⟩
  | step _ hal hs ih =>
    obtain ⟨H, I⟩ := ih
    exact I.step hal hs

/-! ## Main theorems -/

/-- **Serial entries and local paths never overlap** (the Dekker handshake of
§7, in the interleaving model): while the gate is closed, which a serial body
requires, no local path is in progress. -/
theorem no_overlap {s0 s : Cfg A V C L} (h0 : Init s0) (h : GReach s0 s) :
    s.gate = .closed → NoLoc s := by
  obtain ⟨H, I⟩ := greach_inv h0 h
  exact I.clo

/-- **Every execution is a serial one** (DESIGN §9, P2 (3)): in every reachable
state, running the completed entries one after another (serial entries in the
order they ran under the gate, local paths in the order they finished) from
the initial memory can give a memory `H` that the current memory equals on
every word no in-progress local path has written. -/
theorem serializable {s0 s : Cfg A V C L} (h0 : Init s0) (h : GReach s0 s) :
    ∃ H, RunAll s.log s0.mem H ∧
      ∀ x, (∀ d p0 p W, s.ph d = .loc p0 p W → x ∉ W) → s.mem x = H x := by
  obtain ⟨H, I⟩ := greach_inv h0 h
  exact ⟨H, I.hist, I.agree⟩

/-- With no local path in progress, memory is exactly a serial run of the
completed entries in completion order. -/
theorem serializable_quiescent {s0 s : Cfg A V C L} (h0 : Init s0) (h : GReach s0 s)
    (hq : NoLoc s) : RunAll s.log s0.mem s.mem := by
  obtain ⟨H, hH, hag⟩ := serializable h0 h
  have : s.mem = H := funext fun x =>
    hag x (fun d q0 q U hd => absurd (by rw [hd]; trivial) (hq d))
  rw [this]; exact hH

theorem reach_greach {s0 s : Cfg A V C L} (hfp : FootprintOK s0) (h : Reach s0 s) :
    GReach s0 s := by
  induction h with
  | refl => exact .refl
  | step _ hs ih => exact .step ih (hfp _ ih _) hs

/-- `serializable_quiescent` for every execution, under the footprint premise
`FootprintOK` [W]. -/
theorem serializable_reach {s0 s : Cfg A V C L} (h0 : Init s0) (hfp : FootprintOK s0)
    (h : Reach s0 s) (hq : NoLoc s) : RunAll s.log s0.mem s.mem :=
  serializable_quiescent h0 (reach_greach hfp h) hq

/-! ## Access footprints and the denotational properties -/

/-- Every access of the body lies in `F`. -/
inductive Within (F : Set A) : Prog A V L → Prop
  | done : Within F .done
  | rd {a : A} {k : V → Prog A V L} : a ∈ F → (∀ v, Within F (k v)) → Within F (.rd a k)
  | wr {a : A} {v : V} {k : Prog A V L} : a ∈ F → Within F k → Within F (.wr a v k)
  | lock {l : L} {k : Bool → Prog A V L} : (∀ b, Within F (k b)) → Within F (.lock l k)
  | rds {a : A} {k : V → Prog A V L} : a ∈ F → (∀ v, Within F (k v)) → Within F (.rds a k)

/-- (a) An access footprint is a write footprint. -/
theorem within_unchanged {F : Set A} {p : Prog A V L} {m m' : A → V} (hw : Within F p)
    (hr : Run p m m') : ∀ x ∉ F, m' x = m x := by
  induction hr with
  | done => intro _ _; rfl
  | rd _ ih => cases hw with | rd _ hk => exact ih (hk _)
  | @wr a v k m m' _ ih =>
    cases hw with
    | wr ha hk =>
      intro x hx
      rw [ih hk x hx, Function.update_of_ne (fun h => hx (by rw [h]; exact ha))]
  | lock b _ ih => cases hw with | lock hk => exact ih (hk b)
  | rds v _ ih => cases hw with | rds _ hk => exact ih (hk v)

/-- (b) An access footprint is a frame. -/
theorem within_frame {F : Set A} {p : Prog A V L} {m m' : A → V} (hw : Within F p)
    (hr : Run p m m') : ∀ n : A → V, (∀ x ∈ F, n x = m x) →
      ∃ n', Run p n n' ∧ ∀ x ∈ F, n' x = m' x := by
  induction hr with
  | done m => intro n hn; exact ⟨n, .done n, hn⟩
  | @rd a k m m' _ ih =>
    cases hw with
    | rd ha hk =>
      intro n hn
      obtain ⟨n', h1, h2⟩ := ih (hk _) n hn
      exact ⟨n', .rd (by rw [hn a ha]; exact h1), h2⟩
  | @wr a v k m m' _ ih =>
    cases hw with
    | wr ha hk =>
      intro n hn
      obtain ⟨n', h1, h2⟩ := ih hk (Function.update n a v) (by
        intro x hx
        by_cases hxa : x = a
        · subst hxa; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hxa, Function.update_of_ne hxa]; exact hn x hx)
      exact ⟨n', .wr h1, h2⟩
  | lock b _ ih =>
    cases hw with
    | lock hk =>
      intro n hn
      obtain ⟨n', h1, h2⟩ := ih (hk b) n hn
      exact ⟨n', .lock b h1, h2⟩
  | rds v _ ih =>
    cases hw with
    | rds _ hk =>
      intro n hn
      obtain ⟨n', h1, h2⟩ := ih (hk v) n hn
      exact ⟨n', .rds v h1, h2⟩

theorem run_rd_inv {a : A} {k : V → Prog A V L} {m m' : A → V} (h : Run (.rd a k) m m') :
    Run (k (m a)) m m' := by cases h; assumption

theorem run_wr_inv {a : A} {v : V} {k : Prog A V L} {m m' : A → V}
    (h : Run (.wr a v k) m m') : Run k (Function.update m a v) m' := by cases h; assumption

theorem run_done_inv {m m' : A → V} (h : Run (Prog.done : Prog A V L) m m') : m' = m := by
  cases h; rfl

/-! ## Why the footprint must bound accesses, not just the sequential meaning

Words: `false` (`z`) and `true` (`w`). `cxP` reads `z` twice and writes to `w`
whether the reads agreed; run alone it always writes 0, so its sequential
meaning changes only `w` and its result there depends on nothing: (a) and (b)
hold for the footprint `{w}`. `cxQ` writes 1 to `z`: footprint `{z}`. Core
`false` runs `cxP`, core `true` runs `cxQ`, and `cxQ` runs between `cxP`'s two
reads. -/

/-- Reads `z` twice, writes whether they agreed to `w`. -/
def cxP : Prog Bool ℕ Empty :=
  .rd false (fun v1 => .rd false (fun v2 => .wr true (if v1 = v2 then 0 else 1) .done))

/-- Writes 1 to `z`. -/
def cxQ : Prog Bool ℕ Empty := .wr false 1 .done

def cx0 : Cfg Bool ℕ Bool Empty where
  mem := fun _ => 0
  gate := .opn
  holder := none
  seen := ∅
  lk := fun _ => none
  ph := fun _ => .idle
  log := []
  own := fun _ _ => .gate

theorem cxP_run {m m' : Bool → ℕ} (h : Run cxP m m') : m' = Function.update m true 0 := by
  have h3 := run_wr_inv (run_rd_inv (run_rd_inv h))
  rw [run_done_inv h3]; simp

theorem cxQ_run {m m' : Bool → ℕ} (h : Run cxQ m m') : m' = Function.update m false 1 := by
  rw [run_done_inv (run_wr_inv h)]

/-- **Denotational footprints do not give commutation**: `cxP` writes only `w`
with a result there that depends on nothing, `cxQ` writes only `z`, yet an
interleaving of the two (both completing, no local path left) ends with
`w = 1`, which neither serial order gives. -/
theorem denotational_insufficient :
    (∀ m m', Run cxP m m' → m' = Function.update m true 0) ∧
    (∀ m m', Run cxQ m m' → m' = Function.update m false 1) ∧
    ∃ s, Reach cx0 s ∧ NoLoc s ∧ s.log = [cxQ, cxP] ∧ s.mem true = 1 ∧
      (∀ m', RunAll [cxQ, cxP] cx0.mem m' → m' true = 0) ∧
      (∀ m', RunAll [cxP, cxQ] cx0.mem m' → m' true = 0) := by
  refine ⟨fun _ _ => cxP_run, fun _ _ => cxQ_run, ?_⟩
  refine ⟨_, .step (c := false) (.step (c := false) (.step (c := false) (.step (c := true)
    (.step (c := true) (.step (c := true) (.step (c := true) (.step (c := false)
    (.step (c := false) (.step (c := false) .refl
      (Step.arm cxP rfl))
      (Step.enter (p := cxP) rfl rfl))
      (Step.rd rfl))
      (Step.arm cxQ rfl))
      (Step.enter (p := cxQ) rfl rfl))
      (Step.wr rfl))
      (Step.leave rfl))
      (Step.rd rfl))
      (Step.wr rfl))
      (Step.leave rfl), ?_, rfl, rfl, ?_, ?_⟩
  · intro d; cases d <;> exact fun h => h
  · intro m' h
    simp only [RunAll] at h
    obtain ⟨m1, h1, m2, h2, rfl⟩ := h
    rw [cxP_run h2]; simp
  · intro m' h
    simp only [RunAll] at h
    obtain ⟨m1, h1, m2, h2, rfl⟩ := h
    rw [cxQ_run h2, cxP_run h1]; simp

end

end Fl4Proofs.P2.Serial

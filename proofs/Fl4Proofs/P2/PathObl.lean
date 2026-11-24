/-
P2 (DESIGN.md §9, §7 "Checking a local path"): **the per-path footprint
obligation**, the interface between the extracted local paths and the
concurrency theorem of `P2/Serial.lean`.

`Serial.lean` proves that every execution whose local-path accesses are
`Allowed` equals a serial one, and shows (`denotational_insufficient`) that a
write footprint plus a frame lemma of a path's *sequential meaning* is not
enough: the obligation must bound every *access*, reads included. The
extracted Store interface cannot observe accesses through results (two reads
of a word with no write between always agree), so the bound is stated by
running the body on a **guarded store** that fails on any access outside the
stated sets: `guard st R W` answers reads (and both words of `read_pair`) only
inside `R`, and writes (`write`, every word of a `zero` / `clear_free` range)
only inside `W`, and fails otherwise; `ks_base`, `cur_cpu` and `frame_masks`
are not memory and pass through.

## What each local path delivers (v3)

A line proving a local path (the extracted body `f`, e.g.
`syscall.handle_syscall_local st ar · · number found`, its arguments other
than the store, the state and the Arch value fixed; result `(x, s', a')`) gives

* `Acc : X → Prop`: the run was accepted (for the local paths, `x = true`);
* `ReadSet WriteSet DecSet : S → U64 → Prop`, functions of the entry state:
  the words an *accepted* run may read and write, and the words a *declined*
  run may write (`FAULT_IP`, the timestamp words: what the general path
  repeats);
* `Pre : S → Prop`: the entry facts the proof uses, any (P1's heap-wide
  invariants included): every obligation is asked only at the real entry
  state `s`;
* `acc`: at `s`, an accepted run reads only `ReadSet s` and writes only
  `WriteSet s` (the run on `guard` succeeds the same way);
* `dec_alt`: if the run at `s` declines, then from every **alternative** state
  `s'` (`Alt`: same `cpu`, `ksb`, `frame_masks`; equal on `ReadSet s`; and, on
  the words outside it that the path may read by class (`ko` gate or this
  core), the same value class) and any Arch value, the run also declines,
  writes only `DecSet s`, and passes the per-write check below. This is where
  a declined run's racy reads are covered: the values another core may leave
  in a word are exactly those of its class (a CNode slot's `CAP0`: Null or
  Frame; p2lt's `STATE`: Recv/RunningVM vs other). Proofs follow the decline
  path and need no invariants at `s'`. `s' = s` gives the plain decline;
* `read_own`, `write_own`: `ReadSet s` / `WriteSet s ∪ DecSet s` kernel words
  (`User`, user memory such as IPC buffers, exempt) are readable / held;
  `aligned`: written words are aligned (the store laws are for aligned words);
* `move`: the run at `s` passes the per-write check `StepOK` (the run on
  `mguard` succeeds the same way): each write moves owners only between owners
  the path holds, and keeps every changed kernel word's value class unless its
  `ko` is this core or `free`.

`DecOnce` [W] (per path, discharged by the line where it can): a declined
run reads each word outside `ReadSet` at most once, which makes `dec_alt`'s
per-state alternatives cover `Serial`'s per-read ones.

`PathObl` packages these. Arch calls are not memory and are outside the
model (`Serial.lean`, Scope); in `Serial` a read of a user word is an input
(any value) and a write to one is not tracked: races on a frame two cores'
threads share are the user's (DESIGN §7).

## The global side

* `own : (U64 → U64) → U64 → Owner U64 U64`, one map for the whole kernel
  (DESIGN §7 "What a local path may write"): a word of this core's node
  state, of a thread or SC on core `c` (checked before any write), or a timer
  link of a thread in core `c`'s timer tree, is owned by `core c`; a word of a
  lockable object (endpoint, notification, reply object), or a queue link of a
  thread queued on one, by `lock <object address>`; everything else by the
  gate. Lock owners are indexed by object address, finer than the 4,096-entry
  hash table (a collision only makes the real exclusion coarser, so the finer
  map is sound). Fixing `own` concretely is the remaining global [W].
* `GateOnly own m x := own m x = .gate`: no local path writes it
  (`write_own` of every path); local paths may read it.
* `Locks : S → U64 → Prop`: the objects the fl4-sync glue (`local_syscall`,
  `local_vm_fault`, `run_timer_irq`'s plan, `localtimer::cspace_step`) has
  locked when it calls the body, as a function of the entry state. Lock
  attempts are the glue's, not the body's: in `Serial`'s `Prog` they are
  `lock` steps before the body's steps.

## The bridge (proved in `P2/PathBridge.lean`)

* `IsProg f p` [P], one schema premise for all bodies (stated and justified
  once in `PathBridge.lean`): the extracted body is the tree `p : SProg` of its
  Store-trait calls (`interp st p = f st` for every store instance). True by
  construction for a function generic over `Store` (Rust generics, and Aeneas
  threads the state only through the trait methods); not provable inside Lean
  in general (it is a free theorem).
* The store state type is `S : Type` (every store the kernel and the proofs
  instantiate is).
* From `IsProg f p` and `PathObl.access`: the projection (the guarded run is the
  real run) and `PathWithin`: every access of the sequential run of `p` lies in
  `ReadSet` / `WriteSet`, which with `read_own` / `write_own` / `move` is
  `Serial.Allowed` at each step of the path's sequential run, hence (by
  `Serial`'s simulation invariant) at each step of every interleaving: the
  path's share of `Serial.FootprintOK`.
-/
import Fl4Proofs.P1.Store
import Fl4Proofs.P2.Serial
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner ClsOwner)

noncomputable section
open Classical

variable {S : Type}

/-- Word `b` lies in `[a, a + n)`. -/
def InRange (a n b : U64) : Prop := a.val ≤ b.val ∧ b.val < a.val + n.val

/-- The store that answers only reads in `R` and writes in `W`, and fails on
every other access. -/
def guard (st : machine.Store S) (R W : U64 → Prop) : machine.Store S where
  frame_masks := st.frame_masks
  read s a := if R a then st.read s a else fail .panic
  read_pair s a :=
    if R a ∧ R (core.num.U64.wrapping_add a 8#u64) then st.read_pair s a else fail .panic
  write s a v := if W a then st.write s a v else fail .panic
  zero s a n := if ∀ b, InRange a n b → W b then st.zero s a n else fail .panic
  clear_free s a n := if ∀ b, InRange a n b → W b then st.clear_free s a n else fail .panic
  ks_base := st.ks_base
  cur_cpu := st.cur_cpu

section guard
variable {st : machine.Store S} {R W : U64 → Prop}

theorem guard_read {s : S} {a : U64} (h : R a) : (guard st R W).read s a = st.read s a := by
  show (if R a then st.read s a else fail .panic) = _
  rw [if_pos h]

theorem guard_read_pair {s : S} {a : U64} (h : R a) (h8 : R (core.num.U64.wrapping_add a 8#u64)) :
    (guard st R W).read_pair s a = st.read_pair s a := by
  show (if R a ∧ R (core.num.U64.wrapping_add a 8#u64) then st.read_pair s a else fail .panic) = _
  rw [if_pos ⟨h, h8⟩]

theorem guard_write {s : S} {a v : U64} (h : W a) : (guard st R W).write s a v = st.write s a v := by
  show (if W a then st.write s a v else fail .panic) = _
  rw [if_pos h]

theorem guard_zero {s : S} {a n : U64} (h : ∀ b, InRange a n b → W b) :
    (guard st R W).zero s a n = st.zero s a n := by
  show (if ∀ b, InRange a n b → W b then st.zero s a n else fail .panic) = _
  rw [if_pos h]

theorem guard_clear_free {s : S} {a n : U64} (h : ∀ b, InRange a n b → W b) :
    (guard st R W).clear_free s a n = st.clear_free s a n := by
  show (if ∀ b, InRange a n b → W b then st.clear_free s a n else fail .panic) = _
  rw [if_pos h]

@[simp] theorem guard_ks_base : (guard st R W).ks_base = st.ks_base := rfl
@[simp] theorem guard_cur_cpu : (guard st R W).cur_cpu = st.cur_cpu := rfl
@[simp] theorem guard_frame_masks : (guard st R W).frame_masks = st.frame_masks := rfl

theorem guard_read_out {s : S} {a : U64} (h : ¬ R a) : (guard st R W).read s a = fail .panic := by
  show (if R a then st.read s a else fail .panic) = _
  rw [if_neg h]

theorem guard_write_out {s : S} {a v : U64} (h : ¬ W a) :
    (guard st R W).write s a v = fail .panic := by
  show (if W a then st.write s a v else fail .panic) = _
  rw [if_neg h]

/-- Widening the sets keeps a guarded access. -/
theorem guard_mono_read {R' W' : U64 → Prop} (hR : ∀ b, R b → R' b) {s : S} {a : U64} (h : R a) :
    (guard st R' W').read s a = (guard st R W).read s a := by
  rw [guard_read h, guard_read (hR a h)]

end guard

/-- The store that checks `Q` between the state before and after every write
(`write`, `zero`, `clear_free`), failing where it does not hold; reads pass. -/
def mguard (st : machine.Store S) (Q : S → S → Prop) : machine.Store S where
  frame_masks := st.frame_masks
  read := st.read
  read_pair := st.read_pair
  write s a v := do let s' ← st.write s a v; if Q s s' then ok s' else fail .panic
  zero s a n := do let s' ← st.zero s a n; if Q s s' then ok s' else fail .panic
  clear_free s a n := do let s' ← st.clear_free s a n; if Q s s' then ok s' else fail .panic
  ks_base := st.ks_base
  cur_cpu := st.cur_cpu

theorem mguard_write {st : machine.Store S} {Q : S → S → Prop} {s s' : S} {a v : U64}
    (h : st.write s a v = ok s') (hq : Q s s') : (mguard st Q).write s a v = ok s' := by
  show (do let s' ← st.write s a v; if Q s s' then ok s' else fail .panic) = _
  rw [h, bind_tc_ok, if_pos hq]

/-! ## Ownership -/

/-- Owners a local path on core `c` holding the locks `lk` holds. -/
def HeldBy (c : U64) (lk : U64 → Prop) : Owner U64 U64 → Prop
  | .core d => d = c
  | .lock l => lk l
  | .gate => False

/-- Words only the gate writes. -/
def GateOnly (own : (U64 → U64) → U64 → Owner U64 U64) (m : U64 → U64) (x : U64) : Prop :=
  own m x = .gate

/-- A local path on core `c` with locks `lk` may write `x`. -/
def WPerm (own : (U64 → U64) → U64 → Owner U64 U64) (c : U64) (lk : U64 → Prop)
    (m : U64 → U64) (x : U64) : Prop :=
  HeldBy c lk (own m x)

/-- A local path on core `c` with locks `lk` may read `x`. -/
def RPerm (own : (U64 → U64) → U64 → Owner U64 U64) (c : U64) (lk : U64 → Prop)
    (m : U64 → U64) (x : U64) : Prop :=
  HeldBy c lk (own m x) ∨ GateOnly own m x

/-- From `m` to `m'`, owners changed only between owners the path holds. -/
def OwnMove (own : (U64 → U64) → U64 → Owner U64 U64) (c : U64) (lk : U64 → Prop)
    (m m' : U64 → U64) : Prop :=
  ∀ x, own m' x ≠ own m x → HeldBy c lk (own m x) ∧ HeldBy c lk (own m' x)

/-! ## The obligation -/

/-- Every changed kernel word keeps its value class, unless its class owner is
the core `c` or untracked. -/
def ClsStep (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (User : U64 → Prop) (c : U64)
    (m m' : U64 → U64) : Prop :=
  ∀ x, m' x ≠ m x → ¬ User x → cls x (m' x) = cls x (m x) ∨ ko x = .core c ∨ ko x = .free

/-- The per-write check: owner moves and value classes. -/
def StepOK (own : (U64 → U64) → U64 → Owner U64 U64) (cls : U64 → U64 → U64)
    (ko : U64 → ClsOwner U64) (User : U64 → Prop) (c : U64) (lk : U64 → Prop)
    (m m' : U64 → U64) : Prop :=
  OwnMove own c lk m m' ∧ ClsStep cls ko User c m m'

/-- `s'` is an alternative to the entry state `s`: what a declined run's racy
reads may see instead. -/
structure Alt (st : machine.Store S) [L : LawfulStore st] (ReadSet : U64 → Prop)
    (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (User : U64 → Prop) (s s' : S) : Prop where
  cpu : L.cpu s' = L.cpu s
  ksb : L.ksb s' = L.ksb s
  masks : st.frame_masks s' = st.frame_masks s
  read : ∀ x, ReadSet x → L.mem s' x = L.mem s x
  clsEq : ∀ x, ¬ ReadSet x → ¬ User x → (ko x = .gate ∨ ko x = .core (L.cpu s)) →
    cls x (L.mem s' x) = cls x (L.mem s x)

theorem Alt.refl {st : machine.Store S} [L : LawfulStore st] {R : U64 → Prop}
    {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop} (s : S) :
    Alt st R cls ko User s s :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- **The per-path obligation** [W] (per local path, other lines' work), v3,
for the extracted body `f` (other arguments fixed), under `Pre` (any facts),
with the locks `Locks` the fl4-sync glue holds, the ownership map `own`, the
value classes `cls` / `ko` and user memory `User`; the core is `L.cpu s`.
Module docstring, "What each local path delivers (v3)". -/
structure PathObl {A X : Type} (st : machine.Store S) [L : LawfulStore st]
    (f : machine.Store S → S → A → Result (X × S × A)) (Acc : X → Prop)
    (own : (U64 → U64) → U64 → Owner U64 U64) (cls : U64 → U64 → U64)
    (ko : U64 → ClsOwner U64) (User : U64 → Prop)
    (Locks : S → U64 → Prop) (Pre : S → Prop)
    (ReadSet WriteSet DecSet : S → U64 → Prop) : Prop where
  acc : ∀ s a r, Pre s → f st s a = ok r → Acc r.1 →
    f (guard st (ReadSet s) (WriteSet s)) s a = ok r
  dec_alt : ∀ s a r, Pre s → f st s a = ok r → ¬ Acc r.1 →
    ∀ s' a' r', Alt st (ReadSet s) cls ko User s s' → f st s' a' = ok r' →
      ¬ Acc r'.1 ∧ f (guard st (fun _ => True) (DecSet s)) s' a' = ok r' ∧
      f (mguard st (fun x y => StepOK own cls ko User (L.cpu s) (Locks s) (L.mem x) (L.mem y)))
        s' a' = ok r'
  read_own : ∀ s x, Pre s → ReadSet s x → ¬ User x → RPerm own (L.cpu s) (Locks s) (L.mem s) x
  write_own : ∀ s x, Pre s → (WriteSet s x ∨ DecSet s x) → ¬ User x →
    WPerm own (L.cpu s) (Locks s) (L.mem s) x
  aligned : ∀ s x, Pre s → (WriteSet s x ∨ DecSet s x) → Aligned x
  move : ∀ s a r, Pre s → f st s a = ok r →
    f (mguard st (fun x y => StepOK own cls ko User (L.cpu s) (Locks s) (L.mem x) (L.mem y)))
      s a = ok r

/-- The plain decline (`dec_alt` at `s' = s`). -/
theorem PathObl.dec {A X : Type} {st : machine.Store S} [L : LawfulStore st]
    {f : machine.Store S → S → A → Result (X × S × A)} {Acc : X → Prop}
    {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {ko : U64 → ClsOwner U64} {User : U64 → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop}
    {RS WS DS : S → U64 → Prop} (O : PathObl st f Acc own cls ko User Locks Pre RS WS DS)
    {s : S} {a : A} {r : X × S × A} (hpre : Pre s) (h : f st s a = ok r) (hdec : ¬ Acc r.1) :
    f (guard st (fun _ => True) (DS s)) s a = ok r :=
  (O.dec_alt s a r hpre h hdec s a r (Alt.refl s) h).2.1

/-! ## A Store-generic body as a tree of trait calls -/

/-- The trait calls of a Store-generic body, in program order, with Arch calls
(not memory) as opaque effects on `A`. -/
inductive SProg (A X : Type) : Type 1 where
  | ret (x : X)
  | err (e : Error)
  | rd (a : U64) (k : U64 → SProg A X)
  | rdp (a : U64) (k : U64 × U64 → SProg A X)
  | wr (a v : U64) (k : SProg A X)
  | zero (a n : U64) (k : SProg A X)
  | clr (a n : U64) (k : SProg A X)
  | ksb (k : U64 → SProg A X)
  | cpu (k : U64 → SProg A X)
  | masks (k : U64 × U64 → SProg A X)
  | eff {B : Type} (g : A → Result (B × A)) (k : B → SProg A X)

/-- Running the tree on a store instance. -/
def interp {A X : Type} (st : machine.Store S) : SProg A X → S → A → Result (X × S × A)
  | .ret x, s, a => ok (x, s, a)
  | .err e, _, _ => fail e
  | .rd p k, s, a => do let v ← st.read s p; interp st (k v) s a
  | .rdp p k, s, a => do let v ← st.read_pair s p; interp st (k v) s a
  | .wr p v k, s, a => do let s' ← st.write s p v; interp st k s' a
  | .zero p n k, s, a => do let s' ← st.zero s p n; interp st k s' a
  | .clr p n k, s, a => do let s' ← st.clear_free s p n; interp st k s' a
  | .ksb k, s, a => do let v ← st.ks_base s; interp st (k v) s a
  | .cpu k, s, a => do let v ← st.cur_cpu s; interp st (k v) s a
  | .masks k, s, a => do let v ← st.frame_masks s; interp st (k v) s a
  | .eff g k, s, a => do let (b, a') ← g a; interp st (k b) s a'

/-- **`IsProg f p`** [P]: the extracted body `f` is the tree `p` of its trait
calls, on every store instance over `S` (a free theorem of Store-generic Rust
code and its extraction; module docstring). -/
def IsProg {A X : Type} (f : machine.Store S → S → A → Result (X × S × A)) (p : SProg A X) :
    Prop :=
  ∀ st : machine.Store S, f st = interp st p

end

end Fl4Proofs.P2.PathObl

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

## What each local path delivers (v2)

A line proving a local path (the extracted body `f`, e.g.
`syscall.handle_syscall_local st ar · · number found`, its arguments other
than the store, the state and the Arch value fixed; result `(x, s', a')`) gives

* `Acc : X → Prop`: the run was accepted (for the local paths, `x = true`);
* `ReadSet WriteSet DecSet : S → U64 → Prop`, functions of the entry state:
  the words an *accepted* run may read and write, and the words a *declined*
  run may write (`FAULT_IP`, the timestamp words: what the general path
  repeats);
* `Pre : S → Prop`: the entry facts the proof uses;
* the two access lemmas, for a `LawfulStore` `st`:

      theorem <path>_acc [L : LawfulStore st] (hpre : Pre s)
          (h : f st s a = ok r) (hacc : Acc r.1) :
          f (guard st (ReadSet s) (WriteSet s)) s a = ok r
      theorem <path>_dec [L : LawfulStore st] (hpre : Pre s)
          (h : f st s a = ok r) (hdec : ¬ Acc r.1) :
          f (guard st (fun _ => True) (DecSet s)) s a = ok r

  An accepted run reads only `ReadSet` and writes only `WriteSet`; a declined
  run may read anything (a racy read of a word another core may be writing,
  e.g. an unlocked CSpace walk hitting a Null/Frame slot) but writes only
  `DecSet`. Typical proof: the spec proof replayed with `guard_read` /
  `guard_write` / … in place of the store's own equations;
* once the ownership map is fixed (`P2/OwnMap.lean`), the facts linking the
  sets to it, kernel words only (`User`, user memory such as IPC buffers, is
  exempt): `read_own` (accepted reads: held or gate-owned), `write_own`
  (accepted and declined writes: held) and `move` (owners change only between
  held owners).

How the reads of a declined run enter `Serial`: in the path's `Serial.Prog`
the reads outside `ReadSet` are speculative (`Serial.Prog.rds`): they read
memory, need no ownership, and the path's sequential meaning lets them return
any value. So refinement (P2 obligation (2)) for a local path is stated for
every value of those reads: the run declines (writing only `DecSet`, with
values from `ReadSet` words) or behaves as the general path (localinv: a plan
whose recorded words `still_holds` re-checks under the locks). The extracted
store cannot vary a word between two reads with no write between, so the line
proves it for every entry state agreeing with the real one on `ReadSet`, and
`DecOnce` [W] (per path, discharged by the line where it can) states that a
declined run reads each word outside `ReadSet` at most once, which makes the
two the same.

`PathObl` packages these. The `Arch` value is threaded unchanged in kind:
Arch calls are not memory and are outside the model (`Serial.lean`, Scope).
In `Serial` a read of a user word is an input (any value) and a write to one is
not tracked: races on a frame two cores' threads share are the user's
(DESIGN §7); no local path branches on an IPC-buffer word it reads twice.

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
open Fl4Proofs.P2.Serial (Owner)

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

/-- **The per-path obligation** [W] (per local path, other lines' work), v2,
for the extracted body `f` (other arguments fixed), under `Pre`, with the
locks `Locks` the fl4-sync glue holds, the global ownership map `own` and user
memory `User`; the core is `L.cpu s`.

* `acc`: an accepted run reads only `ReadSet` and writes only `WriteSet`;
* `dec`: a declined run writes only `DecSet` (its reads are unrestricted);
* `read_own`: `ReadSet`'s kernel words are held or gate-owned;
* `write_own`: `WriteSet`'s and `DecSet`'s kernel words are held;
* `move`: the run moves owners only between owners the path holds. -/
structure PathObl {A X : Type} (st : machine.Store S) [L : LawfulStore st]
    (f : machine.Store S → S → A → Result (X × S × A)) (Acc : X → Prop)
    (own : (U64 → U64) → U64 → Owner U64 U64) (User : U64 → Prop)
    (Locks : S → U64 → Prop) (Pre : S → Prop)
    (ReadSet WriteSet DecSet : S → U64 → Prop) : Prop where
  acc : ∀ s a r, Pre s → f st s a = ok r → Acc r.1 →
    f (guard st (ReadSet s) (WriteSet s)) s a = ok r
  dec : ∀ s a r, Pre s → f st s a = ok r → ¬ Acc r.1 →
    f (guard st (fun _ => True) (DecSet s)) s a = ok r
  read_own : ∀ s x, Pre s → ReadSet s x → ¬ User x → RPerm own (L.cpu s) (Locks s) (L.mem s) x
  write_own : ∀ s x, Pre s → (WriteSet s x ∨ DecSet s x) → ¬ User x →
    WPerm own (L.cpu s) (Locks s) (L.mem s) x
  move : ∀ s a r, Pre s → f st s a = ok r →
    OwnMove own (L.cpu s) (Locks s) (L.mem s) (L.mem r.2.1)

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

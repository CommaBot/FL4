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

/-! ## A Store- and Arch-generic body as a tree of trait calls -/

/-- An Arch call's result, uniformly: a word, a flag, or nothing. -/
inductive AV where
  | u (x : U64)
  | b (x : Bool)
  | none

/-- An Arch-trait call (`machine.Arch`'s methods) with its arguments. -/
inductive ArchCall where
  | private_device_frame (x : U64)
  | dma_ram (x y : U64)
  | dma_frame (x y : U64) (z : Bool)
  | virtualization
  | vcpu_capability (x : U64)
  | vcpu_barrier
  | invalidate_ept (x y : U64)
  | tdx_active
  | tdx_report (x0 x1 x2 x3 x4 x5 x6 x7 x8 : U64)
  | tdx_extend_rtmr (x0 x1 x2 x3 x4 x5 x6 : U64)
  | tdx_get_quote (x y : U64)
  | now
  | set_deadline (x : U64)
  | us_to_ticks (x : U64)
  | ticks_to_us (x : U64)
  | max_us
  | kernel_wcet_ticks
  | irq_pending
  | take_pending_irq
  | mask_irq (x : U64) (y : Bool)
  | ack_irq (x : U64)
  | irq_free (x : U64)
  | set_vspace (x y : U64)
  | invalidate_page (x y : U64)
  | invalidate_asid (x : U64)
  | invalidate_page_structures (x : U64)
  | ioapic_map (x0 x1 x2 x3 x4 : U64)
  | ioapic_map_remapped (x0 x1 x2 x3 x4 x5 : U64)
  | num_ioapics
  | ioapic_pins (x : U64)
  | port_in (x y : U64)
  | port_out (x y z : U64)
  | fpu_flush (x : U64)
  | fpu_sanitise (x : U64)
  | fpu_reload (x : U64)
  | fpu_release (x : U64)
  | remote_stall (x : U64)
  | send_reschedule (x : U64)
  | putc (x : U64)
  | get_char
  | halt

/-- Performing an Arch call on an instance. -/
def callArch {A : Type} (ar : machine.Arch A) : ArchCall → A → Result (AV × A)
  | .private_device_frame x, a => do let r ← ar.private_device_frame a x; ok (.b r, a)
  | .dma_ram x y, a => do let r ← ar.dma_ram a x y; ok (.b r, a)
  | .dma_frame x y z, a => do let a' ← ar.dma_frame a x y z; ok (.none, a')
  | .virtualization, a => do let r ← ar.virtualization a; ok (.u r, a)
  | .vcpu_capability x, a => do let r ← ar.vcpu_capability a x; ok (.u r, a)
  | .vcpu_barrier, a => do let a' ← ar.vcpu_barrier a; ok (.none, a')
  | .invalidate_ept x y, a => do let a' ← ar.invalidate_ept a x y; ok (.none, a')
  | .tdx_active, a => do let r ← ar.tdx_active a; ok (.b r, a)
  | .tdx_report x0 x1 x2 x3 x4 x5 x6 x7 x8, a => do
      let (r, a') ← ar.tdx_report a x0 x1 x2 x3 x4 x5 x6 x7 x8; ok (.u r, a')
  | .tdx_extend_rtmr x0 x1 x2 x3 x4 x5 x6, a => do
      let (r, a') ← ar.tdx_extend_rtmr a x0 x1 x2 x3 x4 x5 x6; ok (.u r, a')
  | .tdx_get_quote x y, a => do let (r, a') ← ar.tdx_get_quote a x y; ok (.u r, a')
  | .now, a => do let (r, a') ← ar.now a; ok (.u r, a')
  | .set_deadline x, a => do let a' ← ar.set_deadline a x; ok (.none, a')
  | .us_to_ticks x, a => do let r ← ar.us_to_ticks a x; ok (.u r, a)
  | .ticks_to_us x, a => do let r ← ar.ticks_to_us a x; ok (.u r, a)
  | .max_us, a => do let r ← ar.max_us a; ok (.u r, a)
  | .kernel_wcet_ticks, a => do let r ← ar.kernel_wcet_ticks a; ok (.u r, a)
  | .irq_pending, a => do let (r, a') ← ar.irq_pending a; ok (.b r, a')
  | .take_pending_irq, a => do let (r, a') ← ar.take_pending_irq a; ok (.u r, a')
  | .mask_irq x y, a => do let a' ← ar.mask_irq a x y; ok (.none, a')
  | .ack_irq x, a => do let a' ← ar.ack_irq a x; ok (.none, a')
  | .irq_free x, a => do let a' ← ar.irq_free a x; ok (.none, a')
  | .set_vspace x y, a => do let a' ← ar.set_vspace a x y; ok (.none, a')
  | .invalidate_page x y, a => do let a' ← ar.invalidate_page a x y; ok (.none, a')
  | .invalidate_asid x, a => do let a' ← ar.invalidate_asid a x; ok (.none, a')
  | .invalidate_page_structures x, a => do
      let a' ← ar.invalidate_page_structures a x; ok (.none, a')
  | .ioapic_map x0 x1 x2 x3 x4, a => do
      let (r, a') ← ar.ioapic_map a x0 x1 x2 x3 x4; ok (.b r, a')
  | .ioapic_map_remapped x0 x1 x2 x3 x4 x5, a => do
      let (r, a') ← ar.ioapic_map_remapped a x0 x1 x2 x3 x4 x5; ok (.b r, a')
  | .num_ioapics, a => do let r ← ar.num_ioapics a; ok (.u r, a)
  | .ioapic_pins x, a => do let r ← ar.ioapic_pins a x; ok (.u r, a)
  | .port_in x y, a => do let (r, a') ← ar.port_in a x y; ok (.u r, a')
  | .port_out x y z, a => do let a' ← ar.port_out a x y z; ok (.none, a')
  | .fpu_flush x, a => do let a' ← ar.fpu_flush a x; ok (.none, a')
  | .fpu_sanitise x, a => do let a' ← ar.fpu_sanitise a x; ok (.none, a')
  | .fpu_reload x, a => do let a' ← ar.fpu_reload a x; ok (.none, a')
  | .fpu_release x, a => do let a' ← ar.fpu_release a x; ok (.none, a')
  | .remote_stall x, a => do let a' ← ar.remote_stall a x; ok (.none, a')
  | .send_reschedule x, a => do let a' ← ar.send_reschedule a x; ok (.none, a')
  | .putc x, a => do let a' ← ar.putc a x; ok (.none, a')
  | .get_char, a => do let (r, a') ← ar.get_char a; ok (.u r, a')
  | .halt, a => do let a' ← ar.halt a; ok (.none, a')

/-- The trait calls of a body generic in `Store` and `Arch`, in program order:
memory calls, and Arch calls by method and arguments (`ArchCall`). -/
inductive SProg (X : Type) : Type where
  | ret (x : X)
  | err (e : Error)
  | rd (a : U64) (k : U64 → SProg X)
  | rdp (a : U64) (k : U64 × U64 → SProg X)
  | wr (a v : U64) (k : SProg X)
  | zero (a n : U64) (k : SProg X)
  | clr (a n : U64) (k : SProg X)
  | ksb (k : U64 → SProg X)
  | cpu (k : U64 → SProg X)
  | masks (k : U64 × U64 → SProg X)
  | arch (op : ArchCall) (k : AV → SProg X)

/-- Running the tree on a store and an Arch instance. -/
def interp {A X : Type} (st : machine.Store S) (ar : machine.Arch A) :
    SProg X → S → A → Result (X × S × A)
  | .ret x, s, a => ok (x, s, a)
  | .err e, _, _ => fail e
  | .rd p k, s, a => do let v ← st.read s p; interp st ar (k v) s a
  | .rdp p k, s, a => do let v ← st.read_pair s p; interp st ar (k v) s a
  | .wr p v k, s, a => do let s' ← st.write s p v; interp st ar k s' a
  | .zero p n k, s, a => do let s' ← st.zero s p n; interp st ar k s' a
  | .clr p n k, s, a => do let s' ← st.clear_free s p n; interp st ar k s' a
  | .ksb k, s, a => do let v ← st.ks_base s; interp st ar (k v) s a
  | .cpu k, s, a => do let v ← st.cur_cpu s; interp st ar (k v) s a
  | .masks k, s, a => do let v ← st.frame_masks s; interp st ar (k v) s a
  | .arch op k, s, a => do let (v, a') ← callArch ar op a; interp st ar (k v) s a'

/-- **`IsProg F p`** [P], the one schema premise (`PathBridge.lean`): the
extracted body family `F` (generic in the Arch instance as in the Store one)
is the tree `p` of its trait calls, on every store and Arch instance (a free
theorem of Rust code generic in `S: Store` and `A: Arch` and of its
extraction). -/
def IsProg {X : Type}
    (F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A))
    (p : SProg X) : Prop :=
  ∀ (A : Type) (ar : machine.Arch A) (st : machine.Store S), F ar st = interp st ar p

end

end Fl4Proofs.P2.PathObl

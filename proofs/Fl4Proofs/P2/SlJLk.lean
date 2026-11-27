/-
# P2 (line slhuf, gen 6): the lock premise `hlk` from "the locks are kernel words", and `hCs` from P3

## What `Locks` is in P2's model (why there is no concrete `fl4Locks` over model memory)
The local paths' `Locks : S → U64 → Prop` (`E2E.LocalPath.Locks`) is tied to the execution model only by
`E2E.StartAt`: `P.Locks σ = hs` with `hs = fun l => s.lk l = some c` (`E2E.Fl4Step.start`). The lock state of
`Serial.Cfg` is the separate component `lk : L → Option C` (`Step.lock` / `Step.leave` change `lk`, never `mem`),
so the lock words are deliberately **not** in model memory (`Serial`: "kernel memory only", lock words are covered
by the [P] sequential-consistency premise of fl4-sync/fl4-store). Two further facts make a memory-read lock map
impossible to state faithfully here:
* fl4-store's lock word (`crates/fl4-store/src/lock.rs`, `TABLE`: 4,096 64-byte-aligned `AtomicU64` in the kernel
  image's static data) stores `1` when taken, not the taker's core: which core holds a lock is only in the glue's
  stack-local `Held` record (`Held { e, n }`, `MAX_HELD = 6`), i.e. outside both `LawfulStore.mem`'s objects and
  `K`'s layout;
* the model's locks are indexed by **object address** (`OwnMap`'s `.lock p`, "finer than `fl4_store::lock`'s
  4,096-entry hash table: sound, since a hash collision only makes the real exclusion coarser"), while `Held`
  records hash indices (`index(addr)`). A map reading `TABLE`/`Held` would give the index-level set, which is not
  `{l | s.lk l = some c}` and so could not meet `StartAt`'s equality.
So `Locks` is the glue's ghost "locks this core holds", as `StartAt` [P] states. What `hlk` really needs is that a
user-word write cannot change it. This module proves `hlk` for the widest natural class of such maps:

* `LkDet K g Locks s`: at `s`, `Locks` is determined by a projection `g` (any ghost component, e.g. the glue's
  held set kept beside the store), the core, the kernel base and the aligned non-user words. `g := fun _ => ()`
  is "`Locks` determined by kernel words" (`KernDetAt`).
* **`hlk_of_lkDet`**: such a `Locks` is unchanged by a write of an aligned user word, given that the write keeps
  `g` (`hg`; free for `g := fun _ => ()`).
* **`hlk_of_kernelDet`**: the guarded `hlk` of `sl_pathsKC4` / `irq_pathsJ3`
  (`∀ K s b v, SlJAt K s → b ∈ K.user → Aligned b → Locks (wr s b v) = Locks s`) from
  `hKD : ∀ K s, SlJAt K s → KernDetAt K Locks s` [P]; `hlk_of_kernelDetK` for one layout (`rr_localPathJK`).
* `LkReads R Locks` (`Locks` reads only the words `R`, plus core and kernel base) with `R` aligned and disjoint
  from the user words at every bundle state gives `KernDetAt` (`kernelDet_of_reads`): this is the form a concrete
  lock map over kernel words (a lock table in kernel static data, a per-core held record on the kernel stack)
  discharges, `hRu` being the boot layout's "kernel image and stacks are in no user frame".

* **Any written-word set `U` and guard `P`** (`LkDetS`, `KernDetS`, `hlk_of_lkDetS`, **`hlk_of_kernelDetU`**,
  `kernelDetS_of_reads`, `hlk_of_readsU`): the same for writes of aligned `U` words at `P` states. Line vlift's
  concrete family writes `(userV K).user` = user words and VCPU data words: one hypothesis "the locks read no user
  word and no VCPU data word" (`KernDetS (userV K).user` at `SlJAt K.toKLayout` states, or `kernelDetS_of_reads`
  with `R` off both) gives vlift's guarded `IrqPrem.lk` by `hlk_of_kernelDetU` and, by `kernDetAt_of_S`
  (`K.user ⊆ U`, `LkDetS.mono`), the `K.user` forms above, so it discharges both versions.
* `hlk_of_ghost`: the unguarded, unaligned form (vlift's `StPrem.lk`) for a lock map that is a function of a ghost
  projection every such write keeps. A memory-reading map cannot give it (`LawfulStore` says nothing about an
  unaligned write), so `StPrem.lk` should take `Aligned b` like its `eu` / `uf`.

## `hCs` at P3's sets
`sl_pathsKC4` / `rr_localPathJK` ask `hCs : ∀ c ∈ Cs, c.val < 64` [P] of their fixed core set. It holds at P3's
sets: `SlJAtZ.csLt` (P3 `JKern.csLt` of the bundle's `JAtZ`), `SlJAt.ncores_le` (`K.ncores ≤ 64` at every bundle
state), `SlJAt.hCs` (the layout's cores `{c | c.val < K.ncores}`, the set the timer-interrupt path instantiates
`Cs` with, `IrqPreJ3.entM`), and `hCs_of_sub` (any `Cs` inside the layout's cores at some bundle state).
-/
import Fl4Proofs.P2.SlJEnt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}

/-- **`Locks` determined at `s` by a projection `g`, the core, the kernel base and the aligned non-user words.** -/
def LkDet {G : Type} (K : KLayout) (g : S → G) (Locks : S → U64 → Prop) (s : S) : Prop :=
  ∀ s' : S, g s' = g s → L.cpu s' = L.cpu s → L.ksb s' = L.ksb s →
    (∀ x, Aligned x → x ∉ K.user → L.mem s' x = L.mem s x) → Locks s' = Locks s

/-- **`Locks` determined at `s` by kernel words** (core, kernel base, aligned non-user words). -/
def KernDetAt (K : KLayout) (Locks : S → U64 → Prop) (s : S) : Prop :=
  LkDet (L := L) K (fun _ => ()) Locks s

/-- **`Locks` reads only the words `R`** (and the core and kernel base), at every state. -/
def LkReads (R : Set U64) (Locks : S → U64 → Prop) : Prop :=
  ∀ s s' : S, L.cpu s' = L.cpu s → L.ksb s' = L.ksb s → (∀ x ∈ R, L.mem s' x = L.mem s x) →
    Locks s' = Locks s

/-- **A user-word write keeps a lock map determined by kernel words and a write-stable ghost.** -/
theorem hlk_of_lkDet {G : Type} {g : S → G} {s : S} (hD : LkDet (L := L) K g Locks s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) (hg : g (L.wr s b v) = g s) :
    Locks (L.wr s b v) = Locks s :=
  hD _ hg (L.cpu_wr _ _ _) (L.ksb_wr _ _ _)
    (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))

/-- **`hlk` from "the locks are kernel words"**, at one state. -/
theorem KernDetAt.wr {s : S} (hD : KernDetAt (L := L) K Locks s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) : Locks (L.wr s b v) = Locks s :=
  hlk_of_lkDet hD hb hba v rfl

/-- **The guarded `hlk` of `sl_pathsKC4` / `irq_pathsJ3`** from `hKD` [P]: at every bundle state the glue's
locks are determined by kernel words. -/
theorem hlk_of_kernelDet (hKD : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K Locks s) :
    ∀ (K : KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s :=
  fun K s _ v hJ hb hba => (hKD K s hJ).wr hb hba v

/-- **The guarded `hlk` of `rr_localPathJK`** (one layout) from `hKD` [P]. -/
theorem hlk_of_kernelDetK (hKD : ∀ s : S, SlJAt (L := L) K s → KernDetAt (L := L) K Locks s) :
    ∀ s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s :=
  fun s _ v hJ hb hba => (hKD s hJ).wr hb hba v

/-- **A lock map reading only aligned kernel words is determined by kernel words** at every bundle state:
`hR` (it reads only `R`), `hRa` (`R` aligned), `hRu` [P] (`R` holds no user word at a bundle state). -/
theorem kernelDet_of_reads {R : Set U64} (hR : LkReads (L := L) R Locks) (hRa : ∀ x ∈ R, Aligned x)
    (hRu : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → ∀ x ∈ R, x ∉ K.user) :
    ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K Locks s :=
  fun K s hJ s' _ hc hk hm => hR s s' hc hk (fun x hx => hm x (hRa x hx) (hRu K s hJ x hx))

/-- **The guarded `hlk` from a lock map reading only aligned non-user words.** -/
theorem hlk_of_reads {R : Set U64} (hR : LkReads (L := L) R Locks) (hRa : ∀ x ∈ R, Aligned x)
    (hRu : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → ∀ x ∈ R, x ∉ K.user) :
    ∀ (K : KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s :=
  hlk_of_kernelDet (kernelDet_of_reads hR hRa hRu)

/-! ### Any written-word set `U` and any guard `P` (line vlift's `userV`: user words and VCPU data words) -/

/-- **`Locks` determined at `s` by `g`, the core, the kernel base and the aligned words outside `U`.** -/
def LkDetS {G : Type} (U : Set U64) (g : S → G) (Locks : S → U64 → Prop) (s : S) : Prop :=
  ∀ s' : S, g s' = g s → L.cpu s' = L.cpu s → L.ksb s' = L.ksb s →
    (∀ x, Aligned x → x ∉ U → L.mem s' x = L.mem s x) → Locks s' = Locks s

/-- **`Locks` determined at `s` by the core, the kernel base and the aligned words outside `U`.** -/
def KernDetS (U : Set U64) (Locks : S → U64 → Prop) (s : S) : Prop :=
  LkDetS (L := L) U (fun _ => ()) Locks s

/-- Determined by the words outside a larger set is determined by the words outside a smaller one. -/
theorem LkDetS.mono {G : Type} {g : S → G} {U U' : Set U64} {s : S} (hUU : U ⊆ U')
    (h : LkDetS (L := L) U' g Locks s) : LkDetS (L := L) U g Locks s :=
  fun s' hg hc hk hm => h s' hg hc hk (fun x hx hxu => hm x hx (fun h' => hxu (hUU h')))

/-- **One hypothesis for both scopes**: locks determined by the words outside a set `U ⊇ K.user` (e.g. vlift's
`(userV K).user`, user words and VCPU data words) are determined by kernel words in `KernDetAt K`'s sense. -/
theorem kernDetAt_of_S {U : Set U64} {s : S} (hUU : K.user ⊆ U) (h : KernDetS (L := L) U Locks s) :
    KernDetAt (L := L) K Locks s :=
  LkDetS.mono hUU h

/-- **A write of an aligned `U` word keeps a lock map determined by the words outside `U`** (and a
write-stable ghost `g`). -/
theorem hlk_of_lkDetS {G : Type} {g : S → G} {U : Set U64} {s : S} (hD : LkDetS (L := L) U g Locks s)
    {b : U64} (hb : b ∈ U) (hba : Aligned b) (v : U64) (hg : g (L.wr s b v) = g s) :
    Locks (L.wr s b v) = Locks s :=
  hD _ hg (L.cpu_wr _ _ _) (L.ksb_wr _ _ _)
    (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))

/-- **The guarded `hlk` for any written-word set `U` and guard `P`** from `hKD` [P]. At `U := (userV K).user`,
`P := SlJAt K.toKLayout` it is line vlift's `IrqPrem.lk`; at `U := K.user`, `P := SlJAt K` the form of
`sl_pathsKC4` / `rr_localPathJK` / `irq_pathsJ3`. -/
theorem hlk_of_kernelDetU {P : S → Prop} {U : Set U64}
    (hKD : ∀ s : S, P s → KernDetS (L := L) U Locks s) :
    ∀ s b v, P s → b ∈ U → Aligned b → Locks (L.wr s b v) = Locks s :=
  fun s _ v hP hb hba => hlk_of_lkDetS (hKD s hP) hb hba v rfl

/-- **A lock map reading only aligned words off `U` at the guarded states is determined by the words outside
`U`** there: `hR`, `hRa`, `hRU` [P] (for vlift: the lock words are no user word and no VCPU data word). -/
theorem kernelDetS_of_reads {P : S → Prop} {U R : Set U64} (hR : LkReads (L := L) R Locks)
    (hRa : ∀ x ∈ R, Aligned x) (hRU : ∀ s : S, P s → ∀ x ∈ R, x ∉ U) :
    ∀ s : S, P s → KernDetS (L := L) U Locks s :=
  fun s hP s' _ hc hk hm => hR s s' hc hk (fun x hx => hm x (hRa x hx) (hRU s hP x hx))

/-- **The guarded `hlk` for `U`, `P` from a lock map reading only aligned words off `U`.** -/
theorem hlk_of_readsU {P : S → Prop} {U R : Set U64} (hR : LkReads (L := L) R Locks)
    (hRa : ∀ x ∈ R, Aligned x) (hRU : ∀ s : S, P s → ∀ x ∈ R, x ∉ U) :
    ∀ s b v, P s → b ∈ U → Aligned b → Locks (L.wr s b v) = Locks s :=
  hlk_of_kernelDetU (kernelDetS_of_reads hR hRa hRU)

/-- **The unguarded, unaligned `hlk`** (line vlift's `StPrem.lk`: `∀ s b v, b ∈ U → …`, no `Aligned b`) holds for
a lock map that is a function of a ghost projection `g` every such write keeps (`hg` [P]). A map reading memory
cannot give it: `LawfulStore` states nothing about an unaligned write (`mem_wr` asks `Aligned a`), so such a write
may change any word; vlift's `StPrem.lk` should take `Aligned b` (as its `eu` / `uf` / `IrqPrem.lk` do) to be
dischargeable by `hlk_of_kernelDetU`. -/
theorem hlk_of_ghost {G : Type} {F : G → U64 → Prop} {g : S → G} {U : Set U64}
    (hL : ∀ s, Locks s = F (g s)) (hg : ∀ s b v, b ∈ U → g (L.wr s b v) = g s) :
    ∀ s b v, b ∈ U → Locks (L.wr s b v) = Locks s :=
  fun s b v hb => by rw [hL, hL, hg s b v hb]

end

/-! ## `hCs` at P3's sets -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

/-- **P3's core set is below 64 cores** (`JKern.csLt` of the bundle's `JAtZ`). -/
theorem SlJAtZ.csLt (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) : ∀ c ∈ Cx, c.val < 64 :=
  B.j.kern.csLt

/-- **A bundle layout counts at most 64 cores.** -/
theorem SlJAt.ncores_le (B : SlJAt (L := L) K s) : K.ncores ≤ 64 := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := B
  by_contra h
  have h64 : (64#u64).val = 64 := by simp
  have hin : (64#u64) ∈ Cx := (B.cs _).2 (by rw [h64]; omega)
  have := B.csLt _ hin
  rw [h64] at this
  omega

/-- **`hCs` at the layout's cores** `{c | c.val < K.ncores}` (P3's `Cs`, `SlJAtZ.cs`), at a bundle state. -/
theorem SlJAt.hCs (B : SlJAt (L := L) K s) : ∀ c ∈ {c : U64 | c.val < K.ncores}, c.val < 64 :=
  fun _ hc => lt_of_lt_of_le hc B.ncores_le

/-- **`hCs` for any `Cs` inside the layout's cores** at some bundle state. -/
theorem hCs_of_sub {Cs : Set U64} (B : SlJAt (L := L) K s) (h : Cs ⊆ {c : U64 | c.val < K.ncores}) :
    ∀ c ∈ Cs, c.val < 64 :=
  fun c hc => B.hCs c (h hc)

end

end Fl4Proofs.P2.PathObl

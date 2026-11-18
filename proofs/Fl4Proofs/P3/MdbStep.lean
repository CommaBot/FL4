/-
P3 (DESIGN.md §9): **`MdbStep`**, what an operation did to the MDB, at the
level of slot contents and the ghost tree. It is defined early (before
CnodeCopy) with no dependency on the invariants it serves, so that the
operations' posts can carry it; `MdbStep.inv` (MdbStepInv) then keeps
`Vs.FrameInv`, `UtInv` and `NoOverlap` along any step, from per-primitive
lemmas.

Constructors (pre-state `mem`/`G`, post-state `mem'`/`G'`):
* `keep`: the MDB's caps and revocable bits kept (`set_thread_state`,
  writes outside the slots);
* `recap`: one slot's cap replaced by one alike (`CapAlike`: a remapped
  frame or table cap, a zombie for its object);
* `setFi`: an untyped cap's free index changed, up (retype, `MakePool`)
  or down when it has no descendants (reset);
* `insert`: a derived cap inserted after `src` (`InsCtx`: copy, mint,
  mutate, the IRQ handler's notification, TCB caps);
* `nonphys`: a non-physical cap naming no object inserted after a
  non-physical `src` (IRQ control, IO port control);
* `remove`: a slot removed from its chain (`empty_slot`);
* `rename`: the slots renamed along an equivalence (move, swap);
* `frameAlias`: a 4 KiB alias of a page of `src`'s large frame
  (`DeriveSubframe`);
* `pool`: an ASID pool cap over a full untyped cap's whole region, as its
  only child (`MakePool`);
* `retype`: retype's new caps (`RetypeDelta`, with the chains and the
  revocable bits of the old slots kept);
* `trans`: two steps in sequence.

The VSpace side facts (`hv`, `hq4`/`hqal`, `hb`, `hvc`) are what
`MdbStep.vs` (MdbStepVs) needs to keep `Vs.VsMdbInv`, with `UtWin` (the
untyped regions in the kernel window) kept alongside (`MdbStep.win`).

Also here: `CapAlike`, `NoOverlap` (l4v `caps_no_overlap` / distinct
objects for the non-untyped physical caps), and `RetypeDelta` (moved from
UntypedUtInv).
-/
import Fl4Proofs.P3.CapRange
import Fl4Proofs.P3.MdbInvIns
import Fl4Proofs.P3.MdbInvEmp
import Fl4Proofs.P3.FinKeep
import Fl4Proofs.P3.VsFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem objRefs_gen (c : Fl4Spec.Cap) (q : Fl4Spec.ObjRef) :
    q ∈ Fl4Spec.objRefs c ↔ Fl4Spec.GenObjRef.objRef q ∈ Fl4Spec.genObjRefs c := by
  simp only [Fl4Spec.genObjRefs, Set.mem_union, Set.mem_image]
  constructor
  · intro h; exact Or.inl (Or.inl ⟨q, h, rfl⟩)
  · rintro ((⟨x, hx, e⟩ | ⟨x, -, e⟩) | ⟨x, -, e⟩)
    · cases e; exact hx
    · cases e
    · cases e

/-- Two caps alike for the MDB invariants: the same range, physicality,
objects, frame-ness, the same untyped cap if either is one, and a large RAM
frame only for one of the same frame. -/
structure CapAlike (c' c : capability.Cap) : Prop where
  base : baseF c' = baseF c
  top : topF c' = topF c
  phys : physF c' = physF c
  ut : ∀ p sb fi d, c' = .Untyped p sb fi d ↔ c = .Untyped p sb fi d
  refs : Fl4Spec.objRefs (absCap c') = Fl4Spec.objRefs (absCap c)
  frame : isFrame c' = isFrame c
  large : ∀ p r m ep a va, c' = .Frame p .Large r false m ep a va →
    ∃ r0 m0 ep0 a0 v0, c = .Frame p .Large r0 false m0 ep0 a0 v0

theorem CapAlike.refl (c : capability.Cap) : CapAlike c c :=
  ⟨rfl, rfl, rfl, fun _ _ _ _ => Iff.rfl, rfl, rfl, fun p r m ep a va h => ⟨r, m, ep, a, va, h⟩⟩

theorem CapAlike.isUt' {c' c : capability.Cap} (h : CapAlike c' c) : isUt c' = isUt c := by
  cases hc : P3.isUt c with
  | true =>
    obtain ⟨q, sz, f, d, e⟩ : ∃ q sz f d, c = .Untyped q sz f d := by cases c <;> simp_all [P3.isUt]
    rw [(h.ut q sz f d).2 e]; rfl
  | false =>
    cases hc' : P3.isUt c' with
    | false => rfl
    | true =>
      obtain ⟨q, sz, f, d, e⟩ : ∃ q sz f d, c' = .Untyped q sz f d := by cases c' <;> simp_all [P3.isUt]
      rw [(h.ut q sz f d).1 e] at hc; simp [P3.isUt] at hc

/-- A cap of the same shape and object, equal to the old one if that is
untyped, is alike. -/
theorem CapAlike.of_shape {c' c : capability.Cap} (hsh : shape c' = shape c) (hok : okey c' = okey c)
    (hut : P3.isUt c = true → c' = c) : CapAlike c' c := by
  obtain ⟨h1, h2, h3⟩ := range_of_shape hsh
  refine ⟨h1, h2, h3, fun p sb fi d => ⟨fun e => ?_, fun e => ?_⟩, ?_, ?_, ?_⟩
  · have : P3.isUt c = true := by rw [← isUt_of_shape hsh, e]; rfl
    rw [← hut this]; exact e
  · rw [hut (by rw [e]; rfl)]; exact e
  · ext q; rw [objRefs_gen, objRefs_gen, refs_of_shape hsh]
  · cases c' <;> cases c <;> simp_all [shape, isFrame]
  · intro p r m ep a va e
    subst e
    cases c <;> simp_all [shape, okey]

/-- Two non-untyped, non-frame caps with the same pointer, size,
physicality and objects are alike. -/
theorem CapAlike.of_eqs {c' c : capability.Cap} (hp : capability.Cap.ptr c' = capability.Cap.ptr c)
    (hs : objects.cap_size_bits c' = objects.cap_size_bits c)
    (hph : objects.cap_is_physical c' = objects.cap_is_physical c)
    (hu' : P3.isUt c' = false) (hu : P3.isUt c = false)
    (hr : Fl4Spec.objRefs (absCap c') = Fl4Spec.objRefs (absCap c))
    (hf' : isFrame c' = false) (hf : isFrame c = false) : CapAlike c' c := by
  have e1 : ptrF c' = ptrF c := by rw [ptr_eq, ptr_eq] at hp; exact ok_inj hp
  have e2 : sizeF c' = sizeF c := by rw [size_eq, size_eq] at hs; exact ok_inj hs
  have e3 : physF c' = physF c := by rw [phys_eq, phys_eq] at hph; exact ok_inj hph
  refine ⟨by unfold baseF; rw [e1], by unfold topF; rw [e1, e2], e3, fun p sb fi d => ⟨fun e => ?_, fun e => ?_⟩,
    hr, by rw [hf', hf], fun p r m ep a va e => ?_⟩
  · rw [e] at hu'; cases hu'
  · rw [e] at hu; cases hu
  · rw [e] at hf'; cases hf'

/-- A CNode cap's zombie is alike. -/
theorem capAlike_zombie_cnode {p r gs g z : U64} (hr : r ≠ capability.ZOMBIE_TCB) :
    CapAlike (.Zombie p r z) (.CNode p r gs g) :=
  CapAlike.of_eqs rfl (by simp only [objects.cap_size_bits, hr, ↓reduceIte]) rfl rfl rfl rfl rfl rfl

/-- A thread cap's zombie is alike. -/
theorem capAlike_zombie_thread {t n : U64} : CapAlike (.Zombie t capability.ZOMBIE_TCB n) (.Thread t) :=
  CapAlike.of_eqs rfl (by simp only [objects.cap_size_bits, ↓reduceIte]) rfl rfl rfl rfl rfl rfl

/-- A zombie with another count is alike. -/
theorem capAlike_zombie_zombie {p zt n n' : U64} : CapAlike (.Zombie p zt n) (.Zombie p zt n') :=
  CapAlike.of_eqs rfl rfl rfl rfl rfl rfl rfl rfl

theorem not_frame_of_phys {c : capability.Cap} (h : physF c = false) : isFrame c = false := by
  cases hc : c <;> simp [isFrame]
  subst hc
  rw [show physF (.Frame _ _ _ _ _ _ _ _) = true from ok_inj (phys_eq _).symm] at h
  cases h

/-- **No overlap** (l4v `caps_no_overlap` and distinct objects, for the
MDB): the range of a non-untyped physical cap `x` meets another physical
cap `y`'s only if `y` is an untyped cap containing it, or both are frames
and `y` is not revocable (an alias, or a copy) or contains `x`, or neither
is a frame and they have the same range (copies, a zombie). -/
def NoOverlap (mem : U64 → U64) (G : MdbGhost) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ y ∈ G.chains.flatten, physF (capV mem x) = true → physF (capV mem y) = true →
    isUt (capV mem x) = false →
    Disj (capV mem y) (capV mem x) ∨ (isUt (capV mem y) = true ∧ Within (capV mem x) (capV mem y)) ∨
      (isFrame (capV mem x) = true ∧ isFrame (capV mem y) = true ∧
        (revOf mem y = false ∨ Within (capV mem x) (capV mem y))) ∨
      (isFrame (capV mem x) = false ∧ isFrame (capV mem y) = false ∧
        baseF (capV mem y) = baseF (capV mem x) ∧ topF (capV mem y) = topF (capV mem x))

/-- What retype did to the slots and the tree, abstractly: `mem0`/`G0`
before, `mem1` after the free-index update, `memf`/`Gf` after the loop, new
caps `cj j` in slots `dslot j` (`j < w`), `k` bytes apart from `A`. -/
structure RetypeDelta (th : TypedHeap) (mem0 mem1 memf : U64 → U64) (G0 Gf : MdbGhost) (src : U64)
    (p sb fi nfi : U64) (dev : Bool) (A k w : Nat) (dslot : Nat → U64) (cj : Nat → capability.Cap) : Prop where
  hM0 : MdbLinks th mem0 G0
  hsrc : src ∈ G0.chains.flatten
  hcs : capV mem0 src = .Untyped p sb fi dev
  hcs1 : capV mem1 src = .Untyped p sb nfi dev
  hc1 : ∀ x ∈ G0.chains.flatten, x ≠ src → capV mem1 x = capV mem0 x
  hfi : fi.val < 2 ^ sb.val
  hA : p.val + fi.val ≤ A
  hnfi : p.val + nfi.val = A + w * k
  hAw : A + w * k ≤ p.val + 2 ^ sb.val
  hk : 1 ≤ k
  cphys : ∀ j, j < w → physF (cj j) = true
  cbase : ∀ j, j < w → baseF (cj j) = A + j * k
  ctop : ∀ j, j < w → topF (cj j) = A + j * k + k - 1
  cut : ∀ j, j < w → isUt (cj j) = true → ∃ us d, cj j = .Untyped ⟨BitVec.ofNat 64 (A + j * k)⟩ us 0#u64 d ∧
    2 ^ us.val = k
  /-- The new untyped caps are device caps exactly when the parent is
  (`create_object`: `is_device: device`). -/
  cdev : ∀ j, j < w → ∀ q us f d, cj j = .Untyped q us f d → d = dev
  dnot : ∀ j, j < w → dslot j ∉ G0.chains.flatten
  dinj : ∀ j l, j < w → l < w → dslot j = dslot l → j = l
  F1 : ∀ x ∈ Gf.chains.flatten, x ∈ G0.chains.flatten ∨ ∃ j, j < w ∧ x = dslot j
  F1b : ∀ x ∈ G0.chains.flatten, x ∈ Gf.chains.flatten
  F2a : ∀ j, j < w → capV memf (dslot j) = cj j
  F2b : ∀ x ∈ G0.chains.flatten, capV memf x = capV mem1 x
  F3 : ∀ y x, Mdb.Desc Gf.par y x ↔ Mdb.Desc G0.par y x ∨
    ∃ j, j < w ∧ y = dslot j ∧ (x = src ∨ Mdb.Desc G0.par src x)

/-- **The physical address of a kernel pointer**, as a number: layout.rs's
`p.wrapping_sub(PPTR_BASE)` (`PPTR_BASE = 2^64 - 2^39`), i.e.
`(p + 2^39) mod 2^64`. For a pointer of the kernel window it is below
`2^39`; a device untyped's pointer is `paddr + PPTR_BASE` wrapping
(`layout::pptr`), which for `paddr ≥ 512 GiB` lies in the lower half. -/
def paddrN (p : U64) : Nat := (p.val + 549755813888) % 18446744073709551616

/-- **A new cap of retype placed for the VSpace invariant** (`Vs.VCapOK`
in fresh ghost sets, `MdbStep.vs`): a VSpace cap unmapped, its physical
address (`paddrN`) below `2^47` and aligned to its size, a PML4 at or above
`PPTR_BASE` (non-null); retype makes no ASID pool. Frames (and, from the
same bound, tables) are stated by physical address, not `PPTR_BASE ≤ p`:
a frame retyped from a device untyped above 512 GiB has a pointer in the
lower half (boot hands out device memory up to `PADDR_USER_DEVICE_TOP`,
losfair/FL4#34). -/
def NewVPlaced : capability.Cap → Prop
  | .PageTable p mp _ _ => mp = false ∧ paddrN p < 2 ^ 47 ∧ p.val % 2 ^ 12 = 0
  | .PageDirectory p mp _ _ => mp = false ∧ paddrN p < 2 ^ 47 ∧ p.val % 2 ^ 12 = 0
  | .Pdpt p mp _ _ => mp = false ∧ paddrN p < 2 ^ 47 ∧ p.val % 2 ^ 12 = 0
  | .Pml4 p mp _ => mp = false ∧ layout.PPTR_BASE.val ≤ p.val
  | .Frame p sz _ _ m _ _ _ => m = false ∧ paddrN p < 2 ^ 47 ∧ p.val % 2 ^ frameBitsN sz = 0
  | .AsidPool _ _ => False
  | _ => True

/-- **An untyped cap placed** (fl4-kernel's boot, `create_untypeds_for_region`
blocks aligned by pointer; retype keeps it for the children): a RAM
(non-device) untyped at or above `PPTR_BASE` (RAM stops at the kernel
window's top); a device untyped's physical range `[paddrN p, paddrN p + 2^sb)`
below `PADDR_USER_DEVICE_TOP = 2^47` (its pointer may wrap to the lower
half, losfair/FL4#34). The other caps impose nothing. -/
def UtW : capability.Cap → Prop
  | .Untyped p sb _ d => (d = false → layout.PPTR_BASE.val ≤ p.val) ∧ (d = true → paddrN p + 2 ^ sb.val ≤ 2 ^ 47)
  | _ => True

theorem paddrN_lt {p : U64} (hb : layout.PPTR_BASE.val ≤ p.val) : paddrN p < 2 ^ 39 := by
  have := Fl4Proofs.P0.Consts.layout.PPTR_BASE.val_eq
  have : p.val < 2 ^ 64 := p.hBounds
  unfold paddrN; omega

/-- An untyped cap inside a placed one, with its device flag, is placed. -/
theorem utW_within {p sb fi q us f : U64} {d : Bool} (h : UtW (.Untyped p sb fi d)) (h1 : p.val ≤ q.val)
    (h2 : q.val + 2 ^ us.val ≤ p.val + 2 ^ sb.val) : UtW (.Untyped q us f d) := by
  have := Fl4Proofs.P0.Consts.layout.PPTR_BASE.val_eq
  have : p.val < 2 ^ 64 := p.hBounds
  have : q.val < 2 ^ 64 := q.hBounds
  simp only [UtW, paddrN] at h ⊢
  exact ⟨fun e => by have := h.1 e; omega, fun e => by have := h.2 e; omega⟩

/-- A pointer inside a placed untyped region has its physical address below
`2^47`. -/
theorem paddrN_within {p sb fi : U64} {d : Bool} (h : UtW (.Untyped p sb fi d)) {q : U64} (h1 : p.val ≤ q.val)
    (h2 : q.val < p.val + 2 ^ sb.val) : paddrN q < 2 ^ 47 := by
  have := Fl4Proofs.P0.Consts.layout.PPTR_BASE.val_eq
  have : p.val < 2 ^ 64 := p.hBounds
  have : q.val < 2 ^ 64 := q.hBounds
  simp only [UtW, paddrN] at h ⊢
  cases d
  · have := h.1 rfl; omega
  · have := h.2 rfl; omega

theorem utW_nonphys {c : capability.Cap} (h : physF c = false) : UtW c := by
  cases c <;> simp only [UtW]
  rw [show physF (.Untyped _ _ _ _) = true from ok_inj (phys_eq _).symm] at h; cases h

theorem utW_ram {p sb fi : U64} (h : UtW (.Untyped p sb fi false)) : layout.PPTR_BASE.val ≤ p.val := h.1 rfl

/-- **The untyped regions placed**: every untyped cap of the MDB `UtW`
(what retype's new VSpace caps need for their physical addresses,
`NewVPlaced`). -/
def UtWin (mem : U64 → U64) (G : MdbGhost) : Prop :=
  ∀ x ∈ G.chains.flatten, UtW (capV mem x)

/-- `c'` is untyped only as `c` is, with the same region and device flag
(what the untyped-cap invariants need of an inserted cap; `shape` forgets
the device flag). -/
def UtLike (c' c : capability.Cap) : Prop :=
  ∀ p sb fi d, c' = .Untyped p sb fi d → ∃ fi', c = .Untyped p sb fi' d

/-- An inserted cap (`InsCtx`): `src`'s own cap when untyped, else of its
shape. -/
theorem utLike_ins {c s : capability.Cap} (hutc : isUt s = true → c = s) (hsh : shape c = shape s) :
    UtLike c s := by
  intro p sb fi d hc
  subst hc
  cases s with
  | Untyped p' sb' fi' d' => exact ⟨fi, (hutc rfl).symm⟩
  | _ => simp [shape] at hsh

/-- `src`'s cap after an insertion (set full when untyped). -/
theorem utLike_fullF (s c : capability.Cap) : UtLike ((fullF s c).getD s) s := by
  intro p sb fi d h
  cases hf : fullF s c with
  | none => rw [hf] at h; exact ⟨fi, h⟩
  | some c' =>
    rw [hf] at h
    cases s with
    | Untyped p1 b1 f1 d1 =>
      cases c with
      | Untyped p2 b2 f2 d2 =>
        simp only [fullF] at hf
        split_ifs at hf
        cases hf
        simp only [Option.getD_some, capability.Cap.Untyped.injEq] at h
        obtain ⟨rfl, rfl, -, rfl⟩ := h
        exact ⟨f1, rfl⟩
      | _ => simp [fullF] at hf
    | _ => simp [fullF] at hf

/-- An insertion grows every chain. -/
theorem insG_chains_sub (G : MdbGhost) (src dest : U64) (b : Bool) :
    ∀ ch ∈ G.chains, ∃ ch' ∈ (insG G src dest b).chains, ∀ z ∈ ch, z ∈ ch' := by
  intro ch hch
  refine ⟨Mdb.insAfter src dest ch, List.mem_map.2 ⟨ch, hch, rfl⟩, fun z hz => ?_⟩
  by_cases hs : src ∈ ch
  · exact (mem_insAfter hs).2 (Or.inr hz)
  · rw [Mdb.insAfter_of_not_mem hs]; exact hz

/-- **What an operation did to the MDB** (see the module docstring). -/
inductive MdbStep : (U64 → U64) → MdbGhost → (U64 → U64) → MdbGhost → Prop
  /-- The MDB's caps and revocable bits kept. -/
  | keep {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
      (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z)
      (hr : ∀ z ∈ G.chains.flatten, revOf mem' z = revOf mem z) : MdbStep mem G mem' G
  /-- One slot's cap replaced by one alike. -/
  | recap {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) (x0 : U64)
      (ha : CapAlike (capV mem' x0) (capV mem x0))
      (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 (capV mem x0) → Vs.VCapOK P L4 L3 L2 L1 (capV mem' x0))
      (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z)
      (hr : ∀ z ∈ G.chains.flatten, revOf mem' z = revOf mem z) : MdbStep mem G mem' G
  /-- An untyped cap's free index changed: up, or down without descendants. -/
  | setFi {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) (hI : MdbInv mem G)
      {x p sb fi f : U64} {dev : Bool} (hx : x ∈ G.chains.flatten)
      (hcx : capV mem x = .Untyped p sb fi dev) (hcx' : capV mem' x = .Untyped p sb f dev)
      (hf : f.val ≤ 2 ^ sb.val) (hdir : fi.val ≤ f.val ∨ ∀ y, ¬ Mdb.Desc G.par y x)
      (hc : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z)
      (hr : ∀ z ∈ G.chains.flatten, revOf mem' z = revOf mem z) : MdbStep mem G mem' G
  /-- A derived cap inserted after `src` (`src` set full if untyped). -/
  | insert {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} {src dest : U64} {c c1 : capability.Cap}
      (h : InsCtx th mem mem' G src dest c c1)
      (hc1 : c1 = (fullF (capV mem src) c).getD (capV mem src))
      (hutc : isUt (capV mem src) = true → c = capV mem src) (hok : okey c = okey (capV mem src))
      (b : Bool) (hb : isUt (capV mem src) = true → b = true)
      (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 (capV mem src) → Vs.VCapOK P L4 L3 L2 L1 c) :
      MdbStep mem G mem' (insG G src dest b)
  /-- A non-physical cap naming no object inserted after a non-physical `src`. -/
  | nonphys {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) {src dest : U64}
      {c : capability.Cap} (b : Bool) (hsrc : src ∈ G.chains.flatten) (hdest : dest ∉ G.chains.flatten)
      (hsp : physF (capV mem src) = false) (hcd : capV mem' dest = c) (hcp : physF c = false)
      (hrefs : Fl4Spec.objRefs (absCap c) = ∅)
      (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z)
      (hr : ∀ z ∈ G.chains.flatten, revOf mem' z = revOf mem z) : MdbStep mem G mem' (insG G src dest b)
  /-- A slot removed from its chain. -/
  | remove {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) (x : U64)
      (hc : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z)
      (hr : ∀ z ∈ G.chains.flatten, z ≠ x → revOf mem' z = revOf mem z) : MdbStep mem G mem' (remG G x)
  /-- The slots renamed along `e`. -/
  | rename {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) (e : U64 ≃ U64)
      (ha : ∀ z ∈ G.chains.flatten, CapAlike (capV mem' (e z)) (capV mem z) ∧ revOf mem' (e z) = revOf mem z)
      (hv : ∀ z ∈ G.chains.flatten, ∀ P L4 L3 L2 L1 : Set U64,
        Vs.VCapOK P L4 L3 L2 L1 (capV mem z) → Vs.VCapOK P L4 L3 L2 L1 (capV mem' (e z))) :
      MdbStep mem G mem' (renG G e)
  /-- A 4 KiB alias of a page of `src`'s large RAM frame, not revocable,
  inserted after it; the MDB's large frames 2 MiB aligned. -/
  | frameAlias {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) (hI : MdbInv mem G)
      {src dest : U64} (b : Bool) (hsrc : src ∈ G.chains.flatten) (hdest : dest ∉ G.chains.flatten)
      {ptr rt fa fv q0 vm : U64} {mm : Bool}
      (hsC : capV mem src = .Frame ptr .Large rt false mm false fa fv)
      (hcd : capV mem' dest = .Frame q0 .Small vm false false false 0#u64 0#u64)
      (hq1 : ptr.val ≤ q0.val) (hq2 : q0.val < ptr.val + 2 ^ 21)
      (hcin : Within (capV mem' dest) (capV mem src)) (hcr : baseF (capV mem' dest) ≤ topF (capV mem' dest))
      (halg : ∀ x ∈ G.chains.flatten, ∀ p r m ep a va, capV mem x = .Frame p .Large r false m ep a va → p.val % 2 ^ 21 = 0)
      (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) (hrd : revOf mem' dest = false)
      (hr : ∀ z ∈ G.chains.flatten, revOf mem' z = revOf mem z)
      (hq4 : q0.val + 4096 ≤ ptr.val + 2 ^ 21) (hqal : q0.val % 4096 = 0) : MdbStep mem G mem' (insG G src dest b)
  /-- An ASID pool cap over a full untyped cap's whole region, as its only
  child. -/
  | pool {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) (hI : MdbInv mem G)
      {x val p sb f q b : U64} {d : Bool} (hx : x ∈ G.chains.flatten) (hcx : capV mem x = .Untyped p sb f d)
      (hf : f.val = 2 ^ sb.val) (hnd : ∀ y, ¬ Mdb.Desc G.par y x) (hval : val ∉ G.chains.flatten)
      (hcf : capV mem' val = .AsidPool q b)
      (hbA : baseF (.AsidPool q b) = baseF (capV mem x)) (htA : topF (.AsidPool q b) = topF (capV mem x))
      (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z)
      (hr : ∀ z ∈ G.chains.flatten, revOf mem' z = revOf mem z)
      (hb : b.val % 512 = 0 ∧ b.val < 2 ^ 20 ∧ q ≠ 0#u64) : MdbStep mem G mem' (insG G x val true)
  /-- Retype's new caps. -/
  | retype {th : TypedHeap} {mem0 mem1 memf : U64 → U64} {G0 Gf : MdbGhost} {src p sb fi nfi : U64} {dev : Bool}
      {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
      (h : RetypeDelta th mem0 mem1 memf G0 Gf src p sb fi nfi dev A k w dslot cj) (hI : MdbInv mem0 G0)
      (hch : ∀ ch ∈ G0.chains, ∃ ch' ∈ Gf.chains, ∀ z ∈ ch, z ∈ ch')
      (hr : ∀ z ∈ G0.chains.flatten, revOf memf z = revOf mem0 z)
      (hvc : UtW (.Untyped p sb fi dev) → ∀ j, j < w → NewVPlaced (cj j)) :
      MdbStep mem0 G0 memf Gf
  /-- Two steps in sequence. -/
  | trans {mem1 mem2 mem3 : U64 → U64} {G1 G2 G3 : MdbGhost} :
      MdbStep mem1 G1 mem2 G2 → MdbStep mem2 G2 mem3 G3 → MdbStep mem1 G1 mem3 G3

theorem MdbStep.refl {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) :
    MdbStep mem G mem G :=
  .keep hM (fun _ _ => rfl) (fun _ _ => rfl)

/-- Writes outside the slots are a `keep` step. -/
theorem MdbStep.of_same {th : TypedHeap} {m m' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th m G)
    (h : SlotsSame th m m') : MdbStep m G m' G :=
  .keep hM (fun z hz => h.capV ((hM.members z).1 hz).1) (fun z hz => h.revOf ((hM.members z).1 hz).1)

/-- A step, then writes outside the slots. -/
theorem MdbStep.same_right {th : TypedHeap} {m1 m2 m3 : U64 → U64} {G1 G2 : MdbGhost} (h : MdbStep m1 G1 m2 G2)
    (hM : MdbLinks th m2 G2) (hS : SlotsSame th m2 m3) : MdbStep m1 G1 m3 G2 := h.trans (.of_same hM hS)

/-- Writes outside the slots, then a step. -/
theorem MdbStep.same_left {th : TypedHeap} {m1 m2 m3 : U64 → U64} {G1 G2 : MdbGhost} (hM : MdbLinks th m1 G1)
    (hS : SlotsSame th m1 m2) (h : MdbStep m2 G1 m3 G2) : MdbStep m1 G1 m3 G2 := (MdbStep.of_same hM hS).trans h

end

end Fl4Proofs.P3

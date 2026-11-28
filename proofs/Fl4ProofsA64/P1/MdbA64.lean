/-
P1 (aarch64, gen 46): **an A64 MDB chain ghost with its link invariant, and `RngOneA64`** (Architect ruling: CDT
adjacency as an independent step-preserved invariant in x86 `RngOne`'s shape, P3/VirtRngOne, over all object types,
to be conjoined beside the step relation as `JV ∧ MdbLk ∧ RngOneA64`; not in `SlotTyEnt*`).

* `capA st s x`: the cap slot `x` holds (`obj.Slot.cap` is total: `capA_eq`); `NxA st s x`: its `NEXT` pointer
  (`obj.Slot.next`'s value, `next_eq`); `ptrA` / `physA` / `sizeA`: the kernel's own `Cap::ptr`,
  `cap_is_physical`, `cap_size_bits` (objects.rs:20–48, capability.rs:301–323) as total functions.
* **`MdbLk st OS G s`** (P3's `MdbLinks` shape, A64's raw slot words): the ghost `G` (chains of slots, in `NEXT`
  order) has distinct members, no empty chain; consecutive members are linked both ways (`NEXT` of one is the
  next, `PREV` word of the next is the one); a chain's head has `PREV` 0 and its last `NEXT` 0; the members are
  exactly the `OS` slots with a non-null cap. (P3's parent map `par` / `MdbOK` is not carried: `RngOneA64` does not
  need it.)
* `RngKeyA c` (physical, not untyped, not a frame: the caps a non-overlap fact lets share a range only exactly) and
  `clsA c = (ptr, size bits)` (the exact physical range, base and size). **`RngOneA64 st G s`**: `one` — two members
  whose caps are `RngKeyA` of the same class lie in a common chain (x86 `RngOne`); `chunk` — inside a chain the
  members of one class are contiguous (x86 derives this, `VcpuChunked`, from `MdbInv`'s tree; A64 has no tree
  invariant, so it is a field). `is_final_capability` (cdt.rs:158–175) looks only at the two neighbours.
* Boot: `MdbLk.empty` (no non-null cap in `OS`: the empty ghost), `RngOneA64.empty`.
* Preservation, generic: `MdbLk.keep` / `RngOneA64.keep` (the ghost kept; every `OS` slot's link words kept and
  null-ness kept; each member's class kept); the in-place `set_cap` instance `set_cap_links` / `capA_wr2_other`,
  **`MdbLk.set_cap`**, **`RngOneA64.set_cap`** (a non-null cap replaced by a non-null one of the same class, e.g.
  ARMPageTableUnmap's / ARMPageTableMap's / `Assign`'s cap rewrites), `RngKeyA.pt` / `clsA_pt` (`PageTable` caps).

Not yet (still owed): `MdbLk` / `RngOneA64` along `cdt::insert` / `empty_slot` (chain with the slot erased) /
`swap` (chains renamed) and through gen 41's deletion loops; `hone` from `RngOneA64` — which also needs that caps of
one class name objects of one kind (`Thread p` and `PageTable p` are both of class `(p, 12)`: TCB bits 12), i.e. an
object-kind typing of the caps.

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueUnmD
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64}
variable {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## Caps, ranges and links as total functions -/

theorem ptrA_total (c : capability.Cap) : ∃ v, capability.Cap.ptr c = ok v := by cases c <;> exact ⟨_, rfl⟩
theorem physA_total (c : capability.Cap) : ∃ v, objects.cap_is_physical c = ok v := by cases c <;> exact ⟨_, rfl⟩
theorem sizeA_total (c : capability.Cap) : ∃ v, objects.cap_size_bits c = ok v := by
  cases c with
  | Frame p sz _ _ _ _ _ _ => cases sz <;> exact ⟨_, rfl⟩
  | Zombie p zt n => simp only [objects.cap_size_bits]; split <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

noncomputable def ptrA (c : capability.Cap) : U64 := Classical.choose (ptrA_total c)
noncomputable def physA (c : capability.Cap) : Bool := Classical.choose (physA_total c)
noncomputable def sizeA (c : capability.Cap) : U64 := Classical.choose (sizeA_total c)
theorem ptrA_eq (c : capability.Cap) : capability.Cap.ptr c = ok (ptrA c) := Classical.choose_spec (ptrA_total c)
theorem physA_eq (c : capability.Cap) : objects.cap_is_physical c = ok (physA c) :=
  Classical.choose_spec (physA_total c)
theorem sizeA_eq (c : capability.Cap) : objects.cap_size_bits c = ok (sizeA c) :=
  Classical.choose_spec (sizeA_total c)

def isUtA : capability.Cap → Bool
  | .Untyped .. => true
  | _ => false

def isFrA : capability.Cap → Bool
  | .Frame .. => true
  | _ => false

/-- A cap in an exact range class: physical, not untyped, not a frame. -/
def RngKeyA (c : capability.Cap) : Prop := physA c = true ∧ isUtA c = false ∧ isFrA c = false

/-- The exact range class: base and size bits. -/
noncomputable def clsA (c : capability.Cap) : U64 × U64 := (ptrA c, sizeA c)

theorem RngKeyA.pt (p : U64) (m : Bool) (a v : U64) : RngKeyA (.PageTable p m a v) := by
  have h := physA_eq (.PageTable p m a v)
  simp only [objects.cap_is_physical] at h
  exact ⟨(okinj h).symm, rfl, rfl⟩

theorem clsA_pt (p : U64) (m : Bool) (a v : U64) : clsA (.PageTable p m a v) = (p, 12#u64) := by
  have h1 := ptrA_eq (.PageTable p m a v)
  have h2 := sizeA_eq (.PageTable p m a v)
  simp only [capability.Cap.ptr] at h1
  simp only [objects.cap_size_bits] at h2
  unfold clsA; rw [← okinj h1, ← okinj h2]

/-- The cap slot `x` holds at `s`. -/
def capA (st : machine.Store S) [L : LawfulStore st] (s : S) (x : U64) : capability.Cap :=
  CapRt.decodeF (L.mem s x).bv (L.mem s (wa x 8#u64)).bv

theorem capA_eq (s : S) (x : U64) : obj.Slot.cap st x s = ok (capA st s x) := by
  rw [DPF.slot_cap_dec, CapRt.decode_eq]; rfl

/-- `sext48`'s value. -/
def sxF (w : U64) : U64 :=
  if ((w &&& 281474976710655#u64) &&& 140737488355328#u64 != 0#u64) = true
  then (w &&& 281474976710655#u64) ||| 18446462598732840960#u64 else w &&& 281474976710655#u64

theorem sext48_eq (w : U64) : obj.sext48 w = ok (sxF w) := by
  rw [sx_val]; unfold sxF; split <;> rfl

/-- The `NEXT` pointer of slot `x` at `s`. -/
def NxA (st : machine.Store S) [L : LawfulStore st] (s : S) (x : U64) : U64 := sxF (L.mem s (wa x 24#u64))

theorem next_eq (s : S) (x : U64) : obj.Slot.next st x s = ok (NxA st s x) := slot_next_of (sext48_eq _)

/-! ## The ghost, the link invariant, `RngOneA64` -/

/-- **The MDB link invariant** (module docstring). -/
structure MdbLk (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (G : List (List U64)) (s : S) :
    Prop where
  nodup : G.flatten.Nodup
  ne_nil : ∀ ch ∈ G, ch ≠ []
  chain : ∀ ch ∈ G, ∀ i a b, ch[i]? = some a → ch[i + 1]? = some b →
    NxA st s a = b ∧ L.mem s (wa b 16#u64) = a
  head : ∀ ch ∈ G, ∀ a, ch.head? = some a → L.mem s (wa a 16#u64) = 0#u64
  last : ∀ ch ∈ G, ∀ a, ch.getLast? = some a → NxA st s a = 0#u64
  members : ∀ x, x ∈ G.flatten ↔ x ∈ OS ∧ capA st s x ≠ .Null

/-- **`RngOneA64`** (module docstring): every exact range class of `RngKeyA` caps lies in one chain, contiguously. -/
structure RngOneA64 (st : machine.Store S) [L : LawfulStore st] (G : List (List U64)) (s : S) : Prop where
  one : ∀ y ∈ G.flatten, ∀ y' ∈ G.flatten, RngKeyA (capA st s y) → RngKeyA (capA st s y') →
    clsA (capA st s y) = clsA (capA st s y') → ∃ ch ∈ G, y ∈ ch ∧ y' ∈ ch
  chunk : ∀ ch ∈ G, ∀ (i j k : Nat) (y z y' : U64), ch[i]? = some y → ch[j]? = some z → ch[k]? = some y' →
    i < j → j < k → RngKeyA (capA st s y) → RngKeyA (capA st s y') →
    clsA (capA st s y) = clsA (capA st s y') → RngKeyA (capA st s z) ∧ clsA (capA st s z) = clsA (capA st s y)

/-- **Boot**: no non-null cap in `OS` — the empty ghost. -/
theorem MdbLk.empty {OS : Set U64} {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : MdbLk st OS [] s :=
  ⟨by simp, by simp, by simp, by simp, by simp, fun x => by
    simp only [List.flatten_nil, List.not_mem_nil, false_iff, not_and, not_not]; exact h x⟩

theorem RngOneA64.empty {s : S} : RngOneA64 st [] s := ⟨by simp, by simp⟩

/-- **`MdbLk` with the ghost kept**: every `OS` slot's link words and null-ness kept. -/
theorem MdbLk.keep {OS : Set U64} {G : List (List U64)} {s s' : S} (h : MdbLk st OS G s)
    (hl : ∀ x ∈ OS, L.mem s' (wa x 16#u64) = L.mem s (wa x 16#u64) ∧ L.mem s' (wa x 24#u64) = L.mem s (wa x 24#u64))
    (hn : ∀ x ∈ OS, (capA st s' x = .Null ↔ capA st s x = .Null)) : MdbLk st OS G s' := by
  have hOS : ∀ x ∈ G.flatten, x ∈ OS := fun x hx => ((h.members x).1 hx).1
  have hmem : ∀ ch ∈ G, ∀ i a, ch[i]? = some a → a ∈ OS := fun ch hch i a ha =>
    hOS a (List.mem_flatten.2 ⟨ch, hch, List.mem_of_getElem? ha⟩)
  have hnx : ∀ a ∈ OS, NxA st s' a = NxA st s a := fun a ha => by unfold NxA; rw [(hl a ha).2]
  refine ⟨h.nodup, h.ne_nil, fun ch hch i a b ha hb => ?_, fun ch hch a ha => ?_, fun ch hch a ha => ?_,
    fun x => ?_⟩
  · rw [hnx a (hmem ch hch i a ha), (hl b (hmem ch hch (i + 1) b hb)).1]
    exact h.chain ch hch i a b ha hb
  · have ha' : a ∈ OS := hmem ch hch 0 a (by rw [← List.head?_eq_getElem?]; exact ha)
    rw [(hl a ha').1]; exact h.head ch hch a ha
  · have ha' : a ∈ OS := hOS a (List.mem_flatten.2 ⟨ch, hch, List.mem_of_getLast? ha⟩)
    rw [hnx a ha']; exact h.last ch hch a ha
  · rw [h.members x]
    constructor
    · rintro ⟨hx, hc⟩; exact ⟨hx, fun e => hc ((hn x hx).1 e)⟩
    · rintro ⟨hx, hc⟩; exact ⟨hx, fun e => hc ((hn x hx).2 e)⟩

/-- **`RngOneA64` with the ghost kept**: each member's key and class kept. -/
theorem RngOneA64.keep {G : List (List U64)} {s s' : S} (h : RngOneA64 st G s)
    (hk : ∀ x ∈ G.flatten, (RngKeyA (capA st s' x) ↔ RngKeyA (capA st s x)) ∧
      (RngKeyA (capA st s x) → clsA (capA st s' x) = clsA (capA st s x))) : RngOneA64 st G s' := by
  refine ⟨fun y hy y' hy' k k' hc => ?_, fun ch hch i j k y z y' hi hj hk' hij hjk ky ky' hc => ?_⟩
  · have k0 := (hk y hy).1.1 k
    have k0' := (hk y' hy').1.1 k'
    refine h.one y hy y' hy' k0 k0' ?_
    rw [← (hk y hy).2 k0, ← (hk y' hy').2 k0']; exact hc
  · have mem : ∀ {n w}, ch[n]? = some w → w ∈ G.flatten := fun e =>
      List.mem_flatten.2 ⟨ch, hch, List.mem_of_getElem? e⟩
    have k0 := (hk y (mem hi)).1.1 ky
    have k0' := (hk y' (mem hk')).1.1 ky'
    obtain ⟨kz, cz⟩ := h.chunk ch hch i j k y z y' hi hj hk' hij hjk k0 k0' (by
      rw [← (hk y (mem hi)).2 k0, ← (hk y' (mem hk')).2 k0']; exact hc)
    refine ⟨(hk z (mem hj)).1.2 kz, ?_⟩
    rw [(hk z (mem hj)).2 kz, (hk y (mem hi)).2 k0]; exact cz

/-! ## The in-place `set_cap` -/

section setcap
variable {OS : Set U64}

/-- A two-word cap write into slot `x0` keeps every `OS` slot's link words. -/
theorem set_cap_links (hO : OSOK T Ω Sg OS) {s : S} {x0 w0 w1 : U64} (hx0 : x0 ∈ OS) :
    ∀ y ∈ OS, L.mem (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) (wa y 16#u64) = L.mem s (wa y 16#u64) ∧
      L.mem (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) (wa y 24#u64) = L.mem s (wa y 24#u64) := by
  intro y hy
  obtain ⟨v8, v16, v24⟩ := vals hO hx0
  have a0 := hO.al0 hx0
  have a8 := hO.al hx0 (k := 8#u64) (by simp) (by simp)
  by_cases hyx : y = x0
  · subst hyx
    have a16 := hO.al hy (k := 16#u64) (by simp) (by simp)
    have a24 := hO.al hy (k := 24#u64) (by simp) (by simp)
    exact ⟨by rw [L.mem_wr_ne a8 a16 (by omega), L.mem_wr_ne a0 a16 (by omega)],
      by rw [L.mem_wr_ne a8 a24 (by omega), L.mem_wr_ne a0 a24 (by omega)]⟩
  · obtain ⟨-, -, e16, e24⟩ := other_keep (st := st) (s := L.wr s x0 w0) (v := w1) hO hx0 hy hyx a8 ⟨by omega, by omega⟩
    obtain ⟨-, -, f16, f24⟩ := other_keep (st := st) (s := s) (v := w0) hO hx0 hy hyx a0 ⟨by omega, by omega⟩
    exact ⟨e16.trans f16, e24.trans f24⟩

/-- A two-word cap write into slot `x0` keeps every other `OS` slot's cap. -/
theorem capA_wr2_other (hO : OSOK T Ω Sg OS) {s : S} {x0 w0 w1 : U64} (hx0 : x0 ∈ OS) {y : U64} (hy : y ∈ OS)
    (hyx : y ≠ x0) : capA st (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) y = capA st s y := by
  obtain ⟨v8, -, -⟩ := vals hO hx0
  obtain ⟨e0, e8, -, -⟩ := other_keep (st := st) (s := L.wr s x0 w0) (v := w1) hO hx0 hy hyx
    (hO.al hx0 (k := 8#u64) (by simp) (by simp)) ⟨by omega, by omega⟩
  obtain ⟨f0, f8, -, -⟩ := other_keep (st := st) (s := s) (v := w0) hO hx0 hy hyx (hO.al0 hx0) ⟨by omega, by omega⟩
  unfold capA; rw [e0, e8, f0, f8]

/-- A two-word cap write into slot `x0` makes it hold the decoded cap. -/
theorem capA_wr2_self (hO : OSOK T Ω Sg OS) {s : S} {x0 w0 w1 : U64} (hx0 : x0 ∈ OS) {c : capability.Cap}
    (hd : capability.Cap.decode w0 w1 = ok c) : capA st (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) x0 = c := by
  obtain ⟨v8, -, -⟩ := vals hO hx0
  have a0 := hO.al0 hx0
  have a8 := hO.al hx0 (k := 8#u64) (by simp) (by simp)
  have h0 : L.mem (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) x0 = w0 := by
    rw [L.mem_wr_ne a8 a0 (by omega), L.mem_wr_same a0]
  have h8 : L.mem (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) (wa x0 8#u64) = w1 := L.mem_wr_same a8
  have := capA_eq (st := st) (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) x0
  rw [DPF.slot_cap_dec, h0, h8, hd] at this; exact (okinj this).symm

/-- **`MdbLk` along an in-place `set_cap`** of a non-null cap into a slot holding a non-null cap. -/
theorem MdbLk.set_cap (hO : OSOK T Ω Sg OS) {G : List (List U64)} {s : S} (h : MdbLk st OS G s) {x0 : U64}
    (hx0 : x0 ∈ OS) {c : capability.Cap} {w0 w1 : U64} (hd : capability.Cap.decode w0 w1 = ok c)
    (hc : c ≠ .Null) (hc0 : capA st s x0 ≠ .Null) : MdbLk st OS G (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) := by
  refine h.keep (set_cap_links hO hx0) fun y hy => ?_
  by_cases hyx : y = x0
  · subst hyx
    have e : capA st (L.wr (L.wr s y w0) (wa y 8#u64) w1) y = c := capA_wr2_self hO hx0 hd
    rw [e]; exact ⟨fun h' => absurd h' hc, fun h' => absurd h' hc0⟩
  · rw [capA_wr2_other hO hx0 hy hyx]

/-- **`RngOneA64` along an in-place `set_cap`** of a cap with the old cap's key and class. -/
theorem RngOneA64.set_cap (hO : OSOK T Ω Sg OS) {G : List (List U64)} {s : S} (h : RngOneA64 st G s)
    (hG : ∀ x ∈ G.flatten, x ∈ OS) {x0 : U64} (hx0 : x0 ∈ OS) {c : capability.Cap} {w0 w1 : U64}
    (hd : capability.Cap.decode w0 w1 = ok c) (hk : RngKeyA c ↔ RngKeyA (capA st s x0))
    (hcl : RngKeyA (capA st s x0) → clsA c = clsA (capA st s x0)) :
    RngOneA64 st G (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) := by
  refine h.keep fun y hy => ?_
  by_cases hyx : y = x0
  · subst hyx
    have e : capA st (L.wr (L.wr s y w0) (wa y 8#u64) w1) y = c := capA_wr2_self hO hx0 hd
    rw [e]; exact ⟨hk, hcl⟩
  · rw [capA_wr2_other hO hx0 (hG y hy) hyx]; exact ⟨Iff.rfl, fun _ => rfl⟩

end setcap

end ST
end R
end W7

end

end Fl4ProofsA64.P1

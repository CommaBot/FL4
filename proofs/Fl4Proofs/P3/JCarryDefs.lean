/-
P3 (issue #16, jc1; KENTRY-PLAN g7b-4 step 1): **the first two `JCarry` facts
and their frame lemmas**, before they become a `JAtZ` field.

* `BufObjHyp B σ` (C21, C24 bufObj; moved here from XTopJointUtEp, same
  statement): every IPC-buffer word of `B` lies in a spec object.
* `ArchFitHyp H σ` (first half of C16 / C22 / C24 heapH; moved here from
  UtEpSets, same statement): an `other` object of P1's heap at a spec arch
  object is no larger than it.
* `BufPgHyp B σ`: the carried form of `BufObjHyp`, every word of `B` in a
  **non-device data page** of `σ` (`bufObj_of_pg`). `BufObjHyp` cannot be
  carried across a frame step as stated: the frame facts every `JAtZ`
  construction has (`KSz`, backward: an object after was one of the same type
  before; `IpcFrKeep.page`, forward for non-device data pages) do not keep an
  arbitrary object, while `B`'s words are user-frame words (`B` only grows by
  the frame retype's new pages, UtFrameAdd `BNew`, and is pruned by the
  detype's `KeepB (KBOf p sb)`), so the page form is the invariant.
* `JCarry Z H σ := BufPgHyp Z.B σ ∧ ArchFitHyp H σ` with `JCarry.frame`: one
  call at a frame step, from the step's `IpcFrKeep` (as `JAtZ.fcov`'s
  `FrameCover.ipcFr`) and `KSz` (as `JAtZ.sfree`'s `SpecFree.frame`), `B`
  shrunk or kept, `H` kept.

jc2 (KENTRY-PLAN g7b-4 step 3): the σ-only pair is now `JCarryS B H σ`, and
`JCarry Z H Cs s σ` adds `devApart` (C25, DevJ's `DevApart`, moved here) and
`devSep` (`DevSep`: RAM and device untyped ranges disjoint, which keeps `devApart`
across a RAM retype). Lemmas: `DevApart.frame` / `.frameH` / `.setFi`, `devRetypeR`,
`devSep_retypeD`, `DevSep.frame`, `IdleH` (the idle clause of `DevApart` from the
idle objects being `H`'s TCB and SC, `devApart_idle`), `JCarryS.withP`.
-/
import Fl4Proofs.P3.BufDefs
import Fl4Proofs.P3.StepSem
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **[J] Every IPC-buffer word lies in a spec object** (l4v
`valid_ipc_buffer_cap` + `obj_at`). -/
def BufObjHyp (B : Set (U64 × Fl4Spec.Word)) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ wp ∈ B, ∃ (o : Fl4Spec.ObjRef) (ko : Fl4Spec.KernelObject), σ.kheap o = some ko ∧ o.toNat ≤ wp.1.val ∧
    wp.1.val + 8 ≤ o.toNat + 2 ^ Fl4Spec.objBits ko

/-- **[J] P1's `other` objects fit their spec arch objects** (l4v arch
`obj_range`). -/
def ArchFitHyp (H : P1.Heap) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ o ao n, σ.kheap o = some (.archObj ao) → H ⟨o⟩ = some (.other n) → n ≤ Fl4Spec.objBits (.archObj ao)

/-- **Every word of `B` in a non-device data page** (the carried form of `BufObjHyp`). -/
def BufPgHyp (B : Set (U64 × Fl4Spec.Word)) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ wp ∈ B, ∃ (q : Fl4Spec.ObjRef) (vms : Fl4Spec.VMPageSize),
    σ.kheap q = some (.archObj (.dataPage false vms)) ∧ q.toNat ≤ wp.1.val ∧
    wp.1.val + 8 ≤ q.toNat + 2 ^ Fl4Spec.pageBitsForSize vms

theorem bufObj_of_pg {B : Set (U64 × Fl4Spec.Word)} {σ : Fl4Spec.State Unit} (h : BufPgHyp B σ) :
    BufObjHyp B σ := fun wp hw => by
  obtain ⟨q, vms, hq, h1, h2⟩ := h wp hw
  exact ⟨q, _, hq, h1, h2⟩

/-- `BufPgHyp` across a step keeping the non-device data pages, `B` shrunk or kept. -/
theorem BufPgHyp.frame {B B' : Set (U64 × Fl4Spec.Word)} {σ σ' : Fl4Spec.State Unit} (h : BufPgHyp B σ)
    (hB : B' ⊆ B)
    (hp : ∀ p vms, σ.kheap p = some (.archObj (.dataPage false vms)) →
      σ'.kheap p = some (.archObj (.dataPage false vms))) : BufPgHyp B' σ' := fun wp hw => by
  obtain ⟨q, vms, hq, h1, h2⟩ := h wp (hB hw)
  exact ⟨q, vms, hp q vms hq, h1, h2⟩

/-- `BufPgHyp` with `B` grown by words of new non-device pages (the frame retype's `BNew`). -/
theorem BufPgHyp.grow {B B' : Set (U64 × Fl4Spec.Word)} {σ σ' : Fl4Spec.State Unit} {Wn : U64 → Prop}
    (h : BufPgHyp B σ)
    (hB : ∀ wp ∈ B', wp ∈ B ∨ (Wn wp.1 ∧ wp.2 = wp.1.bv))
    (hp : ∀ p vms, σ.kheap p = some (.archObj (.dataPage false vms)) →
      σ'.kheap p = some (.archObj (.dataPage false vms)))
    (hn : ∀ a, Wn a → ∃ (q : Fl4Spec.ObjRef) (vms : Fl4Spec.VMPageSize),
      σ'.kheap q = some (.archObj (.dataPage false vms)) ∧ q.toNat ≤ a.val ∧
      a.val + 8 ≤ q.toNat + 2 ^ Fl4Spec.pageBitsForSize vms) : BufPgHyp B' σ' := fun wp hw => by
  rcases hB wp hw with hw | ⟨hw, -⟩
  · obtain ⟨q, vms, hq, h1, h2⟩ := h wp hw
    exact ⟨q, vms, hp q vms hq, h1, h2⟩
  · exact hn wp.1 hw

/-- The size an arch object type fixes. -/
def aaSize : Fl4Spec.AAType → Nat
  | .aASIDPool => Fl4Spec.pageBits
  | .aVcpu => 15
  | .aEpt _ => Fl4Spec.tableSize
  | .aPageTable => Fl4Spec.tableSize
  | .aPageDirectory => Fl4Spec.tableSize
  | .aPDPointerTable => Fl4Spec.tableSize
  | .aPageMapL4 => Fl4Spec.tableSize
  | .aUserData sz => Fl4Spec.pageBitsForSize sz
  | .aDeviceData sz => Fl4Spec.pageBitsForSize sz

theorem archKobjSize_aaSize (a : Fl4Spec.ArchKernelObj) : Fl4Spec.archKobjSize a = aaSize (Fl4Spec.aaType a) := by
  cases a <;> simp only [Fl4Spec.aaType, Fl4Spec.archKobjSize] <;> (try split) <;> rfl

/-- An object of the type of an arch object is an arch object of its size. -/
theorem archObj_of_aType {ko : Fl4Spec.KernelObject} {ao : Fl4Spec.ArchKernelObj}
    (h : Fl4Spec.aType ko = Fl4Spec.aType (.archObj ao)) :
    ∃ ao0, ko = .archObj ao0 ∧ Fl4Spec.objBits (.archObj ao0) = Fl4Spec.objBits (.archObj ao) := by
  cases ko with
  | archObj ao0 =>
    refine ⟨ao0, rfl, ?_⟩
    have e : Fl4Spec.aaType ao0 = Fl4Spec.aaType ao := by
      simpa only [Fl4Spec.aType, Fl4Spec.AType.aArch.injEq] using h
    show Fl4Spec.archKobjSize ao0 = Fl4Spec.archKobjSize ao
    rw [archKobjSize_aaSize, archKobjSize_aaSize, e]
  | cnode sz cs =>
    simp only [Fl4Spec.aType] at h; split at h <;> cases h
  | schedContext x n =>
    simp only [Fl4Spec.aType] at h; split at h <;> cases h
  | _ => simp [Fl4Spec.aType] at h

/-- `ArchFitHyp` across a step with `KSz`, `H` kept. -/
theorem ArchFitHyp.frame {H : P1.Heap} {σ σ' : Fl4Spec.State Unit} (h : ArchFitHyp H σ) (hk : KSz σ σ') :
    ArchFitHyp H σ' := by
  intro o ao n ho hH
  obtain ⟨ko, hko, ht⟩ := hk o _ ho
  obtain ⟨ao0, rfl, hb⟩ := archObj_of_aType ht
  rw [← hb]; exact h o ao0 n hko hH

/-- **The joint facts carried for the [J] leaves** (KENTRY-PLAN g7b-4; step 1:
C21 / C24 bufObj and the first half of C16 / C22 / C24 heapH). -/
structure JCarryS (B : Set (U64 × Fl4Spec.Word)) (H : P1.Heap) (σ : Fl4Spec.State Unit) : Prop where
  /-- C21, C24 bufObj, in its carried form (`JCarry.bufObj`). -/
  bufPg : BufPgHyp B σ
  /-- C16, C22, C24 heapH (first half). -/
  archFit : ArchFitHyp H σ

theorem JCarryS.bufObj {B : Set (U64 × Fl4Spec.Word)} {H : P1.Heap} {σ : Fl4Spec.State Unit}
    (h : JCarryS B H σ) : BufObjHyp B σ := bufObj_of_pg h.bufPg

/-- **`JCarry` across a frame step** (module docstring). -/
theorem JCarryS.frame {B B' : Set (U64 × Fl4Spec.Word)} {H : P1.Heap} {σ σ' : Fl4Spec.State Unit}
    (h : JCarryS B H σ) (hB : B' ⊆ B) (hF : IpcFrKeep σ σ') (hk : KSz σ σ') : JCarryS B' H σ' :=
  ⟨h.bufPg.frame hB hF.page, h.archFit.frame hk⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **[J] The device untyped caps' apartness** (moved here from DevJ, jc2;
statement unchanged; l4v `valid_untyped` / `pspace_no_overlap` for device
caps, `valid_global_refs`, `kernel_window`): every device untyped cap of the
MDB has an aligned range off the kernel-state block, the nodes, the
ASID-table area, the idle objects and the typed heap's objects, and every `H`
object meeting the range lies in its used part `[p, p + fi)` and is a device
frame (`.other`); the range lies in one canonical half with a nonzero base
(`CanonR`), and its size is at least 2^4 bytes. See DevJ's docstring. -/
def DevApart (th : TypedHeap) (H : P1.Heap) (G : MdbGhost) (Cs : Set U64) (s : S) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV (L.mem s) x = .Untyped p sb fi true →
    p.val % 2 ^ sb.val = 0 ∧
    (p.val + 2 ^ sb.val ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val) ∧
    (∀ c ∈ Cs, p.val + 2 ^ sb.val ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val) ∧
    (p.val + 2 ^ sb.val ≤ (L.ksb s).val + 288000 ∨ (L.ksb s).val + 288000 + 16384 ≤ p.val) ∧
    (∀ q, Sched.IdleAt (L := L) s q → q.val < p.val ∨ p.val + 2 ^ sb.val ≤ q.val) ∧
    RegionFree th p.val (p.val + 2 ^ sb.val) ∧
    (∀ q kd, H q = some kd → q.val + 2 ^ kd.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val ∨
      (p.val ≤ q.val ∧ q.val + 2 ^ kd.bits ≤ p.val + fi.val ∧ ∃ z, kd = .other z)) ∧
    CanonR p.val (p.val + 2 ^ sb.val) ∧ 4 ≤ sb.val

/-- **[carried] RAM and device untyped ranges are disjoint** (jc2; l4v
`untyped_inc` with the device flag inherited by retype: two untyped caps
whose ranges meet are nested, `UtInv.drange`, and a child untyped has its
parent's device flag; boot hands out RAM and device regions apart). Needed to
keep `DevApart` across a RAM retype, whose new objects lie in the RAM
source's free part. -/
def DevSep (G : MdbGhost) (m : U64 → U64) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ y ∈ G.chains.flatten, ∀ p sb fi p' sb' fi',
    capV m x = .Untyped p sb fi false → capV m y = .Untyped p' sb' fi' true →
    p.val + 2 ^ sb.val ≤ p'.val ∨ p'.val + 2 ^ sb'.val ≤ p.val

/-- The device untyped caps after a step are old ones with the same region
and a free index no larger (`UtFrom` for device caps, with the order). -/
def DevFrom (G G' : MdbGhost) (m m' : U64 → U64) : Prop :=
  ∀ x ∈ G'.chains.flatten, ∀ p sb fi, capV m' x = .Untyped p sb fi true →
    ∃ y ∈ G.chains.flatten, ∃ fi0 : U64, fi0.val ≤ fi.val ∧ capV m y = .Untyped p sb fi0 true

/-- **The idle objects are `H` objects other than frames** (or the idle SC
null): the idle TCB is a TCB of `H`, the idle SC an SC of `H` (`idleH_of`,
JointAt, from `ActIdle`, `Inv.back` and `JPlaced`). With `DevApart`'s `H`
clause and `CanonR` this gives its idle clause at any state. -/
def IdleH (H : P1.Heap) (s : S) : Prop :=
  H (L.idleW s) = some .tcb ∧ (Sched.idleScW (L := L) s = 0#u64 ∨ ∃ z, H (Sched.idleScW (L := L) s) = some (.sc z))

theorem DevFrom.of_eq {G : MdbGhost} {m m' : U64 → U64}
    (h : ∀ x ∈ G.chains.flatten, capV m' x = capV m x) : DevFrom G G m m' :=
  fun x hx p sb fi hc => ⟨x, hx, fi, le_rfl, by rw [← h x hx]; exact hc⟩

theorem DevFrom.toUtFrom {G G' : MdbGhost} {m m' : U64 → U64} (h : DevFrom G G' m m')
    (hr : ∀ x ∈ G'.chains.flatten, ∀ p sb fi, capV m' x = .Untyped p sb fi false →
      ∃ y ∈ G.chains.flatten, ∃ fi', capV m y = .Untyped p sb fi' false) : Sched.UtFrom G G' m m' := by
  intro x hx p sb fi d hc
  cases d
  · exact hr x hx p sb fi hc
  · obtain ⟨y, hy, fi0, -, e⟩ := h x hx p sb fi hc; exact ⟨y, hy, fi0, e⟩

/-- **`DevSep` across a step whose untyped caps are old ones** (`UtFrom`). -/
theorem DevSep.frame {G G' : MdbGhost} {m m' : U64 → U64} (h : DevSep G m) (hU : Sched.UtFrom G G' m m') :
    DevSep G' m' := by
  intro x hx y hy p sb fi p' sb' fi' hcx hcy
  obtain ⟨x0, hx0, f1, e1⟩ := hU x hx p sb fi false hcx
  obtain ⟨y0, hy0, f2, e2⟩ := hU y hy p' sb' fi' true hcy
  exact h x0 hx0 y0 hy0 p sb _ p' sb' _ e1 e2

/-- The idle clause of `DevApart` from `IdleH`, the `H` clause and `CanonR`. -/
theorem devApart_idle {H : P1.Heap} {s : S} (hI : IdleH (L := L) H s) {p sb fi : U64}
    (hH : ∀ q kd, H q = some kd → q.val + 2 ^ kd.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val ∨
      (p.val ≤ q.val ∧ q.val + 2 ^ kd.bits ≤ p.val + fi.val ∧ ∃ z, kd = .other z))
    (hc : CanonR p.val (p.val + 2 ^ sb.val)) :
    ∀ q, Sched.IdleAt (L := L) s q → q.val < p.val ∨ p.val + 2 ^ sb.val ≤ q.val := by
  have key : ∀ q kd, H q = some kd → (∀ z, kd ≠ .other z) → q.val < p.val ∨ p.val + 2 ^ sb.val ≤ q.val := by
    intro q kd hq hn
    have := Nat.one_le_two_pow (n := kd.bits)
    rcases hH q kd hq with e | e | ⟨-, -, z, rfl⟩
    · left; omega
    · right; exact e
    · exact absurd rfl (hn z)
  rintro q (rfl | rfl)
  · exact key _ _ hI.1 fun z e => by cases e
  · rcases hI.2 with e | ⟨z, e⟩
    · left; rw [e]; exact hc.1
    · exact key _ _ e fun z' e' => by cases e'

/-- **`DevApart` across a step** keeping the kernel-state base, the typed heap
and `H` (or shrinking them), the device caps old ones with a free index no
smaller (`DevFrom`); the idle clause from `IdleH` after. -/
theorem DevApart.frame {th th' : TypedHeap} {H H' : P1.Heap} {G G' : MdbGhost} {Cs : Set U64} {s s' : S}
    (h : DevApart (L := L) th H G Cs s) (hth : ∀ q k, th' q = some k → th q = some k)
    (hH : ∀ q k, H' q = some k → H q = some k) (hks : L.ksb s' = L.ksb s)
    (hD : DevFrom G G' (L.mem s) (L.mem s')) (hI : IdleH (L := L) H' s') :
    DevApart (L := L) th' H' G' Cs s' := by
  intro x hx p sb fi hc
  obtain ⟨y, hy, fi0, hle, hc0⟩ := hD x hx p sb fi hc
  obtain ⟨a1, a2, a3, a4, -, a6, a7, a8, a9⟩ := h y hy p sb fi0 hc0
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  have a7' : ∀ q kd, H' q = some kd → q.val + 2 ^ kd.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val ∨
      (p.val ≤ q.val ∧ q.val + 2 ^ kd.bits ≤ p.val + fi.val ∧ ∃ z, kd = .other z) := by
    intro q kd hq
    rcases a7 q kd (hH q kd hq) with e | e | ⟨e1, e2, e3⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr ⟨e1, by omega, e3⟩)
  exact ⟨a1, by rw [hks]; exact a2, fun c hc => by rw [hnb]; exact a3 c hc, by rw [hks]; exact a4,
    devApart_idle hI a7' a8, fun q k hq => a6 q k (hth q k hq), a7', a8, a9⟩

/-- **`DevApart` across a write of one device cap's free index** (the reset's
`set_cap` to `Untyped p sb f' true`), every `H` object meeting the range below
the new free index (`hHr`), the other caps kept. -/
theorem DevApart.setFi {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {Cs : Set U64} {s s' : S}
    (h : DevApart (L := L) th H G Cs s) (hks : L.ksb s' = L.ksb s) (hI : IdleH (L := L) H s')
    {x p sb f f' : U64} (hx : x ∈ G.chains.flatten) (hcx : capV (L.mem s) x = .Untyped p sb f true)
    (hcx' : capV (L.mem s') x = .Untyped p sb f' true)
    (hco : ∀ y ∈ G.chains.flatten, y ≠ x → capV (L.mem s') y = capV (L.mem s) y)
    (hHr : ∀ q kd, H q = some kd → q.val + 2 ^ kd.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val ∨
      (p.val ≤ q.val ∧ q.val + 2 ^ kd.bits ≤ p.val + f'.val ∧ ∃ z, kd = .other z)) :
    DevApart (L := L) th H G Cs s' := by
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  intro y hy p0 sb0 fi0 hc
  by_cases e : y = x
  · subst e
    rw [hcx'] at hc
    simp only [capability.Cap.Untyped.injEq] at hc
    obtain ⟨rfl, rfl, rfl, -⟩ := hc
    obtain ⟨a1, a2, a3, a4, -, a6, -, a8, a9⟩ := h y hy p sb f hcx
    exact ⟨a1, by rw [hks]; exact a2, fun c hc => by rw [hnb]; exact a3 c hc, by rw [hks]; exact a4,
      devApart_idle hI hHr a8, a6, hHr, a8, a9⟩
  · rw [hco y hy e] at hc
    obtain ⟨a1, a2, a3, a4, -, a6, a7, a8, a9⟩ := h y hy p0 sb0 fi0 hc
    exact ⟨a1, by rw [hks]; exact a2, fun c hc => by rw [hnb]; exact a3 c hc, by rw [hks]; exact a4,
      devApart_idle hI a7 a8, a6, a7, a8, a9⟩

/-- A RAM retype makes no device untyped cap. -/
theorem newCapOf_ram {n : Nat} {base us p sb fi : U64} : newCapOf n base us false ≠ .Untyped p sb fi true := by
  intro h
  unfold newCapOf at h
  by_cases e2 : n = 2
  · rw [if_pos e2] at h; cases h
  rw [if_neg e2] at h
  by_cases e3 : n = 3
  · rw [if_pos e3] at h; cases h
  rw [if_neg e3] at h
  by_cases e4 : n = 4
  · rw [if_pos e4] at h; cases h
  rw [if_neg e4] at h
  by_cases e0 : n = 0
  · rw [if_pos e0] at h; cases h
  rw [if_neg e0] at h
  by_cases e5 : n = 5
  · rw [if_pos e5] at h; cases h
  rw [if_neg e5] at h
  by_cases e1 : n = 1
  · rw [if_pos e1] at h; cases h
  rw [if_neg e1] at h
  by_cases e7 : n = 7
  · rw [if_pos e7] at h; cases h
  rw [if_neg e7] at h
  by_cases e8 : n = 8
  · rw [if_pos e8] at h; cases h
  rw [if_neg e8] at h
  by_cases e9 : n = 9
  · rw [if_pos e9] at h; cases h
  rw [if_neg e9] at h
  by_cases e10 : n = 10
  · rw [if_pos e10] at h; cases h
  rw [if_neg e10] at h
  by_cases e11 : n = 11
  · rw [if_pos e11] at h; cases h
  rw [if_neg e11] at h
  by_cases e12 : n = 12
  · rw [if_pos e12] at h; cases h
  rw [if_neg e12] at h
  by_cases e13 : n = 13
  · rw [if_pos e13] at h; cases h
  rw [if_neg e13] at h
  cases h

/-- `H` after a retype (`HOut`): an old object, or a new one in the window
`[A, A + w * k)` when the new kind fits a slot (jc2). -/
theorem hH_of_hout {H H' : P1.Heap} {lo hi A k w : Nat} {K : Option P1.HKind}
    (hO : Sched.HOut H H' lo hi A k w K) (hb : ∀ kd, K = some kd → 2 ^ kd.bits ≤ k) :
    ∀ q kd, H' q = some kd → H q = some kd ∨ (A ≤ q.val ∧ q.val + 2 ^ kd.bits ≤ A + w * k) := by
  intro q kd hq
  rw [hO q] at hq
  split_ifs at hq with h1 h2
  · obtain ⟨⟨j, hj, e⟩, -⟩ := h1
    have := hb kd hq
    have h2 := Nat.mul_le_mul_right k (show j + 1 ≤ w by omega)
    rw [Nat.succ_mul] at h2
    right; omega
  all_goals first | exact Or.inl hq | exact absurd hq (by simp)

/-- **The device facts across a retype from a RAM untyped cap** (jc2): the
device caps after are old ones, unchanged (the source is RAM, no new device
cap, `hcjD`); the new typed-heap and `H` objects lie in the window
`[A, A + w * k)` inside the source's range, which `DevSep` keeps off every
device range; the new RAM caps lie in the window too (`UtInv.reg` after). -/
theorem devRetypeR {th th' : TypedHeap} {H H' : P1.Heap} {G G' : MdbGhost} {Cs : Set U64} {s s' : S}
    {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hD : DevApart (L := L) th H G Cs s) (hS : DevSep G (L.mem s))
    (hE : RetExp th th' (L.mem s) (L.mem s') G G' A k w dslot cj xs) (hU' : UtInv (L.mem s') G')
    (hram : ∀ p sb fi d, capV (L.mem s) xs = .Untyped p sb fi d → d = false)
    (hcjD : ∀ j, j < w → ∀ p sb fi, cj j ≠ .Untyped p sb fi true)
    (hks : L.ksb s' = L.ksb s) (hI : IdleH (L := L) H' s')
    (hH : ∀ q kd, H' q = some kd → H q = some kd ∨ (A ≤ q.val ∧ q.val + 2 ^ kd.bits ≤ A + w * k)) :
    DevApart (L := L) th' H' G' Cs s' ∧ DevSep G' (L.mem s') := by
  obtain ⟨hxs, ps, sbs, fis, fis1, d0, hc0, hc1, hA1, -, hA2, -, hoth⟩ := hE.usrc
  obtain rfl : d0 = false := hram _ _ _ _ hc0
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  have win : ∀ y ∈ G.chains.flatten, ∀ p' sb' fi' : U64, capV (L.mem s) y = .Untyped p' sb' fi' true →
      A + w * k ≤ p'.val ∨ p'.val + 2 ^ sb'.val ≤ A := by
    intro y hy p' sb' fi' hc
    rcases hS xs hxs y hy _ _ _ _ _ _ hc0 hc with h | h
    · left; omega
    · right; omega
  have devOld : ∀ x ∈ G'.chains.flatten, ∀ p sb fi : U64, capV (L.mem s') x = .Untyped p sb fi true →
      x ∈ G.chains.flatten ∧ capV (L.mem s) x = .Untyped p sb fi true := by
    intro x hx p sb fi hc
    rcases hE.gmem x hx with hx0 | ⟨j, hj, rfl⟩
    · by_cases hu : isUt (capV (L.mem s) x) = true
      · by_cases e : x = xs
        · subst e; rw [hc1] at hc; cases hc
        · exact ⟨hx0, by rw [← hoth x hx0 hu e]; exact hc⟩
      · have e := (hE.keep x hx0 (by simpa using hu)).2
        rw [e] at hc; rw [hc] at hu; exact absurd (isUt_untyped _ _ _ _) hu
    · rw [hE.newc j hj] at hc; exact absurd hc (hcjD j hj p sb fi)
  have hjk : ∀ j, j < w → j * k + k ≤ w * k := fun j hj => by
    have := Nat.mul_le_mul_right k (show j + 1 ≤ w by omega)
    rwa [Nat.succ_mul] at this
  refine ⟨fun x hx p sb fi hc => ?_, fun x hx y hy p sb fi p' sb' fi' hcx hcy => ?_⟩
  · obtain ⟨hx0, hc0'⟩ := devOld x hx p sb fi hc
    obtain ⟨a1, a2, a3, a4, -, a6, a7, a8, a9⟩ := hD x hx0 p sb fi hc0'
    have hw := win x hx0 p sb fi hc0'
    have a7' : ∀ q kd, H' q = some kd → q.val + 2 ^ kd.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val ∨
        (p.val ≤ q.val ∧ q.val + 2 ^ kd.bits ≤ p.val + fi.val ∧ ∃ z, kd = .other z) := by
      intro q kd hq
      rcases hH q kd hq with h | ⟨h1, h2⟩
      · exact a7 q kd h
      · rcases hw with hw | hw
        · left; omega
        · right; left; omega
    refine ⟨a1, by rw [hks]; exact a2, fun c hc => by rw [hnb]; exact a3 c hc, by rw [hks]; exact a4,
      devApart_idle hI a7' a8, fun q kd hq => ?_, a7', a8, a9⟩
    rcases hE.th q kd hq with ⟨h, -⟩ | ⟨⟨j, hj, hqj, -⟩, hsz⟩
    · exact a6 q kd h
    · have := hjk j hj
      rcases hw with hw | hw
      · left; omega
      · right; omega
  · obtain ⟨hy0, hcy0⟩ := devOld y hy p' sb' fi' hcy
    rcases hE.gmem x hx with hx0 | ⟨j, hj, rfl⟩
    · by_cases hu : isUt (capV (L.mem s) x) = true
      · by_cases e : x = xs
        · subst e; rw [hc1] at hcx
          simp only [capability.Cap.Untyped.injEq] at hcx
          obtain ⟨rfl, rfl, -, -⟩ := hcx
          exact hS _ hx0 y hy0 _ _ _ _ _ _ hc0 hcy0
        · rw [hoth x hx0 hu e] at hcx
          exact hS x hx0 y hy0 _ _ _ _ _ _ hcx hcy0
      · have e := (hE.keep x hx0 (by simpa using hu)).2
        rw [e] at hcx; rw [hcx] at hu; exact absurd (isUt_untyped _ _ _ _) hu
    · have hph : physF (capV (L.mem s') (dslot j)) = true := by rw [hE.newc j hj]; exact hE.cphys j hj
      have hr := hU'.reg _ (hE.newm j hj) hph
      have hb := hE.cbase j hj
      have ht := hE.ctop j hj
      rw [← hE.newc j hj, hcx] at hb ht
      rw [hcx] at hr
      obtain ⟨e1, e2, -⟩ := ut_range (capV_ut_sb hcx) hr
      have := hjk j hj
      have h1 : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow
      have hk1 := hE.k1
      rcases win y hy0 p' sb' fi' hcy0 with hw | hw
      · left; omega
      · right; omega

/-- An untyped cap after a retype: an old one with the same region and flag,
or a new one in the window (jc2). -/
theorem retype_utOld {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost}
    {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hE : RetExp th th' m m' G G' A k w dslot cj xs) (hU' : UtInv m' G')
    {x p sb fi : U64} {d : Bool} (hx : x ∈ G'.chains.flatten) (hc : capV m' x = .Untyped p sb fi d) :
    (x ∈ G.chains.flatten ∧ ∃ fi0 : U64, capV m x = .Untyped p sb fi0 d) ∨
    (∃ j, j < w ∧ cj j = .Untyped p sb fi d ∧ A ≤ p.val ∧ p.val + 2 ^ sb.val ≤ A + w * k) := by
  obtain ⟨hxs, ps, sbs, fis, fis1, d0, hc0, hc1, -, -, -, -, hoth⟩ := hE.usrc
  rcases hE.gmem x hx with hx0 | ⟨j, hj, rfl⟩
  · left
    refine ⟨hx0, ?_⟩
    by_cases hu : isUt (capV m x) = true
    · by_cases e : x = xs
      · subst e; rw [hc1] at hc
        simp only [capability.Cap.Untyped.injEq] at hc
        obtain ⟨rfl, rfl, -, rfl⟩ := hc
        exact ⟨_, hc0⟩
      · exact ⟨fi, by rw [← hoth x hx0 hu e]; exact hc⟩
    · have e := (hE.keep x hx0 (by simpa using hu)).2
      rw [e] at hc; rw [hc] at hu; exact absurd (isUt_untyped _ _ _ _) hu
  · right
    have hph : physF (capV m' (dslot j)) = true := by rw [hE.newc j hj]; exact hE.cphys j hj
    have hr := hU'.reg _ (hE.newm j hj) hph
    have hb := hE.cbase j hj
    have ht := hE.ctop j hj
    have hcj := hE.newc j hj
    rw [hc] at hcj
    rw [← hcj] at hb ht
    rw [hc] at hr
    obtain ⟨e1, e2, -⟩ := ut_range (capV_ut_sb hc) hr
    have h2 := Nat.mul_le_mul_right k (show j + 1 ≤ w by omega)
    rw [Nat.succ_mul] at h2
    have h1 : 1 ≤ 2 ^ sb.val := Nat.one_le_two_pow
    have hk1 := hE.k1
    exact ⟨j, hj, hcj.symm, by omega, by omega⟩

/-- **`DevSep` across a retype from a device untyped cap** (jc2): the new
caps are no RAM untypeds (`hcjR`, DevJ's `SrcOK`), the new device caps lie in
the source's range, which `DevSep` keeps off every RAM range. -/
theorem devSep_retypeD {th th' : TypedHeap} {m m' : U64 → U64} {G G' : MdbGhost}
    {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hS : DevSep G m) (hE : RetExp th th' m m' G G' A k w dslot cj xs) (hU' : UtInv m' G')
    (hdev : ∀ p sb fi d, capV m xs = .Untyped p sb fi d → d = true)
    (hcjR : ∀ j, j < w → ∀ p sb fi, cj j ≠ .Untyped p sb fi false) : DevSep G' m' := by
  obtain ⟨hxs, ps, sbs, fis, fis1, d0, hc0, -, hA1, -, hA2, -, -⟩ := hE.usrc
  obtain rfl : d0 = true := hdev _ _ _ _ hc0
  intro x hx y hy p sb fi p' sb' fi' hcx hcy
  rcases retype_utOld hE hU' hx hcx with ⟨hx0, fx, ex⟩ | ⟨j, hj, e, -⟩
  · rcases retype_utOld hE hU' hy hcy with ⟨hy0, fy, ey⟩ | ⟨j, hj, -, h1, h2⟩
    · exact hS x hx0 y hy0 _ _ _ _ _ _ ex ey
    · rcases hS x hx0 xs hxs _ _ _ _ _ _ ex hc0 with h | h
      · left; omega
      · right; omega
  · exact absurd e (hcjR j hj p sb fi)

/-- **`DevApart` across a step adding `H` objects inside a range off every
device range** (MakePool's pool page; jc2), the rest as `DevApart.frame`. -/
theorem DevApart.frameH {th th' : TypedHeap} {H H' : P1.Heap} {G G' : MdbGhost} {Cs : Set U64} {s s' : S}
    {lo hi : Nat}
    (h : DevApart (L := L) th H G Cs s) (hth : ∀ q k, th' q = some k → th q = some k)
    (hH : ∀ q k, H' q = some k → H q = some k ∨ (lo ≤ q.val ∧ q.val + 2 ^ k.bits ≤ hi))
    (hsep : ∀ y ∈ G.chains.flatten, ∀ p sb fi : U64, capV (L.mem s) y = .Untyped p sb fi true →
      hi ≤ p.val ∨ p.val + 2 ^ sb.val ≤ lo)
    (hks : L.ksb s' = L.ksb s)
    (hD : DevFrom G G' (L.mem s) (L.mem s')) (hI : IdleH (L := L) H' s') :
    DevApart (L := L) th' H' G' Cs s' := by
  intro x hx p sb fi hc
  obtain ⟨y, hy, fi0, hle, hc0⟩ := hD x hx p sb fi hc
  obtain ⟨a1, a2, a3, a4, -, a6, a7, a8, a9⟩ := h y hy p sb fi0 hc0
  have hw := hsep y hy p sb fi0 hc0
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  have a7' : ∀ q kd, H' q = some kd → q.val + 2 ^ kd.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val ∨
      (p.val ≤ q.val ∧ q.val + 2 ^ kd.bits ≤ p.val + fi.val ∧ ∃ z, kd = .other z) := by
    intro q kd hq
    rcases hH q kd hq with hq | ⟨h1, h2⟩
    · rcases a7 q kd hq with e | e | ⟨e1, e2, e3⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr ⟨e1, by omega, e3⟩)
    · rcases hw with hw | hw
      · left; omega
      · right; left; omega
  exact ⟨a1, by rw [hks]; exact a2, fun c hc => by rw [hnb]; exact a3 c hc, by rw [hks]; exact a4,
    devApart_idle hI a7' a8, fun q k hq => a6 q k (hth q k hq), a7', a8, a9⟩

/-- `IdleH` across a step keeping the idle words and `H` at them. -/
theorem IdleH.keep {H H' : P1.Heap} {s s' : S} (h : IdleH (L := L) H s) (hidl : Sched.IdleKeep (L := L) s s')
    (hH : ∀ q, Sched.IdleAt (L := L) s' q → H' q = H q) : IdleH (L := L) H' s' := by
  refine ⟨?_, ?_⟩
  · rw [hH _ (Or.inl rfl), hidl.1]; exact h.1
  · rw [hH _ (Or.inr rfl), hidl.2]; exact h.2

/-- `IdleH` across the drop of a region's `H` objects, the idle objects
off the region. -/
theorem IdleH.drop {H : P1.Heap} {s : S} {lo hi : Nat} (h : IdleH (L := L) H s)
    (hoff : ∀ q, Sched.IdleAt (L := L) s q → ∀ k, H q = some k → q.val + 2 ^ k.bits ≤ lo ∨ hi ≤ q.val) :
    IdleH (L := L) (H.drop (P1.RegionD H lo hi)) s :=
  h.keep (Sched.IdleKeep.refl s) fun q hq => by
    cases hk : H q with
    | none =>
      refine Option.ext fun k => ?_
      rw [P1.Heap.drop_eq_some, hk]; simp
    | some k =>
      rw [P1.Heap.drop_of_not]
      · exact hk
      · unfold P1.RegionD P1.MeetsR
        rw [hk]; simp only [Option.elim, not_not]
        exact hoff q hq k hk

/-! ### jc3: `vsTyp` (C4) -/

/-- (jc3) Every spec arch object kept, of the same type (`IpcFrKeep.arch`). -/
def ArchFwd (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∀ p ao, σ.kheap p = some (.archObj ao) → ∃ ao', σ'.kheap p = some (.archObj ao') ∧
    Fl4Spec.aaType ao' = Fl4Spec.aaType ao

theorem ArchFwd.of_ipcFr {σ σ' : Fl4Spec.State Unit} (h : IpcFrKeep σ σ') : ArchFwd σ σ' := h.arch

theorem ArchFwd.of_eq {σ σ' : Fl4Spec.State Unit} (h : ∀ q ao, σ.kheap q = some (.archObj ao) →
    σ'.kheap q = some (.archObj ao)) : ArchFwd σ σ' := fun p ao hp => ⟨ao, h p ao hp, rfl⟩

/-- The spec type of a level-`k` table (`1` page table, `2` page directory, `3` PDPT). -/
def tabT : Nat → Fl4Spec.AAType
  | 1 => .aPageTable
  | 2 => .aPageDirectory
  | 3 => .aPDPointerTable
  | _ => .aPageMapL4

/-- A table of `tabT k` is a page (`2 ^ 12` bytes). -/
theorem objBits_tabT {ao : Fl4Spec.ArchKernelObj} {k : Nat} (h : Fl4Spec.aaType ao = tabT k) :
    Fl4Spec.objBits (.archObj ao) = 12 := by
  show Fl4Spec.archKobjSize ao = 12
  rw [archKobjSize_aaSize, h]
  unfold tabT; split <;> rfl

/-- The set of `Z` holding the level-`k` tables (`univ` at other levels). -/
def tabSet (Z : XSets) (k : Nat) : Set U64 :=
  if k = 1 then Z.L1 else if k = 2 then Z.L2 else if k = 3 then Z.L3 else Set.univ

theorem tabSet_mono {Z Z' : XSets} (h1 : Z.L1 ⊆ Z'.L1) (h2 : Z.L2 ⊆ Z'.L2) (h3 : Z.L3 ⊆ Z'.L3) (k : Nat) :
    tabSet Z k ⊆ tabSet Z' k := by
  unfold tabSet; split_ifs
  · exact h1
  · exact h2
  · exact h3
  · exact subset_rfl

/-- **A table frame off the fixed kernel areas and `Z.B`'s words** (jc3): no
byte of `[q, q + 4096)` in core `Z.c`'s node, in the kernel-state block's
`OObj` part, in the ASID-table area, or in a word of `Z.B`. -/
def OffK (Z : XSets) (s : S) (q : U64) : Prop :=
  ∀ b : U64, q.val ≤ b.val → b.val < q.val + 4096 →
    ¬ ((L.ksb s).val + 13568 + Z.c.val * 4288 ≤ b.val ∧ b.val < (L.ksb s).val + 13568 + Z.c.val * 4288 + 4288) ∧
    ¬ ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568 ∧
      (b.val < (L.ksb s).val + 1248 ∨ (L.ksb s).val + 5344 ≤ b.val)) ∧
    ¬ ((L.ksb s).val + 288000 ≤ b.val ∧ b.val < (L.ksb s).val + 288000 + 16384) ∧
    ∀ wp ∈ Z.B, ¬ (wp.1.val ≤ b.val ∧ b.val < wp.1.val + 8)

/-- **A level-`k` table named by a cap, when not in its set** (jc3): a spec
table of that level there, its frame `OffK`. -/
def OffR (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) (k : Nat) (q : U64) : Prop :=
  q ∉ tabSet Z k →
    (∃ ao, σ.kheap q.bv = some (.archObj ao) ∧ Fl4Spec.aaType ao = tabT k) ∧ OffK (L := L) Z s q

/-- **[C4, carried] Every slot's table cap's table off its set is a spec table
with its frame `OffK`** (l4v `valid_cap` typ_at, `pspace_distinct`; XTopJointVsOff's
`OffTabOK` follows at a `JAtZ` state, JCarryVsTyp's `JAtZ.offTabOK`). -/
def VsTyp (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  Vs.TabSlots Z.th (OffR (L := L) Z s σ) (L.mem s)

/-- The new words of `B'` miss every spec table's frame (`B` grown by a
frame retype: the new pages in the retype's window, apart from old objects). -/
def BNewOff (B B' : Set (U64 × Fl4Spec.Word)) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (k : Nat) (q : U64), (∃ ao, σ.kheap q.bv = some (.archObj ao) ∧ Fl4Spec.aaType ao = tabT k) →
    ∀ wp ∈ B', wp ∈ B ∨ ∀ b : U64, q.val ≤ b.val → b.val < q.val + 4096 → ¬ (wp.1.val ≤ b.val ∧ b.val < wp.1.val + 8)

theorem BNewOff.of_sub {B B' : Set (U64 × Fl4Spec.Word)} {σ : Fl4Spec.State Unit} (h : B' ⊆ B) :
    BNewOff B B' σ := fun _ _ _ _ hw => Or.inl (h hw)

theorem OffR.mono' {Z Z' : XSets} {s s' : S} {σ σ' : Fl4Spec.State Unit} {k : Nat} {q : U64}
    (h : OffR (L := L) Z s σ k q) (hL : tabSet Z k ⊆ tabSet Z' k) (hB : BNewOff Z.B Z'.B σ) (hc : Z'.c = Z.c)
    (hks : L.ksb s' = L.ksb s) (hA : ArchFwd σ σ') : OffR (L := L) Z' s' σ' k q := by
  intro hq
  obtain ⟨⟨ao, h1, h2⟩, hO⟩ := h fun h' => hq (hL h')
  obtain ⟨ao', h1', h2'⟩ := hA _ ao h1
  refine ⟨⟨ao', h1', h2'.trans h2⟩, fun b g1 g2 => ?_⟩
  rw [hks, hc]
  obtain ⟨a1, a2, a3, a4⟩ := hO b g1 g2
  refine ⟨a1, a2, a3, fun wp hw => ?_⟩
  rcases hB k q ⟨ao, h1, h2⟩ wp hw with hw | hw
  · exact a4 wp hw
  · exact hw b g1 g2

theorem OffR.mono {Z Z' : XSets} {s s' : S} {σ σ' : Fl4Spec.State Unit} {k : Nat} {q : U64}
    (h : OffR (L := L) Z s σ k q) (hL : tabSet Z k ⊆ tabSet Z' k) (hB : Z'.B ⊆ Z.B) (hc : Z'.c = Z.c)
    (hks : L.ksb s' = L.ksb s) (hA : ArchFwd σ σ') : OffR (L := L) Z' s' σ' k q :=
  h.mono' hL (BNewOff.of_sub hB) hc hks hA

/-- An unmapped table cap placed at `Z`'s sets (`VCapW`) names a table of its
set, so `OffR` holds of it vacuously. -/
theorem offR_of_un {Z : XSets} {s : S} {σ : Fl4Spec.State Unit} {c : capability.Cap}
    (hv : Vs.VCapW Z.P Z.L4 Z.L3 Z.L2 Z.L1 c) (hu : Vs.TabUn c) : Vs.TabR (OffR (L := L) Z s σ) c := by
  cases c with
  | PageTable q mp a v => exact fun hq => absurd (hv.1 hu) (by simpa [tabSet] using hq)
  | PageDirectory q mp a v => exact fun hq => absurd (hv.1 hu) (by simpa [tabSet] using hq)
  | Pdpt q mp a v => exact fun hq => absurd (hv.1 hu) (by simpa [tabSet] using hq)
  | _ => trivial

/-- A cap that is no mapped table cap (`TabUn` or no table cap). -/
def MapFree (c : capability.Cap) : Prop := Vs.TabUn c ∨ ∀ R, Vs.TabR R c

theorem mapFree_of_un {c : capability.Cap} (hv : MapFree c) {Z : XSets} {s : S} {σ : Fl4Spec.State Unit}
    (hvc : Vs.VCapW Z.P Z.L4 Z.L3 Z.L2 Z.L1 c) : Vs.TabR (OffR (L := L) Z s σ) c :=
  hv.elim (offR_of_un hvc) fun h => h _

/-- `VsTyp` across a step: the table caps step by `TabSlots` (`hT`, at every
`R`), the sets kept or grown, `B` kept or shrunk, the kernel-state base kept,
the spec's arch objects kept (`ArchFwd`). -/
theorem VsTyp.step {Z Z' : XSets} {s s' : S} {σ σ' : Fl4Spec.State Unit} (h : VsTyp (L := L) Z s σ)
    (hT : ∀ R, Vs.TabSlots Z.th R (L.mem s) → Vs.TabSlots Z'.th R (L.mem s'))
    (hL : ∀ k, tabSet Z k ⊆ tabSet Z' k) (hB : Z'.B ⊆ Z.B) (hc : Z'.c = Z.c)
    (hks : L.ksb s' = L.ksb s) (hA : ArchFwd σ σ') : VsTyp (L := L) Z' s' σ' := by
  intro y hy
  exact Vs.TabR.imp (fun k q h => h.mono (hL k) hB hc hks hA) (hT _ h y hy)

/-- The newer form at a slot step whose new caps are no mapped table caps
or placed at the sets after (`hvc`), the old ones kept (`hold`). -/
theorem VsTyp.stepN {Z Z' : XSets} {s s' : S} {σ σ' : Fl4Spec.State Unit} (h : VsTyp (L := L) Z s σ)
    (hvc : Vs.VsSlotsW Z'.th Z'.P Z'.L4 Z'.L3 Z'.L2 Z'.L1 (L.mem s'))
    (hold : ∀ y, IsSlot Z'.th y → MapFree (capV (L.mem s') y) ∨ ∃ y0, IsSlot Z.th y0 ∧ capV (L.mem s') y = capV (L.mem s) y0)
    (hL : ∀ k, tabSet Z k ⊆ tabSet Z' k) (hB : BNewOff Z.B Z'.B σ) (hc : Z'.c = Z.c)
    (hks : L.ksb s' = L.ksb s) (hA : ArchFwd σ σ') : VsTyp (L := L) Z' s' σ' := by
  intro y hy
  rcases hold y hy with hf | ⟨y0, hy0, e⟩
  · exact mapFree_of_un hf (hvc y hy)
  · rw [e]; exact Vs.TabR.imp (fun k q h => h.mono' (hL k) hB hc hks hA) (h y0 hy0)

/-- `VsTyp` across a step keeping the slots (`VsSlotsT`), the typed heap and the sets. -/
theorem VsTyp.frame {Z : XSets} {s s' : S} {σ σ' : Fl4Spec.State Unit} (h : VsTyp (L := L) Z s σ)
    (hT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s')) (hks : L.ksb s' = L.ksb s) (hA : ArchFwd σ σ') :
    VsTyp (L := L) Z s' σ' :=
  h.step (fun _ h => h.step hT) (tabSet_mono subset_rfl subset_rfl subset_rfl) subset_rfl rfl hks hA

/-- **The joint facts carried for the [J] leaves** (KENTRY-PLAN g7b-4; jc1b
step 1: `bufPg`, `archFit` = `JCarryS`; jc2 step 3: `devApart` (C25) with
`devSep`; jc3 step 4: `vsTyp` (C4)). -/
structure JCarry (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  /-- C21, C24 bufObj, in its carried form (`JCarry.bufObj`). -/
  bufPg : BufPgHyp Z.B σ
  /-- C16, C22, C24 heapH (first half). -/
  archFit : ArchFitHyp H σ
  /-- C25 (DevJ's `DevApart`). -/
  devApart : DevApart (L := L) Z.th H Z.G Cs s
  /-- RAM and device untyped ranges apart (what keeps `devApart` across a RAM retype). -/
  devSep : DevSep Z.G (L.mem s)
  /-- C4 (jc3): every table cap's table off its set a spec table, its frame `OffK`. -/
  vsTyp : VsTyp (L := L) Z s σ

theorem JCarry.toS {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (h : JCarry (L := L) Z H Cs s σ) : JCarryS Z.B H σ := ⟨h.bufPg, h.archFit⟩

theorem JCarryS.withD {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (h : JCarryS Z.B H σ) (hD : DevApart (L := L) Z.th H Z.G Cs s) (hS : DevSep Z.G (L.mem s))
    (hV : VsTyp (L := L) Z s σ) :
    JCarry (L := L) Z H Cs s σ := ⟨h.bufPg, h.archFit, hD, hS, hV⟩

theorem JCarryS.withP {Z : XSets} {B : Set (U64 × Fl4Spec.Word)} {th : TypedHeap} {G : MdbGhost} {H : P1.Heap}
    {Cs : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (h : JCarryS B H σ) (hD : DevApart (L := L) th H G Cs s ∧ DevSep G (L.mem s)) (hV : VsTyp (L := L) Z s σ)
    (hB : B = Z.B := by rfl) (hth : th = Z.th := by rfl) (hG : G = Z.G := by rfl) : JCarry (L := L) Z H Cs s σ := by
  subst hB hth hG; exact ⟨h.bufPg, h.archFit, hD.1, hD.2, hV⟩

theorem JCarry.bufObj {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (h : JCarry (L := L) Z H Cs s σ) : BufObjHyp Z.B σ := bufObj_of_pg h.bufPg

/-- **`vsTyp` across a step** at sets `Z'` with `Z`'s typed heap, the
VSpace table sets kept or grown, `B` kept or shrunk (`VsTyp.step`). -/
theorem JCarry.vsStep {Z Z' : XSets} {H : P1.Heap} {Cs : Set U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : JCarry (L := L) Z H Cs s σ) (hth : Z'.th = Z.th) (hT : Vs.VsSlotsT Z.th (L.mem s) (L.mem s'))
    (h1 : Z.L1 ⊆ Z'.L1) (h2 : Z.L2 ⊆ Z'.L2) (h3 : Z.L3 ⊆ Z'.L3) (hB : Z'.B ⊆ Z.B) (hc : Z'.c = Z.c)
    (hks : L.ksb s' = L.ksb s) (hA : ArchFwd σ σ') : VsTyp (L := L) Z' s' σ' :=
  h.vsTyp.step (fun R hR => by rw [hth]; exact hR.step hT) (tabSet_mono h1 h2 h3) hB hc hks hA

/-- `JCarry.vsStep` at the same sets (but the MDB ghost), the slots kept. -/
theorem JCarry.vsSame {Z Z' : XSets} {H : P1.Heap} {Cs : Set U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : JCarry (L := L) Z H Cs s σ) (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hks : L.ksb s' = L.ksb s)
    (hA : ArchFwd σ σ') (hth : Z'.th = Z.th := by rfl) (h1 : Z.L1 ⊆ Z'.L1 := by exact subset_rfl)
    (h2 : Z.L2 ⊆ Z'.L2 := by exact subset_rfl) (h3 : Z.L3 ⊆ Z'.L3 := by exact subset_rfl)
    (hB : Z'.B ⊆ Z.B := by exact subset_rfl) (hc : Z'.c = Z.c := by rfl) : VsTyp (L := L) Z' s' σ' :=
  h.vsStep hth (Vs.VsSlotsT.of_eq fun _ hy => hSS.capV hy) h1 h2 h3 hB hc hks hA

/-- The σ part across a frame step (`JCarryS.frame`). -/
theorem JCarry.frame {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {σ σ' : Fl4Spec.State Unit}
    {B' : Set (U64 × Fl4Spec.Word)} (h : JCarry (L := L) Z H Cs s σ) (hB : B' ⊆ Z.B) (hF : IpcFrKeep σ σ')
    (hk : KSz σ σ') : JCarryS B' H σ' :=
  h.toS.frame hB hF hk

/-- **The device facts across a step keeping the slots** (`SlotsSame` on the
MDB members, `th` and `H` kept or shrunk), `IdleH` after. -/
theorem JCarry.devSame {Z : XSets} {H H' : P1.Heap} {Cs : Set U64} {s s' : S} {σ : Fl4Spec.State Unit}
    {th' : TypedHeap} {G' : MdbGhost}
    (h : JCarry (L := L) Z H Cs s σ) (hth : ∀ q k, th' q = some k → Z.th q = some k)
    (hH : ∀ q k, H' q = some k → H q = some k) (hks : L.ksb s' = L.ksb s)
    (hG : ∀ x ∈ G'.chains.flatten, x ∈ Z.G.chains.flatten ∧ capV (L.mem s') x = capV (L.mem s) x)
    (hI : IdleH (L := L) H' s') :
    DevApart (L := L) th' H' G' Cs s' ∧ DevSep G' (L.mem s') := by
  have hD : DevFrom Z.G G' (L.mem s) (L.mem s') := fun x hx p sb fi hc =>
    ⟨x, (hG x hx).1, fi, le_rfl, by rw [← (hG x hx).2]; exact hc⟩
  refine ⟨h.devApart.frame hth hH hks hD hI, h.devSep.frame fun x hx p sb fi d hc => ⟨x, (hG x hx).1, fi, ?_⟩⟩
  rw [← (hG x hx).2]; exact hc

end

end

end Fl4Proofs.P3

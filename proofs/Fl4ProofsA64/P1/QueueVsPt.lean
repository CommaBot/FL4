/-
P1 (aarch64, gen 36): **VSpace writes over `JV` from a ghost page-table set `Pt`** (a64.md §39's design, first
part): the mapped-frame and VSpace-root finalisations as top-level deletion targets, over `JV`.

Source (objects.rs `finalise_cap_object`, 266–309; arch/aarch64/vspace.rs): a `Frame` cap with `mapped` and
`asid ≠ 0` runs `vspace::unmap_page` at **every** finality (vspace.rs:449–472: `unmap_root` → `lookup_pt_slot` →
one PTE write `s.write(lu.slot, 0)` + an `Arch` TLB invalidation); a final mapped `Pml4` (the A64 VSpace root)
runs `vspace::delete_asid` (vspace.rs:529–549: one ASID-pool entry `pool + 8·(asid & 511)` written 0, then
`set_vm_root`, which writes no word); a final mapped `HighVSpace` the same with the `ROOT_HIGH` tag. A device
frame's `retire_dma_frame` changes only the arch state; a Stage-2 (`is_ept`) frame runs `ept::unmap` (not
covered here).

* **`PtW Pt b`**: `b` is an aligned word of an object of the ghost set `Pt` (page tables and ASID pools, 4 KiB
  each). **`PtOK T Ω Sg OS Vc Pt`** (state-free placement): every `Pt` word is an aligned word of `Ω` off `Sg`
  (QueueVsFin's `VsOK`), lies in no `OS` slot and is no VCPU word.
* **`JV.ptw`**: writes of `Pt` words keep `JV`, every `OS` word (`OSKeep`), the idle word and every thread's `SC`
  field (`ScK`).
* `vspace.unmap_page.pt` (QueueVsFin's `unmap_page.vs` with its walk hypothesis restricted to the root
  `unmap_root` returns), `fin_frame.pt`, `fin_root.pt`, `fin_hvs.pt`; **`finJV_frameP`**, **`cdt.delete.frameP`**
  (a non-EPT frame, mapped or not, any finality), **`finJV_rootP`**, **`cdt.delete.rootP`** (a `Pml4` cap),
  **`finJV_hvsP`**, **`cdt.delete.hvsP`** (a `HighVSpace` cap).

Case hypotheses (facts of the deletion's start state, of the kind of QueueVsFin's `hpt` / `hpool`): the walk
from the frame's ASID root lands on a `Pt` word (`PtWalk`), every nonzero ASID-table entry names a pool whose
entry for the ASID is a `Pt` word (`PtPool`). **Not done** (a64.md §40): the typing `VsTy` that derives `PtWalk`
/ `PtPool` from a closure property of the `Pt` objects' contents and is kept along the Zombie loop — it needs a
write set (not only `JV` / `OSKeep`) of every finaliser of the loop, so the typical thread (mapped VSpace root and
IPC-buffer frame in its slots) is still uncovered. No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueZombieS
import Fl4ProofsA64.P1.QueueVsFin
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

/-- An aligned word of an object of the ghost page-table / ASID-pool set `Pt` (4 KiB objects). -/
def PtW (Pt : Set U64) (b : U64) : Prop := ∃ p ∈ Pt, ∃ o : U64, o.val < 4096 ∧ o.val % 8 = 0 ∧ b = wa p o

/-- **The walk from the ASID's root lands on a `Pt` word** (at a state). -/
def PtWalk (st : machine.Store S) [L : LawfulStore st] (Pt : Set U64) (s : S) (asid vaddr : U64) : Prop :=
  ∀ root high, vspace.unmap_root st s asid = ok (some (root, high)) →
    vspace.lookup_pt_slot st s root vaddr ⦃ lu => PtW Pt lu.slot ⦄

/-- **Every nonzero ASID-table entry names a pool whose entry for `asid` is a `Pt` word** (at a state). -/
def PtPool (st : machine.Store S) [L : LawfulStore st] (Pt : Set U64) (s : S) (asid : U64) : Prop :=
  ∀ i, vspace.asid_table st s i ⦃ pool => pool ≠ 0#u64 →
    PtW Pt (wa pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) ⦄

/-- **`unmap_page`** writes only the slot `lookup_pt_slot` finds from the root `unmap_root` returns. -/
theorem vspace.unmap_page.pt {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (size : capability.FrameSize) (asid vaddr pptr : U64) {Pt : Set U64} (hV : VsOK Ω Sg (PtW Pt))
    (hpt : PtWalk st Pt s asid vaddr) :
    vspace.unmap_page st ar s a size asid vaddr pptr ⦃ r => WritesIn st s r.1 (PtW Pt) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.unmap_page
  obtain ⟨o, ho⟩ := DPF.spec_tot (P0.vspace.unmap_root.p0 st s asid hS)
  rw [ho, bind_ok]
  rcases o with _ | ⟨root, high⟩
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  try dsimp only
  refine WP.spec_bind (hpt root high ho) fun lu hlu => ?_
  refine WP.spec_bind (P0.vspace.page_shift.p0 size) fun sh _ => ?_
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step with LawfulStore.read_spec as ⟨e, _⟩
  refine WP.spec_bind (P0.vspace.is_page.p0 e lu.shift) fun b _ => ?_
  split
  · refine WP.spec_bind (P0.vspace.page_base.p0 e lu.shift) fun pb _ => ?_
    refine WP.spec_bind (P0.layout.paddr.p0 pptr) fun pa _ => ?_
    split
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    step with LawfulStore.write_spec as ⟨s1, e1⟩
    split
    · refine WP.spec_bind (hA.invalidate_high_page a vaddr) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact writesIn_wr_V hV hlu
    · refine WP.spec_bind (hA.invalidate_page a asid vaddr) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact writesIn_wr_V hV hlu
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **A non-EPT, non-device frame's finalisation** (any finality) writes only `Pt` words. -/
theorem fin_frame.pt {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (ptr : U64) (size : capability.FrameSize) (rights : U64) (mapped : Bool) (asid vaddr : U64) (fin : Bool)
    {Pt : Set U64} (hV : VsOK Ω Sg (PtW Pt)) (hpt : PtWalk st Pt s asid vaddr) :
    objects.finalise_cap_object st ar s a (.Frame ptr size rights false mapped false asid vaddr) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ WritesIn st s r.2.1 (PtW Pt) ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  refine WP.spec_bind (Pₘ := fun r : S × A => WritesIn st s r.1 (PtW Pt)) ?_ ?_
  · split
    · split
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact vspace.unmap_page.pt hA s a size asid vaddr ptr hV hpt
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rintro ⟨s1, a1⟩ w1
  try dsimp only
  cases fin <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> exact (WP.spec_ok _).2 ⟨rfl, w1⟩

/-- **A VSpace-root (`Pml4`) cap's finalisation** writes only `Pt` words (`delete_asid`). -/
theorem fin_root.pt {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (ptr : U64) (mapped : Bool) (asid : U64) (fin : Bool) {Pt : Set U64} (hV : VsOK Ω Sg (PtW Pt))
    (hpool : PtPool st Pt s asid) :
    objects.finalise_cap_object st ar s a (.Pml4 ptr mapped asid) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ WritesIn st s r.2.1 (PtW Pt) ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · refine WP.spec_bind (vspace.delete_asid.vs hA s a asid ptr hV hpool) ?_
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, WritesIn.refl _ _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, WritesIn.refl _ _⟩

/-- **A `HighVSpace` cap's finalisation** writes only `Pt` words (`delete_asid` of the tagged root). -/
theorem fin_hvs.pt {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (ptr : U64) (mapped : Bool) (asid : U64) (fin : Bool) {Pt : Set U64} (hV : VsOK Ω Sg (PtW Pt))
    (hpool : PtPool st Pt s asid) :
    objects.finalise_cap_object st ar s a (.HighVSpace ptr mapped asid) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ WritesIn st s r.2.1 (PtW Pt) ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  · split
    · try simp only [lift, bind_ok]
      refine WP.spec_bind (vspace.delete_asid.vs hA s a asid _ hV hpool) ?_
      rintro ⟨s1, a1⟩ w1
      exact (WP.spec_ok _).2 ⟨rfl, w1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, WritesIn.refl _ _⟩
  · exact (WP.spec_ok _).2 ⟨rfl, WritesIn.refl _ _⟩

namespace W7
namespace R
namespace ST

section pt
variable {OS Vc Ub : Set U64}

/-- **Placement of the ghost page-table set** (state-free): `Pt` words are aligned words of `Ω` off `Sg`, in no
`OS` slot, no VCPU word. -/
structure PtOK (T Ω Sg OS Vc Pt : Set U64) : Prop where
  vs : VsOK Ω Sg (PtW Pt)
  os : ∀ b, PtW Pt b → ∀ y ∈ OS, ¬ (y.val ≤ b.val ∧ b.val < y.val + 32)
  vc : ∀ b, PtW Pt b → ¬ VcW Vc b

set_option maxHeartbeats 4000000 in
/-- **Writes of `Pt` words keep `JV`**, every `OS` word, the idle word and every thread's `SC` field. -/
theorem JV.ptw (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {Pt : Set U64} (hPt : PtOK T Ω Sg OS Vc Pt)
    {s0 s s' : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hw : WritesIn st s s' (PtW Pt)) :
    JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s' ∧ OSKeep st OS s s' ∧ L.idleW s' = L.idleW s ∧
      ScK st T s s' := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hT := q.tcbs
  have hN := q.nodes _ q.cur
  have hΩ : ∀ b, PtW Pt b → b ∈ Ω := fun b hb' => (hPt.vs b hb').2.1
  have kf : ∀ z ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → L.mem s' (wa z K) = L.mem s (wa z K) :=
    fun z hz K hK h8 => hw.mem_eq (field_aligned (hT z hz) hK h8) fun hp =>
      (out_ne_field (q.omega _ (hΩ _ hp)) hz (hT z hz) hK) rfl
  have c0 := h.1.1.1.capw hw fun b hb' => Or.inr ⟨(hPt.vs b hb').2.1, (hPt.vs b hb').2.2⟩
  have kst : StK st T s s' := fun z hz => by rw [stA_eq]; exact kf z hz _ (by simp) (by simp)
  have rv := h.1.1.2.keep kst (fun z hz => kf z hz 3672#u64 (by simp) (by simp))
  have k : OSKeep st OS s s' := fun y hy => by
    obtain ⟨v8, v16, v24⟩ := vals hO hy
    have m := fun (b : U64) (hal : Aligned b) (h1 : y.val ≤ b.val) (h2 : b.val < y.val + 32) =>
      hw.mem_eq hal fun hp => hPt.os _ hp y hy ⟨h1, h2⟩
    exact ⟨m _ (hO.al0 hy) le_rfl (by omega), m _ (hO.al hy (k := 8#u64) (by simp) (by simp)) (by omega) (by omega),
      m _ (hO.al hy (k := 16#u64) (by simp) (by simp)) (by omega) (by omega),
      m _ (hO.al hy (k := 24#u64) (by simp) (by simp)) (by omega) (by omega)⟩
  have vk : VKeep st T Vc s s' :=
    ⟨hw.1, fun b hb' => hw.mem_eq (h.2.w hb').1 (fun hp => hPt.vc _ hp hb'),
      fun t ht => kf t ht 3664#u64 (by simp) (by simp), fun t ht => kf t ht 3672#u64 (by simp) (by simp),
      fun t ht => Or.inl (k.cap (hV.bcov t ht))⟩
  refine ⟨⟨⟨⟨c0, rv⟩, h.1.2.keep k⟩, h.2.keep vk⟩, k, ?_, fun z hz => by rw [scA_eq]; exact kf z hz _ (by simp) (by simp)⟩
  unfold LawfulStore.idleW
  rw [hw.2.1, nodeAt_of_ksb hw.1]
  exact hw.mem_eq (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8])) fun hp =>
    out_ne_node (q.omega _ (hΩ _ hp)) q.cur hN (by rw [idle8]; omega) rfl

/-- **A non-EPT, non-device frame's finalisation over `JV`** (mapped or not, any finality), the walk from its ASID
root landing on `Pt` words. -/
theorem finJV_frameP (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {A : Type _} {ar : machine.Arch A}
    (hP : P0.ArchTotal ar) {Pt : Set U64} (hPt : PtOK T Ω Sg OS Vc Pt) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x ptr rights asid vaddr : U64}
    {size : capability.FrameSize} {mapped : Bool}
    (hc : obj.Slot.cap st x s = ok (.Frame ptr size rights false mapped false asid vaddr))
    (hpt : PtWalk st Pt s asid vaddr) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c fin hc'
  rw [hc] at hc'
  obtain rfl := okinj hc'
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (fin_frame.pt hP s a ptr size rights mapped asid vaddr fin hPt.vs hpt) fun r hr =>
    ⟨hr.1, (JV.ptw hO hV hPt h hr.2).1⟩

/-- **The exposed `cdt.delete` of a non-EPT, non-device frame slot of `OS` keeps `JV`.** -/
theorem cdt.delete.frameP {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {Pt : Set U64} (hPt : PtOK T Ω Sg OS Vc Pt) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x ptr rights asid vaddr : U64}
    {size : capability.FrameSize} {mapped : Bool} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.Frame ptr size rights false mapped false asid vaddr))
    (hpt : PtWalk st Pt s asid vaddr) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.finJV hO hV h hx (finJV_frameP hO hV hP hPt h hc hpt)

/-- **A VSpace-root (`Pml4`) cap's finalisation over `JV`** (mapped or not, any finality). -/
theorem finJV_rootP (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {A : Type _} {ar : machine.Arch A}
    (hP : P0.ArchTotal ar) {Pt : Set U64} (hPt : PtOK T Ω Sg OS Vc Pt) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x ptr asid : U64} {mapped : Bool}
    (hc : obj.Slot.cap st x s = ok (.Pml4 ptr mapped asid)) (hpool : PtPool st Pt s asid) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c fin hc'
  rw [hc] at hc'
  obtain rfl := okinj hc'
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (fin_root.pt hP s a ptr mapped asid fin hPt.vs hpool) fun r hr =>
    ⟨hr.1, (JV.ptw hO hV hPt h hr.2).1⟩

/-- **The exposed `cdt.delete` of a VSpace-root slot of `OS` keeps `JV`.** -/
theorem cdt.delete.rootP {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {Pt : Set U64} (hPt : PtOK T Ω Sg OS Vc Pt) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x ptr asid : U64} {mapped : Bool} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.Pml4 ptr mapped asid)) (hpool : PtPool st Pt s asid) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.finJV hO hV h hx (finJV_rootP hO hV hP hPt h hc hpool)

/-- **A `HighVSpace` cap's finalisation over `JV`.** -/
theorem finJV_hvsP (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {A : Type _} {ar : machine.Arch A}
    (hP : P0.ArchTotal ar) {Pt : Set U64} (hPt : PtOK T Ω Sg OS Vc Pt) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x ptr asid : U64} {mapped : Bool}
    (hc : obj.Slot.cap st x s = ok (.HighVSpace ptr mapped asid)) (hpool : PtPool st Pt s asid) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c fin hc'
  rw [hc] at hc'
  obtain rfl := okinj hc'
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (fin_hvs.pt hP s a ptr mapped asid fin hPt.vs hpool) fun r hr =>
    ⟨hr.1, (JV.ptw hO hV hPt h hr.2).1⟩

/-- **The exposed `cdt.delete` of a `HighVSpace` slot of `OS` keeps `JV`.** -/
theorem cdt.delete.hvsP {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {Pt : Set U64} (hPt : PtOK T Ω Sg OS Vc Pt) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x ptr asid : U64} {mapped : Bool} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.HighVSpace ptr mapped asid)) (hpool : PtPool st Pt s asid) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.finJV hO hV h hx (finJV_hvsP hO hV hP hPt h hc hpool)

end pt

end ST
end R
end W7

end

end Fl4ProofsA64.P1

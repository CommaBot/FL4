-- AArch64 port of Fl4Proofs.P1.QueueVsFin (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1's side of the rest of the P3 CSpace side's `FinWorkHyp`.

* VSpace finalisations (`unmap_page_table`, `unmap_page`, `delete_asid`,
  `delete_asid_pool`, and `set_vm_root`, which writes no word): they write
  only page-table and ASID-pool/table words, given as a set `V` of aligned
  words of `Ω` outside `Sg` (`VsOK`); `blk_of_vs` then keeps `BlkOK` with
  the `CaiFr` frame, every TCB field from offset 192, every node word and
  every `Sg` word (so P1's invariant is untouched).

a64 (AArch64 rework; the unmap / ASID-delete lemmas are new proofs over the AArch64 code, the rest is the x86_64
text):
* AArch64 roots carry a tag (`root &&& ROOT_TAG`): a Stage-2 root (`ROOT_S2`) is unmapped by `ept.unmap_table`
  and invalidated by VMID, a TTBR1 high VSpace (`ROOT_HIGH`) is invalidated by `invalidate_high_vspace` /
  `invalidate_high_page`, a TTBR0 root by ASID. Every Arch call returns only the arch state, so the tags do not
  change the written words.
* `vspace.unmap_page_table.vs`: the walk (`unmap_page_table_loop`, or the Stage-2 `ept.unmap_table_loop`) finds
  at most one slot, which is written; the caller hypotheses `hlk` / `hel` say a found slot is a `V` word (as
  x86_64's `hlk` for `lookup_pd_slot`). `vspace.unmap_page.vs`: `lookup_pt_slot`'s slot (`hpt`).
  `ept.unmap_table.vs` is the Stage-2 half.
* `delete_asid_pool_loop` returns only the arch state on AArch64 (it reads the pool, invalidates per entry), so
  x86_64's `delete_asid_pool_loop.same` / `ept.invalidate.same` are not needed; `delete_asid_pool.vs` uses its
  P0 totality.
* `set_vm_root` / `set_kernel_vm_root` write no word: from `QueueSwitch.set_vm_root_same` and the AArch64
  `set_kernel_vm_root` (kernel root read, `set_high_vspace`, `set_vspace`).

No named premises. `hlk`, `hel`, `hpt`, `hpool`, `hset`, `hcap`, `hes` are caller hypotheses of the same kind
as x86_64's (facts of the state at the call that P3's `FinWorkHyp` supplies).
* `deleting_irq_handler`: the IRQ slot's cap (null or a notification cap)
  is finalised with `fin_ntfn.blk`, writing no cap-slot word; then the slot
  is emptied (`hes`, the slot frame, as in `cdt.delete.ep`).
-/
import Fl4ProofsA64.P1.QueueFinCap
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- The VSpace words: aligned words of the other objects, outside `Sg`. -/
def VsOK (Ω Sg : Set U64) (V : U64 → Prop) : Prop := ∀ b, V b → Aligned b ∧ b ∈ Ω ∧ b ∉ Sg

/-- **Writes to VSpace words leave P1's invariant untouched.** -/
theorem blk_of_vs {s s' : S} {V : U64 → Prop} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hV : VsOK Ω Sg V)
    (hw : WritesIn st s s' V) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ CaiFr st T Scs 0#u64 s s' ∧ L.actionW s' = L.actionW s ∧
      L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, 192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ∧
      (∀ b ∈ Sg, L.mem s' b = L.mem s b) := by
  have hB : ∀ b, V b → CapW T Ω Sg b := fun b hb => Or.inr ⟨(hV b hb).2.1, (hV b hb).2.2⟩
  obtain ⟨h', -, ec, ecs, ea, fld, nod, sig⟩ := blk_of_capw h hw hB
  exact ⟨h', CaiFr.of_capw h hw hB, ea, ec, ecs, fld, nod, sig⟩

theorem writesIn_wr_V {s : S} {V : U64 → Prop} {x v : U64} (hV : VsOK Ω Sg V) (hx : V x) :
    WritesIn st s (L.wr s x v) V :=
  (writesIn_wr (hV x hx).1).mono fun b e => by rw [e]; exact hx

/-- `set_kernel_vm_root` writes no word. a64: AArch64's also clears the TTBR1 high VSpace (`set_high_vspace`). -/
theorem vspace.set_kernel_vm_root.same {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) :
    vspace.set_kernel_vm_root st ar s a ⦃ r => r.1 = s ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.set_kernel_vm_root
  refine WP.spec_bind (P0.vspace.kernel_root.p0 st s hS) fun k _ => ?_
  refine WP.spec_bind (hA.set_high_vspace a 0#u64 0#u64) fun a1 _ => ?_
  exact WP.spec_bind (hA.set_vspace a1 k 0#u64) fun a2 _ => (WP.spec_ok _).2 rfl

/-- `set_vm_root` writes no word (a64: from `set_vm_root_same`, `QueueSwitch`). -/
theorem vspace.set_vm_root.same {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) : vspace.set_vm_root st ar s a t ⦃ r => r.1 = s ⦄ :=
  WP.spec_mono (set_vm_root_same hA s a t) fun r e => by
    obtain ⟨s', a'⟩ := r
    simpa only [WP.uncurry'_pair] using e

/-- a64: **the Stage-2 `unmap_table`** writes only the slot its walk finds (`hel`). -/
theorem ept.unmap_table.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (asid ipa pt : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hel : ∀ table shift mask rem, ept.unmap_table_loop st s ipa pt table shift mask rem ⦃ r => ∀ x, r = some x → V x ⦄) :
    ept.unmap_table st ar s a asid ipa pt ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ept.unmap_table
  refine WP.spec_bind (P0.ept.find.p0 st s asid hS) fun r _ => ?_
  rcases r with r1 | e
  · refine WP.spec_bind (hA.s2_ipa_bits a) fun ib _ => ?_
    refine WP.spec_bind (P0.ept.geom.p0 ib) fun g _ => ?_
    simp only [lift, bind_ok]
    refine WP.spec_bind (hel _ _ _ _) fun f hf => ?_
    rcases f with _ | slot
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · have hx := hf slot rfl
      step with LawfulStore.write_spec as ⟨s1, e1⟩
      refine WP.spec_bind (hA.invalidate_stage2_vmid a asid) fun a1 _ => ?_
      rw [WP.spec_ok, e1]; exact writesIn_wr_V hV hx
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`unmap_page_table`** writes only the slot its walk finds. a64: the TTBR0 / TTBR1 walk
(`unmap_page_table_loop`, `hlk`), or the Stage-2 walk (`ept.unmap_table`, `hel`) for a `ROOT_S2` root. -/
theorem vspace.unmap_page_table.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (asid vaddr pt : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hlk : ∀ table shift level, vspace.unmap_page_table_loop st s vaddr pt table shift level ⦃ r =>
      ∀ x, r = some x → V x ⦄)
    (hel : ∀ table shift mask rem, ept.unmap_table_loop st s vaddr pt table shift mask rem ⦃ r =>
      ∀ x, r = some x → V x ⦄) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.unmap_page_table
  refine WP.spec_bind (P0.vspace.find_asid_raw.p0 st s asid hS) fun r _ => ?_
  rcases r with r1 | e
  · simp only [lift, bind_ok]
    by_cases h2 : (r1 &&& vspace.ROOT_TAG) = vspace.ROOT_S2
    · rw [if_pos h2]; exact ept.unmap_table.vs hA s a asid vaddr pt hV hel
    rw [if_neg h2]
    refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun x _ => ?_
    · split
      · step*
      · exact (WP.spec_ok _).2 trivial
    obtain ⟨table, shift, level⟩ := x
    try dsimp only
    refine WP.spec_bind (hlk table shift level) fun f hf => ?_
    rcases f with _ | slot
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · have hx := hf slot rfl
      try dsimp only
      step with LawfulStore.write_spec as ⟨s1, e1⟩
      split
      · refine WP.spec_bind (hA.invalidate_high_vspace a _) fun a1 _ => ?_
        rw [WP.spec_ok, e1]; exact writesIn_wr_V hV hx
      · refine WP.spec_bind (hA.invalidate_asid a asid) fun a1 _ => ?_
        rw [WP.spec_ok, e1]; exact writesIn_wr_V hV hx
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`unmap_page`** writes only the slot `lookup_pt_slot` finds (`hpt`). a64: AArch64 has one walk for every
frame size (`lookup_pt_slot`, the size checked against the slot's shift). -/
theorem vspace.unmap_page.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (size : capability.FrameSize) (asid vaddr pptr : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hpt : ∀ root, vspace.lookup_pt_slot st s root vaddr ⦃ lu => V lu.slot ⦄) :
    vspace.unmap_page st ar s a size asid vaddr pptr ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.unmap_page
  refine WP.spec_bind (P0.vspace.unmap_root.p0 st s asid hS) fun o _ => ?_
  rcases o with _ | ⟨root, high⟩
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  try dsimp only
  refine WP.spec_bind (hpt root) fun lu hlu => ?_
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

/-- **`delete_asid`** writes only the ASID-pool entry. a64: the invalidation is by VMID, high VSpace or ASID
(`ROOT_TAG`), each changing only the arch state. -/
theorem vspace.delete_asid.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (asid root : U64) {V : U64 → Prop} (hV : VsOK Ω Sg V)
    (hpool : ∀ i, vspace.asid_table st s i ⦃ pool => pool ≠ 0#u64 →
      V (core.num.U64.wrapping_add pool (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) ⦄) :
    vspace.delete_asid st ar s a asid root ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.delete_asid
  step as ⟨i, _⟩
  refine WP.spec_bind (hpool i) fun pool hp => ?_
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rename_i hp0
  have he := hp hp0
  simp only [lift, bind_ok]
  step with LawfulStore.read_spec as ⟨v, _⟩
  split
  · refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun a1 _ => ?_
    · split
      · exact hA.invalidate_stage2_vmid a asid
      · split
        · exact hA.invalidate_high_vspace a _
        · exact hA.invalidate_asid a asid
    step with LawfulStore.write_spec as ⟨s1, e1⟩
    step with sched.cur_thread.spec as ⟨ct, _⟩
    refine WP.spec_mono (vspace.set_vm_root.same hA s1 a1 ct) fun r e => ?_
    rw [e, e1]; exact writesIn_wr_V hV he
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`delete_asid_pool`** writes only the ASID-table entry. a64: its loop returns only the arch state. -/
theorem vspace.delete_asid_pool.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (base pool : U64) {V : U64 → Prop}
    (hset : ∀ hi, vspace.set_asid_table st s hi 0#u64 ⦃ s1 => WritesIn st s s1 V ⦄) :
    vspace.delete_asid_pool st ar s a base pool ⦃ r => WritesIn st s r.1 V ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.delete_asid_pool
  step as ⟨i, _⟩
  refine WP.spec_bind (P0.vspace.asid_table.p0 st s i hS) fun p1 _ => ?_
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  refine WP.spec_bind (P0.vspace.delete_asid_pool_loop.p0 st ar s a base pool 0#u64 hS hA) fun a1 _ => ?_
  step as ⟨i2, _⟩
  refine WP.spec_bind (hset i2) fun s1 w1 => ?_
  step with sched.cur_thread.spec as ⟨ct, _⟩
  exact WP.spec_mono (vspace.set_vm_root.same hA s1 a1 ct) fun r e => by rw [e]; exact w1

/-- **`deleting_irq_handler`**: the IRQ slot holds a null or notification
cap; finalising it (`fin_ntfn.blk`) keeps `BlkOK` and writes no cap-slot
word, and the slot is then emptied (`hes`: `empty_slot` writes only cap-slot
words, from a state agreeing with `s` on them, with any fact `P` of its
result). -/
theorem interrupt.deleting_irq_handler.blk {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (irq isl : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hisl : interrupt.irq_slot st s irq = ok isl)
    (hcap : obj.Slot.cap st isl s ⦃ c => c = .Null ∨
      ∃ n b0 b1 b2, c = .Notification n b0 b1 b2 ∧ n ∈ Nt ∧ H n = some .ntfn ⦄)
    {P : S × A → Prop}
    (hes : ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 isl .Null ⦃ r => WritesIn st s1 r.1 (CapW T Ω Sg) ∧ P r ⦄) :
    interrupt.deleting_irq_handler st ar s a irq ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ (r = (s, a) ∨ P r) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold interrupt.deleting_irq_handler
  rw [hisl]
  simp only [bind_ok]
  unfold cdt.delete_one
  refine WP.spec_bind hcap fun c hc => ?_
  rcases hc with rfl | ⟨n, b0, b1, b2, rfl, hn, hH⟩
  · simp only [capability.Cap.is_null, bind_ok, ite_true, WP.spec_ok]
    exact ⟨h, by first | exact Or.inl rfl | exact Or.inl trivial | trivial⟩
  · simp only [capability.Cap.is_null, bind_ok, Bool.false_eq_true, ite_false]
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s isl
      (.Notification n b0 b1 b2) hS) fun fin _ => ?_
    have hm : ({n} : Set U64) ⊆ EH H := fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact Or.inr hH
    refine WP.spec_bind (fin_ntfn.blk (ar := ar) s a n b0 b1 b2 fin h hn hH) ?_
    rintro ⟨rr, s1, a1⟩ ⟨-, -, h1, f1⟩
    simp only [uncurry_apply_pair, WP.uncurry'_pair]
    exact WP.spec_mono (hes s1 a1 (foot_keeps_capw h (f1.mono hm))) fun r ⟨w, hP⟩ =>
      ⟨(blk_of_capw h1 w fun b hb => hb).1, Or.inr hP⟩

end

end Fl4ProofsA64.P1

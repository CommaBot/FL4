/-
P3x for virtualization (line virt, gen 25, item 2): **FL4's `is_final = true` for a `Vcpu` cap, and the final
delete leaves no cap to the VCPU** (under `VcpuChunked`, P3/VirtVChunk).

* **`srB_vcpu_self`** / `soB_vcpu_self`: `same_region_as (Vcpu v) (Vcpu v) = true` for **every** `v` — FL4's
  `same_region_as` compares VCPU caps by pointer (objects.rs l. 123: `Cap::Vcpu { ptr } => matches!(b, Cap::Vcpu
  { ptr: p } if p == ptr)`; extracted `objects.same_region_as`, `Vcpu` arm `if p = ptr then ok true`). Gen 24's
  side note (a region test that could fail for a wrapping 2^15 region) is not so: no placement hypothesis is needed.
* **`isFinal_vcpu_true`**: `is_final_capability_with_cap slot (Vcpu v) = true` (cdt.rs l. 163-175) gives
  `vcpu_alone`'s neighbour conditions (`prev` null or not `Vcpu v`, `next` null or not `Vcpu v`).
* **`delete_vcpu_final_alone`**: `cdt.delete` (either `exposed`) on a slot holding `Vcpu v`: `Ok`, and when the cap
  was final, **no slot of the typed heap holds `Vcpu v` afterwards** — `vcpu_alone` at the entry (the other slots'
  caps are kept by `vcpu.finalise`, VirtVCappedDel's `finW_nSl`, and by `empty_slot`, which nulls the slot). This is
  the `Vcpu` half of `JExtV.shrink`'s `hc`.

**Found (not provable as asked): `JExtV` is not kept across a final `Vcpu` delete.** `JExtV.cap` asks of an IO-port
cap `IoPort f l o` that `o ≠ 0 → o ∈ V`, but FL4 leaves IO-port caps naming a deleted VCPU in place: `vcpu::finalise`
(vcpu.rs l. 737-753) only stalls, releases, detaches and unlinks; `X86VCPUEnableIOPort` (vcpu.rs l. 1020-1052) writes
`vcpu: v` into the IO-port cap and validates a stale owner by list membership only ("before touching an object that
may have been deleted"), as does `revoke_ports` (l. 767-782). Counterexample shape (reachable): retype a VCPU `v`
(one `Vcpu v` cap), issue an IO-port cap from `IoPortControl` (`vcpu: 0`, ioport.rs l. 102), `EnableIOPort` on `v`
with it (now `IoPort f l v`), delete the `Vcpu v` cap (final: `vcpu::finalise` unlinks `v`, `V' = V \ {v}`); the
IO-port cap still names `v ∉ V'`, so `JExtV V' X` fails at its slot. What `JExtV` needs instead is an IO-port clause
that allows stale owners (e.g. `o ≠ 0 → o ∈ V ∨ o` unlisted), a change of the existing `JExtV` statement (mmuAD's
`JExtV`), which this line does not make.

No [J]/[P]/[W] premise is added. Used unchanged: `hns` [J] / `hnd` [J] / `hhv` [J] / `hhc` [J] (as
`delete_vcpu_vcapped`: `vcpu_finalise_vlW`'s and `finW_nSl`'s); `VcpuChunked` is a state hypothesis (gen 24: to be a
[J] carried field). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtVChunk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVFinal
open fl4_core Classical Fl4Proofs.P3 Fl4Proofs.P3.VirtVCapped Fl4Proofs.P3.VirtVCappedDel Fl4Proofs.P3.VirtVChunk

noncomputable section

/-- **`same_region_as (Vcpu v) (Vcpu v)` for every `v`** (objects.rs l. 123). -/
theorem srB_vcpu_self (v : U64) : srB (.Vcpu v) (.Vcpu v) = true :=
  srB_of_eq (by simp [objects.same_region_as])

theorem soB_vcpu_self (v : U64) : soB (.Vcpu v) (.Vcpu v) = true := by
  rw [soB_vcpu_eq]; exact srB_vcpu_self v

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **A final `Vcpu v` cap has no MDB neighbour holding `Vcpu v`** (cdt.rs l. 163-175). -/
theorem isFinal_vcpu_true {s : S} {slot v : U64}
    (h : cdt.is_final_capability_with_cap st s slot (.Vcpu v) = ok true) :
    (prevOf (L.mem s) slot = 0#u64 ∨ capV (L.mem s) (prevOf (L.mem s) slot) ≠ .Vcpu v) ∧
    (nextOf (L.mem s) slot = 0#u64 ∨ capV (L.mem s) (nextOf (L.mem s) slot) ≠ .Vcpu v) := by
  unfold cdt.is_final_capability_with_cap at h
  simp only [slot_prev_eq, slot_next_eq, is_null_eq, slot_cap_eq, capAt_capV, soB_eq, bind_ok] at h
  have hs := soB_vcpu_self v
  refine ⟨?_, ?_⟩
  · by_cases hp : prevOf (L.mem s) slot = 0#u64
    · exact Or.inl hp
    · refine Or.inr fun hc => ?_
      simp [hp, hc, hs] at h
  · by_cases hn : nextOf (L.mem s) slot = 0#u64
    · exact Or.inl hn
    · refine Or.inr fun hc => ?_
      by_cases hp : prevOf (L.mem s) slot = 0#u64
      · simp [hp, hn, hc, hs] at h
      · cases ha : soB (capV (L.mem s) (prevOf (L.mem s) slot)) (.Vcpu v)
        · simp [hp, hn, hc, hs, ha] at h
        · simp [hp, ha] at h

variable {V X U : Set U64} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **The final delete of a `Vcpu v` cap leaves no cap to `v`** (module docstring). -/
theorem delete_vcpu_final_alone (hA : P0.ArchTotal arI) (Ly : JVLay V th U) {s : S}
    (Da : DetAtB st V th (fun _ => U) s) (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s)
    (Vl : VList st V th s)
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val)
    (hhv : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhc : ¬ CW st V th (fun _ => U) s (P1.vHeadA st s))
    (hns : ∀ b, (b = ipiA st s ∨ b = actA st s ∨ b = P1.vHeadA st s) → ¬ SlR th b)
    {G : MdbGhost} (hM : MdbLinks th (L.mem s) G) (hK : VcpuChunked G (L.mem s))
    {a : A} {slot v : U64} {exposed : Bool} (hx : IsSlot th slot) (hc : capAt (L.mem s) slot = ok (.Vcpu v))
    {y : core.result.Result Unit error.Exc × S × A} (h : cdt.delete st arI s a slot exposed = ok y) :
    y.1 = .Ok () ∧ ∃ fin, cdt.is_final_capability_with_cap st s slot (.Vcpu v) = ok fin ∧
      (fin = true → ∀ y0, IsSlot th y0 → capV (L.mem y.2.1) y0 ≠ .Vcpu v) := by
  have hP := Ly.pl
  obtain ⟨hy1, fin, s1, a1, hfin, -, hf1, he⟩ := delete_vcpu_ok arI hc h
  refine ⟨hy1, fin, hfin, fun hft => ?_⟩
  subst hft
  have hcv : capV (L.mem s) slot = .Vcpu v := capV_of_capAt hc
  have hxm : slot ∈ G.chains.flatten := (hM.members slot).2 ⟨hx, _, hc, vcpu_ne_null v⟩
  obtain ⟨hpn, hnn⟩ := isFinal_vcpu_true hfin
  have halone := vcpu_alone hP hM hK hxm hcv hpn hnn
  have hvV : v ∈ V := by have := E.cap slot hx; rw [hcv] at this; exact this
  obtain ⟨-, -, -, -, hw⟩ := P1.spec_at (vcpu_finalise_vlW hA Ly Da E R Vl hnd hhv hhc a hvV) (hf1 rfl)
  have hSS := slotsSame_of_writes hP hw (finW_nSl Ly hns)
  have hc1 : capAt (L.mem s1) slot = ok (.Vcpu v) := by rw [hSS.capAt hx]; exact hc
  have hM1 : MdbLinks th (L.mem s1) G := hM.of_same hSS
  have hpv : prevOf (L.mem s1) slot = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s1) slot) ∧ prevOf (L.mem s1) slot ≠ slot) := by
    by_cases hp : prevOf (L.mem s1) slot = 0#u64
    · exact Or.inl hp
    · exact Or.inr (mdb_prev_slot hP hM1 hxm hx hp)
  have hnx : nextOf (L.mem s1) slot = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s1) slot) ∧ nextOf (L.mem s1) slot ≠ slot) := by
    by_cases hn : nextOf (L.mem s1) slot = 0#u64
    · exact Or.inl hn
    · exact Or.inr (mdb_next_slot hM1 hxm hn)
  have hPN : prevOf (L.mem s1) slot ≠ 0#u64 → nextOf (L.mem s1) slot ≠ 0#u64 →
      prevOf (L.mem s1) slot ≠ nextOf (L.mem s1) slot := fun h1 h2 => hM1.prev_ne_next hP hxm h1 h2
  have hEW := (P1.spec_at (empty_slot_mem (ar := arI) hP s1 a1 slot hx _ hc1 (vcpu_ne_null v) hpv hnx hPN) he).1
  intro y0 hy0 hcy
  have e0 := hEW y0 hy0 0#u64 off0
  have e8 := hEW y0 hy0 8#u64 off8
  rw [wordOf_zero] at e0
  by_cases hne : y0 = slot
  · rw [if_pos hne] at e0 e8
    have hz : capV (L.mem y.2.1) y0 = .Null := by unfold capV; rw [e0, e8]; rfl
    rw [hz] at hcy
    cases hcy
  · simp [hne] at e0 e8
    rw [capV_of_words e0 e8, hSS.capV hy0] at hcy
    have hy0m : y0 ∈ G.chains.flatten := (hM.members y0).2 ⟨hy0, _, by rw [capAt_capV, hcy], vcpu_ne_null v⟩
    exact hne (halone y0 hy0m hcy)

end

end
end Fl4Proofs.P3.VirtVFinal

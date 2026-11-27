/-
P3x for virtualization (line virt, gen 22, item 3): **`untyped::reset_untyped` and the VCPU relation**.

Gen 21 found that the reset's footprint (UntypedFrame `ResetW p sb x PW`: the whole untyped region `[p, p + 2^sb)`,
the source slot's two cap words, the preemption points' `PW`) is too coarse for `VRelAll V`: a VCPU object lying in
the region is zeroed, and the spec's `delete_objects` (`detype`) removes it.

* `VOut V lo hi`: the VCPUs of `V` whose objects miss `[lo, hi)`.
* **`offV_resetW`**: every aligned `ResetW` word is off every VCPU of `VOut V p (p + 2^sb)` (the region by
  `VOut`, the slot's words by `hxV`, the preemption points' words by `hPW`).
* **`VRelAll.of_reset`**: the reset's `WFrame` and the spec's VCPUs kept outside the region give
  **`VRelAll (VOut V p (p + 2^sb))`** at the reset's state; `vcpuAt_detype` (`detype R` keeps `vcpuAt` off `R`).
* **The region is VCPU-free on reachable states** (`vcpu_out_of_reset`, then `VOut_eq`: `VOut V … = V`, so the
  bridge gives `VRelAll V` itself). FL4 resets only when `cdt::ensure_no_children` succeeds (untyped.rs l. 57, 116),
  i.e. the untyped cap `x` has no MDB descendant. From that and:
  - **`VCapped V mem G`**: every VCPU of `V` has a `Vcpu` cap in some slot of the MDB. On reachable states this is
    the invariant "a listed VCPU has a cap": the retype that lists it inserts its cap (`create_new_objects_vcpu_jext`:
    `LoopInv`'s `F2a`), copies keep a cap, and when the **last** cap is deleted `finalise_cap` runs
    `vcpu::finalise` (objects.rs l. 265, `if fin`), which unlinks it from the VCPU list (vcpu.rs l. 737-753), so it
    leaves `V` (= the list's members, `VList`). Deleted VCPUs' objects therefore stay in the region but are not in `V`.
  - UntypedUtInv's `UtInv.drange` (l4v `untyped_children_in_mdb`): a physical cap meeting the untyped's range is its
    descendant or its ancestor; `UtInv.reg` (the untyped's range does not wrap);
  - `MdbInv.desc` (a descendant's ancestor is its MDB parent, `isPM`): a `Vcpu` cap is never an untyped cap's MDB
    parent (`same_region_as (Vcpu, Untyped) = false`, `srB_vcpu_left`);
  every VCPU of `V` lies outside `[p, p + 2^sb)`.
  `VCapped` is stated here as a hypothesis of `vcpu_out_of_reset` (a state fact, the invariant above); it is not yet
  carried by any joint bundle of this line — it belongs to the VM-epoch bundle (mmuAD's `JAtZV3`), kept by the
  steps that create, copy and delete caps.

No [J]/[P]/[W] premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtLoopSharp
import Fl4Proofs.P3.VirtVBridge
import Fl4Proofs.P3.UntypedFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtResetV
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtVKeep
open Fl4Proofs.P3.VirtVBridge Fl4Proofs.P3.VirtLoopFrame

noncomputable section

/-- The VCPUs of `V` whose objects miss `[lo, hi)`. -/
def VOut (V : Set U64) (lo hi : Nat) : Set U64 := {v | v ∈ V ∧ (v.val + 32768 ≤ lo ∨ hi ≤ v.val)}

theorem VOut_sub (V : Set U64) (lo hi : Nat) : VOut V lo hi ⊆ V := by
  intro v hv; exact hv.1

theorem VOut_eq {V : Set U64} {lo hi : Nat} (h : ∀ v ∈ V, v.val + 32768 ≤ lo ∨ hi ≤ v.val) : VOut V lo hi = V := by
  ext v; exact ⟨fun hv => hv.1, fun hv => ⟨hv, h v hv⟩⟩

/-- **The reset's words are off the VCPUs outside its region** (module docstring). -/
theorem offV_resetW {V : Set U64} {p sb x : U64} {PW : U64 → Prop} (hp8 : p.val % 8 = 0) (hsb3 : 3 ≤ sb.val)
    (hx8 : x.val % 8 = 0) (hxV : ∀ v ∈ V, x.val + 16 ≤ v.val ∨ v.val + 32768 ≤ x.val)
    (hPW : ∀ b, PW b → P1.Aligned b → OffV V b) :
    ∀ b, ResetW p sb x PW b → P1.Aligned b → OffV (VOut V p.val (p.val + 2 ^ sb.val)) b := by
  intro b hb hal v hv
  obtain ⟨hvV, hout⟩ := hv
  obtain ⟨c, hc⟩ : 8 ∣ 2 ^ sb.val := by
    have := Nat.pow_dvd_pow 2 hsb3; simpa using this
  have hal' : b.val % 8 = 0 := hal
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
  · rcases hout with h | h
    · right; omega
    · left; omega
  · rcases hxV v hvV with h | h
    · left; omega
    · right; omega
  · exact hPW b h hal v hvV

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`VRelAll` across the reset, outside its region** (module docstring). -/
theorem VRelAll.of_reset {Z : Type} {V : Set U64} (hf : ∀ v ∈ V, VFits v) {s s' : S} {σ σ' : Fl4Spec.State Z}
    (h : VRelAll V (memW st s) σ) {p sb x : U64} {PW : U64 → Prop} (hw : WFrame (L := L) s s' (ResetW p sb x PW))
    (hp8 : p.val % 8 = 0) (hsb3 : 3 ≤ sb.val) (hx8 : x.val % 8 = 0)
    (hxV : ∀ v ∈ V, x.val + 16 ≤ v.val ∨ v.val + 32768 ≤ x.val) (hPW : ∀ b, PW b → P1.Aligned b → OffV V b)
    (hs : ∀ v ∈ VOut V p.val (p.val + 2 ^ sb.val), Fl4Spec.vcpuAt σ' v.bv = Fl4Spec.vcpuAt σ v.bv) :
    VRelAll (VOut V p.val (p.val + 2 ^ sb.val)) (memW st s') σ' :=
  VRelAll.of_writes (fun v (hv : v ∈ VOut V _ _) => hf v hv.1) (VRelAll.mono (VOut_sub V _ _) h) (WritesIn.of_wframe hw)
    (offV_resetW hp8 hsb3 hx8 hxV hPW) hs

end

/-- `detype R` keeps every VCPU off `R`. -/
theorem vcpuAt_detype {Z : Type} {R : Set Fl4Spec.ObjRef} {σ : Fl4Spec.State Z} {v : Fl4Spec.ObjRef} (h : v ∉ R) :
    Fl4Spec.vcpuAt (Fl4Spec.detype R σ) v = Fl4Spec.vcpuAt σ v := by
  unfold Fl4Spec.vcpuAt Fl4Spec.detype
  simp [h]

/-! ## The reset's region holds no VCPU of `V` -/

/-- **Every VCPU of `V` has a cap** in a slot of the MDB (module docstring: the invariant). -/
def VCapped (V : Set U64) (mem : U64 → U64) (G : MdbGhost) : Prop :=
  ∀ v ∈ V, ∃ y ∈ G.chains.flatten, capV mem y = .Vcpu v

/-- A `Vcpu` cap is no untyped cap's MDB parent. -/
theorem not_isPM_vcpu_ut {mem : U64 → U64} {y x v p sb fi : U64} {d : Bool} (hy : capV mem y = .Vcpu v)
    (hx : capV mem x = .Untyped p sb fi d) : isPM mem y x = false := by
  unfold isPM isPF
  rw [hy, hx]
  cases h : srB (.Vcpu v) (.Untyped p sb fi d)
  · simp
  · have := srB_vcpu_left h
    simp [shape] at this

/-- **No VCPU of `V` in the region of an untyped cap without children** (module docstring). -/
theorem vcpu_out_of_reset {mem : U64 → U64} {G : MdbGhost} {V : Set U64} (hU : UtInv mem G) (hI : MdbInv mem G)
    (hVC : VCapped V mem G) (hfit : ∀ v ∈ V, v.val + 32768 ≤ 2 ^ 64)
    {x p sb fi : U64} {d : Bool} (hx : x ∈ G.chains.flatten) (hcx : capV mem x = .Untyped p sb fi d)
    (hnc : ∀ y, ¬ Mdb.Desc G.par y x) :
    ∀ v ∈ V, v.val + 32768 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ v.val := by
  intro v hv
  obtain ⟨y, hy, hcy⟩ := hVC v hv
  have hsb := capV_ut_sb hcx
  have hreg := hU.reg x hx (by rw [hcx]; exact ok_inj (phys_eq _).symm)
  rw [hcx] at hreg
  obtain ⟨hb, ht, -⟩ := ut_range hsb hreg
  have hyx : y ≠ x := by
    intro e; rw [e, hcx] at hcy; cases hcy
  by_contra hov
  have hnd : ¬ Disj (capV mem y) (capV mem x) := by
    rw [hcy, hcx]
    unfold Disj
    rw [topF_vcpu (hfit v hv), baseF_vcpu, hb, ht]
    omega
  rcases hU.drange x hx p sb fi d hcx y hy hyx (by rw [hcy]; exact physF_vcpu v) hnd with h | h
  · exact hnc y h
  · have := hI.desc y x h
    rw [not_isPM_vcpu_ut hcy hcx] at this
    cases this

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`VRelAll V` across the reset of an untyped cap without children** (module docstring: `VRelAll.of_reset` with
`VOut V … = V` by `vcpu_out_of_reset`). -/
theorem VRelAll.of_reset_noChildren {Z : Type} {V : Set U64} (hf : ∀ v ∈ V, VFits v) {s s' : S}
    {σ σ' : Fl4Spec.State Z} (h : VRelAll V (memW st s) σ) {G : MdbGhost} (hU : UtInv (L.mem s) G)
    (hI : MdbInv (L.mem s) G) (hVC : VCapped V (L.mem s) G) {x p sb fi : U64} {d : Bool}
    (hx : x ∈ G.chains.flatten) (hcx : capV (L.mem s) x = .Untyped p sb fi d) (hnc : ∀ y, ¬ Mdb.Desc G.par y x)
    {PW : U64 → Prop} (hw : WFrame (L := L) s s' (ResetW p sb x PW))
    (hp8 : p.val % 8 = 0) (hsb3 : 3 ≤ sb.val) (hx8 : x.val % 8 = 0)
    (hxV : ∀ v ∈ V, x.val + 16 ≤ v.val ∨ v.val + 32768 ≤ x.val) (hPW : ∀ b, PW b → P1.Aligned b → OffV V b)
    (hs : ∀ v ∈ V, Fl4Spec.vcpuAt σ' v.bv = Fl4Spec.vcpuAt σ v.bv) :
    VRelAll V (memW st s') σ' := by
  have e := VOut_eq (vcpu_out_of_reset hU hI hVC (fun v hv => (hf v hv).2) hx hcx hnc)
  have := VRelAll.of_reset hf h hw hp8 hsb3 hx8 hxV hPW (fun v hv => hs v hv.1)
  rwa [e] at this

end

end
end Fl4Proofs.P3.VirtResetV

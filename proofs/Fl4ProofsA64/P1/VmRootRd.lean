/-
# P1 (AArch64): what `set_vm_root` reads, and that it commutes with writes elsewhere

The AArch64 counterpart of part (c1) of x86_64's `Fl4Proofs.P1.FastFin`. x86_64's `set_vm_root` reads a
thread's VTABLE slot, the kernel root word and the ASID table / pool words. AArch64's
(arch/aarch64/vspace.rs `set_vm_root`, lines 365–403) reads more, and what it reads depends on the
state:

* `vcpu::bound(t)`: the thread's `VCPU` word (TCB + 3664);
* with a bound VCPU: the kernel root word, then `set_stage2_root(t)`: the thread's VTABLE slot (two
  words) and, for an `Ept` (stage-2) cap, the ASID table / pool words (`ept::find` = `find_asid_raw`);
* without: the VTABLE slot; for a `Pml4` cap the ASID table / pool words (`find_vspace_for_asid`), the
  thread's `STATE` word and, off `TS_RUNNING_VM`, `high_root_of(t)`: the `HIGH_VSPACE` slot (two words)
  and the ASID table / pool words (`find_high_asid`); for any other cap the kernel root word;
* then, at the same store, the `STATE` word again and, in `TS_RUNNING_VM`: the thread's `RUN_VCPU` word
  (TCB + 3672), the run VCPU's guest-TCB word (`RUN_VCPU` value + `vcpu::TCB`), and, when that is
  nonzero, `set_stage2_root(guest)`: the guest's VTABLE slot and the ASID words.

`VmOff s t A` says that none of these words is `A` (the value-dependent ones — ASID pools, the guest
TCB word and the guest's slot — at the values `s` holds, as x86_64's `TabOff` does for the pools). Then:

* `set_vm_root_wr`: `set_vm_root` commutes with a write to `A` (x86_64 `FastFin.set_vm_root_wr`);
* `VmOff.wr`: `VmOff` survives writes it allows, `set_vm_root_wrs`: so it commutes with a sequence;
* `set_vm_root_ok_s`: an `ok` run returns its input store (it only reads and calls the Arch).

The ASID table is at `ks + 772352` (AArch64 `ks::ASID_TABLE`: 223488 + 128 · 4288) and has 128 entries
(`N_ASID_POOLS` = 1 << 7; x86_64: 2048 at `ks + 288000`).

No premises.
-/
import Fl4ProofsA64.P1.FastSched
import Fl4ProofsA64.P2.GuardBase
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! ## Addresses -/

/-- The address of word `hi` of the AArch64 ASID table (`ks::ASID_TABLE` = 772352). -/
def atAF (ksb hi : U64) : U64 :=
  core.num.U64.wrapping_add ksb (core.num.U64.wrapping_add 772352#u64 (core.num.U64.wrapping_mul hi 8#u64))
/-- The address of word `lo` of the ASID pool at `p`. -/
def peAF (p lo : U64) : U64 := core.num.U64.wrapping_add p (core.num.U64.wrapping_mul lo 8#u64)
/-- The thread's VTABLE slot. -/
def vtA (t : U64) : U64 := core.num.U64.wrapping_add t (core.num.U64.wrapping_mul layout.tcb.SLOT_VTABLE layout.cte.SIZE)
/-- The thread's `HIGH_VSPACE` slot (the TTBR1 high VSpace). -/
def hvA (t : U64) : U64 :=
  core.num.U64.wrapping_add t (core.num.U64.wrapping_mul layout.tcb.SLOT_HIGH_VSPACE layout.cte.SIZE)
/-- The thread's bound-VCPU word (`layout::tcb::VCPU` = 3664). -/
def vcA (t : U64) : U64 := core.num.U64.wrapping_add t 3664#u64
/-- The kernel root word. -/
def krA (s : S) : U64 := core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT
/-- The guest-TCB word of the VCPU that `t` runs (`RUN_VCPU(t)` + `vcpu::TCB`), at the values of `s`. -/
def gtA (s : S) (t : U64) : U64 := core.num.U64.wrapping_add (L.mem s (runVcpuA t)) vcpu.TCB

/-! ## The ASID lookup -/

theorem asid_table_eq (s : S) (hi : U64) :
    vspace.asid_table st s hi = ok (L.mem s (atAF (L.ksb s) (hi &&& 127#u64))) := by
  apply eq_of_spec_fd
  unfold vspace.asid_table obj.ks_get
  step*
  subst_vars
  congr 4
  apply UScalar.eq_of_val_eq
  simp_all [UScalar.val_and]

/-- The ASID table and pool words are aligned and not `A` (only the words `find_asid_raw` can read:
table word `hi < 128`, pool word `lo < 512`). -/
def TabOff (s : S) (A : U64) : Prop :=
  ∀ hi : U64, hi.val < 128 → (Aligned (atAF (L.ksb s) hi) ∧ A ≠ atAF (L.ksb s) hi) ∧
    ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      Aligned (peAF (L.mem s (atAF (L.ksb s) hi)) lo) ∧ A ≠ peAF (L.mem s (atAF (L.ksb s) hi)) lo

theorem and127_lt (i : U64) : (i &&& 127#u64).val < 128 := by
  rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem and511_lt (i : U64) : (i &&& 511#u64).val < 512 := by
  rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem find_asid_raw_wr {s : S} {A v : U64} (hA : Aligned A) (hT : TabOff (L := L) s A) (asid : U64) :
    vspace.find_asid_raw st (L.wr s A v) asid = vspace.find_asid_raw st s asid := by
  unfold vspace.find_asid_raw
  congr 1; funext i
  by_cases h0 : (i != 0#u64) = true
  · simp only [if_pos h0]
  · simp only [if_neg h0]
    congr 1; funext i1
    rw [asid_table_eq, asid_table_eq, L.ksb_wr]
    obtain ⟨⟨h1, h2⟩, h3⟩ := hT (i1 &&& 127#u64) (and127_lt i1)
    rw [mem_wr_ne' hA h1 h2]
    by_cases hp : L.mem s (atAF (L.ksb s) (i1 &&& 127#u64)) = 0#u64
    · simp only [hp, bind_ok, ↓reduceIte]
    · simp only [hp, bind_ok, ↓reduceIte, lift, L.read_eq]
      obtain ⟨h4, h5⟩ := h3 (asid &&& 511#u64) (and511_lt asid) hp
      unfold peAF at h4 h5
      rw [mem_wr_ne' hA h4 h5]

theorem find_asid_wr {s : S} {A v : U64} (hA : Aligned A) (hT : TabOff (L := L) s A) (asid : U64) :
    vspace.find_asid st (L.wr s A v) asid = vspace.find_asid st s asid := by
  unfold vspace.find_asid; rw [find_asid_raw_wr hA hT]

theorem find_vspace_for_asid_wr {s : S} {A v : U64} (hA : Aligned A) (hT : TabOff (L := L) s A) (asid : U64) :
    vspace.find_vspace_for_asid st (L.wr s A v) asid = vspace.find_vspace_for_asid st s asid := by
  unfold vspace.find_vspace_for_asid; rw [find_asid_wr hA hT]

theorem find_high_asid_wr {s : S} {A v : U64} (hA : Aligned A) (hT : TabOff (L := L) s A) (asid : U64) :
    vspace.find_high_asid st (L.wr s A v) asid = vspace.find_high_asid st s asid := by
  unfold vspace.find_high_asid; rw [find_asid_raw_wr hA hT]

theorem ept_find_wr {s : S} {A v : U64} (hA : Aligned A) (hT : TabOff (L := L) s A) (asid : U64) :
    ept.find st (L.wr s A v) asid = ept.find st s asid := by
  unfold ept.find; rw [find_asid_raw_wr hA hT]

/-! ## Single reads -/

theorem kernel_root_wr {s : S} {A v : U64} (hA : Aligned A) (h : Aligned (krA (L := L) s) ∧ A ≠ krA (L := L) s) :
    vspace.kernel_root st (L.wr s A v) = vspace.kernel_root st s := by
  unfold vspace.kernel_root obj.ks_get
  simp only [L.ks_base_eq, bind_ok, lift, L.read_eq, L.ksb_wr]
  unfold krA at h
  rw [mem_wr_ne' hA h.1 h.2]

theorem cap_wr {s : S} {A v : U64} (sl : U64) (hA : Aligned A) (h0 : Aligned sl ∧ A ≠ sl)
    (h1 : Aligned (core.num.U64.wrapping_add sl 8#u64) ∧ A ≠ core.num.U64.wrapping_add sl 8#u64) :
    obj.Slot.cap st sl (L.wr s A v) = obj.Slot.cap st sl s := by
  unfold obj.Slot.cap
  rw [L.read_pair_eq, L.read_pair_eq, mem_wr_ne' hA h0.1 h0.2, mem_wr_ne' hA h1.1 h1.2]

theorem slot_vt (t : U64) : obj.Tcb.slot t layout.tcb.SLOT_VTABLE = ok (vtA t) := by
  simp [obj.Tcb.slot, lift, vtA]

theorem slot_hv (t : U64) : obj.Tcb.slot t layout.tcb.SLOT_HIGH_VSPACE = ok (hvA t) := by
  simp [obj.Tcb.slot, lift, hvA]

theorem state_wr {s : S} {A v : U64} (t : U64) (hA : Aligned A) (h : Aligned (stA t) ∧ A ≠ stA t) :
    obj.Tcb.state st t (L.wr s A v) = obj.Tcb.state st t s := by
  unfold obj.Tcb.state
  simp only [lift, bind_ok, L.read_eq]
  unfold stA at h
  rw [mem_wr_ne' hA h.1 h.2]

theorem bound_wr {s : S} {A v : U64} (t : U64) (hA : Aligned A) (h : Aligned (vcA t) ∧ A ≠ vcA t) :
    vcpu.bound st (L.wr s A v) t = vcpu.bound st s t := by
  rw [eq_of_spec_fd (vcpu.bound.spec (L := L) (L.wr s A v) t), eq_of_spec_fd (vcpu.bound.spec (L := L) s t)]
  unfold vcA at h
  rw [mem_wr_ne' hA h.1 h.2]

theorem high_root_of_wr {s : S} {A v : U64} (t : U64) (hA : Aligned A) (h0 : Aligned (hvA t) ∧ A ≠ hvA t)
    (h1 : Aligned (core.num.U64.wrapping_add (hvA t) 8#u64) ∧ A ≠ core.num.U64.wrapping_add (hvA t) 8#u64)
    (hT : TabOff (L := L) s A) :
    vspace.high_root_of st (L.wr s A v) t = vspace.high_root_of st s t := by
  unfold vspace.high_root_of
  rw [slot_hv]; simp only [bind_ok]
  rw [cap_wr _ hA h0 h1]
  simp only [find_high_asid_wr (v := v) hA hT]

/-! ## The read set -/

/-- The thread's slot `sl` (two words) is aligned and not `A`. -/
def SlotOff (sl A : U64) : Prop :=
  (Aligned sl ∧ A ≠ sl) ∧ (Aligned (core.num.U64.wrapping_add sl 8#u64) ∧ A ≠ core.num.U64.wrapping_add sl 8#u64)

/-- **What AArch64's `set_vm_root t` reads is not the word `A`** (aligned words only; see the module
docstring). The guest words are read only when `t` has a nonzero `RUN_VCPU` (`gt`) and that VCPU a
nonzero guest TCB (`gs`), at the values of `s`. -/
structure VmOff (s : S) (t A : U64) : Prop where
  hA : Aligned A
  vc : Aligned (vcA t) ∧ A ≠ vcA t
  sl : SlotOff (vtA t) A
  hv : SlotOff (hvA t) A
  kr : Aligned (krA (L := L) s) ∧ A ≠ krA (L := L) s
  tab : TabOff (L := L) s A
  st : Aligned (stA t) ∧ A ≠ stA t
  rv : Aligned (runVcpuA t) ∧ A ≠ runVcpuA t
  gt : L.mem s (runVcpuA t) ≠ 0#u64 → Aligned (gtA (L := L) s t) ∧ A ≠ gtA (L := L) s t
  gs : L.mem s (runVcpuA t) ≠ 0#u64 → L.mem s (gtA (L := L) s t) ≠ 0#u64 →
    SlotOff (vtA (L.mem s (gtA (L := L) s t))) A

variable {A : Type _} (ar : machine.Arch A)

/-! ## Commuting past one write -/

theorem set_kernel_vm_root_wr {s : S} {X v : U64} (a : A) (hX : Aligned X)
    (h : Aligned (krA (L := L) s) ∧ X ≠ krA (L := L) s) :
    vspace.set_kernel_vm_root st ar (L.wr s X v) a =
      (vspace.set_kernel_vm_root st ar s a) >>= fun r => ok (L.wr r.1 X v, r.2) := by
  unfold vspace.set_kernel_vm_root
  rw [kernel_root_wr hX h]
  simp only [bind_tc_eq, Std.bind_assoc, bind_ok]

theorem set_kernel_vm_root_ok_s {s : S} {a : A} {r : S × A} (h : vspace.set_kernel_vm_root st ar s a = ok r) :
    r.1 = s := by
  unfold vspace.set_kernel_vm_root at h
  obtain ⟨k, -, h⟩ := bind_eq_ok h
  obtain ⟨a1, -, h⟩ := bind_eq_ok h
  obtain ⟨a2, -, h⟩ := bind_eq_ok h
  have h2 := spec_of_eq_fd h; rw [WP.spec_ok] at h2; rw [← h2]

/-- A bind over the Arch value that returns the store `s`: past a write it is the bind returning the
written store. -/
theorem arm_wr {s : S} {X v : U64} (m : Result A) :
    Std.bind m (fun a1 => (ok (L.wr s X v, a1) : Result (S × A))) =
      Std.bind (Std.bind m fun a1 => (ok (s, a1) : Result (S × A))) fun r => ok (L.wr r.1 X v, r.2) := by
  simp only [bind_tc_eq, Std.bind_assoc, bind_ok]

theorem arm_ok {s : S} {m : Result A} {r : S × A} (h : Std.bind m (fun a1 => (ok (s, a1) : Result (S × A))) = ok r) :
    r.1 = s := by
  obtain ⟨a1, -, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]

/-- `Result`'s bind congruence at the values the first step produces (`P2.PathObl.bind_guard_congr`, at
any universe). -/
theorem bind_guard {α β : Type _} {m : Result α} {k k' : α → Result β}
    (hk : ∀ x, m = ok x → k' x = k x) : Std.bind m k' = Std.bind m k := by
  cases m with
  | ret x => rw [bind_ok, bind_ok]; exact hk x rfl
  | vis i k0 =>
    rw [bind_vis, bind_vis]; congr 1; funext y; cases i; exact PEmpty.elim y
  | div => rw [bind_div, bind_div]

/-- Pushing a continuation `W` under a bind, given it at every value. -/
theorem bind_push {α β γ : Type _} (m : Result α) {k : α → Result β} {k' : α → Result γ} {W : β → Result γ}
    (hk : ∀ x, k' x = Std.bind (k x) W) : Std.bind m k' = Std.bind (Std.bind m k) W := by
  cases m with
  | ret x => rw [bind_ok, bind_ok]; exact hk x
  | vis i k0 =>
    rw [bind_vis, bind_vis, bind_vis]; congr 1; funext y; cases i; exact PEmpty.elim y
  | div => rw [bind_div, bind_div, bind_div]

/-- The `Ept` arm of `set_stage2_root`, its `match i with | 0 => … | _ => …` written as an `if`. -/
def s2Ept (s : S) (a : A) (ptr i : U64) (b : Bool) (asid : U64) : Result (S × A) :=
  if i = 0#u64
  then
    if b
    then do
      let r ← ept.find st s asid
      match r with
      | core.result.Result.Ok r1 =>
        if r1 = ptr
        then do
          let a1 ← ar.set_stage2_vspace a ptr asid
          ok (s, a1)
        else do
          let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
          ok (s, a1)
      | core.result.Result.Err _ => do
        let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
        ok (s, a1)
    else do
      let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
      ok (s, a1)
  else do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)

/-- The cap match of `set_stage2_root` (AArch64 body), the `Ept` arm as `s2Ept`. -/
def s2Arm (s : S) (a : A) (c : capability.Cap) : Result (S × A) :=
  match c with
  | capability.Cap.Null => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Untyped _ _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Endpoint _ _ _ _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Notification _ _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Reply _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.CNode _ _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Thread _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.IrqControl => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.IrqHandler _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Zombie _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Domain => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.SchedContext _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.SchedControl _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Frame _ _ _ _ _ _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.PageTable _ _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.PageDirectory _ _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Pdpt _ _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Pml4 _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Vcpu _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.Ept ptr i b asid _ => s2Ept (st := st) ar s a ptr i b asid
  | capability.Cap.AsidControl => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.AsidPool _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.IoPortControl => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.IoPort _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.TdxControl => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)
  | capability.Cap.HighVSpace _ _ _ => do
    let a1 ← ar.set_stage2_vspace a 0#u64 0#u64
    ok (s, a1)

/-- `set_stage2_root` is the slot read, then `s2Arm`. -/
theorem set_stage2_root_unf (s : S) (a : A) (t : U64) :
    vspace.set_stage2_root st ar s a t = Std.bind (obj.Slot.cap st (vtA t) s) (s2Arm (st := st) ar s a) := by
  unfold vspace.set_stage2_root
  rw [slot_vt]; simp only [bind_ok]
  congr 1; funext c
  cases c
  all_goals try rfl
  rename_i ptr i b asid x0
  simp only [s2Arm, s2Ept]
  split
  · exact (if_pos rfl).symm
  · rw [if_neg (fun e => by
      first
        | exact absurd e ‹¬ i = _›
        | exact ‹i = _ → False› e)]

theorem s2Ept_wr {s : S} {X v : U64} (a : A) (ptr i : U64) (b : Bool) (asid : U64) (hX : Aligned X)
    (hT : TabOff (L := L) s X) :
    s2Ept (st := st) ar (L.wr s X v) a ptr i b asid =
      (s2Ept (st := st) ar s a ptr i b asid) >>= fun r => ok (L.wr r.1 X v, r.2) := by
  unfold s2Ept
  by_cases hi : i = 0#u64
  · simp only [if_pos hi]
    cases b
    · exact arm_wr _
    · simp only [↓reduceIte]
      rw [ept_find_wr hX hT]
      refine bind_push _ fun r => ?_
      rcases r with r1 | e
      · by_cases e1 : r1 = ptr
        · simp only [e1, ↓reduceIte]; exact arm_wr _
        · simp only [e1, ↓reduceIte]; exact arm_wr _
      · exact arm_wr _
  · simp only [if_neg hi]; exact arm_wr _

theorem s2Ept_ok_s {s : S} {a : A} {ptr i : U64} {b : Bool} {asid : U64} {r : S × A}
    (h : s2Ept (st := st) ar s a ptr i b asid = ok r) : r.1 = s := by
  unfold s2Ept at h
  by_cases hi : i = 0#u64
  · rw [if_pos hi] at h
    cases b
    · exact arm_ok h
    · simp only [↓reduceIte] at h
      obtain ⟨x, -, h⟩ := bind_eq_ok h
      rcases x with r1 | e
      · by_cases e1 : r1 = ptr
        · simp only [e1, ↓reduceIte] at h; exact arm_ok h
        · simp only [e1, ↓reduceIte] at h; exact arm_ok h
      · exact arm_ok h
  · rw [if_neg hi] at h; exact arm_ok h

theorem s2Arm_wr {s : S} {X v : U64} (a : A) (c : capability.Cap) (hX : Aligned X) (hT : TabOff (L := L) s X) :
    s2Arm (st := st) ar (L.wr s X v) a c = (s2Arm (st := st) ar s a c) >>= fun r => ok (L.wr r.1 X v, r.2) := by
  cases c
  all_goals try exact arm_wr _
  rename_i ptr i b asid x0
  exact s2Ept_wr ar a ptr i b asid hX hT

theorem s2Arm_ok_s {s : S} {a : A} {c : capability.Cap} {r : S × A} (h : s2Arm (st := st) ar s a c = ok r) :
    r.1 = s := by
  cases c
  all_goals try exact arm_ok h
  exact s2Ept_ok_s ar h

/-- `set_stage2_root t` commutes with a write off `t`'s VTABLE slot and the ASID words. -/
theorem set_stage2_root_wr {s : S} {X v : U64} (a : A) (t : U64) (hX : Aligned X) (hs : SlotOff (vtA t) X)
    (hT : TabOff (L := L) s X) :
    vspace.set_stage2_root st ar (L.wr s X v) a t =
      (vspace.set_stage2_root st ar s a t) >>= fun r => ok (L.wr r.1 X v, r.2) := by
  rw [set_stage2_root_unf (st := st) ar (L.wr s X v) a t, set_stage2_root_unf (st := st) ar s a t,
    cap_wr _ hX hs.1 hs.2]
  refine (congrArg (Std.bind (obj.Slot.cap st (vtA t) s)) (funext fun c => s2Arm_wr (st := st) ar a c hX hT)).trans ?_
  first
    | exact (Std.bind_assoc _ _ _).symm
    | (simp only [Std.bind_assoc]; done)
    | rfl

theorem set_stage2_root_ok_s {s : S} {a : A} {t : U64} {r : S × A} (h : vspace.set_stage2_root st ar s a t = ok r) :
    r.1 = s := by
  rw [set_stage2_root_unf (st := st) ar s a t] at h
  obtain ⟨c, -, h⟩ := bind_eq_ok h
  exact s2Arm_ok_s ar h

/-- The cap match of `set_vm_root` (no bound VCPU), as it stands in AArch64's body. -/
def vmHead (s : S) (a : A) (t : obj.Tcb) (c : capability.Cap) : Result (S × A) :=
  match c with
  | capability.Cap.Null => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Untyped _ _ _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Endpoint _ _ _ _ _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Notification _ _ _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Reply _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.CNode _ _ _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Thread _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.IrqControl => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.IrqHandler _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Zombie _ _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Domain => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.SchedContext _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.SchedControl _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Frame _ _ _ _ _ _ _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.PageTable _ _ _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.PageDirectory _ _ _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Pdpt _ _ _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Pml4 ptr b asid =>
    if b
    then
      do
      let r ← vspace.find_vspace_for_asid st s asid
      match r with
      | core.result.Result.Ok r1 =>
        if r1 = ptr
        then
          let i1 ← obj.Tcb.state st t s
          let high ←
            if i1 = sched.TS_RUNNING_VM
            then ok 0#u64
            else vspace.high_root_of st s t
          let t1 ←
            if high = 0#u64
            then
              do
              let a2 ← ar.set_high_vspace a 0#u64 asid
              ar.set_vspace a2 ptr asid
            else
              do
              let a2 ← ar.set_vspace a ptr asid
              ar.set_high_vspace a2 high asid
          ok (s, t1)
        else vspace.set_kernel_vm_root st ar s a
      | core.result.Result.Err _ =>
        vspace.set_kernel_vm_root st ar s a
    else vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Vcpu _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.Ept _ _ _ _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.AsidControl => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.AsidPool _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.IoPortControl => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.IoPort _ _ _ => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.TdxControl => vspace.set_kernel_vm_root st ar s a
  | capability.Cap.HighVSpace _ _ _ => vspace.set_kernel_vm_root st ar s a

/-- The `TS_RUNNING_VM` tail of `set_vm_root`, as it stands in AArch64's body. -/
def vmTail (s2 : S) (a1 : A) (t : obj.Tcb) : Result (S × A) := do
  let i1 ← obj.Tcb.state st t s2
  if i1 = sched.TS_RUNNING_VM
  then
    let i2 ← layout.tcb.RUN_VCPU
    let i3 ← lift (core.num.U64.wrapping_add t i2)
    let run_v ← st.read s2 i3
    if run_v != 0#u64
    then
      let i4 ← lift (core.num.U64.wrapping_add run_v vcpu.TCB)
      let guest_tcb ← st.read s2 i4
      if guest_tcb != 0#u64
      then
        vspace.set_stage2_root st ar s2 a1 guest_tcb
      else ok (s2, a1)
    else ok (s2, a1)
  else ok (s2, a1)

/-- AArch64's `set_vm_root`, with its cap match and its tail named. -/
theorem set_vm_root_split (s : S) (a : A) (t : obj.Tcb) :
    vspace.set_vm_root st ar s a t = (do
      let i ← vcpu.bound st s t
      if i != 0#u64
      then
        let (s1, a1) ← vspace.set_kernel_vm_root st ar s a
        vspace.set_stage2_root st ar s1 a1 t
      else
        let c ← obj.Slot.cap st (vtA t) s
        let (s2, a1) ← vmHead (st := st) ar s a t c
        vmTail (st := st) ar s2 a1 t) := by
  unfold vspace.set_vm_root
  rw [slot_vt]; simp only [bind_ok]
  rfl

theorem vmHead_wr {s : S} {X v : U64} (a : A) (t : U64) (c : capability.Cap) (h : VmOff (L := L) s t X) :
    vmHead (st := st) ar (L.wr s X v) a t c =
      (vmHead (st := st) ar s a t c) >>= fun r => ok (L.wr r.1 X v, r.2) := by
  have K := set_kernel_vm_root_wr (L := L) ar (v := v) a h.hA h.kr
  unfold vmHead
  cases c
  all_goals try exact K
  rename_i ptr b asid
  cases b
  · exact K
  · simp only [↓reduceIte]
    rw [find_vspace_for_asid_wr h.hA h.tab]
    simp only [bind_tc_eq, Std.bind_assoc]
    congr 1; funext r
    rcases r with r1 | e
    · by_cases e1 : r1 = ptr
      · simp only [e1, ↓reduceIte, bind_tc_eq, Std.bind_assoc]
        rw [state_wr t h.hA h.st, high_root_of_wr t h.hA h.hv.1 h.hv.2 h.tab]
        simp only [bind_tc_eq, Std.bind_assoc, bind_ok]
      · simp only [e1, ↓reduceIte]; exact K
    · exact K

theorem vmHead_ok_s {s : S} {a : A} {t : U64} {c : capability.Cap} {r : S × A}
    (h : vmHead (st := st) ar s a t c = ok r) : r.1 = s := by
  unfold vmHead at h
  cases c
  all_goals try exact set_kernel_vm_root_ok_s ar h
  rename_i ptr b asid
  cases b
  · exact set_kernel_vm_root_ok_s ar h
  · simp only [↓reduceIte] at h
    obtain ⟨x, -, h⟩ := bind_eq_ok h
    rcases x with r1 | e
    · by_cases e1 : r1 = ptr
      · simp only [e1, ↓reduceIte] at h
        obtain ⟨i1, -, h⟩ := bind_eq_ok h
        obtain ⟨hi, -, h⟩ := bind_eq_ok h
        obtain ⟨a1, -, h⟩ := bind_eq_ok h
        have h2 := spec_of_eq_fd h; rw [WP.spec_ok] at h2; rw [← h2]
      · simp only [e1, ↓reduceIte] at h; exact set_kernel_vm_root_ok_s ar h
    · exact set_kernel_vm_root_ok_s ar h

theorem vmTail_wr {s : S} {X v : U64} (a1 : A) (t : U64) (h : VmOff (L := L) s t X) :
    vmTail (st := st) ar (L.wr s X v) a1 t =
      (vmTail (st := st) ar s a1 t) >>= fun r => ok (L.wr r.1 X v, r.2) := by
  unfold vmTail
  rw [state_wr t h.hA h.st]
  simp only [bind_tc_eq, Std.bind_assoc]
  congr 1; funext i1
  split
  next hi =>
    rw [eq_of_spec_fd layout.tcb.RUN_VCPU.spec]
    simp only [bind_ok, lift, L.read_eq, Std.bind_assoc]
    have hrv := h.rv
    unfold runVcpuA at hrv
    rw [mem_wr_ne' h.hA hrv.1 hrv.2]
    split
    next h0 =>
      have hn : L.mem s (runVcpuA t) ≠ 0#u64 := by
        unfold runVcpuA; rw [bne_iff_ne] at h0; exact h0
      have hg := h.gt hn
      unfold gtA runVcpuA at hg
      rw [mem_wr_ne' h.hA hg.1 hg.2]
      split
      next h1 =>
        have hg2 : L.mem s (gtA (L := L) s t) ≠ 0#u64 := by
          unfold gtA runVcpuA; rw [bne_iff_ne] at h1; exact h1
        have hs := h.gs hn hg2
        unfold gtA runVcpuA at hs
        exact set_stage2_root_wr ar a1 _ h.hA hs h.tab
      next h1 => simp only [bind_ok]
    next h0 => simp only [bind_ok]
  next hi => simp only [bind_ok]

theorem vmTail_ok_s {s : S} {a1 : A} {t : U64} {r : S × A}
    (h : vmTail (st := st) ar s a1 t = ok r) : r.1 = s := by
  have fin : r = (s, a1) → r.1 = s := fun e => by rw [e]
  unfold vmTail at h
  obtain ⟨i1, -, h⟩ := bind_eq_ok h
  by_cases hi : i1 = sched.TS_RUNNING_VM
  · rw [if_pos hi] at h
    obtain ⟨i2, -, h⟩ := bind_eq_ok h
    obtain ⟨i3, -, h⟩ := bind_eq_ok h
    obtain ⟨rv, -, h⟩ := bind_eq_ok h
    by_cases h0 : (rv != 0#u64) = true
    · rw [if_pos h0] at h
      obtain ⟨i4, -, h⟩ := bind_eq_ok h
      obtain ⟨g, -, h⟩ := bind_eq_ok h
      by_cases h1 : (g != 0#u64) = true
      · rw [if_pos h1] at h
        exact set_stage2_root_ok_s ar h
      · rw [if_neg h1] at h
        exact fin (ok_inj_ff h).symm
    · rw [if_neg h0] at h
      exact fin (ok_inj_ff h).symm
  · rw [if_neg hi] at h
    exact fin (ok_inj_ff h).symm

/-- **(c1, AArch64) `set_vm_root` commutes with a write it does not read.** -/
theorem set_vm_root_wr {s : S} {X v : U64} (a : A) (t : U64) (h : VmOff (L := L) s t X) :
    vspace.set_vm_root st ar (L.wr s X v) a t =
      (vspace.set_vm_root st ar s a t) >>= fun r => ok (L.wr r.1 X v, r.2) := by
  rw [set_vm_root_split, set_vm_root_split, bound_wr t h.hA h.vc]
  simp only [bind_tc_eq, Std.bind_assoc]
  congr 1; funext i
  by_cases hi : (i != 0#u64) = true
  · simp only [if_pos hi]
    rw [set_kernel_vm_root_wr ar a h.hA h.kr]
    simp only [bind_tc_eq, Std.bind_assoc, bind_ok]
    refine bind_guard fun r hr => ?_
    obtain ⟨s1, a1⟩ := r
    have e : s1 = s := set_kernel_vm_root_ok_s ar hr
    show vspace.set_stage2_root st ar (L.wr s1 X v) a1 t =
      vspace.set_stage2_root st ar s1 a1 t >>= fun r => ok (L.wr r.1 X v, r.2)
    rw [e]
    exact set_stage2_root_wr ar a1 t h.hA h.sl h.tab
  · simp only [if_neg hi]
    rw [cap_wr _ h.hA h.sl.1 h.sl.2]
    simp only [bind_tc_eq, Std.bind_assoc]
    congr 1; funext c
    rw [vmHead_wr ar a t c h]
    simp only [bind_tc_eq, Std.bind_assoc, bind_ok]
    refine bind_guard fun r hr => ?_
    obtain ⟨s2, a1⟩ := r
    have e : s2 = s := vmHead_ok_s ar hr
    show vmTail (st := st) ar (L.wr s2 X v) a1 t =
      vmTail (st := st) ar s2 a1 t >>= fun r => ok (L.wr r.1 X v, r.2)
    rw [e]
    exact vmTail_wr ar a1 t h

/-- `set_vm_root` returns its store unchanged. -/
theorem set_vm_root_ok_s {s : S} {a : A} {t : U64} {r : S × A} (h : vspace.set_vm_root st ar s a t = ok r) :
    r.1 = s := by
  rw [set_vm_root_split] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases hi : (i != 0#u64) = true
  · rw [if_pos hi] at h
    obtain ⟨⟨s1, a1⟩, h1, h⟩ := bind_eq_ok h
    have e : s1 = s := set_kernel_vm_root_ok_s ar h1
    rw [← e]
    exact set_stage2_root_ok_s (s := s1) (a := a1) (t := t) ar h
  · rw [if_neg hi] at h
    obtain ⟨c, -, h⟩ := bind_eq_ok h
    obtain ⟨⟨s2, a1⟩, h1, h⟩ := bind_eq_ok h
    have e : s2 = s := vmHead_ok_s ar h1
    rw [← e]
    exact vmTail_ok_s (s := s2) (a1 := a1) (t := t) ar h

/-! ## Commuting past a sequence of writes -/

theorem VmOff.wr {s : S} {t X B w : U64} (hX : VmOff (L := L) s t X) (hB : VmOff (L := L) s t B) :
    VmOff (L := L) (L.wr s B w) t X := by
  have rvB : L.mem (L.wr s B w) (runVcpuA t) = L.mem s (runVcpuA t) := mem_wr_ne' hB.hA hB.rv.1 hB.rv.2
  have gtB : gtA (L := L) (L.wr s B w) t = gtA (L := L) s t := by unfold gtA; rw [rvB]
  refine ⟨hX.hA, hX.vc, hX.sl, hX.hv, by unfold krA; rw [L.ksb_wr]; exact hX.kr, fun hi hhi => ?_, hX.st, hX.rv,
    fun hn => ?_, fun hn hg => ?_⟩
  · rw [L.ksb_wr]
    obtain ⟨⟨b1, b2⟩, -⟩ := hB.tab hi hhi
    rw [mem_wr_ne' hB.hA b1 b2]
    exact hX.tab hi hhi
  · rw [rvB] at hn; rw [gtB]; exact hX.gt hn
  · rw [rvB] at hn; rw [gtB] at hg ⊢
    have hgB := hB.gt hn
    rw [mem_wr_ne' hB.hA hgB.1 hgB.2] at hg ⊢
    exact hX.gs hn hg

/-- A sequence of writes. -/
def wrs (s : S) : List (U64 × U64) → S
  | [] => s
  | x :: l => wrs (L.wr s x.1 x.2) l

/-- **(c1, AArch64) `set_vm_root` commutes with a sequence of writes it does not read.** -/
theorem set_vm_root_wrs (a : A) (t : U64) :
    ∀ (l : List (U64 × U64)) (x : U64 × U64) (s : S), (∀ y ∈ x :: l, VmOff (L := L) s t y.1) →
      vspace.set_vm_root st ar (wrs (L := L) s (x :: l)) a t =
        (vspace.set_vm_root st ar s a t) >>= fun r => ok (wrs (L := L) r.1 (x :: l), r.2) := by
  intro l
  induction l with
  | nil => intro x s h; simp only [wrs]; exact set_vm_root_wr ar a t (h x (by simp))
  | cons y l ih =>
    intro x s h
    have h0 := h x (by simp)
    have h1 : ∀ z ∈ y :: l, VmOff (L := L) (L.wr s x.1 x.2) t z.1 := fun z hz => (h z (by simp [hz])).wr h0
    show vspace.set_vm_root st ar (wrs (L := L) (L.wr s x.1 x.2) (y :: l)) a t = _
    rw [ih y _ h1, set_vm_root_wr ar a t h0]
    simp only [bind_tc_eq, Std.bind_assoc, bind_ok]
    rfl

end
end Fl4ProofsA64.P1

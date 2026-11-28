/-
P1 (aarch64, gen 55): **retype at function level for the tree** — `insert_new_cap`, the `create_new_objects` loop
building gen 54's `RetypeDeltaA`, `create_object`'s cap shapes, and `untyped::retype` (no reset) keeping `TreeA`.
Each piece names the x86 lemma it mirrors.

* **Cap shapes** (x86 UntypedRetype `newCapOf` / `create_object_eq`, UntypedLoop `ptrF_newCap` / `physF_newCap` /
  `sizeF_newCap` / `newCap_range` / `isUt_newCap`): `newCapA n base us dev` (the cap `objects::create_object`
  returns for A64 type number `n`, objects.rs:447–474 and the arch `create_arch_object`; numbering
  `fl4_abi::consts::object`), `zA n us` (`objects::object_size`'s value), `object_size_eqA` / `object_size_lt`,
  **`create_object.pureA`** (every type but `Tcb` (1), `ArmVcpu` (12), `ArmHighVSpace` (14) writes nothing and
  returns `newCapA`), `newCapA_ptr` / `newCapA_phys` / `newCapA_size` / `newCapA_range` / `newCapA_ut`,
  `newCapA_encWf`.
* **`cdt.insert_new_cap.lr`** (x86 has it inside `NullKeep.ins` / `loop_step`; A64 mirror of gen 48's
  `insert_with_cap.lr` without `set_untyped_cap_as_full`, cdt.rs:187–196: the new slot's `PREV` = parent,
  `NEXT` = parent's old `NEXT` `N`, flags revocable / first-badged, `N.PREV` = slot, parent's `NEXT` = slot) and
  **`cdt.insert_new_cap.lkT`**: `MdbLk` at `insG src dest G` and `Mdb.MdbOK` at `update par dest (some src)`
  (x86 `loop_step`'s `MdbLinks` part; `MdbOK.insert` with `InsCase` left).
* `desc_upd_src` (x86 UntypedLoop `desc_insG_true`).
* **The loop** (x86 `LoopInv` / `loop_step` / `create_loop_rel`, MDB part only): `LoopA` (after `i` objects: the
  link invariant and tree at some ghost, `src` a member, old slots as at `s1`, the first `i` new slots holding
  `cj j`, the descent relation grown by `i` children of `src`); `LoopA.keep` (an `OSKeep` step, i.e. a
  `create_object` that writes no `OS` slot); `LoopA.step` (one `insert_new_cap`);
  **`objects.create_new_objects_loop.loopA`**. The `create_object` step is the case hypothesis `hCO` (returns
  `cj j`, keeps every `OS` word): `create_object.pureA` discharges it for 12 of the 15 types
  (`create_object.pureCO`); for `Tcb` / `ArmVcpu` / `ArmHighVSpace` (state written: TCB context, VCPU, high
  VSpace) it is the caller's (the x86 loop excludes TCBs the same way, `create_loop_rel`'s `hn`).
* **`untyped.retype.tree`** (the `reset = false` path; x86 `utinv_retype` assembled): from `TreeA` at the start,
  the source an `Untyped p sb fi dev` slot, the decode's size checks as case hypotheses (`fi < 2^sb`,
  `p + fi ≤ base`, `base + len·2^z ≤ p + 2^sb`, `z < 64`), the destination slots null `OS` slots, distinct and
  canonical, and `hCO` — `TreeA` at the end at the grown ghost; the gen-54 `RetypeDeltaA` is built here
  (`RetypeDeltaA.utinv`).

Not here (still owed): the reset path, `OSOK` / `WinOK` where `OS` grows (new CNode / TCB slots), the frame of
`create_object` for `Tcb` / `ArmVcpu` / `ArmHighVSpace`, `RngOneA64` / `KindA` along retype.
* **Gen 60, the one proof of each run**: `objects.create_new_objects_loop.genJK` (the loop for an invariant `J`
  before and `K` after each `create_object`; `loopA` here, MdbTreeK's `inv` and MdbUZL's `invZ` are instances) and
  `untyped.retype.genJK` (the only unfolding of `untyped::retype` (no reset): invariants indexed by the state after
  the source's rewrite, `RtSrc`, with `RtSrc.facts` / `RtSrc.lk`); `untyped.retype.genFG` (an invariant `I` and an
  extra invariant `Zq`: MdbTreeN's `gen`, MdbVUR's `genF`, MdbUZL's `genFZ`); `untyped.retype.treeG` (`tree` with
  `Zq := True` and MdbUZL's `treeZ`); helpers `spec_andL`, `MdbLk.nxG`, `cdt.insert_new_cap.capwG` / `.zqW`.

No named premise; new definitions and theorems only (the hypotheses above are case hypotheses of the callers).
-/
import Fl4ProofsA64.P1.MdbTreeR
import Fl4ProofsA64.P1.MdbTreeF
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## The new caps -/

theorem u64_eq_iffA (x y : U64) : x = y ↔ x.val = y.val := ⟨congrArg _, UScalar.eq_of_val_eq⟩

theorem wa_comm (x y : U64) : wa x y = wa y x :=
  UScalar.eq_of_val_eq (by rw [wa_val, wa_val, Nat.add_comm])

/-- The cap `create_object` returns for the A64 type number `n` (x86 `newCapOf`). -/
def newCapA (n : Nat) (base us : U64) (dev : Bool) : capability.Cap :=
  if n = 0 then .Untyped base us 0#u64 dev
  else if n = 1 then .Thread base
  else if n = 2 then .Endpoint base 0#u64 true true true true
  else if n = 3 then .Notification base 0#u64 true true
  else if n = 4 then .CNode base us 0#u64 0#u64
  else if n = 5 then .SchedContext base us
  else if n = 6 then .Reply base true
  else if n = 8 then .Pml4 base false 0#u64
  else if n = 9 then .Frame base .Small 3#u64 dev false false 0#u64 0#u64
  else if n = 10 then .Frame base .Large 3#u64 dev false false 0#u64 0#u64
  else if n = 11 then .PageTable base false 0#u64 0#u64
  else if n = 12 then .Vcpu base
  else if n = 13 then .Ept base 0#u64 false 0#u64 0#u64
  else if n = 14 then .HighVSpace base false 0#u64
  else .Frame base .Huge 3#u64 dev false false 0#u64 0#u64

/-- `objects::object_size`'s value for the A64 type number `n < 15`. -/
def zA (n : Nat) (us : U64) : U64 :=
  if n = 0 then us
  else if n = 1 then 12#u64
  else if n = 2 then 4#u64
  else if n = 3 then 6#u64
  else if n = 4 then wa us 5#u64
  else if n = 5 then us
  else if n = 6 then 5#u64
  else if n = 7 then 30#u64
  else if n = 8 then 12#u64
  else if n = 9 then 12#u64
  else if n = 10 then 21#u64
  else if n = 11 then 12#u64
  else if n = 12 then 12#u64
  else 13#u64

theorem object_size_eqA (nt us : U64) (hn : nt.val < 15) :
    objects.object_size nt us = ok (some (zA nt.val us)) := by
  unfold objects.object_size zA
  simp only [fl4_abi.consts.object.Tcb, fl4_abi.consts.object.Endpoint, fl4_abi.consts.object.Notification,
    fl4_abi.consts.object.CapTable, fl4_abi.consts.object.Untyped, fl4_abi.consts.object.SchedContext,
    fl4_abi.consts.object.Reply, fl4_abi.consts.object.ArmSmallPage, fl4_abi.consts.object.ArmLargePage,
    fl4_abi.consts.object.ArmHugePage, fl4_abi.consts.object.ArmPageTable, fl4_abi.consts.object.ArmVSpace,
    fl4_abi.consts.object.ArmVcpu, fl4_abi.consts.object.ArmStage2VSpace, fl4_abi.consts.object.ArmHighVSpace,
    fl4_abi.consts.bits.TCB, fl4_abi.consts.bits.ENDPOINT, fl4_abi.consts.bits.NOTIFICATION,
    fl4_abi.consts.bits.SLOT, fl4_abi.consts.bits.REPLY, fl4_abi.consts.bits.VCPU,
    fl4_abi.consts.bits.STAGE2_VSPACE, fl4_abi.consts.bits.HIGH_VSPACE, u64_eq_iffA, lift, bind_ok,
    wa_comm 5#u64 us]
  generalize nt.val = n at *
  interval_cases n <;> simp

theorem object_size_lt {nt us z : U64} (h : objects.object_size nt us = ok (some z)) : nt.val < 15 := by
  by_contra hn
  unfold objects.object_size at h
  simp only [fl4_abi.consts.object.Tcb, fl4_abi.consts.object.Endpoint, fl4_abi.consts.object.Notification,
    fl4_abi.consts.object.CapTable, fl4_abi.consts.object.Untyped, fl4_abi.consts.object.SchedContext,
    fl4_abi.consts.object.Reply, fl4_abi.consts.object.ArmSmallPage, fl4_abi.consts.object.ArmLargePage,
    fl4_abi.consts.object.ArmHugePage, fl4_abi.consts.object.ArmPageTable, fl4_abi.consts.object.ArmVSpace,
    fl4_abi.consts.object.ArmVcpu, fl4_abi.consts.object.ArmStage2VSpace, fl4_abi.consts.object.ArmHighVSpace,
    u64_eq_iffA] at h
  generalize nt.val = n at *
  have : n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 5 ∧ n ≠ 6 ∧ n ≠ 7 ∧ n ≠ 8 ∧ n ≠ 9 ∧ n ≠ 10 ∧ n ≠ 11 ∧
    n ≠ 12 ∧ n ≠ 13 ∧ n ≠ 14 := by omega
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := this
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14] at h
  try exact absurd (okinj h) (by simp)

/-- **`create_object` for every type but `Tcb` / `ArmVcpu` / `ArmHighVSpace`** writes nothing and returns
`newCapA` (x86 `create_object_eq`). -/
theorem create_object.pureA {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (nt base us : U64) (dev : Bool)
    (hn : nt.val < 15) (h1 : nt.val ≠ 1) (h12 : nt.val ≠ 12) (h14 : nt.val ≠ 14) :
    objects.create_object st ar s a nt base us dev = ok (newCapA nt.val base us dev, s, a) := by
  unfold objects.create_object objects.create_arch_object newCapA
  simp only [fl4_abi.consts.object.Tcb, fl4_abi.consts.object.Endpoint, fl4_abi.consts.object.Notification,
    fl4_abi.consts.object.CapTable, fl4_abi.consts.object.Untyped, fl4_abi.consts.object.SchedContext,
    fl4_abi.consts.object.Reply, fl4_abi.consts.object.ArmSmallPage, fl4_abi.consts.object.ArmLargePage,
    fl4_abi.consts.object.ArmPageTable, fl4_abi.consts.object.ArmVSpace,
    fl4_abi.consts.object.ArmVcpu, fl4_abi.consts.object.ArmStage2VSpace, fl4_abi.consts.object.ArmHighVSpace,
    capability.VM_READ_WRITE, u64_eq_iffA]
  generalize nt.val = n at *
  interval_cases n <;> simp_all

theorem ptrA_of {c : capability.Cap} {v : U64} (h : capability.Cap.ptr c = ok v) : ptrA c = v :=
  okinj ((ptrA_eq c).symm.trans h)
theorem sizeA_of {c : capability.Cap} {v : U64} (h : objects.cap_size_bits c = ok v) : sizeA c = v :=
  okinj ((sizeA_eq c).symm.trans h)
theorem physA_of {c : capability.Cap} {v : Bool} (h : objects.cap_is_physical c = ok v) : physA c = v :=
  okinj ((physA_eq c).symm.trans h)

theorem ite_propA {α : Type _} {P : α → Prop} {c : Prop} [Decidable c] {a b : α} (ha : c → P a)
    (hb : ¬ c → P b) : P (ite c a b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

/-- The cases of `newCapA` (x86 `newCapOf_ind`). -/
theorem newCapA_ind (P : capability.Cap → Prop) (n : Nat) (base us : U64) (dev : Bool)
    (h0 : n = 0 → P (.Untyped base us 0#u64 dev)) (h1 : P (.Thread base))
    (h2 : P (.Endpoint base 0#u64 true true true true)) (h3 : P (.Notification base 0#u64 true true))
    (h4 : P (.CNode base us 0#u64 0#u64)) (h5 : P (.SchedContext base us)) (h6 : P (.Reply base true))
    (h8 : P (.Pml4 base false 0#u64)) (h9 : P (.Frame base .Small 3#u64 dev false false 0#u64 0#u64))
    (h10 : P (.Frame base .Large 3#u64 dev false false 0#u64 0#u64)) (h11 : P (.PageTable base false 0#u64 0#u64))
    (h12 : P (.Vcpu base)) (h13 : P (.Ept base 0#u64 false 0#u64 0#u64)) (h14 : P (.HighVSpace base false 0#u64))
    (h7 : P (.Frame base .Huge 3#u64 dev false false 0#u64 0#u64)) : P (newCapA n base us dev) := by
  unfold newCapA
  exact ite_propA h0 fun _ => ite_propA (fun _ => h1) fun _ => ite_propA (fun _ => h2) fun _ =>
    ite_propA (fun _ => h3) fun _ => ite_propA (fun _ => h4) fun _ => ite_propA (fun _ => h5) fun _ =>
    ite_propA (fun _ => h6) fun _ => ite_propA (fun _ => h8) fun _ => ite_propA (fun _ => h9) fun _ =>
    ite_propA (fun _ => h10) fun _ => ite_propA (fun _ => h11) fun _ => ite_propA (fun _ => h12) fun _ =>
    ite_propA (fun _ => h13) fun _ => ite_propA (fun _ => h14) fun _ => h7

theorem newCapA_ptr (n : Nat) (base us : U64) (dev : Bool) : ptrA (newCapA n base us dev) = base := by
  apply newCapA_ind (fun c => ptrA c = base) <;> intros <;> exact ptrA_of rfl

theorem newCapA_phys (n : Nat) (base us : U64) (dev : Bool) : physA (newCapA n base us dev) = true := by
  apply newCapA_ind (fun c => physA c = true) <;> intros <;> exact physA_of rfl

theorem newCapA_size {n : Nat} (hn : n < 15) (base us : U64) (dev : Bool) :
    sizeA (newCapA n base us dev) = zA n us := by
  interval_cases n <;> simp only [newCapA, zA] <;> simp <;>
    exact sizeA_of (by simp [objects.cap_size_bits, capability.FrameSize.bits, fl4_abi.consts.bits.TCB,
      fl4_abi.consts.bits.ENDPOINT, fl4_abi.consts.bits.NOTIFICATION, fl4_abi.consts.bits.SLOT,
      fl4_abi.consts.bits.REPLY, fl4_abi.consts.bits.VCPU, fl4_abi.consts.bits.STAGE2_VSPACE,
      fl4_abi.consts.bits.HIGH_VSPACE])

theorem newCapA_ut {n : Nat} {base us : U64} {dev : Bool} (h : isUtA (newCapA n base us dev) = true) :
    n = 0 ∧ newCapA n base us dev = .Untyped base us 0#u64 dev := by
  revert h
  apply newCapA_ind (fun c => isUtA c = true → n = 0 ∧ c = .Untyped base us 0#u64 dev) <;> intros <;>
    first | exact ⟨by assumption, rfl⟩ | (simp [isUtA] at *)

/-- **The range of a new cap** (x86 `newCap_range`): `2^z` bytes from `base`. -/
theorem newCapA_range {n : Nat} (hn : n < 15) (base us : U64) (dev : Bool) (hz : (zA n us).val < 64)
    (hb : base.val + 2 ^ (zA n us).val ≤ 2 ^ 64) :
    baseA (newCapA n base us dev) = base.val ∧
      topA (newCapA n base us dev) = base.val + 2 ^ (zA n us).val - 1 := by
  refine ⟨by unfold baseA; rw [newCapA_ptr], ?_⟩
  unfold topA
  rw [newCapA_ptr, newCapA_size hn, wa_val, mskA_val hz]
  have h1 : 1 ≤ 2 ^ (zA n us).val := Nat.one_le_two_pow
  rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem canon_zero : CapRt.Canonical 0#u64 := Or.inl fun j hj _ => by simp

/-- The new caps are encodable (x86 `newCap_encWf`). -/
theorem newCapA_encWf (n : Nat) (base us : U64) (dev : Bool) (hb : CapRt.Canonical base) (hus : us.val < 64) :
    CapRt.EncWf (newCapA n base us dev) := by
  apply newCapA_ind CapRt.EncWf <;> intros <;> simp only [CapRt.EncWf] <;>
    first
      | exact hb
      | exact ⟨hb, hus⟩
      | exact ⟨hb, hus, by simp, by simp⟩
      | exact ⟨hb, by simp, by simp, canon_zero⟩
      | exact ⟨hb, by simp, canon_zero⟩
      | exact ⟨hb, by simp, by simp, by simp⟩

theorem newCapA_ne (n : Nat) (base us : U64) (dev : Bool) : newCapA n base us dev ≠ .Null := by
  apply newCapA_ind (fun c => c ≠ .Null) <;> intros <;> exact fun h => by cases h

/-! ## `insert_new_cap` -/

section ins
variable {OS : Set U64}

set_option maxHeartbeats 2000000 in
/-- **`insert_new_cap`'s links and caps** (module docstring; mirror of `insert_with_cap.lr`). -/
theorem cdt.insert_new_cap.lr (hO : OSOK T Ω Sg OS) {s : S} {pv nx : U64 → U64} (hL : LR st OS s pv nx)
    {src dest : U64} {nc : capability.Cap} (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest)
    (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hnN : nx src ≠ 0#u64 → nx src ∈ OS) :
    cdt.insert_new_cap st s src dest nc ⦃ s' => LR st OS s'
      (fun z => if nx src ≠ 0#u64 ∧ z = nx src then dest else if z = dest then src else pv z)
      (fun z => if z = src then dest else if z = dest then nx src else nx z) ∧
      capA st s' dest = nc ∧ (∀ y ∈ OS, y ≠ dest → capA st s' y = capA st s y) ⦄ := by
  have cnN : obj.sext48 (nx src) = ok (nx src) := by rw [← (hL src hsrc).2]; exact nxA_can s src
  unfold cdt.insert_new_cap
  rw [next_eq, bind_ok, (hL src hsrc).2]
  obtain ⟨w0, w1, he, hr⟩ := CapRt.decode_encode nc hw
  rw [set_cap_eq he, bind_ok]
  have L2 := hL.wr2 hO hd (w0 := w0) (w1 := w1)
  have C2 : capA st (L.wr (L.wr s dest w0) (wa dest 8#u64) w1) dest = nc ∧
      ∀ y ∈ OS, y ≠ dest → capA st (L.wr (L.wr s dest w0) (wa dest 8#u64) w1) y = capA st s y :=
    ⟨capA_wr2_self hO hd hr, fun y hy n2 => capA_wr2_other hO hd hy n2⟩
  generalize L.wr (L.wr s dest w0) (wa dest 8#u64) w1 = s2 at L2 C2 ⊢
  rw [set_prev_eq, bind_ok]
  have L3 := L2.prev hO hd src
  refine WP.spec_bind (set_nf_spec _ dest _ true true) ?_
  rintro s4 ⟨w4, rfl, hw4⟩
  have L4 := L3.nw hO hd hw4 cnN
  have C4 := ((CK.refl (st := st) (OS := OS) s2).p hO hd src).n hO hd w4
  have fin : ∀ s' : S, CK st OS s2 s' →
      capA st s' dest = nc ∧ (∀ y ∈ OS, y ≠ dest → capA st s' y = capA st s y) := fun s' hc =>
    ⟨(hc dest hd).trans C2.1, fun y hy n2 => (hc y hy).trans (C2.2 y hy n2)⟩
  simp only [obj.Slot.is_null, bind_ok]
  split
  · rename_i hn0
    have hN0 : nx src = 0#u64 := by simpa using hn0
    simp only [bind_ok]
    rw [set_next_eq, WP.spec_ok]
    refine ⟨(L4.nw hO hsrc (link_bits _ dest) hdc).congr (fun z _ => ?_) (fun _ _ => rfl), fin _ (C4.n hO hsrc _)⟩
    simp [hN0]
  · rename_i hn0
    have hN0 : nx src ≠ 0#u64 := by simpa using hn0
    rw [set_prev_eq, bind_ok, set_next_eq, WP.spec_ok]
    refine ⟨((L4.prev hO (hnN hN0) dest).nw hO hsrc (link_bits _ dest) hdc).congr (fun z _ => ?_)
      (fun _ _ => rfl), fin _ ((C4.p hO (hnN hN0) dest).n hO hsrc _)⟩
    simp only [ne_eq, hN0, not_false_eq_true, true_and]

variable {G : List (List U64)} {par : U64 → Option U64}

set_option maxHeartbeats 1000000 in
/-- **`insert_new_cap` keeps the link invariant and the tree** (x86 `loop_step`'s `MdbLinks` / `MdbOK` part):
the ghost `insG src dest G`, the parent map `update par dest (some src)`. -/
theorem cdt.insert_new_cap.lkT (hO : OSOK T Ω Sg OS) {s : S} (hM : MdbLk st OS G s) (hT : Mdb.MdbOK par G)
    {src dest : U64} {nc : capability.Cap} (hsrc : src ∈ G.flatten) (hd : dest ∈ OS)
    (hd0 : capA st s dest = .Null) (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hnc : nc ≠ .Null) :
    cdt.insert_new_cap st s src dest nc ⦃ s' => MdbLk st OS (insG src dest G) s' ∧
      Mdb.MdbOK (Function.update par dest (some src)) (insG src dest G) ∧ capA st s' dest = nc ∧
      (∀ y ∈ OS, y ≠ dest → capA st s' y = capA st s y) ⦄ := by
  have h0 : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have os := inOS src hsrc
  have dG : dest ∉ G.flatten := fun hm => ((hM.members dest).1 hm).2 hd0
  have hsd : src ≠ dest := fun e => dG (e ▸ hsrc)
  have hNm : NxA st s src ≠ 0#u64 → NxA st s src ∈ G.flatten := F.nxm _ hsrc
  have hNd : NxA st s src ≠ dest := fun e => by
    have h1 : NxA st s src ≠ 0#u64 := fun e0 => h0 dest hd (e ▸ e0)
    exact dG (e ▸ hNm h1)
  refine WP.spec_mono (cdt.insert_new_cap.lr hO (LR.self s) os hd hsd hdc hw (fun h => inOS _ (hNm h))) ?_
  rintro s' ⟨hL, ed, ek⟩
  refine ⟨hM.ins h0 hsrc hd hd0 (by rw [ed]; exact hnc) (fun y hy hyd => by rw [ek y hy hyd]) ?_ ?_ ?_
    (fun hN => ?_) (fun y hy h1 h2 => ?_) (fun y hy h1 h2 => ?_), by rw [insG_eq]; exact hT.insert hsrc dG (Or.inl rfl),
    ed, ek⟩
  · rw [(hL src os).2]; simp
  · rw [(hL dest hd).1]; simp [hNd.symm]
  · rw [(hL dest hd).2]; simp [hsd.symm]
  · rw [(hL _ (inOS _ (hNm hN))).1]; simp [hN]
  · rw [(hL y hy).2]; simp [h1, h2]
  · rw [(hL y hy).1]; simp [h1, h2]

end ins

/-- **Descent after adding a child `d` of `src`** (x86 `desc_insG_true`). -/
theorem desc_upd_src {par : U64 → Option U64} {src d : U64} (hpd : ∀ z, par z ≠ some d) (hdn : par d = none)
    (hsd : src ≠ d) (y x : U64) :
    Mdb.Desc (Function.update par d (some src)) y x ↔
      Mdb.Desc par y x ∨ (y = d ∧ (x = src ∨ Mdb.Desc par src x)) := by
  rw [Mdb.desc_update_iff hpd hdn (fun e => hsd (Option.some_injective _ e))]
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨rfl, ?_⟩
      rcases h with e | ⟨p, e, h⟩
      · exact Or.inl (Option.some_injective _ e).symm
      · obtain rfl := Option.some_injective _ e; exact Or.inr h
  · rintro (h | ⟨rfl, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨rfl, ?_⟩
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr ⟨src, rfl, h⟩

/-! ## The loop -/

/-- **The loop invariant after `i` objects** (x86 `LoopInv`, MDB part; module docstring). -/
def LoopA (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (par0 : U64 → Option U64) (s1 : S)
    (src : U64) (dslot : Nat → U64) (cj : Nat → capability.Cap) (s : S) (i : Nat) : Prop :=
  ∃ G : List (List U64), ∃ par : U64 → Option U64, MdbLk st OS G s ∧ Mdb.MdbOK par G ∧ src ∈ G.flatten ∧
    (∀ x ∈ OS, (∀ j, j < i → x ≠ dslot j) → capA st s x = capA st s1 x) ∧
    (∀ j, j < i → capA st s (dslot j) = cj j) ∧
    (∀ y x, Mdb.Desc par y x ↔ Mdb.Desc par0 y x ∨
      ∃ j, j < i ∧ y = dslot j ∧ (x = src ∨ Mdb.Desc par0 src x))

section loop
variable {OS : Set U64} {par0 : U64 → Option U64} {s1 : S} {src : U64} {dslot : Nat → U64}
  {cj : Nat → capability.Cap}

/-- The start: nothing inserted yet. -/
theorem LoopA.start {G : List (List U64)} (hM : MdbLk st OS G s1) (hT : Mdb.MdbOK par0 G) (hsrc : src ∈ G.flatten) :
    LoopA st OS par0 s1 src dslot cj s1 0 :=
  ⟨G, par0, hM, hT, hsrc, fun _ _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero j),
    fun y x => ⟨Or.inl, fun h => h.elim id fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero j)⟩⟩

/-- **A step writing no `OS` word keeps the invariant** (`create_object`). -/
theorem LoopA.keep {s s' : S} {i : Nat} (h : LoopA st OS par0 s1 src dslot cj s i) (hdO : ∀ j, j < i → dslot j ∈ OS)
    (k : OSKeep st OS s s') : LoopA st OS par0 s1 src dslot cj s' i := by
  obtain ⟨G, par, hM, hT, hs, h1, h2, h3⟩ := h
  refine ⟨G, par, hM.keep (fun x hx => ⟨(k x hx).2.2.1, (k x hx).2.2.2⟩) (fun x hx => by rw [k.capA hx]), hT, hs,
    fun x hx hn => (k.capA hx).trans (h1 x hx hn), fun j hj => (k.capA (hdO j hj)).trans (h2 j hj), h3⟩

/-- **One `insert_new_cap`** (x86 `loop_step`). -/
theorem LoopA.step (hO : OSOK T Ω Sg OS) {s : S} {i w : Nat} (hi : i < w)
    (h : LoopA st OS par0 s1 src dslot cj s i) (hdO : ∀ j, j < w → dslot j ∈ OS)
    (hdn : ∀ j, j < w → capA st s1 (dslot j) = .Null) (hdc : ∀ j, j < w → obj.sext48 (dslot j) = ok (dslot j))
    (hinj : ∀ j l, j < w → l < w → dslot j = dslot l → j = l) (hsn : ∀ j, j < w → src ≠ dslot j)
    (hwf : ∀ j, j < w → CapRt.EncWf (cj j)) (hcn : ∀ j, j < w → cj j ≠ .Null) :
    cdt.insert_new_cap st s src (dslot i) (cj i) ⦃ s' => LoopA st OS par0 s1 src dslot cj s' (i + 1) ⦄ := by
  obtain ⟨G, par, hM, hT, hs, h1, h2, h3⟩ := h
  have hne : ∀ j, j < i → dslot i ≠ dslot j := fun j hj e => by
    have := hinj i j hi (by omega) e; omega
  have hd0 : capA st s (dslot i) = .Null := by rw [h1 _ (hdO i hi) hne]; exact hdn i hi
  have dG : dslot i ∉ G.flatten := fun hm => ((hM.members _).1 hm).2 hd0
  refine WP.spec_mono (cdt.insert_new_cap.lkT hO hM hT hs (hdO i hi) hd0 (hdc i hi) (hwf i hi) (hcn i hi)) ?_
  rintro s' ⟨hM', hT', ed, ek⟩
  have hsOS : src ∈ OS := ((hM.members src).1 hs).1
  refine ⟨_, _, hM', hT', ?_, fun x hx hn => ?_, fun j hj => ?_, fun y x => ?_⟩
  · refine (hM'.members src).2 ⟨hsOS, ?_⟩
    rw [ek src hsOS (hsn i hi)]; exact ((hM.members src).1 hs).2
  · rw [ek x hx (hn i (by omega))]; exact h1 x hx fun j hj => hn j (by omega)
  · by_cases hji : j = i
    · subst hji; exact ed
    · rw [ek _ (hdO j (by omega)) (fun e => hji (hinj j i (by omega) hi e))]; exact h2 j (by omega)
  · have hpd : ∀ z, par z ≠ some (dslot i) := fun z e => dG (hT.par_mem z _ e).2
    have hdn' : par (dslot i) = none := by
      cases e : par (dslot i) with
      | none => rfl
      | some q => exact absurd (hT.par_mem _ q e).1 dG
    have hsrcd : ∀ x, Mdb.Desc par src x ↔ Mdb.Desc par0 src x := fun x => by
      rw [h3]
      constructor
      · rintro (h | ⟨j, hj, e, -⟩)
        · exact h
        · exact absurd e (hsn j (by omega))
      · exact Or.inl
    rw [desc_upd_src hpd hdn' (hsn i hi), h3, hsrcd]
    constructor
    · rintro ((h | ⟨j, hj, e, hx⟩) | ⟨e, hx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, e, hx⟩
      · exact Or.inr ⟨i, by omega, e, hx⟩
    · rintro (h | ⟨j, hj, e, hx⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hji : j = i
        · subst hji; exact Or.inr ⟨e, hx⟩
        · exact Or.inl (Or.inr ⟨j, by omega, e, hx⟩)

end loop

theorem spec_exA {α : Type _} {m : Result α} {P : α → Prop} (h : m ⦃ r => P r ⦄) : ∃ v, m = ok v ∧ P v := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

theorem u64_ofNatA (x : U64) (n : Nat) (h : x.val = n) : x = ⟨BitVec.ofNat 64 n⟩ := by
  apply UScalar.eq_of_val_eq
  have : x.val < 2 ^ 64 := by have := x.hBounds; simpa [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits] using this
  show x.val = (BitVec.ofNat 64 n).toNat
  simp; omega

/-- The `j`-th object's base. -/
def bjA (base z : U64) (j : Nat) : U64 := ⟨BitVec.ofNat 64 (base.val + j * 2 ^ z.val)⟩

/-- The `j`-th destination slot. -/
def djA (dcn off : U64) (j : Nat) : U64 := slotIdx dcn (wa off ⟨BitVec.ofNat 64 j⟩)

theorem bjA_val {base z : U64} {j : Nat} (h : base.val + j * 2 ^ z.val < 2 ^ 64) :
    (bjA base z j).val = base.val + j * 2 ^ z.val := by
  show (BitVec.ofNat 64 _).toNat = _; simp; omega

theorem spec_andL {α : Type _} {m : Result α} {P Q : α → Prop} (h1 : m ⦃ r => P r ⦄) (h2 : m ⦃ r => Q r ⦄) :
    m ⦃ r => P r ∧ Q r ⦄ := by
  obtain ⟨v, hv, hp⟩ := spec_exA h1
  rw [hv, WP.spec_ok] at h2 ⊢
  exact ⟨hp, h2⟩

set_option maxHeartbeats 2000000 in
/-- **`create_new_objects`' loop, the one proof** (gen 60): an invariant `J` before each `create_object` and `K`
after it — `create_object` of object `j` from `J · j` returns `cj j` and gives `K · j`, each `insert_new_cap` from
`K · i` gives `J · (i + 1)`. `loopA` (gen 55), `inv` (gen 56) and `invZ` (gen 59) are its instances. -/
theorem objects.create_new_objects_loop.genJK {A : Type _} (ar : machine.Arch A) {cj : Nat → capability.Cap}
    {J K : S → Nat → Prop} (t src dcn off w base us z : U64) (dev : Bool)
    (hz : z.val < 64) (hfit : base.val + w.val * 2 ^ z.val ≤ 2 ^ 64)
    (hCO : ∀ (s : S) (a : A) (j : Nat), j < w.val → J s j →
      objects.create_object st ar s a t (bjA base z j) us dev ⦃ r => r.1 = cj j ∧ K r.2.1 j ⦄)
    (hstep : ∀ (s : S) (i : Nat), i < w.val → K s i →
      cdt.insert_new_cap st s src (djA dcn off i) (cj i) ⦃ s' => J s' (i + 1) ⦄)
    (s : S) (a : A) (hinv : J s 0) :
    objects.create_new_objects_loop st ar s a t src dcn off w base us dev z 0#u64 ⦃ r => J r.1 w.val ⦄ := by
  unfold objects.create_new_objects_loop
  have hk1 : 1 ≤ 2 ^ z.val := Nat.one_le_two_pow
  have h63 := and63_of_lt hz
  refine loop.spec_decr_nat (measure := fun x => w.val - x.2.2.val)
    (inv := fun x => x.2.2.val ≤ w.val ∧ J x.1 x.2.2.val) _ _ _ ?_ ⟨by simp, hinv⟩
  rintro ⟨s2, a2, i⟩ ⟨hiw, hI⟩
  simp only at hiw hI ⊢
  unfold objects.create_new_objects_loop.body
  by_cases hit : i < w
  · rw [if_pos hit]
    have hit' : i.val < w.val := hit
    simp only [lift, bind_ok]
    have hik : (i.val + 1) * 2 ^ z.val ≤ w.val * 2 ^ z.val := Nat.mul_le_mul_right _ hit'
    rw [Nat.add_mul, Nat.one_mul] at hik
    obtain ⟨i2, hi2, hv2, -⟩ := spec_exA (U64.ShiftLeft_spec i (z &&& 63#u64) (by rw [h63]; simpa using hz))
    rw [hi2]; simp only [lift, bind_ok]
    have hi2v : i2.val = i.val * 2 ^ z.val := by
      rw [hv2, h63, Nat.shiftLeft_eq]
      simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
    have hi3 : wa base i2 = bjA base z i.val := by
      apply u64_ofNatA
      rw [wa_val, hi2v]; exact Nat.mod_eq_of_lt (by omega)
    rw [hi3]
    refine WP.spec_bind (hCO s2 a2 i.val hit' hI) ?_
    rintro ⟨c, s3, a3⟩ ⟨hc, hK3⟩
    try dsimp only at hc hK3
    subst hc
    try dsimp only
    try simp only [lift, bind_ok]
    refine WP.spec_bind (slot_index_in dcn _) ?_
    rintro sl rfl
    have hsl : slotIdx dcn (wa off i) = djA dcn off i.val := by
      unfold djA; rw [← u64_ofNatA i i.val rfl]
    rw [hsl]
    refine WP.spec_bind (hstep s3 i.val hit' hK3) ?_
    intro s4 hs4
    obtain ⟨i5, h5e, h5v⟩ := spec_exA (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h5e, bind_ok, WP.spec_ok]
    have h5 : i5.val = i.val + 1 := by simpa using h5v
    try dsimp only
    have H1 : i5.val ≤ w.val := by omega
    have H2 : J s4 i5.val := by rw [h5]; exact hs4
    have H3 : w.val - i5.val < w.val - i.val := by omega
    first | exact ⟨⟨H1, H2⟩, H3⟩ | exact ⟨H1, H2, H3⟩
  · rw [if_neg hit, WP.spec_ok]
    have : i.val = w.val := by have : ¬ i.val < w.val := hit; omega
    rw [this] at hI
    exact hI

/-- **`create_new_objects`' loop** (x86 `create_loop_rel`, MDB part): from `LoopA` at `0`, `LoopA` at `w` —
each `create_object` given by `hCO` (it returns `cj j` and writes no `OS` word; `create_object.pureCO`). -/
theorem objects.create_new_objects_loop.loopA {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {par0 : U64 → Option U64} {s1 : S} {cj : Nat → capability.Cap} (t src dcn off w base us z : U64) (dev : Bool)
    (hz : z.val < 64) (hfit : base.val + w.val * 2 ^ z.val ≤ 2 ^ 64)
    (hCO : ∀ (s : S) (a : A) (j : Nat), j < w.val →
      objects.create_object st ar s a t (bjA base z j) us dev ⦃ r => r.1 = cj j ∧ OSKeep st OS s r.2.1 ⦄)
    (hdO : ∀ j, j < w.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < w.val → capA st s1 (djA dcn off j) = .Null)
    (hdc : ∀ j, j < w.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < w.val → l < w.val → djA dcn off j = djA dcn off l → j = l)
    (hsn : ∀ j, j < w.val → src ≠ djA dcn off j)
    (hwf : ∀ j, j < w.val → CapRt.EncWf (cj j)) (hcn : ∀ j, j < w.val → cj j ≠ .Null)
    (s : S) (a : A) (hinv : LoopA st OS par0 s1 src (djA dcn off) cj s 0) :
    objects.create_new_objects_loop st ar s a t src dcn off w base us dev z 0#u64 ⦃ r =>
      LoopA st OS par0 s1 src (djA dcn off) cj r.1 w.val ⦄ :=
  objects.create_new_objects_loop.genJK ar t src dcn off w base us z dev hz hfit
    (fun s a j hj h => WP.spec_mono (hCO s a j hj) fun r hr => ⟨hr.1, h.keep (fun l hl => hdO l (by omega)) hr.2⟩)
    (fun s i hi h => LoopA.step hO hi h hdO hdn hdc hinj hsn hwf hcn) s a hinv

/-- **The pure `create_object` instance of `hCO`** (types other than `Tcb` / `ArmVcpu` / `ArmHighVSpace`). -/
theorem create_object.pureCO {A : Type _} (ar : machine.Arch A) {OS : Set U64} (t us base z : U64) (dev : Bool)
    (hn : t.val < 15) (h1 : t.val ≠ 1) (h12 : t.val ≠ 12) (h14 : t.val ≠ 14) :
    ∀ (s : S) (a : A) (j : Nat), objects.create_object st ar s a t (bjA base z j) us dev ⦃ r =>
      r.1 = newCapA t.val (bjA base z j) us dev ∧ OSKeep st OS s r.2.1 ⦄ := fun s a j => by
  rw [create_object.pureA ar s a t _ us dev hn h1 h12 h14, WP.spec_ok]
  exact ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-! ## Retype (no reset): the one function-level proof (gen 60) -/

section rtgen
variable {OS : Set U64}

/-- A member's `NEXT` is null or an `OS` slot (gen 59's `MdbLk.nxOS`). -/
theorem MdbLk.nxG (hO : OSOK T Ω Sg OS) {G : List (List U64)} {s : S} (hM : MdbLk st OS G s) {src : U64}
    (hs : src ∈ G.flatten) : src ∈ OS ∧ (NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) :=
  ⟨((hM.members src).1 hs).1, fun h0 => ((hM.members _).1 ((hM.lkF hO.nz).nxm _ hs h0)).1⟩

/-- **`insert_new_cap` writes only cap-slot words** (gen 59's `cdt.insert_new_cap.capw`; cdt.rs:187–196). -/
theorem cdt.insert_new_cap.capwG (hO : OSOK T Ω Sg OS) {s : S} {src dest : U64} {nc : capability.Cap}
    (hsrc : src ∈ OS) (hd : dest ∈ OS) (hnN : NxA st s src ≠ 0#u64 → NxA st s src ∈ OS) :
    cdt.insert_new_cap st s src dest nc ⦃ s' => WritesIn st s s' (W7.CapW T Ω Sg) ⦄ := by
  unfold cdt.insert_new_cap
  rw [next_eq, bind_ok]
  refine WP.spec_bind (W7.obj.Slot.set_cap.capw (hO.slot dest hd)) fun s1 w1 => ?_
  refine WP.spec_bind (W7.obj.Slot.set_prev.capw (hO.slot dest hd)) fun s2 w2 => ?_
  refine WP.spec_bind (W7.obj.Slot.set_next_flags.capw (hO.slot dest hd)) fun s3 w3 => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s4 => WritesIn st s s4 (W7.CapW T Ω Sg)) ?_ fun s4 w4 => ?_
  · split
    · exact (WP.spec_ok _).2 ((w1.trans1 w2).trans1 w3)
    · rename_i e
      exact WP.spec_mono (W7.obj.Slot.set_prev.capw (hO.slot _ (hnN (by simpa using e)))) fun s' w' =>
        ((w1.trans1 w2).trans1 w3).trans1 w'
  · exact WP.spec_mono (W7.obj.Slot.set_next.capw (hO.slot src hsrc)) fun s' w' => w4.trans1 w'

/-- **An extra invariant kept by cap-slot writes survives `insert_new_cap`** (the `Zq` half of every
bundle-form loop step). -/
theorem cdt.insert_new_cap.zqW (hO : OSOK T Ω Sg OS) {Zq : S → Nat → Prop}
    (hZW : ∀ (s1 s2 : S) (j : Nat), Zq s1 j → WritesIn st s1 s2 (W7.CapW T Ω Sg) → Zq s2 j)
    {s : S} {src dest : U64} {nc : capability.Cap} {j : Nat} (hd : dest ∈ OS)
    (hnx : src ∈ OS ∧ (NxA st s src ≠ 0#u64 → NxA st s src ∈ OS)) (hz : Zq s j) :
    cdt.insert_new_cap st s src dest nc ⦃ s' => Zq s' j ⦄ :=
  WP.spec_mono (cdt.insert_new_cap.capwG hO hnx.1 hd hnx.2) fun _ w => hZW _ _ _ hz w

/-- **The state after the source's free index is rewritten** (untyped.rs:286): the source's two cap words hold an
encoding of `Untyped p sb nfi dev`, `nfi = E − p` whenever `p ≤ b` and `E − p` fits. -/
def RtSrc (st : machine.Store S) [L : LawfulStore st] (s : S) (src p sb : U64) (dev : Bool) (b E : Nat) (s1 : S) :
    Prop :=
  ∃ nfi w0 w1 : U64, (p.val ≤ b → E - p.val < 2 ^ 64 → nfi.val = E - p.val) ∧
    capability.Cap.decode w0 w1 = ok (.Untyped p sb nfi dev) ∧ s1 = L.wr (L.wr s src w0) (wa src 8#u64) w1

theorem RtSrc.facts (hO : OSOK T Ω Sg OS) {s s1 : S} {src p sb : U64} {dev : Bool} {b E : Nat} (hsrc : src ∈ OS)
    (h : RtSrc st s src p sb dev b E s1) :
    ∃ nfi : U64, (p.val ≤ b → E - p.val < 2 ^ 64 → nfi.val = E - p.val) ∧
      capA st s1 src = .Untyped p sb nfi dev ∧ (∀ x ∈ OS, x ≠ src → capA st s1 x = capA st s x) ∧
      (∀ y ∈ OS, L.mem s1 (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s1 (wa y 24#u64) = L.mem s (wa y 24#u64)) ∧
      WritesIn st s s1 (fun b => b = src ∨ b = wa src 8#u64) := by
  obtain ⟨nfi, w0, w1, hv, hd, rfl⟩ := h
  exact ⟨nfi, hv, capA_wr2_self hO hsrc hd, fun x hx hne => capA_wr2_other hO hsrc hx hne,
    set_cap_links (st := st) (s := s) (w0 := w0) (w1 := w1) hO hsrc,
    (writesIn_wr (hO.al0 hsrc)).trans (writesIn_wr (hO.al hsrc (k := 8#u64) (by simp) (by simp)))⟩

theorem RtSrc.lk (hO : OSOK T Ω Sg OS) {s s1 : S} {src p sb : U64} {dev : Bool} {b E : Nat} (hsrc : src ∈ OS)
    (h : RtSrc st s src p sb dev b E s1) {G : List (List U64)} (hM : MdbLk st OS G s)
    (hc0 : capA st s src ≠ .Null) : MdbLk st OS G s1 := by
  obtain ⟨nfi, w0, w1, -, hd, rfl⟩ := h
  exact hM.set_cap hO hsrc hd (fun h => by cases h) hc0

end rtgen

set_option maxHeartbeats 4000000 in
/-- **`untyped::retype` (no reset), the one function-level proof** (gen 60; untyped.rs:266–288): for invariants
`J s1` / `K s1` indexed by the state `s1` after the source's rewrite (`RtSrc`), `J s1 s1 0`, each `create_object`
from `J s1 · j` returning `newCapA` with `K s1 · j`, each `insert_new_cap` from `K s1 · i` giving `J s1 · (i + 1)`
⇒ `Ok` and `J s1 · len` for some such `s1`. Every other retype run is an instance. -/
theorem untyped.retype.genJK {A : Type _} (ar : machine.Arch A) {s : S} (a : A) {src p sb fi : U64} {dev : Bool}
    (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfit : base.val + len.val * 2 ^ (zA nt.val us).val ≤ 2 ^ 64)
    {J K : S → S → Nat → Prop}
    (hCO : ∀ s1 : S, RtSrc st s src p sb dev base.val (base.val + len.val * 2 ^ (zA nt.val us).val) s1 →
      ∀ (s' : S) (a' : A) (j : Nat), j < len.val → J s1 s' j →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ K s1 r.2.1 j ⦄)
    (hstep : ∀ s1 : S, RtSrc st s src p sb dev base.val (base.val + len.val * 2 ^ (zA nt.val us).val) s1 →
      ∀ (s' : S) (i : Nat), i < len.val → K s1 s' i →
      cdt.insert_new_cap st s' src (djA dcn off i) (newCapA nt.val (bjA base (zA nt.val us) i) us device) ⦃ s'' =>
        J s1 s'' (i + 1) ⦄)
    (hstart : ∀ s1 : S, RtSrc st s src p sb dev base.val (base.val + len.val * 2 ^ (zA nt.val us).val) s1 →
      J s1 s1 0) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      ∃ s1 : S, RtSrc st s src p sb dev base.val (base.val + len.val * 2 ^ (zA nt.val us).val) s1 ∧
        J s1 r.2.1 len.val ⦄ := by
  set z := zA nt.val us with hzdef
  unfold untyped.retype
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [object_size_eqA nt us hn]
  simp only [lift, bind_ok, core.option.Option.unwrap_or]
  obtain ⟨tot, htot, hv, -⟩ := spec_exA (U64.ShiftLeft_spec len (z &&& 63#u64)
    (by rw [and63_of_lt hz]; simpa using hz))
  rw [htot, bind_ok, capA_eq, bind_ok, hcs]
  try dsimp only
  try simp only [lift, bind_ok]
  set nfi := core.num.U64.wrapping_sub (wa base tot) p with hnfi
  have hnv : p.val ≤ base.val → base.val + len.val * 2 ^ z.val - p.val < 2 ^ 64 →
      nfi.val = base.val + len.val * 2 ^ z.val - p.val := fun hpb hlt => by
    have hlk : len.val * 2 ^ z.val < 2 ^ 64 := by omega
    have htv : tot.val = len.val * 2 ^ z.val := by
      rw [hv, and63_of_lt hz, Nat.shiftLeft_eq]
      simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
    rw [hnfi, core.num.U64.wrapping_sub_val_eq, wa_val, htv]
    simp [U64.size_def, U64.numBits]; omega
  have w0 : CapRt.EncWf (.Untyped p sb fi dev) := by
    have w := CapRt.decodeF_encWf (L.mem s src).bv (L.mem s (wa src 8#u64)).bv
    have e : CapRt.decodeF (L.mem s src).bv (L.mem s (wa src 8#u64)).bv = .Untyped p sb fi dev := hcs
    rw [e] at w; exact w
  have wN : CapRt.EncWf (.Untyped p sb nfi dev) := w0
  obtain ⟨c0, c1, he, hr⟩ := CapRt.decode_encode _ wN
  rw [set_cap_eq he, bind_ok]
  have H1 : RtSrc st s src p sb dev base.val (base.val + len.val * 2 ^ z.val)
      (L.wr (L.wr s src c0) (wa src 8#u64) c1) := ⟨nfi, c0, c1, hnv, hr, rfl⟩
  unfold objects.create_new_objects
  rw [object_size_eqA nt us hn, bind_ok]
  try dsimp only
  refine WP.spec_bind (objects.create_new_objects_loop.genJK ar
    (cj := fun j => newCapA nt.val (bjA base z j) us device) (J := J _) (K := K _)
    nt src dcn off len base us z device hz hfit (hCO _ H1) (hstep _ H1) _ a (hstart _ H1)) ?_
  rintro ⟨sf, af⟩ hJ
  exact (WP.spec_ok (core.result.Result.Ok (), sf, af)).2 ⟨rfl, _, H1, hJ⟩

set_option maxHeartbeats 4000000 in
/-- **Retype (no reset) for an invariant `I` and an extra invariant `Zq`** (gen 60; the shape of gen 57's
`untyped.retype.gen`, gen 58's `genF` and gen 59's `genFZ`, all three its instances): `I` at the state after the
source's rewrite (its free index `base + len·2^z − p` when that fits), kept by `create_object`'s `OSKeep`
(`hkeep`) and by each `insert_new_cap` together with `Zq` (`hstepZ`); `Zq` from `hCOZ` / `hZ0`. -/
theorem untyped.retype.genFG {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S}
    (a : A) {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfit : base.val + len.val * 2 ^ (zA nt.val us).val ≤ 2 ^ 64)
    {Zq : S → Nat → Prop}
    (hCOZ : ∀ (s' : S) (a' : A) (j : Nat), j < len.val → Zq s' j →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ∧ Zq r.2.1 (j + 1) ⦄)
    (hZ0 : ∀ s1 : S, WritesIn st s s1 (fun b => b = src ∨ b = wa src 8#u64) → Zq s1 0)
    {I : S → Nat → Prop}
    (hstart : ∀ (s1 : S) (nfi : U64), (p.val ≤ base.val →
        base.val + len.val * 2 ^ (zA nt.val us).val - p.val < 2 ^ 64 →
        nfi.val = base.val + len.val * 2 ^ (zA nt.val us).val - p.val) →
      capA st s1 src = .Untyped p sb nfi dev →
      (∀ x ∈ OS, x ≠ src → capA st s1 x = capA st s x) →
      (∀ y ∈ OS, L.mem s1 (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s1 (wa y 24#u64) = L.mem s (wa y 24#u64)) →
      I s1 0)
    (hkeep : ∀ (s s' : S) (i : Nat), i < len.val → I s i → OSKeep st OS s s' → I s' i)
    (hstepZ : ∀ (s : S) (i : Nat), i < len.val → I s i → Zq s (i + 1) →
      cdt.insert_new_cap st s src (djA dcn off i) (newCapA nt.val (bjA base (zA nt.val us) i) us device) ⦃ s' =>
        I s' (i + 1) ∧ Zq s' (i + 1) ⦄) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧ I r.2.1 len.val ∧
      Zq r.2.1 len.val ⦄ := by
  refine WP.spec_mono (untyped.retype.genJK ar a hcs nt us dcn off len base device hn hz hfit
    (J := fun _ s' i => I s' i ∧ Zq s' i) (K := fun _ s' i => I s' i ∧ Zq s' (i + 1))
    (fun _ _ s' a' j hj h => WP.spec_mono (hCOZ s' a' j hj h.2) fun r hr =>
      ⟨hr.1, hkeep s' r.2.1 j hj h.1 hr.2.1, hr.2.2⟩)
    (fun _ _ s' i hi h => hstepZ s' i hi h.1 h.2)
    (fun s1 h1 => by
      obtain ⟨nfi, hv, h1, h2, h3, hW⟩ := h1.facts hO hsrc
      exact ⟨hstart s1 nfi hv h1 h2 h3, hZ0 s1 hW⟩)) ?_
  rintro r ⟨hok, -, -, hI, hZf⟩
  exact ⟨hok, hI, hZf⟩

set_option maxHeartbeats 4000000 in
/-- **Retype (no reset) keeps the tree, with an extra invariant** (gen 60: the common proof of gen 55's
`untyped.retype.tree` (`Zq := fun _ _ => True`) and gen 59's `treeZ`): `LoopA` along `untyped.retype.genJK`, the
gen-54 `RetypeDeltaA` built from the source's rewrite. -/
theorem untyped.retype.treeG {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    {Zq : S → Nat → Prop}
    (hCOZ : ∀ (s' : S) (a' : A) (j : Nat), j < len.val → Zq s' j →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ∧ Zq r.2.1 (j + 1) ⦄)
    (hZW : ∀ (s1 s2 : S) (j : Nat), Zq s1 j → WritesIn st s1 s2 (W7.CapW T Ω Sg) → Zq s2 j)
    (hZ0 : ∀ s1 : S, WritesIn st s s1 (fun b => b = src ∨ b = wa src 8#u64) → Zq s1 0)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      (∃ G' : List (List U64), ∃ par' : U64 → Option U64, TreeA st OS G' par' r.2.1) ∧ Zq r.2.1 len.val ⦄ := by
  have hU := hT.ut
  have hM := hT.lk
  set z := zA nt.val us with hzdef
  have hk1 : 1 ≤ 2 ^ z.val := Nat.one_le_two_pow
  obtain ⟨-, -, hpfit⟩ := ut_rangeA (capA_ut_b hcs) (by
    have := hU.reg src hsrc (by rw [hcs]; exact physA_ut _ _ _ _); rwa [hcs] at this)
  have hsb : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (capA_ut_b hcs)
  have hs0 : capA st s src ≠ .Null := by rw [hcs]; exact fun h => by cases h
  have hsG : src ∈ G.flatten := (hM.members src).2 ⟨hsrc, hs0⟩
  have hsn : ∀ j, j < len.val → src ≠ djA dcn off j := fun j hj e => hs0 (by rw [e]; exact hdn j hj)
  have hwf : ∀ j, j < len.val → CapRt.EncWf (newCapA nt.val (bjA base z j) us device) := fun j hj =>
    newCapA_encWf _ _ _ _ (hcan j hj) hus
  have hfit : base.val + len.val * 2 ^ z.val ≤ 2 ^ 64 := by omega
  have hdn1 : ∀ s1, RtSrc st s src p sb dev base.val (base.val + len.val * 2 ^ z.val) s1 →
      ∀ j, j < len.val → capA st s1 (djA dcn off j) = .Null := fun s1 h1 j hj => by
    obtain ⟨-, -, -, hc1, -, -⟩ := h1.facts hO hsrc
    rw [hc1 _ (hdO j hj) (fun e => hsn j hj e.symm)]; exact hdn j hj
  refine WP.spec_mono (untyped.retype.genJK ar a hcs nt us dcn off len base device hn hz hfit
    (J := fun s1 s' i => LoopA st OS par s1 src (djA dcn off) (fun j => newCapA nt.val (bjA base z j) us device) s' i ∧
      Zq s' i)
    (K := fun s1 s' i => LoopA st OS par s1 src (djA dcn off) (fun j => newCapA nt.val (bjA base z j) us device) s' i ∧
      Zq s' (i + 1))
    (fun _ _ s' a' j hj h => WP.spec_mono (hCOZ s' a' j hj h.2) fun r hr =>
      ⟨hr.1, h.1.keep (fun l hl => hdO l (by omega)) hr.2.1, hr.2.2⟩)
    (fun s1 h1 s' i hi h => spec_andL
      (LoopA.step hO hi h.1 hdO (hdn1 s1 h1) hdc hinj hsn hwf (fun j _ => newCapA_ne _ _ _ _))
      (cdt.insert_new_cap.zqW hO hZW (hdO i hi)
        (by obtain ⟨G1, par1, hM1, -, hs1, -⟩ := h.1; exact MdbLk.nxG hO hM1 hs1) h.2))
    (fun s1 h1 => ⟨LoopA.start (h1.lk hO hsrc hM hs0) hT.tree hsG,
      hZ0 s1 (by obtain ⟨-, -, -, -, -, hW⟩ := h1.facts hO hsrc; exact hW)⟩)) ?_
  rintro r ⟨hok, s1, h1, ⟨G', par', hM', hT', -, hF2b, hF2a, hF3⟩, hZf⟩
  obtain ⟨nfi, hnv0, hcs1, hc1, -, -⟩ := h1.facts hO hsrc
  have hnv : nfi.val = base.val + len.val * 2 ^ z.val - p.val := hnv0 (by omega) (by first | omega | (rw [← hzdef]; omega))
  refine ⟨hok, ⟨G', par', hM', hT', ?_⟩, hZf⟩
  have hbj : ∀ j, j < len.val → (bjA base z j).val = base.val + j * 2 ^ z.val := fun j hj => by
    have : (j + 1) * 2 ^ z.val ≤ len.val * 2 ^ z.val := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at this
    exact bjA_val (by omega)
  have dG : ∀ j, j < len.val → djA dcn off j ∉ G.flatten := fun j hj hm => ((hM.members _).1 hm).2 (hdn j hj)
  have hR : RetypeDeltaA st OS par par' s s1 r.2.1 src p sb fi nfi dev base.val (2 ^ z.val) len.val (djA dcn off)
      (fun j => newCapA nt.val (bjA base z j) us device) := by
    refine ⟨hT.parIn, hsrc, hcs, hcs1, hc1, hfi, hA, by rw [hnv]; omega, by omega, hk1,
      fun j _ => newCapA_phys _ _ _ _, fun j hj => ?_, fun j hj => ?_, fun j hj hu => ?_, hdn, hinj,
      fun j hj y => ⟨Mdb.not_desc_of_none ?_, Mdb.not_desc_of_no_child fun q e => dG j hj (hT.tree.par_mem q _ e).2⟩,
      hF2a, hF2b, hF3⟩
    · show baseA _ = _
      unfold baseA; rw [newCapA_ptr, hbj j hj]
    · have hjk : (j + 1) * 2 ^ z.val ≤ len.val * 2 ^ z.val := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at hjk
      have e1 := (newCapA_range hn (bjA base z j) us device hz
        (by rw [hbj j hj, ← hzdef]; omega)).2
      rw [← hzdef, hbj j hj] at e1
      rw [e1]
    · obtain ⟨h0, e⟩ := newCapA_ut hu
      refine ⟨us, device, e, ?_⟩
      rw [hzdef, h0]; simp [zA]
    · cases e : par (djA dcn off j) with
      | none => rfl
      | some q => exact absurd (hT.tree.par_mem _ q e).1 (dG j hj)
  exact hR.utinv hU

/-- **`untyped::retype` without reset keeps the tree** (module docstring; x86 `utinv_retype` assembled at
function level): the gen-54 `RetypeDeltaA` built from the source's `set_cap` and `LoopA` at `len`. -/
theorem untyped.retype.tree {A : Type _} (ar : machine.Arch A) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {G : List (List U64)} {par : U64 → Option U64} {s : S} (hT : TreeA st OS G par s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hn : nt.val < 15) (hz : (zA nt.val us).val < 64)
    (hfi : fi.val < 2 ^ sb.val) (hA : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hCO : ∀ (s' : S) (a' : A) (j : Nat), j < len.val →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ⦄)
    (hdO : ∀ j, j < len.val → djA dcn off j ∈ OS)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      ∃ G' : List (List U64), ∃ par' : U64 → Option U64, TreeA st OS G' par' r.2.1 ⦄ :=
  WP.spec_mono (untyped.retype.treeG ar hO hT a hsrc hcs nt us dcn off len base device hn hz hfi hA hAw
    (Zq := fun _ _ => True) (fun s' a' j hj _ => WP.spec_mono (hCO s' a' j hj) fun r h => ⟨h.1, h.2, trivial⟩)
    (fun _ _ _ _ _ => trivial) (fun _ _ => trivial) hdO hdn hdc hinj hcan hus) fun _ h => ⟨h.1, h.2.1⟩

/-! ## Reset: the free index lowered on an untyped slot without descendants -/

section reset
variable {OS : Set U64} {G : List (List U64)} {par : U64 → Option U64}

set_option maxHeartbeats 2000000 in
/-- **The free index lowered keeps `UtInvA`** when the slot has no descendants (x86 `UtInv.raise_fi` with the
index lowered instead of raised; `noDesc` gives the hypothesis `hnd` after `ensure_no_children`). Only `inc`,
`noov`, `excl`, `fib` read the free index: `inc` / `noov` at the slot itself need no descendants (every cap
meeting it is an ancestor, untyped by `anc`, containing it by `inc`); `excl` against a same-region untyped `v`:
the slot is `v`'s descendant (`drange`), so `v` is full (`inc`). -/
theorem UtInvA.lower {s s' : S} (hU : UtInvA st OS par s) (hP : ParIn OS par) {x p b i i' : U64} {d : Bool}
    (hx : x ∈ OS) (hcx : capA st s x = .Untyped p b i d) (hcx' : capA st s' x = .Untyped p b i' d)
    (hi' : i'.val ≤ 2 ^ b.val) (hnd : ∀ y, ¬ Mdb.Desc par y x)
    (hk : ∀ y ∈ OS, y ≠ x → capA st s' y = capA st s y) : UtInvA st OS par s' := by
  have rb : ∀ z ∈ OS, baseA (capA st s' z) = baseA (capA st s z) ∧ topA (capA st s' z) = topA (capA st s z) ∧
      physA (capA st s' z) = physA (capA st s z) ∧ isUtA (capA st s' z) = isUtA (capA st s z) := by
    intro z hz
    by_cases hzx : z = x
    · rw [hzx, hcx, hcx']; exact ut_rng p b i' i d d
    · rw [hk z hz hzx]; exact ⟨rfl, rfl, rfl, rfl⟩
  have reg : ∀ z ∈ OS, physA (capA st s z) = true → baseA (capA st s z) ≤ topA (capA st s z) := hU.reg
  have xr := ut_rangeA (capA_ut_b hcx) (by have := reg x hx (by rw [hcx]; exact physA_ut _ _ _ _); rwa [hcx] at this)
  -- a same-region untyped `v ≠ x` is full
  have full : ∀ v ∈ OS, v ≠ x → ∀ i2 d2, capA st s v = .Untyped p b i2 d2 → 2 ^ b.val ≤ i2.val := by
    intro v hv hvx i2 d2 hcv
    have hnD : ¬ DisjA (capA st s v) (capA st s x) := by
      unfold DisjA
      rw [hcv, hcx]
      obtain ⟨g1, g2, -⟩ := ut_rng p b i2 i d2 d
      rw [g1, g2]
      have := reg x hx (by rw [hcx]; exact physA_ut _ _ _ _)
      rw [hcx] at this
      omega
    rcases hU.drange x hx p b i d hcx v hv hvx (by rw [hcv]; exact physA_ut _ _ _ _) hnD with h | h
    · exact absurd h (hnd v)
    · have := (hU.inc v hv p b i2 d2 hcv x h).2.2
      rw [hcx, xr.2.1] at this; omega
  refine ⟨fun z hz hp => ?_, fun u hu pu bu iu du hcu y hy => ?_, fun u hu pu bu iu du hcu y hy hp => ?_,
    fun u hu v hv huv pu bu i1 i2 d1 d2 h1 h2 => ?_, fun u hu pu bu iu du hcu => ?_,
    fun u hu pu bu iu du hcu y hy hyu hp hD => ?_, fun a c hd hu => ?_⟩
  · obtain ⟨e1, e2, e3, -⟩ := rb z hz
    rw [e1, e2]; rw [e3] at hp; exact reg z hz hp
  · by_cases hux : u = x
    · rw [hux] at hy; exact absurd hy (hnd y)
    · rw [hk u hu hux] at hcu
      obtain ⟨hyO, -⟩ := desc_in hP hy
      obtain ⟨e1, e2, e3, -⟩ := rb y hyO
      rw [e1, e2, e3]; exact hU.inc u hu pu bu iu du hcu y hy
  · obtain ⟨e1, e2, e3, e4⟩ := rb y hy
    obtain ⟨f1, f2, -, -⟩ := rb u hu
    rw [e3] at hp
    unfold DisjRA WithinA
    rw [e1, e2, e4, f1, f2]
    by_cases hux : u = x
    · rw [hux, hcx'] at hcu
      cases hcu
      rw [hux]
      by_cases hyx : y = x
      · rw [hyx, hcx]; exact Or.inr ⟨rfl, le_refl _, le_refl _⟩
      · by_cases hD : DisjA (capA st s y) (capA st s x)
        · left; unfold DisjA at hD; rw [hcx, xr.1, xr.2.1] at hD; omega
        · right
          rcases hU.drange x hx p b i d hcx y hy hyx hp hD with h | h
          · exact absurd h (hnd y)
          · have hyu : isUtA (capA st s y) = true := hU.anc y x h (by rw [hcx]; rfl)
            obtain ⟨py, by_, iy, dy, hcy⟩ := isUtA_ex hyu
            have hi := hU.inc y hy py by_ iy dy hcy x h
            have yr := ut_rangeA (capA_ut_b hcy) (by have := reg y hy hp; rwa [hcy] at this)
            have fb := hU.fib y hy py by_ iy dy hcy
            refine ⟨hyu, ?_, ?_⟩
            · have := hi.2.1; rw [hcy, yr.1]; exact this
            · have := hi.2.2; rw [hcy, yr.2.1]; omega
    · rw [hk u hu hux] at hcu
      have := hU.noov u hu pu bu iu du hcu y hy hp
      unfold DisjRA WithinA at this; exact this
  · by_cases hux : u = x
    · rw [hux, hcx'] at h1; cases h1
      have hvx : v ≠ x := fun e => huv (by rw [hux, e])
      rw [hk v hv hvx] at h2
      exact Or.inr (full v hv hvx i2 d2 h2)
    · by_cases hvx : v = x
      · rw [hvx, hcx'] at h2; cases h2
        rw [hk u hu hux] at h1
        exact Or.inl (full u hu hux i1 d1 h1)
      · rw [hk u hu hux] at h1; rw [hk v hv hvx] at h2
        exact hU.excl u hu v hv huv pu bu i1 i2 d1 d2 h1 h2
  · by_cases hux : u = x
    · rw [hux, hcx'] at hcu; cases hcu; exact hi'
    · rw [hk u hu hux] at hcu; exact hU.fib u hu pu bu iu du hcu
  · obtain ⟨e1, e2, e3, -⟩ := rb y hy
    obtain ⟨f1, f2, -, -⟩ := rb u hu
    rw [e3] at hp
    have hD' : ¬ DisjA (capA st s y) (capA st s u) := by
      unfold DisjA at hD ⊢; rw [e1, e2, f1, f2] at hD; exact hD
    by_cases hux : u = x
    · rw [hux] at hD' hyu ⊢; exact hU.drange x hx p b i d hcx y hy hyu hp hD'
    · rw [hk u hu hux] at hcu; exact hU.drange u hu pu bu iu du hcu y hy hyu hp hD'
  · obtain ⟨hcO, haO⟩ := desc_in hP hd
    rw [(rb c hcO).2.2.2] at hu; rw [(rb a haO).2.2.2]; exact hU.anc a c hd hu

/-- **`TreeA` with the free index lowered** (links kept, the ghost kept). -/
theorem TreeA.lower {s s' : S} (h : TreeA st OS G par s) {x p b i i' : U64} {d : Bool} (hx : x ∈ OS)
    (hcx : capA st s x = .Untyped p b i d) (hcx' : capA st s' x = .Untyped p b i' d) (hi' : i'.val ≤ 2 ^ b.val)
    (hnd : ∀ y, ¬ Mdb.Desc par y x) (hk : ∀ y ∈ OS, y ≠ x → capA st s' y = capA st s y)
    (hl : ∀ y ∈ OS, L.mem s' (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s' (wa y 24#u64) = L.mem s (wa y 24#u64)) :
    TreeA st OS G par s' := by
  refine ⟨h.lk.keep hl fun y hy => ?_, h.tree, h.ut.lower h.parIn hx hcx hcx' hi' hnd hk⟩
  by_cases hyx : y = x
  · rw [hyx, hcx, hcx']; exact ⟨fun e => (by cases e), fun e => (by cases e)⟩
  · rw [hk y hy hyx]

/-- **The in-place rewrite of an untyped cap with a lower free index** (`reset_untyped`'s final `set_cap`). -/
theorem TreeA.lowerW (hO : OSOK T Ω Sg OS) {s : S} (h : TreeA st OS G par s) {x p b i i' : U64} {d : Bool}
    (hx : x ∈ OS) (hcx : capA st s x = .Untyped p b i d) (hi' : i'.val ≤ 2 ^ b.val)
    (hnd : ∀ y, ¬ Mdb.Desc par y x) {w0 w1 : U64}
    (hd : capability.Cap.decode w0 w1 = ok (.Untyped p b i' d)) :
    TreeA st OS G par (L.wr (L.wr s x w0) (wa x 8#u64) w1) :=
  h.lower hx hcx (capA_wr2_self hO hx hd) hi' hnd (fun y hy hyx => capA_wr2_other hO hx hy hyx)
    (set_cap_links hO hx)

/-- **A device untyped's reset keeps the tree** (`reset_untyped_dev`: the state kept or the cap rewritten with
free index 0), when the slot has no descendants (`ensure_no_children.noDesc`). -/
theorem untyped.reset_untyped.dev_tree {A : Type _} (ar : machine.Arch A) (hO : OSOK T Ω Sg OS) {s : S}
    (h : TreeA st OS G par s) (a : A) {x p b i : U64} (hx : x ∈ OS) (hxw : CapSlotW T Ω Sg x)
    (hcx : capA st s x = .Untyped p b i true) (hnd : ∀ y, ¬ Mdb.Desc par y x) :
    ∃ s1, untyped.reset_untyped st ar s a x = ok (.Ok (), s1, a) ∧ TreeA st OS G par s1 := by
  obtain ⟨s1, h1, hor⟩ := reset_untyped_dev (st := st) (T := T) (Ω := Ω) (Sg := Sg) ar s a x p b i hxw
    (by rw [capA_eq, hcx])
  refine ⟨s1, h1, ?_⟩
  rcases hor with rfl | e
  · exact h
  · have wf : CapRt.EncWf (.Untyped p b 0#u64 true) := by
      have w := CapRt.decodeF_encWf (L.mem s x).bv (L.mem s (wa x 8#u64)).bv
      have e' : CapRt.decodeF (L.mem s x).bv (L.mem s (wa x 8#u64)).bv = .Untyped p b i true := hcx
      rw [e'] at w; exact w
    obtain ⟨w0, w1, he, hr⟩ := CapRt.decode_encode _ wf
    rw [set_cap_eq he] at e
    obtain rfl := okinj e
    exact h.lowerW hO hx hcx (by simp) hnd hr

/-- **With `ensure_no_children`**: `Ok` at a revocable untyped slot discharges `hnd` (`noDesc`). -/
theorem TreeA.lowerW_enc (hO : OSOK T Ω Sg OS) {s : S} (h : TreeA st OS G par s) {x p b i i' : U64} {d : Bool}
    (hx : x ∈ OS) (hcx : capA st s x = .Untyped p b i d) (hi' : i'.val ≤ 2 ^ b.val)
    (hr : obj.Slot.revocable st x s = ok true)
    (he : cdt.ensure_no_children st s x = ok (core.result.Result.Ok ())) {w0 w1 : U64}
    (hd : capability.Cap.decode w0 w1 = ok (.Untyped p b i' d)) :
    TreeA st OS G par (L.wr (L.wr s x w0) (wa x 8#u64) w1) :=
  h.lowerW hO hx hcx hi' (cdt.ensure_no_children.noDesc hO h hx hcx hr he) hd

end reset

end ST
end R
end W7

end

end Fl4ProofsA64.P1

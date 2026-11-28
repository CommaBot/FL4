/-
P1 (aarch64, gen 58): **`hCO` for `ArmVcpu` and `ArmHighVSpace`** — the memory-writing `create_object` cases other
than `Tcb` (gen 55's `create_object.pureCO` covers the 12 pure types), from `ValidUntypedA`.

* **`InWin b0 n`**: the bytes `[b0, b0 + n)`. `wr_win`, `write_winT` (a store write of `b0 + o`, `o < n`),
  `OSKeep.of_off` (an `OS`-word-avoiding frame keeps every `OS` slot's words).
* **`vcpu.init.win`** (vcpu.rs `init`: the `TCB` / `OWNER_CPU` / `VPPI_MASKED` / `RUN_*` words, the register file
  through `reg_set`, `sync_vgic_status`'s `ELRSR` / `EISR` / `MISR` writes; register indices `< 64`,
  `vcpu.reg_addr.offA`): writes in `[vc, vc + 4096)`. `vcpu.reg_set.winT`, `vcpu.sync_vgic_status.winT` (as
  QueueDecVcpuRegA's `cur0A` lemmas).
* **`vspace.init_high_vspace.win`** (vspace.rs:283–297: entries `0 … 510` copied from `kernel_ttbr1_entry`, entry
  511 the table descriptor): writes in `[base, base + 4096)` (the level-0 table; the 8 KiB object's level-1 half is
  not written).
* **`create_object.vcpuW`** / **`create_object.highW`**: `create_object` of type `ArmVcpu` (12) / `ArmHighVSpace` (14)
  returns `newCapA` and writes only in its first 4 KiB.
* **`create_object.hCO_vcpu`** / **`create_object.hCO_high`**: gen 55's `hCO` (every `j < len`, any state) for these
  two types, from `ValidUntypedA H` at the retype's start, the source a RAM `Untyped p sb fi false` of `OS`,
  `OSOK H.tcbs H.omega Sg OS`, `HeapOK H` and the decode's window checks (`p + fi ≤ base`,
  `base + len·2^z ≤ p + 2^sb`): every `OS` word lies off the free part (`ValidUntypedA.word_off`), every new object
  inside it. With `create_object.pureCO`, `hCO` holds for 14 of the 15 types.

**`Tcb` (type 1): `hCO` as stated is false** (not proved here; the argument, for the Architect): `create_object`'s
`Tcb` arm ends in `debug_append(base)` (objects.rs:418–427), which reads `cpu := Tcb(base).affinity` — a word of the
new TCB that `create_object` never initialises (`regs::init_context`, `init_fpu`, `debug::init_context` (a no-op on
AArch64), `set_domain`, `set_child_name` leave it) — then writes `node_base(cpu) + DEBUG_TCBS` and, when the head
read there is non-zero, `head + DEBUG_PREV`. `hCO` quantifies over every state `s'`, where `cpu` and `head` are
arbitrary words, so both written addresses can be any `OS` slot word and `OSKeep` fails. Discharging it needs a loop
invariant carrying (a) the new TCB's affinity word (zero memory in the free part, or an explicit write — seL4's
`createObject` sets `tcbAffinity`, FL4's does not) and (b) the debug list heads being null or heap TCBs, i.e. a
loop form whose `hCO` takes the invariant (not gen 55's ∀-state form).

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbVUR
import Fl4ProofsA64.P1.QueueDecVcpuRegA
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- The bytes `[b0, b0 + n)`. -/
def InWin (b0 : U64) (n : Nat) (b : U64) : Prop := b0.val ≤ b.val ∧ b.val < b0.val + n

theorem wr_win {s : S} {b0 o v : U64} {n : Nat} (hal : b0.val % 8 = 0) (hf : b0.val + n ≤ 2 ^ 64)
    (ho : o.val < n) (h8 : o.val % 8 = 0) : WritesIn st s (L.wr s (wa b0 o) v) (InWin b0 n) := by
  have hv : (wa b0 o).val = b0.val + o.val := by rw [wa_val]; exact Nat.mod_eq_of_lt (by omega)
  refine (writesIn_wr (by show (wa b0 o).val % 8 = 0; rw [hv]; omega)).mono fun b e => ?_
  subst e; unfold InWin; rw [hv]; omega

theorem write_winT {s0 s : S} {b0 o v : U64} {n : Nat} (h : WritesIn st s0 s (InWin b0 n))
    (hal : b0.val % 8 = 0) (hf : b0.val + n ≤ 2 ^ 64) (ho : o.val < n) (h8 : o.val % 8 = 0) :
    st.write s (wa b0 o) v ⦃ s' => WritesIn st s0 s' (InWin b0 n) ⦄ :=
  WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => by subst e; exact h.trans1 (wr_win hal hf ho h8)

/-- **A frame avoiding every `OS` slot word keeps them** (`OSKeep.of_writes` with the `OS` words only). -/
theorem OSKeep.of_off {OS : Set U64} (hO : OSOK T Ω Sg OS) {s s' : S} {F : U64 → Prop} (hw : WritesIn st s s' F)
    (hF : ∀ y ∈ OS, ∀ o : U64, o.val < 32 → o.val % 8 = 0 → ¬ F (wa y o)) : OSKeep st OS s s' := fun y hy =>
  ⟨hw.mem_eq (hO.al0 hy) (by have := hF y hy 0#u64 (by simp) (by simp); rwa [SFF.wadd0'] at this),
   hw.mem_eq (hO.al hy (by simp) (by simp)) (hF y hy _ (by simp) (by simp)),
   hw.mem_eq (hO.al hy (by simp) (by simp)) (hF y hy _ (by simp) (by simp)),
   hw.mem_eq (hO.al hy (by simp) (by simp)) (hF y hy _ (by simp) (by simp))⟩

/-! ## `vcpu::init` -/

theorem vcpu.reg_set.winT {s0 s : S} {vc idx v : U64} (h : WritesIn st s0 s (InWin vc 4096))
    (hal : vc.val % 8 = 0) (hf : vc.val + 4096 ≤ 2 ^ 64) (hi : idx.val < 64) :
    vcpu.reg_set st s vc idx v ⦃ s' => WritesIn st s0 s' (InWin vc 4096) ⦄ := by
  obtain ⟨o, ho, h8, e⟩ := vcpu.reg_addr.offA vc idx hi
  unfold vcpu.reg_set
  rw [e, bind_ok]
  exact write_winT h hal hf ho h8

set_option maxHeartbeats 2000000 in
theorem vcpu.sync_vgic_status.winT {s0 s : S} {vc lrs : U64} {g : Bool} (h : WritesIn st s0 s (InWin vc 4096))
    (hal : vc.val % 8 = 0) (hf : vc.val + 4096 ≤ 2 ^ 64) (hl : lrs.val ≤ 64) :
    vcpu.sync_vgic_status st s vc lrs g ⦃ s' => WritesIn st s0 s' (InWin vc 4096) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.sync_vgic_status
  refine WP.spec_bind (Pₘ := fun _ => True)
    (WP.spec_mono (P0.vcpu.sync_vgic_status_loop.p0 st s vc lrs g 0#u64 0#u64 0#u64 false 0#u64 hS hl
      (by simp)) fun _ _ => trivial) ?_
  rintro ⟨elrsr, eisr, vl, hp⟩ -
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (P0.vcpu.reg_get.p0 st s vc _ hS) fun hcr _ => ?_
  refine WP.spec_bind (P0.vcpu.reg_get.p0 st s vc _ hS) fun vmcr _ => ?_
  simp only [lift, bind_ok]
  repeat' (first
    | exact vcpu.reg_set.winT (h := by assumption) hal hf (by
        simp [fl4_abi.consts.vcpu_reg.VGIC_MISR])
    | (refine WP.spec_bind (vcpu.reg_set.winT (h := by assumption) hal hf (by
        simp [fl4_abi.consts.vcpu_reg.VGIC_ELRSR, fl4_abi.consts.vcpu_reg.VGIC_EISR])) fun _ _ => ?_)
    | (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun _ _ => ?_))

section arch
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **`vcpu::init` writes in the VCPU's 4 KiB** (module docstring). -/
theorem vcpu.init.win (hA : P0.ArchTotal ar) (s : S) (a : A) {vc : U64} (hal : vc.val % 8 = 0)
    (hf : vc.val + 4096 ≤ 2 ^ 64) :
    vcpu.init st ar s a vc ⦃ s' => WritesIn st s s' (InWin vc 4096) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h0 : WritesIn st s s (InWin vc 4096) := WritesIn.refl _ _
  unfold vcpu.init
  simp only [lift, bind_ok]
  repeat' (first
    | exact vcpu.sync_vgic_status.winT (h := by assumption) hal hf (by omega)
    | (refine WP.spec_bind (P0.vcpu.num_lrs.p0 ar a hA) fun _ _ => ?_)
    | (refine WP.spec_bind (write_winT (h := by assumption) hal hf (by
        simp [vcpu.TCB, vcpu.OWNER_CPU, vcpu.VPPI_MASKED, vcpu.RUN_CALLER, vcpu.RUN_OFFSET, vcpu.RUN_OUT_MASK])
        (by simp [vcpu.TCB, vcpu.OWNER_CPU, vcpu.VPPI_MASKED, vcpu.RUN_CALLER, vcpu.RUN_OFFSET,
          vcpu.RUN_OUT_MASK])) fun _ _ => ?_)
    | (refine WP.spec_bind (vcpu.reg_set.winT (h := by assumption) hal hf (by
        simp [fl4_abi.consts.vcpu_reg.SCTLR, fl4_abi.consts.vcpu_reg.VMPIDR_EL2, fl4_abi.consts.vcpu_reg.VPIDR_EL2,
          fl4_abi.consts.vcpu_reg.HCR_EL2, fl4_abi.consts.vcpu_reg.VGIC_HCR, fl4_abi.consts.vcpu_reg.VGIC_VTR]))
        fun _ _ => ?_)
    | (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun _ _ => ?_))

/-! ## `vspace::init_high_vspace` -/

set_option maxHeartbeats 2000000 in
theorem vspace.init_high_vspace_loop.win (hA : P0.ArchTotal ar) (s : S) (a : A) {b0 : U64}
    (hal : b0.val % 8 = 0) (hf : b0.val + 4096 ≤ 2 ^ 64) :
    vspace.init_high_vspace_loop st ar s a b0 0#u64 ⦃ s' => WritesIn st s s' (InWin b0 4096) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h511 : vspace.HIGH_L0_INDEX.val = 511 := by simp [vspace.HIGH_L0_INDEX]
  unfold vspace.init_high_vspace_loop
  refine loop.spec_decr_nat (measure := fun x => 511 - x.2.val)
    (inv := fun x => x.2.val ≤ 511 ∧ WritesIn st s x.1 (InWin b0 4096)) _ _ _ ?_ ⟨by simp, WritesIn.refl _ _⟩
  rintro ⟨s2, i⟩ ⟨hi, hW⟩
  simp only at hi hW ⊢
  unfold vspace.init_high_vspace_loop.body
  by_cases hit : i < vspace.HIGH_L0_INDEX
  · rw [if_pos hit]
    have hit' : i.val < 511 := by have : i.val < vspace.HIGH_L0_INDEX.val := hit; omega
    refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun e _ => ?_
    refine WP.spec_bind (Pₘ := fun s3 => WritesIn st s s3 (InWin b0 4096)) ?_ fun s3 h3 => ?_
    · split
      · obtain ⟨i1, h1e, h1v⟩ := spec_exA (U64.mul_spec (x := i) (y := 8#u64) (by scalar_tac))
        rw [h1e, bind_ok]
        simp only [lift, bind_ok]
        have hv : i1.val = i.val * 8 := by simpa using h1v
        exact write_winT hW hal hf (by omega) (by omega)
      · exact (WP.spec_ok _).2 hW
    · obtain ⟨i5, h5e, h5v⟩ := spec_exA (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
      rw [h5e, bind_ok, WP.spec_ok]
      have h5 : i5.val = i.val + 1 := by simpa using h5v
      try dsimp only
      have H1 : i5.val ≤ 511 := by omega
      have H3 : 511 - i5.val < 511 - i.val := by omega
      first | exact ⟨⟨H1, h3⟩, H3⟩ | exact ⟨H1, h3, H3⟩
  · rw [if_neg hit, WP.spec_ok]
    exact hW

set_option maxHeartbeats 2000000 in
/-- **`vspace::init_high_vspace` writes in the level-0 table** (module docstring). -/
theorem vspace.init_high_vspace.win (hA : P0.ArchTotal ar) (s : S) (a : A) {b0 : U64} (hal : b0.val % 8 = 0)
    (hf : b0.val + 4096 ≤ 2 ^ 64) :
    vspace.init_high_vspace st ar s a b0 ⦃ r => WritesIn st s r.1 (InWin b0 4096) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h511 : vspace.HIGH_L0_INDEX.val = 511 := by simp [vspace.HIGH_L0_INDEX]
  unfold vspace.init_high_vspace
  simp only [lift, bind_ok]
  refine WP.spec_bind (vspace.init_high_vspace_loop.win hA s a hal hf) fun s1 h1 => ?_
  obtain ⟨i, hie, hiv⟩ := spec_exA (U64.mul_spec (x := vspace.HIGH_L0_INDEX) (y := 8#u64) (by
    rw [h511]; scalar_tac))
  rw [hie, bind_ok]
  have hv : i.val = 4088 := by have := hiv; simp only [h511] at this; simpa using this
  try simp only [lift, bind_ok]
  repeat' (first
    | exact (WP.spec_ok _).2 (by assumption)
    | (refine WP.spec_bind (write_winT (h := h1) hal hf (by omega) (by omega)) fun _ _ => ?_)
    | (refine WP.spec_bind (Pₘ := fun _ => True) (by p0_split) fun _ _ => ?_))

/-! ## `create_object` -/

theorem u64_ne_of_val {x y : U64} (h : x.val ≠ y.val) : x ≠ y := fun e => h (congrArg _ e)

set_option maxHeartbeats 2000000 in
/-- **`create_object` of an `ArmVcpu`** (module docstring). -/
theorem create_object.vcpuW (hA : P0.ArchTotal ar) (s : S) (a : A) (nt b0 us : U64) (dev : Bool)
    (hn : nt.val = 12) (hal : b0.val % 8 = 0) (hf : b0.val + 4096 ≤ 2 ^ 64) :
    objects.create_object st ar s a nt b0 us dev ⦃ r => r.1 = newCapA nt.val b0 us dev ∧
      WritesIn st s r.2.1 (InWin b0 4096) ⦄ := by
  obtain rfl : nt = 12#u64 := UScalar.eq_of_val_eq (by simp [hn])
  have hcap : newCapA (12#u64 : U64).val b0 us dev = .Vcpu b0 := by first | rfl | simp [newCapA]
  rw [hcap]
  unfold objects.create_object objects.create_arch_object
  simp (config := { decide := true }) only [fl4_abi.consts.object.Tcb, fl4_abi.consts.object.Endpoint,
    fl4_abi.consts.object.Notification, fl4_abi.consts.object.CapTable, fl4_abi.consts.object.Untyped,
    fl4_abi.consts.object.SchedContext, fl4_abi.consts.object.Reply, fl4_abi.consts.object.ArmPageTable,
    fl4_abi.consts.object.ArmVSpace, fl4_abi.consts.object.ArmVcpu, ↓reduceIte, ite_true, ite_false]
  refine WP.spec_bind (vcpu.init.win hA s a hal hf) fun s1 h1 => ?_
  exact (WP.spec_ok _).2 ⟨rfl, h1⟩

set_option maxHeartbeats 2000000 in
/-- **`create_object` of an `ArmHighVSpace`** (module docstring). -/
theorem create_object.highW (hA : P0.ArchTotal ar) (s : S) (a : A) (nt b0 us : U64) (dev : Bool)
    (hn : nt.val = 14) (hal : b0.val % 8 = 0) (hf : b0.val + 4096 ≤ 2 ^ 64) :
    objects.create_object st ar s a nt b0 us dev ⦃ r => r.1 = newCapA nt.val b0 us dev ∧
      WritesIn st s r.2.1 (InWin b0 4096) ⦄ := by
  obtain rfl : nt = 14#u64 := UScalar.eq_of_val_eq (by simp [hn])
  have hcap : newCapA (14#u64 : U64).val b0 us dev = .HighVSpace b0 false 0#u64 := by
    first | rfl | simp [newCapA]
  rw [hcap]
  unfold objects.create_object objects.create_arch_object
  simp (config := { decide := true }) only [fl4_abi.consts.object.Tcb, fl4_abi.consts.object.Endpoint,
    fl4_abi.consts.object.Notification, fl4_abi.consts.object.CapTable, fl4_abi.consts.object.Untyped,
    fl4_abi.consts.object.SchedContext, fl4_abi.consts.object.Reply, fl4_abi.consts.object.ArmPageTable,
    fl4_abi.consts.object.ArmVSpace, fl4_abi.consts.object.ArmVcpu, fl4_abi.consts.object.ArmStage2VSpace,
    fl4_abi.consts.object.ArmHighVSpace, ↓reduceIte, ite_true, ite_false]
  refine WP.spec_bind (vspace.init_high_vspace.win hA s a hal hf) ?_
  rintro ⟨s1, a1⟩ h1
  try dsimp only
  try simp only [uncurry_apply_pair]
  exact (WP.spec_ok _).2 ⟨rfl, h1⟩

/-! ## `hCO` from the free-region fact -/

variable {OS : Set U64} {H : Heap}

/-- **The new object's first 4 KiB miss every `OS` word**: the window lies in the source's free part. -/
theorem win_off (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S} (hV : ValidUntypedA st H OS s)
    {src p sb fi : U64} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi false) {b0 : U64}
    (hlo : p.val + fi.val ≤ b0.val) (hhi : b0.val + 4096 ≤ p.val + 2 ^ sb.val) :
    ∀ y ∈ OS, ∀ o : U64, o.val < 32 → o.val % 8 = 0 → ¬ InWin b0 4096 (wa y o) := by
  intro y hy o ho h8 hin
  unfold InWin at hin
  rcases hV.word_off hH hO hsrc hcs hy ho h8 with g | g <;> omega

/-- The `j`-th object of the window: placed and inside the window. -/
theorem bj_win {base : U64} {z : U64} {len j : Nat} (hj : j < len) (hfit : base.val + len * 2 ^ z.val ≤ 2 ^ 64)
    (hal : base.val % 8 = 0) (hz : 3 ≤ z.val) :
    (bjA base z j).val = base.val + j * 2 ^ z.val ∧ (bjA base z j).val % 8 = 0 ∧
      (bjA base z j).val + 2 ^ z.val ≤ base.val + len * 2 ^ z.val := by
  have hk : (j + 1) * 2 ^ z.val ≤ len * 2 ^ z.val := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at hk
  have h1 : 1 ≤ 2 ^ z.val := Nat.one_le_two_pow
  have hv : (bjA base z j).val = base.val + j * 2 ^ z.val := bjA_val (by omega)
  have h8 : 2 ^ z.val % 8 = 0 := by
    obtain ⟨k, hk'⟩ : ∃ k, z.val = 3 + k := ⟨z.val - 3, by omega⟩
    rw [hk', pow_add]; simp
  refine ⟨hv, ?_, by omega⟩
  rw [hv, Nat.add_mod, Nat.mul_mod, h8, hal]; simp

theorem zA_12 (us : U64) : (zA 12 us).val = 12 := by simp [zA]
theorem zA_14 (us : U64) : (zA 14 us).val = 13 := by simp [zA]

/-- **`hCO` for `ArmVcpu`** (module docstring). -/
theorem create_object.hCO_vcpu (hA : P0.ArchTotal ar) (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S}
    (hV : ValidUntypedA st H OS s) {src p sb fi : U64} (hsrc : src ∈ OS)
    (hcs : capA st s src = .Untyped p sb fi false) (nt us len base : U64) (device : Bool) (hn : nt.val = 12)
    (hal : base.val % 8 = 0) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val) (hpf : p.val + 2 ^ sb.val ≤ 2 ^ 64) :
    ∀ (s' : S) (a' : A) (j : Nat), j < len.val →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ⦄ := by
  intro s' a' j hj
  have hz : (zA nt.val us).val = 12 := by rw [hn]; exact zA_12 us
  obtain ⟨hv, h8, hle⟩ := bj_win (z := zA nt.val us) hj (by omega) hal (by omega)
  have e12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  rw [hz, e12] at hv hle hAw
  refine WP.spec_mono (create_object.vcpuW hA s' a' nt _ us device hn h8 (by omega)) fun r ⟨h1, h2⟩ => ⟨h1, ?_⟩
  exact OSKeep.of_off hO h2 (win_off hH hO hV hsrc hcs (by rw [hv]; omega) (by omega))

/-- **`hCO` for `ArmHighVSpace`** (module docstring). -/
theorem create_object.hCO_high (hA : P0.ArchTotal ar) (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S}
    (hV : ValidUntypedA st H OS s) {src p sb fi : U64} (hsrc : src ∈ OS)
    (hcs : capA st s src = .Untyped p sb fi false) (nt us len base : U64) (device : Bool) (hn : nt.val = 14)
    (hal : base.val % 8 = 0) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val) (hpf : p.val + 2 ^ sb.val ≤ 2 ^ 64) :
    ∀ (s' : S) (a' : A) (j : Nat), j < len.val →
      objects.create_object st ar s' a' nt (bjA base (zA nt.val us) j) us device ⦃ r =>
        r.1 = newCapA nt.val (bjA base (zA nt.val us) j) us device ∧ OSKeep st OS s' r.2.1 ⦄ := by
  intro s' a' j hj
  have hz : (zA nt.val us).val = 13 := by rw [hn]; exact zA_14 us
  obtain ⟨hv, h8, hle⟩ := bj_win (z := zA nt.val us) hj (by omega) hal (by omega)
  have e13 : (2 : ℕ) ^ 13 = 8192 := by norm_num
  rw [hz, e13] at hv hle hAw
  refine WP.spec_mono (create_object.highW hA s' a' nt _ us device hn h8 (by omega)) fun r ⟨h1, h2⟩ => ⟨h1, ?_⟩
  exact OSKeep.of_off hO h2 (win_off hH hO hV hsrc hcs (by rw [hv]; omega) (by omega))

end arch

end ST
end R
end W7

end

end Fl4ProofsA64.P1

/-
P3 (line p3J, gen 12): **`KCfgFL4`** [P] — the ported spec's two untyped build constants are FL4's.

Fl4Spec `Machine.lean` ports l4v's generated `Kernel_Config` as one `opaque kernelConfig : KernelConfig`,
constrained only by what `Kernel_Config_Lemmas` proves (and l4v proves nothing about
`CONFIG_RETYPE_FAN_OUT_LIMIT` / `CONFIG_RESET_CHUNK_BITS`). So `Fl4Spec.retypeFanOutLimit` and
`Fl4Spec.resetChunkBits` are genuinely unspecified: no theorem can pin them (an `opaque` constant does not
unfold; the `Inhabited KernelConfig` instance used to build it says nothing about its value). FL4's values
are definitional in the extracted code (`crates/fl4-core/src/untyped.rs:15,17`, `proofs/Fl4Core/Funs.lean`
`untyped.RETYPE_FAN_OUT_LIMIT := 256#u64`, `untyped.RESET_CHUNK_BITS := 16#u64`).

* **`KCfgFL4`** [P] (global, opaque configuration, the same kind of premise as `hnd : numDomains = 1`,
  `FpuImplDet`, `FpuWriteDet`): the spec's configuration is FL4's build, i.e. `retypeFanOutLimit` equals the
  extracted `untyped.RETYPE_FAN_OUT_LIMIT` and `resetChunkBits` the extracted `untyped.RESET_CHUNK_BITS`.
  Stated against the extracted constants, not literals, so it names exactly FL4's values.
* `KCfgFL4.fan'` / `KCfgFL4.rcb'`: the literal forms (`256#64`, `16`) every per-entry `fan` / `rcb` field
  of the U-chain asks (`JUtPathM`, `JDevPath`, …, `JUtPathMU29`, `JDevPathU28`).
* `kCfgFL4_consistent`: a `KernelConfig` with FL4's two values and one domain exists (the premise does not
  contradict the structure's own constraints, nor `hnd`).

Named premise: `KCfgFL4` [P]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.UntypedResetRefine
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

/-- **The spec's untyped configuration constants are FL4's** [P] (module docstring): Fl4Spec
`opaque kernelConfig` (l4v generated `Kernel_Config.retypeFanOutLimit` / `resetChunkBits`, unspecified in
the port) at FL4's build values `untyped.RETYPE_FAN_OUT_LIMIT` / `untyped.RESET_CHUNK_BITS`. -/
structure KCfgFL4 : Prop where
  /-- [P] `CONFIG_RETYPE_FAN_OUT_LIMIT` is FL4's `RETYPE_FAN_OUT_LIMIT` (`untyped.rs:15`, 256). -/
  fan : Fl4Spec.retypeFanOutLimit = untyped.RETYPE_FAN_OUT_LIMIT.bv
  /-- [P] `CONFIG_RESET_CHUNK_BITS` is FL4's `RESET_CHUNK_BITS` (`untyped.rs:17`, 16). -/
  rcb : Fl4Spec.resetChunkBits = untyped.RESET_CHUNK_BITS.val

/-- The literal fan-out limit asked by the U-chain's per-entry `fan` fields. -/
theorem KCfgFL4.fan' (h : KCfgFL4) : Fl4Spec.retypeFanOutLimit = 256#64 := by
  rw [h.fan]; unfold untyped.RETYPE_FAN_OUT_LIMIT; rfl

/-- The literal reset chunk size asked by the U-chain's per-entry `rcb` fields. -/
theorem KCfgFL4.rcb' (h : KCfgFL4) : Fl4Spec.resetChunkBits = 16 := by
  rw [h.rcb, reset_chunk_bits_eq]; rfl

/-- `KCfgFL4` is consistent with `KernelConfig`'s own constraints and with one domain. -/
theorem kCfgFL4_consistent : ∃ kc : Fl4Spec.KernelConfig, kc.numDomains = 1 ∧
    kc.retypeFanOutLimit = untyped.RETYPE_FAN_OUT_LIMIT.bv ∧ kc.resetChunkBits = untyped.RESET_CHUNK_BITS.val :=
  ⟨⟨1, by decide, by decide, untyped.RESET_CHUNK_BITS.val, untyped.RETYPE_FAN_OUT_LIMIT.bv⟩, rfl, rfl, rfl⟩

end Fl4Proofs.P3

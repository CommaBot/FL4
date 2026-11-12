# FL4

FL4 is a Rust re-implementation of the seL4 17.0 microkernel (MCS API) with
first-class SMP and fine-grained locking. See [DESIGN.md](DESIGN.md).

## Layout

| Path | Contents |
|---|---|
| `crates/fl4-core` | Kernel logic, safe Rust, extracted to Lean by Charon/Aeneas |
| `crates/fl4-abi` | ABI numbering generated from `interfaces/` and the build configuration |
| `crates/fl4-kernel` | The x86_64 kernel image (boot, glue) |
| `crates/fl4-arch-x86_64` | x86_64 hardware backend |
| `crates/fl4-sync`, `fl4-store` | Transaction runtime and object store |
| `crates/fl4-sim` | Deterministic simulator |
| `interfaces/` | The one interface definition (seL4's XML, pruned to FL4's configuration, plus FL4 methods) |
| `libsel4/` | FL4's libsel4 |
| `cmake/` | Drop-in `kernel` directory for seL4 CMake projects such as sel4test |
| `proofs/` | Lean 4 project: `Fl4Core/` is extracted, `Fl4Proofs/` holds the proofs |
| `vendor/seL4` | Pinned upstream seL4 (submodule) |

## Tasks

All kernel runs happen inside QEMU; FL4 is never booted on the host.

```
cargo xtask run [--setup kvm|kvm-reduced|tcg]   # boot the standalone kernel
cargo xtask sel4test [--release] [--smp N] [--setup ...]
cargo xtask extract                              # Charon + Aeneas -> proofs/Fl4Core
(cd proofs && lake build)                        # check the proofs
```

Host dependencies live in `$FL4_DEPS` (default `~/Projects/fl4-deps`):
`venv/` with `sel4-deps`, and an `aeneas/` checkout with Charon built.

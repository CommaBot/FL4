-- AArch64 counterpart of Fl4Proofs.P1.QueueFinIo (a new proof over Fl4CoreA64, not a port.py copy).
/-
P1: the finalisation of an I/O-port cap (`IoPort first last owner`).

a64 (AArch64): `vcpu::revoke_ports` is a no-op on AArch64 (crates/fl4-core/src/arch/aarch64/vcpu.rs: there are
no I/O ports, so no VCPU I/O bitmaps and no VCPU list walk). x86_64's walk along `VCPU_HEAD` / the VCPUs'
`NEXT` words, the stall of the owner's thread and the bitmap writes do not exist, and with them x86_64's
placement `IoPortPlace` (bitmap / `NEXT` words of the listed VCPUs) is not needed: `finGap_ioPort` holds for
every deletion start, a `FinGap` (stronger than x86_64's `FinGapAt` from `IoPortPlaceAt`). The cleanup cap
is the I/O-port cap itself (`DelCapOK` from the cap's), as on x86_64.

No named premises.
-/
import Fl4ProofsA64.P1.QueueFinThr
import Fl4ProofsA64.P1.QueueDecSc
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- `vcpu::revoke_ports` writes nothing on AArch64. -/
theorem vcpu.revoke_ports.same {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (owner low high : U64) :
    vcpu.revoke_ports st ar s a owner low high = ok (s, a) := by
  unfold vcpu.revoke_ports; rfl

/-- **The I/O-port caps' finalisation** (a64: no placement; `revoke_ports` is a no-op). -/
theorem finGap_ioPort {A : Type _} {ar : machine.Arch A} :
    FinGap st ar T Cs Ω H Sg Rp Scs Nt Z (fun c => ∃ x1 x2 x3, c = .IoPort x1 x2 x3) := by
  rintro Ac s0 s a c fin h hc - ⟨f, l, o, rfl⟩
  simp only [objects.finalise_cap, objects.finalise_cap_object, vcpu.revoke_ports.same, bind_ok]
  split
  · exact (WP.spec_ok _).2 ⟨h, DelCapOK.null, hc⟩
  · exact (WP.spec_ok _).2 ⟨h, DelCapOK.null, DelCapOK.null⟩

end

end Fl4ProofsA64.P1

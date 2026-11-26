/-
P2 (int14 wiring): **lvm's `VexitPEnt` with `vfit` / `pusr` from the heap** (line vlift's `P2/E2EVLvmP.lean`,
`vfit_ofK` / `pusr_ofK`, applied to line lvm's `P2/AccessLvmPo.lean` structure).

* **`VexitPEnt.ofHeap`**: builds `VexitPEnt` from its three other fields (`usr` [J], `buf` [P], `aff0` [J]) and, for
  `vfit` / `pusr`, from `VexitEnt.vin`'s fact (`v ≠ 0 → InVcpu K v (v + PENDING)`, whose first part is
  `v ∈ K.vcpus`), `VcpuHeap` [J], `K.heap = H`, `HeapOK H`, `BXI` at P1's sets convention (`T = H.tcbs`,
  `Ω = H.omega`, `Sg = H.frame`, the SCs typed) and `H`'s `other` objects placed against the kernel-state block
  (P3 `JKern.hksIn`, as `vfar`).

So `VexitPEnt.vfit` / `.pusr` are no longer premises of their own: they reduce to `vin` [J] + `VcpuHeap` [J] (both
[J] for the reason in `AccessLvmOwn` / `E2EVHeap`: P3 covers native threads only).
-/
import Fl4Proofs.P2.AccessLvmPo
import Fl4Proofs.P2.E2EVLvmP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMapV (KLayoutV InVcpu)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}

/-- **`VexitPEnt` with `vfit` / `pusr` from the heap** (module docstring). -/
theorem VexitPEnt.ofHeap {m : U64 → U64} {v : U64} {s : S}
    (usr : ∀ x, x ∈ K.user → Aligned x → UsrW st T Cs H Sg Scs Z s x)
    (buf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK {x | x ∈ K.user ∧ Aligned x} b ⦄)
    (aff0 : m (fld (L.curW s) oAFFINITY) = L.mem s (affA (L.curW s)))
    (hvin : v ≠ 0#u64 → InVcpu K v (core.num.U64.wrapping_add v vcpu.PENDING))
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hT : T = H.tcbs) (hΩ : Ω = H.omega)
    (hSg : Sg = H.frame) (hH : HeapOK H) (hScs : ∀ c ∈ Scs, H c = some (.sc (Z c)))
    (hKI : ∀ p z, H p = some (.other z) → p.val + 2 ^ z ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val ∨
      ((L.ksb s).val ≤ p.val ∧ p.val + 2 ^ z ≤ (L.ksb s).val + 13568))
    (hKH : K.heap = H) (hV : E2EV.VcpuHeap K) :
    VexitPEnt K st T Cs H Sg Scs Z m v s where
  usr := usr
  pusr := E2EV.pusr_ofK hI hT hΩ hSg hH hScs hKI hKH hV fun h0 => (hvin h0).1
  buf := buf
  vfit := E2EV.vfit_ofK hH hKH hV fun h0 => (hvin h0).1
  aff0 := aff0

end

end
end Fl4Proofs.P2

/-
P2 (line vlift, gen 2): **one family of every lifted path**, and the end-to-end theorem over it.

* `PathsV.mix LU hW LC hAv` = `PathsV.sum (PathsV.ofPathsU LU hW) (PathsV.ofPathsCut LC hAv)`: the existing paths
  lifted to `ownV` by the layout route (`LU`, taken at `userV K`, `P2/E2EVUser.lean`) and by the generic cut
  (`LC`, read set cut to `rsV K RS`, `P2/E2EVCutP.lean`).
* **`serializable_e2eV_all`**: `ExecV (PathsV.sum (PathsV.mix LU hW LC hAv) LQ)` ⇒ `RunAll`, with `LQ` the paths
  stated directly for `ownV` (the local VM paths, `local_vm_exit`'s `vexit_localPath` on `par/lvm3`).

Which existing paths go where, and with which premises (status of this generation):
* `LU` (route U, premise `NoVcpuRW` [W] per path, a property of its sets):
  - VM fault `vm_localPath`, VM ReplyRecv `rr_localPath`, I/O port `io_localPath`: `NoVcpuRW` **proved**
    (`vm_noVcpuRW`, `rr_noVcpuRW`, `io_noVcpuRW`). Their `Pre` is asked at `userV K` (via `Fl4StepV.start` [P]);
    `vmPre_userV` / `vmRRPre_userV` / `ioLay_userV` give it from the `K` one plus `VcpuKs` (derived from
    `VcpuHeap` [J] and `JKern.hksIn`, `P2/E2EVHeap.lean`) and `TabNoV` (from `VcpuHeap`, `VcpuTabOff`,
    `PoolObj` [J]).
  - SetTimer, timer IRQ (`MaxR` paths): **not yet** (`MaxR` contains the VCPU data words at `userV K`; the
    `x ∉ K.user` conjunct decided in handoff `vlift.md` §gen2 is pending).
* `LC` (route C, premise `AvoidV` [W] per path, the path's runs read no VCPU data word):
  - syscall_local `sl_localPathK`: `AvoidV` not discharged (handoff `vlift.md`).
* `hW` / `hAv` are asked for every `K` with `RegionOKV` / `UserOKV`, as `E2E.Paths` asks its paths.

Premises: `serializable_e2eV`'s, plus `hW` [W] and `hAv` [W].
-/
import Fl4Proofs.P2.E2EVUser
import Fl4Proofs.P2.E2EVCutP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

/-- **The existing paths, lifted by both routes** (module docstring). -/
def PathsV.mix {ι κ : Type} (LU : Paths ι)
    (hW : ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K),
      NoVcpuRW K (LU i (userV K) m (regionOK_userV hK) (userOK_userV hK hU)))
    (LC : Paths κ)
    (hAv : ∀ j (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K),
      AvoidV K (LC j K.toKLayout m hK.base hU.base)) : PathsV (ι ⊕ κ) :=
  PathsV.sum (PathsV.ofPathsU LU hW) (PathsV.ofPathsCut LC hAv)

/-- **End to end over every lifted path and the `ownV`-native paths** (module docstring). -/
theorem serializable_e2eV_all {ι κ ν : Type} (LU : Paths ι)
    (hW : ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K),
      NoVcpuRW K (LU i (userV K) m (regionOK_userV hK) (userOK_userV hK hU)))
    (LC : Paths κ)
    (hAv : ∀ j (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K),
      AvoidV K (LC j K.toKLayout m hK.base hU.base))
    (LQ : PathsV ν) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV} (h0 : Init s0) (hA0 : ArmInv s0)
    (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV (PathsV.sum (PathsV.mix LU hW LC hAv) LQ) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_e2eV _ h0 hA0 hK0 hU0 hM0 h hq

end
end Fl4Proofs.P2.E2EV

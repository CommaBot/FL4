/-
P3 (p3J gen 35), Mc namespace, FL4 only: **the endpoint send writes only `ProjW`**.

* **`sendIpcProjW`**: under P1's invariants over the sets of `H` (`SchedQueuesInv`, `BoundInv`, `XInv`, `SCsOK`,
  `SgOK`), the sender `CanBlock`, a donating send from a sender with an SC (`hdon`, P1/P2's own side condition), the
  endpoint in `H`, and from a `BufK` state (no frame cap in any TCB's IPC-buffer slot at the base state `sE`:
  `NoBufCap sE`, `BufApart sE`), FL4's `endpoint.send_ipc` (any `blocking` / `do_call` / grant / `can_donate`)
  writes only `ProjW H Cs s`. P2 FootN5's `send_ipc.footN` at `Kp = ∅`, `Nd = False`, `U = ∅`, `P3Ok := True`
  (P2's `xg_triv`), its two transfer hypotheses discharged by P3JFltX's `xferOKRS_nb` / `xferFootOKC_nb` with
  `RS := BufK sE` (kept along `KW` writes by `bufK_kw`), as gen 27's `handle_fault.footNB`; the `IpcWN … ∅`
  footprint lies in `ProjW` (P3JMcFlt's `ipcWN_projW`).

No premise beyond the stated hypotheses; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcFlt
import Fl4Proofs.P3.P3JRecvN
import Fl4Proofs.P2.StallAllJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {H : P1.Heap} {Cs Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 35) **`send_ipc` writes only `ProjW`** from a `BufK` state (module docstring). -/
theorem sendIpcProjW (hA : P0.ArchTotal ar) (hH : P1.HeapOK H) {sE : S}
    (hNB : NoBufCap (L := L) (P1.Heap.tcbs H) sE)
    (hP : BufApart (L := L) (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (EH H) sE)
    (s : S) (a : A) (blocking do_call : Bool) (badge : U64) (g gr don : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H s Q R)
    (hB : BoundInv st (P1.Heap.tcbs H) Ac s)
    (hX : XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
      (P1.Heap.ntfns H) (P1.Heap.scBits H) s)
    (hS : SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s)
    (hSg : SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s) (hc : CanBlock st (P1.Heap.tcbs H) Ac s t)
    (hdon : don = true → L.mem s (scA t) ≠ 0#u64) (hHe : H e = some .ep)
    (hK0 : BufK (L := L) (P1.Heap.tcbs H) sE s) :
    endpoint.send_ipc st ar s a blocking do_call badge g gr don t e ⦃ r =>
      P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄ := by
  have hU : UserOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H ∅ s := fun b hb => absurd hb (Set.notMem_empty b)
  have hxf := xferOKRS_nb (Ω := P1.Heap.omega H) (H := H) (Rp := P1.Heap.replies H) (Nt := P1.Heap.ntfns H)
    (P3Ok := fun _ => True) hA hNB hP
  have hxw := xferFootOKC_nb (Ω := P1.Heap.omega H) (H := H) (Rp := P1.Heap.replies H) (Nt := P1.Heap.ntfns H)
    (G := XG st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (fun _ => True)) hA hNB hP
  refine WP.spec_mono (endpoint.send_ipc.footN (Kp := ∅) (Nd := False) hA hxf hxw s a blocking do_call badge g gr
    don t e Q R h hB hX hS hSg hU hc hdon hHe (fun _ _ _ h1 w => bufK_kw hP h1 w) hK0 (xg_triv s)
    (Set.notMem_empty t) (fun y hy => absurd hy (Set.notMem_empty y)) (fun _ h => h) actOut_empty) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh
  exact (WritesA.w hh.1).mono fun _ hb => ipcWN_projW hH h.nodes hb

end

end Fl4Proofs.P3.Mc

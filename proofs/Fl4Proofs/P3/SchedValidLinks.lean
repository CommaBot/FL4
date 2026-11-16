/-
P3 (DESIGN.md §9): **`ScLinkHyp` at related states** (for `schedValid_of`):
an SC's thread and notification, and a TCB's bound notification, exist in
the spec, from the spec's SCs and TCBs being the relations' (`ObjCover`),
the SC relation (`ScRel1`: the `TCB` and `NTFN` words), the IPC relation
(TCBs, notifications, `TcbRel.bound`) and P1's `ScExtra0` (the words name
TCBs and notifications): `scLinkHyp_of`.
-/
import Fl4Proofs.P3.SchedValidRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
open Fl4Spec

theorem scW_tcb (c : U64) : scW c 24#u64 = scTcbA c := by unfold scW scTcbA layout.sc.TCB; rfl
theorem scW_ntfn (c : U64) : scW c 40#u64 = scNtfnA c := by unfold scW scNtfnA layout.sc.NTFN; rfl

/-- **`ScLinkHyp` from the relations and P1's `ScExtra0`.** -/
theorem scLinkHyp_of {N T E R C Cs Scs Nt : Set U64} {B : Set (U64 × Word)} {s : S} {σ : State Unit}
    (hI : Ipc.IpcRel N T E R B (L.mem s) σ) (hCv : ObjCover N T E R C σ)
    (hscs : ∀ c ∈ C, ∃ x n, σ.kheap c.bv = some (.schedContext x n) ∧ ScRel1 st s c x n)
    (hCS : ∀ c ∈ C, c ∈ Scs) (hX : ScExtra0 st T Cs Scs Nt s) (hNt : ∀ n ∈ Nt, n ∈ N) :
    ScLinkHyp σ := by
  have scOf : ∀ sc y k, σ.kheap sc = some (.schedContext y k) → ∃ c ∈ C, c.bv = sc ∧ ScRel1 st s c y k := by
    intro sc y k hk
    obtain ⟨c, hc, rfl⟩ := hCv.sc sc y k hk
    obtain ⟨x, n, hk', hr⟩ := hscs c hc
    rw [hk] at hk'; cases hk'
    exact ⟨c, hc, rfl, hr⟩
  refine ⟨fun sc y k f hk hy => ?_, fun sc y k n hk hy => ?_, fun t x n hk hb => ?_⟩
  · obtain ⟨c, hc, rfl, hr⟩ := scOf sc y k hk
    rw [hr.tcb, scW_tcb] at hy
    obtain ⟨h0, rfl⟩ := optRef_some hy
    obtain ⟨x, hkx, -⟩ := hI.tcb _ (hX.yt.1 c (hCS c hc) h0)
    exact ⟨x, hkx⟩
  · obtain ⟨c, hc, rfl, hr⟩ := scOf sc y k hk
    rw [hr.ntfn, scW_ntfn] at hy
    obtain ⟨h0, rfl⟩ := optRef_some hy
    obtain ⟨xn, hkn, -⟩ := hI.ntfn _ (hNt _ (hX.scn c (hCS c hc) h0))
    exact ⟨xn, hkn⟩
  · obtain ⟨u, hu, rfl⟩ := hCv.tcb t x hk
    obtain ⟨x', hk', hR⟩ := hI.tcb u hu
    rw [hk] at hk'; cases hk'
    rw [hR.bound] at hb
    obtain ⟨h0, rfl⟩ := optRef_some hb
    obtain ⟨xn, hkn, -⟩ := hI.ntfn _ (hNt _ (hX.bnd u hu h0))
    exact ⟨xn, hkn⟩

end

end

end Fl4Proofs.P3.Sched

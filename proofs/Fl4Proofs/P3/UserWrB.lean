/-
P3 (DESIGN.md §9), line slhuf: **a write of any user word at `JAtZ`**.

`JAtZ.userWrJ` (XTopJointData) writes one word `wp ∈ Z.B` and moves the spec's
`underlyingMemory` by the matching store (`Endp.setUm`), all ghosts kept, given two
facts of the word: apart from every non-`other` object of `H` and inside a spec
object. `JAtZ.bufWord` gives them for an IPC-buffer word. Here they are derived
for **every** word of `Z.B` from `JAtZ` alone, so a user step (any aligned word of
any user frame, any value) keeps `JAtZ` with σ moved by the user-memory update:

* `JAtZ.bWordOK`: `BufWordOK H σ wp.1` for every `wp ∈ Z.B`.
  - apart from `H`'s non-`other` objects (TCBs, endpoints, notifications, replies,
    SCs; CNodes are `other`): a TCB of `H` is one of `Z.th` (`JPlaced.tcb`), so of
    `Z.T` (`thT`), apart by `EPlaced.bt`; endpoints / replies / notifications are
    the sets' (`JAtZ.hset`), apart by `EPlaced.be` / `br` and `BufPlaced.ntfn`; an
    SC of `H` is in `Z.C` (`hscC`), its spec SC (`screply_obj`) of the same size
    (`JPlaced.sc`), apart by `BufPlaced.sc`. Alignment (`EPlaced.balign`, the
    objects' alignment) turns `<` into `+ 8 ≤`.
  - inside a spec object: the word's non-device data page (`JCarry.bufPg`).
* `JAtZ.userWrB`: `JAtZ.userWrJ` at any word of `Z.B` (`BufPlaced` by
  `JAtZ.bufPlacedJ`), no premise.

No named premise.
-/
import Fl4Proofs.P3.XTopJointData
import Fl4Proofs.P3.BufInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **Every word of `Z.B` is a `BufWordOK` word at `J`** (module docstring). -/
theorem JAtZ.bWordOK (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {wp : U64 × Fl4Spec.Word}
    (hwB : wp ∈ Z.B) : BufWordOK H σ wp.1 := by
  have hP := J.xtop.fin.1.2
  have hal : wp.1.val % 8 = 0 := (hP.ep.balign wp hwB).1
  have hBP := J.bufPlacedJ
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  refine ⟨fun p k hp hk => ?_, ?_⟩
  · cases k with
    | tcb =>
      have hT : p ∈ Z.T := J.thT p ((hJ.tcb p).2 hp)
      have h4 : p.val % 4096 = 0 := by simpa using (hP.ep.tcb p hT).align
      have := hP.ep.bt wp hwB p hT
      simp only [P1.HKind.bits]
      omega
    | ep =>
      have hE : p ∈ Z.E := J.hset.1 p hp
      have h16 := (hP.ep.ep p hE).1
      have := hP.ep.be wp hwB p hE
      simp only [P1.HKind.bits]
      omega
    | ntfn =>
      have hN : p ∈ Z.N := J.hset.2.1 p hp
      have := hBP.ntfn wp hwB p hN
      simp only [P1.HKind.bits]
      omega
    | reply =>
      have hR : p ∈ Z.R := J.hset.2.2 p hp
      have h32 := (hP.ep.rep p hR).1
      have := hP.ep.br wp hwB p hR
      simp only [P1.HKind.bits]
      omega
    | sc z =>
      have hC : p ∈ Z.C := J.hscC p z hp
      obtain ⟨x, n, hkx, -⟩ := screply_obj J.xtop.fin.1.1.1 hC
      have hH := (hJ.sc p x n (J.c0 p hC) hkx).2
      rw [hp] at hH
      injection hH with hH
      injection hH with hz
      subst hz
      have := hBP.sc wp hwB p hC x n hkx
      simp only [P1.HKind.bits]
      omega
    | other z => exact absurd rfl (hk z)
  · obtain ⟨q, vms, hq, h1, h2⟩ := J.carry.bufPg wp hwB
    have e : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := rfl
    exact ⟨q, _, hq, h1, by rw [e]; omega⟩

/-- **A write of any word of `Z.B` at `J`** (module docstring): `JAtZ` after at the same
ghosts, the spec's user memory moved by the matching store. -/
theorem JAtZ.userWrB (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {wp : U64 × Fl4Spec.Word}
    (hwB : wp ∈ Z.B) (v : U64) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.wr s wp.1 v) a
      (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv)) :=
  J.userWrJ J.bufPlacedJ hwB (J.bWordOK hwB).1 (J.bWordOK hwB).2 v

end

end

end Fl4Proofs.P3

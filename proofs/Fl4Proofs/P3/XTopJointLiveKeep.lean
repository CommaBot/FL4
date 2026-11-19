/-
P3 (DESIGN.md §9), CSpace: **`LiveJ` and `DbgWF` across a deletion-loop step
that keeps the slots** (toward carrying XTopJointLive's `LiveJ` and DbgWF's
`DbgWF` through the loop instead of XTopJointDelR's `JDelParts.live`).

* `dbgNth_keep`: the debug list walked from a TCB (or `0`) is the same when
  the TCBs' `DEBUG_NEXT` words are (`DbgTz`: each link `0` or a TCB).
* `LiveJ.of_same`: a step keeping every slot (`SlotsSame`), the original
  bits, the debug words (`DbgKeep`, XTopJointDbgKeep) and the dead TCBs
  (`DeadP`) keeps `LiveJ` at the same MDB ghost.
* `DbgWFL.of_keep`: `DbgKeep` and the affinities kept keep `DbgWFL` at the
  same lists; `JAtZ.dbgWF_keep`: the affinities from `JAtZ` before and after
  (`SchedCore.aff`: every TCB on the current core).
-/
import Fl4Proofs.P3.XTopJointDbgKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- **The debug list walked over kept links** (module docstring). -/
theorem dbgNth_keep {T : Set U64} {m m' : U64 → U64} (hdn : ∀ y ∈ T, m' (P1.dnA y) = m (P1.dnA y))
    (hcl : ∀ y ∈ T, P1.Tz T (m (P1.dnA y))) : ∀ (n : Nat) (h : U64), P1.Tz T h → dbgNth m' n h = dbgNth m n h := by
  intro n
  induction n with
  | zero => intro h _; rfl
  | succ n ih =>
    intro h hh
    simp only [dbgNth]
    by_cases h0 : h = 0#u64
    · simp [h0]
    · have hT : h ∈ T := hh.ne0 h0
      simp only [h0, ↓reduceIte]
      rw [hdn h hT]
      exact ih _ (hcl h hT)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`LiveJ` across a step keeping the slots** (module docstring). -/
theorem LiveJ.of_same {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {Cs : Set U64} {s s' : S}
    {σ σ' : Fl4Spec.State Unit} (hL : LiveJ (L := L) th H G s σ) (hSS : SlotsSame th (L.mem s) (L.mem s'))
    (hmem : ∀ y ∈ G.chains.flatten, IsSlot th y) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hc0 : 0#u64 ∈ Cs) (hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s)
    (hdead : ∀ p, DeadP (L := L) H s p → DeadP (L := L) H s' p) :
    LiveJ (L := L) th H G s' σ' := by
  have hU : ∀ y, IsSlot th y → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := fun y hy hu => by
    unfold InUse at hu ⊢
    rw [hSS.capV hy, horig] at hu
    exact hu
  have hhd : dbgHead (L := L) s' = dbgHead (L := L) s := by
    unfold dbgHead
    rw [nodeAt_of_ksb hK.1]
    exact hK.2 _ (Or.inr ⟨0#u64, hc0, rfl⟩)
  have hN : ∀ n, dbgNth (L.mem s') n (dbgHead (L := L) s') = dbgNth (L.mem s) n (dbgHead (L := L) s) := fun n => by
    rw [hhd]
    exact dbgNth_keep (fun y hy => hK.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (fun y hy => hTz.dn y hy) n _ (hTz.dh _ hc0)
  refine ⟨fun q i hqi hu => ?_, fun n hn => ?_, fun y hy p zt n hz i hpi hni hu => ?_,
    fun y hy p zt n hz hzt => ?_⟩
  · obtain ⟨y, hy, hr⟩ := hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hu)
    exact ⟨y, hy, by rw [hSS.capV (hmem y hy)]; exact hr⟩
  · rw [hN] at hn ⊢
    obtain ⟨y, hy, hr⟩ := hL.dbg n hn
    exact ⟨y, hy, by rw [hSS.capV (hmem y hy)]; exact hr⟩
  · exact hL.zslots y hy p zt n (by rw [← hSS.capV hy]; exact hz) i hpi hni (hU _ ⟨p, i, hpi, rfl⟩ hu)
  · exact hdead p (hL.zdead y hy p zt n (by rw [← hSS.capV hy]; exact hz) hzt)

/-- The TCBs of the TCB zombies (type 65) in the slots. -/
def ZTcb (th : TypedHeap) (s : S) : Set U64 :=
  {p | ∃ y, IsSlot th y ∧ ∃ zt n, capV (L.mem s) y = .Zombie p zt n ∧ zt.val = 65}

/-- `LiveJ.zdead` on `ZTcb`. -/
theorem LiveJ.ztcb {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s : S} {σ : Fl4Spec.State Unit}
    (hL : LiveJ (L := L) th H G s σ) : ∀ p ∈ ZTcb (L := L) th s, DeadP (L := L) H s p :=
  fun _ ⟨y, hy, zt, n, hz, h65⟩ => hL.zdead y hy _ zt n hz h65

/-- **`LiveJ.of_same` with only the TCB zombies' TCBs dead after** (`ZTcb`). -/
theorem LiveJ.of_sameZ {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {Cs : Set U64} {s s' : S}
    {σ σ' : Fl4Spec.State Unit} (hL : LiveJ (L := L) th H G s σ) (hSS : SlotsSame th (L.mem s) (L.mem s'))
    (hmem : ∀ y ∈ G.chains.flatten, IsSlot th y) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (hc0 : 0#u64 ∈ Cs) (hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s)
    (hdead : ∀ p ∈ ZTcb (L := L) th s, DeadP (L := L) H s' p) :
    LiveJ (L := L) th H G s' σ' := by
  have hU : ∀ y, IsSlot th y → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := fun y hy hu => by
    unfold InUse at hu ⊢
    rw [hSS.capV hy, horig] at hu
    exact hu
  have hhd : dbgHead (L := L) s' = dbgHead (L := L) s := by
    unfold dbgHead
    rw [nodeAt_of_ksb hK.1]
    exact hK.2 _ (Or.inr ⟨0#u64, hc0, rfl⟩)
  have hN : ∀ n, dbgNth (L.mem s') n (dbgHead (L := L) s') = dbgNth (L.mem s) n (dbgHead (L := L) s) := fun n => by
    rw [hhd]
    exact dbgNth_keep (fun y hy => hK.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (fun y hy => hTz.dn y hy) n _ (hTz.dh _ hc0)
  refine ⟨fun q i hqi hu => ?_, fun n hn => ?_, fun y hy p zt n hz i hpi hni hu => ?_,
    fun y hy p zt n hz hzt => ?_⟩
  · obtain ⟨y, hy, hr⟩ := hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hu)
    exact ⟨y, hy, by rw [hSS.capV (hmem y hy)]; exact hr⟩
  · rw [hN] at hn ⊢
    obtain ⟨y, hy, hr⟩ := hL.dbg n hn
    exact ⟨y, hy, by rw [hSS.capV (hmem y hy)]; exact hr⟩
  · exact hL.zslots y hy p zt n (by rw [← hSS.capV hy]; exact hz) i hpi hni (hU _ ⟨p, i, hpi, rfl⟩ hu)
  · exact hdead p ⟨y, hy, zt, n, by rw [← hSS.capV hy]; exact hz, hzt⟩

/-- **`DbgWFL` across a step keeping the debug words and the affinities.** -/
theorem DbgWFL.of_keep {T Cs : Set U64} {s s' : S} {lst : U64 → List U64}
    (hW : DbgWFL T Cs (L.mem s) (dbgHd (L := L) s) lst) (hK : P1.DbgKeep st T Cs s s')
    (haff : ∀ y ∈ T, L.mem s' (P1.affA y) = L.mem s (P1.affA y)) :
    DbgWFL T Cs (L.mem s') (dbgHd (L := L) s') lst :=
  hW.congr (fun y hy => ⟨hK.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩), hK.2 _ (Or.inl ⟨y, hy, Or.inr rfl⟩), haff y hy⟩)
    (fun c hc => by rw [dbgHd_of_ksb hK.1]; exact hK.2 _ (Or.inr ⟨c, hc, rfl⟩))

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

/-- **A dead set joins the dead set** (as XTopJointFinThreadU's `JAtZ.addDead`). -/
theorem JAtZ.addDeadSet {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {E : Set U64}
    (hd : ∀ p ∈ E, DeadP (L := L) H s p) : JAtZ (L := L) arI AR Z H Cs Ac Lst (D ∪ E) s a σ :=
  { J with
    jcov := ⟨fun q k hq => (J.jcov.th q k hq).imp_right (Or.imp_left Or.inl),
      fun q k hq => (J.jcov.h q k hq).imp_right (Or.imp_left Or.inl),
      fun q hq => hq.elim (J.jcov.dead q) (hd q),
      J.jcov.ks, J.jcov.idleOut⟩
    kern := { J.kern with } }

/-- **`DbgWFL` across a `JAtZ` step keeping the debug words** (the
affinities: every TCB on the current core before and after). -/
theorem JAtZ.dbgWF_keep {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {Z' : XSets} {Ac' : Set U64} {Lst' : U64 → List U64}
    {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (J' : JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' s' a' σ') (hZT : Z'.T = Z.T) (hZc : Z'.c = Z.c)
    {lst : U64 → List U64} (hW : DbgWFL (P1.Heap.tcbs H) Cs (L.mem s) (dbgHd (L := L) s) lst)
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') :
    DbgWFL (P1.Heap.tcbs H) Cs (L.mem s') (dbgHd (L := L) s') lst := by
  obtain ⟨Q0, R0, hc0, -⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q1, R1, hc1, -⟩ := J'.xtop.fin.1.1.1.lists
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  refine hW.of_keep hK fun y hy => ?_
  rw [hc1.aff y (by rw [hZT, hTe]; exact hy), hc0.aff y (by rw [hTe]; exact hy), hZc]

end

end

end Fl4Proofs.P3

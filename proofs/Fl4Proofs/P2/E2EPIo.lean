/-
P2 (line pte, gen 6): **the I/O port path reads no PTE word** (the `io` field of `P3AvP4`, discharged).

The I/O port's read set `IoRS (userV K)` = `Aligned ∧ ∉ user ∧ RPerm` excludes user words, so the `userP` trick of
`P2/E2EPIrq.lean` applies, now that line iolay narrowed `IoLay.ks` (an `IoPre` holds at P3 layouts):

* `ioLay_userP` / `ioPre_userP`: `IoPre` at `userP K` from `IoPre` at `userV K` and two PTE facts: a PTE is region
  `.none` (`RegionOKP.none`) and outside the kernel-state block (`ks_block_pte`, from `PteSl`'s `KsNoE`);
* `alt_userP`: an alternative for `IoRS (userV K)` is one for `IoRS (userP K)` (`IoRS (userP K) = IoRS (userV K) ∖ ptes`);
* acc: `io_acc` at `userP K` (guard `IoRS (userP K) ⊆ IoRS (userV K) ∖ ptes`); declines from every alternative:
  **`io_ra_decU`** (`P2/AccessIoRaU.lean`, p2io's `io_ra_dec` at `R := Aligned ∖ user`) at `userP K`; prog: p2io's
  `io_isProgOn` at `userP K`, the tree being the slot's (`hpz.choose`, rebuilt from famw's `io_hro`).
* **`io_avoidP`**: no new premise (`PteSl` [J]).
-/
import Fl4Proofs.P2.E2EPStm
import Fl4Proofs.P2.AccessIoRaU
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

section lay
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutP}

/-- A word of the kernel-state block is no PTE word (`KsNoE`). -/
theorem ks_block_pte (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) {b : U64} (h1 : K.ksb.val ≤ b.val)
    (h2 : b.val < K.ksb.val + 13568) : b ∉ K.ptes := by
  have hb64 : b.val < 2 ^ 64 := by have := b.hBounds; simpa using this
  have hk64 : K.ksb.val < 2 ^ 64 := by have := K.ksb.hBounds; simpa using this
  have hb := hks (core.num.U64.wrapping_sub b K.ksb) (by
    simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]; omega)
  have e : core.num.U64.wrapping_add K.ksb (core.num.U64.wrapping_sub b K.ksb) = b := by
    apply UScalar.eq_of_val_eq
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]
    omega
  rw [e] at hb
  exact hb

theorem ioLay_userP (hK : RegionOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV)
    (hL : IoLay (userV K.toKLayoutV)) : IoLay (userP K) where
  node := hL.node
  tcbw := hL.tcbw
  slotw := hL.slotw
  slot8 := hL.slot8
  tslot := hL.tslot
  scw := hL.scw
  ks := hL.ks
  ksf := hL.ksf
  user b hb := Or.elim hb (fun h => hL.user b h)
    (fun h => ⟨hK.none b h, fun hk => ks_block_pte hks hk.1 hk.2 h⟩)

theorem ioPre_userP (hK : RegionOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) {s : S}
    (P : IoPre st (userV K.toKLayoutV) T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    IoPre st (userP K) T Cs Ω H Sg Rp Scs Nt Z Ac s :=
  { P with lay := ioLay_userP hK hks P.lay }

/-- An alternative for `IoRS (userV K)` is one for `IoRS (userP K)`. -/
theorem alt_userP {Locks : S → U64 → Prop} {m0 : U64 → U64} {s s' : S}
    (Al : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) Locks s) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m0) (· ∈ (userV K.toKLayoutV).user) s s') :
    PathObl.Alt st (IoRS (st := st) (userP K) Locks s) (OwnMap.cls (userP K)) (OwnMap.ko (userP K) m0)
      (· ∈ (userP K).user) s s' where
  cpu := Al.cpu
  ksb := Al.ksb
  masks := Al.masks
  read x hx := Al.read x ⟨hx.1, fun hu => hx.2.1 (Or.inl hu), hx.2.2⟩
  clsEq x hx hu hk := Al.clsEq x (fun hr => hx ⟨hr.1, fun hu' => Or.elim hu' hr.2.1 (fun hp => hu (Or.inr hp)),
    hr.2.2⟩) (fun h => hu (Or.inl h)) hk

end lay

section io
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **The I/O port's route-U path reads no PTE word**, from `PteSl` [J] (module docstring). -/
theorem io_avoidP_path (i : IoArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hPS : PteSl st K) (h : (ioSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) ((ioSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h) := by
  have vf : VFacts L K.toKLayoutV := VFacts.ofEmpty h.1 h.2.bun.choose_spec
  have pre : ∀ s, SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s →
      IoPre st (userV K.toKLayoutV) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac s :=
    fun s hs => ioPre_userV hK.base (vf.v hs.1).1 (h.2.pe s hs.1 hs.2)
  have preP : ∀ s, SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s →
      IoPre st (userP K) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac s :=
    fun s hs => ioPre_userP hK hPS.1 (pre s hs)
  have hro := io_hro (K := userV K.toKLayoutV) (Locks := i.Locks) (m0 := m) hA (number := i.number)
    (P := fun s => SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s) pre
  have hex : ∃ p : SProg Bool, IsProg (ioBodyP S i.number) p ∧ NoZero p ∧
      ∀ s s' a r, (SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s) →
        (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a i.number = ok (true, s1, a1)) →
        PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' →
        interp st ar p s' a = ok r →
        E2E.Once st ar (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (· ∈ (userV K.toKLayoutV).user) ∅ ∅ p s' a :=
    ⟨_, io_isProg S i.number, io_noZero i.number, hro⟩
  have hIP := io_isProgOn (K := userV K.toKLayoutV) (Locks := i.Locks) (m0 := m) hA
    (P := fun s => SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s) pre (io_isProg S i.number)
  refine ⟨?_, ?_, ?_⟩
  · intro s a r hs hr hb
    have hs' : SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s := hs
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : syscall.handle_ioport_local st ar s a i.number = ok (true, s1, a1) := hr
    have g1 := io_acc hA (Locks := i.Locks) (pre s hs') hr'
    have g2 := io_acc hA (Locks := i.Locks) (preP s hs') hr'
    have e := fun (st' : machine.Store S) (N : Narrow st st') => hIP st' N s (AltOf.pre hs') a
    have w1 := (interp_guard _ s a _ ((e _ (Narrow.guard _ _ _)).symm.trans g1)).2
    have w2 := (interp_guard _ s a _ ((e _ (Narrow.guard _ _ _)).symm.trans g2)).2
    show syscall.handle_ioport_local
      (guard st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (IoWS (st := st) (userV K.toKLayoutV) i.Locks s)) ar s a i.number = ok (true, s1, a1)
    exact (e _ (Narrow.guard _ _ _)).trans (guard_of_within (st := st) (L := L) (ar := ar) _ s a _
      ((e _ (Narrow.self _)).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.1 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2)))
  · intro s a r hs hr hn s' r' hA' h'
    have hs' : SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s := hs
    have hAl : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have hr' : syscall.handle_ioport_local st ar s a i.number = ok r := hr
    have h'' : syscall.handle_ioport_local st ar s' a i.number = ok r' := h'
    have hn' : r.1 ≠ true := hn
    have g := io_ra_decU hA (Locks := i.Locks) (m0 := m) (preP s hs') (alt_userP hAl) hr' hn' h''
    have e := fun (st' : machine.Store S) (N : Narrow st st') => hIP st' N s' ⟨s, hs', hAl⟩ a
    show syscall.handle_ioport_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a i.number = ok r'
    exact (e _ (Narrow.guard _ _ _)).trans (interp_mono (st := st) (fun q hq hp => hq.2 (Or.inr hp))
      (fun _ h => h) _ (io_noZero i.number) s' a r' ((e _ (Narrow.guard _ _ _)).symm.trans g))
  · intro st' N σ g a
    obtain ⟨s, hs, hAc⟩ := g
    have hs' : SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s := hs
    have hAc' : PathObl.Alt st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (OwnMap.cls (userV K.toKLayoutV)) (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s σ := hAc
    have g2 : AltOf st (fun s => SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s)
        (IoRS (st := st) (userP K) i.Locks) (OwnMap.cls (userP K)) (OwnMap.ko (userP K) m) (· ∈ (userP K).user) σ :=
      ⟨s, hs', ⟨hAc'.cpu, hAc'.ksb, hAc'.masks,
        fun x hx => hAc'.read x ⟨⟨hx.1, fun hu => hx.2.1 (Or.inl hu), hx.2.2⟩, fun hp => hx.2.1 (Or.inr hp)⟩,
        fun x hx hu hk => hAc'.clsEq x (fun hr => hx ⟨hr.1.1, fun hu' => Or.elim hu' hr.1.2.1 hr.2, hr.1.2.2⟩)
          (fun h => hu (Or.inl h)) hk⟩⟩
    exact io_isProgOn (K := userP K) (Locks := i.Locks) (m0 := m) hA
      (P := fun s => SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s) preP (Classical.choose_spec hex).1 st' N σ g2 a

/-- **The I/O port path reads no PTE word** (the `io` field of `P3AvP`), from `PteSl` [J]. -/
theorem io_avoidP (i : IoArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hPS : PteSl st K) (h : (ioSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K ((ioSlotP3W st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (ioSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)) := by
    rintro P W rfl
    exact avoidE_liftAtV hK.base _ W (io_avoidP_path st ar hA hm i K m hK hU hPS h)
  exact key _ _ (SlotU.fam_pos _ _ h)

end io

end
end Fl4Proofs.P2.E2EP

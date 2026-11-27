/-
# P2 (line p3mc, gen 29): every PTE-arm CNodeDelete run on a checked store cut by a word class

Handoff §33d item 1. The PTE-arm (`delPteSlot`) analogue of gen 28's `inv_run_gdA` (P2/InvDelGdA): at an entry
`SlJAt ∧ InvQFP` with the reachability convention `CvP`, every run of the invocation runs on the checked store
`gd st R Pw` as on `st`, for any read set `R` holding the `IoRS` words off the leaf entries that a class `G` keeps
(`hR`), the aligned user words (`hRu`) and the **locked leaf entries** (`hRe`), and any write predicate allowing the
prefix words, the slot words, `dest`'s `CAP0 := 0`, the caller's `STATE`, the user words (`hWu`) and the locked leaf
entries (`hWe`, the `unmapLeaf` write `e := 0`).

* **`inv_run_gdP`**: accepted runs by `inv_acc_genV`, the decode block split by `length < 2`: `truncAccV` /
  `truncFinV` (P2/InvDelV, the arm does not matter there) or `delAccPV` / `delFinPV` (P2/InvDelPteV; the leaf `e`
  is a `K.ptes` word by `ptesR_of_spe`); declined runs by `inv_dec_genV` + `io_alt_midRV`.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelGdA
import Fl4Proofs.P2.InvDelPteV
import Fl4Proofs.P2.InvDelPteMoveP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame GateField TimerField)

section gdP
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **Every PTE-arm CNodeDelete run runs on the checked store `gd st R Pw` as on `st`** (module docstring). -/
theorem inv_run_gdP {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) {s : S}
    (hE : SlJAt (L := L) K.toKLayout s ∧ InvQFP st Cs Ω Sg Ac Locks p K.toKLayout m s)
    (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) (hcv : CvP st K s)
    {R G : U64 → Prop} {Pw : S → U64 → U64 → Prop}
    (Gc : GCl st K.toKLayout K.toKLayout.heap.scBits G s)
    (hR : ∀ b, IoRS (st := st) K.toKLayout Locks s b → b ∉ K.ptes → G b → R b)
    (hGs : ∀ b, SlotW K.toKLayout b → G b) (hGv : ∀ b, VsW K.toKLayout b → b ∉ K.ptes → G b)
    (hW : IoWr st (WAll Pw) K.toKLayout.heap.scBits s)
    (hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
      (16 ≤ o.val ∨ (¬ TcbSlot K.toKLayout q ∧ NullOrFrame (L.mem s q))) →
        WAll Pw (core.num.U64.wrapping_add q o))
    (hw0 : ∀ q, q ∈ K.slots → Locks s q → ¬ TcbSlot K.toKLayout q → NullOrFrame (L.mem s q) →
      ∀ x, Pw x q 0#u64)
    (hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      ∀ x, Pw x (core.num.U64.wrapping_add (L.curW s) layout.tcb.STATE) v)
    (hRu : ∀ b, PathObl.UserW K.toKLayout b → R b) (hWu : ∀ b, PathObl.UserW K.toKLayout b → WAll Pw b)
    (hRe : ∀ b, b ∈ K.ptes → Locks s b → R b) (hWe : ∀ b, b ∈ K.ptes → Locks s b → WAll Pw b)
    {a : A} {number : I64} {r : Bool × S × A}
    (h : syscall.handle_invocation_local st ar s a number p = ok r) :
    syscall.handle_invocation_local (gd st R Pw) ar s a number p = ok r := by
  obtain ⟨hJ, hq⟩ := hE
  have PE := hq.1.1.1
  have hL : Slot8 K.toKLayout := fun q hq => PE.lay.slot8 q hq
  have hR' : ∀ b, IoRSR st K.toKLayout Locks s b → G b → R b := fun b h g =>
    hR b h.1 (ioRSR_rsE hK hks h).2 g
  obtain ⟨cp, cr, cg, cgb, dest, fp0, rt0, asid0, va0, e0, C0, hcs, hsK, -, -, -, -, -, hdK, -, hLd, -, -,
    hSn, -⟩ := del_coreP hq
  have hSeen : ∀ x, SeenW p x → R x := by
    intro x hx
    have hd0 : dest ≠ 0#u64 := fun e => hz_of K.toKLayout s hJ (e ▸ hdK)
    obtain ⟨o, ho, rfl⟩ := hSn x hx
    have hov : o.val < 32 ∧ o.val % 8 = 0 := by
      rcases ho with rfl | rfl | rfl | rfl <;>
        simp [layout.cte.CAP0, layout.cte.CAP1, layout.cte.PREV, layout.cte.NEXT]
    exact hR' _ (PE.lockSlotR hdK (hLd hd0) hov.1 hov.2) (hGs _ (slotW_of hL hdK hov.1))
  have hps : R p.slot ∧ R (core.num.U64.wrapping_add p.slot 8#u64) := by
    have e := invPsR_of (L := L) hq
    exact ⟨hR' _ e.1 (Gc.sl _ hsK).1, hR' _ e.2 (Gc.sl _ hsK).2⟩
  have hmi : R (regA (L.curW s) layout.reg.MSG_INFO) :=
    hR' _ (PE.regR (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1 (Gc.r _ (by simp [layout.reg.MSG_INFO]))
  have hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64) :=
    hR' _ (PE.homeR (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField])).1 (Gc.t _ (by simp) (by simp) (by simp))
  have hnx : R (regA (L.curW s) layout.reg.NEXT_IP) :=
    hR' _ (PE.regR (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1 (Gc.r _ (by simp [layout.reg.NEXT_IP]))
  have Ent := PE.entV Gc hR' hW
  have hst' : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING → SWr (gd st R Pw) st (L.curW s) v :=
    fun v hv X => gd_write (hst v hv X)
  obtain ⟨b, s', a'⟩ := r
  by_cases hb : b = true
  · subst hb
    refine inv_acc_genV (gS := gd st R Pw) (W := WAll Pw) hA PE hW Ent hmi hfl hnx
      (fun C hroot hcl hsl hsc0 info emi => PE.midV Gc hR' hW hroot hcl hsl hsc0 info emi) hSeen hps ?_ h
    intro info nx s1 s2 a1 buf length cap emi C hl hcap y hy
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hq
    have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
    rw [hlbl] at hy ⊢
    by_cases hlt : length < 2#u64
    · obtain ⟨hdec, hrep⟩ := truncAccV (R := R) (G := G) (gS := gd st R Pw) hA PE hR' (fun o ho => Gc.n o ho)
        (Gc.t 3512#u64 (by simp) (by simp) (by simp))
        (fun bsl hb => Gc.sl _ (PE.lay.tslot _ (PE.hT _ PE.cT) _ bsl hb (by simp [layout.tcb.SLOT_BUFFER])).1)
        hRu hW hWu hcs hsK (invBufJ8_of hJ) C hcap hlt hy
      refine ⟨hdec, fun z hz' => ?_⟩
      obtain ⟨h1, h2⟩ := truncFinV (Locks := Locks) (gS := gd st R Pw) hA PE Ent (hst' _ (Or.inr rfl)) hcs hsK
        (invBufJ8_of hJ) C hcap hlt hy hz'
      exact ⟨hrep z hz', h1, h2⟩
    have hlen' : ¬ length < 2#u64 := hlt
    have E := delEntP_of (P := fun s => SlJAt (L := L) K.toKLayout s) hJ hq (invCdtJ_of (fun _ h => h))
      (hz_of _ s hJ)
    have hvs := invVsJ_of (st := st) (P := fun s => SlJAt (L := L) K.toKLayout s) (fun _ h => h)
    have hlf := invLeafJ_of (st := st) (P := fun s => SlJAt (L := L) K.toKLayout s) (fun _ h => h) s hJ
    have hvs2 : ∀ sl fp rt asid va, sl ∈ K.slots →
        obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
        va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧
          VsRd st K.toKLayout s asid va :=
      fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hJ hsl hc hA
    obtain ⟨m1, hconv, hag⟩ := hcv
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
    have hsub : ∀ b, b ∈ K.ptes → Fl4Proofs.P3.Vs.PtW Zx.L1 b := fun b hb =>
      ptesR_sub B hag b (by rw [← hconv]; exact hb)
    have hpte : ∀ asid va e, localinv.small_page_entry st s asid va = ok (some e) → e ∈ K.ptes :=
      fun asid va e he => by rw [hconv]; exact ptesR_of_spe B hag nv he
    have hmx := maxA_facts PE.bxi.2.2.1.1 PE.cscS
    obtain ⟨hdec, hrep⟩ := delAccPV (R := R) (X := (· ∈ K.ptes)) (G := G) (gS := gd st R Pw) hA PE hW hwS
      (fun q hq hl hT hn x => gd_write (hw0 q hq hl hT hn x)) hst' E hsK hlen' (B.vsJX hsub)
      (fun b hb => ⟨(hU.kern b hb).1, hK.none b hb, (hU.kern b hb).2⟩)
      hR hGs (fun o ho => Gc.n o ho)
      (by have := Gc.t 3328#u64 (by simp) (by simp) (by simp); rw [Fl4Proofs.P1.stA_eq]; exact this)
      (Gc.t 3464#u64 (by simp) (by simp) (by simp)) (Gc.t 3592#u64 (by simp) (by simp) (by simp))
      (Gc.sc _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩) (fun r hr => Gc.r r hr) hGv
      (fun asid va e he hl' => hRe e (hpte asid va e he) hl') hlf
      (fun asid va e he hl' => hWe e (hpte asid va e he) hl') C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := delFinPV (gS := gd st R Pw) hA PE Ent (hst' _ (Or.inr rfl)) E hsK hlen'
      (fun sl fp rt asid va hsl hc hA => hvs2 sl fp rt asid va hsl hc hA) hlf C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · exact inv_dec_genV (gS := gd st R Pw) (W := WAll Pw) Ent.acc.nd hmi hfl hnx
      (hW.reg _ (by simp [layout.reg.FAULT_IP]))
      (fun nx s1 s2 a1 _ e1 e2 => io_alt_midRV (m0 := m) hA PE Gc hR' (Alt.refl s) e1 e2) hSeen h hb

end gdP

end Fl4Proofs.P2.E2EP

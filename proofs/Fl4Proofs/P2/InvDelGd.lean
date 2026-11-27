/-
# P2 (line p3mc, gen 27): the CNodeDelete run on a checked store reading a cut read set

Handoff §31c. At a CNodeDelete entry `s` (`SlJAt ∧ InvQF`, pte's convention `CvP`, a message of length at least 2,
`InvLen`), **every** run of the invocation — accepted or declined — runs on the checked store `gd st R Pw` as on
`st`, for any read set `R` holding the `IoRS s` words off `K.ptes` of the word classes the run reads (`GCl`, the
capability-slot words, the walk's page-table words off `K.ptes`), and any write predicate `Pw` allowing the
prefix's words (`IoWr`), the locked slots' non-base words, the clear of `dest`'s `CAP0` and the caller's two
`STATE` writes:

* **`inv_run_gdV`**: the accepted run by `inv_acc_genV` with the decode block `delAccV` / `delFinV` (P2/InvDelV,
  P2/InvRunV); the declined run by `inv_dec_genV` with `io_alt_midRV` at the entry itself (`Alt.refl`).

The truncated Delete (`length < 2`, whose error reply reads the caller's IPC buffer, a user word) is not covered.
No named premise (`InvLen` is a hypothesis). New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvRunV
import Fl4Proofs.P2.E2EPU2D
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame GateField TimerField)

section gd
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **Every CNodeDelete run of length at least 2 runs on the checked store `gd st R Pw` as on `st`** (module
docstring). -/
theorem inv_run_gdV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) {s : S}
    (hE : SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s)
    (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) (hcv : CvP st K s) (hlen : InvLen st s)
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
    {a : A} {number : I64} {r : Bool × S × A}
    (h : syscall.handle_invocation_local st ar s a number p = ok r) :
    syscall.handle_invocation_local (gd st R Pw) ar s a number p = ok r := by
  obtain ⟨hJ, hq⟩ := hE
  have PE := hq.1.1.1
  have hL : Slot8 K.toKLayout := fun q hq => PE.lay.slot8 q hq
  have hR' : ∀ b, IoRSR st K.toKLayout Locks s b → G b → R b := fun b h g =>
    hR b h.1 (ioRSR_rsE hK hks h).2 g
  obtain ⟨cp, cr, cg, cgb, dest, fp0, rt0, asid0, va0, mp0, C0, hcs, hsK, -, -, -, -, -, hdK, -, hLd, -, -,
    hSn, -⟩ := del_core hq
  have hSeen : ∀ x, SeenW p x → R x := by
    intro x hx
    have hd0 : dest ≠ 0#u64 := fun e => hz_of K.toKLayout s hJ (e ▸ hdK)
    obtain ⟨o, ho, rfl⟩ := hSn x hx
    have hov : o.val < 32 ∧ o.val % 8 = 0 := by
      rcases ho with rfl | rfl | rfl | rfl <;>
        simp [layout.cte.CAP0, layout.cte.CAP1, layout.cte.PREV, layout.cte.NEXT]
    exact hR' _ (PE.lockSlotR hdK (hLd hd0) hov.1 hov.2) (hGs _ (slotW_of hL hdK hov.1))
  have hps : R p.slot ∧ R (core.num.U64.wrapping_add p.slot 8#u64) := by
    have e := invPsRN (L := L) hq
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
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_core hq
    have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
    rw [hlbl] at hy ⊢
    have hlen' : ¬ length < 2#u64 := len_ge2 (hlen _ info (cur_thread_ok s) emi) hl
    have hvsP := invVsJ_of (st := st)
      (P := fun s => SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) (fun _ h => h.1)
    have E := delEnt_of (P := fun s => SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s)
      ⟨hJ, hq⟩ hq hvsP (invCdtJ_of (fun _ h => h.1)) (hz_of _ s hJ)
    have hvs2 : ∀ sl fp rt asid va, sl ∈ K.slots →
        obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
        va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧
          VsRd st K.toKLayout s asid va :=
      fun sl fp rt asid va hsl hc hA => hvsP s sl fp rt asid va ⟨hJ, hq⟩ hsl hc hA
    obtain ⟨m1, hconv, hag⟩ := hcv
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
    have hsub : ∀ b, b ∈ K.ptes → Fl4Proofs.P3.Vs.PtW Zx.L1 b := fun b hb =>
      ptesR_sub B hag b (by rw [← hconv]; exact hb)
    have hmx := maxA_facts PE.bxi.2.2.1.1 PE.cscS
    obtain ⟨hdec, hrep⟩ := delAccV (R := R) (X := (· ∈ K.ptes)) (G := G) (gS := gd st R Pw) hA PE hW hwS
      (fun q hq hl hT hn x => gd_write (hw0 q hq hl hT hn x)) hst' E hsK hlen' (B.vsJX hsub)
      (fun b hb => ⟨(hU.kern b hb).1, hK.none b hb, (hU.kern b hb).2⟩)
      hR hGs (fun o ho => Gc.n o ho)
      (by have := Gc.t 3328#u64 (by simp) (by simp) (by simp); rw [Fl4Proofs.P1.stA_eq]; exact this)
      (Gc.t 3464#u64 (by simp) (by simp) (by simp)) (Gc.t 3592#u64 (by simp) (by simp) (by simp))
      (Gc.sc _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩) (fun r hr => Gc.r r hr) hGv C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := delFinV (gS := gd st R Pw) hA PE Ent (hst' _ (Or.inr rfl)) E hsK hlen' hvs2 C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · exact inv_dec_genV (gS := gd st R Pw) (W := WAll Pw) Ent.acc.nd hmi hfl hnx
      (hW.reg _ (by simp [layout.reg.FAULT_IP]))
      (fun nx s1 s2 a1 _ e1 e2 => io_alt_midRV (m0 := m) hA PE Gc hR' (Alt.refl s) e1 e2) hSeen h hb

end gd

end Fl4Proofs.P2.E2EP

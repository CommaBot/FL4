/-
P2 (line jsweep, gen 4): **`serializable_fl4_localW11PJ11`: the sl slot's `SlPreB` derived from the chain** (new
definitions only, on top of E2EPW11J10; no existing statement changed).

## Where sl stood (PJ10)

sl's start fact (`StartP3W6`, reached through `StartB` → `StartA` → `StartP3W11JV` → … → `StartP3W8`) is
`∃ h : SlPremP6, GlueAt … (Ch σ ∧ SlQ … m σ)`, `SlQ = SlPreB ∧ SlEntL [P] ∧ SlSyncC [P] ∧ SlAccR [P]`. `SlPreB`
(P2/SlObl.lean) is one [J] blob of 18 fields at the start state `σ`, nine of them quantified over the `LocalPre`
successors `X` of `σ` (the `FAULT_IP` write and `update_timestamp`). No lemma derived any of them.

## The index convention needed: `OmegaS` (finding)

`SlQ` fixes `U = K.user`, and `SlPreB.hF` asks `FaultEntAt … Ω K.user …`, whose `FaultEnt.hU` asks every user word
to lie outside `Ω`. At P3's `Ω = Heap.omega H` this fails for every aligned user word in the first 4 KiB of its
`other` object (`SlJAt.not_userOK_omega`), and at P3's `OmegaU` (the convention vmF / vmR / vt use) it fails the same
way for every user word that is not an IPC-buffer word (`OmegaU` removes only `BufU` from `Heap.omega`). So the trap
arm of `SlPreB` is unsatisfiable at either convention whenever such a user word exists and a fault handler is
waiting. It is satisfiable at **`OmegaS := OmegaU ∖ UsrA`** (`UsrA` = aligned user words) with
**`SgS := frame ∖ UsrA`**: P1's invariants survive removing words of no reply / SC / notification / kernel-state
block (`BXI.shrinkU`, slhuf), and the ASID-table and pool words are no user words (`SlJAt.userAsid`,
`SlJAtZ.userNotVsU`). The index sets are the glue's choice (as `BunIxU`), so this is a convention, not a premise.

## Derived here (at a bundle state `σ`, `SlJAtZ` at index `Cs`/`Ac`, `Ω = OmegaS`, `Sg = SgS`)

* `SlJAtZ.lpW`: `LocalPre` writes only `W3` and keeps the current thread; `SlJAtZ.notW3` (a word in no node and not
  in the current TCB's region is no `W3` word);
* `SlJAtZ.lpBxiS`: `hI` (`BXI`) and `hAs` (`AsidOff`) at every successor (iolay's `lpBxiAsid` at `OmegaU`, then
  `BXI.shrinkU`; pool words by `SlJAtZ.userNotVsU`);
* `SlJAtZ.lpFault`: `hF` (`FaultEntAt` at `K.user`, by P1's `faultEntAt_ofT` from `nb` / `cap` / `user` / `buf` /
  `asid` at the successor) and `hrecv` (`faultRecv_ofT`); `user` by `SlJAtZ.userAl` (`EPlaced.balign`), `buf` by
  `JAtZ.bufOK` with `BufU ⊆ K.user` (`JAtZ.bufU_B`);
* `SlJAtZ.rrPlS`: `hPl` (`RRPl`; W11's `rrPlU` for any fault type and at `OmegaS`);
* `hT`, `hN`, `hcT` (`bxiU`), `hTm` (`TimerOK`, from `BXI`'s `ScExtra`), `aff` (the GlueAt memory link,
  `UserOK.tcb`), `hSt` (`AFFINITY` = core by `SlJAtS.curAffCore`, not queued by `run`, W9's `chain_run` from
  `hct` [P]);
* `SlJAtZ.slSd` / `SlJAtZ.slSu`: `hSd` / `hSu` — the decided thread (the handler `dest` / the replied `u`) is a heap
  TCB (`FaultEnt.hq` / `RRPl.hu`) homed here (`schedulable_here`'s `HereF.aff` at the successor, read back by
  `SlJAtZ.lpTcb`), queued only on a held lock (`dest` is blocked on the endpoint, `vm_queue`, which is locked by
  `SlEntL.lep` [P]; `u` is blocked on reply, not queued), and the `STATE` / `BLOCK_OBJ` words written are home words
  in `SlWS` (`SlJAtZ.homeWS`, `VmBase.homeOf`): **`SlJAtZ.slPreB`**.

## Not derived: `SlPreR` (what stays of `SlPreB`)

* `hy0f`, `hy0r` [J]: the receiver's `YIELD_TO = 0` — owned by line iolay (YieldScope; same gap as vmF `hyt` /
  vmR `ry`), carried verbatim.
* `hrz` [P]: the reply object's call-stack links are clear (as vmR's `VmREntJ11.nb` [P]).
* `hlk` [P]: the endpoint is locked (as vmR's `VmREntJ11.lk` [P]).

## Entry fact, start fact, top

* **`SlEntJ11`**: `ix` (bundle at the index's `Cs`/`Ac`, `Ω = OmegaS`), `sg` (`Sg = SgS`), `hct` [P] (`NonIdle`,
  as io / vmF / vmR), `el` / `sc` / `acc` [P] (`SlQ`'s other three conjuncts, unchanged), `r : SlPreR`.
  `SlEntJ11.toQ`: `SlQ` from it, `run` and the memory link.
* **`StartC`** = `StartB` with sl at `∃ h, GlueAt … (Ch σ ∧ SlEntJ11 σ)`, the program cut; `startAt_C` (sl by
  `chain_run`, the rest by `startA_of_B` and J9's `startAt_A`); **`serializable_fl4_localW11PJ11`**.
* Satisfiability: `slIxS_of` (the convention holds at every bundle state, a choice of index), `startC_sl_sat` (sl's
  start fact at every chain state with `SlEntJ11`, memory `L.mem σ`).
-/
import Fl4Proofs.P2.E2EPW11J10
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld own oAFFINITY InW QueuedState Safe0 stA_fld affA_fld blockA_fld GateField TimerField GField)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)
open Fl4Proofs.P3 (OmegaU VsU BufU)

noncomputable section
open Classical

/-! ## The index convention -/

section conv

/-- The aligned user words. -/
def UsrA (K : KLayout) : Set U64 := {b | b ∈ K.user ∧ Aligned b}

/-- **sl's `Ω`**: `OmegaU` without the aligned user words (module docstring). -/
def OmegaS (K : KLayout) (Zx : Fl4Proofs.P3.XSets) (kb : U64) (σ : Fl4Spec.State Unit) : Set U64 :=
  {a | a ∈ OmegaU K.heap Zx kb σ ∧ a ∉ UsrA K}

/-- **sl's `Sg`**: the frame words without the aligned user words. -/
def SgS (K : KLayout) : Set U64 := {a | a ∈ Heap.frame K.heap ∧ a ∉ UsrA K}

end conv

/-! ## Bundle facts at the `LocalPre` successors -/

section lp
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

/-- **User words are aligned** (`EPlaced.balign`). -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.userAl (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {x : U64} (hx : x ∈ K.user) :
    Aligned x := by
  rw [B.user] at hx
  obtain ⟨wp, hw, rfl⟩ := hx
  exact (B.j.xtop.fin.1.2.ep.balign wp hw).1

/-- **User words are no ASID-table or pool words** (`TopPlaced.disj`). -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.userNotVsU (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {x : U64} (hx : x ∈ K.user) :
    x ∉ VsU Zx (L.ksb s) := by
  rw [B.user] at hx
  obtain ⟨wp, hw, rfl⟩ := hx
  intro hv
  have hO : Fl4Proofs.P3.Vs.OObj st Zx.N Zx.T Zx.C Zx.E Zx.R Zx.B Zx.c s σ wp.1 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩))))))
  exact B.j.xtop.fin.1.2.disj wp.1 hO (Fl4Proofs.P3.Vs.vsWrite_vobj B.j.xtop.fin.1.2.vs hv)

/-- **`LocalPre` writes only `W3` and keeps the current thread.** -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.lpW (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {a : A} {s2 : S}
    {a2 : A} (hLP : LocalPre (st := st) ar s a (s2, a2)) :
    WritesIn st s s2 (W3 (L := L) s) ∧ L.curW s2 = L.curW s := by
  obtain ⟨hT, hN, hcT⟩ := B.j.bxiU.tcbNode
  have hW := localPre_w3 (ar := ar) hA hT hN hcT hLP
  have hcA : TcbAddr (L.curW s) := hT _ hcT
  refine ⟨hW, ?_⟩
  unfold LawfulStore.curW
  rw [hW.2.1, nodeAt_of_ksb hW.1]
  refine hW.mem_eq (nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])) ?_
  rintro (e | e | e)
  · exact node_ne_field hN (by simp [layout.node.CUR_THREAD]) hcT hcA (by simp) e
  · unfold ctA at e
    have h := congrArg UScalar.val e
    rw [nodeAt_val hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD]),
      nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])] at h
    simp [layout.node.CUR_THREAD, layout.node.CUR_TIME] at h
  · unfold cnA at e
    have h := congrArg UScalar.val e
    rw [nodeAt_val hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD]),
      nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])] at h
    simp [layout.node.CUR_THREAD, layout.node.CONSUMED] at h

/-- **A word in no node and outside the current TCB's region is no `W3` word.** -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.notW3 (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {b : U64}
    (h1 : region K b ≠ .tcb (L.curW s)) (h2 : ∀ c, region K b ≠ .node c) : ¬ W3 (L := L) s b := by
  obtain ⟨hT, hN, hcT⟩ := B.j.bxiU.tcbNode
  have X := B.regionOKX
  have hk : K.ksb = L.ksb s := B.ksb.symm
  have nT := ne_ut_of_region hk B.cpu hN h2
  have hrT := X.tcbW _ B.j.kern.curH 392#u64 (by simp) (by simp) (by simp)
  rintro (e | e | e)
  · rw [e] at h1; exact h1 hrT.1
  · exact nT.1 e
  · exact nT.2 e

/-- **`hI` / `hAs` at `OmegaS` / `SgS`** (module docstring). -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.lpBxiS (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
      BXI st (Heap.tcbs K.heap) Cx (OmegaS K Zx (L.ksb s) σ) K.heap (SgS K) (Heap.replies K.heap)
        (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ax s2 ∧
      AsidOff (L := L) (OmegaS K Zx (L.ksb s) σ) (SgS K) s2 := by
  intro a s2 a2 hLP
  have hBA := B.lpBxiAsid hA a s2 a2 hLP
  obtain ⟨hW, -⟩ := B.lpW hA hLP
  have hX := B.regionOKX
  have hJ : SlJAt (L := L) K s := ⟨_, _, _, _, _, _, _, _, _, _, B⟩
  have hkK : L.ksb s2 = K.ksb := by rw [hW.1]; exact B.ksb
  have hk : K.ksb = L.ksb s := B.ksb.symm
  refine ⟨BXI.shrinkU (U := UsrA K) hBA.1
    (fun r hr b h1 h2 hu => hJ.userObj hu.1 (k := .reply) hr (fun z e => by cases e) ⟨h1, by
      show b.val < r.val + 2 ^ 5; omega⟩)
    (fun c hc b hin hu => hJ.userObj hu.1 (scs_heap hc) (fun z e => by cases e) hin)
    (fun c hc o h1 h2 hu => (nu_scw hX (scs_heap hc) h1 h2).2 hu.1)
    (fun n hn o h1 h2 hu => (nu_of_region hX (hX.ntW n hn o h1 h2).2.2
      (by rw [(hX.ntW n hn o h1 h2).1]; intro h; cases h)).2 hu.1)
    (fun o h1 h2 hu => hJ.userKs hu.1 (o := o) h1 (by rw [← hkK])), ?_⟩
  intro hi hhi
  have hA0 := hBA.2 hi hhi
  have ek : L.ksb s2 = L.ksb s := hW.1
  obtain ⟨rN, aT⟩ := hX.asidT hi hhi
  rw [hk] at rN aT
  have em : L.mem s2 (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) :=
    hW.mem_eq aT (B.notW3 (by rw [rN]; intro e; cases e) (fun c => by rw [rN]; intro e; cases e))
  refine ⟨⟨hA0.1, fun hu => hJ.userAsid hu.1 hhi (by rw [ek])⟩, fun h => hA0.2.1 h.1, fun hz lo hlo => ?_⟩
  obtain ⟨h1, h2⟩ := hA0.2.2 hz lo hlo
  refine ⟨⟨h1, fun hu => ?_⟩, fun h => h2 h.1⟩
  rw [ek, em] at hu hz
  have hP : L.mem s (atAF (L.ksb s) hi) ∈ Zx.P := B.j.xtop.fin.2.1.tmem hi hhi hz
  have hWv : peAF (L.mem s (atAF (L.ksb s) hi)) lo ∈ VsU Zx (L.ksb s) :=
    show Fl4Proofs.P3.Vs.VsWrite Zx.P (L.ksb s) _ from Or.inr ⟨_, hP, lo, hlo, rfl⟩
  exact B.userNotVsU hu.1 hWv

/-- **`hF` / `hrecv` at the successors**, at `OmegaS` and the user words (module docstring). -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.lpFault (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING)
    {a : A} {s2 : S} {a2 : A} (hLP : LocalPre (st := st) ar s a (s2, a2)) :
    FaultEntAt (L := L) (Heap.tcbs K.heap) Cx (OmegaS K Zx (L.ksb s) σ) K.user (SgS K) (Heap.replies K.heap)
        s2 (L.curW s) ∧
      ∀ {ptr badge dest r : U64}, FaultChecks st s2 (L.curW s) ptr badge dest r →
        L.mem s2 (stA dest) = sched.TS_BLOCKED_ON_RECV := by
  obtain ⟨hI2, hAs2⟩ := B.lpBxiS hA a s2 a2 hLP
  obtain ⟨hW, ecur⟩ := B.lpW hA hLP
  obtain ⟨hT, hN, hcT⟩ := B.j.bxiU.tcbNode
  have X := B.regionOKX
  have hP := B.layP
  have hJs : SlJAt (L := L) K s := ⟨_, _, _, _, _, _, _, _, _, _, B⟩
  have hcH : K.heap (L.curW s) = some .tcb := B.j.kern.curH
  have et2 : sched.cur_thread st s2 = ok (L.curW s) := by rw [cur_thread_ok, ecur]
  -- cap
  have hcap : obj.Tcb.slot (L.curW s2) layout.tcb.SLOT_FAULT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s2 ⦃ c => CapTyped K.heap (Heap.replies K.heap) (Heap.ntfns K.heap) c ⦄ ⦄ := by
    rw [ecur, Fl4Proofs.P1.tcb_slot_val, WP.spec_ok]
    have hFH : layout.tcb.SLOT_FAULT_HANDLER.val < 6 := by unfold layout.tcb.SLOT_FAULT_HANDLER; simp
    obtain ⟨hs, -, r8, -, a0, a8⟩ := X.tslot _ hcH _ hFH
    have r0 : region K (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) =
        .slot (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) := hP.region_slot hs
    have n0 := B.notW3 (b := slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER)
      (by rw [r0]; intro e; cases e) (fun c => by rw [r0]; intro e; cases e)
    have n8 := B.notW3 (b := core.num.U64.wrapping_add (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) 8#u64)
      (by rw [r8]; intro e; cases e) (fun c => by rw [r8]; intro e; cases e)
    have ecap : obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) s2 =
        obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) s := by
      unfold obj.Slot.cap
      rw [L.read_pair_eq, L.read_pair_eq, hW.mem_eq a0 n0, hW.mem_eq a8 n8]
    obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
    have hsS := hs
    rw [B.slots] at hsS
    have hcv : obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) s =
        ok (Fl4Proofs.P3.capV (L.mem s) (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER)) := by
      rw [Fl4Proofs.P3.slot_cap_eq]; exact Fl4Proofs.P3.capAt_capV _ _
    rw [ecap, hcv, WP.spec_ok]
    exact hJ.typed _ hsS
  -- nb
  have hnb : ¬ Blocked (L.mem s2 (stA (L.curW s2))) := by
    have a3 : Aligned (core.num.U64.wrapping_add (L.curW s) 3328#u64) := field_aligned (hT _ hcT) (by simp) (by simp)
    have n3 : ¬ W3 (L := L) s (core.num.U64.wrapping_add (L.curW s) 3328#u64) :=
      w3_tcb hT hN hcT (by simp) (by simp)
    rw [ecur, stA_eq, hW.mem_eq a3 n3, ← stA_eq]
    intro hb
    have hv := Calm.val (v := L.mem s (stA (L.curW s))) hrun
    rcases hb with e | e | e <;> rw [e] at hv <;>
      simp [sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_NTFN] at hv
  -- user
  have hUs : ∀ b ∈ K.user, OutsideObjs st (Heap.tcbs K.heap) Cx s2 b ∧ b ∉ OmegaS K Zx (L.ksb s) σ := by
    intro b hb
    have ha := B.userAl hb
    refine ⟨⟨ha, fun t ht => ?_, fun c hc => ?_⟩, fun h => h.2 ⟨hb, ha⟩⟩
    · have := hJs.userObj hb (k := .tcb) ht (fun z e => by cases e)
      simp only [InW, HKind.bits] at this
      omega
    · have h := hJs.userNode64 hb (B.csLt c hc)
      have e : L.nodeBase s2 c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hW.1]
      rw [e]; omega
  -- buf
  have hbuf : ∀ y ∈ Heap.tcbs K.heap, msg.lookup_ipc_buffer st s2 true y ⦃ b => BufOK K.user b ⦄ := by
    intro y hy
    have hyH : K.heap y = some .tcb := hy
    have n1 : ¬ W3 (L := L) s (ibWordA y) := by
      by_cases ey : y = L.curW s
      · subst ey; exact w3_tcb hT hN hcT (K := 3512#u64) (by simp) (by simp)
      · have r := X.tcbW y hyH 3512#u64 (by simp) (by simp) (by simp)
        exact B.notW3 (by unfold ibWordA; rw [r.1]; intro e; injection e with e; exact ey e)
          (fun c => by unfold ibWordA; rw [r.1]; intro e; cases e)
    have a1 : Aligned (ibWordA y) := (X.tcbW y hyH 3512#u64 (by simp) (by simp) (by simp)).2.2
    have hSB : layout.tcb.SLOT_BUFFER.val < 6 := by unfold layout.tcb.SLOT_BUFFER; simp
    obtain ⟨hs, -, r8, -, a0, a8⟩ := X.tslot _ hyH _ hSB
    have r0 : region K (slotIdx y layout.tcb.SLOT_BUFFER) = .slot (slotIdx y layout.tcb.SLOT_BUFFER) :=
      hP.region_slot hs
    have eSB : sbWordA y = slotIdx y layout.tcb.SLOT_BUFFER := by
      have h1 := tcb_slot_val y layout.tcb.SLOT_BUFFER
      have h2 : obj.Tcb.slot y layout.tcb.SLOT_BUFFER = ok (sbWordA y) := by simp [obj.Tcb.slot, lift, sbWordA]
      exact ok_inj_ff (h2.symm.trans h1)
    have n0 : ¬ W3 (L := L) s (sbWordA y) := by
      rw [eSB]; exact B.notW3 (by rw [r0]; intro e; cases e) (fun c => by rw [r0]; intro e; cases e)
    have n8 : ¬ W3 (L := L) s (core.num.U64.wrapping_add (sbWordA y) 8#u64) := by
      rw [eSB]; exact B.notW3 (by rw [r8]; intro e; cases e) (fun c => by rw [r8]; intro e; cases e)
    have a0' : Aligned (sbWordA y) := by rw [eSB]; exact a0
    have a8' : Aligned (core.num.U64.wrapping_add (sbWordA y) 8#u64) := by rw [eSB]; exact a8
    rw [lookup_ipc_buffer_same (s := s) (s' := s2) (t := y)
      ⟨hW.mem_eq a1 n1, hW.mem_eq a0' n0, hW.mem_eq a8' n8⟩]
    refine WP.spec_mono (B.j.bufOK hy) fun w hw hne i hi => ?_
    rw [B.user]
    exact B.j.bufU_B (hw hne i hi)
  exact ⟨faultEntAt_ofT hI2 et2 hnb hcap hUs hbuf hAs2, fun hc => faultRecv_ofT hI2 et2 hcap hc⟩

/-- **`hPl` at the successors** (W11's `rrPlU` for any fault type, at `OmegaS` / `SgS`). -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.rrPlS (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {rptr ep : U64}
    (hfd : VmFoundC st rptr ep s) {ty : U64} [HfrRestart st ar ty] :
    ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
      ∀ u usc, RRChecksG st ar ty s2 a2 (L.curW s) rptr ep u usc →
        RRPl (L := L) (Heap.tcbs K.heap) Cx (OmegaS K Zx (L.ksb s) σ) (SgS K)
          (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) s2 (L.curW s) rptr ep u usc := by
  intro a s2 a2 hLP u usc hC
  have hI2 := (B.lpBxiS hA a s2 a2 hLP).1
  obtain ⟨hT, hN, hcT⟩ := B.j.bxiU.tcbNode
  have hcC : L.cpu s ∈ Cx := B.j.kern.cpuCs
  obtain ⟨hW, ecur⟩ := B.lpW hA hLP
  have et := cur_thread_ok (L := L) s
  have hCn := B.cnOffU et
  have hcA : TcbAddr (L.curW s) := hT _ hcT
  have et2 : sched.cur_thread st s2 = ok (L.curW s) := by rw [cur_thread_ok, ecur]
  -- reply_caps
  have hrc2 : fastpath.reply_caps st s2 (L.curW s) = ok (some (rptr, ep)) := by
    refine reply_caps_keep (T := Heap.tcbs K.heap) (Cs := Cx) (Sg := Heap.frame K.heap ∪ K.user) hcA (hfd _ et) hW
      ?_ ?_ hCn
    · intro Kk hK
      have hKv : Kk.val < 4096 ∧ Kk.val ≠ 392 := by
        rcases hK with h | h | h | h <;>
          (try simp [layout.reg.REPLY, layout.reg.R12, layout.reg.CAP, layout.reg.RDI] at h) <;> omega
      exact w3_tcb hT hN hcT hKv.1 hKv.2
    · intro b hb
      exact w3_out hT hN hcT hcC hb.1
  -- the lookup typing
  have hlk : ∀ cptr, cspace.lookup_cap st s2 (L.curW s2) cptr ⦃ r => ∀ c, r = .Ok c →
      CapTyped K.heap (Heap.replies K.heap) (Heap.ntfns K.heap) c ⦄ := by
    intro cptr
    rw [ecur]
    obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.cspace.lookup_cap.p0 st s2 (L.curW s) cptr L.total)
    rw [hr, WP.spec_ok]
    intro c hc
    subst hc
    have hroot0 : obj.Slot.cap st (L.curW s) s = ok (Fl4Proofs.P3.capV (L.mem s) (L.curW s)) := by
      rw [Fl4Proofs.P3.slot_cap_eq]; exact Fl4Proofs.P3.capAt_capV _ _
    obtain ⟨C, hC0, hcl, hWc⟩ := hCn _ _ (tcb_slot_ctable (L.curW s)) hroot0
    have capK : ∀ b, CapSW (L := L) (Heap.tcbs K.heap) Cx (Heap.frame K.heap ∪ K.user) s b → L.mem s2 b = L.mem s b :=
      fun b hb => hW.mem_eq hb.1.1 (w3_out hT hN hcT hcC hb.1)
    have eC : ∀ p r m y, C p r → cspace.mask r = ok m →
        obj.Slot.cap st (cnSlot p (y &&& m)) s2 = obj.Slot.cap st (cnSlot p (y &&& m)) s := by
      intro p r m y hp hm
      obtain ⟨h1, h2⟩ := hWc p r m y hp hm
      unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, capK _ h1, capK _ h2]
    have e0 : obj.Slot.cap st (L.curW s) s2 = obj.Slot.cap st (L.curW s) s := by
      have k0 : L.mem s2 (L.curW s) = L.mem s (L.curW s) := by
        have := hW.mem_eq (b := core.num.U64.wrapping_add (L.curW s) 0#u64)
          (field_aligned hcA (by simp) (by simp)) (w3_tcb hT hN hcT (by simp) (by simp))
        have e00 : core.num.U64.wrapping_add (L.curW s) 0#u64 = L.curW s := by
          apply UScalar.eq_of_val_eq; rw [tcb_wadd_val hcA (by simp)]; simp
        rwa [e00] at this
      have k8 := hW.mem_eq (b := core.num.U64.wrapping_add (L.curW s) 8#u64)
        (field_aligned hcA (by simp) (by simp)) (w3_tcb hT hN hcT (by simp) (by simp))
      unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, k0, k8]
    have hroot : ∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r := fun p r gs g h =>
      hC0 p r gs g (ok_inj_ff (hroot0.symm.trans h))
    unfold cspace.lookup_cap at hr
    obtain ⟨r0, h0, hr⟩ := bind_eq_ok hr
    cases r0 with
    | Ok r1 =>
      obtain ⟨c', hc', hr⟩ := bind_eq_ok hr
      have ecc := ok_inj_ff hr
      injection ecc with ecc
      subst ecc
      have h0s := lookup_slot_back (tcb_slot_ctable (L.curW s)) e0 eC hcl hroot h0
      obtain ⟨p, r, m, y, hp, hm, ey⟩ := lookup_slot_in hroot hcl h0s
      have hcs : obj.Slot.cap st r1.slot s = ok c' := by rw [← hc', ey, eC p r m y hp hm]
      have hls : cspace.lookup_cap st s (L.curW s) cptr = ok (.Ok c') := by
        unfold cspace.lookup_cap; rw [h0s]; simp only [bind_ok]; rw [hcs]; simp only [bind_ok]
      have hty := post_of_ok (B.j.lkTyped cptr) hls
      exact hty _ rfl
    | Err lf =>
      have := ok_inj_ff hr
      cases this
  exact rrPl_lkG (ty := ty) ar (fun _ h => h) hI2 hlk et2 hrc2 hC

/-- **A TCB word off `FAULT_IP` is kept by `LocalPre`.** -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.lpTcb (hA : P0.ArchTotal ar)
    (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {a : A} {s2 : S} {a2 : A}
    (hLP : LocalPre (st := st) ar s a (s2, a2)) {y : U64} (hy : K.heap y = some .tcb) {o : U64}
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h8 : o.val % 8 = 0) (h3 : o.val ≠ 392) :
    L.mem s2 (fld y o) = L.mem s (fld y o) := by
  obtain ⟨hW, -⟩ := B.lpW hA hLP
  obtain ⟨hT, hN, hcT⟩ := B.j.bxiU.tcbNode
  have r := B.regionOKX.tcbW y hy o h1 h2 h8
  refine hW.mem_eq r.2.2 ?_
  by_cases ey : y = L.curW s
  · subst ey; exact w3_tcb hT hN hcT h2 h3
  · exact B.notW3 (by unfold fld; rw [r.1]; intro e; injection e with e; exact ey e)
      (fun c => by unfold fld; rw [r.1]; intro e; cases e)

/-- **The fault-handler cap is kept by `LocalPre`.** -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.lpFH (hA : P0.ArchTotal ar)
    (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {a : A} {s2 : S} {a2 : A}
    (hLP : LocalPre (st := st) ar s a (s2, a2)) :
    obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) s2 =
      obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) s := by
  obtain ⟨hW, -⟩ := B.lpW hA hLP
  have X := B.regionOKX
  have hP := B.layP
  have hcH : K.heap (L.curW s) = some .tcb := B.j.kern.curH
  have hFH : layout.tcb.SLOT_FAULT_HANDLER.val < 6 := by unfold layout.tcb.SLOT_FAULT_HANDLER; simp
  obtain ⟨hs, -, r8, -, a0, a8⟩ := X.tslot _ hcH _ hFH
  have r0 : region K (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) =
      .slot (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) := hP.region_slot hs
  have n0 := B.notW3 (b := slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER)
    (by rw [r0]; intro e; cases e) (fun c => by rw [r0]; intro e; cases e)
  have n8 := B.notW3 (b := core.num.U64.wrapping_add (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) 8#u64)
    (by rw [r8]; intro e; cases e) (fun c => by rw [r8]; intro e; cases e)
  unfold obj.Slot.cap
  rw [L.read_pair_eq, L.read_pair_eq, hW.mem_eq a0 n0, hW.mem_eq a8 n8]

/-- **A home word of a thread homed here is in `SlWS`** (`VmBase.homeOf`, `tcbOwner`: neither a gate, timer nor
queue-link word). -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.homeWS (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING)
    {Locks : S → U64 → Prop} {y : U64} (hy : y ∈ Heap.tcbs K.heap) (haff : L.mem s (affA y) = L.cpu s) {o : U64}
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h8 : o.val % 8 = 0) (hg : ¬ GateField o.val)
    (htm : ¬ TimerField o.val) (hG : ¬ GField o.val) :
    SlWS (st := st) K Locks s (fld y o) := by
  have BU : BunIxU (L := L) K K.heap.tcbs Cx (OmegaU K.heap Zx (L.ksb s) σ) K.heap K.heap.frame K.heap.replies
      K.heap.scs K.heap.ntfns K.heap.scBits Ax s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨A', arI, AR, Zx, Lst, D, a', σ, B, rfl⟩⟩
  have w := ((BU.vmBase hrun).homeOf (Locks := Locks) hy haff h1 h2 h8 hg htm hG).2
  exact ⟨w.1, Or.inr w.2⟩

/-- **`hSd`** (module docstring): the handler a fault run dequeues is a heap TCB homed here, blocked on the
endpoint, which is locked (`SlEntL.lep` [P]); the two `STATE` words are home words. -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.slSd (hA : P0.ArchTotal ar)
    (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING)
    {Locks : S → U64 → Prop} {found : U64 × U64} (El : SlEntL (st := st) K Locks found s) (hS : SlTrap st s)
    {a : A} {s2 : S} {a2 : A} (hLP : LocalPre (st := st) ar s a (s2, a2)) {ptr badge dest r : U64}
    (hc : FaultChecks st s2 (L.curW s) ptr badge dest r) :
    K.heap dest = some .tcb ∧ Safe0 (L.cpu s) (Locks s) (L.mem s) dest ∧
      SlWS (st := st) K Locks s (stA (L.curW s)) ∧ SlWS (st := st) K Locks s (stA dest) := by
  obtain ⟨hF, hrecv⟩ := B.lpFault hA hrun hLP
  have hI2 := (B.lpBxiS hA a s2 a2 hLP).1
  obtain ⟨hW, -⟩ := B.lpW hA hLP
  obtain ⟨hT, hN, hcT⟩ := B.j.bxiU.tcbNode
  have X := B.regionOKX
  have hcH : K.heap (L.curW s) = some .tcb := B.j.kern.curH
  obtain ⟨-, rest, E⟩ := hF.2 ptr badge dest r hc
  have hrc := hrecv hc
  have hdT : dest ∈ Heap.tcbs K.heap := E.hq.mem dest (by simp)
  have hdH : K.heap dest = some .tcb := hdT
  -- the endpoint, locked
  obtain ⟨sl, x, y, g, gr, esl, ecap, -⟩ := hc.cap
  have esl' : sl = slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER :=
    ok_inj_ff (esl.symm.trans (tcb_slot_val _ _))
  subst esl'
  have ecapσ : obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) s =
      ok (capability.Cap.Endpoint ptr badge x y g gr) := by
    rw [← B.lpFH hA hLP]; exact ecap
  have hlkp : Locks s ptr := by
    have h := El.lep hS ⟨ptr, badge, x, y, g, gr, ecapσ⟩
    rwa [resPtr_ok ecapσ] at h
  have hpH : K.heap ptr = some .ep := by
    have hFH : layout.tcb.SLOT_FAULT_HANDLER.val < 6 := by unfold layout.tcb.SLOT_FAULT_HANDLER; simp
    have hs := (X.tslot _ hcH _ hFH).1
    rw [B.slots] at hs
    obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
    have hcv : obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) s =
        ok (Fl4Proofs.P3.capV (L.mem s) (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER)) := by
      rw [Fl4Proofs.P3.slot_cap_eq]; exact Fl4Proofs.P3.capAt_capV _ _
    have e1 := ok_inj_ff (hcv.symm.trans ecapσ)
    have ht := hJ.typed _ hs
    rw [e1] at ht
    exact ht.1 ptr badge x y g gr rfl
  have hhd : dest = L.mem s2 (epHeadA ptr) := by
    have h1 := hc.head
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) _ ptr)] at h1; exact (ok_inj_ff h1).symm
  have hQ := vm_queue hI2 hpH E.hst hhd hrc dest (Or.inl rfl)
  have HF := here_facts (L := L) hc.here
  -- the handler's words at the entry state
  have ea : L.mem s2 (affA dest) = L.mem s (affA dest) :=
    B.lpTcb hA hLP hdH (o := 3520#u64) (by simp) (by simp) (by simp) (by simp)
  have eb : L.mem s2 (blockA dest) = L.mem s (blockA dest) :=
    B.lpTcb hA hLP hdH (o := 3336#u64) (by simp) (by simp) (by simp) (by simp)
  have haff : L.mem s (affA dest) = L.cpu s := by rw [← ea, HF.aff, hW.2.1]
  have hca := (show SlJAtS (L := L) K Cx Ax s from ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩).curAffCore.1
  refine ⟨hdH, ⟨by rw [← affA_fld]; exact haff, fun _ => ?_⟩, ?_, ?_⟩
  · show Locks s (L.mem s (blockA dest))
    rw [← eb, hQ.2.1]; exact hlkp
  · rw [stA_eq]
    exact B.homeWS hrun hcT hca (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) (by simp [GField])
  · rw [stA_eq]
    exact B.homeWS hrun hdT haff (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) (by simp [GField])

/-- **`hSu`** (module docstring): the replied thread is a heap TCB homed here, blocked on reply (not queued); the
`STATE` / `BLOCK_OBJ` words written are home words. -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.slSu (hA : P0.ArchTotal ar)
    (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING)
    {Locks : S → U64 → Prop} {rptr ep : U64} (hfd : VmFoundC st rptr ep s)
    {a : A} {s2 : S} {a2 : A} (hLP : LocalPre (st := st) ar s a (s2, a2)) {u usc : U64}
    (hc : RRChecks st ar s2 a2 (L.curW s) rptr ep u usc) :
    K.heap u = some .tcb ∧ Safe0 (L.cpu s) (Locks s) (L.mem s) u ∧
      SlWS (st := st) K Locks s (stA (L.curW s)) ∧ SlWS (st := st) K Locks s (blockA (L.curW s)) ∧
        SlWS (st := st) K Locks s (stA u) := by
  have hP := B.rrPlS hA hfd a s2 a2 hLP u usc hc
  obtain ⟨hW, -⟩ := B.lpW hA hLP
  obtain ⟨hT, hN, hcT⟩ := B.j.bxiU.tcbNode
  have huT : u ∈ Heap.tcbs K.heap := hP.hu
  have huH : K.heap u = some .tcb := huT
  obtain ⟨b, hb, eb⟩ := hc.here
  subst eb
  have HF := here_facts (L := L) hb
  obtain ⟨i, hi, hne⟩ := hc.ust
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s2 u)] at hi
  have e1 : L.mem s2 (stA u) = i := ok_inj_ff hi
  have e2 : i = sched.TS_BLOCKED_ON_REPLY := by
    by_contra h; exact hne (bne_iff_ne.2 h)
  have ea : L.mem s2 (affA u) = L.mem s (affA u) :=
    B.lpTcb hA hLP huH (o := 3520#u64) (by simp) (by simp) (by simp) (by simp)
  have es : L.mem s2 (stA u) = L.mem s (stA u) := by
    rw [stA_eq]; exact B.lpTcb hA hLP huH (o := 3328#u64) (by simp) (by simp) (by simp) (by simp)
  have haff : L.mem s (affA u) = L.cpu s := by rw [← ea, HF.aff, hW.2.1]
  have hca := (show SlJAtS (L := L) K Cx Ax s from ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩).curAffCore.1
  refine ⟨huH, ⟨by rw [← affA_fld]; exact haff, fun hq => ?_⟩, ?_, ?_, ?_⟩
  · rw [← stA_fld, ← es, e1, e2] at hq
    have h5 : (sched.TS_BLOCKED_ON_REPLY).val = 5 := by simp [sched.TS_BLOCKED_ON_REPLY]
    unfold QueuedState at hq
    rw [h5] at hq
    omega
  · rw [stA_eq]
    exact B.homeWS hrun hcT hca (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) (by simp [GField])
  · exact B.homeWS hrun hcT hca (o := 3336#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) (by simp [GField])
  · rw [stA_eq]
    exact B.homeWS hrun huT haff (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) (by simp [GField])

end lp

/-! ## What stays of `SlPreB`, and `SlPreB` from it -/

section pre
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

variable (st) in
/-- **What stays of `SlPreB`** (module docstring): `hy0f` / `hy0r` [J] (line iolay), `hrz` [P], `hlk` [P]; verbatim
the fields of `SlPreB`. -/
structure SlPreR (K : KLayout) (Locks : S → U64 → Prop) (found : U64 × U64) (s : S) : Prop where
  /-- [J] (line iolay: YieldScope) the handler's `YIELD_TO = 0`, as `SlPreB.hy0f`. -/
  hy0f : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (yieldA dest) = 0#u64
  /-- [P] the reply object's call-stack links are clear (as vmR's `VmREntJ11.nb`). -/
  hrz : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) →
    L.mem X (rNextA found.1) &&& ~~~1#u64 = 0#u64 ∧ L.mem X (rPrevA found.1) &&& ~~~1#u64 = 0#u64
  /-- [J] (line iolay: YieldScope) the replied thread's `YIELD_TO = 0`, as `SlPreB.hy0r`. -/
  hy0r : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc → L.mem X (yieldA u) = 0#u64
  /-- [P] the endpoint is locked (as vmR's `VmREntJ11.lk`). -/
  hlk : ¬ SlTrap st s → Locks s found.2

variable {ar}
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

/-- **`SlPreB` at a bundle state** at `OmegaS` / `SgS`, from `run`, fl4-sync's contract, the memory agreement on
`AFFINITY` and `SlPreR` (module docstring). -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.slPreB (hA : P0.ArchTotal ar) (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING)
    {Locks : S → U64 → Prop} {n : I64} {found : U64 × U64} {m0 : U64 → U64}
    (hC : SlSyncC st n found s) (El : SlEntL (st := st) K Locks found s) (hm0 : AffAg st K m0 s)
    (R : SlPreR st ar K Locks found s) :
    SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cx (OmegaS K Zx (L.ksb s) σ) K.user (SgS K)
      K.heap.replies K.heap.scs K.heap.ntfns Ax K.heap K.heap.scBits s := by
  obtain ⟨hT, hN, hcT⟩ := B.j.bxiU.tcbNode
  have hS : SlJAtS (L := L) K Cx Ax s := ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩
  have hca := hS.curAffCore.1
  refine
    { hT := hT
      hN := hN
      hcT := hcT
      hI := fun a X a1 h => (B.lpBxiS hA a X a1 h).1
      hAs := fun a X a1 h => (B.lpBxiS hA a X a1 h).2
      aff := hm0
      hSt := ⟨B.curTcb.1, by rw [← affA_fld]; exact hca, fun hq => ?_⟩
      hrecv := fun _ a X a1 h => (B.lpFault hA hrun h).2
      hF := fun _ a X a1 h => (B.lpFault hA hrun h).1
      hy0f := R.hy0f
      hTm := fun _ a X a1 h => (B.lpBxiS hA a X a1 h).1.2.2.1.2.2.tm
      hSd := fun hS' a X a1 h => B.slSd hA hrun El hS' h
      hPl := fun hS' a X a1 h u usc hc => B.rrPlS hA (hC.fd.rc hS' (hC.arm hS')) a X a1 h u usc hc
      hrz := R.hrz
      hy0r := R.hy0r
      hSu := fun hS' a X a1 h u usc hc => B.slSu hA hrun (hC.fd.rc hS' (hC.arm hS')) h hc
      hlk := R.hlk }
  rw [← stA_fld] at hq
  have hv := Calm.val (v := L.mem s (stA (L.curW s))) hrun
  unfold QueuedState at hq
  omega

end pre

/-! ## sl's entry fact -/

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **sl's start entry facts** (module docstring): the index at `OmegaS` / `SgS`, `hct` [P], the three [P]
conjuncts of `SlQ` and `SlPreR`. -/
structure SlEntJ11 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : SlArg S) (K : KLayout) (s : S) : Prop where
  /-- Index convention: clause 7 at the state with the index's `Cs` / `Ac` its ghosts, `Ω` its witness's `OmegaS`
  (a choice of index: `slIxS_of`). -/
  ix : ∃ (A' : Type) (arI' : machine.Arch A') (AR' : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI' AR' Zx i.Cs i.Ac Lst D K s a' σ ∧ i.Ω = OmegaS K Zx (L.ksb s) σ
  /-- Index convention: `Sg = SgS`. -/
  sg : i.Sg = SgS K
  /-- [P] (`NonIdle`, as io / vmF / vmR). -/
  hct : NonIdle st arI AR MR s
  /-- [P] (`SlQ`'s `SlEntL`). -/
  el : SlEntL (st := st) K i.Locks i.found s
  /-- [P] (`SlQ`'s `SlSyncC`). -/
  sc : SlSyncC st i.n i.found s
  /-- [P] (`SlQ`'s `SlAccR`). -/
  acc : SlAccR (st := st) ar K i.Locks i.found s
  /-- What stays of `SlPreB` ([J] `hy0f` / `hy0r` line iolay, [P] `hrz` / `hlk`). -/
  r : SlPreR st ar K i.Locks i.found s

variable {st ar}

/-- **`SlQ` from sl's entry facts**, `run` and the memory agreement on `AFFINITY`. -/
theorem SlEntJ11.toQ (hA : P0.ArchTotal ar) {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : SlArg S} {K : KLayout} {m : U64 → U64} {s : S}
    (E : SlEntJ11 st ar arI AR MR i K s)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING)
    (hm : AffAg st K m s) :
    Fl4Proofs.P2.PathObl.SlQ st ar i.Locks i.n i.found i.Cs i.Ω i.Sg i.Ac K m s := by
  obtain ⟨A', arI', AR', Zx, Lst, D, a', σ, B, hΩ⟩ := E.ix
  rw [hΩ, E.sg]
  exact ⟨B.slPreB hA hrun E.sc E.el hm E.r, E.el, E.sc, E.acc⟩

/-- **The convention is satisfiable at every bundle state** (a choice of index). -/
theorem slIxS_of {K : KLayout} {s : S} (h : SlJAt (L := L) K s) :
    ∃ Cs Ac Ω, ∃ (A' : Type) (arI' : machine.Arch A') (AR' : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
      (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
      SlJAtZ (L := L) arI' AR' Zx Cs Ac Lst D K s a' σ ∧ Ω = OmegaS K Zx (L.ksb s) σ := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  exact ⟨Cx, Ax, _, A', arI, AR, Zx, Lst, D, a', σ, B, rfl⟩

end ent

/-! ## The start fact and the top -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start fact with sl at `SlEntJ11`** [P] (module docstring). -/
def StartC (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .sl j => ∃ q0, (∃ h : (slSlotP3W6 st ar hA hm hSt a0).Prem j K.toKLayoutV m,
      GlueAt ((slSlotP3W6 st ar hA hm hSt a0).liftAt j K.toKLayoutV m hK.base hU.base h)
        (fun σ : S => Ch σ ∧ SlEntJ11 st ar arI AR MR j K.toKLayoutV.toKLayout σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | i => StartB st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartC` gives `StartAt` of `fl4LocW11JA`**, given the current chain and the epoch invariant. -/
theorem startAt_C (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} {s : Cfg U64 U64 U64 U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop}
    {q : SP} {i : Fl4IxW (S := S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch)
    (hE : ∃ s1, PteConv st K s1 ∧ ∀ x, GateW K x → s.mem x = s1.mem x)
    (h : StartC st ar hA hm hSt a0 arI AR MR Ch K s.mem hK hU c hs q i) :
    StartAt (fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU) c hs s.mem q := by
  have hC0 := hC
  obtain ⟨σe, hC'⟩ := hC
  cases i with
  | sl j =>
    obtain ⟨q0, ⟨h, hG⟩, e⟩ := h
    refine startAt_A st ar hA hm hSt a0 P hIoa hC0 hE (i := .sl j) ⟨q0, ⟨h, hG.mono fun σ he hμ => ⟨he.1, ?_⟩⟩, e⟩
    have hJ := ChainOf.bun hC' σ he.1
    refine he.2.toQ hA (chain_run P hIoa hC' he.1 he.2.hct) fun d hd => ?_
    obtain ⟨h1, h2⟩ := hJ.userOK.tcb d hd oAFFINITY (Or.inl rfl)
    exact (hμ _ h1 h2).symm
  | vmF j => exact startAt_A st ar hA hm hSt a0 P hIoa hC0 hE (startA_of_B st ar hA hm hSt a0 (i := .vmF j) h)
  | vmR j => exact startAt_A st ar hA hm hSt a0 P hIoa hC0 hE (startA_of_B st ar hA hm hSt a0 (i := .vmR j) h)
  | io j => exact startAt_A st ar hA hm hSt a0 P hIoa hC0 hE (startA_of_B st ar hA hm hSt a0 (i := .io j) h)
  | st j => exact startAt_A st ar hA hm hSt a0 P hIoa hC0 hE (startA_of_B st ar hA hm hSt a0 (i := .st j) h)
  | irq j => exact startAt_A st ar hA hm hSt a0 P hIoa hC0 hE (startA_of_B st ar hA hm hSt a0 (i := .irq j) h)
  | vq j => exact startAt_A st ar hA hm hSt a0 P hIoa hC0 hE (startA_of_B st ar hA hm hSt a0 (i := .vq j) h)

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end, W11's glue, PTE convention, sl's `SlPreB` derived** (module docstring):
`serializable_fl4_localW11PJ10` with `StartC` starts. sl's entry: the index convention (`OmegaS` / `SgS`), `hct`
[P], `SlEntL` / `SlSyncC` / `SlAccR` [P] and `SlPreR` (`hy0f` / `hy0r` [J] iolay, `hrz` / `hlk` [P]). -/
theorem serializable_fl4_localW11PJ11 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesCanon st K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPJ (fl4LocW11JA st ar hA hm hSt a0) (StartC st ar hA hm hSt a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨-, hK0, hU0⟩ := boot_okP st P hB hc0
  exact serializable_e2eP _ h0 hA0 hK0 hU0 hM0
    (execP_of_WPJG (fun _ _ _ _ _ _ _ _ _ hC hE hsf => startAt_C st ar hA hm hSt a0 P hIoa hC hE hsf)
      P h0 hA0 hB hc0 hM0 h).1 hq

end top

/-! ## Satisfiability at a chain state -/

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

omit [Fl4Proofs.P1.PlainStore st] in
/-- **sl's `StartC` holds at every chain state with sl's entry facts** (memory `L.mem σ`, core `L.cpu σ`, locks
`j.Locks σ`), given the record. Nothing is asked about other states. -/
theorem startC_sl_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) {σ : S} (hσ : Ch σ)
    {j : SlArg S} (h : (slSlotP3W6 st ar hA hm hSt a0).Prem j K.toKLayoutV (L.mem σ))
    (hE : SlEntJ11 st ar arI AR MR j K.toKLayoutV.toKLayout σ) (a : A) :
    ∃ q, StartC st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.Locks σ) q (.sl j) :=
  ⟨_, _, ⟨h, σ, a, ⟨hσ, hE⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

end sat

end
end Fl4Proofs.P2.E2EP

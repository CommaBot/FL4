/-
P2 (line famw, gen 5): **the per-slot [J] residue of `serializable_fl4_localW5` shrunk at P3 scope** (new
definitions only; same family `fl4LocP3W5`; no existing statement changes; no `kernel_entry_reach*` touched).

`StartP3W7` implies `StartP3W5` (`startP3W5_of_W7`), so **`serializable_fl4_localW7`** is `serializable_fl4_localW5`
with `StartP3W7` starts. Records that changed are converted inside the start fact (`VtPremP7.toP5`), so the family is
W5's.

## Derived here (from clause 7 at the start state, through `BunIx`'s `SlJAtS`)

* **`SlJAtS.curAffCore`**: the current thread's `AFFINITY` is this core (P3's `SchedRel` lists, `hc.aff` / `hc.cur`,
  as inside `SlJAtZ.cscFacts`) and the current SC's `CORE` is this core (`SlJAtZ.cscFacts`' `ScHere`).
* **`curEnt_of`**: `CurEnt` from the bundle and `run` alone: `curAff`, `cscCore` as above; **`tmc`** from P1's
  timer tree (`tmin_facts`: the earliest timer's thread is armed and in this core's tree, `treeCore_of`).
* **`rdTab_ofBun`**: `RdTab` (the ASID table / pool words are aligned, no user words, region `.none` so read-permitted):
  P3's `irqLayK_of_slJAt` (`tab` / `tabU`) and `rperm_none`.
* **`stPre_ofS`**: all of `StPre` — `aff` (above), `nq` (P3's `JAtZ.curNb`: the current thread is not blocked, so not
  queued), `sct` / `csc` / `core` (`SlJAtZ.cscFacts`).
* **`tg_ofS`**: `target ∈ T` from fl4-sync's `SetTimerFound` (loc_chain_all clause 5's own input, [P]) and P3's
  `JAtZ.threadCapT` (a found `Thread` cap names a heap TCB).
* vt: **`ksb_pin`** (`L.ksb s = K.ksb` at every `VtPre` state, from `StLay.nd` at node offsets 0 and 4287 and
  `inNode_of_region`) and **`vtmU_of`**: `VtmU`'s IRQ-state, kernel-root and ASID-table parts from one bundle state of
  the layout (`SlJAt.userKs`, `SlJAt.userAsid`); only the **pool part** stays (`tp` [J]).

## Start facts and records (`StartP3W7` vs `StartP3W5`)

| slot | removed | added |
|---|---|---|
| vmF (`VmFEntJ7`) | `VmBaseR`'s `curAff` / `cscCore` / `tmc` [J], `RdTab` [J] | — (`run` [J], `VmLay` [J] stay as `VmBaseR7`) |
| vmR (`VmREntJ7`) | the same, and `RdTab` [J] | — |
| io (`IoEntJ7`) | `CurEnt`'s `curAff` / `cscCore` / `tmc` [J] | — (`run` [J] stays) |
| st (`StEntJ7`) | `StPre` [J], `target ∈ T` [J] | `fd : SetTimerFound s target` [P] (clause 5's fl4-sync input) |
| vt (record `VtPremP7`) | `tu` [J] | `tp` [J] (pool words only), `bun` (a bundle state of the layout: the start state, no premise) |

## Not derived, and why (what would have to be exported)

* vmF/vmR/io **`run`** [J] (current thread `RUNNING` or `RESTART`): false when the idle thread is current, so it needs
  the entry's `σ.curThread ≠ σ.idleThread` (clauses 4 / 9 / 10 take it as `hct`) **and** P3 excluding
  `TS_RUNNING_VM` for the current thread (P3's `JAtZ.curFacts` gives only P1's `Runnable`, which includes
  `RUNNING_VM`, and needs `Entered σ`). P3 would have to export "`Entered σ` ⇒ current state ∈ {RUNNING, RESTART}".
* vmF/vmR **`VmLay`** [J] (`IoLay` + endpoint / reply word regions): a layout fact; P2 has no `IoLay`-from-bundle
  lemma. `LayP.region_tcb` / `region_ntfn` / `region_sc` / `region_slot` cover most fields, but `IoLay.ks` (region
  `.none` on the whole 13568-byte kernel block; `SlJAtZ.ksNone` covers 256 bytes, `irqStNone` the IRQ words) and the
  endpoint / reply regions (`region` has no `LayP.region_obj`) are missing. A P2 lemma `SlJAt.ioLay` would close it.
* vmF **`hyp`** [J] (`VmFootHyps` after `update_timestamp`): P3 states the fault path's P1 facts at
  `Ω = OmegaU`, `U = BufU` (`JAtZ.bxiU`, `asidOffU`, `bufU_out`), but `BunIx` fixes `Ω = H.omega`, and `AsidOff` is
  exported only at `OmegaU` (the ASID table words are `VsU` words). Needs (i) `BunIx`'s `Ω` relaxed to the bundle's
  `OmegaU` for the VM slots (decision below), (ii) the fault-handler cap's `CapTyped` from P3 (only `fhCap_rel` /
  `capTyped_ut` / `capTyped_null` exist), (iii) an `update_timestamp` frame lemma carrying `BXI` / `AsidOff` /
  buffer facts from `s` to `s1`.
* vmF **`hyt`** [J] (the handler's `YIELD_TO = 0`): needs the P1 invariant "`YIELD_TO ≠ 0` ⇒ state RUNNING/RESTART"
  (its docstring's follow-up); P1 does not export it.
* io **`iw`** [J] (`IoPre` kept by a user-word write): the `VmBase`-like fields are kept by `SlJAt.vmBase_wr`'s
  argument, but `IoPre.walk` / `fin` (CSpace walk, `WalkCl`, `OutsideObjs`) need a frame lemma "a user-word write
  keeps `cspace.lookup_slot`, `WalkCl` and `OutsideObjs`" (they read slot / TCB / node words only, all `NU`), which no
  P2 file exports (slhuf's `SlJAt.preB_wr` covers `SlPreB`, which has no walk).
* vt **`tp`** [J] (ASID pool words of a `VtPre` state are no user words): `VtPre` has no bundle and the pool pointer
  `mem s (atAF hi)` is state memory; P3 gives it at bundle states only (`irqLayK_of_slJAt`). Closing it needs either a
  vt path whose `Pre` carries the bundle (lvm's `vtimer_localPathF` generic in a `Pre' → VtmEnt`, kept by user writes)
  or a P1 invariant "every ASID pool pointer names a non-frame `.other` object" stated on `VtmEnt`.
-/
import Fl4Proofs.P2.E2EVFl4W5
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot InW InNode)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## 1. Facts from the bundle -/

section bun
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Kl : OwnMap.KLayout} {Cs Ac : Set U64} {s : S}

/-- **The current thread's `AFFINITY` and the current SC's `CORE` are this core** at a bundle state. -/
theorem SlJAtS.curAffCore (h : SlJAtS (L := L) Kl Cs Ac s) :
    L.mem s (affA (L.curW s)) = L.cpu s ∧ L.mem s (scCoreA (L.cscW s)) = L.cpu s := by
  obtain ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩ := h
  have hS := B.j.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hcT : L.curW s ∈ Zx.T := by rw [B.j.tcbs_eq.1]; exact B.j.kern.curH
  have haf : L.mem s (affA (L.curW s)) = L.cpu s := (hc.aff _ hcT).trans hc.cur.symm
  have e16 : fld (L.cscW s) 16#u64 = scCoreA (L.cscW s) := by
    unfold fld scCoreA
    congr 1
    simp [layout.sc.CORE]
  exact ⟨haf, by rw [← e16]; exact B.cscFacts.1.2.2.2⟩

/-- **`CurEnt` from the bundle and `run`** (module docstring): `curAff`, `cscCore`, `tmc` derived. -/
theorem curEnt_of (h : SlJAtS (L := L) Kl Cs Ac s)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING) :
    CurEnt (L := L) s := by
  have hac := h.curAffCore
  obtain ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩ := h
  refine ⟨hrun, hac.1, hac.2, fun h0 => ?_⟩
  have hI := B.j.bxi
  have hcC := hI.1.choose_spec.choose_spec.cur
  obtain ⟨-, q2⟩ := tmin_facts (BXI.blk hI) hcC h0
  exact ⟨q2.1, Fl4Proofs.P2.PathObl.treeCore_of q2.2⟩

/-- **`StPre` from the bundle** (module docstring). -/
theorem stPre_ofS (h : SlJAtS (L := L) Kl Cs Ac s) : StPre st Kl.heap.scs s := by
  have hac := h.curAffCore
  obtain ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩ := h
  have cf := B.cscFacts
  have hC := B.j.curInv (by rw [B.res]; intro e; cases e)
  have nb := B.j.curNb hC
  refine ⟨hac.1, fun hq => nb ?_, cf.2, cf.1.2.1, hac.2⟩
  unfold OwnMap.QueuedState at hq
  rcases hq with e | e
  · exact Or.inr (Or.inl (UScalar.eq_of_val_eq (by rw [e]; simp [sched.TS_BLOCKED_ON_RECV])))
  · exact Or.inr (Or.inr (UScalar.eq_of_val_eq (by rw [e]; simp [sched.TS_BLOCKED_ON_NTFN])))

/-- **`target ∈ T` from fl4-sync's `SetTimerFound`** (P3's `JAtZ.threadCapT`). -/
theorem tg_ofS (h : SlJAtS (L := L) Kl Cs Ac s) {target : U64}
    (hf : Fl4Proofs.P3.SInvR.G5.SetTimerFound (L := L) s target) : target ∈ Kl.heap.tcbs := by
  obtain ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩ := h
  obtain ⟨r, er, ecr⟩ := hf _ (cur_thread_ok (L := L) s)
  exact B.j.threadCapT (cur_thread_ok (L := L) s) er ecr

variable {T Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- **`RdTab` from the bundle** (module docstring). -/
theorem rdTab_ofBun (BI : BunIx (L := L) Kl T Cs Ω H Sg Rp Scs Nt Z Ac s) {Locks : S → U64 → Prop} :
    RdTab (L := L) (IoRS (st := st) Kl Locks s) s := by
  have hY := irqLayK_of_slJAt BI.bxi BI.ac.slJAt
  intro hi hhi
  exact ⟨⟨(hY.tab hi hhi).1.1, (hY.tabU hi hhi).1, rperm_none (hY.tab hi hhi).1.2 _⟩,
    fun lo hlo hne => ⟨((hY.tab hi hhi).2 lo hlo hne).1, (hY.tabU hi hhi).2 lo hlo hne,
      rperm_none ((hY.tab hi hhi).2 lo hlo hne).2 _⟩⟩

end bun

/-! ## 2. vt: the kernel-block parts of `VtmU` -/

section vtu
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- A word of region `.node c` lies in core `c`'s node. -/
theorem inNode_of_region {Kl : OwnMap.KLayout} {b c : U64} (hr : region Kl b = .node c) : InNode Kl c b := by
  unfold region at hr
  by_cases h : ∃ c, InNode Kl c b
  · rw [dif_pos h] at hr
    cases hr
    exact Classical.choose_spec h
  · rw [dif_neg h] at hr
    split_ifs at hr <;> cases hr

variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **The store's kernel base is the layout's** wherever `StLay` holds (its node words are the layout's node). -/
theorem ksb_pin {Kl : OwnMap.KLayout} {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay Kl st T Scs Z s) : L.ksb s = Kl.ksb := by
  have h0 := hI.1.choose_spec.choose_spec
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  obtain ⟨-, a1, -⟩ := inNode_of_region (hL.nd 0#u64 (by simp))
  obtain ⟨-, -, b2⟩ := inNode_of_region (hL.nd 4287#u64 (by simp))
  have v0 := nodeAt_val hN (off := 0#u64) (by simp)
  have v1 := nodeAt_val hN (off := 4287#u64) (by simp)
  have e0 : (0#u64 : U64).val = 0 := by simp
  have e1 : (4287#u64 : U64).val = 4287 := by simp
  unfold LawfulStore.nodeBase at v0 v1
  apply UScalar.eq_of_val_eq
  omega

/-- **`VtmU` at a `VtPre` state from one bundle state of the layout and the pool part** (module docstring). -/
theorem vtmU_of {K : KLayoutV} {lk : S → U64 → Prop} {irq n : U64} {s σ0 : S}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (h0 : SlJAt (L := L) K.toKLayout σ0)
    (tp : ∀ hi : U64, hi.val < 2048 → ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      peAF (L.mem s (atAF (L.ksb s) hi)) lo ∉ K.user) :
    VtmU K st irq s := by
  have hk := ksb_pin hE.ent.inv hE.ent.lay
  have hk0 : L.ksb σ0 = K.ksb := slJAt_ksb h0
  refine ⟨fun hb i hi hu => ?_, fun hu => ?_, fun hi hhi => ⟨fun hu => ?_, fun lo hlo hne => tp hi hhi lo hlo hne⟩⟩
  · rw [Fl4Proofs.P3.state_off_eq] at hi
    obtain rfl := ok_inj_ff hi
    rw [hk] at hu
    exact h0.userKs hu (o := Fl4Proofs.P3.irqOff irq) (by rw [irqOff_val hb]; omega) rfl
  · unfold krA at hu
    rw [hk] at hu
    exact h0.userKs hu (o := layout.ks.KERNEL_ROOT) (by simp [layout.ks.KERNEL_ROOT]) rfl
  · rw [hk, ← hk0] at hu
    exact h0.userAsid hu hhi rfl

end vtu

/-! ## 3. Reduced entry facts and records -/

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **What stays of `VmBaseR`**: `run` [J] and `VmLay` [J] (module docstring). -/
structure VmBaseR7 (Kl : OwnMap.KLayout) (s : S) : Prop where
  /-- [J] (module docstring: needs the entry's non-idle current thread and P3 excluding `RUNNING_VM`). -/
  run : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING
  /-- [J] (module docstring: no `IoLay`-from-bundle lemma). -/
  lay : VmLay Kl

/-- **vmF's start entry facts, shrunk** (module docstring). -/
structure VmFEntJ7 (i : VmFArg S) (K : KLayoutV) (s : S) : Prop where
  /-- No VCPU in the layout (the glue's layout choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Index convention (`BunIx`, a choice of index: `bunIx_of`). -/
  ix : BunIx (L := L) K.toKLayout i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [J] -/
  br : VmBaseR7 st K.toKLayout s
  /-- [J] as `VmFPre.hyp` (module docstring). -/
  hyp : ∀ a s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) →
    VmFootHyps (L := L) i.T i.Cs i.Ω i.U i.Sg i.Rp i.Scs i.Nt i.Ac i.H i.Z s1
  /-- [P] as `VmFPre.lk`. -/
  lk : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → i.Locks s ptr ∧ i.Locks s r
  /-- [J] as `VmFPre.hyt` (module docstring). -/
  hyt : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → L.mem s (yieldA dest) = 0#u64
  /-- [P] -/
  gl : VmGlue st ar i.Locks s

theorem VmFEntJ7.toJ {i : VmFArg S} {K : KLayoutV} {s : S} (E : VmFEntJ7 st ar i K s) : VmFEntJ st ar i K s :=
  ⟨E.nv, E.ix, ⟨curEnt_of E.ix.ac E.br.run, E.br.lay⟩, E.hyp, E.lk, E.hyt, E.gl, rdTab_ofBun E.ix⟩

/-- **vmR's start entry facts, shrunk** (module docstring). -/
structure VmREntJ7 (i : VmRArg S) (Kl : OwnMap.KLayout) (s : S) : Prop where
  /-- Index convention. -/
  ix : BunIx (L := L) Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
    Kl.heap.scBits i.Ac s
  /-- [J] -/
  br : VmBaseR7 st Kl s
  /-- [J] as `VmRPre.mid`. -/
  mid : ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
    BXI st Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits i.Ac s2 ∧
      AsidOff (L := L) i.Ω i.Sg s2 ∧
      ∀ u usc, RRChecksG st ar fl4_abi.consts.fault.VMFault s2 a2 (L.curW s) i.rptr i.ep u usc →
        RRPl (L := L) Kl.heap.tcbs i.Cs i.Ω i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits s2
          (L.curW s) i.rptr i.ep u usc ∧ L.mem s2 (yieldA u) = 0#u64
  /-- [P] -/
  lk : i.Locks s i.rptr ∧ i.Locks s i.ep
  /-- [P] -/
  nb : L.mem s (rPrevA i.rptr) = 0#u64 ∧ L.mem s (rNextA i.rptr) = 0#u64
  /-- [J] -/
  hNt : ∀ p ∈ Kl.heap.ntfns, Kl.heap p = some .ntfn ∧ p.val % 64 = 0 ∧ p.val + 64 ≤ 2 ^ 64 ∧
    ∀ b, InW p 64 b → region Kl b = .ntfn p
  /-- [J] -/
  nbt : L.mem s (boundA (L.curW s)) ≠ 0#u64 → L.mem s (fld (L.mem s (boundA (L.curW s))) 24#u64) = L.curW s
  /-- `loc_chain_all` clause 10's fl4-sync input `hfd`. -/
  fd : VmFoundC st i.rptr i.ep s

theorem VmREntJ7.toJ {i : VmRArg S} {Kl : OwnMap.KLayout} {s : S} (E : VmREntJ7 st ar i Kl s) :
    VmREntJ st ar i Kl s :=
  ⟨E.ix, ⟨curEnt_of E.ix.ac E.br.run, E.br.lay⟩, E.mid, E.lk, E.nb, E.hNt, E.nbt, rdTab_ofBun E.ix, E.fd⟩

/-- **io's start entry facts, shrunk** (module docstring). -/
structure IoEntJ7 (i : IoArg S) (K : KLayoutV) (s : S) : Prop where
  /-- Index convention. -/
  ix : BunIx (L := L) K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
    K.heap.scBits i.Ac s
  /-- [J] (module docstring). -/
  run : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING
  /-- [J] -/
  lay : IoLay K.toKLayout
  /-- [J] as `IoPre.walk`. -/
  walk : ∃ C : U64 → U64 → Prop, (∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r) ∧
    WalkCl (st := st) s C ∧
    ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots ∧
      OutsideObjs st K.heap.tcbs i.Cs s (cnSlot p (y &&& m)) ∧
      OutsideObjs st K.heap.tcbs i.Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)
  /-- [J] as `IoPre.fin`. -/
  fin : ∀ x, cspace.lookup_slot st s (L.curW s) (L.mem s (regA (L.curW s) layout.reg.CAP)) = ok (.Ok x) →
    x.slot ∈ K.slots ∧ OutsideObjs st K.heap.tcbs i.Cs s x.slot ∧
      OutsideObjs st K.heap.tcbs i.Cs s (core.num.U64.wrapping_add x.slot 8#u64)

theorem IoEntJ7.toJ {i : IoArg S} {K : KLayoutV} {s : S} (E : IoEntJ7 st i K s) : IoEntJ st i K s :=
  ⟨E.ix, curEnt_of E.ix.ac E.run, E.lay, E.walk, E.fin⟩

/-- **st's start entry facts, shrunk** (module docstring): `StPre` and `target ∈ T` derived. -/
structure StEntJ7 (i : StArg S) (K : KLayoutV) (s : S) : Prop where
  /-- Index convention. -/
  ix : BunIx (L := L) K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
    K.heap.scBits i.Ac s
  /-- [P] fl4-sync's `SetTimerFound` (`loc_chain_all` clause 5's own input): the `CAP` register names the
  `Thread target` slot. -/
  fd : Fl4Proofs.P3.SInvR.G5.SetTimerFound (L := L) s i.target

theorem StEntJ7.toJ {i : StArg S} {K : KLayoutV} {s : S} (E : StEntJ7 st i K s) : StEntJ4 st i K s :=
  ⟨E.ix, stPre_ofS E.ix.ac, tg_ofS E.ix.ac E.fd⟩

/-- **vt's premises, `tu` shrunk to the pool words** (module docstring). -/
structure VtPremP7 (i : VtArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (the glue's layout choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- [J] at every `VtPre` state the ASID pool words are no user words (module docstring). -/
  tp : ∀ s, VtPre st i K s → ∀ hi : U64, hi.val < 2048 → ∀ lo : U64, lo.val < 512 →
    L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 → peAF (L.mem s (atAF (L.ksb s) hi)) lo ∉ K.user
  /-- [J] -/
  eu : ∀ s b v', VtPre st i K s → b ∈ K.user → Aligned b → VtPre st i K (L.wr s b v')
  /-- [P] -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- P1's notifications typed in the heap. -/
  Nt : ∀ q ∈ i.Nt, i.H q = some .ntfn
  /-- [J] -/
  M : ∀ s, VtPre st i K s → ∀ y ∈ i.T, m (fld y oAFFINITY) = L.mem s (affA y)
  /-- [J] -/
  OL : ObjLay K.toKLayout i.H i.Rp
  /-- [P] -/
  PL : PlanLk i.lk i.pl
  /-- [J] -/
  UB : ∀ s, VtPre st i K s → ∃ U : Set U64, Fl4Proofs.P1.UserOK st i.T i.Cs i.Ω i.H U s ∧
    ∀ y ∈ i.T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄
  /-- [J] -/
  SL : ∀ s, VtPre st i K s → SlotLayV K.toKLayout st i.T s
  /-- [J] -/
  pSg : ∀ s, VtPre st i K s → core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ∉ i.Sg

theorem VtPremP7.toP5 {i : VtArg S} {K : KLayoutV} {m : U64 → U64} (h : VtPremP7 st i K m) : VtPremP5 st i K m :=
  ⟨h.nv, fun s hE => vtmU_of hE h.bun.choose_spec (h.tp s hE), h.eu, h.kd, h.Nt, h.M, h.OL, h.PL, h.UB, h.SL, h.pSg⟩

end ent

/-! ## 4. The start fact and the top -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **The start fact of `fl4LocP3W5`, entry facts and vt's record shrunk** (module docstring). -/
def StartP3W7 (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => ∃ h : VmFPrem st ar j K m, GlueAt ((vmFSlot st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmFEntJ7 st ar j K σ) c hs m q
  | .vmR j => ∃ h : VmRPremP3 st ar j K m, GlueAt ((vmRSlotP3 st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmREntJ7 st ar j (userV K) σ) c hs m q
  | .io j => ∃ h : IoPremW3 st j K m, GlueAt ((ioSlotP3W st ar hA hm).liftAt j K m hK hU h.toP3)
      (fun σ : S => Ch σ ∧ IoEntJ7 st j K σ) c hs m q
  | .st j => ∃ h : StPremW3 st j K m, GlueAt ((stSlotP3W st ar hA hm).liftAt j K m hK hU h.toP3)
      (fun σ : S => Ch σ ∧ StEntJ7 st j K σ) c hs m q
  | .vq (.inr j) => ∃ h : VtPremP7 st j K m, GlueAt ((vtSlotP3W5 st ar hA hm).path j K m hK hU h.toP5)
      (fun σ : S => Ch σ ∧ VtEntJ4 st j K σ) c hs m q
  | i => StartP3W5 st ar hA hm hSt a0 Ch K m hK hU c hs q i

/-- **`StartP3W7` gives `StartP3W5`** (module docstring). -/
theorem startP3W5_of_W7 {Ch : S → Prop} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K}
    {c : U64} {hs : U64 → Prop} {q : SP} {i : Fl4IxW (S := S)}
    (h : StartP3W7 st ar hA hm hSt a0 Ch K m hK hU c hs q i) :
    StartP3W5 st ar hA hm hSt a0 Ch K m hK hU c hs q i := by
  cases i with
  | vmF j =>
    obtain ⟨h, hG⟩ := h
    exact ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ st ar⟩⟩
  | vmR j =>
    obtain ⟨h, hG⟩ := h
    exact ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ st ar⟩⟩
  | io j =>
    obtain ⟨h, hG⟩ := h
    exact ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ st⟩⟩
  | st j =>
    obtain ⟨h, hG⟩ := h
    exact ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ st⟩⟩
  | irq j => exact h
  | sl j => exact h
  | vq j =>
    cases j with
    | inl j => exact h
    | inr j =>
      obtain ⟨h, hG⟩ := h
      exact ⟨h.toP5, hG⟩

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end at P3 scope over W5's family, per-slot [J] residue shrunk** (module docstring):
`serializable_fl4_localW5` with `StartP3W7` starts. -/
theorem serializable_fl4_localW7 (P : LocPlat st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (hB : SerExitW P K0 Ch0) (nv0 : K0.vcpus = ∅)
    (hM0 : MapsV K0 s0)
    (h : ExecW ((fl4LocP3W5 st ar hA hm hSt a0).paths (fl4Dflt st ar hm)) (StartP3W7 st ar hA hm hSt a0) P s0 K0
      Ch0 s K Ch) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have hE := (execV_of_W (fun _ _ _ _ _ _ _ _ _ hCh hi =>
    startAt_P3W5 st ar hA hm hSt a0 hCh (startP3W5_of_W7 st ar hA hm hSt a0 hi)) hB h).1
  have hok := serExitW_ok hB (vcpuLay_empty nv0)
  exact serializable_fl4_localP3W5V st ar hA hm hSt a0 h0 hA0 hok.1 hok.2 hM0 hE hq

end top

end
end Fl4Proofs.P2.E2EV

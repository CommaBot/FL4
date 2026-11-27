/-
# P2 (line vmscope, gen 5): io without [J]; `TCB_SetTimer` and the timer interrupt in VM epochs —
# `serializable_fl4_localVX5`

`serializable_fl4_localVX4` (P2/E2EPVX4.lean) ran the I/O-port slot in VM epochs under two [J]s U1 does not have
(`IoPremX2.iw`: `IoPre` survives a user / VCPU-data write; `.qf`: the caller's `Q` does). This module

1. **discharges both**: every frame fact the io path needs follows from the layout alone once the VCPU data words
   are counted as user memory. **`userLayX_userV`**: `UserLayX` (the store-free user-word layout of VX2) holds at
   `userV K`, from the epoch's `VtxBundle4` (`VcpuHeap`, `vsl`, `VcpuKsOff`, `RegionOKV.none`) and the kernel base's
   fit (any node placement). **`ioPre_wrL`**: `IoPre` is kept by an aligned user-word write at any layout with
   `UserLayX` (`SlJAt.ioPre_wr` without a bundle: `BXI` by `bxi_userX`, node / TCB / SC words by `RegionOKX`, the
   CSpace walk's slot words by `LayP.userSlot` via `cap_wrL`). `qf` follows once the index's `Q` is U1's `IoQ`
   (index convention `hQ`, as U1's `IoPremW9.hQ`). Record **`IoPremX5`** (`hQ`, `hCs` conventions; `kd` [P]),
   **`IoPremX5.toX2`**, **`IoStartX5`**, **`ioStartX_of_X5`**.
2. **`TCB_SetTimer` in VM epochs** (`stSlotX`: `set_timer_localPathA` at `userV K`, `Pre := StEntV`, no P3 bundle):
   **`stEnt_wrL`** (`stEnt_wr` from `UserLayX` instead of a bundle state) gives st's `eu`; `ReadOnce` by `st_hro`,
   the node words by `StLay.nu_node`, the locks by U1's `kd` [P]. PTE avoidance **`st_avoidPX_path`** (copy of
   `stm_avoidPJ_path`), **`stSlotPX`**, record **`StPremX5`** (`hCs`, `kd` [P]), start **`StStartX`**,
   **`stStartX_at`**.
3. **the timer interrupt in VM epochs** (`irqSlotX`: `irq_localPathX`, `Pre := IrqPreX` = `IrqEntM` at `userV K`
   with a `BufAt` placement, no `SlJAt`, no `VFacts`): **`irqLay_wrL`**, **`irqFx_wr`** (the `Pre` across a
   `userV K` user write), **`irq_pathOblX`** / **`irq_pathSideX`** / **`irq_hroX`** (the `_V` proofs with `ObjLay`
   by `objLay_of_layP`, `SlotLayV` by `slotLayV_ofLayX`, `BufAt` from the state), **`irq_avoidPX_path`**,
   **`irqSlotPX`**, record **`IrqPremX5`** (`lt`, `kd` [P], `pl` [P]), start **`IrqStartX`**, **`irqStartX_at`**.
4. Tops: **`StartVX5`**, **`serializable_fl4_localVX5G`**, **`serializable_fl4_localVX5`** = VX4's family
   ⊕ `stSlotPX` ⊕ `irqSlotPX`, the io slot at `IoStartX5`. Glue `ExecVX4` (VM exits carry `VtxBundle4` [S]).

Slots that start in VM epochs: VM exit (vx), VM timer (vt), I/O port (io), `TCB_SetTimer` (st), timer interrupt
(irq). Native epochs: all of U1's (vmF, vmR, io, st, irq, sl, vx, vt, delPte, CNodeDelete, Copy/Mint).

## Premise diff vs `serializable_fl4_localVX4`
| where | VX4 | VX5 |
|---|---|---|
| io record | `IoPremX2`: `iw` [J], `qf` [J], `kd` [P] | `IoPremX5`: `hQ` (conv., U1's `IoPremW9.hQ`), `hCs` (conv., VX2's `VxIx.hCs`), `kd` [P] (unchanged) — **no [J]** |
| io start entry | `IoPre ∧ Q ∧ QPs` [S] | unchanged |
| st | native epochs only | also VM epochs: record `StPremX5` (`hCs` conv., `kd` [P] = U1's `StPremW3B.kd`); start entry `StEnt ∧ QPs` [S]; `GlueAt` data [P] |
| irq | native epochs only | also VM epochs: record `IrqPremX5` (`lt` as U1's, `kd` [P] = U1's `IrqPremK2B.kd` at entry states instead of bundle states, `pl` [P] = U1's); start entry `IrqEnt (userV K) ∧ BufAt ∧ QPs` [S]; `GlueAt` data [P] |
| everything else | | unchanged |
No new [J] and no [W]; VX4's two [J]s are gone, so VX5's VM-epoch slots carry no [J] at all.

## [S] justification (Rust: fl4-core `localtimer.rs`, `timer.rs`, `arch/x86_64/objects.rs`, `vcpu.rs`, `asid.rs`)
* st start entry `StEnt K ∧ QPs` — P1's entry facts of `handle_set_timer_local` (`BXI`, the layout's `StLay`, the
  current thread's scheduling facts, `target ∈ T`) at a state where another core runs a guest. They read the current
  thread, its SC, the timer tree and the target TCB; a guest writes only its VCPU's data words and guest frames
  (`HwStepP`), none of which is a TCB / SC / node word (`VtxBundle`: VCPUs are `other 15` objects). P3 has no such
  state (`JExt.vw`), so the fact is scope, not [J]; natively it is `StEntJ7`'s bundle consequence.
* irq start entry `IrqEnt (userV K) ∧ BufAt ∧ QPs` — `handle_timer_irq_local`'s P1 entry facts: as st's, plus
  `IrqLay` at `userV K` (the IRQ-state / kernel-root / ASID-table words are ks-block words, the ASID-pool entries
  words of untyped-retyped ASID-pool objects: none is a user frame word or a word of a `bits::VCPU` object) and
  `BufAt` (every TCB's IPC buffer is a frame-cap page: `msg::lookup_ipc_buffer` reads the `SLOT_BUFFER` cap, and
  VCPUs are never frames). Natively `IrqPreJ3.entM` / `SlotJC.bufAt` from the bundle.
* `VtxBundle4`, the vx / vt / io entries — unchanged from VX4 (justified there).

## [P]s
* `IoPremX5.kd` — VX4's `IoPremX2.kd` unchanged. `StPremX5.kd` — U1's `StPremW3B.kd` unchanged (unconditional).
  `IrqPremX5.kd` — U1's `IrqPremK2B.kd` ("at bundle states") read at the interrupt's entry states (no `m`): the
  locks are fl4-sync `local_timer_irq`'s `plan_timer_irq` objects, which `plan_timer_irq` reads from this core's node and the timer tree (kernel words) only.
  `IrqPremX5.pl` — U1's `PlanLk`.

No sorry / admit / native_decide / bv_decide. No existing statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPVX4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW InNode RegionOK LayP TcbSlot oTIMER_DEADLINE GateField
  TimerField tcbOwner tOwner)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## Part 1: the user-word layout at `userV K` -/

section lay
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutV}

/-- **`UserLayX` at `userV K`** (the VCPU data words counted as user memory): the VCPU words lie in `other 15`
heap objects (`VcpuHeap`, so off every other heap object, `noVcpu_of_kind`), in no CNode slot (`vsl`), off the
kernel-global area `[ksb, ksb + 304384)` (`VcpuKsOff`, which holds the ks block and the 64 nodes), and in region
`.none` (`RegionOKV.none`). -/
theorem userLayX_userV (U : UserLayX L K.toKLayout) (hK : RegionOKV K) (hV : VcpuHeap K) (ko : VcpuKsOff K)
    (vsl : ∀ p ∈ K.slots, ∀ b, InW p 32 b → ¬ ∃ v, InVcpu K v b) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) :
    UserLayX L (userV K) where
  rx :=
    { tslot := U.rx.tslot, tcbW := U.rx.tcbW, epW := U.rx.epW, rpW := U.rx.rpW, scW := U.rx.scW, scP := U.rx.scP,
      ntW := U.rx.ntW, node := U.rx.node, ks := U.rx.ks, asidT := U.rx.asidT
      kern := fun b hr hu => (mem_userV.1 hu).elim (U.rx.kern b hr) (notVData_of_region' hK hr) }
  lp :=
    { heap := U.lp.heap, node := U.lp.node, slot := U.lp.slot
      user := fun x hx p k hp hk hin => (mem_userV.1 hx).elim (fun hu => U.lp.user x hu p k hp hk hin) fun hv =>
        notVData_of_noVcpu (noVcpu_of_kind U.lp.heap hV hp
          (by rcases hk with rfl | rfl | ⟨z, rfl⟩ <;> intro e <;> cases e) hin) hv
      userSlot := fun x hx p hp hin => (mem_userV.1 hx).elim (fun hu => U.lp.userSlot x hu p hp hin)
        fun ⟨v, hv, _⟩ => vsl p hp x hin ⟨v, hv⟩ }
  uobj := fun x hx p k hp hk hin => (mem_userV.1 hx).elim (fun hu => U.uobj x hu p k hp hk hin) fun hv =>
    notVData_of_noVcpu (noVcpu_of_kind U.lp.heap hV hp (fun e => hk 15 e) hin) hv
  uks := fun x hx o ho e => (mem_userV.1 hx).elim (fun hu => U.uks x hu o ho e) fun ⟨v, ⟨hv, h1, h2⟩, _⟩ => by
    have e' : x = core.num.U64.wrapping_add K.ksb o := e
    have ev : (core.num.U64.wrapping_add K.ksb o).val = K.ksb.val + o.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [e', ev] at h1 h2
    rcases ko v hv with h | h <;> omega
  unode := fun x hx c hc s hs => (mem_userV.1 hx).elim (fun hu => U.unode x hu c hc s hs)
    fun ⟨v, ⟨hv, h1, h2⟩, _⟩ => by
      have hs' : L.ksb s = K.ksb := hs
      simp only [LawfulStore.nodeBase, hs']
      rcases ko v hv with h | h <;> omega
  nc := U.nc

end lay

/-! ## Part 2: `IoPre` across a user-word write, from `UserLayX` -/

section wr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Kl : KLayout} {Cs Ω Sg Ac : Set U64}

/-- A slot's cap is kept by a user-word write (`SlJAt.cap_wr` from `LayP` alone). -/
theorem cap_wrL (hP : LayP Kl) {s : S} {b : U64} (hb : b ∈ Kl.user) (hba : Aligned b) (v : U64)
    {x : U64} (hx : x ∈ Kl.slots) : obj.Slot.cap st x (L.wr s b v) = obj.Slot.cap st x s := by
  obtain ⟨n0, n8⟩ := slot_nu hP hx
  unfold obj.Slot.cap
  rw [L.read_pair_eq, L.read_pair_eq, wr_nu hba hb v n0, wr_nu hba hb v n8]

/-- **`IoPre` is kept by an aligned user-word write, at any layout with `UserLayX`** (`SlJAt.ioPre_wr` without a
P3 bundle: `BXI` by `bxi_userX`, the node / TCB / SC words by `RegionOKX`, the slot words by `LayP.userSlot`;
canonical sets, `Cs` below 64 cores). -/
theorem ioPre_wrL (U : UserLayX L Kl) (hCs : ∀ c ∈ Cs, c.val < 64) {s : S}
    (P : IoPre st Kl Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac s)
    {b : U64} (hb : b ∈ Kl.user) (hba : Aligned b) (v : U64) :
    IoPre st Kl Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac
      (L.wr s b v) := by
  have hX := U.rx
  have hk : L.ksb s = Kl.ksb := P.kb.symm
  have Gw : Ag st (NU Kl) s (L.wr s b v) := ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb v hx⟩
  have hnd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → NU Kl (L.nodeAt s (L.cpu s) o) := fun o ho h8 =>
    nu_of_region hX (nodeAt_aligned P.np ho h8) (by rw [hX.node _ _ (P.inNode o ho)]; intro h; cases h)
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s b v) (L.nodeAt (L.wr s b v) (L.cpu (L.wr s b v)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o ho h8 => by rw [Gw.node]; exact Gw.m _ (hnd o ho h8)
  have ecur : L.curW (L.wr s b v) = L.curW s := eN _ (by rw [curth_val]; omega) (by rw [curth_val])
  have ecsc : L.cscW (L.wr s b v) = L.cscW s := eN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have etm : L.mem (L.wr s b v) (tmA (L := L) (L.wr s b v)) = L.mem s (tmA (L := L) s) :=
    eN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have ek : L.ksb (L.wr s b v) = L.ksb s := L.ksb_wr _ _ _
  have hcH : Kl.heap (L.curW s) = some .tcb := P.hT _ P.cT
  have hcS : L.curW s ∈ Kl.slots :=
    (P.lay.tslot _ hcH _ _ (tcb_slot_ctable (L.curW s)) (by simp [layout.tcb.SLOT_CTABLE])).1
  have ecapR : L.mem (L.wr s b v) (regA (L.curW s) layout.reg.CAP) = L.mem s (regA (L.curW s) layout.reg.CAP) := by
    have hr := (P.reg (Locks := fun _ _ => True) (r := layout.reg.CAP) (by simp [layout.reg.CAP])).1
    exact wr_nu hba hb v ⟨hr.1, hr.2.1⟩
  obtain ⟨C, hroot, hcl, hsl⟩ := P.walk
  have hB := bxi_userX U hk hCs P.bxi Gw
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := P.bxi
  refine
  { bxi := hB
    csc := by rw [ecsc]; exact P.csc
    hcsc := ?_
    run := ?_
    lay := P.lay
    kb := by rw [ek]; exact P.kb
    nc := by rw [L.cpu_wr]; exact P.nc
    hT := P.hT
    hSc := P.hSc
    curAff := ?_
    cscCore := ?_
    affSc := ?_
    tmc := ?_
    walk := ⟨C, fun p r gs g h => hroot p r gs g (by rw [ecur, cap_wrL U.lp hb hba v hcS] at h; exact h),
      fun p r m y p' r' gs' g' hC hm h =>
        hcl p r m y p' r' gs' g' hC hm (by rw [cap_wrL U.lp hb hba v (hsl p r m y hC hm).1] at h; exact h),
      fun p r m y hC hm => ⟨(hsl p r m y hC hm).1, (hsl p r m y hC hm).2.1.ksb ek, (hsl p r m y hC hm).2.2.ksb ek⟩⟩
    fin := fun x hx => by
      rw [ecur, ecapR] at hx
      have hx' := lookup_slot_back (tcb_slot_ctable (L.curW s)) (cap_wrL U.lp hb hba v hcS)
        (fun p r m y hC hm => cap_wrL U.lp hb hba v (hsl p r m y hC hm).1) hcl hroot hx
      obtain ⟨h1, h2, h3⟩ := P.fin x hx'
      exact ⟨h1, h2.ksb ek, h3.ksb ek⟩ }
  · have e : L.mem (L.wr s b v) (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [ecur, ecsc, e]; exact P.hcsc
  · have e : L.mem (L.wr s b v) (stA (L.curW s)) = L.mem s (stA (L.curW s)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega)
        (by rw [st_val]))
    rw [ecur, e]; exact P.run
  · have e : L.mem (L.wr s b v) (affA (L.curW s)) = L.mem s (affA (L.curW s)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ecur, L.cpu_wr, e]; exact P.curAff
  · have e : L.mem (L.wr s b v) (scCoreA (L.cscW s)) = L.mem s (scCoreA (L.cscW s)) :=
      wr_nu hba hb v (nu_scw hX (P.hSc _ P.cscS) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    rw [ecsc, L.cpu_wr, e]; exact P.cscCore
  · intro t ht h0
    have es : L.mem (L.wr s b v) (scA t) = L.mem s (scA t) :=
      wr_nu hba hb v (nu_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [es] at h0 ⊢
    have hsc := (hXI.2.2.bound t ht h0).1
    have ec : L.mem (L.wr s b v) (scCoreA (L.mem s (scA t))) = L.mem s (scCoreA (L.mem s (scA t))) :=
      wr_nu hba hb v (nu_scw hX (P.hSc _ hsc) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    have ea : L.mem (L.wr s b v) (affA t) = L.mem s (affA t) :=
      wr_nu hba hb v (nu_tcb hX ht (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ec, ea]; exact P.affSc t ht h0
  · intro h0
    rw [etm] at h0 ⊢
    have hT := (hXI.2.2.tm.min _ hq.cur).resolve_left h0
    have ed : L.mem (L.wr s b v) (tdA (L.mem s (tmA (L := L) s))) = L.mem s (tdA (L.mem s (tmA (L := L) s))) :=
      wr_nu hba hb v (nu_tcb hX hT (o := 3528#u64) (by simp) (by simp) (by simp))
    have eh : L.mem (L.wr s b v) (thA (L.mem s (tmA (L := L) s))) = L.mem s (thA (L.mem s (tmA (L := L) s))) :=
      wr_nu hba hb v (nu_tcb hX hT (o := 3568#u64) (by simp) (by simp) (by simp))
    rw [ed, eh, L.cpu_wr]; exact P.tmc h0

end wr

/-! ## Part 3: the VM-epoch I/O-port record without [J] -/

section io5
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The VM-epoch I/O-port record** (module docstring): two index conventions and VX4's `kd` [P]; `iw` and `qf`
(VX4's [J]s) are derived (`IoPremX5.toX2`). -/
structure IoPremX5 (i : IoArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- Index convention: the index's `Q` is stpost's `IoQ` (as U1's `IoPremW9.hQ`). -/
  hQ : i.Q = fun K' m' s => IoQ st i.Cs i.Ω i.Sg i.Ac K'.toKLayout m' s
  /-- Index convention: the index's core set is the layout's cores (as VX2's `VxIx.hCs`). -/
  hCs : i.Cs = {c : U64 | c.val < K.ncores}
  /-- [P] at `Pre` states the locks are determined by the words off `(userV K).user` (VX4's `IoPremX2.kd`). -/
  kd : ∀ s, IoPreX st i K m s → KernDetS (L := L) (userV K).user i.Locks s

variable {st}

/-- **`iw` and `qf` derived**: `IoPremX5` and the epoch's `VtxBundle4` give VX4's `IoPremX2` (`ioPre_wrL` at
`userV K`, whose `UserLayX` is `userLayX_userV`; the `AFFINITY` words of `IoQ` are TCB words, `nu_tcb`). -/
theorem IoPremX5.toX2 {K : KLayoutP} {i : IoArg S} {m : U64 → U64} (h : IoPremX5 st i K.toKLayoutV m)
    (hK : RegionOKV K.toKLayoutV) (E : VtxBundle4 st L K) : IoPremX2 st i K.toKLayoutV m := by
  have hCs : ∀ c ∈ i.Cs, c.val < 64 := by
    rw [h.hCs]; intro c hc; exact Nat.lt_of_lt_of_le hc E.b.ul.nc
  have U : ∀ s, IoPreX st i K.toKLayoutV m s → UserLayX L (userV K.toKLayoutV) := fun s hP =>
    userLayX_userV E.b.ul hK E.b.vh E.ko E.b.vsl hP.1.lay.ksf.2
  have iw : ∀ s b v, IoPreX st i K.toKLayoutV m s → b ∈ (userV K.toKLayoutV).user → Aligned b →
      IoPre st (userV K.toKLayoutV) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac (L.wr s b v) :=
    fun s b v hP hb hba => ioPre_wrL (U s hP) hCs hP.1 hb hba v
  refine ⟨iw, fun s b v hP hb hba => ?_, h.kd⟩
  have q : IoQ st i.Cs i.Ω i.Sg i.Ac K.toKLayout m s := by
    have h2 := hP.2.2
    rw [h.hQ] at h2
    exact h2
  rw [h.hQ]
  refine ⟨{ iw s b v hP hb hba with lay := q.1.lay }, fun d hd => ?_⟩
  rw [show L.mem (L.wr s b v) (fld d oAFFINITY) = L.mem s (fld d oAFFINITY) from
    wr_nu hba hb v (nu_tcb (U s hP).rx hd (o := oAFFINITY) (by simp [oAFFINITY]) (by simp [oAFFINITY])
      (by simp [oAFFINITY]))]
  exact q.2 d hd

end io5

/-! ## Part 4: `TCB_SetTimer` at any layout -/

section stF
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Kl : KLayout} {Cs Ω Sg Ac : Set U64} {target : U64}

/-- **`StEnt` across a user-word write, from `UserLayX`** (`stEnt_wr` without a P3 bundle: `BXI` by `bxi_userX`,
the TCB / SC words by `RegionOKX`, the node words by `StLay.nu_node`). -/
theorem stEnt_wrL (U : UserLayX L Kl) (hCs : ∀ c ∈ Cs, c.val < 64) {X : S}
    (hE : StEnt Kl st Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac
      target X) {b : U64} (hb : b ∈ Kl.user) (hba : Aligned b) (v : U64) :
    StEnt Kl st Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac target
      (L.wr X b v) := by
  have hX := U.rx
  have h0 := hE.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st Kl.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have hk : L.ksb X = Kl.ksb := ksb_of_stLay hE.lay hN
  have G : Ag st (NU Kl) X (L.wr X b v) := ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb v hx⟩
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr X b v) (L.nodeAt (L.wr X b v) (L.cpu (L.wr X b v)) o) = L.mem X (L.nodeAt X (L.cpu X) o) :=
    fun o ho h8 => by
      rw [nodeAt_wr, L.cpu_wr]
      exact wr_nu hba hb v ⟨nodeAt_aligned hN ho h8, hE.lay.nu_node ho⟩
  have ecur : L.curW (L.wr X b v) = L.curW X := eN _ (by rw [curth_val]; omega) (by rw [curth_val])
  have ecsc : L.cscW (L.wr X b v) = L.cscW X :=
    eN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have hcH : Kl.heap (L.curW X) = some .tcb := h0.curT
  have hB := bxi_userX U hk hCs hE.inv G
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := hE.inv
  have hP := hE.pre
  refine ⟨hB, stLay_wrU hE.lay b v, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hE.tg⟩
  · have e : L.mem (L.wr X b v) (affA (L.curW X)) = L.mem X (affA (L.curW X)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ecur, L.cpu_wr, e]; exact hP.aff
  · have e : L.mem (L.wr X b v) (stA (L.curW X)) = L.mem X (stA (L.curW X)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega)
        (by rw [st_val]))
    rw [ecur, e]; exact hP.nq
  · have e : L.mem (L.wr X b v) (scA (L.curW X)) = L.mem X (scA (L.curW X)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [ecur, ecsc, e]; exact hP.sct
  · rw [ecsc]; exact hP.csc
  · have e : L.mem (L.wr X b v) (scCoreA (L.cscW X)) = L.mem X (scCoreA (L.cscW X)) :=
      wr_nu hba hb v (nu_scw hX (scs_heap hP.csc) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    rw [ecsc, L.cpu_wr, e]; exact hP.core
  · intro t ht h1
    have es : L.mem (L.wr X b v) (scA t) = L.mem X (scA t) :=
      wr_nu hba hb v (nu_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [es] at h1 ⊢
    have hsc := (hXI.2.2.bound t ht h1).1
    have ec : L.mem (L.wr X b v) (scCoreA (L.mem X (scA t))) = L.mem X (scCoreA (L.mem X (scA t))) :=
      wr_nu hba hb v (nu_scw hX (scs_heap hsc) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    have ea : L.mem (L.wr X b v) (affA t) = L.mem X (affA t) :=
      wr_nu hba hb v (nu_tcb hX ht (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ec, ea]; exact hE.aff t ht h1

/-- The kernel base fits below `2 ^ 64` with its 13568-byte block (from a node placement). -/
theorem ksb_fit_of_np {T : Set U64} {s : S} {c : U64} {k : U64} (hN : NodePlaced st T s c) (hk : L.ksb s = k) :
    k.val + 13568 ≤ 2 ^ 64 := by
  have h := hN.fits
  simp only [LawfulStore.nodeBase, hk] at h
  omega

end stF

section stS
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The `TCB_SetTimer` record at any layout** (module docstring): the epoch's layout facts, the index's core set
convention and the lock premise. -/
structure StPremX (i : StArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- The user-word layout facts (from the epoch's `VtxBundle`). -/
  ul : UserLayX L K.toKLayout
  /-- `VcpuHeap` (from the epoch's `VtxBundle`). -/
  vh : VcpuHeap K
  /-- No VCPU word in a CNode slot (from the epoch's `VtxBundle`). -/
  vsl : ∀ p ∈ K.slots, ∀ b, InW p 32 b → ¬ ∃ v, InVcpu K v b
  /-- No VCPU meets the kernel-global area (from the epoch's `VtxBundle4`). -/
  ko : VcpuKsOff K
  /-- Index convention: the index's core set is the layout's cores (as `VxIx.hCs`). -/
  hCs : i.Cs = {c : U64 | c.val < K.ncores}
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user` (U1's
  `StPremW3B.kd`, unchanged). -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s

variable {st}

theorem StPremX.cs64 {i : StArg S} {K : KLayoutV} {m : U64 → U64} (h : StPremX st i K m) :
    ∀ c ∈ i.Cs, c.val < 64 := by
  rw [h.hCs]; intro c hc; exact Nat.lt_of_lt_of_le hc h.ul.nc

/-- **st's `eu` derived at any layout** (`stEnt_wrL` at `userV K`). -/
theorem StPremX.eu {i : StArg S} {K : KLayoutV} {m : U64 → U64} (hK : RegionOKV K) (h : StPremX st i K m) :
    ∀ s b v, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → b ∈ (userV K).user → Aligned b →
    StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      i.target (L.wr s b v) := by
  intro s b v hE hb hba
  have h0 := hE.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.heap.tcbs s (L.cpu s) := h0.nodes _ h0.cur
  have hk : L.ksb s = K.ksb := ksb_of_stLay (Kl := userV K) hE.lay hN
  exact stEnt_wrL (userLayX_userV h.ul hK h.vh h.ko h.vsl (ksb_fit_of_np hN hk)) h.cs64 hE hb hba v

variable (st)

/-- **The `TCB_SetTimer` slot at any layout** (`set_timer_localPathA` at `userV K`, `Pre := StEntV`, no P3 bundle;
`eu` by `StPremX.eu`, the locks by `kd`, the node words by `StLay.nu_node`, `ReadOnce` by `st_hro`). -/
def stSlotX : SlotU (StArg S) where
  Prem i K m := StPremX st i K m
  path i K m hK hU h :=
    set_timer_localPathA (K := userV K) (m := m) (lk := i.lk) (T := K.heap.tcbs) (Cs := i.Cs) (Ω := i.Ω)
      (H := K.heap) (Sg := i.Sg) (Rp := K.heap.replies) (Scs := K.heap.scs) (Nt := K.heap.ntfns) (Z := K.heap.scBits)
      (Ac := i.Ac) (target := i.target) ar i.n hA (regionOK_userV hK) (userOK_userV hK hU)
      (st_isProg S i.n i.target) (st_noZero i.n i.target) hm
      (st_hro ar i.n hA (regionOK_userV hK) (userOK_userV hK hU) hm) (h.eu hK)
      (fun s b v hb hba => hlk_of_kernelDetU (P := fun _ => True) (fun s _ => h.kd s) s b v trivial hb hba)
      (fun s hE o ho => hE.lay.nu_node ho)
  W i K m hK hU h :=
    ⟨fun _ _ _ hr => maxR_noV hr, fun s _ hp hw => hw.elim (maxW_noV hK) fun hd =>
      Or.inl (stDec_noV hK (StEntK.ent hp) hd)⟩

/-- **The `TCB_SetTimer` path at any layout reads no PTE word under `QPs`** (`stm_avoidPJ_path`'s proof with
`Pre := StEntV`; it never used `vcpus = ∅`). -/
theorem st_avoidPX_path (i : StArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (stSlotX st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((stSlotX st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
  have hKu := regionOK_userV hK.base
  have hUOu := userOK_userV hK.base hU.base
  have hp := st_isProg S i.n i.target
  have hz := st_noZero i.n i.target
  have entP : ∀ s, StEntV K.toKLayoutV st i.Cs i.Ω i.Sg i.Ac i.target m s → QPs K st s →
      StEnt (userP K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac i.target s :=
    fun s hs hq => ⟨hs.ent.inv, stLay_userP hK hs.ent.lay
      (hq.ksw (by simp [layout.ks.CUR_DOMAIN])) (hq.ksw (by simp [layout.ks.DOMAIN_TIME])),
      hs.ent.pre, hs.ent.aff, hs.ent.tg⟩
  refine ⟨?_, ?_, IsProg.on hp _ _ _⟩
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : StEntV K.toKLayoutV st i.Cs i.Ω i.Sg i.Ac i.target m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localtimer.handle_set_timer_local st ar s a i.n i.target = ok (true, s1, a1) := hr
    have eP : ∀ (mm : machine.Store S) (x : S), localtimer.handle_set_timer_local mm ar x a i.n i.target =
        interp mm ar (R.localtimer.handle_set_timer_local i.n i.target) x a :=
      fun mm x => congrFun (congrFun (hp A ar mm) x) a
    have hE := hs'.ent
    have hEP := entP s hs' hq
    have g1 := set_timer_acc_own ar hA (lk := i.lk) hE.inv hE.tg hE.lay hE.aff hr'
    have g2 := set_timer_acc_own ar hA (lk := i.lk) hEP.inv hEP.tg hEP.lay hEP.aff hr'
    replace g1 := (eP _ s).symm.trans g1
    replace g2 := (eP _ s).symm.trans g2
    have w1 := (interp_guard _ s a _ g1).2
    have w2 := (interp_guard _ s a _ g2).2
    show localtimer.handle_set_timer_local
      (guard st (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st i.lk) s) (MaxW (userV K.toKLayoutV) st i.lk s))
      ar s a i.n i.target = ok (true, s1, a1)
    refine (eP _ s).trans ?_
    exact guard_of_within (st := st) (L := L) (ar := ar) _ s a _ ((eP st s).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.2 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2))
  · intro s a r hs hr hn s' r' hA' h'
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : StEntV K.toKLayoutV st i.Cs i.Ω i.Sg i.Ac i.target m s := hs1
    have hq : QPs K st s := hs2
    have hAl : PathObl.Alt st (MaxR (userV K.toKLayoutV) st i.lk s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have h'' : localtimer.handle_set_timer_local st ar s' a i.n i.target = ok r' := h'
    have eP : ∀ (mm : machine.Store S) (x : S), localtimer.handle_set_timer_local mm ar x a i.n i.target =
        interp mm ar (R.localtimer.handle_set_timer_local i.n i.target) x a :=
      fun mm x => congrFun (congrFun (hp A ar mm) x) a
    have hEK := hs'
    have hE := hEK.ent
    have hEP := entP s hs' hq
    have hko : L.mem s (affA i.target) = L.cpu s →
        OwnMap.ko (userV K.toKLayoutV) m (tdA i.target) = .core (L.cpu s) := set_timer_ko hKu hUOu hEK
    have hcls := set_timer_cls hE
    have hU := set_timer_user hKu hUOu hE
    show localtimer.handle_set_timer_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a i.n i.target
      = ok r'
    obtain ⟨b, s1, a1⟩ := r
    cases b
    swap
    · exact absurd rfl hn
    have hr' : localtimer.handle_set_timer_local st ar s a i.n i.target = ok (false, s1, a1) := hr
    by_cases hfar : L.mem s (affA i.target) ≠ L.cpu s ∨ L.mem s (tdA i.target) = 0#u64 ∨
        (L.mem s (thA i.target)).val >>> 8 = (L.cpu s).val
    · have g := set_timer_dec_guard ar hA (lk := i.lk) hEP.inv hEP.tg hEP.lay hEP.pre hEP.aff hfar hr'
      replace g := (eP _ s).symm.trans g
      obtain ⟨s1', g'⟩ := interp_agree hm (fun w hw => hw.2.1) (fun w hw => (hE.dec hw).1) _ hz s s' a false s1 a1
        hAl.ksb hAl.cpu hAl.masks (fun w hw => hAl.read w ⟨hw.1, hw.2.1, fun hu => hw.2.2 (Or.inl hu)⟩) g
      obtain ⟨hst, w⟩ := interp_guard _ s' a _ g'
      have e : r' = (false, s1', a1) := Result.ok_injective (((eP st s').symm.trans h'').symm.trans hst)
      subst e
      refine (eP _ s').trans ?_
      exact guard_of_within (st := st) (L := L) (ar := ar) _ s' a _ hst
        (Within.mono (fun b hb hq => hb.2.2 (Or.inr hq)) (fun _ _ => trivial) _ s' a w)
    · rw [not_or, not_or, not_not] at hfar
      obtain ⟨hat, hd, hh⟩ := hfar
      have h0 := hE.inv.1.choose_spec.choose_spec
      have hT : TcbPlaced (Heap.tcbs K.heap) := h0.tcbs
      have hN : NodePlaced st (Heap.tcbs K.heap) s (L.cpu s) := h0.nodes _ h0.cur
      obtain ⟨W0, ct⟩ := (TInv.rb (BXI.blk hE.inv)).tree _ h0.cur
      have eN : ∀ o, L.nodeAt s' (L.cpu s) o = L.nodeAt s (L.cpu s) o := fun o => nodeAt_of_ksb hAl.ksb _ o
      have keyR : ∀ y ∈ W0.keys, ∀ k : U64, 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
          L.mem s' (core.num.U64.wrapping_add y k) = L.mem s (core.num.U64.wrapping_add y k) := by
        intro y hy k h1 h2 h3
        refine hAl.read _ ⟨Or.inl (held_core ?_), field_aligned (hT y (ct.inT y hy)) (by omega) h3,
          hE.lay.nu_tcb (ct.inT y hy) (by omega) (by omega)⟩
        have e := hE.lay.own_tcb hT (L.mem s) (ct.inT y hy) (k := k) (by omega) (by omega)
        unfold fld at e
        rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
          if_pos (show TimerField k.val by unfold TimerField; omega), tOwner,
          if_pos (show (L.mem s (fld y oTIMER_DEADLINE)).val ≠ 0 from
            fun h => ct.armed y hy (UScalar.eq_of_val_eq h))]
        have e2 := ct.core y hy
        rw [Nat.shiftRight_eq_div_pow] at e2
        exact congrArg Owner.core (MoveTimer.treeCore_of (c := L.cpu s) e2)
      have ct' : CoreTree st (Heap.tcbs K.heap) s' (L.cpu s) W0 := CoreTree.agree ct eN
        (hAl.read _ (nodeR hE (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])))
        (hAl.read _ (nodeR hE (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])))
        (fun y hy => ⟨keyR y hy _ (by simp) (by simp) (by simp), keyR y hy _ (by simp) (by simp) (by simp),
          keyR y hy _ (by simp) (by simp) (by simp), keyR y hy _ (by simp) (by simp) (by simp),
          keyR y hy _ (by simp) (by simp) (by simp)⟩)
      have hd' : L.mem s' (tdA i.target) ≠ 0#u64 := by
        by_cases hin : MaxR (userV K.toKLayoutV) st i.lk s (tdA i.target)
        · rw [hAl.read _ hin]; exact hd
        · have e := hAl.clsEq _ hin hU (Or.inr (hko hat))
          exact fun h => hd ((hcls _ _ e).1 h)
      have hcur : L.curW s' = L.curW s := by
        unfold LawfulStore.curW
        rw [hAl.cpu, eN]
        exact hAl.read _ (nodeR hE (by rw [curth_val]; omega) (by rw [curth_val]))
      have hk : i.target ∉ W0.keys := fun h => hh (ct.core i.target h)
      rw [← hAl.cpu] at ct'
      have hN' : NodePlaced st (Heap.tcbs K.heap) s' (L.cpu s') := by rw [hAl.cpu]; exact hN.ksb hAl.ksb
      have hnR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
          Aligned (L.nodeAt s' (L.cpu s') o) ∧ L.nodeAt s' (L.cpu s') o ∉ K.ptes := by
        intro o h1 h2
        refine ⟨nodeAt_aligned hN' h1 h2, ?_⟩
        have e : L.nodeAt s' (L.cpu s') o = L.nodeAt s (L.cpu s) o := by rw [hAl.cpu]; exact eN o
        rw [e]
        intro hq
        have h3 : region K.toKLayout (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) := hE.lay.nd o h1
        rw [hK.none _ hq] at h3
        cases h3
      have hfR : ∀ {x k : U64}, x ∈ Heap.tcbs K.heap → k.val < 4096 → k.val % 8 = 0 →
          Aligned (core.num.U64.wrapping_add x k) ∧ core.num.U64.wrapping_add x k ∉ K.ptes :=
        fun {x k} hx h1 h2 => ⟨field_aligned (hT _ hx) h1 h2,
          fun hq => region_tcb_ne_none (K := K.toKLayout) hx (tcb_wadd_val (hT _ hx) h1) h1 (hK.none _ hq)⟩
      obtain ⟨-, h2⟩ := set_timer_farR (R := fun w => Aligned w ∧ w ∉ K.ptes) ar hT hN'
        (by rw [hcur]; exact h0.curT) hE.tg ct' hk hd' hnR hfR h''
      replace h2 := (eP _ s').symm.trans h2
      refine (eP _ s').trans ?_
      exact interp_mono (fun _ hq => hq.2) (fun _ hq => hq.elim) _ hz s' a r' h2

/-- **The `TCB_SetTimer` slot's family member reads no PTE word under `QPs`.** -/
theorem st_avoidPX (i : StArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) :
    AvoidP K (((stSlotX st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  by_cases hp : (stSlotX st ar hA hm).Prem i K.toKLayoutV m
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
        P = (stSlotX st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
        AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb)) := by
      rintro P W rfl
      exact avoidE_liftAtV_rJ hK.base _ W (st_avoidPX_path st ar hA hm i K m hK hU hp)
    exact key _ _ (SlotU.fam_pos _ _ hp)
  · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)

/-- **The `TCB_SetTimer` slot under `ownP`**: lifted, restricted to `QPs` states, PTE-cut. -/
def stSlotPX : PathsP (StArg S) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (st_avoidPX st ar hA hm i K m hK hU)

/-- **The `TCB_SetTimer` record without the bundle's fields**: the core-set convention and `kd` [P]. -/
structure StPremX5 (i : StArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- Index convention (as `VxIx.hCs`). -/
  hCs : i.Cs = {c : U64 | c.val < K.ncores}
  /-- [P] (U1's `StPremW3B.kd`). -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s

variable {st}

theorem StPremX5.toX {K : KLayoutP} {i : StArg S} {m : U64 → U64} (h : StPremX5 st i K.toKLayoutV m)
    (E : VtxBundle4 st L K) : StPremX st i K.toKLayoutV m :=
  ⟨E.b.ul, E.b.vh, E.b.vsl, E.ko, h.hCs, h.kd⟩

variable (st)

/-- **The `TCB_SetTimer` slot's start fact in a VM epoch** (module docstring): the record, a start state with
P1's `StEnt` at the layout and `QPs` ([S] entry), its core, locks and memory link ([P], as `GlueAt`), the armed
program the cut of the lifted slot's body there. -/
def StStartX (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : StArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ q0, (∃ h : StPremX5 st j K.toKLayoutV m, ∃ (σ : S) (a : A),
      (StEnt K.toKLayout st K.heap.tcbs j.Cs j.Ω K.heap j.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits
          j.Ac j.target σ ∧ QPs K st σ) ∧
      L.cpu σ = c ∧ j.lk σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
      ∀ E : VtxBundle4 st L K,
        q0 = (LocalPath.liftV hK.base (LocalPath.atV hK.base
          ((stSlotX st ar hA hm).path j K.toKLayoutV m hK.base hU.base (h.toX E))
          ((stSlotX st ar hA hm).W _ _ _ _ _ _)) (noVcpuRd_atV hK.base _ _)).body σ a) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {st ar hA hm}

/-- **`StartAt` of the `TCB_SetTimer` slot** from its start fact and the epoch's bundle (`StEnt` moved to `userV K`
by `stEnt_userV`; the memory link off the smaller user set). -/
theorem stStartX_at {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : StArg S} (E : VtxBundle4 st L K) (h : StStartX st ar hA hm K μ hK hU c hs q j) :
    StartAt (stSlotPX st ar hA hm j K μ hK hU) c hs μ q := by
  obtain ⟨-, q0, ⟨hp, σ, a, ⟨hE, hq⟩, hc, hl, hμ, hb⟩, rfl⟩ := h
  have h0 := hE.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.heap.tcbs σ (L.cpu σ) := h0.nodes _ h0.cur
  have hk : L.ksb σ = K.ksb := ksb_of_stLay hE.lay hN
  have hpre : StEntV K.toKLayoutV st j.Cs j.Ω j.Sg j.Ac j.target μ σ :=
    ⟨stEnt_userV hK.base (vcpuKs_ofKo E.ko) (ksb_fit_of_np hN hk) hk hE,
      fun x hx hxu => hμ x hx fun hu => hxu (Or.inl hu)⟩
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) μ) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P)
      (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb))),
      P = (stSlotX st ar hA hm).path j K.toKLayoutV μ hK.base hU.base (hp.toX E) →
      StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv) c hs μ
        (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c q0 ∅) := by
    rintro P W hAv rfl
    have e : q0 = (LocalPath.liftV hK.base (LocalPath.atV hK.base
        ((stSlotX st ar hA hm).path j K.toKLayoutV μ hK.base hU.base (hp.toX E)) W)
        (noVcpuRd_atV hK.base _ W)).body σ a := hb E
    refine ⟨σ, a, ⟨hpre, hq⟩, hc, hl, hμ, ?_⟩
    rw [body_cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv σ a, e, ← hc]
    rfl
  exact key _ _ _ (SlotU.fam_pos _ _ (hp.toX E))

end stS

/-! ## Part 5: the I/O-port start fact with `IoPremX5` -/

section ioSt
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The I/O-port slot's start fact in a VM epoch, record `IoPremX5`** (VX4's `IoStartX` with the record's `iw`
/ `qf` derived): the record, a start state with P1's `IoPre`, the caller's `Q` and `QPs` ([S] entry), `GlueAt`
data [P], the armed program the cut of the lifted slot's body. -/
def IoStartX5 (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : IoArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ q0, (∃ h : IoPremX5 st j K.toKLayoutV m, ∃ (σ : S) (a : A),
      (IoPre st K.toKLayout K.heap.tcbs j.Cs j.Ω K.heap j.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits
          j.Ac σ ∧ j.Q K.toKLayoutV m σ ∧ QPs K st σ) ∧
      L.cpu σ = c ∧ j.Locks σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
      ∀ E : VtxBundle4 st L K,
        q0 = (LocalPath.liftV hK.base (LocalPath.atV hK.base
          ((ioSlotX st ar hA hm).path j K.toKLayoutV m hK.base hU.base ((h.toX2 hK.base E).toX E))
          ((ioSlotX st ar hA hm).W _ _ _ _ _ _)) (noVcpuRd_atV hK.base _ _)).body σ a) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {st ar hA hm}

/-- **`IoStartX5` and the epoch's bundle give VX4's `IoStartX`** (`IoPremX5.toX2`). -/
theorem ioStartX_of_X5 {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : IoArg S} (E : VtxBundle4 st L K) (h : IoStartX5 st ar hA hm K μ hK hU c hs q j) :
    IoStartX st ar hA hm K μ hK hU c hs q j := by
  obtain ⟨hne, q0, ⟨hp, σ, a, he, hc, hl, hμ, hb⟩, rfl⟩ := h
  exact ⟨hne, q0, ⟨hp.toX2 hK.base E, σ, a, he, hc, hl, hμ, fun E' => hb E'⟩, rfl⟩

end ioSt

/-! ## Part 6a: the timer interrupt at any layout -/

section irqF
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}

/-- **The timer interrupt's state facts in a VM epoch** (module docstring): P1's entry facts at `userV K` with the
store agreeing with `m` off `userV K`'s user words (`IrqEntM`, as `IrqPreV.entM` produces), and an IPC-buffer
placement (`BufAt`, as `SlotJC.bufAt`); no P3 bundle. -/
structure IrqFx (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (Ω Ac : Set U64) (irq : U64)
    (m : U64 → U64) (s : S) : Prop where
  ent : IrqEntM (userV K) st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
    (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq m s
  buf : ∃ U : Set U64, BufAt st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} K.heap (Heap.frame K.heap)
    (Heap.scs K.heap) (Heap.scBits K.heap) U s

/-- **The timer interrupt path's `Pre` in VM epochs** (`IrqPreV` without `SlJAt`). -/
abbrev IrqPreX (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (irq : U64) (m : U64 → U64) (s : S) :
    Prop :=
  ∃ Ω Ac : Set U64, IrqFx K st Ω Ac irq m s

/-- `UserLayX` at `userV K` and the kernel base at an `IrqFx` state. -/
theorem irqFx_ul (ul : UserLayX L K.toKLayout) (hK : RegionOKV K) (vh : VcpuHeap K) (ko : VcpuKsOff K)
    (vsl : ∀ p ∈ K.slots, ∀ b, InW p 32 b → ¬ ∃ v, InVcpu K v b) {Ω Ac : Set U64} {irq : U64} {m : U64 → U64}
    {s : S} (h : IrqFx K st Ω Ac irq m s) : UserLayX L (userV K) ∧ L.ksb s = K.ksb := by
  have h0 := h.ent.ent.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.heap.tcbs s (L.cpu s) := h0.nodes _ h0.cur
  have hk : L.ksb s = K.ksb := ksb_of_stLay (Kl := userV K) h.ent.ent.lay hN
  exact ⟨userLayX_userV ul hK vh ko vsl (ksb_fit_of_np hN hk), hk⟩

/-- **`IrqLay` across a user-word write** (the table and pool words it reads are no user words, its own `tabU`;
the current thread by the node word). -/
theorem irqLay_wrL {Kl : KLayout} {Nt : Set U64} {irq : U64} {X : S}
    (hnd : NU Kl (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD)) (h : IrqLay Kl st Nt irq X) {b : U64}
    (hb : b ∈ Kl.user) (hba : Aligned b) (v : U64) : IrqLay Kl st Nt irq (L.wr X b v) := by
  have ecur : L.curW (L.wr X b v) = L.curW X := by
    unfold LawfulStore.curW
    rw [nodeAt_wr, L.cpu_wr]
    exact wr_nu hba hb v hnd
  have ekr : krA (L := L) (L.wr X b v) = krA (L := L) X := by unfold krA; rw [L.ksb_wr]
  have eA : ∀ hi : U64, hi.val < 2048 → L.mem (L.wr X b v) (atAF (L.ksb X) hi) = L.mem X (atAF (L.ksb X) hi) :=
    fun hi hhi => wr_nu hba hb v ⟨(h.tab hi hhi).1.1, (h.tabU hi hhi).1⟩
  refine ⟨?_, ?_, fun hi hhi => ?_, h.ntw, ?_, ?_, ?_, fun hi hhi => ?_⟩
  · rw [L.ksb_wr]; exact h.iq
  · rw [ekr]; exact h.kr
  · rw [L.ksb_wr, eA hi hhi]; exact h.tab hi hhi
  · rw [ecur]; exact h.cs
  · rw [L.ksb_wr]; exact h.iqU
  · rw [ekr]; exact h.krU
  · rw [L.ksb_wr, eA hi hhi]; exact h.tabU hi hhi

/-- **The timer interrupt's state facts across a write of a `userV K` user word** (`BXI` by `bxi_userX` at
`userV K`; `StLay` by `stLay_wrU`; `IrqLay` by `irqLay_wrL`; `AsidOff` by `asidOff_agN` (table words `NU`, from
`IrqLay`); `aff` by TCB / SC words; the memory link off user words; `BufAt` by TCB words, as `vtFx_wr`). -/
theorem irqFx_wr (U : UserLayX L (userV K)) {Ω Ac : Set U64} {irq : U64} {m : U64 → U64} {X : S}
    (h : IrqFx K st Ω Ac irq m X) (hk : L.ksb X = K.ksb) {b : U64} (hb : b ∈ (userV K).user) (hba : Aligned b)
    (v : U64) : IrqFx K st Ω Ac irq m (L.wr X b v) := by
  have hX := U.rx
  have E := h.ent.ent
  have h0 := E.inv.1.choose_spec.choose_spec
  have hT : TcbPlaced K.heap.tcbs := h0.tcbs
  have hN : NodePlaced st K.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have hCs : ∀ c ∈ ({c : U64 | c.val < K.ncores} : Set U64), c.val < 64 :=
    fun c hc => Nat.lt_of_lt_of_le hc U.nc
  have G : Ag st (NU (userV K)) X (L.wr X b v) :=
    ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb v hx⟩
  have hnd : NU (userV K) (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD) :=
    ⟨nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val]), E.lay.nu_node (by rw [curth_val]; omega)⟩
  have tw : ∀ y, K.heap y = some .tcb → ∀ o : U64, o.val < 4096 → o.val % 8 = 0 →
      L.mem (L.wr X b v) (core.num.U64.wrapping_add y o) = L.mem X (core.num.U64.wrapping_add y o) :=
    fun y hy o h1 h2 => wr_nu hba hb v ⟨field_aligned (hT y hy) h1 h2, fun hu => U.userObj hu hy
      (fun z e => by cases e) (by unfold InW; rw [field_val (hT y hy) h1]; simp only [HKind.bits]; omega)⟩
  have hna : ∀ hi : U64, hi.val < 2048 → NU (userV K) (atAF (L.ksb X) hi) :=
    fun hi hhi => ⟨(E.ly.tab hi hhi).1.1, (E.ly.tabU hi hhi).1⟩
  have hB := bxi_userX U hk hCs E.inv G
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := E.inv
  refine ⟨⟨⟨hB, stLay_wrU E.lay b v, irqLay_wrL hnd E.ly hb hba v, asidOff_agN hna G E.asid, ?_, E.nth⟩,
    fun x hx hxu => by rw [mem_wr_ne' hba hx (fun e => hxu (e ▸ hb))]; exact h.ent.mem x hx hxu⟩, ?_⟩
  · intro t ht h1
    have es : L.mem (L.wr X b v) (scA t) = L.mem X (scA t) :=
      wr_nu hba hb v (nu_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [es] at h1 ⊢
    have hsc := (hXI.2.2.bound t ht h1).1
    have ec : L.mem (L.wr X b v) (scCoreA (L.mem X (scA t))) = L.mem X (scCoreA (L.mem X (scA t))) :=
      wr_nu hba hb v (nu_scw hX (scs_heap hsc) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    have ea : L.mem (L.wr X b v) (affA t) = L.mem X (affA t) :=
      wr_nu hba hb v (nu_tcb hX ht (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ec, ea]; exact E.aff t ht h1
  · obtain ⟨Ub, hB1, hB2⟩ := h.buf
    refine ⟨Ub, fun c hc => (hB1 c hc).ksb (L.ksb_wr _ _ _), fun y hy => ?_⟩
    have ht := hT y hy
    have e1 : L.mem (L.wr X b v) (ibA y) = L.mem X (ibA y) := tw y hy 3512#u64 (by simp) (by simp)
    have e2 : L.mem (L.wr X b v) (sbA y) = L.mem X (sbA y) := by
      rw [sbA_field ht]; exact tw y hy 64#u64 (by simp) (by simp)
    have e3 : L.mem (L.wr X b v) (core.num.U64.wrapping_add (sbA y) 8#u64) =
        L.mem X (core.num.U64.wrapping_add (sbA y) 8#u64) := by
      rw [sbA8_field ht]; exact tw y hy 72#u64 (by simp) (by simp)
    rw [lookup_buf_agree e1 e2 e3]
    exact hB2 y hy

end irqF

section irqP
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}

variable (st) in
/-- **The timer interrupt's record at any layout** (module docstring): the epoch's layout facts, `lt`, and U1's
two [P]s (`kd` asked at entry states instead of bundle states, `pl`). -/
structure IrqPremX (i : IrqArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- The user-word layout facts (from the epoch's `VtxBundle`). -/
  ul : UserLayX L K.toKLayout
  /-- `VcpuHeap` (from the epoch's `VtxBundle`). -/
  vh : VcpuHeap K
  /-- No VCPU word in a CNode slot (from the epoch's `VtxBundle`). -/
  vsl : ∀ p ∈ K.slots, ∀ b, InW p 32 b → ¬ ∃ v, InVcpu K v b
  /-- No VCPU meets the kernel-global area (from the epoch's `VtxBundle4`). -/
  ko : VcpuKsOff K
  /-- The IRQ's state word lies in the kernel-state block (the timer IRQ is 2; U1's `IrqPremK2B.lt`). -/
  lt : i.irq.val < 128
  /-- [P] at the interrupt's entry states the locks are determined by the words off `(userV K).user` (U1's
  `IrqPremK2B.kd`, "bundle states" read as "entry states": no `m`). -/
  kd : ∀ s, (∃ Ω Ac : Set U64, IrqEnt (userV K) st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap
    (Heap.frame K.heap) (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac i.irq s) →
    KernDetS (L := L) (userV K).user i.lk s
  /-- [P] (U1's `IrqPremK2B.pl`). -/
  pl : PlanLk i.lk i.pl

/-- **`PathObl` of the timer interrupt at one VM-epoch entry state** (`irq_pathObl_V`'s proof; `ObjLay` and
`SlotLayV` from `UserLayX`, `BufAt` from the state). -/
theorem irq_pathOblX (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) {i : IrqArg S} {K : KLayoutV} {m : U64 → U64}
    (hKV : RegionOKV K) (hUV : UserOKV K) (h : IrqPremX st i K m) {s0 : S} (h0 : IrqPreX K st i.irq m s0) :
    PathObl.PathObl st (fun mm s a => localtimer.handle_timer_irq_local mm ar s a i.irq i.pl) (fun b => b = true)
      (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user) i.lk
      (fun s => s = s0) (MaxR (userV K) st i.lk) (MaxW (userV K) st i.lk) (IrqDec st) := by
  have hK := regionOK_userV hKV
  have hUO := userOK_userV hKV hUV
  obtain ⟨Ω, Ac, hF⟩ := h0
  have hE := hF.ent
  have hOL : ObjLay (userV K) K.heap (Heap.replies K.heap) := objLay_of_layP h.ul.lp (fun r hr => hr)
  have hSL : SlotLayV (userV K) st (Heap.tcbs K.heap) s0 := slotLayV_ofLayX h.ul (fun y hy => hy) s0
  have hp := irq_isProg S i.irq i.pl
  refine irq_pathObl ar hA hK hUO (P := fun s => s = s0) (fun s e => by subst e; exact hE.ent)
    (fun mm => hp A ar mm) (irq_noZero i.irq i.pl) hm (fun s e q hq => by subst e; exact irq_koF hE.ent hq)
    (Fl4Proofs.P2.ko_aligned hK hUO) ?_ ?_
  · rintro s a s1 a1 rfl hf h'
    by_cases hnw : NoWake st s
    · exact irq_acc_fire_nw ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth hf hnw h'
    · obtain ⟨Ub, hB⟩ := hF.buf
      exact irq_acc_fire_wk2 ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth
        hOL h.pl (irq_bufAt_runB ar hA hE.ent.inv hB hf h') hSL hf hnw h'
  · rintro s a s1 a1 rfl h'
    refine irq_move_acc ar hA hK hUO hp hE.k (fun hf => ?_) h'
    by_cases hnw : NoWake st s
    · exact irq_move_fire_nw ar hA hK hUO hp hE.k hE.ent.ly hE.ent.nth hf hnw h'
    · obtain ⟨Ub, hB⟩ := hF.buf
      exact irq_move_fire_wk2 ar hA hK hUO hp hE.k hE.ent.ly hE.ent.aff hE.ent.nth
        hOL h.pl (irq_bufAt_runB ar hA hE.ent.inv hB hf h') hf hnw h'

/-- **`PathSide` of the timer interrupt under `IrqPreX`** (`irq_pathSide_V`'s proof; `user_free` by `irqFx_wr`,
the locks by `kd` at the entry state). -/
theorem irq_pathSideX (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) {i : IrqArg S} {K : KLayoutV} {m : U64 → U64}
    (hKV : RegionOKV K) (hUV : UserOKV K) (h : IrqPremX st i K m) :
    PathObl.PathSide st (fun mm s a => localtimer.handle_timer_irq_local mm ar s a i.irq i.pl) (OwnMap.cls (userV K))
      (OwnMap.ko (userV K) m) (· ∈ (userV K).user) i.lk (IrqPreX K st i.irq m) (MaxR (userV K) st i.lk)
      (MaxW (userV K) st i.lk) (IrqDec st) := by
  have hK := regionOK_userV hKV
  have hUO := userOK_userV hKV hUV
  have hp := irq_isProg S i.irq i.pl
  have hz := irq_noZero i.irq i.pl
  refine ⟨?_, fun s x _ hx => hx.2.1, Fl4Proofs.P2.ko_aligned hK hUO, ?_⟩
  · intro s s' a r hP hAlt h'
    obtain ⟨Ω, Ac, hF⟩ := hP
    have O := irq_pathOblX hA hm hKV hUV h ⟨Ω, Ac, hF⟩
    have eP : ∀ (mm : machine.Store S) (x : S),
        localtimer.handle_timer_irq_local mm ar x a i.irq i.pl =
          interp mm ar (R.localtimer.handle_timer_irq_local i.irq i.pl) x a :=
      fun mm x => congrFun (congrFun (hp A ar mm) x) a
    rcases irq_alt ar hA hK (fun mm => hp A ar mm) hz hm hF.ent.ent
      (fun s1 a1 _ h1 => O.acc s a (true, s1, a1) rfl h1 rfl) hAlt h' with ⟨_, _, -, -, h2⟩ | ⟨_, _, -, -, h2⟩
    · show localtimer.handle_timer_irq_local _ ar s' a i.irq i.pl = ok r
      rw [eP] at h2 ⊢
      exact interp_mono (fun _ hw => hw.2.1) (fun _ _ => trivial) _ hz s' a r h2
    · show localtimer.handle_timer_irq_local _ ar s' a i.irq i.pl = ok r
      rw [eP] at h2 ⊢
      exact interp_mono (fun _ hw => hw) (fun _ _ => trivial) _ hz s' a r h2
  · intro s b v hP hb hba
    obtain ⟨Ω, Ac, hF⟩ := hP
    obtain ⟨U, hk⟩ := irqFx_ul h.ul hKV h.vh h.ko h.vsl hF
    have keep : ∀ x, Aligned x → x ∉ (userV K).user → L.mem (L.wr s b v) x = L.mem s x :=
      fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb))
    have eo : OwnMap.own (userV K) (L.mem (L.wr s b v)) = OwnMap.own (userV K) (L.mem s) :=
      E2E.ownDep hK hUO _ _ (fun x hx hxu => keep x hx hxu)
    have hl : i.lk (L.wr s b v) = i.lk s := hlk_of_kernelDetU h.kd s b v ⟨Ω, Ac, hF.ent.ent⟩ hb hba
    refine ⟨⟨Ω, Ac, irqFx_wr U hF hk hb hba v⟩, hl, ?_, ?_, irq_dec_user s b v⟩
    · funext w; simp only [MaxR, RPerm, GateOnly, eo, hl, L.cpu_wr]
    · funext w; simp only [MaxW, WPerm, eo, hl, L.cpu_wr]

/-- **`ReadOnce` of the timer interrupt tree under `IrqPreX`** (`irq_hroV`'s proof). -/
theorem irq_hroX (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) {i : IrqArg S} {K : KLayoutV} {m : U64 → U64}
    (hKV : RegionOKV K) (hUV : UserOKV K) (h : IrqPremX st i K m) :
    E2E.ReadOnce st ar (R.localtimer.handle_timer_irq_local i.irq i.pl) (OwnMap.cls (userV K))
      (OwnMap.ko (userV K) m) (· ∈ (userV K).user) (IrqPreX K st i.irq m) (MaxR (userV K) st i.lk) := by
  intro s s' a _ hP hAlt _
  obtain ⟨Ω, Ac, hF⟩ := hP
  have O := irq_pathOblX hA hm hKV hUV h ⟨Ω, Ac, hF⟩
  exact irq_once_alt ar hA (regionOK_userV hKV) hm hF.ent.ent
    (fun s1 a1 _ h1 => O.acc s a (true, s1, a1) rfl h1 rfl) hAlt

/-- **The timer interrupt local path at `userV K` with `Pre := IrqPreX`** (`irq_localPathV` without `VFacts` and
`SlJAt`). -/
noncomputable def irq_localPathX (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) {i : IrqArg S} {K : KLayoutV}
    {m : U64 → U64} (hKV : RegionOKV K) (hUV : UserOKV K) (h : IrqPremX st i K m) :
    E2E.LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user) :=
  { S := S
    A := A
    X := Bool
    st := st
    L := L
    ar := ar
    F := irqBody S i.irq i.pl
    p := R.localtimer.handle_timer_irq_local i.irq i.pl
    Acc := fun b => b = true
    Locks := i.lk
    Pre := IrqPreX K st i.irq m
    RS := MaxR (userV K) st i.lk
    WS := MaxW (userV K) st i.lk
    DS := IrqDec st
    isProg := PathObl.IsProg.on (irq_isProg S i.irq i.pl) _ _ _
    obl := irq_obl_of_pt fun _ h0 => irq_pathOblX hA hm hKV hUV h h0
    side := irq_pathSideX hA hm hKV hUV h
    once := irq_hroX hA hm hKV hUV h
    total := fun s a => by
      obtain ⟨r, e, -⟩ :=
        spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar s a i.irq i.pl LawfulStore.total hA)
      exact ⟨r, e⟩
    masks := hm }

end irqP

section irqS
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The timer interrupt slot at any layout** (route U, `Pre := IrqPreX`). -/
def irqSlotX : SlotU (IrqArg S) where
  Prem i K m := IrqPremX st i K m
  path i K m hK hU h := irq_localPathX hA hm hK hU h
  W i K m hK hU h :=
    ⟨fun _ _ _ hr => maxR_noV hr, fun s _ hp hw => hw.elim (maxW_noV hK) fun hd => by
      obtain ⟨Ω, Ac, hF⟩ := (hp : IrqPreX K st i.irq m s)
      exact Or.inl (irqDec_noV hK hF.ent.ent hd)⟩

/-- **The timer interrupt path at any layout reads no PTE word under `QPs`** (`irq_avoidPJ_path`'s proof with
`Pre := IrqPreX`; it never used `vcpus = ∅`). -/
theorem irq_avoidPX_path (i : IrqArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (irqSlotX st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((irqSlotX st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
  have hP : IrqPremX st i K.toKLayoutV m := h
  have hKr := regionOK_userP hK.base
  have facts : ∀ s, IrqPreX K.toKLayoutV st i.irq m s → QPs K st s →
      ∃ Ω Ac : Set U64, IrqEnt (userP K) st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap
        (Heap.frame K.heap) (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac
        i.irq s := by
    intro s hs hq
    obtain ⟨Ω, Ac, hF⟩ := hs
    exact ⟨Ω, Ac, irqEnt_userP hK hF.ent.ent (fun hb j hj => hq.ksw (state_off_lt hb hj))
      (hq.ksw (by simp [layout.ks.KERNEL_ROOT])) hq.tab
      (hq.ksw (by simp [layout.ks.CUR_DOMAIN]))
      (hq.ksw (by simp [layout.ks.DOMAIN_TIME]))⟩
  refine avoidE_of_entry (P := ((irqSlotX st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K
      (fun b hb => hb))
    (E := (· ∈ K.ptes)) (irq_noZero i.irq i.pl) (IsProg.on (irq_isProg S i.irq i.pl) _ _ _)
    (fun s => MaxR (L := L) (userP K) st i.lk s) (fun s => MaxW (L := L) (userP K) st i.lk s)
    (fun s x _ hx hp => hx.2.2 (Or.inr hp)) ?_
    (fun s => MaxR (L := L) (userP K) st i.lk s) (fun s => IrqDec (L := L) st s)
    (fun s x _ hx => ⟨hx.2.1, ⟨hx.1, hx.2.1, fun hu => hx.2.2 (Or.inl hu)⟩, fun hp => hx.2.2 (Or.inr hp)⟩)
    (fun s x hs hx => by
      obtain ⟨hs1, hs2⟩ := hs
      obtain ⟨Ω, Ac, hE⟩ := facts s hs1 hs2
      exact (hE.dec hx).1) ?_
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : IrqPreX K.toKLayoutV st i.irq m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localtimer.handle_timer_irq_local st ar s a i.irq i.pl = ok (true, s1, a1) := hr
    obtain ⟨Ω, Ac, hE⟩ := facts s hs' hq
    have hEK : IrqEntK (userP K) st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac (L.mem s) s :=
      ⟨hE.inv, hE.lay, fun _ _ _ => rfl, hE.asid⟩
    obtain ⟨Ω', Ac', hF⟩ := hs'
    have hOL : ObjLay (userP K) K.heap (Heap.replies K.heap) := objLay_of_layP hP.ul.lp (fun r hr => hr)
    have hSL : SlotLayV (userP K) st (Heap.tcbs K.heap) s := slotLayV_ofLayX hP.ul (fun y hy => hy) s
    have g : localtimer.handle_timer_irq_local (guard st (MaxR (userP K) st i.lk s) (MaxW (userP K) st i.lk s))
        ar s a i.irq i.pl = ok (true, s1, a1) :=
      irq_acc_own ar hA hKr hEK hE.ly hE.aff (fun hf => by
        by_cases hnw : NoWake st s
        · exact irq_acc_fire_nw ar hA hKr hEK hE.ly hE.aff hE.nth hf hnw hr'
        · obtain ⟨U, hB⟩ := hF.buf
          exact irq_acc_fire_wk2 ar hA hKr hEK hE.ly hE.aff hE.nth hOL hP.pl
            (irq_bufAt_runB ar hA hE.inv hB hf hr') hSL hf hnw hr') hr'
    exact g
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : IrqPreX K.toKLayoutV st i.irq m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    cases b
    · have hr' : localtimer.handle_timer_irq_local st ar s a i.irq i.pl = ok (false, s1, a1) := hr
      obtain ⟨Ω, Ac, hE⟩ := facts s hs' hq
      have g : localtimer.handle_timer_irq_local (guard st (MaxR (userP K) st i.lk s) (IrqDec st s))
          ar s a i.irq i.pl = ok (false, s1, a1) :=
        irq_dec_guard ar hA hKr hE.inv hE.lay hE.ly hE.aff hE.nth hr'
      exact g
    · exact absurd rfl hb

/-- **The timer interrupt slot's family member reads no PTE word under `QPs`.** -/
theorem irq_avoidPX (i : IrqArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) :
    AvoidP K (((irqSlotX st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  by_cases hp : (irqSlotX st ar hA hm).Prem i K.toKLayoutV m
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
        P = (irqSlotX st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
        AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb)) := by
      rintro P W rfl
      exact avoidE_liftAtV_rJ hK.base _ W (irq_avoidPX_path st ar hA hm i K m hK hU hp)
    exact key _ _ (SlotU.fam_pos _ _ hp)
  · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)

/-- **The timer interrupt slot under `ownP`**: lifted, restricted to `QPs` states, PTE-cut. -/
def irqSlotPX : PathsP (IrqArg S) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (irq_avoidPX st ar hA hm i K m hK hU)

/-- **The timer interrupt record without the bundle's fields**: `lt`, `kd` [P], `pl` [P]. -/
structure IrqPremX5 (i : IrqArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- The timer IRQ's state word lies in the kernel-state block (U1's `lt`). -/
  lt : i.irq.val < 128
  /-- [P] (as `IrqPremX.kd`). -/
  kd : ∀ s, (∃ Ω Ac : Set U64, IrqEnt (userV K) st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap
    (Heap.frame K.heap) (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac i.irq s) →
    KernDetS (L := L) (userV K).user i.lk s
  /-- [P] -/
  pl : PlanLk i.lk i.pl

variable {st}

theorem IrqPremX5.toX {K : KLayoutP} {i : IrqArg S} {m : U64 → U64} (h : IrqPremX5 st i K.toKLayoutV m)
    (E : VtxBundle4 st L K) : IrqPremX st i K.toKLayoutV m :=
  ⟨E.b.ul, E.b.vh, E.b.vsl, E.ko, h.lt, h.kd, h.pl⟩

variable (st)

/-- **The timer interrupt slot's start fact in a VM epoch** (module docstring): the record, a start state with
P1's `IrqEnt` at `userV K`, a `BufAt` placement and `QPs` ([S] entry), `GlueAt` data [P], the armed program the cut
of the lifted slot's body there. -/
def IrqStartX (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : IrqArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ q0, (∃ h : IrqPremX5 st j K.toKLayoutV m, ∃ (σ : S) (a : A),
      ((∃ Ω Ac : Set U64, IrqEnt (userV K.toKLayoutV) st (Heap.tcbs K.heap) {x : U64 | x.val < K.ncores} Ω K.heap
          (Heap.frame K.heap) (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac
          j.irq σ) ∧
        (∃ U : Set U64, BufAt st (Heap.tcbs K.heap) {x : U64 | x.val < K.ncores} K.heap (Heap.frame K.heap)
          (Heap.scs K.heap) (Heap.scBits K.heap) U σ) ∧ QPs K st σ) ∧
      L.cpu σ = c ∧ j.lk σ = hs ∧ (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
      ∀ E : VtxBundle4 st L K,
        q0 = (LocalPath.liftV hK.base (LocalPath.atV hK.base
          ((irqSlotX st ar hA hm).path j K.toKLayoutV m hK.base hU.base (h.toX E))
          ((irqSlotX st ar hA hm).W _ _ _ _ _ _)) (noVcpuRd_atV hK.base _ _)).body σ a) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {st ar hA hm}

/-- **`StartAt` of the timer interrupt slot** from its start fact and the epoch's bundle. -/
theorem irqStartX_at {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : IrqArg S} (E : VtxBundle4 st L K) (h : IrqStartX st ar hA hm K μ hK hU c hs q j) :
    StartAt (irqSlotPX st ar hA hm j K μ hK hU) c hs μ q := by
  obtain ⟨-, q0, ⟨hp, σ, a, ⟨⟨Ω, Ac, hE⟩, hB, hq⟩, hc, hl, hμ, hb⟩, rfl⟩ := h
  have hpre : IrqPreX K.toKLayoutV st j.irq μ σ :=
    ⟨Ω, Ac, ⟨hE, fun x hx hxu => hμ x hx fun hu => hxu (Or.inl hu)⟩, hB⟩
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) μ) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P)
      (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb))),
      P = (irqSlotX st ar hA hm).path j K.toKLayoutV μ hK.base hU.base (hp.toX E) →
      StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv) c hs μ
        (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c q0 ∅) := by
    rintro P W hAv rfl
    have e : q0 = (LocalPath.liftV hK.base (LocalPath.atV hK.base
        ((irqSlotX st ar hA hm).path j K.toKLayoutV μ hK.base hU.base (hp.toX E)) W)
        (noVcpuRd_atV hK.base _ W)).body σ a := hb E
    refine ⟨σ, a, ⟨hpre, hq⟩, hc, hl, hμ, ?_⟩
    rw [body_cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv σ a, e, ← hc]
    rfl
  exact key _ _ _ (SlotU.fam_pos _ _ (hp.toX E))

end irqS

/-! ## Part 6: the tops -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The start facts with the VM-exit, VM-timer, I/O-port and `TCB_SetTimer` slots in VM epochs** (VX4's, the
I/O-port slot at `IoStartX5`, the `TCB_SetTimer` slot at `StStartX`). -/
def StartVX5 {ιN : Type}
    (SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : ((((ιN ⊕ VxArg S) ⊕ VtArg S) ⊕ IoArg S) ⊕ StArg S) ⊕ IrqArg S → Prop
  | .inl (.inl (.inl (.inl i))) => StartVX2 st ar hA hm SFN Ch K m hK hU c hs q i
  | .inl (.inl (.inl (.inr j))) => VtStartV4 st ar hA hm K m hK hU c hs q j
  | .inl (.inl (.inr j)) => IoStartX5 st ar hA hm K m hK hU c hs q j
  | .inl (.inr j) => StStartX st ar hA hm K m hK hU c hs q j
  | .inr j => IrqStartX st ar hA hm K m hK hU c hs q j

/-- **FL4 end to end with native and VM epochs; the VM-exit, VM-timer, I/O-port and `TCB_SetTimer` slots in VM
epochs; generic in the native family** (`serializable_fl4_localVX4G` with `stSlotPX` added). -/
theorem serializable_fl4_localVX5G (P : LocPlat st arI AR MR) {ιN : Type} (LN : PathsP ιN)
    {SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop}
    (hSFN : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SFN Ch K s.mem hK hU c hs q i → StartAt (LN i K s.mem hK hU) c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4 (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum LN (vxSlotPV st ar hA hm))
        (vtSlotPV st ar hA hm)) (ioSlotPX st ar hA hm)) (stSlotPX st ar hA hm)) (irqSlotPX st ar hA hm))
      (StartVX5 st ar hA hm SFN) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  have hX := (execVX_of_VX4 hc0.1 h).1
  refine serializable_e2eP _ h0 hA0 hK0 hU0 hM0 (execP_of_VX P ?_ h0 hA0 hB hc0 hM0 hX).1 hq
  intro Ch K s hK hU c hs q i hN hsf
  obtain ⟨hV, hsf⟩ := hsf
  rcases i with ((((i | j) | j) | j) | j) | j
  · have hsf' : K.vcpus = ∅ ∧ SFN Ch K s.mem hK hU c hs q i := hsf
    obtain ⟨nv, hsf'⟩ := hsf'
    obtain ⟨hX, hE⟩ := hN nv
    exact hSFN Ch K s hK hU c hs q i hX.chainOf hE hsf'
  · have hsf' : VxStartV2 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vxStartV_at st ar hA hm (vxStartV_of_V2 (hV (vxStartV2_ne hsf')).b hsf')
  · have hsf' : VtStartV4 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vtStartV2_at (hV hsf'.1).b (vtStartV2_of_V4 (hV hsf'.1).b hsf')
  · have hsf' : IoStartX5 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact ioStartX_at (hV hsf'.1) (ioStartX_of_X5 (hV hsf'.1) hsf')
  · have hsf' : StStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact stStartX_at (hV hsf'.1) hsf'
  · have hsf' : IrqStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact irqStartX_at (hV hsf'.1) hsf'

end top

end
end Fl4Proofs.P2.E2EP

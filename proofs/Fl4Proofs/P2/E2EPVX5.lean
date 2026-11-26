/-
# P2 (line vmscope, gen 5): the VM-epoch I/O-port slot without [J] — `serializable_fl4_localVX5`

(module docstring: see the end of the gen-5 work, below the imports' summary.)
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
    (hs : U64 → Prop) (q : SP) : (((ιN ⊕ VxArg S) ⊕ VtArg S) ⊕ IoArg S) ⊕ StArg S → Prop
  | .inl (.inl (.inl i)) => StartVX2 st ar hA hm SFN Ch K m hK hU c hs q i
  | .inl (.inl (.inr j)) => VtStartV4 st ar hA hm K m hK hU c hs q j
  | .inl (.inr j) => IoStartX5 st ar hA hm K m hK hU c hs q j
  | .inr j => StStartX st ar hA hm K m hK hU c hs q j

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
    (h : ExecVX4 (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum LN (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm))
        (ioSlotPX st ar hA hm)) (stSlotPX st ar hA hm))
      (StartVX5 st ar hA hm SFN) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  have hX := (execVX_of_VX4 hc0.1 h).1
  refine serializable_e2eP _ h0 hA0 hK0 hU0 hM0 (execP_of_VX P ?_ h0 hA0 hB hc0 hM0 hX).1 hq
  intro Ch K s hK hU c hs q i hN hsf
  obtain ⟨hV, hsf⟩ := hsf
  rcases i with (((i | j) | j) | j) | j
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

/-- **FL4 end to end with every U1 slot in native epochs and the VM-exit, VM-timer, I/O-port and `TCB_SetTimer`
slots in VM epochs** (module docstring): `serializable_fl4_localVX4` with the I/O-port record's two [J]s (`iw`,
`qf`) derived (`IoPremX5`: index conventions `hQ`, `hCs`, `kd` [P]) and the `TCB_SetTimer` slot `stSlotPX` added
(record `StPremX5`: `hCs` convention, `kd` [P]; start entry `StEnt ∧ QPs` [S]). No [J] beyond U1's, no [W]. -/
theorem serializable_fl4_localVX5 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4 (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (PathsP.sum (fl4LocW11JA st ar hA hm hSt a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA hm) (invSlotU st ar hA hm)) (cmSlotU st ar hA hm)))
        (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm)) (ioSlotPX st ar hA hm)) (stSlotPX st ar hA hm))
      (StartVX5 st ar hA hm (StartU1 st ar hA hm hSt a0 arI AR MR (StartInvU2 st ar hA hm))) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_fl4_localVX5G st ar hA hm P _ ?_ h0 hA0 hB hc0 hM0 h hq
  intro Ch K s hK hU c hs q i hC hE hsf
  rcases i with i | ((j | j) | j)
  · exact startAt_U st ar hA hm hSt a0 P hIoa hC hE hsf
  · exact delPteStart_at st ar hA hm hC hE hsf
  · exact invStartU2_at st ar hA hm hC hE hsf
  · exact cmStartU2_at st ar hA hm hC hE hsf

end top

end
end Fl4Proofs.P2.E2EP

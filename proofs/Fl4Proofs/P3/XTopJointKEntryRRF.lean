/-
P3 (issue #16, m69): **`kernel_entryJ33F` / `kernel_entryJ34F`**, m66's
`kernel_entryJ33R` / `J34R` with the ReplyRecv read bundle `hRP : P1.RRPreAt`
replaced by what the P3 entry already carries plus two narrow residues:
`hRV : SInvR.RV σ` [J] at the entry's spec state (l4v `valid_refills` /
`refills_sum`; a conjunct of the readiness line's carried `SInvW`) and m67's
`nvm` read `hRP5 : P1.RRPreAt5` (kept, named).

The P1 bundle `RRPreAt` is asked at every dispatch state of the entry (the
`FAULT_IP` write, then a passing `budget_ok`). m68 derived it (`RRPreAt.of2 ∘
RRPreAt2.of5`) from the P1 entry bundles `EntryInv` / `EntryHyps0` at the P1
entry state plus `RRSumAt` [J] / `CnOffAt` [J] / `RRPreAt5`. Here every one of
these is read off the joint relation at the dispatch state instead:

* `JAtZ.rrDisp`: the dispatch state of the real run (the entry's own `NEXT_IP`
  read and `FAULT_IP` write, a passing `budget_ok`) carries `JAtZ` (with the
  entry's `H`, `Cs`), its spec state having the kheap of `faultIPSt σ` (the
  prefix of `kernel_entryJ13PUN`, `JAtZ.budgetOkB`).
* The P1 facts m68's lemmas used at the dispatch state, from that `JAtZ`:
  `BXI` (`JAtZ.blk`); the receive-side cap typing that `EntryHyps0.recvOK` gave
  (`JAtZ.lkTyped`: `lookup_cap_held` + `JPlaced.typed`); `RRSum` (`JAtZ.rrSum`:
  every sporadic SC of `H` is in `Z.C`, related by `ScRelW.strongS` with its
  refills, active by `ScRelW.active_of_rmax`, so `RV`'s `rsum < 2 ^ 64` is the
  ring sum, `amtSum_eq_lsum`); `CnOff` (`JAtZ.cnOff`: the CNode caps reachable
  from the current thread's root name CNodes of `Z.th` with their radix,
  `SlotsValid`; their indexed slots are slots of `Z.th`, so both words lie in an
  `other` object of `H`, hence in `Ω` (`OutsideObjs` by `SchedQueuesInv.omega`)
  and outside the frame words (`HeapOK.disj`)).
* `rrPre_of_lk`: m68's composition with the cap typing as an argument (P1
  `rrEnt_lk` / `rrPl_lk`, the former `rrEnt_of` / `rrPl_of` with `EntryHyps0` /
  `XG` replaced by the one fact they read).
* `RV` at the dispatch state from `RV` at the entry (`rv_faultIP`: the passing
  budget check keeps the kheap, the `FAULT_IP` write changes one TCB).
-/
import Fl4Proofs.P3.XTopJointKEntryRR
import Fl4Proofs.P1.FastRRLk
import Fl4Proofs.P3.SpecInvRd8wB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## Small facts -/

theorem sum_list_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem amtSum_eq_lsum (s : S) (c : U64) : L.amtSum s c = Sched.lsum (L.refills s c) := by
  unfold P1.LawfulStore.amtSum P1.LawfulStore.refills Sched.lsum
  rw [List.map_map]
  exact (sum_list_range _ _).symm

theorem cnSlot_eq (p o : U64) : P1.cnSlot p o = slotAddr p.bv (BitVec.ofNat 64 o.val) := by
  have h := slot_index_spec p o
  unfold obj.Slot.index at h
  simp only [lift, bind_ok, WP.spec_ok] at h
  show core.num.U64.wrapping_add p (core.num.U64.wrapping_mul o layout.cte.SIZE) = _
  rw [h, bv_eq_ofNat o]

theorem andMask_lt_pow {r m : U64} (hm : cspace.mask r = ok m) (x : U64) : (x &&& m).val < 2 ^ r.val := by
  by_cases h64 : r.val < 64
  · have hs := mask_spec r h64
    rw [hm, WP.spec_ok] at hs
    have hp : 1 ≤ 2 ^ r.val := Nat.one_le_two_pow
    rw [UScalar.val_and]
    have := Nat.and_le_right (n := x.val) (m := m.val)
    omega
  · have hx := (x &&& m).hBounds
    have : 2 ^ 64 ≤ 2 ^ r.val := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits] at hx ⊢
    omega

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

/-- m68's composition `RRPre.of2 ∘ RRPre2.of3 ∘ RRPre3.of5` at one dispatch
state, with the receive-side cap typing as an argument (P1 `rrEnt_lk` /
`rrPl_lk`) in place of `EntryHyps0` / `XG`. -/
theorem rrPre_of_lk {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : P1.Heap} {Z : U64 → Nat} {X0 : S} {a : A}
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hI : P1.BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X0)
    (hlk : ∀ cptr, cspace.lookup_cap st X0 (L.curW X0) cptr ⦃ r => ∀ c, r = .Ok c → P1.CapTyped H Rp Nt c ⦄)
    (hS : P1.RRSum (L := L) Scs X0)
    (hCn : ∀ t, sched.cur_thread st X0 = ok t → P1.CnOff (L := L) T Cs Sg X0 t)
    (h : P1.RRPre5 (L := L) arI X0 a) : P1.RRPre (L := L) arI X0 a :=
  P1.RRPre.of2 arI (T := T) (fun _ _ _ _ _ et hrc hC => P1.rrEnt_lk arI hI hlk et hrc hC)
    (P1.RRPre2.of3 arI (fun _ _ _ _ _ et hrc hC => P1.rrPl_lk arI hNt hI hlk et hrc hC) hS
      (P1.RRPre3.of5 arI (fun _ _ _ _ _ et hrc hC => P1.rrPl_lk arI hNt hI hlk et hrc hC) hS hCn h))

/-- `RV` across the entry's front to a passing budget check: the kheap is
`faultIPSt σ`'s, which differs from `σ`'s at the current thread's TCB only. -/
theorem rv_faultIP {σ σb : Fl4Spec.State Unit} {x : Fl4Spec.Tcb}
    (ekh : σb.kheap = (faultIPSt σ σ.curThread x).kheap) (h : SInvR.RV σ) : SInvR.RV σb := by
  intro p y n hp ha
  refine h p y n ?_ ha
  rw [ekh] at hp
  by_cases e : p = σ.curThread
  · subst e; simp [faultIPSt, Notif.updK] at hp
  · simpa [faultIPSt, Notif.updK, e] using hp

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- `BXI` at the P1 sets drawn from `H` (`JAtZ.blk` reordered). -/
theorem JAtZ.bxi {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    P1.BXI st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
      (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s :=
  ⟨J.blk.1, J.blk.2.1, J.blk.2.2.1, J.blk.2.2.2.2, J.blk.2.2.2.1⟩

theorem JAtZ.curW_tcb {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (et : sched.cur_thread st s = ok t) : Z.th t = some .tcb :=
  (J.xtop.curTcb (J.curEq et).1).1

theorem cur_thread_curW (s : S) : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq (L := L) s

/-- **The receive-side cap typing at a `JAtZ` state** (what P1's
`EntryHyps0.recvOK` gave): every cap the current thread looks up is in a slot
of `Z.th` (`lookup_cap_held`), typed by `JPlaced.typed`. -/
theorem JAtZ.lkTyped {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (cptr : U64) : cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c →
      P1.CapTyped H (P1.Heap.replies H) (P1.Heap.ntfns H) c ⦄ := by
  have htcb := J.curW_tcb (cur_thread_curW (L := L) s)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  refine WP.spec_mono (lookup_cap_held Z.th s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 _ htcb cptr) ?_
  intro r hr c hc
  obtain ⟨y, hy, hcv⟩ := hr c hc
  rw [← hcv]; exact hJ.typed y hy

/-- **`RRSum` at a `JAtZ` state from `RV`** (m66's bridge): a sporadic SC of
`H` is one of `Z.C` (`hscC`), related to a spec SC with its refills
(`ScRelW.strongS`), active (`ScRelW.active_of_rmax`), so `RV`'s
`rsum < 2 ^ 64` is its ring sum. -/
theorem JAtZ.rrSum {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hRV : SInvR.RV σ) : P1.RRSum (L := L) (P1.Heap.scs H) s := by
  intro c ⟨z, hz⟩ hsp
  have hcC := J.hscC c z hz
  obtain ⟨Q, R, -, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨y, n, hk, hW⟩ := hs.scs c hcC
  have hsp' : L.mem s (scW c 64#u64) ≠ 0#u64 := by
    have e : P1.sporA c = scW c 64#u64 := by unfold P1.sporA scW; simp [layout.sc.SPORADIC]
    rw [← e]; exact hsp
  have h1 := hW.strongS hsp'
  have ha := hW.active_of_rmax (hW.spor hsp')
  have hr := (hRV _ y n hk ha).2.2.1
  rw [h1.refills, SInvR.rsum_map] at hr
  rw [amtSum_eq_lsum]; exact hr

/-- The words of a CNode slot of `Z.th` are cap-slot words for P1
(`CapSW`): in `Ω` (an `other` object of `H`), so outside the TCBs and nodes,
and outside the frame words. -/
theorem JAtZ.capSW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {p : U64} {n i : Nat} (hth : Z.th p = some (.cnode n)) (hi : i < 2 ^ n) {b : U64}
    (hb : b = slotOf p i ∨ b = core.num.U64.wrapping_add (slotOf p i) 8#u64) :
    P1.CapSW (L := L) (P1.Heap.tcbs H) Cs (P1.Heap.frame H) s b := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hqi : IsSlotAt Z.th p i := Or.inl ⟨n, hth, hi⟩
  have hv := hqi.val hJ.pl
  have hal := hqi.aligned hJ.pl
  have hp := hJ.cnode p n hth
  have hpa := hJ.heap.align p _ hp
  have hpf := hJ.heap.fits p _ hp
  simp only [P1.HKind.bits] at hpa hpf
  have e32 : 2 ^ (n + 5) = 32 * 2 ^ n := by rw [pow_add]; ring
  have hi1 : 32 * (i + 1) ≤ 2 ^ (n + 5) := by rw [e32]; have : i + 1 ≤ 2 ^ n := hi; omega
  have hbv : b.val % 8 = 0 ∧ p.val ≤ b.val ∧ b.val < p.val + 2 ^ (n + 5) := by
    rcases hb with rfl | rfl
    · refine ⟨by omega, by omega, by omega⟩
    · have e : (core.num.U64.wrapping_add (slotOf p i) 8#u64).val = (slotOf p i).val + 8 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      rw [e]; refine ⟨by omega, by omega, by omega⟩
  have hΩ : b ∈ P1.Heap.omega H := ⟨hbv.1, p, _, hp, Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)), hbv.2.1, hbv.2.2⟩
  obtain ⟨⟨Q, R, h0⟩, -⟩ := J.blk
  refine ⟨h0.omega b hΩ, fun hf => ?_⟩
  obtain ⟨-, q, k, hq, hk, hin1, hin2⟩ := hf
  have hpq : q ≠ p := fun e => by
    subst e; rw [hp] at hq; cases hq
    rcases hk with h' | ⟨z', h'⟩ | ⟨h', -⟩ <;> cases h'
  obtain ⟨-, hb1, hb2⟩ := hbv
  have hd := hJ.heap.disj q k p _ hq hp hpq
  rw [show (P1.HKind.other (n + 5)).bits = n + 5 from rfl] at hd
  rcases hd with e | e
  · omega
  · omega

/-- **`CnOff` at a `JAtZ` state** (m68's [J] `CnOffAt`, derived): the CNode
caps reachable from the current thread's root are CNodes of `Z.th` with their
radix (`SlotsValid`, `StateRel.ctable`), whose indexed slots
`x &&& mask r < 2 ^ r` are slots of `Z.th` (`JAtZ.capSW`). -/
theorem JAtZ.cnOff {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    {t : U64} (et : sched.cur_thread st s = ok t) :
    P1.CnOff (L := L) (P1.Heap.tcbs H) Cs (P1.Heap.frame H) s t := by
  have htcb := J.curW_tcb et
  have hR := J.xtop.rel.2.1.1
  have hV := J.xtop.rel.2.1.2.1
  intro sl root hsl hroot
  obtain ⟨tcb, c, -, hc, -, hval⟩ := hR.ctable hV htcb
  have hsl' := tcb_slot_spec t layout.tcb.SLOT_CTABLE
  rw [hsl, WP.spec_ok] at hsl'
  rw [hsl', show (layout.tcb.SLOT_CTABLE.bv : BitVec 64) = 0#64 by simp [layout.tcb.SLOT_CTABLE],
    slot_cap_eq, hc] at hroot
  obtain rfl := P1.ok_inj_ff hroot
  refine ⟨fun p r => Z.th p = some (.cnode r.val), fun p r gs g e => ?_, fun p r m x p' r' gs' g' hC hm e => ?_,
    fun p r m x hC hm => ?_⟩
  · subst e; exact hval.1
  · rw [cnSlot_eq, slot_cap_eq] at e
    exact (hV.cnode p r.val hC _ (andMask_lt_pow hm x) _ e).1
  · have hi := andMask_lt_pow hm x
    rw [cnSlot_eq]
    exact ⟨J.capSW hC hi (Or.inl rfl), J.capSW hC hi (Or.inr rfl)⟩

set_option maxHeartbeats 4000000 in
/-- **The dispatch state of the real run carries `JAtZ`** (the prefix of
`kernel_entryJ13PUN`): after the entry's own `NEXT_IP` read and `FAULT_IP`
write and a passing `budget_ok`, `JAtZ` holds at the ghosts `Z.mv Z.G V0`, `H`,
`Cs`, its spec state with the kheap of `faultIPSt σ`. -/
theorem JAtZ.rrDisp {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (hni : Entered σ) (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {t nx : U64} {s1 s2 : S} {a2 : A} (et : sched.cur_thread st s = ok t)
    (enx : obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1)
    (hb : syscall.budget_ok st arI s1 a = ok (true, s2, a2)) :
    ∃ x σb, σ.kheap σ.curThread = some (.tcb x) ∧ σb.kheap = (faultIPSt σ σ.curThread x).kheap ∧
      ∃ V0 Ac' Lst' D', JAtZ (L := L) arI AR (Z.mv Z.G V0) H Cs Ac' Lst' D' s2 a2 σb := by
  obtain ⟨hcur, -⟩ := J.curEq et
  have hctT : t ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, -⟩ := hI.1.tcb t hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  have hnx : nx = L.mem s (regA t layout.reg.NEXT_IP) := by
    have := Endp.obj.Tcb.reg.spec (L := L) s t layout.reg.NEXT_IP
    rw [enx, WP.spec_ok] at this; exact this
  have hs1 : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    have := Endp.obj.Tcb.set_reg.spec (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
    rw [es1, WP.spec_ok] at this; exact this
  subst hs1
  generalize hv : core.num.U64.wrapping_sub nx 2#u64 = v at hb
  have hvb : v.bv = x.tcbArch.tcbContext.userRegs .nextIP - 2 := by
    rw [← hv, core.num.U64.wrapping_sub_bv_eq, hnx, ← hxs.regs .nextIP, regIdx_nextIP]; rfl
  have hX2 := reg_wr_irel J.ip hI hctT hk Fl4Spec.Register.faultIP (by decide) v
  rw [regIdx_faultIP] at hX2
  obtain ⟨V0, J0⟩ := J.regWrJ hctT hk Fl4Spec.Register.faultIP v (by rw [regIdx_faultIP]; exact hX2)
  rw [regIdx_faultIP, hvb] at J0
  rw [← hcur] at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hni0 : Entered (faultIPSt σ σ.curThread x) := hni
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hBu : KBudgetB arI a (faultIPSt σ σ.curThread x) :=
    ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk' hC, hB x hk', Or.inr hQ⟩
  have hBud := JAtZ.budgetOkB (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu
    (SInv.ns_fl4SyscallFaultIP σ.curThread σ hS.1.1.ns _ hF) hARI.toARKeep hA hnd hmrt hmb hmax htu
  rw [hb, WP.spec_ok] at hBud
  obtain ⟨σb, -, ekh, -, -, -, -, -, -, Ac', Lst', D', J'⟩ := hBud.1 rfl
  exact ⟨x, σb, hk', ekh, V0, Ac', Lst', D', J'⟩

/-- **`P1.RRPreAt` from the joint relation** (module docstring): at every
dispatch state of the entry, `RRPre` from `JAtZ` there, `RV` at the entry's
spec state and m67's `nvm` read (`RRPreAt5`). -/
theorem JAtZ.rrPreAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (hni : Entered σ) (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRV : SInvR.RV σ) (hRP5 : P1.RRPreAt5 (L := L) arI s a) : P1.RRPreAt (L := L) arI s a := by
  intro t nx s1 s2 a2 et enx es1 hb
  obtain ⟨x, σb, -, ekh, V0, Ac', Lst', D', J'⟩ :=
    J.rrDisp hni hR hS hQ hB hARI hA hnd hM hmrt hmb hmax htu et enx es1 hb
  exact rrPre_of_lk (fun _ h => h) J'.bxi J'.lkTyped (J'.rrSum (rv_faultIP ekh hRV)) (fun _ et' => J'.cnOff et')
    (hRP5 t nx s1 s2 a2 et enx es1 hb)

set_option maxHeartbeats 4000000 in
/-- **`kernel_entryJ33R` with `hRP : P1.RRPreAt` replaced** (module
docstring) by `hRV : SInvR.RV σ` [J] (l4v `valid_refills` / `refills_sum`, at
the entry's spec state; a conjunct of the carried `SInvW`, `SInvW.rv`) and
m67's `nvm` read `hRP5 : P1.RRPreAt5` (kept). -/
theorem kernel_entryJ33F [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV33 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRV : SInvR.RV σ)
    (hRP5 : n = fl4_abi.syscall.SysReplyRecv → P1.RRPreAt5 (L := L) arI s a) :
    syscall.handle_syscall st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ33R s a σ J hni hR hS hE hQ hLv n c hn hflag hB hK hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hT
    hmax htu (fun hrr => J.rrPreAt hni hR hS hQ hB hARI hA hnd hM hmrt hmb hmax htu hRV (hRP5 hrr))

set_option maxHeartbeats 4000000 in
/-- **`kernel_entryJ33F` without `hLv`** (`J.live`, as `kernel_entryJ34R`). -/
theorem kernel_entryJ34F [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV33 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRV : SInvR.RV σ)
    (hRP5 : n = fl4_abi.syscall.SysReplyRecv → P1.RRPreAt5 (L := L) arI s a) :
    syscall.handle_syscall st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ33F s a σ J hni hR hS hE hQ J.live n c hn hflag hB hK hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hT
    hmax htu hRV hRP5

/-- `RV` is a conjunct of the readiness line's carried bundle `SInvW`. -/
theorem SInvW.rv {σ : Fl4Spec.State Unit} (h : SInvR.B8w.SInvW σ) : SInvR.RV σ := h.2.1.2.2.2.1

set_option maxHeartbeats 4000000 in
/-- **`kernel_entryJ34F` with `hS` / `hRV` from `SInvW`** (the readiness
line's carried bundle, `kentry_rdyOffW`): no spec-side premise beyond the
carried ones. -/
theorem kernel_entryJ34FW [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (hR : MR a σ.machineState) (hSW : SInvR.B8w.SInvW σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV33 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRP5 : n = fl4_abi.syscall.SysReplyRecv → P1.RRPreAt5 (L := L) arI s a) :
    syscall.handle_syscall st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ34F s a σ J hni hR (SInvR.B8w.SInvW.sb hSW) hE hQ n c hn hflag hB hK hFin hARI hA hnd hM hKD hPA hIA
    hmrt hmb hT hmax htu (SInvW.rv hSW) hRP5

end

end

end Fl4Proofs.P3

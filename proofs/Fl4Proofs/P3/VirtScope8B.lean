/-
P3x for virtualization (line virt, gen 8, item 1, front half): **the syscall entry's budget front, exported, and
`ScopeE8` derived from U36I's syscall clause.**

U33's syscall proof (`kernel_entryJ13PUG`, XTopJointKEntry29) applies the clause's `hK` inside the WP of
`handle_syscall`, at the FL4 state a passing `budget_ok` returns after the `FAULT_IP` write. Here that front is a
lemma outside the WP, so `hK` can be used to derive a spec fact:

* `checkBudget_val`, **`specBudget_bool`** (the spec's budget verdict is a function of the state at
  `numDomains = 1`: no state has both a passing and a stopping outcome).
* `nowAgree_F` (`MachPlat.nowAgree` from `MachPlatF`, the same `now` field).
* `JAtZ.budgetOkB8`: `JAtZ.budgetOkB` without `[VxE Z]` (only the stopping verdict is kept on the stopping side:
  `VxE` was used only for the stopping state's `JAtZ`).
* **`frontB_ex`**: at a `JAtZ` entry state with `KBudgetB`, every passing spec budget outcome after the
  `FaultIP` write (`EntryPt`) is FL4's: there are `s' a'` with `KFrontB s a s' a'` and
  `JAtZ (Z.mv Z.G V') … s' a' t`, and `BudgetAt σ t true`.
* **`scopeE8_of_hK`**: U36I's syscall-clause premise `hK` at an `NR` state ⇒ `VirtScope8.ScopeE8 c σ`
  (`frontB_ex` + VirtScope8J's `offRouteS8_of_disp`).

Named premises: `hvk : virtKind = .none` [S]; `hvirt : ∀ a, arI.virtualization a = ok 0` [P] (as VirtScope8J);
the budget premises are U33's own (`KBudgetB` [P]/[J] parts as `kernel_entryJ13PUG`'s `hB`, discharged from
`SInvX` / `MachPlatF` in VirtKEntryV2). No [W]. New file only.
-/
import Fl4Proofs.P3.VirtScope8J
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The spec's budget verdict is determined -/

theorem checkBudget_val {σ : Fl4Spec.State Unit} {x : Bool × Fl4Spec.State Unit}
    (hx : x ∈ (Fl4Spec.checkBudget (Z := Unit) σ).1) :
    ∃ b, Fl4Spec.readScRefillSufficient σ.curSc σ.consumedTime σ = some b ∧
      x.1 = (b && !Fl4Spec.isCurDomainExpired σ) := by
  unfold Fl4Spec.checkBudget at hx
  obtain ⟨y1, h1, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 h1
  obtain ⟨y2, h2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 h2
  obtain ⟨y3, h3, hx⟩ := hx
  unfold Fl4Spec.getScRefillSufficient at h3
  obtain ⟨hr, e3⟩ := MidRun.mem_getsThe' h3
  refine ⟨y3.1, hr, ?_⟩
  (try dsimp only at hx)
  split at hx
  · next hb =>
    obtain ⟨y4, h4, hx⟩ := hx
    obtain rfl := Set.mem_singleton_iff.1 h4
    rw [Set.mem_singleton_iff.1 hx]
    simp [hb, e3]
  · next hb =>
    obtain ⟨y4, h4, hx⟩ := hx
    obtain ⟨y5, h5, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
    simp [hb]

/-- **The spec's budget verdict is a function of the state** (module docstring). -/
theorem specBudget_bool (hnd : Fl4Spec.numDomains = 1) {σ : Fl4Spec.State Unit} {x y : Bool × Fl4Spec.State Unit}
    (hx : x ∈ (specBudget σ).1) (hy : y ∈ (specBudget σ).1) : x.1 = y.1 := by
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ.machineState))
  unfold specBudget at hx hy
  obtain ⟨⟨u, σu⟩, hu, hx⟩ := hx
  obtain ⟨⟨v, σv⟩, hv, hy⟩ := hy
  rw [hE] at hu hv
  have e1 : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have e2 : σv = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hv)
  subst e1 e2
  obtain ⟨z1, hz1, ex, -⟩ := SInvR.checkBudgetRestart_cases hx
  obtain ⟨z2, hz2, ey, -⟩ := SInvR.checkBudgetRestart_cases hy
  obtain ⟨b1, hb1, ez1⟩ := checkBudget_val hz1
  obtain ⟨b2, hb2, ez2⟩ := checkBudget_val hz2
  rw [hb1] at hb2
  cases hb2
  rw [ex, ey, ez1, ez2]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- `MachPlat.nowAgree` from `MachPlatF` (the same `now` field). -/
theorem nowAgree_F {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlatF arI MR) {a : A}
    {σ : Fl4Spec.State Unit} (hR : MR a σ.machineState) (hV : ValidMachineTime σ) : NowAgree arI a σ := by
  unfold NowAgree
  refine WP.spec_mono (hM.now a _ hR) ?_
  rintro r ⟨hv, -⟩
  refine ⟨gctState σ.machineState, ?_, ?_, rfl⟩
  · rw [hv]; exact doMachineOp_single (getCurrentTime_eq _)
  · rw [hv]; exact vmt_le_gct hV

set_option maxHeartbeats 16000000 in
/-- **`JAtZ.budgetOkB` without `[VxE Z]`** (module docstring). -/
theorem JAtZ.budgetOkB8 {s : S} {a : A} {σ0 : Fl4Spec.State Unit}
    (J0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ0) (hni0 : Entered σ0) (hBu : KBudgetB arI a σ0)
    (hNS0 : NativeScope σ0) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.budget_ok st arI s a ⦃ r =>
      (r.1 = true → ∃ σ', specBudget σ0 = ({(true, σ')}, False) ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget σ0).1, z.1 = false) ⦄ := by
  have hJt : ∀ r : Bool × S × A, (r.1 = true → ∃ σ',
      (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ0 = ({(true, σ')}, False) ∧
      σ'.kheap = σ0.kheap ∧ σ'.curThread = σ0.curThread ∧ σ'.curSc = σ0.curSc ∧
      σ'.schedulerAction = σ0.schedulerAction ∧ σ'.idleThread = σ0.idleThread ∧
      CurInv σ' ∧ OffReady σ' ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ') →
      (r.1 = true → ∃ σ', specBudget σ0 = ({(true, σ')}, False) ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ') :=
    fun r h ht => (h ht).imp fun _ h' => ⟨h'.1, h'.2.2.2.2.2.2.2.2⟩
  have hF : NoTmoSend σ0 → syscall.budget_ok st arI s a ⦃ r =>
      (r.1 = true → ∃ σ', specBudget σ0 = ({(true, σ')}, False) ∧
        ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget σ0).1, z.1 = false) ⦄ := fun hnt =>
    WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkF hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnt)) fun r ⟨h1, h2⟩ => ⟨hJt r h1, fun hf => by
          obtain ⟨σ', he, -⟩ := h2 hf
          refine ⟨(false, σ'), ?_, rfl⟩
          unfold specBudget
          rw [he]; exact Set.mem_singleton _⟩
  rcases hBu.tmo with hnt | hnq
  · exact hF hnt
  by_cases hnt : NoTmoSend σ0
  · exact hF hnt
  unfold NoTmoSend at hnt
  push_neg at hnt
  obtain ⟨⟨xt, hkt, hep⟩, ⟨y, m, hky, hy⟩⟩ := hnt
  have hper : ∀ x n, σ0.kheap σ0.curSc = some (.schedContext x n) → x.scPeriod ≠ 0 := fun x n h => by
    rw [hky] at h; cases h; exact hy
  obtain ⟨p, bd, rr, hth⟩ : ∃ p bd rr, xt.tcbTimeoutHandler = .endpointCap p bd rr := by
    revert hep; cases xt.tcbTimeoutHandler <;> simp [Fl4Spec.isEpCap]
  have hrr : xt.tcbState = .running ∨ xt.tcbState = .restart := by
    have hrun := J0.curRun.run hni0 xt hkt
    have hvm := hNS0 _ xt hkt
    revert hrun hvm; cases xt.tcbState <;> simp [Fl4Spec.runnable]
  by_cases hkl : ∃ l, σ0.kheap p = some (.endpoint (.recvEP l))
  · exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkTR hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hmax htu hnq hkt hrr hth hper hkl))
      fun r ⟨h1, h2⟩ => ⟨hJt r h1, fun hf => by
            obtain ⟨z, hz, hz1, -⟩ := h2 hf
            exact ⟨z, hz, hz1⟩⟩
  · have hcb : ∀ xe, σ0.kheap p = some (.endpoint xe) → Endp.CanBlock false xe := fun xe h => by
      cases xe with
      | idleEP => trivial
      | sendEP q => rfl
      | recvEP q => exact absurd ⟨q, h⟩ hkl
    exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkT hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnq hkt hrr hth hper hcb))
      fun r ⟨h1, h2⟩ => ⟨hJt r h1, fun hf => by
            obtain ⟨z, hz, hz1, -⟩ := h2 hf
            exact ⟨z, hz, hz1⟩⟩

set_option maxHeartbeats 16000000 in
/-- **The syscall entry's front at the passing budget outcomes** (module docstring). -/
theorem frontB_ex {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hni : Entered σ)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hNS0 : NativeScope σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (w : Unit × Fl4Spec.State Unit) (hw : w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1)
    (t : Fl4Spec.State Unit) (ht : VirtR7eK.EntryPt w.2 t) :
    ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
      KFrontB (L := L) arI s a s' a' ∧ JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' t ∧
      BudgetAt σ t true := by
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, -⟩ := hI.1.tcb ct hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  generalize hv : core.num.U64.wrapping_sub (L.mem s (regA ct (regIdx .nextIP))) 2#u64 = v
  have hvb : v.bv = x.tcbArch.tcbContext.userRegs .nextIP - 2 := by
    rw [← hv, core.num.U64.wrapping_sub_bv_eq, hxs.regs .nextIP]; rfl
  have hX2 := reg_wr_irel J.ip hI hctT hk Fl4Spec.Register.faultIP (by decide) v
  rw [regIdx_faultIP] at hX2
  obtain ⟨V0, J0⟩ := J.regWrJ hctT hk Fl4Spec.Register.faultIP v (by rw [regIdx_faultIP]; exact hX2)
  rw [regIdx_faultIP, hvb] at J0
  rw [← hcur] at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hw' : w = ((), faultIPSt σ σ.curThread x) := by
    rw [fl4SyscallFaultIP_eq hk'] at hw; exact Set.mem_singleton_iff.1 hw
  subst hw'
  have hni0 : Entered (faultIPSt σ σ.curThread x) := hni
  have hBud := JAtZ.budgetOkB8 arI (σ0 := faultIPSt σ σ.curThread x) J0 hni0 (hB x hk')
    (SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF) hAK hA hnd hmrt hmb hmax htu
  obtain ⟨⟨b, s2, a1⟩, hbeq, hpost⟩ := spec_exists hBud
  obtain ⟨t1, h1, h2⟩ := ht
  have htb : (true, t) ∈ (specBudget (faultIPSt σ σ.curThread x)).1 := ⟨((), t1), h1, h2⟩
  cases b with
  | false =>
    exfalso
    obtain ⟨z, hz, hz1⟩ := hpost.2 rfl
    have e := specBudget_bool hnd htb hz
    rw [hz1] at e
    cases e
  | true =>
    obtain ⟨σ', he, Ac', Lst', D', J'⟩ := hpost.1 rfl
    have htb' := htb
    rw [he] at htb'
    have et : t = σ' := congrArg Prod.snd (Set.mem_singleton_iff.1 htb')
    subst et
    exact ⟨V0, Ac', Lst', D', s2, a1, ⟨ct, v, hct, hbeq⟩, J', _, hF, htb⟩

set_option maxHeartbeats 4000000 in
/-- **`ScopeE8` from U36I's syscall-clause premise `hK`** (module docstring). -/
theorem scopeE8_of_hK (hvk : Fl4Spec.virtKind = .none) (hvirt : ∀ a : A, arI.virtualization a = ok 0#u64)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hnr : VirtR7e.NR σ) (hni : Entered σ)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hNS0 : NativeScope σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {n : I64} {c : Fl4Spec.Syscall} (hn : NativeSys n c)
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKVU32 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) :
    VirtScope8.ScopeE8 c σ := by
  intro w hw t ht
  obtain ⟨V', Ac', Lst', D', s', a', hF, J', hBA⟩ :=
    frontB_ex arI J hni hB hNS0 hAK hA hnd hmrt hmb hmax htu w hw t ht
  have nw : VirtR7e.NR w.2 := VirtExtTop.nr_fl4SyscallFaultIP _ σ hnr w hw
  obtain ⟨t1, h1, h2⟩ := ht
  have nt : VirtR7e.NR t := VirtNvK2.nr_checkBudgetRestart t1 (VirtNvK2.nr_updateTimeStamp _ nw _ h1) _ h2
  exact offRouteS8_of_disp arI hvk J' (hvirt a') nt hn (hK t hBA V' Ac' Lst' D' s' a' hF J')

end

end

end Fl4Proofs.P3.SInvR.G5

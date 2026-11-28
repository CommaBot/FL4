/-
# P2 (vexit gen 4): the IRQ slots through `vexit_pre` (`hI` discharged)

`syscall.handle_vcpu_exit.entryV` / `entryJ2` (P2/VcpuExitV, VcpuExitJ) take
`hI` [P]: after `vexit_pre`, when an IRQ came, the IRQ handler slots of the
kernel-global IRQ node name heap notifications (`IrqNtAt`). Here:

* **at the entry** (`irqNtAt_of_JAtZ`): at a P3 `JAtZ` state, IRQ `i`'s slot
  (`nodeA kb i`, a one-slot CNode of the typed heap, `IntLayout.node`) is
  related to the spec's IRQ node slot (the CNode relation), so its cap
  decodes, and a notification cap there names one of `Z.N` (`JAtZ.slotN`),
  hence a heap notification (`JAtZ.zH`). This is all of `hI` when
  `stalled = true` (`vexit_pre` is the identity).
* **across `vexit_pre`** (`stalled = false`, `vexit_pre.irq`): the two words of
  every IRQ slot (`IrqW`) are kept (`IrqFr`):
  - `update_timestamp` writes current-node words only (`irqFr_footB0`);
  - `vcpu.check` writes, by the new narrower **`VckN`** (`vcpu.check.vckN`),
    only the thread's register words, user words `U`, the bound notification's
    state word, the thread's state word and the core's action word (`VckW`
    admitted every word outside the TCBs and nodes); none is an IRQ slot word
    (`irqFr_vckN`; the user words by `UsrW.ks`);
  - `check_budget`: `check_budget.allGB` with `G := IrqFr` from the entry,
    every `FootB` step missing the IRQ words (`KgW.not_kwB`); its timeout
    fault in the pinned premise **`TmoIbVI`** [P] (`TmoIbV` plus `IrqFr` across
    the fault: a statement about the timeout fault only).
  The IRQ words are apart from P1's objects (`IrqOff`, `KgW`: outside TCBs and
  nodes, the endpoints and notifications, the frame words and the SC objects),
  which `irqOff_of_JAtZ` derives from P3 `JKern.hks` (every non-`other` heap
  object lies outside the kernel-global block).

**`syscall.handle_vcpu_exit.entryI`**: `entryV` with `hI` replaced by
`IrqOff`/`IrqNtAt` at the entry and `htk` with `TmoIbVI`.
**`syscall.handle_vcpu_exit.entryJ3`** (also `vm_timer_local.entryJ3`): from
every reachable entry state (`JReachU17`), premises `kernel_entry_domInvU29`'s
and `htk` [P] (`TmoIbVI`) only; `hI` gone. **`syscall.handle_vcpu_exit.entryJ3s`**:
the stalled run, `kernel_entry_domInvU29`'s premises only.
-/
import Fl4Proofs.P2.VcpuExitV
import Fl4Proofs.P3.BufAtJ
import Fl4Proofs.P3.JProducers
import Fl4Proofs.P3.Lookup
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

/-! ## The IRQ slot words and their frame -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

theorem slot_cap_dec (sl : obj.Slot) (s : S) :
    obj.Slot.cap st sl s = capability.Cap.decode (L.mem s sl) (L.mem s (core.num.U64.wrapping_add sl 8#u64)) := by
  unfold obj.Slot.cap
  simp [L.read_pair_eq, lift]

/-! ## `vcpu::check`'s words, narrowed (`VckN`) -/

/-- **The words `vcpu::check` of `y` writes** (narrower than `VckW`, whose
`VckR` admits every word outside the TCBs and nodes): `y`'s register words and
the user words `U` (the report, `RepW`), a notification's state word (the
bound notification, set idle), `y`'s state word and the core's action word. -/
def VckN (st : machine.Store S) [L : LawfulStore st] (U Nt : Set U64) (y : U64) (s0 : S) (b : U64) : Prop :=
  RepW y U b ∨ (∃ n ∈ Nt, b = epTSA n) ∨ b = stA y ∨ b = L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION

theorem VckN.ksb {y : U64} {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : VckN st U Nt y s1 b) : VckN st U Nt y s0 b := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, hc, nodeAt_of_ksb hk])))

variable {A : Type _} {ar : machine.Arch A}

/-- **The current thread's report writes `VckN` words** (`vcpu.report.xfV`,
then `set_thread_state`'s state and action words). -/
theorem vcpu.report.vckN (hA : P0.ArchTotal ar) {s : S} (a : A) (y badge : U64)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y = L.curW s)
    (hvm : L.mem s (stA y) = sched.TS_RUNNING_VM)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hpw : L.mem s (core.num.U64.wrapping_add y 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3664#u64)) vcpu.PENDING) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3664#u64)) vcpu.PENDING ∈ U) :
    vcpu.report st ar s a y badge ⦃ s' => WritesIn st s s' (VckN st U Nt y s) ⦄ := by
  subst hy
  have hb := EntryInv.vckBlk h
  obtain ⟨⟨Q, R, hq⟩, -, -, -, -⟩ := EntryInv.vckBlk h
  have hcT : L.curW s ∈ T := hq.curT
  refine WP.spec_mono (vcpu.report.xfV hA s a _ badge hb hcT hvm hU hbuf hpw) ?_
  rintro s' ⟨s2, h2, -, w2, e⟩
  obtain ⟨⟨Q2, R2, q2⟩, -, -, -, -⟩ := h2
  have hw := sched.set_thread_state.vckW2 s2 (L.curW s) sched.TS_RUNNING q2.tcbs (q2.nodes _ q2.cur) hcT
  rw [e, WP.spec_ok] at hw
  refine (w2.trans hw.1).mono fun b hb => ?_
  rcases hb with hb | hb | hb
  · exact Or.inl hb
  · exact Or.inr (Or.inr (Or.inl hb))
  · exact Or.inr (Or.inr (Or.inr (by rw [hb, w2.2.1, nodeAt_of_ksb w2.1])))

/-- **`vcpu::check` of the current thread writes only `VckN` words** (the walk
of `vcpu.check.vck`, with the narrower footprint). Premises as `vcpu.check.vck`. -/
theorem vcpu.check.vckN (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK U b ⦄)
    (hpw : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING ∈ U) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => WritesIn st s s' (VckN st U Nt (L.curW s) s) ⦄ := by
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ := (EntryInv.vckBlk h)
  have hT := hq.tcbs
  have hcT : L.curW s ∈ T := hq.curT
  have OK0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => WritesIn st s s' (VckN st U Nt (L.curW s) s) ⦄ :=
    (WP.spec_ok _).2 (WritesIn.refl _ _)
  unfold vcpu.check
  step with obj.Tcb.state.spec as ⟨i, ei⟩
  split
  · exact OK0
  rename_i hvm0
  have hvm : L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM := by
    rw [← ei]; by_contra hne; exact hvm0 (bne_iff_ne.mpr hne)
  have REP0 : ∀ bd : U64, (do
      let s1 ← vcpu.report st ar s a (L.curW s) bd
      ok (s1, a)) ⦃ s' _ => WritesIn st s s' (VckN st U Nt (L.curW s) s) ⦄ := fun bd =>
    WP.spec_bind (vcpu.report.vckN hA a _ bd h rfl hvm hU hbuf (fun h0 _ => hpw h0)) fun s1 hs1 =>
      (WP.spec_ok _).2 hs1
  -- the bound notification's badge (the VCPU, if any, has no pending exit)
  have NT : (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING) =
        0#u64) → ∀ n : U64, n = L.mem s (boundA (L.curW s)) → n ≠ 0#u64 → L.epState s n = obj.NTFN_ACTIVE →
      (do
        let badge ← obj.Ntfn.badge st n s
        let s1 ← obj.Ntfn.set_state st n s obj.NTFN_IDLE
        let s2 ← vcpu.report st ar s1 a (L.curW s) badge
        ok (s2, a)) ⦃ s' _ => WritesIn st s s' (VckN st U Nt (L.curW s) s) ⦄ := by
    intro hP0 n en hn0 hact
    have hnN : n ∈ Nt := by rw [en]; exact hX.2.2.bnd _ hcT (by rw [← en]; exact hn0)
    have hnH := hNt n hnN
    obtain ⟨E, EQ, hEW⟩ := hq.eps
    have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hnH)
    obtain ⟨hE, hEN, -⟩ := hEW.1 n he
    have hEΩ : ∀ x ∈ Ω, x.val + 8 ≤ n.val ∨ n.val + 16 ≤ x.val := hEW.2.2.1 n he
    have hTS := epTSA_val hE
    have a2 : Aligned (epTSA n) := (ep_aligned hE).2
    refine WP.spec_bind (obj.Ntfn.badge.any s n) fun bd _ => ?_
    refine WP.spec_bind (obj.Ntfn.set_state.val s n _) fun s1 e1 => ?_
    subst e1
    obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, -, ea2, -, ec2⟩ :=
      ntfn_idle_all hq hB hX hS hSg hnH (by rw [hact, ntfn_active_val])
    set s1 := L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) with hs1
    have hout : OutsideObjs st T Cs s (epTSA n) := by
      refine ⟨a2, fun t ht => ?_, fun c hc => ?_⟩
      · have := hE.disj t ht; rw [hTS]; omega
      · have := hEN.1 c hc; rw [hTS]; omega
    have hnh : ∀ c ∈ Scs, epTSA n ≠ scReplyA c ∧ epTSA n ≠ scTcbA c := by
      intro c hc
      obtain ⟨⟨a1, i1⟩, ⟨a3, i3⟩⟩ := vck_sclink_in hX.1 hc
      have r1 := hEΩ _ (hX.1.scW c hc _ a1 i1)
      have r3 := hEΩ _ (hX.1.scW c hc _ a3 i3)
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have := congrArg UScalar.val e; rw [hTS] at this; omega
      · have := congrArg UScalar.val e; rw [hTS] at this; omega
    have w1 : WritesIn st s s1 (VckW st T Cs Scs (L.curW s) s) :=
      (writesIn_wr a2).mono fun b e => Or.inl (Or.inl (by rw [e]; exact ⟨hout, hnh⟩))
    have w1n : WritesIn st s s1 (fun b => b = epTSA n) := writesIn_wr a2
    obtain ⟨-, eC1, ec1, -, fld1, -⟩ := VckW.frames hq hcT w1
    have h1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 :=
      EntryInv.vckStep h ⟨⟨Q, R, h2⟩, hB2, hX2, hS2, hSg2⟩ ec1 eC1 (Or.inl ea2) fun z hz => by
        rw [scA_eq]; exact fld1 z hz _ (by simp) (by simp) (fun _ => Or.inr (by simp))
    have st1 : L.mem s1 (stA (L.curW s)) = sched.TS_RUNNING_VM := by
      rw [stA_eq, f2 _ hcT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hvm
    have hU1 : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s1 b := fun b hb => (hU b hb).ksb w1.1
    have hbuf1 : msg.lookup_ipc_buffer st s1 true (L.curW s) ⦃ b => BufOK U b ⦄ := by
      rw [lookup_ipc_buffer_same ((VckW.ibFr hq hcT w1).2 _ hcT)]; exact hbuf
    have ev1 : L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64) =
        L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
      f2 _ hcT _ (by simp) (by simp) (by simp) (by simp)
    have hp1 : L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
        L.mem s1 (core.num.U64.wrapping_add (L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64))
          vcpu.PENDING) = 0#u64 := by
      intro hv0
      rw [ev1] at hv0 ⊢
      have hu := hU _ (hpw hv0)
      have hne := hu.eps n (Or.inr hnH)
      rw [hs1, L.mem_wr_ne a2 hu.out.1 (by rw [hTS]; omega)]
      exact hP0 hv0
    refine WP.spec_bind (vcpu.report.vckN hA a _ bd h1 eC1.symm st1 hU1 hbuf1 (fun h0 hp => absurd (hp1 h0) hp))
      fun s2 hs2 => (WP.spec_ok _).2 ?_
    exact (w1n.trans hs2).mono fun b hb => hb.elim (fun e => Or.inr (Or.inl ⟨n, hnN, e⟩))
      (fun hb => VckN.ksb w1n.1 w1n.2.1 hb)
  unfold vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  split
  · rename_i hv0
    unfold vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.read_spec s _) fun i1 ei1 => ?_
    split
    · exact REP0 0#u64
    · rename_i hi1
      have hP0 : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
          L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64))
            vcpu.PENDING) = 0#u64 := fun _ => by
              rw [← ev, ← ei1]; by_contra hne; exact hi1 (bne_iff_ne.mpr hne)
      refine WP.spec_bind (obj.Tcb.bound_ntfn.val s _) fun i2 ei2 => ?_
      split
      · rename_i hi2
        refine WP.spec_bind (obj.Ntfn.state.spec s i2) fun i3 ei3 => ?_
        split
        · rename_i hi3
          exact NT hP0 i2 ei2 (by simpa using hi2) (by rw [← ei3]; exact hi3)
        · split
          · exact REP0 0#u64
          · exact OK0
      · split
        · exact REP0 0#u64
        · exact OK0
  · rename_i hv0
    have hP0 : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
        L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64))
          vcpu.PENDING) = 0#u64 := fun hne => absurd (by rw [← ev]; by_contra hne'; exact hv0 (bne_iff_ne.mpr hne')) hne
    refine WP.spec_bind (obj.Tcb.bound_ntfn.val s _) fun i2 ei2 => ?_
    split
    · rename_i hi2
      refine WP.spec_bind (obj.Ntfn.state.spec s i2) fun i3 ei3 => ?_
      split
      · rename_i hi3
        exact NT hP0 i2 ei2 (by simpa using hi2) (by rw [← ei3]; exact hi3)
      · split
        · exact REP0 0#u64
        · exact OK0
    · split
      · exact REP0 0#u64
      · exact OK0

/-! ## The budget check -/

end

/-! ## From a reachable entry state -/

open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

end Fl4Proofs.P2.Stall

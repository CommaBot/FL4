/-
P2 (tmofr, part C): **vexit's `htk` discharged** by the shared timeout-fault
lemma (`tmoIbVI_of`, P2/TmoFrB).

* `TmoCapW s t`: thread `t`'s timeout handler cap, decoded from its two slot
  words (TCB offsets 128, 136), is typed. `TmoCapW.slot`: the cap read
  `handle_timeout` does. `tmoIbVI_ofW`: `tmoIbVI_of` with the cap fact at the
  budget check's start only (`ChgW` writes miss the TCB's cap slots).
* **`vexit_tk`**: `htk` (`update_timestamp ⦃ vcpu.check ⦃ TmoIbVI ⦄ ⦄`) from
  facts at the VM exit's entry: `EntryInv`, `BufAt`, `PendAt`, `IrqOff`, the
  current thread not queued (`hnq`), the idle thread not runnable (`hni`) and
  `TmoCapW` of the current thread. `update_timestamp` writes node words only;
  `vcpu.check` writes (`VckW.frames`) only the current thread's register words
  and state word, so the queue word, the idle thread's state and the cap slot
  words reach the budget check (on `RUNNING_VM` the current thread is runnable,
  hence not the idle thread).
* **`syscall.handle_vcpu_exit.entryK`**, **`vm_timer_local.entryK`**: `entryI`
  with the run premise `htk` replaced by the entry facts `hnq`, `hni` [P] and
  `hcw` [P].
* `tmoCapW_of_JAtZ`: `hcw` at a P3 `JAtZ` state (`JAtZ.timeoutTyped` at the
  current thread's slot 4).
* **`syscall.handle_vcpu_exit.entryJ4`**, **`vm_timer_local.entryJ4`**: from
  every reachable entry state (`JReachU17`), premises `kernel_entry_domInvU29`'s
  and two facts about the entry state itself, no run premise: `hnq` [P] (the
  current thread's `Q_QUEUED` bit clear: P3 `JAtZ.curBits` from the spec's
  `SInvC.ctQ`) and `hni` [P] (the idle thread's state word not runnable: the
  spec's valid-idle invariant).
-/
import Fl4Proofs.P2.TmoFrB
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

theorem tmo_slot (t : U64) :
    obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER = ok (core.num.U64.wrapping_add t 128#u64) := by
  rw [tcb_slot_val]; unfold slotIdx
  have e : core.num.U64.wrapping_mul layout.tcb.SLOT_TIMEOUT_HANDLER 32#u64 = 128#u64 := by
    apply UScalar.eq_of_val_eq
    simp [layout.tcb.SLOT_TIMEOUT_HANDLER, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  rw [e]

theorem tmoSlot8_eq (t : U64) :
    core.num.U64.wrapping_add (core.num.U64.wrapping_add t 128#u64) 8#u64 = core.num.U64.wrapping_add t 136#u64 := by
  apply UScalar.eq_of_val_eq
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  try omega

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- Thread `t`'s timeout handler cap, decoded from its slot's two words at `s`, is typed. -/
def TmoCapW (st : machine.Store S) [L : LawfulStore st] (H : Heap) (Rp Nt : Set U64) (s : S) (t : U64) : Prop :=
  capability.Cap.decode (L.mem s (core.num.U64.wrapping_add t 128#u64))
    (L.mem s (core.num.U64.wrapping_add t 136#u64)) ⦃ c => CapTyped H Rp Nt c ⦄

theorem TmoCapW.slot {s : S} {t : U64} (h : TmoCapW st H Rp Nt s t) :
    obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄ := by
  rw [tmo_slot, WP.spec_ok, slot_cap_dec, tmoSlot8_eq]; exact h

theorem TmoCapW.of_eq {s s' : S} {t : U64} (h : TmoCapW st H Rp Nt s t)
    (e1 : L.mem s' (core.num.U64.wrapping_add t 128#u64) = L.mem s (core.num.U64.wrapping_add t 128#u64))
    (e2 : L.mem s' (core.num.U64.wrapping_add t 136#u64) = L.mem s (core.num.U64.wrapping_add t 136#u64)) :
    TmoCapW st H Rp Nt s' t := by
  unfold TmoCapW; rw [e1, e2]; exact h

variable {A : Type _} {ar : machine.Arch A}

/-- `tmoIbVI_of` with the current thread's cap fact at the budget check's start. -/
theorem tmoIbVI_ofW (hA : P0.ArchTotal ar) (s0 : S) (h0 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0)
    (hO : IrqOff st T Cs H Sg Scs Z s0)
    (hnq : (L.mem s0 (inqA (L.curW s0)) &&& sched.Q_QUEUED) = 0#u64)
    (hni : ¬ Runnable (L.mem s0 (stA (L.idleW s0))))
    (hcw : TmoCapW st H Rp Nt s0 (L.curW s0)) :
    TmoIbVI st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0 :=
  tmoIbVI_of hA s0 h0 hO hnq hni fun s hw => by
    obtain ⟨⟨Q1, R1, q1⟩, -, hX1, -, -⟩ := h0
    have wF : WritesIn st s0 s (L.Free s0 Ω Cs) := hw.mono' fun b hb hh => by
      rcases hh with ⟨c, hc, hin⟩ | e
      · exact Or.inl (hX1.1.scW c hc b hb hin)
      · exact e ▸ free_cur_node q1.cur (by simp [layout.node.CONSUMED, LowFree])
    obtain ⟨-, kc, -, -⟩ := free_keys q1 wF
    have hcT := q1.curT
    have KK : ∀ K : U64, K.val < 192 → K.val % 8 = 0 →
        L.mem s (core.num.U64.wrapping_add (L.curW s0) K) = L.mem s0 (core.num.U64.wrapping_add (L.curW s0) K) :=
      fun K hK h8 => by
        refine wF.mem_eq (field_aligned (q1.tcbs _ hcT) (by omega) h8) ?_
        rintro (hm | ⟨c, hc, o, ho, e⟩)
        · exact out_ne_field (K := K) (q1.omega _ hm) hcT (q1.tcbs _ hcT) (by omega) rfl
        · exact node_ne_field (q1.nodes c hc) (by simp only [LowFree] at ho; omega) hcT (q1.tcbs _ hcT)
            (by omega) e.symm
    rw [kc]
    exact (hcw.of_eq (KK 128#u64 (by simp) (by simp)) (KK 136#u64 (by simp) (by simp))).slot

/-- **`htk` from the VM exit's entry** (`tmoIbVI_ofW` at the budget check's
start). Named premises (facts at the entry state): `hnq` [P], `hni` [P],
`hcw` [P]. -/
theorem vexit_tk (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (hPd : PendAt st U s)
    (hO : IrqOff st T Cs H Sg Scs Z s)
    (hnq : (L.mem s (inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64)
    (hni : ¬ Runnable (L.mem s (stA (L.idleW s))))
    (hcw : TmoCapW st H Rp Nt s (L.curW s)) :
    sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbVI st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄ := by
  have hq := h.1.choose_spec.choose_spec
  have hcT : L.curW s ∈ T := hq.curT
  have hiT : L.idleW s ∈ T := hq.idleT
  refine WP.spec_mono (WP.spec_and (Fl4Proofs.P1.sched.update_timestamp.bxc hA s a (EntryInv.bxi h))
      (Fl4Proofs.P2.Stall.sched.update_timestamp.kwB (T := ∅) (Sg := ∅) (Scs := ∅) (Es := ∅)
        (Z := fun _ => 0) hA s a (nodePlaced0 (hq.nodes _ hq.cur)) hq.cur)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨hb1, c1, k1⟩, n1, f1⟩, F1⟩
  try simp only [WP.uncurry'_pair]
  have E1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := EntryInv.of_step h hb1.blk c1 n1.2.2 (Or.inl n1.1) f1
  have hcur : L.curW s1 = L.curW s := k1.1
  have hidl : L.idleW s1 = L.idleW s := n1.2.1
  have hk1 : L.ksb s1 = L.ksb s := F1.1
  have fk : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK h8 => footB0_fld hq hy hK h8 F1
  have I1 : IbFr (L := L) T s s1 := ibFr_footB0 hq F1
  have V1 : VmPl st T Cs H Sg Scs Z U s1 := fun hv => by
    rw [hcur] at hv ⊢
    have est : L.mem s1 (stA (L.curW s)) = L.mem s (stA (L.curW s)) :=
      footB0_fld hq hcT (by simp [layout.tcb.STATE]) (by simp [layout.tcb.STATE]) F1
    have evc : L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64) =
        L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
      footB0_fld hq hcT (by simp) (by simp) F1
    refine ⟨hBA.of_fr I1, fun hw => ?_⟩
    rw [evc] at hw ⊢
    exact hPd (est ▸ hv) hw
  have hq1 := E1.1.choose_spec.choose_spec
  -- the entry facts at `s1`
  have nq1 : (L.mem s1 (inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [inqA_eq, fk _ hcT 3592#u64 (by simp) (by simp), ← inqA_eq]; exact hnq
  have ni1 : ¬ Runnable (L.mem s1 (stA (L.idleW s))) := by
    rw [stA_eq, fk _ hiT 3328#u64 (by simp) (by simp), ← stA_eq]; exact hni
  have cw1 : TmoCapW st H Rp Nt s1 (L.curW s) :=
    hcw.of_eq (fk _ hcT 128#u64 (by simp) (by simp)) (fk _ hcT 136#u64 (by simp) (by simp))
  by_cases hv : L.mem s1 (stA (L.curW s1)) = sched.TS_RUNNING_VM
  · obtain ⟨hBA1, hpw⟩ := V1 hv
    refine WP.spec_mono (vcpu.check.vck hA hNt s1 a1 E1 hBA1.1 (hBA1.2 _ hq1.curT) hpw) ?_
    rintro ⟨s2, a2⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    obtain ⟨E2, w2, -⟩ := hh
    obtain ⟨-, ec2, -, ei2, fld2, -⟩ := VckW.frames hq1 hq1.curT w2
    have hne : L.idleW s ≠ L.curW s := fun e => by
      have hr : Runnable (L.mem s1 (stA (L.curW s1))) := Or.inr (Or.inr hv)
      rw [hcur, ← e] at hr
      exact ni1 hr
    have fk2 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = L.curW s → K.val < 256 ∨ 3328 < K.val) →
        L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s1 (core.num.U64.wrapping_add y K) :=
      fun y hy K hK h8 hc => fld2 y hy K hK h8 (fun e => hc (e.trans hcur))
    refine tmoIbVI_ofW hA s2 (EntryInv.bxi E2) (hO.ksb (w2.1.trans hk1)) ?_ ?_ ?_
    · rw [ec2, hcur, inqA_eq, fk2 _ hcT 3592#u64 (by simp) (by simp) (fun _ => Or.inr (by simp)), ← inqA_eq]
      exact nq1
    · rw [ei2, hidl, stA_eq, fk2 _ hiT 3328#u64 (by simp) (by simp) (fun e => absurd e hne), ← stA_eq]
      exact ni1
    · rw [ec2, hcur]
      exact cw1.of_eq (fk2 _ hcT 128#u64 (by simp) (by simp) (fun _ => Or.inl (by simp)))
        (fk2 _ hcT 136#u64 (by simp) (by simp) (fun _ => Or.inl (by simp)))
  · rw [check_of_ne ar s1 a1 _ hv, WP.spec_ok]
    refine tmoIbVI_ofW hA s1 (EntryInv.bxi E1) (hO.ksb hk1) ?_ ?_ ?_
    · rw [hcur]; exact nq1
    · rw [hidl]; exact ni1
    · rw [hcur]; exact cw1

/-- **(tmofr) The serial VM exit keeps `EntryInv`, no run premise**:
`entryI` with `htk` from `vexit_tk`. Named premises (at the entry state):
`hBA` [P], `hO` [P], `hIN` [P] (as `entryI`), `hnq` [P], `hni` [P], `hcw` [P]. -/
theorem syscall.handle_vcpu_exit.entryK (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq : U64) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hz : VcpuZ st T s) (hO : IrqOff st T Cs H Sg Scs Z s)
    (hIN : IrqNtAt st Nt s)
    (hnq : (L.mem s (inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64)
    (hni : ¬ Runnable (L.mem s (stA (L.idleW s))))
    (hcw : TmoCapW st H Rp Nt s (L.curW s)) :
    syscall.handle_vcpu_exit st ar s a irq stalled ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  syscall.handle_vcpu_exit.entryI hA hNt s a irq stalled h hBA hz hO hIN
    (fun _ => vexit_tk hA hNt s a h hBA (pendAt_of_vcpuZ hz h.1.choose_spec.choose_spec.curT) hO hnq hni hcw)

/-- **(tmofr) The x86 local VM timer exit keeps `EntryInv`, no run premise**
(`vm_timer_local.entryI` with `vexit_tk`). -/
theorem vm_timer_local.entryK (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq n : U64) (p : localtimer.TimerIrqPlan) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hz : VcpuZ st T s) (hO : IrqOff st T Cs H Sg Scs Z s)
    (hIN : IrqNtAt st Nt s)
    (hnq : (L.mem s (inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64)
    (hni : ¬ Runnable (L.mem s (stA (L.idleW s))))
    (hcw : TmoCapW st H Rp Nt s (L.curW s)) :
    localvm.handle_vm_timer_irq_local st ar s a irq p n ⦃ r => r.1 = true →
      EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ :=
  vm_timer_local.entryI hA hNt s a irq n p h hBA hz hO hIN
    (vexit_tk hA hNt s a h hBA (pendAt_of_vcpuZ hz h.1.choose_spec.choose_spec.curT) hO hnq hni hcw)

end

/-! ## From a reachable entry state -/

open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem slotOf4 (t : U64) : core.num.U64.wrapping_add t 128#u64 = slotOf t 4 := by
  apply UScalar.eq_of_val_eq
  show (core.num.U64.wrapping_add t 128#u64).val = (t.bv + BitVec.ofNat 64 4 * 32#64).toNat
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  try omega

/-- **The current thread's timeout handler cap is typed at a `JAtZ` state**
(`JAtZ.timeoutTyped` at its TCB slot 4). -/
theorem tmoCapW_of_JAtZ {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    TmoCapW st H (Heap.replies H) (Heap.ntfns H) s (L.curW s) := by
  have hsl : IsSlot Z.th (core.num.U64.wrapping_add (L.curW s) 128#u64) :=
    ⟨L.curW s, 4, Or.inr ⟨J.curW_tcb (cur_thread_curW (L := L) s), by simp [tcbSlots]⟩, slotOf4 _⟩
  have h1 := J.timeoutTyped hsl
  rw [slot_cap_dec, tmoSlot8_eq] at h1
  exact h1

set_option maxHeartbeats 4000000 in
/-- **(tmofr) The serial VM exit from every reachable entry state keeps
`EntryInv`, with no run premise** (`entryK`; `htk` of `entryJ3` gone).
Premises: `kernel_entry_domInvU29`'s, and two facts of the entry state:
`hnq` [P] (the current thread's `Q_QUEUED` bit is clear) and `hni` [P] (the
idle thread's state word is not runnable). -/
theorem syscall.handle_vcpu_exit.entryJ4 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    (hnq : (L.mem s (P1.inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64)
    (hni : ¬ P1.Runnable (L.mem s (P1.stA (L.idleW s)))) :
    ∃ (H : Heap) (Cs Ac : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      ∀ (a0 : A) (irq : U64) (stalled : Bool),
      syscall.handle_vcpu_exit st arI s a0 irq stalled ⦃ s' _ => EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H
        (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s' ⦄ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, ⟨hI, -⟩, -⟩ :=
    kernel_entry_domInvU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  obtain ⟨hc, -, hz⟩ := ventS_of_JAtZ J
  exact ⟨H, Cs, Ac, hc, hI, fun a0 irq stalled =>
    syscall.handle_vcpu_exit.entryK hA (fun _ hn => hn) s a0 irq stalled hI J.bufAtJ hz (irqOff_of_JAtZ J)
      (irqNtAt_of_JAtZ J) hnq hni (tmoCapW_of_JAtZ J)⟩

set_option maxHeartbeats 4000000 in
/-- **(tmofr) The x86 local VM timer exit from every reachable entry state
keeps `EntryInv`, with no run premise** (`vm_timer_local.entryK`). Premises:
`kernel_entry_domInvU29`'s, `hnq` [P], `hni` [P]. -/
theorem vm_timer_local.entryJ4 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    (hnq : (L.mem s (P1.inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64)
    (hni : ¬ P1.Runnable (L.mem s (P1.stA (L.idleW s)))) :
    ∃ (H : Heap) (Cs Ac : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      ∀ (a0 : A) (irq n : U64) (p : localtimer.TimerIrqPlan),
      localvm.handle_vm_timer_irq_local st arI s a0 irq p n ⦃ r => r.1 = true →
        EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
          (Heap.scBits H) Ac r.2.1 ⦄ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, ⟨hI, -⟩, -⟩ :=
    kernel_entry_domInvU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  obtain ⟨hc, -, hz⟩ := ventS_of_JAtZ J
  exact ⟨H, Cs, Ac, hc, hI, fun a0 irq n p =>
    vm_timer_local.entryK hA (fun _ hn => hn) s a0 irq n p hI J.bufAtJ hz (irqOff_of_JAtZ J)
      (irqNtAt_of_JAtZ J) hnq hni (tmoCapW_of_JAtZ J)⟩

end

end Fl4Proofs.P2.Stall

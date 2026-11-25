/-
P2 (tmofr, part B): **the shared timeout-fault lemma** `faults.handle_timeout.tmoFr`
(P2/TmoFrA) **discharges `TmoIbVI`** (vexit gen 4's `htk` content).

* Frames of a timeout fault's footprint (`FootT`, P2/TmoFrA) over no protected
  thread in no-donation mode (`Kp = ∅`, `Nd`): every TCB's VCPU word
  (`FootT.vcpu`: a protected word, `PrW`), the buffer-lookup words
  (`FootT.ibFr`: `KWB` has no `IPC_BUFFER` word, the transfer writes register
  words `≥ 256` and SC words only), the IRQ slot words (`FootT.irqFr`: no
  `KWB`, debug-list, TCB or SC word is a `KgW` word).
* **`tmoIbVI_of`**: `TmoIbVI s0` (now over `Timeout` faults, the only fault
  `end_timeslice` raises) from facts at the budget check's start `s0`:
  `BXI`, `IrqOff`, the current thread not queued (`hnq`), the idle thread not
  runnable (`hni`, so the runnable current thread is not idle), and
  `hcap` [P]: the current thread's timeout handler cap typed at the states
  `ChgW` writes reach from `s0`. No transfer premise (`XferOKRS`,
  `XferFootOKC` are not needed for a timeout fault).
-/
import Fl4Proofs.P2.TmoFrA
import Fl4Proofs.P2.VcpuExitI
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- A timeout fault's footprint over no protected thread keeps every TCB's VCPU word. -/
theorem FootT.vcpu {s s' : S} (hT : TcbPlaced T) (f : FootT st ∅ True T Cs Sg Scs Z (EH H) s s') :
    VcpuWK st T s s' := fun t ht =>
  f.mem_eq (field_aligned (hT t ht) (by simp) (by simp)) fun hb =>
    hb.2 (Or.inr (Or.inr ⟨trivial, Or.inr (Or.inr ⟨t, ht, hT t ht, rfl⟩)⟩))

/-- … the buffer-lookup words. -/
theorem FootT.ibFr {Kp : Set U64} {Nd : Prop} {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (f : FootT st Kp Nd T Cs Sg Scs Z (EH H) s s') : IbFr (L := L) T s s' := by
  obtain ⟨⟨Q, R, q⟩, -, hX, -, hSg⟩ := h
  refine IbFr.of_bufKeep f.1 (BufKeep.of_writes q.tcbs f.w fun b hal hb => ?_)
  rcases hb.1 with hk | hd | (⟨y, hy, K, h1, h2, -, e⟩ | hu) | ⟨c, hc, e⟩
  · exact kwB_notBufW q hX.1 hSg.sub (fun _ he => he) hal hk
  · exact notBufW_dbg q.tcbs q.nodes hd
  · subst e; exact notBufW_field q.tcbs hy (by omega) (by omega) (by omega)
  · exact absurd hu (Set.notMem_empty _)
  · subst e
    exact notBufW_out q.tcbs (q.omega _ (hX.1.scW c hc _ hal (consW_in hX.1 hc).2))

/-- … the IRQ slot words (placed apart from P1's objects, `IrqOff`). -/
theorem FootT.irqFr {Kp : Set U64} {Nd : Prop} {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hO : IrqOff st T Cs H Sg Scs Z s) (f : FootT st Kp Nd T Cs Sg Scs Z (EH H) s s') : IrqFr st s s' := by
  obtain ⟨⟨Q, R, q⟩, -, hX, -, -⟩ := h
  refine irqFr_step (IrqFr.refl s) f.w fun b hb => ⟨(hO b hb).out.1, fun hw => ?_⟩
  have k := hO b hb
  rcases hw.1 with hk | hd | (⟨y, hy, K, -, h2, -, e⟩ | hu) | ⟨c, hc, e⟩
  · exact k.not_kwB q hk
  · exact notDbgW_out q.tcbs q.nodes k.out hd
  · exact out_ne_field (K := K) k.out hy (q.tcbs y hy) (by omega) (by rw [e])
  · exact absurd hu (Set.notMem_empty _)
  · exact k.sc c hc (e ▸ (consW_in hX.1 hc).2)

variable {A : Type _} {ar : machine.Arch A}

/-- **`TmoIbVI` from the shared timeout-fault lemma** (`handle_timeout.tmoFr`):
at the states a budget check from `s0` reaches by `ChgW` writes, the current
thread can block (as P2's `tmoKC_N` derives it: `CurOK`, its queue flag at
`s0`, and it is not the idle thread, which is not runnable at `s0`), and the
timeout fault keeps `BXI`, the buffer-lookup words, every VCPU word and the
IRQ slot words. **Named premise `hcap` [P]**: the current thread's timeout
handler cap is typed at those states (P3's cap relation; the TCB's cap slots
are untouched by `ChgW` writes). -/
theorem tmoIbVI_of (hA : P0.ArchTotal ar) (s0 : S) (h0 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s0)
    (hO : IrqOff st T Cs H Sg Scs Z s0)
    (hnq : (L.mem s0 (inqA (L.curW s0)) &&& sched.Q_QUEUED) = 0#u64)
    (hni : ¬ Runnable (L.mem s0 (stA (L.idleW s0))))
    (hcap : ∀ s : S, WritesIn st s0 s (ChgW st Scs Z s0) →
      obj.Tcb.slot (L.curW s) layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
        obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄) :
    TmoIbVI st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0 := fun s a f Q R h hB hX hSg hS hw hok => by
  obtain ⟨⟨Q1, R1, q1⟩, -, hX1, -, -⟩ := h0
  have hk : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩
  have wF : WritesIn st s0 s (L.Free s0 Ω Cs) := hw.mono' fun b hb hh => by
    rcases hh with ⟨c, hc, hin⟩ | e
    · exact Or.inl (hX1.1.scW c hc b hb hin)
    · exact e ▸ free_cur_node q1.cur (by simp [layout.node.CONSUMED, LowFree])
  obtain ⟨-, kc, ki, -⟩ := free_keys q1 wF
  have hcT := q1.curT
  have kq : L.mem s (inqA (L.curW s0)) = L.mem s0 (inqA (L.curW s0)) := by
    rw [inqA_eq]
    refine wF.mem_eq (field_aligned (q1.tcbs _ hcT) (by simp) (by simp)) ?_
    rintro (hm | ⟨c, hc, o, ho, e⟩)
    · exact out_ne_field (q1.omega _ hm) hcT (q1.tcbs _ hcT) (by simp) rfl
    · exact node_ne_field (q1.nodes c hc) (by simp only [LowFree] at ho; omega) hcT (q1.tcbs _ hcT) (by simp) e.symm
  have hiT := q1.idleT
  have ks : L.mem s (stA (L.idleW s0)) = L.mem s0 (stA (L.idleW s0)) := by
    rw [stA_eq]
    refine wF.mem_eq (field_aligned (q1.tcbs _ hiT) (by simp) (by simp)) ?_
    rintro (hm | ⟨c, hc, o, ho, e⟩)
    · exact out_ne_field (q1.omega _ hm) hiT (q1.tcbs _ hiT) (by simp) rfl
    · exact node_ne_field (q1.nodes c hc) (by simp only [LowFree] at ho; omega) hiT (q1.tcbs _ hiT) (by simp) e.symm
  have hni' : L.idleW s ≠ L.curW s := fun e => by
    have hr := hok.run
    rw [← e, ki, ks] at hr
    exact hni hr
  have hc : CanBlock st T Ac s (L.curW s) :=
    ⟨h.curT, fun hb => blocked_not_runnable hb hok.run, runnable_ne_reply hok.run,
      by rw [kc, kq]; exact hnq, hok.rel, hok.act, hni',
      fun _ => (hS.act _ (hX.2.2.bound _ h.curT hok.bnd).1).2 hok.rmx⟩
  have hO' : IrqOff st T Cs H Sg Scs Z s := hO.ksb hw.1
  refine WP.spec_mono (faults.handle_timeout.tmoFr (Kp := (∅ : Set U64)) (Nd := True) hA s a _ f hk hc (hcap s hw)
    (Set.notMem_empty _) (fun _ hy => absurd hy (Set.notMem_empty _)) (fun _ hy => absurd hy (Set.notMem_empty _))
    (fun _ => Set.notMem_empty _)) ?_
  rintro ⟨s', a'⟩ hr
  simp only [WP.uncurry'_pair] at hr ⊢
  exact ⟨BlkOK.bxi hr.1, FootT.ibFr hk hr.2, FootT.vcpu h.tcbs hr.2, FootT.irqFr hk hO' hr.2⟩

end

end Fl4Proofs.P2.Stall

/-
# P2 (line lvm, gen 8): **`local_vm_timer_irq` under `ownV`: the entry facts, `acc` and `move`**

For rule 7's map `OwnMapV.ownV K` and `local_vm_exit`'s sets `VexitRS` / `VexitWS` (aligned user words and the words
`ownV` lets the path read / write):

* `vOf st s`: the current thread's bound VCPU (its `VCPU` word); `VtmEnt`: the entry facts of `local_vm_timer_irq`,
  `local_vm_exit`'s `VexitEnt` for `v = vOf st s` and the glue's notification `n`, plus the timer interrupt's
  kernel-global words (`IrqLay.iq` / `.kr` / `.tab`, each also outside every VCPU) and P1's `AsidOff`;
* `vtimer_irq_lt`: an accepted run has `irq < 128` (as `irq_lt_of_acc`);
* **`vtimer_acc_own`**: `PathObl.acc` of an accepted quiet or round-robin run, on `guard st (VexitRS …)
  (VexitWS …)` (`vtimer_accG` with `vexit_rd`, `irq_wr_own` + `wpermV_of_own'`, the kernel-global words by
  `rperm_none` + `rpermV_of_own`, `PENDING` by `pending_rd`, `TAIL_STATE` by `ntfn_tail_rd`), the fire case a
  premise;
* **`vtimer_move`**: `PathObl.move` of an accepted quiet or round-robin run: the run on the checked store whose
  writes are `ownV`'s `StepOK` (`StWrOKV`) is the real one (`vtimer_accG`; every write is an `IrqWr` word other
  than the current thread's `STATE`, which the run never writes: `irq_wr_nondec`, `stepOK_nondec`,
  `stepOKV_of_stepOK`), and `interp_gd` turns it into the run on `mguard` (`IsProg` [P]); the fire case a premise.

Premises (fields of `VtmEnt`): `ent` (`VexitEnt`'s, see `P2/AccessLvmOwn.lean`: [J] inv / lay / ntw / cs / aff /
curAff / cscCore / ksv / vin / vfar / nfar, [P] vlk: the glue holds `lock` of the bound VCPU); **[J] `iq`, `kr`,
`tab`**: the IRQ's state word, the kernel root word and the ASID table / pool words are aligned, in no region
(`IrqLay`'s, from P3 as in `irqLayK_of_slJAt` / `SlJAtZ.irqStNone`) and outside every VCPU (line vlift's `VcpuKs`
covers the state word, `TabNoV` / `VcpuTabOff` / `PoolObj` the table); **[J] `asid`** (P1 `AsidOff`, as
`IrqEntK.asid`). The fire case: `hF` / `hFm` (the timer interrupt's fire walk with the VM head, not done here).
-/
import Fl4Proofs.P2.AccessLvmTw
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV InVcpu VcpuGate RegionOKV UserOKV rpermV_of_own rpermV_vcpu
  wpermV_of_own' stepOKV_of_stepOK)
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}

/-- The current thread's bound VCPU (its `VCPU` word, what `vcpu::bound` reads). -/
def vOf (st : machine.Store S) [L : LawfulStore st] (s : S) : U64 :=
  L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)

/-- **The entry facts of `local_vm_timer_irq`** (module docstring) for the IRQ `irq` and the glue's notification
`n`, with the glue's locks `lk`. -/
structure VtmEnt (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (lk : S → U64 → Prop) (irq n : U64) (s : S) :
    Prop where
  ent : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk (vOf st s) n s
  iq : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i →
    Aligned (core.num.U64.wrapping_add (L.ksb s) i) ∧
      region K.toKLayout (core.num.U64.wrapping_add (L.ksb s) i) = .none ∧
      ¬ ∃ w, InVcpu K w (core.num.U64.wrapping_add (L.ksb s) i)
  kr : Aligned (krA (L := L) s) ∧ region K.toKLayout (krA (L := L) s) = .none ∧
    ¬ ∃ w, InVcpu K w (krA (L := L) s)
  tab : ∀ hi : U64, hi.val < 2048 →
    (Aligned (atAF (L.ksb s) hi) ∧ region K.toKLayout (atAF (L.ksb s) hi) = .none ∧
      ¬ ∃ w, InVcpu K w (atAF (L.ksb s) hi)) ∧
    ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      Aligned (peAF (L.mem s (atAF (L.ksb s) hi)) lo) ∧
        region K.toKLayout (peAF (L.mem s (atAF (L.ksb s) hi)) lo) = .none ∧
        ¬ ∃ w, InVcpu K w (peAF (L.mem s (atAF (L.ksb s) hi)) lo)
  asid : AsidOff (L := L) Ω Sg s

variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop}

/-- **An accepted VM-timer run has `irq < 128`** (`vtimer_split`: `irq ≤ irqn::MAX`). -/
theorem vtimer_irq_lt {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) : irq.val < 128 := by
  obtain ⟨mx, -, emx, hle, -⟩ := vtimer_split ar h
  rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
  have e := ok_inj_ff emx
  subst e
  scalar_tac

/-- The facts of an accepted run `vtimer_accG` needs beside the store: the bound VCPU (`vOf`), nonzero, and the
bound notification `n`. -/
theorem vtimer_bnd {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    vcpu.bound st s (L.curW s) = ok (vOf st s) ∧ vOf st s ≠ 0#u64 ∧ L.mem s (boundA (L.curW s)) = n := by
  obtain ⟨-, -, -, -, -, -, -, -, en, -, evr, -⟩ := vtimer_split ar h
  obtain ⟨v', ev', hv0, -⟩ := vm_running_true evr
  have hvb : vcpu.bound st s (L.curW s) = ok (vOf st s) := eq_of_spec_fd (vcpu.bound.spec (L := L) s _)
  rw [hvb] at ev'
  obtain rfl := ok_inj_ff ev'
  refine ⟨hvb, hv0, ?_⟩
  rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en
  exact ok_inj_ff en

/-- **`acc` of an accepted `local_vm_timer_irq`**, quiet or round-robin, under `ownV` (module docstring). -/
theorem vtimer_acc_own (hA : P0.ArchTotal ar) (hK : RegionOKV K) {s s' : S} {a a' : A} {irq n : U64}
    {p : localtimer.TimerIrqPlan}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s)
    (hF : IrqFire st ar s a → localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s))
      ar s a irq p n = ok (true, s', a'))
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq p n =
      ok (true, s', a') := by
  have hb := vtimer_irq_lt ar h
  obtain ⟨hvb, hv0, hbn⟩ := vtimer_bnd ar h
  have E := hE.ent
  have hI := E.inv
  have hL := E.lay
  exact vtimer_accG (gS := guard st (VexitRS K st lk s) (VexitWS K st lk s)) (R := VexitRS K st lk s)
    (W := VexitWS K st lk s) ar hA hI
    (fun hok w ha hw => ⟨ha, Or.inr (vexit_rd hK hI hL E.ntw E.cs E.aff hok.aff hok.core hw)⟩)
    (fun hok w ha hw _ => ⟨ha, Or.inr (wpermV_of_own' hK (irq_wr_own hI hL hok hw))⟩)
    (fun _ i hi => ⟨(hE.iq hb i hi).1,
      Or.inr (rpermV_of_own (hE.iq hb i hi).2.2 (rperm_none (hE.iq hb i hi).2.1 _))⟩)
    (fun _ => ⟨hL.domA, Or.inr (rpermV_of_own E.ksv.1 (rperm_none hL.dom _))⟩)
    (fun _ => ⟨hL.dtmA, Or.inr (rpermV_of_own E.ksv.2 (rperm_none hL.dtm _))⟩)
    (fun _ => ⟨hE.kr.1, Or.inr (rpermV_of_own hE.kr.2.2 (rperm_none hE.kr.2.1 _))⟩)
    (fun _ hi hhi => ⟨⟨(hE.tab hi hhi).1.1,
        Or.inr (rpermV_of_own (hE.tab hi hhi).1.2.2 (rperm_none (hE.tab hi hhi).1.2.1 _))⟩,
      fun lo hlo hne => ⟨((hE.tab hi hhi).2 lo hlo hne).1,
        Or.inr (rpermV_of_own ((hE.tab hi hhi).2 lo hlo hne).2.2 (rperm_none ((hE.tab hi hhi).2 lo hlo hne).2.1 _))⟩⟩)
    hE.asid hvb
    ⟨(E.vfar hv0).1.1, Or.inr (pending_rd hK (E.vin hv0) (E.vlk hv0))⟩
    (fun hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL E.ntw E.curAff hn
      exact ⟨q1, Or.inr q2⟩)
    (E.vfar hv0) (fun hn => E.nfar n hbn hn) hF h

/-- **`move` of an accepted `local_vm_timer_irq`**, quiet or round-robin, under `ownV` (module docstring). -/
theorem vtimer_move (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K) {m : U64 → U64}
    {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (Bool × S × A)} {p : SProg Bool}
    {irq n : U64} {pl : localtimer.TimerIrqPlan}
    (hF : IsProg F p)
    (eF : ∀ mm : machine.Store S, F ar mm = fun s a => localvm.handle_vm_timer_irq_local mm ar s a irq pl n)
    {s s' : S} {a a' : A}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s)
    (hFm : IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (lk s)
          (L.mem x) (L.mem y))) ar s a irq pl n = ok (true, s', a'))
    (h : localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s', a')) :
    localvm.handle_vm_timer_irq_local (mguard st
      (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (lk s)
        (L.mem x) (L.mem y))) ar s a irq pl n = ok (true, s', a') := by
  by_cases hf : IrqFire st ar s a
  · exact hFm hf
  obtain ⟨hvb, hv0, hbn⟩ := vtimer_bnd ar h
  have E := hE.ent
  have hI := E.inv
  have hL := E.lay
  have hg : localvm.handle_vm_timer_irq_local (gd st (fun _ => True) (StWrOKV st K m (L.cpu s) (lk s))) ar s a
      irq pl n = ok (true, s', a') :=
    vtimer_accG (gS := gd st (fun _ => True) (StWrOKV st K m (L.cpu s) (lk s))) (R := fun _ => True)
      (W := WAll (StWrOKV st K m (L.cpu s) (lk s))) ar hA hI (fun _ _ _ _ => trivial)
      (fun _ w ha hw hn x _ => stepOKV_of_stepOK hK
        (stepOK_nondec hK.base hU.base ha (irq_wr_nondec hK.base hI hL hw hn)))
      (fun _ _ _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
      (fun _ _ _ => ⟨trivial, fun _ _ _ => trivial⟩) hE.asid hvb trivial (fun _ => trivial)
      (E.vfar hv0) (fun hn => E.nfar n hbn hn) (fun h' => absurd h' hf) h
  have eP : ∀ mm : machine.Store S, localvm.handle_vm_timer_irq_local mm ar s a irq pl n = interp mm ar p s a := by
    intro mm
    have e1 := congrFun (congrFun (eF mm) s) a
    have e2 := congrFun (congrFun (hF A ar mm) s) a
    try simp only at e1
    rw [← e1]
    exact e2
  rw [eP] at hg
  rw [eP]
  exact interp_gd (R := fun _ => True) (P := StWrOKV st K m (L.cpu s) (lk s))
    (Q := fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
      (lk s) (L.mem x) (L.mem y)) (I := fun _ => True)
    (fun x q w x' _ hq hw => by
      rw [L.write_eq] at hw
      have e := ok_inj_ff hw
      subst e
      exact ⟨hq, trivial⟩) p s a _ trivial hg

end

end Fl4Proofs.P2

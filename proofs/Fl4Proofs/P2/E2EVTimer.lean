/-
P2 (line vlift, gen 3): **the two `MaxR` paths (`TCB_SetTimer`, the timer interrupt) lifted through `userV`**.

`MaxR` now carries `x ∉ K.user` (`P2/FootTimerSetOwn.lean`; neither timer path reads a user word, every producer
shows it from the region: `StLay.user` / `domU` / `dtmU`, `IrqLay.iqU` / `krU` / `tabU`). So at `userV K` the read
set excludes the VCPU data words by definition and route U (`E2EV.PathsV.ofPathsU`) applies without re-walking
either path:

* `maxR_noV`, `maxW_noV`, `stDec_noV`, `irqDec_noV`: the sets at `userV K` hold no VCPU data word (`MaxR` by
  definition; `MaxW` since `own` gives every VCPU word to the gate, `OwnMapV.own_vcpu`; `StDec` / `IrqDec` words lie
  in node / TCB regions, `RegionOKV.none`).
* **`set_timer_noVcpuRW`**, **`irq_noVcpuRW`** (`irq_localPath`), **`irqW_noVcpuRW`** (`irq_localPathW`),
  **`irqP_noVcpuRW`** (`irq_localPathP`): `NoVcpuRW` of the paths built at `userV K`, for any of their arguments —
  the `hW` premise of `PathsV.ofPathsU` / `PathsV.mix` / `serializable_e2eV_all` for these paths.
* The paths' `Pre` at `userV K` from the `K` one (`P2/E2EVTimerLay.lean`): `stLay_userV`, `irqLay_userV`, `stEnt_userV`, `stEntK_userV`,
  `irqEnt_userV`, `irqEntM_userV` (from `RegionOKV`, `VcpuKs` (derived in `P2/E2EVHeap.lean`), the kernel-state
  block's fit, `L.ksb s = K.ksb`, `TabNoV` for the ASID words, and `irq < 128` for the IRQ state word).

Premises: none new. The layout facts added to `StLay` / `IrqLay` are [J] like the rest of those structures
(user words are region `.none`, as `AccessIoOwn.IoLay.user`; the region-`.none` words the timer paths read are no
user words); at `userV K` they follow from the `K` ones by the lemmas above.
-/
import Fl4Proofs.P2.E2EVUser
import Fl4Proofs.P2.FootTimerSetLP
import Fl4Proofs.P2.FootTimerIrqLPP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld)

noncomputable section
open Classical

/-! ## The sets at `userV K` hold no VCPU data word -/

section sets
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {lk : S → U64 → Prop} {x : U64}

theorem maxR_noV (h : MaxR (userV K) st lk s x) : ¬ VData K x ∨ x ∈ K.user :=
  Or.inl fun hv => h.2.2 (Or.inr hv)

theorem maxW_noV (hK : RegionOKV K) (h : MaxW (userV K) st lk s x) : ¬ VData K x ∨ x ∈ K.user := by
  refine Or.inl fun ⟨v, hv, _⟩ => ?_
  have h2 := h.1
  unfold WPerm at h2
  rw [show OwnMap.own (userV K) = OwnMap.own K.toKLayout from rfl, own_vcpu hK hv] at h2
  exact h2

theorem stDec_noV (hK : RegionOKV K) {target : U64} (hE : StEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac target s)
    (hq : StDec st s x) : ¬ VData K x := by
  apply notVData_of_region' hK
  rw [← region_userV]
  rcases (hE.dec hq).2.2 with ⟨c, hc⟩ | ⟨t, ht, -⟩
  · rw [hc]; intro e; cases e
  · rw [ht]; intro e; cases e

theorem irqDec_noV (hK : RegionOKV K) {irq : U64} (hE : IrqEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq s)
    (hq : IrqDec st s x) : ¬ VData K x := by
  apply notVData_of_region' hK
  rw [← region_userV]
  obtain ⟨c, hc⟩ := (hE.dec hq).2.2
  rw [hc]; intro e; cases e

end sets

/-! ## `NoVcpuRW` of the two paths at `userV K` -/

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {target irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop}

/-- **`NoVcpuRW` of the `TCB_SetTimer` path at `userV K`.** -/
theorem set_timer_noVcpuRW (hKV : RegionOKV K) (n : I64) {p : SProg Bool} (hA : P0.ArchTotal ar)
    (hK : OwnMap.RegionOK (userV K)) (hUO : E2E.UserOK (userV K))
    (hp : IsProg (stBody S n target) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hmv : ∀ s a s1 a1, StEntK (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac target m s →
      localtimer.handle_set_timer_local st ar s a n target = ok (true, s1, a1) →
      localtimer.handle_set_timer_local (mguard st
        (fun x y => StepOK (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m)
          (· ∈ (userV K).user) (L.cpu s) (lk s) (L.mem x) (L.mem y))) ar s a n target = ok (true, s1, a1))
    (hro : E2E.ReadOnce st ar p (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)
      (StEntK (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac target m) (MaxR (userV K) st lk))
    (hEU : ∀ s b v, StEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac target s → b ∈ (userV K).user → Aligned b →
      StEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac target (L.wr s b v))
    (hlk : ∀ s b v, b ∈ (userV K).user → lk (L.wr s b v) = lk s)
    (hNU : ∀ s, StEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac target s → ∀ o : U64, o.val < 4288 →
      L.nodeAt s (L.cpu s) o ∉ (userV K).user) :
    NoVcpuRW K (set_timer_localPath ar n hA hK hUO hp hz hm hmv hro hEU hlk hNU) where
  rd _ _ _ hr := maxR_noV hr
  wr s _ hp hw := hw.elim (maxW_noV hKV) fun hd => Or.inl (stDec_noV hKV hp.ent hd)

variable {pl : localtimer.TimerIrqPlan} {p : SProg Bool}

/-- **`NoVcpuRW` of the timer-interrupt path at `userV K`** (`irq_localPath`, the fire case premises). -/
theorem irq_noVcpuRW (hKV : RegionOKV K) (hA : P0.ArchTotal ar) (hK : OwnMap.RegionOK (userV K))
    (hUO : E2E.UserOK (userV K))
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)
      (IrqEntM (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR (userV K) st lk))
    (hEU : ∀ s b v, IrqEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ (userV K).user → Aligned b →
      IrqEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ (userV K).user → lk (L.wr s b v) = lk s)
    (hF : ∀ s a s1 a1, IrqEntM (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR (userV K) st lk s) (MaxW (userV K) st lk s)) ar s a irq pl =
        ok (true, s1, a1))
    (hFm : ∀ s a s1 a1, IrqEntM (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (mguard st
        (fun x y => StepOK (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m)
          (· ∈ (userV K).user) (L.cpu s) (lk s) (L.mem x) (L.mem y))) ar s a irq pl = ok (true, s1, a1)) :
    NoVcpuRW K (irq_localPath ar hA hK hUO hp hz hm hro hEU hlk hF hFm) where
  rd _ _ _ hr := maxR_noV hr
  wr s _ hp hw := hw.elim (maxW_noV hKV) fun hd => Or.inl (irqDec_noV hKV hp.ent hd)

/-- **`NoVcpuRW` of `irq_localPathW` at `userV K`.** -/
theorem irqW_noVcpuRW (hKV : RegionOKV K) (hA : P0.ArchTotal ar) (hK : OwnMap.RegionOK (userV K))
    (hUO : E2E.UserOK (userV K))
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)
      (IrqEntM (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR (userV K) st lk))
    (hEU : ∀ s b v, IrqEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ (userV K).user → Aligned b →
      IrqEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ (userV K).user → lk (L.wr s b v) = lk s)
    (hFw : ∀ s a s1 a1, IrqEntM (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a →
      ¬ NoWake st s → localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR (userV K) st lk s) (MaxW (userV K) st lk s)) ar s a irq pl =
        ok (true, s1, a1))
    (hFmw : ∀ s a s1 a1, IrqEntM (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a →
      ¬ NoWake st s → localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (mguard st
        (fun x y => StepOK (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m)
          (· ∈ (userV K).user) (L.cpu s) (lk s) (L.mem x) (L.mem y))) ar s a irq pl = ok (true, s1, a1)) :
    NoVcpuRW K (irq_localPathW ar hA hK hUO hp hz hm hro hEU hlk hFw hFmw) where
  rd _ _ _ hr := maxR_noV hr
  wr s _ hp hw := hw.elim (maxW_noV hKV) fun hd => Or.inl (irqDec_noV hKV hp.ent hd)

/-- **`NoVcpuRW` of `irq_localPathP` (the waking fire case proved) at `userV K`.** -/
theorem irqP_noVcpuRW (hKV : RegionOKV K) (hA : P0.ArchTotal ar) (hK : OwnMap.RegionOK (userV K))
    (hUO : E2E.UserOK (userV K))
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)
      (IrqEntM (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR (userV K) st lk))
    (hEU : ∀ s b v, IrqEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ (userV K).user → Aligned b →
      IrqEnt (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ (userV K).user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) (hOL : ObjLay (userV K) H Rp)
    (hBA : ∀ s a, IrqEntM (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a → ¬ NoWake st s →
      ∃ U : Set U64, ∀ s2 a2 s3 a3, interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) →
        BufAt st T Cs H Sg Scs Z U s3)
    (hSwT : ∀ s, IrqEntM (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s →
      SwTailP st (guard st (MaxR (userV K) st lk s) (MaxW (userV K) st lk s)) ar T Cs Ω H Sg Rp Scs Nt Z Ac
        (MaxR (userV K) st lk s) s)
    (hSwTm : ∀ s, IrqEntM (userV K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s →
      SwTailP st (gd st (fun _ => True) (StWrOK st (userV K) m (L.cpu s) (lk s))) ar T Cs Ω H Sg Rp Scs Nt Z Ac
        (fun _ => True) s) :
    NoVcpuRW K (irq_localPathP ar hA hK hUO hp hz hm hro hEU hlk hPL hOL hBA hSwT hSwTm) where
  rd _ _ _ hr := maxR_noV hr
  wr s _ hp hw := hw.elim (maxW_noV hKV) fun hd => Or.inl (irqDec_noV hKV hp.ent hd)

end paths

end
end Fl4Proofs.P2.E2EV

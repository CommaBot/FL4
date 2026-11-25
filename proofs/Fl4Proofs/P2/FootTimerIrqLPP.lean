/-
# P2 (p2lf): the timer interrupt local path with the waking fire case proved

`irq_localPathP`: `irq_localPathW` (`P2/FootTimerIrqLPW`) with its waking-fire premises `hFw` / `hFmw` discharged by
`irq_acc_fire_wk` (`P2/FootTimerFireAk`) and `irq_move_fire_wk` (`P2/FootTimerFireMk`).

Premises: as `irq_localPathW` without `hFw` / `hFmw` (`hp` [P], `hz` [W], `hm` [P], `hro` [W], `IrqEnt`'s [J] parts,
`hEU` [J], `hlk` [P]), plus

* `hPL` [P] (`PlanLk lk pl`: the plan's notification / endpoint / reply locks are held — the lock discipline of the
  local path's plan);
* `hOL` [J] (`ObjLay K H Rp`: endpoints and replies lie in their object regions);
* `hBA` [P] (`BufAt` after `handle_interrupt` on a waking fire run: the woken thread's message buffer reads, from
  P1 `UserOK` at the entry and `IbFr` across `update_timestamp` / `handle_interrupt` — not yet derived);
* `hSwT` / `hSwTm` [P] (`SwTailP` on the `acc` / `move` guarded stores: the scheduler tail when the action is the
  woken thread — remaining work `aw_tail_sw`, see handoff p2lf gen8).
-/
import Fl4Proofs.P2.FootTimerFireMk
import Fl4Proofs.P2.FootTimerIrqLPW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Classical
open Fl4Proofs.P2.PathObl (guard mguard gd IsProg NoZero StepOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- **The timer interrupt is a local path, the waking fire case proved** (module docstring). -/
noncomputable def irq_localPathP (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR K st lk))
    (hEU : ∀ s b v, IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ K.user → Aligned b →
      IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) (hOL : ObjLay K H Rp)
    (hBA : ∀ s a, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a → ¬ NoWake st s →
      ∃ U : Set U64, ∀ s2 a2 s3 a3, interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) →
        BufAt st T Cs H Sg Scs Z U s3)
    (hSwT : ∀ s, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s →
      SwTailP st (guard st (MaxR K st lk s) (MaxW K st lk s)) ar T Cs Ω H Sg Rp Scs Nt Z Ac (MaxR K st lk s) s)
    (hSwTm : ∀ s, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s →
      SwTailP st (gd st (fun _ => True) (StWrOK st K m (L.cpu s) (lk s))) ar T Cs Ω H Sg Rp Scs Nt Z Ac
        (fun _ => True) s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  irq_localPathW ar hA hK hUO hp hz hm hro hEU hlk
    (fun s a s1 a1 hE hf hw h => by
      obtain ⟨U, hU⟩ := hBA s a hE hf hw
      exact irq_acc_fire_wk ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth hOL hPL hU (hSwT s hE) hf hw h)
    (fun s a s1 a1 hE hf hw h => by
      obtain ⟨U, hU⟩ := hBA s a hE hf hw
      exact irq_move_fire_wk ar hA hK hUO hp hE.k hE.ent.ly hE.ent.aff hE.ent.nth hOL hPL hU (hSwTm s hE) hf hw h)

end

end Fl4Proofs.P2

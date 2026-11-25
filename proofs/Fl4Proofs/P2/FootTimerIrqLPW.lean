/-
# P2 (p2lf): the timer interrupt local path, the fire case premises narrowed to waking signals

`irq_localPathW`: `irq_localPath` (`P2/FootTimerIrqObl`) with its fire-case premises `hF` / `hFm` discharged for every
run whose signal wakes nobody (`NoWake`: `irq_acc_fire_nw`, `irq_move_fire_nw`), so asked only of runs whose due
thread's bound notification wakes a thread (`hFw` / `hFmw`).

Premises: as `irq_localPath` (`hp` [P], `hz` [W], `hm` [P], `hro` [W], `IrqEnt`'s [J] parts, `hEU` [J], `hlk` [P]);
`hFw` / `hFmw` [P] (the waking fire case, the p2lf line's remaining step: `FootTimerFireWk` has the signal on the
guarded store; the scheduler tail with the woken thread, its ownership under `PlanLk` and `move` remain).
-/
import Fl4Proofs.P2.FootTimerFireOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Classical
open Fl4Proofs.P2.PathObl (guard mguard IsProg NoZero StepOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- **The timer interrupt is a local path, the fire case asked only of waking signals** (module docstring). -/
noncomputable def irq_localPathW (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR K st lk))
    (hEU : ∀ s b v, IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ K.user → Aligned b →
      IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hFw : ∀ s a s1 a1, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a → ¬ NoWake st s →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq pl = ok (true, s1, a1))
    (hFmw : ∀ s a s1 a1, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a → ¬ NoWake st s →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (mguard st
        (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
          (L.mem y))) ar s a irq pl = ok (true, s1, a1)) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  irq_localPath ar hA hK hUO hp hz hm hro hEU hlk
    (fun s a s1 a1 hE hf h => if hnw : NoWake st s then
        irq_acc_fire_nw ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth hf hnw h
      else hFw s a s1 a1 hE hf hnw h)
    (fun s a s1 a1 hE hf h => if hnw : NoWake st s then
        irq_move_fire_nw ar hA hK hUO hp hE.k hE.ent.ly hE.ent.nth hf hnw h
      else hFmw s a s1 a1 hE hf hnw h)

end

end Fl4Proofs.P2

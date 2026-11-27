/-
# P2: the timer interrupt's program premises discharged (line hpzg)

`irq_isProg`: `localtimer.handle_timer_irq_local` is the generated tree `R.localtimer.handle_timer_irq_local irq pl`
(`P2/ProgGenTm*.lean` on top of `P2/ProgGenIo*.lean` / `P2/ProgGenL*.lean`, from `xtask/scripts/gen_prog.py`) on
every store and Arch instance; `irq_noZero`: the tree has no `zero` / `clr` node. So the timer path's `hp` [P]
and `hz` [W] (`irq_localPath`, and p2lf's `irq_pathsJ3`) hold for that tree.

`irq_localPathG`: `irq_localPath` (`P2/FootTimerIrqObl.lean`) at that tree, without `hp` / `hz`. Remaining
premises (unchanged): `hm` [P], `hro` [W] (`ReadOnce`, now of the concrete tree), `hEU` [J], `hlk` [P],
`hF` / `hFm` (the fire case).
-/
import Fl4Proofs.P2.FootTimerIrqObl
import Fl4Proofs.P2.ProgGenTmTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl

/-- **`IsProg` for the timer interrupt body**: it is the generated tree, on every store and Arch instance. -/
theorem irq_isProg (S : Type) (irq : U64) (pl : localtimer.TimerIrqPlan) :
    IsProg (irqBody S irq pl) (R.localtimer.handle_timer_irq_local irq pl) := by
  intro A ar st
  funext s a
  rw [R.localtimer.handle_timer_irq_local_eq st ar, bind_proj3]

theorem irq_noZero (irq : U64) (pl : localtimer.TimerIrqPlan) :
    NoZero (R.localtimer.handle_timer_irq_local irq pl) :=
  R.localtimer.handle_timer_irq_local_nz irq pl

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}

/-- **The timer interrupt is a local path, `IsProg` / `NoZero` discharged** (module docstring). -/
noncomputable def irq_localPathG (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar (R.localtimer.handle_timer_irq_local irq pl) (OwnMap.cls K) (OwnMap.ko K m)
      (· ∈ K.user) (IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR K st lk))
    (hEU : ∀ s b v, IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ K.user → Aligned b →
      IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hF : ∀ s a s1 a1, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq pl = ok (true, s1, a1))
    (hFm : ∀ s a s1 a1, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (mguard st
        (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
          (L.mem y))) ar s a irq pl = ok (true, s1, a1)) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  irq_localPath ar hA hK hUO (irq_isProg S irq pl) (irq_noZero irq pl) hm hro hEU hlk hF hFm

end

end Fl4Proofs.P2

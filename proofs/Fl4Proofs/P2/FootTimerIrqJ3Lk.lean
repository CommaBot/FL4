/-
# P2 (line slhuf, gen 6): the timer interrupt local path with `hlk` from "the locks are kernel words"

Sibling of `irq_pathsJ3` / `irq_pathsJ3_startAt` (P2/FootTimerIrqJ3.lean, statements unchanged): the guarded lock
premise `hlk` [P] is replaced by **`hKD` [P]** (at every bundle state the glue's locks are determined by kernel
words, `KernDetAt`, P2/SlJLk.lean) and discharged by `hlk_of_kernelDet`, the same contract as the syscall path's
`sl_pathsKC5` (P2/SlJLk2.lean).

Premises of `irq_pathsJ3L`: `hA`, `hp` [P], `hz` [W], `hm` [P], `hro` [W], `hKD` [P], `hPL` [P].

-/
import Fl4Proofs.P2.FootTimerIrqJ3
import Fl4Proofs.P2.SlJLk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl

section path
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {irq : U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- **The timer interrupt path, `hlk` from kernel-word locks** (`irq_pathsJ3` with `hlk` discharged by
`hlk_of_kernelDet`). Premises: `hA`, `hp` [P], `hz` [W], `hm` [P], `hro` [W], `hKD` [P], `hPL` [P]. -/
noncomputable def irq_pathsJ3L (hA : P0.ArchTotal ar) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p)
    (hm : E2E.MasksWr st)
    (hro : ∀ K m, E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (IrqPreJ3 K st m)
      (MaxR K st lk))
    (hKD : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K lk s)
    (hPL : PlanLk lk pl) : E2E.Paths Unit :=
  irq_pathsJ3 ar hA hp hz hm hro (hlk_of_kernelDet hKD) hPL

/-- **`StartAt` for `irq_pathsJ3L`**. -/
theorem irq_pathsJ3L_startAt (hA : P0.ArchTotal ar) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p)
    (hm : E2E.MasksWr st)
    (hro : ∀ K m, E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (IrqPreJ3 K st m)
      (MaxR K st lk))
    (hKD : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K lk s)
    (hPL : PlanLk lk pl)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hM : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (irq_pathsJ3L ar hA hp hz hm hro hKD hPL () K m hK hU) c hs μ
      ((irq_pathsJ3L ar hA hp hz hm hro hKD hPL () K m hK hU).body σ a) :=
  irq_pathsJ3_startAt ar hA hp hz hm hro (hlk_of_kernelDet hKD) hPL K m hK hU a hJ hM hc hl hμ

end path

end Fl4Proofs.P2

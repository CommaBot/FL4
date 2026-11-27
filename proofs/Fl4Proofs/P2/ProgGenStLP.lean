/-
# P2: `TCB_SetTimer` with its program premises discharged (line hpzg)

`st_isProg`: `localtimer.handle_set_timer_local` is the generated tree `R.localtimer.handle_set_timer_local n
target` (`P2/ProgGenL*.lean`, from `xtask/scripts/gen_prog.py`) on every store and Arch instance; `st_noZero`: the
tree has no `zero` / `clr` node. So `set_timer_localPath`'s `hp` [P] and `hz` [W] hold for that tree.

`set_timer_localPathG`: `set_timer_localPath` (`P2/FootTimerSetLP.lean`) at that tree, without `hp` / `hz`.
Remaining premises (unchanged): `hm` [P], `hmv` [W], `hro` [W] (`ReadOnce`, now of the concrete tree), `hEU` [J],
`hlk` [P], `hNU` [J].
-/
import Fl4Proofs.P2.FootTimerSetLP
import Fl4Proofs.P2.ProgGenLTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl

/-- **`IsProg` for the `TCB_SetTimer` body**: it is the generated tree, on every store and Arch instance. -/
theorem st_isProg (S : Type) (n : I64) (target : U64) :
    IsProg (stBody S n target) (R.localtimer.handle_set_timer_local n target) := by
  intro A ar st
  funext s a
  rw [R.localtimer.handle_set_timer_local_eq st ar, bind_proj3]

theorem st_noZero (n : I64) (target : U64) : NoZero (R.localtimer.handle_set_timer_local n target) :=
  R.localtimer.handle_set_timer_local_nz n target

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {target : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) (n : I64) {lk : S → U64 → Prop}

/-- **`TCB_SetTimer` is a local path, `IsProg` / `NoZero` discharged** (module docstring). -/
noncomputable def set_timer_localPathG (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hm : E2E.MasksWr st)
    (hmv : ∀ s a s1 a1, StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m s →
      localtimer.handle_set_timer_local st ar s a n target = ok (true, s1, a1) →
      localtimer.handle_set_timer_local (mguard st
        (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
          (L.mem y))) ar s a n target = ok (true, s1, a1))
    (hro : E2E.ReadOnce st ar (R.localtimer.handle_set_timer_local n target) (OwnMap.cls K) (OwnMap.ko K m)
      (· ∈ K.user) (StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m) (MaxR K st lk))
    (hEU : ∀ s b v, StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s → b ∈ K.user → Aligned b →
      StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hNU : ∀ s, StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s → ∀ o : U64, o.val < 4288 →
      L.nodeAt s (L.cpu s) o ∉ K.user) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  set_timer_localPath ar n hA hK hUO (st_isProg S n target) (st_noZero n target) hm hmv hro hEU hlk hNU

end

end Fl4Proofs.P2

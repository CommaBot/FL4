/-
# P2 (line slhuf, gen 6): the syscall and VM ReplyRecv local paths with `hlk` from "the locks are kernel words"

Siblings of `sl_pathsKC4` / `sl_pathsKC4_startAt` (P2/SlJUB4.lean) and `rr_localPathJK` (P2/SlJUB5.lean), their
statements unchanged: the lock premise `hlk` [P] (a user-word write at a bundle state keeps the glue's locks) is
replaced by **`hKD` [P]**: at every bundle state the glue's locks are determined by kernel words (`KernDetAt`,
P2/SlJLk.lean), and discharged by `hlk_of_kernelDet` / `hlk_of_kernelDetK`. Why `Locks` stays abstract (the model's
lock state is `Serial.Cfg.lk`, ghost, indexed by object address; fl4-store's lock table is not in model memory and
does not record the holder): P2/SlJLk.lean's module docstring.

* **`sl_pathsKC5`**, `sl_pathsKC5_startAt`: premises `hSt`, `hA`, `hm`, `a0`, `hCs` [P] (satisfied by P3's sets:
  `SlJAt.hCs`, `hCs_of_sub`), `hKD` [P], `hpz` (ReadOnce [W], Pre `SlJAt ∧ SlQ`).
* **`rr_localPathJK2`**: premises `hA`, `hK`, `hU`, `hLA`, `hm`, `hCs` [P], `hKD` [P] (one layout), `hmA`, `hpz`.
-/
import Fl4Proofs.P2.SlJUB5
import Fl4Proofs.P2.SlJLk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Locks : S → U64 → Prop}
variable {A : Type}
variable {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **The syscall local path, `hlk` from kernel-word locks** (`sl_pathsKC4` with `hlk` discharged by
`hlk_of_kernelDet`). Premises: `hCs` [P] (P3's sets: `SlJAt.hCs`), `hKD` [P] (the glue's locks are determined by
kernel words at every bundle state), `hpz`, and `hSt`, `hA`, `hm`, `a0`. -/
noncomputable def sl_pathsKC5 (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hKD : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
        (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  sl_pathsKC4 (Locks := Locks) ar hSt hA hm a0 hCs (hlk_of_kernelDet hKD) hpz

/-- **`StartAt` for `sl_pathsKC5`**. -/
theorem sl_pathsKC5_startAt (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hKD : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
        (SlRS (st := st) K Locks))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : SlQ st ar Locks n found Cs Ω Sg Ac K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsKC5 (Locks := Locks) ar hSt hA hm a0 hCs hKD hpz () K m hK hU) c hs μ
      ((sl_pathsKC5 (Locks := Locks) ar hSt hA hm a0 hCs hKD hpz () K m hK hU).body σ a) :=
  sl_pathsKC4_startAt ar hSt hA hm a0 hCs (hlk_of_kernelDet hKD) hpz K m hK hU a hJ hq hc hl hμ

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} (ar : machine.Arch A)

/-- **The VM ReplyRecv local path, `hlk` from kernel-word locks** (`rr_localPathJK` with `hlk` discharged by
`hlk_of_kernelDetK`). Premises: `hCs` [P], `hKD` [P] (the glue's locks are determined by kernel words at every
bundle state of `K`), and `rr_localPathJK`'s `hA`, `hK`, `hU`, `hLA`, `hm`, `hmA`, `hpz`. -/
noncomputable def rr_localPathJK2 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {rptr ep : U64} (hm : E2E.MasksWr st) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hKD : ∀ s : S, SlJAt (L := L) K s → KernDetAt (L := L) K Locks s)
    (hmA : ∀ s, VmRRPreJ st ar K K.heap.tcbs Cs Ω Sg K.heap.scs K.heap.ntfns K.heap.scBits Ac Locks rptr ep s →
      ∀ d, K.heap d = some .tcb → m0 (fld d OwnMap.oAFFINITY) = L.mem s (fld d OwnMap.oAFFINITY))
    (hpz : ∃ p : SProg Bool, IsProg (rrBody S rptr ep) p ∧ NoZero p ∧
      ∀ s s' a r, VmRRPreJ st ar K K.heap.tcbs Cs Ω Sg K.heap.scs K.heap.ntfns K.heap.scBits Ac Locks rptr ep s →
        (∃ b, RrRep st rptr s b) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r → E2E.Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  rr_localPathJK ar hA hK hU hLA hm hCs (hlk_of_kernelDetK hKD) hmA hpz

end

end Fl4Proofs.P2.PathObl

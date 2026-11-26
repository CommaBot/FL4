/-
# P2 (line p3mc, gen 17): the family with sl's program the extracted tree (`fl4LocW11JB`)

## Why
The sl slot of `fl4LocW11JA` (`slSlotP3W6`, built by `SlJLay.sl_localPathK`) runs `p := hpz.choose` for
`hpz = ⟨R.syscall.handle_syscall_local n found, sl_isProg …, sl_noZero …, sl_hro …⟩` (`SlOnce.sl_pathsKC6`).
`Classical.choose` of that proof is some tree with `IsProg` / `NoZero` / `ReadOnce`, not provably the extracted tree,
and `tr` / `Once` are structural in the tree. So no fact proved about the extracted tree alone (p3mc16's foreign-thread
decline certificate `sl_fh_annV`) can be said of the slot's armed program.

## What
* **`LocalPath.withProg P p hI ho`**: `P` with its program replaced by `p`, given `IsProg P.F p` [P] (for the
  extracted tree: `sl_isProg`, a theorem) and `ReadOnce` of `p` at `P`'s own `Pre` / `RS` (for sl: `sl_hro2`, a
  theorem). Every other field (states, body function `F`, `Pre`, `RS`, `WS`, `DS`, `Locks`, obligations, side
  conditions) is `P`'s. `avoidV_withProg`, `avoidE_cutLiftV_withProg_rJ`: `AvoidV` / route-C `AvoidE` carry over (their
  `acc` / `dec` parts do not mention the program; `prog` by `IsProg.on`).
* **`slSlotB`**: `slSlotP3W6` with each path's program the extracted tree (`slSlotB_path`, by `rfl`). Same `Prem`.
* **`fl4LocB`**: `fl4LocA` with `sl := slSlotB` (the other six slots are `fl4LocA`'s, literally). **`allB`**,
  **`fl4LocW11JB`**: `fl4LocW11JA`'s construction (PTE cut and lift to `ownP`) over `fl4LocB`. **`fl4LocW11JB_eq`**:
  at every index that is not an sl index, `fl4LocW11JB i = fl4LocW11JA i` (`rfl`). **`fl4LocW11JB_sl`**: at an sl
  index where the record holds, the path is the cut lift of `slSlotB`'s path at the record.
* **`StartU2B` / `StartV2B`** [P]: `StartU2` / `StartV2` with the sl clause's glue (`GlueAt`) about `slSlotB`'s path,
  i.e. the armed program is the **extracted tree's** body at the glue's state. The other clauses are `StartU2`'s /
  `StartV2`'s (by the wildcard). This is the reading `IsProg` [P] always intended (`PathObl.IsProg`'s docstring: the
  tree is the body's own call tree), now stated: not a new premise but the same glue fact about the right program.
* **`startAt_slB`**, **`startAt_UNB`**: `StartU2B` gives `StartAt` of `fl4LocW11JB` (sl: from the glue's state, the
  chain's bundle `ChainOf.bun`, the entry conversions `SlEntU.toJ12` / `toJ11` / `toQ`, `qPs_of_convRN`; other
  indices: `startAt_UN` as it is). **`sl_v0_SFB`**: `sl_v0_SF` for `StartV2B`.

No premise added. No existing statement changed.
-/
import Fl4Proofs.P2.SlFhView
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD)

noncomputable section
open Classical

/-! ## Swapping a path's program -/

section swap
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
  {User : U64 → Prop}

/-- **`P` with its program replaced by `p`** (module docstring): `IsProg` of `p` for `P`'s body function and
`ReadOnce` of `p` at `P`'s entry states and read set; every other field is `P`'s. -/
def _root_.Fl4Proofs.P2.E2E.LocalPath.withProg (P : LocalPath own cls ko User) (p : SProg P.X) (hI : IsProg P.F p)
    (ho : @E2E.ReadOnce P.S P.A P.X P.st P.L P.ar p cls ko User P.Pre P.RS) : LocalPath own cls ko User where
  S := P.S
  A := P.A
  X := P.X
  st := P.st
  L := P.L
  ar := P.ar
  F := P.F
  p := p
  Acc := P.Acc
  Locks := P.Locks
  Pre := P.Pre
  RS := P.RS
  WS := P.WS
  DS := P.DS
  isProg := IsProg.on hI P.ar P.st _
  obl := P.obl
  side := P.side
  once := ho
  total := P.total
  masks := P.masks

theorem avoidV_withProg {K : KLayoutV} {P : LocalPath (OwnMap.own K.toKLayout) cls ko User} {p : SProg P.X}
    {hI : IsProg P.F p} {ho} (h : AvoidV K P) : AvoidV K (P.withProg p hI ho) :=
  ⟨h.acc, h.dec, IsProg.on hI _ _ _⟩

/-- **Route C: `AvoidE` of the restricted cut lift carries over to the program swap.** -/
theorem avoidE_cutLiftV_withProg_rJ {Kp : KLayoutP} {Ex : U64 → Prop} (hK : RegionOKV Kp.toKLayoutV)
    (hU : UserOKV Kp.toKLayoutV) (hko : ∀ x, VData Kp.toKLayoutV x → ko x = .free)
    {P : LocalPath (OwnMap.own Kp.toKLayout) cls ko (· ∈ Kp.user)} (W : AvoidV Kp.toKLayoutV P)
    {p : SProg P.X} {hI : IsProg P.F p} {ho} (W' : AvoidV Kp.toKLayoutV (P.withProg p hI ho))
    (h : AvoidE Ex ((LocalPath.cutLiftV hK hU hko P W).rJ Kp (fun b hb => Or.inl hb))) :
    AvoidE Ex ((LocalPath.cutLiftV hK hU hko (P.withProg p hI ho) W').rJ Kp (fun b hb => Or.inl hb)) :=
  ⟨h.acc, h.dec, IsProg.on hI _ _ _⟩

theorem cutLiftP_congr {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {hko : ∀ x, x ∈ K.ptes → ko x = .free}
    {P P' : LocalPath (ownV K.toKLayoutV) cls ko User} (e : P = P') (h : AvoidP K P) (h' : AvoidP K P') :
    LocalPath.cutLiftP hK hU hko P h = LocalPath.cutLiftP hK hU hko P' h' := by
  subst e; rfl

end swap

/-! ## The sl slot with the extracted tree, the family -/

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **syscall_local's slot with the extracted tree as its program** (module docstring). -/
def slSlotB : SlotC (SlArg S) where
  Prem := (slSlotP3W6 st ar hA hm hSt a0).Prem
  path i K m hK hU h := ((slSlotP3W6 st ar hA hm hSt a0).path i K m hK hU h).withProg
    (R.syscall.handle_syscall_local i.n i.found) (sl_isProg S i.n i.found)
    (sl_hro2 (Locks := i.Locks) (n := i.n) (found := i.found) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac)
      ar hSt hA hm a0 K.toKLayout m)
  Av i K m hK hU h := avoidV_withProg ((slSlotP3W6 st ar hA hm hSt a0).Av i K m hK hU h)

/-- **Only the program differs**: `slSlotB`'s path is `slSlotP3W6`'s with the extracted tree swapped in. -/
theorem slSlotB_path {i : SlArg S} {K : KLayoutV} {m : U64 → U64} (hK : RegionOKV K) (hU : UserOKV K)
    (h : (slSlotB st ar hA hm hSt a0).Prem i K m) :
    (slSlotB st ar hA hm hSt a0).path i K m hK hU h =
      ((slSlotP3W6 st ar hA hm hSt a0).path i K m hK hU h).withProg
        (R.syscall.handle_syscall_local i.n i.found) (sl_isProg S i.n i.found)
        (sl_hro2 (Locks := i.Locks) (n := i.n) (found := i.found) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac)
          ar hSt hA hm a0 K.toKLayout m) :=
  rfl

/-- **`fl4LocA` with sl's program the extracted tree.** -/
def fl4LocB : Fl4Loc (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) (VxArg S ⊕ VtArg S) where
  vmF := vmFSlotA st ar hA hm
  vmR := vmRSlotA st ar hA hm
  io := ioSlotP3W st ar hA hm
  st := stSlotP3W st ar hA hm
  irq := irqSlotP3W st ar hA hm
  sl := slSlotB st ar hA hm hSt a0
  vq := PathsV.sum ((vxSlotP3 st ar hA hm).fam (fl4Dflt st ar hm)) ((vtSlotA st ar hA hm).fam (fl4Dflt st ar hm))

/-- **`slSlotB`'s path at a record, restricted to `QPs` states, reads no PTE word** (`sl_avoidPJ_W6` carried over). -/
theorem sl_avoidAt_B (i : SlArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (slSlotB st ar hA hm hSt a0).Prem i K.toKLayoutV m) :
    AvoidP K (((slSlotB st ar hA hm hSt a0).liftAt i K.toKLayoutV m hK.base hU.base h).rJ K
      (fun b hb => Or.inl hb)) := by
  have h0 := sl_avoidPJ_W6 st ar hA hm hSt a0 i K m hK hU h
  rw [SlotC.lift_eq (fl4Dflt st ar hm) (slSlotP3W6 st ar hA hm hSt a0) h] at h0
  exact avoidE_cutLiftV_withProg_rJ (hI := sl_isProg S i.n i.found) hK.base hU.base _ _ _ h0

/-- **Every path of `fl4LocB`, restricted to `QPs` states, reads no PTE word** (`allA` for the new family). -/
theorem allB :
    ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K),
      AvoidP K ((((fl4LocB st ar hA hm hSt a0).paths (fl4Dflt st ar hm)) i K.toKLayoutV m hK.base hU.base).rJ K
        (fun b hb => Or.inl hb)) := by
  intro i K m hK hU
  cases i with
  | vmF j => exact allA st ar hA hm hSt a0 (.vmF j) K m hK hU
  | vmR j => exact allA st ar hA hm hSt a0 (.vmR j) K m hK hU
  | io j => exact allA st ar hA hm hSt a0 (.io j) K m hK hU
  | st j => exact allA st ar hA hm hSt a0 (.st j) K m hK hU
  | irq j => exact allA st ar hA hm hSt a0 (.irq j) K m hK hU
  | vq j => exact allA st ar hA hm hSt a0 (.vq j) K m hK hU
  | sl j =>
    by_cases hp : (slSlotB st ar hA hm hSt a0).Prem j K.toKLayoutV m
    · show AvoidP K (((slSlotB st ar hA hm hSt a0).lift (fl4Dflt st ar hm) j K.toKLayoutV m hK.base hU.base).rJ K
        (fun b hb => Or.inl hb))
      rw [SlotC.lift_eq (fl4Dflt st ar hm) (slSlotB st ar hA hm hSt a0) hp]
      exact sl_avoidAt_B st ar hA hm hSt a0 j K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotC.noPre (fl4Dflt st ar hm) _ hp)

/-- **`fl4LocB`'s eight paths, each restricted to `QPs` states, PTE-cut and lifted to `ownP`.** -/
def fl4LocW11JB : PathsP (Fl4IxW (S := S)) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _
    (allB st ar hA hm hSt a0 i K m hK hU)

/-- **Off the sl indices the new family is the old one** (by definition). -/
theorem fl4LocW11JB_eq (i : Fl4IxW (S := S)) (hi : ∀ j, i ≠ .sl j) :
    fl4LocW11JB st ar hA hm hSt a0 i = fl4LocW11JA st ar hA hm hSt a0 i := by
  cases i with
  | sl j => exact absurd rfl (hi j)
  | vmF j => rfl
  | vmR j => rfl
  | io j => rfl
  | st j => rfl
  | irq j => rfl
  | vq j => rfl

/-- **The sl path of the new family at a record**: the cut lift of `slSlotB`'s path. -/
theorem fl4LocW11JB_sl {j : SlArg S} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K}
    (h : (slSlotB st ar hA hm hSt a0).Prem j K.toKLayoutV m) :
    fl4LocW11JB st ar hA hm hSt a0 (.sl j) K m hK hU =
      LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m)
        (((slSlotB st ar hA hm hSt a0).liftAt j K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => Or.inl hb))
        (sl_avoidAt_B st ar hA hm hSt a0 j K m hK hU h) :=
  cutLiftP_congr (congrArg (fun P => LocalPath.rJ P K (fun b hb => Or.inl hb)) (SlotC.lift_eq _ _ h)) _ _

end slot

/-! ## The start facts with sl's glue about the extracted tree -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start facts of the new family** [P] (module docstring): `StartU2` with the sl clause's glue about
`slSlotB`'s path (the extracted tree's body at the glue's state); every other clause is `StartU2`'s. -/
def StartU2B (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .sl j => ∃ q0, (LkC j.Locks ∧ ∃ σ : S, (Ch σ ∧ SlEntU st ar arI AR MR j K.toKLayoutV.toKLayout σ) ∧
      ∀ h : (slSlotB st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV m,
        GlueAt ((slSlotB st ar hA (masksWr_plain st) L.total a0).liftAt j K.toKLayoutV m hK.base hU.base h)
          (fun σ' : S => σ' = σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | i => StartU2 st ar hA a0 arI AR MR Ch K m hK hU c hs q i

/-- **The start facts of the new family with the invocation summands** (`StartV2` with `StartU2B`). -/
def StartV2B (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S) → Prop
  | .inl i => StartU2B st ar hA a0 arI AR MR Ch K m hK hU c hs q i
  | .inr j => StartInvU3 st ar hA Ch K m hK hU c hs q j

variable {arI AR MR}

/-- **An sl start of the new family** (module docstring). -/
theorem startAt_slB (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} {s : Cfg U64 U64 U64 U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop}
    {q : SP} {j : SlArg S}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K s.mem)
    (h : StartU2B st ar hA a0 arI AR MR Ch K s.mem hK hU c hs q (.sl j)) :
    StartAt (fl4LocW11JB st ar hA (masksWr_plain st) L.total a0 (.sl j) K s.mem hK hU) c hs s.mem q := by
  obtain ⟨q0, ⟨hL, σ, ⟨hCσ, hEn⟩, hG⟩, rfl⟩ := h
  obtain ⟨σe, hC'⟩ := hC
  obtain ⟨s1, ⟨nv, hcv⟩, hk1⟩ := hE
  obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, B, -⟩ := hEn.ix
  have hR : (slSlotB st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV s.mem :=
    show K.toKLayoutV.vcpus = ∅ ∧ SlPremP6 st j K.toKLayoutV from
      ⟨nv, ⟨σ, ChainOf.bun hC' σ hCσ⟩, B.csLt, fun K' s _ => hL.kernDetAt K' s⟩
  obtain ⟨σ', a, e', hc, hl, hμ, rfl⟩ := hG hR
  subst e'
  have hJ : SlJAt (L := L) K.toKLayout σ' := ChainOf.bun hC' σ' hCσ
  have hrun := chain_run P hIoa hC' hCσ hEn.hct
  have hq : Fl4Proofs.P2.PathObl.SlQ st ar j.Locks j.n j.found j.Cs j.Ω j.Sg j.Ac K.toKLayout s.mem σ' :=
    ((hEn.toJ12 hA hrun).toJ11 hA).toQ hA hrun fun d hd => by
      obtain ⟨h1, h2⟩ := hJ.userOK.tcb d hd oAFFINITY (Or.inl rfl)
      exact (hμ _ h1 h2).symm
  have hk : L.ksb σ' = K.ksb := slJAt_ksb hJ
  have hμ' : ∀ x, Aligned x → x ∉ K.user → L.mem σ' x = s.mem x := hμ
  have hqp : QPs K st σ' := qPs_of_convRN (L := L) (L' := L) hcv nv ⟨σ', hJ⟩ hk1 hk hμ'
  have hc' : L.cpu σ' = c := hc
  rw [fl4LocW11JB_sl st ar hA (masksWr_plain st) L.total a0 hR]
  refine ⟨σ', a, ⟨⟨hJ, hq⟩, hqp⟩, hc, hl, hμ, ?_⟩
  refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
    (sl_avoidAt_B st ar hA (masksWr_plain st) L.total a0 j K s.mem hK hU hR) σ' a).symm
  show cutP _ _ _ _ c _ ∅ = cutP _ _ _ _ (L.cpu σ') _ ∅
  rw [hc']
  try rfl

/-- **`StartU2B` gives `StartAt` of the new family** (`startAt_UN` off sl, `startAt_slB` at sl). -/
theorem startAt_UNB (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} {s : Cfg U64 U64 U64 U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop}
    {q : SP} {i : Fl4IxW (S := S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K s.mem)
    (h : StartU2B st ar hA a0 arI AR MR Ch K s.mem hK hU c hs q i) :
    StartAt (fl4LocW11JB st ar hA (masksWr_plain st) L.total a0 i K s.mem hK hU) c hs s.mem q := by
  have nv : K.vcpus = ∅ := by
    obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
    exact nv
  cases i with
  | sl j => exact startAt_slB st ar hA a0 P hIoa hC hE h
  | vmF j =>
    exact startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE
      (startU_of_U2 st ar hA a0 hC nv (i := .vmF j) h)
  | vmR j =>
    exact startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE
      (startU_of_U2 st ar hA a0 hC nv (i := .vmR j) h)
  | io j =>
    exact startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE
      (startU_of_U2 st ar hA a0 hC nv (i := .io j) h)
  | st j =>
    exact startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE
      (startU_of_U2 st ar hA a0 hC nv (i := .st j) h)
  | irq j =>
    exact startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE
      (startU_of_U2 st ar hA a0 hC nv (i := .irq j) h)
  | vq j =>
    exact startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE
      (startU_of_U2 st ar hA a0 hC nv (i := .vq j) h)

/-- **The sl start fact of a chain gives `SlV0`** (`sl_v0_SF` for `StartV2B`). -/
theorem sl_v0_SFB (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    {ρ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : SlArg S}
    (h : StartV2B st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.inl (.sl j))) :
    SlV0 st K c ρ := by
  have h' : StartU2B st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.sl j) := h
  obtain ⟨q0, ⟨hL, σ, ⟨hCσ, hE⟩, hG⟩, -⟩ := h'
  obtain ⟨σe, hC'⟩ := hC
  obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, B, -⟩ := hE.ix
  have hR : (slSlotB st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV (view K.toKLayout c ρ) :=
    show K.toKLayoutV.vcpus = ∅ ∧ SlPremP6 st j K.toKLayoutV from
      ⟨nv, ⟨σ, ChainOf.bun hC' σ hCσ⟩, B.csLt, fun K' s _ => hL.kernDetAt K' s⟩
  obtain ⟨σ', a'', e', hc, -, hμ, -⟩ := hG hR
  subst e'
  exact ⟨_, hc, slJAt_ksb (ChainOf.bun hC' _ hCσ), fun x hx hu => hμ x hx hu,
    chain_act0 st P hIoa hC' hCσ hE.hct, chain_run P hIoa hC' hCσ hE.hct⟩

end start

end
end Fl4Proofs.P2.E2EP

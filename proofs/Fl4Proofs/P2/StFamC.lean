/-
# P2 (line p3mc, gen 18): the family with st's program the extracted tree too (`fl4LocW11JC`)

## Why
The st slot of `fl4LocW11JB` (`stSlotP3W`, built by `tm_localPathV`) runs `p := hpz.choose` for
`hpz = ⟨R.localtimer.handle_set_timer_local n target, st_isProg …, st_noZero …, st_hro …⟩` (`stSlot`,
E2EVFl4.lean), passed to `set_timer_localPathA` as `hpz.choose_spec`s. As for sl (P2/SlFamB), `Classical.choose` of
that proof is not provably the extracted tree, so no decline certificate about the extracted tree can be said of the
armed program.

## What
* **`st_hroC`**: `ReadOnce` of the extracted tree at the st path's own `Pre` (`SlJAt K ∧ Q`) and read set
  (`MaxR (userV K) st lk`), from `StOnce.st_hro` (a theorem) through the record's `pe`.
* **`stSlotC`**: `stSlotP3W` with each path `.withProg (R.localtimer.handle_set_timer_local i.n i.target)
  (st_isProg …) (st_hroC …)` (`stSlotC_path`, by `rfl`). Same `Prem`; `NoVcpuRW` carries over (its fields do not
  mention the program).
* **`fl4LocC`**: `fl4LocB` with `st := stSlotC` (the other six slots are `fl4LocB`'s, literally). **`allC`**,
  **`fl4LocW11JC`**: `fl4LocW11JB`'s construction over `fl4LocC`. **`fl4LocW11JC_eq`**: off the st indices,
  `fl4LocW11JC i = fl4LocW11JB i` (`rfl`). **`fl4LocW11JC_st`**: at an st record, the cut lift of `stSlotC`'s path.
* **`StartU2C` / `StartV2C`** [P]: `StartU2B` / `StartV2B` with only the st clause's glue (`GlueAt`) about `stSlotC`'s
  path. The st clause is `StartU2`'s st clause unfolded (`LkC`, then under `kd`: `StartP3W11T`'s st clause — the
  record `StPremW3B`, the entry `StEntJ7` at a chain state `σ`, and for every proof of `Cs < 64` the glue at `σ` — with
  the PTE cut) with the slot `stSlotP3W` replaced by `stSlotC`, whose `Prem`, states, `Pre`, sets and body function
  are `stSlotP3W`'s. So it is **the same claim about the extracted tree**: the armed program is the extracted tree's
  body at the glue's state (the reading `IsProg` [P] always stated), not a new premise.
* **`startAt_stC`**, **`startAt_UNC`**: `StartU2C` gives `StartAt` of `fl4LocW11JC` (st: from the glue's state, the
  chain's bundle `ChainOf.bun`, `StEntJ7.toJ` / `StEntJ4.q` for `Q`, `qPs_of_convRN`; other indices: `startAt_UNB`).
* **U16 over the new family**: `sl_annV_allC`, `vSafe_ioC`, `vmF_annV_allC`, `vmR_annV_allC` (U16's lemmas, by
  defeq off st), **`serializable_fl4_localU16C`** (`ExecWPRV10 (fl4LocW11JC ⊕ invocations) (¬IoIx) U16At StartV2C`).

## Premises of `serializable_fl4_localU16C` vs `serializable_fl4_localU16`
* **Changed: the family and the start fact.** `fl4LocW11JB` / `StartV2B` [P] become `fl4LocW11JC` / `StartV2C` [P]:
  the st slot's program and its glue are the extracted tree's. Every other slot, record and clause is the same.
  Nothing added or removed; `VSafe9` [J] still asked at st, irq, vq and invocation starts; `VSafe` [J] unchanged.
* U16 over `fl4LocW11JB` is not derived from it (an old execution arms `choose`'s st tree).

No existing statement changed.
-/
import Fl4Proofs.P2.E2EPU16
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

/-! ## The st slot with the extracted tree, the family -/

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

include hA hm in
/-- **`ReadOnce` of the extracted st tree at the st path's `Pre` / read set** (`st_hro` through `pe`). -/
theorem st_hroC (i : StArg S) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K)
    (h : K.vcpus = ∅ ∧ StPremK2B st i K m) :
    E2E.ReadOnce st ar (R.localtimer.handle_set_timer_local i.n i.target) (OwnMap.cls (userV K))
      (OwnMap.ko (userV K) m) (· ∈ (userV K).user) (fun s => SlJAt (L := L) K.toKLayout s ∧ i.Q K m s)
      (MaxR (userV K) st i.lk) := by
  have vf : VFacts L K := VFacts.ofEmpty h.1 h.2.bun.choose_spec
  intro s s' a r hp hAl hr
  exact st_hro ar i.n hA (regionOK_userV hK) (userOK_userV hK hU) hm s s' a r
    (stEntK_userV hK (vf.v hp.1).1 (vf.v hp.1).2.1 (slJAt_ksb hp.1) (h.2.pe s hp.1 hp.2)) hAl hr

/-- **`TCB_SetTimer`'s slot with the extracted tree as its program** (module docstring). -/
def stSlotC : SlotU (StArg S) where
  Prem := (stSlotP3W st ar hA hm).Prem
  path i K m hK hU h := ((stSlotP3W st ar hA hm).path i K m hK hU h).withProg
    (R.localtimer.handle_set_timer_local i.n i.target) (st_isProg S i.n i.target)
    (st_hroC st ar hA hm i K m hK hU h)
  W i K m hK hU h := ⟨((stSlotP3W st ar hA hm).W i K m hK hU h).rd, ((stSlotP3W st ar hA hm).W i K m hK hU h).wr⟩

/-- **Only the program differs**: `stSlotC`'s path is `stSlotP3W`'s with the extracted tree swapped in. -/
theorem stSlotC_path {i : StArg S} {K : KLayoutV} {m : U64 → U64} (hK : RegionOKV K) (hU : UserOKV K)
    (h : (stSlotC st ar hA hm).Prem i K m) :
    (stSlotC st ar hA hm).path i K m hK hU h =
      ((stSlotP3W st ar hA hm).path i K m hK hU h).withProg
        (R.localtimer.handle_set_timer_local i.n i.target) (st_isProg S i.n i.target)
        (st_hroC st ar hA hm i K m hK hU h) :=
  rfl

/-- **`fl4LocB` with st's program the extracted tree.** -/
def fl4LocC : Fl4Loc (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) (VxArg S ⊕ VtArg S) where
  vmF := vmFSlotA st ar hA hm
  vmR := vmRSlotA st ar hA hm
  io := ioSlotP3W st ar hA hm
  st := stSlotC st ar hA hm
  irq := irqSlotP3W st ar hA hm
  sl := slSlotB st ar hA hm hSt a0
  vq := PathsV.sum ((vxSlotP3 st ar hA hm).fam (fl4Dflt st ar hm)) ((vtSlotA st ar hA hm).fam (fl4Dflt st ar hm))

/-- **`stSlotC`'s path at a record, restricted to `QPs` states, reads no PTE word** (`stm_avoidPJ_path` carried
over). -/
theorem stC_avoidAt (i : StArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (stSlotC st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((stSlotC st ar hA hm).liftAt i K.toKLayoutV m hK.base hU.base h).rJ K
      (fun b hb => Or.inl hb)) := by
  have h0 := stm_avoidPJ_path st ar hA hm i K m hK hU h
  exact avoidE_liftAtV_rJ hK.base _ _ ⟨h0.acc, h0.dec, IsProg.on (st_isProg S i.n i.target) _ _ _⟩

/-- **Every path of `fl4LocC`, restricted to `QPs` states, reads no PTE word.** -/
theorem allC :
    ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K),
      AvoidP K ((((fl4LocC st ar hA hm hSt a0).paths (fl4Dflt st ar hm)) i K.toKLayoutV m hK.base hU.base).rJ K
        (fun b hb => Or.inl hb)) := by
  intro i K m hK hU
  cases i with
  | vmF j => exact allB st ar hA hm hSt a0 (.vmF j) K m hK hU
  | vmR j => exact allB st ar hA hm hSt a0 (.vmR j) K m hK hU
  | io j => exact allB st ar hA hm hSt a0 (.io j) K m hK hU
  | sl j => exact allB st ar hA hm hSt a0 (.sl j) K m hK hU
  | irq j => exact allB st ar hA hm hSt a0 (.irq j) K m hK hU
  | vq j => exact allB st ar hA hm hSt a0 (.vq j) K m hK hU
  | st j =>
    by_cases hp : (stSlotC st ar hA hm).Prem j K.toKLayoutV m
    · show AvoidP K (((stSlotC st ar hA hm).lift (fl4Dflt st ar hm) j K.toKLayoutV m hK.base hU.base).rJ K
        (fun b hb => Or.inl hb))
      rw [SlotU.lift_eq (fl4Dflt st ar hm) (stSlotC st ar hA hm) hp]
      exact stC_avoidAt st ar hA hm j K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)

/-- **`fl4LocC`'s eight paths, each restricted to `QPs` states, PTE-cut and lifted to `ownP`.** -/
def fl4LocW11JC : PathsP (Fl4IxW (S := S)) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _
    (allC st ar hA hm hSt a0 i K m hK hU)

/-- **Off the st indices the new family is U16's** (by definition). -/
theorem fl4LocW11JC_eq (i : Fl4IxW (S := S)) (hi : ∀ j, i ≠ .st j) :
    fl4LocW11JC st ar hA hm hSt a0 i = fl4LocW11JB st ar hA hm hSt a0 i := by
  cases i with
  | st j => exact absurd rfl (hi j)
  | vmF j => rfl
  | vmR j => rfl
  | io j => rfl
  | sl j => rfl
  | irq j => rfl
  | vq j => rfl

/-- **The st path of the new family at a record**: the cut lift of `stSlotC`'s path. -/
theorem fl4LocW11JC_st {j : StArg S} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K}
    (h : (stSlotC st ar hA hm).Prem j K.toKLayoutV m) :
    fl4LocW11JC st ar hA hm hSt a0 (.st j) K m hK hU =
      LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m)
        (((stSlotC st ar hA hm).liftAt j K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => Or.inl hb))
        (stC_avoidAt st ar hA hm j K m hK hU h) :=
  cutLiftP_congr (congrArg (fun P => LocalPath.rJ P K (fun b hb => Or.inl hb)) (SlotU.lift_eq _ _ h)) _ _

end slot

/-! ## The start facts with st's glue about the extracted tree -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start facts of the new family** [P] (module docstring): `StartU2B` with the st clause's glue about
`stSlotC`'s path (the extracted tree's body at the glue's state); the st clause is otherwise `StartU2`'s st clause
unfolded; every other clause is `StartU2B`'s. -/
def StartU2C (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .st j => LkC j.lk ∧ ((∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.lk s) →
      ∃ q0, (∃ h : StPremW3B st j K.toKLayoutV m, ∃ σ : S, (Ch σ ∧ StEntJ7 st j K.toKLayoutV σ) ∧
        ∀ hC : (∀ c ∈ j.Cs, c.val < 64),
          GlueAt ((stSlotC st ar hA (masksWr_plain st)).liftAt j K.toKLayoutV m hK.base hU.base
            (h.toA hC).toW3.toP3) (fun σ' : S => σ' = σ) c hs m q0) ∧
        q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅)
  | i => StartU2B st ar hA a0 arI AR MR Ch K m hK hU c hs q i

/-- **The start facts of the new family with the invocation summands** (`StartV2B` with `StartU2C`). -/
def StartV2C (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S) → Prop
  | .inl i => StartU2C st ar hA a0 arI AR MR Ch K m hK hU c hs q i
  | .inr j => StartInvU3 st ar hA Ch K m hK hU c hs q j

variable {arI AR MR}

/-- **The glue's state of an st start of the new family, with its facts** (used by `startAt_stC` and U17). -/
theorem stC_glue {Ch : S → Prop} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : StArg S}
    (h : StartU2C st ar hA a0 arI AR MR Ch K m hK hU c hs q (.st j)) :
    ∃ q0, (∃ hR : (stSlotC st ar hA (masksWr_plain st)).Prem j K.toKLayoutV m, ∃ σ : S,
        (Ch σ ∧ StEntJ7 st j K.toKLayoutV σ) ∧ StPremW3 st j K.toKLayoutV m ∧
        GlueAt ((stSlotC st ar hA (masksWr_plain st)).liftAt j K.toKLayoutV m hK.base hU.base hR)
          (fun σ' : S => σ' = σ) c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅ := by
  obtain ⟨hL, hG0⟩ := h
  obtain ⟨q0, ⟨h1, σ, ⟨hCσ, hE⟩, hG⟩, e⟩ := hG0 (fun s => hL.kernDetS _ s)
  have hCs : ∀ c ∈ j.Cs, c.val < 64 := by
    obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, Bz⟩ := hE.ix.ac
    exact fun c hc => Bz.j.kern.csLt c hc
  exact ⟨q0, ⟨(h1.toA hCs).toW3.toP3, σ, ⟨hCσ, hE⟩, (h1.toA hCs).toW3, hG hCs⟩, e⟩

/-- **An st start of the new family** (module docstring). -/
theorem startAt_stC {Ch : S → Prop}
    {K : KLayoutP} {s : Cfg U64 U64 U64 U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop}
    {q : SP} {j : StArg S}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K s.mem)
    (h : StartU2C st ar hA a0 arI AR MR Ch K s.mem hK hU c hs q (.st j)) :
    StartAt (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0 (.st j) K s.mem hK hU) c hs s.mem q := by
  obtain ⟨q0, ⟨hR, σ, ⟨hCσ, hEn⟩, hW3, hG⟩, rfl⟩ := stC_glue st ar hA a0 h
  obtain ⟨σe, hC'⟩ := hC
  obtain ⟨s1, ⟨nv, hcv⟩, hk1⟩ := hE
  obtain ⟨σ', a, e', hc, hl, hμ, rfl⟩ := hG
  subst e'
  have hJ : SlJAt (L := L) K.toKLayout σ' := ChainOf.bun hC' σ' hCσ
  have hμ' : ∀ x, Aligned x → x ∉ K.user → L.mem σ' x = s.mem x := hμ
  have hq : j.Q K.toKLayoutV s.mem σ' := (StEntJ7.toJ st hEn).q st hW3 hμ'
  have hk : L.ksb σ' = K.ksb := slJAt_ksb hJ
  have hqp : QPs K st σ' := qPs_of_convRN (L := L) (L' := L) hcv nv ⟨σ', hJ⟩ hk1 hk hμ'
  have hc' : L.cpu σ' = c := hc
  rw [fl4LocW11JC_st st ar hA (masksWr_plain st) L.total a0 hR]
  refine ⟨σ', a, ⟨⟨hJ, hq⟩, hqp⟩, hc, hl, hμ, ?_⟩
  refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
    (stC_avoidAt st ar hA (masksWr_plain st) j K s.mem hK hU hR) σ' a).symm
  show cutP _ _ _ _ c _ ∅ = cutP _ _ _ _ (L.cpu σ') _ ∅
  rw [hc']
  try rfl

/-- **`startAt_UNC` on the re-based platform** (gen 54, in place: `hRun : ChainRun` for `P` / `hIoa`). -/
theorem startAt_UNC_C (hRun : ChainRun st arI AR MR) {Ch : S → Prop}
    {K : KLayoutP} {s : Cfg U64 U64 U64 U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop}
    {q : SP} {i : Fl4IxW (S := S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K s.mem)
    (h : StartU2C st ar hA a0 arI AR MR Ch K s.mem hK hU c hs q i) :
    StartAt (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0 i K s.mem hK hU) c hs s.mem q := by
  cases i with
  | st j => exact startAt_stC st ar hA a0 hC hE h
  | sl j => exact startAt_UNB_C st ar hA a0 hRun (i := .sl j) hC hE h
  | vmF j => exact startAt_UNB_C st ar hA a0 hRun (i := .vmF j) hC hE h
  | vmR j => exact startAt_UNB_C st ar hA a0 hRun (i := .vmR j) hC hE h
  | io j => exact startAt_UNB_C st ar hA a0 hRun (i := .io j) hC hE h
  | irq j => exact startAt_UNB_C st ar hA a0 hRun (i := .irq j) hC hE h
  | vq j => exact startAt_UNB_C st ar hA a0 hRun (i := .vq j) hC hE h

end start

/-! ## U16 over the new family -/

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **`sl_annV_allC` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem sl_annV_allC_C (P : LocPlatCR st arI AR MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : SlAllAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact sl_annV_allB_C st ar hA a0 P (hK := hK) (hU := hU) (i := .inl (.sl j)) hC hE hsf hM hV hf
  all_goals exact False.elim hf

/-- **The io starts' `VSafe` over the new family** (`vSafe_ioB`). -/
theorem vSafe_ioC {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (hM : MapsP K s)
    (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) (hi : IoIx (S := S) i) :
    VSafe (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st)))) s K c k hK hU ρ i := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hi
  · exact False.elim hi
  · exact vSafe_ioB st ar hA a0 (i := .inl (.io j)) hM hV hi
  all_goals exact False.elim hi

/-- **`vmF_annV_allC` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem vmF_annV_allC_C (P : LocPlatCR st arI AR MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) (hf : VmFIx (S := S) i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact vmF_annV_allB_C st ar hA a0 P (hK := hK) (hU := hU) (i := .inl (.vmF j)) hC hE hsf hM hV hf
  all_goals exact False.elim hf

/-- **`vmR_annV_allC` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem vmR_annV_allC_C (P : LocPlatCR st arI AR MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) (hf : VmRIx (S := S) i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact vmR_annV_allB_C st ar hA a0 P (hK := hK) (hU := hU) (i := .inl (.vmR j)) hC hE hsf hM hV hf
  all_goals exact False.elim hf

end all

end
end Fl4Proofs.P2.E2EP

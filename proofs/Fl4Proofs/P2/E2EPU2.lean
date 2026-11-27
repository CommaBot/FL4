/-
# P2 (line unify, gen 2): every slot in one family, no [W] — `serializable_fl4_localU1`

gen 1's `serializable_fl4_localU1W` (P2/E2EPU1W.lean) has two [W] premises, `AvInvW` / `AvCMW`: PTE avoidance of
the cut `ownV` lifts of invj's `invSlotW` (CNodeDelete, no PTE lock) and slhuf's `cmSlotW2` (Copy / Mint) at `QPs`
states, for every layout. As stated they are not provable (P2/E2EPU2D.lean module docstring): the paths' trees are
choices (`hpz.choose`), so the program premise on the cut set's alternatives is out of reach; and for the CNodeDelete
path `QPs` lets an upper page-table entry be a "PTE word" (false at such unreachable layouts: a stale-mapped frame
cap's walk reads it). Neither is a counterexample at a reachable start. This module replaces the two slots:

* **`invPathVU`** / **`cmPathVU`**: the paths with the explicit tree (`inv_pathDelE` / `inv_pathCME`), restricted
  to **`QU`** (`QPs` and pte's reachability convention `CvP`), lifted to `ownV` by route C (`cutLiftV`);
* **`invAvU`** / **`cmAvU`**: their `AvoidP`, **proved** (`avoidE_delE` / `avoidE_cmE` through
  `avoidE_cutLiftV_empty`; no premise);
* **`invSlotU`** / **`cmSlotU`**: the `ownP` slots (`cutLiftP`, `LocalPath.void` where `InvPremW` fails);
* **`InvStartU2`** / **`CMStartU2`** [P]: the slots' start facts, as gen 1's `InvStartU` / `CMStartU` (record
  `InvPremW` and `GlueAt` [P] with `InvQF` / `InvQCMW`; the armed program the cut of the `ownV` program);
  **`invStartU2_at`** / **`cmStartU2_at`**: `StartAt` from the chain and the epoch data (`QPs` by
  `qPs_of_convR`, `CvP` from the epoch memory: gate words by the memory link and `gateW_of_region`, as invj's
  `delPteStart_at`);
* **`serializable_fl4_localU1`**: `serializable_fl4_localU1G` at
  `LQ := (delPteSlot ⊕ invSlotU) ⊕ cmSlotU` — the eight W11 slots (PJ12 with `yb`), the mapped-frame Delete slot,
  the CNodeDelete slot and the Copy / Mint slot. **No [W].** Premises: exactly U1D's plus the two invocation
  slots' own [P]s (`InvPremW.lk` [P] — `nv` / `bunS` are records the sat lemmas build — and `GlueAt` [P]);
* satisfiability: **`invStartU2_sat`** / **`cmStartU2_sat`** (gen 1's `invStartU_sat` / `cmStartU_sat` for the
  new start facts, same inputs: `invStartW_sat` / `cmStartW_sat2`, `m := L.mem s`).

No named premise beyond those. New module; no existing statement changes.
-/
import Fl4Proofs.P2.E2EPU2C
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The CNodeDelete (no PTE lock) path under `ownV`**: `inv_pathDelE` restricted to `QU`, route-C lifted. -/
noncomputable def invPathVU (j : InvArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : InvPremW st j K.toKLayoutV m) :
    LocalPath (ownV K.toKLayoutV) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  LocalPath.cutLiftV hK.base hU.base (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv m)
    ((inv_pathDelE (Cs := j.Cs) (Ω := j.Ω) (Sg := j.Sg) (Ac := j.Ac) (Locks := j.Locks) ar hA j.number j.p hm
      (h.hCs st) h.lk K.toKLayout m hK.base.base hU.base.base).restrQ (fun s => QU st K s)
      (fun _ _ _ _ h hb ha => qU_wr h hb ha))
    (avoidV_restrQ (avoidV_nv h.nv _ (inv_noZero j.number j.p)))

/-- **The Copy / Mint path under `ownV`**: `inv_pathCME` restricted to `QU`, route-C lifted. -/
noncomputable def cmPathVU (j : InvArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : InvPremW st j K.toKLayoutV m) :
    LocalPath (ownV K.toKLayoutV) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  LocalPath.cutLiftV hK.base hU.base (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv m)
    ((inv_pathCME (Cs := j.Cs) (Ω := j.Ω) (Sg := j.Sg) (Ac := j.Ac) (Locks := j.Locks) ar hA j.number j.p hm
      (h.hCs st) h.lk K.toKLayout m hK.base.base hU.base.base).restrQ (fun s => QU st K s)
      (fun _ _ _ _ h hb ha => qU_wr h hb ha))
    (avoidV_restrQ (avoidV_nv h.nv _ (inv_noZero j.number j.p)))

/-- **`AvoidP` of the CNodeDelete path** (proved; gen 1's `AvInvW` for the explicit-tree, `QU`-restricted path). -/
theorem invAvU (j : InvArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : InvPremW st j K.toKLayoutV m) : AvoidP K (invPathVU st ar hA hm j K m hK hU h) :=
  avoidE_cutLiftV_empty hK.base hU.base h.nv _ _ _ (avoidE_delE ar hA j.number j.p hm (h.hCs st) h.lk K m hK hU)

/-- **`AvoidP` of the Copy / Mint path** (proved; gen 1's `AvCMW` for the explicit-tree, `QU`-restricted path). -/
theorem cmAvU (j : InvArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : InvPremW st j K.toKLayoutV m) : AvoidP K (cmPathVU st ar hA hm j K m hK hU h) :=
  avoidE_cutLiftV_empty hK.base hU.base h.nv _ _ _ (avoidE_cmE ar hA j.number j.p hm (h.hCs st) h.lk K m hK hU)

/-- **The CNodeDelete (no PTE lock) slot under `ownP`**. -/
noncomputable def invSlotU : PathsP (InvArg S) :=
  fun j K m hK hU => if h : InvPremW st j K.toKLayoutV m then
      LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (invAvU st ar hA hm j K m hK hU h)
    else E2EV.LocalPath.void (fl4Dflt st ar hm)
      (fun x hx => Fl4Proofs.P2.ko_aligned hK.base.base hU.base.base x hx)

/-- **The Copy / Mint slot under `ownP`**. -/
noncomputable def cmSlotU : PathsP (InvArg S) :=
  fun j K m hK hU => if h : InvPremW st j K.toKLayoutV m then
      LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (cmAvU st ar hA hm j K m hK hU h)
    else E2EV.LocalPath.void (fl4Dflt st ar hm)
      (fun x hx => Fl4Proofs.P2.ko_aligned hK.base.base hU.base.base x hx)

theorem invSlotU_pos {j : InvArg S} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K}
    (h : InvPremW st j K.toKLayoutV m) :
    invSlotU st ar hA hm j K m hK hU =
      LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (invAvU st ar hA hm j K m hK hU h) :=
  dif_pos h

theorem cmSlotU_pos {j : InvArg S} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K}
    (h : InvPremW st j K.toKLayoutV m) :
    cmSlotU st ar hA hm j K m hK hU =
      LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (cmAvU st ar hA hm j K m hK hU h) :=
  dif_pos h

/-- **The CNodeDelete slot's start fact** [P]: the record and `GlueAt` with `InvQF` (as gen 1's `InvStartU`). -/
def InvStartU2 (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : InvArg S) : Prop :=
  ∃ q0, (∃ h : InvPremW st j K.toKLayoutV m,
      GlueAt (invPathVU st ar hA hm j K m hK hU h)
        (fun σ : S => Ch σ ∧ InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m σ) c hs m q0) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

/-- **The Copy / Mint slot's start fact** [P]: the record and `GlueAt` with `InvQCMW` (as gen 1's `CMStartU`). -/
def CMStartU2 (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : InvArg S) : Prop :=
  ∃ q0, (∃ h : InvPremW st j K.toKLayoutV m,
      GlueAt (cmPathVU st ar hA hm j K m hK hU h)
        (fun σ : S => Ch σ ∧ InvQCMW st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m σ) c hs m q0) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- `QU` at a glue start state from the chain's bundle, the epoch data and the memory link. -/
theorem qU_start {K : KLayoutP} {s : Cfg U64 U64 U64 U64} {σ : S}
    (hσe : ∃ σe, SlJAt (L := L) K.toKLayout σe) (hJ : SlJAt (L := L) K.toKLayout σ)
    (hE : ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x)
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = s.mem x) : QU st K σ := by
  obtain ⟨s1, ⟨nv, hcv⟩, hk1⟩ := hE
  refine ⟨qPs_of_convR hcv nv hσe hk1 (slJAt_ksb (L := L) hJ) (fun x hx hu => hμ x hx hu), s1.mem, hcv,
    fun w hr hp hu ha => ?_⟩
  exact (hμ w ha hu).trans (hk1 w (gateW_of_region hr (by rw [hcv]; exact hp) nv))

/-- **`StartAt` of the CNodeDelete slot under `ownP`** from its start fact, the chain and the epoch data. -/
theorem invStartU2_at [Fl4Proofs.P1.PlainStore st]
    {Ch : S → Prop} {K : KLayoutP} {s : Cfg U64 U64 U64 U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : InvArg S}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (hE : ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x)
    (h : InvStartU2 st ar hA hm Ch K s.mem hK hU c hs q j) :
    StartAt (invSlotU st ar hA hm j K s.mem hK hU) c hs s.mem q := by
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  obtain ⟨q0, ⟨h, σ, a, he, hc, hl, hμ, e⟩, rfl⟩ := h
  have hJ := ChainOf.bun hC' σ he.1
  have hq : QU st K σ :=
    qU_start st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
  rw [invSlotU_pos st ar hA hm h]
  refine ⟨σ, a, ⟨⟨hJ, he.2⟩, hq⟩, hc, hl, hμ, ?_⟩
  refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ (invAvU st ar hA hm j K s.mem hK hU h)
    σ a).symm
  change _ = cutP _ _ _ _ ((invPathVU st ar hA hm j K s.mem hK hU h).L.cpu σ)
    ((invPathVU st ar hA hm j K s.mem hK hU h).body σ a) ∅
  rw [hc, ← e]

/-- **`StartAt` of the Copy / Mint slot under `ownP`** from its start fact, the chain and the epoch data. -/
theorem cmStartU2_at [Fl4Proofs.P1.PlainStore st]
    {Ch : S → Prop} {K : KLayoutP} {s : Cfg U64 U64 U64 U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : InvArg S}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (hE : ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x)
    (h : CMStartU2 st ar hA hm Ch K s.mem hK hU c hs q j) :
    StartAt (cmSlotU st ar hA hm j K s.mem hK hU) c hs s.mem q := by
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  obtain ⟨q0, ⟨h, σ, a, he, hc, hl, hμ, e⟩, rfl⟩ := h
  have hJ := ChainOf.bun hC' σ he.1
  have hq : QU st K σ :=
    qU_start st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
  rw [cmSlotU_pos st ar hA hm h]
  refine ⟨σ, a, ⟨⟨hJ, he.2⟩, hq⟩, hc, hl, hμ, ?_⟩
  refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ (cmAvU st ar hA hm j K s.mem hK hU h)
    σ a).symm
  change _ = cutP _ _ _ _ ((cmPathVU st ar hA hm j K s.mem hK hU h).L.cpu σ)
    ((cmPathVU st ar hA hm j K s.mem hK hU h).body σ a) ∅
  rw [hc, ← e]

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The three invocation summands' start facts** (`(delPte ⊕ CNodeDelete) ⊕ Copy/Mint`). -/
def StartInvU2 (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : (InvArg S ⊕ InvArg S) ⊕ InvArg S → Prop
  | .inl (.inl j) => DelPteStart st ar hA hm Ch K m hK hU c hs q j
  | .inl (.inr j) => InvStartU2 st ar hA hm Ch K m hK hU c hs q j
  | .inr j => CMStartU2 st ar hA hm Ch K m hK hU c hs q j

end top

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The CNodeDelete slot's start fact holds at every chain state planning a CNodeDelete with no PTE lock**
(gen 1's `invStartU_sat` for `InvStartU2`). -/
theorem invStartU2_sat (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S}
    {K : KLayoutP} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    (hK : RegionOKP K) (hU : UserOKP K)
    {s : S} (hs : Ch s) (hct : NonIdle st arI AR MR s) {n : I64} {p : localinv.Plan}
    (hp : localinv.plan st s n = ok (some p)) (harm : InvArm st p s) (a : A) :
    ∃ Ac : Set U64, ∀ j : InvArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac → j.p = p → j.Locks = planLocks p →
      ∃ q, InvStartU2 st ar hA hm Ch K (L.mem s) hK hU (L.cpu s) (j.Locks s) q j := by
  obtain ⟨Ac, H⟩ := invStartW_sat (K := K.toKLayoutV) st P hIoa hC nv hs hct hp harm
  refine ⟨Ac, fun j e1 e2 e3 e4 e5 e6 => ?_⟩
  obtain ⟨h, hQ⟩ := H j e1 e2 e3 e4 e5 e6
  exact ⟨_, _, ⟨h, s, a, ⟨hs, hQ⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

/-- **The Copy / Mint slot's start fact holds at every chain state planning a CNodeCopy / CNodeMint** (gen 1's
`cmStartU_sat` for `CMStartU2`). -/
theorem cmStartU2_sat (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S}
    {K : KLayoutP} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    (hK : RegionOKP K) (hU : UserOKP K)
    {s : S} (hs : Ch s) (hct : NonIdle st arI AR MR s) {n : I64} {p : localinv.Plan}
    (hp : localinv.plan st s n = ok (some p)) (harm : InvCMArm st s) (a : A) :
    ∃ Ac : Set U64, ∀ j : InvArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac → j.p = p → j.Locks = planLocks p →
      ∃ q, CMStartU2 st ar hA hm Ch K (L.mem s) hK hU (L.cpu s) (j.Locks s) q j := by
  obtain ⟨Ac, H⟩ := cmStartW_sat2 (K := K.toKLayoutV) st P hIoa hC nv hs hct hp harm
  refine ⟨Ac, fun j e1 e2 e3 e4 e5 e6 => ?_⟩
  obtain ⟨h, hQ⟩ := H j e1 e2 e3 e4 e5 e6
  exact ⟨_, _, ⟨h, s, a, ⟨hs, hQ⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

end sat

end
end Fl4Proofs.P2.E2EP

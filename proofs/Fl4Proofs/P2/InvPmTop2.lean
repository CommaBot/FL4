/-
# P2 (line pte, generation 11): the PageMap slot with `pr`, `dec`, `ra`, `ro` proved and `uf` reduced

`serializable_fl4_localW11PRIPm` (`P2/InvPmTop.lean`) took the bundle `PmObl` (seven fields). Here, at the start
fact narrowed by the plan's lookup (`PmQF = PmQ ∧ InvLk`, `P2/InvPmDec.lean`; satisfiable: `pmQF_of_plan`, and
the leaf half by `pm_leaf_locked`, whose hypotheses `PmPreF` implies):

* `pr`, `dec`, `ra`, `ro` are theorems (`pm_prune`, `pm_dec`, `pm_ra`, `pm_ro`, `P2/InvPmDec.lean`);
* **`pm_huf`**: `uf` from three smaller premises, the ones the CNode arm's `hufQL_of` (`P2/InvHuf.lean`) takes:
  [J] `iw` (`IoPre` survives a user-word write at a bundle state; `io_pathsKQ`'s `hIw`), [J] `pdw` (the plan
  `InvPlanD` survives it: `plan_with`'s PageMap arm reads the slot cap, the `extra[0]` cap, `R10` and the page-table
  walk — no user word, but P3 does not export that for the paging-structure words, as for `hufQL_of`'s `hPDw`) and
  [P] `lk` (the glue's locks are determined by kernel words, `hlk_of_kernelDetU`); `SlJAt`, `IoQ`, `PmArm`, the
  plan's locks, `InvLk` (`invLk_wr`), `GateEp` and the sets `PmRS` / `PmWS` / `IoDS` (`ownP` reads no user word:
  `own` by `E2E.ownDep`, no VCPU, a PTE word's owner is fixed) are proved;
* `PmObl2` (what is left: [W] `acc`, [W] `mv`, and `iw`, `pdw`, `lk`), `pmPathsF`, `StartPmF`, **`pm_hSFQF`**,
  **`serializable_fl4_localW11PRIPm2`**.

Premises of `serializable_fl4_localW11PRIPm2` beyond `serializable_fl4_localW11PR`'s: `B : PmObl2` — [W] `acc`,
[W] `mv` (the decode block on the guarded / move-checked store), [J] `iw`, [J] `pdw`, [P] `lk`.
No existing statement or file changed.
-/
import Fl4Proofs.P2.InvPmDec
import Fl4Proofs.P2.InvPmTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

section huf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

variable (st) in
/-- [J] **`IoPre` survives a user-word write** at a bundle state (`io_pathsKQ`'s / `hufQL_of`'s `hIw`). -/
def PmIw (Cs Ω Sg Ac : Set U64) : Prop :=
  ∀ (K : OwnMap.KLayout) s b v, SlJAt (L := L) K s →
    IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s →
    b ∈ K.user → Aligned b →
    IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac (L.wr s b v)

variable (st) in
/-- [J] **The PageMap plan survives a user-word write** at a `PmPreF` state (`hufQL_of`'s `hPDw` for this arm). -/
def PmPdw (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop :=
  ∀ (j : I64 × localinv.Plan) (K : KLayoutP) m s b v, PmPreF st Cs Ω Sg Ac Locks j.2 K m s → b ∈ K.user →
    Aligned b → InvPlanD st j.2 (L.wr s b v)

variable (st) in
/-- [P] **The glue's locks are not changed by a user-word write** (`hufQL_of`'s `hlk`). -/
def PmLk (Locks : S → U64 → Prop) : Prop :=
  ∀ (K : OwnMap.KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s

/-- **`uf` of the PageMap slot** from [J] `hIw`, [J] `hPDw`, [P] `hlk` (module docstring). -/
theorem pm_huf (hIw : PmIw st Cs Ω Sg Ac) (hPDw : PmPdw st Cs Ω Sg Ac Locks) (hlk : PmLk st Locks) :
    ∀ (j : I64 × localinv.Plan) (K : KLayoutP) m s b v, PmPreF st Cs Ω Sg Ac Locks j.2 K m s →
      b ∈ K.user → Aligned b →
      (SlJAt (L := L) K.toKLayout (L.wr s b v) ∧ PmQF st Cs Ω Sg Ac Locks j.2 K m (L.wr s b v)) ∧
        Locks (L.wr s b v) = Locks s ∧
        PmRS st K Locks (L.wr s b v) = PmRS st K Locks s ∧
        PmWS st K Locks (L.wr s b v) = PmWS st K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro j K m s b v hE hb hba
  have hE0 := hE
  obtain ⟨hJ, ⟨⟨hio, hpd, harm, hlks⟩, hlk0⟩, hG⟩ := hE
  have P := hio.1
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have el := hlk K.toKLayout s b v hJ hb hba
  have ecur := hJ.curW_wr hb hba v
  have emsg := msgInfo_wr hJ hb hba v hT P.tA
  have hct : ∀ t, sched.cur_thread st (L.wr s b v) = ok t → t = L.curW s := by
    intro t ht
    rw [cur_thread_ok, ecur] at ht
    exact (ok_inj_ff ht).symm
  have eo : OwnMap.own K.toKLayout (L.mem (L.wr s b v)) = OwnMap.own K.toKLayout (L.mem s) :=
    E2E.ownDep hJ.regionOK hJ.userOK _ _ (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))
  have eoP : ownP K (L.mem (L.wr s b v)) = ownP K (L.mem s) := by
    funext x
    by_cases hx : x ∈ K.ptes
    · rw [ownP_pte hx, ownP_pte hx]
    · have hv : ¬ ∃ w, InVcpu K.toKLayoutV w x := fun ⟨_, hw⟩ => not_inVcpu_empty hG.nv hw
      rw [ownP_off hx, ownP_off hx, ownV_off hv, ownV_off hv, eo]
  have e3 := (hJ.ioRWDS_wrSt (st := st) (Locks := Locks) hb hba v el).2.2
  refine ⟨⟨hJ.userWr hb v, ⟨⟨ioQ_wr hIw K.toKLayout m s b v hJ hio hb hba, hPDw j K m s b v hE0 hb hba, ?_, ?_⟩,
    invLk_wr hJ P hlk0 hb hba v⟩⟩, el, ?_, ?_, e3⟩
  · intro t info ht hi
    obtain rfl := hct t ht
    rw [emsg] at hi
    exact harm _ info (cur_thread_ok s) hi
  · intro i x hi hx
    rw [el]
    exact hlks i x hi hx
  · funext w
    simp only [PmRS, RPerm, GateOnly, eoP, el, LawfulStore.cpu_wr]
  · funext w
    simp only [PmWS, WPerm, eoP, el, LawfulStore.cpu_wr]

end huf

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **What is left of the PageMap slot's obligations** (module docstring). -/
structure PmObl2 (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop where
  /-- [W] `acc`. -/
  acc : ∀ (j : I64 × localinv.Plan) K m, PmAccW st ar j.1 j.2 K Locks (PmPreF st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `move`. -/
  mv : ∀ (j : I64 × localinv.Plan) K m, PmMoveW st ar j.1 j.2 K Locks m (PmPreF st Cs Ω Sg Ac Locks j.2 K m)
  /-- [J] `IoPre` survives a user write. -/
  iw : PmIw st Cs Ω Sg Ac
  /-- [J] the plan survives a user write. -/
  pdw : PmPdw st Cs Ω Sg Ac Locks
  /-- [P] the locks survive a user write. -/
  lk : PmLk st Locks

variable {st ar}

/-- **The PageMap slot family at `PmPreF`**, with `pr`, `dec`, `ra`, `ro` proved and `uf` from `pm_huf`. -/
def pmPathsF {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl2 st ar Cs Ω Sg Ac Locks) :
    PathsP (I64 × localinv.Plan) :=
  fun j K m hK hU =>
    pm_localPath (K := K) (m0 := m) (Locks := Locks) ar hA hK hU j.1 j.2 hm
      (P := PmPreF st Cs Ω Sg Ac Locks j.2 K m) (fun _ h => h.2.1.1.1.1)
      (B.acc j K m) (pm_dec hA j.1) (B.mv j K m) (pm_ra hA j.1)
      (fun s b v h hb ha => by
        obtain ⟨⟨h1, h2⟩, h3⟩ := pm_huf B.iw B.pdw B.lk j K m s b v h hb ha
        exact ⟨⟨h1, h2, gateEp_userWr h.2.2 hb ha⟩, h3⟩)
      (pm_hpz (pm_prune hA j.1) (pm_ro hA j.1))

/-- **The PageMap slot's start fact at `PmQF`** (as `StartPm`). -/
def StartPmF {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl2 st ar Cs Ω Sg Ac Locks)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : I64 × localinv.Plan) : Prop :=
  ∃ (σ : S) (a : A), Ch σ ∧ PmQF st Cs Ω Sg Ac Locks j.2 K m σ ∧ L.cpu σ = c ∧ Locks σ = hs ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x) ∧ q = (pmPathsF hA hm B j K m hK hU).body σ a

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **`hSFQ` of `serializable_fl4_localW11PRI` for the PageMap slot at `PmQF`.** -/
theorem pm_hSFQF {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl2 st ar Cs Ω Sg Ac Locks) :
    ∀ Ch K m hK hU c hs q j, (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → m x = s1.mem x) →
      StartPmF hA hm B Ch K m hK hU c hs q j → StartAt (pmPathsF hA hm B j K m hK hU) c hs m q := by
  rintro Ch K m hK hU c hs q j ⟨σe, hC⟩ ⟨s1, hc1, hg⟩ ⟨σ, a, hCh, hQ, hc, hl, hμ, rfl⟩
  obtain ⟨Z, H, Cx, nc, -, -, -, hCL, -⟩ := hC
  exact ⟨σ, a, ⟨hCL.bun σ hCh, hQ, s1.mem, hc1, fun x hx ha hu => (hμ x ha hu).trans (hg x hx)⟩, hc, hl, hμ,
    rfl⟩

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end over W11's slots and the PageMap slot**, `pr` / `dec` / `ra` / `ro` proved, `uf` reduced
(module docstring). -/
theorem serializable_fl4_localW11PRIPm2 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl2 st ar Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPR (PathsP.sum (fl4LocW11J st ar hA hm hSt a0) (pmPathsF hA hm B))
      (StartW11RI st ar hA hm hSt a0 arI AR MR (StartPmF hA hm B)) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localW11PRI st ar hA hm hSt a0 P hIoa (pmPathsF hA hm B) (pm_hSFQF hA hm B) h0 hA0 hB hc0 hM0
    h hq

end top

end
end Fl4Proofs.P2.E2EP

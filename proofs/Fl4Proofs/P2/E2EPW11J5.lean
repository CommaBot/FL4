/-
P2 (line jsweep, gen 1): **st's `eu` [J] discharged** — `serializable_fl4_localW11PJ5`.

`StPremW3.eu` asks that `StEnt` (the set-timer path's `Pre`, at the canonical sets) survive an aligned write of a
user word at **every** `StEnt` state, not only at bundle states. It does: `StEnt` carries `StLay` (every node /
TCB / SC word of the entry lies in a typed region, so is no user word) and `BXI` (P1's sets), and the only layout
facts the frame needs beyond those are facts about the layout alone, available from any bundle state with the same
kernel base:

* **`stLay_wrU`**: `StLay` reads the state only through the kernel base and the core, which a write keeps.
* **`stEnt_wr`**: from one bundle state `σb` of the layout, `∀ c ∈ Cs, c < 64`, an `StEnt` state `X` and a user
  word `b`: `StEnt` at `L.wr X b v`. `L.ksb X = L.ksb σb` by `ksb_of_stLay`; `BXI` by `bxi_userJ` (which already
  separates the bundle state from the frame state); `StPre` / `aff` read node, TCB and SC words, all `NU`
  (`StLay.nu_node`, `nu_tcb`, `nu_scw` with `RegionOKX` of the layout).
* **`StPremW3B`** = `StPremW3A` minus `eu`; `StPremW3B.toA` (given `Cs` below 64 cores); `StPremW3B.ofA`.
* **`StartP3W11T`**: `StartP3W11S` with st at `StPremW3B`, the start state named before `eu` (its `BunIx` gives
  the index's `Cs` the bundle ghosts, below 64 by P3's `csLt`); **`startP3W11S_of_T`**;
  **`serializable_fl4_localW11PJ5`**: `serializable_fl4_localW11PJ4` with `StartP3W11JT` starts.

No new premise; st's record keeps only `nv`, `bun`, `hQ` (conventions / start state) and `kd` [P]. No existing
statement changed.
-/
import Fl4Proofs.P2.E2EPW11J4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section fr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Kl : KLayout} {T Scs : Set U64} {Z : U64 → Nat}

/-- **`StLay` across a write** (it reads the kernel base and the core only). -/
theorem stLay_wrU {X : S} (h : StLay Kl st T Scs Z X) (b v : U64) : StLay Kl st T Scs Z (L.wr X b v) :=
  { nd := fun o ho => by rw [nodeAt_wr, L.cpu_wr]; exact h.nd o ho
    tcb := h.tcb
    sc := h.sc
    dom := by rw [L.ksb_wr]; exact h.dom
    dtm := by rw [L.ksb_wr]; exact h.dtm
    domA := by rw [L.ksb_wr]; exact h.domA
    dtmA := by rw [L.ksb_wr]; exact h.dtmA
    user := h.user
    domU := by rw [L.ksb_wr]; exact h.domU
    dtmU := by rw [L.ksb_wr]; exact h.dtmU }

variable {Cs Ω Sg Ac : Set U64} {target : U64}

/-- **`StEnt` across a user-word write at any `StEnt` state** (module docstring). -/
theorem stEnt_wr {σb X : S} (B : SlJAt (L := L) Kl σb) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hE : StEnt Kl st Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac
      target X) {b : U64} (hb : b ∈ Kl.user) (hba : Aligned b) (v : U64) :
    StEnt Kl st Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac target
      (L.wr X b v) := by
  have hX := B.regionOKX
  have h0 := hE.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st Kl.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have hk : L.ksb X = L.ksb σb := by rw [ksb_of_stLay hE.lay hN, B.kc.1]
  have G : Ag st (NU Kl) X (L.wr X b v) := ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb v hx⟩
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr X b v) (L.nodeAt (L.wr X b v) (L.cpu (L.wr X b v)) o) = L.mem X (L.nodeAt X (L.cpu X) o) :=
    fun o ho h8 => by
      rw [nodeAt_wr, L.cpu_wr]
      exact wr_nu hba hb v ⟨nodeAt_aligned hN ho h8, hE.lay.nu_node ho⟩
  have ecur : L.curW (L.wr X b v) = L.curW X := eN _ (by rw [curth_val]; omega) (by rw [curth_val])
  have ecsc : L.cscW (L.wr X b v) = L.cscW X :=
    eN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have hcH : Kl.heap (L.curW X) = some .tcb := h0.curT
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := hE.inv
  have hP := hE.pre
  refine ⟨bxi_userJ B hk hCs hE.inv G, stLay_wrU hE.lay b v, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hE.tg⟩
  · have e : L.mem (L.wr X b v) (affA (L.curW X)) = L.mem X (affA (L.curW X)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ecur, L.cpu_wr, e]; exact hP.aff
  · have e : L.mem (L.wr X b v) (stA (L.curW X)) = L.mem X (stA (L.curW X)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega)
        (by rw [st_val]))
    rw [ecur, e]; exact hP.nq
  · have e : L.mem (L.wr X b v) (scA (L.curW X)) = L.mem X (scA (L.curW X)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [ecur, ecsc, e]; exact hP.sct
  · rw [ecsc]; exact hP.csc
  · have e : L.mem (L.wr X b v) (scCoreA (L.cscW X)) = L.mem X (scCoreA (L.cscW X)) :=
      wr_nu hba hb v (nu_scw hX (scs_heap hP.csc) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    rw [ecsc, L.cpu_wr, e]; exact hP.core
  · intro t ht h1
    have es : L.mem (L.wr X b v) (scA t) = L.mem X (scA t) :=
      wr_nu hba hb v (nu_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [es] at h1 ⊢
    have hsc := (hXI.2.2.bound t ht h1).1
    have ec : L.mem (L.wr X b v) (scCoreA (L.mem X (scA t))) = L.mem X (scCoreA (L.mem X (scA t))) :=
      wr_nu hba hb v (nu_scw hX (scs_heap hsc) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    have ea : L.mem (L.wr X b v) (affA t) = L.mem X (affA t) :=
      wr_nu hba hb v (nu_tcb hX ht (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ec, ea]; exact hE.aff t ht h1

end fr

section prem
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **`StPremW3` without `nu` and `eu`** (module docstring). -/
structure StPremW3B (i : StArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (as `stSlotP3W`). -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- Index convention: the index's `Q` is `StEntK` (stpost's `StEntKK`). -/
  hQ : i.Q = fun K' m' s => StEntK K'.toKLayout st K'.heap.tcbs i.Cs i.Ω K'.heap i.Sg K'.heap.replies
    K'.heap.scs K'.heap.ntfns K'.heap.scBits i.Ac i.target m' s
  /-- [P] -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s

variable {st} in
theorem StPremW3B.toA {i : StArg S} {K : KLayoutV} {m : U64 → U64} (h : StPremW3B st i K m)
    (hCs : ∀ c ∈ i.Cs, c.val < 64) : StPremW3A st i K m := by
  refine ⟨h.nv, h.bun, h.hQ, fun s b v hE hb hba => ?_, h.kd⟩
  rw [userV_empty h.nv] at hE hb ⊢
  exact stEnt_wr h.bun.choose_spec hCs hE hb hba v

variable {st} in
theorem StPremW3B.ofA {i : StArg S} {K : KLayoutV} {m : U64 → U64} (h : StPremW3A st i K m) :
    StPremW3B st i K m :=
  ⟨h.nv, h.bun, h.hQ, h.kd⟩

end prem

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **`StartP3W11S` with st at `StPremW3B`** (module docstring). -/
def StartP3W11T (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .st j => ∃ h : StPremW3B st j K m, ∃ σ : S, (Ch σ ∧ StEntJ7 st j K σ) ∧
      ∀ hC : (∀ c ∈ j.Cs, c.val < 64),
        GlueAt ((stSlotP3W st ar hA hm).liftAt j K m hK hU (h.toA hC).toW3.toP3) (fun σ' : S => σ' = σ) c hs m q
  | i => StartP3W11S st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartP3W11T` gives `StartP3W11S`.** -/
theorem startP3W11S_of_T {Ch : S → Prop} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K}
    {c : U64} {hs : U64 → Prop} {q : SP} {i : Fl4IxW (S := S)}
    (h : StartP3W11T st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartP3W11S st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i := by
  cases i with
  | st j =>
    obtain ⟨h1, σ, ⟨hC, hE⟩, hG⟩ := h
    have hCs : ∀ c ∈ j.Cs, c.val < 64 := by
      obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, Bz⟩ := hE.ix.ac
      exact fun c hc => Bz.j.kern.csLt c hc
    exact ⟨h1.toA hCs, (hG hCs).mono fun σ' e _ => by subst e; exact ⟨hC, hE⟩⟩
  | vmF j => exact h
  | vmR j => exact h
  | io j => exact h
  | irq j => exact h
  | sl j => exact h
  | vq j => exact h

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

variable {arI AR MR}

end top

end
end Fl4Proofs.P2.E2EP

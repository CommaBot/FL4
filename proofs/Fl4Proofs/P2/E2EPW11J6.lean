/-
P2 (line jsweep, gen 1): **vt's `eu` [J] discharged** — `serializable_fl4_localW11PJ6`.

`VtPremP7.eu` asks that `VtPre` (= `VtmEnt`, the VM-timer path's `Pre`) survive an aligned write of a user word at
every `VtPre` state. As for st (E2EPW11J5) it does, from one bundle state of the layout (the start state) and the
index's canonical sets (its `BunIxU`):

* **`vtmEnt_wr`**: `VtmEnt` at `L.wr X b v` from `VtmEnt` at `X` (no VCPU in the layout). `BXI` by `bxi_userJ`
  (any `Ω`, `Sg`); `StLay` by `stLay_wrU`; the current thread, its bound VCPU (`vOf`), `AFFINITY`, `SC` and bound
  notification are TCB words, the current SC's `CORE` an SC word (`XInv`'s `cur`), the current thread / SC node
  words: all `NU`; the VCPU clauses are vacuous (`vin` at `X`, no VCPU); `iq` / `kr` read the kernel base only;
  `tab` and `AsidOff` the ASID-table words (`SlJAt.nuAsid`, `asidOff_agN`); `nfar`'s `VFar` moves by
  `OutsideObjs.ksb`.
* **`VtPremP7M`** = `VtPremP7N` minus `eu`; `VtPremP7M.toN`, `.ofN`; **`vtEu_of`**: the field from the start
  state's `VtEntJ8` (canonical sets, `Cs` below 64 cores by P3's `csLt`).
* **`StartP3W11U`**: `StartP3W11T` with vt at `VtPremP7M` (the start state, already named for `OL` / `SL`, also
  gives `eu`); **`startP3W11T_of_U`**; **`serializable_fl4_localW11PJ6`**.

No new premise. vt's record keeps `nv`, `bun` (choice / start state), `kd`, `PL` [P], `Nt` (P1 typing) and the
[J]s `tp`, `M`, `UB`, `pSg` (handoff jsweep.md: not derivable from `VtPre`). No existing statement changed.
-/
import Fl4Proofs.P2.E2EPW11J5
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
variable {K : KLayoutV} {Cs Ω Sg Ac : Set U64} {lk : S → U64 → Prop} {irq n : U64}

/-- **`VtmEnt` across a user-word write at any `VtmEnt` state** (module docstring). -/
theorem vtmEnt_wr (nv : K.vcpus = ∅) {σb X : S} (B : SlJAt (L := L) K.toKLayout σb) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hE : VtmEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac lk irq n
      X) {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    VtmEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac lk irq n
      (L.wr X b v) := by
  have hX := B.regionOKX
  have E := hE.ent
  have h0 := E.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have hk : L.ksb X = L.ksb σb := by rw [ksb_of_stLay E.lay hN, B.kc.1]
  have G : Ag st (NU K.toKLayout) X (L.wr X b v) :=
    ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb v hx⟩
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr X b v) (L.nodeAt (L.wr X b v) (L.cpu (L.wr X b v)) o) = L.mem X (L.nodeAt X (L.cpu X) o) :=
    fun o ho h8 => by
      rw [nodeAt_wr, L.cpu_wr]
      exact wr_nu hba hb v ⟨nodeAt_aligned hN ho h8, E.lay.nu_node ho⟩
  have ecur : L.curW (L.wr X b v) = L.curW X := eN _ (by rw [curth_val]; omega) (by rw [curth_val])
  have ecsc : L.cscW (L.wr X b v) = L.cscW X :=
    eN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have hcH : K.heap (L.curW X) = some .tcb := h0.curT
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := E.inv
  have evOf : vOf st (L.wr X b v) = vOf st X := by
    unfold vOf
    rw [ecur]
    exact wr_nu hba hb v (nu_tcb hX hcH (o := 3664#u64) (by simp) (by simp) (by simp))
  have ekr : krA (L := L) (L.wr X b v) = krA (L := L) X := by unfold krA; rw [L.ksb_wr]
  have hv0 : ∀ w, w ≠ 0#u64 → w = vOf st X → False := fun w hw e => by
    subst e; exact not_inVcpu_empty nv (E.vin hw)
  refine ⟨?_, by rw [L.ksb_wr]; exact hE.iq, by rw [ekr]; exact hE.kr, fun hi hhi => ?_,
    asidOff_agN (fun hi hhi => B.nuAsid hk hhi) G hE.asid⟩
  · rw [evOf]
    refine ⟨bxi_userJ B hk hCs E.inv G, stLay_wrU E.lay b v, E.ntw, by rw [ecur]; exact E.cs, ?_, ?_, ?_,
      by rw [L.ksb_wr]; exact E.ksv, E.vin, fun h => (hv0 _ h rfl).elim, fun h => (hv0 _ h rfl).elim, ?_⟩
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
      rw [ec, ea]; exact E.aff t ht h1
    · have e : L.mem (L.wr X b v) (affA (L.curW X)) = L.mem X (affA (L.curW X)) :=
        wr_nu hba hb v (nu_tcb hX hcH (o := 3520#u64) (by simp) (by simp) (by simp))
      rw [ecur, L.cpu_wr, e]; exact E.curAff
    · have e : L.mem (L.wr X b v) (scCoreA (L.cscW X)) = L.mem X (scCoreA (L.cscW X)) :=
        wr_nu hba hb v (nu_scw hX (scs_heap hXI.2.2.cur) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
          (by simp [layout.sc.CORE]))
      rw [ecsc, L.cpu_wr, e]; exact E.cscCore
    · intro n' hn hn0
      have eb : L.mem (L.wr X b v) (boundA (L.curW X)) = L.mem X (boundA (L.curW X)) :=
        wr_nu hba hb v (nu_tcb hX hcH (o := 3368#u64) (by simp) (by simp) (by simp))
      rw [ecur, eb] at hn
      have hF := E.nfar n' hn hn0
      exact ⟨hF.1.ksb (L.ksb_wr _ _ _), hF.2⟩
  · have eA : L.mem (L.wr X b v) (atAF (L.ksb X) hi) = L.mem X (atAF (L.ksb X) hi) := G.m _ (B.nuAsid hk hhi)
    rw [L.ksb_wr, eA]
    exact hE.tab hi hhi

end fr

section prem
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **`VtPremP7N` without `eu`** (module docstring). -/
structure VtPremP7M (i : VtArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (the glue's layout choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- [J] at every `VtPre` state the ASID pool words are no user words. -/
  tp : ∀ s, VtPre st i K s → ∀ hi : U64, hi.val < 2048 → ∀ lo : U64, lo.val < 512 →
    L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 → peAF (L.mem s (atAF (L.ksb s) hi)) lo ∉ K.user
  /-- [P] -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- P1's notifications typed in the heap. -/
  Nt : ∀ q ∈ i.Nt, i.H q = some .ntfn
  /-- [J] the map memory agrees with every `VtPre` state on every thread's `AFFINITY`. -/
  M : ∀ s, VtPre st i K s → ∀ y ∈ i.T, m (fld y oAFFINITY) = L.mem s (affA y)
  /-- [P] -/
  PL : PlanLk i.lk i.pl
  /-- [J] -/
  UB : ∀ s, VtPre st i K s → ∃ U : Set U64, Fl4Proofs.P1.UserOK st i.T i.Cs i.Ω i.H U s ∧
    ∀ y ∈ i.T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄
  /-- [J] -/
  pSg : ∀ s, VtPre st i K s → core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ∉ i.Sg

/-- vt's `eu` field (`VtPremP7.eu`). -/
def VtEuX (i : VtArg S) (K : KLayoutV) : Prop :=
  ∀ s b v', VtPre st i K s → b ∈ K.user → Aligned b → VtPre st i K (L.wr s b v')

variable {st} in
theorem VtPremP7M.toN {i : VtArg S} {K : KLayoutV} {m : U64 → U64} (h : VtPremP7M st i K m) (E : VtEuX st i K) :
    VtPremP7N st i K m :=
  ⟨h.nv, h.bun, h.tp, E, h.kd, h.Nt, h.M, h.PL, h.UB, h.pSg⟩

variable {st} in
theorem VtPremP7M.ofN {i : VtArg S} {K : KLayoutV} {m : U64 → U64} (h : VtPremP7N st i K m) :
    VtPremP7M st i K m :=
  ⟨h.nv, h.bun, h.tp, h.kd, h.Nt, h.M, h.PL, h.UB, h.pSg⟩

variable {st} in
/-- **vt's `eu` from the start state's `VtEntJ8`** (module docstring). -/
theorem vtEu_of {i : VtArg S} {K : KLayoutV} {σ : S} (hE : VtEntJ8 st i K σ) : VtEuX st i K := by
  have B : SlJAt (L := L) K.toKLayout σ := hE.ix.slJAtS.slJAt
  have hCs : ∀ c ∈ i.Cs, c.val < 64 := by
    obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, Bz, -⟩ := hE.ix.ac
    exact fun c hc => Bz.j.kern.csLt c hc
  have hKH := hE.ix.hKH
  have hT := hE.ix.hT
  have hRp := hE.ix.hRp
  have hScs := hE.ix.hScs
  have hNt := hE.ix.hNt
  have hZ := hE.ix.hZ
  intro s b v hP hb hba
  show VtmEnt K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.irq i.n (L.wr s b v)
  have hP' : VtmEnt K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.irq i.n s := hP
  rw [hT, hRp, hScs, hNt, hZ, ← hKH] at hP' ⊢
  exact vtmEnt_wr hE.nv B hCs hP' hb hba v

end prem

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **`StartP3W11T` with vt at `VtPremP7M`** (module docstring). -/
def StartP3W11U (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vq (.inr j) => ∃ h : VtPremP7M st j K m, ∃ σ : S, (Ch σ ∧ VtEntJ8 st j K σ) ∧
      ∀ (E : VtEuX st j K) (X : VtLayX st j K),
        GlueAt ((vtSlotP3W5 st ar hA hm).path j K m hK hU ((h.toN E).toP7 X).toP5) (fun σ' : S => σ' = σ) c hs m q
  | i => StartP3W11T st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartP3W11U` gives `StartP3W11T`.** -/
theorem startP3W11T_of_U {Ch : S → Prop} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K}
    {c : U64} {hs : U64 → Prop} {q : SP} {i : Fl4IxW (S := S)}
    (h : StartP3W11U st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartP3W11T st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i := by
  cases i with
  | vq j =>
    cases j with
    | inl j => exact h
    | inr j =>
      obtain ⟨h1, σ, ⟨hC, hE⟩, hG⟩ := h
      exact ⟨h1.toN (vtEu_of hE), σ, ⟨hC, hE⟩, fun X => hG (vtEu_of hE) X⟩
  | vmF j => exact h
  | vmR j => exact h
  | io j => exact h
  | st j => exact h
  | irq j => exact h
  | sl j => exact h

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

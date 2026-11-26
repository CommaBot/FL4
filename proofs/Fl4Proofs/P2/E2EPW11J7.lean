/-
P2 (line jsweep, gen 1): **vx's `eu` [J] discharged** — `serializable_fl4_localW11PJ7`.

`VxPremP3.eu` asks that `VxPre` (= `VexitEnt ∧ VexitPEnt`, the VM-exit path's `Pre`) survive an aligned write of a
user word at every `VxPre` state. As for st / vt (E2EPW11J5 / J6), from one bundle state and the index's canonical
sets (the start state's `BunIx`):

* **`vexitEnt_wr`**: `VexitEnt` for any `v` with no VCPU in the layout (its VCPU clauses vacuous by `vin`), the
  same field-by-field frame as `vtmEnt_wr`.
* **`vexitPEnt_wr`**: `usr` by `UsrW.ksb`; `buf` by `lookup_buf_agree` (the IPC-buffer pointer and the buffer cap
  slot are words of the current TCB, and user words lie in no TCB, `SlJAt.userObj`); `aff0` a TCB word; `pusr` /
  `vfit` vacuous.
* **`VxPremP3E`** = `VxPremP3` minus `eu` (`nv`, `kd` [P]); **`vxEu_of`**: the field from the start state's
  `VxEntJ8N`.
* **`StartP3W11V`**: `StartP3W11U` with vx at `VxPremP3E`, the start state named before `eu`;
  **`startP3W11U_of_V`**; **`serializable_fl4_localW11PJ7`**.

No new premise. No existing statement changed.
-/
import Fl4Proofs.P2.E2EPW11J6
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section fr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutV} {Cs Ω Sg Ac : Set U64} {lk : S → U64 → Prop} {v n : U64}

/-- **`VexitEnt` across a user-word write at any `VexitEnt` state** (no VCPU in the layout). -/
theorem vexitEnt_wr (nv : K.vcpus = ∅) {σb X : S} (B : SlJAt (L := L) K.toKLayout σb) (hCs : ∀ c ∈ Cs, c.val < 64)
    (E : VexitEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac lk v n X)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (w : U64) :
    VexitEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac lk v n
      (L.wr X b w) := by
  have hX := B.regionOKX
  have h0 := E.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have hk : L.ksb X = L.ksb σb := by rw [ksb_of_stLay E.lay hN, B.kc.1]
  have G : Ag st (NU K.toKLayout) X (L.wr X b w) :=
    ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb w hx⟩
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr X b w) (L.nodeAt (L.wr X b w) (L.cpu (L.wr X b w)) o) = L.mem X (L.nodeAt X (L.cpu X) o) :=
    fun o ho h8 => by
      rw [nodeAt_wr, L.cpu_wr]
      exact wr_nu hba hb w ⟨nodeAt_aligned hN ho h8, E.lay.nu_node ho⟩
  have ecur : L.curW (L.wr X b w) = L.curW X := eN _ (by rw [curth_val]; omega) (by rw [curth_val])
  have ecsc : L.cscW (L.wr X b w) = L.cscW X :=
    eN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have hcH : K.heap (L.curW X) = some .tcb := h0.curT
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := E.inv
  have hv0 : v ≠ 0#u64 → False := fun hw => not_inVcpu_empty nv (E.vin hw)
  refine ⟨bxi_userJ B hk hCs E.inv G, stLay_wrU E.lay b w, E.ntw, by rw [ecur]; exact E.cs, ?_, ?_, ?_,
    by rw [L.ksb_wr]; exact E.ksv, E.vin, fun h => (hv0 h).elim, fun h => (hv0 h).elim, ?_⟩
  · intro t ht h1
    have es : L.mem (L.wr X b w) (scA t) = L.mem X (scA t) :=
      wr_nu hba hb w (nu_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [es] at h1 ⊢
    have hsc := (hXI.2.2.bound t ht h1).1
    have ec : L.mem (L.wr X b w) (scCoreA (L.mem X (scA t))) = L.mem X (scCoreA (L.mem X (scA t))) :=
      wr_nu hba hb w (nu_scw hX (scs_heap hsc) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    have ea : L.mem (L.wr X b w) (affA t) = L.mem X (affA t) :=
      wr_nu hba hb w (nu_tcb hX ht (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ec, ea]; exact E.aff t ht h1
  · have e : L.mem (L.wr X b w) (affA (L.curW X)) = L.mem X (affA (L.curW X)) :=
      wr_nu hba hb w (nu_tcb hX hcH (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ecur, L.cpu_wr, e]; exact E.curAff
  · have e : L.mem (L.wr X b w) (scCoreA (L.cscW X)) = L.mem X (scCoreA (L.cscW X)) :=
      wr_nu hba hb w (nu_scw hX (scs_heap hXI.2.2.cur) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    rw [ecsc, L.cpu_wr, e]; exact E.cscCore
  · intro n' hn hn0
    have eb : L.mem (L.wr X b w) (boundA (L.curW X)) = L.mem X (boundA (L.curW X)) :=
      wr_nu hba hb w (nu_tcb hX hcH (o := 3368#u64) (by simp) (by simp) (by simp))
    rw [ecur, eb] at hn
    have hF := E.nfar n' hn hn0
    exact ⟨hF.1.ksb (L.ksb_wr _ _ _), hF.2⟩

variable {m : U64 → U64}

/-- **`VexitPEnt` across a user-word write** at a `VexitEnt` state (no VCPU in the layout). -/
theorem vexitPEnt_wr (nv : K.vcpus = ∅) {σb X : S} (B : SlJAt (L := L) K.toKLayout σb)
    (E : VexitEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac lk v n X)
    (P : VexitPEnt K st K.heap.tcbs Cs K.heap Sg K.heap.scs K.heap.scBits m v X)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (w : U64) :
    VexitPEnt K st K.heap.tcbs Cs K.heap Sg K.heap.scs K.heap.scBits m v (L.wr X b w) := by
  have h0 := E.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have hcH : K.heap (L.curW X) = some .tcb := h0.curT
  have ht' : TcbAddr (L.curW X) := h0.tcbs _ h0.curT
  have ecur : L.curW (L.wr X b w) = L.curW X := by
    unfold LawfulStore.curW
    rw [nodeAt_wr, L.cpu_wr]
    exact wr_nu hba hb w ⟨nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val]),
      E.lay.nu_node (by rw [curth_val]; omega)⟩
  have tw : ∀ o : U64, o.val < 4096 → o.val % 8 = 0 →
      L.mem (L.wr X b w) (core.num.U64.wrapping_add (L.curW X) o) =
        L.mem X (core.num.U64.wrapping_add (L.curW X) o) := fun o h1 h2 =>
    wr_nu hba hb w ⟨field_aligned ht' h1 h2, fun hu => B.userObj hu hcH (fun z e => by cases e)
      (by unfold InW; rw [field_val ht' h1]; simp only [HKind.bits]; omega)⟩
  have hv0 : v ≠ 0#u64 → False := fun hw => not_inVcpu_empty nv (E.vin hw)
  refine ⟨fun x hx hxa => (P.usr x hx hxa).ksb (L.ksb_wr _ _ _), fun h => (hv0 h).elim, ?_,
    fun h => (hv0 h).elim, ?_⟩
  · have e1 : L.mem (L.wr X b w) (ibA (L.curW X)) = L.mem X (ibA (L.curW X)) :=
      tw 3512#u64 (by simp) (by simp)
    have e2 : L.mem (L.wr X b w) (sbA (L.curW X)) = L.mem X (sbA (L.curW X)) := by
      rw [sbA_field ht']; exact tw 64#u64 (by simp) (by simp)
    have e3 : L.mem (L.wr X b w) (core.num.U64.wrapping_add (sbA (L.curW X)) 8#u64) =
        L.mem X (core.num.U64.wrapping_add (sbA (L.curW X)) 8#u64) := by
      rw [sbA8_field ht']; exact tw 72#u64 (by simp) (by simp)
    rw [ecur, lookup_buf_agree e1 e2 e3]
    exact P.buf
  · rw [ecur, P.aff0]
    exact (tw 3520#u64 (by simp) (by simp)).symm

end fr

section prem
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **`VxPremP3` without `eu`** (module docstring). -/
structure VxPremP3E (i : VxArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (the glue's choice at P3 scope; gives `VcpuNU`). -/
  nv : K.vcpus = ∅
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s

/-- vx's `eu` field (`VxPremP3.eu`). -/
def VxEuX (i : VxArg S) (K : KLayoutV) (m : U64 → U64) : Prop :=
  ∀ s b v', VxPre st i K m s → b ∈ K.user → Aligned b → VxPre st i K m (L.wr s b v')

variable {st} in
theorem VxPremP3E.toP3 {i : VxArg S} {K : KLayoutV} {m : U64 → U64} (h : VxPremP3E st i K m)
    (E : VxEuX st i K m) : VxPremP3 st i K m :=
  ⟨h.nv, E, h.kd⟩

variable {st} in
/-- **vx's `eu` from the start state's `VxEntJ8N`** (module docstring). -/
theorem vxEu_of {i : VxArg S} {K : KLayoutV} {m : U64 → U64} {σ : S} (nv : K.vcpus = ∅)
    (hE : VxEntJ8N st i K σ) : VxEuX st i K m := by
  have B : SlJAt (L := L) K.toKLayout σ := hE.ix.ac.slJAt
  have hCs : ∀ c ∈ i.Cs, c.val < 64 := by
    obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, Bz⟩ := hE.ix.ac
    exact fun c hc => Bz.j.kern.csLt c hc
  have hKH := hE.ix.hKH
  have hT := hE.ix.hT
  have hRp := hE.ix.hRp
  have hScs := hE.ix.hScs
  have hNt := hE.ix.hNt
  have hZ := hE.ix.hZ
  intro s b w hP hb hba
  have hE1 : VexitEnt K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.v i.n s := hP.1
  have hP1 : VexitPEnt K st i.T i.Cs i.H i.Sg i.Scs i.Z m i.v s := hP.2
  show VexitEnt K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.v i.n (L.wr s b w) ∧
    VexitPEnt K st i.T i.Cs i.H i.Sg i.Scs i.Z m i.v (L.wr s b w)
  rw [hT, hRp, hScs, hNt, hZ, ← hKH] at hE1
  rw [hT, hScs, hZ, ← hKH] at hP1
  rw [hT, hRp, hScs, hNt, hZ, ← hKH]
  exact ⟨vexitEnt_wr nv B hCs hE1 hb hba w, vexitPEnt_wr nv B hE1 hP1 hb hba w⟩

end prem

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **`StartP3W11U` with vx at `VxPremP3E`** (module docstring). -/
def StartP3W11V (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vq (.inl j) => ∃ h : VxPremP3E st j K m, ∃ σ : S, (Ch σ ∧ VxEntJ8N st j K σ) ∧
      ∀ E : VxEuX st j K m,
        GlueAt ((vxSlotP3 st ar hA hm).path j K m hK hU (h.toP3 E)) (fun σ' : S => σ' = σ) c hs m q
  | i => StartP3W11U st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartP3W11V` gives `StartP3W11U`.** -/
theorem startP3W11U_of_V {Ch : S → Prop} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K}
    {c : U64} {hs : U64 → Prop} {q : SP} {i : Fl4IxW (S := S)}
    (h : StartP3W11V st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartP3W11U st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i := by
  cases i with
  | vq j =>
    cases j with
    | inl j =>
      obtain ⟨h1, σ, ⟨hC, hE⟩, hG⟩ := h
      have E := vxEu_of (m := m) h1.nv hE
      exact ⟨h1.toP3 E, (hG E).mono fun σ' e _ => by subst e; exact ⟨hC, hE⟩⟩
    | inr j => exact h
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

/-- **The start fact with vx at `VxPremP3E`, the armed program cut.** -/
def StartP3W11JV (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K)
    (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : Fl4IxW (S := S)) : Prop :=
  ∃ q0, StartP3W11V st ar hA hm hSt a0 arI AR MR Ch K.toKLayoutV m hK.base hU.base c hs q0 i ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {arI AR MR}

/-- **FL4 end to end, W11's family and glue, PTE convention, jsweep's [J]s discharged** (st `nu` / `eu`; vt `OL` /
`SL` / `eu`; vx `usr` / `eu`; module docstrings of E2EPW11J4–J7): `serializable_fl4_localW11PJ6` with
`StartP3W11JV` starts. -/
theorem serializable_fl4_localW11PJ7 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesCanon st K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPJ (fl4LocW11J st ar hA hm hSt a0) (StartP3W11JV st ar hA hm hSt a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have h' := ExecWPJ.mono st (SF' := StartP3W11JU st ar hA hm hSt a0 arI AR MR)
    (fun Ch K m hK hU c hs q i hsf => by
      obtain ⟨q0, hW, e⟩ := hsf
      exact ⟨q0, startP3W11U_of_V st ar hA hm hSt a0 hW, e⟩) h
  exact serializable_fl4_localW11PJ6 st ar hA hm hSt a0 P hIoa h0 hA0 hB hc0 hM0 h' hq

end top

end
end Fl4Proofs.P2.E2EP

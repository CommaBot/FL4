/-
P2 (line pte, gen 3): **syscall_local's PTE avoidance** (the `sl` field of `P3AvP`, discharged) and
**`serializable_fl4_localP3P2`**, `serializable_fl4_localP3P` with that field gone.

* `avoidE_cutLiftV_empty`: with no VCPU (`K.vcpus = ∅`, the P3-scope slots' `Prem`) the VCPU cut is the identity
  (`rsV K RS = RS`), so an `AvoidE` of an `own` path is one of its VCPU cut-lift.
* **`sl_avoidP`**: the P3-scope sl slot's lifted path reads no PTE word, by `sl_avoidVKE` (`P2/E2EPSl.lean`) at
  `Ex := (· ∈ K.ptes)`: `RegionOKE` from `RegionOKP.none` (a PTE is region `.none`), `UserNoE` from `UserOKP.kern`,
  and **`PteSl K` [J]** for the two facts `RegionOKP` does not give: no PTE word in the kernel-state block
  `[ksb, ksb + 13568)` (that block is region `.none`, `RegionOKX.ks`, so `RegionOKP` cannot separate it from a PTE),
  and, at every bundle state, no PTE word is an ASID-table word (`ksb + 288000 …`, also region `.none`) or a word of
  an ASID pool the table names (pools are heap `other` objects, region `.none`). Source: P1 `HeapOK` (page-table
  pages, ASID pools and the kernel-state block are distinct objects).
* `P3AvP2`: `P3AvP` without `sl`, plus `PteSl` [J]; `P3AvP2.toP3`; **`serializable_fl4_localP3P2`**.

Remaining [W] (`P3AvP2` fields): vmF, vmR, io, stm, irq, vx, vt (module docstring of `P2/E2EPFl4.lean`).
-/
import Fl4Proofs.P2.E2EPSl
import Fl4Proofs.P2.E2EPFl4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-- **With no VCPU the VCPU cut changes nothing**: `AvoidE` of an `own` path gives `AvoidE` of its cut-lift. -/
theorem avoidE_cutLiftV_empty {K : KLayoutV} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
    {User : U64 → Prop} {Ex : U64 → Prop} (hK : RegionOKV K) (hU : UserOKV K) (nv : K.vcpus = ∅)
    (hko : ∀ x, VData K x → ko x = .free) (P : E2E.LocalPath (OwnMap.own K.toKLayout) cls ko User)
    (W : AvoidV K P) (h : AvoidE Ex P) : AvoidE Ex (LocalPath.cutLiftV hK hU hko P W) := by
  have e : rsV K P.RS = P.RS := by
    funext s x; exact propext ⟨fun h => h.1, fun h => ⟨h, not_vData_empty nv⟩⟩
  obtain ⟨ha, hd, hp⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show AvAccE Ex P.st (P.F P.ar) P.Acc P.Pre (rsV K P.RS) P.WS
    rw [e]; exact ha
  · show @AvDecE P.S P.A P.X Ex P.st P.L (P.F P.ar) P.Acc cls ko User P.Pre (rsV K P.RS)
    rw [e]; exact hd
  · show IsProgOn (P.F P.ar) P.ar P.st (@AltOf P.S P.st P.L P.Pre (rsE Ex (rsV K P.RS)) cls ko User) P.p
    rw [e]; exact hp

section sl
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **`PteSl K`** [J] (module docstring): no PTE word in the kernel-state block, and at every bundle state no PTE
word is an ASID-table or ASID-pool word. Source: P1 `HeapOK` (page-table pages, the kernel-state block, the
ASID table and the ASID pools are distinct heap objects), so a later line can derive it from the placement. -/
def PteSl (K : KLayoutP) : Prop :=
  KsNoE (· ∈ K.ptes) K.toKLayoutV ∧ ∀ s : S, SlJAt (L := L) K.toKLayout s → TabNoE (L := L) (· ∈ K.ptes) s

theorem regionOKE_pte {K : KLayoutP} (hK : RegionOKP K) : RegionOKE (· ∈ K.ptes) K.toKLayoutV :=
  ⟨hK.base.base, fun b hb hp => hb (hK.none b hp)⟩

theorem userNoE_pte {K : KLayoutP} (hU : UserOKP K) : UserNoE (· ∈ K.ptes) K.toKLayoutV :=
  fun b hb hp => (hU.kern b hp).2 hb

/-- **syscall_local reads no PTE word** (the `sl` field of `P3AvP`), from `PteSl` [J]. -/
theorem sl_avoidP (i : SlArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hPS : PteSl st K) (h : (slSlotP3 st ar hA hSt hm a0).Prem i K.toKLayoutV m) :
    AvoidP K ((slSlotP3 st ar hA hSt hm a0).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
      (· ∈ K.user)) (W : AvoidV K.toKLayoutV P),
      P = (slSlotP3 st ar hA hSt hm a0).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K (LocalPath.cutLiftV hK.base hU.base (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv m) P W) := by
    rintro P W rfl
    apply avoidE_cutLiftV_empty hK.base hU.base h.1
    dsimp only [slSlotP3, SlotC.ofP3, SlotC.pull, slSlotK]
    unfold sl_pathsKC5 sl_pathsKC4 sl_pathsKF sl_pathsKU sl_pathsK
    exact sl_avoidVKE ar hSt hA hm a0 (regionOKE_pte hK) hU.base.base (fun _ h' => h'.1) _ _ _ _ _ _
      (fun _ _ => hPS.1) (fun s h' => hPS.2 s h'.1) (userNoE_pte hU)
  exact key _ _ (SlotC.fam_pos _ _ h)

/-- **`P3AvP` without the `sl` field**, plus `PteSl` [J] at every layout. The seven fields left are [W]. -/
structure P3AvP2 : Prop where
  pteSl : ∀ K : KLayoutP, RegionOKP K → K.ptes ≠ ∅ → PteSl st K
  vmF : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).vmF.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).vmF.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  vmR : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).vmR.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).vmR.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  io : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).io.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).io.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  stm : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).st.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).st.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  irq : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).irq.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).irq.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  vx : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m →
    AvoidP K ((vxSlotP3 st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  vt : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (vtSlotP3 st ar hA hm).Prem i K.toKLayoutV m →
    AvoidP K ((vtSlotP3 st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)

theorem P3AvP2.toP3 (h : P3AvP2 st ar hA hSt hm a0) : P3AvP st ar hA hSt hm a0 where
  vmF := h.vmF
  vmR := h.vmR
  io := h.io
  stm := h.stm
  irq := h.irq
  sl i K m hK hU he hp := sl_avoidP st ar hA hSt hm a0 i K m hK hU (h.pteSl K hK he) hp
  vx := h.vx
  vt := h.vt

/-- **FL4 end to end with rules 7 and 8, `K.ptes` arbitrary, syscall_local's PTE premise discharged**
(`serializable_fl4_localP3P` with `P3AvP2`: the `sl` [W] replaced by `PteSl` [J]). -/
theorem serializable_fl4_localP3P2 (hAv : P3AvP2 st ar hA hSt hm a0) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP (fl4LocP3P st ar hA hSt hm a0 (P3AvP2.toP3 st ar hA hSt hm a0 hAv)) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localP3P st ar hA hSt hm a0 _ h0 hA0 hK0 hU0 hM0 h hq

end sl

end
end Fl4Proofs.P2.E2EP

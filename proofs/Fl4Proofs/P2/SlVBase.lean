/-
# P2 (line p3mc, gen 15): the facts at a syscall-local (sl) start at a core's view

At a start state `σ` of the sl path at core `c`'s view `view K c ρ` (`SlJAt K σ`, `σ`'s aligned kernel words the
view's), the glue's chain state `σc` (`StartU2`'s witness) has the same aligned kernel words, kernel base and core,
action `RESUME_CURRENT` (`chain_act0`) and a running current thread (`chain_run`):

* `SlV0 K c ρ`: such a state exists (the sl counterpart of `Act0V`, with `run`);
* **`sl_v0_SF`**: an sl start fact of a chain gives `SlV0` (as `vmR_act0_SF`);
* **`sl_view_act`**: then `σ` itself has action 0 and a running current thread (the action word and the current
  thread's `STATE` are aligned kernel words, the current thread is a node word);
* **`sl_vmBase`**: `σ` carries `VmBase` (at `userV K` and at `userP K`) for some index sets (`bunIxU_of`,
  `BunIxU.vmBase`, `vmBase_userP`), so the VM pin lemmas (`vm_cur_home`, `vm_homes`, `vm_sc_home_of_tcb`) apply.

No premise: every fact is a hypothesis or derived from P3 through the chain. No existing statement changed.
-/
import Fl4Proofs.P2.E2EPU14
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD)

noncomputable section
open Classical

section act
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **A state on `c` with the view's kernel words, action 0 and a running current thread** (module docstring). -/
def SlV0 (K : KLayoutP) (c : U64) (ρ : U64 → U64) : Prop :=
  ∃ σc : S, L.cpu σc = c ∧ L.ksb σc = K.ksb ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σc x = view K.toKLayout c ρ x) ∧ L.actionW σc = 0#u64 ∧
    (L.mem σc (stA (L.curW σc)) = sched.TS_RESTART ∨ L.mem σc (stA (L.curW σc)) = sched.TS_RUNNING)

/-- **The sl start fact of a chain gives `SlV0`** (the glue's witness is the chain state). -/
theorem sl_v0_SF (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    {ρ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : SlArg S}
    (h : StartV2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.inl (.sl j))) :
    SlV0 st K c ρ := by
  have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.sl j) := h
  obtain ⟨q0, ⟨hL, σ, ⟨hCσ, hE⟩, hG⟩, -⟩ := h'
  obtain ⟨σe, hC'⟩ := hC
  obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, B, -⟩ := hE.ix
  have hR : (slSlotP3W6 st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV (view K.toKLayout c ρ) :=
    show K.toKLayoutV.vcpus = ∅ ∧ SlPremP6 st j K.toKLayoutV from
      ⟨nv, ⟨σ, ChainOf.bun hC' σ hCσ⟩, B.csLt, fun K' s _ => hL.kernDetAt K' s⟩
  obtain ⟨σ', a'', e', hc, -, hμ, -⟩ := hG hR
  subst e'
  exact ⟨_, hc, slJAt_ksb (ChainOf.bun hC' _ hCσ), fun x hx hu => hμ x hx hu,
    chain_act0 st P hIoa hC' hCσ hE.hct, chain_run P hIoa hC' hCσ hE.hct⟩

end act

section view
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The action and the current thread's state at a view start** (module docstring). -/
theorem sl_view_act {K : KLayoutP} {c : U64} {ρ : U64 → U64} {σ : S} {T : Set U64}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hN : NodePlaced st T σ (L.cpu σ))
    (hcH : K.heap (L.curW σ) = some .tcb) (hc : L.cpu σ = c)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) (h0 : SlV0 st K c ρ) :
    L.actionW σ = 0#u64 ∧
      (L.mem σ (stA (L.curW σ)) = sched.TS_RESTART ∨ L.mem σ (stA (L.curW σ)) = sched.TS_RUNNING) := by
  obtain ⟨σc, hcc, hkc, hmc, ha0, hr0⟩ := h0
  have hk : L.ksb σc = L.ksb σ := hkc.trans (slJAt_ksb hJ).symm
  have eN : ∀ o, L.nodeAt σc (L.cpu σc) o = L.nodeAt σ (L.cpu σ) o := fun o => by
    rw [hcc, hc]; exact nodeAt_of_ksb hk c o
  have nodeE : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem σc (L.nodeAt σc (L.cpu σc) o) = L.mem σ (L.nodeAt σ (L.cpu σ) o) := by
    intro o h1 h2
    have hn := hJ.nuNode hN h1 h2
    rw [eN, hmc _ hn.1 hn.2, hm _ hn.1 hn.2]
  have ecur : L.curW σc = L.curW σ := nodeE _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  refine ⟨?_, ?_⟩
  · unfold LawfulStore.actionW at ha0 ⊢
    rw [← nodeE _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])]
    exact ha0
  · have hn : NU K.toKLayout (stA (L.curW σ)) := by
      rw [Fl4Proofs.P1.stA_eq]
      exact nu_tcb hJ.regionOKX hcH (o := 3328#u64) (by simp) (by simp) (by simp)
    have e : L.mem σ (stA (L.curW σ)) = L.mem σc (stA (L.curW σc)) := by
      rw [ecur, hm _ hn.1 hn.2, hmc _ hn.1 hn.2]
    rw [e]; exact hr0

/-- **`VmBase` at an sl start state** (module docstring). -/
theorem sl_vmBase {K : KLayoutP} (nv : K.vcpus = ∅) (hK : RegionOKP K)
    (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) {σ : S} (hJ : SlJAt (L := L) K.toKLayout σ)
    (hrun : L.mem σ (stA (L.curW σ)) = sched.TS_RESTART ∨ L.mem σ (stA (L.curW σ)) = sched.TS_RUNNING) :
    ∃ Cs Ac Ω,
      VmBase st (userV K.toKLayoutV) K.toKLayout.heap.tcbs Cs Ω K.toKLayout.heap K.toKLayout.heap.frame
        K.toKLayout.heap.replies K.toKLayout.heap.scs K.toKLayout.heap.ntfns K.toKLayout.heap.scBits Ac σ ∧
      VmBase st (userP K) K.toKLayout.heap.tcbs Cs Ω K.toKLayout.heap K.toKLayout.heap.frame
        K.toKLayout.heap.replies K.toKLayout.heap.scs K.toKLayout.heap.ntfns K.toKLayout.heap.scBits Ac σ := by
  obtain ⟨Cs, Ac, Ω, BU⟩ := bunIxU_of hJ
  have B0 := BU.vmBase hrun
  have B : VmBase st (userV K.toKLayoutV) K.toKLayout.heap.tcbs Cs Ω K.toKLayout.heap K.toKLayout.heap.frame
      K.toKLayout.heap.replies K.toKLayout.heap.scs K.toKLayout.heap.ntfns K.toKLayout.heap.scBits Ac σ := by
    rw [userV_empty nv]; exact B0
  exact ⟨Cs, Ac, Ω, B, vmBase_userP hK hks B⟩

end view

end
end Fl4Proofs.P2.E2EP

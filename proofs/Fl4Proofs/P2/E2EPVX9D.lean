/-
# P2 (line vmscope, gen 9, delPte module 1): the Delete PTE arm's entry fact across user writes without a P3 bundle

The Delete PTE-arm path `inv_localPathPP` (P2/InvDelPteOnceP.lean) has `Pre := PreP = SlJAt ∧ InvQFP ∧ CvP`, and its
`user_free` (`invUfPP`) keeps `PreP` across a user write through the bundle (`SlJAt.userWr`, `SlJAt.curW_wr`,
`msgInfo_wr`, `planDel_userWr` with P3's `smallPageEntry_userWr`, `invLk_wr`, `ioQ_wr ∘ ioPre_wr_hIw`). In a VM epoch
there is no bundle state. This module is the first step of the VM-epoch route recorded in the handoff (cut VCPUs
first, then a lift that tolerates the one locked PTE): the entry fact of the PTE arm, `InvQFP`, kept by a user
write from the epoch's layout facts (`UserLayX`) and the walk fact `InvLXS.vs` alone, as E2EPVX9 does for `InvQF`:

* `invPlanD_wrPX` (`invPlanD_wrP` without the bundle: `planDel_userWrX`, the target's `small_page_entry` kept by
  `vsRdG_wrX` from `InvLXS.vs`);
* **`invQFP_wrX`** (`invUfPP`'s `InvQFP` half without the bundle and without [J] `hIw`; locks kept by hypothesis);
* **`invEntP_cl`**: `InvLXS ∧ InvQFP` along `UReach` from the start state, the locks by `InvPremX.lk`-shaped [P]
  at `InvLX (fun _ => True)` states (as VX9's `invEntV_of9D`).

No new premise; no slot or top here (the path itself is the next module: module docstring of E2EPVX9's handoff).
No sorry / admit / native_decide / bv_decide. No existing statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPVX9
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout fld oAFFINITY)

section pte
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {b : U64}
variable {Cs Ω Sg Ac : Set U64}

/-- `invPlanD_wrP` without the bundle: the PTE arm's plan survives a user write at an `InvQFP` state whose
target's walk fact `hspe` holds. -/
theorem invPlanD_wrPX {Locks : S → U64 → Prop} {p : localinv.Plan} {m : U64 → U64}
    (U : Fl4Proofs.P2.E2EP.UserLayX L K) (hqf : InvQFP st Cs Ω Sg Ac Locks p K m s)
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hspe : ∀ d, d ∈ K.slots → ∀ fp rt asid va,
      obj.Slot.cap st d s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      localinv.small_page_entry st (L.wr s b v) asid va = localinv.small_page_entry st s asid va) :
    InvPlanD st p (L.wr s b v) := by
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, C, hcap, hsK, -, -, hC, hcl, hCs, -⟩ := del_coreP hqf
  obtain ⟨⟨hio, ⟨t, info, ex, ht, hi, hpw⟩, harm, -⟩, -⟩ := hqf
  have P := hio.1
  have et : t = L.curW s := by rw [cur_thread_ok] at ht; exact (ok_inj_ff ht).symm
  subst et
  have hlbl := (harm _ info (cur_thread_ok s) hi).1
  rw [hlbl] at hpw
  refine ⟨L.curW s, info, ex, ?_, ?_, ?_⟩
  · rw [cur_thread_ok, curW_wrP U P hb hba v]
  · rw [msgInfo_wrP P hb hba v]; exact hi
  · rw [hlbl, planDel_userWrX P hb hba v hsK hcap hC hcl (fun p r m y hp hm => (hCs p r m y hp hm).1) hspe ex]
    exact hpw

/-- **`InvQFP` is kept by a user write** at an `InvLXS` state with `UserLayX`, the locks kept (`invUfPP`'s
`InvQFP` half without the bundle and without [J] `hIw`). -/
theorem invQFP_wrX {Locks : S → U64 → Prop} {p : localinv.Plan} {m : U64 → U64}
    (U : Fl4Proofs.P2.E2EP.UserLayX L K) (hCs : ∀ c ∈ Cs, c.val < 64) (X : InvLXS st K s)
    (hq : InvQFP st Cs Ω Sg Ac Locks p K m s) (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (el : Locks (L.wr s b v) = Locks s) : InvQFP st Cs Ω Sg Ac Locks p K m (L.wr s b v) := by
  have hq0 := hq
  obtain ⟨⟨hio, hpd, harm, hlks⟩, hlk0⟩ := hq
  have P := hio.1
  have ecur := curW_wrP U P hb hba v
  have emsg := msgInfo_wrP P hb hba v
  have hct : ∀ t, sched.cur_thread st (L.wr s b v) = ok t → t = L.curW s := by
    intro t ht
    rw [cur_thread_ok, ecur] at ht
    exact (ok_inj_ff ht).symm
  have hspe : ∀ d, d ∈ K.slots → ∀ fp rt asid va,
      obj.Slot.cap st d s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      localinv.small_page_entry st (L.wr s b v) asid va = localinv.small_page_entry st s asid va :=
    fun d hd fp rt asid va hc ha =>
      (vsRdG_wrX (V := VsW K) (fun a ha => read_wr_nu hb hba v ha.1 ha.2.2) (ksBase_wr b v)
        (X.vs d fp rt asid va hd hc ha).2.2).2
  refine ⟨⟨ioQ_wrX U hCs hio hb hba v, invPlanD_wrPX U hq0 hb hba v hspe, ?_, ?_⟩,
    invLk_wrX U P hlk0 hb hba v⟩
  · intro t info ht hi
    obtain rfl := hct t ht
    rw [emsg] at hi
    exact harm _ info (cur_thread_ok s) hi
  · intro i x hi hx
    rw [el]
    exact hlks i x hi hx

/-- **The PTE arm's entry facts along `UReach`** (module docstring): from `InvLXS ∧ InvQFP` at `σ`, at every state
reached by aligned user-word writes; the locks kept at every state with `InvLX (fun _ => True)` ([P], the shape of
VX8's `InvPremX.lk`). -/
theorem invEntP_cl {Locks : S → U64 → Prop} {p : localinv.Plan} {m : U64 → U64}
    (hK : OwnMap.RegionOK K) (hU : E2E.UserOK K) (la : IoLayA K) (hz : (0#u64) ∉ K.slots)
    (U : Fl4Proofs.P2.E2EP.UserLayX L K) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ s b v, InvLX st (fun _ => True) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    {σ : S} (h : InvLXS st K σ ∧ InvQFP st Cs Ω Sg Ac Locks p K m σ) :
    ∀ s', UReach (L := L) K σ s' → InvLXS st K s' ∧ InvQFP st Cs Ω Sg Ac Locks p K m s' := by
  intro s' hr
  refine ureach_cl (K := K)
    (P1 := fun s => InvLXS st K s ∧ IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies
      K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (P := fun s => InvLXS st K s ∧ InvQFP st Cs Ω Sg Ac Locks p K m s)
    (fun s b v h hb hba => ⟨invLXS_wrX U h.2 h.1 hb hba v, Fl4Proofs.P2.E2EP.ioPre_wrL U hCs h.2 hb hba v⟩)
    (fun s b v hc h hb hba => ?_) (fun s h => ⟨h.1, h.2.1.1.1⟩) σ s' hr h
  have hX : InvLX st (fun _ => True) K s :=
    ⟨hK, hU, la, U, hz, fun s'' hr'' => ⟨(hc s'' hr'').1, trivial⟩⟩
  exact ⟨invLXS_wrX U h.2.1.1.1 h.1 hb hba v, invQFP_wrX U hCs h.1 h.2 hb hba v (hlk s b v hX hb hba)⟩

end pte

end Fl4Proofs.P2.PathObl

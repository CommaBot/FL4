/-
# P2 (line pte, generation 13): the PageMap decode's ASID / page-table walk on another store (first `blk` piece)

`decode_page_map` (Small, the plan's arm) walks twice: `check_vspace` (`find_vspace_for_asid` of the PML4 cap's ASID)
and `page_entry_slot … Small` (= `lookup_pt_slot`, no further read for a small page). Both run at the decode state
`s2` (after the prefix) and, for `blk` / `mv` / `roA`, on another store (`guard`, `mguard`, the alternatives).

* **`vsRdG_tr`**: from `VsRdG st V s asid va` (the walk at `s` runs alike on the store guarded to `V`), on any store
  `m'` at any state `x'` that reads every `V` word as `st` at `s` and has `s`'s kernel base, the walk gives `st`'s
  results at `s` (InvVs's `*.trV` transfers);
* **`check_vspace_tr`**, **`page_entry_slot_small_tr`**: `check_vspace` of a mapped PML4 cap and the small-page
  `page_entry_slot` likewise;
* **`pm_vsRd`**: at a `PmPreF` state the walk reads only `VsW` words off `K.ptes` (invj gen 6's `SlJAtZ.vsRdX`
  with `X := K.ptes`, `ptesR_sub` through `GateEp`), and those words are `IoRS (ptU K)` words (`pm_vsW_ioRS`), so a
  store reading `IoRS (ptU K) s` as `st` (and a state agreeing with `s` on them) sees `st`'s walk at `s`.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmTop3
import Fl4Proofs.P2.InvDelPteG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP

noncomputable section

section tr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {V : U64 → Prop} {m' : machine.Store S} {x' s : S}

/-- **The walk transfers to any store reading the `V` words alike** (from `VsRdG`). -/
theorem vsRdG_tr {asid va : U64} (hV : VsRdG st V s asid va) (hr : ∀ a, V a → m'.read x' a = st.read s a)
    (hk : m'.ks_base x' = st.ks_base s) :
    vspace.find_vspace_for_asid m' x' asid = vspace.find_vspace_for_asid st s asid ∧
      ∀ root, vspace.find_vspace_for_asid st s asid = ok (.Ok root) →
        vspace.lookup_pt_slot m' x' root va = vspace.lookup_pt_slot st s root va := by
  obtain ⟨h1, h2⟩ := hV
  refine ⟨?_, fun root hroot => ?_⟩
  · obtain ⟨r, hr', -⟩ := spec_ex_fd (P0.vspace.find_vspace_for_asid.p0 st s asid L.total)
    rw [hr']
    rw [hr'] at h1
    exact vspace.find_vspace_for_asid.trV (W := fun _ => False) hr hk h1
  · obtain ⟨r, hr', -⟩ := spec_ex_fd (P0.vspace.lookup_pt_slot.p0 st s root va L.total)
    have h2' := h2 root hroot
    rw [hr'] at h2' ⊢
    exact vspace.lookup_pt_slot.trV (W := fun _ => False) hr h2'

/-- **`check_vspace` of a mapped PML4 cap transfers** (its only read is `find_vspace_for_asid`). -/
theorem check_vspace_tr {root rasid : U64}
    (hf : vspace.find_vspace_for_asid m' x' rasid = vspace.find_vspace_for_asid st s rasid) :
    vspace.check_vspace m' x' (.Pml4 root true rasid) = vspace.check_vspace st s (.Pml4 root true rasid) := by
  unfold vspace.check_vspace
  simp only [↓reduceIte, hf]

/-- **The small-page `page_entry_slot` transfers** (it is `lookup_pt_slot`, no further read). -/
theorem page_entry_slot_small_tr {root va : U64}
    (hl : vspace.lookup_pt_slot m' x' root va = vspace.lookup_pt_slot st s root va) :
    vspace.page_entry_slot m' x' root va .Small = vspace.page_entry_slot st s root va .Small := by
  unfold vspace.page_entry_slot
  simp only [hl, bind_ok, ↓reduceIte]

end tr

section words
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
  {s : S}

/-- A `VsW` word off the PTE set is an `IoRS (ptU K)` word (gate-owned, not in `K.user ∪ K.ptes`). -/
theorem pm_vsW_ioRS {w : U64} (hw : VsW K.toKLayout w) (hp : w ∉ K.ptes) :
    IoRS (st := st) K.ptU Locks s w := by
  refine ⟨hw.1, ?_, Or.inr (own_none (K := K.ptU) hw.2.1)⟩
  rintro (hu | hu)
  · exact hw.2.2 hu
  · exact hp hu

/-- **At a `PmPreF` state the walk reads only `VsW` words off `K.ptes`** (invj's `SlJAtZ.vsRdX`). -/
theorem pm_vsRd (hE : PmPreF st Cs Ω Sg Ac Locks p K μ s) (asid va : U64) (hv : Fl4Proofs.P3.Vs.UserV va) :
    VsRdG st (fun b => VsW K.toKLayout b ∧ ¬ b ∈ K.ptes) s asid va := by
  obtain ⟨hJ, -, hG⟩ := hE
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := id hJ
  obtain ⟨m1, ⟨-, he⟩, hag⟩ := gateAg_of_ep hG
  have hsub : ∀ b, b ∈ K.ptes → Fl4Proofs.P3.Vs.PtW Zx.L1 b := fun b hb => by
    rw [he] at hb; exact ptesR_sub B hag b hb
  exact B.vsRdX hsub asid va hv

end words

end
end Fl4Proofs.P2.E2EP

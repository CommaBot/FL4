/-
# P2 (line p3mc, gen 49): `InsV15V` at the irq starts of U21–U24

The irq certificates `irq_fh_annV` (U21: earliest thread none or foreign), `irq_hn_annV` (U22: homed, wakes nobody),
`irq_wf_annV` (U23: homed, notification waiting with a foreign head waiter) and `irq_wh_annV` (U24: homed, wakes a
thread of `c`) are `PathObl.safe_tr_wr` on their data `irq_fh_cert` / `irq_hn_cert` / `irq_wf_cert` / `irq_wh_cert`
(split out of them in place this generation, statements unchanged; P2/IrqFhAnn, P2/IrqHnAnn, P2/IrqWfAnn,
P2/IrqWhAnn). Their `InsA` twins are `PathObl.insA_narrow_tr_wr` (P2/InsTrWr) on the same
data, once the read and write sets are off the paging words `PWE K E` of the epoch:

* **`irq_fh_rdRT`**, **`irq_hn_rdRT`**, **`irq_wf_rdRT`**, **`irq_wh_rdRT`**: every read word is region-tagged or kernel-static (`RTK`:
  node words, TCB words of the current thread, the release head, the earliest thread, the tree's armed threads and the
  head waiter, homed threads' TCB and `VTABLE` slot words, SC words, the bound notification's words, held-lock
  words (`WPerm`), caller slots, the kernel globals and the IRQ word) or an
  ASID word of the epoch (`AsidW K.ksb E`: the table, and the pools through the table word, which the view keeps
  equal to `E`, `atAF_view`). So none is a `PWE` word (`rt_notPWE'` with "no PTE word" from the read set's `rsE`;
  `pwe_asid`).
* The writes are held at the start (`WPerm` of `own`), and `own` is `.gate` on region `.none`, so no write is a `PWE`
  word (`wperm_region`).
* **`irq_insA_of`** (one proof of the `InsA` twin from the data), **`irq_fh_insA`**, **`irq_hn_insA`**,
  **`irq_wf_insA`**, **`irq_wh_insA`**; **`irq_insA_annV_of`** (the glue of `irq_annV_fh` / `_hn` / `_wf` / `_wh`, once, over `IrqAtG H` and the
  slot certificate `IrqInsCert H`), **`irq_insCerts`**, `IrqPmG`, `IrqCPm`, **`insAP_irq_view`**.

## The open set and the top
* `Open50 s K c ρ k0 i := Open49S … ∧ ¬ IrqCPm K c ρ i` (`IrqCPm`: the irq starts of U21–U24).
* **`insV15NOV50_of_49S`** (`Open50 ⊆ Open49S`), **`insV15NOV49S_of_50`** (at the `IrqCPm` starts by
  `insAP_irq_view`): equivalent for `nativePmKAD B`.
* **`serializable_fl4_V15_pmKADI`** (authoritative): `serializable_fl4_V15_pmKADS` with `InsV15NOV … Open50` [J] for
  `InsV15NOV … Open49S` [J], all other premises unchanged; **`serializable_fl4_V15_pmKADSofI`**: the previous statement
  from it.
* **`irqCPm_irq`**: every irq start is one of U21–U24's, so `Open50` asks the obligation at no irq start: the irq
  slot is closed.

Named premises: `InsV15NOV … Open50` [J] (replaces `InsV15NOV … Open49S` [J]; justification as `InsV15` [J],
P2/E2EPV15AD). New module; existing files touched: P2/IrqFhAnn, P2/IrqHnAnn, P2/IrqWfAnn, P2/IrqWhAnn (the `…_cert` splits, every
existing statement byte-identical).

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `insV15NOV50_of_49S`,
`serializable_fl4_V15_pmKADI`, `serializable_fl4_V15_pmKADSofI`.
-/
import Fl4Proofs.P2.InsV15O49S
import Fl4Proofs.P2.InsTrWr
import Fl4Proofs.P2.E2EPU21
import Fl4Proofs.P2.E2EPU24
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll VEq Safe InsA InsAP insAP_of_insA narrowSP PO HeldV)
open Fl4Proofs.P3.Vs (atA peA)
open Fl4Proofs.P2.CoreView (view)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

/-- A word held for writing is region-tagged (`own` is `.gate` on region `.none`). -/
theorem wperm_region {K : KLayout} {c : U64} {lk : U64 → Prop} {m : U64 → U64} {b : U64}
    (h : PathObl.WPerm (OwnMap.own K) c lk m b) : region K b ≠ .none := by
  intro hr
  unfold PathObl.WPerm OwnMap.own at h
  rw [hr] at h
  exact h

section rd
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **Every word of `IrqFhRd` is region-tagged, kernel-static or an ASID word of the epoch** (module docstring). -/
theorem irq_fh_rdRT {K : KLayoutP} {E : U64 → U64} {c : U64} {ρ : U64 → U64} {irq : U64} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hirq : irq.val < 128)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    ∀ b, IrqFhRd st (Heap.scBits K.toKLayout.heap) irq σ b → RTK K.toKLayout b ∨ AsidW K.ksb E b := by
  have hX := hJ.regionOKX
  obtain ⟨hk, -⟩ := hJ.kc
  obtain ⟨Ω, Ac, EM⟩ := IrqPreJ3.entM (st := st) (K := K.toKLayout) (m := L.mem σ) (s := σ) (irq := irq)
    ⟨hJ, fun _ _ _ => rfl⟩
  have E0 := EM.ent
  have hI := E0.inv
  have hY := E0.ly
  have h0 := hI.1.choose_spec.choose_spec
  have hN : NodePlaced st (Heap.tcbs K.toKLayout.heap) σ (L.cpu σ) := h0.nodes _ h0.cur
  have hcT : L.curW σ ∈ Heap.tcbs K.toKLayout.heap := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have hcs : L.cscW σ ∈ Heap.scs K.toKLayout.heap := hI.2.2.1.2.2.cur
  have rN : ∀ o : U64, o.val < 4288 → RTK K.toKLayout (L.nodeAt σ (L.cpu σ) o) := fun o ho =>
    PathObl.SlJAt.rtNode hJ hN ho
  have rC : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 →
      RTK K.toKLayout (core.num.U64.wrapping_add (L.curW σ) k) := fun k h1 h2 h3 =>
    rtk_tcb hX htH (by omega) h2 h3
  have rKs : ∀ o : U64, o.val < 13568 → RTK K.toKLayout (core.num.U64.wrapping_add (L.ksb σ) o) := fun o ho =>
    Or.inr ⟨o, ho, by rw [hk]⟩
  intro b hb
  rcases hb with hb | ⟨hne, rfl⟩
  · rcases hb with ⟨o, ho, -, rfl⟩ | ⟨k, h1, h2, h3, -, -, -, rfl⟩ | ⟨-, -, hb⟩ | ⟨hne, rfl⟩ |
        ⟨o, ho, rfl⟩ | ⟨-, i, hi, rfl⟩ | ⟨-, hi, hhi, rfl | ⟨lo, hlo, hne, rfl⟩⟩
    · exact Or.inl (rN o ho)
    · exact Or.inl (rC k h1 h2 h3)
    · rcases hb with ⟨o, ho, -, rfl⟩ | ⟨k, h1, h2, h3, -, -, -, rfl⟩ | hb | ⟨hne, rfl | hb⟩ | ⟨hne, rfl⟩ |
          ⟨k, hk', hk32, -, rfl⟩
      · exact Or.inl (rN o ho)
      · exact Or.inl (rC k h1 h2 h3)
      · exact Or.inl (rtk_sc hX (st_scH (K := K) hcs) hb)
      · obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne
        exact Or.inl (rtk_tcb hX (show K.toKLayout.heap _ = some .tcb from r1) (o := 3464#u64) (by simp)
          (by simp) (by simp))
      · obtain ⟨-, -, -, r4, -⟩ := rel_facts hI hne
        exact Or.inl (rtk_sc hX (st_scH (K := K) r4) hb)
      · obtain ⟨tmT, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
        exact Or.inl (rtk_tcb hX (show K.toKLayout.heap _ = some .tcb from tmT) (o := 3528#u64) (by simp)
          (by simp) (by simp))
      · obtain ⟨p, hr, -, -⟩ := hY.cs k hk' hk32
        exact Or.inl (rtk_of hr (by simp))
    · obtain ⟨hcs0, -, -⟩ := hI.2.2.1.2.2.bound _ h0.curT hne
      have hcs' : L.mem σ (scA (L.curW σ)) ∈ Heap.scs K.toKLayout.heap := hcs0
      exact Or.inl (rtk_scw hX (st_scH (K := K) hcs') (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    · refine Or.inl (rKs o ?_)
      rcases ho with rfl | rfl | rfl
      · simp [layout.ks.CUR_DOMAIN]
      · simp [layout.ks.DOMAIN_TIME]
      · simp [layout.ks.KERNEL_ROOT]
    · exact Or.inl (rKs i (state_off_lt hirq hi))
    · exact Or.inr (Or.inl ⟨hi, hhi, by rw [hk]; rfl⟩)
    · have e0 : L.mem σ (atAF (L.ksb σ) hi) = E (atA K.ksb hi) := by
        rw [hmm _ (hY.tab hi hhi).1.1 (hY.tabU hi hhi).1, hk, hT hi hhi]
        rfl
      refine Or.inr (Or.inr ⟨hi, hhi, ?_, lo, hlo, ?_⟩)
      · rw [← e0]; exact hne
      · rw [← e0]; rfl
  · obtain ⟨tmT, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
    exact Or.inl (rtk_tcb hX (show K.toKLayout.heap _ = some .tcb from tmT) (o := 3520#u64) (by simp)
      (by simp) (by simp))

end rd

section rdHn
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **Every word of `IrqHnRd` is region-tagged, kernel-static or an ASID word of the epoch** (module docstring;
`irq_fh_rdRT` on `IrqFhRn`, TCB words of the earliest and the tree's armed threads, the bound notification's words). -/
theorem irq_hn_rdRT {K : KLayoutP} {E : U64 → U64} {c : U64} {ρ : U64 → U64} {irq : U64} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hirq : irq.val < 128)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi))
    (htm0 : L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN) ≠ 0#u64) :
    ∀ b, IrqHnRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) irq σ b →
      RTK K.toKLayout b ∨ AsidW K.ksb E b := by
  have hX := hJ.regionOKX
  obtain ⟨Ω, Ac, EM⟩ := IrqPreJ3.entM (st := st) (K := K.toKLayout) (m := L.mem σ) (s := σ) (irq := irq)
    ⟨hJ, fun _ _ _ => rfl⟩
  have E0 := EM.ent
  have hI := E0.inv
  have hY := E0.ly
  have h0 := hI.1.choose_spec.choose_spec
  have hcT : L.curW σ ∈ Heap.tcbs K.toKLayout.heap := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have hcs : L.cscW σ ∈ Heap.scs K.toKLayout.heap := hI.2.2.1.2.2.cur
  have hN : NodePlaced st (Heap.tcbs K.toKLayout.heap) σ (L.cpu σ) := h0.nodes _ h0.cur
  have hFh := irq_fh_rdRT (E := E) hJ hirq hmm hT
  -- the TCB words of a thread of the layout
  have rY : ∀ y k, y ∈ Heap.tcbs K.toKLayout.heap → 192 ≤ k.val → k.val < 4096 → k.val % 8 = 0 →
      RTK K.toKLayout (core.num.U64.wrapping_add y k) := fun y k hy h1 h2 h3 =>
    rtk_tcb hX (show K.toKLayout.heap y = some .tcb from hy) h1 h2 h3
  -- the earliest thread and its bound notification
  have rTm : ∀ k : U64, 192 ≤ k.val → k.val < 4096 → k.val % 8 = 0 →
      RTK K.toKLayout (core.num.U64.wrapping_add (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN)) k) :=
    fun k h1 h2 h3 => rY _ k (tmin_facts (BXI.blk hI) h0.cur htm0).1 h1 h2 h3
  have rNt : L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))) ≠ 0#u64 →
      ∀ k : U64, k.val < 64 → k.val % 8 = 0 → RTK K.toKLayout (core.num.U64.wrapping_add
        (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN)))) k) := by
    intro hb k h1 h2
    have tmT := (tmin_facts (BXI.blk hI) h0.cur htm0).1
    have hNt : L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))) ∈
        K.toKLayout.heap.ntfns := hI.2.2.1.2.2.bnd _ tmT hb
    have hpH : K.toKLayout.heap (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN)))) =
        some .ntfn := hNt
    obtain ⟨r, -, -⟩ := hX.ntW _ hpH k h1 h2
    exact rtk_of r (by simp)
  have rTS := fun hb => rNt hb layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE])
    (by simp [layout.ntfn.TAIL_STATE])
  have rBT := fun hb => rNt hb layout.ntfn.BOUND_TCB (by simp [layout.ntfn.BOUND_TCB])
    (by simp [layout.ntfn.BOUND_TCB])
  intro b hb
  rcases hb with hb | ⟨-, -, hb | ⟨y, hy, -, k, h1, h2, h8, rfl⟩ | ⟨-, hb0, k, hk, h8, rfl⟩⟩ |
      ⟨k, hk, rfl⟩ | ⟨hb0, rfl | rfl⟩
  · exact hFh b (Or.inl hb)
  · rcases hb with ⟨o, ho, -, rfl⟩ | ⟨k, h1, h2, h3, -, -, -, rfl⟩ | hb | ⟨hne, rfl | hb⟩ | ⟨-, hb⟩ |
        ⟨k, hk', hk32, -, rfl⟩
    · exact Or.inl (PathObl.SlJAt.rtNode hJ hN ho)
    · exact Or.inl (rY _ k hcT (by omega) h2 h3)
    · exact Or.inl (rtk_sc hX (st_scH (K := K) hcs) hb)
    · obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne
      exact Or.inl (rY _ 3464#u64 r1 (by simp) (by simp) (by simp))
    · obtain ⟨-, -, -, r4, -⟩ := rel_facts hI hne
      exact Or.inl (rtk_sc hX (st_scH (K := K) r4) hb)
    · rcases hb with ⟨k, hk, rfl⟩ | ⟨-, ⟨k, hk, rfl⟩ | ⟨hb0, rfl | rfl⟩⟩
      · exact Or.inl (rTm k (by rcases hk with e | e | e | e <;> omega) (by rcases hk with e | e | e | e <;> omega)
          (by rcases hk with e | e | e | e <;> omega))
      · exact Or.inl (rTm k (by rcases hk with e | e | e <;> omega) (by rcases hk with e | e | e <;> omega)
          (by rcases hk with e | e | e <;> omega))
      · exact Or.inl (rTS hb0)
      · exact Or.inl (rBT hb0)
    · obtain ⟨p, hr, -, -⟩ := hY.cs k hk' hk32
      exact Or.inl (rtk_of hr (by simp))
  · exact Or.inl (rY y k hy (by omega) (by omega) h8)
  · exact Or.inl (rNt hb0 k hk h8)
  · exact Or.inl (rTm k (by rcases hk with e | e | e | e | e | e <;> omega)
      (by rcases hk with e | e | e | e | e | e <;> omega) (by rcases hk with e | e | e | e | e | e <;> omega))
  · exact Or.inl (rTS hb0)
  · exact Or.inl (rBT hb0)

end rdHn

section rdWf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **Every word of `IrqWfRd` is region-tagged, kernel-static or an ASID word of the epoch** (module docstring;
`irq_hn_rdRT` on `IrqHnRd`, the tree's TCB words, the bound notification's words, the head waiter's `AFFINITY`). -/
theorem irq_wf_rdRT {K : KLayoutP} {E : U64 → U64} {c : U64} {ρ : U64 → U64} {irq : U64} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hirq : irq.val < 128)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi))
    (htm0 : L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN) ≠ 0#u64)
    (hwT : L.mem σ (epHeadA (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))))) ∈
      Heap.tcbs K.toKLayout.heap) :
    ∀ b, IrqWfRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) irq σ b →
      RTK K.toKLayout b ∨ AsidW K.ksb E b := by
  have hX := hJ.regionOKX
  obtain ⟨Ω, Ac, EM⟩ := IrqPreJ3.entM (st := st) (K := K.toKLayout) (m := L.mem σ) (s := σ) (irq := irq)
    ⟨hJ, fun _ _ _ => rfl⟩
  have hI := EM.ent.inv
  have h0 := hI.1.choose_spec.choose_spec
  have hHn := irq_hn_rdRT (E := E) hJ hirq hmm hT htm0
  rintro b ((hb | ⟨-, y, hy, -, k, h1, h2, h8, rfl⟩ | ⟨-, -, hb0, k, hk, h8, rfl⟩) | rfl)
  · exact hHn b hb
  · exact Or.inl (rtk_tcb hX (show K.toKLayout.heap y = some .tcb from hy) (by omega) (by omega) h8)
  · have tmT := (tmin_facts (BXI.blk hI) h0.cur htm0).1
    have hNt : L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN))) ∈
        K.toKLayout.heap.ntfns := hI.2.2.1.2.2.bnd _ tmT hb0
    have hpH : K.toKLayout.heap (L.mem σ (boundA (L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN)))) =
        some .ntfn := hNt
    obtain ⟨r, -, -⟩ := hX.ntW _ hpH k hk h8
    exact Or.inl (rtk_of r (by simp))
  · exact Or.inl (rtk_tcb hX (show K.toKLayout.heap _ = some .tcb from hwT) (o := 3520#u64) (by simp) (by simp)
      (by simp))

end rdWf

section rdWh
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **Every word of `IrqWhRd` is region-tagged, kernel-static or an ASID word of the epoch** (module docstring;
`irq_hn_rdRT` on `IrqHnRd`; `IrqWhRL`: homed threads' TCB words and `VTABLE` slot words, SC words, held-lock
words). -/
theorem irq_wh_rdRT {K : KLayoutP} {E : U64 → U64} {c : U64} {ρ : U64 → U64} {lk : U64 → Prop} {irq : U64} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hirq : irq.val < 128)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi))
    (htm0 : L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN) ≠ 0#u64) :
    ∀ b, IrqWhRd st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap)
      (Heap.scBits K.toKLayout.heap) lk ρ c irq σ b → RTK K.toKLayout b ∨ AsidW K.ksb E b := by
  have hX := hJ.regionOKX
  have hK0 := hJ.regionOK
  obtain ⟨Ω, Ac, EM⟩ := IrqPreJ3.entM (st := st) (K := K.toKLayout) (m := L.mem σ) (s := σ) (irq := irq)
    ⟨hJ, fun _ _ _ => rfl⟩
  have hI := EM.ent.inv
  have hL := EM.ent.lay
  have hHn := irq_hn_rdRT (E := E) hJ hirq hmm hT htm0
  rintro b (hb | ⟨y, hy, -, k, h1, h2, h3, -, -, rfl⟩ | ⟨p, hp, -, -, -, hb⟩ | ⟨y, hy, -, hb⟩ | ⟨-, hb⟩)
  · exact hHn b hb
  · exact Or.inl (rtk_tcb hX (show K.toKLayout.heap y = some .tcb from hy.1) (by omega) h2 h3)
  · exact Or.inl (rtk_sc hX (st_scH (K := K) hp) hb)
  · obtain ⟨r1, r2⟩ := rtk_tslot hK0 hX (show K.toKLayout.heap y = some .tcb from hy.1)
      (i := layout.tcb.SLOT_VTABLE) (by simp [layout.tcb.SLOT_VTABLE])
    rcases hb with rfl | rfl
    · rw [vtA_slot]; exact Or.inl r1
    · rw [vtA_slot]; exact Or.inl r2
  · exact Or.inl (Or.inl (wperm_region (lkw_own hI hL (lk := lk) (Lk := lk) (fun _ h => h) hb).1))

end rdWh

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The `InsA` twin of an irq certificate from its data** (module docstring): the data `safe_tr_wr` takes, the
writes' `WPerm` at the start and the read words region-tagged, kernel-static or ASID words of the epoch. -/
theorem irq_insA_of {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A} (hc : L.cpu σ = c)
    {Rd Wd : U64 → Prop} {E : U64 → U64} (hcv : K.ptes = ptesR K E)
    (hal : ∀ b, Rd b → Aligned b)
    (hR0 : ∀ q, Rd q → (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q) ∧ ¬ q ∈ K.user)
    (hWd : ∀ x, Wd x → Aligned x ∧ (¬ x ∈ K.user → HeldV c hs (ownP K μ x)))
    (hRPO : ∀ q, ¬ q ∈ K.user → (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q) →
      PO c hs (ownP K μ q))
    (hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st Rd Wd) ar (R.localtimer.handle_timer_irq_local irq pl) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.localtimer.handle_timer_irq_local irq pl) s a)
    (hWp : ∀ x, Wd x → PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) x)
    (hRT : ∀ b, Rd b → RTK K.toKLayout b ∨ AsidW K.ksb E b) :
    InsA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localtimer.handle_timer_irq_local irq pl) ∅ a)) := by
  refine PathObl.insA_narrow_tr_wr (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar adEq_equiv (moveHeldP hK) (ownDepP hK hU) (masksWr_plain st) (pwe_own hK)
    (fun x hx => pwe_ko hK μ hx) (fun b hb => pwe_user hU hb) (a := a)
    (R.localtimer.handle_timer_irq_local irq pl) (irq_noZero irq pl) hc
    (R0 := rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (Qv := VO K c ρ) (Rd := Rd) (Wd := Wd)
    (fun b hb => vo_of_pwe hK hb) hal hR0 ?_ ?_ hWd hRPO (fun x hx => hV.2.1 x hx) hgo
  · intro b hb
    rcases hRT b hb with hr | ha
    · exact rt_notPWE' hK (hR0 b hb).1.1.2 hr
    · exact pwe_asid hcv ha
  · intro b hb
    exact Or.inr fun hp => wperm_region (hWp b hb) (pwe_region hK hp)

set_option maxHeartbeats 4000000 in
/-- **The `InsA` twin of `irq_fh_annV`** (module docstring). -/
theorem irq_fh_insA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ) (hirq : irq.val < 128)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hF : ρ (tmA (L := L) σ) ≠ 0#u64 → ρ (affA (ρ (tmA (L := L) σ))) ≠ c)
    {E : U64 → U64} (hcv : K.ptes = ptesR K E)
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    InsA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localtimer.handle_timer_irq_local irq pl) ∅ a)) := by
  obtain ⟨hal, hR0, hWd, hRPO, hgo, hWp⟩ := irq_fh_cert ar hA hK hU nv hV hJ hq hirq hc hl hmm hF
  exact irq_insA_of ar hK hU hV hc hcv hal hR0 hWd hRPO hgo hWp (irq_fh_rdRT hJ hirq hmm hT)

set_option maxHeartbeats 4000000 in
/-- **The `InsA` twin of `irq_hn_annV`** (module docstring). -/
theorem irq_hn_insA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ) (hirq : irq.val < 128)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hH : ρ (tmA (L := L) σ) ≠ 0#u64 ∧ ρ (affA (ρ (tmA (L := L) σ))) = c ∧ NoWakeR ρ (ρ (tmA (L := L) σ)))
    {E : U64 → U64} (hcv : K.ptes = ptesR K E)
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    InsA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localtimer.handle_timer_irq_local irq pl) ∅ a)) := by
  obtain ⟨hal, hR0, hWd, hRPO, hgo, hWp, htm0⟩ := irq_hn_cert ar hA hK hU nv hV hJ hq hirq hc hl hmm hH
  exact irq_insA_of ar hK hU hV hc hcv hal hR0 hWd hRPO hgo hWp (irq_hn_rdRT hJ hirq hmm hT htm0)

set_option maxHeartbeats 4000000 in
/-- **The `InsA` twin of `irq_wf_annV`** (module docstring). -/
theorem irq_wf_insA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ) (hirq : irq.val < 128)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hH : IrqWfR ρ c (ρ (tmA (L := L) σ)))
    {E : U64 → U64} (hcv : K.ptes = ptesR K E)
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    InsA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localtimer.handle_timer_irq_local irq pl) ∅ a)) := by
  obtain ⟨hal, hR0, hWd, hRPO, hgo, hWp, htm0, hwT⟩ := irq_wf_cert ar hA hK hU nv hV hJ hq hirq hc hl hmm hH
  exact irq_insA_of ar hK hU hV hc hcv hal hR0 hWd hRPO hgo hWp (irq_wf_rdRT hJ hirq hmm hT htm0 hwT)

set_option maxHeartbeats 4000000 in
/-- **The `InsA` twin of `irq_wh_annV`** (module docstring). -/
theorem irq_wh_insA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ) (hirq : irq.val < 128)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hPL : PlanLk lk pl) (hH : IrqWhR ρ c (ρ (tmA (L := L) σ)))
    {E : U64 → U64} (hcv : K.ptes = ptesR K E)
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi)) :
    InsA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localtimer.handle_timer_irq_local irq pl) ∅ a)) := by
  obtain ⟨hal, hR0, hWd, hRPO, hgo, hWp, htm0⟩ := irq_wh_cert ar hA hK hU nv hV hJ hq hirq hc hl hmm hPL hH
  exact irq_insA_of ar hK hU hV hc hcv hal hR0 hWd hRPO hgo hWp (irq_wh_rdRT hJ hirq hmm hT htm0)

end main

section glue
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- The irq starts whose earliest thread `t := ρ (irqTmW K.ksb c)` satisfies `H ρ c t` (U21–U24's `IrqFhAt`,
`IrqHnAt`, `IrqWfAt`, `IrqWhAt` are instances). -/
def IrqAtG (H : (U64 → U64) → U64 → U64 → Prop) (K : KLayoutP) (c : U64) (ρ : U64 → U64) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.irq _) => H ρ c (ρ (irqTmW K.ksb c))
  | _ => False

/-- The certificate an irq start of `IrqAtG H` asks: the `InsA` twin at every view start of the slot. -/
def IrqInsCert (H : (U64 → U64) → U64 → U64 → Prop) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64)
    (ρ : U64 → U64) (E : U64 → U64) : Prop :=
  ∀ (lk : S → U64 → Prop) (irq : U64) (pl : localtimer.TimerIrqPlan) (σ : S) (a : A),
    SlJAt (L := L) K.toKLayout σ → QPs K st σ → irq.val < 128 → L.cpu σ = c → lk σ = (fun l => s.lk l = some c) →
    (∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) → PlanLk lk pl →
    H ρ c (ρ (tmA (L := L) σ)) → InsA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) c
      (fun l => s.lk l = some c) s.mem
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localtimer.handle_timer_irq_local irq pl) ∅ a))

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsA` at every irq start of `IrqAtG H`** from the slot's certificate (the glue of
`irq_annV_fh` / `irq_annV_hn` / `irq_annV_wf` / `irq_annV_wh`, once). -/
theorem irq_insA_annV_of {H : (U64 → U64) → U64 → U64 → Prop} {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} {E : U64 → U64}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hcert : IrqInsCert st ar H s K c ρ E) (hf : IrqAtG (S := S) H K c ρ i) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · obtain ⟨σe, hC'⟩ := hC
    obtain ⟨hLk, hG0⟩ := hsf
    obtain ⟨q0, ⟨h1, hG⟩, e⟩ := hG0 (fun s _ => hLk.kernDetS _ s)
    obtain ⟨σ', a, hCh, hc, hl, hμ, rfl⟩ := hG
    subst e
    have hJ : SlJAt (L := L) K.toKLayout σ' := ChainOf.bun hC' σ' hCh
    have h1' : K.toKLayoutV.vcpus = ∅ ∧ IrqPremK2B st j K.toKLayoutV (view K.toKLayout c ρ) := h1
    have hc' : L.cpu σ' = c := hc
    have hl' : j.lk σ' = (fun l => s.lk l = some c) := hl
    have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x := hμ
    obtain ⟨s1, ⟨nv, he⟩, hkeep⟩ := hE
    have hq : QPs K st σ' :=
      qPs_of_convRN (S' := S) (st' := st) (L' := L) (L := L) (σ := σ') he nv ⟨σ', hJ⟩ hkeep hJ.kc.1 hmm
    have etm : tmA (L := L) σ' = irqTmW K.ksb c := irqTmW_eq hq.ksb hc'
    have hF : H ρ c (ρ (tmA (L := L) σ')) := by
      rw [etm]; exact hf
    unfold annV
    rw [hM.own, hM.cls, hM.ko]
    have h := hcert j.lk j.irq j.pl σ' a hJ hq h1'.2.lt hc' hl' hmm h1'.2.pl hF
    have h' : InsA (PWE K E) ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) c
        (fun l => s.lk l = some c) s.mem (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) c
          (VO K c ρ) ∅
          (tr (fun x => MaxR (userV K.toKLayoutV) st j.lk σ' x ∧ ¬ x ∈ K.ptes) (· ∈ K.user)
            (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ') (masksOf st σ') ar
            (R.localtimer.handle_timer_irq_local j.irq j.pl) ∅ a)) := h
    rw [tr_cut (MaxR (userV K.toKLayoutV) st j.lk σ') (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ') (masksOf st σ') ar
      (R.localtimer.handle_timer_irq_local j.irq j.pl) ∅ a] at h'
    convert h' using 3
    unfold LocalPath.body
    rw [hc]
    all_goals rfl
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf

set_option maxHeartbeats 4000000 in
/-- **The four irq certificates at a view start without a VCPU** (`irq_fh_insA`, `irq_hn_insA`, `irq_wf_insA`,
`irq_wh_insA` with `atAF_view`). -/
theorem irq_insCerts (hA : P0.ArchTotal ar) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (hK : RegionOKP K) (hU : UserOKP K) {c : U64} {ρ : U64 → U64} (E : U64 → U64) (nv : K.vcpus = ∅)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s) (hM : MapsP K s)
    (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    IrqInsCert st ar (fun ρ c t => t ≠ 0#u64 → ρ (affA t) ≠ c) s K c ρ E ∧
      IrqInsCert st ar (fun ρ c t => t ≠ 0#u64 ∧ ρ (affA t) = c ∧ NoWakeR ρ t) s K c ρ E ∧
      IrqInsCert st ar (fun ρ c t => IrqWfR ρ c t) s K c ρ E ∧
      IrqInsCert st ar (fun ρ c t => IrqWhR ρ c t) s K c ρ E := by
  have hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi) :=
    fun hi hhi => atAF_view L J nv hM hV (bun_of_chain st (arI := arI) (AR := AR) (MR := MR) hC) hhi
  rw [hM.own, hM.cls, hM.ko] at hV
  exact ⟨fun lk irq pl σ a hJ hq hirq hc hl hmm _ hH =>
      irq_fh_insA ar hA hK hU nv hV hJ hq hirq hc hl hmm hH J.conv hT,
    fun lk irq pl σ a hJ hq hirq hc hl hmm _ hH => irq_hn_insA ar hA hK hU nv hV hJ hq hirq hc hl hmm hH J.conv hT,
    fun lk irq pl σ a hJ hq hirq hc hl hmm _ hH => irq_wf_insA ar hA hK hU nv hV hJ hq hirq hc hl hmm hH J.conv hT,
    fun lk irq pl σ a hJ hq hirq hc hl hmm hPL hH =>
      irq_wh_insA ar hA hK hU nv hV hJ hq hirq hc hl hmm hPL hH J.conv hT⟩

end glue

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The irq indices of the PageMap index type whose earliest thread satisfies `H` (`IrqAtG` lifted). -/
def IrqPmG (H : (U64 → U64) → U64 → U64 → Prop) (K : KLayoutP) (c : U64) (ρ : U64 → U64) : IxV13Pm S → Prop
  | .inl (.inl (.irq _)) => H ρ c (ρ (irqTmW K.ksb c))
  | _ => False

/-- **The irq starts closed this generation** (U21–U24: earliest thread none or foreign; homed and waking nobody;
homed with a waiting notification whose head waiter is foreign; homed and waking a thread of `c`). -/
def IrqCPm (K : KLayoutP) (c : U64) (ρ : U64 → U64) (i : IxV13Pm S) : Prop :=
  IrqPmG (fun ρ c t => t ≠ 0#u64 → ρ (affA t) ≠ c) K c ρ i ∨
    IrqPmG (fun ρ c t => t ≠ 0#u64 ∧ ρ (affA t) = c ∧ NoWakeR ρ t) K c ρ i ∨
    IrqPmG (fun ρ c t => IrqWfR ρ c t) K c ρ i ∨ IrqPmG (fun ρ c t => IrqWhR ρ c t) K c ρ i

/-- **Every irq start is one of U21–U24's** (by cases on the earliest thread, its `AFFINITY`, `NoWakeR` and the head
waiter's `AFFINITY`): `Open50` asks the obligation at no irq start. -/
theorem irqCPm_irq (K : KLayoutP) (c : U64) (ρ : U64 → U64) (j : _) :
    IrqCPm (S := S) K c ρ (.inl (.inl (.irq j))) := by
  show (_ ∨ _ ∨ _ ∨ _)
  simp only [IrqPmG]
  generalize ρ (irqTmW K.ksb c) = t
  by_cases h0 : t = 0#u64
  · exact Or.inl fun h => absurd h0 h
  by_cases ha : ρ (affA t) = c
  · by_cases hw : NoWakeR ρ t
    · exact Or.inr (Or.inl ⟨h0, ha, hw⟩)
    by_cases hwt : (ρ (epTSA (ρ (boundA t))) &&& 3#u64) = obj.NTFN_WAITING
    · by_cases hh : ρ (affA (ρ (epHeadA (ρ (boundA t))))) = c
      · exact Or.inr (Or.inr (Or.inr ⟨h0, ha, hw, fun _ => hh⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h0, ha, fun e => hw (Or.inl e), hwt, hh⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h0, ha, hw, fun h => absurd h hwt⟩))
  · exact Or.inl fun _ => ha

set_option maxHeartbeats 4000000 in
/-- **`InsV15V`'s obligation of `nativePmKAD B` at an irq start of `IrqPmG H`** from the slot's certificate. -/
theorem insAP_irq_view (B : PmObl7 st Cs Ω Sg Ac Locks) {H : (U64 → U64) → U64 → U64 → Prop} {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {E : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : IrqPmG (S := S) H K c ρ i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hcert : IrqInsCert st ar H s K c ρ E)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (((j | j | j | j | j | j | j) | j) | j)
  all_goals try exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inl (.irq j))) := fun h => h
  rw [if_pos hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inl (.irq j)) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  exact insAP_of_insA (irq_insA_annV_of st ar hA a0 hC (epochPteN_view_of J nv hM hV) hsf' hM hcert hx)

/-- **The view starts at which the obligation is still asked after gen 49's irq step** (module docstring). -/
def Open50 (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (ρ : U64 → U64) (k0 : SP) (i : IxV13Pm S) : Prop :=
  Open49S st s K c ρ k0 i ∧ ¬ IrqCPm (S := S) K c ρ i

set_option maxHeartbeats 4000000 in
/-- **`InsV15NOV … Open50` gives `InsV15NOV … Open49S`** for `nativePmKAD B` (module docstring). -/
theorem insV15NOV49S_of_50 (B : PmObl7 st Cs Ω Sg Ac Locks)
    (h : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open50 st)) :
    InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open49S st) := by
  intro Ch s K E hK hU c k0 ρ i nv hO hC J hM hVq hi
  by_cases hl : IrqCPm (S := S) K c ρ i
  · obtain ⟨c1, c2, c3, c4⟩ := irq_insCerts st ar hA hK hU E nv hC J hM hVq
    rcases hl with hx | hx | hx | hx
    · exact insAP_irq_view st ar hA a0 B nv hx hC J hM hVq c1 hi
    · exact insAP_irq_view st ar hA a0 B nv hx hC J hM hVq c2 hi
    · exact insAP_irq_view st ar hA a0 B nv hx hC J hM hVq c3 hi
    · exact insAP_irq_view st ar hA a0 B nv hx hC J hM hVq c4 hi
  exact h Ch s K E hK hU c k0 ρ i nv ⟨hO, hl⟩ hC J hM hVq hi

/-- **`serializable_fl4_V15_pmKADI` on the re-based platform**
(gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem serializable_fl4_V15_pmKADI_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    (hI : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open50 st))
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitC P.toC K0.toKLayoutV (Ch0 e))
    (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15C (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) P.toC s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_V15_pmKADS_C st ar hA a0 P B (insV15NOV49S_of_50 st ar hA a0 B hI) h0 hA0 hB hc0 hM0 h hq

end pm

end
end Fl4Proofs.P2.E2EP

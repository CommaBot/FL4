/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch6 (B)): **`schedule` and
`finish` at `J` without `σ.domainTime ≠ 0`**, up to the FPU.

XTopJointSchedRF2's `jat_scheduleWP0F` ends at SchedRel level: `JAtZ` after
the timers at `rf`/`σ1`, FL4's writes from there in `KFootN` (KFoot plus
`next_domain`'s DOMAIN_TIME / DOM_SCHED_IDX / WORK_UNITS words), and the spec
outcome `schedule σ1 = {σ'}`. The tail of `jat_scheduleFRF` needs `JAtZ` at a
state from which the writes are in `KFoot`. Here that state is a *fake
pre-state*:

* FL4: `ndF rf.1 kb v16 v24 v40` = `rf.1` with the three `NdW` words set to
  their values in the final state; spec: `ndFSt σ1 v16.bv di` = `σ1` with
  the domain time and index replaced.
* `schedStep_dom2`: the DOMAIN_TIME / DOM_SCHED_IDX writes are a scheduler
  step (`SchedStep`, DomDecode's `schedStep_start` without the start word),
  so `JAtZ.schedJ` keeps `JAtZ`; WORK_UNITS by `JAtZ.workUnitsJD`
  (`JAtZ.ndFJ`).
* `ndF_writes`: from the fake state the writes are in `KFoot` (the `NdW`
  words agree with the final state by construction).
* Every spec fact of the tail (`SchS`, `LK`, the idle fields) reads neither
  the domain time nor the index, so the facts for `σ1 → σ'` are the facts
  for `ndFSt σ1 … → σ'` by definitional unfolding; `JAtZ.sch_tailS` is
  `JAtZ.sch_tail` taking them instead of `schedule σ = {σ'}`.

`jat_scheduleFR2` / `jat_scheduleSR2` / `jat_finishJ2`: `jat_scheduleFRF` /
`jat_scheduleSRF` / `jat_finishJF` with `hd : σ.domainTime ≠ 0 ∨ NdOK s σ`
(NdOK's [J] facts at the entry, sch2/sch3) and `ArchNdF` [P]; `hTail`'s
footprint is `KFootN`. They supersede the `F` versions.
-/
import Fl4Proofs.P3.SchedIdx
import Fl4Proofs.P3.XTopJointSchedR
import Fl4Proofs.P3.ScScheduleF
import Fl4Proofs.P3.ScFpuOwnK
import Fl4Proofs.P3.G7dVsRoot
import Fl4Proofs.P3.ScNextDomCF
import Fl4Proofs.P3.JEntryIrq
import Fl4Proofs.P3.XTopJointCopyRegs
import Fl4Proofs.P3.XTopJointPP
import Fl4Proofs.P3.BufAtJR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- FL4's DOMAIN_TIME / DOM_SCHED_IDX words written. -/
def ndF2 (s : S) (kb v16 v24 : U64) : S :=
  L.wr (L.wr s (ksW kb 16#u64) v16) (ksW kb 24#u64) v24

/-- The fake pre-state: the three `NdW` words written. -/
def ndF (s : S) (kb v16 v24 v40 : U64) : S :=
  L.wr (ndF2 (L := L) s kb v16 v24) (ksW kb 40#u64) v40

/-- The spec's fake pre-state: domain time and index replaced. -/
def ndFSt (σ : Fl4Spec.State Unit) (dt : BitVec 64) (di : Nat) : Fl4Spec.State Unit :=
  { σ with domainTime := dt, domainIndex := di }

/-- **The DOMAIN_TIME / DOM_SCHED_IDX writes as a scheduler step** (as
DomDecode's `schedStep_start`, without the start word). -/
theorem schedStep_dom2 (th : TypedHeap) (s1 : S) (σ1 : Fl4Spec.State Unit) {kb : U64} (v16 v24 : U64) (di : Nat)
    (hk1 : L.ksb s1 = kb) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) (h24 : v24 = 0#u64) :
    SchedStep (L := L) th s1 σ1 (ndF2 (L := L) s1 kb v16 v24) (ndFSt σ1 v16.bv di) := by
  subst hk1
  set kb := L.ksb s1
  have hw : P1.WritesIn st s1 (ndF2 (L := L) s1 kb v16 v24) (DomKW kb) :=
    wtrans (writesIn_ksW s1 v16 hkf hka (o := 16#u64) (by simp)) (writesIn_ksW _ v24 hkf hka (o := 24#u64) (by simp))
  have hw4 : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 24 →
      L.mem (ndF2 (L := L) s1 kb v16 v24) (ksW kb o) = L.mem s1 (ksW kb o) := by
    intro o ho h8 n16 n24
    rw [ndF2, mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n24.symm),
      mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n16.symm)]
  have h16 : L.mem (ndF2 (L := L) s1 kb v16 v24) (ksW kb 16#u64) = v16 := by
    rw [ndF2, mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
      mem_ks_same _ _ hkf hka (by decide) (by decide)]
  refine ⟨by constructor <;> rfl, fun N T C c _ hS _ => ⟨hS.domW hw (by constructor <;> rfl) rfl rfl ?_,
    hw.mono fun b hb => Or.inr (Or.inr hb), fun hD => ?_⟩, ⟨fun d p _ hu => Or.inl ⟨d, p, hu⟩, Or.inr rfl⟩,
    blkKeep_domKW hw hka⟩
  · show v16.bv = (L.mem (ndF2 (L := L) s1 kb v16 v24) (ksW kb 16#u64)).bv
    rw [h16]
  · obtain ⟨hl1, hent1, hst1⟩ := domRel_iff.2 hD
    refine domRel_iff.1 ⟨hl1, fun i hi => ?_, by
      rw [hw4 _ (by decide) (by decide) (by decide) (by decide)]; exact hst1.1, by
      rw [ndF2, mem_ks_same _ _ hkf hka (by decide) (by decide)]; exact h24⟩
    obtain ⟨b1, b2, b3, b4, -, b6, b7, -, b9, b10⟩ := dur_off_bounds hi
    rw [hw4 _ b1 b2 b6 b7, hw4 _ b3 b4 b9 b10]
    exact hent1 i hi

theorem ndF_ksb (s : S) (kb v16 v24 v40 : U64) : L.ksb (ndF (L := L) s kb v16 v24 v40) = L.ksb s := by
  simp only [ndF, ndF2, P1.LawfulStore.ksb_wr]

theorem ndF_cpu (s : S) (kb v16 v24 v40 : U64) : L.cpu (ndF (L := L) s kb v16 v24 v40) = L.cpu s := by
  simp only [ndF, ndF2, P1.LawfulStore.cpu_wr]

/-- The fake state's words off the three `NdW` words. -/
theorem ndF_mem_ne (s : S) {kb : U64} (v16 v24 v40 : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0)
    {b : U64} (hb : P1.Aligned b) (hn : ¬ NdW kb b) : L.mem (ndF (L := L) s kb v16 v24 v40) b = L.mem s b := by
  have hn' : ¬ (b = ksW kb 16#u64 ∨ b = ksW kb 24#u64 ∨ b = ksW kb 40#u64) := hn
  rw [ndF, ndF2, L.mem_wr _ _ _ _ (ksW_al hkf hka (by decide) (by decide)) hb,
    if_neg (fun e => hn' (Or.inr (Or.inr e.symm))),
    L.mem_wr _ _ _ _ (ksW_al hkf hka (by decide) (by decide)) hb, if_neg (fun e => hn' (Or.inr (Or.inl e.symm))),
    L.mem_wr _ _ _ _ (ksW_al hkf hka (by decide) (by decide)) hb, if_neg (fun e => hn' (Or.inl e.symm))]

theorem ndF_mem16 (s : S) {kb : U64} (v16 v24 v40 : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) :
    L.mem (ndF (L := L) s kb v16 v24 v40) (ksW kb 16#u64) = v16 := by
  rw [ndF, ndF2, mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
    mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
    mem_ks_same _ _ hkf hka (by decide) (by decide)]

theorem ndF_mem24 (s : S) {kb : U64} (v16 v24 v40 : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) :
    L.mem (ndF (L := L) s kb v16 v24 v40) (ksW kb 24#u64) = v24 := by
  rw [ndF, ndF2, mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
    mem_ks_same _ _ hkf hka (by decide) (by decide)]

theorem ndF_mem40 (s : S) {kb : U64} (v16 v24 v40 : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) :
    L.mem (ndF (L := L) s kb v16 v24 v40) (ksW kb 40#u64) = v40 := by
  rw [ndF, mem_ks_same _ _ hkf hka (by decide) (by decide)]

/-- **From the fake state, FL4's writes are in `KFoot`** (module docstring). -/
theorem ndF_writes {T N C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit} (di : Nat)
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hw : P1.WritesIn st s s' (KFootN st T N C c s σ)) :
    P1.WritesIn st (ndF (L := L) s (L.ksb s) (L.mem s' (ksW (L.ksb s) 16#u64)) (L.mem s' (ksW (L.ksb s) 24#u64))
        (L.mem s' (ksW (L.ksb s) 40#u64))) s'
      (KFoot st T N C c (ndF (L := L) s (L.ksb s) (L.mem s' (ksW (L.ksb s) 16#u64))
        (L.mem s' (ksW (L.ksb s) 24#u64)) (L.mem s' (ksW (L.ksb s) 40#u64)))
        (ndFSt σ (L.mem s' (ksW (L.ksb s) 16#u64)).bv di)) := by
  have hk := ndF_ksb (L := L) s (L.ksb s) (L.mem s' (ksW (L.ksb s) 16#u64)) (L.mem s' (ksW (L.ksb s) 24#u64))
    (L.mem s' (ksW (L.ksb s) 40#u64))
  refine ⟨hw.1.trans hk.symm, hw.2.1.trans (ndF_cpu (L := L) _ _ _ _ _).symm, fun b hb hn => ?_⟩
  by_cases hN : NdW (L.ksb s) b
  · rcases hN with rfl | rfl | rfl
    · rw [ndF_mem16 _ _ _ _ hkf hka]
    · rw [ndF_mem24 _ _ _ _ hkf hka]
    · rw [ndF_mem40 _ _ _ _ hkf hka]
  · rw [ndF_mem_ne _ _ _ _ hkf hka hb hN]
    refine hw.2.2 b hb fun h => ?_
    rcases h with (h | h | h) | h
    · exact hn (Or.inl ((SFoot.ksb hk).2 h))
    · exact hn (Or.inr (Or.inl h))
    · exact hn (Or.inr (Or.inr h))
    · exact hN h

set_option maxHeartbeats 4000000 in
/-- The spec step's facts read neither the domain time nor the index. -/
theorem SchS.ndF {σ σ' : Fl4Spec.State Unit} (h : SchS σ σ') (dt : BitVec 64) (di : Nat) :
    SchS (ndFSt σ dt di) σ' :=
  ⟨⟨h.1.kh, h.1.um, h.1.cdt, h.1.orig, h.1.dl, h.1.dsi, h.1.io, h.1.gpml4, h.1.huge, h.1.asid, h.1.ist, h.1.inode, h.1.isc⟩,
    ⟨h.2.kh, h.2.cdt, h.2.orig, h.2.dl, h.2.dsi, h.2.isc⟩⟩

end

end

end Fl4Proofs.P3

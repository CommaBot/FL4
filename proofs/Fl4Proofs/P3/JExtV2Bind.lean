/-
P3x for virtualization (line virt, gen 27, items 3-4): **pieces of mmuAD's `JAtZV4` migration that live in new files
on this branch** (handoff `# gen 26`, item 3), and **`NoIoTcb` across the steps that write TCB slots**.

* **`JExtV2.unbind_w`**, **`JExtV2.bind_w`**: JExtVSteps' `JExtV.unbind_w` / `JExtV.bind_w` at `JExtV2` (same
  proofs over P3/JExtV2's `JExtV2.unbind` / `JExtV2.bind`); mmuAD's JAtZBBind / JAtZBVcpuX use the `JExtV` ones.
* `NoIoTcb` frames: **`NoIoTcb.of_capEq`** (the TCB slots' caps kept), **`NoIoTcb.of_writes`** (a footprint missing
  `JW`, as `JExtV2.of_writes`: every slot word is a `JW` word), **`NoIoTcb.two_w`** (the bind / unbind two-word
  footprint `{vTcbA v, tVcpuA t}`).
* **`NoIoTcb.of_instFr`** — the TCB-slot installs (TcbCaps' `InstFr`, the slot frame of `tcb::install_tcb_cap`,
  tcb.rs l. 68-75, and `tcb::install_buffer`, l. 88-100, in their `InstPost`): every slot outside the target TCB's is
  kept, emptied or a home zombie (`ChgZ`), so `NoIoTcb` there is the entry's; the target's slots are `ChgZ` or
  derived (`TcbDer`), and a derived slot must not hold an owned IO-port cap (`ht`, a state hypothesis: `TcbDer`
  records only the shape of *some* slot's cap, so the installed cap is not visible in `InstFr`; at FL4 it is the
  `new_cap` of the call — a CNode root (tcb.rs l. 189-192), a PML4 (l. 193-196), an endpoint (fault / timeout
  handler, `valid_fault_handler`, faults.rs l. 57-63; slot 3 is an endpoint by `TcbDer` itself), a frame
  (`install_buffer`, vspace.rs l. 179) — none an `IoPort`). `NoIoTcb.of_instFr3` discharges slot 3.
* `TCBSetEPTRoot` (tcb.rs l. 410-417): only the decode is proved on this branch (P3/VirtSetEptDec: FL4's decode *is*
  `setEptRootF` = delete the EPT slot, insert the decoded `Ept` cap); its perform half has no P3 post yet, so no
  `NoIoTcb` lemma is stated for it here (once a post gives "the EPT slot is `Null` or the `Ept` cap, the other TCB
  slots kept", `NoIoTcb.of_capEq` and a one-slot case give it).

No named premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.JExtV2
import Fl4Proofs.P3.TcbCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {V X : Set U64} {th : TypedHeap} {s s' : S}

/-- **Unbinding from a two-word footprint** (`JExtV.unbind_w` at `JExtV2`, same proof). -/
theorem JExtV2.unbind_w (E : JExtV2 (L := L) V X th s) (P : JWPl V th) {t v : U64} (ht : th t = some .tcb)
    (hv : v ∈ V) (htv : L.mem s (tVcpuA t) = v) (hvt : L.mem s (vTcbA v) = t)
    (hW : P1.WritesIn st s s' (fun b => b = vTcbA v ∨ b = tVcpuA t))
    (h1 : L.mem s' (tVcpuA t) = 0#u64) (h2 : L.mem s' (vTcbA v) = 0#u64) : JExtV2 (L := L) V X th s' := by
  refine E.unbind hv htv hvt (fun y hy => ?_) h1 h2 (fun t' ht' hne => ?_) (fun w hw hne => ?_)
  · unfold capV
    rw [hW.mem_eq (P.jw _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (by
          rintro (e | e)
          · exact (P.slb y hy v hv).1 e
          · exact (P.slv y hy t ht).1 e),
        hW.mem_eq (P.jw _ (Or.inl ⟨y, hy, Or.inr rfl⟩)) (by
          rintro (e | e)
          · exact (P.slb y hy v hv).2 e
          · exact (P.slv y hy t ht).2 e)]
  · exact hW.mem_eq (P.jw _ (Or.inr (Or.inl ⟨t', ht', rfl⟩))) (by
      rintro (e | e)
      · exact P.vb t' ht' v hv e
      · exact hne (tVcpuA_inj e))
  · exact hW.mem_eq (P.jw _ (Or.inr (Or.inr ⟨w, hw, rfl⟩))) (by
      rintro (e | e)
      · exact hne (vTcbA_inj e)
      · exact P.vb t ht w hw e.symm)

/-- **Binding from a two-word footprint** (`JExtV.bind_w` at `JExtV2`, same proof). -/
theorem JExtV2.bind_w (E : JExtV2 (L := L) V X th s) (P : JWPl V th) {t v : U64} (ht : th t = some .tcb)
    (hv : v ∈ V) (hw0 : L.mem s (tVcpuA t) = 0#u64) (hb0 : L.mem s (vTcbA v) = 0#u64) (h0 : th 0#u64 ≠ some .tcb)
    (hW : P1.WritesIn st s s' (fun b => b = vTcbA v ∨ b = tVcpuA t))
    (h1 : L.mem s' (tVcpuA t) = v) (h2 : L.mem s' (vTcbA v) = t) : JExtV2 (L := L) V X th s' := by
  refine E.bind ht hv hw0 hb0 h0 (fun y hy => ?_) h1 h2 (fun t' ht' hne => ?_) (fun w hw hne => ?_)
  · unfold capV
    rw [hW.mem_eq (P.jw _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (by
          rintro (e | e)
          · exact (P.slb y hy v hv).1 e
          · exact (P.slv y hy t ht).1 e),
        hW.mem_eq (P.jw _ (Or.inl ⟨y, hy, Or.inr rfl⟩)) (by
          rintro (e | e)
          · exact (P.slb y hy v hv).2 e
          · exact (P.slv y hy t ht).2 e)]
  · exact hW.mem_eq (P.jw _ (Or.inr (Or.inl ⟨t', ht', rfl⟩))) (by
      rintro (e | e)
      · exact P.vb t' ht' v hv e
      · exact hne (tVcpuA_inj e))
  · exact hW.mem_eq (P.jw _ (Or.inr (Or.inr ⟨w, hw, rfl⟩))) (by
      rintro (e | e)
      · exact hne (vTcbA_inj e)
      · exact P.vb t ht w hw e.symm)

/-- **`NoIoTcb` with the TCB slots' caps kept.** -/
theorem NoIoTcb.of_capEq {m m' : U64 → U64} (hT : NoIoTcb th m)
    (hc : ∀ y, IsSlot (thTcb th) y → capV m' y = capV m y) : NoIoTcb th m' := by
  intro y hy f l o h
  rw [hc y hy] at h
  exact hT y hy f l o h

/-- **`NoIoTcb` across a footprint missing `JW`** (every slot word is a `JW` word). -/
theorem NoIoTcb.of_writes (P : JWPl V th) {W : U64 → Prop} (hW : P1.WritesIn st s s' W)
    (hd : ∀ b, W b → ¬ JW V th b) (hT : NoIoTcb th (L.mem s)) : NoIoTcb th (L.mem s') := by
  have k : ∀ b, JW V th b → L.mem s' b = L.mem s b := fun b hb =>
    hW.mem_eq (P.jw b hb) fun hw => hd b hw hb
  refine hT.of_capEq fun y hy => ?_
  have hy' := isSlot_thTcb hy
  unfold capV
  rw [k y (Or.inl ⟨y, hy', Or.inl rfl⟩), k _ (Or.inl ⟨y, hy', Or.inr rfl⟩)]

/-- **`NoIoTcb` across the bind / unbind footprint** `{vTcbA v, tVcpuA t}`. -/
theorem NoIoTcb.two_w (P : JWPl V th) {t v : U64} (ht : th t = some .tcb) (hv : v ∈ V)
    (hW : P1.WritesIn st s s' (fun b => b = vTcbA v ∨ b = tVcpuA t)) (hT : NoIoTcb th (L.mem s)) :
    NoIoTcb th (L.mem s') := by
  refine hT.of_capEq fun y hy => ?_
  have hy' := isSlot_thTcb hy
  unfold capV
  rw [hW.mem_eq (P.jw _ (Or.inl ⟨y, hy', Or.inl rfl⟩)) (by
        rintro (e | e)
        · exact (P.slb y hy' v hv).1 e
        · exact (P.slv y hy' t ht).1 e),
      hW.mem_eq (P.jw _ (Or.inl ⟨y, hy', Or.inr rfl⟩)) (by
        rintro (e | e)
        · exact (P.slb y hy' v hv).2 e
        · exact (P.slv y hy' t ht).2 e)]

end

/-- **`NoIoTcb` across the installs into TCB `t`** (module docstring). -/
theorem NoIoTcb.of_instFr {th : TypedHeap} {t : U64} {m0 m : U64 → U64} (hT : NoIoTcb th m0)
    (hF : InstFr th t m0 m)
    (ht : ∀ i, i < tcbSlots → TcbDer th t m0 m i → ∀ f l o,
      capV m (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) = .IoPort f l o → o = 0#u64) : NoIoTcb th m := by
  have chg : ∀ y, IsSlot (thTcb th) y → ChgZ m0 m y → ∀ f l o, capV m y = .IoPort f l o → o = 0#u64 := by
    intro y hy hc f l o h
    rcases hc with e | e | ⟨zt, n, e⟩
    · rw [e] at h; exact hT y hy f l o h
    · rw [e] at h; cases h
    · rw [e] at h; cases h
  intro y hy f l o h
  by_cases hyt : ∃ i, i < tcbSlots ∧ y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)
  · obtain ⟨i, hi, e⟩ := hyt
    rw [e] at hy h
    rcases hF.2 i hi with hc | hd
    · exact chg _ hy hc f l o h
    · exact ht i hi hd f l o h
  · exact chg y hy (hF.1 y (isSlot_thTcb hy) (fun i hi e => hyt ⟨i, hi, e⟩)) f l o h

/-- `NoIoTcb.of_instFr` with slot 3 discharged (`TcbDer` makes it an endpoint). -/
theorem NoIoTcb.of_instFr3 {th : TypedHeap} {t : U64} {m0 m : U64 → U64} (hT : NoIoTcb th m0)
    (hF : InstFr th t m0 m)
    (ht : ∀ i, i < tcbSlots → i ≠ 3 → TcbDer th t m0 m i → ∀ f l o,
      capV m (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) = .IoPort f l o → o = 0#u64) : NoIoTcb th m := by
  refine hT.of_instFr hF fun i hi hd f l o h => ?_
  by_cases h3 : i = 3
  · obtain ⟨e, b, x1, x2, x3, x4, he⟩ := hd.2 h3
    rw [he] at h; cases h
  · exact ht i hi h3 hd f l o h

end
end Fl4Proofs.P3

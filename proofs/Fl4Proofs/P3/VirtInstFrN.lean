/-
P3x for virtualization (line virt, gen 28, item 2): **the TCB-slot install's frame naming the installed cap**, so
that `NoIoTcb` is kept by `tcb::install_tcb_cap` with no hypothesis on the slot after.

TcbCaps' `InstFr th t m0 m` records, for each of TCB `t`'s slots, "`ChgZ` from `m0`, or derived" (`TcbDer`: the shape
of *some* slot's cap at `m0`), which does not exclude an owned IO-port cap (gen 27, P3/JExtV2Bind
`NoIoTcb.of_instFr`'s `ht`). Here:

* `InstFrN th t m0 m P` = `InstFr th t m0 m` ∧ each of `t`'s slots is `ChgZ` from `m0` or holds a cap with property
  `P` (the caller's property of the caps it installs); `InstFrN.refl`, **`InstFrN.install`** (`InstFr.install` plus
  `P nc` for the installed cap `nc`), `InstFrN.delete`.
* `InstPostWN` = TcbCaps' `InstPostW` with `InstFrN` for `InstFr`; `InstPostWN.toW` forgets the addition.
* **`install_tcb_cap_refinesWN`**: `install_tcb_cap_refinesW`'s statement (same hypotheses) with `InstFrN … P` at
  the entry, `P nc`, and `InstPostWN` after. Proof: `install_tcb_cap_refinesW`'s two branches (empty slot / delete
  first) re-done with `InstFrN.install` in place of `InstFr.install`; the old statement is unchanged.
* `NoOwnIo c` (`c` is no IO-port cap with a nonzero owner); **`NoIoTcb.of_instFrN`**: `NoIoTcb th m0` and
  `InstFrN th t m0 m NoOwnIo` give `NoIoTcb th m` — `of_instFr`'s `ht` discharged. `noOwnIo_of_ne` gives `P nc` for
  every cap FL4 installs into a TCB slot (a CNode root, tcb.rs l. 189-192; a PML4, l. 193-196; an endpoint or null
  fault / timeout handler, faults.rs l. 57-63; a frame buffer, vspace.rs l. 179; an `Ept` cap, tcb.rs l. 410-417):
  none is an `IoPort`.

No named premise (`P nc` is a fact of the call's argument, discharged by the decoder that produced `nc`). New file
only; no existing statement changed.
-/
import Fl4Proofs.P3.JExtV2Bind
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **The install frame naming the installed caps** (module docstring). -/
def InstFrN (th : TypedHeap) (t : U64) (m0 m : U64 → U64) (P : capability.Cap → Prop) : Prop :=
  InstFr th t m0 m ∧ ∀ i, i < tcbSlots →
    ChgZ m0 m (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) ∨ P (capV m (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)))

theorem InstFrN.refl (th : TypedHeap) (t : U64) (m : U64 → U64) (P : capability.Cap → Prop) :
    InstFrN th t m m P :=
  ⟨InstFr.refl th t m, fun _ _ => Or.inl (ChgZ.refl _ _)⟩

/-- The second half of `InstFrN` across a step: `t`'s slots `ChgZ` from `m1`, or (slot `n`) holding a `P` cap. -/
theorem instFrN_step2 {t : U64} {m0 m1 m2 : U64 → U64} {P : capability.Cap → Prop}
    (h : ∀ i, i < tcbSlots →
      ChgZ m0 m1 (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) ∨ P (capV m1 (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i))))
    (hT : ∀ i, i < tcbSlots → ChgZ m1 m2 (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) ∨
      P (capV m2 (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)))) :
    ∀ i, i < tcbSlots →
      ChgZ m0 m2 (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) ∨ P (capV m2 (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i))) := by
  intro i hi
  rcases hT i hi with hc | hp
  · rcases h i hi with h0 | hp0
    · exact Or.inl (h0.trans hc)
    · rcases hc with e | e | e
      · exact Or.inr (by rw [e]; exact hp0)
      · exact Or.inl (Or.inr (Or.inl e))
      · exact Or.inl (Or.inr (Or.inr e))
  · exact Or.inr hp

/-- **An install's frame, naming the installed cap** (`InstFr.install` + `P nc`). -/
theorem InstFrN.install {th : TypedHeap} (hP : Placed th) {t : U64} (ht : th t = some .tcb) {m0 m1 m2 : U64 → U64}
    {P : capability.Cap → Prop} (h : InstFrN th t m0 m1 P) {n : Nat} (hn : n < tcbSlots)
    (hzz : ∀ y, IsSlot th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) → ChgZ m1 m2 y)
    {nc : capability.Cap}
    (htg : capV m2 (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null ∨
      capV m2 (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = nc)
    {y0 : U64} (hy0 : IsSlot th y0) (hsh : shape nc = shape (capV m0 y0))
    (hep : n = 3 → nc ≠ .Null → ∃ e b x1 x2 x3 x4, nc = .Endpoint e b x1 x2 x3 x4) (hPn : P nc) :
    InstFrN th t m0 m2 P := by
  refine ⟨h.1.install hP ht hn hzz htg hy0 hsh hep, instFrN_step2 h.2 fun i hi => ?_⟩
  by_cases e : i = n
  · subst e
    rcases htg with h0 | h1
    · exact Or.inl (Or.inr (Or.inl h0))
    · exact Or.inr (by rw [h1]; exact hPn)
  · refine Or.inl (hzz _ (AbsSlot.isSlot ⟨t, rfl, Or.inr ⟨ht, i, hi, rfl⟩⟩) fun e' => e ?_)
    have hAi : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex i) := ⟨t, rfl, Or.inr ⟨ht, i, hi, rfl⟩⟩
    have hAn : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
    exact tcbCnodeIndex_inj hi hn (congrArg Prod.snd (cslotAddr_inj hP hAi hAn e'))

/-- **A delete's frame** (`InstFr.delete`; slot `n` emptied). -/
theorem InstFrN.delete {th : TypedHeap} (hP : Placed th) {t : U64} (ht : th t = some .tcb) {m0 m1 m2 : U64 → U64}
    {P : capability.Cap → Prop} (h : InstFrN th t m0 m1 P) {n : Nat} (hn : n < tcbSlots)
    (hzz : ∀ y, IsSlot th y → y ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n) → ChgZ m1 m2 y)
    (hnull : capV m2 (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex n)) = .Null) : InstFrN th t m0 m2 P := by
  refine ⟨h.1.delete hP ht hn hzz hnull, instFrN_step2 h.2 fun i hi => ?_⟩
  by_cases e : i = n
  · subst e; exact Or.inl (Or.inr (Or.inl hnull))
  · refine Or.inl (hzz _ (AbsSlot.isSlot ⟨t, rfl, Or.inr ⟨ht, i, hi, rfl⟩⟩) fun e' => e ?_)
    have hAi : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex i) := ⟨t, rfl, Or.inr ⟨ht, i, hi, rfl⟩⟩
    have hAn : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
    exact tcbCnodeIndex_inj hi hn (congrArg Prod.snd (cslotAddr_inj hP hAi hAn e'))

/-- **No IO-port cap with a nonzero owner.** -/
def NoOwnIo (c : capability.Cap) : Prop := ∀ f l o, c = .IoPort f l o → o = 0#u64

theorem noOwnIo_of_ne {c : capability.Cap} (h : ∀ f l o, c ≠ .IoPort f l o) : NoOwnIo c :=
  fun f l o e => absurd e (h f l o)

/-- **`NoIoTcb` across the installs into TCB `t`, with no hypothesis on the slots after** (module docstring). -/
theorem NoIoTcb.of_instFrN {th : TypedHeap} {t : U64} {m0 m : U64 → U64} (hT : NoIoTcb th m0)
    (hF : InstFrN th t m0 m NoOwnIo) : NoIoTcb th m := by
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
    rcases hF.2 i hi with hc | hp
    · exact chg _ hy hc f l o h
    · exact hp f l o h
  · exact chg y hy (hF.1.1 y (isSlot_thTcb hy) (fun i hi e => hyt ⟨i, hi, e⟩)) f l o h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `InstPostW` with `InstFrN` (module docstring). -/
def InstPostWN (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (t : U64)
    (P : capability.Cap → Prop) (m : Fl4Spec.PMonad Unit Unit) (s : S) (σ : Fl4Spec.State Unit)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ' G', ((res.1 = .Ok () ∧ (.ok (), σ') ∈ (m.run σ).1 ∧ InstFrN th t (L.mem s) (L.mem res.2.1) P) ∨
      (res.1 = .Err .Preempted ∧ (.error (), σ') ∈ (m.run σ).1)) ∧
    DState (L := L) th res.2.1 σ' G' ∧ W res.2.1 res.2.2 σ' G'

theorem InstPostWN.toW {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap} {t : U64}
    {P : capability.Cap → Prop} {m : Fl4Spec.PMonad Unit Unit} {s : S} {σ : Fl4Spec.State Unit}
    {res : core.result.Result Unit error.Exc × S × A} (h : InstPostWN (L := L) W th t P m s σ res) :
    InstPostW (L := L) W th t m s σ res := by
  obtain ⟨σ', G', hc, hD, hW⟩ := h
  exact ⟨σ', G', hc.imp (fun ⟨a, b, c⟩ => ⟨a, b, c.1⟩) id, hD, hW⟩

set_option maxHeartbeats 4000000 in
/-- **`tcb::install_tcb_cap` with the frame naming the installed cap** (module docstring). -/
theorem install_tcb_cap_refinesWN [Fl4Proofs.P1.PlainStore st] (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (hP : Placed th)
    (hH : DelHypsW (L := L) arI W th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (hB : ∀ m G, MdbLinks th m G → psiD m G + 2 * K + 2 < 2 ^ 64 - 1)
    (s0 s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hW : W s a σ G)
    (t : U64) (ht : th t = some .tcb) (n : Nat) (hn : n < tcbSlots) (idx : U64) (hidx : idx.val = n)
    {P : capability.Cap → Prop} (hcz0 : InstFrN th t (L.mem s0) (L.mem s) P)
    (ssl : Fl4Spec.CslotPtr) (hAs : AbsSlot th ssl)
    (nc : capability.Cap) (hwf : CapWf nc) (hcv : CapValid th nc) (he : EncWf nc)
    (hfw : isFrame nc = true → Fl4Spec.sameObjectAs (absCap nc) (absCap nc))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    {srcC0 : capability.Cap} (hsrc0 : capV (L.mem s0) (cslotAddr (ps.bv, idxs)) = srcC0)
    (hsh : shape nc = shape srcC0) (hbd : badgeF nc = badgeF srcC0 ∨ badgeF srcC0 = 0#u64)
    (hkey : okey nc = okey srcC0)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC0 → Vs.VCapOK P L4 L3 L2 L1 nc)
    (hep : n = 3 → nc ≠ .Null → ∃ e b x1 x2 x3 x4, nc = .Endpoint e b x1 x2 x3 x4) (hPn : P nc) :
    tcb.install_tcb_cap st arI s a t (cslotAddr ssl) idx nc (cslotAddr (ps.bv, idxs)) ⦃ res =>
      InstPostWN (L := L) W th t P (Fl4Spec.installTcbCap t.bv ssl n (some (absCap nc, (ps.bv, idxs)))) s0 σ res ⦄ := by
  have hAt : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex n) := ⟨t, rfl, Or.inr ⟨ht, n, hn, rfl⟩⟩
  have hAsrc : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hsrcT := cnode_slot_ne_tcb hP hps hls ht
  have hczs0 := hcz0.1.1 _ hAsrc.isSlot hsrcT
  have hsh0 : shape nc = shape (capV (L.mem s0) (cslotAddr (ps.bv, idxs))) := by rw [hsrc0]; exact hsh
  unfold tcb.install_tcb_cap
  rw [spec_eq_ok (tcb_slot_spec t idx), tcb_root_eq t idx hn hidx]
  simp only [bind_ok]
  obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hAt
  by_cases hc0n : c0 = .Null
  · subst hc0n
    rw [delete_null_eq arI s a _ hc0 σ]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
    refine WP.spec_mono (WP.spec_and (install_after th hP s0 s a σ G hDS t ht n hn (by rw [capV_of_capAt hc0])
      ssl hAs nc hwf hcv he hfw hps hls hczs0 hsrc0 hsh hbd hkey hv)
      (install_after_frame hP s a hDS.1.2.2.1 hDS.2.1 t (cslotAddr ssl) nc hAsrc.isSlot hAt.isSlot)) ?_
    rintro res ⟨⟨σ', G', hrun, hr1, ha1, hDS', hcap, hst, htg, -⟩, hF⟩
    have hg0' : Fl4Spec.getCap (Z := Unit) (t.bv, Fl4Spec.tcbCnodeIndex n) σ = ({(.nullCap, σ)}, False) := by
      rw [hg0, hca0.abs]; rfl
    refine ⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok (by rw [capDelete_null hg0']; rfl) (mem_of_run hrun),
      hcz0.install hP ht hn (fun y hy hne => ChgZ.of_eq (hcap y hy hne)) htg hAsrc.isSlot hsh0 hep hPn⟩,
      hDS', by rw [ha1]; exact hH.slot s res.2.1 a σ σ' G G' hW hDS hDS' hF (cnk_of_inst hrun) hst⟩
  · apply WP.spec_bind (delete_fullW arI W th hP (finalHyp_full th hP) hH K hK hK6 _ hAt s a σ G hDS hW
      (by rw [capV_of_capAt hc0]; exact hc0n) (hB _ G hDS.1.2.2.1))
    rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hDS1, -, -, hmD, hcase, hW1⟩
    simp only [uncurry_apply_pair] at hcase hDS1 hmD hW1 ⊢
    rcases hcase with ⟨rfl, hmem, -, hnull, hcz⟩ | ⟨rfl, hmem⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_mono (WP.spec_and (install_after th hP s0 s1 a1 σ1 G1 hDS1 t ht n hn hnull ssl hAs nc hwf hcv he
        hfw hps hls (hczs0.trans (hcz _ hAsrc.isSlot (hsrcT n hn))) hsrc0 hsh hbd hkey hv)
        (install_after_frame hP s1 a1 hDS1.1.2.2.1 hDS1.2.1 t (cslotAddr ssl) nc hAsrc.isSlot hAt.isSlot)) ?_
      rintro res ⟨⟨σ', G', hrun, hr1, ha1, hDS', hcap, hst, htg, -⟩, hF⟩
      exact ⟨σ', G', Or.inl ⟨hr1, mem_bindE_ok hmem (mem_of_run hrun),
        hcz0.install hP ht hn (fun y hy hne => (hcz y hy hne).trans (ChgZ.of_eq (hcap y hy hne))) htg
          hAsrc.isSlot hsh0 hep hPn⟩,
        hDS', by rw [ha1]; exact hH.slot s1 res.2.1 a1 σ1 σ' G1 G' hW1 hDS1 hDS' hF (cnk_of_inst hrun) hst⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨σ1, G1, Or.inr ⟨rfl, mem_bindE_err hmem⟩, hDS1, hW1⟩

end

end
end Fl4Proofs.P3

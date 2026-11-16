/-
P3 (DESIGN.md §9), TCB invocations: **the replies of the TCB labels whose
spec result is data** (ReadRegisters, SetFlags, GetBreakpoint,
ConfigureSingleStepping), for `TopPostRMX` with `X` true: FL4 writes the
reply registers (and, past `MR3`, the caller's IPC buffer) and sets the
caller `Running`; the spec runs `reply_from_kernel (0, rr)` and
`set_thread_state Running` (`specTail`).

* `RL`: the parts of `RelTopM` at one typed heap and ghost (`RL.relTop`).
* `WFr`: an FL4 step keeping the slot words, the kernel-global base, the
  core and the domain-schedule words (`RL.wfr`); `wfr_wr` for a write
  outside the slots and the domain schedule, `KsbPlaced` (the domain
  schedule apart from the typed heap's objects) for the TCB words.
* `RL.spec`: a spec step changing only a TCB, keeping its caps, and the
  domain schedule.
* `BufOutsideHyp`: the caller's IPC-buffer words outside the slots and the
  domain schedule (`bufOutside_of_placed`: from VSpace's `BufPlaced`).
-/
import Fl4Proofs.P3.VsReplyTop
import Fl4Proofs.P3.BufPlaced
import Fl4Proofs.P3.TcbExt
import Fl4Proofs.P3.TcbNil
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The parts of `RelTopM` at the typed heap `th` and ghost `G`. -/
def RL (th : TypedHeap) (G : MdbGhost) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  CRel th (L.mem s) σ G ∧ FinInv th (L.mem s) σ G ∧ MdbOKV (L.ksb s) (L.mem s) G ∧
    DomRel (L.mem s) (L.ksb s) σ

theorem RL.relTop {th : TypedHeap} {G : MdbGhost} {s : S} {σ : Fl4Spec.State Unit} (hP : Placed th)
    (h : RL (L := L) th G s σ) : RelTopM (L := L) s σ :=
  ⟨th, G, hP, h.1, h.2.1, h.2.2.2, h.2.2.1⟩

/-- An FL4 step keeping the slot words, the kernel-global base, the core
and the domain-schedule words. -/
def WFr (th : TypedHeap) (s s' : S) : Prop :=
  SlotsSame th (L.mem s) (L.mem s') ∧ L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧
    DomSame (L.mem s) (L.mem s') (L.ksb s)

theorem WFr.refl (th : TypedHeap) (s : S) : WFr (L := L) th s s :=
  ⟨SlotsSame.refl _ _, rfl, rfl, DomSame.refl _ _⟩

theorem WFr.trans {th : TypedHeap} {s1 s2 s3 : S} (h1 : WFr (L := L) th s1 s2) (h2 : WFr (L := L) th s2 s3) :
    WFr (L := L) th s1 s3 :=
  ⟨h1.1.trans h2.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h1.2.2.2.trans (by rw [← h1.2.1]; exact h2.2.2.2)⟩

theorem RL.wfr {th : TypedHeap} {G : MdbGhost} {s s' : S} {σ : Fl4Spec.State Unit}
    (h : RL (L := L) th G s σ) (hw : WFr (L := L) th s s') : RL (L := L) th G s' σ := by
  obtain ⟨hCR, hFI, hMO, hD⟩ := h
  obtain ⟨hSS, hk, -, hds⟩ := hw
  obtain ⟨h1, h2, h3⟩ := Vs.cspace_step hCR hFI hMO hSS ⟨rfl, rfl, fun o h => absurd rfl h, rfl⟩
    (hCR.1.of_caps fun x hx => hSS.capAt hx)
  exact ⟨h1, h2, by rw [hk]; exact h3, by rw [hk]; exact hD.of_same hds rfl rfl⟩

/-- **A spec step changing only a TCB** (keeping its caps), the CDT, the
current thread and the domain schedule. -/
theorem RL.spec {th : TypedHeap} {G : MdbGhost} {s : S} {σ σ' : Fl4Spec.State Unit}
    (h : RL (L := L) th G s σ) {t : Fl4Spec.ObjRef} {x y : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb x))
    (h1 : σ'.kheap = Function.update σ.kheap t (some (.tcb y)))
    (hy : ∀ i, Fl4Spec.tcbCnodeMap y i = Fl4Spec.tcbCnodeMap x i)
    (hc : σ'.cdt = σ.cdt) (hio : σ'.isOriginalCap = σ.isOriginalCap) (hcur : σ'.curThread = σ.curThread)
    (hdl : σ'.domainList = σ.domainList) (hds : σ'.domainStartIndex = σ.domainStartIndex) :
    RL (L := L) th G s σ' := by
  obtain ⟨hCR, hFI, hMO, hD⟩ := h
  have hK : Vs.KFoot σ σ' := by
    refine ⟨hc, hio, fun o hne => ?_, hcur⟩
    by_cases e : o = t
    · subst e
      exact Or.inr (Or.inr ⟨x, y, hk, by rw [h1, Function.update_self]⟩)
    · rw [h1, Function.update_of_ne e] at hne; exact absurd rfl hne
  obtain ⟨c1, c2, c3⟩ := Vs.cspace_step hCR hFI hMO (SlotsSame.refl _ _) hK (Vs.StateRel.tcb_upd hCR.1 hk h1 hy)
  exact ⟨c1, c2, c3, hD.of_same (DomSame.refl _ _) hdl hds⟩

/-- A spec step changing only the machine state. -/
theorem RL.ms {th : TypedHeap} {G : MdbGhost} {s : S} {σ σ' : Fl4Spec.State Unit}
    (h : RL (L := L) th G s σ) (hk : σ'.kheap = σ.kheap) (hc : σ'.cdt = σ.cdt)
    (hio : σ'.isOriginalCap = σ.isOriginalCap) (hcur : σ'.curThread = σ.curThread)
    (hdl : σ'.domainList = σ.domainList) (hds : σ'.domainStartIndex = σ.domainStartIndex) :
    RL (L := L) th G s σ' := by
  obtain ⟨hCR, hFI, hMO, hD⟩ := h
  have hR : StateRel th (L.mem s) σ' := by
    refine ⟨fun p r hp => ?_, fun t ht => ?_⟩
    · obtain ⟨cs, h1, h2, h3⟩ := hCR.1.cnode p r hp; exact ⟨cs, by rw [hk]; exact h1, h2, h3⟩
    · obtain ⟨x, h1, h2⟩ := hCR.1.tcb t ht; exact ⟨x, by rw [hk]; exact h1, h2⟩
  obtain ⟨c1, c2, c3⟩ := Vs.cspace_step hCR hFI hMO (SlotsSame.refl _ _)
    ⟨hc, hio, fun o h => absurd (by rw [hk]) h, hcur⟩ hR
  exact ⟨c1, c2, c3, hD.of_same (DomSame.refl _ _) hdl hds⟩

/-- **The domain schedule apart from the typed heap's objects** (a
placement fact of the joint invariant): the kernel-global block's first
256 bytes. -/
structure KsbPlaced (th : TypedHeap) (kb : U64) : Prop where
  fits : kb.val + 13568 ≤ 2 ^ 64
  align : kb.val % 8 = 0
  apart : ∀ p k, th p = some k → p.val + objSize k ≤ kb.val ∨ kb.val + 256 ≤ p.val

/-- **A write outside the slots and the domain schedule.** -/
theorem wfr_wr {th : TypedHeap} (hP : Placed th) {s : S} (hK : KsbPlaced th (L.ksb s)) {w : U64}
    (ha : P1.Aligned w) (hslot : ∀ x, IsSlot th x → ¬ (x.val ≤ w.val ∧ w.val < x.val + 32))
    (hdom : w.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ w.val) (v : U64) :
    WFr (L := L) th s (L.wr s w v) := by
  refine ⟨slotsSame_wr hP s v ha hslot, L.ksb_wr _ _ _, L.cpu_wr _ _ _,
    Vs.domSame_low hK.fits hK.align fun b hb h1 h2 => ?_⟩
  refine L.mem_wr_ne ha hb ?_
  intro e
  unfold P1.Aligned at ha hb
  omega

/-- **A write to a word of a TCB past its slots.** -/
theorem wfr_tcbw {th : TypedHeap} (hP : Placed th) {s : S} (hK : KsbPlaced th (L.ksb s)) {t w : U64}
    (ht : th t = some .tcb) (hw1 : t.val + 192 ≤ w.val) (hw2 : w.val < t.val + 4096) (ha : P1.Aligned w)
    (v : U64) : WFr (L := L) th s (L.wr s w v) := by
  refine wfr_wr hP hK ha (fun a ha' ⟨h1, h2⟩ => ?_) ?_ v
  · obtain ⟨p, k, hk, g1, g2, g3⟩ := slot_in_object hP ha'
    by_cases hpt : p = t
    · subst hpt; rw [ht] at hk; cases hk
      have := g3 rfl; simp [tcbSlots] at this; omega
    · have e4 : objSize ObjKind.tcb = 4096 := rfl
      rcases hP.disj p t k .tcb hk ht hpt with h | h <;> omega
  · have := hK.apart t .tcb ht
    have := hP.align t _ ht
    have e4 : objSize ObjKind.tcb = 4096 := rfl
    unfold P1.Aligned at ha
    omega

/-- **The caller's IPC-buffer words outside the slots and the domain
schedule** (FL4's buffer `rw` of the caller: zero, or every word of it). -/
def BufOutsideHyp (th : TypedHeap) (s : S) (rw : U64) : Prop :=
  rw ≠ 0#u64 → ∀ i : U64, i.val < 128 → P1.Aligned (Endp.fl4BufA rw i) ∧
    (∀ x, IsSlot th x → ¬ (x.val ≤ (Endp.fl4BufA rw i).val ∧ (Endp.fl4BufA rw i).val < x.val + 32)) ∧
    ((Endp.fl4BufA rw i).val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ (Endp.fl4BufA rw i).val)

/-- **`BufOutsideHyp` from VSpace's `BufPlaced`**, for a buffer mapped by `B`
(`BufMap`) with aligned words (EpRel's `EPlaced.balign`). -/
theorem bufOutside_of_placed {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64}
    {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hT : Vs.TopPlaced st th P L4 L3 L2 L1 N T C E R B c s σ) (hB : Vs.BufPlaced (L := L) N C B c s σ)
    (hal : ∀ wp ∈ B, wp.1.val % 8 = 0) {rw : U64} {p : Fl4Spec.Word} (hm : rw ≠ 0#u64 → Endp.BufMap B rw p) :
    BufOutsideHyp (L := L) th s rw := by
  intro h0 i hi
  have hw := hm h0 i hi
  exact ⟨hal _ hw, fun x hx => Vs.BufPlaced.slot hT hw hx, Vs.BufPlaced.dom hB hw⟩


/-! ### FL4's reply writes -/

theorem regA_val' {t i : U64} (hf : t.val + 4096 ≤ 2 ^ 64) (hi : i.val < 24) :
    (Endp.regA t i).val = t.val + 256 + 8 * i.val := by
  unfold Endp.regA layout.tcb.REGS
  have hs : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
  have h1 : (256#u64 : U64).val = 256 := rfl
  have h2 : (8#u64 : U64).val = 8 := rfl
  rw [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq,
    hs, h1, h2]
  have : (i.val * 8) % 2 ^ 64 = i.val * 8 := Nat.mod_eq_of_lt (by omega)
  rw [this]
  have : (t.val + 256) % 2 ^ 64 = t.val + 256 := Nat.mod_eq_of_lt (by omega)
  rw [this, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A write to a register word of a TCB. -/
theorem wfr_reg {th : TypedHeap} (hP : Placed th) {s : S} (hK : KsbPlaced th (L.ksb s)) {t : U64}
    (ht : th t = some .tcb) {i : U64} (hi : i.val < 24) (v : U64) :
    WFr (L := L) th s (L.wr s (Endp.regA t i) v) := by
  have hf := hP.fits t _ ht
  have ha := hP.align t _ ht
  have e4 : objSize ObjKind.tcb = 4096 := rfl
  rw [e4] at hf
  have hv := regA_val' hf hi
  exact wfr_tcbw hP hK ht (by rw [hv]; omega) (by rw [hv]; omega) (by unfold P1.Aligned; rw [hv]; omega) v

/-- **A register write of a TCB.** -/
theorem set_reg_wfr {th : TypedHeap} (hP : Placed th) {s : S} (hK : KsbPlaced th (L.ksb s)) {t : U64}
    (ht : th t = some .tcb) {i : U64} (hi : i.val < 24) (v : U64) :
    obj.Tcb.set_reg st t s i v ⦃ s' => WFr (L := L) th s s' ⦄ := by
  refine WP.spec_mono (Endp.obj.Tcb.set_reg.spec s t i v) ?_
  rintro s' rfl
  exact wfr_reg hP hK ht hi v

/-- **`set_mr`** of the caller (a register, or a buffer word). -/
theorem set_mr_wfr {th : TypedHeap} (hP : Placed th) {s : S} (hK : KsbPlaced th (L.ksb s)) {t : U64}
    (ht : th t = some .tcb) {buf : U64} {i : U64} (hB : 4 ≤ i.val → BufOutsideHyp (L := L) th s buf)
    (hi : i.val < 127) (v : U64) : msg.set_mr st s t buf i v ⦃ r => WFr (L := L) th s r.2 ⦄ := by
  unfold msg.set_mr
  by_cases h4 : i < msg.N_MSG_REGISTERS
  · have hi4 : i.val < 4 := by
      have := (P1.gt_iff_val).1 h4
      have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
      omega
    simp only [h4, ↓reduceIte]
    refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
    rintro r rfl
    refine WP.spec_bind (set_reg_wfr hP hK ht (Endp.regIdx_lt _) v) ?_
    intro s1 hw
    unfold lift
    simp only [bind_ok, WP.spec_ok]
    exact hw
  · rw [if_neg h4]
    by_cases hb : buf = 0#u64
    · subst hb
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact WFr.refl _ _
    · have hb' : (buf != 0#u64) = true := by simp [hb]
      simp only [hb', ↓reduceIte]
      unfold lift
      simp only [bind_ok]
      have hiv : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have hi4 : 4 ≤ i.val := by
        have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
        by_contra hc; exact h4 ((P1.gt_iff_val).2 (by rw [hN]; omega))
      obtain ⟨ha, hsl, hd⟩ := hB hi4 hb _ (by rw [hiv]; omega)
      refine WP.spec_bind (Endp.msg.buf_set.spec s buf _ v) ?_
      rintro s1 rfl
      simp only [WP.spec_ok]
      exact wfr_wr hP hK ha hsl hd v

/-- **`set_msg_info`** of the caller. -/
theorem set_msg_info_wfr {th : TypedHeap} (hP : Placed th) {s : S} (hK : KsbPlaced th (L.ksb s)) {t : U64}
    (ht : th t = some .tcb) (lab n : U64) (hn : n.val < 128) :
    msg.set_msg_info st s t { label := lab, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := n } ⦃ s' =>
      WFr (L := L) th s s' ⦄ := by
  refine WP.spec_mono (Endp.set_msg_info_spec s t lab n hn) ?_
  rintro s' ⟨v, rfl, -⟩
  exact wfr_reg hP hK ht (i := layout.reg.MSG_INFO) (by unfold layout.reg.MSG_INFO layout.reg.RSI; decide) v

/-- **`set_thread_state`**, the scheduler-action word outside the objects and
the domain schedule. -/
theorem sts_wfr {th : TypedHeap} (hP : Placed th) {s : S} (hK : KsbPlaced th (L.ksb s)) {t : U64}
    (ht : th t = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hna : (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val + 8 ≤ (L.ksb s).val ∨
      (L.ksb s).val + 256 ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val) (v : U64) :
    sched.set_thread_state st s t v ⦃ s' => WFr (L := L) th s s' ⦄ := by
  refine WP.spec_mono (set_thread_state_cases s t v) ?_
  have hf := hP.fits t _ ht
  have ha := hP.align t _ ht
  have e4 : objSize ObjKind.tcb = 4096 := rfl
  rw [e4] at hf
  have hv := stA_val hP ht
  have h1 : WFr (L := L) th s (L.wr s (stA t) v) :=
    wfr_tcbw hP hK ht (by rw [hv]; omega) (by rw [hv]; omega) (by unfold P1.Aligned; rw [hv]; omega) v
  have hK1 : KsbPlaced th (L.ksb (L.wr s (stA t) v)) := by rw [L.ksb_wr]; exact hK
  have hslot : ∀ x, IsSlot th x → ¬ (x.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < x.val + 32) := by
    rintro x hx ⟨g1, g2⟩
    obtain ⟨p, k, hk, k1, k2, -⟩ := slot_in_object hP hx
    exact hact.2 p k hk ⟨by omega, by omega⟩
  rintro s' (rfl | rfl)
  · exact h1
  · refine h1.trans (wfr_wr hP hK1 hact.1 hslot (by rw [L.ksb_wr]; exact hna) _)


/-- **`reply_words`** of the caller. -/
theorem reply_words_wfr {th : TypedHeap} (hP : Placed th) {s : S} (hK : KsbPlaced th (L.ksb s)) {t : U64}
    (ht : th t = some .tcb) (n : U64) (hn : n.val < 128) :
    tcb.reply_words st s t n ⦃ s' => WFr (L := L) th s s' ⦄ := by
  unfold tcb.reply_words
  refine WP.spec_bind (set_reg_wfr hP hK ht (i := layout.reg.BADGE)
    (by unfold layout.reg.BADGE layout.reg.RDI; decide) 0#u64) ?_
  intro s1 h1
  unfold msginfo.MessageInfo.new
  simp only [bind_ok]
  have hK1 : KsbPlaced th (L.ksb s1) := by rw [h1.2.1]; exact hK
  exact WP.spec_mono (set_msg_info_wfr hP hK1 ht 0#u64 n hn) fun _ h2 => h1.trans h2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The context of the reply writes** at `s` for the caller `t`: the domain
schedule apart from the objects, `t` a TCB, the scheduler-action word
outside the objects and the domain schedule. -/
structure TCtx (th : TypedHeap) (s : S) (t : U64) : Prop where
  ksb : KsbPlaced th (L.ksb s)
  tcb : th t = some .tcb
  act : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)
  actd : (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val + 8 ≤ (L.ksb s).val ∨
    (L.ksb s).val + 256 ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val

theorem TCtx.wfr {th : TypedHeap} {s s' : S} {t : U64} (h : TCtx (L := L) th s t) (hw : WFr (L := L) th s s') :
    TCtx (L := L) th s' t := by
  have hn : L.nodeAt s' (L.cpu s') layout.node.SCHED_ACTION = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION := by
    rw [hw.2.2.1]; simp [P1.LawfulStore.nodeAt, hw.2.1]
  exact ⟨by rw [hw.2.1]; exact h.ksb, h.tcb, by rw [hn]; exact h.act, by rw [hn, hw.2.1]; exact h.actd⟩

/-- **`set_mr`**, with the length returned. -/
theorem set_mr_t {th : TypedHeap} (hP : Placed th) {s : S} {t : U64} (hC : TCtx (L := L) th s t) {buf : U64}
    {i : U64} (hB : 4 ≤ i.val → BufOutsideHyp (L := L) th s buf) (hi : i.val < 127) (v : U64) :
    msg.set_mr st s t buf i v ⦃ r => r.1.val < 128 ∧ WFr (L := L) th s r.2 ⦄ := by
  refine WP.spec_mono (WP.spec_and (set_mr_wfr hP hC.ksb hC.tcb hB hi v) (?_ : msg.set_mr st s t buf i v ⦃ r =>
    r.1.val < 128 ⦄)) fun _ ⟨h1, h2⟩ => ⟨h2, h1⟩
  unfold msg.set_mr
  have hiv : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  split
  · refine WP.spec_bind (WP.spec_mono (Endp.msg_register_spec i (by
      have := (P1.gt_iff_val).1 ‹_›
      have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
      omega)) fun _ _ => trivial) ?_
    intro r _
    refine WP.spec_bind (WP.spec_mono (Endp.obj.Tcb.set_reg.spec s t r v) fun _ _ => trivial) ?_
    intro s1 _
    unfold lift; simp only [bind_ok, WP.spec_ok]; rw [hiv]; omega
  · split
    · unfold lift; simp only [bind_ok]
      refine WP.spec_bind (WP.spec_mono (Endp.msg.buf_set.spec s buf _ v) fun _ _ => trivial) ?_
      intro s1 _
      simp only [WP.spec_ok]; rw [hiv]; omega
    · simp only [WP.spec_ok]; unfold msg.N_MSG_REGISTERS; decide

/-- **`reply_words`.** -/
theorem reply_words_t {th : TypedHeap} (hP : Placed th) {s : S} {t : U64} (hC : TCtx (L := L) th s t) (n : U64)
    (hn : n.val < 128) : tcb.reply_words st s t n ⦃ s' => WFr (L := L) th s s' ⦄ :=
  reply_words_wfr hP hC.ksb hC.tcb n hn

/-- **`set_thread_state`**, the state word written. -/
theorem sts_t {th : TypedHeap} (hP : Placed th) {s : S} {t : U64} (hC : TCtx (L := L) th s t) (v : U64) :
    sched.set_thread_state st s t v ⦃ s' => WFr (L := L) th s s' ∧ L.mem s' (stA t) = v ⦄ := by
  refine WP.spec_mono (WP.spec_and (sts_wfr hP hC.ksb hC.tcb hC.act hC.actd v) (set_thread_state_cases s t v)) ?_
  rintro s' ⟨hw, hc⟩
  refine ⟨hw, ?_⟩
  have hf := hP.fits t _ hC.tcb
  have ha := hP.align t _ hC.tcb
  have e4 : objSize ObjKind.tcb = 4096 := rfl
  rw [e4] at hf
  have hv := stA_val hP hC.tcb
  have hal : P1.Aligned (stA t) := by unfold P1.Aligned; rw [hv]; omega
  rcases hc with rfl | rfl
  · exact L.mem_wr_same hal
  · rw [L.mem_wr_ne hC.act.1 hal (fun e => hC.act.2 t _ hC.tcb ⟨by rw [e, hv]; omega, by rw [e, hv, e4]; omega⟩)]
    exact L.mem_wr_same hal

theorem running_ne_restart : sched.TS_RUNNING ≠ sched.TS_RESTART := by
  unfold sched.TS_RUNNING sched.TS_RESTART; decide

end

/-! ### The spec's reply -/

section Spec
open Fl4Spec Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

/-- **`reply_from_kernel (l, ms)`**: one outcome, the thread's user context
and (past `MR3`, with a buffer) the user memory changed. -/
theorem replyFromKernel_gen {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (l : Word) (ms : List Word)
    (hbuf : ∀ q, ipcBufOf true x = some q → ∀ z ∈ mrPairs ms, (bufAddr q z.1).toNat % 8 = 0 ∧ inUserFrame (bufAddr q z.1) σ) :
    ∃ σ', replyFromKernel (Z := Unit) t (l, ms) σ = ({((), σ')}, False) ∧
      (∃ y, σ'.kheap = Function.update σ.kheap t (some (.tcb y)) ∧ y = { x with tcbArch := y.tcbArch }) ∧
      σ'.cdt = σ.cdt ∧ σ'.isOriginalCap = σ.isOriginalCap ∧ σ'.curThread = σ.curThread ∧
      σ'.domainList = σ.domainList ∧ σ'.domainStartIndex = σ.domainStartIndex := by
  unfold replyFromKernel
  rw [nd_pure_bind']
  dsimp only
  rw [nd_bind_one (lookupIpcBuffer_eq hk true), nd_bind_one (asUser_setRegister_eq _ _ hk)]
  set x1 := setReg x badge_register 0 with hx1
  have hk1 : (updK σ t (.tcb x1)).kheap t = some (.tcb x1) := by simp [updK]
  set x2 := withRegs x1 (mrRegs x1.tcbArch.tcbContext.userRegs ms) with hx2
  have fin : ∀ σ2 : State Unit, σ2.kheap = Function.update σ.kheap t (some (.tcb x2)) →
      σ2.cdt = σ.cdt → σ2.isOriginalCap = σ.isOriginalCap → σ2.curThread = σ.curThread →
      σ2.domainList = σ.domainList → σ2.domainStartIndex = σ.domainStartIndex → ∀ v,
      ∃ σ', setMessageInfo (Z := Unit) t v σ2 = ({((), σ')}, False) ∧
        (∃ y, σ'.kheap = Function.update σ.kheap t (some (.tcb y)) ∧ y = { x with tcbArch := y.tcbArch }) ∧
        σ'.cdt = σ.cdt ∧ σ'.isOriginalCap = σ.isOriginalCap ∧ σ'.curThread = σ.curThread ∧
        σ'.domainList = σ.domainList ∧ σ'.domainStartIndex = σ.domainStartIndex := by
    intro σ2 hk2 e1 e2 e3 e4 e5 v
    have hk2' : σ2.kheap t = some (.tcb x2) := by rw [hk2]; simp
    refine ⟨_, asUser_setRegister_eq _ _ hk2', ⟨setReg x2 msg_info_register (messageInfoToData v), ?_, rfl⟩,
      e1, e2, e3, e4, e5⟩
    simp only [updK, hk2, Function.update_idem]
  cases hb : ipcBufOf true x with
  | none =>
    rw [nd_bind_one (setMrs_eqN hk1 _)]
    refine fin _ ?_ ?_ ?_ ?_ ?_ ?_ _
    all_goals first | rfl | exact Function.update_idem _ _ _
  | some q =>
    rw [nd_bind_one (setMrs_eq hk1 q ms (fun z hz => by
      obtain ⟨g1, g2⟩ := hbuf q hb z hz
      exact ⟨g1, inUserFrame_updK hk (fun _ h => by cases h) _ g2⟩))]
    refine fin _ ?_ ?_ ?_ ?_ ?_ ?_ _
    all_goals first | rfl | exact Function.update_idem _ _ _

/-- **The spec's success tail** (`specTail`) of a `Restart` thread: an
outcome keeping `RL`. -/
theorem specTail_rl {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {th : TypedHeap} {G : MdbGhost}
    {s : S} {σ : State Unit} (h : RL (L := L) th G s σ) {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hrs : x.tcbState = .restart) (call : Bool) (rr : List Word)
    (hbuf : call = true → ∀ q, ipcBufOf true x = some q → ∀ z ∈ mrPairs rr,
      (bufAddr q z.1).toNat % 8 = 0 ∧ inUserFrame (bufAddr q z.1) σ) :
    ∃ z ∈ (specTail call t rr σ).1, RL (L := L) th G s z.2 := by
  unfold specTail
  rw [nd_bind_one (getThreadState_eq hk), hrs]
  dsimp only
  have tail : ∀ σ1 : State Unit, RL (L := L) th G s σ1 → ∀ x1 : Tcb, σ1.kheap t = some (.tcb x1) →
      (∀ i, tcbCnodeMap x1 i = tcbCnodeMap x i) →
      ∃ z ∈ (setThreadState (Z := Unit) t .running σ1).1, RL (L := L) th G s z.2 := by
    intro σ1 h1 x1 hk1 hc1
    refine ⟨_, by rw [Notif.setThreadState_eq .running hk1]; exact Set.mem_singleton _, ?_⟩
    have hka := Notif.stsAct_kheap (updK σ1 t (.tcb { x1 with tcbState := .running })) t
    refine h1.spec hk1 (y := { x1 with tcbState := .running }) (by rw [hka]; rfl) (fun i => rfl)
      ?_ ?_ ?_ ?_ ?_
    all_goals (unfold stsAct; split <;> rfl)
  cases call with
  | false =>
    simp only [NonDet.when, Bool.false_eq_true, ↓reduceIte]
    rw [nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl)]
    exact tail σ h x hk fun _ => rfl
  | true =>
    simp only [NonDet.when, ↓reduceIte]
    obtain ⟨σ', he, ⟨y, hky, hy⟩, e1, e2, e3, e4, e5⟩ := replyFromKernel_gen hk 0 rr (hbuf rfl)
    rw [nd_bind_one he]
    have hcm : ∀ i, tcbCnodeMap y i = tcbCnodeMap x i := by intro i; rw [hy]; rfl
    exact tail σ' (h.spec hk hky hcm e1 e2 e3 e4 e5) y (by rw [hky]; simp) hcm

end Spec


/-- **The spec's IPC buffer of thread `t`**: aligned words in a user frame
(the spec side of `BufOutsideHyp`; the Ep side's `hu`). -/
def BufSpecHyp (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) : Prop :=
  ∀ x q, σ.kheap t = some (.tcb x) → Endp.ipcBufOf true x = some q → ∀ k, k < 128 →
    (Endp.bufAddr q k).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q k) σ

theorem mrPairs_lt {ms : List Fl4Spec.Word} {z : Nat × Fl4Spec.Word} (h : z ∈ Endp.mrPairs ms) : z.1 < 128 := by
  unfold Endp.mrPairs at h
  have := (List.of_mem_zip h).1
  simp [List.mem_range'] at this
  omega

theorem BufSpecHyp.pairs {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} (h : BufSpecHyp σ t) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (call : Bool) (rr : List Fl4Spec.Word) :
    call = true → ∀ q, Endp.ipcBufOf true x = some q → ∀ z ∈ Endp.mrPairs rr,
      (Endp.bufAddr q z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q z.1) σ :=
  fun _ q hq z hz => h x q hk hq z.1 (mrPairs_lt hz)

/-! ### The restart and the close -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **The restart keeps `RL`**, the caller then a `Restart` TCB. -/
theorem restart_rl {th : TypedHeap} (hP : Placed th) {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hDS : DState (L := L) th s σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    {ct : U64} (hC : TCtx (L := L) th s ct) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) :
    ∃ s1 σ1, tcb.restart_caller st s = ok s1 ∧ sched.set_thread_state st s ct sched.TS_RESTART = ok s1 ∧
      Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      RL (L := L) th G s1 σ1 ∧ DState (L := L) th s1 σ1 G ∧ TCtx (L := L) th s1 ct ∧ WFr (L := L) th s s1 ∧
      σ1.curThread = σ.curThread ∧ ∃ x, σ1.kheap ct.bv = some (.tcb x) ∧ x.tcbState = .restart ∧
        (BufSpecHyp σ ct.bv → BufSpecHyp σ1 ct.bv) := by
  obtain ⟨s1, σ1, hrc, hs1, hst1, hS1, hDS1, hc1, hk1, hcp1⟩ :=
    restart_dstate th hP s σ G hDS ct hct hcur hC.tcb hC.act
  have hW : WFr (L := L) th s s1 := by
    have h := sts_t hP hC sched.TS_RESTART
    rw [hs1] at h
    exact ((WP.spec_ok _).1 h).1
  obtain ⟨x, hkt, -⟩ := hDS.1.1.tcb ct hC.tcb
  have hkt' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hkt
  have hdom := setThreadState_dom hkt' hst1
  have e1 := Notif.setThreadState_eq (Z := Unit) .restart hkt'
  rw [hst1] at e1
  have hσ1 : σ1 = Notif.stsAct (Notif.updK σ σ.curThread (.tcb { x with tcbState := .restart })) σ.curThread := by
    have := congrArg (fun y => y.1) e1; simpa using this
  have hk1' : σ1.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
    rw [hσ1, Notif.stsAct_kheap, ← hcur]; simp [Notif.updK]
  have hbs : BufSpecHyp σ ct.bv → BufSpecHyp σ1 ct.bv := by
    intro hb x' q hx' hq k hk
    rw [hk1'] at hx'; cases hx'
    obtain ⟨g1, g2⟩ := hb x q hkt hq k hk
    refine ⟨g1, ?_⟩
    obtain ⟨sz, hsz⟩ := g2
    refine ⟨sz, ?_⟩
    rw [hσ1, Notif.stsAct_kheap]
    have hne : (Endp.bufAddr q k &&& ~~~(Fl4Spec.mask (Fl4Spec.pageBitsForSize sz))) ≠ σ.curThread := by
      intro e; rw [e, hkt'] at hsz; cases hsz
    simp only [Notif.updK, Function.update_of_ne hne]; exact hsz
  refine ⟨s1, σ1, hrc, hs1, hst1, ⟨hDS1.1, hDS1.2.2, ?_, ?_⟩, hDS1, hC.wfr hW, hW, hc1, _, hk1', rfl, hbs⟩
  · rw [hk1]; exact MdbOKV.of_same hDS.1.2.2.1 hS1 hFR
  · rw [hk1]; exact hDR.of_same hW.2.2.2 hdom.1 hdom.2

/-- **The close of a decode replying itself**: after the restart, the
spec's invocation with result `rr` keeping the state (FL4's work and reply
writes `WFr`, the caller no longer `Restart`) is a `TopPostRM` outcome. -/
theorem rm_close {th : TypedHeap} (hP : Placed th) {G : MdbGhost} {σ σ1 : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {inv : Fl4Spec.Fl4Invocation}
    {ct : U64} {s s1 s2 : S} (a : A) (hdec : DecOut m σ inv)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (hRL : RL (L := L) th G s1 σ1) {x : Fl4Spec.Tcb} (hk : σ1.kheap ct.bv = some (.tcb x))
    (hrs : x.tcbState = .restart) (rr : List Fl4Spec.Word)
    (hy : (.ok rr, σ1) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1)
    (hbuf : call = true → ∀ q, Endp.ipcBufOf true x = some q → ∀ z ∈ Endp.mrPairs rr,
      (Endp.bufAddr q z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q z.1) σ1)
    (hW : WFr (L := L) th s1 s2) (hne : L.mem s2 (stA ct) ≠ sched.TS_RESTART) :
    TopPostRM (L := L) σ blk call don m ct s (.Ok (), s2, a) := by
  obtain ⟨z, hz, hz2⟩ := specTail_rl (hRL.wfr hW) hk hrs call rr hbuf
  exact Or.inr ⟨rfl, hne, inv, hdec, σ1, hst, rr, σ1, hy, z, hz, hz2.relTop hP⟩

/-- `rm_close` with the spec's invocation changing the state (`σy`). -/
theorem rm_close' {th : TypedHeap} (hP : Placed th) {G : MdbGhost} {σ σ1 σy : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {inv : Fl4Spec.Fl4Invocation}
    {ct : U64} {s s1 s2 : S} (a : A) (hdec : DecOut m σ inv)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (rr : List Fl4Spec.Word)
    (hy : (.ok rr, σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1)
    (hRL : RL (L := L) th G s1 σy) {x : Fl4Spec.Tcb} (hk : σy.kheap ct.bv = some (.tcb x))
    (hrs : x.tcbState = .restart)
    (hbuf : call = true → ∀ q, Endp.ipcBufOf true x = some q → ∀ z ∈ Endp.mrPairs rr,
      (Endp.bufAddr q z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q z.1) σy)
    (hW : WFr (L := L) th s1 s2) (hne : L.mem s2 (stA ct) ≠ sched.TS_RESTART) :
    TopPostRM (L := L) σ blk call don m ct s (.Ok (), s2, a) := by
  obtain ⟨z, hz, hz2⟩ := specTail_rl (hRL.wfr hW) hk hrs call rr hbuf
  exact Or.inr ⟨rfl, hne, inv, hdec, σ1, hst, rr, σy, hy, z, hz, hz2.relTop hP⟩

end

end

end Fl4Proofs.P3

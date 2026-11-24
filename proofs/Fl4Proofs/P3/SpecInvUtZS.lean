/-
P3 (DESIGN.md §9), invariant line G1 (g5g, KENTRY-PLAN g5g): **the performs of
`ZR` (l4v `untyped_ranges_zero` with `valid_untyped` for data pages) that the
generated families leave out, but the untyped perform** (spec side only;
outside the `JAtZ` cone).

* The performs the generated families leave out:
  - ReadFPU (`invokeFl4Tcb (fpuTransfer t true frame)`, `fl4FpuToFrame`
    writes the 2696 bytes at `frame`): the decode (`okv_fl4Decode_z`,
    `decodeFl4FpuTransfer`) gives a non-device page cap of the state's view
    whose frame holds those bytes (`FrameIn`); ut4's `CapFreeV` (carried in
    `P3`, l4v `valid_caps` + `valid_untyped`) puts every byte of a cap's frame
    outside every untyped's free part, so the write misses the free parts
    (`zr_invokeFl4Tcb`, on the canonical sets `HasU` / `PgOf` of the perform
    state);
  - MakePool (`perform_asid_control_invocation`): `retype_region` of an ASID
    pool creates no data page (`yk_retypeRegion_nd`);
  - the arch performs (`archPerformInvocation`): the IO-port reads / writes
    are `MZ` machine operations.
* NOT in this module (the second half, proofs/scratch/g5g/S.tail.lean, not
  green): `PerfGapZ` (the untyped perform obligation), `zr_fl4Perform`, the
  shell `zr_handleInvocationR` (ut7's `p3N_handleInvocationR` with `ZR`), the
  syscalls, events, `fl4CallKernel`, the entry (`kentry_zr_of`,
  `kcall_zr_of`, `kcall_zr_other`); KENTRY-PLAN g5g (7).
-/
import Fl4Proofs.P3.SpecInvUtZX
import Fl4Proofs.P3.SpecInvUtP6
import Fl4Proofs.P3.SpecFbX
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Canonical sets -/

theorem zs_canon {σ : State Unit} (h : ZR σ) : ZS (HasU σ) (PgOf σ) σ := by
  obtain ⟨hZ, hR⟩ := zr_iff.1 h
  refine ⟨?_, ?_, ?_, fun o sz h => h, ?_⟩
  · rintro b n f ⟨p, cref, hc⟩ o sz ho
    exact hR p cref b n f hc o sz ho
  · intro p cref c hc b n f e
    subst e
    exact ⟨f, ⟨p, cref, hc⟩, Or.inl le_rfl⟩
  · rintro o sz ho a ha ⟨b, n, f, ⟨p, cref, hc⟩, hfa⟩
    exact (hR p cref b n f hc o sz ho).1 a ha hfa
  · rintro a ⟨b, n, f, ⟨p, cref, hc⟩, h1, h2⟩
    exact hZ p cref b n f hc a h1 h2

theorem capAt_capOpt (σ : State Unit) (sl : CslotPtr) : SInvU.capAt σ sl = capOpt (σ.kheap sl.1) sl.2 := by
  unfold SInvU.capAt
  cases σ.kheap sl.1 with
  | none => rfl
  | some o => cases o <;> first | rfl | (simp only [SInvU.capView, capOpt]; split <;> rfl)

/-! ## ReadFPU: the decode -/

/-- The 2696 bytes ReadFPU writes lie in the frame of a non-device page cap. -/
def FrameIn (c : Cap) (frame : Word) : Prop :=
  ∃ (x : ObjRef) (R : VMRights) (mt : VMMapType) (sz : VMPageSize) (mp : Option (Asid × VSpaceRef)) (off : Word),
    c = .archObjectCap (.pageCap false x R mt sz mp) ∧ frame = x + off ∧
    off.toNat + fl4FpuStateSize ≤ 2 ^ pageBitsForSize sz

/-- The decode's fact for ReadFPU: its frame lies in a cap of the view. -/
def FpuI (w : UView) : Fl4TcbInvocation → Prop
  | .fpuTransfer _ true frame => ∃ p c, w.2.1 p = some c ∧ FrameIn c frame
  | _ => True

/-- #68: the `n` bytes at `frame` lie in the page of the page cap `c` (the TD
module writes them: GetReport's TDREPORT, GetQuote's quote). -/
def TdxFrameIn (c : Cap) (frame : Word) (n : Nat) : Prop :=
  ∃ (dev : Bool) (R : VMRights) (mt : VMMapType) (sz : VMPageSize) (mp : Option (Asid × VSpaceRef)),
    c = .archObjectCap (.pageCap dev frame R mt sz mp) ∧ n ≤ 2 ^ pageBitsForSize sz

/-- #68: the decode's fact for the TDX frame writes: the frame lies in a cap of the view. -/
def TdxI (w : UView) : Fl4TdxInvocation → Prop
  | .getReport f _ => ∃ p c, w.2.1 p = some c ∧ TdxFrameIn c f 0x1000
  | .extendRtmr _ _ => True
  | .getQuote f len => ∃ p c, w.2.1 p = some c ∧ TdxFrameIn c f (unat len)

/-- The decode's facts the hand-written performs need. -/
def InvZ (w : UView) : Fl4Invocation → Prop
  | .invokeFl4TCB i => FpuI w i
  | .invokeArchObject (.tdx i) => TdxI w i
  | _ => True

theorem the_head {α : Type} [Nonempty α] {l : List α} (h : l ≠ []) : ∃ x ∈ l, the l[0]? = x := by
  cases l with
  | nil => exact absurd rfl h
  | cons x l => exact ⟨x, List.mem_cons_self .., rfl⟩

/-- The decoders' traversal (results of other constructors). -/
macro "okz_auto" : tactic => `(tactic| repeat' (first
  | exact okv_throw _ | exact okv_throw_bind _ | exact okv_returnOk trivial
  | (refine okv_returnOk_bind ?_)
  | (refine okv_bind_uk (fun _ => by uk_auto) fun _ => ?_)
  | (refine okv_ite ?_ ?_)
  | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE)
  | split | (dsimp only)))

set_option maxHeartbeats 4000000 in
theorem okv_fpuTransfer {w : UView} (toFrame : Bool) (args : List Data) (t : ObjRef) (ex : List (Cap × CslotPtr))
    (hex : ∀ p ∈ ex, w.2.1 p.2 = some p.1) :
    OkV w (FpuI w) (decodeFl4FpuTransfer (Z := Unit) toFrame args t ex) := by
  unfold decodeFl4FpuTransfer NonDetE.whenE
  split
  · exact okv_throw_bind _
  rename_i h0
  refine okv_returnOk_bind (okv_returnOk_bind ?_)
  have hne : ex ≠ [] := fun e => h0 (Or.inl e)
  obtain ⟨⟨c0, s0⟩, he0, he⟩ := the_head hne
  rw [he]
  dsimp only
  cases c0 with
  | archObjectCap a =>
    cases a with
    | pageCap dev base rights mt sz mp =>
      dsimp only
      split
      · exact okv_throw _
      rename_i h1
      split
      · exact okv_throw_bind _
      rename_i h2
      refine okv_returnOk_bind (okv_returnOk ?_)
      cases toFrame
      · trivial
      · have hd : dev = false := by simp_all
        subst hd
        simp only [not_or, not_lt, not_le, ne_eq, Decidable.not_not] at h2
        exact ⟨s0, _, hex _ he0, base, rights, mt, sz, mp, the args[0]?, rfl, rfl, by omega⟩
    | _ => exact okv_throw _
  | _ => exact okv_throw _

set_option maxHeartbeats 4000000 in
theorem okv_fl4TcbExt {w : UView} (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (hex : ∀ p ∈ ex, w.2.1 p.2 = some p.1) :
    OkV w (FpuI w) (decodeFl4TcbExt (Z := Unit) l args t ex buf) := by
  cases l with
  | readFpu => exact okv_fpuTransfer true args t ex hex
  | writeFpu => exact okv_fpuTransfer false args t ex hex
  | _ =>
    simp only [decodeFl4TcbExt]
    first
      | (unfold decodeFl4SetBreakpoint; okz_auto)
      | (unfold decodeFl4GetBreakpoint; okz_auto)
      | (unfold decodeFl4UnsetBreakpoint; okz_auto)
      | (unfold decodeFl4ConfigureSingleStepping; okz_auto)
      | (unfold decodeFl4SetTimer; okz_auto)

theorem tdx_report_frame_in {c : Cap} {p : ObjRef} (h : tdxReportFrame c = some p) : TdxFrameIn c p 0x1000 := by
  unfold tdxReportFrame at h
  split at h
  · split at h
    · cases h
      exact ⟨_, _, _, _, _, rfl, by simp [pageBitsForSize, pageBits]⟩
    · cases h
  · cases h

theorem tdx_quote_frame_in {c : Cap} {p : ObjRef} {n : Nat} (h : tdxQuoteFrame c = some (p, n)) :
    TdxFrameIn c p n := by
  unfold tdxQuoteFrame at h
  split at h
  · split at h
    · cases h
      exact ⟨_, _, _, _, _, rfl, by simp [pageBitsForSize, pageBits]⟩
    · cases h
  · split at h
    · cases h
      exact ⟨_, _, _, _, _, rfl, by simp [pageBitsForSize, pageBits, ptTranslationBits]⟩
    · cases h
  · cases h

theorem TdxFrameIn.mono {c : Cap} {p : ObjRef} {n m : Nat} (h : TdxFrameIn c p n) (hm : m ≤ n) : TdxFrameIn c p m := by
  obtain ⟨d, R, mt, sz, mp, e, hn⟩ := h
  exact ⟨d, R, mt, sz, mp, e, by omega⟩

set_option maxHeartbeats 4000000 in
/-- #68: the TDX decode's frames lie in caps of the view. -/
theorem okv_decodeTdx {w : UView} (label : Data) (args : List Data) (ex : List (Cap × CslotPtr))
    (hex : ∀ p ∈ ex, w.2.1 p.2 = some p.1) :
    OkV w (TdxI w) (decodeTdxInvocation (Z := Unit) label args ex) := by
  unfold decodeTdxInvocation NonDetE.unlessE
  refine okv_bind_uk (fun v => by uk_auto) (fun plat => ?_)
  dsimp only
  split
  · refine okv_returnOk_bind (okv_ite ?_ (okv_ite ?_ (okv_ite ?_ (okv_throw _))))
    · unfold NonDetE.whenE
      split
      · exact okv_throw_bind _
      rename_i h0
      refine okv_returnOk_bind ?_
      have hne : ex ≠ [] := fun e => h0 (Or.inr e)
      obtain ⟨⟨c0, s0⟩, he0, he⟩ := the_head hne
      rw [he]
      dsimp only
      split
      · rename_i p hp
        exact okv_returnOk ⟨s0, c0, hex _ he0, tdx_report_frame_in hp⟩
      · exact okv_throw _
    · unfold NonDetE.whenE
      okz_auto
    · unfold NonDetE.whenE
      split
      · exact okv_throw_bind _
      rename_i h0
      refine okv_returnOk_bind ?_
      have hne : ex ≠ [] := fun e => h0 (Or.inr e)
      obtain ⟨⟨c0, s0⟩, he0, he⟩ := the_head hne
      rw [he]
      dsimp only
      split
      · rename_i p n hp
        split
        · refine okv_returnOk_bind ?_
          split
          · rename_i hl
            exact okv_returnOk_bind (okv_returnOk ⟨s0, c0, hex _ he0, (tdx_quote_frame_in hp).mono hl.2.2⟩)
          · exact okv_throw_bind _
        · exact okv_throw_bind _
      · exact okv_throw _
  · exact okv_throw_bind _

set_option maxHeartbeats 8000000 in
/-- **The decode's facts** (the ReadFPU frame). -/
theorem okv_fl4Decode_z {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (hex : ∀ p ∈ ex, w.2.1 p.2 = some p.1) :
    OkV w (InvZ w) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | threadCap p =>
    unfold fl4DecodeInvocation
    refine okv_ite (okv_throw _) ?_
    unfold fl4DecodeTcbInvocation
    refine okv_ite (okv_liftME (P := InvZ w) ?_) ?_
    · unfold decodeFl4SetFlags; okz_auto
    · split
      · exact okv_liftME (P := InvZ w) (okv_fl4TcbExt _ _ _ _ _ hex)
      · exact okv_liftME (okv_triv fun _ => trivial)
  | archObjectCap a =>
    unfold fl4DecodeInvocation
    refine okv_liftME (P := InvZ w) ?_
    cases a with
    | tdxControlCap =>
      simp only [fl4ArchDecodeInvocation]
      exact okv_liftME (okv_decodeTdx label args ex hex)
    | _ =>
      simp only [fl4ArchDecodeInvocation]
      repeat' (first | exact okv_liftME (okv_triv fun _ => trivial) | (refine okv_ite ?_ ?_))
  | _ =>
    unfold fl4DecodeInvocation
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_)
      | (dsimp only)
      | split)

/-! ## ReadFPU: the perform -/

/-- **The bytes of a page cap's frame miss every free part** (ut4's `CapFreeV`). -/
theorem fpu_bytes_free {σ : State Unit} (hC : CapFreeV (uV σ)) {p : CslotPtr} {c : Cap}
    (hp : (uV σ).2.1 p = some c) {frame : Word} (hF : FrameIn c frame) (a : Word)
    (ha : (a - frame).toNat < fl4FpuStateSize) : a.toNat ∉ FU (HasU σ) := by
  rintro ⟨b, n, f, ⟨p', cref, hc'⟩, hfa⟩
  obtain ⟨x, R, mt, sz, mp, off, rfl, rfl, hb⟩ := hF
  have hu : (uV σ).2.1 (p', cref) = some (.untypedCap false b n f) := by
    show SInvU.capAt σ (p', cref) = _; rw [capAt_capOpt]; exact hc'
  have hpb := pageBits_mem' sz
  have hpb' : 2 ^ pageBitsForSize sz ≤ 2 ^ 30 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
    rcases hpb with h | h | h <;> rw [h] <;> simp only [Nat.reducePow] <;> omega
  have hk : off.toNat + (a - (x + off)).toNat < 2 ^ pageBitsForSize sz := by
    unfold fl4FpuStateSize at hb ha; omega
  have hr : a ∈ capRng (.archObjectCap (.pageCap false x R mt sz mp)) := by
    refine ⟨off.toNat + (a - (x + off)).toNat, hk, ?_⟩
    have e1 : (BitVec.ofNat 64 (off.toNat + (a - (x + off)).toNat) : Word) = off + (a - (x + off)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_add]
    rw [e1]
    bv_omega
  exact hC _ _ _ _ _ hu _ _ _ hp hr hfa

theorem mem_fpuToFrame {frame : Word} {ms : MachineState} {x : Unit × MachineState}
    (hx : x ∈ (fl4FpuToFrame frame ms).1) (a : Word) (hne : x.2.underlyingMemory a ≠ ms.underlyingMemory a) :
    (a - frame).toNat < fl4FpuStateSize := by
  unfold fl4FpuToFrame at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  obtain ⟨z, ⟨hz, rfl⟩, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx] at hne
  by_contra hlt
  exact hne (hz a (by omega))

set_option maxHeartbeats 4000000 in
/-- **ReadFPU and the other FL4 TCB extensions keep `ZR`**, the frame's bytes
outside the free parts. -/
theorem zr_invokeFl4Tcb (i : Fl4TcbInvocation) (σ : State Unit) (hZ : ZR σ) (hC : CapFreeV (uV σ))
    (hF : FpuI (uV σ) i) : ∀ y ∈ ((invokeFl4Tcb (Z := Unit) i).run σ).1, ZR y.2 := by
  have hS := zs_canon hZ
  have hH : IKHE (HU (HasU σ)) (invokeFl4Tcb (Z := Unit) i) := by
    cases i <;> simp only [invokeFl4Tcb] <;> hv_auto
  have hY : IKp (YP (PgOf σ) (FU (HasU σ))) σ ((invokeFl4Tcb (Z := Unit) i).run) := by
    cases i with
    | fpuTransfer t toFrame frame =>
      simp only [invokeFl4Tcb]
      split
      · rename_i htf
        subst htf
        obtain ⟨p, c, hp, hFc⟩ := hF
        intro h y hy
        obtain ⟨z, hz, rfl⟩ := mem_liftE' hy
        obtain ⟨z1, hz1, hz⟩ := hz
        rw [Set.mem_singleton_iff.1 hz]
        exact ikp_dmo_w σ (fun x hx a hne ha => absurd ha
          (fpu_bytes_free hC hp hFc a (mem_fpuToFrame hx a hne))) h z1 hz1
      · exact ikp_of_ik (by yk_auto) σ
    | _ => exact ikp_of_ik (by simp only [invokeFl4Tcb]; yk_auto) σ
  intro y hy
  exact ⟨HasU σ, PgOf σ, hS.1, hH σ hS.2.1 y hy, hY hS.2.2 y hy⟩

/-! ## MakePool and the arch performs (memory half) -/

theorem yk_retypeRegionWith_nd {D : PgSet} {F : Set Nat} (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef)
    (n oB : Nat) (ty : ApiObjectType) (dev : Bool)
    (hty : ∀ d sz, defaultObject ty dev oB d ≠ .archObj (.dataPage false sz)) :
    YK D F (retypeRegionWith (Z := Unit) bA ptr n oB ty dev) := by
  intro σ h y hy
  rcases (SInvU.retypeRegionWith_out hy).2 with e | ⟨-, e⟩
  · rw [e]; exact h
  · rw [e]
    refine ⟨h.1, fun o sz ho => ?_, h.2.2⟩
    simp only [SInvU.retKh] at ho
    split_ifs at ho
    · exact absurd (Option.some.inj ho) (hty _ _)
    · exact h.2.1 o sz ho

theorem yk_retypeRegion_nd {D : PgSet} {F : Set Nat} (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType) (dev : Bool)
    (hty : ∀ d sz, defaultObject ty dev oB d ≠ .archObj (.dataPage false sz)) :
    YK D F (retypeRegion (Z := Unit) ptr n oB ty dev) := by
  rw [← retypeRegionWith_objBitsApi]; exact yk_retypeRegionWith_nd _ _ _ _ _ _ hty

macro_rules | `(tactic| yk_leaf) => `(tactic| ((with_reducible refine yk_retypeRegion_nd _ _ _ _ _ ?_); intro _ _ h; simp [defaultObject, defaultArchObject] at h))

theorem yk_performAsidControlInvocation {D : PgSet} {F : Set Nat} (iv : AsidControlInvocation) :
    YK D F (performAsidControlInvocation (Z := Unit) iv) := by
  cases iv; simp only [performAsidControlInvocation]; yk_auto

macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performAsidControlInvocation _)

set_option maxHeartbeats 4000000 in
theorem yk_archPerformInvocation {D : PgSet} {F : Set Nat} (ai : ArchInvocation) :
    YKE D F (archPerformInvocation (Z := Unit) ai) := by
  unfold archPerformInvocation; yk_auto

macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_archPerformInvocation _)

/-- fb3e: the frame batch (`SInv.ik_performFrameBatchW`). -/
theorem yk_performFrameBatch {D : PgSet} {F : Set Nat} (b : Fl4FrameBatchInvocation) :
    YK D F (performFrameBatch (Z := Unit) b) :=
  Fl4Proofs.P3.SInv.ik_performFrameBatchW b (fun _ _ _ _ => yk_capInsert _ _ _) (fun _ => yk_performPageInvocation _)
    (fun _ _ _ _ _ _ _ => yk_archFinaliseCap _ _) (fun _ => yk_emptySlot _ _)
    (fun _ _ _ _ => by unfold unmapPageUnflushed; yk_auto) (fun _ _ _ => yk_setCap _ _) (yk_flushAll _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performFrameBatch _)

/-- The arch performs but the TDX frame writes (`zr_tdx`). -/
theorem yk_fl4ArchPerformInvocation {D : PgSet} {F : Set Nat} (fa : Fl4ArchInvocation)
    (hT : ∀ i, fa ≠ .tdx i) : YKE D F (fl4ArchPerformInvocation (Z := Unit) fa) := by
  cases fa with
  | tdx i => exact absurd rfl (hT i)
  | _ => simp only [fl4ArchPerformInvocation]; yk_auto

theorem hu_setCap_bind_dead {U : UtSet} {β : Type} (cap : Cap) (sl : CslotPtr) {k : Unit → NonDet (State Unit) β}
    (hk : ∀ a, IKH (HU U) (k a))
    (hd : ∀ b n f, cap = .untypedCap false b n f → ∀ a σ x, x ∈ (k a σ).1 → False) :
    IKH (HU U) (setCap (Z := Unit) cap sl >>= k) := by
  intro σ h x ⟨y, hy, hx⟩
  by_cases hc : ∃ b n f, cap = .untypedCap false b n f
  · obtain ⟨b, n, f, e⟩ := hc; exact (hd b n f e _ _ x hx).elim
  · exact hk _ _ (hu_setCap cap sl (utIn_noUt (fun b n f e => hc ⟨b, n, f, e⟩) U) σ h y hy) x hx

/-- The dead continuation: the second bind's head fails. -/
macro "ut_dead_k" : tactic => `(tactic| (intro _ _ _ e _ _ x hx; subst e; obtain ⟨_, _, _, hf, _⟩ := hx; first | exact hf | (simp [NonDet.fail] at hf) | cases hf))

/-- The same with the map entry matched first (the page map). -/
macro "ut_dead_k2" : tactic => `(tactic| (intro _ _ _ e _ _ x hx; subst e; revert hx; split <;> (intro hx; obtain ⟨_, _, hx⟩ := hx; obtain ⟨_, hf, _⟩ := hx; first | exact hf | cases hf)))

theorem hu_performPageInvocation {U : UtSet} (iv : PageInvocation) :
    IKH (HU U) (performPageInvocation (Z := Unit) iv) := by
  cases iv with
  | pageMap cap sl ent vs =>
    simp only [performPageInvocation]
    exact hu_setCap_bind_dead _ _ (fun _ => by hv_auto) (by ut_dead_k2)
  | _ => simp only [performPageInvocation]; hv_auto

theorem hu_performPageTableInvocation {U : UtSet} (iv : PageTableInvocation) :
    IKH (HU U) (performPageTableInvocation (Z := Unit) iv) := by
  cases iv with
  | pageTableMap cap sl pde pd vs =>
    simp only [performPageTableInvocation]
    exact hu_setCap_bind_dead _ _ (fun _ => by hv_auto) (by ut_dead_k)
  | pageTableUnmap c sl =>
    by_cases hc : ∃ p ma, c = .archObjectCap (.pageTableCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hc; simp only [performPageTableInvocation]; hv_auto
    · simp only [performPageTableInvocation]
      split
      all_goals first | (exfalso; simp_all; done) | exact ik_fail

theorem hu_performPageDirectoryInvocation {U : UtSet} (iv : PageDirectoryInvocation) :
    IKH (HU U) (performPageDirectoryInvocation (Z := Unit) iv) := by
  cases iv with
  | pageDirectoryMap cap sl pde pd vs =>
    simp only [performPageDirectoryInvocation]
    exact hu_setCap_bind_dead _ _ (fun _ => by hv_auto) (by ut_dead_k)
  | pageDirectoryUnmap c sl =>
    by_cases hc : ∃ p ma, c = .archObjectCap (.pageDirectoryCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hc; simp only [performPageDirectoryInvocation]; hv_auto
    · simp only [performPageDirectoryInvocation]
      split
      all_goals first | (exfalso; simp_all; done) | exact ik_fail

theorem hu_performPdptInvocation {U : UtSet} (iv : PdptInvocation) :
    IKH (HU U) (performPdptInvocation (Z := Unit) iv) := by
  cases iv with
  | pdptMap cap sl pde pd vs =>
    simp only [performPdptInvocation]
    exact hu_setCap_bind_dead _ _ (fun _ => by hv_auto) (by ut_dead_k)
  | pdptUnmap c sl =>
    by_cases hc : ∃ p ma, c = .archObjectCap (.pdPointerTableCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hc; simp only [performPdptInvocation]; hv_auto
    · simp only [performPdptInvocation]
      split
      all_goals first | (exfalso; simp_all; done) | exact ik_fail

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_performPageInvocation _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_performPageTableInvocation _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_performPageDirectoryInvocation _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_performPdptInvocation _)

set_option maxHeartbeats 4000000 in
theorem hu_archPerformInvocation {U : UtSet} (ai : ArchInvocation) :
    IKHE (HU U) (archPerformInvocation (Z := Unit) ai) := by
  unfold archPerformInvocation; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_archPerformInvocation _)

theorem utIn_frame {U : UtSet} {c : Cap} (hc : Fl4Proofs.P3.SInv.IsFrameCap c) : UtIn U c :=
  fun b n f e => by subst e; exact False.elim hc

/-- fb3e: the frame batch (`SInv.ik_performFrameBatchW`): it inserts and writes frame caps only. -/
theorem hu_performFrameBatch {U : UtSet} (b : Fl4FrameBatchInvocation) : IKH (HU U) (performFrameBatch (Z := Unit) b) :=
  Fl4Proofs.P3.SInv.ik_performFrameBatchW b (fun c s d hc => hu_capInsert c s d (utIn_frame hc))
    (fun _ => hu_performPageInvocation _) (fun _ _ _ _ _ _ _ => hv_archFinaliseCap _ _)
    (fun sl => by unfold emptySlot; hv_auto) (fun _ _ _ _ => by unfold unmapPageUnflushed; hv_auto)
    (fun c sl hc => hu_setCap c sl (utIn_frame hc)) (hv_flushAll _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_performFrameBatch _)

theorem hu_fl4ArchPerformInvocation {U : UtSet} (fa : Fl4ArchInvocation) :
    IKHE (HU U) (fl4ArchPerformInvocation (Z := Unit) fa) := by
  cases fa <;> simp only [fl4ArchPerformInvocation] <;> hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_fl4ArchPerformInvocation _)

/-! ## The TDX frame writes (#68) -/

theorem mem_tdxFrameWrite {base : Word} {n : Nat} {ms : MachineState} {x : Unit × MachineState}
    (hx : x ∈ (tdxFrameWrite base n ms).1) (a : Word) (hne : x.2.underlyingMemory a ≠ ms.underlyingMemory a) :
    ∃ i < n, a = base + BitVec.ofNat 64 i := by
  unfold tdxFrameWrite at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  obtain ⟨z, ⟨hz, rfl⟩, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx] at hne
  by_contra hlt
  exact hne (hz a hlt)

/-- **The bytes of a TDX frame miss every free part** (ut4's `CapFreeV`). -/
theorem tdx_bytes_free {σ : State Unit} (hC : CapFreeV (uV σ)) {p : CslotPtr} {c : Cap}
    (hp : (uV σ).2.1 p = some c) {frame : Word} {n : Nat} (hF : TdxFrameIn c frame n) (a : Word)
    (ha : ∃ i < n, a = frame + BitVec.ofNat 64 i) : a.toNat ∉ FU (HasU σ) := by
  rintro ⟨b, m, f, ⟨p', cref, hc'⟩, hfa⟩
  obtain ⟨dev, R, mt, sz, mp, rfl, hb⟩ := hF
  have hu : (uV σ).2.1 (p', cref) = some (.untypedCap false b m f) := by
    show SInvU.capAt σ (p', cref) = _; rw [capAt_capOpt]; exact hc'
  obtain ⟨i, hi, rfl⟩ := ha
  exact hC _ _ _ _ _ hu _ _ _ hp ⟨i, by omega, rfl⟩ hfa

theorem tdxStatus_state {s : State Unit} {z : List Data × State Unit} (h : z ∈ (tdxStatus (Z := Unit) s).1) :
    z.2 = s := by
  unfold tdxStatus at h
  obtain ⟨y, ⟨-, rfl⟩, h⟩ := h
  rw [Set.mem_singleton_iff.1 h]

set_option maxHeartbeats 4000000 in
/-- **The TDX performs keep `ZR`**, the frames' bytes outside the free parts. -/
theorem zr_tdx (i : Fl4TdxInvocation) (σ : State Unit) (hZ : ZR σ) (hC : CapFreeV (uV σ))
    (hF : TdxI (uV σ) i) : ∀ y ∈ ((fl4ArchPerformInvocation (Z := Unit) (.tdx i)).run σ).1, ZR y.2 := by
  have hS := zs_canon hZ
  have hH : IKHE (HU (HasU σ)) (fl4ArchPerformInvocation (Z := Unit) (.tdx i)) := hu_fl4ArchPerformInvocation _
  have hY : IKp (YP (PgOf σ) (FU (HasU σ))) σ ((fl4ArchPerformInvocation (Z := Unit) (.tdx i)).run) := by
    cases i with
    | extendRtmr _ _ =>
      exact ikp_of_ik (by simp only [fl4ArchPerformInvocation, performTdxInvocation, tdxStatus]; yk_auto) σ
    | getReport f d =>
      obtain ⟨p, c, hp, hFc⟩ := hF
      simp only [fl4ArchPerformInvocation, performTdxInvocation]
      intro h y hy
      obtain ⟨z, hz, rfl⟩ := mem_liftE' hy
      obtain ⟨z1, hz1, hz⟩ := hz
      rw [tdxStatus_state hz]
      exact ikp_dmo_w σ (fun x hx a hne ha => absurd ha
        (tdx_bytes_free hC hp hFc a (mem_tdxFrameWrite hx a hne))) h z1 hz1
    | getQuote f l =>
      obtain ⟨p, c, hp, hFc⟩ := hF
      simp only [fl4ArchPerformInvocation, performTdxInvocation]
      intro h y hy
      obtain ⟨z, hz, rfl⟩ := mem_liftE' hy
      obtain ⟨z1, hz1, hz⟩ := hz
      rw [tdxStatus_state hz]
      exact ikp_dmo_w σ (fun x hx a hne ha => absurd ha
        (tdx_bytes_free hC hp hFc a (mem_tdxFrameWrite hx a hne))) h z1 hz1
  intro y hy
  exact ⟨HasU σ, PgOf σ, hS.1, hH σ hS.2.1 y hy, hY hS.2.2 y hy⟩

end

end Fl4Proofs.P3.SInvUZ

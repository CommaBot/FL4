/-
# P2 (line p3mc, gen 44): the PageMap certificate at every view start — `PmFhK` from the guarded-run fact `PmGdV`

Handoff §48c second bullet. The PageMap analogue of gen 29's PTE-delete certificate (P2/InvDelPteAnnA), same route
(`PathObl.safe_tr_wrU`), with the read set of the PTE-delete slot (`DelRdP`: `IoRS ∩ SR`, the locked leaf entries, the
aligned user words) and its checked writes (`DelPwP`: non-decision words, the caller's `STATE`, a Null / Frame word
into a locked non-TCB slot of the read set holding Null / Frame — the PageMap's `set_cap` of the mapped Frame cap,
`nof_enc_framePm` — the user words, and the locked leaves with any value — `write_mapping`'s leaf):

* **`PmGdV`** (module docstring below): at a PageMap view start the run of `R.invBodyPmG` on
  `gd st DelRdP DelPwP` is the real one — the exact statement P2/InvDelPteAnnA.lean:98 (`inv_pte_gdA`) proves for the
  PTE-arm Delete body, here for the PageMap body. Introduced here as a [J] premise; **discharged** in the same
  generation by `pmGdV_holds` (P2/InvPmGdV.lean), so it is no premise of the authoritative top
  `serializable_fl4_V15_pmKF`.
* **`wrsPm_facts`**: aligned user-word writes keep `PmPreG`, `QU`, the locks, `IoRS`, `IoWS`, the current thread and
  `PmRSU` (`pm_hufG`, `SlJAt.ioRWDS_wrSt`, `qU_wr`, `SlJAt.curW_wr`; the locks by `PmLk` [P], `PmObl7.lk`);
* **`pm_annA`**: the certificate from `PmGdV` (`Once` from the path's own `ReadOnce` — mmuAD's `pm_roAG` / `pm_ro`,
  through `pmPathsK`'s `once` field — at the user-word variant `σ'`, carried by `once_agreeJ`, narrowed by
  `once_downR`; the read words are `PmRS` words by `ioRSP_rperm`, so permitted-owned at the physical memory);
* **`pmFhK_of_gd`**: gen 44's [J] `PmFhK B7` (P2/E2EPV15PmK) from `PmGdV` — the glue (`StartPmK` → `PmPreG` by
  `gateEp_viewStart` / `pmRoot_of_qf`, `QU` by `qU_startN`);
* **`serializable_fl4_V15_pmKG`**: the PageMap top with `PmGdV` in place of `PmFhK` [J], from
  `serializable_fl4_V15_pmK` (the hypothesis `hGd` is supplied by `pmGdV_holds` in `serializable_fl4_V15_pmKF`).

## `PmGdV` (discharged: `pmGdV_holds`, P2/InvPmGdV.lean)
Statement: for every `K` with `RegionOKP` / `UserOKP`, core `c`, view source `ρ`, PageMap index `j`, state `σ` with
`PmPreG` at the view memory, `QU`, `cpu σ = c` and agreement with the view off user words, the run of
`R.invBodyPmG j.1 j.2` on `gd st (DelRdP K c ρ (IoRS K Locks σ) (Locks σ)) (DelPwP …)` ends as the real one.
Justification (why it holds; FL4 file:line): the accepted PageMap run reads only `IoRS (ptU K) σ` words and the
locked leaf `e` (P2/InvPmRoB.lean:31 `pmAccN`: hypotheses `hR`, `hRe` used only at `e`) — the prefix / plan words,
the caller's TCB and node, the frame-cap and PML4-cap slots, the ks `FEATURES` word, the ASID table / pool and the
upper paging words (region `.none`, kept by the view: `view_none_eq`) — and writes the caller's `STATE`, the slot's
`CAP0` with a Frame word (P2/InvPmMvA.lean:21), its `CAP1`, the leaf, the reply registers (P2/InvPmMvC.lean:50
`pm_mvG`, every write `StepOK`); a declined run writes the `IoDS` words only (P2/InvPmDec.lean:357 `pm_dec`). Every
one of these words is in `DelRdP` / passes `DelPwP` at a view start; the word classes are those of the PTE-arm
Delete body, for which P2/InvDelPteGd.lean:32 (`inv_run_gdP`) proves the statement. The proof (P2/InvPmGdV.lean,
`pm_run_gdV` / `pmGdV_holds`) uses the `G`-cut forms `pm_decRdC` / `pm_decWalkC` (P2/InvPmDecRd.lean), `pmAccG2C`
(P2/InvPmMvB.lean) and `pmFinGC` (P2/InvPmBlkE.lean), of which the uncut originals are instances. Not false at reachable states: at every
P3-covered state the PageMap walk is over `Zx.L1` tables (region `.none`, `RegionOKP.none`), the leaf is locked by
the plan (`pm_leaf_locked`, P2/InvPmLP.lean:337), and the caller's words are home (`vx_cur_home`).

Premise of `serializable_fl4_V15_pmKG`: `PmGdV` (replaces `PmFhK` [J]); both are theorems (`pmGdV_holds`,
`pmFhK_holds`, P2/InvPmGdV.lean). New module; no existing statement changes.

**Gen 51 (line p3mc), in-place split, every existing statement byte-identical up to `:=`**: `pm_annA`'s run oracle is
split out as **`pm_hgoX`** (≤ 4M), which also returns the user-word variant `σ'` of the start the oracle state runs at
(`PmPreG`, `QU`, agreement on the read set, kernel base, core and masks, its run inside `DelRdP` / `DelWdP`);
`pm_annA` is re-proved from it. P2/InsV15Pm uses `pm_hgoX` for the `InsAP` twin.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `serializable_fl4_V15_pmKG`.
-/
import Fl4Proofs.P2.E2EPV15PmK
import Fl4Proofs.P2.InvDelPteAnnA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE oSTATE InW GateField TimerField GField
  tcbOwner TcbSlot NullOrFrame)
open Fl4Proofs.P2.E2E (SP tr masksOf Once StartAt LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN NotForeign vn_of_nf nf_node nf_slot nf_none nf_tcb TZero)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

variable (st) in
/-- **The PageMap guarded-run fact at a view start** (module docstring): the run of the PageMap body on the
checked store `gd st DelRdP DelPwP` is the real one (the PageMap counterpart of `inv_pte_gdA`); a theorem,
`pmGdV_holds` (P2/InvPmGdV.lean). -/
def PmGdV (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop :=
  ∀ (K : KLayoutP), RegionOKP K → UserOKP K → ∀ (c : U64) (ρ : U64 → U64) (j : I64 × localinv.Plan) (σ : S) (a : A),
    PmPreG st Cs Ω Sg Ac Locks j.2 K (view K.toKLayout c ρ) σ → QU st K σ → L.cpu σ = c →
    (∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) →
    ∃ r, interp (gd st (DelRdP K c ρ (IoRS (st := st) K.toKLayout Locks σ) (Locks σ))
        (DelPwP (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ) (IoWS (st := st) K.toKLayout Locks σ)
          (L.curW σ) (L.mem σ) (Locks σ))) ar (R.invBodyPmG j.1 j.2) σ a = ok r ∧
      interp st ar (R.invBodyPmG j.1 j.2) σ a = ok r

omit [Fl4Proofs.P1.PlainStore st] in
/-- **Aligned user-word writes keep the PageMap view start's facts** (module docstring). -/
theorem wrsPm_facts {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {j : I64 × localinv.Plan} {K : KLayoutP}
    {m f : U64 → U64} (hCs : ∀ c ∈ Cs, c.val < 64) (hlk : PmLk st Locks) :
    ∀ (l : List U64) (s : S), (∀ x ∈ l, Aligned x ∧ x ∈ K.user) →
      PmPreG st Cs Ω Sg Ac Locks j.2 K m s → QU st K s →
      PmPreG st Cs Ω Sg Ac Locks j.2 K m (E2E.wrs st f l s) ∧ QU st K (E2E.wrs st f l s) ∧
      Locks (E2E.wrs st f l s) = Locks s ∧
      IoRS (st := st) K.toKLayout Locks (E2E.wrs st f l s) = IoRS (st := st) K.toKLayout Locks s ∧
      IoWS (st := st) K.toKLayout Locks (E2E.wrs st f l s) = IoWS (st := st) K.toKLayout Locks s ∧
      L.curW (E2E.wrs st f l s) = L.curW s ∧
      PmRSU st K Locks (E2E.wrs st f l s) = PmRSU st K Locks s := by
  intro l
  induction l with
  | nil => intro s _ h1 h3; exact ⟨h1, h3, rfl, rfl, rfl, rfl, rfl⟩
  | cons x l ih =>
    intro s hl h1 h3
    obtain ⟨ha, hu⟩ := hl x (List.mem_cons_self ..)
    obtain ⟨g1, g3, g8, -, -⟩ := pm_hufG (pm_iw hCs) hlk j K m s x (f x) h1 hu ha
    obtain ⟨g4, g5, -⟩ := h1.1.1.ioRWDS_wrSt hu ha (f x) g3
    have g6 : QU st K (L.wr s x (f x)) := qU_wr h3 hu ha
    have g7 := h1.1.1.curW_wr hu ha (f x)
    obtain ⟨k1, k3, k4, k5, k6, k7, k8⟩ := ih _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) g1 g6
    exact ⟨k1, k3, k4.trans g3, k5.trans g4, k6.trans g5, k7.trans g7, k8.trans g8⟩

set_option maxHeartbeats 4000000 in
/-- (gen 51, split out of `pm_annA` in place) **`pm_annA`'s run oracle, with the user-word variant of the start it
runs at** (as P2/InvDelPteAnnA's `pte_hgoX`): the original's three facts, and `σ'` = `σ` with `s`'s user words is again
a PageMap view start (`PmPreG`, `QU`), agreeing with `s` on the read set, the kernel base, the core and the masks, its
run inside `DelRdP` / `DelWdP`. -/
theorem pm_hgoX (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {j : I64 × localinv.Plan} {σ : S} {a : A}
    (hCs : ∀ c ∈ Cs, c.val < 64) (hlk : PmLk st Locks) (hGd : PmGdV st ar Cs Ω Sg Ac Locks)
    (hPre : PmPreG st Cs Ω Sg Ac Locks j.2 K (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ →
      (∀ b, ((IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b) ∨ PteRd K (Locks σ) b) → L.mem s b = ρ b) →
      ∃ r, interp (guard st (fun b => ((IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b) ∨ PteRd K (Locks σ) b) ∨
          PathObl.UserW K.toKLayout b) (DelWdP K c ρ (IoWS (st := st) K.toKLayout Locks σ) (Locks σ))) ar
          (R.invBodyPmG j.1 j.2) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.invBodyPmG j.1 j.2) s a ∧
        Once st ar (fun q => PmRSU st K Locks σ q ∧ VO K c ρ q) (· ∈ K.user) ∅ ∅ (R.invBodyPmG j.1 j.2) s a ∧
        ∃ σ' : S, PmPreG st Cs Ω Sg Ac Locks j.2 K (view K.toKLayout c ρ) σ' ∧ QU st K σ' ∧
          (∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x) ∧
          L.ksb s = L.ksb σ' ∧ L.cpu s = L.cpu σ' ∧ st.frame_masks s = st.frame_masks σ' ∧
          (∀ b, DelRdP K c ρ (IoRS (st := st) K.toKLayout Locks σ) (Locks σ) b → L.mem s b = L.mem σ' b) ∧
          Within st ar (DelRdP K c ρ (IoRS (st := st) K.toKLayout Locks σ) (Locks σ))
            (DelWdP K c ρ (IoWS (st := st) K.toKLayout Locks σ) (Locks σ)) (R.invBodyPmG j.1 j.2) σ' a := by
  have hJ : SlJAt (L := L) K.toKLayout σ := hPre.1.1
  have hq := hPre.1.2.1
  have nv : K.vcpus = ∅ := hPre.1.2.2.nv
  have hX := hJ.regionOKX
  have hK0 := hJ.regionOK
  have hUO := hJ.userOK
  obtain ⟨Ac', B⟩ := bunIx_of hJ
  have hI := B.bxi
  have hL := B.stLay
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayout.heap.tcbs := h0.tcbs
  have hcT : L.curW σ ∈ K.toKLayout.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have ht' := hT _ hcT
  have hcur : ρ (fld (L.curW σ) oAFFINITY) = c := vx_cur_home hJ hmm
  have PE := hq.1.1.1
  have hL8 : Slot8 K.toKLayout := fun q hq => PE.lay.slot8 q hq
  have srT : ∀ k : U64, 192 ≤ k.val → k.val < 4096 → k.val % 8 = 0 →
      SR K c ρ (core.num.U64.wrapping_add (L.curW σ) k) := fun k h1 h2 h3 =>
    sr_tcb hK hX htH hcur (o := k) h1 h2 h3
  -- the read sets
  have kPte : ∀ b, b ∈ K.ptes → Aligned b ∧ b ∉ K.user := fun b hb => hU.kern b hb
  have vPte : ∀ b, b ∈ K.ptes → VN K c ρ b := fun b hb => vn_of_nf hK (nf_none (hK.none b hb))
  have oPte : ∀ b, b ∈ K.ptes → VO K c ρ b := fun b hb => by unfold VO; rw [ownP_pte hb, ownP_pte hb]
  let Rd : U64 → Prop := fun b => (IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b) ∨ PteRd K (Locks σ) b
  let Ro : U64 → Prop := fun q => PmRSU st K Locks σ q ∧ VO K c ρ q
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := by
    rintro q (⟨h1, h2⟩ | ⟨hp, hl'⟩)
    · have hio : IoRSP st K Locks σ q := ⟨h1, fun hp => absurd hp h2.2⟩
      exact ⟨⟨⟨h1.1, Or.inr ⟨h1.1, h1.2.1, ioRSP_rperm nv hio⟩⟩, h2.1.2⟩, h1.2.1⟩
    · have hio : IoRSP st K Locks σ q :=
        ⟨VsW.ioRS ⟨(kPte q hp).1, hK.none q hp, (kPte q hp).2⟩, fun _ => hl'⟩
      exact ⟨⟨⟨(kPte q hp).1, Or.inr ⟨(kPte q hp).1, (kPte q hp).2, ioRSP_rperm nv hio⟩⟩, oPte q hp⟩,
        (kPte q hp).2⟩
  have hal : ∀ b, Rd b → Aligned b := by
    rintro b (hb | hb)
    · exact hb.1.1
    · exact (kPte b hb.1).1
  have kvR : ∀ b, Rd b → L.mem σ b = ρ b := by
    rintro b (hb | hb)
    · exact (hmm b hb.1.1 hb.1.2.1).trans hb.2.1.1
    · exact (hmm b (kPte b hb.1).1 (kPte b hb.1).2).trans (vPte b hb.1).1
  let Ru : U64 → Prop := PathObl.UserW K.toKLayout
  let RdU : U64 → Prop := DelRdP K c ρ (IoRS (st := st) K.toKLayout Locks σ) (Locks σ)
  have hRal : ∀ b, RdU b → Aligned b := fun b h => Or.elim h (hal b) (fun h => h.1)
  -- the write sets
  let Wd : U64 → Prop := DelWdP K c ρ (IoWS (st := st) K.toKLayout Locks σ) (Locks σ)
  let Pw0 : S → U64 → U64 → Prop := DelPw (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ)
    (IoWS (st := st) K.toKLayout Locks σ) (L.curW σ) (L.mem σ) (Locks σ)
  let Pw : S → U64 → U64 → Prop := DelPwP (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ)
    (IoWS (st := st) K.toKLayout Locks σ) (L.curW σ) (L.mem σ) (Locks σ)
  have wdW : ∀ b, IoWS (st := st) K.toKLayout Locks σ b → SR K c ρ b →
      IoWS (st := st) K.toKLayout Locks σ b ∧ b ∉ K.ptes ∧ VO K c ρ b := fun b h g => ⟨h, g.2, g.1.2⟩
  have eSt : core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE = core.num.U64.wrapping_add (L.curW σ) 3328#u64 := by
    rw [← Fl4Proofs.P1.stA_eq]; rfl
  have hPW0 : ∀ x q v, Pw0 x q v → DelWd K c ρ (IoWS (st := st) K.toKLayout Locks σ) q := by
    rintro x q v (⟨-, -, h⟩ | ⟨rfl, -⟩ | ⟨hq', hT', hRd, hn, -, hl'⟩ | hu)
    · exact Or.inl h
    · have e := wdW _ PE.stw.2
      rw [Fl4Proofs.P1.stA_eq] at e
      rw [eSt]; exact Or.inl (e (srT 3328#u64 (by simp) (by simp) (by simp)))
    · have w := (PE.lockSlot hq' hl' (o := 0#u64) (by simp) (by simp)).2 (Or.inr ⟨hT', hn⟩)
      rw [wadd_zero (hL8 q hq').2] at w
      exact Or.inl (wdW _ w hRd.2)
    · exact Or.inr hu
  have hPW : ∀ x q v, Pw x q v → Wd q := by
    rintro x q v (h | h)
    · exact Or.inl (hPW0 x q v h)
    · exact Or.inr h
  have hWal : ∀ b, Wd b → Aligned b := by
    rintro b ((h | h) | h)
    · exact h.1.1
    · exact h.1
    · exact (kPte b h.1).1
  have hPal : ∀ x q v, Pw x q v → Aligned q := fun x q v h => hWal q (hPW x q v h)
  -- the checked writes pass `StepOK`, keeping the invariant
  have hpA : fld (L.curW σ) oAFFINITY ∉ K.ptes := (srT 3520#u64 (by simp) (by simp) (by simp)).2
  have hμc : μ (fld (L.curW σ) oAFFINITY) = c := by
    have hpo : PO c hs (ownP K μ (fld (L.curW σ) oAFFINITY)) := by
      right; rw [ownP_eq_own nv hpA]; exact OwnMap.own_aff_gate hK0 htH μ
    rw [← hV.2.1 _ hpo]; exact hcur
  have affC : L.mem σ (fld (L.curW σ) oAFFINITY) = c := by
    have hu : fld (L.curW σ) oAFFINITY ∉ K.user := hL.nu_tcb hcT (k := 3520#u64) (by simp) (by simp)
    have ha : Aligned (fld (L.curW σ) oAFFINITY) := field_aligned ht' (by simp [OwnMap.oAFF_val])
      (by simp [OwnMap.oAFF_val])
    rw [hmm _ ha hu]
    exact CoreView.view_aff hK0 htH c ρ
  have aA : Aligned (fld (L.curW σ) oAFFINITY) := field_aligned ht' (by simp [OwnMap.oAFF_val])
    (by simp [OwnMap.oAFF_val])
  have aS : Aligned (fld (L.curW σ) oSTATE) := by rw [← OwnMap.stA_fld]; exact field_aligned ht' (by simp) (by simp)
  have dA : OwnMap.DecW K.toKLayout (fld (L.curW σ) oAFFINITY) := OwnMap.decW_tcb htH (Or.inl rfl)
  have dS : OwnMap.DecW K.toKLayout (fld (L.curW σ) oSTATE) := OwnMap.decW_tcb htH (Or.inr (Or.inl rfl))
  have nAS : fld (L.curW σ) oAFFINITY ≠ fld (L.curW σ) oSTATE :=
    OwnMap.fld_ne_off hK0 htH (Or.inl rfl) (Or.inr (Or.inl rfl)) (by simp [OwnMap.oAFF_val, OwnMap.oSTATE_val])
  have nSl : ∀ q, q ∈ K.slots → ∀ off, OwnMap.DecOff off → fld (L.curW σ) off ≠ q := fun q hq' off ho e => by
    have h1 := (hK0.tcb _ htH off ho.reg).1
    rw [e, hK0.slot _ hq'] at h1; exact OwnMap.Region.noConfusion h1
  have eS' : core.num.U64.wrapping_add (L.curW σ) layout.tcb.STATE = fld (L.curW σ) oSTATE := by
    rw [← OwnMap.stA_fld]; rfl
  let Rd0 : U64 → Prop := fun b => IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b
  let Inv : S → Prop := fun x => L.mem x (fld (L.curW σ) oAFFINITY) = c ∧
    ¬ OwnMap.QueuedState (L.mem x (fld (L.curW σ) oSTATE)) ∧
    ∀ q, q ∈ K.slots → ¬ TcbSlot K.toKLayout q → Rd0 q → NullOrFrame (L.mem σ q) → NullOrFrame (L.mem x q)
  have hStep : ∀ (x : S) (q v : U64) (x' : S), Inv x → Pw x q v → st.write x q v = ok x' →
      PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem x)
        (L.mem x') ∧ Inv x' := by
    intro x q v x' hI' hP hw
    rw [L.write_eq] at hw
    have e := ok_inj_ff hw
    subst e
    have ha := hPal x q v hP
    obtain ⟨i1, i2, i3⟩ := hI'
    rcases hP with (⟨-, hnd, -⟩ | ⟨rfl, hv⟩ | ⟨hq', hT', hRd, hn, hv, -⟩ | hu) | ⟨hp, -⟩
    · refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd)),
        ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dA))]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dS))]; exact i2
      · intro q' hq' hT' hRd' hn'
        have dq : OwnMap.DecW K.toKLayout q' := Or.inr (Or.inl hq')
        rw [OwnMap.mem_wr_upd ha (hRd'.1.1), Function.update_of_ne (fun h => hnd (by rw [← h]; exact dq))]
        exact i3 q' hq' hT' hRd' hn'
    · rw [eS'] at ha ⊢
      refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_state hK0 hUO (m0 := μ) htH i1 hμc
        (fun hq' => absurd hq' i2) (fun hq' => absurd hq' (nq_run hv)))), ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne nAS]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_self]; exact nq_run hv
      · intro q' hq' hT' hRd' hn'
        rw [OwnMap.mem_wr_upd ha (hRd'.1.1), Function.update_of_ne (nSl q' hq' _ (Or.inr (Or.inl rfl))).symm]
        exact i3 q' hq' hT' hRd' hn'
    · refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base
        (OwnMap.stepOK_slot hK0 hUO (m0 := μ) hq' hT' (i3 q hq' hT' hRd hn) hv)), ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne (nSl q hq' _ (Or.inl rfl))]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_of_ne (nSl q hq' _ (Or.inr (Or.inl rfl)))]; exact i2
      · intro q' hq'' hT'' hRd' hn'
        rw [OwnMap.mem_wr_upd ha (hRd'.1.1)]
        by_cases e : q' = q
        · subst e; rw [Function.update_self]; exact hv
        · rw [Function.update_of_ne e]; exact i3 q' hq'' hT'' hRd' hn'
    · have hnd : ¬ OwnMap.DecW K.toKLayout q := fun hd => (OwnMap.decW_ok hUO hd).2 hu.2
      refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd)),
        ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dA))]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dS))]; exact i2
      · intro q' hq' hT' hRd' hn'
        have dq : OwnMap.DecW K.toKLayout q' := Or.inr (Or.inl hq')
        rw [OwnMap.mem_wr_upd ha (hRd'.1.1), Function.update_of_ne (fun h => hnd (by rw [← h]; exact dq))]
        exact i3 q' hq' hT' hRd' hn'
    · have hnd : ¬ OwnMap.DecW K.toKLayout q := pte_nondec hK hp
      refine ⟨stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd)),
        ?_, ?_, ?_⟩
      · rw [OwnMap.mem_wr_upd ha aA, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dA))]; exact i1
      · rw [OwnMap.mem_wr_upd ha aS, Function.update_of_ne (fun h => hnd (by rw [← h]; exact dS))]; exact i2
      · intro q' hq' hT' hRd' hn'
        have dq : OwnMap.DecW K.toKLayout q' := Or.inr (Or.inl hq')
        rw [OwnMap.mem_wr_upd ha (hRd'.1.1), Function.update_of_ne (fun h => hnd (by rw [← h]; exact dq))]
        exact i3 q' hq' hT' hRd' hn'
  -- the aligned user words
  have hfin : Set.Finite {x : U64 | Aligned x ∧ x ∈ K.user} := Set.toFinite _
  obtain ⟨ul, hul⟩ : ∃ l : List U64, ∀ x, x ∈ l ↔ Aligned x ∧ x ∈ K.user :=
    ⟨hfin.toFinset.toList, fun x => by simp⟩
  have slNU : ∀ q, q ∈ K.slots → Aligned q ∧ q ∉ K.user := fun q hq' => OwnMap.decW_ok hUO (Or.inr (Or.inl hq'))
  -- every state carrying `ρ` on the kernel reads runs as a view start with its user words
  intro s hcs' hks hag
  have hagR : ∀ b, Rd b → L.mem s b = L.mem σ b := fun b hb => (hag b hb).trans (kvR b hb).symm
  obtain ⟨σ', hσ'⟩ : ∃ x, x = E2E.wrs st (L.mem s) ul σ := ⟨_, rfl⟩
  obtain ⟨c1, c2, c3⟩ := E2E.wrs_const st (ν := L.mem s) (masksWr_plain st) ul σ
  have hM := E2E.wrs_mem st (ν := L.mem s) ul σ (fun x hx => ((hul x).mp hx).1)
  obtain ⟨hPre', hqu', eL, eRS, eWS, eCur, ePm⟩ := wrsPm_facts (f := L.mem s) hCs hlk ul σ
    (fun x hx => (hul x).mp hx) hPre hqu
  rw [← hσ'] at c1 c2 c3 hM hPre' hqu' eL eRS eWS eCur ePm
  have hmm' : ∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x := fun x hx hu => by
    rw [hM x hx, if_neg (fun h => hu ((hul x).mp h).2)]; exact hmm x hx hu
  obtain ⟨r', hg', hs'⟩ := hGd K hK hU c ρ j σ' a hPre' hqu' (c1.trans hc) hmm'
  have eP : DelPwP (S := S) K c ρ (IoRS (st := st) K.toKLayout Locks σ') (IoWS (st := st) K.toKLayout Locks σ')
      (L.curW σ') (L.mem σ') (Locks σ') = Pw := by
    rw [eRS, eWS, eCur, eL]
    exact delPwP_mem fun q hq' => by
      rw [hM q (slNU q hq').1, if_neg (fun h => (slNU q hq').2 ((hul q).mp h).2)]
  rw [eP, eRS, eL] at hg'
  have hagU : ∀ b, RdU b → L.mem s b = L.mem σ' b := by
    rintro b (hb | hb)
    · rw [hagR b hb, hM b (hal b hb), if_neg (fun h => (hR0 b hb).2 ((hul b).mp h).2)]
    · rw [hM b hb.1, if_pos ((hul b).mpr hb)]
  have hmk' : st.frame_masks s = st.frame_masks σ' := by
    rw [PlainStore.frame_masks_eq, PlainStore.frame_masks_eq]
  obtain ⟨x0, s0', a0'⟩ := r'
  obtain ⟨s1', hs1⟩ := interp_agree_gd (st := st) (masksWr_plain st) hRal hPal (fun _ _ _ _ _ h => h)
    (R.invBodyPmG j.1 j.2) (pm_noZero j.1 j.2) σ' s a x0 s0' a0' (hks.trans c2.symm) (hcs'.trans c1.symm)
    hmk' hagU hg'
  have hgs := interp_gd_guard (R' := RdU) (W := Wd) (fun q h => h) hPW _ s a _ hs1
  -- `StepOK` per write
  have hI0 : Inv s := by
    have rA : Rd0 (fld (L.curW σ) oAFFINITY) :=
      ⟨PE.gate (Locks := Locks) (off := 3520#u64) PE.cT (by simp) (by simp) (by simp) (by simp [GateField]),
        srT 3520#u64 (by simp) (by simp) (by simp)⟩
    have rS : Rd0 (fld (L.curW σ) oSTATE) := by
      rw [← OwnMap.stA_fld]
      refine ⟨PE.stw.1, ?_⟩
      rw [Fl4Proofs.P1.stA_eq]; exact srT 3328#u64 (by simp) (by simp) (by simp)
    refine ⟨(hagR _ (Or.inl rA)).trans affC, ?_, fun q hq' hT' hRd hn => by rw [hagR q (Or.inl hRd)]; exact hn⟩
    rw [hagR _ (Or.inl rS), ← OwnMap.stA_fld]
    exact nq_run PE.run
  have hm := interp_gd (R := RdU) (P := Pw)
    (Q := fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs
      (L.mem x) (L.mem y)) (I := Inv) hStep _ s a _ hI0 hs1
  -- `Once`: the path's `ReadOnce` at `σ'` (mmuAD's `pm_roAG` / `pm_ro`), carried to `s`, narrowed
  have hO1 : Once st ar (PmRSU st K Locks σ') (· ∈ K.user) ∅ ∅ (R.invBodyPmG j.1 j.2) σ' a :=
    (pmPathsK hA (masksWr_plain st) (⟨hCs, hlk⟩ : PmObl7 st Cs Ω Sg Ac Locks) j K (view K.toKLayout c ρ) hK
      hU).once σ' σ' a _ hPre' (Alt.refl (L := L) σ') hs'
  have hO1' : Once st ar (PmRSU st K Locks σ) (· ∈ K.user) ∅ ∅ (R.invBodyPmG j.1 j.2) σ' a := by
    have h' := hO1
    rw [ePm] at h'
    exact h'
  have hgσ' := interp_gd_guard (R' := RdU) (W := Wd) (fun q h => h) hPW _ σ' a _ hg'
  have hO2 := once_agreeJ (masksWr_plain st) (Rd := PmRSU st K Locks σ) (User := (· ∈ K.user))
    hRal hWal (R.invBodyPmG j.1 j.2) (pm_noZero j.1 j.2) σ' s a _ ∅ ∅ (hks.trans c2.symm) (hcs'.trans c1.symm)
    hmk' hagU hgσ' hO1'
  have hO3 := once_downR (R := Rd) (Ro := Ro) (R' := PmRSU st K Locks σ) (U := Ru) (W := Wd)
    (User := (· ∈ K.user)) (fun q h => (hR0 q h).2) (fun q h => (hR0 q h).1) (fun q h => h.1) (fun q h => h.2)
    (R.invBodyPmG j.1 j.2) (pm_noZero j.1 j.2) ∅ ∅ s a _ hgs hO2
  exact ⟨_, hgs, (interp_mguard _ s a _ hm).2, hO3, σ', hPre', hqu', hmm', hks.trans c2.symm, hcs'.trans c1.symm,
    hmk', hagU, (interp_guard _ σ' a _ hgσ').2⟩

set_option maxHeartbeats 4000000 in
/-- **The PageMap program is `Safe` at every PageMap view start, given `PmGdV`** (module docstring). -/
theorem pm_annA (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {j : I64 × localinv.Plan} {σ : S} {a : A}
    (hCs : ∀ c ∈ Cs, c.val < 64) (hlk : PmLk st Locks) (hGd : PmGdV st ar Cs Ω Sg Ac Locks)
    (hPre : PmPreG st Cs Ω Sg Ac Locks j.2 K (view K.toKLayout c ρ) σ) (hqu : QU st K σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (PmRSU st K Locks σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.invBodyPmG j.1 j.2) ∅ a)) := by
  have nv : K.vcpus = ∅ := hPre.1.2.2.nv
  have hgoX := pm_hgoX ar hA hK hU hV (j := j) (a := a) hCs hlk hGd hPre hqu hc hmm
  -- the read sets
  have kPte : ∀ b, b ∈ K.ptes → Aligned b ∧ b ∉ K.user := fun b hb => hU.kern b hb
  have oPte : ∀ b, b ∈ K.ptes → VO K c ρ b := fun b hb => by unfold VO; rw [ownP_pte hb, ownP_pte hb]
  let Rd : U64 → Prop := fun b => (IoRS (st := st) K.toKLayout Locks σ b ∧ SR K c ρ b) ∨ PteRd K (Locks σ) b
  let Ro : U64 → Prop := fun q => PmRSU st K Locks σ q ∧ VO K c ρ q
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := by
    rintro q (⟨h1, h2⟩ | ⟨hp, hl'⟩)
    · have hio : IoRSP st K Locks σ q := ⟨h1, fun hp => absurd hp h2.2⟩
      exact ⟨⟨⟨h1.1, Or.inr ⟨h1.1, h1.2.1, ioRSP_rperm nv hio⟩⟩, h2.1.2⟩, h1.2.1⟩
    · have hio : IoRSP st K Locks σ q :=
        ⟨VsW.ioRS ⟨(kPte q hp).1, hK.none q hp, (kPte q hp).2⟩, fun _ => hl'⟩
      exact ⟨⟨⟨(kPte q hp).1, Or.inr ⟨(kPte q hp).1, (kPte q hp).2, ioRSP_rperm nv hio⟩⟩, oPte q hp⟩,
        (kPte q hp).2⟩
  have hal : ∀ b, Rd b → Aligned b := by
    rintro b (hb | hb)
    · exact hb.1.1
    · exact (kPte b hb.1).1
  let Ru : U64 → Prop := PathObl.UserW K.toKLayout
  let Wd : U64 → Prop := DelWdP K c ρ (IoWS (st := st) K.toKLayout Locks σ) (Locks σ)
  -- ownership of the read and written words at the physical memory
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hWd : ∀ x, Wd x → Aligned x ∧ (¬ x ∈ K.user → HeldV c hs (ownP K μ x)) := by
    rintro x ((⟨⟨ha, hw⟩, hp, hvo⟩ | hu) | ⟨hp, hlx⟩)
    · refine ⟨ha, fun _ => ?_⟩
      have h1 : HeldV c hs (ownP K (L.mem σ) x) := by
        rw [ownP_eq_own nv hp, ← hc, ← hl]
        exact heldV_of_heldBy hw
      rw [eown, hvo] at h1
      rw [hV.1 x (Or.inl h1)]
      exact h1
    · exact ⟨hu.1, fun h => absurd hu.2 h⟩
    · refine ⟨(kPte x hp).1, fun _ => ?_⟩
      rw [ownP_pte hp]
      show hs x
      rw [← hl]; exact hlx
  have hRPO : ∀ x, ¬ x ∈ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have hrs : PmRS st K Locks σ x := pmRSU_nu hx.1 hu
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      have := po_of_rperm hrs.2.2
      rw [hc, hl] at this
      exact this
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  -- every state carrying `ρ` on the kernel reads runs as a view start with its user words (`pm_hgoX`)
  have hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st (fun b => Rd b ∨ Ru b) Wd) ar (R.invBodyPmG j.1 j.2) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.invBodyPmG j.1 j.2) s a ∧
        Once st ar Ro (· ∈ K.user) ∅ ∅ (R.invBodyPmG j.1 j.2) s a := by
    intro s hcs' hks hag
    obtain ⟨r, h1, h2, h3, -⟩ := hgoX s hcs' hks hag
    exact ⟨r, h1, h2, h3⟩
  have h := PathObl.safe_tr_wrU (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) (masksWr_plain st) (a := a)
    (R.invBodyPmG j.1 j.2) hc (Ro := Ro) (Rd := Rd) (Ru := Ru) (Wd := Wd) hal hR0 (fun b h => h.1)
    hWd hRPO (fun x hx => hV.2.1 x hx) hgo
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

/-! ## The glue and the top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

set_option maxHeartbeats 4000000 in
/-- **`PmFhK` from `PmGdV`** (module docstring): the glue at a `StartPmK` view start. -/
theorem pmFhK_of_gd (B : PmObl7 st Cs Ω Sg Ac Locks) (hGd : PmGdV st ar Cs Ω Sg Ac Locks) :
    PmFhK st ar hA (arI := arI) (AR := AR) (MR := MR) B := by
  intro Ch s K hK hU c k ρ j hC hE hsf hM hV
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  obtain ⟨σ, a, hCh, hQ, hEx, hc, hl, hμ, e⟩ := hsf
  subst e
  have hJ : SlJAt (L := L) K.toKLayout σ := ChainOf.bun hC' σ hCh
  have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = CoreView.view K.toKLayout c ρ x := hμ
  have hqu : QU st K σ :=
    qU_startN st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
  have hPre : PmPreG st Cs Ω Sg Ac Locks j.2 K (CoreView.view K.toKLayout c ρ) σ :=
    ⟨⟨hJ, hQ, gateEp_viewStart hJ hE hμ⟩, hEx, pmRoot_of_qf hQ⟩
  subst hc
  unfold annV
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  exact pm_annA ar hA hK hU hV (j := j) (a := a) B.cs B.lk hGd hPre hqu rfl hl hmm

end top

end
end Fl4Proofs.P2.E2EP

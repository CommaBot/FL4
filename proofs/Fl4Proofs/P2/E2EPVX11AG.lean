/-
# P2 (line mmuAD, gen 15): **CNodeDelete and delPte in VM epochs under A/D writes** — `serializable_fl4_localVX11AG`

`E2EPVX11AF` leaves [W] `VmInsAF` (CNodeDelete and delPte in VM epochs). Both read paging words by design
(`unmap_page`'s walk and leaf), so gen 5's avoidance trick does not apply. Their entry facts `FDel`'s `VsXW` / `WalkP`
say the walk reads no `XD` word, which is false at `KU K E`. This module redoes gen 7's masked-walk proof at the VM
layout.

* **`VmPweT`** [S]: `VmPwe` plus `tabw`, which says the ASID-table words and the named pools' words of the epoch are
  `VsW` words (aligned, region `.none`, not user). Natively this is the bundle's `SlJAtZ.rdTab` (`RegionOKX.asidT`,
  `region_none_pool`). gen 7's walk lemmas need `RdTab (VsW K)` at the path's entry (`insT_blkP` / `insT_blkN`'s
  `hRTv`: the table and pool words that `find_vspace_for_asid` reads stay unchanged up to `unmap_page`), and no VM
  start fact gives it. Rust: `layout.rs` `ASID_TABLE` (kernel-global block), `objects.rs` `create_arch_object`
  (ASID pools are retyped arch objects: no typed-heap region, no user frame). `VmPweT` has the same standing as
  `VmPwe`.
* `TabKU K E s` (the paths' restriction: `TabNoE (KU K E).ptes ∧ RdTab (VsW K)`), `tabKU_wr` (kept by user writes),
  **`tabKU_start`** (at a VM start: `EpochJV`, `VmPweT`, `σ`'s kernel base), `rdTab_kuT`.
* CNodeDelete: `invRV` (VX8's `invSlotVX` path restricted to `TabKU`), **`accIns_invRV`** (`accIns_invR` with VX8's
  `InvLX` facts — `invSeenRNX`, `invVsJX_of`, `invCdtJX_of`, `hzX_of`, `InvLX.buf8`, `FDel`'s `VsXW` as the walk
  fact with `Xp := XD K` — in place of P3's bundle), **`inv_decV`** (declined runs, `exOK_VP`), **`insAW_inv`**.
* delPte: `delRV`, **`accIns_delRV`** (`accIns_delR` at VX10's `PrePX`: `invSeenR_ofZ`, `delEntP_of` at `InvLX`,
  `WalkP.vsX` / `WalkP.lf`), **`delPte_decV`**, **`insAW_del`**.
* **`ExecVX4d`** (`ExecVX4c` with `VmPweT`), `execVX4d_aRunR`, `serializable_VX4d_of`, and
  **`serializable_fl4_localVX11AG`**: VX11's premises over `ExecVX4d`, [P] `MmuAD`, **no [W]**.

Named premises of `serializable_fl4_localVX11AG` beyond VX11's and [P] `MmuAD`: [S] `VmPweT` at VM serial exits (in
`ExecVX4d`'s step). No [W]. No existing statement changed (new file; root import list extended).
-/
import Fl4Proofs.P2.E2EPVX11AF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath InsT insT_of_within)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg HwWr allowed_of_sinv
  InsA ARunR aRunR_inv serializable_safeR)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv adEq_trans adOr_adEq)

noncomputable section
open Classical

/-! ## 1. The table half of the VM layout fact, and the restriction `TabKU` -/

section tab
variable {K : KLayoutP} {E : U64 → U64}

/-- **[S] The VM layout fact with the ASID words' placement** (module docstring): `VmPwe` and the ASID-table words
and the named pools' words of the epoch are `VsW` words (aligned, region `.none`, not user).

Justification of `tabw` (accepted by the line's coordinator, gen 15 review): the ASID table sits in the kernel-global
block (fl4-core `layout.rs` `ASID_TABLE = NODES + MAX_NODES * node::SIZE`: aligned, no typed-heap object there, not a
user frame), and ASID pools are retyped arch objects (`arch/x86_64/objects.rs` `create_arch_object`: an `ASIDPool` is
untyped-retyped memory, never a TCB, CNode slot, notification, endpoint, reply, SC or user frame, so its words are
region `.none` and kernel words). Natively it is P3's bundle `SlJAtZ.rdTab` (`RegionOKX.asidT`, `region_none_pool`,
P2/E2EPJEp2.lean, from the spec arch objects `VsRel.pool` / `SpecCover.arch`). In VM epochs it has the status of
`VmPwe` and vmscope's other [S] layout facts (`VtxBundle4`), pending the VT-x refinement. -/
structure VmPweT (K : KLayoutP) (E : U64 → U64) : Prop extends VmPwe K E where
  /-- [S] The ASID-table and pool words of the epoch are `VsW` words (natively `SlJAtZ.rdTab`). -/
  tabw : ∀ hi : U64, hi.val < 2048 → VsW K.toKLayout (atAF K.ksb hi) ∧
    ∀ lo : U64, lo.val < 512 → E (atAF K.ksb hi) ≠ 0#u64 → VsW K.toKLayout (peAF (E (atAF K.ksb hi)) lo)

variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The restriction of the two masked-walk slots**: the ASID words read now are off the epoch's paging words and
are `VsW` words. -/
def TabKU (K : KLayoutP) (E : U64 → U64) (s : S) : Prop :=
  TabNoE (L := L) (· ∈ (KU K E).ptes) s ∧ RdTab (L := L) (VsW K.toKLayout) s

/-- `TabKU` is kept by an aligned user write. -/
theorem tabKU_wr {s : S} {b v : U64} (h : TabKU (L := L) K E s) (hb : b ∈ K.user) (ha : Aligned b) :
    TabKU (L := L) K E (L.wr s b v) := by
  have hk : L.ksb (L.wr s b v) = L.ksb s := L.ksb_wr s b v
  have ht : ∀ hi : U64, hi.val < 2048 →
      L.mem (L.wr s b v) (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) := fun hi hhi =>
    Fl4Proofs.P3.Notif.rd_wr_ne ha (h.2 hi hhi).1.1 (fun e => (h.2 hi hhi).1.2.2 (e ▸ hb))
  refine ⟨fun hi hhi => ?_, fun hi hhi => ?_⟩
  · rw [hk, ht hi hhi]; exact h.1 hi hhi
  · rw [hk, ht hi hhi]; exact h.2 hi hhi

/-- **`TabKU` at a start state of a VM epoch** (`EpochJV`, `VmPweT`). -/
theorem tabKU_start {s : Cfg U64 U64 U64 U64} {σ : S} (J : EpochJV K E s) (hP : VmPweT K E)
    (hk : L.ksb σ = K.ksb) (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = s.mem x) :
    TabKU (L := L) K E σ := by
  have hm : ∀ hi : U64, hi.val < 2048 → L.mem σ (atAF K.ksb hi) = E (atAF K.ksb hi) := by
    intro hi hhi
    rw [hμ _ (hP.tabw hi hhi).1.1 (hP.tabw hi hhi).1.2.2]
    exact J.eq _ (hP.tab hi hhi) (fun hp => pwe_asid J.conv (Or.inl ⟨hi, hhi, rfl⟩) hp)
  refine ⟨fun hi hhi => ?_, fun hi hhi => ?_⟩
  · rw [hk]
    refine ⟨fun hb => pwe_asid J.conv (Or.inl ⟨hi, hhi, rfl⟩) hb.1, fun lo hlo hne hb => ?_⟩
    rw [hm hi hhi] at hne hb
    exact pwe_asid J.conv (Or.inr ⟨hi, hhi, hne, lo, hlo, rfl⟩) hb.1
  · rw [hk]
    refine ⟨(hP.tabw hi hhi).1, fun lo hlo hne => ?_⟩
    rw [hm hi hhi] at hne ⊢
    exact (hP.tabw hi hhi).2 lo hlo hne

/-- `rdTab_ku` from `TabKU`. -/
theorem rdTab_kuT {s : S} (h : TabKU (L := L) K E s) :
    RdTab (L := L) (fun q => VsW K.toKLayout q ∧ q ∉ (KU K E).ptes) s := fun hi hhi =>
  ⟨⟨(h.2 hi hhi).1, (h.1 hi hhi).1⟩, fun lo hlo h0 => ⟨(h.2 hi hhi).2 lo hlo h0, (h.1 hi hhi).2 lo hlo h0⟩⟩

end tab

/-! ## 2. CNodeDelete in VM epochs -/

section inv
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- VX8's CNodeDelete path restricted to `TabKU` states. -/
noncomputable abbrev invRV (j : InvArg S) (K : KLayoutP) (E m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : InvPremX st j K) :
    LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (invAvPX st ar hA hm j K m hK hU h)).restrQ
    (fun σ => TabKU (L := L) K E σ) (fun _ _ _ _ h hb ha => tabKU_wr h hb ha)

set_option maxHeartbeats 4000000 in
/-- **CNodeDelete's accepted runs in a VM epoch are `InsT` at the epoch's paging words** (`accIns_invR` with VX8's
`InvLX` facts in place of P3's bundle, `TabKU` in place of `QPs (KU K E)` and the bundle's `rdTab`). -/
theorem accIns_invRV (j : InvArg S) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (h : InvPremX st j K) : AccIns (invRV st ar hA hm j K E m hK hU h) (PWE K E) := by
  intro (s : S) (a : A) (r : Bool × S × A) hs hr hacc
  have hs' := hs
  obtain ⟨hE0, hT0⟩ := hs
  have hE : (InvLX st (FDel st j K m) K.toKLayout s ∧
      InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) ∧ QPs K st s := hE0
  have hT : TabKU (L := L) K E s := hT0
  have hks := hE.2.ks
  have PE := hE.1.2.1.1.1
  have hr0 : syscall.handle_invocation_local st ar s a j.number j.p = ok r := hr
  have h0 : syscall.handle_invocation_local st ar s a j.number j.p = ok (true, r.2.1, r.2.2) := by
    obtain ⟨b, s1, a1⟩ := r
    have hb : b = true := hacc
    subst hb
    exact hr0
  by_cases hL : InvLen st s
  · letI := (invRV st ar hA hm j K E m hK hU h).L
    have hr' : interp st ar (R.invBodyG j.number j.p) s a = ok r :=
      ((invRV st ar hA hm j K E m hK hU h).isProg _ (Narrow.self st) s (AltOf.pre hs') a).symm.trans hr
    show InsT st ar (PWE K E) ADEq NotPresent (· ∈ K.user) (R.invBodyG j.number j.p) s a
    refine insT_entR hA (P := fun s => ((InvLX st (FDel st j K m) K.toKLayout s ∧
        InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) ∧ QPs K st s) ∧ TabKU (L := L) K E s ∧
        InvLen st s) (Locks := j.Locks) (fun s h => h.1.1.2.1.1.1)
      (fun s h q hq => hq.elim (ioRSR_notPWE hK h.1.2.ks) (ioWS_notPWE hK))
      (fun s h => invSeenRNX h.1.1.1 h.1.1.2) (fun s h => invPsRN h.1.1.2) ?_ s a r ⟨hE, hT, hL⟩
      ⟨_, _, h0⟩ hr'
    intro s a info nx s1 s2 a1 buf length cap r' hs _ emi C ebuf ecap hl hR
    obtain ⟨⟨⟨hJ, hq⟩, hqK⟩, hTs, hLs⟩ := hs
    have PE := hq.1.1.1
    have hks := hqK.ks
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_core hq
    have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
    have hlen : ¬ length < 2#u64 := len_ge2 (hLs (L.curW s) info (cur_thread_ok s) emi) hl
    have hvsP := invVsJX_of (st := st)
      (P := fun s => InvLX st (FDel st j K m) K.toKLayout s ∧
        InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) (fun _ h => h.1)
    have Ed := delEnt_of
      (P := fun s => InvLX st (FDel st j K m) K.toKLayout s ∧
        InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s)
      ⟨hJ, hq⟩ hq hvsP (invCdtJX_of (fun _ h => h.1)) (hzX_of _ s hJ)
    exact insT_blkN hA (fun q h => ioRSR_notPWE hK hks h) (fun q h => ioWS_notPWE hK h)
      (fun q h => rf_notPWE h) (rdTab_kuT hTs) hTs.2 PE Ed hsK hlen hJ.here.2.1.2
      (fun sl fp rt asid va hsl hc' hA' => hvsP s sl fp rt asid va ⟨hJ, hq⟩ hsl hc' hA') C ecap hlbl hR
  · haveI : GRd (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) st (IoRSR st K.toKLayout j.Locks s) :=
      grd_sub (fun _ h => ioRSR_notPWE hK hks h)
    have hW : IoWr st (fun b => ¬ PWE K E b) K.heap.scBits s :=
      (PE.ioWr (Locks := j.Locks)).mono (fun _ h => ioWS_notPWE hK h)
    have hg := inv_acc_genR (W := fun b => ¬ PWE K E b)
      (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE hW (invSeenRNX hE.1.1 hE.1.2)
      (invPsRN hE.1.2) (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => ?_) h0
    · have hg' : (invRV st ar hA hm j K E m hK hU h).F (invRV st ar hA hm j K E m hK hU h).ar
          (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) s a = ok r := by
        obtain ⟨b, s1, a1⟩ := r
        have hb : b = true := hacc
        subst hb
        exact hg
      exact insT_guardRun _ (fun _ h => h) (fun _ h => h) hs' hg'
    have hq := hE.1.2
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_core hq
    have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
    rw [hlbl] at hy ⊢
    have hlen : length < 2#u64 := trunc_len (len_lt2 hL emi) hl
    clear this
    obtain ⟨hdec, hrep⟩ := truncAccR (R := fun b => ¬ PWE K E b) (Locks := j.Locks)
      (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE
      (fun _ h => ioRSR_notPWE hK hks h) (fun _ h hp => pwe_user hU hp h.2) hW
      (fun _ h hp => pwe_user hU hp h.2) hcs hsK (InvLX.buf8 hE.1.1) hc hk hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) st (IoRSR st K.toKLayout j.Locks s) :=
      grd_sub (fun _ h => ioRSR_notPWE hK hks h)
    obtain ⟨h1, h2⟩ := truncFinR (Locks := j.Locks)
      (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE hW
      (SWr.of_W (ioWS_notPWE hK (PE.stw (Locks := j.Locks)).2)) hcs hsK (InvLX.buf8 hE.1.1) hc hk hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- **CNodeDelete's declined runs in a VM epoch touch no paging word** (`inv_dec` with `exOK_VP`). -/
theorem inv_decV (j : InvArg S) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (h : InvPremX st j K) :
    let P := LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (invAvPX st ar hA hm j K m hK hU h)
    ∀ s s' a r, P.Pre s → P.F P.ar P.st s a = ok r → ¬ P.Acc r.1 →
      @Alt _ P.st P.L (P.RS s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s s' →
      Within P.st P.ar (fun b => ¬ PWE K E b) (fun b => b ∈ K.user ∨ ¬ PWE K E b) P.p s' a := by
  intro P
  refine LocalPath.decG P (R0 := fun s => IoRSR st K.toKLayout j.Locks s) ?_ ?_ ?_
  · intro s s' a r r' hs0 hr hn Al hr'
    have hs : (InvLX st (FDel st j K m) K.toKLayout s ∧
        InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) ∧ QPs K st s := hs0
    have E0 := exOK_VP hK hU hs.1.1.here.2.2 (ksfit_of_ioPre st hs.1.2.1.1.1) hs.2.ks
    have Al' : Alt st (rsE (· ∈ K.ptes) (rsV K.toKLayoutV (InvCMRS (st := st) K.toKLayout j.Locks)) s)
        (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s s' := Al
    have AlR := Al'.anti (R' := IoRSR st K.toKLayout j.Locks s)
      (fun x hx => ⟨⟨(ioRSR_rsEX E0 hx).1, fun hv => (ioRSR_rsEX E0 hx).2 (Or.inl hv)⟩,
        fun hp => (ioRSR_rsEX E0 hx).2 (Or.inr hp)⟩)
    have hr0 : r.1 ≠ true := hn
    exact inv_dec_guardRSR hA hs.1.2.1.1.1 (invSeenRNX hs.1.1 hs.1.2) AlR hr hr0 hr'
  · intro s x hs0 hx
    have hs : (InvLX st (FDel st j K m) K.toKLayout s ∧
        InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) ∧ QPs K st s := hs0
    exact ioRSR_notPWE hK hs.2.ks hx
  · intro s x hs0 hx
    have hs : (InvLX st (FDel st j K m) K.toKLayout s ∧
        InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) ∧ QPs K st s := hs0
    exact ioDS_notPWE hK hs.2.ks hs.1.2.1.1.1 hx

/-- One VM-epoch slot family's share of `hIns` given the [S] `VmPweT`. -/
def InsAWT {ιv : Type} (LPv : PathsP ιv) : Prop :=
  ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : ιv), K.vcpus ≠ ∅ → VtxBundle4 st L K → VmPweT K E → EpochJV K E s →
    MapsP K s → StartAt (LPv j K s.mem hK hU) c hs s.mem q →
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q

set_option maxHeartbeats 2000000 in
/-- **CNodeDelete in VM epochs.** -/
theorem insAW_inv : InsAWT st (invSlotVX st ar hA hm) := by
  intro K E s hK hU c hs q j _ _ hP J hM h
  by_cases hp : InvPremX st j K
  · rw [invSlotVX_pos st ar hA hm hp] at h
    obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := h
    have hpre' : (InvLX st (FDel st j K s.mem) K.toKLayout σ ∧
        InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout s.mem σ) ∧ QPs K st σ := hpre
    have hT : TabKU (L := L) K E σ := tabKU_start J hP hpre'.2.ksb hμ
    have h' : StartAt (invRV st ar hA hm j K E s.mem hK hU hp) c hs s.mem
        ((LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
          (invAvPX st ar hA hm j K s.mem hK hU hp)).body σ a) :=
      ⟨σ, a, ⟨hpre, hT⟩, hc, hl, hμ, rfl⟩
    rw [hM.own, hM.cls, hM.ko]
    exact LocalPath.insAQ _ adEq_equiv (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) (fun x hx => pwe_ko hK _ hx)
      (fun x hx => pwe_user hU hx) (accIns_invRV st ar hA hm j (E := E) (m := s.mem) hK hU hp)
      (fun s1 s2 a r hs1 hr hn Al => inv_decV st ar hA hm j (E := E) (m := s.mem) hK hU hp s1 s2 a r hs1.1 hr hn Al) h'
  · unfold invSlotVX at h
    rw [dif_neg hp] at h
    obtain ⟨σ, a, hpre, -⟩ := h
    exact (hpre : False).elim

end inv

/-! ## 3. delPte in VM epochs -/

section del
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- VX10's delPte path restricted to `TabKU` states. -/
noncomputable abbrev delRV (j : InvArg S) (K : KLayoutP) (E m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : DelPtePremX st j K) :
    LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  (delPtePathX st ar hA hm j K m hK hU h).restrQ (fun σ => TabKU (L := L) K E σ)
    (fun _ _ _ _ h hb ha => tabKU_wr h hb ha)

set_option maxHeartbeats 4000000 in
/-- **delPte's accepted runs in a VM epoch are `InsT` at the epoch's paging words** (`accIns_delR` with VX10's
`PrePX`: `InvLX`, `WalkP`, `KsNoE`, `InvVF` in place of `SlJAt` / `CvP`, `TabKU` for the ASID words). -/
theorem accIns_delRV (j : InvArg S) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (h : DelPtePremX st j K) : AccIns (delRV st ar hA hm j K E m hK hU h) (PWE K E) := by
  intro (s : S) (a : A) (r : Bool × S × A) hs hr hacc
  have hs' := hs
  obtain ⟨hE0, hT0⟩ := hs
  have hE : PrePX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hE0
  have hT : TabKU (L := L) K E s := hT0
  have hks := hE.2.2.2.1
  have PE := hE.2.1.1.1.1
  have hr0 : syscall.handle_invocation_local st ar s a j.number j.p = ok r := hr
  have h0 : syscall.handle_invocation_local st ar s a j.number j.p = ok (true, r.2.1, r.2.2) := by
    obtain ⟨b, s1, a1⟩ := r
    have hb : b = true := hacc
    subst hb
    exact hr0
  by_cases hL : InvLen st s
  · letI := (delRV st ar hA hm j K E m hK hU h).L
    have hr' : interp st ar (R.invBodyG j.number j.p) s a = ok r :=
      ((delRV st ar hA hm j K E m hK hU h).isProg _ (Narrow.self st) s (AltOf.pre hs') a).symm.trans hr
    show InsT st ar (PWE K E) ADEq NotPresent (· ∈ K.user) (R.invBodyG j.number j.p) s a
    refine insT_entR hA (P := fun s => (PrePX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s ∧ TabKU (L := L) K E s) ∧
        InvLen st s) (Locks := j.Locks) (fun s h => h.1.1.2.1.1.1.1)
      (fun s h q hq => hq.elim (ioRSR_notPWE hK h.1.1.2.2.2.1) (ioWS_notPWE hK))
      (fun s h => invSeenR_ofZ h.1.1.1.hz h.1.1.2.1) (fun s h => invPsR_of h.1.1.2.1) ?_ s a r ⟨⟨hE, hT⟩, hL⟩
      ⟨_, _, h0⟩ hr'
    intro s a info nx s1 s2 a1 buf length cap r' hs _ emi C ebuf ecap hl hR
    obtain ⟨⟨⟨hJ, hq, hWk, hks, -⟩, hTs⟩, hLs⟩ := hs
    have PE := hq.1.1.1
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hq
    have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
    have hlen : ¬ length < 2#u64 := len_ge2 (hLs (L.curW s) info (cur_thread_ok s) emi) hl
    have Ed := delEntP_of (P := fun s => InvLX st (fun _ => True) K.toKLayout s) hJ hq
      (invCdtJX_of (fun _ h => h)) (hzX_of _ s hJ)
    have hvs := invVsJX_of (st := st) (P := fun s => InvLX st (fun _ => True) K.toKLayout s) (fun _ h => h)
    exact insT_blkP hA (fun q h => ioRSR_notPWE hK hks h) (fun q h => ioWS_notPWE hK h)
      (fun q h => rf_notPWE h) (rdTab_kuT hTs) hTs.2 PE Ed hsK hlen (WalkP.vsX hJ.here.1 hWk)
      (fun sl fp rt asid va hsl hc' hA' => hvs s sl fp rt asid va hJ hsl hc' hA')
      (fun asid va e he => (WalkP.lf hWk asid va e he).2) C ecap hlbl hR
  · haveI : GRd (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) st (IoRSR st K.toKLayout j.Locks s) :=
      grd_sub (fun _ h => ioRSR_notPWE hK hks h)
    have hW : IoWr st (fun b => ¬ PWE K E b) K.heap.scBits s :=
      (PE.ioWr (Locks := j.Locks)).mono (fun _ h => ioWS_notPWE hK h)
    have hg := inv_acc_genR (W := fun b => ¬ PWE K E b)
      (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE hW (invSeenR_ofZ hE.1.hz hE.2.1)
      (invPsR_of hE.2.1) (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => ?_) h0
    · have hg' : (delRV st ar hA hm j K E m hK hU h).F (delRV st ar hA hm j K E m hK hU h).ar
          (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) s a = ok r := by
        obtain ⟨b, s1, a1⟩ := r
        have hb : b = true := hacc
        subst hb
        exact hg
      exact insT_guardRun _ (fun _ h => h) (fun _ h => h) hs' hg'
    have hq := hE.2.1
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hq
    have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
    rw [hlbl] at hy ⊢
    have hlen : length < 2#u64 := trunc_len (len_lt2 hL emi) hl
    clear this
    obtain ⟨hdec, hrep⟩ := truncAccR (R := fun b => ¬ PWE K E b) (Locks := j.Locks)
      (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE
      (fun _ h => ioRSR_notPWE hK hks h) (fun _ h hp => pwe_user hU hp h.2) hW
      (fun _ h hp => pwe_user hU hp h.2) hcs hsK (InvLX.buf8 hE.1) hc hk hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) st (IoRSR st K.toKLayout j.Locks s) :=
      grd_sub (fun _ h => ioRSR_notPWE hK hks h)
    obtain ⟨h1, h2⟩ := truncFinR (Locks := j.Locks)
      (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE hW
      (SWr.of_W (ioWS_notPWE hK (PE.stw (Locks := j.Locks)).2)) hcs hsK (InvLX.buf8 hE.1) hc hk hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- **delPte's declined runs in a VM epoch touch no paging word** (`delPte_dec` at `PrePX`). -/
theorem delPte_decV (j : InvArg S) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (h : DelPtePremX st j K) :
    ∀ s s' a r, (delPtePathX st ar hA hm j K m hK hU h).Pre s →
      (delPtePathX st ar hA hm j K m hK hU h).F (delPtePathX st ar hA hm j K m hK hU h).ar
        (delPtePathX st ar hA hm j K m hK hU h).st s a = ok r →
      ¬ (delPtePathX st ar hA hm j K m hK hU h).Acc r.1 →
      @Alt _ (delPtePathX st ar hA hm j K m hK hU h).st (delPtePathX st ar hA hm j K m hK hU h).L
        ((delPtePathX st ar hA hm j K m hK hU h).RS s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' →
      Within (delPtePathX st ar hA hm j K m hK hU h).st (delPtePathX st ar hA hm j K m hK hU h).ar
        (fun b => ¬ PWE K E b) (fun b => b ∈ K.user ∨ ¬ PWE K E b)
        (delPtePathX st ar hA hm j K m hK hU h).p s' a := by
  refine LocalPath.decG _ (R0 := fun s => IoRSR st K.toKLayout j.Locks s) ?_ ?_ ?_
  · intro s s' a r r' hE hr hn Al hr'
    have hE' : PrePX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hE
    have E0 := exOK_VP hK hU hE'.2.2.2.2 (ksfit_of_ioPre st hE'.2.1.1.1.1) hE'.2.2.2.1
    have Al' : Alt st (InvRSV st K j.Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' := Al
    have hr0 : r.1 ≠ true := hn
    exact inv_dec_guardRSR hA hE'.2.1.1.1.1 (invSeenR_ofZ hE'.1.hz hE'.2.1)
      (Al'.anti (R' := IoRSR st K.toKLayout j.Locks s) (fun x hx =>
        ⟨ioRSP_inv (ioRSR_P hK hE'.2.2.2.1 hx), fun hv => (ioRSR_rsEX E0 hx).2 (Or.inl hv)⟩)) hr hr0 hr'
  · intro s x hE hx
    have hE' : PrePX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hE
    exact ioRSR_notPWE hK hE'.2.2.2.1 hx
  · intro s x hE hx
    have hE' : PrePX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hE
    exact ioDS_notPWE hK hE'.2.2.2.1 hE'.2.1.1.1.1 hx

/-- **delPte in VM epochs.** -/
theorem insAW_del : InsAWT st (delPteSlotVX st ar hA hm) := by
  intro K E s hK hU c hs q j _ _ hP J hM h
  by_cases hp : DelPtePremX st j K
  · rw [delPteSlotVX_pos st ar hA hm hp] at h
    obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := h
    have hpre' : PrePX st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K s.mem σ := hpre
    have hT : TabKU (L := L) K E σ := tabKU_start J hP hpre'.2.1.1.1.1.kb.symm hμ
    have h' : StartAt (delRV st ar hA hm j K E s.mem hK hU hp) c hs s.mem
        ((delPtePathX st ar hA hm j K s.mem hK hU hp).body σ a) :=
      ⟨σ, a, ⟨hpre, hT⟩, hc, hl, hμ, rfl⟩
    rw [hM.own, hM.cls, hM.ko]
    exact LocalPath.insAQ _ adEq_equiv (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) (fun x hx => pwe_ko hK _ hx)
      (fun x hx => pwe_user hU hx) (accIns_delRV st ar hA hm j hK hU hp)
      (fun s1 s2 a r hs1 hr hn Al => delPte_decV st ar hA hm j hK hU hp s1 s2 a r hs1.1 hr hn Al) h'
  · unfold delPteSlotVX at h
    rw [dif_neg hp] at h
    obtain ⟨σ, a, hpre, -⟩ := h
    exact (hpre : False).elim

end del

/-! ## 4. `ExecVX4d`: VM serial exits give `VmPweT` -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **`ExecVX4c` whose VM serial exits give the [S] layout fact `VmPweT`** of the new epoch. -/
inductive ExecVX4d (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → (U64 → U64) → Prop
  | refl : ExecVX4d LP SF P s0 K0 Ch0 s0 K0 Ch0 s0.mem
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} {E : U64 → U64} :
      ExecVX4d LP SF P s0 K0 Ch0 s K Ch E → Step s c s' → Fl4StepVX4 LP SF P s K Ch c s' K' Ch' →
      /- [S] the VM layout fact at a VM serial exit -/
      (SerStep s c → K'.vcpus ≠ ∅ → VmPweT K' s'.mem) →
      ExecVX4d LP SF P s0 K0 Ch0 s' K' Ch' (if SerStep s c then s'.mem else E)
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {v a x : U64} :
      ExecVX4d LP SF P s0 K0 Ch0 s K Ch E → HwStepP K s v a x → ExecVX4d LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E
  | mmu {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {a x : U64} :
      ExecVX4d LP SF P s0 K0 Ch0 s K Ch E → MmuAD (PWE K E) s.mem a x →
      ExecVX4d LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E

/-- **`ExecVX4d` on the re-based platform** (gen 55): the same constructors over `Fl4StepVX4C`. -/
inductive ExecVX4dC (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlatC st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → (U64 → U64) → Prop
  | refl : ExecVX4dC LP SF P s0 K0 Ch0 s0 K0 Ch0 s0.mem
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} {E : U64 → U64} :
      ExecVX4dC LP SF P s0 K0 Ch0 s K Ch E → Step s c s' → Fl4StepVX4C LP SF P s K Ch c s' K' Ch' →
      /- [S] the VM layout fact at a VM serial exit -/
      (SerStep s c → K'.vcpus ≠ ∅ → VmPweT K' s'.mem) →
      ExecVX4dC LP SF P s0 K0 Ch0 s' K' Ch' (if SerStep s c then s'.mem else E)
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {v a x : U64} :
      ExecVX4dC LP SF P s0 K0 Ch0 s K Ch E → HwStepP K s v a x → ExecVX4dC LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E
  | mmu {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {E : U64 → U64} {a x : U64} :
      ExecVX4dC LP SF P s0 K0 Ch0 s K Ch E → MmuAD (PWE K E) s.mem a x →
      ExecVX4dC LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch E

/-- An `ExecVX4d` run is an `ExecVX4dC` run at `P.toC`. -/
theorem ExecVX4d.toC {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64}
    (h : ExecVX4d LP SF P s0 K0 Ch0 s K Ch E) : ExecVX4dC LP SF P.toC s0 K0 Ch0 s K Ch E := by
  induction h with
  | refl => exact .refl
  | step _ hS g hPw ih => exact .step ih hS g.toC hPw
  | hw _ hH ih => exact .hw ih hH
  | mmu _ hH ih => exact .mmu ih hH

/-- **An `ExecVX4d` execution is an `ARunR` one at the epoch's paging words**; `hIns` also receives `VmPweT` in VM
epochs (`execVX4c_aRunR`'s proof). -/
theorem execVX4d_aRunR {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (P : LocPlat st arI AR MR)
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (Ch : S → Prop) (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
      (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : ι),
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      (K.vcpus ≠ ∅ → VmPweT K E) → EpochJV K E s →
      MapsP K s → SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecVX4d LP SF P s0 K0 Ch0 s K Ch E) :
    ARunR ADEq NotPresent s0 s (PWE K E) ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s ∧
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) ∧ (K.vcpus ≠ ∅ → VtxBundle4 st L K) ∧
      (K.vcpus ≠ ∅ → VmPweT K E) ∧ EpochJV K E s := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨.refl _, hK0, hU0, hM0, fun _ => hB, fun hn => (hn hc0.1).elim, fun hn => (hn hc0.1).elim,
      epochJV_ser hc0.2⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g hPw ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, hW, J⟩ := ih
    obtain ⟨⟨H, I⟩, -, hSI, -⟩ := aRunR_inv adEq_equiv h0 hA0 hR
    have hN : K1.vcpus = ∅ → NatEp P K1 Ch1 s1 := fun nv => ⟨hX nv, epoch_start (J.toJ nv)⟩
    have hst : ∀ p0 k W, s1.ph c1 = .loc p0 (.start k) W →
        ∃ i, SF Ch1 K1 s1.mem hK hU c1 (fun l => s1.lk l = some c1) k i ∧
          StartAt (LP i K1 s1.mem hK hU) c1 (fun l => s1.lk l = some c1) s1.mem k := by
      intro p0 k W hph
      obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
      exact ⟨i, hi, hSF _ _ s1 _ _ _ _ _ i hN hV hi⟩
    have hok : Fl4Proofs.P2.Serial.SafeStep s1 c1 s1' := by
      refine ⟨g.arm, fun p0 k W hph => ?_⟩
      obtain ⟨i, -, hP⟩ := hst p0 k W hph
      rw [hM.own, hM.cls, hM.ko]
      exact (LP i K1 s1.mem hK hU).safe (moveHeldP hK) (ownDepP hK hU) hP
    by_cases hs : SerStep s1 c1
    · rw [if_pos hs]
      have hnl := I.inv.clo hs.1
      have hR' := ARunR.regate (PWE K1' s1'.mem) hR hs.1
      have hst' : ARunR ADEq NotPresent s0 s1' (PWE K1' s1'.mem) :=
        .step hR' hS hok (fun p0 k W hph => absurd (by rw [hph]; trivial) (hnl c1))
      rcases g.ser hs with ⟨hXs, nv, hc⟩ | ⟨hne, hc, hb⟩
      · have hK' := okP_R hXs ⟨nv, hc⟩
        exact ⟨hst', hK'.1, hK'.2, g.serG hs, fun _ => hXs, fun hn => (hn nv).elim, fun hn => (hn nv).elim,
          epochJV_ser hc⟩
      · have hK' := hb.b.okP hc
        exact ⟨hst', hK'.1, hK'.2, g.serG hs, fun nv => (hne nv).elim, fun _ => hb, hPw hs,
          epochJV_ser hc⟩
    · rw [if_neg hs]
      obtain ⟨eK, eC⟩ := g.keep hs
      subst eK eC
      have hal := allowed_of_sinv hSI c1
      refine ⟨.step hR hS hok (fun p0 k W hph => ?_), hK, hU, maps_stepP hK hM hal hS hs, hX, hV, hW,
        epochJV_keep J (fun x hx => step_gate_keep hM hal hS hs hx)⟩
      obtain ⟨i, hi, hP⟩ := hst p0 k W hph
      exact hIns _ _ _ _ hK hU _ _ _ i hX hV hW J hM hi hP
  | hw _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, hW, J⟩ := ih
    exact ⟨.hw hR (hH.hwWr hK hM), hK, hU, maps_hwP hK hM hH, hX, hV, hW,
      epochJV_keep J (fun x hx => hw_gate_keep hK hM hH hx)⟩
  | mmu _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, hV, hW, J⟩ := ih
    exact ⟨.ad hR (adWr_pwe hK hM hH), hK, hU, maps_pwe hK hM hH, hX, hV, hW, epochJV_mmu J hH⟩

/-- **Every quiescent `ExecVX4d` state is serial**, given `hSF` and `hIns`. -/
theorem serializable_VX4d_of {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (P : LocPlat st arI AR MR)
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (K.vcpus = ∅ → NatEp P K Ch s) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (Ch : S → Prop) (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
      (hU : UserOKP K) (c : U64) (hs : U64 → Prop) (q : SP) (i : ι),
      (K.vcpus = ∅ → SerExitW P K.toKLayoutV Ch) → (K.vcpus ≠ ∅ → VtxBundle4 st L K) →
      (K.vcpus ≠ ∅ → VmPweT K E) → EpochJV K E s →
      MapsP K s → SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecVX4d LP SF P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_safeR adEq_equiv h0 hA0 (execVX4d_aRunR P hSF hIns h0 hA0 hB hc0 hM0 h).1 hq

end exec

/-! ## 5. The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end with every U1 slot in native and VM epochs and the host walker's A/D writes** (module
docstring): VX11's premises (`P`, [P] `hIoa`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, the execution, `hq`) over `ExecVX4d`
(so [S] `VmPweT` at VM serial exits) and [P] `MmuAD` (its `mmu` step). No [W]. -/
theorem serializable_fl4_localVX11AG (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX4d (famVX11 st ar hA hm hSt a0) (StartVX11U st ar hA hm hSt a0 (arI := arI) (AR := AR) (MR := MR))
      P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_VX4d_of P (vx11_startAt st ar hA hm hSt a0 P hIoa) ?_ h0 hA0 hB hc0 hM0 h hq
  intro Ch K E s hK hU c hs q i hX hV hW J hM hsf hP
  rcases i with ((((((((((i | j) | j) | j) | j) | j) | j) | j) | j) | j) | j) | j
  · have hsf' : K.vcpus = ∅ ∧ StartU1 st ar hA hm hSt a0 arI AR MR (StartInvU2 st ar hA hm) Ch K s.mem hK hU c hs
        q i := hsf
    have nv := hsf'.1
    have J' := J.toJ nv
    have hb : ∃ σe, SlJAt (L := L) K.toKLayout σe := by
      obtain ⟨σe, hC'⟩ := (hX nv).chainOf
      have hσe : Ch σe := by
        obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
        exact h'
      exact ⟨σe, ChainOf.bun hC' σe hσe⟩
    rcases i with i | ((j | j) | j)
    · exact insA_w11 st ar hA hm hSt a0 i (hK := hK) (hU := hU) hb J' hM hP
    · exact insA_delR st ar hA hm j (hK := hK) (hU := hU) hb J' hM hP
    · exact insA_invR st ar hA hm j (hK := hK) (hU := hU) hb J' hM hP
    · exact insA_cm st ar hA hm j (hK := hK) (hU := hU) hb J' hM hP
  · have hsf' : VxStartV2 st ar hA hm K s.mem hK hU c hs q j := hsf
    have hne := vxStartV2_ne hsf'
    exact insAW_vx st ar hA hm K E s hK hU c hs q j hne (hV hne) (hW hne).toVmPwe J hM hP
  · have hsf' : VtStartV4 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_vt st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1).toVmPwe J hM hP
  · have hsf' : IoStartX5 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_io st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1).toVmPwe J hM hP
  · have hsf' : StStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_st st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1).toVmPwe J hM hP
  · have hsf' : IrqStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_irq st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1).toVmPwe J hM hP
  · have hsf' : SlStartX st ar hA hm hSt a0 K s.mem hK hU c hs q j := hsf
    exact insAW_sl st ar hA hm hSt a0 K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1).toVmPwe J hM hP
  · have hsf' : InvStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_inv st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP
  · have hsf' : CMStartX9 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_cm st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1).toVmPwe J hM hP
  · have hsf' : DelPteStartX st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_del st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1) J hM hP
  · have hsf' : VmFStartY st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_vmF st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1).toVmPwe J hM hP
  · have hsf' : VmRStartY st ar hA hm K s.mem hK hU c hs q j := hsf
    exact insAW_vmR st ar hA hm K E s hK hU c hs q j hsf'.1 (hV hsf'.1) (hW hsf'.1).toVmPwe J hM hP

end top

end
end Fl4Proofs.P2.E2EP

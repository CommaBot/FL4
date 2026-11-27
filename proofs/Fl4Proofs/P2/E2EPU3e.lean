/-
# P2 (line mmuAD, gen 6): **delPte and CNodeDelete through the masked bridge** — the U3b top reduced to the
accepted runs' walk insensitivity

`E2EPU3d.serializable_fl4_localU3b_ofDI` leaves `hIns` for the two slots whose runs read paging words by design:
delPte (`delPtePath`: the `unmap_page` walk and the held leaf, which it stores `0` into) and the no-PTE-lock
CNodeDelete (`invSlotU`: a stale-mapped frame cap's `unmap_page` walks the upper levels). Their `hNG` is false, so
`E2EAD.LocalPath.insA` does not apply; `E2EADQ.LocalPath.insAQ` (the masked bridge) does, with two obligations:

* `hDec` — runs from alternatives of **declined** entry states touch no paging word. Proved here for both slots:
  a declined run reads only `IoRSR` words (`inv_dec_guardRSR`: typed-region or kernel-block words) and writes only
  `IoDS` words (`PathObl.dec_alt`), and `IoRSR` is disjoint from `PWE K E` (**`ioRSR_notPWE`**: paging words are
  region `.none` and off the kernel block). Generic step: **`LocalPath.decG`** (any path, any word set).
* `hAcc` — **accepted** runs from entry states are `InsT` (`AccIns`): every paging-word read along the run has a
  continuation equal for every `ADEq`-variant of the value read, and the only store into a paging word stores a
  non-present value. This is the walk itself (`lookup_*_slot`, the leaf `e &&& 1`, `&&& 128`, frame masks; the leaf
  store `0`), a tree-level fact along `R.invBodyG`'s accepted run; it is left as the hypotheses `hDelA` / `hInvA`
  of the reduction theorem below (no premise of a top).

Results: `AccIns`, `LocalPath.decG`, `ioRSR_notPWE`, `pwe_ko`, `pwe_user`, **`delPte_dec`**, **`inv_dec`**,
**`insA_delQ`**, **`insA_invQ`**, **`serializable_fl4_localU3b_ofAcc`** (`serializable_fl4_localU3b_ofDI` with
`hDel` / `hInv` replaced by the accepted-run facts `hDelA` / `hInvA`).

No [W], no new [J]; the only [P] is `MmuAD` (P2/MmuADWalk.lean). `hDelA` / `hInvA` are hypotheses of a reduction
theorem. No existing statement changed.
-/
import Fl4Proofs.P2.E2EPU3d
import Fl4Proofs.P2.E2EADQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath InsT)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg HwWr allowed_of_sinv
  InsA ARunR aRunR_inv serializable_safeR)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

/-! ## 1. Generic: the two obligations of the masked bridge -/

section gen
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
  {User : U64 → Prop}

/-- **Accepted runs from entry states read `G` words only `ADEq`-insensitively** (the walk obligation). -/
def AccIns (P : LocalPath own cls ko User) (G : U64 → Prop) : Prop :=
  ∀ s a r, P.Pre s → P.F P.ar P.st s a = ok r → P.Acc r.1 → InsT P.st P.ar G ADEq NotPresent User P.p s a

/-- **Runs from alternatives of declined entry states touch no `G` word**, from a guarded declined run on a read
set `R0` off `G` and a decline write set off `G`. -/
theorem _root_.Fl4Proofs.P2.E2E.LocalPath.decG (P : LocalPath own cls ko User) {G : U64 → Prop}
    {R0 : P.S → U64 → Prop}
    (hRd : ∀ s s' a r r', P.Pre s → P.F P.ar P.st s a = ok r → ¬ P.Acc r.1 →
      @Alt P.S P.st P.L (P.RS s) cls ko User s s' → P.F P.ar P.st s' a = ok r' →
      P.F P.ar (guard P.st (R0 s) (fun _ => True)) s' a = ok r')
    (hR0 : ∀ s x, P.Pre s → R0 s x → ¬ G x) (hD : ∀ s x, P.Pre s → P.DS s x → ¬ G x) :
    ∀ s s' a r, P.Pre s → P.F P.ar P.st s a = ok r → ¬ P.Acc r.1 →
      @Alt P.S P.st P.L (P.RS s) cls ko User s s' →
      Within P.st P.ar (fun b => ¬ G b) (fun b => User b ∨ ¬ G b) P.p s' a := by
  intro s s' a r hs hr hn Al
  letI := P.L
  obtain ⟨r', hr'⟩ := P.total s' a
  have g : AltOf P.st P.Pre P.RS cls ko User s' := ⟨s, hs, Al⟩
  have h1 := hRd s s' a r r' hs hr hn Al hr'
  have h2 := (P.obl.dec_alt s a r hs hr hn s' r' Al hr').2.1
  rw [P.isProg _ (Narrow.guard _ _ _) s' g a] at h1 h2
  have w1 := (interp_guard P.p s' a r' h1).2
  have w2 := (interp_guard P.p s' a r' h2).2
  exact Within.mono (fun b hb => hR0 s b hs hb.1) (fun b hb => Or.inr (hD s b hs hb.2)) P.p s' a
    (E2E.within_and P.p s' a w1 w2)

end gen

/-! ## 2. Paging words of an epoch -/

section pwe
variable {K : KLayoutP} {E : U64 → U64}

theorem pwe_ko (hK : RegionOKP K) (m : U64 → U64) {x : U64} (h : PWE K E x) :
    OwnMap.ko K.toKLayout m x = .free :=
  OwnMap.ko_free_of_nondec hK.base.base
    (OwnMap.nondec_of_region hK.base.base (Or.inr (Or.inr (Or.inr (Or.inl (pwe_region hK h)))))) m

theorem pwe_user (hU : UserOKP K) {x : U64} (h : PWE K E x) : x ∉ K.user := by
  rcases h with hp | h
  · exact (hU.kern x hp).2
  · exact h.2.2.2.1

variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {Locks : S → U64 → Prop} {s : S}

/-- **No region-tagged read-set word is a paging word of the epoch.** -/
theorem ioRSR_notPWE (hK : RegionOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) {x : U64}
    (h : IoRSR st K.toKLayout Locks s x) : ¬ PWE K E x := by
  intro hp
  rcases h.2 with hr | ⟨o, ho, rfl⟩
  · exact hr (pwe_region hK hp)
  · rcases hp with hp | hp
    · exact hks o ho hp
    · exact hp.2.2.2.2 o ho rfl

/-- The decline write set `IoDS` holds no paging word. -/
theorem ioDS_notPWE {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hK : RegionOKP K)
    (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV)
    (P : IoPre st K.toKLayout T Cs Ω H Sg Rp Scs Nt Z Ac s) {x : U64} (h : IoDS (st := st) s x) :
    ¬ PWE K E x := by
  rcases h with rfl | rfl | rfl
  · exact ioRSR_notPWE hK hks (P.regR (Locks := fun _ _ => True) (by simp [layout.reg.FAULT_IP])).1
  · exact ioRSR_notPWE hK hks
      (P.ndR (Locks := fun _ _ => True) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME])
        (by simp [layout.node.CUR_TIME])).1
  · exact ioRSR_notPWE hK hks
      (P.ndR (Locks := fun _ _ => True) layout.node.CONSUMED (by simp [layout.node.CONSUMED])
        (by simp [layout.node.CONSUMED])).1

end pwe

/-! ## 3. The declined half for delPte and CNodeDelete -/

section dec
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **delPte's declined runs touch no paging word of the epoch.** -/
theorem delPte_dec (j : InvArg S) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (h : DelPtePrem st j K) :
    ∀ s s' a r, (delPtePath st ar hA hm j K m hK hU h).Pre s →
      (delPtePath st ar hA hm j K m hK hU h).F (delPtePath st ar hA hm j K m hK hU h).ar
        (delPtePath st ar hA hm j K m hK hU h).st s a = ok r →
      ¬ (delPtePath st ar hA hm j K m hK hU h).Acc r.1 →
      @Alt _ (delPtePath st ar hA hm j K m hK hU h).st (delPtePath st ar hA hm j K m hK hU h).L
        ((delPtePath st ar hA hm j K m hK hU h).RS s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' →
      Within (delPtePath st ar hA hm j K m hK hU h).st (delPtePath st ar hA hm j K m hK hU h).ar
        (fun b => ¬ PWE K E b) (fun b => b ∈ K.user ∨ ¬ PWE K E b) (delPtePath st ar hA hm j K m hK hU h).p s' a := by
  refine LocalPath.decG _ (R0 := fun s => IoRSR st K.toKLayout j.Locks s) ?_ ?_ ?_
  · intro s s' a r r' hE hr hn Al hr'
    have hE' : PreP st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hE
    have hks := ksNoE_conv hE'.2.2.choose_spec.1
    have Al' : Alt st (InvRSP st K j.Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' := Al
    have hr0 : r.1 ≠ true := hn
    exact inv_dec_guardRSR hA hE'.2.1.1.1.1 (invSeenR_of hE'.1 hE'.2.1)
      (Al'.anti (fun x hx => ioRSP_inv (ioRSR_P hK hks hx))) hr hr0 hr'
  · intro s x hE hx
    have hE' : PreP st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hE
    exact ioRSR_notPWE hK (ksNoE_conv hE'.2.2.choose_spec.1) hx
  · intro s x hE hx
    have hE' : PreP st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hE
    exact ioDS_notPWE hK (ksNoE_conv hE'.2.2.choose_spec.1) hE'.2.1.1.1.1 hx

/-- **CNodeDelete's (no PTE lock) declined runs touch no paging word of the epoch.** -/
theorem inv_dec (j : InvArg S) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (h : InvPremW st j K.toKLayoutV m) :
    let P := LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (invAvU st ar hA hm j K m hK hU h)
    ∀ s s' a r, P.Pre s → P.F P.ar P.st s a = ok r → ¬ P.Acc r.1 →
      @Alt _ P.st P.L (P.RS s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s s' →
      Within P.st P.ar (fun b => ¬ PWE K E b) (fun b => b ∈ K.user ∨ ¬ PWE K E b) P.p s' a := by
  intro P
  refine LocalPath.decG P (R0 := fun s => IoRSR st K.toKLayout j.Locks s) ?_ ?_ ?_
  · intro s s' a r r' hs0 hr hn Al hr'
    have hs : (SlJAt (L := L) K.toKLayout s ∧ InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) ∧
        QU st K s := hs0
    have Al' : Alt st (rsE (· ∈ K.ptes) (rsV K.toKLayoutV (InvCMRS (st := st) K.toKLayout j.Locks)) s)
        (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s s' := Al
    have AlR := Al'.anti (R' := IoRSR st K.toKLayout j.Locks s)
      (fun x hx => ⟨⟨ioRS_cm hx.1, not_vData_empty h.nv⟩, (ioRSR_rsE hK hs.2.1.ks hx).2⟩)
    have hr0 : r.1 ≠ true := hn
    exact inv_dec_guardRSR hA hs.1.2.1.1.1 (invSeenRN hs.1.1 hs.1.2) AlR hr hr0 hr'
  · intro s x hs0 hx
    have hs : (SlJAt (L := L) K.toKLayout s ∧ InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) ∧
        QU st K s := hs0
    exact ioRSR_notPWE hK hs.2.1.ks hx
  · intro s x hs0 hx
    have hs : (SlJAt (L := L) K.toKLayout s ∧ InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) ∧
        QU st K s := hs0
    exact ioDS_notPWE hK hs.2.1.ks hs.1.2.1.1.1 hx

end dec

/-! ## 4. The two slots' `hIns` from the accepted-run walk facts -/

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **delPte's share of `hIns`**, from its accepted-run walk fact. -/
theorem insA_delQ (j : InvArg S) {K : KLayoutP} {E : U64 → U64} {s : Cfg U64 U64 U64 U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} (hM : MapsP K s)
    (hAcc : ∀ h : DelPtePrem st j K, AccIns (delPtePath st ar hA hm j K s.mem hK hU h) (PWE K E))
    (h : StartAt (delPteSlot st ar hA hm j K s.mem hK hU) c hs s.mem q) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q := by
  by_cases hp : DelPtePrem st j K
  · rw [delPteSlot_pos st ar hA hm hp] at h
    rw [hM.own, hM.cls, hM.ko]
    exact LocalPath.insAQ _ adEq_equiv (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) (fun x hx => pwe_ko hK _ hx)
      (fun x hx => pwe_user hU hx) (hAcc hp) (delPte_dec st ar hA hm j hK hU hp) h
  · unfold delPteSlot at h
    rw [dif_neg hp] at h
    obtain ⟨σ, a, hpre, -⟩ := h
    exact (hpre : False).elim

/-- **CNodeDelete's (no PTE lock) share of `hIns`**, from its accepted-run walk fact. -/
theorem insA_invQ (j : InvArg S) {K : KLayoutP} {E : U64 → U64} {s : Cfg U64 U64 U64 U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} (hM : MapsP K s)
    (hAcc : ∀ h : InvPremW st j K.toKLayoutV s.mem,
      AccIns (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ (invAvU st ar hA hm j K s.mem hK hU h))
        (PWE K E))
    (h : StartAt (invSlotU st ar hA hm j K s.mem hK hU) c hs s.mem q) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q := by
  by_cases hp : InvPremW st j K.toKLayoutV s.mem
  · rw [invSlotU_pos st ar hA hm hp] at h
    rw [hM.own, hM.cls, hM.ko]
    exact LocalPath.insAQ _ adEq_equiv (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) (fun x hx => pwe_ko hK _ hx)
      (fun x hx => pwe_user hU hx) (hAcc hp) (inv_dec st ar hA hm j hK hU hp) h
  · unfold invSlotU at h
    rw [dif_neg hp] at h
    obtain ⟨σ, a, hpre, -⟩ := h
    exact (hpre : False).elim

end slot

/-! ## 5. The top, reduced to the accepted-run walk facts -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end with the page walker's A/D writes, over U2's family, given only the two walk facts**:
`serializable_fl4_localU3b_ofDI` with `hDel` / `hInv` replaced by `hDelA` / `hInvA` — accepted runs of delPte and
of CNodeDelete (no PTE lock) from their entry states read paging words of the epoch only `ADEq`-insensitively and
store only non-present values into them (`AccIns`). Premises: U2's (`P`, [P] `hIoa`, `h0`, `hA0`, `hB`, `hc0`, `hM0`,
the execution, `hq`) and [P] `MmuAD` (in `ExecU3b`); `hDelA` / `hInvA` are hypotheses of this reduction. -/
theorem serializable_fl4_localU3b_ofAcc (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (hDelA : ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
      (j : InvArg S), (∃ σe, SlJAt (L := L) K.toKLayout σe) → EpochJ K E s → MapsP K s →
      ∀ h : DelPtePrem st j K, AccIns (delPtePath st ar hA (masksWr_plain st) j K s.mem hK hU h) (PWE K E))
    (hInvA : ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
      (j : InvArg S), (∃ σe, SlJAt (L := L) K.toKLayout σe) → EpochJ K E s → MapsP K s →
      ∀ h : InvPremW st j K.toKLayoutV s.mem,
        AccIns (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
          (invAvU st ar hA (masksWr_plain st) j K s.mem hK hU h)) (PWE K E))
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecU3b (famU2 st ar hA a0) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU3b_ofDI st ar hA a0 P hIoa
    (fun K E s hK hU c hs q j hb J hM hP =>
      insA_delQ st ar hA (masksWr_plain st) j hM (hDelA K E s hK hU j hb J hM) hP)
    (fun K E s hK hU c hs q j hb J hM hP =>
      insA_invQ st ar hA (masksWr_plain st) j hM (hInvA K E s hK hU j hb J hM) hP)
    h0 hA0 hB hc0 hM0 h hq

end top

end
end Fl4Proofs.P2.E2EP

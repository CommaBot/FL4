/-
# P2 (line mmuAD, gen 5): **`hIns` for the W11 slots and Copy / Mint** — the U3b top over the remaining two slots

`E2EPU3c.serializable_fl4_localU3b_of` takes the per-slot run-relative A/D insensitivity `hIns` as a hypothesis.
This module discharges it for the eight W11 slots (`fl4LocW11JA`) and the Copy / Mint slot (`cmSlotU`), and
states the top with `hIns` left only for the two slots whose runs read paging words by design (delPte and the
no-PTE-lock CNodeDelete, whose stale-mapped `unmap_page` walks the upper levels: `E2EPU2D` module docstring).

**The enlarged layout** `KU K E`: `K` with every aligned paging word of the epoch (`PWE K E`, leaves and upper-level
entries) as a "PTE word". At an epoch state it is a legal layout (`regionOKP_ku`, `userOKP_ku`: the upper entries
are region `.none`, kernel words, no VCPU at P3 scope), and **`QPs (KU K E)` holds at every start state**
(`qPs_ku`): the kernel-block half is in `PWE`'s definition and `ptesR_ks`; the ASID-table / pool half because those
words are `AsidW` of the epoch memory (excluded from `PWE`, `pwe_asid`), the table words being gate words
(`region_none_tab`, `gateW_of_region`) that equal the epoch memory (`EpochJ.eq`).

So **every existing PTE-avoidance proof, instantiated at `KU K E`, says that the run reads no paging word of the
epoch**: no per-slot proof is copied.
* `LocalPath.within_avoidE` (generic): `AvoidE E R` ⇒ the run from an alternative of any read set containing
  `rsE E R.RS s` reads only aligned words off `E` and writes only `R.WS s` / `R.DS s` (`alt_backE`,
  `back_withinE`, `sim_off`, as `E2EPCut.cut_read_alignedE`). `LocalPath.noPWE_of_avoid`: with `E := (KU K E).ptes`
  and an `own` that gives every `PWE` word to the gate, this is exactly `insA_of_noG`'s `hNG` (written words are
  held: `write_own`; a gate word is never held).
* W11: `allA` at `KU K E` (`w11_noG`); the slot's path is restricted by `QPs (KU K E)` (`LocalPath.restrQ`), which
  its start state satisfies, and `LocalPath.insA` gives **`insA_w11`**.
* Copy / Mint: `avoidE_cmE`'s proof does not use the `CvP` half of `QU`, so it is repeated with `QPs (KU K E)` for
  the cut (**`avoidE_cmKU`**; `CvP` at `KU K E` is false once an upper entry exists); **`insA_cm`**.
* `execU3b_aRunRB`: `execU3b_aRunR` with the bundle (`∃ σe, SlJAt K σe`, from the chain) also handed to `hIns`.
* **`serializable_fl4_localU3b_ofDI`**: `serializable_fl4_localU3b_of` with `hIns` only for **delPte** (`hDel`) and
  **CNodeDelete** (`hInv`). Both read paging words (walks, the held leaf) with masks that clear bits 5 and 6; their
  discharge is the masked bridge (handoff mmuAD gen 5).

No [W], no new [J]; the only [P] is `MmuAD` (P2/MmuADWalk.lean). `hDel` / `hInv` are hypotheses of a reduction
theorem, not premises of a top. No existing statement changed.
-/
import Fl4Proofs.P2.E2EPU3c
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg HwWr allowed_of_sinv
  InsA ARunR aRunR_inv serializable_safeR)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

/-! ## 1. Runs of an avoiding path -/

section gen
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
  {User : U64 → Prop}

/-- **From `AvoidE E R`**: the run from an alternative of any read set containing `rsE E R.RS s` reads only aligned
words off `E` and writes only `R.WS s` / `R.DS s` words. -/
theorem _root_.Fl4Proofs.P2.E2E.LocalPath.within_avoidE (R : LocalPath own cls ko User) {E : U64 → Prop}
    (hAv : AvoidE E R) {R0 : U64 → Prop} {s s2 : R.S} (hs : R.Pre s)
    (hA : @Alt R.S R.st R.L R0 cls ko User s s2) (hsub : ∀ x, R.RS s x → ¬ E x → R0 x) (a : R.A) :
    Within R.st R.ar (GE E) (fun b => R.WS s b ∨ R.DS s b) R.p s2 a := by
  letI := R.L
  have hA' : Alt R.st (rsE E R.RS s) cls ko User s s2 := hA.anti (fun x hx => hsub x hx.1 hx.2)
  obtain ⟨s'', hA'', hAg⟩ := alt_backE R.side R.masks hs hA'
  have w := back_withinE (a := a) hAv.progCut R.obl R.side R.once R.total R.masks hAv.acc hAv.dec hs hA''
  obtain ⟨r'', h''⟩ := R.total s'' a
  have e := R.isProg R.st (Narrow.self R.st) s'' ⟨s, hs, hA''⟩ a
  have hO := R.once s s'' a r'' hs hA'' (e.symm.trans h'')
  exact (sim_off R.masks ge_ok (fun b hb => hb.elim (fun h => R.obl.aligned s b hs (Or.inl h))
    (fun h => R.obl.aligned s b hs (Or.inr h))) R.p s2 s'' a ∅ ∅ hAg w hO).1

end gen

/-! ## 2. The enlarged layout -/

section ku
variable {K : KLayoutP} {E : U64 → U64}

/-- **`K` with every aligned paging word of the epoch as a PTE word** (module docstring). -/
def KU (K : KLayoutP) (E : U64 → U64) : KLayoutP := { K with ptes := {b | PWE K E b ∧ Aligned b} }

theorem pte_ku (hU : UserOKP K) {b : U64} (h : b ∈ K.ptes) : b ∈ (KU K E).ptes :=
  ⟨Or.inl h, (hU.kern b h).1⟩

theorem regionOKP_ku (hK : RegionOKP K) (nv : K.vcpus = ∅) : RegionOKP (KU K E) :=
  ⟨hK.base, fun _ he => pwe_region hK he.1, fun _ _ ⟨_, hv⟩ => not_inVcpu_empty nv hv⟩

theorem userOKP_ku (hU : UserOKP K) : UserOKP (KU K E) := by
  refine ⟨hU.base, fun e he => ⟨he.2, ?_⟩⟩
  rcases he.1 with hp | h
  · exact (hU.kern e hp).2
  · exact h.2.2.2.1

/-- **`QPs (KU K E)` at a start state of the epoch** (module docstring). -/
theorem qPs_ku {S S' : Type} {st : machine.Store S} [L : LawfulStore st] {st' : machine.Store S'}
    (L' : LawfulStore st') {s : Cfg U64 U64 U64 U64} (J : EpochJ K E s)
    (hb : ∃ σe, SlJAt (L := L') K.toKLayout σe) {σ : S} (hq : QPs K st σ)
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = s.mem x) : QPs (KU K E) st σ := by
  obtain ⟨σe, A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B⟩ := hb
  have hnA : ∀ b, AsidW K.ksb E b → ¬ PWE K E b := fun b hb => pwe_asid J.conv hb
  have hm : ∀ hi : U64, hi.val < 2048 → L.mem σ (atAF K.ksb hi) = E (atAF K.ksb hi) := by
    intro hi hhi
    have ht : AsidW K.ksb E (atAF K.ksb hi) := Or.inl ⟨hi, hhi, rfl⟩
    rw [hμ _ (hq.al hi hhi) (fun hu => hq.uoff _ (Or.inl hu) hi hhi rfl)]
    exact J.eq _ (gateW_of_region (region_none_tab B hhi) (fun hp => hnA _ ht (Or.inl hp)) J.nv) (hnA _ ht)
  refine ⟨fun o ho hb => ?_, hq.ksb, ?_, hq.al, hq.uoff⟩
  · obtain ⟨hp, -⟩ := hb
    rcases hp with hp | h
    · exact hq.ks o ho hp
    · exact h.2.2.2.2 o ho rfl
  · intro hi hhi
    rw [hq.ksb]
    refine ⟨fun hb => hnA _ (Or.inl ⟨hi, hhi, rfl⟩) hb.1, fun lo hlo hne hb => ?_⟩
    rw [hm hi hhi] at hne hb
    exact hnA _ (Or.inr ⟨hi, hhi, hne, lo, hlo, rfl⟩) hb.1

/-- A paging word of the epoch is the gate's under `OwnMap.own` (region `.none`). -/
theorem own_pwe_gate (hK : RegionOKP K) {m : U64 → U64} {b : U64} (h : PWE K E b) :
    OwnMap.own K.toKLayout m b = .gate := by
  unfold OwnMap.own
  rw [pwe_region hK h]

/-- A paging word of the epoch is the gate's under `ownV` (no VCPU). -/
theorem ownV_pwe_gate (hK : RegionOKP K) (nv : K.vcpus = ∅) {m : U64 → U64} {b : U64} (h : PWE K E b) :
    ownV K.toKLayoutV m b = .gate := by
  unfold ownV
  rw [dif_neg (by rintro ⟨v, hv⟩; exact not_inVcpu_empty nv hv)]
  exact own_pwe_gate hK h

end ku

section gen2
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
  {User : U64 → Prop}

/-- **`insA_of_noG`'s `hNG` from `AvoidE` at the enlarged layout.** -/
theorem _root_.Fl4Proofs.P2.E2E.LocalPath.noPWE_of_avoid (R : LocalPath own cls ko User) {K : KLayoutP}
    {E : U64 → U64} (hown : ∀ m b, PWE K E b → own m b = .gate) (hAv : AvoidE (· ∈ (KU K E).ptes) R)
    {R0 : U64 → Prop} {s s2 : R.S} (hs : R.Pre s) (hA : @Alt R.S R.st R.L R0 cls ko User s s2)
    (hsub : ∀ x, R.RS s x → x ∉ (KU K E).ptes → R0 x) (a : R.A) :
    Within R.st R.ar (fun b => ¬ PWE K E b) (fun b => User b ∨ ¬ PWE K E b) R.p s2 a := by
  letI := R.L
  refine Within.mono (fun b hb hpw => hb.2 ⟨hpw, hb.1⟩) (fun b hb => ?_) R.p s2 a
    (R.within_avoidE hAv hs hA hsub a)
  by_cases hu : User b
  · exact Or.inl hu
  · refine Or.inr fun hpw => ?_
    have hw := R.obl.write_own s b hs hb hu
    unfold WPerm at hw
    rw [hown _ _ hpw] at hw
    exact hw

end gen2

/-! ## 3. The W11 slots -/

section w11
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **A W11 slot's runs, at `QPs (KU K E)` states, touch no paging word of the epoch** (`allA` at `KU K E`). -/
theorem w11_noG (i : Fl4IxW (S := S)) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (nv : K.vcpus = ∅) (s1 s2 : (fl4LocW11JA st ar hA hm hSt a0 i K m hK hU).S)
    (a : (fl4LocW11JA st ar hA hm hSt a0 i K m hK hU).A)
    (hp : (fl4LocW11JA st ar hA hm hSt a0 i K m hK hU).Pre s1)
    (hq : QPt (KU K E) (fl4LocW11JA st ar hA hm hSt a0 i K m hK hU) s1)
    (hAl : @Alt _ (fl4LocW11JA st ar hA hm hSt a0 i K m hK hU).st (fl4LocW11JA st ar hA hm hSt a0 i K m hK hU).L
      ((fl4LocW11JA st ar hA hm hSt a0 i K m hK hU).RS s1) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
      (· ∈ K.user) s1 s2) :
    Within (fl4LocW11JA st ar hA hm hSt a0 i K m hK hU).st (fl4LocW11JA st ar hA hm hSt a0 i K m hK hU).ar
      (fun b => ¬ PWE K E b) (fun b => b ∈ K.user ∨ ¬ PWE K E b) (fl4LocW11JA st ar hA hm hSt a0 i K m hK hU).p
      s2 a := by
  have hK' := regionOKP_ku (E := E) hK nv
  have hU' := userOKP_ku (E := E) hU
  have hAv := allA st ar hA hm hSt a0 i (KU K E) m hK' hU'
  obtain ⟨hp1, -⟩ := hp
  exact LocalPath.noPWE_of_avoid _ (fun _ _ h => ownV_pwe_gate hK nv h) hAv ⟨hp1, hq⟩ hAl
    (fun x hx hn => ⟨hx, fun hp => hn (pte_ku hU hp)⟩) a

/-- **`hIns` for a W11 slot.** -/
theorem insA_w11 (i : Fl4IxW (S := S)) {K : KLayoutP} {E : U64 → U64} {s : Cfg U64 U64 U64 U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP}
    (hb : ∃ σe, SlJAt (L := L) K.toKLayout σe) (J : EpochJ K E s) (hM : MapsP K s)
    (h : StartAt (fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU) c hs s.mem q) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q := by
  obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := h
  have hqK := hpre.2
  letI := (fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU).L
  have hq : QPt (KU K E) (fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU) σ :=
    qPs_ku L J hb hqK (fun x hx hu => hμ x hx hu)
  have h' : StartAt ((fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU).restrQ
      (QPt (KU K E) (fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU))
      (qPt_stab (KU K E) _ (fun b hb => Or.inl hb))) c hs s.mem
      ((fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU).body σ a) :=
    ⟨σ, a, ⟨hpre, hq⟩, hc, hl, hμ, rfl⟩
  rw [hM.own, hM.cls, hM.ko]
  refine LocalPath.insA _ (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) ?_ h'
  intro s1 s2 a' hp1 hA'
  exact w11_noG st ar hA hm hSt a0 i (E := E) (m := s.mem) hK hU J.nv s1 s2 a' hp1.1 hp1.2 hA'

end w11

/-! ## 4. The Copy / Mint slot -/

section cm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar)

/-- **The Copy / Mint path, restricted to `QU K ∧ QPs (KU K E)`, reads no paging word of the epoch**
(`avoidE_cmE`'s proof at `KU K E`). No premise. -/
theorem avoidE_cmKU {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (K : KLayoutP) (E m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (hK' : RegionOKP (KU K E))
    (hU' : UserOKP (KU K E)) :
    AvoidE (· ∈ (KU K E).ptes) ((inv_pathCME (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA
      number p hm hCs hlk K.toKLayout m hK.base.base hU.base.base).restrQ
      (fun s => QU st K s ∧ QPs (KU K E) st s)
      (fun _ _ _ _ h hb ha => ⟨qU_wr h.1 hb ha, h.2.wr (Or.inl hb) ha⟩)) := by
  have hSC : InvSlotCN st K.toKLayout p
      (fun s => (SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧
        (QU st K s ∧ QPs (KU K E) st s)) :=
    fun s h => cmSC_ofZ K.toKLayout m s h.1
  have hpR := inv_isProgOnR (Locks := Locks) (m0 := m) hA
    (P := fun s => (SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧
      (QU st K s ∧ QPs (KU K E) st s))
    (fun _ h => h.1.2.1.1.1) hSC (inv_isProg S number p)
  refine ⟨?_, ?_, ?_⟩
  · intro s a r hs hr hb
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hs' : (SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧
        (QU st K s ∧ QPs (KU K E) st s) := hs
    have hr' : syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) := hr
    show syscall.handle_invocation_local (guard st (rsE (· ∈ (KU K E).ptes)
      (InvCMRS (st := st) K.toKLayout Locks) s) (InvCMWS (st := st) K.toKLayout Locks s)) ar s a number p
      = ok (true, s1, a1)
    exact invCMAccN (K := KU K E) hA hK' hU' hs'.1 hs'.2.2.ks hr'
  · intro s a r hs0 hr hn s' r' hA' h'
    have hs : (SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧
        (QU st K s ∧ QPs (KU K E) st s) := hs0
    have Al : Alt st (InvCMRS (st := st) K.toKLayout Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' := hA'
    have AlR := Al.anti (R' := IoRSR st K.toKLayout Locks s) (fun x hx => ioRS_cm hx.1)
    have hr' : syscall.handle_invocation_local st ar s a number p = ok r := hr
    have h'' : syscall.handle_invocation_local st ar s' a number p = ok r' := h'
    have g := inv_dec_guardRSR hA hs.1.2.1.1.1 (cmSeenRN hs.1.1 hs.1.2) AlR hr' hn h''
    have e := fun (st' : machine.Store S) (N : Narrow st st') => hpR st' N s' ⟨s, hs, AlR⟩ a
    show syscall.handle_invocation_local (guard st (fun b => ¬ b ∈ (KU K E).ptes) (fun _ => True)) ar s' a
      number p = ok r'
    exact (e _ (Narrow.guard _ _ _)).trans (interp_mono (st := st)
      (fun q hq hp => (ioRSR_rsE (K := KU K E) hK' hs.2.2.ks hq).2 hp)
      (fun _ h => h) _ (inv_noZero number p) s' a r' ((e _ (Narrow.guard _ _ _)).symm.trans g))
  · intro st' N σ g a
    obtain ⟨s, hs0, hAc⟩ := g
    have hs : (SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧
        (QU st K s ∧ QPs (KU K E) st s) := hs0
    have hAc' : Alt st (rsE (· ∈ (KU K E).ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
        (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s σ := hAc
    exact hpR st' N σ ⟨s, hs, hAc'.anti (R' := IoRSR st K.toKLayout Locks s)
      (fun x hx => ioRSR_rsE (K := KU K E) hK' hs.2.2.ks hx)⟩ a

end cm

section cmslot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The Copy / Mint slot's runs, at `QPs (KU K E)` states, touch no paging word of the epoch.** -/
theorem cm_noG (j : InvArg S) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (nv : K.vcpus = ∅) (h : InvPremW st j K.toKLayoutV m) (s1 s2 : S) (a : A)
    (hp : (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (cmAvU st ar hA hm j K m hK hU h)).Pre s1)
    (hq : QPs (KU K E) st s1)
    (hAl : Alt st ((LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (cmAvU st ar hA hm j K m hK hU h)).RS
      s1) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s1 s2) :
    Within st ar (fun b => ¬ PWE K E b) (fun b => b ∈ K.user ∨ ¬ PWE K E b)
      (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (cmAvU st ar hA hm j K m hK hU h)).p s2 a := by
  have hK' := regionOKP_ku (E := E) hK nv
  have hU' := userOKP_ku (E := E) hU
  have hAv := avoidE_cmKU (Cs := j.Cs) (Ω := j.Ω) (Sg := j.Sg) (Ac := j.Ac) (Locks := j.Locks) ar hA j.number j.p
    hm (h.hCs st) h.lk K E m hK hU hK' hU'
  obtain ⟨hp1, hp2⟩ := hp
  exact LocalPath.noPWE_of_avoid _ (fun _ _ h => own_pwe_gate hK h) hAv ⟨hp1, hp2, hq⟩ hAl
    (fun x hx hn => ⟨⟨hx, not_vData_empty nv⟩, fun hp => hn (pte_ku hU hp)⟩) a

/-- **`hIns` for the Copy / Mint slot.** -/
theorem insA_cm (j : InvArg S) {K : KLayoutP} {E : U64 → U64} {s : Cfg U64 U64 U64 U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP}
    (hb : ∃ σe, SlJAt (L := L) K.toKLayout σe) (J : EpochJ K E s) (hM : MapsP K s)
    (h : StartAt (cmSlotU st ar hA hm j K s.mem hK hU) c hs s.mem q) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q := by
  by_cases hp : InvPremW st j K.toKLayoutV s.mem
  · rw [cmSlotU_pos st ar hA hm hp] at h
    obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := h
    have hqK : QPs K st σ := hpre.2.1
    have hq : QPs (KU K E) st σ := qPs_ku L J hb hqK (fun x hx hu => hμ x hx hu)
    have h' : StartAt ((LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
        (cmAvU st ar hA hm j K s.mem hK hU hp)).restrQ (fun σ => QPs (KU K E) st σ)
        (fun _ _ _ _ hq' hb' ha => hq'.wr (Or.inl hb') ha)) c hs s.mem
        ((LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
          (cmAvU st ar hA hm j K s.mem hK hU hp)).body σ a) :=
      ⟨σ, a, ⟨hpre, hq⟩, hc, hl, hμ, rfl⟩
    rw [hM.own, hM.cls, hM.ko]
    refine LocalPath.insA _ (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) ?_ h'
    intro s1 s2 a' hp1 hA'
    exact cm_noG st ar hA hm j (E := E) (m := s.mem) hK hU J.nv hp s1 s2 a' hp1.1 hp1.2 hA'
  · unfold cmSlotU at h
    rw [dif_neg hp] at h
    obtain ⟨σ, a, hpre, -⟩ := h
    exact (hpre : False).elim

end cmslot

/-! ## 5. `ExecU3b` with the bundle handed to `hIns`, and the top over delPte / CNodeDelete -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **`execU3b_aRunR` with the epoch's bundle state handed to `hIns`.** -/
theorem execU3b_aRunRB {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (hIns : ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
      (c : U64) (hs : U64 → Prop) (q : SP) (i : ι), (∃ σe, SlJAt (L := L) K.toKLayout σe) → EpochJ K E s →
      MapsP K s → StartAt (LP i K s.mem hK hU) c hs s.mem q →
      InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecU3b LP SF P s0 K0 Ch0 s K Ch E) :
    ARunR ADEq NotPresent s0 s (PWE K E) ∧ RegionOKP K ∧ UserOKP K ∧ MapsP K s ∧
      SerExitW P K.toKLayoutV Ch ∧ EpochJ K E s := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  induction h with
  | refl => exact ⟨.refl _, hK0, hU0, hM0, hB, epochJ_ser hc0⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 E1 _ hS g ih =>
    obtain ⟨hR, hK, hU, hM, hX, J⟩ := ih
    obtain ⟨⟨H, I⟩, -, hSI, -⟩ := aRunR_inv adEq_equiv h0 hA0 hR
    have hb : ∃ σe, SlJAt (L := L) K1.toKLayout σe := by
      obtain ⟨σe, hC'⟩ := hX.chainOf
      have hσe : Ch1 σe := by
        obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
        exact h'
      exact ⟨σe, ChainOf.bun hC' σe hσe⟩
    have hst : ∀ p0 k W, s1.ph c1 = .loc p0 (.start k) W →
        ∃ i, StartAt (LP i K1 s1.mem hK hU) c1 (fun l => s1.lk l = some c1) s1.mem k := by
      intro p0 k W hph
      obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
      exact ⟨i, hSF _ _ s1 _ _ _ _ _ i hX.chainOf (epoch_start J) hi⟩
    have hok : Fl4Proofs.P2.Serial.SafeStep s1 c1 s1' := by
      refine ⟨g.arm, fun p0 k W hph => ?_⟩
      obtain ⟨i, hP⟩ := hst p0 k W hph
      rw [hM.own, hM.cls, hM.ko]
      exact (LP i K1 s1.mem hK hU).safe (moveHeldP hK) (ownDepP hK hU) hP
    by_cases hs : SerStep s1 c1
    · rw [if_pos hs]
      have hnl := I.inv.clo hs.1
      have hR' := ARunR.regate (PWE K1' s1'.mem) hR hs.1
      have hK' := okP_R (g.serX hs) (g.serC hs)
      refine ⟨.step hR' hS hok (fun p0 k W hph => absurd (by rw [hph]; trivial) (hnl c1)), hK'.1, hK'.2,
        g.serG hs, g.serX hs, epochJ_ser (g.serC hs)⟩
    · rw [if_neg hs]
      obtain ⟨eK, eC⟩ := g.keep hs
      subst eK eC
      have hal := allowed_of_sinv hSI c1
      refine ⟨.step hR hS hok (fun p0 k W hph => ?_), hK, hU, maps_stepP hK hM hal hS hs, hX,
        epochJ_keep J (fun x hx => step_gate_keep hM hal hS hs hx)⟩
      obtain ⟨i, hP⟩ := hst p0 k W hph
      exact hIns _ _ _ hK hU _ _ _ i hb J hM hP
  | hw _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, J⟩ := ih
    exact ⟨.hw hR (hH.hwWr hK hM), hK, hU, maps_hwP hK hM hH, hX,
      epochJ_keep J (fun x hx => hw_gate_keep hK hM hH hx)⟩
  | mmu _ hH ih =>
    obtain ⟨hR, hK, hU, hM, hX, J⟩ := ih
    exact ⟨.ad hR (adWr_pwe hK hM hH), hK, hU, maps_pwe hK hM hH, hX, epochJ_mmu J hH⟩

end exec

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end with A/D writes to every paging word of the epoch, given `hIns` for delPte and CNodeDelete
only**: `serializable_fl4_localU3b_of` with the W11 and Copy / Mint shares discharged (`insA_w11`, `insA_cm`).
`hDel` / `hInv` are the two slots whose runs read paging words (module docstring). -/
theorem serializable_fl4_localU3b_ofDI (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (hDel : ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
      (c : U64) (hs : U64 → Prop) (q : SP) (j : InvArg S), (∃ σe, SlJAt (L := L) K.toKLayout σe) →
      EpochJ K E s → MapsP K s → StartAt (delPteSlot st ar hA (masksWr_plain st) j K s.mem hK hU) c hs s.mem q →
      InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    (hInv : ∀ (K : KLayoutP) (E : U64 → U64) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K)
      (c : U64) (hs : U64 → Prop) (q : SP) (j : InvArg S), (∃ σe, SlJAt (L := L) K.toKLayout σe) →
      EpochJ K E s → MapsP K s → StartAt (invSlotU st ar hA (masksWr_plain st) j K s.mem hK hU) c hs s.mem q →
      InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecU3b (famU2 st ar hA a0) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_safeR adEq_equiv h0 hA0 (execU3b_aRunRB ?_ ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  · intro Ch K s hK hU c hs q i hC hE hsf
    have nv : K.vcpus = ∅ := by
      obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
      exact nv
    rcases i with i | ((j | j) | j)
    · exact startAt_U st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE (startU_of_U2 st ar hA a0 hC nv hsf)
    · exact delPteStart_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact invStartU2_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact cmStartU2_at st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · intro K E s hK hU c hs q i hb J hM hP
    rcases i with i | ((j | j) | j)
    · exact insA_w11 st ar hA (masksWr_plain st) L.total a0 i hb J hM hP
    · exact hDel K E s hK hU c hs q j hb J hM hP
    · exact hInv K E s hK hU c hs q j hb J hM hP
    · exact insA_cm st ar hA (masksWr_plain st) j hb J hM hP

end top

end
end Fl4Proofs.P2.E2EP

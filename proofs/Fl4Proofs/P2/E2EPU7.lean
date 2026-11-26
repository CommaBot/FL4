/-
# P2 (line p3mc, gen 3): `serializable_fl4_localU7`, U6 without `VPte`, and the view on the words a core can tell

## 1. `VPte` [P] is not needed (proved)
U6 asks, per start, `VPte K c ρ`: a PTE convention witness for `ρ` on **every** gate word gives one for
`view K c ρ`. That statement is not provable from layout facts alone: `ptesR` follows pointers read from memory,
and for an arbitrary memory a pool or table pointer may point into a TCB, whose gate words the view rewrites.

The witness is never used on every gate word. The four start lemmas that consume it (`startAt_U` through
`startAt_cutAR` and `qPs_of_convR`, `delPteStart_at`, and `invStartU2_at`/`cmStartU2_at` through `qU_start`) use
it only at gate words **of region `.none` off the PTE set** (each use goes through `gateW_of_region`). The view
rewrites only TCB, SC and node words (`CoreView.repl2_region`), so it keeps every region-`.none` word. Hence:
* `EpochPteN K m`: the witness on region-`.none` words off `K.ptes`. `epochPteN_of` gets it from the old form,
  and **`epochPteN_view`** shows the view keeps it, for every memory, core and layout;
* `qPs_of_convRN`, `startAt_cutARN`, `startAt_UN`, `delPteStart_atN`, `qU_startN`, `invStartU2_atN`,
  `cmStartU2_atN`: copies of the five consumers that take `EpochPteN`, with proofs unchanged except at the
  `gateW_of_region` step;
* `Fl4StepWPRV7` / `ExecWPRV7`: `Fl4StepWPRV` / `ExecWPRV` with `VPte` dropped from `start`;
  `execPV_of_WPRV7`, in which the epoch witness of the physical memory yields `EpochPteN` at the view;
* **`serializable_fl4_localU7`**: U6's conclusion over `ExecWPRV7`;
* `execWPRV7_of_WPRV` (U6 ⊆ U7), `execWPRV7_of_WPRRHo` and **`serializable_fl4_localU5Ho7`** (homed U5 ⊆ U7).

## 2. The view on the words a core can tell (`CoreView.NotForeign`, proved)
`NotForeign K c ρ b` holds when `b` is not a word of another core's thread or SC, not a queue word of another
core's node, and not a word of a notification bound to another core's thread. On those words:
* `view_eq_nf`: the view has `ρ`'s value;
* `own_view_nf`, `ownP_view_nf`: the view has `ρ`'s owner. Notification words are in the definition because
  `ntfnOwner` reads the bound thread's `AFFINITY`, so the view moves their owner although it keeps their values;
* `veq_view_nf`: U5's `VEq ρ μ` gives `VEq`'s first two clauses between the view and `μ` on these words. This is
  the restricted `VEq` that a localised `body_safeH` needs.

The pinning lemmas give a word's real home from the view: `view_hidden_home` (a running, restarting, idle or
VM state at the view means the thread is really homed on `c`), `view_tzero_home` (a nonzero `SC`, `IN_QUEUES` or
debug link), `view_sctcb_home` (a nonzero SC `TCB` word), and `view_node_nz` (a nonzero queue word of a node at
the view is a word of `c`'s own node).

## 3. `ViewSafe` [J]: kept for every slot (status in `WS/handoff/p3mc.md` §6)
No slot's `ViewSafe` is discharged here. The obstacle is the same for all eleven. Every path's read set `RS` is a
maximal permission set at the start state: `IoRS` and the like are every aligned kernel word that the core holds,
or that the gate owns, under `own` **at the start memory**. At the view this includes other cores' threads,
whose words the view gives to `c`. `body_safeH`'s `RInv` needs every `RS` word readable at the physical memory,
and its check memory has to be the store memory on all kernel words (`sim`), so neither can be narrowed without
new per-path read-set obligations. Two slots are also not dischargeable through this view at all: `st` and `irq`
read the `AFFINITY` of other cores' threads in `c`'s timer tree on accepted runs, and a P3 state at the view
cannot show such a thread as homed elsewhere (`SchedCore.aff`). See the handoff.

## Premises of `serializable_fl4_localU7` vs `serializable_fl4_localU6`
* **Removed: `VPte` [P]** (from `start`).
* **Unchanged**: `start` [P] otherwise (`∃ ρ, VEq ρ s.mem ∧ ∃ i, SF (Ch c) K (view K c ρ) … ∧ VSafe …`), `VSafe` [J]
  (family form `ViewSafe` [J]) for all slots, `serX` [P] / `hB` (one chain per core), `arm` [P], `serC`, `serG` [P],
  `keep`, `P`, `hIoa`, `h0`, `hA0`, `hc0`, `hM0`, `hq`, and the slot records inside `StartV2` with `yb` [J].

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPU6
open Aeneas Aeneas.Std Result

/-! ## The view on the words a core can tell -/

namespace Fl4Proofs.P2.CoreView
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.OwnMapP (KLayoutP ownP RegionOKP ownP_off)
open Fl4Proofs.P2.OwnMapV (ownV_off)

noncomputable section
open Classical

/-- **`b` is not a word another core owns or decides** (module docstring §2). -/
def NotForeign (K : KLayout) (c : U64) (ρ : U64 → U64) (b : U64) : Prop :=
  (∀ t, region K b = .tcb t → ρ (fld t oAFFINITY) = c) ∧
  (∀ p, region K b = .sc p → ρ (fld p 16#u64) = c) ∧
  (∀ d, region K b = .node d → d = c ∨ ¬ QWord (nodeOff K d b)) ∧
  (∀ p, region K b = .ntfn p → K.heap (ρ (fld p 24#u64)) = some .tcb →
    ρ (fld (ρ (fld p 24#u64)) oAFFINITY) = c)

/-- **The view keeps the value of a not-foreign word.** -/
theorem view_eq_nf {K : KLayout} {c : U64} {ρ : U64 → U64} {b : U64} (h : NotForeign K c ρ b) :
    view K c ρ b = ρ b := by
  cases hr : region K b with
  | tcb t => exact view_home hr (h.1 t hr)
  | sc p => exact view_sc_home hr (h.2.1 p hr)
  | node d =>
    rcases h.2.2.1 d hr with hd | hq
    · subst hd; exact view_node_self hr
    · by_cases hd : d = c
      · subst hd; exact view_node_self hr
      · exact view_none (by simp only [repl, repl2, hr, nodeRepl, if_neg hd, if_neg hq])
  | slot p => exact view_none (by simp only [repl, repl2, hr])
  | ntfn p => exact view_none (by simp only [repl, repl2, hr])
  | obj p => exact view_none (by simp only [repl, repl2, hr])
  | none => exact view_none (by simp only [repl, repl2, hr])

/-- Every word of a thread homed on `c` keeps its value. -/
theorem view_tcb_fld {K : KLayout} (hK : RegionOK K) {c t : U64} {ρ : U64 → U64} (ht : K.heap t = some .tcb)
    (ha : ρ (fld t oAFFINITY) = c) {off : U64}
    (ho : off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨ off = oREPLY_OBJ ∨ off = oTIMER_DEADLINE ∨
      off = oTIMER_HEIGHT) : view K c ρ (fld t off) = ρ (fld t off) :=
  view_home (hK.tcb t ht off ho).1 ha

/-- **The view keeps the owner of a not-foreign word** (module docstring §2). -/
theorem own_view_nf {K : KLayout} (hK : RegionOK K) {c : U64} {ρ : U64 → U64} {b : U64}
    (h : NotForeign K c ρ b) : own K (view K c ρ) b = own K ρ b := by
  cases hr : region K b with
  | tcb t =>
    have ht := hK.tcbOf t b hr
    have ha := h.1 t hr
    have e1 := view_tcb_fld hK ht ha (Or.inl rfl)
    have e2 := view_tcb_fld hK ht ha (Or.inr (Or.inl rfl))
    have e3 := view_tcb_fld hK ht ha (Or.inr (Or.inr (Or.inl rfl)))
    have e5 := view_tcb_fld hK ht ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    have e6 := view_tcb_fld hK ht ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    simp only [own, hr, tcbOwner, e1, e2, e3, e5, e6]
  | sc p =>
    have e : view K c ρ (fld p 16#u64) = ρ (fld p 16#u64) :=
      view_sc_home (hK.scw p b hr).1 (h.2.1 p hr)
    simp only [own, hr, e]
  | node d => simp only [own, hr]
  | slot p =>
    have e : view K c ρ p = ρ p := view_none (by simp only [repl, repl2, hK.slot p (hK.slotOf p b hr)])
    simp only [own, hr, slotOwner, e]
  | ntfn p =>
    have hn := hK.ntfnOf p b hr
    have e : view K c ρ (fld p 24#u64) = ρ (fld p 24#u64) :=
      view_none (by simp only [repl, repl2, (hK.ntfn p hn).1])
    simp only [own, hr, ntfnOwner, e]
    by_cases hb : K.heap (ρ (fld p 24#u64)) = some .tcb
    · rw [if_pos hb, if_pos hb, view_aff hK hb c ρ, h.2.2.2 p hr hb]
    · rw [if_neg hb, if_neg hb]
  | obj p => simp only [own, hr]
  | none => simp only [own, hr]

/-- `own_view_nf` for `ownP` (VCPU and PTE words are region `.none`, never rewritten). -/
theorem ownP_view_nf {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {b : U64}
    (h : NotForeign K.toKLayout c ρ b) : ownP K (view K.toKLayout c ρ) b = ownP K ρ b := by
  simp only [Fl4Proofs.P2.OwnMapP.ownP, Fl4Proofs.P2.OwnMapV.ownV, own_view_nf hK.base.base h]

/-- **U5's `VEq` gives `VEq`'s owner and value clauses between the view and `μ` on not-foreign words** (module
docstring §2). -/
theorem veq_view_nf {K : KLayoutP} (hK : RegionOKP K) {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64}
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} (hV : Serial.VEq (ownP K) cls ko c hs ρ μ) {x : U64}
    (hx : NotForeign K.toKLayout c ρ x) :
    (Serial.PO c hs (ownP K (view K.toKLayout c ρ) x) → ownP K μ x = ownP K (view K.toKLayout c ρ) x) ∧
      (Serial.PO c hs (ownP K μ x) → view K.toKLayout c ρ x = μ x) := by
  rw [ownP_view_nf hK hx, view_eq_nf hx]
  exact ⟨hV.1 x, hV.2.1 x⟩

/-! ### Pinning: a word's real home from the view -/

/-- **A thread running, restarting, idle or in a VM at `c`'s view is really homed on `c`.** -/
theorem view_hidden_home {K : KLayout} (hK : RegionOK K) {c t : U64} {ρ : U64 → U64} (ht : K.heap t = some .tcb)
    (h : Hidden (view K c ρ (fld t oSTATE))) : ρ (fld t oAFFINITY) = c := by
  by_contra ha
  obtain ⟨hr, ho⟩ := hK.tcb t ht oSTATE (Or.inr (Or.inl rfl))
  exact view_state hr ha (by rw [ho, oSTATE_val]) h

/-- **A nonzero `SC`, `IN_QUEUES` or debug link at `c`'s view is a word of a thread really homed on `c`.** -/
theorem view_tzero_home {K : KLayout} {c t b : U64} {ρ : U64 → U64} (hb : region K b = .tcb t)
    (ho : TZero (b.val - t.val)) (h : view K c ρ b ≠ 0#u64) : ρ (fld t oAFFINITY) = c := by
  by_contra ha
  exact h (view_tzero hb ha ho)

/-- **An SC whose `TCB` word is nonzero at `c`'s view is really on core `c`.** -/
theorem view_sctcb_home {K : KLayout} {c p b : U64} {ρ : U64 → U64} (hb : region K b = .sc p)
    (ho : b.val - p.val = 24) (h : view K c ρ b ≠ 0#u64) : ρ (fld p 16#u64) = c := by
  by_contra ha
  apply h
  exact view_some (by simp only [repl, repl2, hb, scRepl, if_neg ha]; rw [if_neg (by omega), if_pos ho])

/-- **A nonzero queue word of a node at `c`'s view is a word of `c`'s own node.** -/
theorem view_node_nz {K : KLayout} {c d b : U64} {ρ : U64 → U64} (hb : region K b = .node d)
    (hq : QWord (nodeOff K d b)) (h : view K c ρ b ≠ 0#u64) : d = c := by
  by_contra hd
  exact h (view_node_other hb hd hq)

end
end Fl4Proofs.P2.CoreView

/-! ## U7: the start lemmas on the region-`.none` epoch witness -/

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq SafeStepH
  XSafeRunH serializable_safeXH xsafeRunH_inv xsafeRunH_agree allowed_of_sinv veq_start Safe xsafeRun_greach)

noncomputable section
open Classical

/-- **The epoch's PTE convention, witnessed on the region-`.none` words off the PTE set** (module docstring §1):
the only words at which the start lemmas use the witness. -/
def EpochPteN (K : KLayoutP) (m : U64 → U64) : Prop :=
  ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧
    ∀ x, OwnMap.region K.toKLayout x = .none → x ∉ K.ptes → m x = s1.mem x

/-- The old witness gives the new one. -/
theorem epochPteN_of {K : KLayoutP} {m : U64 → U64} (h : EpochPte K m) : EpochPteN K m := by
  obtain ⟨s1, ⟨nv, hc⟩, hk⟩ := h
  exact ⟨s1, ⟨nv, hc⟩, fun x hr hp => hk x (gateW_of_region hr hp nv)⟩

/-- **The view keeps the region-`.none` epoch witness**, for every memory, core and layout (module docstring §1;
this is what `VPte` [P] was asked for). -/
theorem epochPteN_view {K : KLayoutP} {m : U64 → U64} (c : U64) (h : EpochPteN K m) :
    EpochPteN K (CoreView.view K.toKLayout c m) := by
  obtain ⟨s1, hc, hk⟩ := h
  refine ⟨s1, hc, fun x hr hp => ?_⟩
  rw [CoreView.view_none (by simp only [CoreView.repl, CoreView.repl2, hr])]
  exact hk x hr hp

section conv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `qPs_of_convR` on `EpochPteN`'s agreement. -/
theorem qPs_of_convRN {S' : Type} {st' : machine.Store S'} [L' : LawfulStore st'] {K : KLayoutP}
    {s1 : Cfg U64 U64 U64 U64} {m : U64 → U64} (he : K.ptes = ptesR K s1.mem) (nv : K.vcpus = ∅)
    (hb : ∃ σe, SlJAt (L := L) K.toKLayout σe)
    (hkeep : ∀ x, OwnMap.region K.toKLayout x = .none → x ∉ K.ptes → m x = s1.mem x)
    {σ : S'} (hk : L'.ksb σ = K.ksb) (hμ : ∀ x, Aligned x → x ∉ K.user → L'.mem σ x = m x) :
    QPs K st' σ := by
  obtain ⟨σe, A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B⟩ := hb
  let K0 : KLayoutP := { K with ptes := ∅ }
  have B0 : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K0.toKLayout σe a' τ := B
  have Q0 : QPs K0 st σe := qPs_of_bundle B0 (fun b hb => absurd hb (Set.notMem_empty b)) nv
  have hnu : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.user :=
    fun hi hhi hu => Q0.uoff _ (Or.inl hu) hi hhi rfl
  have hnp : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.ptes := by
    intro hi hhi hb
    rw [he] at hb
    exact hb.2.1 (Or.inl ⟨hi, hhi, rfl⟩)
  have hm : ∀ hi : U64, hi.val < 2048 → L'.mem σ (atAF K.ksb hi) = s1.mem (atAF K.ksb hi) := by
    intro hi hhi
    rw [hμ _ (Q0.al hi hhi) (hnu hi hhi)]
    exact hkeep _ (region_none_tab B hhi) (hnp hi hhi)
  refine ⟨fun o ho hb => ?_, hk, ?_, Q0.al, Q0.uoff⟩
  · rw [he] at hb
    exact ptesR_ks o ho hb
  · intro hi hhi
    rw [hk]
    refine ⟨hnp hi hhi, fun lo hlo hne hb => ?_⟩
    rw [hm hi hhi] at hne hb
    rw [he] at hb
    exact hb.2.1 (Or.inr (Or.inl ⟨hi, hhi, hne, lo, hlo, rfl⟩))

end conv

section cut
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- `startAt_cutAR` on `EpochPteN`. -/
theorem startAt_cutARN (i : Fl4IxW (S := S)) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K)
    (hU : UserOKP K) {c : U64} {hs : U64 → Prop} {q0 : SP}
    (hS : StartAt ((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base)
      c hs s.mem q0)
    (hb : ∃ σe, SlJAt (L := L) K.toKLayout σe)
    (hE : EpochPteN K s.mem) :
    StartAt (fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU) c hs s.mem
      (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout s.mem) c q0 ∅) := by
  obtain ⟨s1, ⟨nv, hcv⟩, hk1⟩ := hE
  obtain ⟨σ, a, hP, hc, hl, hμ, e⟩ := hS
  have hk := pre_ksbA st ar hA hm hSt a0 i K s.mem hK hU σ hP
  have hq := qPs_of_convRN
    (L' := ((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base).L)
    hcv nv hb hk1 hk (fun x hx hu => hμ x hx hu)
  refine ⟨σ, a, ⟨hP, hq⟩, hc, hl, hμ, ?_⟩
  show _ = (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
    (allA st ar hA hm hSt a0 i K s.mem hK hU)).body σ a
  refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
    (allA st ar hA hm hSt a0 i K s.mem hK hU) σ a).symm
  change _ = cutP _ _ _ _
    (((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base).L.cpu σ)
    (((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV s.mem hK.base hU.base).body σ a) ∅
  rw [hc, ← e]

end cut

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- `startAt_U` on `EpochPteN`. -/
theorem startAt_UN (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutP} {s : Cfg U64 U64 U64 U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop}
    {q : SP} {i : Fl4IxW (S := S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (hE : EpochPteN K s.mem)
    (h : StartU st ar hA hm hSt a0 arI AR MR Ch K s.mem hK hU c hs q i) :
    StartAt (fl4LocW11JA st ar hA hm hSt a0 i K s.mem hK hU) c hs s.mem q := by
  obtain ⟨q0, hS, rfl⟩ := startAtV_C st ar hA hm hSt a0 P hIoa hC
    (startC_of_D st ar hA hm hSt a0 (startD_of_U st ar hA hm hSt a0 P hIoa hC h))
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  exact startAt_cutARN st ar hA hm hSt a0 i K s hK hU hS ⟨σe, ChainOf.bun hC' σe hσe⟩ hE

end start

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- `delPteStart_at` on `EpochPteN`. -/
theorem delPteStart_atN [Fl4Proofs.P1.PlainStore st] {Ch : S → Prop} {K : KLayoutP} {m : U64 → U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : InvArg S}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (hEp : EpochPteN K m)
    (h : DelPteStart st ar hA hm Ch K m hK hU c hs q j) :
    StartAt (delPteSlot st ar hA hm j K m hK hU) c hs m q := by
  obtain ⟨σe, hC⟩ := hC
  have hCh := ChainOf.bun hC
  obtain ⟨s1, ⟨nv, hc⟩, hk⟩ := hEp
  obtain ⟨h, hG⟩ := h
  rw [delPteSlot_pos st ar hA hm h]
  refine hG.startAt fun σ he hμ => ⟨hCh σ he.1, he.2, s1.mem, hc, fun w hr hp hu ha => ?_⟩
  exact (hμ w ha hu).trans (hk w hr (by rw [hc]; exact hp))

/-- `qU_start` on `EpochPteN`. -/
theorem qU_startN {K : KLayoutP} {m : U64 → U64} {σ : S}
    (hσe : ∃ σe, SlJAt (L := L) K.toKLayout σe) (hJ : SlJAt (L := L) K.toKLayout σ)
    (hE : EpochPteN K m)
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x) : QU st K σ := by
  obtain ⟨s1, ⟨nv, hcv⟩, hk1⟩ := hE
  refine ⟨qPs_of_convRN hcv nv hσe hk1 (slJAt_ksb (L := L) hJ) (fun x hx hu => hμ x hx hu), s1.mem, hcv,
    fun w hr hp hu ha => ?_⟩
  exact (hμ w ha hu).trans (hk1 w hr (by rw [hcv]; exact hp))

/-- `invStartU2_at` on `EpochPteN`. -/
theorem invStartU2_atN [Fl4Proofs.P1.PlainStore st]
    {Ch : S → Prop} {K : KLayoutP} {s : Cfg U64 U64 U64 U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : InvArg S}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (hE : EpochPteN K s.mem)
    (h : InvStartU2 st ar hA hm Ch K s.mem hK hU c hs q j) :
    StartAt (invSlotU st ar hA hm j K s.mem hK hU) c hs s.mem q := by
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  obtain ⟨q0, ⟨h, σ, a, he, hc, hl, hμ, e⟩, rfl⟩ := h
  have hJ := ChainOf.bun hC' σ he.1
  have hq : QU st K σ :=
    qU_startN st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
  rw [invSlotU_pos st ar hA hm h]
  refine ⟨σ, a, ⟨⟨hJ, he.2⟩, hq⟩, hc, hl, hμ, ?_⟩
  refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ (invAvU st ar hA hm j K s.mem hK hU h)
    σ a).symm
  change _ = cutP _ _ _ _ ((invPathVU st ar hA hm j K s.mem hK hU h).L.cpu σ)
    ((invPathVU st ar hA hm j K s.mem hK hU h).body σ a) ∅
  rw [hc, ← e]

/-- `cmStartU2_at` on `EpochPteN`. -/
theorem cmStartU2_atN [Fl4Proofs.P1.PlainStore st]
    {Ch : S → Prop} {K : KLayoutP} {s : Cfg U64 U64 U64 U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : InvArg S}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (hE : EpochPteN K s.mem)
    (h : CMStartU2 st ar hA hm Ch K s.mem hK hU c hs q j) :
    StartAt (cmSlotU st ar hA hm j K s.mem hK hU) c hs s.mem q := by
  obtain ⟨σe, hC'⟩ := hC
  have hσe : Ch σe := by
    obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
    exact h'
  obtain ⟨q0, ⟨h, σ, a, he, hc, hl, hμ, e⟩, rfl⟩ := h
  have hJ := ChainOf.bun hC' σ he.1
  have hq : QU st K σ :=
    qU_startN st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
  rw [cmSlotU_pos st ar hA hm h]
  refine ⟨σ, a, ⟨⟨hJ, he.2⟩, hq⟩, hc, hl, hμ, ?_⟩
  refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _ (cmAvU st ar hA hm j K s.mem hK hU h)
    σ a).symm
  change _ = cutP _ _ _ _ ((cmPathVU st ar hA hm j K s.mem hK hU h).L.cpu σ)
    ((cmPathVU st ar hA hm j K s.mem hK hU h).body σ a) ∅
  rw [hc, ← e]

end slot

/-! ## U7: steps and executions without `VPte` -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 with the glue premises named, one chain per core, the start fact at the core's view, no
`VPte`** (module docstring §1): `Fl4StepWPRV` with `VPte` dropped from `start`. -/
structure Fl4StepWPRV7 (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : U64 → S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : U64 → S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact, of core `c`'s own chain `Ch c` at `c`'s view of a memory `ρ` that `c` cannot tell
  from the physical one (`VEq`), with `VSafe` [J] (the read premise, used only where the view is not `ρ`). -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i, SF (Ch c) K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i ∧
        VSafe LP s K c k hK hU ρ i
  /-- [P] the serial exit's ghost choice, one P3 chain per core. -/
  serX : SerStep s c → ∀ e, SerExitW P K'.toKLayoutV (Ch' e)
  /-- The glue's layout convention at the serial exit. -/
  serC : SerStep s c → K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chains change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4 with the glue steps, one chain per core, starts at the cores' views, no `VPte`.** -/
inductive ExecWPRV7 (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : U64 → S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (U64 → S → Prop) → Prop
  | refl : ExecWPRV7 LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : U64 → S → Prop} {c : U64} :
      ExecWPRV7 LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPRV7 LP SF P s K Ch c s' K' Ch' →
      ExecWPRV7 LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : U64 → S → Prop} {v a x : U64} :
      ExecWPRV7 LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecWPRV7 LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

/-- **Every U6 execution is a U7 execution** (drop `VPte`). -/
theorem execWPRV7_of_WPRV {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop}
    (h : ExecWPRV LP SF P s0 K0 Ch0 s K Ch) : ExecWPRV7 LP SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih =>
    refine .step ih hS ⟨g.arm, fun p0 k W hph hK hU => ?_, g.serX, g.serC, g.serG, g.keep⟩
    obtain ⟨ρ, hV, i, hi, -, hvs⟩ := g.start p0 k W hph hK hU
    exact ⟨ρ, hV, i, hi, hvs⟩
  | hw _ hH ih => exact .hw ih hH

/-- **An `ExecWPRV7` is an `ExecPV`, with the epoch invariant** (`execPV_of_WPRVG` with `hSF` on `EpochPteN`: the
physical epoch witness gives `EpochPteN` at the view, `epochPteN_view`). -/
theorem execPV_of_WPRV7 {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochPteN K s.mem →
      SF Ch K s.mem hK hU c hs q i → StartAt (LP i K s.mem hK hU) c hs s.mem q)
    (P : LocPlat st arI AR MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecWPRV7 LP SF P s0 K0 Ch0 s K Ch) :
    ExecPV LP s0 K0 s K ∧ (∀ e, SerExitW P K.toKLayoutV (Ch e)) ∧
      ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  induction h with
  | refl => exact ⟨.refl, hB, s0, hc0, fun _ _ => rfl⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨H1, hR, -, -, hM⟩ := exec_safeRunPV h0 hA0 hK0 hU0 hM0 hE
    have hst : Fl4StepPV LP s1 K1 c1 s1' K1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩
      · obtain ⟨ρ, hV, i, hi, hvs⟩ := g.start p0 k W hph hK hU
        have hρg : ∀ x, GateW K1 x → ρ x = e1.mem x := fun x hx =>
          (hV.2.1 x (by rw [hM.own, hx s1.mem]; exact Or.inr rfl)).trans (hk1 x hx)
        have hEv : EpochPteN K1 (CoreView.view K1.toKLayout c1 ρ) :=
          epochPteN_view c1 (epochPteN_of ⟨e1, hCe, hρg⟩)
        have hA := hSF (Ch1 c1) _ { s1 with mem := CoreView.view K1.toKLayout c1 ρ } _ _ _ _ _ i
          (hX c1).chainOf hEv hi
        exact ⟨ρ, hV, i, hA, hvs⟩
      · have hP := okP_R (g.serX hs 0#u64) (g.serC hs)
        exact ⟨hP.1, hP.2, g.serG hs⟩
    refine ⟨.step hE hS hst, ?_, ?_⟩
    · by_cases hs : SerStep s1 c1
      · exact g.serX hs
      · obtain ⟨e1, e2⟩ := g.keep hs
        rw [e1, e2]; exact hX
    · by_cases hs : SerStep s1 c1
      · exact ⟨s1', g.serC hs, fun _ _ => rfl⟩
      · obtain ⟨eK, -⟩ := g.keep hs
        subst eK
        obtain ⟨-, -, -, hSI, -⟩ := xsafeRunH_inv h0 hA0 hR
        refine ⟨e1, hCe, fun x hx => ?_⟩
        rw [← hk1 x hx]
        exact step_gate_keep hM (Fl4Proofs.P2.Serial.allowed_of_sinv hSI c1) hS hs hx
  | @hw s1 K1 Ch1 v a y _ hH ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨H1, -, hK, -, hM⟩ := exec_safeRunPV h0 hA0 hK0 hU0 hM0 hE
    refine ⟨.hw hE hH, hX, e1, hCe, fun x hx => ?_⟩
    rw [← hk1 x hx]
    exact hw_gate_keep hK hM hH hx

/-- **Every homed U5 execution is a U7 execution.** -/
theorem execWPRV7_of_WPRRHo {LP : PathsP ι}
    {SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop}
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop}
    (h : ExecWPRRHo LP SF P s0 K0 Ch0 s K Ch) :
    ExecWPRV7 LP SF P s0 K0 (fun _ => Ch0) s K (fun _ => Ch) :=
  execWPRV7_of_WPRV (execWPRV_of_WPRRHo h)

end exec

/-! ## The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end with every slot, one P3 chain per core, each start fact at the starting core's view, without
`VPte`** (module docstring): `serializable_fl4_localU6` over `ExecWPRV7`. The conclusion is about the physical
memory. `ViewSafe` [J] / `VSafe` [J] is kept for every slot (module docstring §3). -/
theorem serializable_fl4_localU7 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV7 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  refine serializable_e2ePV _ h0 hA0 hK0 hU0 hM0 (execPV_of_WPRV7 ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  intro Ch K s hK hU c hs q i hC hE hsf
  have nv : K.vcpus = ∅ := by
    obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
    exact nv
  rcases i with i | ((j | j) | j)
  · exact startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE (startU_of_U2 st ar hA a0 hC nv hsf)
  · exact delPteStart_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · exact invStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · exact cmStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)

/-- **U7 is not weaker than U5 on homed executions**: U5's conclusion for every homed U5 execution, from
`serializable_fl4_localU7`, under U5's premises only. -/
theorem serializable_fl4_localU5Ho7 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRRHo (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU7 st ar hA a0 P hIoa h0 hA0 (fun _ => hB) hc0 hM0 (execWPRV7_of_WPRRHo h) hq

/-- **U6 follows from U7** (every U6 execution is a U7 execution): `VPte` is redundant in U6. -/
theorem serializable_fl4_localU6of7 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU7 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0 (execWPRV7_of_WPRV h) hq

end top

end
end Fl4Proofs.P2.E2EP

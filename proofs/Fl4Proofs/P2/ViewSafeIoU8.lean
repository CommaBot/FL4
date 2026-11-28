/-
# P2 (line p3mc, gen 4): `ViewSafe` for the I/O port slot, and `serializable_fl4_localU8`

## 1. The I/O port path at a core's view satisfies `NarrowV` (proved: `io_narrowV`)
For every argument `j`, layout `K`, core `c` and memory `ρ`, the I/O port path of U7's family taken at
`view K c ρ` (`fl4LocW11JA … (.io j) K (view K c ρ)`: the slot path at `userV K`, given back the real user memory,
lifted to `ownV`, restricted to `QPs` start states, PTE-cut and lifted to `ownP`) has `CoreView.NarrowV`:
* accepted runs: `io_acc` at `userV K` and `io_accN` at `userP K` with `IoNar` from `io_narA_view` (the pins), joined
  on the guard (`within_and`, `guard_of_within`), as `E2EPJW5.io_avoidPJ_path` joins its two guards;
* declined runs at every alternative of the cut read set: the alternative is one of `IoRS (userP K)`
  (`io_avoidPJ_path`'s conversion), and `io_decN` with `IoNarD` from `io_narD_view`;
* where the slot's premise fails the path is the empty one, whose `Pre` is `False`.
**`io_viewSafe`**: hence `ViewSafe`'s conclusion for every io start (`CoreView.viewSafeAt_of_narrow`).

## 2. U8 (`serializable_fl4_localU8`)
`Fl4StepWPRV8` / `ExecWPRV8`: U7's step and execution with `VSafe` asked **only for starts of non-io paths**
(`¬ IoIx i → VSafe …`). `execPV_of_WPRV8` rebuilds U6's `Fl4StepPV` (every start with its `VSafe`), proving the io
starts' `VSafe` by `io_viewSafe` (the ghost maps are `ownP`'s by `exec_safeRunPV`'s `MapsP`). **`serializable_fl4_localU8`**:
U7's conclusion `RunAll s.log s0.mem s.mem` over `ExecWPRV8`. `execWPRV8_of_WPRV7`: every U7 execution is a U8 one.

## Premises of `serializable_fl4_localU8` vs `serializable_fl4_localU7`
* **Removed: `VSafe` [J] / `ViewSafe` [J] for the io slot** (`.inl (.io j)` starts).
* **Unchanged**: `VSafe` [J] for the other slots (vmF, vmR, st, irq, sl, vq, delPte, inv, cm), `start` [P] otherwise,
  `serX` [P] / `hB`, `arm` [P], `serC`, `serG` [P], `keep`, `P`, `hIoa`, `h0`, `hA0`, `hc0`, `hM0`, `hq`, the slot records
  inside `StartV2` with `yb` [J]. Nothing new: `io_viewSafe` uses only the io slot's own premise record (`IoPremW2B`,
  whose `pe` [J] gives `IoPre` at the view start state) that U7 already carries.

## The invariant `t.sc ≠ 0 → CORE(sc t) = AFFINITY t` (sl, vmF, vmR, io rely on it)
`fastpath.schedulable_here` checks the thread's `AFFINITY`, not its SC's `CORE` (`may_run_here` checks both), so the
fast paths are correct on SMP only if a bound SC lives on its thread's core. **P3 carries it at chain states**:
`SchedCore.aff` puts every thread of the state on the state's core and `SchedRel.core` every SC, so at a P3 state
both sides equal `cpu` (for the io path this is `IoPre.affSc` [J], `P2/InvAff.lean` (2)). **It survives the view**:
`view_aff` / `view_sc_core` set both to `c` at `view K c ρ` for every `ρ`, so it holds at every view whatever `ρ` is;
by the same token the view says nothing about it in `ρ`. In `ρ` it is the real invariant P1's `ScExtra.aff`
(`ScAff`) states: where it held in `ρ` the pins above see it (the io path never needs it in `ρ`: it pins the current
SC through the SC's `TCB` back-pointer, `CoreView.sc_home_of_tcb`, not through the thread's `AFFINITY`).

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.ViewSafeIoPin
import Fl4Proofs.P2.E2EPJW5
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe
  xsafeRunH_inv)
open Fl4Proofs.P2.CoreView (view VN VKc VNW NarrowV)

noncomputable section
open Classical

section io
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **The I/O port path at core `c`'s view has `NarrowV`** (module docstring §1). -/
theorem io_narrowV (j : IoArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (ρ : U64 → U64) :
    NarrowV (K := K) (c := c) (ρ := ρ)
      (fl4LocW11JA st ar hA hm hSt a0 (.io j) K (view K.toKLayout c ρ) hK hU) := by
  by_cases hp : (ioSlotP3W st ar hA hm).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = (ioSlotP3W st ar hA hm).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp →
        NarrowV (K := K) (c := c) (ρ := ρ) (LocalPath.cutLiftP hK hU
          (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) := by
      rintro P W hAv rfl
      have h := hp
      have vf : VFacts L K.toKLayoutV := VFacts.ofEmpty h.1 h.2.bun.choose_spec
      have pre : ∀ s, SlJAt (L := L) K.toKLayout s ∧ j.Q K.toKLayoutV (view K.toKLayout c ρ) s →
          IoPre st (userV K.toKLayoutV) K.heap.tcbs j.Cs j.Ω K.heap j.Sg K.heap.replies K.heap.scs K.heap.ntfns
            K.heap.scBits j.Ac s :=
        fun s hs => ioPre_userV hK.base (vf.v hs.1).1 (h.2.pe s hs.1 hs.2)
      have preP : ∀ s, (SlJAt (L := L) K.toKLayout s ∧ j.Q K.toKLayoutV (view K.toKLayout c ρ) s) ∧ QPs K st s →
          IoPre st (userP K) K.heap.tcbs j.Cs j.Ω K.heap j.Sg K.heap.replies K.heap.scs K.heap.ntfns
            K.heap.scBits j.Ac s :=
        fun s hs => ioPre_userP hK hs.2.ks (pre s hs.1)
      have hIP := io_isProgOn (K := userV K.toKLayoutV) (Locks := j.Locks) (m0 := view K.toKLayout c ρ) hA
        (P := fun s => SlJAt (L := L) K.toKLayout s ∧ j.Q K.toKLayoutV (view K.toKLayout c ρ) s) pre
        (io_isProg S j.number)
      refine ⟨?_, ?_⟩
      · intro s a r hs hc hmm hr hb
        obtain ⟨hs1, hs2⟩ := hs
        have hs' : SlJAt (L := L) K.toKLayout s ∧ j.Q K.toKLayoutV (view K.toKLayout c ρ) s := hs1
        have hq : QPs K st s := hs2
        obtain ⟨b, s1, a1⟩ := r
        have hb' : b = true := hb
        subst hb'
        have hr' : syscall.handle_ioport_local st ar s a j.number = ok (true, s1, a1) := hr
        have hc' : L.cpu s = c := hc
        have hmm' : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x := hmm
        have g1 := io_acc hA (Locks := j.Locks) (pre s hs') hr'
        have g2 := io_accN hA (Locks := j.Locks) (preP s ⟨hs', hq⟩)
          (CoreView.io_narA_view (preP s ⟨hs', hq⟩) hK hc' hmm') hr'
        have e := fun (st' : machine.Store S) (N : Narrow st st') => hIP st' N s (AltOf.pre hs') a
        have w1 := (interp_guard _ s a _ ((e _ (Narrow.guard _ _ _)).symm.trans g1)).2
        have w2 := (interp_guard _ s a _ ((e _ (Narrow.guard _ _ _)).symm.trans g2)).2
        show syscall.handle_ioport_local
          (guard st (fun b => VN K c ρ b ∧ (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) s b ∨
            VKc K.toKLayout c ρ b)) (VNW K c ρ)) ar s a j.number = ok (true, s1, a1)
        exact (e _ (Narrow.guard _ _ _)).trans (guard_of_within (st := st) (L := L) (ar := ar) _ s a _
          ((e _ (Narrow.self _)).symm.trans hr')
          (Within.mono (fun b hb => ⟨hb.2.2, Or.inl ⟨hb.1, fun hq => hb.2.1.2.1 (Or.inr hq)⟩⟩)
            (fun b hb => hb.2.2) _ s a (Fl4Proofs.P2.E2E.within_and _ s a w1 w2)))
      · intro s a r hs hc hmm hr hn s' r' hA' h'
        obtain ⟨hs1, hs2⟩ := hs
        have hs' : SlJAt (L := L) K.toKLayout s ∧ j.Q K.toKLayoutV (view K.toKLayout c ρ) s := hs1
        have hq : QPs K st s := hs2
        have hc' : L.cpu s = c := hc
        have hmm' : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x := hmm
        have hAc' : PathObl.Alt st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) s)
            (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user) s s' := hA'
        have Al : PathObl.Alt st (IoRS (st := st) (userP K) j.Locks s) (OwnMap.cls (userP K))
            (OwnMap.ko (userP K) (view K.toKLayout c ρ)) (· ∈ (userP K).user) s s' :=
          ⟨hAc'.cpu, hAc'.ksb, hAc'.masks,
            fun x hx => hAc'.read x ⟨⟨hx.1, fun hu => hx.2.1 (Or.inl hu), hx.2.2⟩, fun hp => hx.2.1 (Or.inr hp)⟩,
            fun x hx hu hk => hAc'.clsEq x (fun hr => hx ⟨hr.1.1, fun hu' => Or.elim hu' hr.1.2.1 hr.2, hr.1.2.2⟩)
              (fun h => hu (Or.inl (Or.inl h))) hk⟩
        have hr' : syscall.handle_ioport_local st ar s a j.number = ok r := hr
        have h'' : syscall.handle_ioport_local st ar s' a j.number = ok r' := h'
        have hn' : r.1 ≠ true := hn
        have hRS : L.mem s (tmA (L := L) s) ≠ 0#u64 →
            rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) s
              (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64) := fun h0 =>
          ⟨(pre s hs').td (Locks := j.Locks) h0,
            fun hp => ((preP s ⟨hs', hq⟩).td (Locks := j.Locks) h0).2.1 (Or.inr hp)⟩
        exact io_decN hA (preP s ⟨hs', hq⟩) (CoreView.io_narD_view (preP s ⟨hs', hq⟩) hK hc' hmm' hRS) Al hr' hn' h''
    exact key _ _ (allA st ar hA hm hSt a0 (.io j) K (view K.toKLayout c ρ) hK hU) (SlotU.fam_pos _ _ hp)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = LocalPath.void (fl4Dflt st ar hm)
          (OwnMap.ko_aligned (regionOK_userV hK.base) (userOK_userV hK.base hU.base) (view K.toKLayout c ρ)) →
        NarrowV (K := K) (c := c) (ρ := ρ) (LocalPath.cutLiftP hK hU
          (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) := by
      rintro P W hAv rfl
      exact ⟨fun s _ _ hs => absurd hs.1 id, fun s _ _ hs => absurd hs.1 id⟩
    exact key _ _ (allA st ar hA hm hSt a0 (.io j) K (view K.toKLayout c ρ) hK hU) (dif_neg hp)

/-- **`ViewSafe`'s conclusion for every I/O port start** (module docstring §1). -/
theorem io_viewSafe (j : IoArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (ρ μ : U64 → U64) (q : SP)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (hS : StartAt (fl4LocW11JA st ar hA hm hSt a0 (.io j) K (view K.toKLayout c ρ) hK hU) c hs
      (view K.toKLayout c ρ) q) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ q :=
  CoreView.viewSafeAt_of_narrow hK hU _ (io_narrowV st ar hA hm hSt a0 j K hK hU c ρ) hV hS

end io

/-! ## U8 -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 as in U7, with `VSafe` asked only where `NoV i` holds** (module docstring §2). -/
structure Fl4StepWPRV8 (LP : PathsP ι) (NoV : ι → Prop)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : U64 → S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : U64 → S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact at `c`'s view, with `VSafe` [J] only for paths with `NoV` (in U8: the non-io
  slots). -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i, SF (Ch c) K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i ∧
        (NoV i → VSafe LP s K c k hK hU ρ i)
  /-- [P] the serial exit's ghost choice, one P3 chain per core. -/
  serX : SerStep s c → ∀ e, SerExitW P K'.toKLayoutV (Ch' e)
  /-- The glue's layout convention at the serial exit. -/
  serC : SerStep s c → K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chains change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

inductive ExecWPRV8 (LP : PathsP ι) (NoV : ι → Prop)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : U64 → S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (U64 → S → Prop) → Prop
  | refl : ExecWPRV8 LP NoV SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : U64 → S → Prop} {c : U64} :
      ExecWPRV8 LP NoV SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepWPRV8 LP NoV SF P s K Ch c s' K' Ch' →
      ExecWPRV8 LP NoV SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : U64 → S → Prop} {v a x : U64} :
      ExecWPRV8 LP NoV SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecWPRV8 LP NoV SF P s0 K0 Ch0 (hwCfg s a x) K Ch

end exec

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- The starts of the I/O port slot of U7's family. -/
def IoIx : (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.io _) => True
  | _ => False

/-- **The io starts' `VSafe`** (module docstring §2). -/
theorem vSafe_io {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (hM : MapsP K s)
    (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) (hi : IoIx (S := S) i) :
    VSafe (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st)))) s K c k hK hU ρ i := by
  rcases i with ((i | i | j | i | i | i | i) | j)
  · exact False.elim hi
  · exact False.elim hi
  · intro _ hP
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    exact io_viewSafe st ar hA (masksWr_plain st) L.total a0 j K hK hU c _ ρ s.mem k hV hP
  · exact False.elim hi
  · exact False.elim hi
  · exact False.elim hi
  · exact False.elim hi
  · exact False.elim hi

end top

end
end Fl4Proofs.P2.E2EP

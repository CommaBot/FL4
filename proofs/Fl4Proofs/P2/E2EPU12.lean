/-
# P2 (line p3mc, gen 12): U12, vmF's `VSafe9` discharged at every start

## Every vmF start of a chain (`vmF_annV_all`)
At a vmF start fact `StartV2 … (.inl (.vmF j))` of a P3 chain at core `c`'s view of `ρ`, the re-annotated body
`annV k0` is `Safe` at the physical memory. The start state `σ` of the path (`StartAt` from `startAt_UN`) has action
`RESUME_CURRENT` (`Act0V` from the chain, U12a's `vmF_act0_SF` / `act_of_view`). Then:
* **the handler of some receiving fault endpoint is another core's**: U10's `vmF_fh_annV`;
* **otherwise** (`vmF_k0_safe`, the starts of U11's item 1 included): the run from every start agreeing with `σ`
  on the aligned kernel words, and from every alternative of a declining one, is the run from `σ` on the view's
  words (`vmB_run`, P2/VmBRun: accepted by `vm_accR`, declined by `vm_local_guard_dec`), moved to those states by
  `run_transfer` / `run_transfer2`; `LocalPath.safeVQ` (P2/SafeVQ) with `Q :=` "agrees with `σ` on the aligned
  kernel words, the core, the kernel base and the frame masks" gives `Safe k0`, and `safe_narrow` `Safe (annV k0)`.
  The path's accepted-run obligations (`move`, `StepOK` under `ownP`, writes held at `μ`) are its own (`PathObl`),
  as in `viewSafeAt_of_narrow`.
The ASID words are in no region at a bundle state with the view's memory (the chain state of `StartU`:
`region_none_tab`, `SlJAtZ.pool`).

## U12
`VmFAt` (every vmF index) as the exempt set of `ExecWPRV10`: **`serializable_fl4_localU12`** (`NoV := ¬IoIx`,
`FH := VmFAt`, so `VSafe9` [J] is asked exactly where `¬IoIx ∧ ¬VmFIx`), through U12a's converter
`execPV9_of_WPRV10S`; **`serializable_fl4_localU11of12`**, **`serializable_fl4_localU12aof12`**.

## Premises of `serializable_fl4_localU12` vs `serializable_fl4_localU11`
* **Removed: `VSafe9` [J] at every vmF start** (U11 kept it at the starts of its items 1 and 2). Nothing added.
* `VSafe9` [J] stays at the vmR, sl, st, irq, vq and invocation starts; `VSafe` [J] where the armed program is the
  body itself (non-io, vmF included, unchanged); everything else as in U11.

No existing statement changed except the root import list.

Gen 48 (in place, statements unchanged): `vmF_k0_nar` (the homed branch's run facts) split out of `vmF_k0_safe`.
-/
import Fl4Proofs.P2.VmBRun
import Fl4Proofs.P2.E2EPU12a
import Fl4Proofs.P2.SafeVQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP
  xsafeRunH_inv)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD)

noncomputable section
open Classical

/-! ## Moving one guarded run -/

section move
variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}

/-- `run_transfer` with the answer kept. -/
theorem run_transfer2 (hm : E2E.MasksWr st) {F : machine.Store S → S → A → Result (X × S × A)} {p : SProg X}
    (hz : NoZero p) {G : S → Prop} (hp : IsProgOn F ar st G p) {Rd Wr : U64 → Prop}
    (hRal : ∀ w, Rd w → Aligned w) (hWal : ∀ w, Wr w → Aligned w)
    {σ s' : S} {a : A} {rσ r' : X × S × A} (hσ : G σ) (hs' : G s')
    (h1 : L.ksb s' = L.ksb σ) (h2 : L.cpu s' = L.cpu σ) (h3 : st.frame_masks s' = st.frame_masks σ)
    (h4 : ∀ w, Rd w → L.mem s' w = L.mem σ w)
    (hg : F (guard st Rd Wr) σ a = ok rσ) (hr : F st s' a = ok r') : r'.1 = rσ.1 := by
  rw [hp _ (Narrow.guard _ _ _) σ hσ a] at hg
  obtain ⟨x, s1, a1⟩ := rσ
  obtain ⟨s1', h'⟩ := interp_agree hm hRal hWal p hz σ s' a x s1 a1 h1 h2 h3 h4 hg
  have e := (interp_guard p s' a _ h').1
  rw [hp _ (Narrow.self _) s' hs' a, e] at hr
  rw [← ok_inj_ff hr]

/-- A guarded run passes a larger guard (for a path's body). -/
theorem run_mono {F : machine.Store S → S → A → Result (X × S × A)} {p : SProg X} (hz : NoZero p) {G : S → Prop}
    (hp : IsProgOn F ar st G p) {s : S} {a : A} {r : X × S × A} (hs : G s) {R W R' W' : U64 → Prop}
    (hR : ∀ q, R q → R' q) (hW : ∀ q, W q → W' q) (h : F (guard st R W) s a = ok r) :
    F (guard st R' W') s a = ok r := by
  rw [hp _ (Narrow.guard _ _ _) s hs a] at h ⊢
  exact interp_mono hR hW p hz s a r h

end move

/-! ## The vmF body at a view start -/

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

/-- The ASID words' regions at the states with the view's kernel words (module docstring). -/
def TabRV (K : KLayoutP) (c : U64) (ρ : U64 → U64) : Prop :=
  ∀ σ : S, QPs K st σ → (∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) →
    ∀ hi : U64, hi.val < 2048 → region K.toKLayout (atAF (L.ksb σ) hi) = .none ∧
      (L.mem σ (atAF (L.ksb σ) hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
        region K.toKLayout (peAF (L.mem σ (atAF (L.ksb σ) hi)) lo) = .none)

/-- `TabRV` from a bundle state with the view's kernel words. -/
theorem tabRV_of {K : KLayoutP} {c : U64} {ρ : U64 → U64} {σc : S} (hb : SlJAt (L := L) K.toKLayout σc)
    (hmc : ∀ x, Aligned x → x ∉ K.user → L.mem σc x = view K.toKLayout c ρ x) : TabRV st K c ρ := by
  intro σ hq hm hi hhi
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, Bz⟩ := hb
  rw [hq.ksb]
  refine ⟨region_none_tab Bz hhi, fun h0 lo hlo => ?_⟩
  have ha := hq.al hi hhi
  have hu : atAF K.ksb hi ∉ K.user := fun h => hq.uoff _ (Or.inl h) hi hhi rfl
  have e : L.mem σ (atAF K.ksb hi) = L.mem σc (atAF K.ksb hi) := (hm _ ha hu).trans (hmc _ ha hu).symm
  rw [e] at h0 ⊢
  exact (SlJAtZ.pool Bz hi hhi h0 lo hlo).2

variable {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`vmF_bun_SF` on the re-based platform** (gen 54, in place: `hRun : ChainRun` for `P` / `hIoa`). -/
theorem vmF_bun_SF_C {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} (hRun : ChainRun st arI AR MR)
    {Ch : S → Prop} {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    {ρ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : VmFArg S}
    (h : StartV2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.inl (.vmF j))) :
    TabRV st K c ρ := by
  have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.vmF j) := h
  have hSU := startU_of_U2 st ar hA a0 hC nv h'
  obtain ⟨q0, ⟨hB, σ, ⟨hCσ, hE⟩, hG⟩, -⟩ := hSU
  obtain ⟨σe, hC'⟩ := hC
  have hpa : VmFPremA st ar j K.toKLayoutV :=
    hB.toA hA ((hE.toJ12 st ar).toJ10 st ar hA (hRun hC' hCσ hE.hct))
  obtain ⟨σ', a', e', hc, -, hμ, -⟩ := hG hpa
  subst e'
  exact tabRV_of st (ChainOf.bun hC' _ hCσ) (fun x hx hu => hμ x hx hu)

/-- **A bundle state with the view's kernel words** at a vmF start fact of a chain (`vmF_act0_SF`'s witness). -/
theorem vmF_bun_SF {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Ch : S → Prop} {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    {ρ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : VmFArg S}
    (h : StartV2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.inl (.vmF j))) :
    TabRV st K c ρ :=
  vmF_bun_SF_C st ar hA a0 (chainRun_of P hIoa) hC nv h

set_option maxHeartbeats 4000000 in
/-- **vmF's narrowed runs at a view start with action 0 whose fault handler is homed wherever reached** (split out
of `vmF_k0_safe`'s proof in place, gen 48): the run facts `LocalPath.safeVQ` asks (`VQNar`), for the vmF path at the
view, the start states agreeing with `σ` on the core, the kernel base, the frame masks and the aligned kernel
words. -/
theorem vmF_k0_nar (j : VmFArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (ρ : U64 → U64)
    (hLk : LkC j.Locks) (h0 : Act0V st K c ρ) (hTR : TabRV st K c ρ)
    (hp : (vmFSlotA st ar hA (masksWr_plain st)).Prem j K.toKLayoutV (view K.toKLayout c ρ))
    (W : NoVcpuRW K.toKLayoutV
      ((vmFSlotA st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp))
    (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base
      ((vmFSlotA st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp) W)
        (noVcpuRd_atV hK.base _ W)).rJ K (fun b hb => Or.inl hb)))
    (σ : S) (a : A)
    (hpre : (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv).Pre σ)
    (hc' : L.cpu σ = c) (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    {n : U64} {a2 : A} (eu : sched.update_timestamp st ar σ a = ok (utW (L := L) σ n, a2))
    (hB : ∀ sl ptr badge x' y g gr, obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
      obj.Slot.cap st sl (utW (L := L) σ n) = ok (capability.Cap.Endpoint ptr badge x' y g gr) →
      L.epState (utW (L := L) σ n) ptr = obj.EP_RECV →
      ρ (affA (L.mem (utW (L := L) σ n) (epHeadA ptr))) = c) :
    (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv).VQNar σ a
      (view K.toKLayout c ρ)
      (fun s0 b => VN K c ρ b ∧
        (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) s0 b ∨ VKc K.toKLayout c ρ b))
      (fun _ => VNW K c ρ)
      (fun s0 => L.cpu s0 = L.cpu σ ∧ L.ksb s0 = L.ksb σ ∧ st.frame_masks s0 = st.frame_masks σ ∧
        ∀ x, Aligned x → x ∉ K.user → L.mem s0 x = L.mem σ x) := by
  obtain ⟨⟨hP, -⟩, hq⟩ := id hpre
  have hP' : VmPre st ar (userV K.toKLayoutV) j.T j.Cs j.Ω j.U j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.Locks σ := hP
  have hq' : QPs K st σ := hq
  have B := hP'.1.base
  have hact : L.actionW σ = 0#u64 := act_of_view B hq'.ksb hc' hmm h0
  obtain ⟨Rd, Wr, rσ, hRd, hWr, hDec, hrσ, hgσ⟩ := vmB_run hA hK (addr := j.addr) (code := j.code) (a := a)
    hP' hq' hc' hmm hact eu hB (hTR σ hq' hmm)
  -- the read set's congruence between `σ` and a state agreeing with it on the aligned kernel words
  have eL : ∀ s0 : S, j.Locks s0 = j.Locks σ := by
    intro s0; obtain ⟨X, hX⟩ := hLk; rw [hX]
  have rsOf : ∀ (s0 : S), L.cpu s0 = L.cpu σ → (∀ x, Aligned x → x ∉ K.user → L.mem s0 x = L.mem σ x) →
      ∀ b, IoRS (st := st) (userP K) j.Locks σ b →
        rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) s0 b := by
    intro s0 hcp hmem b hb
    obtain ⟨h1, h2⟩ := ioRS_of_userP hb
    have eown : OwnMap.own (userV K.toKLayoutV) (L.mem s0) = OwnMap.own (userV K.toKLayoutV) (L.mem σ) :=
      E2E.ownDep (regionOK_userV hK.base) (userOK_userV hK.base hU.base) _ _
        (fun x hx hu => hmem x hx (fun h => hu (mem_userV.2 (Or.inl h))))
    refine ⟨⟨h1.1, h1.2.1, ?_⟩, h2⟩
    have e2 : RPerm (OwnMap.own (userV K.toKLayoutV)) (L.cpu s0) (j.Locks s0) (L.mem s0) b =
        RPerm (OwnMap.own (userV K.toKLayoutV)) (L.cpu σ) (j.Locks σ) (L.mem σ) b := by
      unfold RPerm GateOnly; rw [hcp, eL s0, eown]
    show RPerm (OwnMap.own (userV K.toKLayoutV)) (L.cpu s0) (j.Locks s0) (L.mem s0) b
    rw [e2]; exact h1.2.2
  have hRal : ∀ w, Rd w → Aligned w := fun w hw => (hRd w hw).1
  have hWal : ∀ w, Wr w → Aligned w := fun w hw => (hWr w hw).1
  have hz := vm_noZero j.addr j.code
  unfold Fl4Proofs.P2.E2E.LocalPath.VQNar
  refine ⟨?_, ?_⟩
  · -- accepted (and declined) starts agreeing with `σ`
    intro s0 r hpre0 hQ0 _ _ hrun0 _
    have g := E2E.run_transfer (st := st) (masksWr_plain st) hz
      (IsProg.on (vm_isProg S j.addr j.code) ar st (fun _ => True))
      hRal hWal trivial (trivial) hQ0.2.1 hQ0.1 hQ0.2.2.1
      (fun w hw => hQ0.2.2.2 w (hRd w hw).1 (hRd w hw).2.1) hgσ hrun0
    refine run_mono (st := st) hz
      (IsProg.on (vm_isProg S j.addr j.code) ar st (fun _ => True))
      (trivial) (fun q hq0 => ⟨(hRd q hq0).2.2.1, ?_⟩) (fun q hq0 => (hWr q hq0).2) g
    rcases (hRd q hq0).2.2.2 with h | h
    · exact Or.inl (rsOf s0 hQ0.1 hQ0.2.2.2 q h)
    · exact Or.inr h
  · -- the alternatives of a declining start agreeing with `σ`
    intro s0 r hpre0 hQ0 _ _ hrun0 hdec0 s' r' hAlt0 hrun'
    have hAlt : Alt st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) s0)
        (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user) s0 s' := hAlt0
    by_cases hσa : rσ.1 = true
    · exfalso
      apply hdec0
      have e := run_transfer2 (st := st) (masksWr_plain st) hz
        (IsProg.on (vm_isProg S j.addr j.code) ar st (fun _ => True))
        hRal hWal trivial (trivial) hQ0.2.1 hQ0.1 hQ0.2.2.1
        (fun w hw => hQ0.2.2.2 w (hRd w hw).1 (hRd w hw).2.1) hgσ hrun0
      show r.1 = true
      rw [e]; exact hσa
    · have hio := hDec hσa
      have hag : ∀ w, Rd w → L.mem s' w = L.mem σ w := fun w hw =>
        (hAlt.read w (rsOf s0 hQ0.1 hQ0.2.2.2 w (hio w hw))).trans
          (hQ0.2.2.2 w (hRd w hw).1 (hRd w hw).2.1)
      have g := E2E.run_transfer (st := st) (masksWr_plain st) hz
        (IsProg.on (vm_isProg S j.addr j.code) ar st (fun _ => True))
        hRal hWal trivial trivial (hAlt.ksb.trans hQ0.2.1)
        (hAlt.cpu.trans hQ0.1) (hAlt.masks.trans hQ0.2.2.1) hag hgσ hrun'
      refine run_mono (st := st) hz
        (IsProg.on (vm_isProg S j.addr j.code) ar st (fun _ => True))
        trivial (fun q hq0 => ⟨(hRd q hq0).2.2.1, Or.inl (rsOf s0 hQ0.1 hQ0.2.2.2 q (hio q hq0))⟩)
        (fun q hq0 => (hWr q hq0).2) g

set_option maxHeartbeats 8000000 in
/-- **The vmF body is `Safe` at every view start with action 0** (module docstring). -/
theorem vmF_k0_safe (j : VmFArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (hLk : LkC j.Locks) (h0 : Act0V st K c ρ) (hTR : TabRV st K c ρ)
    (hS : StartAt (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0 (.vmF j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
  have hK0 := hK.base.base
  have hko := Fl4Proofs.P2.CoreView.ko_of_veq hK hV
  by_cases hp : (vmFSlotA st ar hA (masksWr_plain st)).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = (vmFSlotA st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      have hpr : VmFPremA st ar j K.toKLayoutV := hp
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      obtain ⟨⟨hP, -⟩, hq⟩ := id hpre
      have hP' : VmPre st ar (userV K.toKLayoutV) j.T j.Cs j.Ω j.U j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.Locks σ := hP
      have hq' : QPs K st σ := hq
      have hc' : L.cpu σ = c := hc
      have hl' : j.Locks σ = hs := hl
      have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
      have B := hP'.1.base
      have hact : L.actionW σ = 0#u64 := act_of_view B hq'.ksb hc' hmm h0
      obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
      have eu : sched.update_timestamp st ar σ a = ok (utW (L := L) σ n, a2) := update_timestamp_ok ar B.np hn
      by_cases hB : ∀ sl ptr badge x' y g gr, obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
          obj.Slot.cap st sl (utW (L := L) σ n) = ok (capability.Cap.Endpoint ptr badge x' y g gr) →
          L.epState (utW (L := L) σ n) ptr = obj.EP_RECV →
          ρ (affA (L.mem (utW (L := L) σ n) (epHeadA ptr))) = c
      · -- the handler homed wherever it is reached: one run for every agreeing state
        refine Fl4Proofs.P2.Serial.safe_narrow _ ?_ ∅
        obtain ⟨hNA, hND⟩ := vmF_k0_nar st ar hA j K hK hU c ρ hLk h0 hTR hp W hAv σ a hpre hc' hmm eu hB
        have := E2E.LocalPath.safeVQ
          (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv)
          (moveHeldP hK) (ownDepP hK hU) (ρv := view K.toKLayout c ρ) (ρ := ρ) (μ := μ) (σ := σ) (a := a)
          hpre hμ (by rw [hc, hl]; exact hV)
          (N := VN K c ρ) (Kc := VKc K.toKLayout c ρ) (NW := VNW K c ρ) (DD := VDD K.toKLayout c ρ)
          (fun x h => h.1) (fun x h => h.2) (fun x h => by rw [hko]; exact h) (fun x h => ⟨h.1, h.2.1⟩)
          (fun m m' h y hy => Fl4Proofs.P2.CoreView.vown_off hK hU m m' h y hy)
          (fun q hq m v y hy => Fl4Proofs.P2.CoreView.vown_upd hK hq.2.2 m v y hy)
          (NR := fun s0 b => VN K c ρ b ∧
            (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) s0 b ∨ VKc K.toKLayout c ρ b))
          (NWs := fun _ => VNW K c ρ) (fun _ _ h => h) (fun _ _ h => h)
          (fun s0 => L.cpu s0 = L.cpu σ ∧ L.ksb s0 = L.ksb σ ∧ st.frame_masks s0 = st.frame_masks σ ∧
            ∀ x, Aligned x → x ∉ K.user → L.mem s0 x = L.mem σ x)
          ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
          (fun s b v _ hQ hu hb => by
            refine ⟨(L.cpu_wr s b v).trans hQ.1, (L.ksb_wr s b v).trans hQ.2.1,
              (masksWr_plain st s b v).trans hQ.2.2.1, fun x hx hu' => ?_⟩
            exact (mem_wr_ne' (L := L) hb hx (fun e => hu' (e ▸ hu))).trans (hQ.2.2.2 x hx hu'))
          hNA hND
        rw [hc, hl] at this; exact this
      · -- a receiving fault endpoint's head is another core's: U10's decline split
        push_neg at hB
        obtain ⟨sl, ptr, badge, x', y, g, gr, hsl, hcap, hst, hρd⟩ := hB
        have h := vmF_fh_annV (addr := j.addr) (code := j.code) hA (masksWr_plain st) hK hU hpr.nv
          ⟨hpr.lay.slot8, hpr.lay.tcb, hpr.lay.ntfn8, hpr.lay.sc8⟩ hV hP' hq' hc' hl' hmm hact eu hsl hcap hst hρd
        convert h using 2
        unfold LocalPath.body
        rw [hc]
        all_goals rfl
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmF j) K (view K.toKLayout c ρ) hK hU)
      (SlotU.fam_pos _ _ hp) hS
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = LocalPath.void (fl4Dflt st ar (masksWr_plain st))
          (OwnMap.ko_aligned (regionOK_userV hK.base) (userOK_userV hK.base hU.base) (view K.toKLayout c ρ)) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, -⟩ := hS'
      exact absurd hpre.1 id
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmF j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

end body

/-! ## Every vmF start -/

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- The vmF indices. -/
def VmFIx : (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.vmF _) => True
  | _ => False

/-- **The exempt starts of U12: every vmF start.** -/
def VmFAt (_K : KLayoutP) (_c : U64) (_hs : U64 → Prop) (_ρ : U64 → U64) (_k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop := VmFIx i

/-- **`vmF_annV_all` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem vmF_annV_all_C (P : LocPlatCR st arI AR MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) (hf : VmFIx (S := S) i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  have nv : K.vcpus = ∅ := by
    obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
    exact nv
  rcases i with ((j | j | j | j | j | j | j) | j)
  · have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
        (.vmF j) := hsf
    have hS := startAt_UN_C st ar hA (masksWr_plain st) L.total a0 P.run
      (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE (startU_of_U2 st ar hA a0 hC nv h')
    have h0 := vmF_act0_SF_C st ar hA a0 P hC nv hsf
    have hTR := vmF_bun_SF_C st ar hA a0 P.run hC nv hsf
    have hLk : LkC j.Locks := h'.1
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    exact vmF_k0_safe st ar hA a0 j K hK hU c _ ρ s.mem k hV hLk h0 hTR hS
  all_goals exact False.elim hf

end all

/-! ## U12 -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP

/-
# P2 (line p3mc, gen 14): U14, vmR's `VSafe9` discharged at every start

## Every vmR start of a chain (`vmR_annV_all`)
At a vmR start fact `StartV2 … (.inl (.vmR j))` of a P3 chain at core `c`'s view of `ρ`, the re-annotated body
`annV k0` is `Safe` at the physical memory. The start state `σ` of the path (`StartAt` from `startAt_UN`) has action
`RESUME_CURRENT` (`vmR_act0_SF`, U13). Then:
* **the reply object names a thread homed on another core** (`RFH`): U13's `vmR_k0_fh`;
* **otherwise** (no receiver, or one homed on `c`; `vmR_k0_safe`): the run from every start agreeing with `σ` on the
  aligned kernel words, and from every alternative of a declining one, is the run from `σ` on the view's words
  (`rrB_run`, P2/RrBRun: accepted by `rr_accR` with the record `rr_narA_view`, declined by `rr_local_guard_dec`),
  moved to those states by `run_transfer` / `run_transfer2`; `LocalPath.safeVQ` gives `Safe k0` and `safe_narrow`
  `Safe (annV k0)`, as `vmF_k0_safe` (U12) does for vmF.
The ASID words are in no region at the chain state of `StartU` (`vmR_bun_SF`, as `vmF_bun_SF`).

## U14
`U14At := VmFAt ∨ VmRAt` (every vmF and every vmR index) as the exempt set of `ExecWPRV10`:
**`serializable_fl4_localU14`** (`NoV := ¬IoIx`, `FH := U14At`, so `VSafe9` [J] is asked exactly where
`¬IoIx ∧ ¬VmFIx ∧ ¬VmRIx`), through U12a's converter `execPV9_of_WPRV10S`; **`serializable_fl4_localU13of14`**.

## Premises of `serializable_fl4_localU14` vs `serializable_fl4_localU13`
* **Removed: `VSafe9` [J] at the vmR starts without `RFH`** (no receiver, or the receiver homed on `c`), so with
  U13 at every vmR start. Nothing added.
* `VSafe9` [J] stays at the sl, st, irq, vq and invocation starts; `VSafe` [J] where the armed program is the body
  itself (unchanged); everything else as in U13.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.RrBRun
import Fl4Proofs.P2.E2EPU13
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

/-! ## The ASID words at a vmR start -/

section bun
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **A bundle state with the view's kernel words** at a vmR start fact of a chain (`vmR_act0_SF`'s witness). -/
theorem vmR_bun_SF {Ch : S → Prop}
    {K : KLayoutP} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    {ρ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP} {j : VmRArg S}
    (h : StartV2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.inl (.vmR j))) :
    TabRV st K c ρ := by
  have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c hs q (.vmR j) := h
  obtain ⟨q0, ⟨hL, σ, ⟨hCσ, hE⟩, hG⟩, -⟩ := h'
  obtain ⟨σe, hC'⟩ := hC
  obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, B, -⟩ := hE.ix.ac
  have hR : VmRPremA st j K.toKLayoutV :=
    ⟨nv, ⟨σ, by rw [userV_empty nv]; exact ChainOf.bun hC' σ hCσ⟩, B.csLt, fun s _ => hL.kernDetAt _ s⟩
  obtain ⟨σ', a'', e', hc, -, hμ, -⟩ := hG hR
  subst e'
  exact tabRV_of st (ChainOf.bun hC' _ hCσ) (fun x hx hu => hμ x hx hu)

end bun

/-! ## The vmR body at a view start -/

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

set_option maxHeartbeats 8000000 in
/-- **The vmR body is `Safe` at every view start with action 0** (module docstring). -/
theorem vmR_k0_safe (j : VmRArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (hLk : LkC j.Locks) (h0 : Act0V st K c ρ) (hTR : TabRV st K c ρ)
    (hS : StartAt (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
  by_cases hF : RFH K c ρ j
  · exact vmR_k0_fh st ar hA a0 j K hK hU c hs ρ μ k0 hV h0 hF hS
  have hBv : view K.toKLayout c ρ (rTcbA j.rptr) ≠ 0#u64 →
      ρ (affA (view K.toKLayout c ρ (rTcbA j.rptr))) = c := fun h1 => by
    by_contra h2; exact hF ⟨h1, h2⟩
  have hko := Fl4Proofs.P2.CoreView.ko_of_veq hK hV
  by_cases hp : (vmRSlotA st ar hA (masksWr_plain st)).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = (vmRSlotA st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      obtain ⟨⟨hP, -⟩, hq⟩ := id hpre
      have hP' : VmRRPreJ st ar (userV K.toKLayoutV) (userV K.toKLayoutV).heap.tcbs j.Cs j.Ω j.Sg
          (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits j.Ac
          j.Locks j.rptr j.ep σ := hP
      have hq' : QPs K st σ := hq
      have hc' : L.cpu σ = c := hc
      have hl' : j.Locks σ = hs := hl
      have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
      obtain ⟨Q, hrR, hpE, hTab⟩ := VmRRPreJ.pre hP'
      have B := Q.base
      have hact : L.actionW σ = 0#u64 := act_of_view B hq'.ksb hc' hmm h0
      -- the reply's `TCB` word is a kernel word
      have rp := B.bxi.2.2.1.1.rp j.rptr hrR
      have hrK := Q.hRp j.rptr hrR
      have hrt : IoRS (st := st) (userV K.toKLayoutV) j.Locks σ (rTcbA j.rptr) := by
        have h := rTcbA_val0 j.rptr; have := rp.1; have := rp.2
        exact (B.reply (Locks := j.Locks) hrK (b := rTcbA j.rptr) ⟨by omega, by omega⟩
          (by unfold Aligned; omega) Q.lk.1).1
      have eu : L.mem σ (rTcbA j.rptr) = view K.toKLayout c ρ (rTcbA j.rptr) :=
        hmm _ hrt.1 (fun hu => hrt.2.1 (mem_userV.2 (Or.inl hu)))
      have hH : L.mem σ (rTcbA j.rptr) ≠ 0#u64 → ρ (affA (L.mem σ (rTcbA j.rptr))) = c := by
        rw [eu]; exact hBv
      obtain ⟨Rd, Wr, rσ, hRd, hWr, hDec, hrσ, hgσ⟩ := rrB_run hA hK (a := a) Q hrR hpE hTab hq' hc' hmm hact hH
        (hTR σ hq' hmm)
      refine Fl4Proofs.P2.Serial.safe_narrow _ ?_ ∅
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
      have hz := rr_noZero j.rptr j.ep
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
        ?_ ?_
      · rw [hc, hl] at this; exact this
      · -- accepted (and declined) starts agreeing with `σ`
        intro s0 r hpre0 hQ0 _ _ hrun0 _
        have g := E2E.run_transfer (st := st) (masksWr_plain st) hz
          (IsProg.on (rr_isProg S j.rptr j.ep) ar st (fun _ => True))
          hRal hWal trivial (trivial) hQ0.2.1 hQ0.1 hQ0.2.2.1
          (fun w hw => hQ0.2.2.2 w (hRd w hw).1 (hRd w hw).2.1) hgσ hrun0
        refine run_mono (st := st) hz
          (IsProg.on (rr_isProg S j.rptr j.ep) ar st (fun _ => True))
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
            (IsProg.on (rr_isProg S j.rptr j.ep) ar st (fun _ => True))
            hRal hWal trivial (trivial) hQ0.2.1 hQ0.1 hQ0.2.2.1
            (fun w hw => hQ0.2.2.2 w (hRd w hw).1 (hRd w hw).2.1) hgσ hrun0
          show r.1 = true
          rw [e]; exact hσa
        · have hio := hDec hσa
          have hag : ∀ w, Rd w → L.mem s' w = L.mem σ w := fun w hw =>
            (hAlt.read w (rsOf s0 hQ0.1 hQ0.2.2.2 w (hio w hw))).trans
              (hQ0.2.2.2 w (hRd w hw).1 (hRd w hw).2.1)
          have g := E2E.run_transfer (st := st) (masksWr_plain st) hz
            (IsProg.on (rr_isProg S j.rptr j.ep) ar st (fun _ => True))
            hRal hWal trivial trivial (hAlt.ksb.trans hQ0.2.1)
            (hAlt.cpu.trans hQ0.1) (hAlt.masks.trans hQ0.2.2.1) hag hgσ hrun'
          refine run_mono (st := st) hz
            (IsProg.on (rr_isProg S j.rptr j.ep) ar st (fun _ => True))
            trivial (fun q hq0 => ⟨(hRd q hq0).2.2.1, Or.inl (rsOf s0 hQ0.1 hQ0.2.2.2 q (hio q hq0))⟩)
            (fun q hq0 => (hWr q hq0).2) g
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
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
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

end body

/-! ## Every vmR start -/

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- The vmR indices. -/
def VmRIx : (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.vmR _) => True
  | _ => False

/-- **Every vmR start.** -/
def VmRAt (_K : KLayoutP) (_c : U64) (_hs : U64 → Prop) (_ρ : U64 → U64) (_k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop := VmRIx i

/-- **The exempt starts of U14**: every vmF and every vmR start. -/
def U14At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  VmFAt (S := S) K c hs ρ k0 i ∨ VmRAt (S := S) K c hs ρ k0 i

/-- **U9's re-annotated body is `Safe` at every vmR start of a chain** (module docstring). -/
theorem vmR_annV_all (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) (hf : VmRIx (S := S) i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  have nv : K.vcpus = ∅ := by
    obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
    exact nv
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
        (.vmR j) := hsf
    have hS := startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa
      (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE (startU_of_U2 st ar hA a0 hC nv h')
    have h0 := vmR_act0_SF st ar hA a0 P hIoa hC nv hsf
    have hTR := vmR_bun_SF st ar hA a0 hC nv hsf
    have hLk : LkC j.Locks := by
      obtain ⟨q0, ⟨hL, -⟩, -⟩ := h'
      exact hL
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    exact vmR_k0_safe st ar hA a0 j K hK hU c _ ρ s.mem k hV hLk h0 hTR hS
  all_goals exact False.elim hf

end all

/-! ## U14 -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end, U13 with vmR's `VSafe9` discharged at every start** (module docstring): `VSafe9` [J] is asked
only at starts that are neither io, nor vmF, nor vmR. The conclusion is about the physical memory. -/
theorem serializable_fl4_localU14 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U14At (S := S)) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  refine serializable_e2ePV9 _ h0 hA0 hK0 hU0 hM0 (execPV9_of_WPRV10S ?_ ?_ ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  · intro Ch K s hK hU c hs q i hC hE hsf
    have nv : K.vcpus = ∅ := by
      obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
      exact nv
    rcases i with i | ((j | j) | j)
    · exact startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa hC hE (startU_of_U2 st ar hA a0 hC nv hsf)
    · exact delPteStart_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact invStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact cmStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · intro s K hK hU c k ρ i hM hV hn
    exact vSafe_io st ar hA a0 hM hV (not_not.mp hn)
  · intro Ch s K hK hU c k ρ i hC hE hsf hM hV hf
    rcases hf with hf | hf
    · exact vmF_annV_all st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact vmR_annV_all st ar hA a0 P hIoa hC hE hsf hM hV hf

/-- **U13 follows from U14** (every U13 execution is a U14 one). -/
theorem serializable_fl4_localU13of14 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U13At (S := S)) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_fl4_localU14 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    (execWPRV10_mono (fun _ _ _ _ _ i hf => ?_) h) hq
  rcases hf with hf | hf
  · exact Or.inl hf
  · right
    rcases i with ((j | j | j | j | j | j | j) | j)
    all_goals first | trivial | exact False.elim hf

end top

end
end Fl4Proofs.P2.E2EP

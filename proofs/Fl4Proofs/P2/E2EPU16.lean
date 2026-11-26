/-
# P2 (line p3mc, gen 17): U16, sl's `VSafe9` discharged at every sl start (over `fl4LocW11JB`)

## The family
`fl4LocW11JB` (P2/SlFamB): `fl4LocW11JA` with the sl slot's program the extracted tree
`R.syscall.handle_syscall_local n found` instead of `Classical.choose` of a proof that some tree has `IsProg` /
`NoZero` / `ReadOnce` (`slSlotB_path`, `fl4LocW11JB_eq`: nothing else differs). Start facts `StartV2B` [P]: `StartV2`
with the sl glue about that tree's body.

## The sl starts
* **homed** (`SlHome`): **`sl_k0_safeB`**, U15's `sl_k0_safe` verbatim over the new family (`safeVQ` with the path's
  own `ReadOnce`, `sl_acc_v`, `sl_dec_v` + `run_transfer`).
* **foreign** (`¬ SlHome`: the decided thread is live and another core's in `ρ`): **`sl_k0_fhB`**. At the start `σ`
  (`SlJAt`, `SlQ`, `QPs`, the view's kernel words, core `c`) `SlOF` (`slOF_of`), `SlVC` (`slVC_of`, from the chain's
  `SlV0`) and p3mc16's decline certificate `sl_fh_annV` give `Safe` of U9's re-annotated body: the armed program is
  now the extracted tree, so the certificate is about it. (The real run there declines after the prefix writes
  `FAULT_IP`, `CUR_TIME`, `CONSUMED`, reading the decided thread's home-owned words at most once each.)

## U16
`SlAllAt` (every sl start), `U16At := U14At ∨ SlAllAt`; **`sl_annV_allB`**; **`serializable_fl4_localU16`**
(`ExecWPRV10 (fl4LocW11JB ⊕ invocations) (¬IoIx) U16At StartV2B`); **`serializable_fl4_localU15of16`**: U15's
statement over the new family (`U15At`, `StartV2B`) follows from U16.

## Premises of `serializable_fl4_localU16` vs `serializable_fl4_localU15`
* **Removed: `VSafe9` [J] at the sl starts without `SlHome`.** With U15's homed case, `VSafe9` is discharged at
  **every** sl start. Nothing added.
* **Changed: the family and the start fact.** `fl4LocW11JA` / `StartV2` [P] become `fl4LocW11JB` / `StartV2B` [P]: the
  sl slot's program and its glue are the extracted tree's (the reading `IsProg` [P] always stated in its docstring),
  not an unnamed `choose` witness. Every other slot, record and clause is the same (`fl4LocW11JB_eq`, `StartU2B`'s
  wildcard). `serializable_fl4_localU15` (over `fl4LocW11JA`) is not derived from U16: an execution of the old
  family arms `choose`'s tree, which is not provably the extracted one, so it is not an execution of the new family.
* `VSafe9` [J] stays at st, irq, vq and invocation starts; `VSafe` [J] unchanged.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.SlFamB
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

/-! ## The sl body at a view start of the new family -/

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

set_option maxHeartbeats 8000000 in
/-- **The sl body is `Safe` at every view start whose decided thread is homed** (module docstring). -/
theorem sl_k0_safeB (j : SlArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (h0 : SlV0 st K c ρ) (hH : SlHome st K c ρ j)
    (hS : StartAt (fl4LocW11JB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
  have hko := Fl4Proofs.P2.CoreView.ko_of_veq hK hV
  -- every start state at the view sees the decided thread homed
  have HH : ∀ s0 : S, (F0 : SlOF (st := st) ar K.toKLayout j.Locks (view K.toKLayout c ρ) j.n j.found j.Cs j.Ω j.Sg
      j.Ac s0) → QPs K st s0 → L.cpu s0 = c →
      (∀ x, Aligned x → x ∉ K.user → L.mem s0 x = view K.toKLayout c ρ x) →
      SlLive st j.found.1 s0 → ρ (fld (slThr st j.found.1 s0) oAFFINITY) = c := by
    intro s0 F0 hq0 hc0 hm0 lv
    obtain ⟨σ', hc', hk', hm', hh'⟩ := hH
    have G : Ag st (NU K.toKLayout) s0 σ' :=
      ⟨hk'.trans hq0.ksb.symm, hc'.trans hc0.symm, fun b hb => (hm' b hb.1 hb.2).trans (hm0 b hb.1 hb.2).symm⟩
    have hrp : ¬ SlTrap st s0 → NU K.toKLayout (rTcbA j.found.1) := fun hS0 =>
      nu_rp F0.B.regionOKX (F0.B.rrG F0.C.fd hS0 (F0.C.arm hS0)).1 (o := layout.reply.TCB)
        (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
    obtain ⟨e1, e2⟩ := slThr_ag F0.B F0.E.hN F0.E.hSt.1 hrp G
    rw [← e1]; exact hh' (e2.2 lv)
  by_cases hp : (slSlotB st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user)) (W : AvoidV K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.cutLiftV hK.base hU.base
          (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv (view K.toKLayout c ρ)) P W).rJ K (fun b hb => Or.inl hb))),
        P = (slSlotB st ar hA (masksWr_plain st) L.total a0).path j K.toKLayoutV (view K.toKLayout c ρ)
          hK.base hU.base hp →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      have hc' : L.cpu σ = c := hc
      have hl' : j.Locks σ = hs := hl
      refine Fl4Proofs.P2.Serial.safe_narrow _ ?_ ∅
      have hz := sl_noZero j.n j.found
      have hPg := IsProg.on (sl_isProg S j.n j.found) ar st (fun _ => True)
      -- the facts at a start state
      have At : ∀ s0 : S, (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv).Pre s0 →
          L.cpu s0 = c → (∀ x, Aligned x → x ∉ K.user → L.mem s0 x = view K.toKLayout c ρ x) →
          ∃ F0 : SlOF (st := st) ar K.toKLayout j.Locks (view K.toKLayout c ρ) j.n j.found j.Cs j.Ω j.Sg j.Ac s0,
            SlVC (L := L) K c ρ s0 ∧
            (SlLive st j.found.1 s0 → ρ (fld (slThr st j.found.1 s0) oAFFINITY) = c) := by
        intro s0 hpre0 hc0 hm0
        obtain ⟨⟨hJ0, hq0⟩, hQP0⟩ := id hpre0
        have hJ0' : SlJAt (L := L) K.toKLayout s0 := hJ0
        have hq0' : Fl4Proofs.P2.PathObl.SlQ st ar j.Locks j.n j.found j.Cs j.Ω j.Sg j.Ac K.toKLayout (view K.toKLayout c ρ) s0 := hq0
        have hQP0' : QPs K st s0 := hQP0
        have F0 := slOF_of ar L.total hA a0 hJ0' hq0'
        exact ⟨F0, slVC_of ar nv hK hU F0 hQP0' hc0 hm0 h0, HH s0 F0 hQP0' hc0 hm0⟩
      have := E2E.LocalPath.safeVQ
        (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv)
        (moveHeldP hK) (ownDepP hK hU) (ρv := view K.toKLayout c ρ) (ρ := ρ) (μ := μ) (σ := σ) (a := a)
        hpre hμ (by rw [hc, hl]; exact hV)
        (N := VN K c ρ) (Kc := VKc K.toKLayout c ρ) (NW := VNW K c ρ) (DD := VDD K.toKLayout c ρ)
        (fun x h => h.1) (fun x h => h.2) (fun x h => by rw [hko]; exact h) (fun x h => ⟨h.1, h.2.1⟩)
        (fun m m' h y hy => Fl4Proofs.P2.CoreView.vown_off hK hU m m' h y hy)
        (fun q hq m v y hy => Fl4Proofs.P2.CoreView.vown_upd hK hq.2.2 m v y hy)
        (NR := fun s0 b => VN K c ρ b ∧
          (rsE (· ∈ K.ptes) (rsV K.toKLayoutV (SlRS (st := st) K.toKLayout j.Locks)) s0 b ∨ VKc K.toKLayout c ρ b))
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
      · -- accepted runs, at each start agreeing with `σ`
        intro s0 r hpre0 _ hc0 hρ0 hrun0 hacc0
        obtain ⟨F0, V0, hH0⟩ := At s0 hpre0 (hc0.trans hc') hρ0
        obtain ⟨b, s1, a1⟩ := r
        have hb : b = true := hacc0
        subst hb
        have hr0 : syscall.handle_syscall_local st ar s0 a j.n j.found = ok (true, s1, a1) := hrun0
        have g := sl_acc_v ar hA F0 V0 hH0 hr0
        exact run_mono (st := st) hz hPg trivial
          (fun q hq => ⟨hq.2.1, Or.inl ⟨⟨hq.1, not_vData_empty nv⟩, hq.2.2⟩⟩) (fun q hq => hq.2) g
      · -- declined runs, at every alternative of each start agreeing with `σ`
        intro s0 r hpre0 _ hc0 hρ0 hrun0 hdec0 s' r' hAlt0 hrun'
        obtain ⟨F0, V0, hH0⟩ := At s0 hpre0 (hc0.trans hc') hρ0
        have hr0 : syscall.handle_syscall_local st ar s0 a j.n j.found = ok r := hrun0
        have hAlt : Alt st (rsE (· ∈ K.ptes) (rsV K.toKLayoutV (SlRS (st := st) K.toKLayout j.Locks)) s0)
            (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user) s0 s' := hAlt0
        have g0 := sl_dec_v ar hA F0 V0 hH0 hr0 hdec0
        have PA := preAcc_v ar V0 F0.B F0.E
        have g := E2E.run_transfer (st := st) (masksWr_plain st) hz hPg
          (fun w hw => hw.1.1) (fun w hw => (SlDS.ws F0.P.preG hw.1).1) trivial trivial hAlt.ksb hAlt.cpu
          hAlt.masks (fun w hw => hAlt.read w ⟨⟨hw.1, not_vData_empty nv⟩, hw.2.2⟩) g0 hrun'
        refine run_mono (st := st) hz hPg trivial
          (fun q hq => ⟨hq.2.1, Or.inl ⟨⟨hq.1, not_vData_empty nv⟩, hq.2.2⟩⟩) (fun q hq => ?_) g
        rcases hq.1 with rfl | rfl | rfl
        · exact PA.fi
        · exact (PA.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2
        · exact (PA.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2
    exact key _ _ (allB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      (SlotC.fam_pos _ _ hp) hS
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user)) (W : AvoidV K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.cutLiftV hK.base hU.base
          (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv (view K.toKLayout c ρ)) P W).rJ K (fun b hb => Or.inl hb))),
        P = LocalPath.void (fl4Dflt st ar (masksWr_plain st)) (OwnMap.ko_aligned hK.base.base hU.base.base
          (view K.toKLayout c ρ)) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, -⟩ := hS'
      exact absurd hpre.1 id
    exact key _ _ (allB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

set_option maxHeartbeats 8000000 in
/-- **The sl body is `Safe` at every view start whose decided thread is not homed** (module docstring). -/
theorem sl_k0_fhB (j : SlArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (h0 : SlV0 st K c ρ) (hF : ¬ SlHome st K c ρ j)
    (hS : StartAt (fl4LocW11JB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
  by_cases hp : (slSlotB st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user)) (W : AvoidV K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.cutLiftV hK.base hU.base
          (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv (view K.toKLayout c ρ)) P W).rJ K (fun b hb => Or.inl hb))),
        P = (slSlotB st ar hA (masksWr_plain st) L.total a0).path j K.toKLayoutV (view K.toKLayout c ρ)
          hK.base hU.base hp →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      have hc' : L.cpu σ = c := hc
      have hl' : j.Locks σ = hs := hl
      have hm' : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
      obtain ⟨⟨hJ0, hq0⟩, hQP0⟩ := id hpre
      have hJ0' : SlJAt (L := L) K.toKLayout σ := hJ0
      have hq0' : Fl4Proofs.P2.PathObl.SlQ st ar j.Locks j.n j.found j.Cs j.Ω j.Sg j.Ac K.toKLayout
          (view K.toKLayout c ρ) σ := hq0
      have hQP0' : QPs K st σ := hQP0
      have F0 := slOF_of ar L.total hA a0 hJ0' hq0'
      have V0 := slVC_of ar nv hK hU F0 hQP0' hc' hm' h0
      have hfor : SlLive st j.found.1 σ ∧ ρ (fld (slThr st j.found.1 σ) oAFFINITY) ≠ c := by
        by_contra hn
        exact hF ⟨σ, hc', hQP0'.ksb, hm', fun lv => by_contra fun hne => hn ⟨lv, hne⟩⟩
      have h := sl_fh_annV ar hA (masksWr_plain st) hU nv hV F0 V0 hl' hfor.1 hfor.2 (a := a)
      unfold LocalPath.body
      first
        | (rw [hc]; exact h)
        | (convert h using 4 <;> first | rfl | exact hc | exact hc.symm)
    exact key _ _ (allB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      (SlotC.fam_pos _ _ hp) hS
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user)) (W : AvoidV K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.cutLiftV hK.base hU.base
          (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv (view K.toKLayout c ρ)) P W).rJ K (fun b hb => Or.inl hb))),
        P = LocalPath.void (fl4Dflt st ar (masksWr_plain st)) (OwnMap.ko_aligned hK.base.base hU.base.base
          (view K.toKLayout c ρ)) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, -⟩ := hS'
      exact absurd hpre.1 id
    exact key _ _ (allB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS


end body

/-! ## Every sl start, the other exempt slots over the new family -/

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **Every sl start.** -/
def SlAllAt (_K : KLayoutP) (_c : U64) (_hs : U64 → Prop) (_ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.sl _) => True
  | _ => False

/-- **The exempt starts of U16**: U14's and every sl start. -/
def U16At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U14At (S := S) K c hs ρ k0 i ∨ SlAllAt (S := S) K c hs ρ k0 i

theorem slAll_of_h {K : KLayoutP} {c : U64} {hs : U64 → Prop} {ρ : U64 → U64} {k0 : SP}
    {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (h : SlHAt st K c hs ρ k0 i) :
    SlAllAt (S := S) K c hs ρ k0 i := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  all_goals first | exact False.elim h | trivial

/-- **U9's re-annotated body is `Safe` at every sl start of a chain of the new family** (module docstring). -/
theorem sl_annV_allB (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2B st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : SlAllAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  have nv : K.vcpus = ∅ := by
    obtain ⟨_, ⟨nv, _⟩, _⟩ := hE
    exact nv
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · have h' : StartU2B st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
        (.sl j) := hsf
    have hS := startAt_slB st ar hA a0 P hIoa
      (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE h'
    have h0 := sl_v0_SFB st ar hA a0 P hIoa hC nv hsf
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    by_cases hH : SlHome st K c ρ j
    · exact sl_k0_safeB st ar hA a0 j K hK hU nv c _ ρ s.mem k hV h0 hH hS
    · exact sl_k0_fhB st ar hA a0 j K hK hU nv c _ ρ s.mem k hV h0 hH hS
  all_goals exact False.elim hf

/-- **The io starts' `VSafe` over the new family** (`vSafe_io`: the io path is the old family's). -/
theorem vSafe_ioB {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (hM : MapsP K s)
    (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) (hi : IoIx (S := S) i) :
    VSafe (PathsP.sum (fl4LocW11JB st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st)))) s K c k hK hU ρ i := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hi
  · exact False.elim hi
  · exact vSafe_io st ar hA a0 (i := .inl (.io j)) hM hV hi
  all_goals exact False.elim hi

/-- **vmF starts over the new family** (`vmF_annV_all`: the vmF clause of `StartV2B` is `StartV2`'s). -/
theorem vmF_annV_allB (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2B st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) (hf : VmFIx (S := S) i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact vmF_annV_all st ar hA a0 P hIoa (hK := hK) (hU := hU) (i := .inl (.vmF j)) hC hE hsf hM hV hf
  all_goals exact False.elim hf

/-- **vmR starts over the new family** (`vmR_annV_all`). -/
theorem vmR_annV_allB (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2B st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) (hf : VmRIx (S := S) i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact vmR_annV_all st ar hA a0 P hIoa (hK := hK) (hU := hU) (i := .inl (.vmR j)) hC hE hsf hM hV hf
  all_goals exact False.elim hf

end all

/-! ## U16 -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end with sl's `VSafe9` discharged at every sl start** (module docstring), over the family whose sl
program is the extracted tree: `VSafe9` [J] is asked only at starts that are neither io, vmF, vmR nor sl starts (st,
irq, vq, invocations). The conclusion is about the physical memory. -/
theorem serializable_fl4_localU16 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JB st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U16At (S := S)) (StartV2B st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  refine serializable_e2ePV9 _ h0 hA0 hK0 hU0 hM0 (execPV9_of_WPRV10S ?_ ?_ ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  · intro Ch K s hK hU c hs q i hC hE hsf
    rcases i with i | ((j | j) | j)
    · exact startAt_UNB st ar hA a0 P hIoa hC hE hsf
    · exact delPteStart_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact invStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact cmStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · intro s K hK hU c k ρ i hM hV hn
    exact vSafe_ioB st ar hA a0 hM hV (not_not.mp hn)
  · intro Ch s K hK hU c k ρ i hC hE hsf hM hV hf
    rcases hf with (hf | hf) | hf
    · exact vmF_annV_allB st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact vmR_annV_allB st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact sl_annV_allB st ar hA a0 P hIoa hC hE hsf hM hV hf

/-- **U15's statement over the new family follows from U16** (every such execution is a U16 one). -/
theorem serializable_fl4_localU15of16 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JB st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U15At st) (StartV2B st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU16 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    (execWPRV10_mono (fun _ _ _ _ _ _ hf => hf.imp id (slAll_of_h st)) h) hq

end top

end
end Fl4Proofs.P2.E2EP

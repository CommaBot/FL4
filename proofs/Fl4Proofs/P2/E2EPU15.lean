/-
# P2 (line p3mc, gen 15): U15, sl's `VSafe9` discharged at the starts whose decided thread is homed (or absent)

## The sl starts discharged (`SlHAt`)
An sl start (`StartV2 … (.inl (.sl j))`) at core `c`'s view of `ρ` whose **decided thread** (`slThr`: the trap arm's
handler-endpoint head, the ReplyRecv arm's replied thread) is, when live (`SlLive`), homed on `c` in `ρ`. The fact is
stated at some state with the view's kernel words (`SlHAt`); every start state of the epoch at that view has the same
decided thread (`slThr_ag`: it is read from aligned kernel words).

## The proof (`sl_k0_safe`)
At such a start `σ` (`SlJAt`, `SlQ`, `QPs`, the view's kernel words) the glue's chain gives action 0 and a running
current thread (`sl_v0_SF`, P2/SlVBase), so `SlVC` (`slVC_of`: current thread, current SC, release head, SCs with a
nonzero back-pointer homed on `c`). Then `LocalPath.safeVQ` (as `vmR_k0_safe`, U14) with `Q` = agreement with `σ` on
the aligned kernel words, the core, the kernel base and the frame masks:
* **accepted** runs from every such start `s0` are runs on `guard (SlRS s0 ∧ SR) (SlWS s0 ∧ VNW)` (`sl_acc_v`,
  P2/SlBRun, applied at `s0` itself: its decided thread is `σ`'s, so homed);
* **declined** runs from `s0` are runs on `guard (SlRS s0 ∧ SR) (SlDS s0)` (`sl_dec_v`), moved to every alternative
  of `s0` by `run_transfer` (the alternative agrees with `s0` on `SlRS s0`).
`SR ⊆ VN ∧ ¬ PTE`, `VNW` as `safeVQ` asks.

**The caller's message registers and IPC buffer** (read by the non-VM `fastpath.reply_recv_found`): the registers are
the current thread's TCB words (homed), the buffer words user words in no region, which the view keeps with their
owner (P2/SlVAccR's docstring). Accepted runs are not moved between start states (they may read different buffer
values at different `s0`): the narrowed run is proved at each `s0`.

## U15
`U15At := U14At ∨ SlHAt`: **`serializable_fl4_localU15`** (`ExecWPRV10 … (¬IoIx) U15At StartV2`),
**`serializable_fl4_localU14of15`**.

## Premises of `serializable_fl4_localU15` vs `serializable_fl4_localU14`
* **Removed: `VSafe9` [J] at the sl starts with `SlHAt`** (decided thread homed on `c`, or not live). Nothing added.
* `VSafe9` [J] stays at the sl starts whose decided thread is another core's (the foreign-thread decline
  certificate, as U13's `vmR_fh_annV` / U10's `vmF_fh_annV`, is not done), and at st, irq, vq, invocation starts;
  `VSafe` [J] unchanged.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.SlBRun
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

/-! ## The decided thread at agreeing states, the view context -/

section ag
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 2000000 in
/-- **The decided thread is read from aligned kernel words.** -/
theorem slThr_ag {Kl : KLayout} {rp : U64} {s s' : S} (hJ : SlJAt (L := L) Kl s) {T : Set U64}
    (hN : NodePlaced st T s (L.cpu s)) (hcH : Kl.heap (L.curW s) = some .tcb)
    (hrp : ¬ SlTrap st s → NU Kl (rTcbA rp)) (G : Ag st (NU Kl) s s') :
    slThr st rp s' = slThr st rp s ∧ (SlLive st rp s' ↔ SlLive st rp s) := by
  have hX := hJ.regionOKX
  have hK := hJ.regionOK
  have ecur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW
    rw [G.node]
    exact G.m _ (hJ.nuNode hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]))
  have hT : SlTrap st s' ↔ SlTrap st s := by
    unfold SlTrap
    rw [ecur, PathObl.flags_ok, PathObl.flags_ok, G.m _ (nu_tcb hX hcH (o := 3456#u64) (by simp) (by simp) (by simp))]
  obtain ⟨n0, n8⟩ := nu_tslot hK hX hcH (i := layout.tcb.SLOT_FAULT_HANDLER) (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  have hf : fhA (L := L) s' = fhA (L := L) s := congrArg (fun t => slotIdx t layout.tcb.SLOT_FAULT_HANDLER) ecur
  have ecap : obj.Slot.cap st (fhA (L := L) s) s' = obj.Slot.cap st (fhA (L := L) s) s :=
    cap_congr (G.m _ n0) (G.m _ n8)
  have hEp : IsEp (obj.Slot.cap st (fhA (L := L) s) s) →
      Kl.heap (resPtr (obj.Slot.cap st (fhA (L := L) s) s)) = some .ep := fun h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, B'⟩ := hJ
    exact B'.hep h
  refine ⟨?_, ?_⟩
  · unfold slThr
    by_cases hS : SlTrap st s
    · rw [if_pos (hT.2 hS), if_pos hS, hf, ecap]
      by_cases hE : IsEp (obj.Slot.cap st (fhA (L := L) s) s)
      · have eh : L.mem s' (epHeadA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) =
            L.mem s (epHeadA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) :=
          G.m _ (nu_ep hX (hEp hE) (o := layout.ep.HEAD) (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD]))
        rw [if_pos hE, if_pos hE, eh]
      · rw [if_neg hE, if_neg hE]
    · rw [if_neg (fun h => hS (hT.1 h)), if_neg hS, G.m _ (hrp hS)]
  · unfold SlLive
    by_cases hS : SlTrap st s
    · rw [if_pos (hT.2 hS), if_pos hS, hf, ecap]
      by_cases hE : IsEp (obj.Slot.cap st (fhA (L := L) s) s)
      · have et : L.mem s' (epTSA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) =
            L.mem s (epTSA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) :=
          G.m _ (nu_ep hX (hEp hE) (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
            (by simp [layout.ep.TAIL_STATE]))
        rw [ep_state_congr (st := st) et]
      · exact ⟨fun h => absurd h.1 hE, fun h => absurd h.1 hE⟩
    · rw [if_neg (fun h => hS (hT.1 h)), if_neg hS, G.m _ (hrp hS)]

variable {A : Type} (ar : machine.Arch A)
variable {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **The view context of an sl start state** (module docstring). -/
theorem slVC_of {K : KLayoutP} (nv : K.vcpus = ∅) (hK : RegionOKP K) (hU : UserOKP K) {c : U64}
    {ρ : U64 → U64} {s : S} (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s)
    (hq : QPs K st s) (hc : L.cpu s = c)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x) (h0 : SlV0 st K c ρ) :
    SlVC (L := L) K c ρ s := by
  obtain ⟨hact, hrun⟩ := sl_view_act F.B F.E.hN F.E.hSt.1 hc hm h0
  obtain ⟨Cs', Ac', Ω', BV, BP⟩ := sl_vmBase nv hK hq.ks F.B hrun
  have scn : L.mem s (scA (L.curW s)) ≠ 0#u64 := BV.bxi.2.1.resume hact
  exact
  { hK := hK
    cpu := hc
    hm := hm
    cur := vm_cur_home hK BV hm
    csc := (vm_homes BP hm).1 scn
    rh := (vm_homes BP hm).2
    scb := fun p hp h0 => vm_sc_home_of_tcb BP hm hp h0
    ks := hq.ks
    ksb := hq.ksb
    tab := hq.tab
    upte := userNoE_pte hU
    scn := scn }

end ag

/-! ## The sl body at a view start whose decided thread is homed -/

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

/-- **The decided thread is homed on `c` (or not live)**, seen at some state with the view's kernel words. -/
def SlHome (K : KLayoutP) (c : U64) (ρ : U64 → U64) (j : SlArg S) : Prop :=
  ∃ σ' : S, L.cpu σ' = c ∧ L.ksb σ' = K.ksb ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x) ∧
    (SlLive st j.found.1 σ' → ρ (fld (slThr st j.found.1 σ') oAFFINITY) = c)

set_option maxHeartbeats 8000000 in
/-- **The sl body is `Safe` at every view start whose decided thread is homed** (module docstring). -/
theorem sl_k0_safe (j : SlArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (h0 : SlV0 st K c ρ) (hH : SlHome st K c ρ j)
    (hS : StartAt (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
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
  by_cases hp : (slSlotP3W6 st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user)) (W : AvoidV K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.cutLiftV hK.base hU.base
          (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv (view K.toKLayout c ρ)) P W).rJ K (fun b hb => Or.inl hb))),
        P = (slSlotP3W6 st ar hA (masksWr_plain st) L.total a0).path j K.toKLayoutV (view K.toKLayout c ρ)
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
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
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
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

end body

/-! ## The discharged sl starts -/

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The sl starts whose decided thread is homed** (module docstring). -/
def SlHAt (K : KLayoutP) (c : U64) (_hs : U64 → Prop) (ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.sl j) => SlHome st K c ρ j
  | _ => False

/-- **The exempt starts of U15**: U14's and the sl starts whose decided thread is homed. -/
def U15At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U14At (S := S) K c hs ρ k0 i ∨ SlHAt st K c hs ρ k0 i

/-- **U9's re-annotated body is `Safe` at every `SlHAt` start of a chain** (module docstring). -/
theorem sl_annV_h (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : SlHAt st K c (fun l => s.lk l = some c) ρ k i) :
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
  · have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
        (.sl j) := hsf
    have hS := startAt_UN st ar hA (masksWr_plain st) L.total a0 P hIoa
      (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE (startU_of_U2 st ar hA a0 hC nv h')
    have h0 := sl_v0_SF st ar hA a0 P hIoa hC nv hsf
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    exact sl_k0_safe st ar hA a0 j K hK hU nv c _ ρ s.mem k hV h0 hf hS
  all_goals exact False.elim hf

end all

/-! ## U15 -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end, U14 with sl's `VSafe9` discharged at the starts whose decided thread is homed** (module
docstring): `VSafe9` [J] is asked only at starts that are neither io, vmF, vmR, nor `SlHAt` sl starts. The
conclusion is about the physical memory. -/
theorem serializable_fl4_localU15 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U15At st) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
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
    rcases hf with (hf | hf) | hf
    · exact vmF_annV_all st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact vmR_annV_all st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact sl_annV_h st ar hA a0 P hIoa hC hE hsf hM hV hf

/-- **U14 follows from U15** (every U14 execution is a U15 one). -/
theorem serializable_fl4_localU14of15 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U14At (S := S)) (StartV2 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU15 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    (execWPRV10_mono (fun _ _ _ _ _ _ hf => Or.inl hf) h) hq

end top

end
end Fl4Proofs.P2.E2EP

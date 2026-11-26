/-
# P2 (line p3mc, gen 16): U9's re-annotated sl body is `Safe` at a view start whose decided thread is another core's

The decline split for sl at core `c`'s view `view K c ρ` (the counterpart of `RrFhView.vmR_fh_annV`): at an sl
entry state `σ` (`SlOF` at the view's memory, `SlVC`) whose decided thread `d = slThr σ` is live and has
`ρ (AFFINITY d) ≠ c`, U9's armed program `narrowSP cls (ko K μ) c (VO K c ρ) ∅ (body σ a)` is `Safe` at the
physical memory `μ` (`VEq ρ μ`):

* **`rrDR0_v`**: `rrDR_v` without the replied thread's clauses (the thread-free `RrDR0` at `SR`, no homing asked);
  **`rrDecT_v0`**: `rrDecT_v` from it;
* **`sl_fh_annV`**: `PathObl.sl_fh_safe` with `Rd := (SlRS σ ∧ NU K) ∧ SR` (`SlFhR`: `F.D`'s halves, `fltDec_nu` /
  `rrDec_nu`, `fltDecT_v` / `rrDecT_v0`, the head refill by `F.P.hhd` / `rdHead_hereN` / `rdHead_v`),
  `Ro := rsE ptes (rsV K (SlRS)) σ ∧ VO`, then `E2E.safe_narrow_tr`. `d`'s `AFFINITY` is gate-owned at every memory
  (`own_aff_gate`), so in `Ro`; the prefix words are held at `μ` (writable at the view, `VN` by `preAcc_v`, `VEq`) and
  are `SafeW` (`slDS_region`), so their writes pass `StepOK` (`stepOK_safeP`).

**Not yet a U-theorem.** `sl_fh_annV` is about the translation of the extracted tree
`R.syscall.handle_syscall_local n found`. The sl slot of `fl4LocW11JA` (`slSlotP3W6` → `sl_pathsKC5` →
`SlJLay.sl_localPathK`) carries `p := hpz.choose` for `hpz := ⟨R.syscall.handle_syscall_local n found, …⟩`, which is
not definitionally that tree (`Classical.choose`), and `Once` / `tr` are structural in the tree, so the start's body
`k0` cannot be identified with this theorem's program. U15's `sl_k0_safe` did not need it (`safeVQ` uses the path's
own `ReadOnce` at alternatives); the foreign case has no alternative to use (every `Pre` state has `d`'s
`AFFINITY = c`). The bridge is an sl slot with the concrete program (`ProgGenSyLP.sl_localPathG` has
`p := R.syscall.handle_syscall_local n found`, `SlOnce.sl_hro` its `ReadOnce`) — handoff p3mc §19.

No premise: every fact is a hypothesis of the theorems. No existing statement changed.
-/
import Fl4Proofs.P2.SlFhCert
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE InW)
open Fl4Proofs.P2.E2E (SP tr masksOf)
open Fl4Proofs.P2.Serial (Owner VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb vn_td
  view_keep_tcb vkc_of not_vdec_node not_vdec_sc not_vdec_tcb TZero decOff_list)

noncomputable section
open Classical

section rec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayoutP} {c : U64} {ρ : U64 → U64} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64}
  {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The ReplyRecv arm's words before the replied thread's are `SR`** (`rrDR_v` without the replied thread's
clauses: no homing asked). -/
theorem rrDR0_v (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    (hS : ¬ SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    RrDR0 (L := L) (SR K c ρ) X (L.curW s) found.1 found.2 := by
  have B := F.B
  have E := F.E
  have Hh := F.Hh
  have hK := V.hK
  have hX := B.regionOKX
  obtain ⟨hk, hcp⟩ := B.kc
  have C := slCom_v ar hA V B E LP
  have hcH := E.hSt.1
  obtain ⟨hrp, hep⟩ := B.rrG F.C.fd hS (F.C.arm hS)
  obtain ⟨-, -, hXI, -, -⟩ := E.hI a X a1 LP
  have hX0 := hXI.2.2.toScExtra0
  have tw : ∀ y, K.toKLayout.heap y = some .tcb → ρ (fld y oAFFINITY) = c → ∀ o : U64, 192 ≤ o.val →
      o.val < 4096 → o.val % 8 = 0 → SR K c ρ (core.num.U64.wrapping_add y o) :=
    fun y hy hya o h1 h2 h3 => sr_tcb hK hX hy hya h1 h2 h3
  have eM : ∀ w, Aligned w → (∀ d, region K.toKLayout w ≠ .node d) →
      region K.toKLayout w ≠ .tcb (L.curW s) → L.mem X w = L.mem s w := fun w aw r1 r2 =>
    lp_mem ar hA E.hT E.hN E.hcT LP aw (not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp r1 r2)
  obtain ⟨KM, hKM, eKM⟩ := regA_eq (E.hT _ E.hcT) (r := layout.reg.MSG_INFO)
    (by simp [layout.reg.MSG_INFO])
  refine ⟨C.nd, C.dt, C.cd, C.tm, C.rh, tw _ hcH V.cur layout.tcb.STATE (by rw [st_val]; omega)
    (by rw [st_val]; omega) (by rw [st_val]), tw _ hcH V.cur 3464#u64 (by simp) (by simp) (by simp), fun h0 => ?_,
    tw _ hcH V.cur 3592#u64 (by simp) (by simp) (by simp), ?_, tw _ hcH V.cur 3368#u64 (by simp) (by simp) (by simp),
    tw _ hcH V.cur 3448#u64 (by simp) (by simp) (by simp), fun h0 => ?_,
    (srw_rp hK hX hrp (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])).1,
    (srw_rp hK hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])).1,
    (srw_ep hK hX hep (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE])).1⟩
  · -- the current SC's `REFILL_MAX` (homed: its `TCB` back-pointer is the current thread)
    obtain ⟨hcS, htb, -⟩ := hX0.bound _ hcH h0
    have hz := scs_heap (K := K.toKLayout) hcS
    generalize L.mem X (scA (L.curW s)) = p at hcS htb hz
    obtain ⟨-, aT, -, rT⟩ := sc_off hX hz (o := layout.sc.TCB) (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB])
    have rT' : region K.toKLayout (scTcbA p) = .sc p := rT
    have eT : L.mem X (scTcbA p) = L.mem s (scTcbA p) :=
      eM _ aT (fun d => by rw [rT']; intro h; cases h) (by rw [rT']; intro h; cases h)
    have hpc : ρ (fld p 16#u64) = c :=
      V.scb p hcS (by rw [← eT, htb]; exact fun e => (E.hT _ E.hcT).ne0 (by rw [e]; rfl))
    exact sr_scw hK hX hz hpc (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
      (by simp [layout.sc.REFILL_MAX])
  · have hKM' : KM.val = 256 + 8 * layout.reg.MSG_INFO.val := hKM
    rw [eKM]
    exact tw _ hcH V.cur KM (by rw [hKM']; simp [layout.reg.MSG_INFO]) (by rw [hKM']; simp [layout.reg.MSG_INFO])
      (by rw [hKM']; simp [layout.reg.MSG_INFO])
  · -- the bound notification
    have eB : L.mem X (boundA (L.curW s)) = L.mem s (boundA (L.curW s)) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hcH 3368#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT hcH hk hcp hcH (by simp) (by simp) (by simp) (by simp))
    obtain ⟨hn, hbk⟩ := ntf_of ar hA hX (slSets_conv K.toKLayout) E hk hcp LP (by rw [← eB]; exact h0)
    rw [eB]
    generalize L.mem s (boundA (L.curW s)) = p at hn hbk
    obtain ⟨r24, -, a24⟩ := hX.ntW _ hn 24#u64 (by simp) (by simp)
    have hb : ρ (fld p 24#u64) = L.curW s := by
      have r24' : region K.toKLayout (fld p 24#u64) = .ntfn p := r24
      have e1 : view K.toKLayout c ρ (fld p 24#u64) = ρ (fld p 24#u64) := view_ntfn r24'
      have e2 : L.mem s (fld p 24#u64) = view K.toKLayout c ρ (fld p 24#u64) :=
        V.hm (fld p 24#u64) a24 (hX.kern _ (by rw [r24']; intro h; cases h))
      rw [← e1, ← e2]; exact hbk
    have hnf : ∀ b, region K.toKLayout b = .ntfn p → NotForeign K.toKLayout c ρ b := fun b hr =>
      nf_ntfn hr (fun _ => by rw [hb]; exact V.cur)
    obtain ⟨r1, -, -⟩ := hX.ntW _ hn layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE])
      (by simp [layout.ntfn.TAIL_STATE])
    obtain ⟨r2, -, -⟩ := hX.ntW _ hn layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])
    exact ⟨sr_nf hK (by rw [r1]; intro h; cases h) (hnf _ r1), sr_nf hK (by rw [r2]; intro h; cases h) (hnf _ r2)⟩

set_option maxHeartbeats 4000000 in
/-- **The ReplyRecv arm's words before the replied thread's are `SR`** (from `RrDR0`). -/
theorem rrDecT_v0 (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    (hS : ¬ SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    (D' : RrDR0 (L := L) (SR K c ρ) X (L.curW s) found.1 found.2) :
    RrDecT (L := L) (SR K c ρ) X (L.curW s) found.1 found.2 := by
  have B := F.B
  have E := F.E
  have C := slCom_v ar hA V B E LP
  obtain ⟨-, -, aT, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have eS : L.mem X (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    aT _ E.hcT 3464#u64 (by simp) (by simp) (by simp)
  refine ⟨D'.nd, D'.dt, D'.cd, C.bm, D'.tm, D'.rh, D'.tSt, D'.tSc, D'.tMx (by rw [eS]; exact V.scn), D'.tIq,
    D'.tMi, D'.tBn, D'.tPr, ?_, D'.rRt, D'.rNx, D'.eTS⟩
  intro nt hnt hne
  have e1 := (eq_of_spec_fd (obj.Tcb.bound_ntfn.val X (L.curW s))).symm.trans hnt
  have en : nt = L.mem X (boundA (L.curW s)) := (ok_inj_ff e1).symm
  subst en
  exact D'.ntf (fun h0 => by rw [h0] at hne; simp at hne)

end rec

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {Locks : S → U64 → Prop} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 8000000 in
/-- **U9's armed sl program is `Safe` at a view start whose decided thread is another core's** (module
docstring). -/
theorem sl_fh_annV (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hU : UserOKP K)
    (nv : K.vcpus = ∅) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ) {σ : S} {a : A}
    (F : SlOF (st := st) ar K.toKLayout Locks (view K.toKLayout c ρ) n found Cs Ω Sg Ac σ)
    (V : SlVC (L := L) K c ρ σ) (hl : Locks σ = hs)
    (lv : SlLive st found.1 σ) (hρ : ρ (fld (slThr st found.1 σ) oAFFINITY) ≠ c) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (rsV K.toKLayoutV (SlRS (st := st) K.toKLayout Locks)) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.syscall.handle_syscall_local n found) ∅ a)) := by
  have hK := V.hK
  have hc := V.cpu
  have B := F.B
  have E := F.E
  have hX := B.regionOKX
  have hK0 := B.regionOK
  obtain ⟨hk, hcp⟩ := B.kc
  have ht := F.N.hthr lv
  -- the read sets
  let Rd : U64 → Prop := fun q =>
    (SlRS (st := st) K.toKLayout Locks σ q ∧ NU K.toKLayout q) ∧ SR K c ρ q
  let Ro : U64 → Prop := fun q =>
    rsE (· ∈ K.ptes) (rsV K.toKLayoutV (SlRS (st := st) K.toKLayout Locks)) σ q ∧ VO K c ρ q
  have PD := preDec_v ar V B E
  have D : SlFhR (st := st) ar found Rd σ a :=
    { al := fun b hb => hb.1.1.1
      pd := ⟨fun o h1 h2 => ⟨⟨(F.P.preG.nd o h1 h2).1, B.nuNode E.hN h1 h2⟩, PD.nd o h1 h2⟩,
        Or.inr (Or.inl rfl), Or.inr (Or.inr rfl),
        ⟨⟨F.P.preG.fl, nu_tcb hX E.hSt.1 (o := 3456#u64) (by simp) (by simp) (by simp)⟩, PD.fl⟩,
        ⟨⟨F.P.preG.nx, nuReg hX E.hSt.1 (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])⟩, PD.nx⟩,
        Or.inl rfl⟩
      hd := fun X a1 csc LP hcs => by
        have h1 := F.P.hhd a X a1 csc LP hcs
        obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
        have e : csc = L.cscW σ := by
          rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at hcs
          rw [← ok_inj_ff hcs]; exact ecs
        subst e
        exact RdHead.meet (RdHead.meet h1 (rdHead_hereN ar hA hX E F.Hh LP F.Hh.cs))
          (rdHead_v ar hA V B E F.Hh LP F.Hh.cs V.csc)
      fT := fun hS X a1 LP => FltDecT.meet (FltDecT.meet (F.D.fT hS a X a1 LP)
        (FltDec.toT (fltDec_nu ar hA B E LP))) (fltDecT_v ar hA F V LP)
      rT := fun hS X a1 LP => RrDecT.meet (RrDecT.meet (F.D.rT hS a X a1 LP)
        (RrDec.toT (rrDec_nu ar hA F hS LP))) (rrDecT_v0 ar hA F V hS LP (rrDR0_v ar hA F V hS LP)) }
  have hR0 : ∀ q, Rd q → Ro q ∧ q ∉ K.user := fun q hq =>
    ⟨⟨⟨⟨hq.1.1, not_vData_empty nv⟩, hq.2.2⟩, hq.2.1.2⟩, hq.1.2.2⟩
  -- the decided thread's `AFFINITY`
  have afI := F.I.af lv
  obtain ⟨rA, -, -⟩ := hX.tcbW _ ht 3520#u64 (by simp) (by simp) (by simp)
  have rA' : region K.toKLayout (affA (slThr st found.1 σ)) = .tcb (slThr st found.1 σ) := rA
  have hpA : affA (slThr st found.1 σ) ∉ K.ptes := fun hp => by
    have h := hK.none _ hp
    rw [rA'] at h
    cases h
  have hgo : Ro (affA (slThr st found.1 σ)) ∧ affA (slThr st found.1 σ) ∉ K.user := by
    refine ⟨⟨⟨⟨afI.1, not_vData_empty nv⟩, hpA⟩, ?_⟩, hX.kern _ (by rw [rA']; intro h; cases h)⟩
    show ownP K (view K.toKLayout c ρ) (affA (slThr st found.1 σ)) = ownP K ρ (affA (slThr st found.1 σ))
    rw [ownP_eq_own nv hpA, ownP_eq_own nv hpA]
    exact (OwnMap.own_aff_gate hK0 ht _).trans (OwnMap.own_aff_gate hK0 ht _).symm
  have hρd : ρ (affA (slThr st found.1 σ)) ≠ c := by rw [OwnMap.affA_fld]; exact hρ
  -- the memories
  have hRdρ : ∀ b, Rd b → ρ b = L.mem σ b := fun b hb =>
    hb.2.1.1.symm.trans (V.hm b hb.1.2.1 hb.1.2.2).symm
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => V.hm x hx hu
  have hRPO : ∀ x, x ∉ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hx.1.2, ← hc, ← hl]
      exact po_of_rperm (hx.1.1.1.2.resolve_left hu)
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  have hDU := slDS_nu hX F.N
  have PA := preAcc_v ar V B E
  have hH : ∀ x, SlDS (L := L) σ x → HeldV c hs (ownP K μ x) := by
    intro x hx
    have hW := (SlDS.ws F.P.preG hx).2.resolve_left (hDU x hx)
    have hr := slDS_region hX E.hN E.hT E.hcT E.hSt.1 hk hcp hx
    have hpx : x ∉ K.ptes := fun hp => by
      have h := hK.none _ hp
      rcases hr with h' | ⟨h', -⟩ <;> rw [h'] at h <;> cases h
    have hvn : VN K c ρ x := by
      rcases hx with rfl | rfl | rfl
      · exact PA.fi.1
      · exact (PA.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2.1
      · exact (PA.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2.1
    have h1 : HeldV c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hpx, ← hc, ← hl]
      unfold WPerm at hW
      revert hW
      cases OwnMap.own K.toKLayout (L.mem σ) x <;> exact id
    rw [eown, hvn.2] at h1
    rw [hV.1 _ (Or.inl h1)]
    exact h1
  have hSO : ∀ (z : S) b v, SlDS (L := L) σ b →
      StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem z)
        (L.mem (L.wr z b v)) := by
    intro z b v hb
    have ha := (SlDS.ws F.P.preG hb).1
    have hsw : SafeW K.toKLayout b := by
      rcases slDS_region hX E.hN E.hT E.hcT E.hSt.1 hk hcp hb with h | ⟨h, hv⟩
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr (Or.inl ⟨_, 392, E.hSt.1, h, by omega, hv, by omega, by omega, by omega, by omega, by omega,
          by omega⟩)
    exact stepOK_safeP hK nv B.ioLayA ha hsw
  have h := sl_fh_safe (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) hmk hA hc F (Ro := Ro) D hR0 lv hgo hρd hRdρ hRPO
    (fun x hx => hV.2.1 x hx) hDU hH hSO
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

end
end Fl4Proofs.P2.E2EP

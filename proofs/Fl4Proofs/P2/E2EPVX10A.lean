/-
# P2 (line vmscope, gen 10, delPte module 2): the Delete PTE-arm path in VM epochs (`inv_localPathPV`)

The native PTE-arm path `inv_localPathPP` (P2/InvDelPteOnceP.lean) is an `ownP` path at `Pre := PreP = SlJAt ∧
InvQFP ∧ CvP` with read set `InvRSP` and `K.vcpus = ∅` (`nv`) in `obl` / `side` / `once`. This module builds the same
path at layouts **with VCPUs** and **without a P3 bundle**:

* **Entry states `PrePX`** (handoff step 1): `InvLX st (fun _ => True) K` (VX8's bundle replacement: layout facts and
  `InvLXS` at every user-write-reachable state) ∧ `InvQFP` (the PTE arm's entry fact, as natively) ∧ **`WalkP`** (the
  walk fact replacing `CvP`: for every ASID and user address the walk reads only `VsW` words off `XD = VData ∨ ptes`,
  and a found leaf entry is a word of `K.ptes` and a `VsW` word — natively `SlJAtZ.vsRdX` + `ptesR_sub`,
  `ptesR_of_spe`, `SlJAtZ.leafVsW`) ∧ the layout facts `KsNoE (· ∈ K.ptes)` (natively `ksNoE_conv` from `CvP`) and
  `InvVF` (the epoch's `VtxBundle4`: `vu`, `ko`).
* **Read set `InvRSV := InvRSP ∧ ¬ VData`** (handoff steps 2–4 in one): `InvRSP` (`IoRS` minus the unlocked leaves)
  cut off the VCPU data words at construction. The handoff's route (a base path under `own`, `cutLiftV` at
  `Ex := VData`, then a new `cutLiftPE`) cannot be taken literally: the PTE arm **writes** its locked leaf, which is the
  gate's under `own` and `ownV` (`ownV_pte`), so no `own` / `ownV` path can carry that write (`write_own`). Building the
  path directly under `ownP` with the cut read set is the composition of the two lifts: reads by `rpermV_of_own_nd`
  (off `VData`) + `rpermP_of_V` / `rpermP_pte` (the locked leaf), writes by `wpermV_of_own'` + `wpermP_of_V` /
  `wpermP_pte`, per-write checks by `stepOKV_of_stepOK` (no `nv`) + `stepOKP_of_stepOKV`. The avoidance of `VData`
  is proved inside each accepted-run block (`delAccX` / `delAcc2X` at `X := XD K`, the `R`-parametric blocks), so no
  separate `AvoidE` is needed.
* Copies (gen-7/8 invj text, `SlJAt` → `InvLX` / `WalkP`, `nv` → `RegionOKV` / `InvVF`): `invSeenR_ofZ`,
  `invBlkPV`, `invAccPV` (acc), `rsv_read_own`, `wsp_write_own`, `wsp_aligned`, `invDecPV`, `invBlkGdPV`,
  `invMovePV`, `inv_isProgOnPV`, **`invOblPV`**, `invRaPV`, `invUfPV` (user_free: `InvLX.wr`, VX9D's `invQFP_wrX`,
  `walkP_wr`; locks by [P] `hlk`), `invU_decOncePV`, `invBlkPLV`, `invAccPLV`, **`invRoPV`**, and the path
  **`inv_localPathPV`** (`LocalPath (ownP K)` at `RegionOKP K`, `UserOKP K`, any VCPU set).

Premises of `inv_localPathPV`: `hA`, [P] `hm` (`MasksWr`), `hCs` (`Cs` below 64), [P] `hlk` (the locks kept by an
aligned user write at an `InvLX` state, VX8's `InvPremX.lk`). No [J] / [W] / [S] here (the walk fact is part of `Pre`;
the slot's start fact supplies it, E2EPVX10). No sorry / admit / native_decide / bv_decide. New module; no existing
statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPVX9D
open Aeneas Aeneas.Std Result

/-! ## The truncated-decode `Once` at `InvLX` (`PathObl`) -/

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section restPV
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- (vmscope gen 10: copy of invj's `invU_decOnceP` at `InvLX` in place of `SlJAt`) **The decode onward of an
accepted truncated PTE-arm Delete reads once** (`InvUDecOnceW` at `Pre ∧ ¬ InvLen`). No premise. -/
theorem invU_decOncePV (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {m0 : U64 → U64} :
    InvUDecOnceW st ar number p K Locks
      (fun s => (InvLX st (fun _ => True) K s ∧ InvQFP st Cs Ω Sg Ac Locks p K m0 s) ∧ ¬ InvLen st s) := by
  intro s a info nx s1 s2 a1 buf length cap r' hE hac emi C ebuf ecap hlen h Wd
  obtain ⟨⟨hJ, hqf⟩, hnL⟩ := hE
  obtain ⟨sA, aA, h0⟩ := hac
  have P := hqf.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsl, -⟩ := del_coreP hqf
  have hlbl : info.label = fl4_abi.label.CNodeDelete := (hqf.1.2.2.1 _ info (cur_thread_ok s) emi).1
  have hil : info.length < 2#u64 := by
    by_contra hc
    apply hnL
    intro t info' ht hi'
    have et : t = L.curW s := ok_inj_ff (ht.symm.trans (cur_thread_ok s))
    subst et
    rw [emi] at hi'
    have ei : info = info' := ok_inj_ff hi'
    subst ei
    have : ¬ info.length.val < 2 := fun h' => hc (by scalar_tac)
    omega
  have hlen' := hlen hil
  have enx := C.1
  have es1 := C.2.1
  have eu := C.2.2.1
  have hL : Slot8 K := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA P.tp P.np P.cT es1 eu
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact P.slot_keep w0 hq hbq hb
  have ecap0 := ecap
  rw [cap_agree hL hsl ag, hcs] at ecap0
  have hcap' : cap = .CNode cp cr cg cgb := (ok_inj_ff ecap0).symm
  subst hcap'
  have M := invCM_hmid (Locks := Locks) hA P h0 info nx s1 s2 a1 emi enx es1 eu
  have hctR : IoRS (st := st) K Locks s (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [M.c, nodeAt_of_ksb M.k]
    exact (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])).1
  have edec : ∀ m : machine.Store S, sched.cur_thread m s2 = sched.cur_thread st s2 →
      decCNG m ar s2 a1 fl4_abi.label.CNodeDelete length p.slot (.CNode cp cr cg cgb) true true true false buf
        p.extra = ok (.Err (.Sys .TruncatedMessage), s2, a1) := by
    intro m hm
    unfold decCNG
    rw [hm, cur_thread_ok]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact cnode_decode_trunc ar m hlen'
  unfold invCMRest at h ⊢
  rw [hlbl] at h ⊢
  refine once_gstep (R0 := IoRS (st := st) K Locks s) (W0 := IoWS (st := st) K Locks s)
    (fun q hq => ⟨ioRS_cm hq, hq.2.1⟩) (fun q hq => P.ioWS_nu hq) (R.decCNG_nz _ _ _ _ _ _ _ _ _ _) h
    (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.decCNG_eq] at h1 ⊢
    rw [edec _ (sched.cur_thread.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s)
      (IoWS (st := st) K Locks s)) s2 hctR)]
    rw [edec st rfl] at h1
    exact h1
  rw [R.decCNG_eq] at h1
  obtain ⟨r0, er0, rfl⟩ := bind_shape h1
  rw [edec st rfl] at er0
  obtain rfl := ok_inj_ff er0
  dsimp only at hk ⊢
  unfold R.invPostG at hk ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.blk] at hk ⊢
  exact invU_replyOnce P M (fun x5 Wd' T' er hk' =>
    invU_tailOnce hA P hcs hsl hJ.buf8 C ecap hlen' er hk' Wd' T') hk Wd1

end restPV

end Fl4Proofs.P2.PathObl

/-! ## The walk fact, the cut read set, and the path (`E2EP`) -/

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame fld)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- **The PTE arm's walk fact** (module docstring): for every ASID and user address the walk reads only `VsW` words
off `XD` (no VCPU data word, no leaf PTE), and a found leaf entry is a word of `K.ptes` and a `VsW` word. Natively
`SlJAtZ.vsRdX` with `ptesR_sub` (`CvP`), `ptesR_of_spe`, `SlJAtZ.leafVsW`. -/
def WalkP (K : KLayoutP) (s : S) : Prop :=
  ∀ asid va, va ≤ fl4_abi.consts.USER_TOP →
    VsRdG st (fun b => VsW K.toKLayout b ∧ ¬ XD K b) s asid va ∧
    ∀ e, localinv.small_page_entry st s asid va = ok (some e) → e ∈ K.ptes ∧ VsW K.toKLayout e

variable {K : KLayoutP} {s : S}

/-- A found small-page entry is for a user address. -/
theorem spe_topX {asid va e : U64} (hc : localinv.small_page_entry st s asid va = ok (some e)) :
    va ≤ fl4_abi.consts.USER_TOP := by
  unfold localinv.small_page_entry at hc
  obtain ⟨r, hr, hc⟩ := bind_eq_ok hc
  cases r with
  | Err e0 =>
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual] at hc
    exact absurd (ok_inj_ff hc) (by simp)
  | Ok root =>
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok] at hc
    unfold localinv.page_entry at hc
    by_cases hu : va > fl4_abi.consts.USER_TOP
    · rw [if_pos hu] at hc
      exact absurd (ok_inj_ff hc) (by simp)
    · have : ¬ fl4_abi.consts.USER_TOP.val < va.val := hu
      show va.val ≤ fl4_abi.consts.USER_TOP.val
      omega

/-- The leaf half of `WalkP`, for every walk. -/
theorem WalkP.lf (W : WalkP st K s) :
    ∀ asid va e, localinv.small_page_entry st s asid va = ok (some e) → e ∈ K.ptes ∧ VsW K.toKLayout e :=
  fun asid va e he => (W asid va (spe_topX he)).2 e he

/-- **`VsXW`-shaped walk facts of the mapped frame caps** from `InvLXS.vs` and `WalkP`. -/
theorem WalkP.vsX (X : InvLXS st K.toKLayout s) (W : WalkP st K s) :
    ∀ sl fp rt asid va, sl ∈ K.slots →
      obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧
        VsRdG st (fun b => VsW K.toKLayout b ∧ ¬ XD K b) s asid va := by
  intro sl fp rt asid va hsl hc ha
  obtain ⟨h1, h2, -⟩ := X.vs sl fp rt asid va hsl hc ha
  exact ⟨h1, h2, (W asid va h1).1⟩

/-- **`WalkP` is kept by an aligned user-word write** (the walk reads no user word: `vsRdG_wrX`). -/
theorem walkP_wr {b : U64} (hb : b ∈ K.toKLayout.user) (hba : Aligned b) (v : U64) (W : WalkP st K s) :
    WalkP st K (L.wr s b v) := by
  intro asid va hva
  obtain ⟨h1, h2⟩ := W asid va hva
  obtain ⟨h1', e⟩ := vsRdG_wrX (V := fun b => VsW K.toKLayout b ∧ ¬ XD K b)
    (fun a ha => read_wr_nu hb hba v ha.1.1 ha.1.2.2) (ksBase_wr b v) h1
  exact ⟨h1', fun e' he => h2 e' (by rw [← e]; exact he)⟩

end walk

section sets
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- **The VM-epoch PTE-arm read set**: `InvRSP` off the VCPU data words. -/
def InvRSV (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  InvRSP st K Locks s x ∧ ¬ VData K.toKLayoutV x

variable (st) in
/-- `IoRSP` off the VCPU data words (the `ReadOnce` guard of the `length ≥ 2` arm). -/
def IoRSPV (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  IoRSP st K Locks s x ∧ ¬ VData K.toKLayoutV x

variable (st) in
/-- **The entry states of the VM-epoch PTE-arm path** (module docstring). -/
def PrePX (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayoutP) (m : U64 → U64)
    (s : S) : Prop :=
  InvLX st (fun _ => True) K.toKLayout s ∧ InvQFP st Cs Ω Sg Ac Locks p K.toKLayout m s ∧ WalkP st K s ∧
    (KsNoE (· ∈ K.ptes) K.toKLayoutV ∧ InvVF K)

variable {K : KLayoutP} {Locks : S → U64 → Prop} {s : S} {x : U64}

theorem rsv_ioRSR (hK : RegionOKP K) (hU : UserOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) (vf : InvVF K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (h : IoRSR st K.toKLayout Locks s x) : InvRSV st K Locks s x :=
  ⟨ioRSP_inv (ioRSR_P hK hks h), (ioRSR_rsEX (exOK_V hK hU vf hf) h).2⟩

theorem rsv_user (hK : RegionOKP K) (hU : UserOKP K) (vf : InvVF K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64)
    (h : UserW K.toKLayout x) : InvRSV st K Locks s x :=
  ⟨⟨h.1, Or.inl h.2⟩, (exOK_V hK hU vf hf).user x h.2⟩

theorem rsv_io (h : IoRS (st := st) K.toKLayout Locks s x) (hX : ¬ XD K x) : InvRSV st K Locks s x :=
  ⟨ioRSP_inv ⟨h, fun hp => absurd (Or.inr hp) hX⟩, fun hv => hX (Or.inl ⟨h.1, hv⟩)⟩

theorem rsv_leaf (hK : RegionOKP K) (he : x ∈ K.ptes) (hv : VsW K.toKLayout x) (hl : Locks s x) :
    InvRSV st K Locks s x :=
  ⟨ioRSP_inv ⟨VsW.ioRS hv, fun _ => hl⟩, fun ⟨w, hw, _⟩ => hK.novcpu x he ⟨w, hw⟩⟩

theorem rsvi_ioRSR (hK : RegionOKP K) (hU : UserOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) (vf : InvVF K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (h : IoRSR st K.toKLayout Locks s x) : IoRSPV st K Locks s x :=
  ⟨ioRSR_P hK hks h, (ioRSR_rsEX (exOK_V hK hU vf hf) h).2⟩

theorem rsvi_io (h : IoRS (st := st) K.toKLayout Locks s x) (hX : ¬ XD K x) : IoRSPV st K Locks s x :=
  ⟨⟨h, fun hp => absurd (Or.inr hp) hX⟩, fun hv => hX (Or.inl ⟨h.1, hv⟩)⟩

theorem rsvi_leaf (hK : RegionOKP K) (he : x ∈ K.ptes) (hv : VsW K.toKLayout x) (hl : Locks s x) :
    IoRSPV st K Locks s x :=
  ⟨⟨VsW.ioRS hv, fun _ => hl⟩, fun ⟨w, hw, _⟩ => hK.novcpu x he ⟨w, hw⟩⟩

theorem rsvi_rsv (h : IoRSPV st K Locks s x) : InvRSV st K Locks s x := ⟨ioRSP_inv h.1, h.2⟩

/-- **`write_own` of `IoWSP` under rule 8 with VCPUs** (`ioWSP_wperm` without `nv`). -/
theorem ioWSP_wpermV (hK : RegionOKP K) {b : U64} (h : IoWSP st K Locks s b) :
    PathObl.WPerm (ownP K) (L.cpu s) (Locks s) (L.mem s) b := by
  rcases h with h | ⟨hb, hl⟩
  · exact wpermP_of_V hK (wpermV_of_own' hK.base h.2)
  · exact wpermP_pte hb hl

end sets

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64} {s : S}

/-- `invSeenR_of` from `0 ∉ K.slots` (no bundle). -/
theorem invSeenR_ofZ (hz : (0#u64) ∉ K.slots) (hq : InvQFP st Cs Ω Sg Ac Locks p K μ s) :
    ∀ x, SeenW p x → IoRSR st K Locks s x := by
  intro x hx
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, e, C, -, -, -, -, -, -, -, hdK, -, hLd, -, -, hSn, -⟩ :=
    del_coreP hq
  have hd0 : dest ≠ 0#u64 := fun e => hz (e ▸ hdK)
  obtain ⟨o, ho, rfl⟩ := hSn x hx
  have hov : o.val < 32 ∧ o.val % 8 = 0 := by
    rcases ho with rfl | rfl | rfl | rfl <;> simp [layout.cte.CAP0, layout.cte.CAP1, layout.cte.PREV, layout.cte.NEXT]
  exact PE.lockSlotR hdK (hLd hd0) hov.1 hov.2

end ent

section blk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `IoRSR ⊆ InvRSV` at a `PrePX` state. -/
theorem PrePX.rsv {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP}
    {m : U64 → U64} {s : S} (hK : RegionOKP K) (hU : UserOKP K) (hE : PrePX st Cs Ω Sg Ac Locks p K m s) :
    ∀ x, IoRSR st K.toKLayout Locks s x → InvRSV st K Locks s x :=
  fun _ h => rsv_ioRSR hK hU hE.2.2.2.1 hE.2.2.2.2 hE.2.1.1.1.1.lay.ksf.2 h

/-- (vmscope gen 10: copy of invj's `invBlkPP` at `PrePX`, read set `InvRSV`) **Both arms of the PTE-arm decode
block on `guard st (InvRSV s) (InvWSP s)`**. No premise. -/
theorem invBlkPV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) {s : S} (hE : PrePX st Cs Ω Sg Ac Locks p K m s)
    {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A} {buf length : U64}
    {cap : capability.Cap} (emi : msg.msg_info st s (L.curW s) = ok info)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hl : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (y : (core.result.Result Unit error.Exc) × S × A)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (guard st (InvRSV st K Locks s) (InvWSP st K Locks s)) ar s2 a1
        info.label length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (guard st (InvRSV st K Locks s) (InvWSP st K Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
      z.2.2 = core.result.Result.Ok () ∧
      FinOK (L := L) (guard st (InvRSV st K Locks s) (InvWSP st K Locks s))
        (IoRSR st K.toKLayout Locks s) (InvWSP st K Locks s) ar s z.1 z.2.1 := by
  have hR := hE.rsv hK hU
  obtain ⟨hJ, hq, hWk, hks, vf⟩ := hE
  have PE := hq.1.1.1
  have hf : K.ksb.val + 13568 ≤ 2 ^ 64 := PE.lay.ksf.2
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hq
  have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  have hW : IoWr st (InvWSP st K Locks s) K.heap.scBits s := PE.ioWr.mono (fun _ h => ioWS_inv h)
  haveI : GRd (guard st (InvRSV st K Locks s) (InvWSP st K Locks s)) st (IoRSR st K.toKLayout Locks s) :=
    grd_sub hR
  by_cases hlen : length < 2#u64
  · obtain ⟨hdec, hrep⟩ := truncAccR (R := InvRSV st K Locks s)
      (gS := guard st (InvRSV st K Locks s) (InvWSP st K Locks s)) hA PE
      hR (fun _ h => rsv_user hK hU vf hf h) hW
      (fun _ h => ⟨h.1, Or.inl h.2⟩) hcs hsK hJ.buf8 C hcap hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ :=
      truncFinR (gS := guard st (InvRSV st K Locks s) (InvWSP st K Locks s)) hA PE hW
      (SWr.of_W (ioWS_inv PE.stw.2)) hcs hsK hJ.buf8 C hcap hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · have E := delEntP_of (P := fun s => InvLX st (fun _ => True) K.toKLayout s) hJ hq
      (invCdtJX_of (fun _ h => h)) (hzX_of _ s hJ)
    have hvs := invVsJX_of (st := st) (P := fun s => InvLX st (fun _ => True) K.toKLayout s) (fun _ h => h)
    have hlf := WalkP.lf hWk
    obtain ⟨hdec, hrep⟩ := delAccX (X := XD K) (R := InvRSV st K Locks s) (W := InvWSP st K Locks s)
      (gS := guard st (InvRSV st K Locks s) (InvWSP st K Locks s)) hA PE hW (fun b hb => ioWS_inv hb) E hsK hlen
      (WalkP.vsX hJ.here.1 hWk) (fun b h => xd_vsW hK hU vf h) (fun b h hx => rsv_io h hx)
      (fun asid va e he hl' => rsv_leaf hK (hlf asid va e he).1 (hlf asid va e he).2 hl')
      (fun asid va e he => (hlf asid va e he).2)
      (fun asid va e he hl' => ⟨(hU.kern e (hlf asid va e he).1).1, Or.inr (Or.inr ⟨(hlf asid va e he).1, hl'⟩)⟩)
      C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ :=
      delFinR (gS := guard st (InvRSV st K Locks s) (InvWSP st K Locks s)) hA PE hW
      (ioWS_inv PE.stw.2) E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hJ hsl hc hA)
      (fun asid va e he => (hlf asid va e he).2) C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- (vmscope gen 10: copy of `invAccPP`) **`acc` of the VM-epoch PTE-arm path**. No premise. -/
theorem invAccPV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) {s s' : S} {a a' : A}
    (hE : PrePX st Cs Ω Sg Ac Locks p K m s)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local (guard st (InvRSV st K Locks s) (InvWSP st K Locks s)) ar s a number p =
      ok (true, s', a') := by
  have hq := hE.2.1
  have PE := hq.1.1.1
  haveI : GRd (guard st (InvRSV st K Locks s) (InvWSP st K Locks s)) st (IoRSR st K.toKLayout Locks s) :=
    grd_sub (hE.rsv hK hU)
  exact inv_acc_genR (W := InvWSP st K Locks s) hA PE (PE.ioWr.mono (fun _ h => ioWS_inv h))
    (invSeenR_ofZ hE.1.hz hq) (invPsR_of hq)
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => invBlkPV hA hK hU hE emi hc hl hk y hy) h

end blk

section obl
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}

/-- **`read_own` of the VM-epoch PTE-arm path** (no `nv`: a read word is off `VData`). -/
theorem rsv_read_own (hK : RegionOKP K) :
    ∀ s x, PrePX st Cs Ω Sg Ac Locks p K m s → InvRSV st K Locks s x → ¬ x ∈ K.user →
      PathObl.RPerm (ownP K) (L.cpu s) (Locks s) (L.mem s) x := by
  intro s x _ hr hu
  have h : IoRSP st K Locks s x := hr.1.2.resolve_left hu
  by_cases hb : x ∈ K.ptes
  · exact rpermP_pte hb (h.2 hb)
  · exact rpermP_of_V hb (rpermV_of_own_nd hK.base hr.2 h.1.2.2)

/-- **`write_own` of the VM-epoch PTE-arm path** (`invWSP_write_own` without `nv`). -/
theorem wsp_write_own (hK : RegionOKP K) :
    ∀ s x, PrePX st Cs Ω Sg Ac Locks p K m s → (InvWSP st K Locks s x ∨ IoDS (st := st) s x) → ¬ x ∈ K.user →
      PathObl.WPerm (ownP K) (L.cpu s) (Locks s) (L.mem s) x := by
  intro s x hE hx hu
  refine ioWSP_wpermV hK ?_
  rcases hx with hx | hx
  · exact hx.2.resolve_left hu
  · have PE := hE.2.1.1.1.1
    refine Or.inl ?_
    rcases hx with rfl | rfl | rfl
    · exact (PE.reg (Locks := Locks) (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])).2
    · exact (PE.nd (Locks := Locks) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME])
        (by simp [layout.node.CUR_TIME])).2
    · exact (PE.nd (Locks := Locks) layout.node.CONSUMED (by simp [layout.node.CONSUMED])
        (by simp [layout.node.CONSUMED])).2

/-- **`aligned` of the VM-epoch PTE-arm path.** -/
theorem wsp_aligned :
    ∀ s x, PrePX st Cs Ω Sg Ac Locks p K m s → (InvWSP st K Locks s x ∨ IoDS (st := st) s x) → Aligned x := by
  intro s x hE hx
  rcases hx with hx | hx
  · exact hx.1
  · exact (IoDS.safe hE.2.1.1.1.1 hx).1

end obl

section dec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (vmscope gen 10: copy of `invDecPP`) **`dec_alt` of the VM-epoch PTE-arm path** (`stepOKV_of_stepOK`, no
`nv`). No premise. -/
theorem invDecPV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hKP : RegionOKP K) (hUP : UserOKP K) {q : SProg Bool}
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (PrePX st Cs Ω Sg Ac Locks p K m) (InvRSV st K Locks) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user)) q)
    {s s' : S} {a : A} {r r' : Bool × S × A} (hE : PrePX st Cs Ω Sg Ac Locks p K m s)
    (h : syscall.handle_invocation_local st ar s a number p = ok r) (hr : r.1 ≠ true)
    (Al : Alt st (InvRSV st K Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s s')
    (h' : syscall.handle_invocation_local st ar s' a number p = ok r') :
    r'.1 ≠ true ∧
      syscall.handle_invocation_local (guard st (fun _ => True) (IoDS (st := st) s)) ar s' a number p = ok r' ∧
      syscall.handle_invocation_local (mguard st (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s' a number p =
        ok r' := by
  obtain ⟨h1, h2, h3⟩ := inv_dec_altR hA hE.1.regionOK hE.1.ioLayA hE.2.1.1.1.1 (invSeenR_ofZ hE.1.hz hE.2.1) h hr
    (Al.anti (hE.rsv hKP hUP)) h'
  refine ⟨h1, h2, ?_⟩
  rw [inv_hp hp (Narrow.mguard _ _) ⟨s, hE, Al⟩ a] at h3 ⊢
  exact interp_mguard_mono (fun x y hs => stepOKP_of_stepOKV (stepOKV_of_stepOK hKP.base hs)) q s' a _ h3

end dec

section mv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (vmscope gen 10: copy of `invBlkGdPP` at `PrePX`, read set `InvRSV`) **Both arms of the PTE-arm decode block
on `gd st (InvRSV s) (PWs …)`**. No premise. -/
theorem invBlkGdPV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hKP : RegionOKP K) (hUP : UserOKP K) {s : S} (hE : PrePX st Cs Ω Sg Ac Locks p K m s)
    {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A} {buf length : U64}
    {cap : capability.Cap} (emi : msg.msg_info st s (L.curW s) = ok info)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hl : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (y : (core.result.Result Unit error.Exc) × S × A)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (gd st (InvRSV st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (gd st (InvRSV st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
      z.2.2 = core.result.Result.Ok () ∧
      FinOK (L := L) (gd st (InvRSV st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        (IoRSR st K.toKLayout Locks s) (WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        ar s z.1 z.2.1 := by
  have hR := hE.rsv hKP hUP
  obtain ⟨hJ, hq, hWk, hks, vf⟩ := hE
  have PE := hq.1.1.1
  have hf : K.ksb.val + 13568 ≤ 2 ^ 64 := PE.lay.ksf.2
  have hK := hJ.regionOK
  have hU := hJ.userOK
  have hLA := hJ.ioLayA
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hq
  have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  have hW := mvWrS PE hK hLA (c := L.cpu s) (lk := Locks s) (m := L.mem s)
  have hS0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) := by
    refine ⟨?_, fun hq => absurd hq ?_⟩
    · rw [← OwnMap.affA_fld]; exact PE.curAff
    · rw [← OwnMap.stA_fld]; exact nq_run PE.run
  have hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      SWr (gd st (InvRSV st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st
        (L.curW s) v :=
    fun v hv X => OwnMap.gds_write_state (PE.hT _ PE.cT) hS0 (fun hq => absurd hq (nq_run hv))
  have hWu : ∀ b, UserW K.toKLayout b →
      WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)) b :=
    fun b hb _ _ => Or.inl (Or.inl ⟨hb.1, fun hd => (OwnMap.decW_ok hU hd).2 hb.2⟩)
  by_cases hlen : length < 2#u64
  · obtain ⟨hdec, hrep⟩ := truncAccR (R := InvRSV st K Locks s)
      (gS := gd st (InvRSV st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) hA PE
      hR (fun _ h => rsv_user hKP hUP vf hf h) hW hWu hcs hsK hJ.buf8 C hcap hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := haveI : GRd (gd st (InvRSV st K Locks s)
          (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st (IoRSR st K.toKLayout Locks s) :=
        gdr_sub hR
      truncFinR (gS := gd st (InvRSV st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        hA PE hW (hst _ (Or.inr rfl)) hcs hsK hJ.buf8 C hcap hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · have E := delEntP_of (P := fun s => InvLX st (fun _ => True) K.toKLayout s) hJ hq
      (invCdtJX_of (fun _ h => h)) (hzX_of _ s hJ)
    have hvs := invVsJX_of (st := st) (P := fun s => InvLX st (fun _ => True) K.toKLayout s) (fun _ h => h)
    have hlf := WalkP.lf hWk
    have hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
        (16 ≤ o.val ∨ (¬ TcbSlot K.toKLayout q ∧ NullOrFrame (L.mem s q))) →
        WAll (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)) (core.num.U64.wrapping_add q o) := by
      intro q o hq _ ho h8 h8' _
      obtain ⟨q8, qf⟩ := PE.lay.slot8 q hq
      have hv := PathObl.slot_word_val qf ho
      have hr := PE.lay.slotw q hq _ (slot_inW qf ho)
      have hne : core.num.U64.wrapping_add q o ≠ q := fun e => by
        have := congrArg UScalar.val e; rw [hv] at this; omega
      have ha : Aligned (core.num.U64.wrapping_add q o) := by unfold Aligned; rw [hv]; omega
      exact fun _ _ => Or.inl (Or.inl ⟨ha, OwnMap.nondec_slotw hK hr hne⟩)
    have hw0 : ∀ q, q ∈ K.slots → Locks s q → ¬ TcbSlot K.toKLayout q → NullOrFrame (L.mem s q) →
        ∀ x, (gd st (InvRSV st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))).write
          x q 0#u64 = st.write x q 0#u64 :=
      fun q hq hl hT hn x => OwnMap.gds_write_cap0 hq hT hl hn OwnMap.nof_zero
    obtain ⟨hdec, hrep⟩ := delAcc2X (X := XD K) (R := InvRSV st K Locks s)
      (gS := gd st (InvRSV st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
      hA PE hW hwS hw0 hst E hsK hlen (WalkP.vsX hJ.here.1 hWk)
      (fun b h => xd_vsW hKP hUP vf h) (fun b h hx => rsv_io h hx)
      (fun asid va e he hl' => rsv_leaf hKP (hlf asid va e he).1 (hlf asid va e he).2 hl')
      (fun asid va e he => (hlf asid va e he).2)
      (fun asid va e he _ _ _ => Or.inl (Or.inl ⟨(hUP.kern e (hlf asid va e he).1).1,
        pte_nondec hKP (hlf asid va e he).1⟩)) C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := haveI : GRd (gd st (InvRSV st K Locks s)
          (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st (IoRSR st K.toKLayout Locks s) :=
        gdr_sub hR
      delFin2R (gS := gd st (InvRSV st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s)))
        hA PE hW (hst _ (Or.inr rfl)) E hsK hlen
        (fun sl fp rt asid va hsl hc' hA' => hvs s sl fp rt asid va hJ hsl hc' hA')
        (fun asid va e he => (hlf asid va e he).2) C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- (vmscope gen 10: copy of `invMovePP`) **`move` of accepted VM-epoch PTE-arm runs under rule 8**
(`stepOKV_of_stepOK`, no `nv`). No premise. -/
theorem invMovePV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hKP : RegionOKP K) (hUP : UserOKP K) {q : SProg Bool}
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (PrePX st Cs Ω Sg Ac Locks p K m) (InvRSV st K Locks) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user)) q)
    (hmA : ∀ s, PrePX st Cs Ω Sg Ac Locks p K m s → ∀ d, K.heap d = some .tcb →
      m (fld d OwnMap.oAFFINITY) = L.mem s (fld d OwnMap.oAFFINITY))
    {s s' : S} {a a' : A} (hE : PrePX st Cs Ω Sg Ac Locks p K m s)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local (mguard st (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s a number p =
      ok (true, s', a') := by
  have hq := hE.2.1
  have PE := hq.1.1.1
  have hK := hE.1.regionOK
  have hU := hE.1.userOK
  have hLA := hE.1.ioLayA
  have hg : syscall.handle_invocation_local
      (gd st (InvRSV st K Locks s) (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) ar s a number p =
      ok (true, s', a') :=
    haveI : (GRd (gd st (InvRSV st K Locks s)
        (OwnMap.PWs (L := L) K.toKLayout (L.cpu s) (Locks s) (L.mem s))) st (IoRSR st K.toKLayout Locks s)) :=
      gdr_sub (hE.rsv hKP hUP)
    inv_acc_genR hA PE (mvWrS PE hK hLA) (invSeenR_ofZ hE.1.hz hq) (invPsR_of hq)
      (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => invBlkGdPV hA hKP hUP hE emi hc hl hk y hy) h
  rw [inv_hp hp (Narrow.gd _ _ _) (AltOf.pre hE) a] at hg
  rw [inv_hp hp (Narrow.mguard _ _) (AltOf.pre hE) a]
  exact interp_mguard_mono (fun x y hs => stepOKP_of_stepOKV (stepOKV_of_stepOK hKP.base hs)) q s a _
    (OwnMap.run_gds_mguard hK hU (hmA s hE) q hg)

end mv

section lp
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP}
  {m : U64 → U64}

/-- (vmscope gen 10: copy of `inv_isProgOnP`) **`IsProgOn` of the VM-epoch PTE-arm path over `InvRSV`'s
alternatives**. No premise. -/
theorem inv_isProgOnPV (hA : P0.ArchTotal ar) (hKP : RegionOKP K) (hUP : UserOKP K) :
    IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (PrePX st Cs Ω Sg Ac Locks p K m) (InvRSV st K Locks) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user)) (R.invBodyG number p) := by
  have hSC : InvSlotCN st K.toKLayout p (PrePX st Cs Ω Sg Ac Locks p K m) := fun s hE => by
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hE.2.1
    exact ⟨hsK, cp, cr, cg, cgb, hcs⟩
  exact (inv_isProgOnR (Locks := Locks) (m0 := m) hA (P := PrePX st Cs Ω Sg Ac Locks p K m)
    (fun _ h => h.2.1.1.1.1) hSC (inv_isProg S number p)).mono
    (fun y ⟨s, hE, Al⟩ => ⟨s, hE, Al.anti (hE.rsv hKP hUP)⟩)

/-- (vmscope gen 10) **`PathObl` of the VM-epoch PTE-arm path under rule 8** (module docstring). No premise. -/
theorem invOblPV (hA : P0.ArchTotal ar) (hKP : RegionOKP K) (hUP : UserOKP K) :
    PathObl st (fun m s a => syscall.handle_invocation_local m ar s a number p) (fun b => b = true)
      (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) Locks
      (PrePX st Cs Ω Sg Ac Locks p K m) (InvRSV st K Locks) (InvWSP st K Locks) (IoDS (st := st)) := by
  have hp := inv_isProgOnPV (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks)
    (number := number) (p := p) (m := m) hA hKP hUP
  refine ⟨?_, ?_, rsv_read_own hKP, wsp_write_own hKP, wsp_aligned, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact invAccPV hA hKP hUP hE h
  · intro s a r hE h hn s' r' Al h'
    exact invDecPV hA hKP hUP hp hE h hn Al h'
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (invDecPV hA hKP hUP hp hE h Bool.false_ne_true (Alt.refl s) h).2.2
    · exact invMovePV hA hKP hUP hp (fun _ h => h.2.1.1.1.2) hE h

/-- (vmscope gen 10: copy of `invRaPP`) **`read_aligned` of the VM-epoch PTE-arm path**. No premise. -/
theorem invRaPV (hA : P0.ArchTotal ar) (hKP : RegionOKP K) (hUP : UserOKP K) (hm : E2E.MasksWr st) :
    ∀ s s' a r, PrePX st Cs Ω Sg Ac Locks p K m s →
      Alt st (InvRSV st K Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s s' →
      syscall.handle_invocation_local st ar s' a number p = ok r →
      syscall.handle_invocation_local (guard st (fun b => Aligned b) (fun _ => True)) ar s' a number p = ok r := by
  intro s s' a r hE Al h
  have hp := inv_isProgOnPV (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks)
    (number := number) (p := p) (m := m) hA hKP hUP
  have hz := inv_noZero number p
  by_cases hac : ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)
  · obtain ⟨s1, a1, h0⟩ := hac
    have hg := invAccPV hA hKP hUP hE h0
    rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1.1) (fun w hw => hw.1) _ hz s s' a true s1 a1
      Al.ksb Al.cpu Al.masks Al.read hg
    have hs := interp_to (st := st) (st' := st) (fun _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      rfl rfl rfl _ hz s' a _ hg'
    show syscall.handle_invocation_local _ ar s' a number p = ok r
    rw [inv_hp hp (Narrow.self st) ⟨s, hE, Al⟩ a] at h
    rw [inv_hp hp (Narrow.guard _ _ _) ⟨s, hE, Al⟩ a]
    rw [hs] at h
    rw [← h]
    exact interp_mono (fun _ hw => hw.1.1) (fun _ _ => trivial) _ hz s' a _ hg'
  · obtain ⟨r0, h0⟩ := inv_total (st := st) hA number p s a
    have hr0 : r0.1 ≠ true := by
      obtain ⟨b, z, c⟩ := r0
      intro e
      change b = true at e
      subst e
      exact hac ⟨z, c, h0⟩
    exact inv_ra_decR hA hE.2.1.1.1.1 (invSeenR_ofZ hE.1.hz hE.2.1) (Al.anti (hE.rsv hKP hUP)) h0 hr0 h

/-- (vmscope gen 10: copy of `invUfPP`) **`user_free` of the VM-epoch PTE-arm path**: `hCs` (`Cs` below 64), [P]
`hlk` (the locks are kept by an aligned user write at an `InvLX` state, VX8's `InvPremX.lk`). `PrePX` is kept by
`InvLX.wr`, VX9D's `invQFP_wrX` and `walkP_wr`. -/
theorem invUfPV (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ s b v, InvLX st (fun _ => True) K.toKLayout s → b ∈ K.user → Aligned b →
      Locks (L.wr s b v) = Locks s) :
    ∀ s b v, PrePX st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      PrePX st Cs Ω Sg Ac Locks p K m (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        InvRSV st K Locks (L.wr s b v) = InvRSV st K Locks s ∧
        InvWSP st K Locks (L.wr s b v) = InvWSP st K Locks s ∧ IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro s b v hE hb hba
  obtain ⟨hJ, hq, hWk, hks, vf⟩ := hE
  have P := hq.1.1.1
  have el := hlk s b v hJ hb hba
  obtain ⟨e1, e2, e3⟩ := ioRWDS_wrI hJ P hb hba v el
  refine ⟨⟨hJ.wr hb hba v, invQFP_wrX hJ.ul hCs hJ.here.1 hq hb hba v el, walkP_wr hb hba v hWk, hks, vf⟩,
    el, ?_, ?_, e3⟩
  · funext x
    unfold InvRSV InvRSP IoRSP
    rw [e1, el]
  · funext x
    unfold InvWSP IoWSP
    rw [e2, el]

end lp

/-! ## `ReadOnce` -/

section ro
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (vmscope gen 10: copy of `invBlkPL`) **The `length ≥ 2` arm of the PTE-arm decode block on
`guard st (IoRSPV s) (IoWSP s)`** (no user word and no VCPU data word read). No premise. -/
theorem invBlkPLV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) {s : S} (hE : PrePX st Cs Ω Sg Ac Locks p K m s)
    (hL : InvLen st s)
    {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A} {buf length : U64}
    {cap : capability.Cap} (emi : msg.msg_info st s (L.curW s) = ok info)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hl : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (y : (core.result.Result Unit error.Exc) × S × A)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (guard st (IoRSPV st K Locks s) (IoWSP st K Locks s)) ar s2 a1
        info.label length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (guard st (IoRSPV st K Locks s) (IoWSP st K Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
      z.2.2 = core.result.Result.Ok () ∧
      FinOK (L := L) (guard st (IoRSPV st K Locks s) (IoWSP st K Locks s))
        (IoRSR st K.toKLayout Locks s) (IoWSP st K Locks s) ar s z.1 z.2.1 := by
  obtain ⟨hJ, hq, hWk, hks, vf⟩ := hE
  have PE := hq.1.1.1
  have hf : K.ksb.val + 13568 ≤ 2 ^ 64 := PE.lay.ksf.2
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hq
  have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  have hW : IoWr st (IoWSP st K Locks s) K.heap.scBits s := PE.ioWr.mono (fun _ h => Or.inl h)
  have hlen : ¬ length < 2#u64 := len_ge2 (hL (L.curW s) info (cur_thread_ok s) emi) hl
  have E := delEntP_of (P := fun s => InvLX st (fun _ => True) K.toKLayout s) hJ hq
    (invCdtJX_of (fun _ h => h)) (hzX_of _ s hJ)
  have hvs := invVsJX_of (st := st) (P := fun s => InvLX st (fun _ => True) K.toKLayout s) (fun _ h => h)
  have hlf := WalkP.lf hWk
  obtain ⟨hdec, hrep⟩ := delAccX (X := XD K) (R := IoRSPV st K Locks s) (W := IoWSP st K Locks s)
    (gS := guard st (IoRSPV st K Locks s) (IoWSP st K Locks s)) hA PE hW (fun b hb => Or.inl hb) E hsK hlen
    (WalkP.vsX hJ.here.1 hWk) (fun b h => xd_vsW hK hU vf h) (fun b h hx => rsvi_io h hx)
    (fun asid va e he hl' => rsvi_leaf hK (hlf asid va e he).1 (hlf asid va e he).2 hl')
    (fun asid va e he => (hlf asid va e he).2)
    (fun asid va e he hl' => Or.inr ⟨(hlf asid va e he).1, hl'⟩) C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  obtain ⟨h1, h2⟩ := haveI : (GRd (guard st (IoRSPV st K Locks s) (IoWSP st K Locks s)) st
      (IoRSR st K.toKLayout Locks s)) := grd_sub (fun _ h => rsvi_ioRSR hK hU hks vf hf h)
    delFinR (gS := guard st (IoRSPV st K Locks s) (IoWSP st K Locks s)) hA PE hW
    (Or.inl PE.stw.2) E hsK hlen
    (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hJ hsl hc hA)
    (fun asid va e he => (hlf asid va e he).2) C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

/-- (vmscope gen 10: copy of `invAccPL`) **An accepted VM-epoch PTE-arm run with `InvLen` runs on
`guard st (IoRSPV s) (IoWSP s)`.** No premise. -/
theorem invAccPLV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) {s s' : S} {a a' : A}
    (hE : PrePX st Cs Ω Sg Ac Locks p K m s) (hL : InvLen st s)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local (guard st (IoRSPV st K Locks s) (IoWSP st K Locks s)) ar s a number p =
      ok (true, s', a') := by
  have hq := hE.2.1
  have PE := hq.1.1.1
  have hf : K.ksb.val + 13568 ≤ 2 ^ 64 := PE.lay.ksf.2
  haveI : GRd (guard st (IoRSPV st K Locks s) (IoWSP st K Locks s)) st (IoRSR st K.toKLayout Locks s) :=
    grd_sub (fun _ h => rsvi_ioRSR hK hU hE.2.2.2.1 hE.2.2.2.2 hf h)
  exact inv_acc_genR (W := IoWSP st K Locks s) hA PE (PE.ioWr.mono (fun _ h => Or.inl h))
    (invSeenR_ofZ hE.1.hz hq) (invPsR_of hq)
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => invBlkPLV hA hK hU hE hL emi hc hl hk y hy) h

/-- (vmscope gen 10: copy of `invRoPP`) **`ReadOnce` of the VM-epoch PTE-arm path**. No premise. -/
theorem invRoPV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP}
    {m : U64 → U64} (hKP : RegionOKP K) (hUP : UserOKP K) :
    ReadOnce st ar (R.invBodyG number p) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)
      (PrePX st Cs Ω Sg Ac Locks p K m) (InvRSV st K Locks) := by
  intro s s' a r hE Al h
  have hp := inv_isProgOnPV (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks)
    (number := number) (p := p) (m := m) hA hKP hUP
  have hz := inv_noZero number p
  by_cases hac : ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)
  · obtain ⟨s1, a1, h0⟩ := hac
    have hg := invAccPV hA hKP hUP hE h0
    rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
    by_cases hL : InvLen st s
    · have hg2 := invAccPLV hA hKP hUP hE hL h0
      rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg2
      have o1 : Once st ar (IoRSPV st K Locks s) (· ∈ K.user) ∅ ∅ (R.invBodyG number p) s a :=
        once_of_guardG (fun w hw => hw.1.1.2.1) _ hz ∅ ∅ s a _ hg2
      have o2 := onceU_monoR (fun _ h => rsvi_rsv h) _ ∅ ∅ ∅ s a o1 subset_rfl
      exact once_agreeJ hm (fun w hw => hw.1.1) (fun w hw => hw.1) _ hz s s' a _ ∅ ∅ Al.ksb Al.cpu Al.masks
        (fun w hw => Al.read w hw) hg o2
    · have h0' : interp st ar (R.invBodyG number p) s a = ok (true, s1, a1) := by
        rw [← inv_hp hp (Narrow.self st) (AltOf.pre hE) a]; exact h0
      have hent := invU_entOnce (Locks := Locks) hA
        (P := fun s => (InvLX st (fun _ => True) K.toKLayout s ∧
          InvQFP st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ ¬ InvLen st s)
        (fun _ h => h.1.2.1.1.1) (fun s h x hx => (invSeenR_ofZ h.1.1.hz h.1.2 x hx).1)
        (fun s h => ⟨(invPsR_of h.1.2).1.1, (invPsR_of h.1.2).2.1⟩)
        (invU_decOncePV (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) hA)
        s a _ ⟨⟨hE.1, hE.2.1⟩, hL⟩ ⟨s1, a1, h0⟩ h0'
      have o1 := once_meetG (G := InvRSV st K Locks s) (W := InvWSP st K Locks s) (R' := InvRSV st K Locks s)
        (fun _ hg _ => hg) _ hz ∅ ∅ ∅ s a _ hg hent subset_rfl
      exact once_agreeJ hm (fun w hw => hw.1.1) (fun w hw => hw.1) _ hz s s' a _ ∅ ∅ Al.ksb Al.cpu Al.masks
        (fun w hw => Al.read w hw) hg o1
  · obtain ⟨r0, h0⟩ := inv_total (st := st) hA number p s a
    have hr0 : r0.1 ≠ true := by
      obtain ⟨b, z, c⟩ := r0
      intro e
      change b = true at e
      subst e
      exact hac ⟨z, c, h0⟩
    have h' : syscall.handle_invocation_local st ar s' a number p = ok r := by
      rw [inv_hp hp (Narrow.self st) ⟨s, hE, Al⟩ a]; exact h
    have hg := inv_dec_guardRSR hA hE.2.1.1.1.1 (invSeenR_ofZ hE.1.hz hE.2.1)
      (Al.anti (hE.rsv hKP hUP)) h0 hr0 h'
    rw [inv_hp hp (Narrow.guard _ _ _) ⟨s, hE, Al⟩ a] at hg
    exact onceU_monoR (hE.rsv hKP hUP) _ ∅ ∅ ∅ s' a
      (once_of_guardG (fun w hw => hw.1.2.1) _ hz ∅ ∅ s' a _ hg) subset_rfl

end ro

/-! ## The path -/

section path
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type}

/-- (vmscope gen 10) **The Delete PTE-arm local path for `ownP` at a layout with VCPUs, without a P3 bundle**
(module docstring). Premises: `hA`, [P] `hm`, `hCs`, [P] `hlk`. -/
noncomputable def inv_localPathPV (ar : machine.Arch A) (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} (number : I64) (p : localinv.Plan) (hm : E2E.MasksWr st)
    (hCs : ∀ c ∈ Cs, c.val < 64) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hlk : ∀ s b v, InvLX st (fun _ => True) K.toKLayout s → b ∈ K.user → Aligned b →
      Locks (L.wr s b v) = Locks s) :
    E2E.LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := invBody S number p
  p := R.invBodyG number p
  Acc := fun b => b = true
  Locks := Locks
  Pre := PrePX st Cs Ω Sg Ac Locks p K m
  RS := InvRSV st K Locks
  WS := InvWSP st K Locks
  DS := IoDS (st := st)
  isProg := inv_isProgOnPV hA hK hU
  obl := invOblPV hA hK hU
  side := ⟨invRaPV hA hK hU hm, fun _ _ _ hx => hx.1.1,
    fun x hx => Fl4Proofs.P2.ko_aligned hK.base.base hU.base.base x hx, invUfPV hCs hlk⟩
  once := invRoPV hA hm hK hU
  total := fun s a => inv_total hA number p s a
  masks := hm

end path

end Fl4Proofs.P2.E2EP

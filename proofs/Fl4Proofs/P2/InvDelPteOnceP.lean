/-
# P2 (line invj, generation 8): the Delete PTE-arm path as a `LocalPath` for `ownP` (`inv_localPathPP`)

The remaining obligations of the PTE-arm path at `Pre := PreP` (P2/InvDelPteAccP.lean), read set `InvRSP`, write
set `InvWSP`, decline set `IoDS`, and the path itself:

* `invU_decOnceP`, `invPlanD_wrP`: scripted copies of `invU_decOnce` / `invPlanD_wrF` at `InvQFP` (`del_coreP`
  for `del_core`);
* **`inv_isProgOnP`** (`IsProgOn` over `InvRSP`'s alternatives, no premise: `inv_isProgOnR` with the pruned body's
  tree `R.invBodyG`, `hSC` from `del_coreP`, `Alt.anti`);
* **`invOblPP`** (`PathObl`: `invAccPP`, `invDecPP`, `invRSP_read_own`, `invWSP_write_own`, `invWSP_aligned`,
  `invMovePP` with `hmA` from `PreP` itself — the TCB `AFFINITY` agreement is `IoQ`'s second half, carried in
  `Pre` and kept by user writes, `ioQ_wr`);
* **`invRaPP`** (`read_aligned`: accepted runs by `invAccPP` + `interp_agree`, declines by `inv_ra_decR`),
  **`invUfPP`** (`user_free`: `PreP` and the sets kept by an aligned user write; [P] `hlk` the locks are kept, as
  `InvPremW.lk`), **`invSidePP`**;
* **`invRoPP`** (`ReadOnce`): declines by `inv_dec_guardRSR` + `once_of_guardG`; accepted runs with `InvLen` by the
  accepted run on `guard st (IoRSP s) (IoWSP s)` (`invAccPL`, from `invBlkPL`: the `length ≥ 2` arm, `len_ge2`),
  then `once_of_guardG` / `onceU_monoR` / `once_agreeJ`; truncated accepted runs by `invU_entOnce` +
  `invU_decOnceP` (`Once` for `InvCMRS s` at the entry), moved to `InvRSP s` along the run on
  `guard st (InvRSP s) (InvWSP s)` by `once_meetG` (P2/OnceMeet.lean), then `once_agreeJ`;
* **`inv_localPathPP`**: the `LocalPath (ownP K) …` at a layout with `RegionOKP`, `UserOKP`, no VCPU.

Premises of `inv_localPathPP`: `hA`, [P] `hm` (`MasksWr`), `hCs` (`Cs` below 64, from a bundle state at the slot),
[P] `hlk` (locks kept by an aligned user write). No [J]/[W]. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteDecP
import Fl4Proofs.P2.InvDelPteRaR
import Fl4Proofs.P2.OnceMeet
import Fl4Proofs.P2.InvURoTr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section restP
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- (invj gen 8) `invPlanD_wrF` at `InvQFP`: the plan survives a user write at a bundle state. -/
theorem invPlanD_wrP {p : localinv.Plan} :
    ∀ K m s b v, SlJAt (L := L) K s → InvQFP st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      InvPlanD st p (L.wr s b v) := by
  intro K m s b v hJ hqf hb hba
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, C, hcap, hsK, -, -, hC, hcl, hCs, -⟩ := del_coreP hqf
  obtain ⟨⟨hio, ⟨t, info, ex, ht, hi, hpw⟩, harm, -⟩, -⟩ := hqf
  have P := hio.1
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have et : t = L.curW s := by rw [cur_thread_ok] at ht; exact (ok_inj_ff ht).symm
  subst et
  have hlbl := (harm _ info (cur_thread_ok s) hi).1
  rw [hlbl] at hpw
  refine ⟨L.curW s, info, ex, ?_, ?_, ?_⟩
  · rw [cur_thread_ok, hJ.curW_wr hb hba v]
  · rw [msgInfo_wr hJ hb hba v hT P.tA]; exact hi
  · rw [hlbl, planDel_userWr hJ P hb hba v hsK hcap hC hcl (fun p r m y hp hm => (hCs p r m y hp hm).1) ex]
    exact hpw

/-- (invj gen 8) **The decode onward of an accepted truncated PTE-arm Delete reads once** (`invU_decOnce` at `InvQFP`) (`InvUDecOnceW` at
`Pre ∧ ¬ InvLen`; module docstring). No premise. -/
theorem invU_decOnceP (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {m0 : U64 → U64} :
    InvUDecOnceW st ar number p K Locks
      (fun s => (SlJAt (L := L) K s ∧ InvQFP st Cs Ω Sg Ac Locks p K m0 s) ∧ ¬ InvLen st s) := by
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
    invU_tailOnce hA P hcs hsl (invBufJ8_of hJ) C ecap hlen' er hk' Wd' T') hk Wd1


end restP

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout fld)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section lp
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP}
  {m : U64 → U64}

include hA in
/-- (invj gen 8) **`IsProgOn` of the PTE-arm path over `InvRSP`'s alternatives** (module docstring). No premise. -/
theorem inv_isProgOnP (hKP : RegionOKP K) :
    IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (PreP st Cs Ω Sg Ac Locks p K m) (InvRSP st K Locks) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user)) (R.invBodyG number p) := by
  have hSC : InvSlotCN st K.toKLayout p (PreP st Cs Ω Sg Ac Locks p K m) := fun s hE => by
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hE.2.1
    exact ⟨hsK, cp, cr, cg, cgb, hcs⟩
  exact (inv_isProgOnR (Locks := Locks) (m0 := m) hA (P := PreP st Cs Ω Sg Ac Locks p K m)
    (fun _ h => h.2.1.1.1.1) hSC (inv_isProg S number p)).mono
    (fun y ⟨s, hE, Al⟩ => ⟨s, hE, Al.anti (fun x hx => ioRSP_inv (ioRSR_P hKP (ksNoE_conv hE.2.2.choose_spec.1) hx))⟩)

include hA in
/-- (invj gen 8) **`PathObl` of the PTE-arm path under rule 8** (module docstring). No premise. -/
theorem invOblPP (hKP : RegionOKP K) (hUP : UserOKP K) (nv : K.vcpus = ∅) :
    PathObl st (fun m s a => syscall.handle_invocation_local m ar s a number p) (fun b => b = true)
      (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) Locks
      (PreP st Cs Ω Sg Ac Locks p K m) (InvRSP st K Locks) (InvWSP st K Locks) (IoDS (st := st)) := by
  have hp := inv_isProgOnP (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (number := number) (p := p)
    (m := m) hA hKP
  refine ⟨?_, ?_, invRSP_read_own nv, invWSP_write_own hKP nv, invWSP_aligned, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact invAccPP hA hKP hUP nv hE h
  · intro s a r hE h hn s' r' Al h'
    exact invDecPP hA hKP nv hp hE h hn Al h'
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (invDecPP hA hKP nv hp hE h Bool.false_ne_true (Alt.refl s) h).2.2
    · exact invMovePP hA hKP hUP nv hp (fun _ h => h.2.1.1.1.2) hE h

include hA in
/-- (invj gen 8) **`read_aligned` of the PTE-arm path** (module docstring). No premise. -/
theorem invRaPP (hKP : RegionOKP K) (hUP : UserOKP K) (nv : K.vcpus = ∅) (hm : E2E.MasksWr st) :
    ∀ s s' a r, PreP st Cs Ω Sg Ac Locks p K m s →
      Alt st (InvRSP st K Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s s' →
      syscall.handle_invocation_local st ar s' a number p = ok r →
      syscall.handle_invocation_local (guard st (fun b => Aligned b) (fun _ => True)) ar s' a number p = ok r := by
  intro s s' a r hE Al h
  have hp := inv_isProgOnP (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (number := number) (p := p)
    (m := m) hA hKP
  have hz := inv_noZero number p
  by_cases hac : ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)
  · obtain ⟨s1, a1, h0⟩ := hac
    have hg := invAccPP hA hKP hUP nv hE h0
    rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) _ hz s s' a true s1 a1
      Al.ksb Al.cpu Al.masks Al.read hg
    have hs := interp_to (st := st) (st' := st) (fun _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      rfl rfl rfl _ hz s' a _ hg'
    show syscall.handle_invocation_local _ ar s' a number p = ok r
    rw [inv_hp hp (Narrow.self st) ⟨s, hE, Al⟩ a] at h
    rw [inv_hp hp (Narrow.guard _ _ _) ⟨s, hE, Al⟩ a]
    rw [hs] at h
    rw [← h]
    exact interp_mono (fun _ hw => hw.1) (fun _ _ => trivial) _ hz s' a _ hg'
  · obtain ⟨r0, h0⟩ := inv_total (st := st) hA number p s a
    have hr0 : r0.1 ≠ true := by
      obtain ⟨b, z, c⟩ := r0
      intro e
      change b = true at e
      subst e
      exact hac ⟨z, c, h0⟩
    have hks := ksNoE_conv hE.2.2.choose_spec.1
    exact inv_ra_decR hA hE.2.1.1.1.1 (invSeenR_of hE.1 hE.2.1)
      (Al.anti (fun x hx => ioRSP_inv (ioRSR_P hKP hks hx))) h0 hr0 h

/-- (invj gen 8) **`user_free` of the PTE-arm path** (module docstring): `hCs` (`Cs` below 64), [P] `hlk` (the locks
are kept by an aligned user write at a bundle state, as `InvPremW.lk`). -/
theorem invUfPP (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ (K' : KLayout) (s : S) (b v : U64), SlJAt (L := L) K' s → b ∈ K'.user → Aligned b →
      Locks (L.wr s b v) = Locks s) :
    ∀ s b v, PreP st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      PreP st Cs Ω Sg Ac Locks p K m (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        InvRSP st K Locks (L.wr s b v) = InvRSP st K Locks s ∧
        InvWSP st K Locks (L.wr s b v) = InvWSP st K Locks s ∧ IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro s b v hE hb hba
  obtain ⟨hJ, hq, m1, hc, hag⟩ := hE
  have hq0 := hq
  obtain ⟨⟨hio, hpd, harm, hlks⟩, hlk0⟩ := hq
  have P := hio.1
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have el := hlk K.toKLayout s b v hJ hb hba
  have ecur := hJ.curW_wr hb hba v
  have emsg := msgInfo_wr hJ hb hba v hT P.tA
  have hct : ∀ t, sched.cur_thread st (L.wr s b v) = ok t → t = L.curW s := by
    intro t ht
    rw [cur_thread_ok, ecur] at ht
    exact (ok_inj_ff ht).symm
  obtain ⟨e1, e2, e3⟩ := hJ.ioRWDS_wrSt hb hba v el
  refine ⟨⟨hJ.userWr hb v, ⟨⟨ioQ_wr (ioPre_wr_hIw (Ω := Ω) (Sg := Sg) (Ac := Ac) hCs) K.toKLayout m s b v hJ hio hb hba,
    invPlanD_wrP K.toKLayout m s b v hJ hq0 hb hba, ?_, ?_⟩, invLk_wr hJ P hlk0 hb hba v⟩, m1, hc, ?_⟩,
    el, ?_, ?_, e3⟩
  · intro t info ht hi
    obtain rfl := hct t ht
    rw [emsg] at hi
    exact harm _ info (cur_thread_ok s) hi
  · intro i x hi hx
    rw [el]
    exact hlks i x hi hx
  · intro w hr hp hu ha
    rw [mem_wr_ne' hba ha (fun e => hu (e ▸ hb))]
    exact hag w hr hp hu ha
  · funext x
    unfold InvRSP IoRSP
    rw [e1, el]
  · funext x
    unfold InvWSP IoWSP
    rw [e2, el]

end lp

/-! ## `ReadOnce` -/

section ro
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- A message length of at least 2 gives a decode length of at least 2 (the clamp is to 4). -/
theorem len_ge2 {info : msginfo.MessageInfo} {buf length : U64} (h : 2 ≤ info.length.val)
    (hl : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length) : ¬ length < 2#u64 := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by simp [msg.N_MSG_REGISTERS]
  intro hc
  have hc' : length.val < 2 := by have := hc; scalar_tac
  by_cases h1 : info.length > msg.N_MSG_REGISTERS
  · rw [if_pos h1] at hl
    by_cases h2 : buf = 0#u64
    · rw [if_pos h2] at hl
      have e := ok_inj_ff hl
      rw [← e] at hc'
      omega
    · rw [if_neg h2] at hl
      have e := ok_inj_ff hl
      rw [← e] at hc'
      omega
  · rw [if_neg h1] at hl
    have e := ok_inj_ff hl
    rw [← e] at hc'
    omega

/-- (invj gen 8) **The `length ≥ 2` arm of the PTE-arm decode block on `guard st (IoRSP s) (IoWSP s)`** (no user
word read or written). No premise. -/
theorem invBlkPL {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) {s : S} (hE : PreP st Cs Ω Sg Ac Locks p K m s)
    (hL : InvLen st s)
    {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A} {buf length : U64}
    {cap : capability.Cap} (emi : msg.msg_info st s (L.curW s) = ok info)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hl : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (y : (core.result.Result Unit error.Exc) × S × A)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (guard st (IoRSP st K Locks s) (IoWSP st K Locks s)) ar s2 a1
        info.label length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (guard st (IoRSP st K Locks s) (IoWSP st K Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
      z.2.2 = core.result.Result.Ok () ∧
      FinOK (L := L) (guard st (IoRSP st K Locks s) (IoWSP st K Locks s))
        (IoRSR st K.toKLayout Locks s) (IoWSP st K Locks s) ar s z.1 z.2.1 := by
  obtain ⟨hJ, hq, m1, hc, hag⟩ := hE
  have PE := hq.1.1.1
  have hks := ksNoE_conv hc
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hq
  have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  have hW : IoWr st (IoWSP st K Locks s) K.heap.scBits s := PE.ioWr.mono (fun _ h => Or.inl h)
  have hlen : ¬ length < 2#u64 := len_ge2 (hL (L.curW s) info (cur_thread_ok s) emi) hl
  have E := delEntP_of (P := fun s => SlJAt (L := L) K.toKLayout s) hJ hq (invCdtJ_of (fun _ h => h))
    (hz_of _ s hJ)
  have hvs := invVsJ_of (st := st) (P := fun s => SlJAt (L := L) K.toKLayout s) (fun _ h => h)
  have hlf := invLeafJ_of (st := st) (P := fun s => SlJAt (L := L) K.toKLayout s) (fun _ h => h) s hJ
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
  obtain ⟨hdec, hrep⟩ := haveI : (GRd (guard st (IoRSP st K Locks s) (IoWSP st K Locks s)) st
      (IoRSP st K Locks s)) := grd_sub (fun _ h => h)
    delAccPP (gS := guard st (IoRSP st K Locks s) (IoWSP st K Locks s)) hA B hag hc nv
    hK hU PE hW (fun b h => h) E hsK hlen C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  obtain ⟨h1, h2⟩ := haveI : (GRd (guard st (IoRSP st K Locks s) (IoWSP st K Locks s)) st
      (IoRSR st K.toKLayout Locks s)) := grd_sub (fun _ h => ioRSR_P hK hks h)
    delFinR (gS := guard st (IoRSP st K Locks s) (IoWSP st K Locks s)) hA PE hW
    (Or.inl PE.stw.2) E hsK hlen
    (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ hsl hc hA)
    hlf C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

/-- (invj gen 8) **An accepted PTE-arm run with `InvLen` runs on `guard st (IoRSP s) (IoWSP s)`.** No premise. -/
theorem invAccPL {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) {s s' : S} {a a' : A}
    (hE : PreP st Cs Ω Sg Ac Locks p K m s) (hL : InvLen st s)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local (guard st (IoRSP st K Locks s) (IoWSP st K Locks s)) ar s a number p =
      ok (true, s', a') := by
  have hq := hE.2.1
  have PE := hq.1.1.1
  have hks := ksNoE_conv hE.2.2.choose_spec.1
  haveI : GRd (guard st (IoRSP st K Locks s) (IoWSP st K Locks s)) st (IoRSR st K.toKLayout Locks s) :=
    grd_sub (fun _ h => ioRSR_P hK hks h)
  exact inv_acc_genR (W := IoWSP st K Locks s) hA PE (PE.ioWr.mono (fun _ h => Or.inl h))
    (invSeenR_of hE.1 hq) (invPsR_of hq)
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => invBlkPL hA hK hU nv hE hL emi hc hl hk y hy) h

/-- (invj gen 8) **`ReadOnce` of the PTE-arm path** (module docstring). No premise. -/
theorem invRoPP {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP}
    {m : U64 → U64} (hKP : RegionOKP K) (hUP : UserOKP K) (nv : K.vcpus = ∅) :
    ReadOnce st ar (R.invBodyG number p) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)
      (PreP st Cs Ω Sg Ac Locks p K m) (InvRSP st K Locks) := by
  intro s s' a r hE Al h
  have hp := inv_isProgOnP (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (number := number) (p := p)
    (m := m) hA hKP
  have hz := inv_noZero number p
  have hks := ksNoE_conv hE.2.2.choose_spec.1
  by_cases hac : ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)
  · obtain ⟨s1, a1, h0⟩ := hac
    have hg := invAccPP hA hKP hUP nv hE h0
    rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
    by_cases hL : InvLen st s
    · have hg2 := invAccPL hA hKP hUP nv hE hL h0
      rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg2
      have o1 : Once st ar (IoRSP st K Locks s) (· ∈ K.user) ∅ ∅ (R.invBodyG number p) s a :=
        once_of_guardG (fun w hw => hw.1.2.1) _ hz ∅ ∅ s a _ hg2
      have o2 := onceU_monoR (fun _ h => ioRSP_inv h) _ ∅ ∅ ∅ s a o1 subset_rfl
      exact once_agreeJ hm (fun w hw => hw.1) (fun w hw => hw.1) _ hz s s' a _ ∅ ∅ Al.ksb Al.cpu Al.masks
        (fun w hw => Al.read w hw) hg o2
    · have h0' : interp st ar (R.invBodyG number p) s a = ok (true, s1, a1) := by
        rw [← inv_hp hp (Narrow.self st) (AltOf.pre hE) a]; exact h0
      have hent := invU_entOnce (Locks := Locks) hA
        (P := fun s => (SlJAt (L := L) K.toKLayout s ∧ InvQFP st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧
          ¬ InvLen st s)
        (fun _ h => h.1.2.1.1.1) (fun s h x hx => (invSeenR_of h.1.1 h.1.2 x hx).1)
        (fun s h => ⟨(invPsR_of h.1.2).1.1, (invPsR_of h.1.2).2.1⟩)
        (invU_decOnceP (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) hA)
        s a _ ⟨⟨hE.1, hE.2.1⟩, hL⟩ ⟨s1, a1, h0⟩ h0'
      have o1 := once_meetG (G := InvRSP st K Locks s) (W := InvWSP st K Locks s) (R' := InvRSP st K Locks s)
        (fun _ hg _ => hg) _ hz ∅ ∅ ∅ s a _ hg hent subset_rfl
      exact once_agreeJ hm (fun w hw => hw.1) (fun w hw => hw.1) _ hz s s' a _ ∅ ∅ Al.ksb Al.cpu Al.masks
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
    have hg := inv_dec_guardRSR hA hE.2.1.1.1.1 (invSeenR_of hE.1 hE.2.1)
      (Al.anti (fun x hx => ioRSP_inv (ioRSR_P hKP hks hx))) h0 hr0 h'
    rw [inv_hp hp (Narrow.guard _ _ _) ⟨s, hE, Al⟩ a] at hg
    exact onceU_monoR (fun _ h => ioRSP_inv (ioRSR_P hKP hks h)) _ ∅ ∅ ∅ s' a
      (once_of_guardG (fun w hw => hw.1.2.1) _ hz ∅ ∅ s' a _ hg) subset_rfl

end ro

/-! ## The path -/

section path
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type}

/-- (invj gen 8) **The Delete PTE-arm local path for `ownP`** (module docstring). Premises: `hA`, [P] `hm`, `hCs`,
[P] `hlk`. -/
noncomputable def inv_localPathPP (ar : machine.Arch A) (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} (number : I64) (p : localinv.Plan) (hm : E2E.MasksWr st)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ (K' : KLayout) (s : S) (b v : U64), SlJAt (L := L) K' s → b ∈ K'.user → Aligned b →
      Locks (L.wr s b v) = Locks s)
    (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) :
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
  Pre := PreP st Cs Ω Sg Ac Locks p K m
  RS := InvRSP st K Locks
  WS := InvWSP st K Locks
  DS := IoDS (st := st)
  isProg := inv_isProgOnP hA hK
  obl := invOblPP hA hK hU nv
  side := ⟨invRaPP hA hK hU nv hm, fun _ _ _ hx => hx.1,
    fun x hx => Fl4Proofs.P2.ko_aligned hK.base.base hU.base.base x hx, invUfPP hCs hlk⟩
  once := invRoPP hA hm hK hU nv
  total := fun s a => inv_total hA number p s a
  masks := hm

end path

end Fl4Proofs.P2.E2EP

/-
# P2 (line p2sl): `SlThr` for the concrete decided thread

`slThr_sl`: `SlThr` (P2/SlObl.lean) for `slThr st found.1` (P2/SlThr.lean) and the words
`slTW` a run reads of it before `schedulable_here` checks it (trap arm: `REPLY_OBJ`; ReplyRecv
arm: `STATE`, `fault_type`, `SC`); then `sl_pathObl_sl` / `sl_pathSide_sl`.

* `home` (`sl_home`): `syscall.handle_syscall_local.guard_dec` (P2/SlDecG.lean) on
  `guard st (SlRS s) (SlDS s)`, the arms' read facts at the prefix state given by `SlDecIn`;
* `away` (`sl_away`): the same walk at an alternative `s'` on
  `guard st (SlRS s ∪ slTW (slThr s)) ⊤`: the arms' read facts are moved from the prefix state of
  `s` to that of `s'` (`lp_alt`: the two prefixes agree on every `SlRS s` word, by `Alt.read` and
  the prefix's writes; `FltDecT.congr`, `RrDecT.congr`, `RdHead.congr`: every address the facts
  name is built from values of read-set words), the decided thread's own words are `slTW`, and
  its later words are not needed (`AFFINITY` is not this core's);
* `twA`: `slTW` carries alignment (`tw_al`: from the aligned `AFFINITY` word);
* `alt`, `acc`: `slThr_alt`, `slThr_acc` (P2/SlThr.lean).

Premises: `SlDecIn` [W] (each field tagged there): the words a declining arm reads at the
prefix state, apart from the decided thread's, are in `SlRS s`, and when that thread is homed
here its words too; plus `SlPre`, `SlThrIn` (P2/SlObl.lean, P2/SlThr.lean).
`sl_pathObl_sl` / `sl_pathSide_sl` take the premises of `sl_pathObl_dr` / `sl_pathSide_dr`
(P2/SlObl.lean module docstring; `hz : NoZero p` is [P] there, with the call-graph check
`proofs/scratch/callgraph.py`) with `SlThr` replaced by `SlThrIn` and `SlDecIn`.
-/
import Fl4Proofs.P2.SlDecG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-! ## Read facts without the decided thread, monotone and moved between agreeing states -/

/-- `FltDec` without the receiver's words. -/
structure FltDecT (R : U64 → Prop) (X : S) (t : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)
  bm : RdBitmap (L := L) R X
  tm : L.mem X (tmA (L := L) X) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64)
  rh : L.mem X (rhA (L := L) X) ≠ 0#u64 → R (scA (L.mem X (rhA (L := L) X))) ∧
    RdHead (L := L) R X (L.mem X (scA (L.mem X (rhA (L := L) X))))
  fh : R (slotIdx t layout.tcb.SLOT_FAULT_HANDLER) ∧
    R (core.num.U64.wrapping_add (slotIdx t layout.tcb.SLOT_FAULT_HANDLER) 8#u64)
  ep : ∀ ptr b x y g gr, obj.Slot.cap st (slotIdx t layout.tcb.SLOT_FAULT_HANDLER) X =
      ok (capability.Cap.Endpoint ptr b x y g gr) → R (epTSA ptr) ∧ R (epHeadA ptr)

theorem FltDec.of {R : U64 → Prop} {X : S} {t : U64} (D : FltDecT (L := L) R X t)
    (hd : ∀ ptr b x y g gr, obj.Slot.cap st (slotIdx t layout.tcb.SLOT_FAULT_HANDLER) X =
      ok (capability.Cap.Endpoint ptr b x y g gr) → obj.Ep.state st ptr X = ok obj.EP_RECV →
      ∀ d, obj.Ep.head st ptr X = ok d → DestDec (L := L) R X d) :
    FltDec (L := L) R X t :=
  ⟨D.nd, D.dt, D.cd, D.bm, D.tm, D.rh, D.fh, fun ptr b x y g gr h =>
    ⟨(D.ep ptr b x y g gr h).1, (D.ep ptr b x y g gr h).2, hd ptr b x y g gr h⟩⟩

/-- `RrDec` without the replied thread's words. -/
structure RrDecT (R : U64 → Prop) (X : S) (t rptr ep : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)
  bm : RdBitmap (L := L) R X
  tm : L.mem X (tmA (L := L) X) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64)
  rh : L.mem X (rhA (L := L) X) ≠ 0#u64 → R (scA (L.mem X (rhA (L := L) X))) ∧
    RdHead (L := L) R X (L.mem X (scA (L.mem X (rhA (L := L) X))))
  tSt : R (stA t)
  tSc : R (scA t)
  tMx : R (maxA (L.mem X (scA t)))
  tIq : R (inqA t)
  tMi : R (regA t layout.reg.MSG_INFO)
  tBn : R (core.num.U64.wrapping_add t 3368#u64)
  tPr : R (prioA t)
  ntf : ∀ n, obj.Tcb.bound_ntfn st t X = ok n → (n != 0#u64) = true →
    R (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) ∧ R (core.num.U64.wrapping_add n layout.ntfn.SC)
  rRt : R (rTcbA rptr)
  rNx : R (rNextA rptr)
  eTS : R (epTSA ep)

theorem RrDec.of {R : U64 → Prop} {X : S} {t rptr ep : U64} (D : RrDecT (L := L) R X t rptr ep)
    (hu : ∀ u, obj.Reply.tcb st rptr X = ok u → u ≠ 0#u64 → UDec (L := L) R X u) : RrDec (L := L) R X t rptr ep :=
  ⟨D.nd, D.dt, D.cd, D.bm, D.tm, D.rh, D.tSt, D.tSc, D.tMx, D.tIq, D.tMi, D.tBn, D.tPr, D.ntf, D.rRt, D.rNx,
    D.eTS, hu⟩

section mono
variable {R R' : U64 → Prop} (hR : ∀ b, R b → R' b)
include hR

theorem RdHead.mono {X : S} {sc : obj.Sc} (h : RdHead (L := L) R X sc) : RdHead (L := L) R' X sc :=
  ⟨hR _ h.1, hR _ h.2.1, hR _ h.2.2⟩

theorem RdBitmap.mono {X : S} (h : RdBitmap (L := L) R X) : RdBitmap (L := L) R' X :=
  ⟨hR _ h.1, fun i hi => hR _ (h.2 i hi)⟩

theorem FltDecT.mono {X : S} {t : U64} (D : FltDecT (L := L) R X t) : FltDecT (L := L) R' X t :=
  ⟨fun o h1 h2 => hR _ (D.nd o h1 h2), hR _ D.dt, hR _ D.cd, RdBitmap.mono hR D.bm, fun h => hR _ (D.tm h),
    fun h => ⟨hR _ (D.rh h).1, RdHead.mono hR (D.rh h).2⟩, ⟨hR _ D.fh.1, hR _ D.fh.2⟩,
    fun ptr b x y g gr hc => ⟨hR _ (D.ep ptr b x y g gr hc).1, hR _ (D.ep ptr b x y g gr hc).2⟩⟩

theorem RrDecT.mono {X : S} {t rptr ep : U64} (D : RrDecT (L := L) R X t rptr ep) :
    RrDecT (L := L) R' X t rptr ep :=
  ⟨fun o h1 h2 => hR _ (D.nd o h1 h2), hR _ D.dt, hR _ D.cd, RdBitmap.mono hR D.bm, fun h => hR _ (D.tm h),
    fun h => ⟨hR _ (D.rh h).1, RdHead.mono hR (D.rh h).2⟩, hR _ D.tSt, hR _ D.tSc, hR _ D.tMx, hR _ D.tIq,
    hR _ D.tMi, hR _ D.tBn, hR _ D.tPr, fun n h1 h2 => ⟨hR _ (D.ntf n h1 h2).1, hR _ (D.ntf n h1 h2).2⟩,
    hR _ D.rRt, hR _ D.rNx, hR _ D.eTS⟩

end mono

section congr
variable {R : U64 → Prop} {X X' : S} (hk : L.ksb X' = L.ksb X) (hc : L.cpu X' = L.cpu X)
  (hag : ∀ b, R b → L.mem X' b = L.mem X b)

include hag in
theorem RdHead.congr {sc : obj.Sc} (h : RdHead (L := L) R X sc) : RdHead (L := L) R X' sc := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : L.rhead X' sc = L.rhead X sc := by unfold LawfulStore.rhead; exact hag _ h1
  unfold RdHead
  rw [e]
  exact ⟨h1, h2, h3⟩

include hk hc in
theorem RdBitmap.congr (h : RdBitmap (L := L) R X) : RdBitmap (L := L) R X' := by
  unfold RdBitmap at h ⊢
  simp only [slDS_node hk hc]
  exact h

include hk hc hag in
theorem FltDecT.congr {t : U64} (D : FltDecT (L := L) R X t) : FltDecT (L := L) R X' t := by
  have rtm : R (tmA (L := L) X) := D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have rrh : R (rhA (L := L) X) := D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have etm : tmA (L := L) X' = tmA (L := L) X := slDS_node hk hc
  have erh : rhA (L := L) X' = rhA (L := L) X := slDS_node hk hc
  refine ⟨fun o h1 h2 => by rw [slDS_node hk hc]; exact D.nd o h1 h2, by rw [hk]; exact D.dt,
    by rw [hk]; exact D.cd, RdBitmap.congr hk hc D.bm, ?_, ?_, D.fh, ?_⟩
  · rw [etm, hag _ rtm]; exact D.tm
  · rw [erh, hag _ rrh]
    intro h
    obtain ⟨h1, h2⟩ := D.rh h
    refine ⟨h1, ?_⟩
    rw [hag _ h1]
    exact RdHead.congr hag h2
  · intro ptr b x y g gr h
    exact D.ep ptr b x y g gr ((cap_congr (hag _ D.fh.1) (hag _ D.fh.2)).symm.trans h)

include hk hc hag in
theorem RrDecT.congr {t rptr ep : U64} (D : RrDecT (L := L) R X t rptr ep) : RrDecT (L := L) R X' t rptr ep := by
  have rtm : R (tmA (L := L) X) := D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have rrh : R (rhA (L := L) X) := D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have etm : tmA (L := L) X' = tmA (L := L) X := slDS_node hk hc
  have erh : rhA (L := L) X' = rhA (L := L) X := slDS_node hk hc
  have eb : obj.Tcb.bound_ntfn st t X' = obj.Tcb.bound_ntfn st t X := by
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (st := st) X' t), eq_of_spec_fd (obj.Tcb.bound_ntfn.val (st := st) X t)]
    unfold boundA
    rw [hag _ D.tBn]
  refine ⟨fun o h1 h2 => by rw [slDS_node hk hc]; exact D.nd o h1 h2, by rw [hk]; exact D.dt,
    by rw [hk]; exact D.cd, RdBitmap.congr hk hc D.bm, ?_, ?_, D.tSt, D.tSc, by rw [hag _ D.tSc]; exact D.tMx,
    D.tIq, D.tMi, D.tBn, D.tPr, fun n hn => D.ntf n (by rw [← eb]; exact hn), D.rRt, D.rNx, D.eTS⟩
  · rw [etm, hag _ rtm]; exact D.tm
  · rw [erh, hag _ rrh]
    intro h
    obtain ⟨h1, h2⟩ := D.rh h
    refine ⟨h1, ?_⟩
    rw [hag _ h1]
    exact RdHead.congr hag h2

end congr

/-! ## The prefix at an alternative -/

/-- Two states agreeing on aligned `Q`-words still agree after the same write. -/
theorem agree_wr {Q : U64 → Prop} (hQ : ∀ b, Q b → Aligned b) {x y : S} {w v : U64} (hw : Aligned w)
    (h : ∀ b, Q b → L.mem y b = L.mem x b) : ∀ b, Q b → L.mem (L.wr y w v) b = L.mem (L.wr x w v) b := by
  intro b hb
  rw [L.mem_wr y w v b hw (hQ b hb), L.mem_wr x w v b hw (hQ b hb)]
  split
  · rfl
  · exact h b hb

variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The prefix at a state agreeing with `s` on `Q`** (with `s`'s kernel base, core and
current thread; `Q` aligned and holding the words the prefix reads): the prefix at `s` with the
same Arch state ends in the same Arch state and at a state agreeing on `Q`. -/
theorem lp_alt {T : Set U64} (hA : P0.ArchTotal ar) {Q : U64 → Prop} (hQ : ∀ b, Q b → Aligned b)
    {s s' X' : S} {a a1' : A} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hk : L.ksb s' = L.ksb s) (hc : L.cpu s' = L.cpu s) (hcur : L.curW s' = L.curW s)
    (hag : ∀ b, Q b → L.mem s' b = L.mem s b)
    (hnx : Q (regA (L.curW s) layout.reg.NEXT_IP)) (hct : Q (ctA (L := L) s)) (hcn : Q (cnA (L := L) s))
    (hP' : LocalPre (st := st) ar s' a (X', a1')) :
    ∃ X, LocalPre (st := st) ar s a (X, a1') ∧ ∀ b, Q b → L.mem X' b = L.mem X b := by
  obtain ⟨t, nx, s1', et, enx, es1, eu⟩ := hP'
  have et' : t = L.curW s := by rw [cur_thread_ok] at et; rw [← hcur]; exact (ok_inj_ff et).symm
  subst et'
  have ht' := hT _ hcT
  have e1 := set_fip_wr ht' es1
  have hN' : NodePlaced st T s' (L.cpu s') := by rw [hc]; exact NodePlaced.of_ksb hk hN
  have hN1' : NodePlaced st T s1' (L.cpu s1') := by rw [e1, LawfulStore.cpu_wr]; exact hN'.wr
  obtain ⟨n1, hn, e2⟩ := ut_now ar hA hN1' eu
  try simp only at e2 hn
  have enx' : nx = L.mem s (regA (L.curW s) layout.reg.NEXT_IP) := by
    rw [reg_ok] at enx; rw [← hag _ hnx]; exact (ok_inj_ff enx).symm
  obtain ⟨s1, es1x, -⟩ := spec_ex_fd (obj.Tcb.set_reg.wrK (L := L) s (L.curW s) layout.reg.FAULT_IP
    (core.num.U64.wrapping_sub nx 2#u64) ht' (by simp [layout.reg.FAULT_IP]))
  have e1x := set_fip_wr ht' es1x
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1x, LawfulStore.cpu_wr]; exact hN.wr
  refine ⟨utW (L := L) s1 n1, ⟨_, nx, s1, cur_thread_ok s, by rw [reg_ok, enx'], es1x,
    update_timestamp_ok ar hN1 hn⟩, ?_⟩
  obtain ⟨KF, hKF, eKF⟩ := regA_eq ht' (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
  have hKF' : KF.val = 392 := by rw [hKF]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := by
    rw [eKF]; exact field_aligned ht' (by omega) (by omega)
  have g1 : ∀ b, Q b → L.mem s1' b = L.mem s1 b := by rw [e1, e1x]; exact agree_wr hQ aF hag
  have hct' : ctA (L := L) s1' = ctA (L := L) s1 := by
    rw [e1, e1x, ctA_wr, ctA_wr]; exact slDS_node hk hc
  have hcn' : cnA (L := L) s1' = cnA (L := L) s1 := by
    rw [e1, e1x, cnA_wr, cnA_wr]; exact slDS_node hk hc
  have hct1 : Q (ctA (L := L) s1) := by rw [e1x, ctA_wr]; exact hct
  have hcn1 : Q (cnA (L := L) s1) := by rw [e1x, cnA_wr]; exact hcn
  obtain ⟨aC, aN, -⟩ := ct_cn hN1
  rw [e2]
  unfold utW
  rw [hct', hcn', g1 _ hct1, g1 _ hcn1]
  exact agree_wr hQ aN (agree_wr hQ aC g1)

/-! ## The decided thread at the prefix state -/

variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- A gate-owned aligned word is in the read set. -/
theorem slRS_of_gate {s : S} {x : U64} (ha : Aligned x) (hg : own K (L.mem s) x = .gate) :
    SlRS (st := st) K Locks s x :=
  ⟨ha, Or.inr (Or.inr hg)⟩

/-- A gate-owned word is not a prefix word (prefix words are writable, `PreAcc`). -/
theorem not_slDS_of_gate {s : S} {x : U64}
    (hp : PreAcc (L := L) (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) s)
    (hg : own K (L.mem s) x = .gate) : ¬ SlDS (L := L) s x := fun hx => by
  have h := (SlDS.ws hp hx).2
  unfold WPerm at h
  rw [hg] at h
  exact h

/-- **`SlThrIn.af` from the ownership map**: a placed TCB's `AFFINITY` word (aligned) is
gate-owned (`RegionOK` [J]), so it is in the read set and not a prefix word. -/
theorem af_of_tcb (hK : RegionOK K) {s : S} {d : U64}
    (hp : PreAcc (L := L) (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) s)
    (ht : K.heap d = some .tcb) (ha : Aligned (affA d)) :
    SlRS (st := st) K Locks s (affA d) ∧ ¬ SlDS (L := L) s (affA d) :=
  ⟨slRS_of_gate ha (own_aff_gate hK ht _), not_slDS_of_gate hp (own_aff_gate hK ht _)⟩

/-- The trap arm's receiver, read at the prefix state, is the decided thread. -/
theorem slThr_hd_trap (hA : P0.ArchTotal ar) {s X : S} {a a1 : A} {rp : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (I : SlThrIn (st := st) K Locks rp s) (hS : SlTrap st s) (LP : LocalPre (st := st) ar s a (X, a1))
    {ptr b : U64} {x y g gr : Bool}
    (hc : obj.Slot.cap st (fhA (L := L) s) X = ok (capability.Cap.Endpoint ptr b x y g gr)) :
    L.mem X (epHeadA ptr) = slThr st rp s := by
  obtain ⟨f1, f2, f3, f4⟩ := I.fh hS
  rw [cap_congr (lp_mem ar hA hT hN hcT LP f1.1 f3) (lp_mem ar hA hT hN hcT LP f2.1 f4)] at hc
  have hp : resPtr (obj.Slot.cap st (fhA (L := L) s) s) = ptr := resPtr_ok hc
  have e2 := I.eh hS
  rw [hp] at e2
  unfold slThr
  rw [if_pos hS, hp]
  exact lp_mem ar hA hT hN hcT LP e2.1.1 e2.2.1

/-- The trap arm's handler endpoint in `RECV` at the prefix state: the decided thread is live. -/
theorem slLive_trap (hA : P0.ArchTotal ar) {s X : S} {a a1 : A} {rp : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (I : SlThrIn (st := st) K Locks rp s) (hS : SlTrap st s) (LP : LocalPre (st := st) ar s a (X, a1))
    {ptr b : U64} {x y g gr : Bool}
    (hc : obj.Slot.cap st (fhA (L := L) s) X = ok (capability.Cap.Endpoint ptr b x y g gr))
    (hst : obj.Ep.state st ptr X = ok obj.EP_RECV) : SlLive st rp s := by
  obtain ⟨f1, f2, f3, f4⟩ := I.fh hS
  rw [cap_congr (lp_mem ar hA hT hN hcT LP f1.1 f3) (lp_mem ar hA hT hN hcT LP f2.1 f4)] at hc
  have hp : resPtr (obj.Slot.cap st (fhA (L := L) s) s) = ptr := resPtr_ok hc
  have e2 := I.eh hS
  rw [hp] at e2
  unfold SlLive
  rw [if_pos hS, hp, ← ep_state_congr (lp_mem ar hA hT hN hcT LP e2.2.2.1.1 e2.2.2.2)]
  exact hst

/-- A nonzero replied thread is live. -/
theorem slLive_rr {s : S} {rp : U64} (hS : ¬ SlTrap st s) (h : slThr st rp s ≠ 0#u64) : SlLive st rp s := by
  unfold SlLive
  unfold slThr at h
  rw [if_neg hS] at h ⊢
  exact h

/-- The ReplyRecv arm's replied thread, read at the prefix state, is the decided thread. -/
theorem slThr_hd_rr (hA : P0.ArchTotal ar) {s X : S} {a a1 : A} {rp : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (I : SlThrIn (st := st) K Locks rp s) (hS : ¬ SlTrap st s) (LP : LocalPre (st := st) ar s a (X, a1)) :
    L.mem X (rTcbA rp) = slThr st rp s := by
  unfold slThr
  rw [if_neg hS]
  exact lp_mem ar hA hT hN hcT LP (I.rt hS).1.1 (I.rt hS).2

/-- The words of the decided thread `t` a run reads before `schedulable_here` checks it
(trap arm: `REPLY_OBJ`; ReplyRecv arm: `STATE`, `fault_type`, `SC`), aligned. -/
def slTW (t b : U64) : Prop :=
  Aligned b ∧ (b = replyA t ∨ b = stA t ∨ b = core.num.U64.wrapping_add t 3376#u64 ∨ b = scA t)

/-- A word at an aligned offset from a thread whose `AFFINITY` word is aligned is aligned. -/
theorem tw_al {d c : U64} (h : Aligned (affA d)) (hc : c.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add d c) := by
  unfold affA Aligned at h
  unfold Aligned
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at h ⊢
  omega

/-- **What a declining arm reads at the prefix state** [W] (per-word layout and fl4-sync's
locks at the entry state `s`, like `SlPre`'s `FltAcc` / `RrAcc` fields, but up to the decline):
* `fT` [W]: the trap arm's words other than its receiver's are in `SlRS s` (node, kernel
  globals, the current thread's fault-handler slot, the locked handler endpoint);
* `fD` [W]: the receiver (the decided thread) live (`SlLive`: endpoint in `RECV`) and homed here, its `REPLY_OBJ`, `AFFINITY` and later
  words are in `SlRS s` (this core's);
* `rT` [W]: the ReplyRecv arm's words other than its replied thread's are in `SlRS s`
  (node, kernel globals, the current thread, the locked reply object and endpoint);
* `rU` [W]: the replied thread (the decided thread) live (nonzero) and homed here, its words are in `SlRS s`. -/
structure SlDecIn (K : KLayout) (Locks : S → U64 → Prop) (found : U64 × U64) (s : S) : Prop where
  fT : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) →
    FltDecT (L := L) (SlRS (st := st) K Locks s) X (L.curW s)
  fD : SlTrap st s → SlLive st found.1 s → L.mem s (affA (slThr st found.1 s)) = L.cpu s → ∀ a X a1,
    LocalPre (st := st) ar s a (X, a1) → DestDec (L := L) (SlRS (st := st) K Locks s) X (slThr st found.1 s)
  rT : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) →
    RrDecT (L := L) (SlRS (st := st) K Locks s) X (L.curW s) found.1 found.2
  rU : ¬ SlTrap st s → SlLive st found.1 s → L.mem s (affA (slThr st found.1 s)) = L.cpu s → ∀ a X a1,
    LocalPre (st := st) ar s a (X, a1) → UDec (L := L) (SlRS (st := st) K Locks s) X (slThr st found.1 s)

set_option maxHeartbeats 4000000 in
/-- **`SlThr.home`**: the decided thread homed here, a declining run is the same run on
`guard st (SlRS s) (SlDS s)`. -/
theorem sl_home (hA : P0.ArchTotal ar) {s : S} {a : A} {r : Bool × S × A}
    (E : SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (I : SlThrIn (st := st) K Locks found.1 s) (D : SlDecIn (st := st) ar K Locks found s)
    (h : syscall.handle_syscall_local st ar s a n found = ok r) (hn : r.1 ≠ true)
    (hh : L.mem s (affA (slThr st found.1 s)) = L.cpu s) :
    syscall.handle_syscall_local (guard st (SlRS (st := st) K Locks s) (SlDS (L := L) s)) ar s a n found = ok r := by
  have hp : PreDec (L := L) (SlRS (st := st) K Locks s) (SlDS (L := L) s) s :=
    ⟨fun o h1 h2 => (E.preG.nd o h1 h2).1, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), E.preG.fl, E.preG.nx,
      Or.inl rfl⟩
  refine syscall.handle_syscall_local.guard_dec (gS := guard st (SlRS (st := st) K Locks s) (SlDS (L := L) s))
    hA E.hT E.hN E.hcT hp (fun X a1 csc LP e => E.hhd a X a1 csc LP e) ?_ ?_ h
  · intro hS X a1 n' LP hf
    refine fastpath.fault.guard_dec (gS := guard st (SlRS (st := st) K Locks s) (SlDS (L := L) s))
      (FltDec.of (D.fT hS a X a1 LP) ?_) hf hn
    intro ptr bb x y g gr hc hst d hd
    have e1 := slThr_hd_trap ar hA E.hT E.hN E.hcT I hS LP hc
    rw [eq_of_spec_fd (obj.Ep.head.spec' (st := st) X ptr), e1] at hd
    rw [← ok_inj_ff hd]
    exact D.fD hS (slLive_trap ar hA E.hT E.hN E.hcT I hS LP hc hst) hh a X a1 LP
  · intro hS X a1 LP hf
    refine fastpath.reply_recv_found.guard_dec (gS := guard st (SlRS (st := st) K Locks s) (SlDS (L := L) s))
      (RrDec.of (D.rT hS a X a1 LP) ?_) hf hn
    intro u hu hu0
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hu, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    have lv := slLive_rr (st := st) hS (by rw [← h1]; exact hu0)
    rw [h1]
    exact D.rU hS lv hh a X a1 LP

set_option maxHeartbeats 8000000 in
/-- **`SlThr.away`**: the decided thread homed elsewhere, a run at an alternative is the same
run on `guard st (SlRS s ∪ slTW (slThr s)) ⊤`. -/
theorem sl_away (hA : P0.ArchTotal ar) {s s' : S} {a : A} {r : Bool × S × A}
    (E : SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (I : SlThrIn (st := st) K Locks found.1 s) (D : SlDecIn (st := st) ar K Locks found s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    (hh : L.mem s (affA (slThr st found.1 s)) ≠ L.cpu s)
    (h : syscall.handle_syscall_local st ar s' a n found = ok r) :
    syscall.handle_syscall_local
      (guard st (fun b => SlRS (st := st) K Locks s b ∨ slTW (slThr st found.1 s) b) (fun _ => True))
      ar s' a n found = ok r := by
  have hn : r.1 ≠ true := fun e => hh (slThr_acc ar hA E I Al h e)
  have hcur := sl_alt_cur E.preG Al
  have hTr := slTrap_alt E.preG.fl Al hcur
  have hN' : NodePlaced st T s' (L.cpu s') := by rw [Al.cpu]; exact NodePlaced.of_ksb Al.ksb E.hN
  have hc' : L.curW s' ∈ T := by rw [hcur]; exact E.hcT
  have hp : PreDec (L := L) (fun b => SlRS (st := st) K Locks s b ∨ slTW (slThr st found.1 s) b)
      (fun _ => True) s' :=
    ⟨fun o h1 h2 => Or.inl (by rw [slDS_node Al.ksb Al.cpu]; exact (E.preG.nd o h1 h2).1), trivial, trivial,
      Or.inl (by rw [hcur]; exact E.preG.fl), Or.inl (by rw [hcur]; exact E.preG.nx), trivial⟩
  have hct : SlRS (st := st) K Locks s (ctA (L := L) s) :=
    (E.preG.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
  have hcn : SlRS (st := st) K Locks s (cnA (L := L) s) :=
    (E.preG.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
  -- the prefix at `s'` against the prefix at `s`
  have PA : ∀ X' a1', LocalPre (st := st) ar s' a (X', a1') → ∃ X, LocalPre (st := st) ar s a (X, a1') ∧
      (∀ b, SlRS (st := st) K Locks s b → L.mem X' b = L.mem X b) ∧ L.ksb X' = L.ksb X ∧ L.cpu X' = L.cpu X := by
    intro X' a1' LP'
    obtain ⟨X, LP, hag⟩ := lp_alt ar hA (fun b hb => hb.1) E.hT E.hN E.hcT Al.ksb Al.cpu hcur Al.read
      E.preG.nx hct hcn LP'
    obtain ⟨hkX, hcX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    obtain ⟨hkX', hcX', -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT hN' hc' LP'
    exact ⟨X, LP, hag, by rw [hkX', hkX, Al.ksb], by rw [hcX', hcX, Al.cpu]⟩
  -- the decided thread's words at the alternative's prefix state
  have hrest : SlLive st found.1 s → ∀ X X' a1', LocalPre (st := st) ar s a (X, a1') →
      (∀ b, SlRS (st := st) K Locks s b → L.mem X' b = L.mem X b) → L.cpu X' = L.cpu X →
      L.mem X' (affA (slThr st found.1 s)) ≠ L.cpu X' := by
    intro lv X X' a1' LP hag hcX e
    have af := I.af lv
    apply hh
    obtain ⟨-, hcX0, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    rw [← lp_mem ar hA E.hT E.hN E.hcT LP af.1.1 af.2, ← hag _ af.1, e, hcX, hcX0]
  refine syscall.handle_syscall_local.guard_dec
    (gS := guard st (fun b => SlRS (st := st) K Locks s b ∨ slTW (slThr st found.1 s) b) (fun _ => True))
    hA E.hT hN' hc' hp ?_ ?_ ?_ h
  · intro X' a1' csc LP' ecsc
    obtain ⟨X, LP, hag, hk, hc⟩ := PA X' a1' LP'
    obtain ⟨hkX, hcX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    have rcs : SlRS (st := st) K Locks s (L.nodeA X layout.node.CUR_SC) := by
      unfold LawfulStore.nodeA; rw [hcX, nodeAt_of_ksb hkX]
      exact (E.preG.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
    have en : L.nodeA X' layout.node.CUR_SC = L.nodeA X layout.node.CUR_SC := by
      unfold LawfulStore.nodeA; exact slDS_node hk hc
    have ecsc' : sched.cur_sc st X = ok csc := by
      rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X')] at ecsc
      rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X), ← hag _ rcs, ← en]
      exact ecsc
    exact RdHead.mono (fun b hb => Or.inl hb) (RdHead.congr hag (E.hhd a X a1' csc LP ecsc'))
  · intro hS' X' a1' n' LP' hf
    have hS := hTr.1 hS'
    obtain ⟨X, LP, hag, hk, hc⟩ := PA X' a1' LP'
    have DT := FltDecT.congr hk hc hag (D.fT hS a X a1' LP)
    rw [hcur] at hf ⊢
    refine fastpath.fault.guard_dec
      (gS := guard st (fun b => SlRS (st := st) K Locks s b ∨ slTW (slThr st found.1 s) b) (fun _ => True))
      (FltDec.of (FltDecT.mono (fun b hb => Or.inl hb) DT) ?_) hf hn
    intro ptr bb x y g gr hcp hst' d hd
    have hc0 : obj.Slot.cap st (fhA (L := L) s) X = ok (capability.Cap.Endpoint ptr bb x y g gr) :=
      (cap_congr (hag _ DT.fh.1) (hag _ DT.fh.2)).symm.trans hcp
    have hst : obj.Ep.state st ptr X = ok obj.EP_RECV :=
      (ep_state_congr (hag _ (DT.ep ptr bb x y g gr hcp).1)).symm.trans hst'
    have lv := slLive_trap ar hA E.hT E.hN E.hcT I hS LP hc0 hst
    have af := I.af lv
    have aA : Aligned (affA (slThr st found.1 s)) := af.1.1
    have e1 := slThr_hd_trap ar hA E.hT E.hN E.hcT I hS LP hc0
    rw [eq_of_spec_fd (obj.Ep.head.spec' (st := st) X' ptr), hag _ (DT.ep ptr bb x y g gr hcp).2, e1] at hd
    rw [← ok_inj_ff hd]
    exact ⟨Or.inr ⟨by unfold replyA; exact tw_al aA (by simp), Or.inl rfl⟩, Or.inl af.1,
      fun e => absurd e (hrest lv X X' a1' LP hag hc)⟩
  · intro hS' X' a1' LP' hf
    have hS : ¬ SlTrap st s := fun h' => hS' (hTr.2 h')
    obtain ⟨X, LP, hag, hk, hc⟩ := PA X' a1' LP'
    have DT := RrDecT.congr hk hc hag (D.rT hS a X a1' LP)
    rw [hcur] at hf ⊢
    refine fastpath.reply_recv_found.guard_dec
      (gS := guard st (fun b => SlRS (st := st) K Locks s b ∨ slTW (slThr st found.1 s) b) (fun _ => True))
      (RrDec.of (RrDecT.mono (fun b hb => Or.inl hb) DT) ?_) hf hn
    intro u hu hu0
    have h1 := obj.Reply.tcb.blk (st := st) X' found.1
    rw [hu, WP.spec_ok, hag _ DT.rRt, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    have lv := slLive_rr (st := st) hS (by rw [← h1]; exact hu0)
    have af := I.af lv
    have aA : Aligned (affA (slThr st found.1 s)) := af.1.1
    rw [h1]
    exact ⟨Or.inr ⟨by rw [stA_eq]; exact tw_al aA (by simp), Or.inr (Or.inl rfl)⟩,
      Or.inr ⟨tw_al aA (by simp), Or.inr (Or.inr (Or.inl rfl))⟩,
      Or.inr ⟨by unfold scA; exact tw_al aA (by simp), Or.inr (Or.inr (Or.inr rfl))⟩, Or.inl af.1,
      fun e => absurd e (hrest lv X X' a1' LP hag hc)⟩

/-- **`SlThr` for the concrete decided thread** `slThr st found.1` with `slTW`. -/
theorem slThr_sl (hA : P0.ArchTotal ar) {P : S → Prop}
    (hPE : ∀ s, P s → SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hI : ∀ s, P s → SlThrIn (st := st) K Locks found.1 s)
    (hD : ∀ s, P s → SlDecIn (st := st) ar K Locks found s) :
    SlThr (st := st) ar (n := n) (found := found) (m0 := m0) P K Locks (slThr st found.1) slTW where
  alt s _ hP Al := slThr_alt (hPE s hP).preG (hI s hP) Al
  acc s _ _ _ hP Al h hr := slThr_acc ar hA (hPE s hP) (hI s hP) Al h hr
  home s _ _ hP h hn hh := sl_home ar hA (hPE s hP) (hI s hP) (hD s hP) h hn hh
  twA _ _ h := h.1
  away s _ _ _ hP Al hh h := sl_away ar hA (hPE s hP) (hI s hP) (hD s hP) Al hh h

variable {p : SProg Bool}

/-- **`PathObl` of the syscall entry** with the concrete decided thread (`sl_pathObl_dr`,
`slThr_sl`). -/
theorem sl_pathObl_sl (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {P : S → Prop} (hPE : ∀ s, P s → SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hI : ∀ s, P s → SlThrIn (st := st) K Locks found.1 s)
    (hD : ∀ s, P s → SlDecIn (st := st) ar K Locks found s) :
    PathObl st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathObl_dr ar hA hK hU hFp hz hm hPE (slThr_sl ar hA hPE hI hD)

/-- **`PathSide` of the syscall entry** with the concrete decided thread (`sl_pathSide_dr`,
`slThr_sl`). -/
theorem sl_pathSide_sl (hS : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {P : S → Prop} (hPE : ∀ s, P s → SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hI : ∀ s, P s → SlThrIn (st := st) K Locks found.1 s)
    (hD : ∀ s, P s → SlDecIn (st := st) ar K Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s) :
    PathSide st (fun m s a => syscall.handle_syscall_local m ar s a n found)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathSide_dr ar hS hA hK hU hFp hz hm hPE (slThr_sl ar hA hPE hI hD) huf

end

end Fl4Proofs.P2.PathObl

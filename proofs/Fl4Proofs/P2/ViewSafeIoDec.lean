/-
# P2 (line p3mc, gen 4): the I/O port path's declined runs on a narrowed guard (`io_decN`)

`AccessIoRa.io_ra_dec` (a run that declines at the entry `s` runs at every alternative `s'` on the store guarded to
aligned reads) with the guard's read set `R` and write set `W` any two predicates that hold on the words the declined
runs touch, stated at the entry (`IoNarD`). One change to the walk-through: the current SC's refill head is read only
after the scheduler-action check passes, and there the action is `RESUME_CURRENT` (`0`), so by `BoundInv.resume` the
current thread has an SC. `IoNarD.rh` is therefore asked only where the current thread has an SC
(`IoMidDN.rh` only where the action is `RESUME_CURRENT`; `ioTail.guardDN` is `ioTail.guardD` with that field).

No premise beyond `IoPre` and `IoNarD`. No existing statement changed.
-/
import Fl4Proofs.P2.AccessIoRa
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InW GateField TimerField)

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

/-- `IoMidD` with the current SC's refill head asked only where the action is `RESUME_CURRENT`. -/
structure IoMidDN (R : U64 → Prop) (s s2 : S) (t : U64) (C : U64 → U64 → Prop) (sl : U64) : Prop where
  k : L.ksb s2 = L.ksb s
  c : L.cpu s2 = L.cpu s
  cur : L.curW s2 = t
  r10 : R (regA t layout.reg.R10)
  cap : R (regA t layout.reg.CAP)
  yld : R (core.num.U64.wrapping_add t 3472#u64)
  hsl : obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl
  hR0 : R sl
  hR8 : R (core.num.U64.wrapping_add sl 8#u64)
  hRc : WalkRc (st := st) R s2 C
  hcl : WalkCl (st := st) s2 C
  hroot : ∀ p r gs g, obj.Slot.cap st sl s2 = ok (.CNode p r gs g) → C p r
  hRf : ∀ cptr x, cspace.lookup_slot st s2 t cptr = ok (.Ok x) →
    R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64)
  ib : R (core.num.U64.wrapping_add t 3512#u64)
  bs : ∀ bsl, obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok bsl → R bsl ∧ R (core.num.U64.wrapping_add bsl 8#u64)
  rh : L.actionW s2 = sched.ACTION_RESUME_CURRENT → RdHead (L := L) R s2 (L.cscW s2)
  td : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 →
    R (core.num.U64.wrapping_add (L.mem s2 (tmA (L := L) s2)) 3528#u64)
  rs : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → R (scA (L.mem s2 (rhA (L := L) s2))) ∧
    RdHead (L := L) R s2 (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
  dt : R (core.num.U64.wrapping_add (L.ksb s2) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb s2) layout.ks.CUR_DOMAIN)
  af : R (affA t)
  dom : R (core.num.U64.wrapping_add t 3432#u64)
  sc : R (scA t)
  inq : R (inqA t)

/-- **`ioTail.guardD` with `IoMidDN`.** -/
theorem ioTail.guardDN {A : Type} (ar : machine.Arch A) {s : S} {a : A} {t : U64}
    {info : msginfo.MessageInfo} {number : I64} {r : Bool × S × A}
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hnx : R (regA t layout.reg.NEXT_IP)) (hfi : W (regA t layout.reg.FAULT_IP))
    (hmid : ∀ nx s1 s2 a1, obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) →
      ∃ C sl, IoMidDN (L := L) R s s2 t C sl)
    (hr : r.1 ≠ true)
    (h : ioTail st ar s a t info number = ok r) :
    ioTail gS ar s a t info number = ok r := by
  unfold ioTail at h ⊢
  revert h
  refine tr_bind_same (fun b _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  refine tr_bind (fun x hx _ => by rw [obj.Tcb.reg.guard t s _ hnx]; exact hx) (fun nx enx => ?_)
  simp only [lift, bind_ok]
  refine tr_bind (fun x hx _ => by rw [obj.Tcb.set_reg.guard t s _ _ hfi]; exact hx) (fun s1 es1 => ?_)
  have e1 : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have k1 : L.ksb s1 = L.ksb s := by rw [e1, L.ksb_wr]
  have c1 : L.cpu s1 = L.cpu s := by rw [e1, LawfulStore.cpu_wr]
  refine tr_bind (fun x hx _ => by
      rw [sched.update_timestamp.guard ar s1 a (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2]; exact hx)
    (fun x eu => ?_)
  obtain ⟨s2, a1⟩ := x
  simp only [uncurry_apply_pair]
  obtain ⟨C, sl, M⟩ := hmid nx s1 s2 a1 enx es1 eu
  have nd2 := nd_at hNd M.k M.c
  have Mc := M.cur
  subst Mc
  rw [obj.Tcb.reg.guard (gS := gS) (L.curW s2) s2 _ M.cap, reg_ok]
  simp only [bind_ok]
  rw [sched.cur_sc.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.action.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1]
  refine tr_bind_same (fun i3 ei3 => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun hc3 => ?_)
  have hact : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at ei3
    have e := (ok_inj_ff ei3).symm
    simp only [bne_iff_ne, ne_eq, not_not] at hc3
    rw [← e]; exact hc3
  rw [obj.Tcb.yield_to.guard (gS := gS) (L.curW s2) s2 M.yld]
  refine tr_bind_same (fun i4 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_bind (fun b1 hb1 _ => ioport.invocation_ok.guard C M.hsl M.hR0 M.hR8 M.hRc M.hcl M.hroot
    (fun x e => M.hRf _ x e) M.ib M.bs M.r10 hb1) (fun b1 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [sched.consumed.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1]
  refine tr_bind_same (fun i5 _ => ?_)
  have ecsc' : csc = L.cscW s2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2)] at ecsc; exact (ok_inj_ff ecsc).symm
  subst ecsc'
  rw [sporadic.sufficient.guard (gS := gS) ar s2 a1 _ i5 (M.rh hact)]
  refine tr_bind_same (fun b2 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [fastpath.schedulable_here.guard (gS := gS) s2 (L.curW s2) (nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
    (nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1 (nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).1
    M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
  refine tr_bind_same (fun b3 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => ?_) (fun _ h => h)
  exfalso
  apply hr
  obtain ⟨⟨r0, s3, a2⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨u, s4, a3⟩, -, h⟩ := bind_eq_ok h
  obtain ⟨⟨s5, a4⟩, -, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  subst e
  rfl

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s' : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}

/-- **The words a declined I/O port run touches, at the entry `s`, in `R` (read) and `W` (written)** (module
docstring). -/
structure IoNarD (K : KLayout) (R W : U64 → Prop) (s : S) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o)
  cur : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → R (core.num.U64.wrapping_add (L.curW s) off)
  fi : W (regA (L.curW s) layout.reg.FAULT_IP)
  slot : ∀ sl ∈ K.slots, R sl ∧ R (core.num.U64.wrapping_add sl 8#u64)
  ks : ∀ o : U64, o.val < 256 → R (core.num.U64.wrapping_add (L.ksb s) o)
  rh : L.mem s (scA (L.curW s)) ≠ 0#u64 → RdHead (L := L) R s (L.cscW s)
  td : L.mem s (tmA (L := L) s) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64)
  rs : L.mem s (rhA (L := L) s) ≠ 0#u64 → R (scA (L.mem s (rhA (L := L) s))) ∧
    RdHead (L := L) R s (L.mem s (scA (L.mem s (rhA (L := L) s))))

theorem IoNarD.reg {R W : U64 → Prop} (N : IoNarD (L := L) K R W s) (hT : TcbAddr (L.curW s)) {r : U64} (hr : r.val < 384) :
    R (regA (L.curW s) r) := by
  obtain ⟨o, ho, e⟩ := regA_eq hT hr
  rw [e]
  exact N.cur o (by omega) (by omega)

/-- **`IoMidDN` at an alternative's post-prefix state** (`io_alt_midD` for `R`). -/
theorem io_alt_midDN {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {R W : U64 → Prop} (N : IoNarD (L := L) K R W s)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {nx : U64} {s1' s2' : S} {a1 : A}
    (hs1 : obj.Tcb.set_reg st (L.curW s) s' layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1')
    (hu : sched.update_timestamp st ar s1' a = ok (s2', a1)) :
    ∃ C sl, IoMidDN (L := L) R s' s2' (L.curW s) C sl := by
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  obtain ⟨⟨Q, Rq, hq⟩, hbI, ⟨hO, -, -⟩, -, hS⟩ := P.bxi
  have hN' : NodePlaced st T s' (L.cpu s') := by rw [Al.cpu]; exact P.np.ksb Al.ksb
  have hcT' : L.curW s' ∈ T := by rw [hcur]; exact P.cT
  have hcC' : L.cpu s' ∈ Cs := by rw [Al.cpu]; exact hq.cur
  rw [← hcur] at hs1
  have w := prefix_writes ar hA P.tp hN' hcT' hs1 hu
  have nk : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ layout.node.CUR_TIME.val →
      o.val ≠ layout.node.CONSUMED.val →
      L.mem s2' (L.nodeAt s2' (L.cpu s2') o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o h1 h2 h3 h4
    rw [w.2.1, nodeAt_of_ksb w.1, pre_node w P.tp hN' hcT' h1 h2 h3 h4, G.node]
    exact G.m _ (P.nd (Locks := Locks) o h1 h2).1
  have po : ∀ b, OutsideObjs st T Cs s b → IoRS (st := st) K Locks s b → L.mem s2' b = L.mem s b := by
    intro b hb hr
    rw [pre_out w hN' hcC' hcT' P.tp (hb.ksb Al.ksb)]
    exact G.m _ hr
  have tk : ∀ u ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
      L.mem s2' (core.num.U64.wrapping_add u K) = L.mem s' (core.num.U64.wrapping_add u K) := by
    intro u hu K hK h8 h392
    have hx := P.tp u hu
    refine w.2.2 _ (field_aligned hx hK h8) ?_
    rintro (⟨K', hK', e⟩ | e | e)
    · exact tcb_word_ne hx (P.tp _ hcT') hK (by omega) (fun _ => by omega) e
    · exact tcb_node_ne hN' hu hx hK (by simp [layout.node.CUR_TIME]) e
    · exact tcb_node_ne hN' hu hx hK (by simp [layout.node.CONSUMED]) e
  -- the prefix keeps every capability slot
  have sk : ∀ sl ∈ K.slots, obj.Slot.cap st sl s2' = obj.Slot.cap st sl s' := by
    intro sl hsl
    obtain ⟨h8, hf⟩ := P.lay.slot8 sl hsl
    have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have np : ∀ b, InW sl 32 b → Aligned b → L.mem s2' b = L.mem s' b := by
      intro b hb ha
      obtain ⟨p1, p2, p3⟩ := prefix_slot P hsl hb
      refine w.2.2 _ ha ?_
      rintro (⟨K', hK', e⟩ | e | e)
      · obtain ⟨k, hk, e2⟩ := regA_eq P.tA (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
        have ek : K' = k := UScalar.eq_of_val_eq (by rw [hK', hk]; simp [layout.reg.FAULT_IP])
        exact p1 (by rw [e2, e, hcur, ek])
      · exact p2 (e.trans (G.node _))
      · exact p3 (e.trans (G.node _))
    unfold obj.Slot.cap
    rw [L.read_pair_eq, L.read_pair_eq, np sl ⟨le_refl _, by omega⟩ h8,
      np _ ⟨by omega, by omega⟩ (by unfold Aligned; omega)]
  -- the walk
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  have hcl2 : WalkCl (st := st) s2' C := by
    intro p r m y p' r' gs' g' hp hm hc
    have hs := (hC p r m y hp hm).1
    rw [sk _ hs] at hc
    exact hcl p r m y p' r' gs' g' hp hm (slot_back P Al hs hc (Or.inl ⟨_, _, _, _, rfl⟩))
  have hsl0 := (P.lay.tslot _ (P.hT _ P.cT) layout.tcb.SLOT_CTABLE _ (tcb_slot_ctable _)
    (by simp [layout.tcb.SLOT_CTABLE])).1
  have hroot2 : ∀ p r gs g, obj.Slot.cap st (L.curW s) s2' = ok (.CNode p r gs g) → C p r := by
    intro p r gs g hc
    rw [sk _ hsl0] at hc
    exact hroot p r gs g (slot_back P Al hsl0 hc (Or.inl ⟨_, _, _, _, rfl⟩))
  have hRf : ∀ cptr (x : cspace.Resolved), cspace.lookup_slot st s2' (L.curW s) cptr = ok (.Ok x) →
      R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64) := by
    intro cptr x h
    unfold cspace.lookup_slot at h
    rw [tcb_slot_ctable] at h; simp only [bind_ok] at h
    obtain ⟨root, er, h⟩ := bind_eq_ok h
    obtain ⟨p, r, m, y, hp, hm, e⟩ := rab_loop_slot st C hcl2 66 root _ 65#u64 x (by simp)
      (fun p r gs g e => hroot2 p r gs g (e ▸ er)) h
    rw [e]; exact N.slot _ (hC p r m y hp hm).1
  -- the SC head words
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  have rdT : ∀ sc, OutsideObjs st T Cs s (headA sc) → RdHead (L := L) (IoRS (st := st) K Locks s) s sc →
      RdHead (L := L) R s sc → RdHead (L := L) R s2' sc := by
    intro sc ho h hR
    have e := po _ ho h.1
    unfold RdHead LawfulStore.rhead at hR ⊢
    rw [e]; exact hR
  have ecs : L.cscW s2' = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    exact nk _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC, layout.node.CUR_TIME]) (by simp [layout.node.CUR_SC, layout.node.CONSUMED])
  have eact : L.actionW s2' = L.actionW s := by
    unfold LawfulStore.actionW
    exact nk _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION, layout.node.CUR_TIME])
      (by simp [layout.node.SCHED_ACTION, layout.node.CONSUMED])
  have etm : L.mem s2' (tmA (L := L) s2') = L.mem s (tmA (L := L) s) :=
    nk _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
  have erh : L.mem s2' (rhA (L := L) s2') = L.mem s (rhA (L := L) s) :=
    nk _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
  have ecur : L.curW s2' = L.curW s := by
    unfold LawfulStore.curW
    exact nk _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD, layout.node.CUR_TIME]) (by simp [layout.node.CUR_THREAD, layout.node.CONSUMED])
  have hsl : ∀ i sl, obj.Tcb.slot (L.curW s) i = ok sl → i.val < 6 →
      R sl ∧ R (core.num.U64.wrapping_add sl 8#u64) := fun i sl h hi =>
    N.slot _ (P.lay.tslot _ (P.hT _ P.cT) i sl h hi).1
  refine ⟨C, L.curW s,
    { k := w.1
      c := w.2.1
      cur := ecur
      r10 := N.reg P.tA (by simp [layout.reg.R10])
      cap := N.reg P.tA (by simp [layout.reg.CAP])
      yld := N.cur 3472#u64 (by simp) (by simp)
      hsl := tcb_slot_ctable _
      hR0 := (N.slot _ hsl0).1
      hR8 := (N.slot _ hsl0).2
      hRc := fun p r m y _ _ _ _ hp hm _ => N.slot _ (hC p r m y hp hm).1
      hcl := hcl2
      hroot := hroot2
      hRf := hRf
      ib := N.cur 3512#u64 (by simp) (by simp)
      bs := fun bsl h => hsl _ bsl h (by simp [layout.tcb.SLOT_BUFFER])
      rh := fun hact => by
        rw [eact] at hact
        have hsc : L.mem s (scA (L.curW s)) ≠ 0#u64 := hbI.resume (hact.trans (by simp [sched.ACTION_RESUME_CURRENT]))
        rw [ecs]
        exact rdT _ (hd P.cscS) ((P.cscacc (Locks := Locks)).head P.cscwf) (N.rh hsc)
      td := by rw [etm]; exact fun h0 => N.td h0
      rs := by
        rw [erh]; intro h0
        obtain ⟨r1, r2⟩ := P.rs (Locks := Locks) h0
        obtain ⟨n1, n2⟩ := N.rs h0
        obtain ⟨hxT, hxS, -⟩ := bxi_rh P.bxi h0
        have e1 : L.mem s2' (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
          (tk _ hxT 3464#u64 (by decide) (by decide) (by decide)).trans (G.m _ r1)
        rw [e1]
        exact ⟨n1, rdT _ (hd hxS) r2 n2⟩
      dt := by
        rw [w.1, Al.ksb]
        exact N.ks _ (by simp [layout.ks.DOMAIN_TIME])
      cd := by
        rw [w.1, Al.ksb]
        exact N.ks _ (by simp [layout.ks.CUR_DOMAIN])
      af := N.cur 3520#u64 (by simp) (by simp)
      dom := N.cur 3432#u64 (by simp) (by simp)
      sc := N.cur 3464#u64 (by simp) (by simp)
      inq := N.cur 3592#u64 (by simp) (by simp) }⟩

/-- **`io_ra_dec` on the narrowed guard** (module docstring). -/
theorem io_decN {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {R W : U64 → Prop} (N : IoNarD (L := L) K R W s)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {r0 r : Bool × S × A} (h0 : syscall.handle_ioport_local st ar s a number = ok r0) (hr0 : r0.1 ≠ true)
    (h : syscall.handle_ioport_local st ar s' a number = ok r) :
    syscall.handle_ioport_local (guard st R W) ar s' a number = ok r := by
  have hr : r.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r
    intro hb
    change b = true at hb
    subst hb
    exact io_alt_not_acc hA P Al h0 hr0 h
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s' (L.cpu s') o) ∧ W (L.nodeAt s' (L.cpu s') o) := fun o h1 h2 => by
    rw [G.node]; exact N.nd o h1 h2
  rw [handle_ioport_local_eq] at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := guard st R W) s'
    (hNd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [hcur, msg.msg_info.guard (gS := guard st R W) s' _ (N.reg P.tA (by simp [layout.reg.MSG_INFO]))]
  refine tr_bind_same (fun info _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard (gS := guard st R W) (L.curW s) s' (N.cur 3456#u64 (by simp) (by simp))]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  have hT := fun (h : ioTail st ar s' a (L.curW s) info number = ok r) =>
    ioTail.guardDN (gS := guard st R W) ar hNd (N.reg P.tA (by simp [layout.reg.NEXT_IP])) N.fi
      (fun nx s1 s2 a1 _ e1 e2 => io_alt_midDN (nx := nx) hA P N Al e1 e2) hr h
  exact tr_ite (fun _ => tr_ite (fun _ h => h) (fun _ => hT)) (fun _ => hT)

end

end Fl4Proofs.P2.PathObl

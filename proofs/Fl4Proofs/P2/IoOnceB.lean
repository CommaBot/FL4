/-
# P2: the I/O port path's reads at an alternative's post-prefix state, against the entry's `IoRS` (line hpzg, gen 3)

AccessIoRa's `io_alt_midD` places the declining run's reads after the prefix in the aligned words; for `ReadOnce`
they are needed in `IoRS s` itself (the entry's read set), except the CSpace slots that hold neither a CNode nor
an I/O port cap (those are the racy ones):

* `IoMidR`: `IoMidD`'s facts for a read set `R`, with the found-slot fact `hRf` replaced by `hIo` (a C-walk slot
  holding an I/O port cap is in `R`);
* `io_alt_midR`: `IoMidR (IoRS s)` at an alternative's post-prefix state (`slot_back` / `IoPre.slot` for the
  CNode- and I/O-port-valued slots, `prefix_writes` for the memory-dependent addresses).

Premises: those of `IoPre`.
-/
import Fl4Proofs.P2.AccessIoRa
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InW GateField TimerField)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- The words the I/O port run reads between the prefix and the end of a declining run, at the post-prefix state
`s2` (current thread `t`, `C` the CNodes the walk may enter, `sl` the CTABLE slot), CSpace slots holding a CNode
or an I/O port cap included, other found slots not. -/
structure IoMidR (R : U64 → Prop) (s2 : S) (t : U64) (C : U64 → U64 → Prop) (sl : U64) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s2 (L.cpu s2) o)
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
  hIo : ∀ p r m y f l z, C p r → cspace.mask r = ok m →
    obj.Slot.cap st (cnSlot p (y &&& m)) s2 = ok (.IoPort f l z) →
    R (cnSlot p (y &&& m)) ∧ R (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)
  ib : R (core.num.U64.wrapping_add t 3512#u64)
  bs : ∀ bsl, obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok bsl → R bsl ∧ R (core.num.U64.wrapping_add bsl 8#u64)
  rh : RdHead (L := L) R s2 (L.cscW s2)
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

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s' : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}

set_option maxHeartbeats 2000000 in
/-- **`IoMidR (IoRS s)` at an alternative's post-prefix state** (module docstring). -/
theorem io_alt_midR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {nx : U64} {s1' s2' : S} {a1 : A}
    (hs1 : obj.Tcb.set_reg st (L.curW s) s' layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1')
    (hu : sched.update_timestamp st ar s1' a = ok (s2', a1)) :
    ∃ C sl, IoMidR (L := L) (IoRS (st := st) K Locks s) s2' (L.curW s) C sl := by
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  obtain ⟨⟨Q, Rq, hq⟩, -, ⟨hO, -, -⟩, -, hS⟩ := P.bxi
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
  have slA : ∀ sl ∈ K.slots, Aligned sl ∧ Aligned (core.num.U64.wrapping_add sl 8#u64) := by
    intro sl hsl
    obtain ⟨h8, hf⟩ := P.lay.slot8 sl hsl
    have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    exact ⟨h8, by unfold Aligned; omega⟩
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
      np _ ⟨by omega, by omega⟩ (slA sl hsl).2]
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  -- a slot of `K.slots` holding a CNode or I/O port cap at `s2'` is in `IoRS s`
  have hRS : ∀ sl ∈ K.slots, ∀ c, obj.Slot.cap st sl s2' = ok c →
      ((∃ p' r' gs' g', c = .CNode p' r' gs' g') ∨ ∃ f l z, c = .IoPort f l z) →
      IoRS (st := st) K Locks s sl ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add sl 8#u64) := by
    intro sl hs c hc hk
    rw [sk _ hs] at hc
    have hb := slot_back P Al hs hc hk
    exact P.slot hs (Or.inr (cap_not_nof hb hk))
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
  have hslot : ∀ i sl, obj.Tcb.slot (L.curW s) i = ok sl → i.val < 6 →
      IoRS (st := st) K Locks s sl ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add sl 8#u64) := fun i sl h hi => by
    obtain ⟨h1, h2⟩ := P.lay.tslot _ (P.hT _ P.cT) i sl h hi
    exact P.slot h1 (Or.inl h2)
  have h0 := hslot _ _ (tcb_slot_ctable (L.curW s)) (by simp [layout.tcb.SLOT_CTABLE])
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  have rdT : ∀ sc, OutsideObjs st T Cs s (headA sc) → RdHead (L := L) (IoRS (st := st) K Locks s) s sc →
      RdHead (L := L) (IoRS (st := st) K Locks s) s2' sc := by
    intro sc ho h
    have e := po _ ho h.1
    unfold RdHead LawfulStore.rhead at h ⊢
    rw [e]; exact h
  have ecs : L.cscW s2' = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    exact nk _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC, layout.node.CUR_TIME]) (by simp [layout.node.CUR_SC, layout.node.CONSUMED])
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
  refine ⟨C, L.curW s,
    { nd := fun o h1 h2 => by
        rw [w.2.1, nodeAt_of_ksb w.1, G.node]; exact (P.nd (Locks := Locks) o h1 h2).1
      cur := ecur
      r10 := (P.reg (Locks := Locks) (by simp [layout.reg.R10])).1
      cap := (P.reg (Locks := Locks) (by simp [layout.reg.CAP])).1
      yld := (P.home (Locks := Locks) (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1
      hsl := tcb_slot_ctable _
      hR0 := h0.1
      hR8 := h0.2
      hRc := fun p r m y p' r' gs' g' hp hm hc =>
        hRS _ (hC p r m y hp hm).1 _ hc (Or.inl ⟨_, _, _, _, rfl⟩)
      hcl := hcl2
      hroot := hroot2
      hIo := fun p r m y f l z hp hm hc => hRS _ (hC p r m y hp hm).1 _ hc (Or.inr ⟨_, _, _, rfl⟩)
      ib := P.gate (Locks := Locks) (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
      bs := fun bsl h => hslot _ bsl h (by simp [layout.tcb.SLOT_BUFFER])
      rh := by rw [ecs]; exact rdT _ (hd P.cscS) ((P.cscacc (Locks := Locks)).head P.cscwf)
      td := by rw [etm]; exact P.td (Locks := Locks)
      rs := by
        rw [erh]; intro h0
        obtain ⟨r1, r2⟩ := P.rs (Locks := Locks) h0
        obtain ⟨hxT, hxS, -⟩ := bxi_rh P.bxi h0
        have e1 : L.mem s2' (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
          (tk _ hxT 3464#u64 (by decide) (by decide) (by decide)).trans (G.m _ r1)
        rw [e1]
        exact ⟨r1, rdT _ (hd hxS) r2⟩
      dt := by
        rw [w.1, Al.ksb]
        exact P.ksw (Locks := Locks) (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
      cd := by
        rw [w.1, Al.ksb]
        exact P.ksw (Locks := Locks) (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
      af := P.gate (Locks := Locks) (off := 3520#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
      dom := P.gate (Locks := Locks) (off := 3432#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
      sc := P.gate (Locks := Locks) (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
      inq := (P.home (Locks := Locks) (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1 }⟩

end

end Fl4Proofs.P2.PathObl

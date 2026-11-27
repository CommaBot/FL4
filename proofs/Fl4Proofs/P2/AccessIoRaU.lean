/-
P2 (line pte, gen 6): **the I/O port path's declines read no user word** (`io_alt_midDU`, `io_ra_decU`): p2io's
`io_alt_midD` / `io_ra_dec` (`P2/AccessIoRa.lean`, unchanged) re-run at `R := Aligned ∖ K.user`. Every read word of the
decline walk is either an `IoRS` word (its `∉ K.user` is `IoRS`'s second conjunct) or a slot / node / TCB word whose
region is not `.none` (`IoPre.region_kernel`). Instantiated at `E2EPIrq.userP K`, "no user word" is "no user and no
PTE word" (`P2/E2EPIo.lean`).
-/
import Fl4Proofs.P2.AccessIoRa
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InW GateField TimerField)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s' : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}

/-- **`IoMidD` (aligned reads) at an alternative's post-prefix state.** -/
theorem io_alt_midDU {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {nx : U64} {s1' s2' : S} {a1 : A}
    (hs1 : obj.Tcb.set_reg st (L.curW s) s' layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1')
    (hu : sched.update_timestamp st ar s1' a = ok (s2', a1)) :
    ∃ C sl, IoMidD (L := L) (fun b => Aligned b ∧ b ∉ K.user) s' s2' (L.curW s) C sl := by
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have ra : ∀ {x : U64}, IoRS (st := st) K Locks s x → Aligned x ∧ x ∉ K.user := fun h => ⟨h.1, h.2.1⟩
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
  -- words kept through the prefix and equal at the alternative
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
  have slU : ∀ sl ∈ K.slots, (Aligned sl ∧ sl ∉ K.user) ∧
      (Aligned (core.num.U64.wrapping_add sl 8#u64) ∧ core.num.U64.wrapping_add sl 8#u64 ∉ K.user) := by
    intro sl hsl
    obtain ⟨h8, hf⟩ := P.lay.slot8 sl hsl
    have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine ⟨⟨(slA sl hsl).1, P.region_kernel (Or.inl ?_)⟩, ⟨(slA sl hsl).2, P.region_kernel (Or.inl ?_)⟩⟩
    · rw [P.lay.slotw sl hsl sl ⟨le_refl _, by omega⟩]; intro e; cases e
    · rw [P.lay.slotw sl hsl _ ⟨by omega, by omega⟩]; intro e; cases e
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
      np _ ⟨by omega, by omega⟩ (slA sl hsl).2]
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
      (Aligned x.slot ∧ x.slot ∉ K.user) ∧
        (Aligned (core.num.U64.wrapping_add x.slot 8#u64) ∧ core.num.U64.wrapping_add x.slot 8#u64 ∉ K.user) := by
    intro cptr x h
    unfold cspace.lookup_slot at h
    rw [tcb_slot_ctable] at h; simp only [bind_ok] at h
    obtain ⟨root, er, h⟩ := bind_eq_ok h
    obtain ⟨p, r, m, y, hp, hm, e⟩ := rab_loop_slot st C hcl2 66 root _ 65#u64 x (by simp)
      (fun p r gs g e => hroot2 p r gs g (e ▸ er)) h
    rw [e]; exact slU _ (hC p r m y hp hm).1
  -- the SC head words
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  have rdT : ∀ sc, OutsideObjs st T Cs s (headA sc) → RdHead (L := L) (IoRS (st := st) K Locks s) s sc →
      RdHead (L := L) (fun b => Aligned b ∧ b ∉ K.user) s2' sc := by
    intro sc ho h
    have e := po _ ho h.1
    unfold RdHead LawfulStore.rhead at h ⊢
    rw [e]; exact ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩⟩
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
  have hsl : ∀ i sl, obj.Tcb.slot (L.curW s) i = ok sl → i.val < 6 →
      (Aligned sl ∧ sl ∉ K.user) ∧
        (Aligned (core.num.U64.wrapping_add sl 8#u64) ∧ core.num.U64.wrapping_add sl 8#u64 ∉ K.user) :=
    fun i sl h hi => slU _ (P.lay.tslot _ (P.hT _ P.cT) i sl h hi).1
  refine ⟨C, L.curW s,
    { k := w.1
      c := w.2.1
      cur := ecur
      r10 := ra (P.reg (Locks := Locks) (by simp [layout.reg.R10])).1
      cap := ra (P.reg (Locks := Locks) (by simp [layout.reg.CAP])).1
      yld := ra (P.home (Locks := Locks) (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1
      hsl := tcb_slot_ctable _
      hR0 := (slU _ hsl0).1
      hR8 := (slU _ hsl0).2
      hRc := fun p r m y _ _ _ _ hp hm _ => slU _ (hC p r m y hp hm).1
      hcl := hcl2
      hroot := hroot2
      hRf := hRf
      ib := ra (P.gate (Locks := Locks) (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
      bs := fun bsl h => hsl _ bsl h (by simp [layout.tcb.SLOT_BUFFER])
      rh := by rw [ecs]; exact rdT _ (hd P.cscS) ((P.cscacc (Locks := Locks)).head P.cscwf)
      td := by rw [etm]; exact fun h0 => ra (P.td (Locks := Locks) h0)
      rs := by
        rw [erh]; intro h0
        obtain ⟨r1, r2⟩ := P.rs (Locks := Locks) h0
        obtain ⟨hxT, hxS, -⟩ := bxi_rh P.bxi h0
        have e1 : L.mem s2' (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
          (tk _ hxT 3464#u64 (by decide) (by decide) (by decide)).trans (G.m _ r1)
        rw [e1]
        exact ⟨ra r1, rdT _ (hd hxS) r2⟩
      dt := by
        rw [w.1, Al.ksb]
        exact ra (P.ksw (Locks := Locks) (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))
      cd := by
        rw [w.1, Al.ksb]
        exact ra (P.ksw (Locks := Locks) (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN]))
      af := ra (P.gate (Locks := Locks) (off := 3520#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
      dom := ra (P.gate (Locks := Locks) (off := 3432#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
      sc := ra (P.gate (Locks := Locks) (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
      inq := ra (P.home (Locks := Locks) (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1 }⟩

/-- **`PathSide.read_aligned` from a declining entry**: a run that declines at `s`
runs at every alternative `s'` on the store guarded to aligned reads as on `st`. -/
theorem io_ra_decU {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {r0 r : Bool × S × A} (h0 : syscall.handle_ioport_local st ar s a number = ok r0) (hr0 : r0.1 ≠ true)
    (h : syscall.handle_ioport_local st ar s' a number = ok r) :
    syscall.handle_ioport_local (guard st (fun b => Aligned b ∧ b ∉ K.user) (fun _ => True)) ar s' a number = ok r := by
  have hr : r.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r
    intro hb
    change b = true at hb
    subst hb
    exact io_alt_not_acc hA P Al h0 hr0 h
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have ra : ∀ {x : U64}, IoRS (st := st) K Locks s x → Aligned x ∧ x ∉ K.user := fun h => ⟨h.1, h.2.1⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      (Aligned (L.nodeAt s' (L.cpu s') o) ∧ L.nodeAt s' (L.cpu s') o ∉ K.user) ∧ True := fun o h1 h2 =>
    ⟨by rw [G.node]; exact ra (P.nd (Locks := Locks) o h1 h2).1, trivial⟩
  rw [handle_ioport_local_eq] at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := guard st (fun b => Aligned b ∧ b ∉ K.user) (fun _ => True)) s'
    (hNd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [hcur, msg.msg_info.guard (gS := guard st (fun b => Aligned b ∧ b ∉ K.user) (fun _ => True)) s' _
    (ra (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1)]
  refine tr_bind_same (fun info _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard (gS := guard st (fun b => Aligned b ∧ b ∉ K.user) (fun _ => True)) (L.curW s) s'
    (ra (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField])).1)]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  have hT := fun (h : ioTail st ar s' a (L.curW s) info number = ok r) =>
    ioTail.guardD (gS := guard st (fun b => Aligned b ∧ b ∉ K.user) (fun _ => True)) ar hNd
      (ra (P.reg (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1) trivial
      (fun nx s1 s2 a1 _ e1 e2 => io_alt_midDU (nx := nx) hA P Al e1 e2) hr h
  exact tr_ite (fun _ => tr_ite (fun _ h => h) (fun _ => hT)) (fun _ => hT)

end

end Fl4Proofs.P2.PathObl

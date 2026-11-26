/-
# P2 (line invj, generation 8): declines and the pruned body at the alternatives of `IoRSR`

Scripted copies with the region-tagged read set `IoRSR` (P2/InvDelPteIoR.lean) in place of `IoRS` and its `IoPre`
lemmas (`…R`), so that they hold at the alternatives of the PTE-arm path's read set `InvRSP` (`Alt.anti`:
`IoRSR ⊆ IoRSP ⊆ InvRSP`):

* `slot_backR` (`slot_back`), `io_alt_midDR` (`io_alt_midD`), **`inv_ra_decR`** (`inv_ra_dec`: `read_aligned` of a
  declining entry), `io_alt_midRR` (`io_alt_midR`), **`inv_dec_guardRSR`** (`inv_dec_guardRS`: a declining run on
  the store guarded to `IoRSR s`, for `ReadOnce`);
* **`inv_pruneR`**, **`inv_isProgOnR`** (`inv_prune`, `inv_isProgOn`: the program premise over `IoRSR`'s
  alternatives from the pruned body's tree).

Heartbeats: `io_alt_midRR` keeps `io_alt_midR`'s `maxHeartbeats 2000000`, `inv_pruneR` keeps `inv_prune`'s
1000000. No named premise (`hSC` / `hSeen` as in the sources, discharged by the caller). New module; no existing
statement changes.
-/
import Fl4Proofs.P2.InvDelPteDecR
import Fl4Proofs.P2.InvOnce
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section decR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s' : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}


/-- At an alternative state, a slot's CNode or I/O port cap was there at `s`. -/
theorem slot_backR (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (Al : Alt st (IoRSR st K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {sl : U64} (hsl : sl ∈ K.slots) {c : capability.Cap} (hc : obj.Slot.cap st sl s' = ok c)
    (h : (∃ p' r' gs' g', c = .CNode p' r' gs' g') ∨ ∃ f l z, c = .IoPort f l z) :
    obj.Slot.cap st sl s = ok c := by
  have hn' := cap_not_nof hc h
  obtain ⟨h8, hf⟩ := P.lay.slot8 sl hsl
  have hr : region K sl = .slot sl := P.lay.slotw sl hsl sl ⟨le_refl _, by omega⟩
  have hg : TcbSlot K sl ∨ ¬ NullOrFrame (L.mem s sl) := by
    by_cases hT : TcbSlot K sl
    · exact Or.inl hT
    refine Or.inr fun hn => ?_
    by_cases hR : IoRSR st K Locks s sl
    · rw [Al.read sl hR] at hn'; exact hn' hn
    · have hk : OwnMap.ko K m0 sl = .gate := by
        unfold OwnMap.ko; simp only [hr]; rw [if_pos ⟨rfl, hT⟩]
      have hu : sl ∉ K.user := P.region_kernel (Or.inl (by rw [hr]; simp))
      have e := Al.clsEq sl hR hu (Or.inl hk)
      unfold OwnMap.cls at e
      simp only [hr] at e
      rw [if_neg (fun h => hn' h.2.2), if_pos ⟨rfl, hT, hn⟩] at e
      exact hn' (by rw [e]; left; rfl)
  obtain ⟨r0, r8⟩ := P.slotR (Locks := Locks) hsl hg
  unfold obj.Slot.cap at hc ⊢
  rw [L.read_pair_eq] at hc ⊢
  rw [Al.read _ r0, Al.read _ r8] at hc
  exact hc


/-- **`IoMidD` (aligned reads) at an alternative's post-prefix state.** -/
theorem io_alt_midDR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (Al : Alt st (IoRSR st K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {nx : U64} {s1' s2' : S} {a1 : A}
    (hs1 : obj.Tcb.set_reg st (L.curW s) s' layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1')
    (hu : sched.update_timestamp st ar s1' a = ok (s2', a1)) :
    ∃ C sl, IoMidD (L := L) (fun b => Aligned b) s' s2' (L.curW s) C sl := by
  have G : Ag st (IoRSR st K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
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
    exact G.m _ (P.ndR (Locks := Locks) o h1 h2).1
  have po : ∀ b, OutsideObjs st T Cs s b → IoRSR st K Locks s b → L.mem s2' b = L.mem s b := by
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
    exact hcl p r m y p' r' gs' g' hp hm (slot_backR P Al hs hc (Or.inl ⟨_, _, _, _, rfl⟩))
  have hsl0 := (P.lay.tslot _ (P.hT _ P.cT) layout.tcb.SLOT_CTABLE _ (tcb_slot_ctable _)
    (by simp [layout.tcb.SLOT_CTABLE])).1
  have hroot2 : ∀ p r gs g, obj.Slot.cap st (L.curW s) s2' = ok (.CNode p r gs g) → C p r := by
    intro p r gs g hc
    rw [sk _ hsl0] at hc
    exact hroot p r gs g (slot_backR P Al hsl0 hc (Or.inl ⟨_, _, _, _, rfl⟩))
  have hRf : ∀ cptr (x : cspace.Resolved), cspace.lookup_slot st s2' (L.curW s) cptr = ok (.Ok x) →
      Aligned x.slot ∧ Aligned (core.num.U64.wrapping_add x.slot 8#u64) := by
    intro cptr x h
    unfold cspace.lookup_slot at h
    rw [tcb_slot_ctable] at h; simp only [bind_ok] at h
    obtain ⟨root, er, h⟩ := bind_eq_ok h
    obtain ⟨p, r, m, y, hp, hm, e⟩ := rab_loop_slot st C hcl2 66 root _ 65#u64 x (by simp)
      (fun p r gs g e => hroot2 p r gs g (e ▸ er)) h
    rw [e]; exact slA _ (hC p r m y hp hm).1
  -- the SC head words
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  have rdT : ∀ sc, OutsideObjs st T Cs s (headA sc) → RdHead (L := L) (IoRSR st K Locks s) s sc →
      RdHead (L := L) (fun b => Aligned b) s2' sc := by
    intro sc ho h
    have e := po _ ho h.1
    unfold RdHead LawfulStore.rhead at h ⊢
    rw [e]; exact ⟨h.1.1.1, h.2.1.1.1, h.2.2.1.1⟩
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
      Aligned sl ∧ Aligned (core.num.U64.wrapping_add sl 8#u64) := fun i sl h hi =>
    slA _ (P.lay.tslot _ (P.hT _ P.cT) i sl h hi).1
  refine ⟨C, L.curW s,
    { k := w.1
      c := w.2.1
      cur := ecur
      r10 := (P.reg (Locks := Locks) (by simp [layout.reg.R10])).1.1
      cap := (P.reg (Locks := Locks) (by simp [layout.reg.CAP])).1.1
      yld := (P.home (Locks := Locks) (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1.1
      hsl := tcb_slot_ctable _
      hR0 := (slA _ hsl0).1
      hR8 := (slA _ hsl0).2
      hRc := fun p r m y _ _ _ _ hp hm _ => slA _ (hC p r m y hp hm).1
      hcl := hcl2
      hroot := hroot2
      hRf := hRf
      ib := (P.gate (Locks := Locks) (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])).1
      bs := fun bsl h => hsl _ bsl h (by simp [layout.tcb.SLOT_BUFFER])
      rh := by rw [ecs]; exact rdT _ (hd P.cscS) ((P.cscaccR (Locks := Locks)).head P.cscwf)
      td := by rw [etm]; exact fun h0 => (P.td (Locks := Locks) h0).1
      rs := by
        rw [erh]; intro h0
        obtain ⟨r1, r2⟩ := P.rsR (Locks := Locks) h0
        obtain ⟨hxT, hxS, -⟩ := bxi_rh P.bxi h0
        have e1 : L.mem s2' (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
          (tk _ hxT 3464#u64 (by decide) (by decide) (by decide)).trans (G.m _ r1)
        rw [e1]
        exact ⟨r1.1.1, rdT _ (hd hxS) r2⟩
      dt := by
        rw [w.1, Al.ksb]
        exact (P.ksw (Locks := Locks) (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])).1
      cd := by
        rw [w.1, Al.ksb]
        exact (P.ksw (Locks := Locks) (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])).1
      af := (P.gate (Locks := Locks) (off := 3520#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])).1
      dom := (P.gate (Locks := Locks) (off := 3432#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])).1
      sc := (P.gate (Locks := Locks) (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])).1
      inq := (P.home (Locks := Locks) (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1.1 }⟩



/-- **`PathSide.read_aligned` from a declining entry** of the frame-cap invocation path: a run that declines at
`s` runs at every alternative `s'` on the store guarded to aligned reads as on `st` (`hSeen` [J]). -/
theorem inv_ra_decR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ x, SeenW p x → IoRSR st K Locks s x)
    (Al : Alt st (IoRSR st K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {r0 r : Bool × S × A} (h0 : syscall.handle_invocation_local st ar s a number p = ok r0)
    (hr0 : r0.1 ≠ true) (h : syscall.handle_invocation_local st ar s' a number p = ok r) :
    syscall.handle_invocation_local (guard st (fun b => Aligned b) (fun _ => True)) ar s' a number p = ok r := by
  have hr : r.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r
    intro hb
    change b = true at hb
    subst hb
    exact inv_alt_not_accR hA P hSeen Al h0 hr0 h
  have G : Ag st (IoRSR st K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      Aligned (L.nodeAt s' (L.cpu s') o) ∧ True := fun o h1 h2 =>
    ⟨by rw [G.node]; exact nodeAt_aligned P.np h1 h2, trivial⟩
  rw [handle_invocation_local_eq] at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := guard st (fun b => Aligned b) (fun _ => True)) s'
    (hNd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [hcur, msg.msg_info.guard (gS := guard st (fun b => Aligned b) (fun _ => True)) s' _
    (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1.1]
  refine tr_bind_same (fun info _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard (gS := guard st (fun b => Aligned b) (fun _ => True)) (L.curW s) s'
    (field_aligned P.tA (K := 3456#u64) (by decide) (by decide))]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ ht => ?_)
  exact invTail.guardD (gS := guard st (fun b => Aligned b) (fun _ => True)) ar hNd
    (P.reg (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1.1 trivial
    (fun nx s1 s2 a1 _ e1 e2 => io_alt_midDR (nx := nx) hA P Al e1 e2)
    (fun x => still_holds_guard p x (fun w hw => (hSeen w hw).1.1)) hr ht

set_option maxHeartbeats 2000000 in
/-- **`IoMidR (IoRS s)` at an alternative's post-prefix state** (module docstring). -/
theorem io_alt_midRR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (Al : Alt st (IoRSR st K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {nx : U64} {s1' s2' : S} {a1 : A}
    (hs1 : obj.Tcb.set_reg st (L.curW s) s' layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1')
    (hu : sched.update_timestamp st ar s1' a = ok (s2', a1)) :
    ∃ C sl, IoMidR (L := L) (IoRSR st K Locks s) s2' (L.curW s) C sl := by
  have G : Ag st (IoRSR st K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
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
    exact G.m _ (P.ndR (Locks := Locks) o h1 h2).1
  have po : ∀ b, OutsideObjs st T Cs s b → IoRSR st K Locks s b → L.mem s2' b = L.mem s b := by
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
      IoRSR st K Locks s sl ∧ IoRSR st K Locks s (core.num.U64.wrapping_add sl 8#u64) := by
    intro sl hs c hc hk
    rw [sk _ hs] at hc
    have hb := slot_backR P Al hs hc hk
    exact P.slotR (Locks := Locks) hs (Or.inr (cap_not_nof hb hk))
  have hcl2 : WalkCl (st := st) s2' C := by
    intro p r m y p' r' gs' g' hp hm hc
    have hs := (hC p r m y hp hm).1
    rw [sk _ hs] at hc
    exact hcl p r m y p' r' gs' g' hp hm (slot_backR P Al hs hc (Or.inl ⟨_, _, _, _, rfl⟩))
  have hsl0 := (P.lay.tslot _ (P.hT _ P.cT) layout.tcb.SLOT_CTABLE _ (tcb_slot_ctable _)
    (by simp [layout.tcb.SLOT_CTABLE])).1
  have hroot2 : ∀ p r gs g, obj.Slot.cap st (L.curW s) s2' = ok (.CNode p r gs g) → C p r := by
    intro p r gs g hc
    rw [sk _ hsl0] at hc
    exact hroot p r gs g (slot_backR P Al hsl0 hc (Or.inl ⟨_, _, _, _, rfl⟩))
  have hslot : ∀ i sl, obj.Tcb.slot (L.curW s) i = ok sl → i.val < 6 →
      IoRSR st K Locks s sl ∧ IoRSR st K Locks s (core.num.U64.wrapping_add sl 8#u64) := fun i sl h hi => by
    obtain ⟨h1, h2⟩ := P.lay.tslot _ (P.hT _ P.cT) i sl h hi
    exact P.slotR (Locks := Locks) h1 (Or.inl h2)
  have h0 := hslot _ _ (tcb_slot_ctable (L.curW s)) (by simp [layout.tcb.SLOT_CTABLE])
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  have rdT : ∀ sc, OutsideObjs st T Cs s (headA sc) → RdHead (L := L) (IoRSR st K Locks s) s sc →
      RdHead (L := L) (IoRSR st K Locks s) s2' sc := by
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
        rw [w.2.1, nodeAt_of_ksb w.1, G.node]; exact (P.ndR (Locks := Locks) o h1 h2).1
      cur := ecur
      r10 := (P.regR (Locks := Locks) (by simp [layout.reg.R10])).1
      cap := (P.regR (Locks := Locks) (by simp [layout.reg.CAP])).1
      yld := (P.homeR (Locks := Locks) (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1
      hsl := tcb_slot_ctable _
      hR0 := h0.1
      hR8 := h0.2
      hRc := fun p r m y p' r' gs' g' hp hm hc =>
        hRS _ (hC p r m y hp hm).1 _ hc (Or.inl ⟨_, _, _, _, rfl⟩)
      hcl := hcl2
      hroot := hroot2
      hIo := fun p r m y f l z hp hm hc => hRS _ (hC p r m y hp hm).1 _ hc (Or.inr ⟨_, _, _, rfl⟩)
      ib := P.gateR (Locks := Locks) (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
      bs := fun bsl h => hslot _ bsl h (by simp [layout.tcb.SLOT_BUFFER])
      rh := by rw [ecs]; exact rdT _ (hd P.cscS) ((P.cscaccR (Locks := Locks)).head P.cscwf)
      td := by rw [etm]; exact P.tdR (Locks := Locks)
      rs := by
        rw [erh]; intro h0
        obtain ⟨r1, r2⟩ := P.rsR (Locks := Locks) h0
        obtain ⟨hxT, hxS, -⟩ := bxi_rh P.bxi h0
        have e1 : L.mem s2' (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
          (tk _ hxT 3464#u64 (by decide) (by decide) (by decide)).trans (G.m _ r1)
        rw [e1]
        exact ⟨r1, rdT _ (hd hxS) r2⟩
      dt := by
        rw [w.1, Al.ksb]
        exact P.kswR (Locks := Locks) (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
      cd := by
        rw [w.1, Al.ksb]
        exact P.kswR (Locks := Locks) (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
      af := P.gateR (Locks := Locks) (off := 3520#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
      dom := P.gateR (Locks := Locks) (off := 3432#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
      sc := P.gateR (Locks := Locks) (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
      inq := (P.homeR (Locks := Locks) (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1 }⟩

/-- **A run declining at `s` runs at every alternative `s'` on the store guarded to `IoRS s`** (reads; writes
unguarded) as on `st` (`hSeen` [J]). -/
theorem inv_dec_guardRSR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64}
    {p : localinv.Plan} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ x, SeenW p x → IoRSR st K Locks s x)
    (Al : Alt st (IoRSR st K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {r0 r : Bool × S × A} (h0 : syscall.handle_invocation_local st ar s a number p = ok r0)
    (hr0 : r0.1 ≠ true) (h : syscall.handle_invocation_local st ar s' a number p = ok r) :
    syscall.handle_invocation_local (guard st (IoRSR st K Locks s) (fun _ => True)) ar s' a number p =
      ok r := by
  have hr : r.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r
    intro hb
    change b = true at hb
    subst hb
    exact inv_alt_not_accR hA P hSeen Al h0 hr0 h
  have G : Ag st (IoRSR st K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRSR st K Locks s (L.nodeAt s' (L.cpu s') o) ∧ True := fun o h1 h2 =>
    ⟨by rw [G.node]; exact (P.ndR (Locks := Locks) o h1 h2).1, trivial⟩
  rw [handle_invocation_local_eq] at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := guard st (IoRSR st K Locks s) (fun _ => True)) s'
    (hNd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [hcur, msg.msg_info.guard (gS := guard st (IoRSR st K Locks s) (fun _ => True)) s' _
    (P.regR (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1]
  refine tr_bind_same (fun info _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard (gS := guard st (IoRSR st K Locks s) (fun _ => True)) (L.curW s) s'
    (P.homeR (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField])).1]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ ht => ?_)
  exact invTail.guardR (gS := guard st (IoRSR st K Locks s) (fun _ => True)) ar hNd
    (P.regR (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1 trivial
    (fun nx s1 s2 a1 _ e1 e2 => io_alt_midRR (nx := nx) hA P Al e1 e2)
    (fun x => still_holds_guard p x (fun w hw => hSeen w hw)) hr ht

end decR

section pruneR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **The frame-cap invocation body is `invBodyG`** on every store narrowing `st`, from every entry state and
every alternative of one (`hSC` [J]). -/
theorem inv_pruneR (hA : P0.ArchTotal ar) {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {p : localinv.Plan}
    (hSC : InvSlotCN st K p P) {m : machine.Store S} (N : Narrow st m)
    {s' : S} (hG : AltOf st P (IoRSR st K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s')
    (a : A) (number : I64) :
    syscall.handle_invocation_local m ar s' a number p = invBodyG m ar s' a number p := by
  obtain ⟨s, hE, Al⟩ := hG
  have P := hPE s hE
  obtain ⟨hsl, x1, x2, x3, x4, hcs⟩ := hSC s hE
  have G : Ag st (IoRSR st K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hN' : NodePlaced st T s' (L.cpu s') := by rw [Al.cpu]; exact P.np.ksb Al.ksb
  have hcT' : L.curW s' ∈ T := by rw [hcur]; exact P.cT
  -- the cap at `p.slot` at the alternative is the entry's CNode cap
  have hnf := cap_not_nof hcs (Or.inl ⟨x1, x2, x3, x4, rfl⟩)
  obtain ⟨r0, r8⟩ := P.slotR (Locks := Locks) hsl (Or.inr hnf)
  have hcs' : obj.Slot.cap st p.slot s' = ok (.CNode x1 x2 x3 x4) := by
    rw [← hcs]
    unfold obj.Slot.cap
    rw [L.read_pair_eq, L.read_pair_eq, Al.read _ r0, Al.read _ r8]
  obtain ⟨h8, hf⟩ := P.lay.slot8 _ hsl
  have hv : (core.num.U64.wrapping_add p.slot 8#u64).val = p.slot.val + 8 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine hil_eq_G m ar s' a number p fun t i2 s1 s2 a1 c ht hs1 hu hc => ?_
  have et : t = L.curW s' := by
    have := (cur_thread_nar N s').ok_eq ht
    rw [cur_thread_ok] at this
    exact (ok_inj_ff this).symm
  subst et
  have es1 := (set_reg_nar N _ s' _ i2).ok_eq hs1
  have eu := (update_timestamp_nar N ar s1 a).ok_eq hu
  have ec := (slot_cap_nar N _ s2).ok_eq hc
  have w := prefix_writes ar hA P.tp hN' hcT' es1 eu
  have np : ∀ b, InW p.slot 32 b → Aligned b → L.mem s2 b = L.mem s' b := by
    intro b hb ha
    obtain ⟨p1, p2, p3⟩ := prefix_slot P hsl hb
    refine w.2.2 _ ha ?_
    rintro (⟨K', hK', e⟩ | e | e)
    · obtain ⟨k, hk, e2⟩ := regA_eq P.tA (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
      have ek : K' = k := UScalar.eq_of_val_eq (by rw [hK', hk]; simp [layout.reg.FAULT_IP])
      exact p1 (by rw [e2, e, hcur, ek])
    · exact p2 (e.trans (G.node _))
    · exact p3 (e.trans (G.node _))
  have sk : obj.Slot.cap st p.slot s2 = obj.Slot.cap st p.slot s' := by
    unfold obj.Slot.cap
    rw [L.read_pair_eq, L.read_pair_eq, np p.slot ⟨le_refl _, by omega⟩ h8,
      np _ ⟨by omega, by omega⟩ (by unfold Aligned; omega)]
  rw [sk, hcs'] at ec
  exact ⟨x1, x2, x3, x4, (ok_inj_ff ec).symm⟩

/-- **The relativised program premise of the frame-cap invocation path** from a tree of the pruned body
(`hSC` [J]). -/
theorem inv_isProgOnR (hA : P0.ArchTotal ar) {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {number : I64} {p : localinv.Plan}
    (hSC : InvSlotCN st K p P) {q : SProg Bool} (hp : IsProg (invBodyP S number p) q) :
    IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRSR st K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q :=
  fun m N s' hG a => by
    show syscall.handle_invocation_local m ar s' a number p = _
    exact (inv_pruneR (Locks := Locks) hA hPE hSC N hG a number).trans (congrFun (congrFun (hp A ar m) s') a)

end pruneR

end Fl4Proofs.P2.PathObl

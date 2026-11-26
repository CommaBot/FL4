/-
# P2 (line p3mc, gen 27): the CNodeDelete run's entry facts and outer skeleton on a read set cut by a word class

Handoff §31c. The invocation's outer skeleton (`syscall.handle_invocation_local.guard_acc2`, `invTail.guardR`) is
generic in the read set; what fixes it to `IoRSR` are the entry facts (`IoPre.entR`, `IoPre.midR`,
`io_alt_midRR`) and the wrappers `inv_acc_genR` / `inv_dec_guardRSR`. Here they are restated for any read set `R`
holding the `IoRSR s` words of a set of word classes `G` (`GCl`: the node words, the current thread's words at
192–4095, its registers, the capability slots' base / second words, the current SC's words, the kernel-global
words `ksb + o`, `o < 256`, the earliest timer's deadline, the release head's `SC` word and refill head):

* `GCl`, `rdh_and`; **`IoPre.iaccV`**, **`IoPre.entV`** (`IoEnt` over `R`), **`IoPre.midV`** (`IoMid` over `R`),
  **`io_alt_midRV`** (`IoMidR` over `R` at an alternative's post-prefix state; scripted from `io_alt_midRR`);
* **`inv_acc_genV`** (`inv_acc_genR` with `Ent`, the three prefix reads and `IoMid` over `R` given): the accepted run
  on a store `gS` reading `R` and writing `W` ends as on `st`, given the decode block over `R`;
* **`inv_dec_genV`**: a run declining at `s` runs at `s` on such a store as on `st` (`inv_dec_guardRSR` at the entry
  itself, the writes `W`-checked).

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelV
import Fl4Proofs.P2.InvDelPteRaR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section gcl
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The word classes the CNodeDelete run reads at its entry `s`** (module docstring), each in `G`. -/
structure GCl (K : KLayout) (Z : U64 → Nat) (G : U64 → Prop) (s : S) : Prop where
  n : ∀ o : U64, o.val < 4288 → G (L.nodeAt s (L.cpu s) o)
  t : ∀ k : U64, 192 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → G (fld (L.curW s) k)
  r : ∀ r : U64, r.val < 384 → G (regA (L.curW s) r)
  sl : ∀ q ∈ K.slots, G q ∧ G (core.num.U64.wrapping_add q 8#u64)
  sc : ∀ b, Aligned b → InSC (L.cscW s) (Z (L.cscW s)) b → G b
  ks : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → G (core.num.U64.wrapping_add (L.ksb s) o)
  td : L.mem s (tmA (L := L) s) ≠ 0#u64 → G (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64)
  rs : L.mem s (rhA (L := L) s) ≠ 0#u64 → G (scA (L.mem s (rhA (L := L) s))) ∧
    RdHead (L := L) G s (L.mem s (scA (L.mem s (rhA (L := L) s))))

variable {st}

theorem rdh_and {R0 G R : U64 → Prop} {s : S} {sc : U64} (h0 : RdHead (L := L) R0 s sc)
    (hg : RdHead (L := L) G s sc) (hR : ∀ b, R0 b → G b → R b) : RdHead (L := L) R s sc :=
  ⟨hR _ h0.1 hg.1, hR _ h0.2.1 hg.2.1, hR _ h0.2.2 hg.2.2⟩

end gcl

section pre
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop}
variable (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {R G : U64 → Prop} (Gc : GCl st K Z G s)
  (hR : ∀ b, IoRSR st K Locks s b → G b → R b)
include P Gc hR

/-- `IoPre.iaccR` over `R`. -/
theorem IoPre.iaccV {W : U64 → Prop} (hW : IoWr st W Z s) : IoAcc st R W s (L.cscW s) (Z (L.cscW s)) where
  acc := ⟨fun b ha hi => hR _ ((P.cscaccR (Locks := Locks)).rd b ha hi) (Gc.sc b ha hi), hW.ring, hW.cons⟩
  nd := fun o h1 h2 => ⟨hR _ (P.ndR (Locks := Locks) o h1 h2).1 (Gc.n o h1), hW.nd o h1 h2⟩
  sc := hR _ (P.gateR (Locks := Locks) (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
    (Gc.t _ (by simp) (by simp) (by simp))
  dt := hR _ (P.kswR (Locks := Locks) (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))
    (Gc.ks _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))
  td := fun h0 => hR _ (P.tdR (Locks := Locks) h0) (Gc.td h0)
  rs := fun h0 => ⟨hR _ (P.rsR (Locks := Locks) h0).1 (Gc.rs h0).1,
    rdh_and (P.rsR (Locks := Locks) h0).2 (Gc.rs h0).2 hR⟩
  ryl := hR _ (P.homeR (Locks := Locks) (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    (by simp [TimerField])).1 (Gc.t _ (by simp) (by simp) (by simp))
  rst := hR _ (P.stwR (Locks := Locks)).1 (by
    have := Gc.t 3328#u64 (by simp) (by simp) (by simp)
    rw [Fl4Proofs.P1.stA_eq]; exact this)
  rfi := hR _ (P.regR (Locks := Locks) (by simp [layout.reg.FAULT_IP])).1 (Gc.r _ (by simp [layout.reg.FAULT_IP]))
  wnx := hW.reg _ (by simp [layout.reg.NEXT_IP])
  rin := hR _ (P.homeR (Locks := Locks) (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    (by simp [TimerField])).1 (Gc.t _ (by simp) (by simp) (by simp))

/-- `IoPre.entR` over `R`. -/
theorem IoPre.entV {W : U64 → Prop} (hW : IoWr st W Z s) : IoEnt st T Cs Ω H Sg Rp Scs Nt Z Ac R W s :=
  ⟨P.bxi, P.csc, P.hcsc, P.run, P.iaccV Gc hR hW⟩

/-- `IoPre.midR` over `R`. -/
theorem IoPre.midV {W : U64 → Prop} (hW : IoWr st W Z s) {C : U64 → U64 → Prop}
    (hroot : ∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r) (hcl : WalkCl (st := st) s C)
    (hsl : ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots)
    (hsc0 : L.mem s (scA (L.curW s)) = L.cscW s)
    (info : msginfo.MessageInfo) (emi : msg.msg_info st s (L.curW s) = ok info) :
    IoMid (L := L) R W s s (L.curW s) info (L.mem s (regA (L.curW s) layout.reg.CAP)) C (L.curW s) := by
  have hslot : ∀ i sl, obj.Tcb.slot (L.curW s) i = ok sl → i.val < 6 →
      R sl ∧ R (core.num.U64.wrapping_add sl 8#u64) := fun i sl h hi => by
    obtain ⟨h1, h2⟩ := P.lay.tslot _ (P.hT _ P.cT) i sl h hi
    have e := P.slotR (Locks := Locks) h1 (Or.inl h2)
    exact ⟨hR _ e.1 (Gc.sl _ h1).1, hR _ e.2 (Gc.sl _ h1).2⟩
  have hsl2 : ∀ sl, sl ∈ K.slots → (TcbSlot K sl ∨ ¬ NullOrFrame (L.mem s sl)) →
      R sl ∧ R (core.num.U64.wrapping_add sl 8#u64) := fun sl h1 h2 => by
    have e := P.slotR (Locks := Locks) h1 h2
    exact ⟨hR _ e.1 (Gc.sl _ h1).1, hR _ e.2 (Gc.sl _ h1).2⟩
  have h0 := hslot _ _ (tcb_slot_ctable (L.curW s)) (by simp [layout.tcb.SLOT_CTABLE])
  have hO := P.bxi.2.2.1.1
  have hmx := maxA_facts hO P.cscS
  have ac := P.iaccV Gc hR hW
  exact
  { k := rfl, c := rfl, cur := rfl, mi := emi
    rmi := hR _ (P.regR (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1 (Gc.r _ (by simp [layout.reg.MSG_INFO]))
    r10 := hR _ (P.regR (Locks := Locks) (by simp [layout.reg.R10])).1 (Gc.r _ (by simp [layout.reg.R10]))
    cap := hR _ (P.regR (Locks := Locks) (by simp [layout.reg.CAP])).1 (Gc.r _ (by simp [layout.reg.CAP]))
    yld := ac.ryl
    hsl := tcb_slot_ctable _
    hR0 := h0.1, hR8 := h0.2
    hRc := fun p r m y p' r' gs' g' hp hm hc =>
      hsl2 _ (hsl p r m y hp hm) (Or.inr (cap_not_nof hc (Or.inl ⟨_, _, _, _, rfl⟩)))
    hcl := hcl
    hroot := hroot
    hRf := fun x f l z hx hc => hsl2 _ (P.fin x hx).1 (Or.inr (cap_not_nof hc (Or.inr ⟨_, _, _, rfl⟩)))
    rh := ScAcc.head ac.acc P.cscwf
    td := ac.td
    rs := ac.rs
    dt := ac.dt
    cd := hR _ (P.kswR (Locks := Locks) (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN]))
      (Gc.ks _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN]))
    af := hR _ (P.gateR (Locks := Locks) (off := 3520#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
      (Gc.t _ (by simp) (by simp) (by simp))
    dom := hR _ (P.gateR (Locks := Locks) (off := 3432#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
      (Gc.t _ (by simp) (by simp) (by simp))
    iok := ⟨
      { tcb := P.tA
        regR := fun r hr => hR _ (P.regR (Locks := Locks) hr).1 (Gc.r r hr)
        regW := fun r hr => hW.reg r hr
        stR := ac.rst
        sc := ac.sc
        max := by rw [hsc0]; exact ac.acc.rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩
        inq := ac.rin
        ib := hR _ (P.gateR (Locks := Locks) (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
          (Gc.t _ (by simp) (by simp) (by simp))
        bs := fun sl h => hslot _ sl h (by simp [layout.tcb.SLOT_BUFFER]) },
      ⟨(ac.nd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1,
        (ac.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1,
        hW.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])⟩,
      nodeAt_aligned P.np (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]),
      node_ne_field P.np (by simp [layout.node.SCHED_ACTION]) P.cT P.tA (by simp)⟩ }

end pre

section decV
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s' : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}

set_option maxHeartbeats 2000000 in
/-- (p3mc gen 27) **`IoMidR R` at an alternative's post-prefix state**, `R` any read set holding the `IoRSR s`
words of the classes `Gc` (`io_alt_midRR` with every field cut by `G`). -/
theorem io_alt_midRV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {R G : U64 → Prop} (Gc : GCl st K Z G s)
    (hR : ∀ b, IoRSR st K Locks s b → G b → R b)
    (Al : Alt st (IoRSR st K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {nx : U64} {s1' s2' : S} {a1 : A}
    (hs1 : obj.Tcb.set_reg st (L.curW s) s' layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1')
    (hu : sched.update_timestamp st ar s1' a = ok (s2', a1)) :
    ∃ C sl, IoMidR (L := L) R s2' (L.curW s) C sl := by
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
      R sl ∧ R (core.num.U64.wrapping_add sl 8#u64) := by
    intro sl hs c hc hk
    rw [sk _ hs] at hc
    have hb := slot_backR P Al hs hc hk
    have e := P.slotR (Locks := Locks) hs (Or.inr (cap_not_nof hb hk))
    exact ⟨hR _ e.1 (Gc.sl _ hs).1, hR _ e.2 (Gc.sl _ hs).2⟩
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
      R sl ∧ R (core.num.U64.wrapping_add sl 8#u64) := fun i sl h hi => by
    obtain ⟨h1, h2⟩ := P.lay.tslot _ (P.hT _ P.cT) i sl h hi
    have e := P.slotR (Locks := Locks) h1 (Or.inl h2)
    exact ⟨hR _ e.1 (Gc.sl _ h1).1, hR _ e.2 (Gc.sl _ h1).2⟩
  have h0 := hslot _ _ (tcb_slot_ctable (L.curW s)) (by simp [layout.tcb.SLOT_CTABLE])
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  have rdT : ∀ sc, OutsideObjs st T Cs s (headA sc) → IoRSR st K Locks s (headA sc) →
      RdHead (L := L) R s sc → RdHead (L := L) R s2' sc := by
    intro sc ho h1 h
    have e := po _ ho h1
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
        rw [w.2.1, nodeAt_of_ksb w.1, G.node]; exact hR _ (P.ndR (Locks := Locks) o h1 h2).1 (Gc.n o h1)
      cur := ecur
      r10 := hR _ (P.regR (Locks := Locks) (by simp [layout.reg.R10])).1 (Gc.r _ (by simp [layout.reg.R10]))
      cap := hR _ (P.regR (Locks := Locks) (by simp [layout.reg.CAP])).1 (Gc.r _ (by simp [layout.reg.CAP]))
      yld := hR _ (P.homeR (Locks := Locks) (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1 (Gc.t _ (by simp) (by simp) (by simp))
      hsl := tcb_slot_ctable _
      hR0 := h0.1
      hR8 := h0.2
      hRc := fun p r m y p' r' gs' g' hp hm hc =>
        hRS _ (hC p r m y hp hm).1 _ hc (Or.inl ⟨_, _, _, _, rfl⟩)
      hcl := hcl2
      hroot := hroot2
      hIo := fun p r m y f l z hp hm hc => hRS _ (hC p r m y hp hm).1 _ hc (Or.inr ⟨_, _, _, rfl⟩)
      ib := hR _ (P.gateR (Locks := Locks) (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
        (Gc.t _ (by simp) (by simp) (by simp))
      bs := fun bsl h => hslot _ bsl h (by simp [layout.tcb.SLOT_BUFFER])
      rh := by
        rw [ecs]
        exact rdT _ (hd P.cscS) ((P.cscaccR (Locks := Locks)).head P.cscwf).1
          (ScAcc.head ⟨fun b ha hi => hR _ ((P.cscaccR (Locks := Locks)).rd b ha hi) (Gc.sc b ha hi),
            (P.cscaccR (Locks := Locks)).wr, (P.cscaccR (Locks := Locks)).cons⟩ P.cscwf)
      td := by rw [etm]; exact fun h0 => hR _ (P.tdR (Locks := Locks) h0) (Gc.td h0)
      rs := by
        rw [erh]; intro h0
        obtain ⟨r1, r2⟩ := P.rsR (Locks := Locks) h0
        obtain ⟨g1, g2⟩ := Gc.rs h0
        obtain ⟨hxT, hxS, -⟩ := bxi_rh P.bxi h0
        have e1 : L.mem s2' (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
          (tk _ hxT 3464#u64 (by decide) (by decide) (by decide)).trans (G.m _ r1)
        rw [e1]
        exact ⟨hR _ r1 g1, rdT _ (hd hxS) r2.1 (rdh_and r2 g2 hR)⟩
      dt := by
        rw [w.1, Al.ksb]
        exact hR _ (P.kswR (Locks := Locks) (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))
          (Gc.ks _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))
      cd := by
        rw [w.1, Al.ksb]
        exact hR _ (P.kswR (Locks := Locks) (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN]))
          (Gc.ks _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN]))
      af := hR _ (P.gateR (Locks := Locks) (off := 3520#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
        (Gc.t _ (by simp) (by simp) (by simp))
      dom := hR _ (P.gateR (Locks := Locks) (off := 3432#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
        (Gc.t _ (by simp) (by simp) (by simp))
      sc := hR _ (P.gateR (Locks := Locks) (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
        (Gc.t _ (by simp) (by simp) (by simp))
      inq := hR _ (P.homeR (Locks := Locks) (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1 (Gc.t _ (by simp) (by simp) (by simp)) }⟩

set_option maxHeartbeats 1000000 in
/-- (p3mc gen 27) **A run declining at `s` runs at `s` on a store reading `R` and writing `W` as on `st`**
(`inv_dec_guardRSR` at the entry itself; the reads by `hNd` / `hmi` / `hfl` / `hnx` / `hmid` / `hSeen`, the writes
— node words, `FAULT_IP` — by `hNd` / `hfi`). -/
theorem inv_dec_genV {A : Type} {ar : machine.Arch A} {number : I64} {p : localinv.Plan}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hmi : R (regA (L.curW s) layout.reg.MSG_INFO))
    (hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hnx : R (regA (L.curW s) layout.reg.NEXT_IP)) (hfi : W (regA (L.curW s) layout.reg.FAULT_IP))
    {a : A} (hmid : ∀ nx s1 s2 a1, obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) → ∃ C sl, IoMidR (L := L) R s2 (L.curW s) C sl)
    (hSeen : ∀ x, SeenW p x → R x)
    {r : Bool × S × A} (h : syscall.handle_invocation_local st ar s a number p = ok r) (hr : r.1 ≠ true) :
    syscall.handle_invocation_local gS ar s a number p = ok r := by
  rw [handle_invocation_local_eq] at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := gS) s
    (hNd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [msg.msg_info.guard (gS := gS) s _ hmi]
  refine tr_bind_same (fun info _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard (gS := gS) (L.curW s) s hfl]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ ht => ?_)
  exact invTail.guardR (gS := gS) ar hNd hnx hfi hmid
    (fun x => still_holds_congr p x (fun w hw => GRd.read (hSeen w hw) x)) hr ht

end decV

section accV
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- (p3mc gen 27) **The accepted run on a store `gS` reading `R` and writing `W` ends as on `st`** (`inv_acc_genR`
with the entry's access facts `Ent`, the prefix reads, the entry `IoMid` (`hMid`), the seen and invoked-slot words
over `R` given). -/
theorem inv_acc_genV {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {s s' : S} {a a' : A} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R]
    [GWr gS st W] (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hW : IoWr st W Z s)
    (Ent : IoEnt st T Cs Ω H Sg Rp Scs Nt Z Ac R W s)
    (hmi : R (regA (L.curW s) layout.reg.MSG_INFO))
    (hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hnx : R (regA (L.curW s) layout.reg.NEXT_IP))
    (hMid : ∀ C, (∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r) →
      WalkCl (st := st) s C → (∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots) →
      L.mem s (scA (L.curW s)) = L.cscW s → ∀ info, msg.msg_info st s (L.curW s) = ok info →
      IoMid (L := L) R W s s (L.curW s) info (L.mem s (regA (L.curW s) layout.reg.CAP)) C (L.curW s))
    (hSeen : ∀ x, SeenW p x → R x)
    (hps : R p.slot ∧ R (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ info nx s1 s2 a1 buf length cap, msg.msg_info st s (L.curW s) = ok info →
      InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
        obj.Slot.cap st p.slot s2 = ok cap →
      ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
        syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
        ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
          invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧ z.2.2 = core.result.Result.Ok () ∧
          FinOK (L := L) gS R W ar s z.1 z.2.1)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local gS ar s a number p = ok (true, s', a') := by
  obtain ⟨info, -, -, -, ht⟩ := handle_inv_inv h
  obtain ⟨nx0, s10, s20, a10, -, -, es10, eu0, -, -, -, hh0, -⟩ := invTail_inv ht
  have hsc2 := (here_facts hh0).sc
  have w := prefix_writes ar hA P.tp P.np P.cT es10 eu0
  have e1 : L.mem s20 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (field_aligned P.tA (by simp) (by simp)) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s := (P.hcsc (by rw [← e1]; exact hsc2)).symm
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  refine syscall.handle_invocation_local.guard_acc2 (gS := gS) ar Ent.acc.nd hmi hfl hnx
    (hW.reg _ (by simp [layout.reg.FAULT_IP]))
    ?_ (fun x => still_holds_congr p x (fun w hw => GRd.read (hSeen w hw) x)) hps hblk h
  intro info nx s1 s2 a1 emi enx es1 eu
  have M2 := io_hmid' (a := a) ar hA hq.tcbs (hq.nodes _ hq.cur) hq.cur hq.curT
    (hMid C hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2) (hd hX.cur)
    (fun h0 => ⟨(bxi_rh P.bxi h0).1, hd (bxi_rh P.bxi h0).2.1⟩) info nx _ s2 a1 emi enx es1 eu
  exact ⟨M2.k, M2.c, M2.cur, M2.yld, M2.rh, M2.td, M2.rs, M2.dt, M2.cd, M2.af, M2.dom, M2.iok.1.sc, M2.iok.1.inq,
    M2.iok.1.ib, M2.iok.1.bs⟩

end accV

end Fl4Proofs.P2.PathObl

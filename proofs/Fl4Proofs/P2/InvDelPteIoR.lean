/-
# P2 (line invj, generation 7): the entry facts on a read set without the leaf entries (`IoRSR`)

The `acc` chain of the frame-cap invocation path (`inv_acc_gen2`, `delFin`, `truncAcc8`, `truncFin8`) states its
read facts for `IoRS s`, which holds every region-`.none` word, the leaf page-table entries included; under pte's
rule 8 (`ownP`) an unlocked leaf may not be read. Every word those facts name is a node, TCB-field, register, SC,
capability-slot or kernel-global (`ksb + o`, `o < 13568`) word. So the facts are restated for

* **`IoRSR K Locks s x`** := `IoRS … x ∧ (region K x ≠ .none ∨ x` a kernel-global word`)`;
* the `IoPre` lemmas behind them for `IoRSR` (`IoPre.ndR`, `homeR`, `gateR`, `regR`, `stwR`, `scaccR`,
  `cscaccR`, `slotR`, `kswR`, `tdR`, `rsR`, `lockSlotR`, `iaccR`, **`entR`**, **`midR`**): each is the `IoRS`
  lemma plus the word's region (`IoLay`: `node`, `tcbw`, `scw`, `slotw`);
* `FinOK.mono`, `InvMid.mono` (both are positive in the read set);
* **`ioRSR_P`** (namespace `E2EP`): an `IoRSR` word is an `IoRSP` word — a leaf entry is region `.none`
  (`RegionOKP.none`) and no kernel-global word (`KsNoE`, from pte's convention by `ptesR_ks`).

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region GateField TimerField TcbSlot NullOrFrame)

section ior
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop}

variable (st) in
/-- **`IoRS` at the words of a region other than `.none`, or the kernel-global words** (module docstring). -/
def IoRSR (K : KLayout) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  IoRS (st := st) K Locks s x ∧
    (region K x ≠ .none ∨ ∃ o : U64, o.val < 13568 ∧ x = core.num.U64.wrapping_add K.ksb o)

theorem IoRSR.io {x : U64} (h : IoRSR st K Locks s x) : IoRS (st := st) K Locks s x := h.1

theorem ioRSR_of {x : U64} (h : IoRS (st := st) K Locks s x) (hr : region K x ≠ .none) : IoRSR st K Locks s x :=
  ⟨h, Or.inl hr⟩

section pre
variable (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
include P

theorem IoPre.ndR (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    IoRSR st K Locks s (L.nodeAt s (L.cpu s) o) ∧ IoWS (st := st) K Locks s (L.nodeAt s (L.cpu s) o) :=
  ⟨ioRSR_of (P.nd o ho h8).1 (by rw [P.lay.node _ _ (P.inNode o ho)]; simp), (P.nd o ho h8).2⟩

theorem IoPre.homeR {off : U64} (h1 : 192 ≤ off.val) (h2 : off.val < 4096) (h8 : off.val % 8 = 0)
    (hg : ¬ GateField off.val) (htm : ¬ TimerField off.val) :
    IoRSR st K Locks s (fld (L.curW s) off) ∧ IoWS (st := st) K Locks s (fld (L.curW s) off) :=
  ⟨ioRSR_of (P.home h1 h2 h8 hg htm).1 (by rw [P.lay.tcbw _ (P.hT _ P.cT) off h1 h2]; simp),
    (P.home h1 h2 h8 hg htm).2⟩

theorem IoPre.gateR {t off : U64} (ht : t ∈ T) (h1 : 192 ≤ off.val) (h2 : off.val < 4096) (h8 : off.val % 8 = 0)
    (hg : GateField off.val) : IoRSR st K Locks s (fld t off) :=
  ioRSR_of (P.gate ht h1 h2 h8 hg) (by rw [P.lay.tcbw _ (P.hT _ ht) off h1 h2]; simp)

theorem IoPre.regR {r : U64} (hr : r.val < 384) :
    IoRSR st K Locks s (regA (L.curW s) r) ∧ IoWS (st := st) K Locks s (regA (L.curW s) r) := by
  obtain ⟨k, hk, e⟩ := regA_eq P.tA hr
  rw [e]
  refine P.homeR (off := k) (by omega) (by omega) (by omega) ?_ ?_
  · unfold GateField; omega
  · unfold TimerField; omega

theorem IoPre.stwR : IoRSR st K Locks s (stA (L.curW s)) ∧ IoWS (st := st) K Locks s (stA (L.curW s)) := by
  refine P.homeR (off := layout.tcb.STATE) ?_ ?_ ?_ ?_ ?_ <;> rw [st_val] <;> simp [GateField, TimerField]

theorem IoPre.scaccR {c : U64} (hc : c ∈ Scs) (hcore : L.mem s (scCoreA c) = L.cpu s) :
    ScAcc (IoRSR st K Locks s) (IoWS (st := st) K Locks s) c (Z c) := by
  have A := P.scacc (Locks := Locks) hc hcore
  have hh := P.hSc _ hc
  exact ⟨fun b ha hb => ioRSR_of (A.rd b ha hb) (by rw [P.lay.scw _ _ hh b hb]; simp), A.wr, A.cons⟩

theorem IoPre.cscaccR : ScAcc (IoRSR st K Locks s) (IoWS (st := st) K Locks s) (L.cscW s) (Z (L.cscW s)) :=
  P.scaccR P.cscS P.cscCore

theorem IoPre.slotR {sl : U64} (h : sl ∈ K.slots) (hg : TcbSlot K sl ∨ ¬ NullOrFrame (L.mem s sl)) :
    IoRSR st K Locks s sl ∧ IoRSR st K Locks s (core.num.U64.wrapping_add sl 8#u64) := by
  obtain ⟨h8, hf⟩ := P.lay.slot8 sl h
  have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have A := P.slot (Locks := Locks) h hg
  refine ⟨ioRSR_of A.1 ?_, ioRSR_of A.2 ?_⟩
  · rw [P.lay.slotw sl h sl ⟨le_refl _, by omega⟩]; simp
  · rw [P.lay.slotw sl h _ ⟨by omega, by omega⟩]; simp

theorem IoPre.kswR {o : U64} (ho : o.val < 256) (h8 : o.val % 8 = 0) :
    IoRSR st K Locks s (core.num.U64.wrapping_add (L.ksb s) o) :=
  ⟨P.ksw ho h8, Or.inr ⟨o, by omega, by rw [P.kb]⟩⟩

theorem IoPre.tdR (h0 : L.mem s (tmA (L := L) s) ≠ 0#u64) :
    IoRSR st K Locks s (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64) := by
  refine ioRSR_of (P.td h0) ?_
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hT := (hX.tm.min _ hq.cur).resolve_left h0
  have := P.lay.tcbw _ (P.hT _ hT) 3528#u64 (by simp) (by simp)
  unfold fld at this; rw [this]; simp

theorem IoPre.rsR (h0 : L.mem s (rhA (L := L) s) ≠ 0#u64) :
    IoRSR st K Locks s (scA (L.mem s (rhA (L := L) s))) ∧
      RdHead (L := L) (IoRSR st K Locks s) s (L.mem s (scA (L.mem s (rhA (L := L) s)))) := by
  obtain ⟨hT, hsc, ha⟩ := bxi_rh P.bxi h0
  obtain ⟨hW, -⟩ := bxi_scin P.bxi hsc ha
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hrel := hq.release _ hq.cur
  have hd : L.mem s (rhA (L := L) s) = (Rq (L.cpu s)).headD 0#u64 := hrel.head
  have hm : L.mem s (rhA (L := L) s) ∈ Rq (L.cpu s) := by
    cases hl : Rq (L.cpu s) with
    | nil => rw [hl] at hd; exact absurd hd h0
    | cons r rs => rw [hl] at hd; rw [hd]; simp
  have haff := hq.inR _ hq.cur _ hm
  have hne := hb.r _ hT ((hq.released _ hT).2 (by rw [haff]; exact hm))
  exact ⟨P.gateR (off := 3464#u64) hT (by simp) (by simp) (by simp) (by simp [GateField]),
    (P.scaccR hsc ((P.affSc _ hT hne).trans haff)).head hW⟩

theorem IoPre.lockSlotR {p o : U64} (hp : p ∈ K.slots) (hl : Locks s p) (ho : o.val < 32) (h8 : o.val % 8 = 0) :
    IoRSR st K Locks s (core.num.U64.wrapping_add p o) := by
  obtain ⟨p8, pf⟩ := P.lay.slot8 p hp
  have hv := slot_word_val pf ho
  have hin : InW p 32 (core.num.U64.wrapping_add p o) := ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  exact ioRSR_of (P.lockSlot hp hl ho h8).1 (by rw [P.lay.slotw p hp _ hin]; simp)

theorem IoPre.iaccR {W : U64 → Prop} (hW : IoWr st W Z s) :
    IoAcc st (IoRSR st K Locks s) W s (L.cscW s) (Z (L.cscW s)) where
  acc := ⟨(P.cscaccR (Locks := Locks)).rd, hW.ring, hW.cons⟩
  nd := fun o h1 h2 => ⟨(P.ndR (Locks := Locks) o h1 h2).1, hW.nd o h1 h2⟩
  sc := P.gateR (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  dt := P.kswR (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  td := P.tdR
  rs := P.rsR
  ryl := (P.homeR (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  rst := P.stwR.1
  rfi := (P.regR (by simp [layout.reg.FAULT_IP])).1
  wnx := hW.reg _ (by simp [layout.reg.NEXT_IP])
  rin := (P.homeR (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1

theorem IoPre.entR {W : U64 → Prop} (hW : IoWr st W Z s) :
    IoEnt st T Cs Ω H Sg Rp Scs Nt Z Ac (IoRSR st K Locks s) W s :=
  ⟨P.bxi, P.csc, P.hcsc, P.run, P.iaccR hW⟩

/-- **`IoMid` at the entry for `IoRSR`** (`IoPre.mid` with the region-tagged lemmas). -/
theorem IoPre.midR {W : U64 → Prop} (hW : IoWr st W Z s) {C : U64 → U64 → Prop}
    (hroot : ∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r) (hcl : WalkCl (st := st) s C)
    (hsl : ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots)
    (hsc0 : L.mem s (scA (L.curW s)) = L.cscW s)
    (info : msginfo.MessageInfo) (emi : msg.msg_info st s (L.curW s) = ok info) :
    IoMid (L := L) (IoRSR st K Locks s) W s s (L.curW s) info
      (L.mem s (regA (L.curW s) layout.reg.CAP)) C (L.curW s) := by
  have hslot : ∀ i sl, obj.Tcb.slot (L.curW s) i = ok sl → i.val < 6 →
      IoRSR st K Locks s sl ∧ IoRSR st K Locks s (core.num.U64.wrapping_add sl 8#u64) := fun i sl h hi => by
    obtain ⟨h1, h2⟩ := P.lay.tslot _ (P.hT _ P.cT) i sl h hi
    exact P.slotR h1 (Or.inl h2)
  have h0 := hslot _ _ (tcb_slot_ctable (L.curW s)) (by simp [layout.tcb.SLOT_CTABLE])
  have nd1 := P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have nd2 := P.ndR (Locks := Locks) layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have hO := P.bxi.2.2.1.1
  have hmx := maxA_facts hO P.cscS
  exact
  { k := rfl, c := rfl, cur := rfl, mi := emi
    rmi := (P.regR (by simp [layout.reg.MSG_INFO])).1
    r10 := (P.regR (by simp [layout.reg.R10])).1
    cap := (P.regR (by simp [layout.reg.CAP])).1
    yld := (P.homeR (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
    hsl := tcb_slot_ctable _
    hR0 := h0.1, hR8 := h0.2
    hRc := fun p r m y p' r' gs' g' hp hm hc =>
      P.slotR (hsl p r m y hp hm) (Or.inr (cap_not_nof hc (Or.inl ⟨_, _, _, _, rfl⟩)))
    hcl := hcl
    hroot := hroot
    hRf := fun x f l z hx hc => P.slotR (P.fin x hx).1 (Or.inr (cap_not_nof hc (Or.inr ⟨_, _, _, rfl⟩)))
    rh := P.cscaccR.head P.cscwf
    td := P.tdR
    rs := P.rsR
    dt := P.kswR (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
    cd := P.kswR (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
    af := P.gateR (off := 3520#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
    dom := P.gateR (off := 3432#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
    iok := ⟨
      { tcb := P.tA
        regR := fun r hr => (P.regR hr).1
        regW := fun r hr => hW.reg r hr
        stR := P.stwR.1
        sc := P.gateR (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
        max := by rw [hsc0]; exact P.cscaccR.rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩
        inq := (P.homeR (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
        ib := P.gateR (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
        bs := fun sl h => hslot _ sl h (by simp [layout.tcb.SLOT_BUFFER]) },
      ⟨nd1.1, nd2.1, hW.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])⟩,
      nodeAt_aligned P.np (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]),
      node_ne_field P.np (by simp [layout.node.SCHED_ACTION]) P.cT P.tA (by simp)⟩ }

end pre

end ior

section mono
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R R' W : U64 → Prop}

/-- `FinOK` for a larger read set. -/
theorem FinOK.mono {A : Type} {gS : machine.Store S} {ar : machine.Arch A} {s s3 : S} {a3 : A}
    (h : ∀ x, R x → R' x) (F : FinOK (L := L) gS R W ar s s3 a3) : FinOK (L := L) gS R' W ar s s3 a3 :=
  ⟨F.k, F.c, F.nd, fun h0 => h _ (F.td h0), fun h0 => ⟨h _ (F.rs h0).1, ⟨h _ (F.rs h0).2.1, h _ (F.rs h0).2.2.1, h _ (F.rs h0).2.2.2⟩⟩, F.ha, F.hsw, F.hfr,
    F.hact, fun s1 a1 s2 a2 e1 e2 => ⟨h _ (F.hvc s1 a1 s2 a2 e1 e2).1, h _ (F.hvc s1 a1 s2 a2 e1 e2).2.1,
      (F.hvc s1 a1 s2 a2 e1 e2).2.2⟩⟩

end mono

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.OwnMap (KLayout region)
open Fl4Proofs.P2.E2EV (KsNoE)

section conv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutP} {Locks : S → U64 → Prop} {s : S}

/-- **An `IoRSR` word is an `IoRSP` word**: no leaf entry is of a region other than `.none` (`RegionOKP.none`) or a
kernel-global word (`KsNoE`). -/
theorem ioRSR_P (hK : RegionOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) {x : U64}
    (h : IoRSR st K.toKLayout Locks s x) : IoRSP st K Locks s x := by
  refine ⟨h.1, fun hx => absurd hx ?_⟩
  rcases h.2 with hr | ⟨o, ho, rfl⟩
  · exact fun hx => hr (hK.none _ hx)
  · exact hks o ho

/-- `KsNoE` from pte's convention. -/
theorem ksNoE_conv {m : U64 → U64} (hc : K.ptes = ptesR K m) : KsNoE (· ∈ K.ptes) K.toKLayoutV := by
  rw [hc]; exact ptesR_ks

end conv

end Fl4Proofs.P2.E2EP

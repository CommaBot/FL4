/-
# P2 (line p3mc, gen 4): the I/O port path's accepted run on a narrowed guard (`io_accN`)

`io_acc` with the read set `IoRS ∧ NN` and the write set `IoWS ∧ NW` for any two word predicates `NN`, `NW` that hold
on the objects the accepted run touches (`IoNar`): the core's node, the current thread's words from offset 192 on
(written: all but `AFFINITY`), every capability slot, the kernel-global words, the current SC (its `ScAcc`, where the
current thread has an SC), the earliest timer's `TIMER_DEADLINE`, the release head's `SC` field and its SC's words.
`AccessIoEnt.IoAcc` / `AccessIoPath.IoMid` are generic in the sets, so `io_acc`'s proof goes through with
`IoPre.iaccN` / `IoPre.midN` in place of `IoPre.iacc` / `IoPre.mid`.

No premise beyond `IoPre` and `IoNar`. No existing statement changed.
-/
import Fl4Proofs.P2.AccessIoOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region GateField TimerField GField tcbOwner TcbSlot NullOrFrame)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- **The words the I/O port path touches, in `NN` (read) and `NW` (written)** (module docstring). -/
structure IoNar (K : KLayout) (Z : U64 → Nat) (NN NW : U64 → Prop) (s : S) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → NN (L.nodeAt s (L.cpu s) o) ∧ NW (L.nodeAt s (L.cpu s) o)
  cur : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → NN (core.num.U64.wrapping_add (L.curW s) off)
  curW : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val ≠ 3520 →
    NW (core.num.U64.wrapping_add (L.curW s) off)
  slot : ∀ sl ∈ K.slots, NN sl ∧ NN (core.num.U64.wrapping_add sl 8#u64)
  ks : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → NN (core.num.U64.wrapping_add (L.ksb s) o)
  csc : L.mem s (scA (L.curW s)) ≠ 0#u64 → ScAcc NN NW (L.cscW s) (Z (L.cscW s))
  td : L.mem s (tmA (L := L) s) ≠ 0#u64 → NN (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64)
  rs : L.mem s (rhA (L := L) s) ≠ 0#u64 → NN (scA (L.mem s (rhA (L := L) s))) ∧
    ∀ b, Aligned b → InSC (L.mem s (scA (L.mem s (rhA (L := L) s))))
      (Z (L.mem s (scA (L.mem s (rhA (L := L) s))))) b → NN b

theorem IoNar.reg {NN NW : U64 → Prop} (N : IoNar (L := L) K Z NN NW s) (hT : TcbAddr (L.curW s)) {r : U64} (hr : r.val < 384) :
    NN (regA (L.curW s) r) ∧ NW (regA (L.curW s) r) := by
  obtain ⟨o, ho, e⟩ := regA_eq hT hr
  rw [e]
  exact ⟨N.cur o (by omega) (by omega), N.curW o (by omega) (by omega) (by omega)⟩

section
variable (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
include P

/-- The release head's SC words in `NN ∧ IoRS`, as `RdHead`. -/
theorem IoPre.rsN {NN NW : U64 → Prop} (N : IoNar (L := L) K Z NN NW s) (h0 : L.mem s (rhA (L := L) s) ≠ 0#u64) :
    (IoRS (st := st) K Locks s (scA (L.mem s (rhA (L := L) s))) ∧ NN (scA (L.mem s (rhA (L := L) s)))) ∧
      RdHead (L := L) (fun b => IoRS (st := st) K Locks s b ∧ NN b) s
        (L.mem s (scA (L.mem s (rhA (L := L) s)))) := by
  obtain ⟨r1, r2⟩ := P.rs (Locks := Locks) h0
  obtain ⟨n1, n2⟩ := N.rs h0
  obtain ⟨-, hsc, ha⟩ := bxi_rh P.bxi h0
  obtain ⟨hW, -⟩ := bxi_scin P.bxi hsc ha
  have hA : ScAcc NN (fun _ => True) (L.mem s (scA (L.mem s (rhA (L := L) s))))
      (Z (L.mem s (scA (L.mem s (rhA (L := L) s))))) :=
    ⟨fun b hb hi => n2 b hb hi, fun _ _ _ => trivial, trivial⟩
  obtain ⟨h1, h2, h3⟩ := hA.head hW
  exact ⟨⟨r1, n1⟩, ⟨r2.1, h1⟩, ⟨r2.2.1, h2⟩, ⟨r2.2.2, h3⟩⟩

theorem IoPre.cscaccN {NN NW : U64 → Prop} (N : IoNar (L := L) K Z NN NW s) (hsc : L.mem s (scA (L.curW s)) ≠ 0#u64) :
    ScAcc (fun b => IoRS (st := st) K Locks s b ∧ NN b) (fun b => IoWS (st := st) K Locks s b ∧ NW b)
      (L.cscW s) (Z (L.cscW s)) :=
  ⟨fun b ha hb => ⟨(P.cscacc (Locks := Locks)).rd b ha hb, (N.csc hsc).rd b ha hb⟩,
    fun b ha hb => ⟨(P.cscacc (Locks := Locks)).wr b ha hb, (N.csc hsc).wr b ha hb⟩,
    ⟨(P.cscacc (Locks := Locks)).cons, (N.csc hsc).cons⟩⟩

theorem IoPre.ioWrN {NN NW : U64 → Prop} (N : IoNar (L := L) K Z NN NW s) (hsc : L.mem s (scA (L.curW s)) ≠ 0#u64) :
    IoWr st (fun b => IoWS (st := st) K Locks s b ∧ NW b) Z s :=
  ⟨fun o h1 h2 => ⟨(P.nd o h1 h2).2, (N.nd o h1 h2).2⟩, fun r hr => ⟨(P.reg hr).2, (N.reg P.tA hr).2⟩,
    (P.cscaccN N hsc).wr, (P.cscaccN N hsc).cons⟩

theorem IoPre.iaccN {NN NW : U64 → Prop} (N : IoNar (L := L) K Z NN NW s) (hsc : L.mem s (scA (L.curW s)) ≠ 0#u64) :
    IoAcc st (fun b => IoRS (st := st) K Locks s b ∧ NN b) (fun b => IoWS (st := st) K Locks s b ∧ NW b) s
      (L.cscW s) (Z (L.cscW s)) where
  acc := P.cscaccN N hsc
  nd := fun o h1 h2 => ⟨⟨(P.nd (Locks := Locks) o h1 h2).1, (N.nd o h1 h2).1⟩,
    ⟨(P.nd (Locks := Locks) o h1 h2).2, (N.nd o h1 h2).2⟩⟩
  sc := ⟨P.gate (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]),
    N.cur 3464#u64 (by simp) (by simp)⟩
  dt := ⟨P.ksw (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]),
    N.ks _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])⟩
  td := fun h0 => ⟨P.td h0, N.td h0⟩
  rs := fun h0 => ⟨(P.rsN N h0).1, (P.rsN N h0).2⟩
  ryl := ⟨(P.home (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1,
    N.cur 3472#u64 (by simp) (by simp)⟩
  rst := ⟨P.stw.1, N.cur layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)⟩
  rfi := ⟨(P.reg (by simp [layout.reg.FAULT_IP])).1, (N.reg P.tA (by simp [layout.reg.FAULT_IP])).1⟩
  wnx := ⟨(P.reg (by simp [layout.reg.NEXT_IP])).2, (N.reg P.tA (by simp [layout.reg.NEXT_IP])).2⟩
  rin := ⟨(P.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1,
    N.cur 3592#u64 (by simp) (by simp)⟩

theorem IoPre.entN {NN NW : U64 → Prop} (N : IoNar (L := L) K Z NN NW s) (hsc : L.mem s (scA (L.curW s)) ≠ 0#u64) :
    IoEnt st T Cs Ω H Sg Rp Scs Nt Z Ac (fun b => IoRS (st := st) K Locks s b ∧ NN b)
      (fun b => IoWS (st := st) K Locks s b ∧ NW b) s :=
  ⟨P.bxi, P.csc, P.hcsc, P.run, P.iaccN N hsc⟩

/-- **`IoMid` at the entry, narrowed.** -/
theorem IoPre.midN {NN NW : U64 → Prop} (N : IoNar (L := L) K Z NN NW s) {C : U64 → U64 → Prop}
    (hroot : ∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r) (hcl : WalkCl (st := st) s C)
    (hsl : ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots)
    (hsc0 : L.mem s (scA (L.curW s)) = L.cscW s) (hsc : L.mem s (scA (L.curW s)) ≠ 0#u64)
    (info : msginfo.MessageInfo) (emi : msg.msg_info st s (L.curW s) = ok info) :
    IoMid (L := L) (fun b => IoRS (st := st) K Locks s b ∧ NN b) (fun b => IoWS (st := st) K Locks s b ∧ NW b) s s
      (L.curW s) info (L.mem s (regA (L.curW s) layout.reg.CAP)) C (L.curW s) := by
  have M := P.mid (Locks := Locks) (P.ioWrN (Locks := Locks) N hsc) hroot hcl hsl hsc0 info emi
  have hslot : ∀ i sl, obj.Tcb.slot (L.curW s) i = ok sl → i.val < 6 →
      NN sl ∧ NN (core.num.U64.wrapping_add sl 8#u64) := fun i sl h hi =>
    N.slot _ (P.lay.tslot _ (P.hT _ P.cT) i sl h hi).1
  have h0 := hslot _ _ (tcb_slot_ctable (L.curW s)) (by simp [layout.tcb.SLOT_CTABLE])
  have hO := P.bxi.2.2.1.1
  have hmx := maxA_facts hO P.cscS
  have rhN : RdHead (L := L) (fun b => IoRS (st := st) K Locks s b ∧ NN b) s (L.cscW s) :=
    (P.cscaccN N hsc).head P.cscwf
  obtain ⟨iR, iN, iA⟩ := M.iok
  exact
  { k := rfl, c := rfl, cur := rfl, mi := emi
    rmi := ⟨M.rmi, (N.reg P.tA (by simp [layout.reg.MSG_INFO])).1⟩
    r10 := ⟨M.r10, (N.reg P.tA (by simp [layout.reg.R10])).1⟩
    cap := ⟨M.cap, (N.reg P.tA (by simp [layout.reg.CAP])).1⟩
    yld := ⟨M.yld, N.cur 3472#u64 (by simp) (by simp)⟩
    hsl := tcb_slot_ctable _
    hR0 := ⟨M.hR0, h0.1⟩, hR8 := ⟨M.hR8, h0.2⟩
    hRc := fun p r m y p' r' gs' g' hp hm hc =>
      ⟨⟨(M.hRc p r m y p' r' gs' g' hp hm hc).1, (N.slot _ (hsl p r m y hp hm)).1⟩,
        ⟨(M.hRc p r m y p' r' gs' g' hp hm hc).2, (N.slot _ (hsl p r m y hp hm)).2⟩⟩
    hcl := hcl
    hroot := hroot
    hRf := fun x f l z hx hc => ⟨⟨(M.hRf x f l z hx hc).1, (N.slot _ (P.fin x hx).1).1⟩,
      ⟨(M.hRf x f l z hx hc).2, (N.slot _ (P.fin x hx).1).2⟩⟩
    rh := rhN
    td := fun h0 => ⟨M.td h0, N.td h0⟩
    rs := fun h0 => ⟨(P.rsN N h0).1, (P.rsN N h0).2⟩
    dt := ⟨M.dt, N.ks _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])⟩
    cd := ⟨M.cd, N.ks _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])⟩
    af := ⟨M.af, N.cur 3520#u64 (by simp) (by simp)⟩
    dom := ⟨M.dom, N.cur 3432#u64 (by simp) (by simp)⟩
    iok := ⟨
      { tcb := iR.tcb
        regR := fun r hr => ⟨iR.regR r hr, (N.reg P.tA hr).1⟩
        regW := fun r hr => iR.regW r hr
        stR := ⟨iR.stR, N.cur layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)⟩
        sc := ⟨iR.sc, N.cur 3464#u64 (by simp) (by simp)⟩
        max := ⟨iR.max, by rw [hsc0]; exact (N.csc hsc).rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩⟩
        inq := ⟨iR.inq, N.cur 3592#u64 (by simp) (by simp)⟩
        ib := ⟨iR.ib, N.cur 3512#u64 (by simp) (by simp)⟩
        bs := fun sl h => ⟨⟨(iR.bs sl h).1, (hslot _ sl h (by simp [layout.tcb.SLOT_BUFFER])).1⟩,
          ⟨(iR.bs sl h).2, (hslot _ sl h (by simp [layout.tcb.SLOT_BUFFER])).2⟩⟩ },
      ⟨⟨iN.1, (N.nd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1⟩,
        ⟨iN.2.1, (N.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1⟩,
        iN.2.2⟩, iA⟩ }

end

/-- **`io_acc` on the narrowed guard** (module docstring). -/
theorem io_accN {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {s' : S} {a a' : A}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {NN NW : U64 → Prop} (N : IoNar (L := L) K Z NN NW s)
    (h : syscall.handle_ioport_local st ar s a number = ok (true, s', a')) :
    syscall.handle_ioport_local (PathObl.guard st (fun b => IoRS (st := st) K Locks s b ∧ NN b)
      (fun b => IoWS (st := st) K Locks s b ∧ NW b)) ar s a number = ok (true, s', a') := by
  obtain ⟨info, -, -, -, ht⟩ := handle_ioport_inv h
  obtain ⟨nx, s1, s2, a1, -, -, hs1, hu, -, -, -, -, -, hh⟩ := ioTail_inv ht
  have hsc2 := (here_facts hh).sc
  have w := prefix_writes ar hA P.tp P.np P.cT hs1 hu
  have e1 : L.mem s2 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (field_aligned P.tA (by simp) (by simp)) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc : L.mem s (scA (L.curW s)) ≠ 0#u64 := by rw [← e1]; exact hsc2
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s := (P.hcsc hsc).symm
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  exact syscall.handle_ioport_local.guard_ent ar hA (P.entN (Locks := Locks) N hsc)
    (P.midN (Locks := Locks) N hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0 hsc)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2)
    ⟨(P.reg (by simp [layout.reg.MSG_INFO])).1, (N.reg P.tA (by simp [layout.reg.MSG_INFO])).1⟩
    ⟨(P.home (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1,
      N.cur 3456#u64 (by simp) (by simp)⟩
    ⟨(P.reg (by simp [layout.reg.NEXT_IP])).1, (N.reg P.tA (by simp [layout.reg.NEXT_IP])).1⟩
    ⟨(P.reg (by simp [layout.reg.FAULT_IP])).2, (N.reg P.tA (by simp [layout.reg.FAULT_IP])).2⟩
    (IoSW.of_W ⟨P.stw.2, N.curW layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)
      (by rw [st_val]; omega)⟩) h

end

end Fl4Proofs.P2.PathObl

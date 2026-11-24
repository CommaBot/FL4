/-
# P2: the I/O port path's `IoMid` across the prefix (line p2io)

`syscall.handle_ioport_local.guard_acc` (`P2/AccessIoPath.lean`) asks for
`IoMid` at the post-prefix state `s2` (after the `FAULT_IP` write and
`update_timestamp`). Here it is reduced to `IoMid` at the entry state `s`
itself (`IoMid R W s s …`) and the placement of the words the post-prefix
steps read through the state:

* `prefix_writes`: the prefix writes only `PreW s t` (the current thread's
  `FAULT_IP`, this core's `CUR_TIME`, `CONSUMED`);
* `pre_node`: a node word other than those two is kept;
* `lookup_slot_back`: `lookup_slot` at a state agreeing on the CTable root
  slot and on the radix-masked slots of a closed CNode set answers as at `s`
  (P1's `rab_loop_congr2`);
* `IoMid.of_entry`: `IoMid` moves from `s` to any `s2` agreeing on the words
  it reads through the state (named equalities);
* `io_hmid`: `guard_acc`'s `hmid` from `IoMid` at the entry, P1's placement
  (`TcbPlaced`, `NodePlaced`, the current thread in `T`), the walk's slots
  outside the TCBs and nodes (P1's `CnOff` shape), and the two SC head words
  outside them (`OutsideObjs`).

Premises: none (the hypotheses are entry facts, discharged in the I/O port
obligation).
-/
import Fl4Proofs.P2.AccessIoPath
import Fl4Proofs.P2.FootVm
import Fl4Proofs.P1.LocalTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]

/-- The prefix's words: `t`'s `FAULT_IP` (offset 392), this core's
`CUR_TIME`, `CONSUMED`. -/
def PreW (s : S) (t b : U64) : Prop :=
  (∃ K : U64, K.val = 392 ∧ b = core.num.U64.wrapping_add t K) ∨ b = ctA (L := L) s ∨ b = cnA (L := L) s

/-- **The prefix writes only `PreW`.** -/
theorem prefix_writes {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) {T : Set U64} {s s1 s2 : S}
    {a a2 : A} {v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (es1 : obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP v = ok s1)
    (eu : sched.update_timestamp st ar s1 a = ok (s2, a2)) :
    WritesIn st s s2 (PreW (L := L) s (L.curW s)) := by
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s (L.curW s) layout.reg.FAULT_IP v (hT _ hcT)
    (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨K, hK, e1⟩ := hW1
  have hK' : K.val = 392 := by rw [hK]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (core.num.U64.wrapping_add (L.curW s) K) := field_aligned (hT _ hcT) (by omega) (by omega)
  obtain ⟨⟨n, a1⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  rw [update_timestamp_ok ar hN1 hn] at eu
  obtain ⟨rfl, -⟩ := Prod.mk.inj (ok_inj_ff eu)
  have w1 : WritesIn st s s1 (PreW (L := L) s (L.curW s)) := by
    rw [e1]; exact (writesIn_wr aF).mono fun b e => Or.inl ⟨K, hK', e⟩
  have ec : ctA (L := L) s1 = ctA (L := L) s := by rw [e1, ctA_wr]
  have en : cnA (L := L) s1 = cnA (L := L) s := by rw [e1, cnA_wr]
  refine (w1.trans (utW_writes hN1 n)).mono fun b hb => hb.elim id fun hb => ?_
  rw [ec, en] at hb
  exact Or.inr hb

/-- A node word other than `CUR_TIME` / `CONSUMED` is kept by the prefix. -/
theorem pre_node {T : Set U64} {s s2 : S} {t o : U64} (w : WritesIn st s s2 (PreW (L := L) s t))
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (ht : t ∈ T)
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h1 : o.val ≠ layout.node.CUR_TIME.val)
    (h2 : o.val ≠ layout.node.CONSUMED.val) :
    L.mem s2 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
  refine w.2.2 _ (nodeAt_aligned hN ho h8) ?_
  rintro (⟨K, hK, e⟩ | e | e)
  · exact tcb_node_ne hN ht (hT t ht) (by omega) ho e.symm
  · exact nodeAt_ne hN ho (by simp [layout.node.CUR_TIME]) h1 e
  · exact nodeAt_ne hN ho (by simp [layout.node.CONSUMED]) h2 e

/-- A word outside the TCBs and this core's node is kept by the prefix. -/
theorem pre_out {T Cs : Set U64} {s s2 : S} {t b : U64} (w : WritesIn st s s2 (PreW (L := L) s t))
    (hN : NodePlaced st T s (L.cpu s)) (hcC : L.cpu s ∈ Cs) (ht : t ∈ T) (hT : TcbPlaced T)
    (hb : OutsideObjs st T Cs s b) : L.mem s2 b = L.mem s b := by
  refine w.2.2 _ hb.1 ?_
  have hnb := hb.2.2 _ hcC
  rintro (⟨K, hK, e⟩ | e | e)
  · have := hb.2.1 t ht
    rw [e, tcb_wadd_val (hT t ht) (by omega)] at this; omega
  · have := nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
    rw [e] at hnb; simp only [ctA] at hnb; rw [this] at hnb
    simp [layout.node.CUR_TIME] at hnb <;> omega
  · have := nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
    rw [e] at hnb; simp only [cnA] at hnb; rw [this] at hnb
    simp [layout.node.CONSUMED] at hnb <;> omega

/-- **`lookup_slot` backwards**: at `s2` agreeing with `s` on the CTable root
slot and on the radix-masked slots of a closed set `C` of the root's CNodes. -/
theorem lookup_slot_back {s s2 : S} {t cptr sl : U64} {C : U64 → U64 → Prop}
    {res : core.result.Result cspace.Resolved error.LookupFault}
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl)
    (e0 : obj.Slot.cap st sl s2 = obj.Slot.cap st sl s)
    (eC : ∀ p r m y, C p r → cspace.mask r = ok m →
      obj.Slot.cap st (cnSlot p (y &&& m)) s2 = obj.Slot.cap st (cnSlot p (y &&& m)) s)
    (hcl : WalkCl (st := st) s C) (hroot : ∀ p r gs g, obj.Slot.cap st sl s = ok (.CNode p r gs g) → C p r)
    (h : cspace.lookup_slot st s2 t cptr = ok res) : cspace.lookup_slot st s t cptr = ok res := by
  unfold cspace.lookup_slot at h ⊢
  rw [hsl] at h ⊢; simp only [bind_ok] at h ⊢
  rw [e0] at h
  obtain ⟨root, er, h⟩ := bind_eq_ok h
  rw [er]; simp only [bind_ok]
  refine rab_loop_congr2 st C (fun p r hp m hm x => (eC p r m x hp hm).symm) ?_ 66 root _ 65#u64 _ (by simp)
    (fun p r gs g e => hroot p r gs g (e ▸ er)) h
  intro p r m x p' r' gs' g' hp hm hc
  rw [eC p r m x hp hm] at hc
  exact hcl p r m x p' r' gs' g' hp hm hc

/-- **`IoMid` from the entry to `s2`**, given that `s2` agrees with `s` on the
words `IoMid` reads through the state. -/
theorem IoMid.of_entry {s s2 : S} {t sl : U64} {info : msginfo.MessageInfo} {C : U64 → U64 → Prop}
    (M : IoMid (L := L) R W s s t info (L.mem s (regA t layout.reg.CAP)) C sl)
    (ek : L.ksb s2 = L.ksb s) (ec : L.cpu s2 = L.cpu s) (hcur : L.curW s2 = t)
    (emi : L.mem s2 (regA t layout.reg.MSG_INFO) = L.mem s (regA t layout.reg.MSG_INFO))
    (ecap : L.mem s2 (regA t layout.reg.CAP) = L.mem s (regA t layout.reg.CAP))
    (esl : obj.Slot.cap st sl s2 = obj.Slot.cap st sl s)
    (eC : ∀ p r m y, C p r → cspace.mask r = ok m →
      obj.Slot.cap st (cnSlot p (y &&& m)) s2 = obj.Slot.cap st (cnSlot p (y &&& m)) s)
    (ecsc : L.mem s2 (L.nodeAt s (L.cpu s) layout.node.CUR_SC) = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_SC))
    (ehd : L.mem s2 (headA (L.cscW s)) = L.mem s (headA (L.cscW s)))
    (etm : L.mem s2 (tmA (L := L) s) = L.mem s (tmA (L := L) s))
    (erl : L.mem s2 (rhA (L := L) s) = L.mem s (rhA (L := L) s))
    (erx : L.mem s (rhA (L := L) s) ≠ 0#u64 →
      L.mem s2 (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) ∧
      L.mem s2 (headA (L.mem s (scA (L.mem s (rhA (L := L) s))))) =
        L.mem s (headA (L.mem s (scA (L.mem s (rhA (L := L) s))))))
    (est : L.mem s2 (scA t) = L.mem s (scA t)) :
    IoMid (L := L) R W s s2 t info (L.mem s2 (regA t layout.reg.CAP)) C sl := by
  have nd : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [ec, nodeAt_of_ksb ek]
  have erh : ∀ sc, L.mem s2 (headA sc) = L.mem s (headA sc) → RdHead (L := L) R s sc → RdHead (L := L) R s2 sc := by
    intro sc e h; unfold RdHead LawfulStore.rhead at h ⊢; rw [e]; exact h
  have ecsc' : L.cscW s2 = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA; rw [nd]; exact ecsc
  have etm' : L.mem s2 (tmA (L := L) s2) = L.mem s (tmA (L := L) s) := by simp only [tmA, nd]; exact etm
  have erl' : L.mem s2 (rhA (L := L) s2) = L.mem s (rhA (L := L) s) := by simp only [rhA, nd]; exact erl
  have hcl2 : WalkCl (st := st) s2 C := by
    intro p r m y p' r' gs' g' hp hm hc; rw [eC p r m y hp hm] at hc; exact M.hcl p r m y p' r' gs' g' hp hm hc
  rw [ecap]
  obtain ⟨hi, hn, hd⟩ := M.iok
  exact
  { k := ek
    c := ec
    cur := hcur
    mi := by have h := M.mi; unfold msg.msg_info at h ⊢; rw [reg_ok] at h ⊢; rw [emi]; exact h
    rmi := M.rmi, r10 := M.r10, cap := M.cap, yld := M.yld, hsl := M.hsl, hR0 := M.hR0, hR8 := M.hR8
    hRc := by
      intro p r m y p' r' gs' g' hp hm hc; rw [eC p r m y hp hm] at hc; exact M.hRc p r m y p' r' gs' g' hp hm hc
    hcl := hcl2
    hroot := by intro p r gs g h; rw [esl] at h; exact M.hroot p r gs g h
    hRf := fun x h => M.hRf x (lookup_slot_back M.hsl esl eC M.hcl M.hroot h)
    rh := by rw [ecsc']; exact erh _ ehd M.rh
    td := by rw [etm']; exact M.td
    rs := by
      rw [erl']; intro h0
      obtain ⟨e1, e2⟩ := erx h0
      obtain ⟨r1, r2⟩ := M.rs h0
      rw [e1]; exact ⟨r1, erh _ e2 r2⟩
    dt := by rw [ek]; exact M.dt
    cd := by rw [ek]; exact M.cd
    af := M.af, dom := M.dom
    iok := ⟨{ hi with max := by rw [est]; exact hi.max }, by unfold NodeSt at hn ⊢; simp only [nd]; exact hn,
      by simp only [ActDisj, nd]; exact hd⟩ }


/-- **`guard_acc`'s `hmid` from the entry**: `IoMid` at the entry state for a
CNode set `C` whose radix-masked slots lie outside the TCBs and nodes (P1's
`CnOff`), the current SC's head word outside them, and the release head (if
any) a placed thread whose SC's head word lies outside them. -/
theorem io_hmid {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) {T Cs : Set U64} {s : S} {a : A}
    {C : U64 → U64 → Prop} {sl : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcC : L.cpu s ∈ Cs) (hcT : L.curW s ∈ T)
    (M : ∀ info, msg.msg_info st s (L.curW s) = ok info →
      IoMid (L := L) R W s s (L.curW s) info (L.mem s (regA (L.curW s) layout.reg.CAP)) C sl)
    (hCo : ∀ p r m y, C p r → cspace.mask r = ok m → OutsideObjs st T Cs s (cnSlot p (y &&& m)) ∧
      OutsideObjs st T Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64))
    (hhd : OutsideObjs st T Cs s (headA (L.cscW s)))
    (hrx : L.mem s (rhA (L := L) s) ≠ 0#u64 → L.mem s (rhA (L := L) s) ∈ T ∧
      OutsideObjs st T Cs s (headA (L.mem s (scA (L.mem s (rhA (L := L) s)))))) :
    ∀ info nx s1 s2 a1, msg.msg_info st s (L.curW s) = ok info →
      obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) →
      ∃ C sl, IoMid (L := L) R W s s2 (L.curW s) info (L.mem s2 (regA (L.curW s) layout.reg.CAP)) C sl := by
  intro info nx s1 s2 a1 emi _ es1 eu
  have w := prefix_writes ar hA hT hN hcT es1 eu
  obtain ⟨ecur, tK, -⟩ := inv_prefix ar hT hN hcC (cur_thread_ok s) hcT es1 eu hA
  have ht := hT _ hcT
  have M0 := M info emi
  have hcur : L.curW s2 = L.curW s := by rw [cur_thread_ok] at ecur; exact ok_inj_ff ecur
  have regK : ∀ r : U64, r.val < 384 → r.val ≠ 17 →
      L.mem s2 (regA (L.curW s) r) = L.mem s (regA (L.curW s) r) := by
    intro r hr hr'
    have e := reg_keepK (L := L) ht hr hr' tK
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have esl : obj.Slot.cap st sl s2 = obj.Slot.cap st sl s := by
    have hsl := M0.hsl
    have esl : sl = core.num.U64.wrapping_add (L.curW s)
        (core.num.U64.wrapping_mul layout.tcb.SLOT_CTABLE layout.cte.SIZE) := by
      simp only [obj.Tcb.slot, lift, bind_ok] at hsl; exact (ok_inj_ff hsl).symm
    have tf := ht.fits
    have vsl : sl.val = (L.curW s).val := by
      rw [esl]; simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
      all_goals omega
    have e0 : sl = core.num.U64.wrapping_add (L.curW s) 0#u64 := by
      apply UScalar.eq_of_val_eq; rw [vsl, tcb_wadd_val ht (by decide)]; simp
    have e8 : core.num.U64.wrapping_add sl 8#u64 = core.num.U64.wrapping_add (L.curW s) 8#u64 := by
      apply UScalar.eq_of_val_eq; rw [tcb_wadd_val ht (by decide)]
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vsl]; omega
    unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, e8, e0,
      tK 0#u64 (by decide) (by decide) (by decide), tK 8#u64 (by decide) (by decide) (by decide)]
  have eC : ∀ p r m y, C p r → cspace.mask r = ok m →
      obj.Slot.cap st (cnSlot p (y &&& m)) s2 = obj.Slot.cap st (cnSlot p (y &&& m)) s := by
    intro p r m y hp hm
    obtain ⟨h1, h2⟩ := hCo p r m y hp hm
    unfold obj.Slot.cap
    rw [L.read_pair_eq, L.read_pair_eq, pre_out w hN hcC hcT hT h1, pre_out w hN hcC hcT hT h2]
  have nk : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ layout.node.CUR_TIME.val →
      o.val ≠ layout.node.CONSUMED.val →
      L.mem s2 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o h1 h2 h3 h4 => pre_node w hT hN hcT h1 h2 h3 h4
  have est : L.mem s2 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    tK 3464#u64 (by decide) (by decide) (by decide)
  refine ⟨C, sl, ?_⟩
  refine IoMid.of_entry M0 w.1 w.2.1 hcur
    (regK _ (by simp [layout.reg.MSG_INFO]) (by simp [layout.reg.MSG_INFO]))
    (regK _ (by simp [layout.reg.CAP]) (by simp [layout.reg.CAP])) esl eC
    (nk _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC, layout.node.CUR_TIME]) (by simp [layout.node.CUR_SC, layout.node.CONSUMED]))
    (pre_out w hN hcC hcT hT hhd)
    (nk _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED]))
    (nk _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED]))
    (fun h0 => ?_) est
  obtain ⟨hxT, hxo⟩ := hrx h0
  refine ⟨?_, pre_out w hN hcC hcT hT hxo⟩
  have hx := hT _ hxT
  refine w.2.2 _ (field_aligned hx (by decide) (by decide)) ?_
  rintro (⟨K, hK, e⟩ | e | e)
  · exact tcb_word_ne hx ht (by decide) (by omega) (fun _ => by simp [hK]) e
  · exact tcb_node_ne hN hxT hx (by decide) (by simp [layout.node.CUR_TIME]) e
  · exact tcb_node_ne hN hxT hx (by decide) (by simp [layout.node.CONSUMED]) e

end

end Fl4Proofs.P2.PathObl

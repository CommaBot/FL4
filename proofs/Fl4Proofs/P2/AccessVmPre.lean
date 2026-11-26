/-
# P2: the VM paths' entry facts and their words against the ownership map (line p2e, VM paths)

The VM-fault and VM-ReplyRecv local paths (`handle_vm_fault_local`,
`handle_reply_recv_vm_local`) use the I/O port line's maximal sets `IoRS` /
`IoWS` (`P2/AccessIoOwn.lean`: the aligned kernel words a path on this core
may read / write by `OwnMap.own` at the entry state), with the locks fl4-sync
holds (`local_vm_fault`: the fault endpoint and its waiting handler's reply
object).

* `VmLay` [J]: `IoLay` and the regions of endpoints (16 bytes) and reply
  objects (32 bytes);
* `VmBase`: the entry facts both paths share (`IoPre`'s, without the CSpace
  walk);
* `VmBase.nd` / `home` / `reg` / `stw` / `gate` / `scacc` / `td` / `rs` /
  `cscacc`: as `IoPre`'s, for `VmBase`;
* `VmBase.obj`: the words of a locked endpoint or reply object;
  `VmBase.homeOf`: the home words of a thread homed on this core;
  `VmBase.link`: the queue links of a thread queued on a locked object.

Premises (fields of `VmLay`, `VmBase`), as `IoLay` / `IoPre`'s, plus
`VmLay.epw`, `VmLay.rpw` [J] (P1's typed-heap placement: an endpoint's and a
reply object's words lie in no node, slot, TCB or notification).
-/
import Fl4Proofs.P2.AccessIoOwn
import Fl4Proofs.P2.AccessVmF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region GateField TimerField GField tcbOwner TcbSlot NullOrFrame
  slotOwner treeCore)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- **Layout facts of the VM paths** [J]: `IoLay`, and the words of endpoints
and reply objects lie in their own region. -/
structure VmLay (K : KLayout) : Prop where
  io : IoLay K
  epw : ∀ p, K.heap p = some .ep → ∀ b, InW p 16 b → region K b = .obj p
  rpw : ∀ p, K.heap p = some .reply → ∀ b, InW p 32 b → region K b = .obj p

/-- **The entry facts both VM paths share** (`IoPre`'s, without the CSpace
walk; module docstring). -/
structure VmBase (st : machine.Store S) [L : LawfulStore st] (K : KLayout) (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (s : S) : Prop where
  bxi : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s
  csc : L.cscW s ∈ Ac
  hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))
  run : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING
  lay : VmLay K
  kb : K.ksb = L.ksb s
  nc : (L.cpu s).val < K.ncores
  hT : ∀ t ∈ T, K.heap t = some .tcb
  hSc : ∀ c ∈ Scs, K.heap c = some (.sc (Z c))
  curAff : L.mem s (affA (L.curW s)) = L.cpu s
  cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s
  affSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)
  tmc : L.mem s (tmA (L := L) s) ≠ 0#u64 → L.mem s (tdA (L.mem s (tmA (L := L) s))) ≠ 0#u64 ∧
    treeCore (L.mem s (thA (L.mem s (tmA (L := L) s)))) = L.cpu s

section
variable (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
include P

theorem VmBase.tp : TcbPlaced T := P.bxi.1.choose_spec.choose_spec.tcbs
theorem VmBase.cT : L.curW s ∈ T := P.bxi.1.choose_spec.choose_spec.curT
theorem VmBase.tA : TcbAddr (L.curW s) := P.tp _ P.cT
theorem VmBase.np : NodePlaced st T s (L.cpu s) :=
  P.bxi.1.choose_spec.choose_spec.nodes _ P.bxi.1.choose_spec.choose_spec.cur

theorem VmBase.region_kernel {b : U64} (h : region K b ≠ .none ∨ (K.ksb.val ≤ b.val ∧ b.val < K.ksb.val + 13568)) :
    b ∉ K.user := fun hu => by
  obtain ⟨h1, h2⟩ := P.lay.io.user b hu
  rcases h with h | h
  · exact h h1
  · exact h2 h

theorem VmBase.inNode (o : U64) (ho : o.val < 4288) : InNode K (L.cpu s) (L.nodeAt s (L.cpu s) o) := by
  have hv := nodeAt_val P.np ho
  refine ⟨P.nc, ?_, ?_⟩ <;> rw [hv, P.kb] <;> unfold LawfulStore.nodeBase <;> omega

theorem VmBase.nd (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) o) ∧ IoWS (st := st) K Locks s (L.nodeAt s (L.cpu s) o) := by
  have hin := P.inNode o ho
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) (L.nodeAt s (L.cpu s) o) := by
    unfold WPerm; rw [own_node P.lay.io hin]; rfl
  have ha := nodeAt_aligned P.np ho h8
  exact ⟨⟨ha, P.region_kernel (Or.inl (by rw [P.lay.io.node _ _ hin]; simp)), Or.inl hw⟩, ha, hw⟩

/-- The home words (not gate, timer or queue-link words) of a thread homed on
this core. -/
theorem VmBase.homeOf {y off : U64} (hy : y ∈ T) (haff : L.mem s (affA y) = L.cpu s) (h1 : 192 ≤ off.val)
    (h2 : off.val < 4096) (h8 : off.val % 8 = 0)
    (hg : ¬ GateField off.val) (htm : ¬ TimerField off.val) (hG : ¬ GField off.val) :
    IoRS (st := st) K Locks s (fld y off) ∧ IoWS (st := st) K Locks s (fld y off) := by
  have hA := P.tp y hy
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) (fld y off) := by
    unfold WPerm
    rw [own_tcbw P.lay.io (P.hT _ hy) hA h1 h2]
    unfold tcbOwner
    rw [if_neg hg, if_neg htm, if_neg hG]
    exact haff
  have ha : Aligned (fld y off) := field_aligned hA h2 h8
  exact ⟨⟨ha, P.region_kernel (Or.inl (by rw [P.lay.io.tcbw _ (P.hT _ hy) off h1 h2]; simp)), Or.inl hw⟩, ha, hw⟩

/-- The current thread's home words. -/
theorem VmBase.home {off : U64} (h1 : 192 ≤ off.val) (h2 : off.val < 4096) (h8 : off.val % 8 = 0)
    (hg : ¬ GateField off.val) (htm : ¬ TimerField off.val) :
    IoRS (st := st) K Locks s (fld (L.curW s) off) ∧ IoWS (st := st) K Locks s (fld (L.curW s) off) := by
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) (fld (L.curW s) off) := by
    unfold WPerm
    rw [own_tcb_home P.lay.io (P.hT _ P.cT) P.tA h1 h2 hg htm P.run]
    exact P.curAff
  have ha : Aligned (fld (L.curW s) off) := field_aligned P.tA h2 h8
  exact ⟨⟨ha, P.region_kernel (Or.inl (by rw [P.lay.io.tcbw _ (P.hT _ P.cT) off h1 h2]; simp)), Or.inl hw⟩, ha, hw⟩

/-- A thread's gate-owned words. -/
theorem VmBase.gate {t off : U64} (ht : t ∈ T) (h1 : 192 ≤ off.val) (h2 : off.val < 4096) (h8 : off.val % 8 = 0)
    (hg : GateField off.val) : IoRS (st := st) K Locks s (fld t off) := by
  refine ⟨field_aligned (P.tp t ht) h2 h8,
    P.region_kernel (Or.inl (by rw [P.lay.io.tcbw _ (P.hT _ ht) off h1 h2]; simp)),
    Or.inr (own_tcb_gate P.lay.io (P.hT _ ht) (P.tp t ht) h1 h2 hg)⟩

/-- The queue links of a thread queued (`STATE` 3 or 6) on an object whose
lock the path holds. -/
theorem VmBase.link {y off p : U64} (hy : y ∈ T) (hq : OwnMap.QueuedState (L.mem s (stA y)))
    (hb : L.mem s (blockA y) = p) (hl : Locks s p) (hoff : off.val = 3496 ∨ off.val = 3504) :
    IoRS (st := st) K Locks s (fld y off) ∧ IoWS (st := st) K Locks s (fld y off) := by
  have hA := P.tp y hy
  have h1 : 192 ≤ off.val := by omega
  have h2 : off.val < 4096 := by omega
  have h8 : off.val % 8 = 0 := by omega
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) (fld y off) := by
    unfold WPerm
    rw [own_tcbw P.lay.io (P.hT _ hy) hA h1 h2]
    have hg : ¬ GateField off.val := by unfold GateField; omega
    have htm : ¬ TimerField off.val := by unfold TimerField; omega
    have hG : GField off.val := by unfold GField; omega
    have e1 : fld y OwnMap.oSTATE = stA y := fld_state y
    have e2 : fld y OwnMap.oBLOCK_OBJ = blockA y := rfl
    unfold tcbOwner
    rw [if_neg hg, if_neg htm, if_pos hG, e1, e2]
    unfold OwnMap.gOwner
    rw [if_pos hq, hb]
    exact hl
  have ha : Aligned (fld y off) := field_aligned hA h2 h8
  exact ⟨⟨ha, P.region_kernel (Or.inl (by rw [P.lay.io.tcbw _ (P.hT _ hy) off h1 h2]; simp)), Or.inl hw⟩, ha, hw⟩

/-- The words of an endpoint whose lock the path holds. -/
theorem VmBase.ep {p b : U64} (hp : K.heap p = some .ep) (hb : InW p 16 b) (ha : Aligned b) (hl : Locks s p) :
    IoRS (st := st) K Locks s b ∧ IoWS (st := st) K Locks s b := by
  have hr := P.lay.epw p hp b hb
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) b := by
    unfold WPerm; simp only [own, hr]; exact hl
  exact ⟨⟨ha, P.region_kernel (Or.inl (by rw [hr]; simp)), Or.inl hw⟩, ha, hw⟩

/-- The words of a reply object whose lock the path holds. -/
theorem VmBase.reply {p b : U64} (hp : K.heap p = some .reply) (hb : InW p 32 b) (ha : Aligned b)
    (hl : Locks s p) : IoRS (st := st) K Locks s b ∧ IoWS (st := st) K Locks s b := by
  have hr := P.lay.rpw p hp b hb
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) b := by
    unfold WPerm; simp only [own, hr]; exact hl
  exact ⟨⟨ha, P.region_kernel (Or.inl (by rw [hr]; simp)), Or.inl hw⟩, ha, hw⟩

theorem VmBase.reg {r : U64} (hr : r.val < 384) :
    IoRS (st := st) K Locks s (regA (L.curW s) r) ∧ IoWS (st := st) K Locks s (regA (L.curW s) r) := by
  obtain ⟨k, hk, e⟩ := regA_eq P.tA hr
  rw [e]
  refine P.home (off := k) (by omega) (by omega) (by omega) ?_ ?_
  · unfold GateField; omega
  · unfold TimerField; omega

/-- A register of a thread homed on this core. -/
theorem VmBase.regOf {y r : U64} (hy : y ∈ T) (haff : L.mem s (affA y) = L.cpu s) (hr : r.val < 384) :
    IoRS (st := st) K Locks s (regA y r) ∧ IoWS (st := st) K Locks s (regA y r) := by
  obtain ⟨k, hk, e⟩ := regA_eq (P.tp y hy) hr
  rw [e]
  refine P.homeOf (off := k) hy haff (by omega) (by omega) (by omega) ?_ ?_ ?_
  · unfold GateField; omega
  · unfold TimerField; omega
  · unfold GField; omega

theorem VmBase.stw : IoRS (st := st) K Locks s (stA (L.curW s)) ∧ IoWS (st := st) K Locks s (stA (L.curW s)) := by
  refine P.home (off := layout.tcb.STATE) ?_ ?_ ?_ ?_ ?_ <;> rw [st_val] <;> simp [GateField, TimerField]

/-- The words of an SC on this core. -/
theorem VmBase.scacc {c : U64} (hc : c ∈ Scs) (hcore : L.mem s (scCoreA c) = L.cpu s) :
    ScAcc (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s) c (Z c) := by
  obtain ⟨hP, hz⟩ := P.bxi.2.2.1.1.sc _ hc
  obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
  have hh := P.hSc _ hc
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hw : ∀ b, InSC c (Z c) b → b.val ≠ c.val + 16 → WPerm (own K) (L.cpu s) (Locks s) (L.mem s) b := by
    intro b hb h16
    unfold WPerm; rw [own_sc P.lay.io hh hb h16]; exact hcore
  refine ⟨fun b ha hb => ⟨ha, P.region_kernel (Or.inl (by rw [P.lay.io.scw _ _ hh b hb]; simp)), ?_⟩,
    fun b ha hb => ⟨ha, ?_⟩, ⟨by unfold Aligned; rw [hv, hcv]; omega, ?_⟩⟩
  · by_cases h16 : b.val = c.val + 16
    · exact Or.inr (own_sc16 P.lay.io hh hb h16)
    · exact Or.inl (hw b hb h16)
  · unfold InRing at hb
    exact hw b ⟨by omega, hb.2⟩ (by omega)
  · exact hw _ ⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩ (by rw [hv, hcv]; omega)

theorem VmBase.slot {sl : U64} (h : sl ∈ K.slots) (hg : TcbSlot K sl ∨ ¬ NullOrFrame (L.mem s sl)) :
    IoRS (st := st) K Locks s sl ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add sl 8#u64) := by
  obtain ⟨h8, hf⟩ := P.lay.io.slot8 sl h
  have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have k : ∀ b : U64, InW sl 16 b → Aligned b → IoRS (st := st) K Locks s b := fun b hb ha =>
    ⟨ha, P.region_kernel (Or.inl (by rw [P.lay.io.slotw sl h b ⟨hb.1, by have := hb.2; omega⟩]; simp)),
      Or.inr (own_slot_gate P.lay.io h hb hg)⟩
  exact ⟨k sl ⟨le_refl _, by omega⟩ h8, k _ ⟨by omega, by omega⟩ (by unfold Aligned; omega)⟩

/-- A thread's own capability slot `i < 6` (gate-owned). -/
theorem VmBase.tslot {y : U64} (hy : y ∈ T) {i sl : U64} (h : obj.Tcb.slot y i = ok sl) (hi : i.val < 6) :
    IoRS (st := st) K Locks s sl ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add sl 8#u64) := by
  obtain ⟨h1, h2⟩ := P.lay.io.tslot _ (P.hT _ hy) i sl h hi
  exact P.slot h1 (Or.inl h2)

theorem VmBase.ksw {o : U64} (ho : o.val < 256) (h8 : o.val % 8 = 0) :
    IoRS (st := st) K Locks s (core.num.U64.wrapping_add (L.ksb s) o) := by
  obtain ⟨k8, kf⟩ := P.lay.io.ksf
  rw [P.kb] at k8 kf
  have hv : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have h1 : K.ksb.val ≤ (core.num.U64.wrapping_add (L.ksb s) o).val := by rw [hv, P.kb]; omega
  have h2' : (core.num.U64.wrapping_add (L.ksb s) o).val < K.ksb.val + 256 := by rw [hv, P.kb]; omega
  have h2 : (core.num.U64.wrapping_add (L.ksb s) o).val < K.ksb.val + 13568 := by omega
  have ha : Aligned (core.num.U64.wrapping_add (L.ksb s) o) := by unfold Aligned; omega
  exact ⟨ha, P.region_kernel (Or.inr ⟨h1, h2⟩), Or.inr (own_none (P.lay.io.ks _ ha h1 h2'))⟩

theorem VmBase.td (h0 : L.mem s (tmA (L := L) s) ≠ 0#u64) :
    IoRS (st := st) K Locks s (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64) := by
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hT := (hX.tm.min _ hq.cur).resolve_left h0
  obtain ⟨hd, hc⟩ := P.tmc h0
  have hA := hq.tcbs _ hT
  refine ⟨field_aligned hA (by simp) (by simp), P.region_kernel (Or.inl ?_), Or.inl ?_⟩
  · have := P.lay.io.tcbw _ (P.hT _ hT) 3528#u64 (by simp) (by simp)
    unfold fld at this; rw [this]; simp
  · have e := own_tcbw (m := L.mem s) P.lay.io (P.hT _ hT) hA (off := 3528#u64) (by simp) (by simp)
    unfold fld at e
    rw [e]
    have g1 : ¬ GateField (3528#u64 : U64).val := by simp [GateField]
    have g2 : TimerField (3528#u64 : U64).val := by simp [TimerField]
    have hd' : (L.mem s (fld (L.mem s (tmA (L := L) s)) OwnMap.oTIMER_DEADLINE)).val ≠ 0 := by
      intro e0; exact hd (UScalar.eq_of_val_eq e0)
    simp only [tcbOwner, if_neg g1, if_pos g2, OwnMap.tOwner, if_pos hd']
    exact hc

theorem VmBase.rs (h0 : L.mem s (rhA (L := L) s) ≠ 0#u64) :
    IoRS (st := st) K Locks s (scA (L.mem s (rhA (L := L) s))) ∧
      RdHead (L := L) (IoRS (st := st) K Locks s) s (L.mem s (scA (L.mem s (rhA (L := L) s)))) := by
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
  exact ⟨P.gate (off := 3464#u64) hT (by simp) (by simp) (by simp) (by simp [GateField]),
    (P.scacc hsc ((P.affSc _ hT hne).trans haff)).head hW⟩

theorem VmBase.cscS : L.cscW s ∈ Scs := P.bxi.2.2.1.2.2.cur

theorem VmBase.cscacc : ScAcc (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s) (L.cscW s) (Z (L.cscW s)) :=
  P.scacc P.cscS P.cscCore

theorem VmBase.cscwf : RefillsWF st s (L.cscW s) (Z (L.cscW s)) :=
  (bxi_scin P.bxi P.cscS ((P.bxi.2.2.2.2.act _ P.cscS).1 P.csc)).1

end

end

end Fl4Proofs.P2.PathObl

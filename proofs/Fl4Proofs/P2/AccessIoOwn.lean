/-
# P2: the I/O port path's accesses against the ownership map (line p2io)

`PathObl`'s `acc`, `read_own`, `write_own`, `aligned` for
`syscall.handle_ioport_local`.

* `IoRS` / `IoWS`: the maximal sets (the aligned words a path on this core may
  read / write by `OwnMap.own` at the entry state; user memory left out of
  `IoRS`, the path reads none); `IoDS`: what a declined run writes (`FAULT_IP`,
  the core's `CUR_TIME` and `CONSUMED`);
* `IoLay`: the layout facts, `IoPre`: the entry facts;
* `own_*`: the owner of each word class; `IoPre.ent`: `AccessIoEnt`'s entry
  facts for these sets; `io_acc`: **`PathObl.acc`**.

Premises (fields of `IoLay`, `IoPre`):
* `IoLay` [J]: regions of the layout (`RegionOK`'s kind: nodes, capability
  slots, TCBs, SCs, the kernel-global area and user memory are disjoint);
* `IoPre.bxi`, `csc`, `hcsc`: P1's `EntryInv` / `DecPre` at the entry;
* `IoPre.run` [P]: the current thread is `RUNNING` or `RESTART`
  (`AccessIoEnt`);
* `IoPre.curAff`, `cscCore`, `affSc` [J]: `P2/InvAff.lean`'s (1), (3), (2) (line
  par/p2j: `OwnJ.curAff`, `EntryInv.cur_sc_core`, `OwnJ.affSc`);
* `IoPre.tmc` [J]: the earliest timer is armed, in this core's tree (P1's
  `TimerRB`, DESIGN "Timer ownership");
* `IoPre.walk`, `IoPre.fin` [J]: the CSpace walk's slots are capability slots outside
  the other objects (P1's `CnOff`).
-/
import Fl4Proofs.P2.AccessIoEnt
import Fl4Proofs.P2.OwnMap
import Fl4Proofs.P2.PathBridge
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region GateField TimerField GField tcbOwner TcbSlot NullOrFrame
  slotOwner treeCore)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout} {m : U64 → U64}
variable {Locks : S → U64 → Prop}

/-- **Layout facts** [J]: the region of each class of words. -/
structure IoLay (K : KLayout) : Prop where
  node : ∀ c b, InNode K c b → region K b = .node c
  tcbw : ∀ t, K.heap t = some .tcb → ∀ off : U64, 192 ≤ off.val → off.val < 4096 → region K (fld t off) = .tcb t
  slotw : ∀ p ∈ K.slots, ∀ b, InW p 32 b → region K b = .slot p
  slot8 : ∀ p ∈ K.slots, p.val % 8 = 0 ∧ p.val + 32 ≤ 2 ^ 64
  tslot : ∀ t, K.heap t = some .tcb → ∀ i sl, obj.Tcb.slot t i = ok sl → i.val < 6 → sl ∈ K.slots ∧ TcbSlot K sl
  scw : ∀ p z, K.heap p = some (.sc z) → ∀ b, InW p (2 ^ z) b → region K b = .sc p
  ks : ∀ b : U64, K.ksb.val ≤ b.val → b.val < K.ksb.val + 13568 → region K b = .none
  ksf : K.ksb.val % 8 = 0 ∧ K.ksb.val + 13568 ≤ 2 ^ 64
  user : ∀ b ∈ K.user, region K b = .none ∧ ¬ (K.ksb.val ≤ b.val ∧ b.val < K.ksb.val + 13568)

/-! ## Owners -/

theorem own_node (hL : IoLay K) {c b : U64} (h : InNode K c b) : own K m b = .core c := by
  simp only [own, hL.node c b h]

theorem own_tcbw (hL : IoLay K) {t off : U64} (ht : K.heap t = some .tcb) (hT : TcbAddr t) (h1 : 192 ≤ off.val)
    (h2 : off.val < 4096) : own K m (fld t off) = tcbOwner m t off.val := by
  have e : (fld t off).val - t.val = off.val := by unfold fld; rw [tcb_wadd_val hT h2]; omega
  simp only [own, hL.tcbw t ht off h1 h2, e]

theorem own_tcb_gate (hL : IoLay K) {t off : U64} (ht : K.heap t = some .tcb) (hT : TcbAddr t) (h1 : 192 ≤ off.val)
    (h2 : off.val < 4096) (hg : GateField off.val) : own K m (fld t off) = .gate := by
  rw [own_tcbw hL ht hT h1 h2]; simp only [tcbOwner, if_pos hg]

theorem fld_state (t : U64) : fld t OwnMap.oSTATE = stA t := by
  have e : OwnMap.oSTATE = layout.tcb.STATE := UScalar.eq_of_val_eq (by rw [st_val, OwnMap.oSTATE_val])
  unfold fld stA; rw [e]

theorem own_tcb_home (hL : IoLay K) {t off : U64} (ht : K.heap t = some .tcb) (hT : TcbAddr t) (h1 : 192 ≤ off.val)
    (h2 : off.val < 4096) (hg : ¬ GateField off.val) (htm : ¬ TimerField off.val)
    (hs : m (stA t) = sched.TS_RESTART ∨ m (stA t) = sched.TS_RUNNING) :
    own K m (fld t off) = .core (m (affA t)) := by
  have e1 : fld t OwnMap.oSTATE = stA t := fld_state t
  have e2 : fld t OwnMap.oAFFINITY = affA t := rfl
  rw [own_tcbw hL ht hT h1 h2]
  have q1 : ¬ OwnMap.QueuedState (m (stA t)) := by
    unfold OwnMap.QueuedState
    rcases hs with e | e <;> rw [e] <;> simp [sched.TS_RESTART, sched.TS_RUNNING]
  have q2 : ¬ OwnMap.ReplyState (m (stA t)) := by
    unfold OwnMap.ReplyState
    rcases hs with e | e <;> rw [e] <;> simp [sched.TS_RESTART, sched.TS_RUNNING]
  unfold tcbOwner
  rw [if_neg hg, if_neg htm, e1, e2]
  unfold OwnMap.gOwner
  by_cases hG : GField off.val
  · rw [if_pos hG, if_neg q1, if_neg q2]
  · rw [if_neg hG]

theorem own_sc (hL : IoLay K) {p b : U64} {z : Nat} (hp : K.heap p = some (.sc z)) (hb : InW p (2 ^ z) b)
    (h16 : b.val ≠ p.val + 16) : own K m b = .core (m (scCoreA p)) := by
  have e : fld p 16#u64 = scCoreA p := by unfold fld scCoreA; simp [layout.sc.CORE]
  simp only [own, hL.scw p z hp b hb, if_neg h16, e]

theorem own_sc16 (hL : IoLay K) {p b : U64} {z : Nat} (hp : K.heap p = some (.sc z)) (hb : InW p (2 ^ z) b)
    (h16 : b.val = p.val + 16) : own K m b = .gate := by
  simp only [own, hL.scw p z hp b hb, if_pos h16]

theorem own_slot_gate (hL : IoLay K) {p b : U64} (hp : p ∈ K.slots) (hb : InW p 16 b)
    (h : TcbSlot K p ∨ ¬ NullOrFrame (m p)) : own K m b = .gate := by
  have hr := hL.slotw p hp b ⟨hb.1, by have := hb.2; omega⟩
  have h16 : ¬ 16 ≤ b.val - p.val := by have := hb.1; have := hb.2; omega
  simp only [own, hr, slotOwner, if_neg h16]
  by_cases hT : TcbSlot K p
  · rw [if_pos hT]
  · rw [if_neg hT, if_neg (h.resolve_left hT)]

theorem own_none {b : U64} (h : region K b = .none) : own K m b = .gate := by simp only [own, h]

/-! ## Cap tags -/

theorem decode_tag {w0 w1 : U64} {c : capability.Cap} (h : capability.Cap.decode w0 w1 = ok c) (hn : NullOrFrame w0) :
    (∀ p r g k, c ≠ .CNode p r g k) ∧ (∀ f l z, c ≠ .IoPort f l z) := by
  unfold capability.Cap.decode at h
  obtain ⟨t, ht, h⟩ := bind_eq_ok h
  obtain ⟨p, -, h⟩ := bind_eq_ok h
  have tv : t.val = w0.val / 2 ^ 59 := by
    have hs : (w0 >>> 59#i32) ⦃ t => t.val = w0.val >>> 59 ⦄ := by
      step as ⟨t', h1, h2⟩
      simpa using h1
    rw [post_of_ok hs ht, Nat.shiftRight_eq_div_pow]
  unfold NullOrFrame at hn
  rw [← tv] at hn
  rcases hn with h0 | h0
  · have e : t = 0#u64 := UScalar.eq_of_val_eq (by rw [h0]; rfl)
    subst e
    have h' : (ok capability.Cap.Null : Result capability.Cap) = ok c := h
    cases ok_inj_ff h'
    exact ⟨fun _ _ _ _ e => by simp at e, fun _ _ _ e => by simp at e⟩
  · have e : t = 13#u64 := UScalar.eq_of_val_eq (by rw [h0]; rfl)
    subst e
    have h' : (do
      let i ← w0 >>> 48#i32
      let i1 ← lift (i &&& 3#u64)
      let fs ← capability.FrameSize.from_code i1
      let i2 ← w0 >>> 50#i32
      let i3 ← lift (i2 &&& 3#u64)
      let b ← capability.bit w0 52#u64
      let b1 ← capability.bit w0 53#u64
      let b2 ← capability.bit w0 58#u64
      let i4 ← capability.unpack_asid w0 54#u64 w1
      let i5 ← lift (w1 &&& capability.PTR_MASK)
      ok (capability.Cap.Frame p fs i3 b b1 b2 i4 i5)) = ok c := h
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    cases ok_inj_ff h'
    exact ⟨fun _ _ _ _ e => by simp at e, fun _ _ _ e => by simp at e⟩

theorem cap_not_nof {sl : U64} {c : capability.Cap} (h : obj.Slot.cap st sl s = ok c)
    (hc : (∃ p r g k, c = .CNode p r g k) ∨ (∃ f l z, c = .IoPort f l z)) : ¬ NullOrFrame (L.mem s sl) := by
  intro hn
  unfold obj.Slot.cap at h
  rw [L.read_pair_eq] at h
  simp only [bind_ok] at h
  obtain ⟨h1, h2⟩ := decode_tag h hn
  rcases hc with ⟨p, r, g, k, e⟩ | ⟨f, l, z, e⟩
  · exact h1 _ _ _ _ e
  · exact h2 _ _ _ e

/-! ## The sets and the entry facts -/

/-- What the path may read: aligned kernel words this core may read by `own`. -/
def IoRS (K : KLayout) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ x ∉ K.user ∧ RPerm (own K) (L.cpu s) (Locks s) (L.mem s) x

/-- What an accepted run may write. -/
def IoWS (K : KLayout) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ WPerm (own K) (L.cpu s) (Locks s) (L.mem s) x

/-- What a declined run may write. -/
def IoDS (s : S) (x : U64) : Prop :=
  x = regA (L.curW s) layout.reg.FAULT_IP ∨ x = L.nodeAt s (L.cpu s) layout.node.CUR_TIME ∨
    x = L.nodeAt s (L.cpu s) layout.node.CONSUMED

/-- **The entry facts of the I/O port path** (module docstring). -/
structure IoPre (st : machine.Store S) [L : LawfulStore st] (K : KLayout) (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (s : S) : Prop where
  bxi : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s
  csc : L.cscW s ∈ Ac
  hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))
  run : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING
  lay : IoLay K
  kb : K.ksb = L.ksb s
  nc : (L.cpu s).val < K.ncores
  hT : ∀ t ∈ T, K.heap t = some .tcb
  hSc : ∀ c ∈ Scs, K.heap c = some (.sc (Z c))
  curAff : L.mem s (affA (L.curW s)) = L.cpu s
  cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s
  affSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)
  tmc : L.mem s (tmA (L := L) s) ≠ 0#u64 → L.mem s (tdA (L.mem s (tmA (L := L) s))) ≠ 0#u64 ∧
    treeCore (L.mem s (thA (L.mem s (tmA (L := L) s)))) = L.cpu s
  walk : ∃ C : U64 → U64 → Prop, (∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r) ∧
    WalkCl (st := st) s C ∧
    ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots ∧
      OutsideObjs st T Cs s (cnSlot p (y &&& m)) ∧
      OutsideObjs st T Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)
  fin : ∀ x, cspace.lookup_slot st s (L.curW s) (L.mem s (regA (L.curW s) layout.reg.CAP)) = ok (.Ok x) →
    x.slot ∈ K.slots ∧ OutsideObjs st T Cs s x.slot ∧
      OutsideObjs st T Cs s (core.num.U64.wrapping_add x.slot 8#u64)

section
variable (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
include P

theorem IoPre.tp : TcbPlaced T := P.bxi.1.choose_spec.choose_spec.tcbs
theorem IoPre.cT : L.curW s ∈ T := P.bxi.1.choose_spec.choose_spec.curT
theorem IoPre.tA : TcbAddr (L.curW s) := P.tp _ P.cT
theorem IoPre.np : NodePlaced st T s (L.cpu s) :=
  P.bxi.1.choose_spec.choose_spec.nodes _ P.bxi.1.choose_spec.choose_spec.cur

theorem IoPre.region_kernel {b : U64} (h : region K b ≠ .none ∨ (K.ksb.val ≤ b.val ∧ b.val < K.ksb.val + 13568)) :
    b ∉ K.user := fun hu => by
  obtain ⟨h1, h2⟩ := P.lay.user b hu
  rcases h with h | h
  · exact h h1
  · exact h2 h

theorem IoPre.inNode (o : U64) (ho : o.val < 4288) : InNode K (L.cpu s) (L.nodeAt s (L.cpu s) o) := by
  have hv := nodeAt_val P.np ho
  refine ⟨P.nc, ?_, ?_⟩ <;> rw [hv, P.kb] <;> unfold LawfulStore.nodeBase <;> omega

theorem IoPre.nd (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) o) ∧ IoWS (st := st) K Locks s (L.nodeAt s (L.cpu s) o) := by
  have hin := P.inNode o ho
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) (L.nodeAt s (L.cpu s) o) := by
    unfold WPerm; rw [own_node P.lay hin]; rfl
  have ha := nodeAt_aligned P.np ho h8
  exact ⟨⟨ha, P.region_kernel (Or.inl (by rw [P.lay.node _ _ hin]; simp)), Or.inl hw⟩, ha, hw⟩

/-- The current thread's home words. -/
theorem IoPre.home {off : U64} (h1 : 192 ≤ off.val) (h2 : off.val < 4096) (h8 : off.val % 8 = 0)
    (hg : ¬ GateField off.val) (htm : ¬ TimerField off.val) :
    IoRS (st := st) K Locks s (fld (L.curW s) off) ∧ IoWS (st := st) K Locks s (fld (L.curW s) off) := by
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) (fld (L.curW s) off) := by
    unfold WPerm
    rw [own_tcb_home P.lay (P.hT _ P.cT) P.tA h1 h2 hg htm P.run]
    exact P.curAff
  have ha : Aligned (fld (L.curW s) off) := field_aligned P.tA h2 h8
  exact ⟨⟨ha, P.region_kernel (Or.inl (by rw [P.lay.tcbw _ (P.hT _ P.cT) off h1 h2]; simp)), Or.inl hw⟩, ha, hw⟩

/-- A thread's gate-owned words. -/
theorem IoPre.gate {t off : U64} (ht : t ∈ T) (h1 : 192 ≤ off.val) (h2 : off.val < 4096) (h8 : off.val % 8 = 0)
    (hg : GateField off.val) : IoRS (st := st) K Locks s (fld t off) := by
  refine ⟨field_aligned (P.tp t ht) h2 h8, P.region_kernel (Or.inl (by rw [P.lay.tcbw _ (P.hT _ ht) off h1 h2]; simp)),
    Or.inr (own_tcb_gate P.lay (P.hT _ ht) (P.tp t ht) h1 h2 hg)⟩

theorem IoPre.reg {r : U64} (hr : r.val < 384) :
    IoRS (st := st) K Locks s (regA (L.curW s) r) ∧ IoWS (st := st) K Locks s (regA (L.curW s) r) := by
  obtain ⟨k, hk, e⟩ := regA_eq P.tA hr
  rw [e]
  refine P.home (off := k) (by omega) (by omega) (by omega) ?_ ?_
  · unfold GateField; omega
  · unfold TimerField; omega

theorem IoPre.stw : IoRS (st := st) K Locks s (stA (L.curW s)) ∧ IoWS (st := st) K Locks s (stA (L.curW s)) := by
  refine P.home (off := layout.tcb.STATE) ?_ ?_ ?_ ?_ ?_ <;> rw [st_val] <;> simp [GateField, TimerField]

/-- The words of an SC on this core. -/
theorem IoPre.scacc {c : U64} (hc : c ∈ Scs) (hcore : L.mem s (scCoreA c) = L.cpu s) :
    ScAcc (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s) c (Z c) := by
  obtain ⟨hP, hz⟩ := P.bxi.2.2.1.1.sc _ hc
  obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
  have hh := P.hSc _ hc
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hw : ∀ b, InSC c (Z c) b → b.val ≠ c.val + 16 → WPerm (own K) (L.cpu s) (Locks s) (L.mem s) b := by
    intro b hb h16
    unfold WPerm; rw [own_sc P.lay hh hb h16]; exact hcore
  refine ⟨fun b hb ha => ⟨ha, P.region_kernel (Or.inl (by rw [P.lay.scw _ _ hh b hb]; simp)), ?_⟩, fun b hb ha => ⟨ha, ?_⟩,
    ⟨by unfold Aligned; rw [hv, hcv]; omega, ?_⟩⟩
  · by_cases h16 : b.val = c.val + 16
    · exact Or.inr (own_sc16 P.lay hh hb h16)
    · exact Or.inl (hw b hb h16)
  · unfold InRing at hb
    exact hw b ⟨by omega, hb.2⟩ (by omega)
  · exact hw _ ⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩ (by rw [hv, hcv]; omega)

theorem IoPre.slot {sl : U64} (h : sl ∈ K.slots) (hg : TcbSlot K sl ∨ ¬ NullOrFrame (L.mem s sl)) :
    IoRS (st := st) K Locks s sl ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add sl 8#u64) := by
  obtain ⟨h8, hf⟩ := P.lay.slot8 sl h
  have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have k : ∀ b : U64, InW sl 16 b → Aligned b → IoRS (st := st) K Locks s b := fun b hb ha =>
    ⟨ha, P.region_kernel (Or.inl (by rw [P.lay.slotw sl h b ⟨hb.1, by have := hb.2; omega⟩]; simp)),
      Or.inr (own_slot_gate P.lay h hb hg)⟩
  exact ⟨k sl ⟨le_refl _, by omega⟩ h8, k _ ⟨by omega, by omega⟩ (by unfold Aligned; omega)⟩

theorem IoPre.ksw {o : U64} (ho : o.val < 13568) (h8 : o.val % 8 = 0) :
    IoRS (st := st) K Locks s (core.num.U64.wrapping_add (L.ksb s) o) := by
  obtain ⟨k8, kf⟩ := P.lay.ksf
  rw [P.kb] at k8 kf
  have hv : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have h1 : K.ksb.val ≤ (core.num.U64.wrapping_add (L.ksb s) o).val := by rw [hv, P.kb]; omega
  have h2 : (core.num.U64.wrapping_add (L.ksb s) o).val < K.ksb.val + 13568 := by rw [hv, P.kb]; omega
  exact ⟨by unfold Aligned; omega, P.region_kernel (Or.inr ⟨h1, h2⟩), Or.inr (own_none (P.lay.ks _ h1 h2))⟩

theorem IoPre.td (h0 : L.mem s (tmA (L := L) s) ≠ 0#u64) :
    IoRS (st := st) K Locks s (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64) := by
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hT := (hX.tm.min _ hq.cur).resolve_left h0
  obtain ⟨hd, hc⟩ := P.tmc h0
  have hA := hq.tcbs _ hT
  refine ⟨field_aligned hA (by simp) (by simp), P.region_kernel (Or.inl ?_), Or.inl ?_⟩
  · have := P.lay.tcbw _ (P.hT _ hT) 3528#u64 (by simp) (by simp)
    unfold fld at this; rw [this]; simp
  · have e := own_tcbw (m := L.mem s) P.lay (P.hT _ hT) hA (off := 3528#u64) (by simp) (by simp)
    unfold fld at e
    rw [e]
    have g1 : ¬ GateField (3528#u64 : U64).val := by simp [GateField]
    have g2 : TimerField (3528#u64 : U64).val := by simp [TimerField]
    have hd' : (L.mem s (fld (L.mem s (tmA (L := L) s)) OwnMap.oTIMER_DEADLINE)).val ≠ 0 := by
      intro e0; exact hd (UScalar.eq_of_val_eq e0)
    simp only [tcbOwner, if_neg g1, if_pos g2, OwnMap.tOwner, if_pos hd']
    exact hc

theorem IoPre.rs (h0 : L.mem s (rhA (L := L) s) ≠ 0#u64) :
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

theorem IoPre.cscS : L.cscW s ∈ Scs := P.bxi.2.2.1.2.2.cur

theorem IoPre.cscacc : ScAcc (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s) (L.cscW s) (Z (L.cscW s)) :=
  P.scacc P.cscS P.cscCore

theorem IoPre.cscwf : RefillsWF st s (L.cscW s) (Z (L.cscW s)) :=
  (bxi_scin P.bxi P.cscS ((P.bxi.2.2.2.2.act _ P.cscS).1 P.csc)).1

theorem IoPre.iacc : IoAcc st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s) s (L.cscW s) (Z (L.cscW s)) where
  acc := P.cscacc
  nd := P.nd
  sc := P.gate (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  dt := P.ksw (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  td := P.td
  rs := P.rs
  ryl := (P.home (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  rst := P.stw.1
  rfi := (P.reg (by simp [layout.reg.FAULT_IP])).1
  wnx := (P.reg (by simp [layout.reg.NEXT_IP])).2
  wst := P.stw.2
  rin := (P.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1

theorem IoPre.ent : IoEnt st T Cs Ω H Sg Rp Scs Nt Z Ac (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s) s :=
  ⟨P.bxi, P.csc, P.hcsc, P.run, P.iacc⟩

/-- **`IoMid` at the entry.** -/
theorem IoPre.mid {C : U64 → U64 → Prop}
    (hroot : ∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r) (hcl : WalkCl (st := st) s C)
    (hsl : ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots)
    (hsc0 : L.mem s (scA (L.curW s)) = L.cscW s)
    (info : msginfo.MessageInfo) (emi : msg.msg_info st s (L.curW s) = ok info) :
    IoMid (L := L) (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s) s s (L.curW s) info
      (L.mem s (regA (L.curW s) layout.reg.CAP)) C (L.curW s) := by
  have hslot : ∀ i sl, obj.Tcb.slot (L.curW s) i = ok sl → i.val < 6 →
      IoRS (st := st) K Locks s sl ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add sl 8#u64) := fun i sl h hi => by
    obtain ⟨h1, h2⟩ := P.lay.tslot _ (P.hT _ P.cT) i sl h hi
    exact P.slot h1 (Or.inl h2)
  have h0 := hslot _ _ (tcb_slot_ctable (L.curW s)) (by simp [layout.tcb.SLOT_CTABLE])
  have nd1 := P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have nd2 := P.nd (Locks := Locks) layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have hO := P.bxi.2.2.1.1
  have hmx := maxA_facts hO P.cscS
  exact
  { k := rfl, c := rfl, cur := rfl, mi := emi
    rmi := (P.reg (by simp [layout.reg.MSG_INFO])).1
    r10 := (P.reg (by simp [layout.reg.R10])).1
    cap := (P.reg (by simp [layout.reg.CAP])).1
    yld := (P.home (off := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
    hsl := tcb_slot_ctable _
    hR0 := h0.1, hR8 := h0.2
    hRc := fun p r m y p' r' gs' g' hp hm hc =>
      P.slot (hsl p r m y hp hm) (Or.inr (cap_not_nof hc (Or.inl ⟨_, _, _, _, rfl⟩)))
    hcl := hcl
    hroot := hroot
    hRf := fun x f l z hx hc => P.slot (P.fin x hx).1 (Or.inr (cap_not_nof hc (Or.inr ⟨_, _, _, rfl⟩)))
    rh := P.cscacc.head P.cscwf
    td := P.td
    rs := P.rs
    dt := P.ksw (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
    cd := P.ksw (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
    af := P.gate (off := 3520#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
    dom := P.gate (off := 3432#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
    iok := ⟨
      { tcb := P.tA
        regR := fun r hr => (P.reg hr).1
        regW := fun r hr => (P.reg hr).2
        stR := P.stw.1
        stW := P.stw.2
        sc := P.gate (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
        max := by rw [hsc0]; exact P.cscacc.rd _ ⟨hmx.2.1, hmx.2.2⟩ hmx.1
        inq := (P.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
        ib := P.gate (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
        bs := fun sl h => hslot _ sl h (by simp [layout.tcb.SLOT_BUFFER]) },
      ⟨nd1.1, nd2.1, nd2.2⟩,
      nodeAt_aligned P.np (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]),
      node_ne_field P.np (by simp [layout.node.SCHED_ACTION]) P.cT P.tA (by simp)⟩ }

end

/-! ## `acc` -/

theorem io_consumed_ok (s : S) :
    sched.consumed st s = ok (L.mem s (L.nodeAt s (L.cpu s) layout.node.CONSUMED)) := by
  unfold sched.consumed
  simp only [L.cur_cpu_eq, bind_ok, node_get_ok]

set_option maxHeartbeats 1000000 in
/-- **An accepted run's checks.** -/
theorem ioTail_inv {A : Type} {ar : machine.Arch A} {s' : S} {a a' : A} {t : U64} {info : msginfo.MessageInfo}
    {number : I64} (h : ioTail st ar s a t info number = ok (true, s', a')) :
    ∃ nx s1 s2 a1, ioport.is_port_label info.label = ok true ∧
      obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx ∧
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 ∧
      sched.update_timestamp st ar s1 a = ok (s2, a1) ∧
      sched.action st s2 = ok sched.ACTION_RESUME_CURRENT ∧ obj.Tcb.yield_to st t s2 = ok 0#u64 ∧
      info.extra_caps = 0#u64 ∧
      ioport.invocation_ok st s2 t (L.mem s2 (regA t layout.reg.CAP)) info = ok true ∧
      sporadic.sufficient st ar s2 a1 (L.cscW s2) (L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED)) = ok true ∧
      fastpath.schedulable_here st s2 t = ok true := by
  unfold ioTail at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok h
  cases b
  · rw [if_neg Bool.false_ne_true] at h; have e := ok_inj_ff h; simp at e
  rw [if_pos rfl] at h
  obtain ⟨nx, hnx, h⟩ := bind_eq_ok h
  simp only [lift, bind_ok] at h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2, a1⟩, hu, h⟩ := bind_eq_ok h
  simp only [uncurry_apply_pair] at h
  rw [reg_ok] at h; simp only [bind_ok] at h
  rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2)] at h; simp only [bind_ok] at h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  by_cases c3 : (i3 != sched.ACTION_RESUME_CURRENT) = true
  · rw [if_pos c3] at h; have e := ok_inj_ff h; simp at e
  rw [if_neg c3] at h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  by_cases c4 : (i4 != 0#u64) = true
  · rw [if_pos c4] at h; have e := ok_inj_ff h; simp at e
  rw [if_neg c4] at h
  by_cases c5 : (info.extra_caps != 0#u64) = true
  · rw [if_pos c5] at h; have e := ok_inj_ff h; simp at e
  rw [if_neg c5] at h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
  cases b1
  · rw [if_neg Bool.false_ne_true] at h; have e := ok_inj_ff h; simp at e
  rw [if_pos rfl] at h
  rw [io_consumed_ok s2] at h; simp only [bind_ok] at h
  obtain ⟨b2, hb2, h⟩ := bind_eq_ok h
  cases b2
  · rw [if_neg Bool.false_ne_true] at h; have e := ok_inj_ff h; simp at e
  rw [if_pos rfl] at h
  obtain ⟨b3, hb3, h⟩ := bind_eq_ok h
  cases b3
  · rw [if_neg Bool.false_ne_true] at h; have e := ok_inj_ff h; simp at e
  simp only [bne_iff_ne, ne_eq, not_not] at c3 c4 c5
  subst c3 c4
  exact ⟨nx, s1, s2, a1, hb, hnx, hs1, hu, hi3, hi4, c5, hb1, hb2, hb3⟩

theorem flags_ok (s : S) (t : U64) :
    obj.Tcb.flags st t s = ok (L.mem s (core.num.U64.wrapping_add t 3456#u64)) := by
  unfold obj.Tcb.flags
  rw [eq_ok_of_spec Fl4Proofs.P0.Consts.layout.tcb.FLAGS.spec]
  simp only [lift, bind_ok, L.read_eq]

/-- An accepted run reaches the tail. -/
theorem handle_ioport_inv {A : Type} {ar : machine.Arch A} {s' : S} {a a' : A} {number : I64}
    (h : syscall.handle_ioport_local st ar s a number = ok (true, s', a')) :
    ∃ info, msg.msg_info st s (L.curW s) = ok info ∧
      (L.mem s (core.num.U64.wrapping_add (L.curW s) 3456#u64) &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ∧
      (number ≠ fl4_abi.syscall.SysCall → number = fl4_abi.syscall.SysSend) ∧
      ioTail st ar s a (L.curW s) info number = ok (true, s', a') := by
  rw [handle_ioport_local_eq, cur_thread_ok] at h
  simp only [bind_ok] at h
  obtain ⟨info, hi, h⟩ := bind_eq_ok h
  by_cases c0 : (layout.NUM_DOMAINS != 1#u64) = true
  · rw [if_pos c0] at h; have e := ok_inj_ff h; simp at e
  rw [if_neg c0] at h
  rw [flags_ok s (L.curW s)] at h
  simp only [bind_ok, lift] at h
  by_cases c1 : (L.mem s (core.num.U64.wrapping_add (L.curW s) 3456#u64) &&&
      fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; have e := ok_inj_ff h; simp at e
  rw [if_neg c1] at h
  simp only [bne_iff_ne, ne_eq, not_not] at c1
  by_cases c2 : (number != fl4_abi.syscall.SysCall) = true
  · rw [if_pos c2] at h
    by_cases c3 : (number != fl4_abi.syscall.SysSend) = true
    · rw [if_pos c3] at h; have e := ok_inj_ff h; simp at e
    rw [if_neg c3] at h
    simp only [bne_iff_ne, ne_eq, not_not] at c3
    exact ⟨info, hi, c1, fun _ => c3, h⟩
  · rw [if_neg c2] at h
    simp only [bne_iff_ne, ne_eq, not_not] at c2
    exact ⟨info, hi, c1, fun e => absurd c2 e, h⟩

/-- **`PathObl.acc`** for `handle_ioport_local`. -/
theorem io_acc {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {s' : S} {a a' : A}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (h : syscall.handle_ioport_local st ar s a number = ok (true, s', a')) :
    syscall.handle_ioport_local (PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) ar s a number
      = ok (true, s', a') := by
  obtain ⟨info, -, -, -, ht⟩ := handle_ioport_inv h
  obtain ⟨nx, s1, s2, a1, -, -, hs1, hu, -, -, -, -, -, hh⟩ := ioTail_inv ht
  have hsc2 := (here_facts hh).sc
  have w := prefix_writes ar hA P.tp P.np P.cT hs1 hu
  have e1 : L.mem s2 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (field_aligned P.tA (by simp) (by simp)) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s := (P.hcsc (by rw [← e1]; exact hsc2)).symm
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  exact syscall.handle_ioport_local.guard_ent ar hA P.ent
    (P.mid hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2)
    (P.reg (by simp [layout.reg.MSG_INFO])).1
    (P.home (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
    (P.reg (by simp [layout.reg.NEXT_IP])).1 (P.reg (by simp [layout.reg.FAULT_IP])).2 h

end

end Fl4Proofs.P2.PathObl

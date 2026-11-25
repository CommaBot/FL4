/-
# P2 (line p2sl): `SlDecIn` from the ownership map

`slDecIn_of`: the words a declining syscall arm reads (`SlDecIn`, P2/SlHome.lean) are in the
read set `SlRS s`, from the layout (`RegionOK`, `RegionOKX`), the entry facts (`SlPre`, `SlEnt`)
and the homing facts `SlHere`, word by word through `OwnMap.own`:

* node words of this core: `core (cpu)` (`rs_node`); the kernel globals: the gate (`rs_ks`);
* TCB words from offset 192: gate fields, or the home core's of a thread homed here (`rs_tcb`);
  the `TIMER_MIN` thread's deadline: its tree's core (`rs_timer`);
* SC words of an SC homed here (`scAcc_here`, then `ScAcc.head` with P1's refill
  well-formedness at the prefix state, `BXI`'s `SCsOK`);
* the bound notification of the current thread: its home core (`rs_ntfn`);
* the locked endpoint / reply object words: their lock (`slRS_of_lock`).

The prefix state `X` keeps every word read here (`lp_mem`, with `not_slDS_tcb`,
`not_slDS_node`, `not_slDS_reg`: a TCB word other than `FAULT_IP`, a node word other than
`CUR_TIME` / `CONSUMED`, an SC / object word are not prefix words).

`preAcc_of` / `hhd_of`: `SlPre`'s guarded-prefix facts from the same sources: `preG` (`preAcc_here`:
node words, the current thread's flags / `NEXT_IP` / `FAULT_IP`, homed here by `Safe0`) and `hhd`
(the current SC, homed here, `SlHere.cs`); P2/SlAccL.lean assembles `SlPre` (`slPre_of`).

Premises: `SlHere` [J] (each field tagged there with its intended P1/P3 discharge); `SlPreB`
(`SlPre` without its per-word access fields); the rest as `sl_pathObl_ent`.
-/
import Fl4Proofs.P2.SlLay
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}

/-! ## Owners to the read / write sets -/

/-- A word this core owns is in the read and write sets. -/
theorem slRS_of_core {s : S} {x : U64} (ha : Aligned x) (h : own K (L.mem s) x = .core (L.cpu s)) :
    SlRS (st := st) K Locks s x ∧ SlWS (st := st) K Locks s x := by
  refine ⟨⟨ha, Or.inr (Or.inl ?_)⟩, ⟨ha, Or.inr ?_⟩⟩
  · show HeldBy (L.cpu s) (Locks s) (own K (L.mem s) x)
    rw [h]; simp [HeldBy]
  · show HeldBy (L.cpu s) (Locks s) (own K (L.mem s) x)
    rw [h]; simp [HeldBy]

theorem own_tcbW (hX : RegionOKX K) {t o : U64} (ht : K.heap t = some .tcb) (h1 : 192 ≤ o.val)
    (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (m : U64 → U64) :
    own K m (core.num.U64.wrapping_add t o) = tcbOwner m t o.val := by
  obtain ⟨r, d, -⟩ := hX.tcbW t ht o h1 h2 h3
  simp only [own, r, d]

/-- A gate field of a TCB is in the read set. -/
theorem rs_tcb_gate (hX : RegionOKX K) {t o : U64} (ht : K.heap t = some .tcb) (h1 : 192 ≤ o.val)
    (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hg : GateField o.val) {s : S} :
    SlRS (st := st) K Locks s (core.num.U64.wrapping_add t o) :=
  slRS_of_gate (hX.tcbW t ht o h1 h2 h3).2.2 (by rw [own_tcbW hX ht h1 h2 h3]; simp [tcbOwner, hg])

/-- A home-core word of a TCB homed here is in the read and write sets. -/
theorem rs_tcb_home (hX : RegionOKX K) {t o : U64} (ht : K.heap t = some .tcb) (h1 : 192 ≤ o.val)
    (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hg : ¬ GateField o.val) (hT : ¬ TimerField o.val)
    (hG : ¬ GField o.val) {s : S} (hh : L.mem s (affA t) = L.cpu s) :
    SlRS (st := st) K Locks s (core.num.U64.wrapping_add t o) ∧
      SlWS (st := st) K Locks s (core.num.U64.wrapping_add t o) := by
  refine slRS_of_core (hX.tcbW t ht o h1 h2 h3).2.2 ?_
  rw [own_tcbW hX ht h1 h2 h3]
  simp only [tcbOwner, if_neg hg, if_neg hT, if_neg hG]
  rw [← affA_fld, hh]

/-- The deadline of an armed timer in this core's tree is in the read set. -/
theorem rs_timer (hK : RegionOK K) (hX : RegionOKX K) {t : U64} (ht : K.heap t = some .tcb) {s : S}
    (hd : (L.mem s (fld t oTIMER_DEADLINE)).val ≠ 0)
    (hc : treeCore (L.mem s (fld t oTIMER_HEIGHT)) = L.cpu s) :
    SlRS (st := st) K Locks s (core.num.U64.wrapping_add t 3528#u64) := by
  have ha := (hX.tcbW t ht 3528#u64 (by simp) (by simp) (by simp)).2.2
  have e : core.num.U64.wrapping_add t 3528#u64 = fld t oTIMER_DEADLINE := rfl
  refine (slRS_of_core ha ?_).1
  rw [e, own_timer_at hK ht (Or.inl rfl) (L.mem s) (o := 3528) (by simp [GateField]) (by simp [TimerField])]
  simp only [tcbOwner, tOwner]
  rw [if_neg (by simp [GateField]), if_pos (by simp [TimerField]), if_pos hd, hc]

/-- Node words of this core are in the read and write sets. -/
theorem rs_node (hX : RegionOKX K) {T : Set U64} {s : S} (hN : NodePlaced st T s (L.cpu s))
    (hk : L.ksb s = K.ksb) (hc : (L.cpu s).val < K.ncores) {o : U64} (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) :
    SlRS (st := st) K Locks s (L.nodeAt s (L.cpu s) o) ∧ SlWS (st := st) K Locks s (L.nodeAt s (L.cpu s) o) := by
  have v := nodeAt_val hN ho
  have hr : region K (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) :=
    hX.node _ _ ⟨hc, by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega,
      by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega⟩
  exact slRS_of_core (nodeAt_aligned hN ho h8) (by simp only [own, hr])

/-- The kernel globals below the nodes are in the read set. -/
theorem rs_ks (hX : RegionOKX K) {T : Set U64} {s : S} (hN : NodePlaced st T s (L.cpu s))
    (hk : L.ksb s = K.ksb) {o : U64} (ho : o.val < 13568) (h8 : o.val % 8 = 0) :
    SlRS (st := st) K Locks s (core.num.U64.wrapping_add (L.ksb s) o) := by
  have hf := hN.fits
  have ha := hN.align
  simp only [LawfulStore.nodeBase] at hf ha
  have e : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine slRS_of_gate (by unfold Aligned; rw [e]; omega) ?_
  simp only [own, hX.ks _ (by rw [e, ← hk]; omega) (by rw [e, ← hk]; omega)]

/-- A scheduling context homed here: every word readable, ring and `CONSUMED` writable. -/
theorem scAcc_here (hX : RegionOKX K) {s : S} {sc : U64} {z : Nat} (hz : K.heap sc = some (.sc z))
    (hc : L.mem s (fld sc 16#u64) = L.cpu s) :
    ScAcc (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) sc z := by
  obtain ⟨a8, h128, hfit⟩ := hX.scP sc z hz
  have osc : ∀ b, InSC sc z b → b.val ≠ sc.val + 16 → own K (L.mem s) b = .core (L.cpu s) := by
    intro b hb hne
    simp only [own, hX.scW sc z hz b hb, if_neg hne, hc]
  refine ⟨fun b ha hb => ?_, fun b ha hb => ?_, ?_⟩
  · by_cases e : b.val = sc.val + 16
    · exact slRS_of_gate ha (by simp only [own, hX.scW sc z hz b hb, if_pos e])
    · exact (slRS_of_core ha (osc b hb e)).1
  · obtain ⟨r1, r2⟩ := hb
    exact (slRS_of_core ha (osc b ⟨by omega, r2⟩ (by omega))).2
  · have e : (core.num.U64.wrapping_add sc layout.sc.CONSUMED).val = sc.val + 8 := by
      simp [layout.sc.CONSUMED, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    exact (slRS_of_core (by unfold Aligned; rw [e]; omega)
      (osc _ ⟨by rw [e]; omega, by rw [e]; omega⟩ (by rw [e]; omega))).2

/-- A small aligned offset into a heap SC: its value, alignment and region. -/
theorem sc_off (hX : RegionOKX K) {sc : U64} {z : Nat} (hz : K.heap sc = some (.sc z)) {o : U64}
    (ho : o.val < 128) (h8 : o.val % 8 = 0) :
    (core.num.U64.wrapping_add sc o).val = sc.val + o.val ∧ Aligned (core.num.U64.wrapping_add sc o) ∧
      InSC sc z (core.num.U64.wrapping_add sc o) ∧ region K (core.num.U64.wrapping_add sc o) = .sc sc := by
  obtain ⟨a8, h128, hfit⟩ := hX.scP sc z hz
  have e : (core.num.U64.wrapping_add sc o).val = sc.val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hin : InSC sc z (core.num.U64.wrapping_add sc o) := ⟨by rw [e]; omega, by rw [e]; omega⟩
  exact ⟨e, by unfold Aligned; rw [e]; omega, hin, hX.scW sc z hz _ hin⟩

/-- A word of the current thread's bound notification (bound back to it) is in the read set. -/
theorem rs_ntfn (hX : RegionOKX K) {s : S} {t nt o : U64} (hn : K.heap nt = some .ntfn)
    (hb : L.mem s (fld nt 24#u64) = t) (ht : K.heap t = some .tcb) (hh : L.mem s (affA t) = L.cpu s)
    (ho : o.val < 64) (h8 : o.val % 8 = 0) (h24 : o.val ≠ 24) :
    SlRS (st := st) K Locks s (core.num.U64.wrapping_add nt o) := by
  obtain ⟨r, d, a⟩ := hX.ntW nt hn o ho h8
  refine (slRS_of_core a ?_).1
  simp only [own, r, d, ntfnOwner, if_neg h24, hb, ht, if_true]
  rw [← affA_fld, hh]

/-! ## Words the prefix does not write -/

theorem fip_eq {T : Set U64} {s : S} (hT : TcbPlaced T) (hcT : L.curW s ∈ T) :
    ∃ KF : U64, KF.val = 392 ∧ regA (L.curW s) layout.reg.FAULT_IP = core.num.U64.wrapping_add (L.curW s) KF := by
  obtain ⟨KF, hKF, eKF⟩ := regA_eq (hT _ hcT) (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
  exact ⟨KF, by rw [hKF]; simp [layout.reg.FAULT_IP], eKF⟩

theorem not_slDS_node {T : Set U64} {s : S} (hN : NodePlaced st T s (L.cpu s)) (hT : TcbPlaced T)
    (hcT : L.curW s ∈ T) {o : U64} (ho : o.val < 4288) (h1 : o.val ≠ 48) (h2 : o.val ≠ 40) :
    ¬ SlDS (L := L) s (L.nodeAt s (L.cpu s) o) := by
  have v := nodeAt_val hN ho
  rintro (e | e | e)
  · obtain ⟨KF, hKF, eKF⟩ := fip_eq hT hcT
    have hv := congrArg (fun x : U64 => x.val) (e.trans eKF)
    rw [v, field_val (hT _ hcT) (by omega)] at hv
    rcases hN.disj _ hcT with h | h <;> omega
  · have hv := congrArg (fun x : U64 => x.val) e
    rw [v, nodeAt_val hN (by simp [layout.node.CUR_TIME])] at hv
    simp [layout.node.CUR_TIME] at hv <;> omega
  · have hv := congrArg (fun x : U64 => x.val) e
    rw [v, nodeAt_val hN (by simp [layout.node.CONSUMED])] at hv
    simp [layout.node.CONSUMED] at hv <;> omega

/-- The prefix words lie in this core's node or the current TCB. -/
theorem slDS_region (hX : RegionOKX K) {T : Set U64} {s : S} (hN : NodePlaced st T s (L.cpu s))
    (hT : TcbPlaced T) (hcT : L.curW s ∈ T) (hc : K.heap (L.curW s) = some .tcb)
    (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores) {b : U64} (h : SlDS (L := L) s b) :
    region K b = .node (L.cpu s) ∨
      (region K b = .tcb (L.curW s) ∧ b.val = (L.curW s).val + 392) := by
  have rn : ∀ o : U64, o.val < 4288 → region K (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) := fun o ho =>
    hX.node _ _ ⟨hcp, by rw [nodeAt_val hN ho]; simp only [LawfulStore.nodeBase, hk]; omega,
      by rw [nodeAt_val hN ho]; simp only [LawfulStore.nodeBase, hk]; omega⟩
  rcases h with e | e | e
  · obtain ⟨KF, hKF, eKF⟩ := fip_eq hT hcT
    obtain ⟨r, d, -⟩ := hX.tcbW _ hc KF (by omega) (by omega) (by omega)
    rw [e, eKF]
    exact Or.inr ⟨r, by rw [field_val (hT _ hcT) (by omega)]; omega⟩
  · rw [e]; exact Or.inl (rn _ (by simp [layout.node.CUR_TIME]))
  · rw [e]; exact Or.inl (rn _ (by simp [layout.node.CONSUMED]))

/-- A TCB word other than `FAULT_IP` is not a prefix word. -/
theorem not_slDS_tcb (hX : RegionOKX K) {T : Set U64} {s : S} (hN : NodePlaced st T s (L.cpu s))
    (hT : TcbPlaced T) (hcT : L.curW s ∈ T) (hc : K.heap (L.curW s) = some .tcb)
    (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores) {t o : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hne : o.val ≠ 392) :
    ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun h => by
  obtain ⟨r, d, -⟩ := hX.tcbW t ht o h1 h2 h3
  rcases slDS_region hX hN hT hcT hc hk hcp h with e | ⟨e, v⟩
  · rw [r] at e; cases e
  · rw [r] at e
    cases e
    omega

/-- A word in neither a node nor the current TCB is not a prefix word. -/
theorem not_slDS_reg (hX : RegionOKX K) {T : Set U64} {s : S} (hN : NodePlaced st T s (L.cpu s))
    (hT : TcbPlaced T) (hcT : L.curW s ∈ T) (hc : K.heap (L.curW s) = some .tcb)
    (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores) {b : U64}
    (h1 : ∀ c, region K b ≠ .node c) (h2 : region K b ≠ .tcb (L.curW s)) : ¬ SlDS (L := L) s b := fun h => by
  rcases slDS_region hX hN hT hcT hc hk hcp h with e | ⟨e, -⟩
  · exact h1 _ e
  · exact h2 e

/-! ## The homing facts -/

variable (K) (Z : U64 → Nat) (Scs : Set U64) in
/-- The scheduling context `sc` is a heap SC of size `Z sc`, one of P1's SCs `Scs`, active, and
homed on this core (its `CORE` word). -/
def ScHere (s : S) (sc : U64) : Prop :=
  K.heap sc = some (.sc (Z sc)) ∧ sc ∈ Scs ∧ L.rmax s sc ≠ 0#u64 ∧ L.mem s (fld sc 16#u64) = L.cpu s

/-- **The layout / homing facts a declining syscall arm needs** [J], at the entry state `s`. -/
structure SlHere (K : KLayout) (Z : U64 → Nat) (Scs : Set U64) (found : U64 × U64) (s : S) : Prop where
  /-- [J] the store's kernel base is the layout's (P3: the concrete store's `ks_base` is the
  `KLayout` it is placed by). -/
  ksb : L.ksb s = K.ksb
  /-- [J] this core's index is a node of the layout (P3 boot: `cur_cpu < ncores`). -/
  cpu : (L.cpu s).val < K.ncores
  /-- [J] the node's `TIMER_MIN` thread, when set, is a heap TCB armed in this core's timer
  tree (P1 timer-tree invariant: `TIMER_MIN` is the minimum of this core's tree, whose heights
  carry the core in `>> 8`). -/
  tm : L.mem s (tmA (L := L) s) ≠ 0#u64 → K.heap (L.mem s (tmA (L := L) s)) = some .tcb ∧
    (L.mem s (fld (L.mem s (tmA (L := L) s)) oTIMER_DEADLINE)).val ≠ 0 ∧
    treeCore (L.mem s (fld (L.mem s (tmA (L := L) s)) oTIMER_HEIGHT)) = L.cpu s
  /-- [J] the node's release-queue head, when set, is a heap TCB whose SC is homed here (P1
  release-queue invariant: queued threads have active SCs of this core). -/
  rh : L.mem s (rhA (L := L) s) ≠ 0#u64 → K.heap (L.mem s (rhA (L := L) s)) = some .tcb ∧
    ScHere (st := st) K Z Scs s (L.mem s (scA (L.mem s (rhA (L := L) s))))
  /-- [J] the node's current SC (`CUR_SC`) is homed here (P1: `CUR_SC` is an active SC of
  this core). -/
  cs : ScHere (st := st) K Z Scs s (L.cscW s)
  /-- [J] ReplyRecv: the current thread's SC is homed here (P1: the running thread has an
  active SC on its core). -/
  csc : ¬ SlTrap st s → ScHere (st := st) K Z Scs s (L.mem s (scA (L.curW s)))
  /-- [J] ReplyRecv: the replied thread, homed here, has its nonzero SC homed here (P1: a
  thread's bound SC is on the thread's core). -/
  usc : ¬ SlTrap st s → SlLive st found.1 s → L.mem s (affA (slThr st found.1 s)) = L.cpu s →
    L.mem s (scA (slThr st found.1 s)) ≠ 0#u64 →
    ScHere (st := st) K Z Scs s (L.mem s (scA (slThr st found.1 s)))
  /-- [J] ReplyRecv: the current thread's bound notification, when set, is a heap notification
  bound back to it (P1 `BoundInv`). -/
  ntf : ¬ SlTrap st s → L.mem s (boundA (L.curW s)) ≠ 0#u64 →
    K.heap (L.mem s (boundA (L.curW s))) = some .ntfn ∧
    L.mem s (fld (L.mem s (boundA (L.curW s))) 24#u64) = L.curW s
  /-- [J] ReplyRecv: fl4-sync's endpoint is a heap endpoint (`fastpath::reply_caps`). -/
  ep : ¬ SlTrap st s → K.heap found.2 = some .ep

variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **`PreAcc` for the read / write sets**: the prefix's words (this core's node, the current
thread's flags, `NEXT_IP`, `FAULT_IP`) from the layout, the current thread homed here. -/
theorem preAcc_here (hX : RegionOKX K) {T : Set U64} {s : S} (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T) (hc : K.heap (L.curW s) = some .tcb)
    (hcA : L.mem s (affA (L.curW s)) = L.cpu s) (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores) :
    PreAcc (L := L) (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) s := by
  obtain ⟨KN, hKN, eKN⟩ := regA_eq (hT _ hcT) (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
  have hKN' : KN.val = 368 := by rw [hKN]; simp [layout.reg.NEXT_IP]
  obtain ⟨KF, hKF, eKF⟩ := fip_eq hT hcT
  refine ⟨fun o h1 h2 => rs_node hX hN hk hcp h1 h2,
    (rs_tcb_home hX hc (o := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) (by simp [GField]) hcA).1, ?_, ?_⟩
  · rw [eKN]
    exact (rs_tcb_home hX hc (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
      (by simp only [TimerField]; omega) (by simp only [GField]; omega) hcA).1
  · rw [eKF]
    exact (rs_tcb_home hX hc (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
      (by simp only [TimerField]; omega) (by simp only [GField]; omega) hcA).2

theorem preAcc_of (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K Z Scs found s) :
    PreAcc (L := L) (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) s :=
  preAcc_here hX E.hT E.hN E.hcT E.hSt.1 E.hSt.2.1 Hh.ksb Hh.cpu

/-- The words both declining arms read before their decided thread's, at the prefix state. -/
structure SlCom (R : U64 → Prop) (X : S) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)
  bm : RdBitmap (L := L) R X
  tm : L.mem X (tmA (L := L) X) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64)
  rh : L.mem X (rhA (L := L) X) ≠ 0#u64 → R (scA (L.mem X (rhA (L := L) X))) ∧
    RdHead (L := L) R X (L.mem X (scA (L.mem X (rhA (L := L) X))))

/-- The head refill of an SC homed here is in the read set at the prefix state. -/
theorem rdHead_here (hA : P0.ArchTotal ar) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K Z Scs found s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    {sc : U64} (hs : ScHere (st := st) K Z Scs s sc) : RdHead (L := L) (SlRS (st := st) K Locks s) X sc := by
  obtain ⟨hz, hin, hmx, hco⟩ := hs
  obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
    (by simp [layout.sc.REFILL_MAX])
  have em : L.mem X (maxA sc) = L.mem s (maxA sc) :=
    lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
      (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
  have hW : RefillsWF st X sc (Z sc) :=
    ((E.hI a X a1 LP).2.2.2.2.all sc hin).1 (by show L.mem X (maxA sc) ≠ 0#u64; rw [em]; exact hmx)
  exact ScAcc.head (scAcc_here hX hz hco) hW

/-- **The common words at the prefix state.** -/
theorem slCom_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K Z Scs found s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    SlCom (L := L) (SlRS (st := st) K Locks s) X := by
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → SlRS (st := st) K Locks s (L.nodeAt X (L.cpu X) o) :=
    fun o h1 h2 => by rw [nX]; exact (rs_node hX E.hN Hh.ksb Hh.cpu h1 h2).1
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 → o.val ≠ 40 →
      L.mem X (L.nodeAt X (L.cpu X) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o h1 h2 h3 h4 => by
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN h1 h2) (not_slDS_node E.hN E.hT E.hcT h1 h3 h4)
  have eTm : L.mem X (tmA (L := L) X) = L.mem s (tmA (L := L) s) :=
    eN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) :=
    eN _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  refine ⟨nd, ?_, ?_, ⟨nd _ (by simp [l1Off]) (by simp [l1Off]), fun inv hinv => nd _ (by simp; omega)
    (by simp <;> omega)⟩, fun h => ?_, fun h => ?_⟩
  · rw [kX]; exact rs_ks hX E.hN Hh.ksb (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  · rw [kX]; exact rs_ks hX E.hN Hh.ksb (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  · rw [eTm] at h ⊢
    obtain ⟨ht, hd, hc⟩ := Hh.tm h
    exact rs_timer hK hX ht hd hc
  · rw [eRh] at h ⊢
    obtain ⟨ht, hs⟩ := Hh.rh h
    have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu ht (by simp) (by simp) (by simp) (by simp))
    rw [eS]
    exact ⟨rs_tcb_gate hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
      rdHead_here ar hA hX E Hh LP hs⟩

set_option maxHeartbeats 4000000 in
/-- **`SlDecIn` from the ownership map.** -/
theorem slDecIn_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hh : SlHere (st := st) K Z Scs found s) :
    SlDecIn (st := st) ar K Locks found s := by
  have I : SlThrIn (st := st) K Locks found.1 s := slThrIn_of hK hX (preAcc_of ar hX E Hh) E.hSt.1 N
  have hc := E.hSt.1
  have hcA : L.mem s (affA (L.curW s)) = L.cpu s := E.hSt.2.1
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc Hh.ksb Hh.cpu ht h1 h2 h3 h4
  refine ⟨fun hS a X a1 LP => ?_, fun hS lv hh a X a1 LP => ?_, fun hS a X a1 LP => ?_,
    fun hS lv hh a X a1 LP => ?_⟩
  · -- the trap arm, apart from the receiver
    have C := slCom_of ar hA hK hX E Hh LP
    obtain ⟨f0, f8, d0, d8⟩ := I.fh hS
    have ecap : obj.Slot.cap st (fhA (L := L) s) X = obj.Slot.cap st (fhA (L := L) s) s :=
      cap_congr (lp_mem ar hA E.hT E.hN E.hcT LP f0.1 d0) (lp_mem ar hA E.hT E.hN E.hcT LP f8.1 d8)
    refine ⟨C.nd, C.dt, C.cd, C.bm, C.tm, C.rh, ⟨f0, f8⟩, fun ptr b x y g gr hcap => ?_⟩
    have hcap' : obj.Slot.cap st (fhA (L := L) s) s = ok (capability.Cap.Endpoint ptr b x y g gr) := by
      rw [← ecap]; exact hcap
    have hp : resPtr (obj.Slot.cap st (fhA (L := L) s) s) = ptr := by rw [resPtr_ok hcap']; rfl
    obtain ⟨r1, -, r2, -⟩ := I.eh hS ⟨ptr, b, x, y, g, gr, hcap'⟩
    rw [hp] at r1 r2
    exact ⟨r2, r1⟩
  · -- the receiver, homed here
    have ht := N.hthr lv
    refine ⟨?_, (I.af lv).1, fun _ => ⟨rs_tcb_gate hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
      rs_tcb_gate hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
      (rs_tcb_home hX ht (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField]) hh).1,
      rs_tcb_gate hX ht (by simp) (by simp) (by simp) (by simp [GateField])⟩⟩
    exact (rs_tcb_home hX ht (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) (by simp [GField]) hh).1
  · -- the ReplyRecv arm, apart from the replied thread
    have C := slCom_of ar hA hK hX E Hh LP
    obtain ⟨-, -, aT, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    have home : ∀ {o : U64}, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 → ¬ GateField o.val →
        ¬ TimerField o.val → ¬ GField o.val →
        SlRS (st := st) K Locks s (core.num.U64.wrapping_add (L.curW s) o) := fun h1 h2 h3 h4 h5 h6 =>
      (rs_tcb_home hX hc h1 h2 h3 h4 h5 h6 hcA).1
    have gate : ∀ {o : U64}, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 → GateField o.val →
        SlRS (st := st) K Locks s (core.num.U64.wrapping_add (L.curW s) o) := fun h1 h2 h3 h4 =>
      rs_tcb_gate hX hc h1 h2 h3 h4
    obtain ⟨hz, -, -, hco⟩ := Hh.csc hS
    have eS : L.mem X (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
      aT _ E.hcT 3464#u64 (by simp) (by simp) (by simp)
    obtain ⟨KM, hKM, eKM⟩ := regA_eq (E.hT _ E.hcT) (r := layout.reg.MSG_INFO)
      (by simp [layout.reg.MSG_INFO, layout.reg.RSI])
    have hKM' : KM.val = 264 := by rw [hKM]; simp [layout.reg.MSG_INFO, layout.reg.RSI]
    obtain ⟨r1, a1'⟩ := hX.rpW _ (N.hrp hS) layout.reply.NEXT (by simp [layout.reply.NEXT])
      (by simp [layout.reply.NEXT])
    obtain ⟨r2, a2⟩ := hX.epW _ (Hh.ep hS) layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE])
    refine ⟨C.nd, C.dt, C.cd, C.bm, C.tm, C.rh, ?_, gate (by simp) (by simp) (by simp) (by simp [GateField]),
      ?_, home (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField]) (by simp [GField]),
      ?_, gate (by simp) (by simp) (by simp) (by simp [GateField]),
      gate (by simp) (by simp) (by simp) (by simp [GateField]), fun nt hnt hne => ?_, (I.rt hS).1,
      slRS_of_lock a1' r1 (N.lrp hS), slRS_of_lock a2 r2 (E.hlk hS)⟩
    · rw [stA_eq]
      exact home (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField]) (by simp [GField])
    · rw [eS]
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact (scAcc_here hX hz hco).rd _ am hin
    · rw [eKM]
      exact home (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
        (by simp only [TimerField]; omega) (by simp only [GField]; omega)
    · have e1 := (eq_of_spec_fd (obj.Tcb.bound_ntfn.val X (L.curW s))).symm.trans hnt
      have en : nt = L.mem s (boundA (L.curW s)) := by
        rw [← ok_inj_ff e1]; exact aT _ E.hcT 3368#u64 (by simp) (by simp) (by simp)
      have hne' : L.mem s (boundA (L.curW s)) ≠ 0#u64 := by
        rw [← en]; intro h0; rw [h0] at hne; simp at hne
      obtain ⟨hn, hb⟩ := Hh.ntf hS hne'
      rw [en]
      exact ⟨rs_ntfn hX hn hb hc hcA (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE])
          (by simp [layout.ntfn.TAIL_STATE]),
        rs_ntfn hX hn hb hc hcA (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])⟩
  · -- the replied thread, homed here
    have ht := N.hthr lv
    refine ⟨?_, (rs_tcb_home hX ht (o := 3376#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField]) hh).1,
      rs_tcb_gate hX ht (by simp) (by simp) (by simp) (by simp [GateField]), (I.af lv).1,
      fun _ => ⟨rs_tcb_gate hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
        (rs_tcb_home hX ht (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
          (by simp [TimerField]) (by simp [GField]) hh).1,
        rs_tcb_gate hX ht (by simp) (by simp) (by simp) (by simp [GateField]), fun usc eu hne => ?_⟩⟩
    · rw [stA_eq]
      exact (rs_tcb_home hX ht (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField]) hh).1
    · have eU : L.mem X (scA (slThr st found.1 s)) = L.mem s (scA (slThr st found.1 s)) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
          (nT ht (by simp) (by simp) (by simp) (by simp))
      have e1 : usc = L.mem s (scA (slThr st found.1 s)) := by
        rw [tcb_sc_ok] at eu; rw [← ok_inj_ff eu, eU]
      subst e1
      exact rdHead_here ar hA hX E Hh LP (Hh.usc hS lv hh hne)

/-- **`SlPre.hhd` from the layout**: the current SC (unchanged by the prefix) is homed here. -/
theorem hhd_of (hA : P0.ArchTotal ar) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K Z Scs found s) {a X a1 csc} (LP : LocalPre (st := st) ar s a (X, a1))
    (hcs : sched.cur_sc st X = ok csc) : RdHead (L := L) (SlRS (st := st) K Locks s) X csc := by
  obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have e : csc = L.cscW s := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at hcs
    rw [← ok_inj_ff hcs]; exact ecs
  subst e
  exact rdHead_here ar hA hX E Hh LP Hh.cs

end

end Fl4Proofs.P2.PathObl

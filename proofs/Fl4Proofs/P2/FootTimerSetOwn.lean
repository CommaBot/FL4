/-
# P2: the words an accepted `TCB_SetTimer` local path touches are its own

With the ownership map `OwnMap.own K`:

* `st_rd_own`: at the entry state of an accepted run (`StOk`), every word of `StRd` is readable (`RPerm`: this
  core's or the gate's);
* `st_wr_own`: every aligned word of `StWr` is this core's (`WPerm`);
* `set_timer_acc_own`: `PathObl.acc` for `ReadSet` / `WriteSet` = `MaxR` / `MaxW` (the aligned words
  that the path may read / write at the entry state), so that `read_own`, `write_own`, `aligned` and `rs_aligned`
  hold by construction.

The release head's thread is on this core (P1's release queue); its SC is too by `AffSc` (p2j, `P2/InvAff`).

Premises:
* `StLay` [J]: layout facts (as `OwnMap.RegionOK`, from P1's typed-heap disjointness): which region this core's
  node words, the TCBs' words above their slots, the SCs' words and the kernel's two domain words lie in;
* `hAff` [J] (p2j `P2/InvAff`, `AffSc`): a bound SC's `CORE` is its thread's `AFFINITY`.
-/
import Fl4Proofs.P2.FootTimerSetAcc
import Fl4Proofs.P2.MoveTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Classical
open Fl4Proofs.P2.PathObl (guard RPerm WPerm HeldBy GateOnly)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- **Layout facts** [J] (module docstring) at the entry state `s`. -/
structure StLay (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T Scs : Set U64) (Z : U64 → Nat) (s : S) :
    Prop where
  nd : ∀ o : U64, o.val < 4288 → region K (L.nodeAt s (L.cpu s) o) = .node (L.cpu s)
  tcb : ∀ t ∈ T, ∀ k : U64, 256 ≤ k.val → k.val < 4096 → region K (fld t k) = .tcb t
  sc : ∀ p ∈ Scs, ∀ b, InSC p (Z p) b → region K b = .sc p
  dom : region K (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) = .none
  dtm : region K (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME) = .none
  domA : Aligned (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)
  dtmA : Aligned (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME)

theorem StLay.own_node {s : S} (h : StLay K st T Scs Z s) (m : U64 → U64) {o : U64} (ho : o.val < 4288) :
    own K m (L.nodeAt s (L.cpu s) o) = .core (L.cpu s) := by
  simp only [own, h.nd o ho]

theorem StLay.own_tcb {s : S} (h : StLay K st T Scs Z s) (hT : TcbPlaced T) (m : U64 → U64) {t k : U64} (ht : t ∈ T)
    (h1 : 256 ≤ k.val) (h2 : k.val < 4096) : own K m (fld t k) = tcbOwner m t k.val := by
  have e : (fld t k).val - t.val = k.val := by unfold fld; rw [field_val (hT t ht) h2]; omega
  simp only [own, h.tcb t ht k h1 h2, e]

/-- A key's timer words are this core's. -/
theorem key_own {s : S} (hL : StLay K st T Scs Z s) (hT : TcbPlaced T) {target y : U64} (ho : StOk st Scs s target)
    (hy : StKeys st T s target y) {k : U64} (h1 : 3528 ≤ k.val) (h2 : k.val < 3576) (h8 : k.val % 8 = 0) :
    own K (L.mem s) (core.num.U64.wrapping_add y k) = .core (L.cpu s) := by
  have e := hL.own_tcb hT (L.mem s) hy.1 (k := k) (by omega) (by omega)
  unfold fld at e
  rw [e]
  have g : ¬ GateField k.val := by unfold GateField; omega
  have tf : TimerField k.val := by unfold TimerField; omega
  rw [tcbOwner, if_neg g, if_pos tf, tOwner]
  have arm : FootLtArmed st s (L.cpu s) y → (Owner.core (treeCore (L.mem s (fld y oTIMER_HEIGHT))) : Owner U64 U64) =
      .core (L.cpu s) := fun h => by
    have e2 := h.2
    rw [Nat.shiftRight_eq_div_pow] at e2
    have e3 := MoveTimer.treeCore_of (c := L.cpu s) e2
    exact congrArg Owner.core e3
  rcases hy.2 with rfl | ha
  · split
    · rename_i hd
      refine arm ⟨fun h => hd ?_, ho.town.resolve_left fun h => hd ?_⟩
      · show (L.mem s (tdA y)).val = 0
        rw [h]; rfl
      · show (L.mem s (tdA y)).val = 0
        rw [h]; rfl
    · exact congrArg Owner.core ho.taff
  · rw [if_pos (show (L.mem s (fld y oTIMER_DEADLINE)).val ≠ 0 from fun h => ha.1 (UScalar.eq_of_val_eq h))]
    exact arm ha

theorem tw_own {s : S} (hL : StLay K st T Scs Z s) (hT : TcbPlaced T) {target w : U64} (ho : StOk st Scs s target)
    (h : TW st s (L.cpu s) (StKeys st T s target) w) : own K (L.mem s) w = .core (L.cpu s) := by
  rcases h with ⟨z, hz, k, h1, h2, h3, rfl⟩ | ⟨o, ho', h8, rfl⟩
  · exact key_own hL hT ho hz h1 h2 h3
  · exact hL.own_node _ ho'

/-- A caller's word outside its timer fields, the caller on this core and not blocked: the gate's or this core's. -/
theorem caller_own' {s : S} (hL : StLay K st T Scs Z s) (hT : TcbPlaced T) (hct : L.curW s ∈ T) {k : U64}
    (aff : L.mem s (affA (L.curW s)) = L.cpu s) (q : ¬ QueuedState (L.mem s (stA (L.curW s))))
    (r : ¬ ReplyState (L.mem s (stA (L.curW s)))) (h1 : 256 ≤ k.val) (h2 : k.val < 4096)
    (h3 : k.val < 3528 ∨ 3576 ≤ k.val) :
    own K (L.mem s) (core.num.U64.wrapping_add (L.curW s) k) =
      (if GateField k.val then Owner.gate else Owner.core (L.cpu s)) := by
  have e := hL.own_tcb hT (L.mem s) hct (k := k) h1 h2
  unfold fld at e
  rw [e]
  have ea : L.mem s (fld (L.curW s) oAFFINITY) = L.cpu s := aff
  have es : fld (L.curW s) oSTATE = stA (L.curW s) := by rw [stA_eq]; rfl
  have ht : ¬ TimerField k.val := by unfold TimerField; omega
  rw [tcbOwner, if_neg ht, ea, es]
  simp only [gOwner, if_neg q, if_neg r, ite_self]

/-- A running caller's word: the gate's or this core's. -/
theorem caller_own {s : S} (hL : StLay K st T Scs Z s) (hT : TcbPlaced T) (hct : L.curW s ∈ T) {target k : U64}
    (ho : StOk st Scs s target) (h1 : 256 ≤ k.val) (h2 : k.val < 4096) (h3 : k.val < 3528 ∨ 3576 ≤ k.val) :
    own K (L.mem s) (core.num.U64.wrapping_add (L.curW s) k) =
      (if GateField k.val then Owner.gate else Owner.core (L.cpu s)) :=
  caller_own' hL hT hct ho.aff (by rw [ho.run]; simp [QueuedState, sched.TS_RUNNING])
    (by rw [ho.run]; simp [ReplyState, sched.TS_RUNNING]) h1 h2 h3

/-- An SC's word: the gate's (`CORE`) or its core's. -/
theorem sc_own {s : S} (hL : StLay K st T Scs Z s) {p b : U64} (hp : p ∈ Scs) (hb : InSC p (Z p) b)
    (hc : L.mem s (scCoreA p) = L.cpu s) :
    own K (L.mem s) b = if b.val = p.val + 16 then Owner.gate else Owner.core (L.cpu s) := by
  have e : fld p 16#u64 = scCoreA p := by
    unfold fld scCoreA
    rw [UScalar.eq_of_val_eq (show (16#u64 : U64).val = layout.sc.CORE.val by simp [layout.sc.CORE])]
  simp only [own, hL.sc p hp b hb, e, hc]

theorem held_core {c : U64} {lk : U64 → Prop} {o : Owner U64 U64} (h : o = .core c) : HeldBy c lk o := by
  subst h; exact rfl

/-- **Every word of `StRd` is readable** at an accepted run's entry. -/
theorem st_rd_own {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    {target w : U64} (htg : target ∈ T) (ho : StOk st Scs s target) {lk : U64 → Prop}
    (h : StRd st T Z s target w) : RPerm (own K) (L.cpu s) lk (L.mem s) w := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have gate : ∀ {x : U64} {k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → GateField k.val →
      RPerm (own K) (L.cpu s) lk (L.mem s) (core.num.U64.wrapping_add x k) := fun hx h1 h2 hg =>
    Or.inr (by
      have e := hL.own_tcb hT (L.mem s) hx h1 h2
      unfold fld at e
      unfold GateOnly; rw [e, tcbOwner, if_pos hg])
  have scw : ∀ {p b : U64}, p ∈ Scs → InSC p (Z p) b → L.mem s (scCoreA p) = L.cpu s →
      RPerm (own K) (L.cpu s) lk (L.mem s) b := fun hp hb hc => by
    have e := sc_own hL hp hb hc
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  rcases h with h | ⟨k, h1, h2, -, h4, rfl⟩ | rfl | rfl | rfl | h | ⟨hne, rfl | h⟩
  · exact Or.inl (held_core (tw_own hL hT ho h))
  · have e := caller_own hL hT h0.curT ho h1 h2 h4
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  · exact gate htg (by simp) (by simp) (Or.inl (by simp))
  · exact Or.inr (by unfold GateOnly; simp only [own, hL.dom])
  · exact Or.inr (by unfold GateOnly; simp only [own, hL.dtm])
  · exact scw ho.csc h ho.core
  · obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne
    exact gate r1 (by simp) (by simp) (by simp [GateField])
  · obtain ⟨r1, r2, r3, r4, -⟩ := rel_facts hI hne
    exact scw r4 h (by rw [hAff _ r1 r3, r2])

/-- **Every aligned word of `StWr` is this core's** at an accepted run's entry. -/
theorem st_wr_own {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    {target w : U64} (ho : StOk st Scs s target) {lk : U64 → Prop}
    (h : StWr st T Z s target w) : WPerm (own K) (L.cpu s) lk (L.mem s) w := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hq := scq_of hI.2.2.1.1 hI.2.2.2.2 ho.csc
  rcases h with h | ⟨k, h1, h2, -, rfl⟩ | h | rfl
  · exact held_core (tw_own hL hT ho h)
  · have e := caller_own hL hT h0.curT ho h1 (by omega) (Or.inl (by omega))
    rw [if_neg (show ¬ GateField k.val by unfold GateField; omega)] at e
    exact held_core e
  · have e := sc_own hL ho.csc h.inSC ho.core
    rw [if_neg (by unfold InRing at h; omega)] at e
    exact held_core e
  · have e := sc_own hL ho.csc hq.2.2.1.1 ho.core
    obtain ⟨hP, hz⟩ := hI.2.2.1.1.sc _ ho.csc
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    rw [if_neg (by rw [hv, hcv]; omega)] at e
    exact held_core e

/-- The maximal `ReadSet`: the aligned words the path may read at the entry state. -/
def MaxR (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (lk : S → U64 → Prop) (s : S) (w : U64) : Prop :=
  RPerm (own K) (L.cpu s) (lk s) (L.mem s) w ∧ Aligned w

/-- The maximal `WriteSet`: the aligned words the path may write at the entry state. -/
def MaxW (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (lk : S → U64 → Prop) (s : S) (w : U64) : Prop :=
  WPerm (own K) (L.cpu s) (lk s) (L.mem s) w ∧ Aligned w

/-- **`PathObl.acc` for `TCB_SetTimer`** (module docstring). -/
theorem set_timer_acc_own {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64}
    {target : U64} {lk : S → U64 → Prop} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (htg : target ∈ T)
    (hL : StLay K st T Scs Z s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (true, s', a')) :
    localtimer.handle_set_timer_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a n target =
      ok (true, s', a') :=
  set_timer_acc ar hA hI htg
    (fun ho _ ha hw => ⟨st_rd_own hI hL hAff htg ho hw, ha⟩)
    (fun ho _ ha hw => ⟨st_wr_own hI hL ho hw, ha⟩)
    (fun ho => ⟨st_rd_own hI hL hAff htg ho (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hL.domA⟩)
    (fun ho => ⟨st_rd_own hI hL hAff htg ho (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), hL.dtmA⟩) h

end

end Fl4Proofs.P2

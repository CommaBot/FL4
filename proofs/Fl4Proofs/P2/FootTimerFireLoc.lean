/-
# P2 (p2lf): the words of this core, and of the plan's locks, at the timer interrupt's entry

A waking fire run reads and writes words of threads other than the current one (the woken thread, ready-queue
members, the thread `schedule` chooses) and of their scheduling contexts. Rather than naming each, the read / write
sets of the waking case are stated broadly at the entry state `s`:

* `LocT`: a thread of `T` homed on this core (`AFFINITY = cpu`);
* `LocRd`: this core's node words; a local thread's words outside its timer fields and queue links; a word of an SC
  of `Scs` whose `CORE` is this core;
* `LocWr`: the same without the gate's words (gate fields of a TCB, an SC's `CORE`);
* `LkW Lk`: a queued thread's queue links when the lock its `BLOCK_OBJ` names is held (`Lk`), and a word of an
  object region (endpoint, reply) whose lock is held.

`loc_rd_own` / `loc_wr_own` / `lkw_own`: these are readable (`RPerm`) / writable (`WPerm`) at `s`; `loc_wr_nondec`:
a `LocWr` word other than a thread's `STATE` / `BLOCK_OBJ` decides no owner, `lkw_nondec`: neither does a `LkW` word.

`ObjLay` [J]: endpoints and replies lie in their object regions (as `IrqLay.ntw` for notifications; P3's placement
lemmas are the intended discharge, cf. p2sl's `RegionOKX.epW` / `rpW`).

Named premise: `ObjLay` [J].
-/
import Fl4Proofs.P2.FootTimerFireLkO
import Fl4Proofs.P2.FootTimerFireOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl

section sets
variable {S : Type}

/-- A thread homed on this core at `s`. -/
def LocT (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) (y : U64) : Prop :=
  y ∈ T ∧ L.mem s (affA y) = L.cpu s

/-- What a waking fire run may read of this core at `s` (module docstring). -/
def LocRd (st : machine.Store S) [L : LawfulStore st] (T Scs : Set U64) (Z : U64 → Nat) (s : S) (w : U64) : Prop :=
  (∃ o : U64, o.val < 4288 ∧ o.val % 8 = 0 ∧ w = L.nodeAt s (L.cpu s) o) ∨
  (∃ y, LocT st T s y ∧ ∃ K : U64, 256 ≤ K.val ∧ K.val < 4096 ∧ K.val % 8 = 0 ∧ ¬ TimerField K.val ∧
    ¬ GField K.val ∧ w = core.num.U64.wrapping_add y K) ∨
  (∃ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s ∧ InSC p (Z p) w)

/-- What a waking fire run may write of this core at `s` (module docstring). -/
def LocWr (st : machine.Store S) [L : LawfulStore st] (T Scs : Set U64) (Z : U64 → Nat) (s : S) (w : U64) : Prop :=
  (∃ o : U64, o.val < 4288 ∧ o.val % 8 = 0 ∧ w = L.nodeAt s (L.cpu s) o) ∨
  (∃ y, LocT st T s y ∧ ∃ K : U64, 256 ≤ K.val ∧ K.val < 4096 ∧ K.val % 8 = 0 ∧ ¬ GateField K.val ∧
    ¬ TimerField K.val ∧ ¬ GField K.val ∧ w = core.num.U64.wrapping_add y K) ∨
  (∃ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s ∧ InSC p (Z p) w ∧ w.val ≠ p.val + 16)

/-- The words of held locks at `s` (module docstring). -/
def LkW (st : machine.Store S) [L : LawfulStore st] (K : KLayout) (T : Set U64) (Lk : U64 → Prop) (s : S)
    (w : U64) : Prop :=
  (∃ y ∈ T, QueuedState (L.mem s (stA y)) ∧ Lk (L.mem s (blockA y)) ∧
    ∃ k : U64, (k.val = 3496 ∨ k.val = 3504) ∧ w = core.num.U64.wrapping_add y k) ∨
  (∃ p, Lk p ∧ region K w = .obj p)

/-- **Endpoints and replies lie in their object regions** [J] (module docstring). -/
def ObjLay (K : KLayout) (H : Heap) (Rp : Set U64) : Prop :=
  (∀ e, H e = some .ep → ∀ k : U64, k.val < 16 → region K (core.num.U64.wrapping_add e k) = .obj e) ∧
  (∀ r ∈ Rp, ∀ k : U64, k.val < 32 → region K (core.num.U64.wrapping_add r k) = .obj r)

end sets

section own
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- **Every word of `LocRd` is readable** at `s`. -/
theorem loc_rd_own {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    {lk : U64 → Prop} {w : U64} (h : LocRd st T Scs Z s w) : RPerm (own K) (L.cpu s) lk (L.mem s) w := by
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  rcases h with ⟨o, ho, -, rfl⟩ | ⟨y, ⟨hy, ha⟩, k, h1, h2, -, ht, hg, rfl⟩ | ⟨p, hp, hc, hb⟩
  · exact Or.inl (held_core (hL.own_node _ ho))
  · have e := hL.own_tcb hT (L.mem s) hy h1 h2
    unfold fld at e
    unfold RPerm GateOnly
    rw [e]
    unfold tcbOwner
    by_cases hga : GateField k.val
    · rw [if_pos hga]; exact Or.inr rfl
    · rw [if_neg hga, if_neg ht, if_neg hg]; exact Or.inl ha
  · have e := sc_own hL hp hb hc
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)

/-- **Every word of `LocWr` is writable** at `s`. -/
theorem loc_wr_own {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    {lk : U64 → Prop} {w : U64} (h : LocWr st T Scs Z s w) : WPerm (own K) (L.cpu s) lk (L.mem s) w := by
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  rcases h with ⟨o, ho, -, rfl⟩ | ⟨y, ⟨hy, ha⟩, k, h1, h2, -, hga, ht, hg, rfl⟩ | ⟨p, hp, hc, hb, h16⟩
  · exact held_core (hL.own_node _ ho)
  · have e := hL.own_tcb hT (L.mem s) hy h1 h2
    unfold fld at e
    unfold WPerm
    rw [e]
    unfold tcbOwner
    rw [if_neg hga, if_neg ht, if_neg hg]; exact ha
  · have e := sc_own hL hp hb hc
    rw [if_neg h16] at e
    exact held_core e

/-- **Every word of `LkW Lk` is the path's** when `Lk` is held. -/
theorem lkw_own {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    {lk Lk : U64 → Prop} (hLk : ∀ p, Lk p → lk p) {w : U64} (h : LkW st K T Lk s w) :
    WPerm (own K) (L.cpu s) lk (L.mem s) w ∧ RPerm (own K) (L.cpu s) lk (L.mem s) w := by
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  have k : WPerm (own K) (L.cpu s) lk (L.mem s) w := by
    rcases h with ⟨y, hy, hq, hl, k, hk, rfl⟩ | ⟨p, hp, hr⟩
    · exact held_lock (glink_own hL hT hy hk hq) (hLk _ hl)
    · exact held_lock (obj_own hr) (hLk _ hp)
  exact ⟨k, Or.inl k⟩

/-- **A `LocWr` word other than a thread's `STATE` / `BLOCK_OBJ` decides no owner.** -/
theorem loc_wr_nondec (hK : RegionOK K) {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K st T Scs Z s) {w : U64} (h : LocWr st T Scs Z s w)
    (hS : ∀ y ∈ T, w ≠ stA y) (hB : ∀ y ∈ T, w ≠ blockA y) : ¬ DecW K w := by
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  apply nondec_of_region hK
  rcases h with ⟨o, ho, -, rfl⟩ | ⟨y, ⟨hy, -⟩, k, h1, h2, -, hga, ht, -, rfl⟩ | ⟨p, hp, -, hb, h16⟩
  · exact Or.inr (Or.inl ⟨_, hL.nd o ho⟩)
  · have e : (core.num.U64.wrapping_add y k).val - y.val = k.val := by
      rw [field_val (hT y hy) h2]; omega
    have n1 : k.val ≠ 3328 := fun e' => hS y hy (by
      rw [stA_eq, show k = 3328#u64 from UScalar.eq_of_val_eq (by simp [e'])])
    have n2 : k.val ≠ 3336 := fun e' => hB y hy (by
      rw [blockA_eq, show k = 3336#u64 from UScalar.eq_of_val_eq (by simp [e'])])
    have n3 : k.val ≠ 3520 := fun e' => hga (by unfold GateField; omega)
    have n4 : k.val ≠ 3528 := fun e' => ht (by unfold TimerField; omega)
    have n5 : k.val ≠ 3568 := fun e' => ht (by unfold TimerField; omega)
    exact Or.inl ⟨_, hL.tcb y hy k h1 h2, by rw [e]; exact n3, by rw [e]; exact n1, by rw [e]; exact n2,
      by rw [e]; exact n4, by rw [e]; exact n5⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hL.sc _ hp w hb, h16⟩))))

/-- **A `LkW` word decides no owner.** -/
theorem lkw_nondec (hK : RegionOK K) {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K st T Scs Z s) {Lk : U64 → Prop} {w : U64} (h : LkW st K T Lk s w) : ¬ DecW K w := by
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  apply nondec_of_region hK
  rcases h with ⟨y, hy, -, -, k, hk, rfl⟩ | ⟨p, -, hr⟩
  · have e : (core.num.U64.wrapping_add y k).val - y.val = k.val := by
      rw [field_val (hT y hy) (by omega)]; omega
    exact Or.inl ⟨_, hL.tcb y hy k (by omega) (by omega), by rw [e]; omega, by rw [e]; omega, by rw [e]; omega,
      by rw [e]; omega, by rw [e]; omega⟩
  · exact Or.inr (Or.inr (Or.inl ⟨p, hr⟩))

end own

end Fl4Proofs.P2

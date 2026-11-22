/-
P1 (jc6d, TIMER-RB-PLAN stage 3b, rest): `timer::set_red` as a colour update of the abstract links.  The
write `(h & !RED) | r` of a TCB's height word gives colour `r` (`red_of`), keeps the core bits (`shr8_red`)
and changes no other link (`lk_wr_red`); on the walk state `RW` it is `Links.setRed` (`RW.wr_red`).
-/
import Fl4Proofs.P1.TimerRBRotH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

namespace TRB
@[simp] theorem Links.setRed_l (k : Links) (z : U64) (b : Bool) : (k.setRed z b).l = k.l := rfl
@[simp] theorem Links.setRed_r (k : Links) (z : U64) (b : Bool) : (k.setRed z b).r = k.r := rfl
@[simp] theorem Links.setRed_p (k : Links) (z : U64) (b : Bool) : (k.setRed z b).p = k.p := rfl
@[simp] theorem Links.setRed_red (k : Links) (z : U64) (b : Bool) :
    (k.setRed z b).red = Function.update k.red z b := rfl

theorem LinksEqOn.setRed {T : Set U64} {k k' : Links} (e : LinksEqOn T k k') (z : U64) (b : Bool) :
    LinksEqOn T (k.setRed z b) (k'.setRed z b) := fun y hy => by
  obtain ⟨a, b', c, d⟩ := e y hy
  refine ⟨a, b', c, ?_⟩
  show Function.update k'.red z b y = Function.update k.red z b y
  by_cases h : y = z
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]; exact d
end TRB

/-- The colour value `set_red` ors in. -/
def redW (b : Bool) : U64 := if b then 1#u64 else 0#u64

theorem redW_01 (b : Bool) : redW b = 0#u64 ∨ redW b = 1#u64 := by cases b <;> simp [redW]

theorem red_bit (i : U64) (b : Bool) : (((i &&& ~~~1#u64) ||| redW b) &&& 1#u64) = redW b := by
  have hb : (((i &&& ~~~1#u64) ||| redW b) &&& 1#u64).bv = (redW b).bv := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    by_cases h0 : j = 0 <;> cases b <;>
      simp [redW, h0, UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
        BitVec.getLsbD_not, one_bit, zero_bit]
  exact UScalar.eq_of_val_eq (by show (((i &&& ~~~1#u64) ||| redW b) &&& 1#u64).bv.toNat = (redW b).bv.toNat; rw [hb])

/-- The colour read back after `set_red … b` is `b`. -/
theorem red_of (i : U64) (b : Bool) : ((((i &&& ~~~1#u64) ||| redW b) &&& 1#u64) != 0#u64) = b := by
  rw [red_bit]; cases b <;> simp [redW]

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

theorem timer.set_red.on (s : S) (z : U64) (b : Bool) (hT : TcbPlaced T) (hz : z ∈ T) :
    timer.set_red st s z b ⦃ s' => s' = L.wr s (thA z) ((L.mem s (thA z) &&& ~~~1#u64) ||| redW b) ⦄ := by
  unfold timer.set_red timer.RED
  step with obj.Tcb.is_null.spec as ⟨bn, eb⟩
  split
  · rename_i hb; exfalso; exact (hT z hz).ne0 (by rw [show z = 0#u64 by simpa [eb] using hb]; rfl)
  step with obj.Tcb.timer_height.val as ⟨i, ei⟩
  simp only [lift, Aeneas.Std.bind_ok]
  split
  · rename_i hr
    subst hr
    exact WP.spec_mono (obj.Tcb.set_timer_height.wr s z _) fun s' e => by rw [e, ei]; rfl
  · rename_i hr
    have hr' : b = false := by simpa using hr
    subst hr'
    exact WP.spec_mono (obj.Tcb.set_timer_height.wr s z _) fun s' e => by rw [e, ei]; rfl

/-- The links after `set_red z b`. -/
theorem lk_wr_red {s : S} {z : U64} (b : Bool) (hT : TcbPlaced T) (hz : z ∈ T) :
    TRB.LinksEqOn T ((lk st s).setRed z b)
      (lk st (L.wr s (thA z) ((L.mem s (thA z) &&& ~~~1#u64) ||| redW b))) := by
  intro y hy
  have f : ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ 3568 →
      L.mem (L.wr s (thA z) ((L.mem s (thA z) &&& ~~~1#u64) ||| redW b)) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') :=
    fun K' h1 h2 h3 => by
      rw [show thA z = core.num.U64.wrapping_add z 3568#u64 from rfl,
        trb_fld_wr (K := 3568#u64) (K' := K') hT hz hy (by simp) (by simp) h1 h2, if_neg (fun h => h3 (by simpa using h.2))]
  refine ⟨f 3544#u64 (by simp) (by simp) (by simp), f 3552#u64 (by simp) (by simp) (by simp),
    f 3560#u64 (by simp) (by simp) (by simp), ?_⟩
  show ((L.mem (L.wr s (thA z) ((L.mem s (thA z) &&& ~~~1#u64) ||| redW b)) (thA y) &&& 1#u64) != 0#u64) =
    Function.update (lk st s).red z b y
  rw [show thA z = core.num.U64.wrapping_add z 3568#u64 from rfl, show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl,
    trb_fld_wr (K := 3568#u64) (K' := 3568#u64) hT hz hy (by simp) (by simp) (by simp) (by simp)]
  by_cases e : y = z
  · subst e
    rw [if_pos ⟨rfl, rfl⟩, Function.update_self]
    exact red_of _ b
  · rw [if_neg (fun h => e h.1), Function.update_of_ne e]; rfl

/-- `set_red` keeps the core bits of the height word. -/
theorem core_wr_red (i : U64) (b : Bool) : ((i &&& ~~~1#u64) ||| redW b).val >>> 8 = i.val >>> 8 :=
  shr8_red i (redW b) (redW_01 b)

theorem RW.wr_red {s0 s : S} {c R z : U64} {K : TRB.Links} {F : U64 → Prop} (h : RW st T s0 s c K R F)
    (hT : TcbPlaced T) (hz : z ∈ T) (b : Bool) (hF : F (thA z)) :
    RW st T s0 (L.wr s (thA z) ((L.mem s (thA z) &&& ~~~1#u64) ||| redW b)) c (K.setRed z b) R F :=
  ⟨(h.eq.setRed z b).trans (lk_wr_red b hT hz),
    (root_wr_fld (K := 3568#u64) hT h.np hz (by simp) (by simp)).trans h.root,
    (h.wi.trans (writesIn_wr (a := thA z) (tz_aligned hT (Tz.of_mem hz) (K := 3568#u64) (by simp) (by simp)))).mono
      fun b hb => hb.elim id fun e => by rw [e]; exact hF, h.np.wr⟩

end

end Fl4Proofs.P1

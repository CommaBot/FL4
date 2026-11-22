/-
P1 (jc6d, TIMER-RB-PLAN stage 3b): single timer-word writes as updates of the abstract links.  A write of a
TCB's timer field changes that one field of that one TCB (`trb_fld_wr`) and no node word (`trb_node_wr_fld`); a write
of a node word changes no TCB field (`trb_fld_wr_node`) and only that word of that node (`trb_node_wr_node`).  On the
links: writing `tlA z`/`trA z`/`tpA z` is `Links.setL/setR/setP z` (`lk_wr_tl/tr/tp`), and the colour write
of `set_red` is `Links.setRed z` (`lk_wr_red`), each on the TCBs of `T` (`LinksEqOn`), which is all `Rep`
of a tree with keys in `T` reads (`Rep.congr_on`).
-/
import Fl4Proofs.P1.TimerRBFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

namespace TRB

def Links.setL (k : Links) (z v : U64) : Links := { k with l := Function.update k.l z v }
def Links.setR (k : Links) (z v : U64) : Links := { k with r := Function.update k.r z v }
def Links.setP (k : Links) (z v : U64) : Links := { k with p := Function.update k.p z v }
def Links.setRed (k : Links) (z : U64) (b : Bool) : Links := { k with red := Function.update k.red z b }

/-- Two link functions agree on the nodes `T`. -/
def LinksEqOn (T : Set U64) (k k' : Links) : Prop :=
  ∀ y ∈ T, k'.l y = k.l y ∧ k'.r y = k.r y ∧ k'.p y = k.p y ∧ k'.red y = k.red y

theorem Rep.congr_on {T : Set U64} {k k' : Links} {par x : U64} {t : RBT} (h : Rep k par x t)
    (hT : ∀ y ∈ t.keys, y ∈ T) (e : LinksEqOn T k k') : Rep k' par x t :=
  h.congr fun y hy => e y (hT y hy)

end TRB

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}

/-- A write of field `K` of TCB `z`, read at field `K'` of TCB `y`. -/
theorem trb_fld_wr {s : S} {z y K K' v : U64} (hT : TcbPlaced T) (hz : z ∈ T) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (hK' : K'.val < 4096) (hK8' : K'.val % 8 = 0) :
    L.mem (L.wr s (core.num.U64.wrapping_add z K) v) (core.num.U64.wrapping_add y K') =
      if y = z ∧ K'.val = K.val then v else L.mem s (core.num.U64.wrapping_add y K') := by
  have ha := tz_aligned hT (Tz.of_mem hz) hK hK8
  have hb := tz_aligned hT (Tz.of_mem hy) hK' hK8'
  split
  · rename_i h
    obtain ⟨e1, e⟩ := h
    subst e1
    rw [show K' = K from UScalar.eq_of_val_eq e]; exact L.mem_wr_same ha
  · rename_i h
    refine L.mem_wr_ne ha hb fun e => h ?_
    by_cases hk : K'.val = K.val
    · rw [show K' = K from UScalar.eq_of_val_eq hk] at e
      exact ⟨(tz_inj hT (Tz.of_mem hz) (Tz.of_mem hy) hK e).symm, hk⟩
    · exact absurd e (tz_ne hT (Tz.of_mem hz) (Tz.of_mem hy) hK hK' (Ne.symm hk))

/-- A TCB-field write keeps every node word. -/
theorem trb_node_wr_fld {s : S} {z K v c o : U64} (hT : TcbPlaced T) (hz : z ∈ T) (hK : K.val < 4096)
    (hK8 : K.val % 8 = 0) (hN : NodePlaced st T s c) (ho : o.val < 4288) (ho8 : o.val % 8 = 0) :
    L.mem (L.wr s (core.num.U64.wrapping_add z K) v) (L.nodeAt (L.wr s (core.num.U64.wrapping_add z K) v) c o) =
      L.mem s (L.nodeAt s c o) := by
  rw [nodeAt_of_ksb (L.ksb_wr _ _ _)]
  exact L.mem_wr_ne (tz_aligned hT (Tz.of_mem hz) hK hK8) (nodeAt_aligned hN ho ho8)
    (Ne.symm (node_ne_tz hT hN ho (Tz.of_mem hz) hK))

/-- A node-word write keeps every TCB field. -/
theorem trb_fld_wr_node {s : S} {c o v y K : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (ho8 : o.val % 8 = 0) (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.mem (L.wr s (L.nodeAt s c o) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
  L.mem_wr_ne (nodeAt_aligned hN ho ho8) (tz_aligned hT (Tz.of_mem hy) hK hK8) (node_ne_tz hT hN ho (Tz.of_mem hy) hK)

/-- A node-word write, read at another (or the same) node word. -/
theorem trb_node_wr_node {s : S} {c o v c' o' : U64} (hN : NodePlaced st T s c) (hN' : NodePlaced st T s c')
    (ho : o.val < 4288) (ho8 : o.val % 8 = 0) (ho' : o'.val < 4288) (ho8' : o'.val % 8 = 0) :
    L.mem (L.wr s (L.nodeAt s c o) v) (L.nodeAt (L.wr s (L.nodeAt s c o) v) c' o') =
      if c' = c ∧ o'.val = o.val then v else L.mem s (L.nodeAt s c' o') := by
  rw [nodeAt_of_ksb (L.ksb_wr _ _ _)]
  split
  · rename_i h
    obtain ⟨e1, e⟩ := h
    subst e1
    rw [show o' = o from UScalar.eq_of_val_eq e]; exact L.mem_wr_same (nodeAt_aligned hN ho ho8)
  · rename_i h
    exact L.mem_wr_ne (nodeAt_aligned hN ho ho8) (nodeAt_aligned hN' ho' ho8')
      (node_ne_node hN hN' ho ho' fun e1 e2 => h ⟨e1.symm, e2.symm⟩)

/-- The links after a write of `z`'s left link. -/
theorem lk_wr_tl {s : S} {z v : U64} (hT : TcbPlaced T) (hz : z ∈ T) :
    TRB.LinksEqOn T ((lk st s).setL z v) (lk st (L.wr s (tlA z) v)) := by
  intro y hy
  have f : ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ 3544 →
      L.mem (L.wr s (tlA z) v) (core.num.U64.wrapping_add y K') = L.mem s (core.num.U64.wrapping_add y K') :=
    fun K' h1 h2 h3 => by
      rw [show tlA z = core.num.U64.wrapping_add z 3544#u64 from rfl,
        trb_fld_wr (K := 3544#u64) (K' := K') hT hz hy (by simp) (by simp) h1 h2, if_neg (fun h => h3 (by simpa using h.2))]
  refine ⟨?_, f 3552#u64 (by simp) (by simp) (by simp), f 3560#u64 (by simp) (by simp) (by simp), ?_⟩
  · show L.mem (L.wr s (tlA z) v) (tlA y) = Function.update (lk st s).l z v y
    rw [show tlA z = core.num.U64.wrapping_add z 3544#u64 from rfl, show tlA y = core.num.U64.wrapping_add y 3544#u64 from rfl,
      trb_fld_wr (K := 3544#u64) (K' := 3544#u64) hT hz hy (by simp) (by simp) (by simp) (by simp)]
    by_cases e : y = z
    · subst e; simp
    · rw [if_neg (fun h => e h.1), Function.update_of_ne e]; rfl
  · show ((L.mem (L.wr s (tlA z) v) (thA y) &&& 1#u64) != 0#u64) = ((L.mem s (thA y) &&& 1#u64) != 0#u64)
    rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, f 3568#u64 (by simp) (by simp) (by simp)]

theorem lk_wr_tr {s : S} {z v : U64} (hT : TcbPlaced T) (hz : z ∈ T) :
    TRB.LinksEqOn T ((lk st s).setR z v) (lk st (L.wr s (trA z) v)) := by
  intro y hy
  have f : ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ 3552 →
      L.mem (L.wr s (trA z) v) (core.num.U64.wrapping_add y K') = L.mem s (core.num.U64.wrapping_add y K') :=
    fun K' h1 h2 h3 => by
      rw [show trA z = core.num.U64.wrapping_add z 3552#u64 from rfl,
        trb_fld_wr (K := 3552#u64) (K' := K') hT hz hy (by simp) (by simp) h1 h2, if_neg (fun h => h3 (by simpa using h.2))]
  refine ⟨f 3544#u64 (by simp) (by simp) (by simp), ?_, f 3560#u64 (by simp) (by simp) (by simp), ?_⟩
  · show L.mem (L.wr s (trA z) v) (trA y) = Function.update (lk st s).r z v y
    rw [show trA z = core.num.U64.wrapping_add z 3552#u64 from rfl, show trA y = core.num.U64.wrapping_add y 3552#u64 from rfl,
      trb_fld_wr (K := 3552#u64) (K' := 3552#u64) hT hz hy (by simp) (by simp) (by simp) (by simp)]
    by_cases e : y = z
    · subst e; simp
    · rw [if_neg (fun h => e h.1), Function.update_of_ne e]; rfl
  · show ((L.mem (L.wr s (trA z) v) (thA y) &&& 1#u64) != 0#u64) = ((L.mem s (thA y) &&& 1#u64) != 0#u64)
    rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, f 3568#u64 (by simp) (by simp) (by simp)]

theorem lk_wr_tp {s : S} {z v : U64} (hT : TcbPlaced T) (hz : z ∈ T) :
    TRB.LinksEqOn T ((lk st s).setP z v) (lk st (L.wr s (tpA z) v)) := by
  intro y hy
  have f : ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ 3560 →
      L.mem (L.wr s (tpA z) v) (core.num.U64.wrapping_add y K') = L.mem s (core.num.U64.wrapping_add y K') :=
    fun K' h1 h2 h3 => by
      rw [show tpA z = core.num.U64.wrapping_add z 3560#u64 from rfl,
        trb_fld_wr (K := 3560#u64) (K' := K') hT hz hy (by simp) (by simp) h1 h2, if_neg (fun h => h3 (by simpa using h.2))]
  refine ⟨f 3544#u64 (by simp) (by simp) (by simp), f 3552#u64 (by simp) (by simp) (by simp), ?_, ?_⟩
  · show L.mem (L.wr s (tpA z) v) (tpA y) = Function.update (lk st s).p z v y
    rw [show tpA z = core.num.U64.wrapping_add z 3560#u64 from rfl, show tpA y = core.num.U64.wrapping_add y 3560#u64 from rfl,
      trb_fld_wr (K := 3560#u64) (K' := 3560#u64) hT hz hy (by simp) (by simp) (by simp) (by simp)]
    by_cases e : y = z
    · subst e; simp
    · rw [if_neg (fun h => e h.1), Function.update_of_ne e]; rfl
  · show ((L.mem (L.wr s (tpA z) v) (thA y) &&& 1#u64) != 0#u64) = ((L.mem s (thA y) &&& 1#u64) != 0#u64)
    rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, f 3568#u64 (by simp) (by simp) (by simp)]

end

end Fl4Proofs.P1

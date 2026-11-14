/-
P1: arming a timer (`timer::insert`, the TCB set-timer path) keeps `TInv`:
the disarm (`remove`), the walk down the tree, the new node's fields and the
red-black insert fixup.
-/
import Fl4Proofs.P1.QueueFire
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- `TimerOK` but for the core of the TCB `t` (whose deadline and height are
being set). -/
structure TimerOKx (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (t : U64) (s : S) : Prop where
  lt : ∀ y ∈ T, Tz T (L.mem s (tlA y))
  rt : ∀ y ∈ T, Tz T (L.mem s (trA y))
  pt : ∀ y ∈ T, Tz T (L.mem s (tpA y))
  root : ∀ c ∈ Cs, Tz T (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT))
  min : ∀ c ∈ Cs, Tz T (L.mem s (L.nodeAt s c layout.node.TIMER_MIN))
  core : ∀ y ∈ T, y ≠ t → L.mem s (tdA y) ≠ 0#u64 → ∀ c : U64, c.val = (L.mem s (thA y)).val >>> 8 → c ∈ Cs

theorem TimerOK.x {s : S} (h : TimerOK st T Cs s) (t : U64) : TimerOKx st T Cs t s :=
  ⟨h.lt, h.rt, h.pt, h.root, h.min, fun y hy _ => h.core y hy⟩

/-- A write of a timer field of `t` other than its height. -/
theorem TimerOKx.wr {s : S} {t K v : U64} (h : TimerOKx st T Cs t s) (hT : TcbPlaced T)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (ht : t ∈ T) (hK : 3528 ≤ K.val) (hK' : K.val < 3568)
    (hK8 : K.val % 8 = 0) (hv : (K.val = 3544 ∨ K.val = 3552 ∨ K.val = 3560) → Tz T v) :
    TimerOKx st T Cs t (L.wr s (core.num.U64.wrapping_add t K) v) := by
  have htz : Tz T t := Tz.of_mem ht
  have ha := tz_aligned hT htz (K := K) (by omega) hK8
  have lk : ∀ y K', y ∈ T → (K'.val = 3544 ∨ K'.val = 3552 ∨ K'.val = 3560) →
      Tz T (L.mem s (core.num.U64.wrapping_add y K')) →
      Tz T (L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add y K')) := by
    intro y K' hyT hK'' h0
    have hy := Tz.of_mem (T := T) hyT
    rw [L.mem_wr_val ha (tz_aligned hT hy (by omega) (by omega))]
    split
    · rename_i e
      have : K.val = K'.val := by
        by_contra hne; exact tz_ne hT htz hy (by omega) (by omega) hne e
      exact hv (by omega)
    · exact h0
  have kf : ∀ y, Tz T y → ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (y = t → K'.val ≠ K.val) →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') := by
    intro y hy K' h1 h2 hne
    refine L.mem_wr_ne ha (tz_aligned hT hy h1 h2) (fun e => ?_)
    by_cases hKK : K.val = K'.val
    · have := tz_inj hT htz hy (K := K') (by omega) (by have hk : K = K' := UScalar.eq_of_val_eq hKK; subst hk; exact e)
      exact hne this.symm hKK.symm
    · exact tz_ne hT htz hy (by omega) h1 hKK e
  have kn : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (L.nodeAt (L.wr s (core.num.U64.wrapping_add t K) v) c o) =
        L.mem s (L.nodeAt s c o) := by
    intro c hc o ho h8
    rw [nodeAt_of_ksb (L.ksb_wr _ _ _)]
    exact L.mem_wr_ne ha (nodeAt_aligned (hN c hc) ho h8) (Ne.symm (node_ne_tz hT (hN c hc) ho htz (by omega)))
  refine ⟨fun y hy => lk y _ hy (by simp) (h.lt y hy), fun y hy => lk y _ hy (by simp) (h.rt y hy),
    fun y hy => lk y _ hy (by simp) (h.pt y hy), fun c hc => ?_, fun c hc => ?_, fun y hy hyt hd c hcv => ?_⟩
  · rw [kn c hc _ (by rw [timer_root_val]; omega) (by rw [timer_root_val])]; exact h.root c hc
  · rw [kn c hc _ (by rw [timer_min_val]; omega) (by rw [timer_min_val])]; exact h.min c hc
  · rw [show tdA y = core.num.U64.wrapping_add y 3528#u64 from rfl,
      kf y (Tz.of_mem hy) _ (by simp) (by simp) (fun e => absurd e hyt)] at hd
    rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl,
      kf y (Tz.of_mem hy) _ (by simp) (by simp) (fun e => absurd e hyt)] at hcv
    exact h.core y hy hyt hd c hcv

/-- The height write of `t` that names a core restores `TimerOK`. -/
theorem TimerOKx.wr_ht {s : S} {t v : U64} (h : TimerOKx st T Cs t s) (hT : TcbPlaced T)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (ht : t ∈ T) (hc : ∀ c : U64, c.val = v.val >>> 8 → c ∈ Cs) :
    TimerOK st T Cs (L.wr s (thA t) v) := by
  have htz : Tz T t := Tz.of_mem ht
  have ha : Aligned (thA t) := tz_aligned hT htz (K := 3568#u64) (by simp) (by simp)
  have kp : ∀ y, Tz T y → ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ 3568 →
      L.mem (L.wr s (thA t) v) (core.num.U64.wrapping_add y K') = L.mem s (core.num.U64.wrapping_add y K') :=
    fun y hy K' h1 h2 hne => L.mem_wr_ne ha (tz_aligned hT hy h1 h2) (tz_ne hT htz hy (by simp) h1 (by simp; omega))
  have kn : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s (thA t) v) (L.nodeAt (L.wr s (thA t) v) c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o ho h8
    rw [nodeAt_of_ksb (L.ksb_wr _ _ _)]
    exact L.mem_wr_ne ha (nodeAt_aligned (hN c hc) ho h8) (Ne.symm (node_ne_tz hT (hN c hc) ho htz (by simp)))
  refine ⟨fun c hc => (hN c hc).ksb (L.ksb_wr _ _ _), fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun c hc => ?_, fun c hc => ?_, fun y hy hd c hcv => ?_⟩
  · rw [show tlA y = core.num.U64.wrapping_add y 3544#u64 from rfl, kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp)]
    exact h.lt y hy
  · rw [show trA y = core.num.U64.wrapping_add y 3552#u64 from rfl, kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp)]
    exact h.rt y hy
  · rw [show tpA y = core.num.U64.wrapping_add y 3560#u64 from rfl, kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp)]
    exact h.pt y hy
  · rw [kn c hc _ (by rw [timer_root_val]; omega) (by rw [timer_root_val])]; exact h.root c hc
  · rw [kn c hc _ (by rw [timer_min_val]; omega) (by rw [timer_min_val])]; exact h.min c hc
  · by_cases e : y = t
    · subst e; rw [L.mem_wr_same ha] at hcv; exact hc c hcv
    · rw [show tdA y = core.num.U64.wrapping_add y 3528#u64 from rfl,
        kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp)] at hd
      have n2 : (thA t).val ≠ (thA y).val := fun e' => e (tz_inj hT htz (Tz.of_mem hy) (by simp) e').symm
      rw [L.mem_wr_ne (b := thA y) ha (tz_aligned hT (Tz.of_mem hy) (K := 3568#u64) (by simp) (by simp)) n2] at hcv
      exact h.core y hy e hd c hcv

/-- `TInv` but for the core of `t`. -/
def TInvx (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (t : U64) (s : S) : Prop :=
  BlkT st T Cs Ω H Sg Rp Scs Nt Z s ∧ TimerOKx st T Cs t s

theorem TInvx.wr {s : S} {t K v : U64} (h : TInvx st T Cs Ω H Sg Rp Scs Nt Z t s) (ht : t ∈ T)
    (hK : 3528 ≤ K.val) (hK' : K.val < 3568) (hK8 : K.val % 8 = 0)
    (hv : (K.val = 3544 ∨ K.val = 3552 ∨ K.val = 3560) → Tz T v) :
    TInvx st T Cs Ω H Sg Rp Scs Nt Z t (L.wr s (core.num.U64.wrapping_add t K) v) :=
  ⟨h.1.wr_tfield ht hK (by omega) hK8, h.2.wr h.1.tcbs h.1.nodes ht hK hK' hK8 hv⟩

theorem TInvx.wr_ht {s : S} {t v : U64} (h : TInvx st T Cs Ω H Sg Rp Scs Nt Z t s) (ht : t ∈ T)
    (hc : ∀ c : U64, c.val = v.val >>> 8 → c ∈ Cs) :
    TInv st T Cs Ω H Sg Rp Scs Nt Z (L.wr s (thA t) v) :=
  ((h.1.wr_tfield (K := 3568#u64) ht (by simp) (by simp) (by simp)).ok
    (h.2.wr_ht h.1.tcbs h.1.nodes ht hc)).tinv

theorem obj.Tcb.set_timer_badge.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_timer_badge st t s v ⦃ s' => s' = L.wr s (tbA t) v ⦄ := by
  unfold obj.Tcb.set_timer_badge; step*; simp_all [tbA]

theorem or1_shr8 (i : U64) : (i ||| 1#u64).val >>> 8 = i.val >>> 8 := by
  have hb : (i ||| 1#u64).bv >>> 8 = i.bv >>> 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_ushiftRight, UScalar.bv_or, BitVec.getLsbD_or, one_bit]
    simp
  show (i ||| 1#u64).bv.toNat >>> 8 = i.bv.toNat >>> 8
  rw [← BitVec.toNat_ushiftRight, ← BitVec.toNat_ushiftRight, hb]

theorem shl8_shr8 {c i : U64} (hc : c.val < 2 ^ 56) (hi : i.val = (c.val <<< 8) % U64.size) :
    i.val >>> 8 = c.val := by
  rw [hi, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  simp [U64.size_def, U64.numBits]
  omega

theorem timer.set_left.on (s : S) (t v : U64) (hT : TcbPlaced T) (ht : t ∈ T) :
    timer.set_left st s t v ⦃ s' => s' = L.wr s (tlA t) v ⦄ := by
  unfold timer.set_left
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb; exfalso; exact (hT t ht).ne0 (by rw [show t = 0#u64 by simpa [eb] using hb]; rfl)
  · exact obj.Tcb.set_timer_left.wr s t v

theorem timer.set_right.on (s : S) (t v : U64) (hT : TcbPlaced T) (ht : t ∈ T) :
    timer.set_right st s t v ⦃ s' => s' = L.wr s (trA t) v ⦄ := by
  unfold timer.set_right
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb; exfalso; exact (hT t ht).ne0 (by rw [show t = 0#u64 by simpa [eb] using hb]; rfl)
  · exact obj.Tcb.set_timer_right.wr s t v

theorem timer.set_parent.on (s : S) (t v : U64) (hT : TcbPlaced T) (ht : t ∈ T) :
    timer.set_parent st s t v ⦃ s' => s' = L.wr s (tpA t) v ⦄ := by
  unfold timer.set_parent
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb; exfalso; exact (hT t ht).ne0 (by rw [show t = 0#u64 by simpa [eb] using hb]; rfl)
  · exact obj.Tcb.set_timer_parent.wr s t v

section ops

theorem timer.insert_loop.tz (s : S) (d p cur : U64) (gl fst : Bool) (fuel : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z s) (hp : Tz T p) (hc : Tz T cur) :
    timer.insert_loop st s d p cur gl fst fuel ⦃ r => Tz T r.1 ⦄ := by
  have L1 := timer.left.tz (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt)
  have L2 := timer.right.tz (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt)
  unfold timer.insert_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.2.2.val) (inv := fun x => Tz T x.1 ∧ Tz T x.2.1)
  · rintro ⟨p1, c1, g1, f1, u1⟩ ⟨hp1, hc1⟩
    simp only at hp1 hc1
    unfold timer.insert_loop.body
    step*
  · exact ⟨hp, hc⟩

theorem timer.insert_fixup_loop.tinv (s : S) (c z fuel : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z s) (hc : c ∈ Cs) (hz : Tz T z) :
    timer.insert_fixup_loop st s c z fuel ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
  have L1 := timer.left.tz (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt)
  have L2 := timer.right.tz (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt)
  have L3 := timer.parent.tz (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt)
  have L5 := timer.set_red.tinv (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt)
  have L6 := timer.rotate_left.tinv (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt)
  have L7 := timer.rotate_right.tinv (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt)
  have L8 := timer.is_red.any (L := L)
  have L9 := tcb_eq.iff
  unfold timer.insert_fixup_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z x.1 ∧ Tz T x.2.1)
  · rintro ⟨s1, z1, f1⟩ ⟨h1, hz1⟩
    simp only at h1 hz1
    unfold timer.insert_fixup_loop.body
    step*
    all_goals try (
      refine WP.spec_bind (Pₘ := fun r => TInv st T Cs Ω H Sg Rp Scs Nt Z r.1 ∧ Tz T r.2.1 ∧ Tz T r.2.2) ?_ ?_
      · split <;> step*
      rintro ⟨sa, za, pa⟩ ⟨ha, hza, hpa⟩
      simp only at ha hza hpa
      step*)
  · exact ⟨h, hz⟩

theorem timer.insert_fixup.tinv (s : S) (c z : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z s) (hc : c ∈ Cs)
    (hz : Tz T z) : timer.insert_fixup st s c z ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
  unfold timer.insert_fixup
  refine WP.spec_bind (timer.insert_fixup_loop.tinv s c z _ h hc hz) fun s1 h1 => ?_
  refine WP.spec_bind (timer.root.tz s1 c h1 hc) fun r hr => ?_
  exact timer.set_red.tinv s1 r false h1 hr

end ops

/-- A core's `REPROGRAM` word. -/
theorem reprogram_at.tinv {s : S} {c v : U64} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z s) (hc : c ∈ Cs) :
    TInv st T Cs Ω H Sg Rp Scs Nt Z (L.wr s (L.nodeAt s c layout.node.REPROGRAM) v) := by
  have hI := h
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have hw : WritesIn st s (L.wr s (L.nodeAt s c layout.node.REPROGRAM) v) (L.Free s Ω Cs) :=
    free_node_write rfl hc (h0.nodes _ hc) (by simp [rp, LowFree])
  have f := fr_node (Sg := Sg) (v := v) h0 hSg hc (by rw [rp]; omega) (by rw [rp]) (fun _ => by rw [rp]; omega)
    ⟨by rw [rp]; omega, by rw [rp]; omega⟩
  exact hI.of_tmfr ⟨⟨Q, R, inv_of_free h0 hw⟩, hB.free h0 hw, hX.fr f, hS.fr f, hSg.fr f⟩
    (TmFr.of_fr f hX.1 h0.nodes)

theorem TInv.cpu_small {s : S} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z s) {c : U64} (hc : c ∈ Cs) : c.val < 2 ^ 56 := by
  have := (h.nodes c hc).fits
  simp only [LawfulStore.nodeBase] at this
  omega

/-- seL4 MCS (l4h) `timerQueueInsert`: arming `t`'s timer keeps `TInv`. -/
theorem timer.insert.tinv (s : S) (t d bd : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z s) (ht : t ∈ T) :
    timer.insert st s t d bd ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
  have htz : Tz T t := Tz.of_mem ht
  unfold timer.insert
  refine WP.spec_bind (timer.remove.tinv s t h ht) fun s1 h1 => ?_
  split
  · exact (WP.spec_ok _).2 h1
  refine WP.spec_bind (L.cur_cpu_spec s1) fun cpu ec => ?_
  have hc : cpu ∈ Cs := by
    obtain ⟨⟨Q, R, h0⟩, -⟩ := h1
    rw [ec]; exact h0.cur
  refine WP.spec_bind (timer.root.tz s1 cpu h1 hc) fun cur hcur => ?_
  refine WP.spec_bind (timer.insert_loop.tz s1 d 0#u64 cur false true _ h1 Tz.zero hcur) ?_
  rintro ⟨p, gl, fst⟩ hp
  simp only at hp
  try simp only [WP.uncurry'_pair]
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × U64 => TInv st T Cs Ω H Sg Rp Scs Nt Z r.1 ∧ r.2 = t) ?_ ?_
  · split
    · exact WP.spec_bind (timer.set_root.tinv s1 cpu t h1 hc htz) fun s3 h3 => (WP.spec_ok _).2 ⟨h3, rfl⟩
    · refine WP.spec_bind (Pₘ := fun s2 => TInv st T Cs Ω H Sg Rp Scs Nt Z s2) ?_
        fun s2 h2 => (WP.spec_ok _).2 ⟨h2, rfl⟩
      split
      · exact timer.set_left.tinv s1 p t h1 hp htz
      · exact timer.set_right.tinv s1 p t h1 hp htz
  rintro ⟨s2, t1⟩ ⟨h2, e⟩
  simp only at h2 e
  subst e
  try simp only [WP.uncurry'_pair]
  have hx2 : TInvx st T Cs Ω H Sg Rp Scs Nt Z t1 s2 := ⟨BlkOK.blkT h2, h2.tm.x t1⟩
  refine WP.spec_bind (obj.Tcb.set_timer_deadline.wr s2 t1 d) fun s3 e3 => ?_
  subst e3
  have hx3 := hx2.wr (K := 3528#u64) (v := d) ht (by simp) (by simp) (by simp) (fun h => by simp at h)
  refine WP.spec_bind (obj.Tcb.set_timer_badge.wr _ t1 bd) fun s4 e4 => ?_
  subst e4
  have hx4 := hx3.wr (K := 3536#u64) (v := bd) ht (by simp) (by simp) (by simp) (fun h => by simp at h)
  refine WP.spec_bind (timer.set_parent.on _ t1 p h1.tcbs ht) fun s5 e5 => ?_
  subst e5
  have hx5 := hx4.wr (K := 3560#u64) (v := p) ht (by simp) (by simp) (by simp) (fun _ => hp)
  refine WP.spec_bind (timer.set_left.on _ t1 0#u64 h1.tcbs ht) fun s6 e6 => ?_
  subst e6
  have hx6 := hx5.wr (K := 3544#u64) (v := 0#u64) ht (by simp) (by simp) (by simp) (fun _ => Tz.zero)
  refine WP.spec_bind (timer.set_right.on _ t1 0#u64 h1.tcbs ht) fun s7 e7 => ?_
  subst e7
  have hx7 := hx6.wr (K := 3552#u64) (v := 0#u64) ht (by simp) (by simp) (by simp) (fun _ => Tz.zero)
  step as ⟨i, hi1, hi2⟩
  simp only [lift, timer.RED, Aeneas.Std.bind_ok]
  refine WP.spec_bind (obj.Tcb.set_timer_height.wr _ t1 _) fun s8 e8 => ?_
  subst e8
  have h8 := hx7.wr_ht ht (v := i ||| 1#u64) fun c hcv => by
    rw [or1_shr8, shl8_shr8 (h1.cpu_small hc) hi1] at hcv
    rw [show c = cpu from UScalar.eq_of_val_eq hcv]; exact hc
  refine WP.spec_bind (timer.insert_fixup.tinv _ cpu t1 h8 hc htz) fun s9 h9 => ?_
  split
  · refine WP.spec_bind (obj.node_set.spec s9 cpu _ t1) fun s10 e10 => ?_
    subst e10
    have h10 := h9.wr_node hc (o := layout.node.TIMER_MIN) (by rw [timer_min_val]; simp) htz
    refine WP.spec_mono (obj.node_set.spec _ cpu _ 1#u64) fun s11 e11 => ?_
    subst e11
    exact reprogram_at.tinv h10 hc
  · exact (WP.spec_ok _).2 h9

/-! ## Suspend and restart leave the timer words alone -/

theorem SgOK.ksb' {s s' : S} (h : SgOK st Ω Sg s) (hk : L.ksb s' = L.ksb s) : SgOK st Ω Sg s' :=
  ⟨h.sub, fun b hb => by rw [hk]; exact h.ks b hb, fun o h1 h2 => by rw [hk]; exact h.ksΩ o h1 h2⟩

/-- seL4 `suspend` keeps `TInv`. -/
theorem sched.suspend.tinv {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z s) (ht : t ∈ T) (hna : L.actionW s ≠ t)
    (hyield : L.mem s (yieldA t) ≠ 0#u64 → L.mem s (yieldA t) ∈ Scs) :
    sched.suspend st ar s a t ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (sched.suspend.all s a t Q R h0 ht hB hX hSg hS hna hyield) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  obtain ⟨Q', R', h', hB', hX', hS', tm⟩ := hr
  exact ⟨⟨Q', R', h'⟩, hB', hX', hS', hSg.ksb' tm.1⟩

/-- seL4 `restart` (MCS) keeps `TInv`. -/
theorem sched.restart.tinv {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z s) (ht : t ∈ T) :
    sched.restart st ar s a t ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (sched.restart.all hA s a t Q R h0 ht hB hX hS) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  obtain ⟨Q', R', h', hB', hX', hS', tm⟩ := hr
  exact ⟨⟨Q', R', h'⟩, hB', hX', hS', hSg.ksb' tm.1⟩


/-! ## `BlkOK` forms (`TInv` is `BlkOK` repackaged) -/

theorem timer.remove.blk (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s) (ht : t ∈ T) :
    timer.remove st s t ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ :=
  WP.spec_mono (timer.remove.tinv s t h.tinv ht) fun _ h' => h'

theorem timer.insert.blk (s : S) (t d bd : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s) (ht : t ∈ T) :
    timer.insert st s t d bd ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ :=
  WP.spec_mono (timer.insert.tinv s t d bd h.tinv ht) fun _ h' => h'

/-- The timer step of deleting a thread (`finalise_cap` on a `Thread` cap):
unbind its notification, then take it out of its core's timer tree. -/
theorem thread_unbind_remove.blk (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z s) (ht : t ∈ T) :
    (do let s1 ← notification.unbind_notification st s t; timer.remove st s1 t)
      ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z s' ⦄ :=
  WP.spec_bind (notification.unbind_notification.blk s t h ht) fun s1 h1 => timer.remove.blk s1 t h1 ht

end

end Fl4Proofs.P1

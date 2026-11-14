/-
P1: the per-core timer trees (`timer.rs`).  The timer-tree typing invariant
`TimerOK`: the timer links (`left`, `right`, `parent`) of every TCB and each
core's `TIMER_ROOT` / `TIMER_MIN` hold 0 or a TCB; an armed TCB's height word
names a core.  The tree code reads a null node as having no links and never
writes one, so link typing is all its memory safety needs.
-/import Fl4Proofs.P1.QueueFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- The IPC invariants, which include the timer-tree typing and the
notifications' bound TCBs. -/
abbrev TInv (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s : S) : Prop :=
  BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s

theorem TInv.tm {s : S} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) : TimerOK st T Cs s := h.2.2.1.2.2.tm
theorem TInv.ntb {s : S} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) : NtbOK st T Nt s := h.2.2.1.2.2.ntb

/-! ## Addresses -/

theorem tz_val {y K : U64} (hT : TcbPlaced T) (hy : Tz T y) (hK : K.val < 4096) :
    (core.num.U64.wrapping_add y K).val = y.val + K.val := by
  rcases hy with rfl | hy
  · simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; try omega
  · exact field_val (hT y hy) hK

theorem tz_aligned {y K : U64} (hT : TcbPlaced T) (hy : Tz T y) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add y K) := by
  rcases hy with rfl | hy
  · unfold Aligned; rw [tz_val hT Tz.zero hK]; all_goals simpa using hK8
  · exact field_aligned (hT y hy) hK hK8

theorem tz_big {y : U64} (hT : TcbPlaced T) (hy : y ∈ T) : 4096 ≤ y.val := by
  have := (hT y hy).ne0; have := (hT y hy).align; omega

/-- Two timer-object fields at different offsets are different words. -/
theorem tz_ne {x y K1 K2 : U64} (hT : TcbPlaced T) (hx : Tz T x) (hy : Tz T y) (h1 : K1.val < 4096)
    (h2 : K2.val < 4096) (hne : K1.val ≠ K2.val) :
    (core.num.U64.wrapping_add x K1).val ≠ (core.num.U64.wrapping_add y K2).val := by
  rw [tz_val hT hx h1, tz_val hT hy h2]
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · simp; omega
  · have := tz_big hT hy; simp; omega
  · have := tz_big hT hx; simp; omega
  · have := (hT x hx).align; have := (hT y hy).align; omega

/-- The same field of two timer objects is one word only for one object. -/
theorem tz_inj {x y K : U64} (hT : TcbPlaced T) (hx : Tz T x) (hy : Tz T y) (hK : K.val < 4096)
    (e : (core.num.U64.wrapping_add x K).val = (core.num.U64.wrapping_add y K).val) : x = y := by
  rw [tz_val hT hx hK, tz_val hT hy hK] at e
  exact UScalar.eq_of_val_eq (by omega)

/-- A node word is no timer-object field. -/
theorem node_ne_tz {s : S} {c o y K : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (hy : Tz T y) (hK : K.val < 4096) : (L.nodeAt s c o).val ≠ (core.num.U64.wrapping_add y K).val := by
  rcases hy with rfl | hy
  · rw [nodeAt_val hN ho, tz_val hT Tz.zero hK]; simp only [LawfulStore.nodeBase]; simp; omega
  · intro e; exact node_ne_field hN ho hy (hT y hy) hK (UScalar.eq_of_val_eq e)

theorem mem_wr_or {s : S} {a b v : U64} (ha : Aligned a) (hb : Aligned b) :
    L.mem (L.wr s a v) b = v ∨ L.mem (L.wr s a v) b = L.mem s b := by
  rw [L.mem_wr_val ha hb]; split <;> simp

/-! ## `TimerOK` under writes -/

/-- A write of a link (0 or a TCB) to a timer link of a timer object. -/
theorem TimerOK.wr_ptr {s : S} {x K v : U64} (h : TimerOK st T Cs s) (hT : TcbPlaced T)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hxT : x ∈ T)
    (hK : K.val = 3544 ∨ K.val = 3552 ∨ K.val = 3560 ∨ K.val = 3576 ∨ K.val = 3584)
    (hv : Tz T v) : TimerOK st T Cs (L.wr s (core.num.U64.wrapping_add x K) v) := by
  have hx : Tz T x := Tz.of_mem hxT
  have hK4 : K.val < 4096 := by omega
  have ha := tz_aligned hT hx hK4 (by omega)
  have lk : ∀ y K', y ∈ T → K'.val < 4096 → K'.val % 8 = 0 → Tz T (L.mem s (core.num.U64.wrapping_add y K')) →
      Tz T (L.mem (L.wr s (core.num.U64.wrapping_add x K) v) (core.num.U64.wrapping_add y K')) := by
    intro y K' hy h1 h2 h0
    rcases mem_wr_or (L := L) (s := s) (v := v) ha (tz_aligned hT (Tz.of_mem hy) h1 h2) with e | e <;> rw [e]
    · exact hv
    · exact h0
  have nd : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Tz T (L.mem s (L.nodeAt s c o)) →
      Tz T (L.mem (L.wr s (core.num.U64.wrapping_add x K) v)
        (L.nodeAt (L.wr s (core.num.U64.wrapping_add x K) v) c o)) := by
    intro c hc o ho h8 h0
    rw [nodeAt_of_ksb (L.ksb_wr _ _ _)]
    rcases mem_wr_or (L := L) (s := s) (v := v) ha (nodeAt_aligned (hN c hc) ho h8) with e | e <;> rw [e]
    · exact hv
    · exact h0
  have kp : ∀ y ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ K.val →
      L.mem (L.wr s (core.num.U64.wrapping_add x K) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') := fun y hy K' h1 h2 hne =>
    L.mem_wr_ne ha (tz_aligned hT (Tz.of_mem hy) h1 h2) (tz_ne hT hx (Tz.of_mem hy) hK4 h1 (Ne.symm hne))
  refine ⟨fun c hc => (hN c hc).ksb (L.ksb_wr _ _ _), fun y hy => lk y _ hy (by simp) (by simp) (h.lt y hy), fun y hy => lk y _ hy (by simp) (by simp) (h.rt y hy),
    fun y hy => lk y _ hy (by simp) (by simp) (h.pt y hy),
    fun c hc => nd c hc _ (by rw [timer_root_val]; omega) (by rw [timer_root_val]) (h.root c hc),
    fun c hc => nd c hc _ (by rw [timer_min_val]; omega) (by rw [timer_min_val]) (h.min c hc), fun y hy hd c hcv => ?_,
    fun y hy => lk y _ hy (by simp) (by simp) (h.dn y hy), fun y hy => lk y _ hy (by simp) (by simp) (h.dp y hy),
    fun c hc => nd c hc _ (by rw [debug_val]; omega) (by rw [debug_val]) (h.dh c hc)⟩
  have e1 : L.mem (L.wr s (core.num.U64.wrapping_add x K) v) (tdA y) = L.mem s (tdA y) :=
    kp y hy 3528#u64 (by simp) (by simp) (by simp; omega)
  have e2 : L.mem (L.wr s (core.num.U64.wrapping_add x K) v) (thA y) = L.mem s (thA y) :=
    kp y hy 3568#u64 (by simp) (by simp) (by simp; omega)
  rw [e1] at hd; rw [e2] at hcv
  exact h.core y hy hd c hcv

/-- A write of a timer-tree word of a core's node. -/
theorem TimerOK.wr_node {s : S} {c0 o v : U64} (h : TimerOK st T Cs s) (hT : TcbPlaced T)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hc0 : c0 ∈ Cs) (ho : o.val = 88 ∨ o.val = 104 ∨ o.val = 112)
    (hv : Tz T v) : TimerOK st T Cs (L.wr s (L.nodeAt s c0 o) v) := by
  have ho4 : o.val < 4288 := by omega
  have ha := nodeAt_aligned (hN c0 hc0) ho4 (by omega)
  have kf : ∀ y K', Tz T y → K'.val < 4096 → K'.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s c0 o) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') := fun y K' hy h1 h2 =>
    L.mem_wr_ne ha (tz_aligned hT hy h1 h2) (node_ne_tz hT (hN c0 hc0) ho4 hy h1)
  have nd : ∀ c ∈ Cs, ∀ o' : U64, o'.val < 4288 → o'.val % 8 = 0 → Tz T (L.mem s (L.nodeAt s c o')) →
      Tz T (L.mem (L.wr s (L.nodeAt s c0 o) v) (L.nodeAt (L.wr s (L.nodeAt s c0 o) v) c o')) := by
    intro c hc o' ho' h8 h0
    rw [nodeAt_of_ksb (L.ksb_wr _ _ _)]
    rcases mem_wr_or (L := L) (s := s) (v := v) ha (nodeAt_aligned (hN c hc) ho' h8) with e | e <;> rw [e]
    · exact hv
    · exact h0
  refine ⟨fun c hc => (hN c hc).ksb (L.ksb_wr _ _ _), fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun c hc => nd c hc _ (by rw [timer_root_val]; omega) (by rw [timer_root_val]) (h.root c hc),
    fun c hc => nd c hc _ (by rw [timer_min_val]; omega) (by rw [timer_min_val]) (h.min c hc), fun y hy hd c hcv => ?_,
    fun y hy => by
      rw [show dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, kf y _ (Tz.of_mem hy) (by simp) (by simp)]
      exact h.dn y hy,
    fun y hy => by
      rw [show dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, kf y _ (Tz.of_mem hy) (by simp) (by simp)]
      exact h.dp y hy,
    fun c hc => nd c hc _ (by rw [debug_val]; omega) (by rw [debug_val]) (h.dh c hc)⟩
  · rw [show tlA y = core.num.U64.wrapping_add y 3544#u64 from rfl, kf y _ (Tz.of_mem hy) (by simp) (by simp)]
    exact h.lt y hy
  · rw [show trA y = core.num.U64.wrapping_add y 3552#u64 from rfl, kf y _ (Tz.of_mem hy) (by simp) (by simp)]
    exact h.rt y hy
  · rw [show tpA y = core.num.U64.wrapping_add y 3560#u64 from rfl, kf y _ (Tz.of_mem hy) (by simp) (by simp)]
    exact h.pt y hy
  · rw [show tdA y = core.num.U64.wrapping_add y 3528#u64 from rfl, kf y _ (Tz.of_mem hy) (by simp) (by simp)] at hd
    rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, kf y _ (Tz.of_mem hy) (by simp) (by simp)] at hcv
    exact h.core y hy hd c hcv

/-- A write of a timer object's height word that keeps the core of an armed
TCB. -/
theorem TimerOK.wr_ht {s : S} {x v : U64} (h : TimerOK st T Cs s) (hT : TcbPlaced T)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hx : Tz T x)
    (hc : x ∈ T → L.mem s (tdA x) ≠ 0#u64 → ∀ c : U64, c.val = v.val >>> 8 → c ∈ Cs) :
    TimerOK st T Cs (L.wr s (thA x) v) := by
  have ha : Aligned (thA x) := tz_aligned hT hx (K := 3568#u64) (by simp) (by simp)
  have kp : ∀ y, Tz T y → ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ 3568 →
      L.mem (L.wr s (thA x) v) (core.num.U64.wrapping_add y K') = L.mem s (core.num.U64.wrapping_add y K') :=
    fun y hy K' h1 h2 hne => L.mem_wr_ne ha (tz_aligned hT hy h1 h2) (tz_ne hT hx hy (by simp) h1 (by simp; omega))
  have kn : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s (thA x) v) (L.nodeAt (L.wr s (thA x) v) c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o ho h8
    rw [nodeAt_of_ksb (L.ksb_wr _ _ _)]
    exact L.mem_wr_ne ha (nodeAt_aligned (hN c hc) ho h8) (Ne.symm (node_ne_tz hT (hN c hc) ho hx (by simp)))
  refine ⟨fun c hc => (hN c hc).ksb (L.ksb_wr _ _ _), fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun c hc => ?_, fun c hc => ?_, fun y hy hd c hcv => ?_,
    fun y hy => by
      rw [show dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl,
        kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp)]
      exact h.dn y hy,
    fun y hy => by
      rw [show dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl,
        kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp)]
      exact h.dp y hy,
    fun c hc => by rw [kn c hc _ (by rw [debug_val]; omega) (by rw [debug_val])]; exact h.dh c hc⟩
  · rw [show tlA y = core.num.U64.wrapping_add y 3544#u64 from rfl,
      kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp)]
    exact h.lt y hy
  · rw [show trA y = core.num.U64.wrapping_add y 3552#u64 from rfl,
      kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp)]
    exact h.rt y hy
  · rw [show tpA y = core.num.U64.wrapping_add y 3560#u64 from rfl,
      kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp)]
    exact h.pt y hy
  · rw [kn c hc _ (by rw [timer_root_val]; omega) (by rw [timer_root_val])]; exact h.root c hc
  · rw [kn c hc _ (by rw [timer_min_val]; omega) (by rw [timer_min_val])]; exact h.min c hc
  · rw [show tdA y = core.num.U64.wrapping_add y 3528#u64 from rfl,
      kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp)] at hd
    by_cases e : (thA x).val = (thA y).val
    · have hxy : x = y := tz_inj hT hx (Tz.of_mem hy) (by simp) e
      subst hxy
      rw [L.mem_wr_same ha] at hcv
      exact hc hy hd c hcv
    · rw [L.mem_wr_ne (b := thA y) ha (tz_aligned hT (Tz.of_mem hy) (K := 3568#u64) (by simp) (by simp)) e] at hcv
      exact h.core y hy hd c hcv

/-- Clearing a TCB's height and then its deadline. -/
theorem TimerOK.wr_clear {s : S} {t : U64} (h : TimerOK st T Cs s) (hT : TcbPlaced T)
    (hN : ∀ c ∈ Cs, NodePlaced st T s c) (ht : t ∈ T) :
    TimerOK st T Cs (L.wr (L.wr s (thA t) 0#u64) (tdA t) 0#u64) := by
  have hx := Tz.of_mem (T := T) ht
  have ha : Aligned (thA t) := tz_aligned hT hx (K := 3568#u64) (by simp) (by simp)
  have hd : Aligned (tdA t) := tz_aligned hT hx (K := 3528#u64) (by simp) (by simp)
  have kp : ∀ y, Tz T y → ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ 3568 → K'.val ≠ 3528 →
      L.mem (L.wr (L.wr s (thA t) 0#u64) (tdA t) 0#u64) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') := fun y hy K' h1 h2 hne hne' => by
    rw [L.mem_wr_ne hd (tz_aligned hT hy h1 h2) (tz_ne hT hx hy (by simp) h1 (by simp; omega)),
      L.mem_wr_ne ha (tz_aligned hT hy h1 h2) (tz_ne hT hx hy (by simp) h1 (by simp; omega))]
  have kn : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr (L.wr s (thA t) 0#u64) (tdA t) 0#u64)
        (L.nodeAt (L.wr (L.wr s (thA t) 0#u64) (tdA t) 0#u64) c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o ho h8
    rw [nodeAt_of_ksb (show L.ksb (L.wr (L.wr s (thA t) 0#u64) (tdA t) 0#u64) = L.ksb s by simp)]
    rw [L.mem_wr_ne hd (nodeAt_aligned (hN c hc) ho h8) (Ne.symm (node_ne_tz hT (hN c hc) ho hx (by simp))),
      L.mem_wr_ne ha (nodeAt_aligned (hN c hc) ho h8) (Ne.symm (node_ne_tz hT (hN c hc) ho hx (by simp)))]
  refine ⟨fun c hc => (hN c hc).ksb (by simp), fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun c hc => ?_, fun c hc => ?_, fun y hy hd' c hcv => ?_,
    fun y hy => by
      rw [show dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl,
        kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp) (by simp)]
      exact h.dn y hy,
    fun y hy => by
      rw [show dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl,
        kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp) (by simp)]
      exact h.dp y hy,
    fun c hc => by rw [kn c hc _ (by rw [debug_val]; omega) (by rw [debug_val])]; exact h.dh c hc⟩
  · rw [show tlA y = core.num.U64.wrapping_add y 3544#u64 from rfl,
      kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp) (by simp)]
    exact h.lt y hy
  · rw [show trA y = core.num.U64.wrapping_add y 3552#u64 from rfl,
      kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp) (by simp)]
    exact h.rt y hy
  · rw [show tpA y = core.num.U64.wrapping_add y 3560#u64 from rfl,
      kp y (Tz.of_mem hy) _ (by simp) (by simp) (by simp) (by simp)]
    exact h.pt y hy
  · rw [kn c hc _ (by rw [timer_root_val]; omega) (by rw [timer_root_val])]; exact h.root c hc
  · rw [kn c hc _ (by rw [timer_min_val]; omega) (by rw [timer_min_val])]; exact h.min c hc
  · have hy' := Tz.of_mem (T := T) hy
    by_cases e : t = y
    · subst e; rw [L.mem_wr_same hd] at hd'; exact absurd rfl hd'
    · have n1 : (tdA t).val ≠ (tdA y).val := fun e' => e (tz_inj hT hx hy' (by simp) e')
      have n2 : (thA t).val ≠ (thA y).val := fun e' => e (tz_inj hT hx hy' (by simp) e')
      rw [L.mem_wr_ne (b := tdA y) hd (tz_aligned hT hy' (K := 3528#u64) (by simp) (by simp)) n1,
        L.mem_wr_ne (b := tdA y) ha (tz_aligned hT hy' (K := 3528#u64) (by simp) (by simp))
          (tz_ne hT hx hy' (by simp) (by simp) (by simp))] at hd'
      rw [L.mem_wr_ne (b := thA y) hd (tz_aligned hT hy' (K := 3568#u64) (by simp) (by simp))
          (tz_ne hT hx hy' (by simp) (by simp) (by simp)),
        L.mem_wr_ne (b := thA y) ha (tz_aligned hT hy' (K := 3568#u64) (by simp) (by simp)) n2] at hcv
      exact h.core y hy hd' c hcv

/-! ## The IPC invariants under timer writes -/

/-- The timer words: a TCB's timer fields and a core's timer-tree words. -/
def TW (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s0 : S) (b : U64) : Prop :=
  (∃ y ∈ T, ∃ K : U64, 3528 ≤ K.val ∧ K.val < 3576 ∧ b = core.num.U64.wrapping_add y K) ∨
  (∃ c ∈ Cs, ∃ o : U64, (o.val = 104 ∨ o.val = 112) ∧ b = L.nodeAt s0 c o)

/-- `BlkOK` up to the timer words: the queues hold, and `BlkOK` held at a
state from which only timer words changed.  The timer code passes through
states whose trees are not yet typed. -/
def BlkT (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s : S) : Prop :=
  (∃ Q R, SchedQueuesInv st T Cs Ω H s Q R) ∧
    ∃ s0, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s0 ∧ WritesIn st s0 s (TW st T Cs s0)

theorem BlkOK.blkT {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) : BlkT st T Cs Ω H Sg Rp Scs Nt Z Ac s :=
  ⟨h.1, s, h, WritesIn.refl _ _⟩

theorem BlkOK.tinv {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s :=
  h

theorem BlkT.tcbs {s : S} (h : BlkT st T Cs Ω H Sg Rp Scs Nt Z Ac s) : TcbPlaced T := by
  obtain ⟨⟨Q, R, h0⟩, -⟩ := h; exact h0.tcbs
theorem BlkT.nodes {s : S} (h : BlkT st T Cs Ω H Sg Rp Scs Nt Z Ac s) : ∀ c ∈ Cs, NodePlaced st T s c := by
  obtain ⟨⟨Q, R, h0⟩, -⟩ := h; exact h0.nodes

/-- A timer word is not protected. -/
theorem not_prot_tw {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    {b : U64} (hb : TW st T Cs s b) : ¬ Prot T Rp Scs Nt b := by
  rcases hb with ⟨y, hy, K, hK, hK', rfl⟩ | ⟨c, hc, o, ho, rfl⟩
  · have hya := h.tcbs y hy
    intro hp
    rcases hp with ⟨r, hr, e'⟩ | ⟨c, hc, e'⟩ | ⟨u, hu, e'⟩ | ⟨n, hn, e'⟩
    rotate_right
    · have hm : core.num.U64.wrapping_add y K ∈ Ω := by rw [e']; exact hsub _ (hO.ntW n hn)
      exact out_ne_field (h.omega _ hm) hy hya (by omega) rfl
    · have hm : core.num.U64.wrapping_add y K ∈ Ω := by
        rcases e' with e' | e' | e' <;> rw [e']
        · exact hsub _ (hO.tcbW hr)
        · exact hsub _ (hO.prevW hr)
        · exact hsub _ (hO.nextW hr)
      exact out_ne_field (h.omega _ hm) hy hya (by omega) rfl
    · have hm : core.num.U64.wrapping_add y K ∈ Ω := by
        rcases e' with e' | e' | e' | e' | e' | e' <;> rw [e']
        · exact hsub _ (hO.fixW c hc).1
        · exact hsub _ (hO.fixW c hc).2
        · exact hsub _ (hO.repW c hc)
        · exact hsub _ (hO.snW c hc)
        · exact hsub _ (hO.syW c hc)
        · exact hsub _ (hO.mxW c hc)
      exact out_ne_field (h.omega _ hm) hy hya (by omega) rfl
    · rcases e' with e' | e' | e' | e' | e'
      · rw [scA_eq] at e'
        exact field_ne hya (h.tcbs u hu) (by omega) (by simp) (fun _ => by simp; omega) e'
      · exact field_ne hya (h.tcbs u hu) (by omega) (by simp) (fun _ => by simp; omega) e'
      · rw [stA_eq] at e'
        exact field_ne hya (h.tcbs u hu) (by omega) (by simp) (fun _ => by simp; omega) e'
      · exact field_ne hya (h.tcbs u hu) (by omega) (by simp) (fun _ => by simp; omega) e'
      · exact field_ne hya (h.tcbs u hu) (by omega) (by simp) (fun _ => by simp; omega) e'
  · exact not_prot_node h hO hsub hc (by omega)

/-- A write of a timer field of a TCB. -/
theorem BlkT.wr_tfield {s : S} {x K v : U64} (h : BlkT st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hx : x ∈ T)
    (hK : 3528 ≤ K.val) (hK' : K.val < 3576) (hK8 : K.val % 8 = 0) :
    BlkT st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add x K) v) := by
  obtain ⟨⟨Q, R, h0⟩, s0, hb, hw⟩ := h
  refine ⟨⟨Q, R, inv_wr_field h0 hx (by omega) hK8 (by omega)⟩, s0, hb, ?_⟩
  refine (hw.trans (writesIn_wr (v := v) (field_aligned (h0.tcbs x hx) (by omega) hK8))).mono fun b hb => ?_
  rcases hb with hb | rfl
  · exact hb
  · exact Or.inl ⟨x, hx, K, hK, hK', rfl⟩

/-- A write of a timer-tree word of a core's node. -/
theorem BlkT.wr_node {s : S} {c o v : U64} (h : BlkT st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Cs)
    (ho : o.val = 104 ∨ o.val = 112) :
    BlkT st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (L.nodeAt s c o) v) := by
  obtain ⟨⟨Q, R, h0⟩, s0, hb, hw⟩ := h
  have hN := h0.nodes c hc
  refine ⟨⟨Q, R, inv_of_free h0 (free_node_write rfl hc hN (by simp only [LowFree]; omega))⟩, s0, hb, ?_⟩
  refine (hw.trans (writesIn_wr (v := v) (nodeAt_aligned hN (by omega) (by omega)))).mono fun b hb => ?_
  rcases hb with hb | rfl
  · exact hb
  · exact Or.inr ⟨c, hc, o, ho, by rw [nodeAt_of_ksb hw.1]⟩

/-- Back to `BlkOK` once the timer trees are typed. -/
theorem BlkT.ok {s : S} (h : BlkT st T Cs Ω H Sg Rp Scs Nt Z Ac s) (htm : TimerOK st T Cs s) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨hq, s0, ⟨⟨Q0, R0, h0⟩, hB, hX, hS, hSg⟩, hw⟩ := h
  have hT := h0.tcbs
  have hN' := h0.nodes _ h0.cur
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → (K.val < 3528 ∨ 3576 ≤ K.val) → K.val % 8 = 0 →
      L.mem s (core.num.U64.wrapping_add y K) = L.mem s0 (core.num.U64.wrapping_add y K) :=
    fun y hy K hK4 hK hK8 => hw.mem_eq (field_aligned (hT y hy) (by omega) hK8) fun hb => by
      rcases hb with ⟨y', hy', K', h1, h2, e⟩ | ⟨c, hc, o, ho, e⟩
      · exact field_ne (hT y hy) (hT y' hy') (by omega) (by omega) (fun _ => by omega) e
      · exact node_ne_field (h0.nodes c hc) (by omega) hy (hT y hy) (by omega) e.symm
  have om : ∀ b ∈ Ω, L.mem s b = L.mem s0 b := fun b hb => hw.mem_eq (h0.omega _ hb).1 fun ht => by
    rcases ht with ⟨y, hy, K, h1, h2, e⟩ | ⟨c, hc, o, ho, e⟩
    · exact out_ne_field (h0.omega _ hb) hy (hT y hy) (by omega) (congrArg UScalar.val e).symm
    · exact out_ne_node (h0.omega _ hb) hc (h0.nodes c hc) (by omega) (congrArg UScalar.val e).symm
  have nd : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16 ∨ o.val = 24) →
      L.mem s (L.nodeAt s (L.cpu s) o) = L.mem s0 (L.nodeAt s0 (L.cpu s0) o) := fun o ho => by
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    exact hw.mem_eq (nodeAt_aligned hN' (by omega) (by omega)) fun hb => by
      rcases hb with ⟨y, hy, K, h1, h2, e⟩ | ⟨c, hc, o', ho', e⟩
      · exact node_ne_field hN' (by omega) hy (hT y hy) (by omega) e
      · exact node_ne_node hN' (h0.nodes c hc) (by omega) (by omega) (fun _ => by omega) (congrArg UScalar.val e)
  have hsc : ∀ y ∈ T, L.mem s (scA y) = L.mem s0 (scA y) := fun y hy => by
    rw [scA_eq]; exact fld y hy _ (by simp) (by simp) (by simp)
  have hiq : ∀ y ∈ T, L.mem s (inqA y) = L.mem s0 (inqA y) := fun y hy => by
    rw [inqA_eq]; exact fld y hy _ (by simp) (by simp) (by simp)
  have ea : L.actionW s = L.actionW s0 := by unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega)
  have ec : L.curW s = L.curW s0 := by unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega)
  have ei : L.idleW s = L.idleW s0 := by unfold LawfulStore.idleW; exact nd _ (by rw [idle8]; omega)
  have ecs : L.cscW s = L.cscW s0 := by
    unfold LawfulStore.cscW LawfulStore.nodeA; exact nd _ (by simp [layout.node.CUR_SC])
  obtain ⟨-, hcΩ⟩ := objs_omega hX.1 hSg.sub
  refine ⟨hq, hB.mk' hsc (fun y hy hf => Or.inl (by rw [← hiq y hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← hiq y hy]; exact hf))) (fun haT => ?_)
    (by rw [ei]; exact ⟨h0.idleT, hB.idle⟩) (fun h1 => ?_)
    (hB.nb ei (by rw [stA_eq]; exact fld _ h0.idleT _ (by simp) (by simp) (by simp)))
    (fun y hy hS _ => Or.inl (Sch.of_eq (fun hf => by rwa [hiq y hy] at hf) (fun hf => by rwa [hiq y hy] at hf)
      ea ei ec (by rw [stA_eq]; exact fld _ hy _ (by simp) (by simp) (by simp)) hS)),
    hX.writes hT hw (fun b hb => not_prot_tw h0 hX.1 hSg.sub hb) (by rw [ecs]; exact hX.2.2.cur)
      ⟨htm, fun n hn => by rw [om _ (hSg.sub _ (hX.1.ntB n hn).2)]; exact hX.2.2.ntb n hn⟩,
    SCsOK.keep hS hX hw.1 hsc ecs (fun c hc => ⟨om _ (hcΩ c hc).2.2.1, om _ (hcΩ c hc).2.2.2.1,
      om _ (hcΩ c hc).2.2.2.2⟩) (fun c hc => om _ (spor_omega hX.1 hc)),
    ⟨hSg.sub, fun b hb => by rw [hw.1]; exact hSg.ks b hb, fun o h1 h2 => by rw [hw.1]; exact hSg.ksΩ o h1 h2⟩⟩
  · rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩
  · rw [ea] at h1; rw [ec]; exact ⟨h0.curT, hB.resume h1⟩

/-! ## `TInv` under timer writes -/

theorem TInv.tcbs {s : S} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) : TcbPlaced T := by
  obtain ⟨⟨Q, R, h0⟩, -⟩ := h; exact h0.tcbs
theorem TInv.nodes {s : S} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) : ∀ c ∈ Cs, NodePlaced st T s c := by
  obtain ⟨⟨Q, R, h0⟩, -⟩ := h; exact h0.nodes

theorem NtbOK.wr {s : S} {a v : U64} (h : NtbOK st T Nt s) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (ha : Aligned a)
    (hne : ∀ n ∈ Nt, a.val ≠ (ntfnBtA n).val) : NtbOK st T Nt (L.wr s a v) := fun n hn => by
  rw [L.mem_wr_ne ha (ntfnBt_aligned (hO.ntP n hn)) (hne n hn)]; exact h n hn

/-- A timer-object field is no notification `BOUND_TCB` word. -/
theorem TInv.ntb_ne {s : S} {x K : U64} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hx : x ∈ T)
    (hK : K.val < 4096) (hK' : 3500 ≤ K.val) :
    ∀ n ∈ Nt, (core.num.U64.wrapping_add x K).val ≠ (ntfnBtA n).val := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, hSg⟩ := h
  intro n hn
  exact out_ne_field (h0.omega _ (hSg.sub _ (hX.1.ntB n hn).2)) hx (h0.tcbs x hx) hK

theorem TInv.ntb_ne_node {s : S} {c o : U64} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Cs)
    (ho : o.val < 4288) : ∀ n ∈ Nt, (L.nodeAt s c o).val ≠ (ntfnBtA n).val := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, hSg⟩ := h
  intro n hn
  exact out_ne_node (h0.omega _ (hSg.sub _ (hX.1.ntB n hn).2)) hc (h0.nodes c hc) ho

theorem TInv.objs {s : S} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) : ObjsOK st Ω Sg Rp Scs Nt Z s := h.2.2.1.1

theorem TInv.wr_ptr {s : S} {x K v : U64} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hx : x ∈ T) (hK : K.val = 3544 ∨ K.val = 3552 ∨ K.val = 3560) (hv : Tz T v) :
    TInv st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add x K) v) :=
  (((BlkOK.blkT h).wr_tfield hx (by omega) (by omega) (by omega)).ok (h.tm.wr_ptr h.tcbs h.nodes hx (by omega) hv)).tinv

theorem TInv.wr_ht {s : S} {x v : U64} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hx : x ∈ T) (hc : x ∈ T → L.mem s (tdA x) ≠ 0#u64 → ∀ c : U64, c.val = v.val >>> 8 → c ∈ Cs) :
    TInv st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (thA x) v) :=
  (((BlkOK.blkT h).wr_tfield (K := 3568#u64) hx (by simp) (by simp) (by simp)).ok
    (h.tm.wr_ht h.tcbs h.nodes (Tz.of_mem hx) hc)).tinv

theorem TInv.wr_node {s : S} {c o v : U64} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Cs)
    (ho : o.val = 104 ∨ o.val = 112) (hv : Tz T v) :
    TInv st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (L.nodeAt s c o) v) :=
  (((BlkOK.blkT h).wr_node hc ho).ok (h.tm.wr_node h.tcbs h.nodes hc (by omega) hv)).tinv

theorem TInv.wr_clear {s : S} {t : U64} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    TInv st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr (L.wr s (thA t) 0#u64) (tdA t) 0#u64) :=
  ((((BlkOK.blkT h).wr_tfield (K := 3568#u64) ht (by simp) (by simp) (by simp)).wr_tfield (K := 3528#u64) ht
      (by simp) (by simp) (by simp)).ok (h.tm.wr_clear h.tcbs h.nodes ht)).tinv

/-! ## The accessors -/

theorem shr8_red (i r : U64) (hr : r = 0#u64 ∨ r = 1#u64) : ((i &&& ~~~1#u64) ||| r).val >>> 8 = i.val >>> 8 := by
  have hb : ((i &&& ~~~1#u64) ||| r).bv >>> 8 = i.bv >>> 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rcases hr with rfl | rfl <;>
      simp only [BitVec.getLsbD_ushiftRight, UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and,
        BitVec.getLsbD_or, BitVec.getLsbD_not, one_bit, zero_bit] <;> simp [UScalarTy.numBits] <;>
      exact fun h => BitVec.lt_of_getLsbD h
  show ((i &&& ~~~1#u64) ||| r).bv.toNat >>> 8 = i.bv.toNat >>> 8
  rw [← BitVec.toNat_ushiftRight, ← BitVec.toNat_ushiftRight, hb]

@[step] theorem obj.Tcb.timer_left.val (s : S) (t : obj.Tcb) : obj.Tcb.timer_left st t s ⦃ v => v = L.mem s (tlA t) ⦄ := by
  unfold obj.Tcb.timer_left; step*; simp_all [tlA]
@[step] theorem obj.Tcb.timer_right.val (s : S) (t : obj.Tcb) : obj.Tcb.timer_right st t s ⦃ v => v = L.mem s (trA t) ⦄ := by
  unfold obj.Tcb.timer_right; step*; simp_all [trA]
@[step] theorem obj.Tcb.timer_parent.val (s : S) (t : obj.Tcb) :
    obj.Tcb.timer_parent st t s ⦃ v => v = L.mem s (tpA t) ⦄ := by
  unfold obj.Tcb.timer_parent; step*; simp_all [tpA]
@[step] theorem obj.Tcb.timer_height.val (s : S) (t : obj.Tcb) :
    obj.Tcb.timer_height st t s ⦃ v => v = L.mem s (thA t) ⦄ := by
  unfold obj.Tcb.timer_height; step*; simp_all [thA]
@[step] theorem obj.Tcb.timer_deadline.val (s : S) (t : obj.Tcb) :
    obj.Tcb.timer_deadline st t s ⦃ v => v = L.mem s (tdA t) ⦄ := by
  unfold obj.Tcb.timer_deadline; step*; simp_all [tdA]
@[step] theorem obj.Tcb.timer_badge.val (s : S) (t : obj.Tcb) :
    obj.Tcb.timer_badge st t s ⦃ v => v = L.mem s (tbA t) ⦄ := by
  unfold obj.Tcb.timer_badge; step*; simp_all [tbA]
theorem obj.Tcb.set_timer_left.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_timer_left st t s v ⦃ s' => s' = L.wr s (tlA t) v ⦄ := by
  unfold obj.Tcb.set_timer_left; step*; simp_all [tlA]
theorem obj.Tcb.set_timer_right.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_timer_right st t s v ⦃ s' => s' = L.wr s (trA t) v ⦄ := by
  unfold obj.Tcb.set_timer_right; step*; simp_all [trA]
theorem obj.Tcb.set_timer_parent.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_timer_parent st t s v ⦃ s' => s' = L.wr s (tpA t) v ⦄ := by
  unfold obj.Tcb.set_timer_parent; step*; simp_all [tpA]
theorem obj.Tcb.set_timer_height.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_timer_height st t s v ⦃ s' => s' = L.wr s (thA t) v ⦄ := by
  unfold obj.Tcb.set_timer_height; step*; simp_all [thA]
theorem obj.Tcb.set_timer_deadline.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_timer_deadline st t s v ⦃ s' => s' = L.wr s (tdA t) v ⦄ := by
  unfold obj.Tcb.set_timer_deadline; step*; simp_all [tdA]

/-! ## The tree operations keep `TInv` -/

theorem timer.is_red.any (s : S) (x : U64) : timer.is_red st s x ⦃ _ => True ⦄ := by
  unfold timer.is_red timer.RED; step*

theorem tcb_eq.iff (a b : obj.Tcb) : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq a b ⦃ r => r ↔ a = b ⦄ := by
  simp [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]

theorem timer.core_of.cs (s : S) (t : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hd : L.mem s (tdA t) ≠ 0#u64) : timer.core_of st s t ⦃ c => c ∈ Cs ⦄ := by
  unfold timer.core_of
  step with obj.Tcb.timer_height.val as ⟨i, ei⟩
  step as ⟨c, hc1, hc2⟩
  exact h.tm.core t ht hd c (by rw [hc1, ei])



/-! ## `TInv` with a footprint -/

/-- `TInv`, and a `KW ∅` footprint from `s0`: the timer code writes only TCB
timer fields and node timer-tree words. -/
def TF (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s0 s : S) : Prop :=
  TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧ Foot st T Cs Sg Scs Z ∅ s0 s ∧ ANI st s0 s

theorem TF.tm {s0 s : S} (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : TimerOK st T Cs s := h.1.tm
theorem TF.tcbs {s0 s : S} (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : TcbPlaced T := h.1.tcbs
theorem TF.nodes {s0 s : S} (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : ∀ c ∈ Cs, NodePlaced st T s c := h.1.nodes

theorem TF.wr_ptr {s0 s : S} {x K v : U64} (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hx : x ∈ T) (hK : K.val = 3544 ∨ K.val = 3552 ∨ K.val = 3560) (hv : Tz T v) :
    TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s (core.num.U64.wrapping_add x K) v) :=
  ⟨h.1.wr_ptr hx hK hv, h.2.1.trans (foot_field h.tcbs hx (by omega) (by omega) (by omega) (by omega)),
    h.2.2.trans (ani_field h.tcbs (h.nodes _ h.1.1.choose_spec.choose_spec.cur) hx (by omega) (by omega))⟩

theorem TF.wr_ht {s0 s : S} {x v : U64} (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hx : x ∈ T) (hc : x ∈ T → L.mem s (tdA x) ≠ 0#u64 → ∀ c : U64, c.val = v.val >>> 8 → c ∈ Cs) :
    TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s (thA x) v) :=
  ⟨h.1.wr_ht hx hc, h.2.1.trans (foot_field (K := 3568#u64) h.tcbs hx (by simp) (by simp) (by simp) (by simp)),
    h.2.2.trans (ani_field (K := 3568#u64) h.tcbs (h.nodes _ h.1.1.choose_spec.choose_spec.cur) hx (by simp) (by simp))⟩

theorem TF.wr_node {s0 s : S} {c o v : U64} (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs)
    (ho : o.val = 104 ∨ o.val = 112) (hv : Tz T v) :
    TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s (L.nodeAt s c o) v) :=
  ⟨h.1.wr_node hc ho hv, h.2.1.trans (foot_node (h.nodes c hc) hc (by omega) (by omega) (by omega)),
    h.2.2.trans (ani_node (h.nodes c hc) (h.nodes _ h.1.1.choose_spec.choose_spec.cur) (by omega) (by omega)
      (fun _ => by omega))⟩

theorem TF.wr_clear {s0 s : S} {t : U64} (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : t ∈ T) :
    TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr (L.wr s (thA t) 0#u64) (tdA t) 0#u64) :=
  ⟨h.1.wr_clear ht, (h.2.1.trans (foot_field (K := 3568#u64) h.tcbs ht (by simp) (by simp) (by simp) (by simp))).trans
    (foot_field (K := 3528#u64) h.tcbs ht (by simp) (by simp) (by simp) (by simp)),
    (h.2.2.trans (ani_field (K := 3568#u64) h.tcbs (h.nodes _ h.1.1.choose_spec.choose_spec.cur) ht (by simp)
      (by simp))).trans (ani_field (K := 3528#u64) h.tcbs
        ((h.nodes _ h.1.1.choose_spec.choose_spec.cur).ksb (L.ksb_wr _ _ _) |> fun hh => by
          rw [LawfulStore.cpu_wr]; exact hh) ht (by simp) (by simp))⟩

theorem timer.core_of.csf {s0 : S} (s : S) (t : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : t ∈ T)
    (hd : L.mem s (tdA t) ≠ 0#u64) : timer.core_of st s t ⦃ c => c ∈ Cs ⦄ :=
  timer.core_of.cs s t h.1 ht hd

section ops
variable {s0 : S}

theorem timer.left.tzf (s : S) (x : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x) :
    timer.left st s x ⦃ v => Tz T v ⦄ := by
  unfold timer.left
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 hx
  rename_i hb
  step with obj.Tcb.timer_left.val as ⟨i, ei⟩; try simp only [WP.spec_ok]
  rw [ei]; exact h.tm.lt x (hx.ne0 fun e => hb (by rw [eb, e]; rfl))
theorem timer.right.tzf (s : S) (x : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x) :
    timer.right st s x ⦃ v => Tz T v ⦄ := by
  unfold timer.right
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 hx
  rename_i hb
  step with obj.Tcb.timer_right.val as ⟨i, ei⟩; try simp only [WP.spec_ok]
  rw [ei]; exact h.tm.rt x (hx.ne0 fun e => hb (by rw [eb, e]; rfl))
theorem timer.parent.tzf (s : S) (x : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x) :
    timer.parent st s x ⦃ v => Tz T v ⦄ := by
  unfold timer.parent
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 hx
  rename_i hb
  step with obj.Tcb.timer_parent.val as ⟨i, ei⟩; try simp only [WP.spec_ok]
  rw [ei]; exact h.tm.pt x (hx.ne0 fun e => hb (by rw [eb, e]; rfl))
theorem timer.root.tzf (s : S) (c : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs) :
    timer.root st s c ⦃ v => Tz T v ⦄ := by
  unfold timer.root; step with obj.node_get.spec as ⟨i, ei⟩; try simp only [WP.spec_ok]
  rw [ei]; exact h.tm.root c hc

theorem timer.set_left.tf (s : S) (x v : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x)
    (hv : Tz T v) : timer.set_left st s x v ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.set_left
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hb
  exact WP.spec_mono (obj.Tcb.set_timer_left.wr s x v) fun s' e => by
    subst e; exact TF.wr_ptr (K := 3544#u64) h (hx.ne0 fun e => hb (by rw [eb, e]; rfl)) (by simp) hv
theorem timer.set_right.tf (s : S) (x v : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x)
    (hv : Tz T v) : timer.set_right st s x v ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.set_right
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hb
  exact WP.spec_mono (obj.Tcb.set_timer_right.wr s x v) fun s' e => by
    subst e; exact TF.wr_ptr (K := 3552#u64) h (hx.ne0 fun e => hb (by rw [eb, e]; rfl)) (by simp) hv
theorem timer.set_parent.tf (s : S) (x v : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x)
    (hv : Tz T v) : timer.set_parent st s x v ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.set_parent
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hb
  exact WP.spec_mono (obj.Tcb.set_timer_parent.wr s x v) fun s' e => by
    subst e; exact TF.wr_ptr (K := 3560#u64) h (hx.ne0 fun e => hb (by rw [eb, e]; rfl)) (by simp) hv

theorem timer.set_root.tf (s : S) (c v : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs)
    (hv : Tz T v) : timer.set_root st s c v ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.set_root
  exact WP.spec_mono (obj.node_set.spec s c _ v) fun s' e => by
    subst e; exact h.wr_node hc (by rw [timer_root_val]; simp) hv

theorem timer.set_red.tf (s : S) (x : U64) (red : Bool) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x) :
    timer.set_red st s x red ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.set_red timer.RED
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hb
  have hxT := hx.ne0 fun e => hb (by rw [eb, e]; rfl)
  step with obj.Tcb.timer_height.val as ⟨i, ei⟩
  simp only [lift, Aeneas.Std.bind_ok]
  have key : ∀ r : U64, (r = 0#u64 ∨ r = 1#u64) →
      TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s (thA x) ((i &&& ~~~1#u64) ||| r)) := fun r hr =>
    h.wr_ht hxT fun hxT hd c hc => h.tm.core x hxT hd c (by rw [hc, shr8_red i r hr, ei])
  split
  · exact WP.spec_mono (obj.Tcb.set_timer_height.wr s x _) fun s' e => by subst e; exact key _ (Or.inr rfl)
  · exact WP.spec_mono (obj.Tcb.set_timer_height.wr s x _) fun s' e => by subst e; exact key _ (Or.inl rfl)

theorem timer.replace_child.tf (s : S) (c p old new : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs)
    (hp : Tz T p) (hn : Tz T new) :
    timer.replace_child st s c p old new ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.replace_child
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact timer.set_root.tf s c new h hc hn
  · step with timer.left.tzf s p h hp as ⟨l, hl⟩
    simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, Aeneas.Std.bind_ok]
    split
    · exact timer.set_left.tf s p new h hp hn
    · exact timer.set_right.tf s p new h hp hn

theorem timer.rotate_left.tf (s : S) (c x : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs)
    (hx : Tz T x) : timer.rotate_left st s c x ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.rotate_left
  step with timer.right.tzf s x h hx as ⟨y, hy⟩
  step with timer.left.tzf s y h hy as ⟨yl, hyl⟩
  refine WP.spec_bind (timer.set_right.tf s x yl h hx hyl) fun s1 h1 => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ r.2 = x) ?_ ?_
  · split
    · simp only [WP.spec_ok]; exact ⟨h1, trivial⟩
    · refine WP.spec_bind (timer.set_parent.tf s1 yl x h1 hyl hx) fun s3 h3 => ?_
      simp only [WP.spec_ok]; exact ⟨h3, trivial⟩
  rintro ⟨s2, x1⟩ ⟨h2, e⟩
  simp only at h2 e
  subst e
  try simp only [WP.uncurry'_pair]
  step with timer.parent.tzf s2 x1 h2 hx as ⟨xp, hxp⟩
  refine WP.spec_bind (timer.set_parent.tf s2 y xp h2 hy hxp) fun s3 h3 => ?_
  refine WP.spec_bind (timer.replace_child.tf s3 c xp x1 y h3 hc hxp hy) fun s4 h4 => ?_
  refine WP.spec_bind (timer.set_left.tf s4 y x1 h4 hy hx) fun s5 h5 => ?_
  exact timer.set_parent.tf s5 x1 y h5 hx hy

theorem timer.rotate_right.tf (s : S) (c x : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs)
    (hx : Tz T x) : timer.rotate_right st s c x ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.rotate_right
  step with timer.left.tzf s x h hx as ⟨y, hy⟩
  step with timer.right.tzf s y h hy as ⟨yl, hyl⟩
  refine WP.spec_bind (timer.set_left.tf s x yl h hx hyl) fun s1 h1 => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ r.2 = x) ?_ ?_
  · split
    · simp only [WP.spec_ok]; exact ⟨h1, trivial⟩
    · refine WP.spec_bind (timer.set_parent.tf s1 yl x h1 hyl hx) fun s3 h3 => ?_
      simp only [WP.spec_ok]; exact ⟨h3, trivial⟩
  rintro ⟨s2, x1⟩ ⟨h2, e⟩
  simp only at h2 e
  subst e
  try simp only [WP.uncurry'_pair]
  step with timer.parent.tzf s2 x1 h2 hx as ⟨xp, hxp⟩
  refine WP.spec_bind (timer.set_parent.tf s2 y xp h2 hy hxp) fun s3 h3 => ?_
  refine WP.spec_bind (timer.replace_child.tf s3 c xp x1 y h3 hc hxp hy) fun s4 h4 => ?_
  refine WP.spec_bind (timer.set_right.tf s4 y x1 h4 hy hx) fun s5 h5 => ?_
  exact timer.set_parent.tf s5 x1 y h5 hx hy

theorem timer.remove_loop0.tzf (s : S) (y fuel : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hy : Tz T y) :
    timer.remove_loop0 st s y fuel ⦃ r => Tz T r ⦄ := by
  have L1 := timer.left.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  unfold timer.remove_loop0
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => Tz T x.1)
  · rintro ⟨y1, f1⟩ hy1
    simp only at hy1
    unfold timer.remove_loop0.body
    step*
  · exact hy

theorem timer.remove_loop1.tzf (s : S) (y fuel : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hy : Tz T y) :
    timer.remove_loop1 st s y fuel ⦃ r => Tz T r ⦄ := by
  have L1 := timer.left.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  unfold timer.remove_loop1
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => Tz T x.1)
  · rintro ⟨y1, f1⟩ hy1
    simp only at hy1
    unfold timer.remove_loop1.body
    step*
  · exact hy

theorem timer.remove_loop2.tzf (s : S) (y fuel : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hy : Tz T y) :
    timer.remove_loop2 st s y fuel ⦃ r => Tz T r ⦄ := by
  have L1 := timer.left.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  unfold timer.remove_loop2
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => Tz T x.1)
  · rintro ⟨y1, f1⟩ hy1
    simp only at hy1
    unfold timer.remove_loop2.body
    step*
  · exact hy

theorem timer.remove_loop3.tzf (s : S) (y fuel : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hy : Tz T y) :
    timer.remove_loop3 st s y fuel ⦃ r => Tz T r ⦄ := by
  have L1 := timer.left.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  unfold timer.remove_loop3
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => Tz T x.1)
  · rintro ⟨y1, f1⟩ hy1
    simp only at hy1
    unfold timer.remove_loop3.body
    step*
  · exact hy

theorem timer.remove_fixup_loop.tf (s : S) (c x p fuel : U64)
    (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs) (hx : Tz T x) (hp : Tz T p) :
    timer.remove_fixup_loop st s c x p fuel ⦃ r => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2 ⦄ := by
  have L1 := timer.left.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L2 := timer.right.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L3 := timer.parent.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L4 := timer.root.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L5 := timer.set_red.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L6 := timer.rotate_left.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L7 := timer.rotate_right.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L8 := timer.is_red.any (L := L)
  have L9 := tcb_eq.iff
  have z0 : Tz T 0#u64 := Tz.zero
  unfold timer.remove_fixup_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.2.val)
    (inv := fun x => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 x.1 ∧ Tz T x.2.1 ∧ Tz T x.2.2.1)
  · rintro ⟨s1, x1, p1, f1⟩ ⟨h1, hx1, hp1⟩
    simp only at h1 hx1 hp1
    unfold timer.remove_fixup_loop.body
    step*
    all_goals try (
      refine WP.spec_bind (Pₘ := fun r => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2) ?_ ?_
      · split <;> step*
      rintro ⟨sa, wa⟩ ⟨ha, hwa⟩
      simp only at ha hwa
      step*)
    all_goals try (
      refine WP.spec_bind (Pₘ := fun r => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2) ?_ ?_
      · split <;> step*
      rintro ⟨sb, wb⟩ ⟨hb, hwb⟩
      simp only at hb hwb
      step*)
  · exact ⟨h, hx, hp⟩

theorem timer.remove_fixup.tf (s : S) (c x p : U64)
    (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs) (hx : Tz T x) (hp : Tz T p) :
    timer.remove_fixup st s c x p ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.remove_fixup
  refine WP.spec_bind (timer.remove_fixup_loop.tf s c x p _ h hc hx hp) ?_
  rintro ⟨s1, x1⟩ ⟨h1, hx1⟩
  simp only at h1 hx1
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 h1
  · exact timer.set_red.tf s1 x1 false h1 hx1

set_option maxHeartbeats 2000000 in
theorem timer.remove.tf (s : S) (t : U64) (h : TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (ht : t ∈ T) : timer.remove st s t ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have L1 := timer.left.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L2 := timer.right.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L3 := timer.parent.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L5 := timer.set_red.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L6 := timer.replace_child.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L7 := timer.remove_fixup.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L8 := timer.is_red.any (L := L)
  have L9 := tcb_eq.iff
  have W1 := timer.set_left.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have W2 := timer.set_right.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have W3 := timer.set_parent.tf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have R0 := timer.remove_loop0.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have R1 := timer.remove_loop1.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have R2 := timer.remove_loop2.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have R3 := timer.remove_loop3.tzf (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have hTot := L.total
  have z0 : Tz T 0#u64 := Tz.zero
  have htz : Tz T t := Tz.of_mem ht
  unfold timer.remove
  step with obj.Tcb.timer_deadline.val as ⟨i, ei⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hi
  have hd : L.mem s (tdA t) ≠ 0#u64 := by rw [← ei]; exact hi
  step with timer.core_of.csf s t h ht hd as ⟨cpu, hcpu⟩
  have NS : ∀ (s : S) (v : U64), TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → Tz T v →
      obj.node_set st s cpu layout.node.TIMER_MIN v ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ :=
    fun s v h hv => WP.spec_mono (obj.node_set.spec s cpu _ v) fun s' e => by
      subst e; exact h.wr_node hcpu (by rw [timer_min_val]; simp) hv
  have HH : ∀ s0 : S, obj.Tcb.set_timer_height st t s0 0#u64 ⦃ s' => s' = L.wr s0 (thA t) 0#u64 ⦄ :=
    fun s0 => obj.Tcb.set_timer_height.wr s0 t 0#u64
  have HD : ∀ s7 s8 : S, s8 = L.wr s7 (thA t) 0#u64 → TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s7 →
      obj.Tcb.set_timer_deadline st t s8 0#u64 ⦃ s' => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ :=
    fun s7 s8 e h7 => WP.spec_mono (obj.Tcb.set_timer_deadline.wr s8 t 0#u64) fun s' e' => by
      subst e e'; exact h7.wr_clear ht
  step*
  all_goals try (
    refine WP.spec_bind (Pₘ := fun r => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2) ?_ ?_
    · split <;> step*
    rintro ⟨sa, wa⟩ ⟨ha, hwa⟩
    simp only at ha hwa
    step*)
  all_goals try (
    refine WP.spec_bind (Pₘ := fun r => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2.1 ∧ Tz T r.2.2.1 ∧
      Tz T r.2.2.2) ?_ ?_
    · split
      · step*
      · step*
        all_goals try (
          refine WP.spec_bind (Pₘ := fun r => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2) ?_ ?_
          · split <;> step*
          rintro ⟨sa, wa⟩ ⟨ha, hwa⟩
          simp only at ha hwa
          step*)
    rintro ⟨sa, xa, pa, ya⟩ ⟨ha, hxa, hpa, hya⟩
    simp only at ha hxa hpa hya
    step*)
  all_goals try (
    refine WP.spec_bind (Pₘ := fun r => TF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r) ?_ ?_
    · split <;> step*
    intro sb hb
    step*)

end ops

/-! ## The `TInv` forms -/

theorem timer.left.tz (s : S) (x : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hx : Tz T x) :
    timer.left st s x ⦃ v => Tz T v ⦄ := timer.left.tzf (s0 := s) s x ⟨h, Foot.refl _, ANI.refl _⟩ hx
theorem timer.right.tz (s : S) (x : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hx : Tz T x) :
    timer.right st s x ⦃ v => Tz T v ⦄ := timer.right.tzf (s0 := s) s x ⟨h, Foot.refl _, ANI.refl _⟩ hx
theorem timer.parent.tz (s : S) (x : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hx : Tz T x) :
    timer.parent st s x ⦃ v => Tz T v ⦄ := timer.parent.tzf (s0 := s) s x ⟨h, Foot.refl _, ANI.refl _⟩ hx
theorem timer.root.tz (s : S) (c : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Cs) :
    timer.root st s c ⦃ v => Tz T v ⦄ := timer.root.tzf (s0 := s) s c ⟨h, Foot.refl _, ANI.refl _⟩ hc
theorem timer.set_left.tinv (s : S) (x v : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hx : Tz T x)
    (hv : Tz T v) : timer.set_left st s x v ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (timer.set_left.tf (s0 := s) s x v ⟨h, Foot.refl _, ANI.refl _⟩ hx hv) fun _ h' => h'.1
theorem timer.set_right.tinv (s : S) (x v : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hx : Tz T x)
    (hv : Tz T v) : timer.set_right st s x v ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (timer.set_right.tf (s0 := s) s x v ⟨h, Foot.refl _, ANI.refl _⟩ hx hv) fun _ h' => h'.1
theorem timer.set_parent.tinv (s : S) (x v : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hx : Tz T x)
    (hv : Tz T v) : timer.set_parent st s x v ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (timer.set_parent.tf (s0 := s) s x v ⟨h, Foot.refl _, ANI.refl _⟩ hx hv) fun _ h' => h'.1
theorem timer.set_root.tinv (s : S) (c v : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Cs)
    (hv : Tz T v) : timer.set_root st s c v ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (timer.set_root.tf (s0 := s) s c v ⟨h, Foot.refl _, ANI.refl _⟩ hc hv) fun _ h' => h'.1
theorem timer.set_red.tinv (s : S) (x : U64) (red : Bool) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hx : Tz T x) :
    timer.set_red st s x red ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (timer.set_red.tf (s0 := s) s x red ⟨h, Foot.refl _, ANI.refl _⟩ hx) fun _ h' => h'.1
theorem timer.rotate_left.tinv (s : S) (c x : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Cs)
    (hx : Tz T x) : timer.rotate_left st s c x ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (timer.rotate_left.tf (s0 := s) s c x ⟨h, Foot.refl _, ANI.refl _⟩ hc hx) fun _ h' => h'.1
theorem timer.rotate_right.tinv (s : S) (c x : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Cs)
    (hx : Tz T x) : timer.rotate_right st s c x ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (timer.rotate_right.tf (s0 := s) s c x ⟨h, Foot.refl _, ANI.refl _⟩ hc hx) fun _ h' => h'.1
theorem timer.remove.tinv (s : S) (t : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) : timer.remove st s t ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (timer.remove.tf (s0 := s) s t ⟨h, Foot.refl _, ANI.refl _⟩ ht) fun _ h' => h'.1


end

end Fl4Proofs.P1

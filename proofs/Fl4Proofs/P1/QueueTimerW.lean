/-
P1: timer-object addresses and the typing `TimerOK` under writes of a timer
link or a node's timer-tree word (split out of QueueTimer so that QueueIpc,
which writes debug links when `migrate_tcb` moves a thread, can use them).
-/
import Fl4Proofs.P1.QueueBlock
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}
variable {Cs : Set U64} {Ω : Set U64} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

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

theorem NtbOK.wr {s : S} {a v : U64} (h : NtbOK st T Nt s) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (ha : Aligned a)
    (hne : ∀ n ∈ Nt, a.val ≠ (ntfnBtA n).val) : NtbOK st T Nt (L.wr s a v) := fun n hn => by
  rw [L.mem_wr_ne ha (ntfnBt_aligned (hO.ntP n hn)) (hne n hn)]; exact h n hn

end

end Fl4Proofs.P1

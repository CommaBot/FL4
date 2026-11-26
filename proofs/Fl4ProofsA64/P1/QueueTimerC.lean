-- AArch64 port of Fl4Proofs.P1.QueueTimerC (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: the timer-tree frame `TF` with the current SC word kept (`TF2`, a
separate conjunct, so `TF` and its callers are unchanged): `timer.remove`
keeps `CUR_SC` (`timer.remove.csc`).
-/
import Fl4ProofsA64.P1.QueueFinCur
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- `TFB` with the current SC word kept. -/
def TF2 (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s0 s : S) : Prop :=
  TFB st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s ∧ L.cscW s = L.cscW s0

theorem TF2.start {s : S} (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s s :=
  ⟨TFB.start h, rfl⟩

theorem TF2.tm {s0 s : S} (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : TimerOK st T Cs s := h.1.tm

theorem cscW_wr_node {s : S} {c o v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c)
    (hN' : NodePlaced st T s (L.cpu s)) (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h24 : o.val ≠ 24) :
    L.cscW (L.wr s (L.nodeAt s c o) v) = L.cscW s := by
  unfold LawfulStore.cscW; rw [nodeA_wr]
  refine L.mem_wr_ne (nodeAt_aligned hN ho h8)
    (nodeAt_aligned hN' (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])) fun e => ?_
  unfold LawfulStore.nodeA at e
  rw [nodeAt_val hN ho, nodeAt_val hN' (by simp [layout.node.CUR_SC])] at e
  simp only [LawfulStore.nodeBase] at e
  have : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]
  rw [this] at e
  rcases Nat.lt_trichotomy c.val (L.cpu s).val with hl | hl | hl
  · have : c.val * 4288 + 4288 ≤ (L.cpu s).val * 4288 := by nlinarith
    omega
  · rw [hl] at e; omega
  · have : (L.cpu s).val * 4288 + 4288 ≤ c.val * 4288 := by nlinarith
    omega

theorem TF2.wr_ptr {s0 s : S} {x K v : U64} (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hx : x ∈ T) (hK : K.val = 3544 ∨ K.val = 3552 ∨ K.val = 3560) (hv : Tz T v) :
    TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s (core.num.U64.wrapping_add x K) v) :=
  ⟨h.1.wr_ptr hx hK hv, (cscW_wr_field h.1.tcbs (h.1.nodes _ h.1.cur) hx
    (by omega) (by omega)).trans h.2⟩

theorem TF2.wr_ht {s0 s : S} {x v : U64} (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hx : x ∈ T) (hc : x ∈ T → L.mem s (tdA x) ≠ 0#u64 → ∀ c : U64, c.val = v.val >>> 8 → c ∈ Cs) :
    TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s (thA x) v) :=
  ⟨h.1.wr_ht hx hc, (cscW_wr_field (K := 3568#u64) h.1.tcbs (h.1.nodes _ h.1.cur) hx
    (by simp) (by simp)).trans h.2⟩

theorem TF2.wr_node {s0 s : S} {c o v : U64} (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs)
    (ho : o.val = 104 ∨ o.val = 112) (hv : Tz T v) :
    TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s (L.nodeAt s c o) v) :=
  ⟨h.1.wr_node hc ho hv, (cscW_wr_node h.1.tcbs (h.1.nodes c hc) (h.1.nodes _ h.1.cur)
    (by omega) (by omega) (by omega)).trans h.2⟩

theorem TF2.wr_clear {s0 s : S} {t : U64} (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : t ∈ T) :
    TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr (L.wr s (tdA t) 0#u64) (thA t) 0#u64) := by
  have hN := h.1.nodes _ h.1.cur
  refine ⟨h.1.wr_clear ht, ?_⟩
  rw [thA, cscW_wr_field (K := 3568#u64) h.1.tcbs ((hN.ksb (L.ksb_wr _ _ _)) |> fun hh => by
      rw [LawfulStore.cpu_wr]; exact hh) ht (by simp) (by simp),
    tdA, cscW_wr_field (K := 3528#u64) h.1.tcbs hN ht (by simp) (by simp)]
  exact h.2

theorem timer.core_of.csf2 {s0 : S} (s : S) (t : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : t ∈ T)
    (hd : L.mem s (tdA t) ≠ 0#u64) : timer.core_of st s t ⦃ c => c ∈ Cs ⦄ :=
  timer.core_of.cstm s t h.1.tm ht hd

section ops2
variable {s0 : S}

theorem timer.left.tzf2 (s : S) (x : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x) :
    timer.left st s x ⦃ v => Tz T v ⦄ := by
  unfold timer.left
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 hx
  rename_i hb
  step with obj.Tcb.timer_left.val as ⟨i, ei⟩; try simp only [WP.spec_ok]
  rw [ei]; exact h.tm.lt x (hx.ne0 fun e => hb (by rw [eb, e]; rfl))
theorem timer.right.tzf2 (s : S) (x : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x) :
    timer.right st s x ⦃ v => Tz T v ⦄ := by
  unfold timer.right
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 hx
  rename_i hb
  step with obj.Tcb.timer_right.val as ⟨i, ei⟩; try simp only [WP.spec_ok]
  rw [ei]; exact h.tm.rt x (hx.ne0 fun e => hb (by rw [eb, e]; rfl))
theorem timer.parent.tzf2 (s : S) (x : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x) :
    timer.parent st s x ⦃ v => Tz T v ⦄ := by
  unfold timer.parent
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 hx
  rename_i hb
  step with obj.Tcb.timer_parent.val as ⟨i, ei⟩; try simp only [WP.spec_ok]
  rw [ei]; exact h.tm.pt x (hx.ne0 fun e => hb (by rw [eb, e]; rfl))
theorem timer.root.tzf2 (s : S) (c : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs) :
    timer.root st s c ⦃ v => Tz T v ⦄ := by
  unfold timer.root; step with obj.node_get.spec as ⟨i, ei⟩; try simp only [WP.spec_ok]
  rw [ei]; exact h.tm.root c hc

theorem timer.set_left.tf2 (s : S) (x v : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x)
    (hv : Tz T v) : timer.set_left st s x v ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.set_left
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hb
  exact WP.spec_mono (obj.Tcb.set_timer_left.wr s x v) fun s' e => by
    subst e; exact TF2.wr_ptr (K := 3544#u64) h (hx.ne0 fun e => hb (by rw [eb, e]; rfl)) (by simp) hv
theorem timer.set_right.tf2 (s : S) (x v : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x)
    (hv : Tz T v) : timer.set_right st s x v ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.set_right
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hb
  exact WP.spec_mono (obj.Tcb.set_timer_right.wr s x v) fun s' e => by
    subst e; exact TF2.wr_ptr (K := 3552#u64) h (hx.ne0 fun e => hb (by rw [eb, e]; rfl)) (by simp) hv
theorem timer.set_parent.tf2 (s : S) (x v : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x)
    (hv : Tz T v) : timer.set_parent st s x v ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.set_parent
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hb
  exact WP.spec_mono (obj.Tcb.set_timer_parent.wr s x v) fun s' e => by
    subst e; exact TF2.wr_ptr (K := 3560#u64) h (hx.ne0 fun e => hb (by rw [eb, e]; rfl)) (by simp) hv

theorem timer.set_root.tf2 (s : S) (c v : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs)
    (hv : Tz T v) : timer.set_root st s c v ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.set_root
  exact WP.spec_mono (obj.node_set.spec s c _ v) fun s' e => by
    subst e; exact h.wr_node hc (by rw [timer_root_val]; simp) hv

theorem timer.set_red.tf2 (s : S) (x : U64) (red : Bool) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : Tz T x) :
    timer.set_red st s x red ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.set_red timer.RED
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hb
  have hxT := hx.ne0 fun e => hb (by rw [eb, e]; rfl)
  step with obj.Tcb.timer_height.val as ⟨i, ei⟩
  simp only [lift, Aeneas.Std.bind_ok]
  have key : ∀ r : U64, (r = 0#u64 ∨ r = 1#u64) →
      TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s (thA x) ((i &&& ~~~1#u64) ||| r)) := fun r hr =>
    h.wr_ht hxT fun hxT hd c hc => h.tm.core x hxT hd c (by rw [hc, shr8_red i r hr, ei])
  split
  · exact WP.spec_mono (obj.Tcb.set_timer_height.wr s x _) fun s' e => by subst e; exact key _ (Or.inr rfl)
  · exact WP.spec_mono (obj.Tcb.set_timer_height.wr s x _) fun s' e => by subst e; exact key _ (Or.inl rfl)

theorem timer.replace_child.tf2 (s : S) (c p old new : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs)
    (hp : Tz T p) (hn : Tz T new) :
    timer.replace_child st s c p old new ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.replace_child
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact timer.set_root.tf2 s c new h hc hn
  · step with timer.left.tzf2 s p h hp as ⟨l, hl⟩
    simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, Aeneas.Std.bind_ok]
    split
    · exact timer.set_left.tf2 s p new h hp hn
    · exact timer.set_right.tf2 s p new h hp hn

theorem timer.rotate_left.tf2 (s : S) (c x : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs)
    (hx : Tz T x) : timer.rotate_left st s c x ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.rotate_left
  step with timer.right.tzf2 s x h hx as ⟨y, hy⟩
  step with timer.left.tzf2 s y h hy as ⟨yl, hyl⟩
  refine WP.spec_bind (timer.set_right.tf2 s x yl h hx hyl) fun s1 h1 => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ r.2 = x) ?_ ?_
  · split
    · simp only [WP.spec_ok]; exact ⟨h1, trivial⟩
    · refine WP.spec_bind (timer.set_parent.tf2 s1 yl x h1 hyl hx) fun s3 h3 => ?_
      simp only [WP.spec_ok]; exact ⟨h3, trivial⟩
  rintro ⟨s2, x1⟩ ⟨h2, e⟩
  simp only at h2 e
  subst e
  try simp only [WP.uncurry'_pair]
  step with timer.parent.tzf2 s2 x1 h2 hx as ⟨xp, hxp⟩
  refine WP.spec_bind (timer.set_parent.tf2 s2 y xp h2 hy hxp) fun s3 h3 => ?_
  refine WP.spec_bind (timer.replace_child.tf2 s3 c xp x1 y h3 hc hxp hy) fun s4 h4 => ?_
  refine WP.spec_bind (timer.set_left.tf2 s4 y x1 h4 hy hx) fun s5 h5 => ?_
  exact timer.set_parent.tf2 s5 x1 y h5 hx hy

theorem timer.rotate_right.tf2 (s : S) (c x : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs)
    (hx : Tz T x) : timer.rotate_right st s c x ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.rotate_right
  step with timer.left.tzf2 s x h hx as ⟨y, hy⟩
  step with timer.right.tzf2 s y h hy as ⟨yl, hyl⟩
  refine WP.spec_bind (timer.set_left.tf2 s x yl h hx hyl) fun s1 h1 => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ r.2 = x) ?_ ?_
  · split
    · simp only [WP.spec_ok]; exact ⟨h1, trivial⟩
    · refine WP.spec_bind (timer.set_parent.tf2 s1 yl x h1 hyl hx) fun s3 h3 => ?_
      simp only [WP.spec_ok]; exact ⟨h3, trivial⟩
  rintro ⟨s2, x1⟩ ⟨h2, e⟩
  simp only at h2 e
  subst e
  try simp only [WP.uncurry'_pair]
  step with timer.parent.tzf2 s2 x1 h2 hx as ⟨xp, hxp⟩
  refine WP.spec_bind (timer.set_parent.tf2 s2 y xp h2 hy hxp) fun s3 h3 => ?_
  refine WP.spec_bind (timer.replace_child.tf2 s3 c xp x1 y h3 hc hxp hy) fun s4 h4 => ?_
  refine WP.spec_bind (timer.set_right.tf2 s4 y x1 h4 hy hx) fun s5 h5 => ?_
  exact timer.set_parent.tf2 s5 x1 y h5 hx hy

theorem timer.remove_loop0.tzf2 (s : S) (y fuel : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hy : Tz T y) :
    timer.remove_loop0 st s y fuel ⦃ r => Tz T r ⦄ := by
  have L1 := timer.left.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  unfold timer.remove_loop0
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => Tz T x.1)
  · rintro ⟨y1, f1⟩ hy1
    simp only at hy1
    unfold timer.remove_loop0.body
    step*
  · exact hy

theorem timer.remove_loop1.tzf2 (s : S) (y fuel : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hy : Tz T y) :
    timer.remove_loop1 st s y fuel ⦃ r => Tz T r ⦄ := by
  have L1 := timer.left.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  unfold timer.remove_loop1
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => Tz T x.1)
  · rintro ⟨y1, f1⟩ hy1
    simp only at hy1
    unfold timer.remove_loop1.body
    step*
  · exact hy

theorem timer.remove_loop2.tzf2 (s : S) (y fuel : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hy : Tz T y) :
    timer.remove_loop2 st s y fuel ⦃ r => Tz T r ⦄ := by
  have L1 := timer.left.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  unfold timer.remove_loop2
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => Tz T x.1)
  · rintro ⟨y1, f1⟩ hy1
    simp only at hy1
    unfold timer.remove_loop2.body
    step*
  · exact hy

theorem timer.remove_loop3.tzf2 (s : S) (y fuel : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hy : Tz T y) :
    timer.remove_loop3 st s y fuel ⦃ r => Tz T r ⦄ := by
  have L1 := timer.left.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  unfold timer.remove_loop3
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => Tz T x.1)
  · rintro ⟨y1, f1⟩ hy1
    simp only at hy1
    unfold timer.remove_loop3.body
    step*
  · exact hy

theorem timer.remove_fixup_loop.tf2 (s : S) (c x p fuel : U64)
    (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs) (hx : Tz T x) (hp : Tz T p) :
    timer.remove_fixup_loop st s c x p fuel ⦃ r => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2 ⦄ := by
  have L1 := timer.left.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L2 := timer.right.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L3 := timer.parent.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L4 := timer.root.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L5 := timer.set_red.tf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L6 := timer.rotate_left.tf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L7 := timer.rotate_right.tf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L8 := timer.is_red.any (L := L)
  have L9 := tcb_eq.iff
  have z0 : Tz T 0#u64 := Tz.zero
  unfold timer.remove_fixup_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.2.val)
    (inv := fun x => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 x.1 ∧ Tz T x.2.1 ∧ Tz T x.2.2.1)
  · rintro ⟨s1, x1, p1, f1⟩ ⟨h1, hx1, hp1⟩
    simp only at h1 hx1 hp1
    unfold timer.remove_fixup_loop.body
    step*
    all_goals try (
      refine WP.spec_bind (Pₘ := fun r => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2) ?_ ?_
      · split <;> step*
      rintro ⟨sa, wa⟩ ⟨ha, hwa⟩
      simp only at ha hwa
      step*)
    all_goals try (
      refine WP.spec_bind (Pₘ := fun r => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2) ?_ ?_
      · split <;> step*
      rintro ⟨sb, wb⟩ ⟨hb, hwb⟩
      simp only at hb hwb
      step*)
  · exact ⟨h, hx, hp⟩

theorem timer.remove_fixup.tf2 (s : S) (c x p : U64)
    (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hc : c ∈ Cs) (hx : Tz T x) (hp : Tz T p) :
    timer.remove_fixup st s c x p ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold timer.remove_fixup
  refine WP.spec_bind (timer.remove_fixup_loop.tf2 s c x p _ h hc hx hp) ?_
  rintro ⟨s1, x1⟩ ⟨h1, hx1⟩
  simp only at h1 hx1
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 h1
  · exact timer.set_red.tf2 s1 x1 false h1 hx1

set_option maxHeartbeats 2000000 in
theorem timer.remove.tf2 (s : S) (t : U64) (h : TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (ht : t ∈ T) : timer.remove st s t ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have L1 := timer.left.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L2 := timer.right.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L3 := timer.parent.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L5 := timer.set_red.tf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L6 := timer.replace_child.tf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L7 := timer.remove_fixup.tf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have L8 := timer.is_red.any (L := L)
  have L9 := tcb_eq.iff
  have W1 := timer.set_left.tf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have W2 := timer.set_right.tf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have W3 := timer.set_parent.tf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have R0 := timer.remove_loop0.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have R1 := timer.remove_loop1.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have R2 := timer.remove_loop2.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have R3 := timer.remove_loop3.tzf2 (L := L) (T := T) (Cs := Cs) (Z := Z) (Ω := Ω) (H := H) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (s0 := s0) (Ac := Ac)
  have hTot := L.total
  have z0 : Tz T 0#u64 := Tz.zero
  have htz : Tz T t := Tz.of_mem ht
  unfold timer.remove
  step with obj.Tcb.timer_deadline.val as ⟨i, ei⟩
  split
  · exact (WP.spec_ok _).2 h
  rename_i hi
  have hd : L.mem s (tdA t) ≠ 0#u64 := by rw [← ei]; exact hi
  step with timer.core_of.csf2 s t h ht hd as ⟨cpu, hcpu⟩
  have NS : ∀ (s : S) (v : U64), TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → Tz T v →
      obj.node_set st s cpu layout.node.TIMER_MIN v ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ :=
    fun s v h hv => WP.spec_mono (obj.node_set.spec s cpu _ v) fun s' e => by
      subst e; exact h.wr_node hcpu (by rw [timer_min_val]; simp) hv
  have HH : ∀ s0 : S, obj.Tcb.set_timer_deadline st t s0 0#u64 ⦃ s' => s' = L.wr s0 (tdA t) 0#u64 ⦄ :=
    fun s0 => obj.Tcb.set_timer_deadline.wr s0 t 0#u64
  have HD : ∀ s7 s8 : S, s8 = L.wr s7 (tdA t) 0#u64 → TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s7 →
      obj.Tcb.set_timer_height st t s8 0#u64 ⦃ s' => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ :=
    fun s7 s8 e h7 => WP.spec_mono (obj.Tcb.set_timer_height.wr s8 t 0#u64) fun s' e' => by
      subst e e'; exact h7.wr_clear ht
  step*
  all_goals try (
    refine WP.spec_bind (Pₘ := fun r => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2) ?_ ?_
    · split <;> step*
    rintro ⟨sa, wa⟩ ⟨ha, hwa⟩
    simp only at ha hwa
    step*)
  all_goals try (
    refine WP.spec_bind (Pₘ := fun r => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2.1 ∧ Tz T r.2.2.1 ∧
      Tz T r.2.2.2) ?_ ?_
    · split
      · step*
      · step*
        all_goals try (
          refine WP.spec_bind (Pₘ := fun r => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ Tz T r.2) ?_ ?_
          · split <;> step*
          rintro ⟨sa, wa⟩ ⟨ha, hwa⟩
          simp only at ha hwa
          step*)
    rintro ⟨sa, xa, pa, ya⟩ ⟨ha, hxa, hpa, hya⟩
    simp only at ha hxa hpa hya
    step*)
  all_goals try (
    refine WP.spec_bind (Pₘ := fun r => TF2 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r) ?_ ?_
    · split <;> step*
    intro sb hb
    step*)

end ops2

/-- **`timer.remove` keeps the current SC word.** -/
theorem timer.remove.csc (s : S) (t : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    timer.remove st s t ⦃ s' => L.cscW s' = L.cscW s ⦄ :=
  WP.spec_mono (timer.remove.tf2 (s0 := s) s t (TF2.start h) ht) fun _ h' => h'.2

end

end Fl4ProofsA64.P1

/-
P1 (aarch64, gen 59): **the zero free-memory fact `UtZeroA`** (Architect ruling, option (a): no kernel change) and
**the write frame of a `Tcb` creation** read off it.

* **`UtZeroA st OS s`**: every aligned word of the free part `[p + i, p + 2^b)` of every RAM `Untyped p b i false`
  cap held in an `OS` slot reads 0. l4v: Untyped_AI / Invariants_AI `untyped_ranges_zero` (the free part of every
  non-device untyped is zero); x86: P3 BufDefs `UtZero` (over the spec memory). FL4 source: untyped.rs:225–262
  (`reset_untyped` clears `[ptr, ptr + free_index)` before lowering the index), untyped.rs:266–288 (`retype` raises
  the free index past the new objects). Device untypeds are left out as in `ValidUntypedA` (MdbVU).
* Boot: **`UtZeroA.empty`** (all `OS` slots null, as `ValidUntypedA.empty`).
* Transfer: **`UtZeroA.of_ub`** (every `OS` slot after is `UB` an `OS` slot before, memory kept on the free parts
  before), **`UtZeroA.writes`** (a write frame off every RAM free part), **`UtZeroA.capw`** (a write frame of
  cap-slot words `CapW H.tcbs H.omega Sg`: with `ValidUntypedA` and `HeapOK` every such word lies in a heap object,
  so off every RAM free part, `capw_off`), **`obj.Slot.set_cap.uz`**, `UtZeroA.sub`, `UtZeroA.keepC` (memory
  kept off `OS`'s caps: any step whose write frame is `CapW` and keeps the caps).
* **The `Tcb` arm of `create_object`** (objects.rs:447–474, 418–427; the A64 port of x86 P3 UntypedTcb
  `create_tcb_frame`): `regs::init_context` (37 register words from `REGS` = 256, regs.rs), `init_fpu` /
  `debug::init_context` (no-ops on AArch64), `set_domain` (`F + 104`), `set_child_name` (name words from
  `F + 272`), all inside `[t, t + 4096)` and off the affinity word `t + 3520` (**`TFw`**); then **`debug_append`**:
  with the affinity word 0 (`UtZeroA`: the new TCB lies in zeroed free memory), `cpu = 0`, so it writes the new
  TCB's two debug links, the old head's `DEBUG_PREV` word (`dpA head`) and node 0's `DEBUG_TCBS` word.
  **`create_object.tcbW`**: `create_object` of type 1 returns `newCapA` (`Thread`), writes only
  `InWin t 4096 ∪ {nw} ∪ {dpA head}` (`nw` = node 0's `DEBUG_TCBS` word), and leaves `t` in `nw`.

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbVUZ
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **l4v `untyped_ranges_zero`, A64 form** (module docstring): the free part of every RAM untyped cap of `OS`
reads 0. -/
def UtZeroA (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop :=
  ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false → ∀ a : U64, Aligned a → p.val + i.val ≤ a.val →
    a.val < p.val + 2 ^ b.val → L.mem s a = 0#u64

variable {OS : Set U64} {H : Heap}

/-- **Boot**: null `OS` slots. -/
theorem UtZeroA.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : UtZeroA st OS s :=
  fun u hu p b i hc => by rw [h u hu] at hc; cases hc

theorem UtZeroA.sub {OS' : Set U64} {s : S} (h : UtZeroA st OS s) (hs : OS' ⊆ OS) : UtZeroA st OS' s :=
  fun u hu => h u (hs hu)

/-- **Transfer** (module docstring). -/
theorem UtZeroA.of_ub {OS' : Set U64} {s s' : S} (h : UtZeroA st OS s)
    (hc : ∀ y ∈ OS', ∃ y0 ∈ OS, UB (capA st s' y) (capA st s y0))
    (hm : ∀ y0 ∈ OS, ∀ p b i, capA st s y0 = .Untyped p b i false → ∀ a : U64, Aligned a →
      p.val + i.val ≤ a.val → a.val < p.val + 2 ^ b.val → L.mem s' a = L.mem s a) : UtZeroA st OS' s' := by
  intro u hu p b i hcu a ha h1 h2
  obtain ⟨y0, hy0, hb⟩ := hc u hu
  obtain ⟨i0, hc0, hle⟩ := hb p b i hcu
  rw [hm y0 hy0 p b i0 hc0 a ha (by omega) h2]
  exact h y0 hy0 p b i0 hc0 a ha (by omega) h2

/-- **A write frame off every RAM free part** keeps the fact (caps `UB` the old ones). -/
theorem UtZeroA.writes {s s' : S} {F : U64 → Prop} (h : UtZeroA st OS s) (hw : WritesIn st s s' F)
    (hF : ∀ y0 ∈ OS, ∀ p b i, capA st s y0 = .Untyped p b i false → ∀ w, F w →
      w.val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ w.val)
    (hc : ∀ y ∈ OS, ∃ y0 ∈ OS, UB (capA st s' y) (capA st s y0)) : UtZeroA st OS s' :=
  h.of_ub hc fun y0 hy0 p b i hcy a ha h1 h2 => hw.mem_eq ha fun hFa => by
    rcases hF y0 hy0 p b i hcy a hFa with g | g <;> omega

/-- **Cap-slot words lie off every RAM free part** (`ValidUntypedA.word_off`'s argument for any `CapW` word). -/
theorem capw_off {Sg : Set U64} (hH : HeapOK H) {s : S} (hV : ValidUntypedA st H OS s) {u p b i : U64}
    (hu : u ∈ OS) (hc : capA st s u = .Untyped p b i false) {w : U64} (hw : W7.CapW H.tcbs H.omega Sg w) :
    w.val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ w.val := by
  rcases hw with ⟨t, ht, K, hK, e⟩ | ⟨⟨-, q, k, hq, -, hin⟩, -⟩
  · rw [e, wa_val]
    have ht' : H t = some .tcb := ht
    have hf := hH.fits t _ ht'
    have g := hV u hu p b i hc t .tcb ht'
    simp only [HKind.bits] at hf g
    rcases g with g | g
    · left; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · right; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · unfold InObj at hin
    rcases hV u hu p b i hc q k hq with g | g
    · left; omega
    · right; omega

/-- **A step writing only cap-slot words** keeps the fact. -/
theorem UtZeroA.capw {Sg : Set U64} (hH : HeapOK H) {s s' : S} (h : UtZeroA st OS s)
    (hV : ValidUntypedA st H OS s) (hw : WritesIn st s s' (W7.CapW H.tcbs H.omega Sg))
    (hc : ∀ y ∈ OS, ∃ y0 ∈ OS, UB (capA st s' y) (capA st s y0)) : UtZeroA st OS s' :=
  h.writes hw (fun y0 hy0 p b i hcy w hw' => capw_off hH hV hy0 hcy hw') hc

/-- **`set_cap` of an `OS` slot with a cap `UB` the old one.** -/
theorem obj.Slot.set_cap.uz {Sg : Set U64} (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S}
    (h : UtZeroA st OS s) (hV : ValidUntypedA st H OS s) {x : U64} (hx : x ∈ OS) {c : capability.Cap}
    (hwf : CapRt.EncWf c) (hb : UB c (capA st s x)) :
    obj.Slot.set_cap st x s c ⦃ s' => UtZeroA st OS s' ⦄ := by
  obtain ⟨w0, w1, he, hr⟩ := CapRt.decode_encode c hwf
  rw [set_cap_eq he, WP.spec_ok]
  have hw : WritesIn st s (L.wr (L.wr s x w0) (wa x 8#u64) w1) (W7.CapW H.tcbs H.omega Sg) :=
    ((writesIn_wr (hO.al0 hx)).trans (writesIn_wr (hO.al hx (k := 8#u64) (by simp) (by simp)))).mono
      fun b hb' => by
        rcases hb' with e | e
        · subst e; exact hO.cw0 hx
        · subst e; exact hO.cw hx (by simp) (by simp)
  refine h.capw hH hV hw fun y hy => ⟨y, hy, ?_⟩
  by_cases e : y = x
  · rw [e, capA_wr2_self hO hx hr]; exact hb
  · rw [capA_wr2_other hO hx hy e]; exact UB.refl _

/-! ## The `Tcb` arm of `create_object` -/

/-- The words `[t, t + 4096)` but the affinity word `t + 3520`. -/
def TFw (t : U64) (b : U64) : Prop := InWin t 4096 b ∧ b.val ≠ t.val + 3520

theorem wr_tf {s : S} {t a v : U64} {o : Nat} (hal : t.val % 8 = 0) (ha : a.val = t.val + o) (ho : o < 4096)
    (h8 : o % 8 = 0) (hne : o ≠ 3520) : WritesIn st s (L.wr s a v) (TFw t) :=
  (writesIn_wr (by show a.val % 8 = 0; rw [ha]; omega)).mono fun b e => by
    subst e; unfold TFw InWin; rw [ha]; omega

theorem set_reg_tf {s : S} {t r v : U64} (hal : t.val % 8 = 0) (hf : t.val + 4096 ≤ 2 ^ 64) (hr : r.val < 37) :
    obj.Tcb.set_reg st t s r v ⦃ s' => WritesIn st s s' (TFw t) ⦄ := by
  unfold obj.Tcb.set_reg
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
  subst e
  have hv : (wa (wa t layout.tcb.REGS) (core.num.U64.wrapping_mul r 8#u64)).val = t.val + (256 + 8 * r.val) := by
    simp [layout.tcb.REGS, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def,
      U64.numBits]; omega
  exact wr_tf hal hv (by omega) (by omega) (by omega)

set_option maxHeartbeats 1000000 in
theorem init_context_tf (s : S) {t : U64} (hal : t.val % 8 = 0) (hf : t.val + 4096 ≤ 2 ^ 64) :
    regs.init_context st s t ⦃ s' => WritesIn st s s' (TFw t) ⦄ := by
  unfold regs.init_context regs.init_context_loop
  have hloop : loop (fun (s1, i1) => regs.init_context_loop.body st t s1 i1) (s, 0#u64) ⦃ s' =>
      WritesIn st s s' (TFw t) ⦄ := by
    refine loop.spec_decr_nat (measure := fun x => 37 - x.2.val)
      (inv := fun x => x.2.val ≤ 37 ∧ WritesIn st s x.1 (TFw t)) _ _ _ ?_ ⟨by simp, WritesIn.refl _ _⟩
    rintro ⟨s1, i⟩ ⟨hi, hw⟩
    unfold regs.init_context_loop.body
    simp only at hi hw ⊢
    by_cases hit : i < layout.reg.COUNT
    · rw [if_pos hit]
      have hit' : i.val < 37 := by have : i.val < layout.reg.COUNT.val := hit; simpa [layout.reg.COUNT] using this
      refine WP.spec_bind (set_reg_tf (s := s1) (v := 0#u64) hal hf hit') fun s2 h2 => ?_
      obtain ⟨i1, h1e, h1v⟩ := spec_exA (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
      rw [h1e, bind_ok, WP.spec_ok]
      have h1 : i1.val = i.val + 1 := by simpa using h1v
      try dsimp only
      have H1 : i1.val ≤ 37 := by omega
      have H3 : 37 - i1.val < 37 - i.val := by omega
      first | exact ⟨⟨H1, hw.trans1 h2⟩, H3⟩ | exact ⟨H1, hw.trans1 h2, H3⟩
    · rw [if_neg hit, WP.spec_ok]; exact hw
  refine WP.spec_bind hloop fun s1 h1 => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by unfold regs.PSTATE_USER; p0_split) fun v _ => ?_
  exact WP.spec_mono (set_reg_tf (s := s1) (v := v) hal hf (by simp [layout.reg.SPSR_EL1])) fun s2 h2 =>
    h1.trans1 h2

theorem set_domain_tf (s : S) {t v : U64} (hal : t.val % 8 = 0) (hf : t.val + 4096 ≤ 2 ^ 64) :
    obj.Tcb.set_domain st t s v ⦃ s' => WritesIn st s s' (TFw t) ⦄ := by
  unfold obj.Tcb.set_domain
  rw [show layout.tcb.DOMAIN = ok 3432#u64 by unfold layout.tcb.DOMAIN layout.tcb.F; rfl]
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
  subst e
  exact wr_tf (o := 3432) hal (by simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega)
    (by omega) (by omega) (by omega)

set_option maxHeartbeats 1000000 in
theorem child_names_tf (s : S) {child parent len : U64} (hal : child.val % 8 = 0)
    (hf : child.val + 4096 ≤ 2 ^ 64) :
    objects.set_child_name_loop1 st s child parent len 0#u64 ⦃ s' => WritesIn st s s' (TFw child) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold objects.set_child_name_loop1
  refine loop.spec_decr_nat (measure := fun x => 8 - x.2.val)
    (inv := fun x => x.2.val ≤ 8 ∧ WritesIn st s x.1 (TFw child)) _ _ _ ?_ ⟨by simp, WritesIn.refl _ _⟩
  rintro ⟨s1, w⟩ ⟨hw, hW⟩
  unfold objects.set_child_name_loop1.body
  simp only at hw hW ⊢
  by_cases h : w < 8#u64
  · rw [if_pos h]
    have h' : w.val < 8 := h
    obtain ⟨v, hv, -⟩ := spec_exA (P0.objects.set_child_name_loop1_loop0.p0 st s1 parent len w 0#u64 0#u64 hS)
    rw [hv, bind_ok]
    simp only [obj.Tcb.name_addr, lift, bind_ok]
    rw [show layout.tcb.NAME = ok 3600#u64 by unfold layout.tcb.NAME layout.tcb.F; rfl]
    simp only [bind_ok]
    refine WP.spec_bind (LawfulStore.write_spec s1 _ v) fun s2 e2 => ?_
    subst e2
    have hv' : (wa (wa child 3600#u64) (core.num.U64.wrapping_mul w 8#u64)).val = child.val + (3600 + 8 * w.val) := by
      simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
    have W2 := hW.trans1 (wr_tf (s := s1) (v := v) hal hv' (by omega) (by omega) (by omega))
    obtain ⟨w1, h1e, h1v⟩ := spec_exA (U64.add_spec (x := w) (y := 1#u64) (by scalar_tac))
    rw [h1e, bind_ok, WP.spec_ok]
    have h1 : w1.val = w.val + 1 := by simpa using h1v
    try dsimp only
    have H1 : w1.val ≤ 8 := by omega
    have H3 : 8 - w1.val < 8 - w.val := by omega
    first | exact ⟨⟨H1, W2⟩, H3⟩ | exact ⟨H1, W2, H3⟩
  · rw [if_neg h, WP.spec_ok]; exact hW

theorem set_child_name_tf (s : S) {child parent : U64} (hal : child.val % 8 = 0)
    (hf : child.val + 4096 ≤ 2 ^ 64) :
    objects.set_child_name st s child parent ⦃ s' => WritesIn st s s' (TFw child) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold objects.set_child_name
  simp only [fl4_abi.config.DEBUG_BUILD, ↓reduceIte, obj.Tcb.is_null, bind_ok]
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · obtain ⟨len, hl, -⟩ := spec_exA (P0.objects.set_child_name_loop0.p0 st s parent 0#u64 hS)
    rw [hl, bind_ok]
    exact child_names_tf s hal hf

/-- Node 0's debug-list head word. -/
abbrev nwA (st : machine.Store S) [L : LawfulStore st] (s : S) : U64 := L.nodeAt s 0#u64 layout.node.DEBUG_TCBS

/-- The words a `Tcb` creation at `t` may write (module docstring). -/
def TcbWA (st : machine.Store S) [L : LawfulStore st] (s : S) (t b : U64) : Prop :=
  InWin t 4096 b ∨ b = nwA st s ∨ (L.mem s (nwA st s) ≠ 0#u64 ∧ b = dpA (L.mem s (nwA st s)))

/-- A debug-link word of an 8-aligned pointer is aligned (the wrap keeps the residue). -/
theorem dpA_al {h : U64} (hh : h.val % 8 = 0) : Aligned (dpA h) := by
  show _ % 8 = 0
  unfold dpA
  rw [wa_val, Nat.mod_mod_of_dvd _ (by norm_num : 8 ∣ 2 ^ 64)]
  have : (3584#u64 : U64).val = 3584 := by simp
  omega

set_option maxHeartbeats 1000000 in
/-- **`debug_append` with the affinity word 0** (module docstring; x86 `debug_append_frame`). -/
theorem debug_append_fz (s : S) {t : U64} (hal : t.val % 8 = 0) (hf : t.val + 4096 ≤ 2 ^ 64)
    (haf : L.mem s (affA t) = 0#u64) (hnA : Aligned (nwA st s))
    (hhd : L.mem s (nwA st s) ≠ 0#u64 → (L.mem s (nwA st s)).val % 8 = 0) :
    objects.debug_append st s t ⦃ s' => WritesIn st s s' (TcbWA st s t) ∧ L.mem s' (nwA st s) = t ⦄ := by
  unfold objects.debug_append
  refine WP.spec_bind (obj.Tcb.affinity.spec s t) fun cpu ecpu => ?_
  rw [haf] at ecpu; subst ecpu
  refine WP.spec_bind (obj.node_get.spec s 0#u64 _) fun hd ehd => ?_
  subst ehd
  refine WP.spec_bind (obj.Tcb.set_debug_prev.wr s t 0#u64) fun s1 e1 => ?_
  subst e1
  refine WP.spec_bind (obj.Tcb.set_debug_next.wr _ t _) fun s2 e2 => ?_
  subst e2
  have hdp : (dpA t).val = t.val + 3584 := by
    unfold dpA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hdn : (dnA t).val = t.val + 3576 := by
    unfold dnA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have w1 : WritesIn st s (L.wr s (dpA t) 0#u64) (TcbWA st s t) :=
    (writesIn_wr (by show _ % 8 = 0; rw [hdp]; omega)).mono fun b e => by
      subst e; left; unfold InWin; rw [hdp]; omega
  have w2 := w1.trans1 ((writesIn_wr (s := L.wr s (dpA t) 0#u64) (v := L.mem s (nwA st s))
    (by show _ % 8 = 0; rw [hdn]; omega)).mono fun b e => by
      subst e; left; unfold InWin; rw [hdn]; omega)
  set s2 := L.wr (L.wr s (dpA t) 0#u64) (dnA t) (L.mem s (nwA st s)) with hs2
  have k2 : L.ksb s2 = L.ksb s := w2.1
  refine WP.spec_bind (Pₘ := fun r : S × U64 => r.2 = t ∧ WritesIn st s r.1 (TcbWA st s t)) ?_ ?_
  · split
    · rename_i hn
      have hn' : L.mem s (nwA st s) ≠ 0#u64 := by simpa using hn
      refine WP.spec_bind (obj.Tcb.set_debug_prev.wr _ _ t) fun s3 e3 => ?_
      subst e3
      have ha : Aligned (dpA (L.mem s (nwA st s))) := dpA_al (hhd hn')
      exact (WP.spec_ok _).2 ⟨rfl, w2.trans1 ((writesIn_wr ha).mono fun b e => Or.inr (Or.inr ⟨hn', e⟩))⟩
    · exact (WP.spec_ok _).2 ⟨rfl, w2⟩
  rintro ⟨s3, t1⟩ ⟨e, w3⟩
  simp only at e w3
  subst e
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (obj.node_set.spec s3 0#u64 _ _) fun s4 e4 => ?_
  subst e4
  have hn3 : L.nodeAt s3 0#u64 layout.node.DEBUG_TCBS = nwA st s := nodeAt_of_ksb w3.1 _ _
  rw [hn3]
  refine ⟨w3.trans1 ((writesIn_wr hnA).mono fun b e => Or.inr (Or.inl e)), ?_⟩
  rw [L.mem_wr _ _ _ _ hnA hnA, if_pos rfl]

section arch
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 2000000 in
/-- **`create_object` of a `Tcb`** (module docstring; x86 `create_tcb_frame`). -/
theorem create_object.tcbW (s : S) (a : A) (nt b0 us : U64) (dev : Bool) (hn : nt.val = 1)
    (hal : b0.val % 8 = 0) (hf : b0.val + 4096 ≤ 2 ^ 64) (haf : L.mem s (affA b0) = 0#u64)
    (hnA : Aligned (nwA st s)) (hnW : ¬ InWin b0 4096 (nwA st s))
    (hhd : L.mem s (nwA st s) ≠ 0#u64 → (L.mem s (nwA st s)).val % 8 = 0) :
    objects.create_object st ar s a nt b0 us dev ⦃ r => r.1 = newCapA nt.val b0 us dev ∧
      WritesIn st s r.2.1 (TcbWA st s b0) ∧ L.mem r.2.1 (nwA st s) = b0 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain rfl : nt = 1#u64 := UScalar.eq_of_val_eq (by simp [hn])
  have hcap : newCapA (1#u64 : U64).val b0 us dev = .Thread b0 := by first | rfl | simp [newCapA]
  rw [hcap]
  unfold objects.create_object
  simp (config := { decide := true }) only [fl4_abi.consts.object.Tcb, ↓reduceIte, ite_true]
  refine WP.spec_bind (init_context_tf s hal hf) fun s1 f1 => ?_
  unfold objects.init_fpu debug.init_context
  simp only [bind_ok]
  refine WP.spec_bind (sched.cur_domain.spec' s1) fun d _ => ?_
  refine WP.spec_bind (set_domain_tf s1 (v := d) hal hf) fun s4 f4 => ?_
  refine WP.spec_bind (sched.cur_thread.spec s4) fun ct _ => ?_
  refine WP.spec_bind (set_child_name_tf s4 (parent := ct) hal hf) fun s5 f5 => ?_
  have f := (f1.trans1 f4).trans1 f5
  have hk : L.ksb s5 = L.ksb s := f.1
  have hnw : nwA st s5 = nwA st s := nodeAt_of_ksb hk _ _
  have hav : (affA b0).val = b0.val + 3520 := by
    unfold affA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have haA : Aligned (affA b0) := by show _ % 8 = 0; rw [hav]; omega
  have haf5 : L.mem s5 (affA b0) = 0#u64 := by
    have hnT : ¬ TFw b0 (affA b0) := fun h => h.2 hav
    rw [f.mem_eq haA hnT]; exact haf
  have hhv : L.mem s5 (nwA st s5) = L.mem s (nwA st s) := by
    rw [hnw]; exact f.mem_eq hnA fun h => hnW h.1
  refine WP.spec_bind (debug_append_fz s5 hal hf haf5 (by rw [hnw]; exact hnA) (by rw [hhv]; exact hhd))
    fun s6 ⟨f6, h6⟩ => ?_
  refine (WP.spec_ok _).2 ⟨rfl, ?_, by rw [← hnw]; exact h6⟩
  refine (f.mono fun b h => Or.inl h.1).trans1 (f6.mono fun b h => ?_)
  unfold TcbWA at h
  rw [hhv, hnw] at h
  exact h

end arch

end ST
end R
end W7

end

end Fl4ProofsA64.P1

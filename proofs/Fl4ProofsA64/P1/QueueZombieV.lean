/-
P1 (aarch64, gen 33): **the Zombie loop over `JV`**: `finalise_slot_immediate` of a slot holding a Zombie, a
thread or a CNode cap (final or not), and the exposed `cdt.delete` through it, with the covered slots holding
leaf caps.

cdt.rs 243–318: `finalise_slot_immediate(x)` finalises the cap of `x`; a non-removable remainder (a Zombie
`(p, t, n)`, `n ≠ 0`, not `(n = 1 ∧ x = p)`) is written into `x`, the last covered slot `p + 32 (n − 1)` is
deleted by `delete_deferred` (`finalise_slot_deferred` and `empty_slot`), the Zombie in `x` is decremented if it
is still there, and a preemption point follows; the round repeats.

* **The domain**: a ghost set `D ⊆ OS` of slots (the slots the Zombie covers, transitively none: no Zombie /
  CNode / thread caps inside); `DomL D s`: every slot of `D` holds a **leaf** cap (`ZL`: a `TrivK` cap or an
  endpoint / notification / reply cap, the kinds whose finalisation returns `(Null, Null)` at every finality,
  covered over `JV` by gen 31–32). Then `finalise_slot_deferred` of a slot of `D` returns after one round (the
  remainder is `Null`, removable) and never reaches `cap_swap_for_delete`.
* **The slot `x`** (`XOK D x s`): its cap is a leaf, a thread `p` (not the idle thread) whose seven TCB slots lie in
  `D`, a CNode whose `2^radix` slots lie in `D`, or a Zombie whose `n` covered slots lie in `D`.
* **Steps**: `finL` (a leaf's finalisation: `(Null, Null)`, `JV`, every `OS` word kept), `finJV_threadK`
  (gen 32's `finJV_thread` with `OSKeep`), `fin_cnode.z`, `fin_zombie.z`; `cdt.finalise_slot_deferred.zl`,
  **`cdt.delete_deferred.zl`** (a leaf slot of `OS` deleted: `JV`, every other `OS` slot's cap words kept, the
  slot `Null` or unchanged); `JV.setz` (QueueZombieEnc: the Zombie written back); **`sched.preemption_point.jv`**
  (its words: `WORK_UNITS`, two node words; `OS` kept under `WuApart`, `VcTy` kept).
* **Tops**: **`cdt.finalise_slot_immediate.zv`** and **`cdt.delete.zv`** (`JV` to `JV`, a null cleanup); the
  instances **`cdt.delete.zombieV`** (the Zombie kind, any `n`), **`cdt.delete.threadV`** (a thread cap, final
  or not: the final one ends in the Zombie loop over its TCB slots), **`cdt.delete.cnodeV`** (a CNode cap, final
  or not).

**Placement fact** `WuApart OS kb` (a definition, a plain hypothesis of the tops here): the kernel-global word
`kb + WORK_UNITS` (`layout::ks::WORK_UNITS` = 40, arch/aarch64/layout.rs) lies in no `OS` slot. It is part of
the new entry fact [J] `SlotTyEntZ` (QueueZombieEnt). Not over a word class.

No other premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueZombieEnc
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}

namespace W7
namespace R
namespace ST

local notation "wa" => core.num.U64.wrapping_add

section zv
variable {OS Vc Ub D : Set U64}

/-! ## Definitions -/

/-- **The leaf kinds**: finalised to `(Null, Null)` at every finality, over `JV` (gen 31–32). -/
def ZL (c : capability.Cap) : Prop := TrivK c ∨ EpNtRp c

/-- Every slot of `D` holds a leaf cap. -/
def DomL (st : machine.Store S) [L : LawfulStore st] (D : Set U64) (s : S) : Prop :=
  ∀ y ∈ D, ∀ c, obj.Slot.cap st y s = ok c → ZL c

/-- The cap of the slot being deleted: a leaf, or a thread / CNode / Zombie cap whose slots lie in `D`. -/
def XK (D : Set U64) (idl : U64) (c : capability.Cap) : Prop :=
  ZL c ∨ (∃ p, c = .Thread p ∧ p ≠ idl ∧ ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) ∨
  (∃ p r g b, c = .CNode p r g b ∧ ∀ i : U64, i.val < 2 ^ (r.val % 64) → slotIdx p i ∈ D) ∨
  (∃ p t n, c = .Zombie p t n ∧ ∀ i : U64, i.val < n.val → slotIdx p i ∈ D)

/-- The slot `x`'s cap is `XK` at `s`. -/
def XOK (st : machine.Store S) [L : LawfulStore st] (D : Set U64) (x : U64) (s : S) : Prop :=
  ∀ c, obj.Slot.cap st x s = ok c → XK D (L.idleW s) c

/-- **`WORK_UNITS` apart from `OS`** (module docstring). -/
def WuApart (OS : Set U64) (kb : U64) : Prop :=
  ∀ y ∈ OS, ¬ (y.val ≤ (wa kb layout.ks.WORK_UNITS).val ∧ (wa kb layout.ks.WORK_UNITS).val < y.val + 32)

theorem zl_null : ZL .Null := Or.inl (Or.inl rfl)

theorem zl_not_zombie {p t n : U64} : ¬ ZL (.Zombie p t n) := by
  unfold ZL TrivK EpNtRp; simp

theorem zl_not_thread {p : U64} : ¬ ZL (.Thread p) := by
  unfold ZL TrivK EpNtRp; simp

theorem zl_not_cnode {p r g b : U64} : ¬ ZL (.CNode p r g b) := by
  unfold ZL TrivK EpNtRp; simp

theorem OSKeep.rfl' (s : S) : OSKeep st OS s s := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

theorem OSKeep.trans' {s1 s2 s3 : S} (h1 : OSKeep st OS s1 s2) (h2 : OSKeep st OS s2 s3) : OSKeep st OS s1 s3 :=
  fun y hy => ⟨(h2 y hy).1.trans (h1 y hy).1, (h2 y hy).2.1.trans (h1 y hy).2.1,
    (h2 y hy).2.2.1.trans (h1 y hy).2.2.1, (h2 y hy).2.2.2.trans (h1 y hy).2.2.2⟩

theorem OSKeep.ck {x : U64} {s s' : S} (h : OSKeep st OS s s') : CapKeep st OS x s s' := fun y hy _ =>
  ⟨(h y hy).1, (h y hy).2.1⟩

theorem OSKeep.cap {s s' : S} (h : OSKeep st OS s s') {y : U64} (hy : y ∈ OS) :
    obj.Slot.cap st y s' = obj.Slot.cap st y s := by
  rw [DPF.slot_cap_dec, DPF.slot_cap_dec, (h y hy).1, (h y hy).2.1]

theorem CapKeep.cap {x : U64} {s s' : S} (h : CapKeep st OS x s s') {y : U64} (hy : y ∈ OS) (hne : y ≠ x) :
    obj.Slot.cap st y s' = obj.Slot.cap st y s := by
  rw [DPF.slot_cap_dec, DPF.slot_cap_dec, (h y hy hne).1, (h y hy hne).2]

theorem DomL.ck {x : U64} {s s' : S} (h : DomL st D s) (hDO : D ⊆ OS) (hxD : x ∉ D) (k : CapKeep st OS x s s') :
    DomL st D s' := fun y hy c hc => h y hy c (by
  rw [k.cap (hDO hy) (fun e => hxD (e ▸ hy))] at hc; exact hc)

theorem DomL.osk {s s' : S} (h : DomL st D s) (hDO : D ⊆ OS) (k : OSKeep st OS s s') : DomL st D s' :=
  fun y hy c hc => h y hy c (by rw [k.cap (hDO hy)] at hc; exact hc)

/-- `x` is outside `D` when its cap is no leaf. -/
theorem notin_of {s : S} {x : U64} {c : capability.Cap} (hD : DomL st D s) (hc : obj.Slot.cap st x s = ok c)
    (hn : ¬ ZL c) : x ∉ D := fun hx => hn (hD x hx c hc)

theorem JV.ksb {s0 s : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) : L.ksb s = L.ksb s0 := by
  obtain ⟨-, Ac', -, -, -, -, -, -, w⟩ := h.1.1.1
  exact w.1

/-! ## The leaf finalisations with every `OS` word kept -/

theorem osk_ep {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64} (hx : x ∈ OS) (a : A) (fin : Bool)
    {ep : U64} {b0 : U64} {b1 b2 b3 b4 : Bool} (hc : obj.Slot.cap st x s = ok (.Endpoint ep b0 b1 b2 b3 b4)) :
    objects.finalise_cap st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin false ⦃ r => OSKeep st OS s r.2.1 ⦄ := by
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  have hH : H ep = some .ep := hty.1.1.1 ep b0 b1 b2 b3 b4 rfl
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hsub : ∀ b ∈ Sg, b ∈ Ω := by obtain ⟨-, -, -, -, hSg⟩ := hb.blk; exact hSg.sub
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (K7.fin_endpoint.blk (ar := ar) s a ep b0 b1 b2 b3 b4 fin hb.blk hH) fun r hr =>
    OSKeep.of_kw7 hO q hsub hA (fun e he => by rw [Set.mem_singleton_iff.1 he]; exact Or.inl hH) hr.2.2.2

theorem osk_ntfn {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64} (hx : x ∈ OS) (a : A) (fin : Bool)
    {n b0 : U64} {b1 b2 : Bool} (hc : obj.Slot.cap st x s = ok (.Notification n b0 b1 b2)) :
    objects.finalise_cap st ar s a (.Notification n b0 b1 b2) fin false ⦃ r => OSKeep st OS s r.2.1 ⦄ := by
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  obtain ⟨hn, hH⟩ := hty.1.1.2.1 n b0 b1 b2 rfl
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hsub : ∀ b ∈ Sg, b ∈ Ω := by obtain ⟨-, -, -, -, hSg⟩ := hb.blk; exact hSg.sub
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (K7.fin_ntfn.blk (ar := ar) s a n b0 b1 b2 fin hb.blk hn hH) fun r hr =>
    OSKeep.of_kw7 hO q hsub hA (fun e he => by rw [Set.mem_singleton_iff.1 he]; exact Or.inr hH) hr.2.2.2

theorem osk_reply {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hA : ScApart Scs Z OS) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64} (hx : x ∈ OS) (a : A) (fin : Bool)
    {p : U64} {g : Bool} (hc : obj.Slot.cap st x s = ok (.Reply p g)) :
    objects.finalise_cap st ar s a (.Reply p g) fin false ⦃ r => OSKeep st OS s r.2.1 ⦄ := by
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  have hp : p ∈ Rp := hty.1.1.2.2 p g rfl
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hsub : ∀ b ∈ Sg, b ∈ Ω := by obtain ⟨-, -, -, -, hSg⟩ := hb.blk; exact hSg.sub
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (K7.fin_reply.blk (ar := ar) hP s a p g fin hb.blk hp h.1.1.2) fun r hr =>
    OSKeep.of_kwd7 hO q hsub hA (fun e he => he) hr.2.2

set_option maxHeartbeats 2000000 in
/-- **A leaf cap's finalisation**: `(Null, Null)`, `JV`, every `OS` word kept. -/
theorem finL {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64} (hx : x ∈ OS) {c : capability.Cap}
    (hc : obj.Slot.cap st x s = ok c) (hk : ZL c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => r.1 = (.Null, .Null) ∧
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ OSKeep st OS s r.2.1 ⦄ := by
  rcases hk with ht | he
  · rw [finalise_cap.triv ar s a ht fin, WP.spec_ok]
    exact ⟨rfl, h, OSKeep.rfl' s⟩
  have hk' : ∀ c', obj.Slot.cap st x s = ok c' → c' = c := fun c' hc' => by rw [hc] at hc'; exact (okinj hc').symm
  rcases he with ⟨p, b0, b1, b2, b3, b4, rfl⟩ | ⟨n, b0, b1, b2, rfl⟩ | ⟨p, g, rfl⟩
  · refine WP.spec_mono (WP.spec_and (finJV_ep (ar := ar) hO hA hV h hx (fun c' hc' => ⟨_, _, _, _, _, _, hk' c' hc'⟩)
      a _ fin hc) (osk_ep hO hA h hx a fin hc)) fun r hr => ⟨hr.1.1, hr.1.2, hr.2⟩
  · refine WP.spec_mono (WP.spec_and (finJV_ntfn (ar := ar) hO hA hV h hx (fun c' hc' => ⟨_, _, _, _, hk' c' hc'⟩)
      a _ fin hc) (osk_ntfn hO hA h hx a fin hc)) fun r hr => ⟨hr.1.1, hr.1.2, hr.2⟩
  · refine WP.spec_mono (WP.spec_and (finJV_reply (ar := ar) hP hO hA hV h hx (fun c' hc' => ⟨_, _, hk' c' hc'⟩)
      a _ fin hc) (osk_reply hP hO hA h hx a fin hc)) fun r hr => ⟨hr.1.1, hr.1.2, hr.2⟩

set_option maxHeartbeats 2000000 in
/-- **The thread kind over `JV` with every `OS` word kept** (gen 32's `finJV_thread`, `OSKeep` exported). -/
theorem finJV_threadK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hSA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a (.Thread p) fin false ⦃ r =>
      r.1 = (if fin then .Zombie p capability.ZOMBIE_TCB 7#u64 else .Null, .Null) ∧
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ OSKeep st OS s r.2.1 ⦄ := by
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  have hp : p ∈ T := hty.1.2.2.2.2.2 p rfl
  rw [fin_cap_eq_obj (by simp)]
  refine WP.spec_mono (WP.spec_and (fin_thread.rem hA s a p fin)
    (fin_thread.ubV hA hO hV hSA h.1.1.1 h.1.1.2 h.2 a p fin hp hid)) ?_
  rintro r ⟨e, c0, rv, k, v⟩
  exact ⟨e, And.intro (And.intro (And.intro c0 rv) (h.1.2.keep k)) v, k⟩

/-- **A CNode cap's finalisation** (objects.rs `finalise_cap_object`, CNode arm): no store write; a null
cleanup; the remainder `Null`, or a Zombie of the CNode's `2^radix` slots. -/
theorem fin_cnode.z {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (p r g b : U64) (fin : Bool) :
    objects.finalise_cap st ar s a (.CNode p r g b) fin false ⦃ x => x.2.1 = s ∧ x.1.2 = .Null ∧
      (x.1.1 = .Null ∨ ∃ n : U64, x.1.1 = .Zombie p r n ∧ 0 < n.val ∧
        ∀ i : U64, i.val < n.val → i.val < 2 ^ (r.val % 64)) ⦄ := by
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
  split
  · simp only [lift, bind_ok]
    step as ⟨n, hn⟩
    have h63 : (r &&& 63#u64).val = r.val % 64 := by
      simp [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod r.val 6
    first
      | refine ⟨rfl, rfl, Or.inr ⟨n, rfl, ?_, fun i hi => ?_⟩⟩
      | refine Or.inr ⟨n, rfl, ?_, fun i hi => ?_⟩
      | (simp only [WP.spec_ok]; refine ⟨rfl, rfl, Or.inr ⟨n, rfl, ?_, fun i hi => ?_⟩⟩)
    · rw [hn]
      first | positivity | exact Nat.one_le_two_pow | (simp [Nat.shiftLeft_eq]; positivity) | omega
    · rw [hn, h63] at hi; exact hi
  · exact (WP.spec_ok _).2 ⟨rfl, rfl, Or.inl rfl⟩

/-- **A Zombie cap's finalisation**: the cap itself, a null cleanup, no store write. -/
theorem fin_zombie.z {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (p t n : U64) (fin : Bool) :
    objects.finalise_cap st ar s a (.Zombie p t n) fin false = ok ((.Zombie p t n, .Null), s, a) := by
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
  all_goals rfl

/-! ## `delete_deferred` of a leaf slot -/

set_option maxHeartbeats 4000000 in
/-- `finalise_slot_deferred` of a leaf slot of `OS`: one round, `JV`, every `OS` word kept, a null cleanup. -/
theorem cdt.finalise_slot_deferred.zl {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS)
    (hk : ∀ c, obj.Slot.cap st x s = ok c → ZL c) :
    cdt.finalise_slot_deferred st ar s a x ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      OSKeep st OS s r.2.1 ∧ ∀ v, r.1 = .Ok v → v.cleanup = .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val) (inv := fun y => y.1 = s)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    subst s1
    dsimp only
    unfold cdt.finalise_slot_deferred_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h, OSKeep.rfl' s, by intro v hv; simp_all⟩
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h, OSKeep.rfl' s, fun v hv => by cases hv; rfl⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s x c hS) fun fin _ => ?_
    refine WP.spec_bind (finL hP hO hA hV h hx hc (hk c hc) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨e1, h2, k2⟩
    simp only [Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    try dsimp only
    first
    | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
       exact (WP.spec_ok _).2 ⟨h2, k2, fun v hv => by cases hv; rfl⟩)
    | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]; exact ⟨h2, k2, fun v hv => by cases hv; rfl⟩)
    | (simp [cdt.cap_removable, WP.spec_ok]; exact ⟨h2, k2⟩)
    | (simp [cdt.cap_removable, WP.spec_ok, h2, k2])
  · rfl

set_option maxHeartbeats 4000000 in
/-- **`delete_deferred` of a leaf slot of `OS`**: `JV`, every other `OS` slot's cap words kept, and the slot then
holds a leaf (`Null`, or its cap unchanged). -/
theorem cdt.delete_deferred.zl {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {y : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ OS)
    (hk : ∀ c, obj.Slot.cap st y s = ok c → ZL c) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      CapKeep st OS y s r.2.1 ∧ ∀ c, obj.Slot.cap st y r.2.1 = ok c → ZL c ⦄ := by
  unfold cdt.delete_deferred
  refine WP.spec_bind (cdt.finalise_slot_deferred.zl (a := a) hP hO hA hV h hy hk) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, k1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 k1 hv1 ⊢
  have keep1 : ∀ c, obj.Slot.cap st y s1 = ok c → ZL c := fun c hc => hk c (by rw [k1.cap hy] at hc; exact hc)
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    · rw [hv1 v rfl]
      refine WP.spec_bind (WP.spec_and (cdt.empty_slot.jv (a := a1) hO hV h1 hy)
        (cdt.empty_slot.ck (a := a1) hO h1.1.2 hy)) ?_
      rintro ⟨s2, a2⟩ ⟨h2, k2, c2⟩
      try simp only [uncurry_apply_pair] at h2 k2 c2 ⊢
      exact (WP.spec_ok _).2 ⟨h2, k1.ck.trans k2, fun c hc => by
        rw [c2] at hc; rw [← okinj hc]; exact zl_null⟩
    · exact (WP.spec_ok _).2 ⟨h1, k1.ck, keep1⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h1, k1.ck, keep1⟩

/-! ## The preemption point over `JV` -/

set_option maxHeartbeats 4000000 in
/-- **A preemption point keeps `JV` and every `OS` word** (its words: `WORK_UNITS`, apart from `OS` by `WuApart`,
and the current node's `CUR_TIME` / `CONSUMED`, no `W7.CapW` word and no VCPU word). -/
theorem sched.preemption_point.jv {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hW : WuApart OS (L.ksb s)) :
    sched.preemption_point st ar s a ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      OSKeep st OS s r.2.1 ∧ L.idleW r.2.1 = L.idleW s ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hN := q.nodes _ q.cur
  obtain ⟨hwa, hΩ, -⟩ := ks_work_units hb.blk
  have ho := q.omega _ hΩ
  refine WP.spec_mono (WP.spec_and (Fl4ProofsA64.P1.W7.R.sched.preemption_point.cur0 hP h.1.1)
    (sched.preemption_point.pp (Ac := Ac') hP s a hb.blk)) ?_
  rintro r ⟨c1, -, w⟩
  -- a word of an `OS` slot is no preemption-point word
  have nos : ∀ y ∈ OS, ∀ k : U64, k.val < 32 → k.val % 8 = 0 → ¬ PPW st s (wa y k) := by
    intro y hy k hk h8 hp
    have hcw := hO.cw hy hk h8
    have hv : (wa y k).val = y.val + k.val := wv (hO.fit y hy) hk
    rcases hp with e | e | e
    · exact hW y hy ⟨by rw [← e, hv]; omega, by rw [← e, hv]; omega⟩
    · exact capw_ne_node q hcw q.cur (o := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
        (by unfold LawfulStore.nodeA at e; exact e)
    · exact capw_ne_node q hcw q.cur (o := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
        (by unfold LawfulStore.nodeA at e; exact e)
  have k : OSKeep st OS s r.2.1 := fun y hy => by
    have m := fun (k : U64) (hk : k.val < 32) (h8 : k.val % 8 = 0) =>
      w.2.2 _ (hO.al hy hk h8) (nos y hy k hk h8)
    have m0 := m 0#u64 (by simp) (by simp)
    rw [SFF.wadd0'] at m0
    exact ⟨m0, m 8#u64 (by simp) (by simp), m 16#u64 (by simp) (by simp), m 24#u64 (by simp) (by simp)⟩
  -- the `VcTy` words are kept
  have hT := q.tcbs
  have ffld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem r.2.1 (wa y K) = L.mem s (wa y K) := fun y hy K hK hK8 => by
    refine w.2.2 _ (field_aligned (hT _ hy) hK hK8) fun hp => ?_
    rcases hp with e | e | e
    · exact out_ne_field (K := K) ho hy (hT _ hy) hK (congrArg UScalar.val e)
    · exact node_ne_field (K := K) (o := layout.node.CUR_TIME) hN (by simp [layout.node.CUR_TIME]) hy
        (hT _ hy) hK (by unfold LawfulStore.nodeA at e; exact e.symm)
    · exact node_ne_field (K := K) (o := layout.node.CONSUMED) hN (by simp [layout.node.CONSUMED]) hy
        (hT _ hy) hK (by unfold LawfulStore.nodeA at e; exact e.symm)
  have hvc : ∀ b, VcW Vc b → L.mem r.2.1 b = L.mem s b := fun b hb' => by
    obtain ⟨hal, hbΩ, -⟩ := h.2.w hb'
    have hob := q.omega _ hbΩ
    refine w.2.2 _ hal fun hp => ?_
    rcases hp with e | e | e
    · exact h.2.ks b hb' layout.ks.WORK_UNITS (by simp [layout.ks.WORK_UNITS]) e.symm
    · exact out_ne_node hob q.cur hN (o := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
        (by unfold LawfulStore.nodeA at e; rw [e])
    · exact out_ne_node hob q.cur hN (o := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
        (by unfold LawfulStore.nodeA at e; rw [e])
  have hidle : L.idleW r.2.1 = L.idleW s := by
    have h8 : layout.node.IDLE_THREAD.val < 4288 := by rw [idle8]; omega
    unfold LawfulStore.idleW
    rw [w.2.1, nodeAt_of_ksb w.1]
    refine w.2.2 _ (nodeAt_aligned hN h8 (by rw [idle8])) fun hb => ?_
    rcases hb with e | e | e
    · exact out_ne_node ho q.cur hN h8 (by rw [e])
    · unfold LawfulStore.nodeA at e
      exact nodeAt_ne hN h8 (by simp [layout.node.CUR_TIME]) (by rw [idle8]; simp [layout.node.CUR_TIME]) e
    · unfold LawfulStore.nodeA at e
      exact nodeAt_ne hN h8 (by simp [layout.node.CONSUMED]) (by rw [idle8]; simp [layout.node.CONSUMED]) e
  refine ⟨⟨⟨c1, h.1.2.keep k⟩, h.2.keep ⟨w.1, hvc, fun t ht => ffld t ht _ (by simp) (by simp),
    fun t ht => ffld t ht 3672#u64 (by simp) (by simp), fun t ht => cap_of_os hV k t ht⟩⟩, k, hidle⟩

/-! ## The loop -/

theorem wsub1 {n : U64} (hn : n ≠ 0#u64) : (core.num.U64.wrapping_sub n 1#u64).val = n.val - 1 := by
  have : 0 < n.val := by
    rcases Nat.eq_zero_or_pos n.val with e | e
    · exact absurd (UScalar.eq_of_val_eq (by simpa using e)) hn
    · exact e
  have hlt : n.val < 18446744073709551616 := by scalar_tac
  simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]
  omega

theorem t255 : capability.ZOMBIE_TCB &&& 255#u64 = capability.ZOMBIE_TCB := by
  unfold capability.ZOMBIE_TCB; first | rfl | decide

/-- The non-removable branch's facts about a remainder Zombie. -/
def ZRem (st : machine.Store S) [L : LawfulStore st] (D : Set U64) (rem : capability.Cap) : Prop :=
  rem = .Null ∨ ∃ p t n, rem = .Zombie p t n ∧ Canon p ∧ ∀ i : U64, i.val < n.val → slotIdx p i ∈ D

set_option maxHeartbeats 4000000 in
/-- **The finalisation of the cap of `x`** inside `finalise_slot_immediate`: a null cleanup, `JV`, `DomL D`, and a
remainder `Null` or a Zombie whose covered slots lie in `D`; or the cap was a leaf (remainder `Null`). -/
theorem finX {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hD : DomL st D s) {x : U64} (hx : x ∈ OS)
    {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c) (hX : XK D (L.idleW s) c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => r.1.2 = .Null ∧
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ DomL st D r.2.1 ∧ ZRem st D r.1.1 ∧
      (ZL c → r.1.1 = .Null) ⦄ := by
  rcases hX with hl | ⟨p, rfl, hid, hcov⟩ | ⟨p, r, g, b, rfl, hcov⟩ | ⟨p, t, n, rfl, hcov⟩
  · exact WP.spec_mono (finL hP hO hA hV h hx hc hl a fin) fun r hr => by
      rw [hr.1]; exact ⟨rfl, hr.2.1, hD.osk hDO hr.2.2, Or.inl rfl, fun _ => rfl⟩
  · refine WP.spec_mono (finJV_threadK hP hO hA hV h hx hc hid a fin) fun r hr => ?_
    obtain ⟨e, h2, k2⟩ := hr
    rw [e]
    refine ⟨rfl, h2, hD.osk hDO k2, ?_, fun hl => absurd hl zl_not_thread⟩
    cases fin
    · exact Or.inl rfl
    · exact Or.inr ⟨p, _, _, rfl, (slot_canon hc).1 p rfl, fun i hi => hcov i (by simpa using hi)⟩
  · refine WP.spec_mono (fin_cnode.z ar s a p r g b fin) fun x hr => ?_
    obtain ⟨e, ecl, hrem⟩ := hr
    rw [e]
    refine ⟨ecl, h, hD, ?_, fun hl => absurd hl zl_not_cnode⟩
    rcases hrem with e1 | ⟨n, e1, -, hlt⟩
    · exact Or.inl e1
    · exact Or.inr ⟨p, r, n, e1, (slot_canon hc).2.1 p r g b rfl, fun i hi => hcov i (hlt i hi)⟩
  · rw [fin_zombie.z, WP.spec_ok]
    exact ⟨rfl, h, hD, Or.inr ⟨p, t, n, rfl, (slot_canon hc).2.2 p t n rfl, hcov⟩,
      fun hl => absurd hl zl_not_zombie⟩

set_option hygiene false in
/-- The preemption-point tail of an immediate round (`I` at `s5`). -/
local macro "ztail" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.jv hP hO hV h5 (by rw [h5.ksb]; exact hW)) ?_
  rintro ⟨rr, s6, a6⟩ ⟨h6, k6, i6⟩
  try simp only [uncurry_apply_pair] at h6 k6 i6 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h6, d5.osk hDO k6, fun c hc => ?_, ?_⟩
    · rw [k6.cap hx] at hc
      have := x5 c hc
      rw [i6]
      exact this
    · show fuel1.val < fuel.val
      omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h6, fun v hv => by cases hv⟩))

set_option maxHeartbeats 16000000 in
/-- **`finalise_slot_immediate` of a slot of `OS` whose cap is `XK` over a leaf domain `D`** (module docstring):
`JV` to `JV`, a null cleanup. -/
theorem cdt.finalise_slot_immediate.zv {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) {s0 s : S}
    (hW : WuApart OS (L.ksb s0)) {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomL st D s) (hX : XOK st D x s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ ∀ v, r.1 = .Ok v → v.cleanup = .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧ DomL st D y.1 ∧ XOK st D x y.1)
  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, x1⟩
    simp only at h1 d1 x1
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, by intro v hv; simp_all⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s1 hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; rfl⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (finX hP hO hA hV hDO h1 d1 hx hc (x1 c hc) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨ecl, h2, d2, hrem, hZL⟩
    simp only at ecl hrem hZL
    subst ecl
    rcases hrem with rfl | ⟨p, t, n, rfl, hcp, hcov⟩
    · try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; rfl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]; exact ⟨h2, fun v hv => by cases hv; rfl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact h2)
    -- a Zombie remainder: the cap of `x` was no leaf, so `x` is outside `D`
    have hxD : x ∉ D := fun hx' => by have := hZL (d1 x hx' c hc); cases this
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_removable.p0 (.Zombie p t n) x)) fun b1 hb1 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; rfl⟩
    rename_i hnr
    have hn0 : n ≠ 0#u64 := by
      have hb := hb1.1
      rintro rfl
      simp [cdt.cap_removable] at hb
      simp_all
    have hnp : 0 < n.val := by
      rcases Nat.eq_zero_or_pos n.val with e | e
      · exact absurd (UScalar.eq_of_val_eq (by simpa using e)) hn0
      · exact e
    have hp0 : p ∈ D := by have := hcov 0#u64 (by simpa using hnp); rwa [slotIdx0] at this
    refine WP.spec_bind (JV.setz hO hV h2 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i hi)⟩) ?_
    rintro s3 ⟨h3, k3, c3⟩
    have d3 : DomL st D s3 := d2.ck hDO hxD fun y hy hne => ⟨(k3 y hy hne).1, (k3 y hy hne).2.1⟩
    try dsimp only
    first
      | (refine WP.spec_bind (Pₘ := fun i => i = core.num.U64.wrapping_sub n 1#u64) ((WP.spec_ok _).2 rfl)
          fun i hi => ?_; subst hi)
      | simp only [lift, bind_ok]
    refine WP.spec_bind (slot_index_in p _) fun e he => ?_
    subst he
    have heD : slotIdx p (core.num.U64.wrapping_sub n 1#u64) ∈ D := hcov _ (by rw [wsub1 hn0]; omega)
    have hex : slotIdx p (core.num.U64.wrapping_sub n 1#u64) ≠ x := fun e => hxD (e ▸ heD)
    refine WP.spec_bind (cdt.delete_deferred.zl (a := a2) hP hO hA hV h3 (hDO heD) (d3 _ heD)) ?_
    rintro ⟨r4, s4, a4⟩ ⟨h4, k4, z4⟩
    try simp only [uncurry_apply_pair] at h4 k4 z4 ⊢
    have d4 : DomL st D s4 := fun y hy c' hc' => by
      by_cases ey : y = slotIdx p (core.num.U64.wrapping_sub n 1#u64)
      · subst ey; exact z4 c' hc'
      · exact d3 y hy c' (by rw [k4.cap (hDO hy) ey] at hc'; exact hc')
    have c4 : obj.Slot.cap st x s4 = ok (.Zombie p (t &&& 255#u64) n) := by
      rw [k4.cap hx (Ne.symm hex)]; exact c3
    have zk : ∀ m : U64, m.val ≤ n.val → XK D (L.idleW s4) (.Zombie p (t &&& 255#u64) m) := fun m hm =>
      Or.inr (Or.inr (Or.inr ⟨p, _, _, rfl, fun i hi => hcov i (by omega)⟩))
    rcases r4 with _ | ee
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [c4, bind_ok]
      try dsimp only
      try simp only [eq_self_iff_true, if_true, ite_true, ↓reduceIte, bind_ok]
      refine WP.spec_bind (Pₘ := fun y : S × A => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧
        DomL st D y.1 ∧ XOK st D x y.1) ?_ ?_
      · split
        · try simp only [lift, bind_ok]
          refine WP.spec_bind (JV.setz hO hV h4 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i (by
            rw [wsub1 hn0] at hi; omega))⟩) ?_
          rintro s5 ⟨h5, k5, c5⟩
          refine (WP.spec_ok _).2 ⟨h5, d4.ck hDO hxD (fun y hy hne => ⟨(k5 y hy hne).1, (k5 y hy hne).2.1⟩),
            fun c' hc' => ?_⟩
          rw [c5] at hc'; rw [← okinj hc']
          exact Or.inr (Or.inr (Or.inr ⟨p, _, _, rfl, fun i hi => hcov i (by rw [wsub1 hn0] at hi; omega)⟩))
        · simp only [bind_ok, WP.spec_ok]
          exact ⟨h4, d4, fun c' hc' => by rw [c4] at hc'; rw [← okinj hc']; exact zk n le_rfl⟩
      rintro ⟨s5, a5⟩ ⟨h5, d5, x5⟩
      try simp only [uncurry_apply_pair] at h5 d5 x5 ⊢
      try dsimp only
      ztail
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h4, fun v hv => by cases hv⟩
  · exact ⟨h, hD, hX⟩

set_option maxHeartbeats 4000000 in
/-- **The exposed `cdt.delete` of a slot of `OS` whose cap is `XK` over a leaf domain `D` keeps `JV`.** -/
theorem cdt.delete.zv {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) {s0 s : S}
    (hW : WuApart OS (L.ksb s0)) {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomL st D s) (hX : XOK st D x s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.zv (a := a) hP hO hA hV hDO hW h hx hD hX) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [hv1 v rfl]
    refine WP.spec_bind (cdt.empty_slot.jv hO hV h1 hx) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

/-- **The Zombie kind over `JV`**: the exposed `cdt.delete` of a slot of `OS` holding `Zombie p t n` (any `n`)
whose covered slots form a leaf domain `D` keeps `JV`. -/
theorem cdt.delete.zombieV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) {s0 s : S}
    (hW : WuApart OS (L.ksb s0)) {a : A} {x p t n : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomL st D s)
    (hc : obj.Slot.cap st x s = ok (.Zombie p t n)) (hcov : ∀ i : U64, i.val < n.val → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zv hP hO hA hV hDO hW h hx hD fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inr (Or.inr (Or.inr ⟨p, t, n, rfl, hcov⟩))

/-- **The thread kind's deletion over `JV`, final or not**: the exposed `cdt.delete` of a slot of `OS` holding
`Thread p` (`p` not the idle thread) whose seven TCB slots form a leaf domain `D` keeps `JV` (a final thread's
remainder `Zombie p ZOMBIE_TCB 7` runs the Zombie loop over the TCB slots). -/
theorem cdt.delete.threadV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) {s0 s : S}
    (hW : WuApart OS (L.ksb s0)) {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomL st D s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zv hP hO hA hV hDO hW h hx hD fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩)

/-- **The CNode kind's deletion over `JV`, final or not**: the exposed `cdt.delete` of a slot of `OS` holding
`CNode p r g b` whose `2^radix` slots form a leaf domain `D` keeps `JV` (a final CNode's remainder
`Zombie p r 2^radix` runs the Zombie loop over its slots). -/
theorem cdt.delete.cnodeV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) {s0 s : S}
    (hW : WuApart OS (L.ksb s0)) {a : A} {x p r g b : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomL st D s)
    (hc : obj.Slot.cap st x s = ok (.CNode p r g b))
    (hcov : ∀ i : U64, i.val < 2 ^ (r.val % 64) → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zv hP hO hA hV hDO hW h hx hD fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inr (Or.inr (Or.inl ⟨p, r, g, b, rfl, hcov⟩))

end zv

/-! ## The entry fact -/

/-- **[J] (a64) `SlotTyEntZ`**: [J] `SlotTyEntV` and, for the same `OS`, `WuApart OS (ks e)` (the kernel-global
`WORK_UNITS` word in no `OS` slot). At `P3Ok` states only, over the ghost `OS` and the fixed `ks` base, not a word
class. Source: `layout::ks::WORK_UNITS` = 40 (arch/aarch64/layout.rs) is a word of the kernel-global scalar area
below the IRQ-state table (`ks + 224`) and the IRQ node (`ks + 43232`); `OS` is the live CNode / TCB / IRQ-node
slots (QueueSlotTy's reading): CNodes and TCBs are retyped from untyped memory and lie outside the kernel-global
area (`SchedQueuesInvX.ksOut` for TCBs; untyped.rs for CNodes), and the IRQ-node slots start at `ks + 43232`. -/
def SlotTyEntZ (st : machine.Store S) [L : LawfulStore st] (T Cs Ω Sg : Set U64) (H : Heap) (Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ e, P3Ok e → ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS e ∧ EntApart st e OS ∧
    (∀ t ∈ T, t ∈ OS) ∧ IrqStApart OS (L.ksb e) ∧ ScApart Scs Z OS ∧ VcOK T Scs Z OS Vc Ub ∧
    VcTy st T Cs Ω H Sg Scs Z Vc Ub e ∧ VcEntApart st T e Vc ∧ WuApart OS (L.ksb e)

/-- `SlotTyEntZ` implies `SlotTyEntV` (a field dropped). -/
theorem SlotTyEntZ.toV (h : SlotTyEntZ st T Cs Ω Sg H Rp Scs Nt Z P3Ok) : SlotTyEntV st T Cs Ω Sg H Rp Scs Nt Z P3Ok :=
  fun e he => by
    obtain ⟨OS, Vc, Ub, a, b, c, d, f, g, i, j, k, -⟩ := h e he
    exact ⟨OS, Vc, Ub, a, b, c, d, f, g, i, j, k⟩

/-- **`SlotTyEntZ` at every `EntAt` state** (QueueVcTy's `SlotTyEntV.entAt`, with the `ks` base kept). -/
theorem SlotTyEntZ.entAt (hJ : SlotTyEntZ st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s)
    (hTP : TcbPlaced T) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ (∀ t ∈ T, t ∈ OS) ∧ IrqStApart OS (L.ksb s) ∧
      ScApart Scs Z OS ∧ VcOK T Scs Z OS Vc Ub ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧ WuApart OS (L.ksb s) := by
  obtain ⟨e, he, hw⟩ := hE
  obtain ⟨OS'', Vc', Ub', hO', hT', hA', hc', hap', hsc', hV', hv', hVA', hwu⟩ := hJ e he
  refine ⟨OS'', Vc', Ub', hO', fun y hy => ?_, hc', by rw [hw.1]; exact hap', hsc', hV', hv'.keep ?_,
    by rw [hw.1]; exact hwu⟩
  · obtain ⟨v8, v16, v24⟩ := vals hO' hy
    have k : ∀ b, Aligned b → y.val ≤ b.val → b.val < y.val + 32 → L.mem s b = L.mem e b :=
      fun b hb h1 h2 => hw.mem_eq hb fun hb' => hA' b hb' y hy ⟨h1, h2⟩
    exact (hT' y hy).of_eq (k _ (hO'.al0 hy) (by omega) (by omega))
      (k _ (hO'.al hy (by simp) (by simp)) (by omega) (by omega))
      (k _ (hO'.al hy (by simp) (by simp)) (by omega) (by omega))
      (k _ (hO'.al hy (by simp) (by simp)) (by omega) (by omega))
  · refine ⟨hw.1, fun b hb => hw.mem_eq (hv'.w hb).1 fun hb' => (hVA' b hb').1 hb,
      fun t ht => hw.mem_eq (field_aligned (hTP t ht) (by simp) (by simp)) fun hb' => (hVA' _ hb').2 t ht |>.1 rfl,
      fun t ht => hw.mem_eq (field_aligned (hTP t ht) (by simp) (by simp)) fun hb' => (hVA' _ hb').2 t ht |>.2 rfl,
      fun t ht => Or.inl ?_⟩
    have hy := hV'.bcov t ht
    obtain ⟨v8, -, -⟩ := vals hO' hy
    have k : ∀ b, Aligned b → (sbWordA t).val ≤ b.val → b.val < (sbWordA t).val + 32 → L.mem s b = L.mem e b :=
      fun b hb h1 h2 => hw.mem_eq hb fun hb' => hA' b hb' _ hy ⟨h1, h2⟩
    rw [DPF.slot_cap_dec, DPF.slot_cap_dec, k _ (hO'.al0 hy) (by omega) (by omega),
      k _ (hO'.al hy (k := 8#u64) (by simp) (by simp)) (by omega) (by omega)]

/-- **The Zombie loop from the entry fact**: at an `EntAt` decode start, under [J] `SlotTyEntZ`, the decode's
restart starts `JV`, and from every state it reaches the exposed `cdt.delete` of a slot of `OS` whose cap is `XK`
over a leaf domain `D ⊆ OS` (a Zombie, a thread, a CNode, final or not, or a leaf) keeps `JV`; no apartness
hypothesis is left. -/
theorem cdt.delete.zv_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntZ st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
        JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 ∧
        ∀ (a : A) (x : U64) (Dm : Set U64), Dm ⊆ OS → x ∈ OS → DomL st Dm s1 → XOK st Dm x s1 →
          cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄ ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, hO, hT, -, -, hsc, hV, hv, hwu⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, WP.spec_mono (JV.restart hO hV D hT hv) fun s1 h1 =>
    ⟨h1.1, fun a x Dm hDO hx hD hX => cdt.delete.zv hP hO hsc hV hDO hwu h1.1 hx hD hX⟩⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1

/-
P1 (aarch64, gen 31): **the cleanup kinds over `SlotTy`**: final endpoints (with waiters), final notifications and
final replies (with a TCB), `J` to `J`.

Gen 30 found that every finaliser footprint (`KW` / `KWB`, QueueFoot) covers TCB offsets from 192, which on AArch64
include slot 6 (offsets 192–223), an `OS` slot. QueueFoot7 restates the endpoint / notification / reply chain with
the bound 224 (`K7.KW`). Here:

* **`OS` apart from a `K7.KW` footprint** (`kw7_not_os`): a word of an `OS` slot (a `W7.CapW` word, `OSOK.slot`) is
  * no TCB field at offset ≥ 224 (`capw_ne_hi`) and no node word (`capw_ne_node`), as gen 30's restart;
  * no frame word `Sg`: `Sg ⊆ Ω` lies outside the TCBs (`SgOK.sub`, `SchedQueuesInvX.omega`), and `CapW`'s `Ω`
    part excludes `Sg`;
  * no endpoint / notification queue word: those lie outside the TCBs and apart from `Ω` (`EpsWit`, the
    `SchedQueuesInvX.eps` witness: `ep_out` and its `Ω` clause), **derived, no premise**;
  * no SC word: by **`ScApart Scs Z OS`** (every `OS` slot outside every SC object of `Scs`). SC words are in `Ω`
    (`ObjsOK.scW`) and partly outside `Sg`, so `W7.CapW` alone does not exclude them: this is the one new
    placement fact.
* no debug-list word (`dbg_not_capw`: TCB offsets 3576 / 3584 and the node's `DEBUG_TCBS` word), for the reply's
  `FootD`.
* `OSKeep.of_in` / `.of_kw7` / `.of_kwd7`: such a footprint keeps every `OS` word, so `SlotTy` (`SlotTy.keep`).
* **`FinJ`** (the cap's finalisation, for every finality, ends in `J` with `(Null, Null)`), the generic
  `cdt.finalise_slot_immediate.finJ` and **`cdt.delete.finJ`** (`J` to `J`).
* `finJ_ep` / `finJ_ntfn` / `finJ_reply`: the `Cur0` part from the existing `finGap_ep` / `finGap_ntfn` /
  `W7.R.finGap_reply0`, `RunVcpuInv` from `W7.R.finRv_ep` / `finRv_ntfn` / `finRv_reply`, and `SlotTy` from
  QueueFoot7's `K7.fin_endpoint.blk` / `K7.fin_ntfn.blk` / `K7.fin_reply.blk` with `OSKeep`. They hold for every
  finality and every queue / TCB state: final endpoints with waiters, final notifications (SC unbinding, TCB
  unbinding, waiters), final replies with a TCB (`reply_remove` or `cancel_ipc`) included.
* **`cdt.delete.eprn`**: the exposed `cdt.delete` of an `OS` slot holding an endpoint, notification or reply cap
  keeps `J`, under `ScApart`.
* **[J] `SlotTyEntS`** (new, named): [J] `SlotTyEntI` and `ScApart Scs Z OS` for the same `OS`. It implies
  `SlotTyEntI` (`SlotTyEntS.toI`). `SlotTyEntS.entAt`, **`cdt.delete.eprn_ent`** (from an `EntAt` decode start,
  after the decode's restart, no apartness hypothesis left).

`ScApart` is a fact of the ghost `OS`, the ghost SC set `Scs` and the ghost sizes `Z`, not of a word class and not
of a state, so gen 28's trick (rewrite a free word at an `Fr0 ∧ BXI` state) does not apply to it. Source: under
QueueSlotTy's reading `OS` is the live CNode / TCB / IRQ-node slots. CNodes, TCBs and SCs are distinct objects
carved by `create_new_objects` from the free part of an untyped (objects.rs:528–546, objects at
`base + i << size`; untyped.rs:56–68, the free watermark, reset to 0 only when the untyped has no children), and
the IRQ node is in the kernel-global area (layout.rs `ks::IRQ_NODE`), which no untyped covers. So no SC object
overlaps an `OS` slot on reachable states.

No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueSlotTyIrq
import Fl4ProofsA64.P1.QueueFoot7
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

/-! ## `OS` apart from the finalisers' footprints -/

/-- **Every `OS` slot lies outside every SC object** (module docstring). -/
def ScApart (Scs : Set U64) (Z : U64 → Nat) (OS : Set U64) : Prop :=
  ∀ x ∈ OS, ∀ c ∈ Scs, x.val + 32 ≤ c.val ∨ c.val + 2 ^ Z c ≤ x.val

/-- **A word of an `OS` slot is no `K7.KW` word** (TCB fields from 224, node words, frame words, SC words,
endpoint / notification queue words). -/
theorem kw7_not_os {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {OS Es : Set U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hA : ScApart Scs Z OS)
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) {x b : U64} (hx : x ∈ OS) (hb : W7.CapW T Ω Sg b)
    (h1 : x.val ≤ b.val) (h2 : b.val < x.val + 32) : ¬ K7.KW st T Cs Sg Scs Z Es s b := by
  rintro (⟨y, hy, K, k1, k2, -, -, e⟩ | ⟨c, hc, o, ho, -, e⟩ | hm | ⟨c, hc, hin⟩ | ⟨e', he', hb'⟩)
  · exact capw_ne_hi q hb hy k1 k2 e
  · exact capw_ne_node q hb hc ho e
  · rcases hb with hl | ⟨-, hn⟩
    · exact W7.tlow_ne_out q.tcbs (q.omega _ (hsub b hm)) hl
    · exact hn hm
  · have := hA x hx c hc
    have := hin.1
    have := hin.2
    omega
  · obtain ⟨E, EQ, w1, -, wΩ, -, -, ty⟩ := q.eps
    have heE : e' ∈ E := (ty.2.2.1 e').2 (hE e' he')
    obtain ⟨hE', hEN, -⟩ := w1 e' heE
    obtain ⟨o1, o2⟩ := ep_out hE' hEN
    rcases hb with hl | ⟨hΩ, -⟩
    · rcases hb' with rfl | rfl
      · exact W7.tlow_ne_out q.tcbs o1 hl
      · exact W7.tlow_ne_out q.tcbs o2 hl
    · have := wΩ e' heE b hΩ
      rcases hb' with rfl | rfl
      · rw [epHeadA_val] at this; omega
      · rw [epTSA_val hE'] at this; omega

/-- A cap-slot word is no debug-list word (TCB offsets 3576 / 3584, the node's `DEBUG_TCBS` word). -/
theorem dbg_not_capw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) {b : U64} (hb : W7.CapW T Ω Sg b) : ¬ DbgW st T Cs s b := by
  rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
  · exact capw_ne_hi q hb hy (K := 3576#u64) (by simp) (by simp) e
  · exact capw_ne_hi q hb hy (K := 3584#u64) (by simp) (by simp) e
  · exact capw_ne_node q hb hc (by rw [debug_val]; omega) e

/-- A footprint with no word inside an `OS` slot keeps every `OS` word. -/
theorem OSKeep.of_in {OS : Set U64} (hO : OSOK T Ω Sg OS) {s s' : S} {F : U64 → Prop} (hw : WritesIn st s s' F)
    (hF : ∀ x ∈ OS, ∀ b, W7.CapW T Ω Sg b → x.val ≤ b.val → b.val < x.val + 32 → ¬ F b) :
    OSKeep st OS s s' := fun y hy => by
  have k : ∀ k : U64, k.val < 32 → k.val % 8 = 0 → L.mem s' (wa y k) = L.mem s (wa y k) := fun k hk h8 =>
    hw.mem_eq (hO.al hy hk h8) (hF y hy _ (hO.cw hy hk h8) (by rw [wv (hO.fit y hy) hk]; omega)
      (by rw [wv (hO.fit y hy) hk]; omega))
  have k0 := k 0#u64 (by simp) (by simp)
  rw [SFF.wadd0'] at k0
  exact ⟨k0, k 8#u64 (by simp) (by simp), k 16#u64 (by simp) (by simp), k 24#u64 (by simp) (by simp)⟩

/-- **A `K7.Foot` footprint keeps every `OS` word** (`ScApart`, heap endpoints / notifications as `Es`). -/
theorem OSKeep.of_kw7 {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {OS Es : Set U64} {s s' : S}
    (hO : OSOK T Ω Sg OS) (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hA : ScApart Scs Z OS) (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn)
    (f : K7.Foot st T Cs Sg Scs Z Es s s') : OSKeep st OS s s' :=
  OSKeep.of_in hO f fun _ hx _ hb h1 h2 => kw7_not_os q hsub hA hE hx hb h1 h2

/-- **A `K7.FootD` footprint keeps every `OS` word** (`K7.KW` and debug-list words). -/
theorem OSKeep.of_kwd7 {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {OS Es : Set U64} {s s' : S}
    (hO : OSOK T Ω Sg OS) (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hA : ScApart Scs Z OS) (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn)
    (f : K7.FootD st T Cs Sg Scs Z Es s s') : OSKeep st OS s s' :=
  OSKeep.of_in hO f fun _ hx _ hb h1 h2 hk =>
    hk.elim (kw7_not_os q hsub hA hE hx hb h1 h2) (dbg_not_capw q hb)

/-! ## A finalisation that ends in `J`, and the deletion over it -/

/-- **The finalisation of the cap in slot `x`, for every finality, ends in `J` with `(Null, Null)`.** -/
def FinJ (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac OS : Set U64) (s0 s : S) (x : U64) : Prop :=
  ∀ (a : A) (c : capability.Cap) (fin : Bool), obj.Slot.cap st x s = ok c →
    objects.finalise_cap st ar s a c fin false ⦃ r =>
      r.1 = (.Null, .Null) ∧ J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.2.1 ⦄

set_option maxHeartbeats 4000000 in
/-- `finalise_slot_immediate` of a slot whose cap's finalisation is `FinJ`: `J`, a null cleanup. -/
theorem cdt.finalise_slot_immediate.finJ {A : Type _} {ar : machine.Arch A} {OS : Set U64} {s0 s : S} {a : A}
    {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hk : FinJ st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s x) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.2.1 ∧ ∀ v, r.1 = .Ok v → v.cleanup = .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val) (inv := fun y => y.1 = s)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    have hJ1 : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s1 := h1 ▸ h
    have hk1 : FinJ st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s1 x := h1 ▸ hk
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨hJ1, by intro v hv; simp_all⟩
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s1 hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨hJ1, fun v hv => by cases hv; rfl⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (hk1 a1 c fin hc) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨e1, h2⟩
    simp only [Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    try dsimp only
    first
    | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]; exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; rfl⟩)
    | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]; exact ⟨h2, fun v hv => by cases hv; rfl⟩)
    | (simp [cdt.cap_removable, WP.spec_ok]; exact h2)
    | (simp [cdt.cap_removable, WP.spec_ok, h2])
  · rfl

set_option maxHeartbeats 2000000 in
/-- **The exposed `cdt.delete` of a slot of `OS` whose cap's finalisation is `FinJ` keeps `J`.** -/
theorem cdt.delete.finJ {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS) {s0 s : S} {a : A}
    {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hx : x ∈ OS)
    (hk : FinJ st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s x) :
    cdt.delete st ar s a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.finJ (a := a) h hk) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [hv1 v rfl]
    refine WP.spec_bind (cdt.empty_slot.ty hO h1 hx) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

/-! ## The endpoint, notification and reply kinds -/

theorem dc_ep {ep b0 b1 b2 b3 b4 : _} (hH : H ep = some .ep) :
    Fl4ProofsA64.P1.DelCapOK T Ω Sg H Rp Nt (.Endpoint ep b0 b1 b2 b3 b4) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

theorem dc7_ep {ep b0 b1 b2 b3 b4 : _} (hH : H ep = some .ep) :
    W7.DelCapOK T Ω Sg H Rp Nt (.Endpoint ep b0 b1 b2 b3 b4) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

theorem dc_ntfn {n b0 : U64} {b1 b2 : Bool} (hn : n ∈ Nt) (hH : H n = some .ntfn) :
    Fl4ProofsA64.P1.DelCapOK T Ω Sg H Rp Nt (.Notification n b0 b1 b2) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

theorem dc7_ntfn {n b0 : U64} {b1 b2 : Bool} (hn : n ∈ Nt) (hH : H n = some .ntfn) :
    W7.DelCapOK T Ω Sg H Rp Nt (.Notification n b0 b1 b2) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

theorem dc7_reply {p : U64} {x : Bool} (hp : p ∈ Rp) : W7.DelCapOK T Ω Sg H Rp Nt (.Reply p x) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

theorem finPl_of {s : S} {c : capability.Cap} (h1 : ∀ p, c ≠ .Thread p) (h2 : ∀ p b, c ≠ .SchedContext p b) :
    FinPl st Scs s c := by
  refine ⟨fun p e => absurd e (h1 p), fun p b e => absurd e (h2 p b)⟩

/-- The `J`-state facts the kinds use: the invariants at `s`, its queue witness and `Sg ⊆ Ω`. -/
theorem J.parts {OS : Set U64} {s0 s : S} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) :
    ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s := h.1.bxi

set_option maxHeartbeats 2000000 in
/-- **The endpoint kind, any finality** (a final endpoint with waiters included): `FinJ`. -/
theorem finJ_ep {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    {s0 s : S} {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hx : x ∈ OS)
    (hk : ∀ c, obj.Slot.cap st x s = ok c → ∃ p b0 b1 b2 b3 b4, c = .Endpoint p b0 b1 b2 b3 b4) :
    FinJ st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s x := by
  intro a c fin hc
  obtain ⟨ep, b0, b1, b2, b3, b4, rfl⟩ := hk c hc
  have hty := (h.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  have hH : H ep = some .ep := hty.1.1.1 ep b0 b1 b2 b3 b4 rfl
  obtain ⟨Ac', hb⟩ := h.parts
  have q := hb.1.choose_spec.choose_spec
  have hsub : ∀ b ∈ Sg, b ∈ Ω := by obtain ⟨-, -, -, -, hSg⟩ := hb.blk; exact hSg.sub
  have G := Fl4ProofsA64.P1.finGap_ep (ar := ar) Ac s0 s a _ fin h.1.1 (dc_ep hH)
    (finPl_of (fun _ e => by cases e) (fun _ _ e => by cases e)) ⟨ep, b0, b1, b2, b3, b4, rfl⟩
  have Rv : objects.finalise_cap st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ :=
    Fl4ProofsA64.P1.W7.R.finRv_ep (ar := ar) (a := a) (fin := fin) h.1.1 h.1.2 (dc7_ep hH)
  have F : objects.finalise_cap st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin false ⦃ r =>
      r.1 = (.Null, .Null) ∧ K7.Foot st T Cs Sg Scs Z {ep} s r.2.1 ⦄ := by
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (K7.fin_endpoint.blk (ar := ar) s a ep b0 b1 b2 b3 b4 fin hb.blk hH) fun r hr =>
      ⟨hr.1, hr.2.2.2⟩
  refine WP.spec_mono (WP.spec_and G (WP.spec_and Rv F)) ?_
  rintro r ⟨⟨c0, -, -⟩, rv, e, f⟩
  exact ⟨e, ⟨c0, rv⟩, h.2.keep (OSKeep.of_kw7 hO q hsub hA
    (fun e he => by rw [Set.mem_singleton_iff.1 he]; exact Or.inl hH) f)⟩

set_option maxHeartbeats 2000000 in
/-- **The notification kind, any finality** (SC unbinding, TCB unbinding, waiters): `FinJ`. -/
theorem finJ_ntfn {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    {s0 s : S} {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hx : x ∈ OS)
    (hk : ∀ c, obj.Slot.cap st x s = ok c → ∃ n b0 b1 b2, c = .Notification n b0 b1 b2) :
    FinJ st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s x := by
  intro a c fin hc
  obtain ⟨n, b0, b1, b2, rfl⟩ := hk c hc
  have hty := (h.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  obtain ⟨hn, hH⟩ := hty.1.1.2.1 n b0 b1 b2 rfl
  obtain ⟨Ac', hb⟩ := h.parts
  have q := hb.1.choose_spec.choose_spec
  have hsub : ∀ b ∈ Sg, b ∈ Ω := by obtain ⟨-, -, -, -, hSg⟩ := hb.blk; exact hSg.sub
  have G := Fl4ProofsA64.P1.finGap_ntfn (ar := ar) Ac s0 s a _ fin h.1.1 (dc_ntfn hn hH)
    (finPl_of (fun _ e => by cases e) (fun _ _ e => by cases e)) ⟨n, b0, b1, b2, rfl⟩
  have Rv : objects.finalise_cap st ar s a (.Notification n b0 b1 b2) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ :=
    Fl4ProofsA64.P1.W7.R.finRv_ntfn (ar := ar) (a := a) (fin := fin) h.1.1 h.1.2 (dc7_ntfn hn hH)
  have F : objects.finalise_cap st ar s a (.Notification n b0 b1 b2) fin false ⦃ r =>
      r.1 = (.Null, .Null) ∧ K7.Foot st T Cs Sg Scs Z {n} s r.2.1 ⦄ := by
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (K7.fin_ntfn.blk (ar := ar) s a n b0 b1 b2 fin hb.blk hn hH) fun r hr =>
      ⟨hr.1, hr.2.2.2⟩
  refine WP.spec_mono (WP.spec_and G (WP.spec_and Rv F)) ?_
  rintro r ⟨⟨c0, -, -⟩, rv, e, f⟩
  exact ⟨e, ⟨c0, rv⟩, h.2.keep (OSKeep.of_kw7 hO q hsub hA
    (fun e he => by rw [Set.mem_singleton_iff.1 he]; exact Or.inr hH) f)⟩

set_option maxHeartbeats 2000000 in
/-- **The reply kind, any finality** (a replier blocked on the reply removed, a receiver's IPC cancelled):
`FinJ`. -/
theorem finJ_reply {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) {OS : Set U64}
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    {s0 s : S} {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hx : x ∈ OS)
    (hk : ∀ c, obj.Slot.cap st x s = ok c → ∃ p g, c = .Reply p g) :
    FinJ st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s x := by
  intro a c fin hc
  obtain ⟨p, g, rfl⟩ := hk c hc
  have hty := (h.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  have hp : p ∈ Rp := hty.1.1.2.2 p g rfl
  obtain ⟨Ac', hb⟩ := h.parts
  have q := hb.1.choose_spec.choose_spec
  have hsub : ∀ b ∈ Sg, b ∈ Ω := by obtain ⟨-, -, -, -, hSg⟩ := hb.blk; exact hSg.sub
  have G := Fl4ProofsA64.P1.W7.R.finGap_reply0 (ar := ar) hP (s0 := s0) Ac s a _ fin h.1.1 h.1.2 (dc7_reply hp)
    (finPl_of (fun _ e => by cases e) (fun _ _ e => by cases e)) ⟨p, g, rfl⟩
  have Rv : objects.finalise_cap st ar s a (.Reply p g) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ :=
    Fl4ProofsA64.P1.W7.R.finRv_reply (ar := ar) hP (a := a) (fin := fin) h.1.1 h.1.2 (dc7_reply hp)
  have F : objects.finalise_cap st ar s a (.Reply p g) fin false ⦃ r =>
      r.1 = (.Null, .Null) ∧ K7.FootD st T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (K7.fin_reply.blk (ar := ar) hP s a p g fin hb.blk hp h.1.2) fun r hr =>
      ⟨hr.1, hr.2.2⟩
  refine WP.spec_mono (WP.spec_and G (WP.spec_and Rv F)) ?_
  rintro r ⟨⟨c0, -, -⟩, rv, e, f⟩
  exact ⟨e, ⟨c0, rv⟩, h.2.keep (OSKeep.of_kwd7 hO q hsub hA (fun e he => he) f)⟩

/-- The endpoint, notification and reply kinds. -/
def EpNtRp (c : capability.Cap) : Prop :=
  (∃ p b0 b1 b2 b3 b4, c = .Endpoint p b0 b1 b2 b3 b4) ∨ (∃ n b0 b1 b2, c = .Notification n b0 b1 b2) ∨
    (∃ p g, c = .Reply p g)

/-- The cap in slot `x` is an endpoint, notification or reply cap. -/
def EpNtRpAt (st : machine.Store S) [L : LawfulStore st] (x : U64) (s : S) : Prop :=
  ∀ c, obj.Slot.cap st x s = ok c → EpNtRp c

theorem finJ_eprn {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) {OS : Set U64}
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    {s0 s : S} {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hx : x ∈ OS) (hk : EpNtRpAt st x s) :
    FinJ st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s x := by
  intro a c fin hc
  rcases hk c hc with he | hn | hr
  · exact finJ_ep hO hA h hx (fun c' hc' => by rw [hc] at hc'; rw [← okinj hc']; exact he) a c fin hc
  · exact finJ_ntfn hO hA h hx (fun c' hc' => by rw [hc] at hc'; rw [← okinj hc']; exact hn) a c fin hc
  · exact finJ_reply hP hO hA h hx (fun c' hc' => by rw [hc] at hc'; rw [← okinj hc']; exact hr) a c fin hc

/-- **The exposed `cdt.delete` of an endpoint, notification or reply slot of `OS` keeps `J`** (any finality:
final endpoints with waiters, final notifications, final replies with a TCB included), under `ScApart`. -/
theorem cdt.delete.eprn {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) {OS : Set U64}
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) {s0 s : S} {a : A} {x : U64}
    (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hx : x ∈ OS) (hk : EpNtRpAt st x s) :
    cdt.delete st ar s a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.2.1 ⦄ :=
  cdt.delete.finJ hO h hx (finJ_eprn hP hO hA h hx hk)

/-! ## The entry fact with the SC apartness -/

/-- **[J] (a64) `SlotTyEntS`**: [J] `SlotTyEntI` and `ScApart Scs Z OS` for the same `OS` (module docstring for
the source). At `P3Ok` states only; over the ghost sets `OS`, `Scs` and the ghost sizes `Z`; not a word class. -/
def SlotTyEntS (st : machine.Store S) [L : LawfulStore st] (T Ω Sg : Set U64) (H : Heap) (Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ e, P3Ok e → ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS e ∧ EntApart st e OS ∧ (∀ t ∈ T, t ∈ OS) ∧
    IrqStApart OS (L.ksb e) ∧ ScApart Scs Z OS

/-- `SlotTyEntS` implies `SlotTyEntI` (a field dropped). -/
theorem SlotTyEntS.toI (h : SlotTyEntS st T Ω Sg H Rp Scs Nt Z P3Ok) : SlotTyEntI st T Ω Sg H Rp Nt P3Ok :=
  fun e he => by obtain ⟨OS, a, b, c, d, f, -⟩ := h e he; exact ⟨OS, a, b, c, d, f⟩

/-- `SlotTyEntS` at every `EntAt` state. -/
theorem SlotTyEntS.entAt (hJ : SlotTyEntS st T Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) :
    ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ (∀ t ∈ T, t ∈ OS) ∧ IrqStApart OS (L.ksb s) ∧
      ScApart Scs Z OS := by
  obtain ⟨e, he, hw⟩ := hE
  obtain ⟨OS, hO, hT, hA, hc, hap, hsc⟩ := hJ e he
  refine ⟨OS, hO, fun y hy => ?_, hc, by rw [hw.1]; exact hap, hsc⟩
  obtain ⟨v8, v16, v24⟩ := vals hO hy
  have k : ∀ b, Aligned b → y.val ≤ b.val → b.val < y.val + 32 → L.mem s b = L.mem e b :=
    fun b hb h1 h2 => hw.mem_eq hb fun hb' => hA b hb' y hy ⟨h1, h2⟩
  exact (hT y hy).of_eq (k _ (hO.al0 hy) (by omega) (by omega)) (k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega))
    (k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega)) (k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega))

/-- **The cleanup kinds from the entry fact**: at an `EntAt` decode start, under [J] `SlotTyEntS`, after the
decode's restart (`J.restart`), the exposed `cdt.delete` of an endpoint, notification or reply slot of `OS` keeps
`J`; no apartness hypothesis is left. -/
theorem cdt.delete.eprn_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntS st T Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧
      sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
        J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s s1 ∧
        ∀ (a : A) (x : U64), x ∈ OS → EpNtRpAt st x s1 →
          cdt.delete st ar s1 a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s r.2.1 ⦄ ⦄ := by
  obtain ⟨OS, hO, hT, -, -, hsc⟩ := hJ.entAt hE
  exact ⟨OS, hO, hT, WP.spec_mono (J.restart hO D hT) fun s1 h1 =>
    ⟨h1.1, fun a x hx hk => cdt.delete.eprn hP hO hsc h1.1 hx hk⟩⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1

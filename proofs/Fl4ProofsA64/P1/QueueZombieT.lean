/-
P1 (aarch64, gen 35): **the Zombie loop with thread and VCPU caps inside covered slots** (`ZT`), over `JV`,
extending gen 34's `ZN` loop (QueueZombieN) by the two kinds whose case facts are state-free once the idle-thread
word is carried along the loop (QueueIdleKeep).

* **The idle word along the loop.** Every step of `finalise_slot_immediate` / `finalise_slot_deferred` keeps
  `L.idleW`: the finalisers of the covered kinds (`idlL` for the leaves — `TrivK` writes nothing, endpoint by
  QueueCaiFr's `CaiFr.idle`, notification / reply by QueueIdleKeep —, CNode / Zombie write nothing,
  `fin_thread.idlV`, the VCPU's `UbF.idle`); the cap-slot writes of `set_cap` (the Zombie remainder), `swap` and
  `empty_slot` — they write only `W7.CapW` words (`cdt.swap.jvw`, `cdt.empty_slot.cw`), and a `CapW` word is no node
  word (`capw_ne_node`), so **`idle_of_cw`**; the preemption point (gen 33's `sched.preemption_point.jv`).
* **`ZT Vc D I`** (a domain cap with threads and VCPUs): gen 34's `ZN D`, or `Thread p` with `p ≠ I` and its seven
  TCB slots in `D`, or `Vcpu v` with `v ∈ Vc`. `I` is a ghost value, the loop keeps `L.idleW s = I`; at the top it
  is the idle word of the deletion's start state. **`DomT`** (every slot of `D` holds a `ZT` cap), **`XT`** (the
  deleted slot does).
* **`finXT`** (the finalisation of a `ZT` cap: null cleanup, `JV`, `OSKeep`, a `ZRem` remainder, the idle word
  kept), **`cdt.cap_swap_for_delete.zt`**, **`cdt.finalise_slot_deferred.zt`**, **`cdt.delete_deferred.zt`**,
  **`cdt.finalise_slot_immediate.zt`** (invariant `JV ∧ DomT ∧ XT ∧ idle = I`), **`cdt.delete.ztI`** /
  **`cdt.delete.zt`**, instances **`cdt.delete.threadT`** (a thread whose TCB slots — or the slots of its CSpace
  CNode, at any depth — hold thread caps, e.g. the CSpace root CNode holding the thread's own TCB cap, and VCPU
  caps), **`cdt.delete.cnodeT`**, **`cdt.delete.zombieT`**, gen 34's `ZN` top as a corollary (`cdt.delete.zn''`);
  **`cdt.delete.zt_ent`** ([J] `SlotTyEntZ`), **`syscall.decode_invocation.del_zt`**, **`del_zt_ent`**.

**Not covered** (left out of `ZT`): SC caps (their case `ScPlAt` reads the SC's `TCB` word, which the thread and
reply finalisers of other covered slots write — unbind / donation —, so "not the idle thread" must be re-derived per
step), IrqHandler caps (`IslTriv` of the IRQ-node slot, a state fact on a slot that may itself be in `D`), VSpace /
mapped-frame caps (a64.md §39).

No named premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueIdleKeep
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

section zt
variable {OS Vc Ub D : Set U64}

/-! ## Cap-slot writes keep the idle word -/

/-- **A `W7.CapW` footprint keeps the idle-thread word** (a cap-slot word is no node word). -/
theorem idle_of_cw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' (W7.CapW T Ω Sg)) :
    L.idleW s' = L.idleW s := by
  unfold LawfulStore.idleW
  rw [hw.2.1, nodeAt_of_ksb hw.1]
  exact hw.mem_eq (nodeAt_aligned (q.nodes _ q.cur) (by rw [idle8]; omega) (by rw [idle8]))
    (fun hb => capw_ne_node q hb q.cur (o := layout.node.IDLE_THREAD) (by rw [idle8]; omega) rfl)

theorem JV.idle_cw {s0 s s' : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hw : WritesIn st s s' (W7.CapW T Ω Sg)) : L.idleW s' = L.idleW s := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  exact idle_of_cw hb.1.choose_spec.choose_spec hw

/-! ## The domain class with threads and VCPUs -/

/-- **A domain cap with threads and VCPUs** (module docstring). -/
def ZT (Vc D : Set U64) (I : U64) (c : capability.Cap) : Prop :=
  ZN D c ∨ (∃ p, c = .Thread p ∧ p ≠ I ∧ ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) ∨ (∃ v, c = .Vcpu v ∧ v ∈ Vc)

/-- Every slot of `D` holds a `ZT` cap. -/
def DomT (st : machine.Store S) [L : LawfulStore st] (Vc D : Set U64) (I : U64) (s : S) : Prop :=
  ∀ y ∈ D, ∀ c, obj.Slot.cap st y s = ok c → ZT Vc D I c

/-- The slot `x`'s cap is a `ZT` cap. -/
def XT (st : machine.Store S) [L : LawfulStore st] (Vc D : Set U64) (I : U64) (x : U64) (s : S) : Prop :=
  ∀ c, obj.Slot.cap st x s = ok c → ZT Vc D I c

theorem zt_nf {I : U64} {c : capability.Cap} (h : ZT Vc D I c) : NoFrame c := by
  rcases h with h | ⟨_, rfl, -⟩ | ⟨_, rfl, -⟩
  · exact zn_nf h
  · intro p sz r d m e a v hc; cases hc
  · intro p sz r d m e a v hc; cases hc

theorem DomN.toT {I : U64} {s : S} (h : DomN st D s) : DomT st Vc D I s := fun y hy c hc => Or.inl (h y hy c hc)

theorem XOK.toT {s : S} {x : U64} (h : XOK st D x s) : XT st Vc D (L.idleW s) x s := fun c hc => by
  rcases h c hc with h | ⟨p, rfl, hid, hcov⟩ | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr h))

theorem DomT.osk {I : U64} {s s' : S} (h : DomT st Vc D I s) (hDO : D ⊆ OS) (k : OSKeep st OS s s') :
    DomT st Vc D I s' :=
  fun y hy c hc => h y hy c (by rw [k.cap (hDO hy)] at hc; exact hc)

theorem DomT.upd {I : U64} {s s' : S} (h : DomT st Vc D I s)
    (hk : ∀ y ∈ D, obj.Slot.cap st y s' = obj.Slot.cap st y s ∨
      ∀ c, obj.Slot.cap st y s' = ok c → ZT Vc D I c) :
    DomT st Vc D I s' := fun y hy c hc => by
  rcases hk y hy with e | e
  · rw [e] at hc; exact h y hy c hc
  · exact e c hc

theorem XT.keep {I : U64} {s s1 : S} {x : U64} (hx : x ∈ OS) (k : OSKeep st OS s s1) (hX : XT st Vc D I x s) :
    XT st Vc D I x s1 := fun c hc => by
  rw [k.cap hx] at hc
  exact hX c hc

set_option maxHeartbeats 4000000 in
/-- **`empty_slot` of a slot of `OS`, null cleanup, writes only `W7.CapW` words** (cdt.rs `empty_slot`: the
neighbours' links — `OS` slots by `SlotTy` — and the slot's words). -/
theorem cdt.empty_slot.cw {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) {s : S} {a : A} {x : U64}
    (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hx : x ∈ OS) :
    cdt.empty_slot st ar s a x .Null ⦃ r => WritesIn st s r.1 (W7.CapW T Ω Sg) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  have hxo := hT x hx
  obtain ⟨nx, hnx⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s (wa x 24#u64)))
  have hnl : LinkOK OS nx := hxo.2.2 nx hnx
  have hpv : LinkOK OS (L.mem s (wa x 16#u64)) := hxo.2.1
  rw [slot_prev_eq, bind_ok, slot_next_of hnx, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => WritesIn st s s1 (W7.CapW T Ω Sg)) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · rename_i hp0
      have hpO : L.mem s (wa x 16#u64) ∈ OS := hpv.resolve_left (by simpa using hp0)
      exact W7.obj.Slot.set_next.capw (hO.slot _ hpO)
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (W7.CapW T Ω Sg)) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnO : nx ∈ OS := hnl.resolve_left (by simpa using hn0)
      refine WP.spec_bind (W7.obj.Slot.set_prev.capw (hO.slot _ hnO)) fun s3 w3 => ?_
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx s3 hS) fun nfb _ => ?_
      split <;> exact WP.spec_mono (W7.obj.Slot.set_first_badged.capw (hO.slot _ hnO)) fun s' w =>
        (h1.trans1 w3).trans1 w
  refine WP.spec_bind (W7.obj.Slot.clear.capw (hO.slot _ hx)) fun s3 w3 => ?_
  rw [pcd_null]
  exact (WP.spec_ok _).2 (h2.trans1 w3)

/-! ## `swap` with its write set -/

/-- `SwP` and the swap's writes so far, all `W7.CapW` words. -/
def SwW (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac OS Vc Ub : Set U64) (s0 s : S) (x1 x2 : U64) (c1 c2 : capability.Cap) (s' : S) : Prop :=
  SwP st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s' ∧ WritesIn st s s' (W7.CapW T Ω Sg)

theorem SwW.lnk (hO : OSOK T Ω Sg OS) {s0 s s' : S} {x1 x2 : U64} {c1 c2 : capability.Cap}
    (h : SwW st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s') {p k v : U64} (hp : p ∈ OS)
    (hk : k.val = 16 ∨ k.val = 24) (hj : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 (L.wr s' (wa p k) v))
    (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) :
    SwW st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 (L.wr s' (wa p k) v) := by
  have k32 : k.val < 32 := by rcases hk with e | e <;> omega
  have k8 : k.val % 8 = 0 := by rcases hk with e | e <;> omega
  exact ⟨h.1.lnk hO hp hk hj hx1 hx2, h.2.trans1 ((writesIn_wr (v := v) (hO.al hp k32 k8)).mono fun b e => by
    subst e; exact hO.cw hp k32 k8)⟩

set_option maxHeartbeats 4000000 in
/-- **`cdt.swap.jv` with its write set**: the swap writes only `W7.CapW` words. -/
theorem cdt.swap.jvw (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x1 x2 : U64} {c1 c2 : capability.Cap}
    (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2)
    (hc1 : obj.Slot.cap st x1 s = ok c1) (hc2 : obj.Slot.cap st x2 s = ok c2) (hf1 : NoFrame c1)
    (hf2 : NoFrame c2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => SwW st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hd1 : capability.Cap.decode (L.mem s x1) (L.mem s (wa x1 8#u64)) = ok c1 := by
    rw [DPF.slot_cap_dec] at hc1; exact hc1
  have hd2 : capability.Cap.decode (L.mem s x2) (L.mem s (wa x2 8#u64)) = ok c2 := by
    rw [DPF.slot_cap_dec] at hc2; exact hc2
  have ht1 : CapTy T Ω Sg H Rp Nt OS c1 := (h.1.2 x1 hx1).1 _ hd1
  have ht2 : CapTy T Ω Sg H Rp Nt OS c2 := (h.1.2 x2 hx2).1 _ hd2
  obtain ⟨a1, b1, he1, hr1⟩ := CapRt.dec_rt hd1
  obtain ⟨a2, b2, he2, hr2⟩ := CapRt.dec_rt hd2
  unfold cdt.swap
  refine WP.spec_bind (WP.spec_and (JV.setc hO hV h hx1 he2 hr2 ht2 hf2)
    (W7.obj.Slot.set_cap.capw (hO.slot _ hx1))) ?_
  rintro s1 ⟨⟨h1, k1, e1⟩, w1⟩
  refine WP.spec_bind (WP.spec_and (JV.setc hO hV h1 hx2 he1 hr1 ht1 hf1)
    (W7.obj.Slot.set_cap.capw (hO.slot _ hx2))) ?_
  rintro s2 ⟨⟨h2, k2, e2⟩, w2⟩
  have P2 : SwW st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s2 :=
    ⟨⟨h2, by rw [capk4 k2 hx1 hne]; exact e1, e2, fun y hy n1 n2 => by
      rw [capk4 k2 hy n2, capk4 k1 hy n1]⟩, w1.trans1 w2⟩
  -- slot 1's links at `s2`
  have l1 := h2.1.2 x1 hx1
  rw [slot_prev_eq s2 x1, bind_ok]
  obtain ⟨n1, hn1⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s2 (wa x1 24#u64)))
  rw [slot_next_of hn1, bind_ok]
  have lp1 : LinkOK OS (L.mem s2 (wa x1 16#u64)) := l1.2.1
  have ln1 : LinkOK OS n1 := l1.2.2 n1 hn1
  have in1 : obj.sext48 n1 = ok n1 := sx_idem _ _ hn1
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x1 s2 hS) fun r1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x1 s2 hS) fun f1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s3 => SwW st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s3) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 P2
    · rename_i hp0
      have hpO : L.mem s2 (wa x1 16#u64) ∈ OS := lp1.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact P2.lnk hO hpO (k := 24#u64) (by simp)
        (JV.nextw hO hV h2 hpO (Or.inr hx2) hs2 (link_bits _ _)) hx1 hx2
  intro s3 P3
  refine WP.spec_bind (Pₘ := fun s4 => SwW st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s4) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 P3
    · rename_i hn0
      have hnO : n1 ∈ OS := ln1.resolve_left (by simpa using hn0)
      rw [set_prev_eq, WP.spec_ok]
      exact P3.lnk hO hnO (k := 16#u64) (by simp) (JV.prev hO hV P3.1.1 hnO (Or.inr hx2)) hx1 hx2
  intro s4 P4
  -- slot 2's links at `s4`
  have l2 := P4.1.1.1.2 x2 hx2
  rw [slot_prev_eq s4 x2, bind_ok]
  obtain ⟨n2, hn2⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s4 (wa x2 24#u64)))
  rw [slot_next_of hn2, bind_ok]
  have lp2 : LinkOK OS (L.mem s4 (wa x2 16#u64)) := l2.2.1
  have ln2 : LinkOK OS n2 := l2.2.2 n2 hn2
  have in2 : obj.sext48 n2 = ok n2 := sx_idem _ _ hn2
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x2 s4 hS) fun r2 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x2 s4 hS) fun f2 _ => ?_
  rw [set_prev_eq s4 x1 _, bind_ok]
  have P5 := P4.lnk hO hx1 (k := 16#u64) (by simp) (JV.prev hO hV P4.1.1 hx1 lp2) hx1 hx2
  refine WP.spec_bind (set_nf_spec _ x1 n2 r2 f2) ?_
  rintro s6 ⟨w6, rfl, hw6⟩
  have P6 := P5.lnk hO hx1 (k := 24#u64) (by simp) (JV.nextw hO hV P5.1.1 hx1 ln2 in2 hw6) hx1 hx2
  rw [set_prev_eq _ x2 _, bind_ok]
  have P7 := P6.lnk hO hx2 (k := 16#u64) (by simp) (JV.prev hO hV P6.1.1 hx2 lp1) hx1 hx2
  refine WP.spec_bind (set_nf_spec _ x2 n1 r1 f1) ?_
  rintro s8 ⟨w8, rfl, hw8⟩
  have P8 := P7.lnk hO hx2 (k := 24#u64) (by simp) (JV.nextw hO hV P7.1.1 hx2 ln1 in1 hw8) hx1 hx2
  try simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s9 => SwW st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s9) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 P8
    · rename_i hp0
      have hpO : L.mem s4 (wa x2 16#u64) ∈ OS := lp2.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact P8.lnk hO hpO (k := 24#u64) (by simp)
        (JV.nextw hO hV P8.1.1 hpO (Or.inr hx1) hs1 (link_bits _ _)) hx1 hx2
  intro s9 P9
  split
  · exact (WP.spec_ok _).2 P9
  · rename_i hn0
    have hnO : n2 ∈ OS := ln2.resolve_left (by simpa using hn0)
    rw [set_prev_eq, WP.spec_ok]
    exact P9.lnk hO hnO (k := 16#u64) (by simp) (JV.prev hO hV P9.1.1 hnO (Or.inr hx1)) hx1 hx2

set_option maxHeartbeats 4000000 in
/-- **`cap_swap_for_delete` of two distinct slots of a domain** keeps `JV`, `DomT` and the idle-thread word; every
`OS` slot outside the domain keeps its cap. -/
theorem cdt.cap_swap_for_delete.zt (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS)
    (hDC : DCan D) {s0 s : S} {I : U64} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hD : ∀ y ∈ D, ∀ c, obj.Slot.cap st y s = ok c → ZT Vc D I c)
    {p y : U64} (hp : p ∈ D) (hy : y ∈ D) (hne : p ≠ y) :
    cdt.cap_swap_for_delete st s p y ⦃ s' => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s' ∧
      (∀ y ∈ D, ∀ c, obj.Slot.cap st y s' = ok c → ZT Vc D I c) ∧ OutK st OS D s s' ∧
      L.idleW s' = L.idleW s ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · rename_i he; exfalso; apply hne; simpa using he
  obtain ⟨c1, hc1⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st p s hS)
  obtain ⟨c2, hc2⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st y s hS)
  rw [hc1, bind_ok, hc2, bind_ok]
  have z1 := hD p hp c1 hc1
  have z2 := hD y hy c2 hc2
  refine WP.spec_mono (cdt.swap.jvw hO hV h (hDO hp) (hDO hy) hne (hDC p hp) (hDC y hy) hc1 hc2 (zt_nf z1)
    (zt_nf z2)) ?_
  rintro s' ⟨⟨h', e1, e2, ek⟩, w⟩
  refine ⟨h', fun z hz c hc => ?_, fun z hz hzD => ek z hz (fun e => hzD (e ▸ hp)) (fun e => hzD (e ▸ hy)),
    JV.idle_cw h w⟩
  by_cases e1' : z = p
  · subst e1'; rw [e1] at hc; rw [← okinj hc]; exact z2
  · by_cases e2' : z = y
    · subst e2'; rw [e2] at hc; rw [← okinj hc]; exact z1
    · rw [ek z (hDO hz) e1' e2'] at hc; exact hD z hz c hc

/-! ## The finalisers of the covered kinds keep the idle word -/

set_option maxHeartbeats 2000000 in
/-- **A leaf cap's finalisation keeps the idle-thread word**: `TrivK` writes nothing, the endpoint by
`fin_endpoint.fr` (`CaiFr.idle`), the notification and the reply by QueueIdleKeep. -/
theorem idlL {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64} (hx : x ∈ OS) {c : capability.Cap}
    (hc : obj.Slot.cap st x s = ok c) (hk : ZL c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => L.idleW r.2.1 = L.idleW s ⦄ := by
  rcases hk with ht | he
  · rw [finalise_cap.triv ar s a ht fin]; exact (WP.spec_ok _).2 rfl
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  obtain ⟨Ac', hb⟩ := h.1.parts
  rcases he with ⟨p, b0, b1, b2, b3, b4, rfl⟩ | ⟨n, b0, b1, b2, rfl⟩ | ⟨p, g, rfl⟩
  · have hH : H p = some .ep := hty.1.1.1 p b0 b1 b2 b3 b4 rfl
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_endpoint.fr (ar := ar) s a p b0 b1 b2 b3 b4 fin hb.blk hH) fun r hr =>
      hr.2.2.2.2.1.idle
  · obtain ⟨hn, hH⟩ := hty.1.1.2.1 n b0 b1 b2 rfl
    rw [fin_cap_eq_obj (by simp)]
    exact fin_ntfn.idl (ar := ar) s a n b0 b1 b2 fin hb.blk hn hH
  · have hp : p ∈ Rp := hty.1.1.2.2 p g rfl
    rw [fin_cap_eq_obj (by simp)]
    exact fin_reply.idl hP s a p g fin hb.blk hp h.1.1.2

set_option maxHeartbeats 2000000 in
/-- **The thread finaliser keeps the idle-thread word** (any finality, a bound VCPU or a run in flight
included): the stall and `detach` by `UbF.idle`, the rest by `finThrRest.idl`. -/
theorem fin_thread.idlV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (p : U64) (fin : Bool) (hp : p ∈ T)
    (hid : p ≠ L.idleW s) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r => L.idleW r.2.1 = L.idleW s ⦄ := by
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  cases fin
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · rename_i hf; exact absurd hf (by simp)
    · exact (WP.spec_ok _).2 rfl
  rw [fin_thread_split]
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.ub hA h a p) (smp.remote_tcb_stall.ds hA hO hV hW h a p)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨F1, -, -⟩, D1⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  refine WP.spec_bind (vcpu.detach.ubV hA hO hV F1.cur (hv.keepZ D1.2) a1 p hp) ?_
  rintro ⟨s2, a2⟩ ⟨F2, rv2, D2⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  have F12 := F1.trans F2
  obtain ⟨Ac2, hb2⟩ := F12.cur.bxi
  have hna : L.actionW s2 ≠ p := F12.cur.na p hp
  have hidle : L.idleW s2 ≠ p := by rw [F12.idle]; exact Ne.symm hid
  exact WP.spec_mono (finThrRest.idl hA s2 a2 p hb2.blk hp hna hidle rv2) fun r hr => hr.trans F12.idle

set_option maxHeartbeats 4000000 in
/-- **The finalisation of a `ZT` cap** (gen 34's `finXN` with threads and VCPUs, the idle word kept). -/
theorem finXT {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64} (hx : x ∈ OS)
    {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c) (hX : ZT Vc D (L.idleW s) c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => r.1.2 = .Null ∧
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ OSKeep st OS s r.2.1 ∧ ZRem st D r.1.1 ∧
      L.idleW r.2.1 = L.idleW s ⦄ := by
  rcases hX with hz | ⟨p, rfl, hid, hcov⟩ | ⟨v, rfl, hvV⟩
  · have G : objects.finalise_cap st ar s a c fin false ⦃ r => L.idleW r.2.1 = L.idleW s ⦄ := by
      rcases hz with hl | ⟨p, r, g, b, rfl, -⟩ | ⟨p, t, n, rfl, -⟩
      · exact idlL hP h hx hc hl a fin
      · exact WP.spec_mono (fin_cnode.z ar s a p r g b fin) fun x hr => by rw [hr.1]
      · rw [fin_zombie.z]; exact (WP.spec_ok _).2 rfl
    exact WP.spec_mono (WP.spec_and (finXN hP hO hA hV h hx hc (zn_xk (i := L.idleW s) hz) a fin) G)
      fun r hr => ⟨hr.1.1, hr.1.2.1, hr.1.2.2.1, hr.1.2.2.2, hr.2⟩
  · have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
    have hp : p ∈ T := hty.1.2.2.2.2.2 p rfl
    have G : objects.finalise_cap st ar s a (.Thread p) fin false ⦃ r => L.idleW r.2.1 = L.idleW s ⦄ := by
      rw [fin_cap_eq_obj (by simp)]
      exact fin_thread.idlV hP hO hV h.1.1.1 h.2 a p fin hp hid
    exact WP.spec_mono (WP.spec_and (finXN hP hO hA hV h hx hc (Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩)) a fin) G)
      fun r hr => ⟨hr.1.1, hr.1.2.1, hr.1.2.2.1, hr.1.2.2.2, hr.2⟩
  · have F := finJV_vcpu hP hO hV h hc hvV a _ fin hc
    have G : objects.finalise_cap st ar s a (.Vcpu v) fin false ⦃ r =>
        OSKeep st OS s r.2.1 ∧ L.idleW r.2.1 = L.idleW s ⦄ := by
      rw [fin_cap_eq_obj (by simp)]
      cases fin
      · unfold objects.finalise_cap_object
        dsimp only
        split
        · rename_i hf; exact absurd hf (by simp)
        · exact (WP.spec_ok _).2 ⟨OSKeep.rfl' s, rfl⟩
      · unfold objects.finalise_cap_object
        dsimp only
        split
        · refine WP.spec_bind (vcpu.finalise.ubV hP hO hV h.1.1.1 h.2 a v hvV) ?_
          rintro ⟨s1, a1⟩ ⟨F1, D1⟩
          try simp only [WP.uncurry'_pair, uncurry_apply_pair] at F1 D1 ⊢
          exact (WP.spec_ok _).2 ⟨D1.1, F1.idle⟩
        · rename_i hf; exact absurd rfl hf
    refine WP.spec_mono (WP.spec_and F G) fun r hr => ?_
    rw [hr.1.1]
    exact ⟨rfl, hr.1.2, hr.2.1, Or.inl rfl, hr.2.2⟩

/-! ## The deferred round -/

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_deferred` of a slot of a domain `D` of `ZT` caps**: `JV`, `DomT`, `OutK`, the idle word kept,
a null cleanup — through the swap path and the cyclic exit, at every round. -/
theorem cdt.finalise_slot_deferred.zt {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {y I : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomT st Vc D I s)
    (hI : L.idleW s = I) :
    cdt.finalise_slot_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomT st Vc D I r.2.1 ∧ OutK st OS D s r.2.1 ∧ L.idleW r.2.1 = I ∧
      ∀ v, r.1 = .Ok v → v.cleanup = .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun z => z.2.2.val)
    (inv := fun z => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 z.1 ∧ DomT st Vc D I z.1 ∧
      OutK st OS D s z.1 ∧ L.idleW z.1 = I)
  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, o1, i1⟩
    simp only at h1 d1 o1 i1
    dsimp only
    unfold cdt.finalise_slot_deferred_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, by intro v hv; simp_all⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st y s1 hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1, fun v hv => by cases hv; rfl⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 y c hS) fun fin _ => ?_
    refine WP.spec_bind (finXT hP hO hA hV h1 (hDO hy) hc (by rw [i1]; exact d1 y hy c hc) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨ecl, h2, k2, hrem, j2⟩
    simp only at ecl hrem j2
    subst ecl
    have d2 : DomT st Vc D I s2 := d1.osk hDO k2
    have o2 : OutK st OS D s s2 := o1.trans (OutK.of_osk k2)
    have i2 : L.idleW s2 = I := j2.trans i1
    rcases hrem with rfl | ⟨p, t, n, rfl, hcp, hcov⟩
    · try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h2, d2, o2, i2, fun v hv => by cases hv; rfl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]
         exact ⟨h2, d2, o2, i2, fun v hv => by cases hv; rfl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact ⟨h2, d2, o2, i2⟩)
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_removable.p0 (.Zombie p t n) y)) fun b1 hb1 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h2, d2, o2, i2, fun v hv => by cases hv; rfl⟩
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
    refine WP.spec_bind (WP.spec_and (JV.setz hO hV h2 (hDO hy) hcp ⟨hDO hp0, fun i hi => hDO (hcov i hi)⟩)
      (W7.obj.Slot.set_cap.capw (hO.slot _ (hDO hy)))) ?_
    rintro s3 ⟨⟨h3, k3, c3⟩, w3⟩
    have i3 : L.idleW s3 = I := (JV.idle_cw h2 w3).trans i2
    have d3 : DomT st Vc D I s3 := DomT.upd d2 fun z hz => by
      by_cases e : z = y
      · right; subst e; intro c' hc'; rw [c3] at hc'; rw [← okinj hc']
        exact Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩))
      · left; exact capk4 k3 (hDO hz) e
    have o3 : OutK st OS D s s3 := o2.trans fun z hz hzD => capk4 k3 hz (fun e => hzD (e ▸ hy))
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_cyclic_zombie.p0 (.Zombie p (t) n) y)) fun b2 hb2 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h3, d3, o3, i3, fun v hv => by cases hv; rfl⟩
    rename_i hcy
    have hpy : p ≠ y := by
      intro e
      have hb := hb2.1
      subst e
      simp [cdt.cap_cyclic_zombie] at hb
      simp_all
    try dsimp only
    try simp only []
    refine WP.spec_bind (cdt.cap_swap_for_delete.zt hO hV hDO hDC h3 d3 hp0 hy hpy) ?_
    rintro s4 ⟨h4, d4, o4, j4⟩
    refine WP.spec_bind (sched.preemption_point.jv hP hO hV h4 (by rw [h4.ksb]; exact hW)) ?_
    rintro ⟨rr, s5, a5⟩ ⟨h5, k5, j5⟩
    try simp only [uncurry_apply_pair] at h5 k5 j5 ⊢
    rcases rr with _ | ee
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
      refine (WP.spec_ok _).2 ⟨h5, DomT.osk d4 hDO k5, (o3.trans o4).trans (OutK.of_osk k5),
        j5.trans (j4.trans i3), ?_⟩
      show fuel1.val < fuel.val
      omega
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h5, DomT.osk d4 hDO k5, (o3.trans o4).trans (OutK.of_osk k5),
        j5.trans (j4.trans i3), fun v hv => by cases hv⟩
  · exact ⟨h, hD, OutK.refl s, hI⟩

set_option maxHeartbeats 4000000 in
/-- **`delete_deferred` of a slot of a domain of `ZT` caps**: `JV`, `DomT`, `OutK`, the idle word kept. -/
theorem cdt.delete_deferred.zt {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {y I : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomT st Vc D I s)
    (hI : L.idleW s = I) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomT st Vc D I r.2.1 ∧ OutK st OS D s r.2.1 ∧ L.idleW r.2.1 = I ⦄ := by
  unfold cdt.delete_deferred
  refine WP.spec_bind (cdt.finalise_slot_deferred.zt (a := a) hP hO hA hV hDO hDC hW h hy hD hI) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, d1, o1, i1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 d1 o1 i1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    · rw [hv1 v rfl]
      refine WP.spec_bind (WP.spec_and (WP.spec_and (cdt.empty_slot.jv (a := a1) hO hV h1 (hDO hy))
        (cdt.empty_slot.ck (a := a1) hO h1.1.2 (hDO hy))) (cdt.empty_slot.cw (a := a1) hO h1.1.2 (hDO hy))) ?_
      rintro ⟨s2, a2⟩ ⟨⟨h2, k2, c2⟩, w2⟩
      try simp only [uncurry_apply_pair] at h2 k2 c2 w2 ⊢
      refine (WP.spec_ok _).2 ⟨h2, DomT.upd d1 fun z hz => ?_, fun z hz hzD => ?_, (JV.idle_cw h1 w2).trans i1⟩
      · by_cases e : z = y
        · right; subst e; intro c hc; rw [c2] at hc; rw [← okinj hc]; exact Or.inl (Or.inl zl_null)
        · left; exact k2.cap (hDO hz) e
      · rw [k2.cap hz (fun e => hzD (e ▸ hy))]; exact o1 z hz hzD
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h1, d1, o1, i1⟩

/-! ## The immediate loop -/

set_option hygiene false in
/-- The preemption-point tail of an immediate round (`JV ∧ DomT ∧ XT ∧ idle` at `s5`). -/
local macro "ztailT" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.jv hP hO hV h5 (by rw [h5.ksb]; exact hW)) ?_
  rintro ⟨rr, s6, a6⟩ ⟨h6, k6, i6⟩
  try simp only [uncurry_apply_pair] at h6 k6 i6 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h6, DomT.osk d5 hDO k6, XT.keep hx k6 x5, i6.trans j5, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h6, fun v hv => by cases hv⟩))

set_option maxHeartbeats 4000000 in
/-- **`finalise_slot_immediate` of a slot of `OS` whose cap is `ZT` over a domain `D` of `ZT` caps** (module
docstring): `JV` to `JV`, a null cleanup. -/
theorem cdt.finalise_slot_immediate.zt {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x I : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomT st Vc D I s)
    (hX : XT st Vc D I x s) (hI : L.idleW s = I) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ ∀ v, r.1 = .Ok v → v.cleanup = .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧ DomT st Vc D I y.1 ∧
      XT st Vc D I x y.1 ∧ L.idleW y.1 = I)
  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, x1, j1⟩
    simp only at h1 d1 x1 j1
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
    refine WP.spec_bind (finXT hP hO hA hV h1 hx hc (by rw [j1]; exact x1 c hc) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨ecl, h2, k2, hrem, j2'⟩
    simp only at ecl hrem j2'
    subst ecl
    have d2 : DomT st Vc D I s2 := d1.osk hDO k2
    have j2 : L.idleW s2 = I := j2'.trans j1
    rcases hrem with rfl | ⟨p, t, n, rfl, hcp, hcov⟩
    · try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h2, fun v hv => by cases hv; rfl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]; exact ⟨h2, fun v hv => by cases hv; rfl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact h2)
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
    refine WP.spec_bind (WP.spec_and (JV.setz hO hV h2 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i hi)⟩)
      (W7.obj.Slot.set_cap.capw (hO.slot _ hx))) ?_
    rintro s3 ⟨⟨h3, k3, c3⟩, w3⟩
    have j3 : L.idleW s3 = I := (JV.idle_cw h2 w3).trans j2
    have d3 : DomT st Vc D I s3 := DomT.upd d2 fun z hz => by
      by_cases e : z = x
      · right; subst e; intro c' hc'; rw [c3] at hc'; rw [← okinj hc']
        exact Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩))
      · left; exact capk4 k3 (hDO hz) e
    try dsimp only
    first
      | (refine WP.spec_bind (Pₘ := fun i => i = core.num.U64.wrapping_sub n 1#u64) ((WP.spec_ok _).2 rfl)
          fun i hi => ?_; subst hi)
      | simp only [lift, bind_ok]
    refine WP.spec_bind (slot_index_in p _) fun e he => ?_
    subst he
    have heD : slotIdx p (core.num.U64.wrapping_sub n 1#u64) ∈ D := hcov _ (by rw [wsub1 hn0]; omega)
    refine WP.spec_bind (cdt.delete_deferred.zt (a := a2) hP hO hA hV hDO hDC hW h3 heD d3 j3) ?_
    rintro ⟨r4, s4, a4⟩ ⟨h4, d4, o4, j4⟩
    try simp only [uncurry_apply_pair] at h4 d4 o4 j4 ⊢
    have xo4 : XT st Vc D I x s4 := fun c' hc' => by
      by_cases hxD : x ∈ D
      · exact d4 x hxD c' hc'
      · rw [o4 x hx hxD, c3] at hc'
        rw [← okinj hc']
        exact Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩))
    rcases r4 with _ | ee
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨c4, hc4⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s4 hS)
      rw [hc4, bind_ok]
      try dsimp only
      refine WP.spec_bind (Pₘ := fun y : S × A => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧
        DomT st Vc D I y.1 ∧ XT st Vc D I x y.1 ∧ L.idleW y.1 = I) ?_ ?_
      · split
        all_goals first
          | exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4⟩
          | skip
        split
        · split
          · refine WP.spec_bind (Pₘ := fun s5 => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s5 ∧
              DomT st Vc D I s5 ∧ XT st Vc D I x s5 ∧ L.idleW s5 = I) ?_ fun s5 h5 => (WP.spec_ok _).2 h5
            split
            · try simp only [lift, bind_ok]
              refine WP.spec_mono (WP.spec_and (JV.setz hO hV h4 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i (by
                rw [wsub1 hn0] at hi; omega))⟩) (W7.obj.Slot.set_cap.capw (hO.slot _ hx))) ?_
              rintro s5 ⟨⟨h5, k5, c5⟩, w5⟩
              refine ⟨h5, DomT.upd d4 fun z hz => ?_, fun c' hc' => ?_, (JV.idle_cw h4 w5).trans j4⟩
              · by_cases e : z = x
                · right; subst e; intro c' hc'; rw [c5] at hc'; rw [← okinj hc']
                  exact Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, fun i hi => hcov i (by rw [wsub1 hn0] at hi; omega)⟩))
                · left; exact capk4 k5 (hDO hz) e
              · rw [c5] at hc'; rw [← okinj hc']
                exact Or.inl (Or.inr (Or.inr ⟨p, _, _, rfl, fun i hi => hcov i (by rw [wsub1 hn0] at hi; omega)⟩))
            · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4⟩
          · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4⟩
        · exact (WP.spec_ok _).2 ⟨h4, d4, xo4, j4⟩
      rintro ⟨s5, a5⟩ ⟨h5, d5, x5, j5⟩
      try simp only [uncurry_apply_pair] at h5 d5 x5 j5 ⊢
      try dsimp only
      ztailT
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h4, fun v hv => by cases hv⟩
  · exact ⟨h, hD, hX, hI⟩

/-! ## The exposed deletion -/

set_option maxHeartbeats 4000000 in
/-- **The exposed `cdt.delete` of a slot of `OS` whose cap is `ZT` over a domain of `ZT` caps keeps `JV`**, for a
ghost idle value `I` equal to the idle word of the start state. -/
theorem cdt.delete.ztI {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x I : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomT st Vc D I s)
    (hX : XT st Vc D I x s) (hI : L.idleW s = I) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.zt (a := a) hP hO hA hV hDO hDC hW h hx hD hX hI) ?_
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

/-- **`cdt.delete.ztI` at the start state's idle word.** -/
theorem cdt.delete.zt {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomT st Vc D (L.idleW s) s)
    (hX : XT st Vc D (L.idleW s) x s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.ztI hP hO hA hV hDO hDC hW h hx hD hX rfl

/-- **The thread kind over a domain of `ZT` caps, final or not**: the exposed `cdt.delete` of `Thread p` (`p` not
the idle thread) whose seven TCB slots lie in `D`, the slots of `D` holding leaf, CNode, Zombie, non-idle thread
(with their TCB slots in `D`) and VCPU (`v ∈ Vc`) caps — e.g. a CSpace-root CNode holding the thread's own TCB
cap — keeps `JV`. -/
theorem cdt.delete.threadT {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomT st Vc D (L.idleW s) s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zt hP hO hA hV hDO hDC hW h hx hD fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩)

/-- **The CNode kind over a domain of `ZT` caps, final or not.** -/
theorem cdt.delete.cnodeT {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x p r g b : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomT st Vc D (L.idleW s) s)
    (hc : obj.Slot.cap st x s = ok (.CNode p r g b))
    (hcov : ∀ i : U64, i.val < 2 ^ (r.val % 64) → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zt hP hO hA hV hDO hDC hW h hx hD fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inl (Or.inr (Or.inl ⟨p, r, g, b, rfl, hcov⟩))

/-- **The Zombie kind over a domain of `ZT` caps.** -/
theorem cdt.delete.zombieT {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x p t n : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomT st Vc D (L.idleW s) s)
    (hc : obj.Slot.cap st x s = ok (.Zombie p t n)) (hcov : ∀ i : U64, i.val < n.val → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zt hP hO hA hV hDO hDC hW h hx hD fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inl (Or.inr (Or.inr ⟨p, t, n, rfl, hcov⟩))

/-- Gen 34's `ZN` top as a corollary (a `ZN` domain is a `ZT` domain, for any `Vc`). -/
theorem cdt.delete.zn'' {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomN st D s) (hX : XOK st D x s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zt (Vc := Vc) hP hO hA hV hDO hDC hW h hx hD.toT hX.toT

/-! ## At the decode -/

/-- **The CNode `Delete` of a `ZT` target over a domain of `ZT` caps**, over `JV` (the restart keeps the idle
word, `del_genV`'s frame). -/
theorem syscall.decode_invocation.del_zt {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {Dm : Set U64} (hDO : Dm ⊆ OS)
    (hDC : DCan Dm)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hW : WuApart OS (L.ksb s)) (hD : DomT st Vc Dm (L.idleW s) s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => XT st Vc Dm (L.idleW s) x s) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ :=
  syscall.decode_invocation.del_genV hO hV a len slot cap blk call don fp buf extra D hT hv hf hslot hcap hk
    fun x hx hkx s1 h1 k1 _ i1 =>
      cdt.delete.ztI hP hO hA hV hDO hDC hW h1 hx (hD.osk hDO k1) (hkx.keep hx k1) i1

end zt

/-! ## On the entry fact -/

/-- **The `ZT` loop from the entry fact**: at an `EntAt` decode start, under [J] `SlotTyEntZ`, the restart starts
`JV`, and from every state it reaches the exposed `cdt.delete` of a slot of `OS` whose cap is `ZT` over a canonical
domain `D ⊆ OS` of `ZT` caps (at that state's idle word) keeps `JV`. -/
theorem cdt.delete.zt_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntZ st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
        JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 ∧
        ∀ (a : A) (x : U64) (Dm : Set U64), Dm ⊆ OS → DCan Dm → x ∈ OS → DomT st Vc Dm (L.idleW s1) s1 →
          XT st Vc Dm (L.idleW s1) x s1 →
          cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄ ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, hO, hT, -, -, hsc, hV, hv, hwu⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, WP.spec_mono (JV.restart hO hV D hT hv) fun s1 h1 =>
    ⟨h1.1, fun a x Dm hDO hDC hx hD hX => cdt.delete.zt hP hO hsc hV hDO hDC hwu h1.1 hx hD hX⟩⟩

/-- **The CNode `Delete` over a domain of `ZT` caps on [J] `SlotTyEntZ`**: no apartness hypothesis left. -/
theorem syscall.decode_invocation.del_zt_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntZ st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64) (Dm : Set U64),
        Dm ⊆ OS → DCan Dm → DomT st Vc Dm (L.idleW s) s → capFam cap = .cnode → slot ∈ OS →
        obj.Slot.cap st slot s = ok cap → TgtP st (fun x => XT st Vc Dm (L.idleW s) x s) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
            VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, hO, hT, -, -, hA, hV, hv, hW⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, fun a len slot blk call don fp buf Dm hDO hDC hD hf hs hc hk =>
    syscall.decode_invocation.del_zt hP hO hA hV hDO hDC a len slot cap blk call don fp buf extra D hT hv hW hD hf
      hs hc hk⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1

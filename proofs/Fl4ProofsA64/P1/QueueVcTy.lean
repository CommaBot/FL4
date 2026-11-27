/-
P1 (aarch64, gen 32): **the VCPU typing `VcTy` over a ghost set of VCPU objects, carried in `J`** (handoff §33's
design), and its preservation by the deletions covered so far.

Gen 28–29 refuted every VCPU placement stated over all `Fr0 ∧ BXI` states ([P] `rcw`, `VcPl.vcb` / `rcv`): `Fr0`
lets a TCB's bound-VCPU word (offset 3664, `layout::tcb::VCPU`) or `RUN_VCPU` word (3672) take any value. Here the
facts are a **state invariant over ghost sets**, like `SlotTy`:

* **`VcW Vc b`**: `b` is an aligned word `v + o` (`o < 4096`) of a VCPU object `v ∈ Vc`.
* **`VcOK T Scs Z OS Vc Ub`** (state-free placement): VCPU words lie in no `OS` slot (`os`) and in no SC object
  (`sc`); the ghost user-frame words `Ub` lie in no `OS` slot (`ubos`) and in no VCPU object (`ubv`); every thread's
  IPC-buffer slot (`sbWordA t`, TCB slot 2, `layout::tcb::SLOT_BUFFER`, arch/aarch64/layout.rs:14) is in `OS`
  (`bcov`); the VCPU objects (4 KiB each) do not wrap and are pairwise disjoint (`fit`, `disj`).
* **`VcTy … Vc Ub s`** (at the state):
  * `obj`: every `v ∈ Vc` is a VCPU object (`VcObj`: its words aligned in `Ω \ Sg`, its `TCB` and `RUN_CALLER`
    words `0` or threads);
  * `bnd` / `run`: every thread's bound-VCPU and `RUN_VCPU` words are `0` or in `Vc`;
  * `usr` / `buf`: the words of `Ub` are user words (`UsrW`), and a thread with a run in flight has its run frame
    in `Ub` (`RunBuf Ub`, the shape of P3Place's [P] `vmpl`);
  * `ks`: no VCPU word is a kernel-global word (`ks + o`, `o < 223488`).
* **`JV := J ∧ VcTy`**. Neither `VcOK` nor `VcTy` quantifies over a word class or over a set of states: they are
  facts of the ghost sets `OS`, `Vc`, `Ub` and of the one state.

**Kept by the covered deletions' writes** (`VKeep`: the `ks` base, every VCPU word, every thread's VCPU-link words
and every IPC-buffer slot's cap kept or made `Null`; `VcTy.keep`):
* `empty_slot` (`cdt.empty_slot.vc`): it writes `OS` slot words only (`VKeep.wr_os`): VCPU words are in no `OS` slot
  (`VcOK.os`), a TCB field at offset ≥ 224 is no `OS` word (`capw_ne_hi`), and a buffer slot's cap is kept or
  becomes `Null` (the clear writes `0` to the cap word first, `decode_zero`).
* the endpoint / notification / reply / SC finalisers (`VKeep.of_kwd8`): their QueueFoot8 footprint `K8.FootD`
  (TCB fields from 224 **without 3664 / 3672**, node words, `Sg`, SC words, endpoint words, debug words) misses
  every VCPU word (they are in `Ω \ Sg`, outside the TCBs and nodes, `SchedQueuesInvX.omega`; off the SCs by
  `VcOK.sc`; off the endpoints by `EpsWit`), every VCPU-link word (`field_ne`) and the buffer slots' cap words
  (gen 31's `kw7_not_os`, through `K8.KW.to7`).
* `FinTriv` finalisations change no store word.

**Tops** (`J ∧ VcTy` to `J ∧ VcTy`): `FinJV`, `cdt.finalise_slot_immediate.finJV`, `cdt.delete.finJV`,
`finJV_ep` / `finJV_ntfn` / `finJV_reply` / `finJV_sc`, **`cdt.delete.eprnV`**, **`cdt.delete.scV`**,
**`cdt.delete.fintrivV`** (which covers `TrivK`).

**[J] `SlotTyEntV`** (new, named): [J] `SlotTyEntS` and, for the same `OS`, ghost `Vc`, `Ub` with `VcOK`, `VcTy` at
the entry state and `VcEntApart` (the entry prefix, `EntW`: the caller's `FAULT_IP` register and the current node,
writes no VCPU word and no VCPU-link word). At `P3Ok` states only, over ghost sets, never over a word class.
`SlotTyEntV.toS` (it implies `SlotTyEntS`), `SlotTyEntV.entAt` (carried to every `EntAt` state). Source
(crates/fl4-core/src/arch/aarch64/vcpu.rs): a thread's `VCPU` word is written only by `set_bound` — in
`decode_set_tcb` (377–399) with the object of an invoked `.Vcpu` cap, and in `unbind` (306–316) with `0`; its
`RUN_VCPU` word only by `decode_run` (862, the invoked `.Vcpu` cap's object) and `cancel_run` / `complete_run` /
`unbind` (`0`); a VCPU's `TCB` word by `decode_set_tcb` (a thread cap's TCB), `unbind` / `init` (`0`); its
`RUN_CALLER` word by `decode_run` (861, the current thread) and `cancel_run` / `complete_run` / `unbind` (`0`);
retype zeroes new TCBs and VCPUs; a VCPU's deletion runs `vcpu::finalise` (`unbind`: no thread names it after),
a TCB's deletion `vcpu::detach`. So with `Vc` the live VCPU objects (retyped from untyped memory: no CNode, TCB, SC
or kernel-global word) and `Ub` the words of the live non-device frames, `VcTy` holds on reachable states.

No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueSlotTyDec3
import Fl4ProofsA64.P1.QueueFoot8T
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

local macro "vno" : tactic => `(tactic| first | omega | (simp; omega) | simp_all | (simp at *; omega))

/-! ## The definitions -/

/-- A word of a VCPU object of `Vc`. -/
def VcW (Vc : Set U64) (b : U64) : Prop :=
  ∃ v ∈ Vc, ∃ o : U64, o.val < 4096 ∧ o.val % 8 = 0 ∧ b = wa v o

/-- A word inside a slot of `OS`. -/
def InOS (OS : Set U64) (b : U64) : Prop := ∃ y ∈ OS, y.val ≤ b.val ∧ b.val < y.val + 32

/-- **The ghost VCPU / user-frame sets' placement** (module docstring). -/
structure VcOK (T Scs : Set U64) (Z : U64 → Nat) (OS Vc Ub : Set U64) : Prop where
  os : ∀ b, VcW Vc b → ¬ InOS OS b
  sc : ∀ b, VcW Vc b → ∀ c ∈ Scs, ¬ InSC c (Z c) b
  ubos : ∀ b ∈ Ub, ¬ InOS OS b
  ubv : ∀ b ∈ Ub, ¬ VcW Vc b
  bcov : ∀ t ∈ T, sbWordA t ∈ OS
  fit : ∀ v ∈ Vc, v.val + 4096 ≤ 2 ^ 64
  disj : ∀ v ∈ Vc, ∀ v' ∈ Vc, v ≠ v' → v.val + 4096 ≤ v'.val ∨ v'.val + 4096 ≤ v.val

/-- **The VCPU typing at `s`** (module docstring). -/
structure VcTy (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (Vc Ub : Set U64) (s : S) : Prop where
  obj : ∀ v ∈ Vc, VcObj st T Ω Sg s v
  bnd : ∀ t ∈ T, L.mem s (wa t 3664#u64) = 0#u64 ∨ L.mem s (wa t 3664#u64) ∈ Vc
  run : ∀ t ∈ T, L.mem s (runVcpuA t) = 0#u64 ∨ L.mem s (runVcpuA t) ∈ Vc
  usr : ∀ b ∈ Ub, UsrW st T Cs H Sg Scs Z s b
  buf : ∀ t ∈ T, L.mem s (runVcpuA t) ≠ 0#u64 → RunBuf st Ub s t
  ks : ∀ b, VcW Vc b → ∀ o : U64, o.val < 223488 → wa (L.ksb s) o ≠ b

/-- **The deletion's step relation with the VCPU typing**: `J` and `VcTy`. -/
def JV (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac OS Vc Ub : Set U64) (s0 s : S) : Prop :=
  J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s

/-- A VCPU word is aligned, in `Ω` and off `Sg` (`VcObj`'s `VcWords`). -/
theorem VcTy.w {Vc Ub : Set U64} {s : S} (h : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) {b : U64} (hb : VcW Vc b) :
    Aligned b ∧ b ∈ Ω ∧ b ∉ Sg := by
  obtain ⟨v, hv, o, ho, h8, rfl⟩ := hb
  exact (h.obj v hv).1 o ho h8

/-! ## The frame that keeps `VcTy` -/

/-- **The words `VcTy` reads, kept** (the buffer slot's cap kept or made `Null`). -/
structure VKeep (st : machine.Store S) [L : LawfulStore st] (T Vc : Set U64) (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  vc : ∀ b, VcW Vc b → L.mem s' b = L.mem s b
  bnd : ∀ t ∈ T, L.mem s' (wa t 3664#u64) = L.mem s (wa t 3664#u64)
  run : ∀ t ∈ T, L.mem s' (runVcpuA t) = L.mem s (runVcpuA t)
  cap : ∀ t ∈ T, obj.Slot.cap st (sbWordA t) s' = obj.Slot.cap st (sbWordA t) s ∨
    obj.Slot.cap st (sbWordA t) s' = ok .Null

theorem VKeep.refl {Vc : Set U64} (s : S) : VKeep st T Vc s s :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => Or.inl rfl⟩

theorem VKeep.trans {Vc : Set U64} {s1 s2 s3 : S} (h1 : VKeep st T Vc s1 s2) (h2 : VKeep st T Vc s2 s3) :
    VKeep st T Vc s1 s3 := by
  refine ⟨h2.ksb.trans h1.ksb, fun b hb => (h2.vc b hb).trans (h1.vc b hb),
    fun t ht => (h2.bnd t ht).trans (h1.bnd t ht), fun t ht => (h2.run t ht).trans (h1.run t ht), fun t ht => ?_⟩
  rcases h2.cap t ht with e2 | e2
  · rw [e2]; exact h1.cap t ht
  · exact Or.inr e2

theorem vcw_of {Vc : Set U64} {v o : U64} (hv : v ∈ Vc) (ho : o.val < 4096) (h8 : o.val % 8 = 0) :
    VcW Vc (wa v o) := ⟨v, hv, o, ho, h8, rfl⟩

/-- **`VcTy` along a `VKeep` step.** -/
theorem VcTy.keep {Vc Ub : Set U64} {s s' : S} (h : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (k : VKeep st T Vc s s') :
    VcTy st T Cs Ω H Sg Scs Z Vc Ub s' := by
  refine ⟨fun v hv => ?_, fun t ht => ?_, fun t ht => ?_, fun b hb => (h.usr b hb).ksb k.ksb, fun t ht hne => ?_,
    fun b hb o ho => by rw [k.ksb]; exact h.ks b hb o ho⟩
  · have o := h.obj v hv
    unfold VcObj at o ⊢
    rw [k.vc _ (vcw_of (o := vcpu.TCB) hv (by simp [vcpu.TCB]) (by simp [vcpu.TCB])),
      k.vc _ (vcw_of (o := vcpu.RUN_CALLER) hv (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER]))]
    exact o
  · rw [k.bnd t ht]; exact h.bnd t ht
  · rw [k.run t ht]; exact h.run t ht
  · have hne0 : L.mem s (runVcpuA t) ≠ 0#u64 := by rwa [k.run t ht] at hne
    have hvc : L.mem s (runVcpuA t) ∈ Vc := (h.run t ht).resolve_left hne0
    rcases k.cap t ht with hc | hc
    · exact RunBuf.of_eq (h.buf t ht hne0) hc (k.run t ht)
        (k.vc _ (vcw_of (o := vcpu.RUN_OFFSET) hvc (by simp [vcpu.RUN_OFFSET]) (by simp [vcpu.RUN_OFFSET])))
    · intro ptr size rights dev x1 x2 x3 x4 bits sz e1
      rw [hc] at e1
      cases okinj e1

/-! ## `empty_slot` keeps `VcTy` -/

section os
variable {OS Vc Ub : Set U64}

/-- Two words of `OS` slots at offsets below 32 differ unless they are the same offset of the same slot. -/
theorem os_ne (hO : OSOK T Ω Sg OS) {p y k k' : U64} (hp : p ∈ OS) (hy : y ∈ OS) (hk : k.val < 32)
    (hk' : k'.val < 32) (hne : p = y → k.val ≠ k'.val) : (wa p k).val ≠ (wa y k').val := by
  rw [wv (hO.fit p hp) hk, wv (hO.fit y hy) hk']
  by_cases e : p = y
  · subst e; have := hne rfl; omega
  · have := hO.disj p hp y hy e; omega

/-- **One write of a word of an `OS` slot keeps the `VcTy` words** (a write of the cap word only with `0`, of the
second cap word only when the first is `0`: then the slot's cap is `Null`). -/
theorem VKeep.wr_os {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 : S}
    (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (q : SchedQueuesInvX st T Cs Ω H X s0 Q R)
    (hal : ∀ b, VcW Vc b → Aligned b) {s : S} {p k v : U64} (hp : p ∈ OS) (hk : k.val < 32)
    (h8 : k.val % 8 = 0) (h0 : k.val = 0 → v = 0#u64) (h8' : k.val = 8 → L.mem s p = 0#u64) :
    VKeep st T Vc s (L.wr s (wa p k) v) := by
  have ha := hO.al hp hk h8
  have hin : InOS OS (wa p k) := ⟨p, hp, by rw [wv (hO.fit p hp) hk]; omega, by rw [wv (hO.fit p hp) hk]; omega⟩
  have hcw := hO.cw hp hk h8
  have tf : ∀ t ∈ T, ∀ K : U64, 224 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (wa p k) v) (wa t K) = L.mem s (wa t K) := fun t ht K k1 k2 k3 =>
    L.mem_wr_ne ha (field_aligned (q.tcbs t ht) k2 k3)
      (fun e => capw_ne_hi q hcw ht k1 k2 (UScalar.eq_of_val_eq e))
  refine ⟨L.ksb_wr _ _ _, fun b hb => L.mem_wr_ne ha (hal b hb) (fun e => hV.os b hb ?_),
    fun t ht => tf t ht _ (by simp) (by simp) (by simp), fun t ht => tf t ht 3672#u64 (by simp) (by simp) (by simp),
    fun t ht => ?_⟩
  · have e' : wa p k = b := UScalar.eq_of_val_eq e
    rw [← e']; exact hin
  · have hy := hV.bcov t ht
    have m : ∀ k' : U64, k'.val < 32 → k'.val % 8 = 0 → (p = sbWordA t → k.val ≠ k'.val) →
        L.mem (L.wr s (wa p k) v) (wa (sbWordA t) k') = L.mem s (wa (sbWordA t) k') := fun k' a1 a2 a3 =>
      L.mem_wr_ne ha (hO.al hy a1 a2) (os_ne hO hp hy hk a1 a3)
    have m0 := m 0#u64 (by simp) (by simp)
    have m8 := m 8#u64 (by simp) (by simp)
    rw [SFF.wadd0'] at m0
    by_cases ep : p = sbWordA t
    · by_cases k0 : k.val = 0
      · right
        have ek : wa p k = sbWordA t := by
          apply UScalar.eq_of_val_eq; rw [wv (hO.fit p hp) hk, ep]; simp [k0]
        rw [DPF.slot_cap_dec, ek, L.mem_wr_same (hO.al0 hy), h0 k0, decode_zero]
      by_cases k8 : k.val = 8
      · right
        rw [DPF.slot_cap_dec, m0 (fun _ => by vno)]
        rw [← ep, h8' k8, decode_zero]
      · left
        rw [DPF.slot_cap_dec, DPF.slot_cap_dec, m0 (fun _ => by vno), m8 (fun _ => by vno)]
    · left
      rw [DPF.slot_cap_dec, DPF.slot_cap_dec, m0 (fun e => absurd e ep), m8 (fun e => absurd e ep)]

set_option maxHeartbeats 2000000 in
/-- **`empty_slot` of a slot of `OS`, null cleanup, keeps `VcTy`** (`SlotTy` at the start: the neighbours are
slots of `OS`). -/
theorem cdt.empty_slot.vc {A : Type _} {ar : machine.Arch A} {X : Set U64} {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s : S} {a : A} {x : U64}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hx : x ∈ OS) :
    cdt.empty_slot st ar s a x .Null ⦃ r => VcTy st T Cs Ω H Sg Scs Z Vc Ub r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hal : ∀ b, VcW Vc b → Aligned b := fun b hb => (hv.w hb).1
  have W := fun {s1 : S} {p k v : U64} (hp : p ∈ OS) (hk : k.val < 32) (h8 : k.val % 8 = 0)
    (h0 : k.val = 0 → v = 0#u64) (h8' : k.val = 8 → L.mem s1 p = 0#u64) =>
    VKeep.wr_os (s := s1) (v := v) hO hV q hal hp hk h8 h0 h8'
  refine WP.spec_mono (?_ : cdt.empty_slot st ar s a x .Null ⦃ r => VKeep st T Vc s r.1 ⦄) fun r hr => hv.keep hr
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 (VKeep.refl s)
  have hxo := hT x hx
  obtain ⟨nx, hnx⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s (wa x 24#u64)))
  have hnl : LinkOK OS nx := hxo.2.2 nx hnx
  have hpv : LinkOK OS (L.mem s (wa x 16#u64)) := hxo.2.1
  rw [slot_prev_eq, bind_ok, slot_next_of hnx, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => VKeep st T Vc s s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 (VKeep.refl s)
    · rename_i hp0
      have hpO : L.mem s (wa x 16#u64) ∈ OS := hpv.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact W hpO (k := 24#u64) (by simp) (by simp) (by simp) (by simp)
  refine WP.spec_bind (Pₘ := fun s2 => VKeep st T Vc s s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnO : nx ∈ OS := hnl.resolve_left (by simpa using hn0)
      rw [set_prev_eq, bind_ok]
      have h3 := h1.trans (W (s1 := s1) (v := L.mem s (wa x 16#u64)) hnO (k := 16#u64) (by simp) (by simp)
        (by simp) (by simp))
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx _ hS) fun nfb _ => ?_
      split
      · rw [set_fb_eq_t, WP.spec_ok]; exact h3.trans (W hnO (k := 24#u64) (by simp) (by simp) (by simp) (by simp))
      · cases fb
        · rw [set_fb_eq_f, WP.spec_ok]; exact h3.trans (W hnO (k := 24#u64) (by simp) (by simp) (by simp) (by simp))
        · rw [set_fb_eq_t, WP.spec_ok]; exact h3.trans (W hnO (k := 24#u64) (by simp) (by simp) (by simp) (by simp))
  rw [clear_eq, bind_ok, pcd_null, WP.spec_ok]
  have a0 := hO.al0 hx
  have k0 := W (s1 := s2) (v := 0#u64) hx (k := 0#u64) (by simp) (by simp) (fun _ => rfl) (by simp)
  rw [SFF.wadd0'] at k0
  have k8 := W (s1 := L.wr s2 x 0#u64) (v := 0#u64) hx (k := 8#u64) (by simp) (by simp) (by simp)
    (fun _ => L.mem_wr_same a0)
  have k16 := W (s1 := L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (v := 0#u64) hx (k := 16#u64) (by simp)
    (by simp) (by simp) (by simp)
  have k24 := W (s1 := L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (v := 0#u64) hx
    (k := 24#u64) (by simp) (by simp) (by simp) (by simp)
  exact h2.trans (k0.trans (k8.trans (k16.trans k24)))

end os

/-! ## The `K8` footprints keep `VcTy` -/

/-- A `K8.KW` word is a `K7.KW` word (the `K8` TCB clause is the `K7` one with two more offsets excluded). -/
theorem K8.KW.to7 {Es : Set U64} {s : S} {b : U64} (h : K8.KW st T Cs Sg Scs Z Es s b) :
    K7.KW st T Cs Sg Scs Z Es s b := by
  rcases h with ⟨y, hy, K, k1, k2, k3, k4, e⟩ | h | h
  · exact Or.inl ⟨y, hy, K, k1, k2, k3, k4.1, e⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **A VCPU word is no `K8.KW` word and no debug-list word.** -/
theorem vcw_not_kw8 {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {Vc Es : Set U64} {s : S}
    {OS Ub : Set U64} (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hV : VcOK T Scs Z OS Vc Ub)
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) {b : U64} (hvw : b ∈ Ω ∧ b ∉ Sg) (hb : VcW Vc b) :
    ¬ K8.KW st T Cs Sg Scs Z Es s b ∧ ¬ DbgW st T Cs s b := by
  have ho := q.omega _ hvw.1
  refine ⟨?_, ?_⟩
  · rintro (⟨y, hy, K, k1, k2, -, -, e⟩ | ⟨c, hc, o, ho', -, e⟩ | hm | ⟨c, hc, hin⟩ | ⟨e', he', hb'⟩)
    · exact out_ne_field ho hy (q.tcbs y hy) k2 (by rw [e])
    · exact out_ne_node ho hc (q.nodes c hc) ho' (by rw [e])
    · exact hvw.2 hm
    · exact hV.sc b hb c hc hin
    · obtain ⟨E, EQ, w1, -, wΩ, -, -, ty⟩ := q.eps
      have heE : e' ∈ E := (ty.2.2.1 e').2 (hE e' he')
      obtain ⟨hE', -, -⟩ := w1 e' heE
      have := wΩ e' heE b hvw.1
      rcases hb' with rfl | rfl
      · rw [epHeadA_val] at this; omega
      · rw [epTSA_val hE'] at this; omega
  · rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
    · exact out_ne_field ho hy (q.tcbs y hy) (K := 3576#u64) (by simp) (by rw [e]; try rfl)
    · exact out_ne_field ho hy (q.tcbs y hy) (K := 3584#u64) (by simp) (by rw [e]; try rfl)
    · exact out_ne_node ho hc (q.nodes c hc) (by rw [debug_val]; omega) (by rw [e])

/-- **A thread's VCPU-link word (3664 or 3672) is no `K8.KW` word and no debug-list word.** -/
theorem lnk_not_kw8 {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {Es : Set U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hob : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) {t K' : U64} (ht : t ∈ T)
    (hK : K'.val = 3664 ∨ K'.val = 3672) :
    ¬ K8.KW st T Cs Sg Scs Z Es s (wa t K') ∧ ¬ DbgW st T Cs s (wa t K') := by
  have hta := q.tcbs t ht
  have hK1 : K'.val < 4096 := by omega
  have hal : Aligned (wa t K') := field_aligned hta hK1 (by omega)
  have fo : ∀ a, OutsideObjs st T Cs s a → wa t K' ≠ a := fun a ha e =>
    out_ne_field ha ht hta hK1 (by rw [e])
  refine ⟨?_, ?_⟩
  · rintro (⟨y, hy, K, k1, k2, -, k4, e⟩ | ⟨c, hc, o, ho', -, e⟩ | hm | ⟨c, hc, hin⟩ | ⟨e', he', hb'⟩)
    · obtain ⟨-, k5, k6⟩ := k4
      exact field_ne hta (q.tcbs y hy) hK1 k2 (fun _ => by rcases hK with hK | hK <;> omega) e
    · exact node_ne_field (q.nodes c hc) ho' ht hta hK1 e.symm
    · exact fo _ (q.omega _ (hsub _ hm)) rfl
    · exact fo _ (q.omega _ (hob.scW c hc _ hal hin)) rfl
    · obtain ⟨E, EQ, w1, -, -, -, -, ty⟩ := q.eps
      have heE : e' ∈ E := (ty.2.2.1 e').2 (hE e' he')
      obtain ⟨hE', hEN, -⟩ := w1 e' heE
      obtain ⟨o1, o2⟩ := ep_out hE' hEN
      rcases hb' with e | e
      · exact fo _ o1 e
      · exact fo _ o2 e
  · rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
    · exact field_ne hta (q.tcbs y hy) hK1 (K2 := 3576#u64) (by simp)
        (fun _ => by rcases hK with hK | hK <;> simp [hK]) e
    · exact field_ne hta (q.tcbs y hy) hK1 (K2 := 3584#u64) (by simp)
        (fun _ => by rcases hK with hK | hK <;> simp [hK]) e
    · exact node_ne_field (q.nodes c hc) (by rw [debug_val]; omega) ht hta hK1 e.symm

/-- **A `K8.FootD` footprint keeps the `VcTy` words** (`ScApart` for the buffer slots' cap words, through
`kw7_not_os`). -/
theorem VKeep.of_kwd8 {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {OS Vc Ub Es : Set U64}
    {s s' : S} (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (hA : ScApart Scs Z OS)
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hob : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (f : K8.FootD st T Cs Sg Scs Z Es s s') : VKeep st T Vc s s' := by
  have lk : ∀ t ∈ T, ∀ K' : U64, (K'.val = 3664 ∨ K'.val = 3672) → L.mem s' (wa t K') = L.mem s (wa t K') :=
    fun t ht K' hK => by
      have hn := lnk_not_kw8 (Es := Es) q hob hsub hE ht hK
      exact WritesIn.mem_eq f (field_aligned (q.tcbs t ht) (by omega) (by omega)) fun hF => hF.elim hn.1 hn.2
  have cw : ∀ y ∈ OS, ∀ b, W7.CapW T Ω Sg b → y.val ≤ b.val → b.val < y.val + 32 → Aligned b →
      L.mem s' b = L.mem s b := fun y hy b hb h1 h2 hal =>
    WritesIn.mem_eq f hal fun hF => hF.elim (fun hk => kw7_not_os q hsub hA hE hy hb h1 h2 (K8.KW.to7 hk))
      (dbg_not_capw q hb)
  refine ⟨f.1, fun b hb => ?_, fun t ht => lk t ht _ (Or.inl (by simp)),
    fun t ht => lk t ht 3672#u64 (Or.inr (by simp)), fun t ht => Or.inl ?_⟩
  · obtain ⟨hal, hΩ, hS⟩ := hv.w hb
    have hn := vcw_not_kw8 (Es := Es) q hV hE ⟨hΩ, hS⟩ hb
    exact WritesIn.mem_eq f hal fun hF => hF.elim hn.1 hn.2
  · have hy := hV.bcov t ht
    obtain ⟨v8, -, -⟩ := vals hO hy
    rw [DPF.slot_cap_dec, DPF.slot_cap_dec, cw _ hy _ (hO.cw0 hy) (by omega) (by omega) (hO.al0 hy),
      cw _ hy _ (hO.cw hy (k := 8#u64) (by simp) (by simp)) (by omega) (by omega)
        (hO.al hy (k := 8#u64) (by simp) (by simp))]

/-! ## The deletion over `JV` -/

/-- **The finalisation of the cap in slot `x`, for every finality, ends in `JV` with `(Null, Null)`.** -/
def FinJV (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac OS Vc Ub : Set U64) (s0 s : S) (x : U64) : Prop :=
  ∀ (a : A) (c : capability.Cap) (fin : Bool), obj.Slot.cap st x s = ok c →
    objects.finalise_cap st ar s a c fin false ⦃ r =>
      r.1 = (.Null, .Null) ∧ JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄

/-- `empty_slot` of a slot of `OS`, null cleanup, keeps `JV`. -/
theorem cdt.empty_slot.jv {A : Type _} {ar : machine.Arch A} {OS Vc Ub : Set U64} (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) :
    cdt.empty_slot st ar s a x .Null ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.1 ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  exact WP.spec_and (cdt.empty_slot.ty hO h.1 hx)
    (cdt.empty_slot.vc hO hV hb.1.choose_spec.choose_spec h.1.2 h.2 hx)

set_option maxHeartbeats 4000000 in
/-- `finalise_slot_immediate` of a slot whose cap's finalisation is `FinJV`: `JV`, a null cleanup. -/
theorem cdt.finalise_slot_immediate.finJV {A : Type _} {ar : machine.Arch A} {OS Vc Ub : Set U64} {s0 s : S}
    {a : A} {x : U64} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hk : FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ ∀ v, r.1 = .Ok v → v.cleanup = .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val) (inv := fun y => y.1 = s)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    have hJ1 : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s1 := h1 ▸ h
    have hk1 : FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s1 x := h1 ▸ hk
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
/-- **The exposed `cdt.delete` of a slot of `OS` whose cap's finalisation is `FinJV` keeps `JV`.** -/
theorem cdt.delete.finJV {A : Type _} {ar : machine.Arch A} {OS Vc Ub : Set U64} (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS)
    (hk : FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.finJV (a := a) h hk) ?_
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

/-! ## The kinds over `JV` -/

/-- A `K8.FootD` finaliser keeps `VcTy` from a `J` state (its invariants, `Sg ⊆ Ω`). -/
theorem VcTy.of_fin8 {OS Vc Ub Es : Set U64} {s0 s s' : S} (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub)
    (hA : ScApart Scs Z OS) (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) (f : K8.FootD st T Cs Sg Scs Z Es s s') :
    VcTy st T Cs Ω H Sg Scs Z Vc Ub s' := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  obtain ⟨-, -, hX, -, hSg⟩ := hb.blk
  exact h.2.keep (VKeep.of_kwd8 hO hV hA hb.1.choose_spec.choose_spec hX.1 hSg.sub hE h.2 f)

set_option maxHeartbeats 2000000 in
/-- **The endpoint kind, any finality, over `JV`.** -/
theorem finJV_ep {A : Type _} {ar : machine.Arch A} {OS Vc Ub : Set U64} (hO : OSOK T Ω Sg OS)
    (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS)
    (hk : ∀ c, obj.Slot.cap st x s = ok c → ∃ p b0 b1 b2 b3 b4, c = .Endpoint p b0 b1 b2 b3 b4) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c fin hc
  have J1 := finJ_ep (ar := ar) hO hA h.1 hx hk a c fin hc
  obtain ⟨p, b0, b1, b2, b3, b4, rfl⟩ := hk c hc
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  have hH : H p = some .ep := hty.1.1.1 p b0 b1 b2 b3 b4 rfl
  obtain ⟨Ac', hb⟩ := h.1.parts
  have F : objects.finalise_cap st ar s a (.Endpoint p b0 b1 b2 b3 b4) fin false ⦃ r =>
      K8.FootD st T Cs Sg Scs Z {p} s r.2.1 ⦄ := by
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (K8.fin_endpoint.blk (ar := ar) s a p b0 b1 b2 b3 b4 fin hb.blk hH) fun r hr =>
      K8.Foot.d hr.2.2.2
  exact WP.spec_mono (WP.spec_and J1 F) fun r hr => ⟨hr.1.1, And.intro hr.1.2 (VcTy.of_fin8 hO hV hA h
    (fun e he => by rw [Set.mem_singleton_iff.1 he]; exact Or.inl hH) hr.2)⟩

set_option maxHeartbeats 2000000 in
/-- **The notification kind, any finality, over `JV`.** -/
theorem finJV_ntfn {A : Type _} {ar : machine.Arch A} {OS Vc Ub : Set U64} (hO : OSOK T Ω Sg OS)
    (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS)
    (hk : ∀ c, obj.Slot.cap st x s = ok c → ∃ n b0 b1 b2, c = .Notification n b0 b1 b2) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c fin hc
  have J1 := finJ_ntfn (ar := ar) hO hA h.1 hx hk a c fin hc
  obtain ⟨n, b0, b1, b2, rfl⟩ := hk c hc
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  obtain ⟨hn, hH⟩ := hty.1.1.2.1 n b0 b1 b2 rfl
  obtain ⟨Ac', hb⟩ := h.1.parts
  have F : objects.finalise_cap st ar s a (.Notification n b0 b1 b2) fin false ⦃ r =>
      K8.FootD st T Cs Sg Scs Z {n} s r.2.1 ⦄ := by
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (K8.fin_ntfn.blk (ar := ar) s a n b0 b1 b2 fin hb.blk hn hH) fun r hr =>
      K8.Foot.d hr.2.2.2
  exact WP.spec_mono (WP.spec_and J1 F) fun r hr => ⟨hr.1.1, And.intro hr.1.2 (VcTy.of_fin8 hO hV hA h
    (fun e he => by rw [Set.mem_singleton_iff.1 he]; exact Or.inr hH) hr.2)⟩

set_option maxHeartbeats 2000000 in
/-- **The reply kind, any finality, over `JV`.** -/
theorem finJV_reply {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) {OS Vc Ub : Set U64}
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS)
    (hk : ∀ c, obj.Slot.cap st x s = ok c → ∃ p g, c = .Reply p g) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c fin hc
  have J1 := finJ_reply (ar := ar) hP hO hA h.1 hx hk a c fin hc
  obtain ⟨p, g, rfl⟩ := hk c hc
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  have hp : p ∈ Rp := hty.1.1.2.2 p g rfl
  obtain ⟨Ac', hb⟩ := h.1.parts
  have F : objects.finalise_cap st ar s a (.Reply p g) fin false ⦃ r =>
      K8.FootD st T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (K8.fin_reply.blk (ar := ar) hP s a p g fin hb.blk hp h.1.1.2) fun r hr => hr.2.2
  exact WP.spec_mono (WP.spec_and J1 F) fun r hr => ⟨hr.1.1, And.intro hr.1.2 (VcTy.of_fin8 hO hV hA h
    (fun e he => he) hr.2)⟩

set_option maxHeartbeats 2000000 in
/-- **The SchedContext kind, any finality, over `JV`** (P3's placement of the SC cap, `ScPlAt`). -/
theorem finJV_sc {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) {OS Vc Ub : Set U64}
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hk : ScPlAt st Scs x s) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c fin hc
  have J1 := finJ_sc (ar := ar) hP hO hA h.1 hk a c fin hc
  obtain ⟨⟨p, b, rfl⟩, hpl⟩ := hk c hc
  obtain ⟨hpS, hp0, hid⟩ := hpl.2 p b rfl
  obtain ⟨Ac', hb⟩ := h.1.parts
  have hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p) := fun h0 =>
    h.1.1.1.na _ (hb.2.2.1.2.2.yt.1 p hpS h0)
  have F : objects.finalise_cap st ar s a (.SchedContext p b) fin false ⦃ r =>
      K8.FootD st T Cs Sg Scs Z ∅ s r.2.1 ⦄ := by
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (K8.fin_sc.blk (ar := ar) hP s a p b fin hb.blk hpS hp0 hna hid) fun r hr => by
      obtain ⟨_, _, _, f⟩ := hr
      exact K8.Foot.d f
  exact WP.spec_mono (WP.spec_and J1 F) fun r hr => ⟨hr.1.1, And.intro hr.1.2 (VcTy.of_fin8 hO hV hA h
    (fun e he => absurd he (Set.notMem_empty e)) hr.2)⟩

/-- **The exposed `cdt.delete` of an endpoint, notification or reply slot of `OS` keeps `JV`** (any finality),
under `ScApart` and `VcOK`. -/
theorem cdt.delete.eprnV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) {OS Vc Ub : Set U64}
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hk : EpNtRpAt st x s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ := by
  refine cdt.delete.finJV hO hV h hx fun a c fin hc => ?_
  rcases hk c hc with he | hn | hr
  · exact finJV_ep hO hA hV h hx (fun c' hc' => by rw [hc] at hc'; rw [← okinj hc']; exact he) a c fin hc
  · exact finJV_ntfn hO hA hV h hx (fun c' hc' => by rw [hc] at hc'; rw [← okinj hc']; exact hn) a c fin hc
  · exact finJV_reply hP hO hA hV h hx (fun c' hc' => by rw [hc] at hc'; rw [← okinj hc']; exact hr) a c fin hc

/-- **The exposed `cdt.delete` of an SC slot of `OS` keeps `JV`** (any finality), under `ScApart`, `VcOK` and
P3's placement of the SC cap. -/
theorem cdt.delete.scV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) {OS Vc Ub : Set U64}
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hk : ScPlAt st Scs x s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.finJV hO hV h hx (finJV_sc hP hO hA hV h hk)

set_option maxHeartbeats 2000000 in
/-- **The exposed `cdt.delete` of a `FinTriv` slot of `OS` keeps `JV`** (the finalisation changes no store word,
then `empty_slot`). Covers the `TrivK` kinds (`CapFinTrivAt.of_triv`). -/
theorem cdt.delete.fintrivV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) {OS Vc Ub : Set U64}
    (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hk : CapFinTrivAt st x s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ := by
  refine WP.spec_and (cdt.delete.fintriv hP hO h.1 hx hk) ?_
  obtain ⟨Ac', hb⟩ := h.1.parts
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.fintriv (ar := ar) (a := a) hP hk) ?_
  rintro ⟨r, s1, a1⟩ ⟨e1, hv1⟩
  try simp only [uncurry_apply_pair] at e1 hv1 ⊢
  subst e1
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [hv1 v rfl]
    refine WP.spec_bind (cdt.empty_slot.vc hO hV hb.1.choose_spec.choose_spec h.1.2 h.2 hx) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h.2

/-! ## The entry fact -/

/-- The entry prefix (`EntW e`) writes no VCPU word and no thread's VCPU-link word. -/
def VcEntApart (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (e : S) (Vc : Set U64) : Prop :=
  ∀ b, EntW st e b → ¬ VcW Vc b ∧ ∀ t ∈ T, b ≠ wa t 3664#u64 ∧ b ≠ runVcpuA t

/-- **[J] (a64) `SlotTyEntV`**: [J] `SlotTyEntS` and, for the same `OS`, ghost VCPU / user-frame sets `Vc`, `Ub`
with `VcOK`, `VcTy` at the entry state and `VcEntApart` (module docstring for the source). At `P3Ok` states only,
over ghost sets, not over a word class. -/
def SlotTyEntV (st : machine.Store S) [L : LawfulStore st] (T Cs Ω Sg : Set U64) (H : Heap) (Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ e, P3Ok e → ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS e ∧ EntApart st e OS ∧
    (∀ t ∈ T, t ∈ OS) ∧ IrqStApart OS (L.ksb e) ∧ ScApart Scs Z OS ∧ VcOK T Scs Z OS Vc Ub ∧
    VcTy st T Cs Ω H Sg Scs Z Vc Ub e ∧ VcEntApart st T e Vc

/-- `SlotTyEntV` implies `SlotTyEntS` (fields dropped). -/
theorem SlotTyEntV.toS (h : SlotTyEntV st T Cs Ω Sg H Rp Scs Nt Z P3Ok) : SlotTyEntS st T Ω Sg H Rp Scs Nt Z P3Ok :=
  fun e he => by obtain ⟨OS, _, _, a, b, c, d, f, g, _, _, _⟩ := h e he; exact ⟨OS, a, b, c, d, f, g⟩

/-- **`SlotTyEntV` at every `EntAt` state** (the TCBs placed, as at every `BXI` state). -/
theorem SlotTyEntV.entAt (hJ : SlotTyEntV st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s)
    (hTP : TcbPlaced T) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ (∀ t ∈ T, t ∈ OS) ∧ IrqStApart OS (L.ksb s) ∧
      ScApart Scs Z OS ∧ VcOK T Scs Z OS Vc Ub ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s := by
  obtain ⟨e, he, hw⟩ := hE
  obtain ⟨OS'', Vc', Ub', hO', hT', hA', hc', hap', hsc', hV', hv', hVA'⟩ := hJ e he
  refine ⟨OS'', Vc', Ub', hO', fun y hy => ?_, hc', by rw [hw.1]; exact hap', hsc', hV', hv'.keep ?_⟩
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

end ST
end R
end W7

end

end Fl4ProofsA64.P1

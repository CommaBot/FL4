/-
P1 (aarch64, gen 33): **the Zombie cap's encoding round trip and the slot steps of the Zombie loop over `JV`**,
the base layer of QueueZombieV.

* `Canon p` (a value `unpack_ptr` returns), `unpack_eq_sx` (`unpack_ptr` is `sext48`), `Canon.unpack`;
* `zw p t` (the first word `Cap::encode` gives `Zombie p t n`, capability.rs:236), `encode_zombie`,
  **`decode_zw`**: `Cap::decode (zw p t) n = Zombie p (t & 0xff) n` for a canonical `p` (capability.rs:184);
* `decode_canon`: every pointer `Cap::decode` returns in a `Thread` / `CNode` / `Zombie` cap is canonical;
* **`JV.setz`**: `set_cap` of a Zombie cap whose covered slots lie in `OS` into a slot of `OS` keeps `JV`, keeps
  every other `OS` slot's words, and the slot then reads `Zombie p (t & 0xff) n` (a Zombie cap is no frame cap, so
  the IPC-buffer run frames `VcTy.buf` reads stay vacuous or kept: `VcTy.of_capw`);
* **`cdt.empty_slot.ck`**: `empty_slot` of a slot `x` of `OS` writes no cap word of another `OS` slot, and `x` then
  reads `Null`.

No named premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueVcTyEnt
import Mathlib.Tactic.IntervalCases
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

/-! ## Canonical pointers -/

/-- A canonical pointer: a value `unpack_ptr` returns (capability.rs:86–93). -/
def Canon (p : U64) : Prop := ∃ w, capability.unpack_ptr w = ok p

/-- `unpack_ptr` is `obj::sext48` (the same 48-bit sign extension). -/
theorem unpack_eq_sx (w : U64) : capability.unpack_ptr w = obj.sext48 w := by
  unfold capability.unpack_ptr obj.sext48 capability.PTR_MASK obj.MDB_PTR_MASK
  rfl

theorem Canon.sx {p : U64} (hp : Canon p) : obj.sext48 p = ok p := by
  obtain ⟨w, hw⟩ := hp
  rw [unpack_eq_sx] at hw
  exact sx_idem _ _ hw

/-- A word with a canonical pointer's 48 low bits unpacks to that pointer. -/
theorem Canon.unpack {p w : U64} (hp : Canon p) (hw : w &&& obj.MDB_PTR_MASK = p &&& obj.MDB_PTR_MASK) :
    capability.unpack_ptr w = ok p := by
  rw [unpack_eq_sx, ← sx_mask, hw, sx_mask, hp.sx]

/-! ## The Zombie encoding -/

/-- The first word of `Cap::encode (Zombie p t n)` (capability.rs:236). -/
def zw (p t : U64) : U64 :=
  ((⟨(9#u64).bv <<< (59#i32).toNat⟩ : U64) ||| (p &&& capability.PTR_MASK)) |||
    (⟨(t &&& 255#u64).bv <<< (48#i32).toNat⟩ : U64)

theorem encode_zombie (p t n : U64) : capability.Cap.encode (.Zombie p t n) = ok (zw p t, n) := by
  unfold zw
  simp only [capability.Cap.encode, capability.tag, capability.pack_ptr, lift, bind_ok,
    SFF.shl_eq _ 59#i32 (by decide) (by decide), SFF.shl_eq _ 48#i32 (by decide) (by decide)]
  all_goals rfl

theorem i59 : (59#i32).toNat = 59 := by first | rfl | decide
theorem i48 : (48#i32).toNat = 48 := by first | rfl | decide
theorem bvM : (281474976710655#u64).bv = 0xffffffffffff#64 := by first | rfl | decide
theorem bv9 : (9#u64).bv = 9#64 := by first | rfl | decide
theorem bv255 : (255#u64).bv = 255#64 := by first | rfl | decide

/-- An equation of 64-bit words, bit by bit (Fl4Proofs.P3.Encode's `bvext`). -/
local macro "zbv" : tactic => `(tactic| (
  apply BitVec.eq_of_getElem_eq; intro i hi
  have hi' : i < 64 := by simpa using hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
  interval_cases i <;> simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_eq_getElem, BitVec.getLsbD_of_ge]))

set_option maxHeartbeats 4000000 in
theorem zw_lo (p t : U64) : zw p t &&& obj.MDB_PTR_MASK = p &&& obj.MDB_PTR_MASK := by
  unfold zw capability.PTR_MASK obj.MDB_PTR_MASK
  rw [i59, i48, UScalar.eq_equiv_bv_eq]
  simp only [UScalar.bv_and, UScalar.bv_or, bvM, bv9, bv255]
  zbv

set_option maxHeartbeats 4000000 in
theorem zw_hi (p t : U64) : (zw p t).bv >>> 59 = 9#64 := by
  unfold zw capability.PTR_MASK
  rw [i59, i48]
  simp only [UScalar.bv_and, UScalar.bv_or, bvM, bv9, bv255]
  zbv

theorem zw_hi' (p t : U64) : (zw p t).bv >>> (59#i32).toNat = 9#64 := by rw [i59]; exact zw_hi p t

set_option maxHeartbeats 4000000 in
theorem zw_ty (p t : U64) : (⟨(zw p t).bv >>> 48⟩ : U64) &&& 255#u64 = t &&& 255#u64 := by
  unfold zw capability.PTR_MASK
  rw [i59, i48, UScalar.eq_equiv_bv_eq]
  simp only [UScalar.bv_and, UScalar.bv_or, bvM, bv9, bv255]
  zbv

theorem zw_ty' (p t : U64) : (⟨(zw p t).bv >>> (48#i32).toNat⟩ : U64) &&& 255#u64 = t &&& 255#u64 := by
  rw [i48]; exact zw_ty p t

set_option maxHeartbeats 4000000 in
/-- **`Cap::decode` after `Cap::encode` of a Zombie cap with a canonical pointer** (capability.rs:184, 236): the
type is kept to its 8 encoded bits. -/
theorem decode_zw (p t n : U64) (hp : Canon p) :
    capability.Cap.decode (zw p t) n = ok (.Zombie p (t &&& 255#u64) n) := by
  have ht := zw_hi p t
  have ht' := zw_hi' p t
  unfold capability.Cap.decode
  simp only [DPF.shr_eq _ 59#i32 (by decide) (by decide), hp.unpack (zw_lo p t), bind_ok]
  split <;> rename_i heq <;> first
    | (exfalso; have := congrArg UScalar.bv heq; simp [ht, ht'] at this; done)
    | (simp only [DPF.shr_eq _ 48#i32 (by decide) (by decide), lift, bind_ok, zw_ty, zw_ty']; done)
    | (simp [DPF.shr_eq _ 48#i32 (by decide) (by decide), lift, bind_ok, zw_ty, zw_ty']; done)
    | (exfalso; simp_all; done)
    | (exfalso; have := congrArg UScalar.bv heq; simp_all; done)

/-- `set_cap` of a Zombie cap: the two words. -/
theorem set_cap_zombie (s : S) (x p t n : U64) :
    obj.Slot.set_cap st x s (.Zombie p t n) = ok (L.wr (L.wr s x (zw p t)) (wa x 8#u64) n) := by
  unfold obj.Slot.set_cap
  rw [encode_zombie, bind_ok]
  simp only [L.write_eq, lift, bind_ok]
  all_goals rfl

set_option maxHeartbeats 4000000 in
/-- **The pointers `Cap::decode` returns are canonical** (every arm's pointer is `unpack_ptr w0`). -/
theorem decode_canon' (w0 w1 : U64) :
    capability.Cap.decode w0 w1 ⦃ c => (∀ q, c = .Thread q → Canon q) ∧
      (∀ q r g b, c = .CNode q r g b → Canon q) ∧ (∀ q t n, c = .Zombie q t n → Canon q) ⦄ := by
  obtain ⟨p, hp⟩ := DPF.spec_tot (Fl4ProofsA64.P0.capability.unpack_ptr.p0 w0)
  have hc : Canon p := ⟨w0, hp⟩
  unfold capability.Cap.decode
  simp only [lift, bind_ok]
  refine WP.spec_bind (shr_tot _ _ (by decide) (by decide)) fun t _ => ?_
  rw [hp, bind_ok]
  split
  all_goals
    repeat' (first
      | refine WP.spec_bind (shr_tot _ _ (by decide) (by decide)) fun _ _ => ?_
      | refine WP.spec_bind (Fl4ProofsA64.P0.capability.bit.p0 _ _) fun _ _ => ?_
      | refine WP.spec_bind (Fl4ProofsA64.P0.capability.unpack_asid.p0 _ _ _) fun _ _ => ?_
      | refine WP.spec_bind (Fl4ProofsA64.P0.capability.unpack_ptr.p0 _) fun _ _ => ?_
      | refine WP.spec_bind (Fl4ProofsA64.P0.capability.FrameSize.from_code.p0 _) fun _ _ => ?_
      | split)
  all_goals
    first
    | (simp only [WP.spec_ok]; exact ⟨fun q h => by cases h <;> exact hc, fun q r g b h => by cases h <;> exact hc,
        fun q t n h => by cases h <;> exact hc⟩)
    | (rw [WP.spec_ok]; exact ⟨fun q h => by cases h <;> exact hc, fun q r g b h => by cases h <;> exact hc,
        fun q t n h => by cases h <;> exact hc⟩)
    | (simp only [WP.spec_ok]; exact ⟨fun q h => by cases h, fun q r g b h => by cases h, fun q t n h => by cases h⟩)
    | (rw [WP.spec_ok]; exact ⟨fun q h => by cases h, fun q r g b h => by cases h, fun q t n h => by cases h⟩)

theorem decode_canon {w0 w1 : U64} {c : capability.Cap} (h : capability.Cap.decode w0 w1 = ok c) :
    (∀ q, c = .Thread q → Canon q) ∧ (∀ q r g b, c = .CNode q r g b → Canon q) ∧
      (∀ q t n, c = .Zombie q t n → Canon q) := by
  have := decode_canon' w0 w1
  rw [h, WP.spec_ok] at this
  exact this

theorem slot_canon {s : S} {x : U64} {c : capability.Cap} (h : obj.Slot.cap st x s = ok c) :
    (∀ q, c = .Thread q → Canon q) ∧ (∀ q r g b, c = .CNode q r g b → Canon q) ∧
      (∀ q t n, c = .Zombie q t n → Canon q) := by
  rw [DPF.slot_cap_dec] at h
  exact decode_canon h

/-! ## `VcTy` across a cap write that installs no frame cap -/

/-- A cap that is no frame cap. -/
def NoFrame (c : capability.Cap) : Prop := ∀ p sz r d m e a v, c ≠ .Frame p sz r d m e a v

/-- **`VcTy` along a step that keeps the `VcTy` words and every IPC-buffer slot's cap or makes it a non-frame
cap.** -/
theorem VcTy.of_capw {Vc Ub : Set U64} {s s' : S} (h : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (k1 : L.ksb s' = L.ksb s) (k2 : ∀ b, VcW Vc b → L.mem s' b = L.mem s b)
    (k3 : ∀ t ∈ T, L.mem s' (wa t 3664#u64) = L.mem s (wa t 3664#u64))
    (k4 : ∀ t ∈ T, L.mem s' (runVcpuA t) = L.mem s (runVcpuA t))
    (k5 : ∀ t ∈ T, obj.Slot.cap st (sbWordA t) s' = obj.Slot.cap st (sbWordA t) s ∨
      ∃ c, obj.Slot.cap st (sbWordA t) s' = ok c ∧ NoFrame c) :
    VcTy st T Cs Ω H Sg Scs Z Vc Ub s' := by
  refine ⟨fun v hv => ?_, fun t ht => ?_, fun t ht => ?_, fun b hb => (h.usr b hb).ksb k1, fun t ht hne => ?_,
    fun b hb o ho => by rw [k1]; exact h.ks b hb o ho⟩
  · have o := h.obj v hv
    unfold VcObj at o ⊢
    rw [k2 _ (vcw_of (o := vcpu.TCB) hv (by simp [vcpu.TCB]) (by simp [vcpu.TCB])),
      k2 _ (vcw_of (o := vcpu.RUN_CALLER) hv (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER]))]
    exact o
  · rw [k3 t ht]; exact h.bnd t ht
  · rw [k4 t ht]; exact h.run t ht
  · have hne0 : L.mem s (runVcpuA t) ≠ 0#u64 := by rwa [k4 t ht] at hne
    have hvc : L.mem s (runVcpuA t) ∈ Vc := (h.run t ht).resolve_left hne0
    rcases k5 t ht with hc | ⟨c, hc, hnf⟩
    · exact RunBuf.of_eq (h.buf t ht hne0) hc (k4 t ht)
        (k2 _ (vcw_of (o := vcpu.RUN_OFFSET) hvc (by simp [vcpu.RUN_OFFSET]) (by simp [vcpu.RUN_OFFSET])))
    · intro ptr size rights dev x1 x2 x3 x4 bits sz e1
      rw [hc] at e1
      exact absurd (okinj e1) (hnf _ _ _ _ _ _ _ _)

section steps
variable {OS Vc Ub : Set U64}

/-- **Two writes inside a slot `x` of `OS`** (its words 0 and 8): every other `OS` slot's words kept, the `VcTy`
words kept, every IPC-buffer slot other than `x` keeps its cap. -/
theorem wr2_keep {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 : S}
    (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (q : SchedQueuesInvX st T Cs Ω H X s0 Q R)
    (hal : ∀ b, VcW Vc b → Aligned b) {s : S} {x w0 w1 : U64} (hx : x ∈ OS) :
    (∀ y ∈ OS, y ≠ x → L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) y = L.mem s y ∧ L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) (wa y 8#u64) = L.mem s (wa y 8#u64) ∧
      L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) (wa y 24#u64) = L.mem s (wa y 24#u64)) ∧
    L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) (wa x 16#u64) = L.mem s (wa x 16#u64) ∧ L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) (wa x 24#u64) = L.mem s (wa x 24#u64) ∧
    L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) x = w0 ∧ L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) (wa x 8#u64) = w1 ∧
    L.ksb (L.wr (L.wr s x w0) (wa x 8#u64) w1) = L.ksb s ∧ (∀ b, VcW Vc b → L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) b = L.mem s b) ∧
    (∀ t ∈ T, ∀ K : U64, 224 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) (wa t K) = L.mem s (wa t K)) := by
  have a0 := hO.al0 hx
  have a8 := hO.al hx (k := 8#u64) (by simp) (by simp)
  have a16 := hO.al hx (k := 16#u64) (by simp) (by simp)
  have a24 := hO.al hx (k := 24#u64) (by simp) (by simp)
  obtain ⟨v8, v16, v24⟩ := vals hO hx
  have c0 := hO.cw0 hx
  have c8 := hO.cw hx (k := 8#u64) (by simp) (by simp)
  have in0 : InOS OS x := ⟨x, hx, le_rfl, by omega⟩
  have in8 : InOS OS (wa x 8#u64) := ⟨x, hx, by omega, by omega⟩
  refine ⟨fun y hy hne => ?_, ?_, ?_, ?_, L.mem_wr_same a8, ?_, fun b hb => ?_, fun t ht K k1 k2 k3 => ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := other_keep (st := st) (s := L.wr s x w0) (v := w1) hO hx hy hne a8 (by omega)
    obtain ⟨f1, f2, f3, f4⟩ := other_keep (st := st) (s := s) (v := w0) hO hx hy hne a0 (by omega)
    exact ⟨e1.trans f1, e2.trans f2, e3.trans f3, e4.trans f4⟩
  · show L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) (wa x 16#u64) = _
    rw [L.mem_wr_ne a8 a16 (by omega), L.mem_wr_ne a0 a16 (by omega)]
  · show L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) (wa x 24#u64) = _
    rw [L.mem_wr_ne a8 a24 (by omega), L.mem_wr_ne a0 a24 (by omega)]
  · show L.mem (L.wr (L.wr s x w0) (wa x 8#u64) w1) x = _
    rw [L.mem_wr_ne a8 a0 (by omega), L.mem_wr_same a0]
  · show L.ksb (L.wr (L.wr s x w0) (wa x 8#u64) w1) = _
    rw [L.ksb_wr, L.ksb_wr]
  · have hb' := hal b hb
    rw [L.mem_wr_ne a8 hb' (fun e => hV.os b hb (by rw [← UScalar.eq_of_val_eq e]; exact in8)),
      L.mem_wr_ne a0 hb' (fun e => hV.os b hb (by rw [← UScalar.eq_of_val_eq e]; exact in0))]
  · have hf := field_aligned (q.tcbs t ht) k2 k3
    rw [L.mem_wr_ne a8 hf (fun e => capw_ne_hi q c8 ht k1 k2 (UScalar.eq_of_val_eq e)),
      L.mem_wr_ne a0 hf (fun e => capw_ne_hi q c0 ht k1 k2 (UScalar.eq_of_val_eq e))]

/-- The Zombie's object slot and its covered slots lie in `OS`. -/
def ZIn (OS : Set U64) (p n : U64) : Prop := p ∈ OS ∧ ∀ i : U64, i.val < n.val → slotIdx p i ∈ OS

theorem slotIdx0 (p : U64) : slotIdx p 0#u64 = p := by
  unfold slotIdx
  have : core.num.U64.wrapping_mul 0#u64 32#u64 = 0#u64 := by
    apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_mul_val_eq]
  rw [this, DPF.wadd0]

theorem CapTy.zombie (hO : OSOK T Ω Sg OS) {p t n : U64} (hz : ZIn OS p n) :
    CapTy T Ω Sg H Rp Nt OS (.Zombie p t n) := by
  have hp : p ∈ OS := hz.1
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first
    | (intros; simp_all; done)
    | skip
  · intro p' t' n' e
    cases e
    exact ⟨hO.slot p hp, fun i hi => hO.slot _ (hz.2 i hi)⟩
  · refine And.intro (fun _ _ _ _ e => by cases e) (fun p' t' n' e i hi => ?_)
    cases e
    exact hz.2 i hi

set_option maxHeartbeats 4000000 in
/-- **`set_cap` of a Zombie cap into a slot of `OS` keeps `JV`**, keeps every other `OS` slot's words, and the
slot then reads `Zombie p (t & 0xff) n`. -/
theorem JV.setz (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x p t n : U64} (hx : x ∈ OS) (hp : Canon p)
    (hz : ZIn OS p n) :
    obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s' ∧
      (∀ y ∈ OS, y ≠ x → L.mem s' y = L.mem s y ∧ L.mem s' (wa y 8#u64) = L.mem s (wa y 8#u64) ∧
        L.mem s' (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s' (wa y 24#u64) = L.mem s (wa y 24#u64)) ∧
      obj.Slot.cap st x s' = ok (.Zombie p (t &&& 255#u64) n) ⦄ := by
  rw [set_cap_zombie, WP.spec_ok]
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hal : ∀ b, VcW Vc b → Aligned b := fun b hb' => (h.2.w hb').1
  obtain ⟨ko, k16, k24, m0, m8, kk, kv, kt⟩ := wr2_keep (s := s) (w0 := zw p t) (w1 := n) hO hV q hal hx
  have a0 := hO.al0 hx
  have a8 := hO.al hx (k := 8#u64) (by simp) (by simp)
  have hcap : obj.Slot.cap st x (L.wr (L.wr s x (zw p t)) (wa x 8#u64) n) = ok (.Zombie p (t &&& 255#u64) n) := by
    rw [DPF.slot_cap_dec, m0, m8, decode_zw p t n hp]
  have c1 := h.1.1.capw7 ((writesIn_wr (v := zw p t) a0).trans (writesIn_wr (s := L.wr s x (zw p t)) (v := n) a8))
    fun b hb' => by
      rcases hb' with e | e
      · subst e; exact hO.cw0 hx
      · subst e; exact hO.cw hx (by simp) (by simp)
  refine ⟨⟨⟨c1, ?_⟩, ?_⟩, ko, hcap⟩
  · refine h.1.2.frame (x := x) ko ?_
    have hs := h.1.2 x hx
    unfold SlotOK at hs ⊢
    refine ⟨?_, by rw [k16]; exact hs.2.1, by rw [k24]; exact hs.2.2⟩
    rw [m0, m8, decode_zw p t n hp]
    intro c hc
    rw [← okinj hc]
    exact CapTy.zombie hO hz
  · refine VcTy.of_capw h.2 kk kv (fun t' ht => kt t' ht _ (by simp) (by simp) (by simp))
      (fun t' ht => kt t' ht 3672#u64 (by simp) (by simp) (by simp)) fun t' ht => ?_
    by_cases e : sbWordA t' = x
    · right
      rw [e]
      exact ⟨_, hcap, fun _ _ _ _ _ _ _ _ h' => by cases h'⟩
    · left
      have hy := hV.bcov t' ht
      obtain ⟨e0, e8, -, -⟩ := ko _ hy e
      rw [DPF.slot_cap_dec, DPF.slot_cap_dec, e0, e8]

/-! ## `empty_slot` writes no cap word of another slot -/

/-- The cap words (0 and 8) of every `OS` slot but `x` kept. -/
def CapKeep (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (x : U64) (s s' : S) : Prop :=
  ∀ y ∈ OS, y ≠ x → L.mem s' y = L.mem s y ∧ L.mem s' (wa y 8#u64) = L.mem s (wa y 8#u64)

theorem CapKeep.refl (x : U64) (s : S) : CapKeep st OS x s s := fun _ _ _ => ⟨rfl, rfl⟩

theorem CapKeep.trans {x : U64} {s1 s2 s3 : S} (h1 : CapKeep st OS x s1 s2) (h2 : CapKeep st OS x s2 s3) :
    CapKeep st OS x s1 s3 := fun y hy hne =>
  ⟨(h2 y hy hne).1.trans (h1 y hy hne).1, (h2 y hy hne).2.trans (h1 y hy hne).2⟩

/-- A write at offset 16 or 24 of a slot of `OS` keeps every cap word of every `OS` slot. -/
theorem CapKeep.lnk (hO : OSOK T Ω Sg OS) {s : S} {p k v x : U64} (hp : p ∈ OS) (hk : k.val = 16 ∨ k.val = 24) :
    CapKeep st OS x s (L.wr s (wa p k) v) := fun y hy _ => by
  have hk' : k.val < 32 := by omega
  have ha := hO.al hp hk' (by omega)
  refine ⟨?_, ?_⟩
  · have := L.mem_wr_ne (s := s) (v := v) ha (hO.al0 hy) (by
      have := os_ne hO hp hy (k := k) (k' := 0#u64) hk' (by simp) (fun _ => by simp; omega)
      rwa [SFF.wadd0'] at this)
    exact this
  · exact L.mem_wr_ne ha (hO.al hy (by simp) (by simp))
      (os_ne hO hp hy (k := k) (k' := 8#u64) hk' (by simp) (fun _ => by simp; omega))

set_option maxHeartbeats 4000000 in
/-- **`empty_slot` of a slot `x` of `OS`, null cleanup**: every other `OS` slot keeps its cap words, and `x` then
reads `Null`. -/
theorem cdt.empty_slot.ck {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) {s : S} {a : A} {x : U64}
    (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hx : x ∈ OS) :
    cdt.empty_slot st ar s a x .Null ⦃ r => CapKeep st OS x s r.1 ∧ obj.Slot.cap st x r.1 = ok .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.empty_slot
  obtain ⟨c0, hc0⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s hS)
  rw [hc0, bind_ok]
  obtain ⟨bn, hbn⟩ := DPF.spec_tot (P0.capability.Cap.is_null.p0 c0)
  rw [hbn, bind_ok]
  split
  · rename_i hb
    subst hb
    refine (WP.spec_ok _).2 ⟨CapKeep.refl x s, ?_⟩
    rw [hc0]
    cases c0 <;> simp_all [capability.Cap.is_null]
  have hxo := hT x hx
  obtain ⟨nx, hnx⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s (wa x 24#u64)))
  have hnl : LinkOK OS nx := hxo.2.2 nx hnx
  have hpv : LinkOK OS (L.mem s (wa x 16#u64)) := hxo.2.1
  rw [slot_prev_eq, bind_ok, slot_next_of hnx, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => CapKeep st OS x s s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 (CapKeep.refl x s)
    · rename_i hp0
      have hpO : L.mem s (wa x 16#u64) ∈ OS := hpv.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact CapKeep.lnk hO hpO (k := 24#u64) (by simp)
  refine WP.spec_bind (Pₘ := fun s2 => CapKeep st OS x s s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnO : nx ∈ OS := hnl.resolve_left (by simpa using hn0)
      rw [set_prev_eq, bind_ok]
      have h3 := h1.trans (CapKeep.lnk (s := s1) (v := L.mem s (wa x 16#u64)) hO hnO (k := 16#u64) (by simp))
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx _ hS) fun nfb _ => ?_
      split
      · rw [set_fb_eq_t, WP.spec_ok]; exact h3.trans (CapKeep.lnk hO hnO (k := 24#u64) (by simp))
      · cases fb
        · rw [set_fb_eq_f, WP.spec_ok]; exact h3.trans (CapKeep.lnk hO hnO (k := 24#u64) (by simp))
        · rw [set_fb_eq_t, WP.spec_ok]; exact h3.trans (CapKeep.lnk hO hnO (k := 24#u64) (by simp))
  rw [clear_eq, bind_ok, pcd_null, WP.spec_ok]
  have a0 := hO.al0 hx
  have a8 := hO.al hx (k := 8#u64) (by simp) (by simp)
  have a16 := hO.al hx (k := 16#u64) (by simp) (by simp)
  have a24 := hO.al hx (k := 24#u64) (by simp) (by simp)
  obtain ⟨v8, v16, v24⟩ := vals hO hx
  refine ⟨h2.trans fun y hy hne => ?_, ?_⟩
  · obtain ⟨d1, d2, -, -⟩ := other_keep (st := st)
      (s := L.wr (L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (v := 0#u64) hO hx hy hne a24
      (by omega)
    obtain ⟨e1, e2, -, -⟩ := other_keep (st := st) (s := L.wr (L.wr s2 x 0#u64) (wa x 8#u64) 0#u64) (v := 0#u64)
      hO hx hy hne a16 (by omega)
    obtain ⟨f1, f2, -, -⟩ := other_keep (st := st) (s := L.wr s2 x 0#u64) (v := 0#u64) hO hx hy hne a8 (by omega)
    obtain ⟨g1, g2, -, -⟩ := other_keep (st := st) (s := s2) (v := 0#u64) hO hx hy hne a0 (by omega)
    exact ⟨d1.trans (e1.trans (f1.trans g1)), d2.trans (e2.trans (f2.trans g2))⟩
  · rw [DPF.slot_cap_dec]
    rw [L.mem_wr_ne a24 a0 (by omega), L.mem_wr_ne a16 a0 (by omega), L.mem_wr_ne a8 a0 (by omega),
      L.mem_wr_same a0, L.mem_wr_ne a24 a8 (by omega), L.mem_wr_ne a16 a8 (by omega), L.mem_wr_same a8,
      decode_zero]

end steps

end ST
end R
end W7

end

end Fl4ProofsA64.P1

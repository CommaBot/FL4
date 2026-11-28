/-
P1 (aarch64, gen 34): **the Zombie loop over `JV` with non-leaf covered slots** — the swap path of
`finalise_slot_deferred` (`cap_swap_for_delete`, `cdt.swap`, the cyclic-Zombie exit), extending gen 33's leaf-domain
loop (QueueZombieV) to domains whose slots hold CNode and Zombie caps.

Source (crates/fl4-core/src/cdt.rs): `finalise_slot_immediate` (271–297) sets the Zombie remainder, runs
`delete_deferred` of the last covered slot and decrements the Zombie if it is still there; `finalise_slot_deferred`
(243–268) finalises a covered slot's cap and, for a Zombie remainder `Zombie p …` with `p ≠ slot`, swaps it into
`p` (seL4 `reduceZombie(slot, false)`: `cap_swap_for_delete(p, slot)`, 96–103, `swap`, 67–94); a remainder with
`p = slot` exits (`success = false`). Both loops are bounded by `WALK_FUEL` and end in `Preempted` when it runs out:
the invariant below is a per-round invariant, no termination measure on Zombie depth is needed (every exit, the
fuel exit included, keeps it).

* **`ZN D`** (a *domain cap*): a leaf (`ZL`: `TrivK`, endpoint / notification / reply), a CNode cap whose `2^radix`
  slots lie in `D`, or a Zombie cap whose covered slots lie in `D` (any finality); **`DomN D s`**: every slot of
  `D` holds a domain cap (gen 33's `DomL` is the leaf case: `DomL.toN`). `DomN` is closed under the deferred
  round: a CNode cap finalises to `Null` or `Zombie p r n` with its slots in `D`, a Zombie to itself, and the swap
  exchanges the caps of two slots of `D`. `OutK OS D s s'`: every `OS` slot outside `D` keeps its cap.
* **`DCan D`** (`∀ y ∈ D, sext48 y = y`): the slots of the domain are canonical addresses, so `swap`'s `NEXT`
  links to them read back (`set_next` keeps the 48 pointer bits, `NextOK` reads them with `sext48`). A case
  hypothesis on the ghost domain (state-free), like `D ⊆ OS`.
* Store steps: `set_cap_eq`; **`JV.setc`** (`set_cap` of any cap that decodes back — `CapRt.dec_rt` — typed
  `CapTy`, no frame cap); `J.nextw` (a `NEXT` word whose pointer bits are a link), `JV.nextw`, `JV.prev`,
  `lnk_cap`; `set_nf_spec` (`set_next_flags` writes pointer bits `n`: `nf_bits`); **`cdt.swap.jv`** (`swap` of two
  distinct canonical `OS` slots holding non-frame caps keeps `JV`, exchanges their caps, keeps every other `OS`
  slot's cap); **`cdt.cap_swap_for_delete.zn`**.
* The loop: `finXN` (gen 33's `finX` with `OSKeep`), **`cdt.finalise_slot_deferred.zn`** (the swap path and the
  cyclic exit over `JV ∧ DomN D ∧ OutK`), **`cdt.delete_deferred.zn`**, **`cdt.finalise_slot_immediate.zn`**
  (invariant `JV ∧ DomN D ∧ XOK D x`; `x` may lie in `D` — e.g. a CNode holding a cap to itself — then the swap may
  move `x`'s cap and the decrement is skipped, as in the source), **`cdt.delete.zn`** and the instances
  **`cdt.delete.zombieN`**, **`cdt.delete.threadN`** (a thread whose TCB slots hold CNode / Zombie / leaf caps: the
  CSpace-root CNode included), **`cdt.delete.cnodeN`** (a CNode whose slots hold CNode caps, at any depth, cycles
  included); gen 33's leaf versions as corollaries (`cdt.delete.zv'`). At the entry: **`cdt.delete.zn_ent`** ([J]
  `SlotTyEntZ`); at the decode: **`syscall.decode_invocation.del_zn`**, **`del_zn_ent`**.

* **The VCPU kind** (goal 3): `vcpu.finalise.ubV`, **`finJV_vcpu`** (`Vcpu v`, `v ∈ Vc`, any finality: `(Null, Null)`
  and `JV`, from gen 32's `vcpu.unbind.ubV`, no [P] `DelPlaceAt`), **`cdt.delete.vcpuV`**. Its write set is gen 32's
  `DS` frame (`OSKeep ∧ VKeepZ`: the VCPU's `TCB` / `OWNER_CPU` / `RUN_CALLER` words and the bound thread's two
  VCPU links zeroed, `complete_run`'s caller registers and IPC-buffer words), not a `FootCfg` footprint: VCPU words
  and the links 3664 / 3672 lie outside every `KWc`.

**Not covered** (stated as the class `ZN`): a covered slot holding a thread cap (its final finalisation asks the
thread not to be the idle thread *at that state*; the idle word `IDLE_THREAD` is a node word inside every finaliser
footprint (`KW`'s node clause, offsets `≠ 88`), so its preservation across the finalisers of the other covered
slots is not derivable from the footprints; it needs the finalisers' exact node write sets), SC / IrqHandler / VCPU
/ VSpace / mapped-frame caps in covered slots (the typical thread's VSpace root and IPC-buffer frame).

No named premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueSlotTyDecV
import Fl4ProofsA64.P1.QueueCapRt
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

section zn
variable {OS Vc Ub D : Set U64}

/-! ## Definitions -/

/-- **A domain cap** (module docstring). -/
def ZN (D : Set U64) (c : capability.Cap) : Prop :=
  ZL c ∨ (∃ p r g b, c = .CNode p r g b ∧ ∀ i : U64, i.val < 2 ^ (r.val % 64) → slotIdx p i ∈ D) ∨
  (∃ p t n, c = .Zombie p t n ∧ ∀ i : U64, i.val < n.val → slotIdx p i ∈ D)

/-- Every slot of `D` holds a domain cap. -/
def DomN (st : machine.Store S) [L : LawfulStore st] (D : Set U64) (s : S) : Prop :=
  ∀ y ∈ D, ∀ c, obj.Slot.cap st y s = ok c → ZN D c

/-- Every `OS` slot outside `D` keeps its cap. -/
def OutK (st : machine.Store S) [L : LawfulStore st] (OS D : Set U64) (s s' : S) : Prop :=
  ∀ y ∈ OS, y ∉ D → obj.Slot.cap st y s' = obj.Slot.cap st y s

/-- The domain's slots are canonical addresses (module docstring). -/
def DCan (D : Set U64) : Prop := ∀ y ∈ D, obj.sext48 y = ok y

theorem OutK.refl (s : S) : OutK st OS D s s := fun _ _ _ => rfl

theorem OutK.trans {s1 s2 s3 : S} (h1 : OutK st OS D s1 s2) (h2 : OutK st OS D s2 s3) : OutK st OS D s1 s3 :=
  fun y hy hn => (h2 y hy hn).trans (h1 y hy hn)

theorem OutK.of_osk {s s' : S} (k : OSKeep st OS s s') : OutK st OS D s s' := fun _ hy _ => k.cap hy

theorem zn_xk {i : U64} {c : capability.Cap} (h : ZN D c) : XK D i c := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem zn_nf {c : capability.Cap} (h : ZN D c) : NoFrame c := by
  intro p sz r d m e a v hc
  subst hc
  rcases h with h | ⟨_, _, _, _, h, -⟩ | ⟨_, _, _, h, -⟩
  · unfold ZL TrivK EpNtRp at h; simp at h
  · cases h
  · cases h

theorem DomL.toN {s : S} (h : DomL st D s) : DomN st D s := fun y hy c hc => Or.inl (h y hy c hc)

theorem DomN.osk {s s' : S} (h : DomN st D s) (hDO : D ⊆ OS) (k : OSKeep st OS s s') : DomN st D s' :=
  fun y hy c hc => h y hy c (by rw [k.cap (hDO hy)] at hc; exact hc)

/-- `DomN` along a step where every slot of `D` keeps its cap or holds a domain cap. -/
theorem DomN.upd {s s' : S} (h : DomN st D s)
    (hk : ∀ y ∈ D, obj.Slot.cap st y s' = obj.Slot.cap st y s ∨ ∀ c, obj.Slot.cap st y s' = ok c → ZN D c) :
    DomN st D s' := fun y hy c hc => by
  rcases hk y hy with e | e
  · rw [e] at hc; exact h y hy c hc
  · exact e c hc

theorem capk4 {s s' : S} {x : U64}
    (k : ∀ y ∈ OS, y ≠ x → L.mem s' y = L.mem s y ∧ L.mem s' (wa y 8#u64) = L.mem s (wa y 8#u64) ∧
      L.mem s' (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s' (wa y 24#u64) = L.mem s (wa y 24#u64))
    {y : U64} (hy : y ∈ OS) (hne : y ≠ x) : obj.Slot.cap st y s' = obj.Slot.cap st y s := by
  rw [DPF.slot_cap_dec, DPF.slot_cap_dec, (k y hy hne).1, (k y hy hne).2.1]

/-! ## `set_cap` of a cap that decodes back -/

theorem set_cap_eq {s : S} {x : U64} {c : capability.Cap} {a b : U64} (he : capability.Cap.encode c = ok (a, b)) :
    obj.Slot.set_cap st x s c = ok (L.wr (L.wr s x a) (wa x 8#u64) b) := by
  unfold obj.Slot.set_cap
  rw [he, bind_ok]
  simp only [L.write_eq, lift, bind_ok]
  all_goals rfl

set_option maxHeartbeats 4000000 in
/-- **`set_cap` of a typed non-frame cap that decodes back, into a slot of `OS`, keeps `JV`**, keeps every other
`OS` slot's words, and the slot then reads the cap. -/
theorem JV.setc (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64} {c : capability.Cap} {w0 w1 : U64}
    (hx : x ∈ OS) (he : capability.Cap.encode c = ok (w0, w1)) (hd : capability.Cap.decode w0 w1 = ok c)
    (hty : CapTy T Ω Sg H Rp Nt OS c) (hnf : NoFrame c) :
    obj.Slot.set_cap st x s c ⦃ s' => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s' ∧
      (∀ y ∈ OS, y ≠ x → L.mem s' y = L.mem s y ∧ L.mem s' (wa y 8#u64) = L.mem s (wa y 8#u64) ∧
        L.mem s' (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s' (wa y 24#u64) = L.mem s (wa y 24#u64)) ∧
      obj.Slot.cap st x s' = ok c ⦄ := by
  rw [set_cap_eq he, WP.spec_ok]
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hal : ∀ b, VcW Vc b → Aligned b := fun b hb' => (h.2.w hb').1
  obtain ⟨ko, k16, k24, m0, m8, kk, kv, kt⟩ := wr2_keep (s := s) (w0 := w0) (w1 := w1) hO hV q hal hx
  have a0 := hO.al0 hx
  have a8 := hO.al hx (k := 8#u64) (by simp) (by simp)
  have hcap : obj.Slot.cap st x (L.wr (L.wr s x w0) (wa x 8#u64) w1) = ok c := by
    rw [DPF.slot_cap_dec, m0, m8, hd]
  have c1 := h.1.1.capw7 ((writesIn_wr (v := w0) a0).trans (writesIn_wr (s := L.wr s x w0) (v := w1) a8))
    fun b hb' => by
      rcases hb' with e | e
      · subst e; exact hO.cw0 hx
      · subst e; exact hO.cw hx (by simp) (by simp)
  refine ⟨⟨⟨c1, ?_⟩, ?_⟩, ko, hcap⟩
  · refine h.1.2.frame (x := x) ko ?_
    have hs := h.1.2 x hx
    unfold SlotOK at hs ⊢
    refine ⟨?_, by rw [k16]; exact hs.2.1, by rw [k24]; exact hs.2.2⟩
    rw [m0, m8, hd]
    intro c' hc'
    rw [← okinj hc']
    exact hty
  · refine VcTy.of_capw h.2 kk kv (fun t' ht => kt t' ht _ (by simp) (by simp) (by simp))
      (fun t' ht => kt t' ht 3672#u64 (by simp) (by simp) (by simp)) fun t' ht => ?_
    by_cases e : sbWordA t' = x
    · right
      rw [e]
      exact ⟨_, hcap, hnf⟩
    · left
      have hy := hV.bcov t' ht
      obtain ⟨e0, e8, -, -⟩ := ko _ hy e
      rw [DPF.slot_cap_dec, DPF.slot_cap_dec, e0, e8]

/-! ## The link writes of `swap` -/

/-- **A `NEXT` word whose pointer bits are an MDB link** keeps `J`. -/
theorem J.nextw (hO : OSOK T Ω Sg OS) {s0 s : S} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) {p n w : U64}
    (hp : p ∈ OS) (hn : LinkOK OS n) (hni : obj.sext48 n = ok n)
    (hw : w &&& obj.MDB_PTR_MASK = n &&& obj.MDB_PTR_MASK) :
    J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 (L.wr s (wa p 24#u64) w) := by
  have ha := hO.al hp (k := 24#u64) (by simp) (by simp)
  obtain ⟨v8, v16, v24⟩ := vals hO hp
  refine ⟨h.1.capw7 (writesIn_wr ha) fun b e => by subst e; exact hO.cw hp (by simp) (by simp), ?_⟩
  refine h.2.frame (x := p) (fun y hy hne => other_keep hO hp hy hne ha (by omega)) ?_
  have hs := h.2 p hp
  unfold SlotOK at hs ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [L.mem_wr_ne ha (hO.al0 hp) (by omega), L.mem_wr_ne ha (hO.al hp (by simp) (by simp)) (by omega)]
    exact hs.1
  · rw [L.mem_wr_ne ha (hO.al hp (by simp) (by simp)) (by omega)]; exact hs.2.1
  · rw [L.mem_wr_same ha]
    intro m hm
    rw [← sx_mask, hw, sx_mask, hni] at hm
    exact (okinj hm) ▸ hn

theorem JV.nextw (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {p n w : U64}
    (hp : p ∈ OS) (hn : LinkOK OS n) (hni : obj.sext48 n = ok n)
    (hw : w &&& obj.MDB_PTR_MASK = n &&& obj.MDB_PTR_MASK) :
    JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 (L.wr s (wa p 24#u64) w) := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  exact ⟨J.nextw hO h.1 hp hn hni hw, h.2.keep (VKeep.wr_os hO hV q (fun b hb' => (h.2.w hb').1) hp
    (by simp) (by simp) (fun e => by simp at e) (fun e => by simp at e))⟩

theorem JV.prev (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {n v : U64} (hn : n ∈ OS) (hv : LinkOK OS v) :
    JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 (L.wr s (wa n 16#u64) v) := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  exact ⟨J.prev hO h.1 hn hv, h.2.keep (VKeep.wr_os hO hV q (fun b hb' => (h.2.w hb').1) hn
    (by simp) (by simp) (fun e => by simp at e) (fun e => by simp at e))⟩

/-- A link write (offset 16 or 24 of a slot of `OS`) keeps every `OS` slot's cap. -/
theorem lnk_cap (hO : OSOK T Ω Sg OS) {s : S} {p k v y : U64} (hp : p ∈ OS) (hk : k.val = 16 ∨ k.val = 24)
    (hy : y ∈ OS) : obj.Slot.cap st y (L.wr s (wa p k) v) = obj.Slot.cap st y s := by
  have hk' : k.val < 32 := by omega
  have ha := hO.al hp hk' (by omega)
  have e0 : L.mem (L.wr s (wa p k) v) y = L.mem s y := by
    have := L.mem_wr_ne (s := s) (v := v) ha (hO.al0 hy) (by
      have := os_ne hO hp hy (k := k) (k' := 0#u64) hk' (by simp) (fun _ => by simp; omega)
      rwa [SFF.wadd0'] at this)
    exact this
  have e8 : L.mem (L.wr s (wa p k) v) (wa y 8#u64) = L.mem s (wa y 8#u64) :=
    L.mem_wr_ne ha (hO.al hy (by simp) (by simp))
      (os_ne hO hp hy (k := k) (k' := 8#u64) hk' (by simp) (fun _ => by simp; omega))
  rw [DPF.slot_cap_dec, DPF.slot_cap_dec, e0, e8]

/-- The revocable flag (`1 << 48`). -/
abbrev RVB : U64 := 281474976710656#u64

theorem rvb_val : obj.MDB_REVOCABLE = ok RVB := by
  unfold obj.MDB_REVOCABLE
  rw [SFF.shl_eq _ _ (by decide) (by decide)]
  rfl

theorem rvbc : (RVB &&& obj.MDB_PTR_MASK) = 0#u64 := by unfold obj.MDB_PTR_MASK; rfl
theorem nfc : (~~~ ((obj.MDB_PTR_MASK ||| RVB) ||| FB) &&& obj.MDB_PTR_MASK) = 0#u64 := by
  unfold obj.MDB_PTR_MASK; rfl

theorem nf_bits (w n r f M P : U64) (hr : r &&& P = 0#u64) (hf : f &&& P = 0#u64) (hM : ~~~M &&& P = 0#u64) :
    ((((w &&& ~~~M) ||| (n &&& P)) ||| r) ||| f) &&& P = n &&& P := by
  rw [UScalar.eq_equiv_bv_eq] at hr hf hM ⊢
  apply BitVec.eq_of_getLsbD_eq; intro i
  have h1 := congrArg (fun x => BitVec.getLsbD x i) hr
  have h2 := congrArg (fun x => BitVec.getLsbD x i) hf
  have h3 := congrArg (fun x => BitVec.getLsbD x i) hM
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not] at h1 h2 h3 ⊢
  revert h1 h2 h3
  cases w.bv.getLsbD i <;> cases n.bv.getLsbD i <;> cases r.bv.getLsbD i <;> cases f.bv.getLsbD i <;>
    cases M.bv.getLsbD i <;> cases P.bv.getLsbD i <;> (try simp) <;> omega

/-- **`set_next_flags` writes the `NEXT` word with the pointer bits of `n`.** -/
theorem set_nf_spec (s : S) (x n : U64) (r f : Bool) :
    obj.Slot.set_next_flags st x s n r f ⦃ s' => ∃ w, s' = L.wr s (wa x 24#u64) w ∧
      w &&& obj.MDB_PTR_MASK = n &&& obj.MDB_PTR_MASK ⦄ := by
  unfold obj.Slot.set_next_flags obj.Slot.next_word
  simp only [lift, bind_ok, cte_next, L.read_eq, fb_val, rvb_val]
  cases r <;> cases f <;>
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, L.write_eq, WP.spec_ok] <;>
    exact ⟨_, rfl, nf_bits _ _ _ _ _ _ (by first | exact rvbc | exact fbc3) (by first | exact fbc1 | exact fbc3)
      nfc⟩

/-! ## `swap` over `JV` -/

/-- The running facts of a swap of the caps `c1` (of `x1`) and `c2` (of `x2`) from `s`. -/
def SwP (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac OS Vc Ub : Set U64) (s0 s : S) (x1 x2 : U64) (c1 c2 : capability.Cap) (s' : S) : Prop :=
  JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s' ∧ obj.Slot.cap st x1 s' = ok c2 ∧
    obj.Slot.cap st x2 s' = ok c1 ∧ ∀ y ∈ OS, y ≠ x1 → y ≠ x2 → obj.Slot.cap st y s' = obj.Slot.cap st y s

theorem SwP.lnk (hO : OSOK T Ω Sg OS) {s0 s s' : S} {x1 x2 : U64} {c1 c2 : capability.Cap}
    (h : SwP st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s') {p k v : U64} (hp : p ∈ OS)
    (hk : k.val = 16 ∨ k.val = 24) (hj : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 (L.wr s' (wa p k) v))
    (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) :
    SwP st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 (L.wr s' (wa p k) v) :=
  ⟨hj, by rw [lnk_cap hO hp hk hx1]; exact h.2.1, by rw [lnk_cap hO hp hk hx2]; exact h.2.2.1,
    fun y hy h1 h2 => by rw [lnk_cap hO hp hk hy]; exact h.2.2.2 y hy h1 h2⟩

set_option maxHeartbeats 16000000 in
/-- **`swap` of two distinct canonical `OS` slots holding non-frame caps keeps `JV`**, exchanges the two caps and
keeps every other `OS` slot's cap (cdt.rs 67–94: the two cap writes, then the four slots' MDB links). -/
theorem cdt.swap.jv (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x1 x2 : U64} {c1 c2 : capability.Cap}
    (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2)
    (hc1 : obj.Slot.cap st x1 s = ok c1) (hc2 : obj.Slot.cap st x2 s = ok c2) (hf1 : NoFrame c1)
    (hf2 : NoFrame c2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => SwP st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s' ⦄ := by
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
  refine WP.spec_bind (JV.setc hO hV h hx1 he2 hr2 ht2 hf2) ?_
  rintro s1 ⟨h1, k1, e1⟩
  refine WP.spec_bind (JV.setc hO hV h1 hx2 he1 hr1 ht1 hf1) ?_
  rintro s2 ⟨h2, k2, e2⟩
  have P2 : SwP st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s2 :=
    ⟨h2, by rw [capk4 k2 hx1 hne]; exact e1, e2, fun y hy n1 n2 => by
      rw [capk4 k2 hy n2, capk4 k1 hy n1]⟩
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
  refine WP.spec_bind (Pₘ := fun s3 => SwP st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s3) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 P2
    · rename_i hp0
      have hpO : L.mem s2 (wa x1 16#u64) ∈ OS := lp1.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact P2.lnk hO hpO (k := 24#u64) (by simp)
        (JV.nextw hO hV h2 hpO (Or.inr hx2) hs2 (link_bits _ _)) hx1 hx2
  intro s3 P3
  refine WP.spec_bind (Pₘ := fun s4 => SwP st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s4) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 P3
    · rename_i hn0
      have hnO : n1 ∈ OS := ln1.resolve_left (by simpa using hn0)
      rw [set_prev_eq, WP.spec_ok]
      exact P3.lnk hO hnO (k := 16#u64) (by simp) (JV.prev hO hV P3.1 hnO (Or.inr hx2)) hx1 hx2
  intro s4 P4
  -- slot 2's links at `s4`
  have l2 := P4.1.1.2 x2 hx2
  rw [slot_prev_eq s4 x2, bind_ok]
  obtain ⟨n2, hn2⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s4 (wa x2 24#u64)))
  rw [slot_next_of hn2, bind_ok]
  have lp2 : LinkOK OS (L.mem s4 (wa x2 16#u64)) := l2.2.1
  have ln2 : LinkOK OS n2 := l2.2.2 n2 hn2
  have in2 : obj.sext48 n2 = ok n2 := sx_idem _ _ hn2
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x2 s4 hS) fun r2 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x2 s4 hS) fun f2 _ => ?_
  rw [set_prev_eq s4 x1 _, bind_ok]
  have P5 := P4.lnk hO hx1 (k := 16#u64) (by simp) (JV.prev hO hV P4.1 hx1 lp2) hx1 hx2
  refine WP.spec_bind (set_nf_spec _ x1 n2 r2 f2) ?_
  rintro s6 ⟨w6, rfl, hw6⟩
  have P6 := P5.lnk hO hx1 (k := 24#u64) (by simp) (JV.nextw hO hV P5.1 hx1 ln2 in2 hw6) hx1 hx2
  rw [set_prev_eq _ x2 _, bind_ok]
  have P7 := P6.lnk hO hx2 (k := 16#u64) (by simp) (JV.prev hO hV P6.1 hx2 lp1) hx1 hx2
  refine WP.spec_bind (set_nf_spec _ x2 n1 r1 f1) ?_
  rintro s8 ⟨w8, rfl, hw8⟩
  have P8 := P7.lnk hO hx2 (k := 24#u64) (by simp) (JV.nextw hO hV P7.1 hx2 ln1 in1 hw8) hx1 hx2
  try simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s9 => SwP st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s9) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 P8
    · rename_i hp0
      have hpO : L.mem s4 (wa x2 16#u64) ∈ OS := lp2.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact P8.lnk hO hpO (k := 24#u64) (by simp)
        (JV.nextw hO hV P8.1 hpO (Or.inr hx1) hs1 (link_bits _ _)) hx1 hx2
  intro s9 P9
  split
  · exact (WP.spec_ok _).2 P9
  · rename_i hn0
    have hnO : n2 ∈ OS := ln2.resolve_left (by simpa using hn0)
    rw [set_prev_eq, WP.spec_ok]
    exact P9.lnk hO hnO (k := 16#u64) (by simp) (JV.prev hO hV P9.1 hnO (Or.inr hx1)) hx1 hx2

set_option maxHeartbeats 4000000 in
/-- **`cap_swap_for_delete` of two distinct slots of a domain keeps `JV` and `DomN`**, and every `OS` slot outside
the domain keeps its cap. -/
theorem cdt.cap_swap_for_delete.zn (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS)
    (hDC : DCan D) {s0 s : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hD : DomN st D s)
    {p y : U64} (hp : p ∈ D) (hy : y ∈ D) (hne : p ≠ y) :
    cdt.cap_swap_for_delete st s p y ⦃ s' => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s' ∧ DomN st D s' ∧
      OutK st OS D s s' ⦄ := by
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
  refine WP.spec_mono (cdt.swap.jv hO hV h (hDO hp) (hDO hy) hne (hDC p hp) (hDC y hy) hc1 hc2 (zn_nf z1)
    (zn_nf z2)) ?_
  rintro s' ⟨h', e1, e2, ek⟩
  refine ⟨h', fun z hz c hc => ?_, fun z hz hzD => ek z hz (fun e => hzD (e ▸ hp)) (fun e => hzD (e ▸ hy))⟩
  by_cases e1' : z = p
  · subst e1'; rw [e1] at hc; rw [← okinj hc]; exact z2
  · by_cases e2' : z = y
    · subst e2'; rw [e2] at hc; rw [← okinj hc]; exact z1
    · rw [ek z (hDO hz) e1' e2'] at hc; exact hD z hz c hc

/-! ## The finalisation of a domain / deleted cap -/

set_option maxHeartbeats 4000000 in
/-- **The finalisation of an `XK` cap** (gen 33's `finX`, every `OS` word kept instead of `DomL`). -/
theorem finXN {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64} (hx : x ∈ OS)
    {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c) (hX : XK D (L.idleW s) c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => r.1.2 = .Null ∧
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ OSKeep st OS s r.2.1 ∧ ZRem st D r.1.1 ⦄ := by
  rcases hX with hl | ⟨p, rfl, hid, hcov⟩ | ⟨p, r, g, b, rfl, hcov⟩ | ⟨p, t, n, rfl, hcov⟩
  · exact WP.spec_mono (finL hP hO hA hV h hx hc hl a fin) fun r hr => by
      rw [hr.1]; exact ⟨rfl, hr.2.1, hr.2.2, Or.inl rfl⟩
  · refine WP.spec_mono (finJV_threadK hP hO hA hV h hx hc hid a fin) fun r hr => ?_
    obtain ⟨e, h2, k2⟩ := hr
    rw [e]
    refine ⟨rfl, h2, k2, ?_⟩
    cases fin
    · exact Or.inl rfl
    · exact Or.inr ⟨p, _, _, rfl, (slot_canon hc).1 p rfl, fun i hi => hcov i (by simpa using hi)⟩
  · refine WP.spec_mono (fin_cnode.z ar s a p r g b fin) fun x hr => ?_
    obtain ⟨e, ecl, hrem⟩ := hr
    rw [e]
    refine ⟨ecl, h, OSKeep.rfl' s, ?_⟩
    rcases hrem with e1 | ⟨n, e1, -, hlt⟩
    · exact Or.inl e1
    · exact Or.inr ⟨p, r, n, e1, (slot_canon hc).2.1 p r g b rfl, fun i hi => hcov i (hlt i hi)⟩
  · rw [fin_zombie.z, WP.spec_ok]
    exact ⟨rfl, h, OSKeep.rfl' s, Or.inr ⟨p, t, n, rfl, (slot_canon hc).2.2 p t n rfl, hcov⟩⟩

/-! ## The deferred round with the swap path -/

set_option maxHeartbeats 16000000 in
/-- **`finalise_slot_deferred` of a slot of a domain `D`** (module docstring): `JV`, `DomN D`, the `OS` slots
outside `D` keep their caps, a null cleanup — through the swap path and the cyclic exit, at every round. -/
theorem cdt.finalise_slot_deferred.zn {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {y : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomN st D s) :
    cdt.finalise_slot_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomN st D r.2.1 ∧ OutK st OS D s r.2.1 ∧ ∀ v, r.1 = .Ok v → v.cleanup = .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop
  apply loop.spec_decr_nat (measure := fun z => z.2.2.val)
    (inv := fun z => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 z.1 ∧ DomN st D z.1 ∧ OutK st OS D s z.1)
  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, o1⟩
    simp only at h1 d1 o1
    dsimp only
    unfold cdt.finalise_slot_deferred_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, by intro v hv; simp_all⟩
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st y s1 hS)
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1, fun v hv => by cases hv; rfl⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 y c hS) fun fin _ => ?_
    refine WP.spec_bind (finXN hP hO hA hV h1 (hDO hy) hc (zn_xk (d1 y hy c hc)) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨ecl, h2, k2, hrem⟩
    simp only at ecl hrem
    subst ecl
    have d2 : DomN st D s2 := d1.osk hDO k2
    have o2 : OutK st OS D s s2 := o1.trans (OutK.of_osk k2)
    rcases hrem with rfl | ⟨p, t, n, rfl, hcp, hcov⟩
    · try dsimp only
      first
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]
         exact (WP.spec_ok _).2 ⟨h2, d2, o2, fun v hv => by cases hv; rfl⟩)
      | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]
         exact ⟨h2, d2, o2, fun v hv => by cases hv; rfl⟩)
      | (simp [cdt.cap_removable, WP.spec_ok]; exact ⟨h2, d2, o2⟩)
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_removable.p0 (.Zombie p t n) y)) fun b1 hb1 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h2, d2, o2, fun v hv => by cases hv; rfl⟩
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
    refine WP.spec_bind (JV.setz hO hV h2 (hDO hy) hcp ⟨hDO hp0, fun i hi => hDO (hcov i hi)⟩) ?_
    rintro s3 ⟨h3, k3, c3⟩
    have d3 : DomN st D s3 := DomN.upd d2 fun z hz => by
      by_cases e : z = y
      · right; subst e; intro c' hc'; rw [c3] at hc'; rw [← okinj hc']
        exact Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩)
      · left; exact capk4 k3 (hDO hz) e
    have o3 : OutK st OS D s s3 := o2.trans fun z hz hzD => capk4 k3 hz (fun e => hzD (e ▸ hy))
    refine WP.spec_bind (spec_eqv (P0.cdt.cap_cyclic_zombie.p0 (.Zombie p (t) n) y)) fun b2 hb2 => ?_
    try dsimp only
    split
    · exact (WP.spec_ok _).2 ⟨h3, d3, o3, fun v hv => by cases hv; rfl⟩
    rename_i hcy
    have hpy : p ≠ y := by
      intro e
      have hb := hb2.1
      subst e
      simp [cdt.cap_cyclic_zombie] at hb
      simp_all
    try dsimp only
    try simp only []
    refine WP.spec_bind (cdt.cap_swap_for_delete.zn hO hV hDO hDC h3 d3 hp0 hy hpy) ?_
    rintro s4 ⟨h4, d4, o4⟩
    refine WP.spec_bind (sched.preemption_point.jv hP hO hV h4 (by rw [h4.ksb]; exact hW)) ?_
    rintro ⟨rr, s5, a5⟩ ⟨h5, k5, -⟩
    try simp only [uncurry_apply_pair] at h5 k5 ⊢
    rcases rr with _ | ee
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
      refine (WP.spec_ok _).2 ⟨h5, d4.osk hDO k5, (o3.trans o4).trans (OutK.of_osk k5), ?_⟩
      show fuel1.val < fuel.val
      omega
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h5, d4.osk hDO k5, (o3.trans o4).trans (OutK.of_osk k5), fun v hv => by cases hv⟩
  · exact ⟨h, hD, OutK.refl s⟩

set_option maxHeartbeats 4000000 in
/-- **`delete_deferred` of a slot of a domain `D`**: `JV`, `DomN D`, the `OS` slots outside `D` keep their caps. -/
theorem cdt.delete_deferred.zn {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {y : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomN st D s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomN st D r.2.1 ∧ OutK st OS D s r.2.1 ⦄ := by
  unfold cdt.delete_deferred
  refine WP.spec_bind (cdt.finalise_slot_deferred.zn (a := a) hP hO hA hV hDO hDC hW h hy hD) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, d1, o1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 d1 o1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    · rw [hv1 v rfl]
      refine WP.spec_bind (WP.spec_and (cdt.empty_slot.jv (a := a1) hO hV h1 (hDO hy))
        (cdt.empty_slot.ck (a := a1) hO h1.1.2 (hDO hy))) ?_
      rintro ⟨s2, a2⟩ ⟨h2, k2, c2⟩
      try simp only [uncurry_apply_pair] at h2 k2 c2 ⊢
      refine (WP.spec_ok _).2 ⟨h2, DomN.upd d1 fun z hz => ?_, fun z hz hzD => ?_⟩
      · by_cases e : z = y
        · right; subst e; intro c hc; rw [c2] at hc; rw [← okinj hc]; exact Or.inl zl_null
        · left; exact k2.cap (hDO hz) e
      · rw [k2.cap hz (fun e => hzD (e ▸ hy))]; exact o1 z hz hzD
    · exact (WP.spec_ok _).2 ⟨h1, d1, o1⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 ⟨h1, d1, o1⟩

/-! ## The immediate loop -/

set_option hygiene false in
/-- The preemption-point tail of an immediate round (`JV ∧ DomN ∧ XOK` at `s5`). -/
local macro "ztailN" : tactic => `(tactic| (
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
/-- **`finalise_slot_immediate` of a slot of `OS` whose cap is `XK` over a domain `D`** (module docstring):
`JV` to `JV`, a null cleanup. -/
theorem cdt.finalise_slot_immediate.zn {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomN st D s) (hX : XOK st D x s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ ∀ v, r.1 = .Ok v → v.cleanup = .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧ DomN st D y.1 ∧ XOK st D x y.1)
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
    refine WP.spec_bind (finXN hP hO hA hV h1 hx hc (x1 c hc) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨ecl, h2, k2, hrem⟩
    simp only at ecl hrem
    subst ecl
    have d2 : DomN st D s2 := d1.osk hDO k2
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
    refine WP.spec_bind (JV.setz hO hV h2 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i hi)⟩) ?_
    rintro s3 ⟨h3, k3, c3⟩
    have d3 : DomN st D s3 := DomN.upd d2 fun z hz => by
      by_cases e : z = x
      · right; subst e; intro c' hc'; rw [c3] at hc'; rw [← okinj hc']
        exact Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩)
      · left; exact capk4 k3 (hDO hz) e
    try dsimp only
    first
      | (refine WP.spec_bind (Pₘ := fun i => i = core.num.U64.wrapping_sub n 1#u64) ((WP.spec_ok _).2 rfl)
          fun i hi => ?_; subst hi)
      | simp only [lift, bind_ok]
    refine WP.spec_bind (slot_index_in p _) fun e he => ?_
    subst he
    have heD : slotIdx p (core.num.U64.wrapping_sub n 1#u64) ∈ D := hcov _ (by rw [wsub1 hn0]; omega)
    refine WP.spec_bind (cdt.delete_deferred.zn (a := a2) hP hO hA hV hDO hDC hW h3 heD d3) ?_
    rintro ⟨r4, s4, a4⟩ ⟨h4, d4, o4⟩
    try simp only [uncurry_apply_pair] at h4 d4 o4 ⊢
    have xo4 : XOK st D x s4 := fun c' hc' => by
      by_cases hxD : x ∈ D
      · exact zn_xk (d4 x hxD c' hc')
      · rw [o4 x hx hxD, c3] at hc'
        rw [← okinj hc']
        exact Or.inr (Or.inr (Or.inr ⟨p, _, _, rfl, hcov⟩))
    rcases r4 with _ | ee
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨c4, hc4⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s4 hS)
      rw [hc4, bind_ok]
      try dsimp only
      refine WP.spec_bind (Pₘ := fun y : S × A => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 y.1 ∧
        DomN st D y.1 ∧ XOK st D x y.1) ?_ ?_
      · split
        all_goals first
          | exact (WP.spec_ok _).2 ⟨h4, d4, xo4⟩
          | skip
        split
        · split
          · refine WP.spec_bind (Pₘ := fun s5 => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s5 ∧
              DomN st D s5 ∧ XOK st D x s5) ?_ fun s5 h5 => (WP.spec_ok _).2 h5
            split
            · try simp only [lift, bind_ok]
              refine WP.spec_mono (JV.setz hO hV h4 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i (by
                rw [wsub1 hn0] at hi; omega))⟩) ?_
              rintro s5 ⟨h5, k5, c5⟩
              refine ⟨h5, DomN.upd d4 fun z hz => ?_, fun c' hc' => ?_⟩
              · by_cases e : z = x
                · right; subst e; intro c' hc'; rw [c5] at hc'; rw [← okinj hc']
                  exact Or.inr (Or.inr ⟨p, _, _, rfl, fun i hi => hcov i (by rw [wsub1 hn0] at hi; omega)⟩)
                · left; exact capk4 k5 (hDO hz) e
              · rw [c5] at hc'; rw [← okinj hc']
                exact Or.inr (Or.inr (Or.inr ⟨p, _, _, rfl, fun i hi => hcov i (by rw [wsub1 hn0] at hi; omega)⟩))
            · exact (WP.spec_ok _).2 ⟨h4, d4, xo4⟩
          · exact (WP.spec_ok _).2 ⟨h4, d4, xo4⟩
        · exact (WP.spec_ok _).2 ⟨h4, d4, xo4⟩
      rintro ⟨s5, a5⟩ ⟨h5, d5, x5⟩
      try simp only [uncurry_apply_pair] at h5 d5 x5 ⊢
      try dsimp only
      ztailN
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h4, fun v hv => by cases hv⟩
  · exact ⟨h, hD, hX⟩

set_option maxHeartbeats 4000000 in
/-- **The exposed `cdt.delete` of a slot of `OS` whose cap is `XK` over a domain `D` keeps `JV`.** -/
theorem cdt.delete.zn {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomN st D s) (hX : XOK st D x s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.zn (a := a) hP hO hA hV hDO hDC hW h hx hD hX) ?_
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

/-- **The Zombie kind over a domain**: the exposed `cdt.delete` of `Zombie p t n` whose covered slots lie in a
domain `D` (their caps leaves, CNode or Zombie caps with their slots in `D`) keeps `JV`. -/
theorem cdt.delete.zombieN {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x p t n : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomN st D s)
    (hc : obj.Slot.cap st x s = ok (.Zombie p t n)) (hcov : ∀ i : U64, i.val < n.val → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zn hP hO hA hV hDO hDC hW h hx hD fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inr (Or.inr (Or.inr ⟨p, t, n, rfl, hcov⟩))

/-- **The thread kind over a domain, final or not**: the exposed `cdt.delete` of `Thread p` (`p` not the idle
thread) whose seven TCB slots lie in a domain `D` — e.g. a CSpace-root CNode cap in slot 0 with its CNode's slots in
`D` — keeps `JV`. -/
theorem cdt.delete.threadN {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomN st D s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zn hP hO hA hV hDO hDC hW h hx hD fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩)

/-- **The CNode kind over a domain, final or not**: the exposed `cdt.delete` of `CNode p r g b` whose slots lie in
a domain `D` (CNode caps at any depth, cycles included) keeps `JV`. -/
theorem cdt.delete.cnodeN {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x p r g b : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomN st D s)
    (hc : obj.Slot.cap st x s = ok (.CNode p r g b))
    (hcov : ∀ i : U64, i.val < 2 ^ (r.val % 64) → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zn hP hO hA hV hDO hDC hW h hx hD fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']; exact Or.inr (Or.inr (Or.inl ⟨p, r, g, b, rfl, hcov⟩))

/-- Gen 33's leaf-domain top as a corollary (a leaf domain is a domain), with canonical slots. -/
theorem cdt.delete.zv' {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hW : WuApart OS (L.ksb s0)) {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hD : DomL st D s) (hX : XOK st D x s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zn hP hO hA hV hDO hDC hW h hx hD.toN hX

/-! ## At the decode -/

/-- **The CNode `Delete` of an `XK` target over a domain `D`** (Zombie / thread / CNode / leaf, nested CNode and
Zombie caps in the covered slots), over `JV`. -/
theorem syscall.decode_invocation.del_zn {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {Dm : Set U64} (hDO : Dm ⊆ OS)
    (hDC : DCan Dm)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hW : WuApart OS (L.ksb s)) (hD : DomN st Dm s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => XOK st Dm x s) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ :=
  syscall.decode_invocation.del_genV hO hV a len slot cap blk call don fp buf extra D hT hv hf hslot hcap hk
    fun x hx hkx s1 h1 k1 _ i1 => cdt.delete.zn hP hO hA hV hDO hDC hW h1 hx (hD.osk hDO k1) (hkx.keep hx k1 i1)

/-! ## The VCPU kind over `JV` -/

/-- **`vcpu::finalise`** (`unbind`, then the `Arch` flush, vcpu.rs) over `VcTy`: gen 32's `vcpu.unbind.ubV`. -/
theorem vcpu.finalise.ubV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (v : U64) (hvV : v ∈ Vc) :
    vcpu.finalise st ar s a v ⦃ s' _ => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ∧ DS st T OS Vc s s' ⦄ := by
  unfold vcpu.finalise
  refine WP.spec_bind (vcpu.unbind.ubV hP hO hV h hv a v hvV) ?_
  rintro ⟨s1, a1⟩ F1
  try simp only [WP.uncurry'_pair, uncurry_apply_pair] at F1 ⊢
  refine WP.spec_bind (hP.vcpu_flush_spec a1 v) fun a2 _ => ?_
  exact (WP.spec_ok _).2 F1

set_option maxHeartbeats 2000000 in
/-- **The VCPU kind, any finality, over `JV`**: the finalisation of `Vcpu v` with `v` a VCPU object of the ghost
set `Vc` (a case hypothesis on the deletion's start state, as `ScPlAt` for SCs) ends in `(Null, Null)` and keeps
`JV` (final: `vcpu::finalise` = `unbind` + flush, vcpu.rs; not final: no write). `Vc` is not shrunk: the object
stays a VCPU object (`VcObj`) until it is retyped. No [P] `DelPlaceAt` (gen 27's `fin_vcpuV` used it). -/
theorem finJV_vcpu {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {x v : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hc : obj.Slot.cap st x s = ok (.Vcpu v)) (hvV : v ∈ Vc) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c fin hc'
  rw [hc] at hc'
  obtain rfl := okinj hc'
  rw [fin_cap_eq_obj (by simp)]
  cases fin
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · rename_i hf; exact absurd hf (by simp)
    · exact (WP.spec_ok _).2 ⟨rfl, h⟩
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · refine WP.spec_bind (vcpu.finalise.ubV hP hO hV h.1.1.1 h.2 a v hvV) ?_
      rintro ⟨s1, a1⟩ ⟨F1, D1⟩
      try simp only [WP.uncurry'_pair, uncurry_apply_pair] at F1 D1 ⊢
      exact (WP.spec_ok _).2 ⟨rfl, And.intro (And.intro (And.intro F1.cur (F1.rvi h.1.1.2)) (h.1.2.keep D1.1))
        (h.2.keepZ D1.2)⟩
    · rename_i hf; exact absurd rfl hf

/-- **The exposed `cdt.delete` of a VCPU slot of `OS` keeps `JV`** (any finality; `v ∈ Vc`). -/
theorem cdt.delete.vcpuV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} {x v : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hc : obj.Slot.cap st x s = ok (.Vcpu v))
    (hvV : v ∈ Vc) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.finJV hO hV h hx (finJV_vcpu hP hO hV h hc hvV)

end zn

/-! ## On the entry fact -/

/-- **The Zombie loop over a domain from the entry fact**: at an `EntAt` decode start, under [J] `SlotTyEntZ`, the
restart starts `JV`, and from every state it reaches the exposed `cdt.delete` of a slot of `OS` whose cap is `XK`
over a canonical domain `D ⊆ OS` keeps `JV`. -/
theorem cdt.delete.zn_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntZ st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
        JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 ∧
        ∀ (a : A) (x : U64) (Dm : Set U64), Dm ⊆ OS → DCan Dm → x ∈ OS → DomN st Dm s1 → XOK st Dm x s1 →
          cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄ ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, hO, hT, -, -, hsc, hV, hv, hwu⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, WP.spec_mono (JV.restart hO hV D hT hv) fun s1 h1 =>
    ⟨h1.1, fun a x Dm hDO hDC hx hD hX => cdt.delete.zn hP hO hsc hV hDO hDC hwu h1.1 hx hD hX⟩⟩

/-- **The CNode `Delete` over a domain on [J] `SlotTyEntZ`**: no apartness hypothesis left. -/
theorem syscall.decode_invocation.del_zn_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntZ st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64) (Dm : Set U64),
        Dm ⊆ OS → DCan Dm → DomN st Dm s → capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => XOK st Dm x s) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
            VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, hO, hT, -, -, hA, hV, hv, hW⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, fun a len slot blk call don fp buf Dm hDO hDC hD hf hs hc hk =>
    syscall.decode_invocation.del_zn hP hO hA hV hDO hDC a len slot cap blk call don fp buf extra D hT hv hW hD hf
      hs hc hk⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1

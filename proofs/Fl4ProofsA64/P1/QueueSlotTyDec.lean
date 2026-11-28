/-
P1 (aarch64, gen 30): **the slot-typed deletion lifted to the CNode `Delete` decode** (handoff §33 → §34).

Gen 29 (QueueSlotTy) proved `cdt.delete.triv`: the exposed `cdt.delete` of a slot of the ghost slot set `OS`
holding a cap of a trivial kind (`TrivK`) keeps `J := Cur0R ∧ SlotTy OS`. Here it is lifted to the decode:

* **The restart's footprint misses `OS`** (`sts_fine`, `J.restart`): `set_thread_state t v` writes the TCB
  `STATE` word `t + 3328` and possibly the current core's `SCHED_ACTION` node word (sched.rs `set_thread_state`,
  `schedule_tcb`; Funs.lean 4616–4633). Neither is a `W7.CapW` word (`capw_ne_hi`: a TCB field at offset
  `≥ 224` is neither a TCB low word of a 4096-aligned TCB nor an `Ω` word, `Ω` lying outside the TCBs;
  `capw_ne_node`: a node word is neither, `Ω` lying outside the nodes, `SchedQueuesInvX.omega`). Every word of
  an `OS` slot is `W7.CapW` (`OSOK.slot`), so the restart keeps every `OS` word (`OSKeep`), hence `SlotTy` and
  the target's cap.
* **The lookup target is in `OS`** (`resolve_in`, `lookup_tgt_in`): `resolve_address_bits` (cspace.rs 28–64)
  from a root cap with `CapIn OS` and a radix below 64 (`RootOK`) returns a slot of `OS`. Each step's slot is
  `slotIdx ptr (… &&& mask radix)`, an index below `2 ^ radix` of the current CNode cap, in `OS` by `CapIn`; the
  next CNode cap is read from that `OS` slot, so `SlotTy` gives its `CapIn`, and `Cap::decode` gives its radix
  `< 64` (`decode_rad`: the radix is `(w0 >> 48) & 63`, capability.rs).
* **Decode-level tops** (no named premise): `cnode_del_ty` (restart then `cdt.delete`), `cnode.decode.del_ty`
  (`cnode.decode` at label `CNodeDelete`), `syscall.decode_invocation.del_ty` (the CNode family, invoked slot
  in `OS`), each with post `DecPost ∧ SlotTy OS`. The case hypothesis is `TgtTriv`: the slot the lookup
  returns at the decode start holds a `TrivK` cap.
* **On the entry fact**: `syscall.decode_invocation.del_ent` takes [J] `SlotTyEnt` (gen 29) at an `EntAt`
  state and gives the decode top for the `OS` it provides.
* **[J] `SlotTyEntT`** (new, named): `SlotTyEnt` plus `cover`: every TCB of `T` has its first cap slot (offset
  0, the CSpace root) in `OS`. It implies `SlotTyEnt` (`SlotTyEntT.toEnt`, a field dropped). It is stated at
  `P3Ok` states only, over the ghost TCB set `T`, not over a word class (gen 28's trick needs a premise stated
  at every `Fr0 ∧ BXI` state; this one is not). Source: `OS` read as the live CNode / TCB / IRQ-node slots
  (QueueSlotTy's docstring); a TCB's seven slots are live while the TCB is (objects.rs `create_new_objects`
  zeroes them, so `Null` with null links; `layout::tcb::SLOT_CTABLE` = 0, arch/aarch64/layout.rs:12).
* **Non-vacuity on a kernel-reached state** (`J.witness_ent`): from any `EntAt` state `s` with `DecPre`,
  under `SlotTyEntT`, the kernel's own restart (`set_thread_state … TS_RESTART`) and then its own `empty_slot`
  of the caller's CSpace-root slot (the clearing half of `cdt.delete`) reach a state where `J` holds, the slot
  is in `OS` and holds `Null`, so every premise of `cdt.delete.triv` holds at a state reached from an `EntAt`
  state by kernel code (no arbitrary write).

Named premises: [J] `SlotTyEntT` (new, docstring above); [J] `SlotTyEnt` (gen 29). No existing statement
changed.
-/
import Fl4ProofsA64.P1.QueueSlotTy
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

/-! ## Cap-slot words are not TCB high fields or node words -/

theorem tcb4096 {t : U64} (h : TcbAddr t) : t.val % 4096 = 0 := by
  have := h.align; simpa using this

/-- A `W7.CapW` word is no TCB field at offset `≥ 224`. -/
theorem capw_ne_hi {s : S} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) {b t K : U64} (hb : W7.CapW T Ω Sg b) (ht : t ∈ T)
    (hK : 224 ≤ K.val) (hK2 : K.val < 4096) : b ≠ wa t K := by
  intro e
  subst e
  rcases hb with ⟨t', ht', K', hK', e'⟩ | ⟨hΩ, -⟩
  · have h1 := field_val (q.tcbs t ht) hK2
    have h2 := field_val (q.tcbs t' ht') (by omega : K'.val < 4096)
    have hv := congrArg UScalar.val e'
    rw [h1, h2] at hv
    have a1 := tcb4096 (q.tcbs t ht)
    have a2 := tcb4096 (q.tcbs t' ht')
    omega
  · exact out_ne_field (q.omega _ hΩ) ht (q.tcbs t ht) hK2 rfl

/-- A `W7.CapW` word is no word of a node of `Cs`. -/
theorem capw_ne_node {s : S} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R) {b c o : U64} (hb : W7.CapW T Ω Sg b) (hc : c ∈ Cs)
    (ho : o.val < 4288) : b ≠ L.nodeAt s c o := by
  intro e
  subst e
  rcases hb with ⟨t', ht', K', hK', e'⟩ | ⟨hΩ, -⟩
  · exact node_ne_field (q.nodes c hc) ho ht' (q.tcbs t' ht') (by omega) e'
  · exact out_ne_node (q.omega _ hΩ) hc (q.nodes c hc) ho rfl

/-! ## Words of `OS` kept -/

/-- Every word of every `OS` slot is the same at `s'` as at `s`. -/
def OSKeep (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s s' : S) : Prop :=
  ∀ y ∈ OS, L.mem s' y = L.mem s y ∧ L.mem s' (wa y 8#u64) = L.mem s (wa y 8#u64) ∧
    L.mem s' (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s' (wa y 24#u64) = L.mem s (wa y 24#u64)

theorem OSKeep.of_writes {OS : Set U64} (hO : OSOK T Ω Sg OS) {s s' : S} {F : U64 → Prop}
    (hw : WritesIn st s s' F) (hF : ∀ b, W7.CapW T Ω Sg b → ¬ F b) : OSKeep st OS s s' := fun y hy =>
  ⟨hw.mem_eq (hO.al0 hy) (hF _ (hO.cw0 hy)),
   hw.mem_eq (hO.al hy (by simp) (by simp)) (hF _ (hO.cw hy (by simp) (by simp))),
   hw.mem_eq (hO.al hy (by simp) (by simp)) (hF _ (hO.cw hy (by simp) (by simp))),
   hw.mem_eq (hO.al hy (by simp) (by simp)) (hF _ (hO.cw hy (by simp) (by simp)))⟩

theorem SlotTy.keep {OS : Set U64} {s s' : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (k : OSKeep st OS s s') :
    SlotTy st T Ω Sg H Rp Nt OS s' := fun y hy =>
  (hT y hy).of_eq (k y hy).1 (k y hy).2.1 (k y hy).2.2.1 (k y hy).2.2.2

theorem CapTrivAt.keep {OS : Set U64} {s s' : S} {x : U64} (hk : CapTrivAt st x s) (k : OSKeep st OS s s')
    (hx : x ∈ OS) : CapTrivAt st x s' := by
  intro c hc
  rw [DPF.slot_cap_dec, (k x hx).1, (k x hx).2.1, ← DPF.slot_cap_dec] at hc
  exact hk c hc

/-! ## The restart's footprint -/

/-- **`set_thread_state t v`** writes `t`'s `STATE` word and at most the current core's `SCHED_ACTION` word. -/
theorem sts_fine (s : S) (t v : U64) (hN : NodePlaced st T s (L.cpu s)) (ht : TcbAddr t) :
    sched.set_thread_state st s t v ⦃ s' => WritesIn st s s'
      (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) ⦄ := by
  unfold sched.set_thread_state
  refine WP.spec_bind (obj.Tcb.set_state.spec s t v) fun s1 e1 => ?_
  subst e1
  have ha : Aligned (stA t) := by rw [stA_eq]; exact field_aligned ht (by simp) (by simp)
  have w1 : WritesIn st s (L.wr s (stA t) v)
      (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
    (writesIn_wr ha).mono fun b h => Or.inl h
  have hN1 : NodePlaced st T (L.wr s (stA t) v) (L.cpu (L.wr s (stA t) v)) := by
    rw [LawfulStore.cpu_wr]; exact hN.ksb (L.ksb_wr _ _ _)
  have h16 : layout.node.SCHED_ACTION.val < 4288 := by rw [act_val]; omega
  have h8 : layout.node.SCHED_ACTION.val % 8 = 0 := by rw [act_val]
  unfold sched.schedule_tcb
  refine WP.spec_bind (sched.cur_thread.spec _) fun t1 _ => ?_
  refine WP.spec_bind (tcb_eq.blk t t1) fun b _ => ?_
  split
  · refine WP.spec_bind (sched.action.spec _) fun i _ => ?_
    split
    · refine WP.spec_bind (sched.is_schedulable.spec _ t) fun b1 _ => ?_
      split
      · exact (WP.spec_ok _).2 w1
      · refine WP.spec_mono (sched.set_action.spec _ _) fun s' e => ?_
        subst e
        refine (w1.trans (writesIn_wr (nodeAt_aligned hN1 h16 h8))).mono ?_
        rintro b (h | h)
        · exact h
        · right; rw [h, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
    · exact (WP.spec_ok _).2 w1
  · exact (WP.spec_ok _).2 w1

/-- **The decode's restart keeps every `OS` word** and starts `J`. -/
theorem J.restart {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra)
    (hT : SlotTy st T Ω Sg H Rp Nt OS s) :
    sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
      J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s s1 ∧ OSKeep st OS s s1 ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  have hct : L.curW s ∈ T := q.curT
  refine WP.spec_mono (WP.spec_and (Cur0R.restart D) (sts_fine s _ sched.TS_RESTART (q.nodes _ q.cur)
    (q.tcbs _ hct))) fun s1 hh => ?_
  have k : OSKeep st OS s s1 := OSKeep.of_writes hO hh.2 fun b hb hF => by
    rcases hF with e | e
    · rw [stA_eq] at e
      exact capw_ne_hi q hb hct (K := 3328#u64) (by simp) (by simp) e
    · exact capw_ne_node q hb q.cur (by rw [act_val]; omega) e
  exact ⟨⟨hh.1, hT.keep k⟩, k⟩

/-! ## CNode `Delete` of a trivial-kind slot -/

/-- **The restart, then the exposed `cdt.delete` of a trivial-kind slot of `OS`** keeps the invariants
(`DecPost`) and `SlotTy`. -/
theorem cnode_del_ty {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S} {a : A}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hx : x ∈ OS) (hk : CapTrivAt st x s) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.delete st ar s1 a x true) ⦃ r s' _ =>
        DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ :=
  WP.spec_bind (J.restart hO D hT) fun s1 h1 =>
    WP.spec_mono (cdt.delete.triv (ar := ar) (a := a) hO h1.1 hx (hk.keep h1.2 hx)) fun r hr => by
      obtain ⟨r', s', a'⟩ := r; exact ⟨hr.1.post, hr.2⟩

/-! ## The lookup stays in `OS` -/

/-- A lookup root: its slots in `OS` and, for a CNode cap, a radix below 64. -/
def RootOK (OS : Set U64) (c : capability.Cap) : Prop :=
  CapIn OS c ∧ ∀ p r g b, c = .CNode p r g b → r.val < 64

theorem and63 (x : U64) : (x &&& 63#u64).val < 64 := by
  rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem shr_tot (x : U64) (k : I32) (h0 : 0 ≤ k.val) (h : k.val < 64) : x >>> k ⦃ _ => True ⦄ := by
  rw [DPF.shr_eq x k h0 h]; exact (WP.spec_ok _).2 trivial

set_option maxHeartbeats 4000000 in
/-- `Cap::decode` gives a CNode radix below 64 (`(w0 >> 48) & 63`). -/
theorem decode_rad' (w0 w1 : U64) :
    capability.Cap.decode w0 w1 ⦃ c => ∀ p r g b, c = .CNode p r g b → r.val < 64 ⦄ := by
  unfold capability.Cap.decode
  simp only [lift, bind_ok]
  refine WP.spec_bind (shr_tot _ _ (by decide) (by decide)) fun t _ => ?_
  refine WP.spec_bind (Fl4ProofsA64.P0.capability.unpack_ptr.p0 w0) fun p _ => ?_
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
    | (rw [WP.spec_ok]; intro p r g b h; cases h; done)
    | (rw [WP.spec_ok]; intro p r g b h; cases h; exact and63 _)
    | (simp only [WP.spec_ok]; intro p r g b h; cases h; done)
    | (simp only [WP.spec_ok]; intro p r g b h; cases h; exact and63 _)
    | skip

theorem decode_rad {w0 w1 p r g b : U64} (h : capability.Cap.decode w0 w1 = ok (.CNode p r g b)) :
    r.val < 64 := by
  have := decode_rad' w0 w1
  rw [h, WP.spec_ok] at this
  exact this p r g b rfl

theorem mask_val (bits : U64) (h : bits.val < 64) :
    cspace.mask bits ⦃ m => m.val = 2 ^ bits.val - 1 ⦄ := by
  unfold cspace.mask
  have : ¬ (bits ≥ 64#u64) := by scalar_tac
  simp only [this, ite_false, lift, bind_ok]
  step*
  have h63 : (bits &&& 63#u64).val = bits.val := by
    have : (bits &&& 63#u64).val = bits.val % 64 := by
      simp; exact Nat.and_two_pow_sub_one_eq_mod bits.val 6
    omega
  have hp : 2 ^ bits.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) h
  have hp1 : 1 ≤ 2 ^ bits.val := Nat.one_le_two_pow
  have hi : i1.val = 2 ^ bits.val := by
    rw [i1_post, h63]
  simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi]
  omega

theorem and_lt_pow {x m : U64} {r : Nat} (hm : m.val = 2 ^ r - 1) : (x &&& m).val < 2 ^ r := by
  rw [UScalar.val_and]
  have := Nat.and_le_right (n := x.val) (m := m.val)
  have := Nat.one_le_two_pow (n := r)
  omega

theorem slot_index_in (p i : U64) : obj.Slot.index p i ⦃ sl => sl = slotIdx p i ⦄ := by
  unfold obj.Slot.index slotIdx
  simp only [lift, bind_ok, WP.spec_ok, cte_size]

set_option hygiene false in
local macro "lf_err" : tactic => `(tactic| first
  | (simp only [WP.spec_ok]; done)
  | (simp only [WP.spec_ok]; intro x hx; cases hx; done)
  | (rw [WP.spec_ok]; intro x hx; cases hx; done)
  | (simp [WP.spec_ok]; done))

set_option maxHeartbeats 4000000 in
/-- One step of `resolve_address_bits`: a resolved slot is in `OS`; a next CNode cap is a `RootOK` root. -/
theorem body_in {OS : Set U64} {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (cptr : U64) (c : capability.Cap)
    (n fuel : U64) (hc : RootOK OS c) :
    cspace.resolve_address_bits_loop.body st s cptr c n fuel ⦃ r =>
      match r with
      | .done y => ∀ x, y = .Ok x → x.slot ∈ OS
      | .cont x' => RootOK OS x'.1 ∧ x'.2.2.val < fuel.val ⦄ := by
  have hS : P0.StoreTotal st := L.total
  cases c
  case CNode ptr radix gs guard =>
    obtain ⟨hin, hr⟩ := hc
    have hr64 : radix.val < 64 := hr _ _ _ _ rfl
    unfold cspace.resolve_address_bits_loop.body
    step as ⟨level, hlev⟩
    split
    · lf_err
    split
    · lf_err
    rename_i hf
    have hf' : 0 < fuel.val := by
      rcases Nat.eq_zero_or_pos fuel.val with h0 | h0
      · exact absurd (UScalar.eq_of_val_eq (by simp [h0])) hf
      · exact h0
    step as ⟨fuel1, hf1⟩
    step as ⟨i, hi⟩
    step as ⟨shift, hsh⟩
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    step as ⟨g, hg⟩
    split
    · lf_err
    split
    · lf_err
    split
    · lf_err
    step as ⟨i3, hi3⟩
    step as ⟨i4, hi4⟩
    step as ⟨i5, hi5⟩
    step with mask_val as ⟨i6, hi6⟩
    step as ⟨offset, hoff⟩
    step with slot_index_in as ⟨slot, hslot⟩
    have hslotO : slot ∈ OS := by
      rw [hslot]
      refine hin.1 ptr radix gs guard rfl offset ?_
      rw [Nat.mod_eq_of_lt hr64, hoff]
      exact and_lt_pow hi6
    split
    · simp only [WP.spec_ok]; rintro x ⟨⟩; exact hslotO
    refine WP.spec_bind (spec_eqv (P0.obj.Slot.cap.p0 st slot s hS)) fun nc hnc' => ?_
    have hnc := hnc'.1
    cases nc
    case CNode p' r' g' b' =>
      rw [WP.spec_ok]
      show RootOK OS (.CNode p' r' g' b') ∧ fuel1.val < fuel.val
      have hd : capability.Cap.decode (L.mem s slot) (L.mem s (wa slot 8#u64)) = ok (.CNode p' r' g' b') := by
        rw [← DPF.slot_cap_dec]; exact hnc
      refine ⟨⟨((hT slot hslotO).1 _ hd).2, fun p r g b e => by cases e; exact decode_rad hd⟩, ?_⟩
      omega
    all_goals (simp only [WP.spec_ok]; rintro x ⟨⟩; exact hslotO)
  all_goals (unfold cspace.resolve_address_bits_loop.body; lf_err)

/-- **`resolve_address_bits` from a `RootOK` root returns a slot of `OS`.** -/
theorem resolve_in {OS : Set U64} {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (c : capability.Cap)
    (hc : RootOK OS c) (cptr n : U64) :
    cspace.resolve_address_bits st s c cptr n ⦃ r => ∀ x, r = .Ok x → x.slot ∈ OS ⦄ := by
  unfold cspace.resolve_address_bits cspace.resolve_address_bits_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val) (inv := fun x => RootOK OS x.1)
  · rintro ⟨c1, n1, f1⟩ hx
    first
    | exact body_in hT cptr c1 n1 f1 hx
    | (have h := body_in hT cptr c1 n1 f1 hx
       convert h using 2
       rename_i r; cases r <;> rfl)
  · exact hc

set_option maxHeartbeats 2000000 in
/-- (gen 51) **The CNode operations' lookup (`lookupSlotForCNodeOp`, source / target / pivot) returns a slot of
`OS`** from a `RootOK` root (gen 30's `lookup_tgt_in`'s proof, moved; that lemma is its `false` instance). -/
theorem lookup_op_in {OS : Set U64} {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (b0 : Bool) (c : capability.Cap)
    (hc : RootOK OS c) (i d : U64) :
    cspace.lookup_slot_for_cnode_op st s b0 c i d ⦃ r => ∀ x, r = .Ok x → x ∈ OS ⦄ := by
  unfold cspace.lookup_slot_for_cnode_op
  refine WP.spec_bind (Pₘ := fun _ => True) (by cases c <;> simp [WP.spec_ok]) fun b _ => ?_
  split
  · split
    · lf_err
    split
    · lf_err
    refine WP.spec_bind (resolve_in hT c hc i d) fun r hr => ?_
    rcases r with r1 | lf
    · dsimp only
      split
      · lf_err
      · rw [WP.spec_ok]; intro x hx; cases hx; exact hr r1 rfl
    · dsimp only
      lf_err
  · lf_err

/-- **The CNode operations' target lookup returns a slot of `OS`** from a `RootOK` root. -/
theorem lookup_tgt_in {OS : Set U64} {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (c : capability.Cap)
    (hc : RootOK OS c) (i d : U64) :
    cspace.lookup_target_slot st s c i d ⦃ r => ∀ x, r = .Ok x → x ∈ OS ⦄ :=
  lookup_op_in hT false c hc i d

/-! ## The CNode decode at `CNodeDelete` -/

/-- **The case hypothesis**: the slot the CNode lookup returns at the decode start holds a trivial-kind cap. -/
def TgtTriv (st : machine.Store S) [L : LawfulStore st] (s : S) (c : capability.Cap) (buf : U64) : Prop :=
  ∀ i d x, msg.syscall_arg st s (L.curW s) buf 0#u64 = ok i → msg.syscall_arg st s (L.curW s) buf 1#u64 = ok d →
    cspace.lookup_target_slot st s c i d = ok (.Ok x) → CapTrivAt st x s

theorem lbl_c1 : ¬ (fl4_abi.label.CNodeDelete ≥ fl4_abi.label.CNodeCopy) := by
  unfold fl4_abi.label.CNodeDelete fl4_abi.label.CNodeCopy; decide
theorem lbl_c2 : ¬ (fl4_abi.label.CNodeDelete = fl4_abi.label.CNodeRevoke) := by
  unfold fl4_abi.label.CNodeDelete fl4_abi.label.CNodeRevoke; decide

set_option hygiene false in
local macro "eleaf" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 ⟨D.err _, hT⟩
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     exact (WP.spec_ok _).2 ⟨D.err _, hT⟩))

set_option maxHeartbeats 4000000 in
/-- **`cnode.decode` at `CNodeDelete`** of a `RootOK` root, the target trivial (`TgtTriv`): `DecPost` and
`SlotTy`. -/
theorem cnode.decode.del_ty {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (len buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (c : capability.Cap) (hc : RootOK OS c) (hk : TgtTriv st s c buf) :
    cnode.decode st ar s a fl4_abi.label.CNodeDelete len c buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · eleaf
  split
  · eleaf
  split
  · eleaf
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (spec_eqv (P0.msg.syscall_arg.p0 st s _ buf _ hS)) fun idx hidx => ?_
  refine WP.spec_bind (spec_eqv (P0.msg.syscall_arg.p0 st s _ buf _ hS)) fun dep hdep => ?_
  refine WP.spec_bind (WP.spec_and (lookup_tgt_in hT c hc idx dep)
    (spec_eqv (P0.cspace.lookup_target_slot.p0 st s c idx dep hS))) fun r hr => ?_
  rcases r with v | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    eleaf
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  split
  · rename_i h; exact absurd h lbl_c1
  split
  · rename_i h; exact absurd h lbl_c2
  split
  · exact cnode_del_ty hO D hT (hr.1 v rfl) (hk idx dep v hidx.1 hdep.1 hr.2.1)
  · rename_i h; first | exact absurd rfl h | exact absurd trivial h | simp at h

/-- A cap read from a slot of `OS` is a `RootOK` root. -/
theorem RootOK.of_slot {OS : Set U64} {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) {y : U64}
    {c : capability.Cap} (hy : y ∈ OS) (hc : obj.Slot.cap st y s = ok c) : RootOK OS c := by
  have hd : capability.Cap.decode (L.mem s y) (L.mem s (wa y 8#u64)) = ok c := by
    rw [← DPF.slot_cap_dec]; exact hc
  exact ⟨((hT y hy).1 _ hd).2, fun p r g b e => by subst e; exact decode_rad hd⟩

set_option maxHeartbeats 2000000 in
/-- **The CNode `Delete` invocation, decode level**: the invoked cap read from a slot of `OS`, the target
trivial (`TgtTriv`): `decode_invocation` keeps the invariants and `SlotTy`. No named premise. -/
theorem syscall.decode_invocation.del_ty {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtTriv st s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  have hR := RootOK.of_slot hT hslot hcap
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 ⟨DecPost.keep D.bxi (by simp), hT⟩
  · exact cnode.decode.del_ty hO a len buf D hT _ hR hk

/-- **On the entry fact** ([J] `SlotTyEnt`): at an `EntAt` decode start there is a placed, typed `OS` for which
the CNode `Delete` of a trivial-kind target keeps the invariants and `SlotTy`. -/
theorem syscall.decode_invocation.del_ent {A : Type _} {ar : machine.Arch A}
    (hJ : SlotTyEnt st T Ω Sg H Rp Nt P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64),
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap → TgtTriv st s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  obtain ⟨OS, hO, hT⟩ := hJ.entAt hE
  exact ⟨OS, hO, hT, fun a len slot blk call don fp buf hf hs hc hk =>
    syscall.decode_invocation.del_ty hO a len slot cap blk call don fp buf extra D hT hf hs hc hk⟩

/-! ## The entry fact with the TCB root slots, and the witness -/

/-- **[J] (a64) `SlotTyEntT`** (module docstring): `SlotTyEnt` and every TCB's first cap slot (its CSpace root,
`SLOT_CTABLE` = 0) in `OS`. At `P3Ok` states only; over the ghost TCB set, not a word class. -/
def SlotTyEntT (st : machine.Store S) [L : LawfulStore st] (T Ω Sg : Set U64) (H : Heap) (Rp Nt : Set U64)
    (P3Ok : S → Prop) : Prop :=
  ∀ e, P3Ok e → ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS e ∧ EntApart st e OS ∧ ∀ t ∈ T, t ∈ OS

/-- `SlotTyEntT` implies `SlotTyEnt` (a field dropped). -/
theorem SlotTyEntT.toEnt (h : SlotTyEntT st T Ω Sg H Rp Nt P3Ok) : SlotTyEnt st T Ω Sg H Rp Nt P3Ok :=
  fun e he => by obtain ⟨OS, a, b, c, -⟩ := h e he; exact ⟨OS, a, b, c⟩

theorem SlotTyEntT.entAt (hJ : SlotTyEntT st T Ω Sg H Rp Nt P3Ok) {s : S} (hE : EntAt st P3Ok s) :
    ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ ∀ t ∈ T, t ∈ OS := by
  obtain ⟨e, he, hw⟩ := hE
  obtain ⟨OS, hO, hT, hA, hc⟩ := hJ e he
  refine ⟨OS, hO, fun y hy => ?_, hc⟩
  obtain ⟨v8, v16, v24⟩ := vals hO hy
  have k : ∀ b, Aligned b → y.val ≤ b.val → b.val < y.val + 32 → L.mem s b = L.mem e b :=
    fun b hb h1 h2 => hw.mem_eq hb fun hb' => hA b hb' y hy ⟨h1, h2⟩
  exact (hT y hy).of_eq (k _ (hO.al0 hy) (by omega) (by omega)) (k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega))
    (k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega)) (k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega))

set_option maxHeartbeats 2000000 in
/-- `empty_slot` of a slot of `OS` with a null cleanup keeps `J` and leaves the slot `Null`. -/
theorem cdt.empty_slot.tyN {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {s0 s : S} {a : A} {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hx : x ∈ OS) :
    cdt.empty_slot st ar s a x .Null ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.1 ∧
      obj.Slot.cap st x r.1 = ok .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.empty_slot
  refine WP.spec_bind (spec_eqv (P0.obj.Slot.cap.p0 st x s hS)) fun c0 hc0 => ?_
  refine WP.spec_bind (spec_eqv (P0.capability.Cap.is_null.p0 c0)) fun bn hbn => ?_
  split
  · rename_i hb
    subst hb
    have e0 : c0 = .Null := by
      have hb1 := hbn.1
      cases c0 <;> first | rfl | (exfalso; unfold capability.Cap.is_null at hb1; have := okinj hb1; cases this)
    exact (WP.spec_ok _).2 ⟨h, e0 ▸ hc0.1⟩
  have hxo := h.2 x hx
  obtain ⟨nx, hnx⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s (wa x 24#u64)))
  have hnl : LinkOK OS nx := hxo.2.2 nx hnx
  have hni : obj.sext48 nx = ok nx := sx_idem _ _ hnx
  have hpv : LinkOK OS (L.mem s (wa x 16#u64)) := hxo.2.1
  rw [slot_prev_eq, bind_ok, slot_next_of hnx, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s1) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 h
    · rename_i hp0
      have hpO : L.mem s (wa x 16#u64) ∈ OS := hpv.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact J.next hO h hpO hnl hni
  refine WP.spec_bind (Pₘ := fun s2 => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s2) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnO : nx ∈ OS := hnl.resolve_left (by simpa using hn0)
      rw [set_prev_eq, bind_ok]
      have h3 := J.prev hO h1 hnO hpv
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx _ hS) fun nfb _ => ?_
      split
      · rw [set_fb_eq_t, WP.spec_ok]; exact J.fb hO h3 hnO (Or.inr rfl)
      · cases fb
        · rw [set_fb_eq_f, WP.spec_ok]; exact J.fb hO h3 hnO (Or.inl rfl)
        · rw [set_fb_eq_t, WP.spec_ok]; exact J.fb hO h3 hnO (Or.inr rfl)
  rw [clear_eq, bind_ok, pcd_null, WP.spec_ok]
  refine ⟨J.clear hO h2 hx, ?_⟩
  have a0 := hO.al0 hx
  have a8 := hO.al hx (k := 8#u64) (by simp) (by simp)
  have a16 := hO.al hx (k := 16#u64) (by simp) (by simp)
  have a24 := hO.al hx (k := 24#u64) (by simp) (by simp)
  obtain ⟨v8, v16, v24⟩ := vals hO hx
  rw [DPF.slot_cap_dec, L.mem_wr_ne a24 a0 (by omega), L.mem_wr_ne a16 a0 (by omega), L.mem_wr_ne a8 a0 (by omega),
    L.mem_wr_same a0, L.mem_wr_ne a24 a8 (by omega), L.mem_wr_ne a16 a8 (by omega), L.mem_wr_same a8, decode_zero]

/-- **Non-vacuity on a kernel-reached state**: at any `EntAt` decode start with `DecPre`, under [J]
`SlotTyEntT`, the kernel's restart and then its `empty_slot` of the caller's CSpace-root slot reach a state
where `J` holds and that slot (in `OS`) holds `Null`: every premise of `cdt.delete.triv` holds there. -/
theorem J.witness_ent {A : Type _} {ar : machine.Arch A} (hJ : SlotTyEntT st T Ω Sg H Rp Nt P3Ok) {s : S}
    (hE : EntAt st P3Ok s) {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (a : A) :
    ∃ OS, OSOK T Ω Sg OS ∧ L.curW s ∈ OS ∧
      (do
        let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
        cdt.empty_slot st ar s1 a (L.curW s) .Null) ⦃ r =>
          J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s r.1 ∧ CapTrivAt st (L.curW s) r.1 ∧
            obj.Slot.cap st (L.curW s) r.1 = ok .Null ⦄ := by
  obtain ⟨OS, hO, hT, hc⟩ := hJ.entAt hE
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have hx : L.curW s ∈ OS := hc _ hct
  refine ⟨OS, hO, hx, WP.spec_bind (J.restart hO D hT) fun s1 h1 =>
    WP.spec_mono (cdt.empty_slot.tyN (ar := ar) (a := a) hO h1.1 hx) fun r hr => ⟨hr.1, fun c hc' => ?_, hr.2⟩⟩
  rw [hr.2] at hc'
  rw [← okinj hc']
  exact Or.inl rfl

end ST
end R
end W7

end

end Fl4ProofsA64.P1

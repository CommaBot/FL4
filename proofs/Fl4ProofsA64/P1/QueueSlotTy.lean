/-
P1 (aarch64, gen 29): **the slot typing carried as a state invariant** (`SlotTy`), the redesign gen 28 asked
for (handoff §32–§33), and the first deletion top over it.

Gen 28 (QueueDelPlaceFalse) and gen 29 (QueueSlotFieldsFalse) refuted every slot field of every `DelPlaceAt` /
`DelGapsAt`: each is stated at every `Fr0 ∧ BXI` state, and `Fr0` lets every cap-slot word change. Here the
typing is a predicate of **one store over a ghost set of actual slots**, carried along the deletion with the
step relation, as x86's P3 carries `JPlaced.typed` over the typed heap's slots (`AbsSlot`):

* `OSOK OS`: the ghost `OS` is a set of cap-slot base addresses (the slots of live CNodes, the seven slots of
  each TCB, the IRQ node's slots), each a `W7.SlotW` slot (its four words `W7.CapW`), not wrapping, pairwise
  disjoint (32 bytes each), none at address 0 (`nz`, gen 49). State-independent.
* `SlotOK OS s x` (one slot): its cap decodes to a cap typed for deletion with the **A64 IRQ bound true on GIC**
  (`W7.R.A5.I.DelCapOK`, IRQ `< 5376`) whose CNode / Zombie slots lie in `OS` (`CapIn`); its `PREV` word is `0`
  or a slot of `OS`; its `NEXT` word's 48-bit pointer (`sext48`) is `0` or a slot of `OS`.
* **`SlotTy OS s`**: `SlotOK OS s x` for every `x ∈ OS`.

The step relation of the deletion becomes `Cur0R s0 s ∧ SlotTy OS s` (`J`). Proved here, no premise:

* the store facts of the MDB words (`set_next_eq`, `set_prev_eq`, `set_fb_eq_t/f`, `clear_eq`, `sext48`
  idempotence `sx_idem`, masking `sx_mask`, the link and flag bit lemmas `link_bits`, `fb_bits`);
* `SlotTy.frame` (other slots' words kept and the written slot `SlotOK`), `J.next` / `J.prev` / `J.fb` /
  `J.clear` (each MDB write of `empty_slot` keeps `J`);
* **`cdt.empty_slot.ty`**: `empty_slot` of a slot of `OS` with a null cleanup keeps `J`;
* `TrivK` (the kinds whose `finalise_cap` changes nothing and leaves `(Null, Null)`: `Null`, `Untyped`,
  `IrqControl`, `Domain`, `SchedControl`, `AsidControl`, `IoPortControl`, `TdxControl`, and unmapped
  `PageTable` / `PageDirectory` / `Pdpt` / `Pml4` / `HighVSpace` caps, final or not), `finalise_cap.triv`,
  `cdt.finalise_slot_immediate.triv`;
* **`cdt.delete.triv`** (the first deletion top over `SlotTy`): the exposed `cdt.delete` of a slot of `OS` whose
  cap is of a `TrivK` kind keeps `Cur0R` and `SlotTy`. It covers exactly the `TrivK` kinds;
* **`J.witness`**: non-vacuity. From any `Cur0R` state (e.g. the one `Cur0R.restart` gives at every decode
  start) and any thread `t ∈ T`, one writes a `Domain` cap with null links into `t`'s first cap slot (four
  `W7.CapW` words) and gets a state with `Cur0R`, `OSOK {t}`, `SlotTy {t}` and a `TrivK` cap in `t`: every
  premise of `cdt.delete.triv` holds together.

The entry fact is **[J] `SlotTyEnt`** (named, a definition; not a premise of any theorem here, consumed only by
`SlotTyEnt.entAt`): at every `P3Ok` kernel entry state `e` there is an `OS` with `OSOK OS`, `SlotTy OS e` and no
word of an `OS` slot written by the entry prefix (`EntW e`: the current thread's `FAULT_IP` register at TCB
offset ≥ 256, outside the seven slots below 224, and the current core's node at `ks + 223488 + 4288·cpu`,
above the IRQ node `ks + 43232 … ks + 215264`). It is stated at the `P3Ok` state only, not over a word class,
so gen 28's trick does not apply. `SlotTyEnt.entAt` carries it to every `EntAt` state.

No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueSlotFieldsFalse
import Fl4ProofsA64.P1.QueueIrqWideA5
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop}

namespace W7
namespace R
namespace ST

local notation "wa" => core.num.U64.wrapping_add

/-! ## Bit facts of the MDB words -/

theorem okinj {α : Type _} {x y : α} (h : (ok x : Result α) = ok y) : x = y := by
  have h2 := spec_of_eq_fd h; rw [WP.spec_ok] at h2; exact h2

theorem or_and_eq (x y m : U64) (hy : y &&& m = 0#u64) : (x ||| y) &&& m = x &&& m := by
  rw [UScalar.eq_equiv_bv_eq] at hy ⊢
  apply BitVec.eq_of_getLsbD_eq; intro i
  have h1 := congrArg (fun z => BitVec.getLsbD z i) hy
  simp only [UScalar.bv_and, UScalar.bv_or, BitVec.getLsbD_and, BitVec.getLsbD_or] at h1 ⊢
  revert h1
  cases x.bv.getLsbD i <;> cases y.bv.getLsbD i <;> cases m.bv.getLsbD i <;> simp

theorem and_and_self' (x m : U64) : (x &&& m) &&& m = x &&& m := by
  rw [UScalar.eq_equiv_bv_eq]
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [UScalar.bv_and, BitVec.getLsbD_and]
  cases x.bv.getLsbD i <;> cases m.bv.getLsbD i <;> simp

theorem link_bits (a n : U64) :
    (((a &&& ~~~ obj.MDB_PTR_MASK) ||| (n &&& obj.MDB_PTR_MASK)) &&& obj.MDB_PTR_MASK) = (n &&& obj.MDB_PTR_MASK) := by
  rw [UScalar.eq_equiv_bv_eq]
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not]
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not]
  cases a.bv.getLsbD i <;> cases n.bv.getLsbD i <;> cases obj.MDB_PTR_MASK.bv.getLsbD i <;> simp

theorem fb_bits (w v F M : U64) (hv : v &&& M = 0#u64) (hF : ~~~F &&& M = M) :
    ((w &&& ~~~F) ||| v) &&& M = w &&& M := by
  rw [UScalar.eq_equiv_bv_eq] at hv hF ⊢
  apply BitVec.eq_of_getLsbD_eq; intro i
  have h1 := congrArg (fun x => BitVec.getLsbD x i) hv
  have h2 := congrArg (fun x => BitVec.getLsbD x i) hF
  simp only [UScalar.bv_and, UScalar.bv_or, UScalar.bv_not, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not] at h1 h2 ⊢
  revert h1 h2
  cases w.bv.getLsbD i <;> cases v.bv.getLsbD i <;> cases F.bv.getLsbD i <;> cases M.bv.getLsbD i <;> simp

/-- The first-badged flag (`1 << 49`). -/
abbrev FB : U64 := 562949953421312#u64

theorem fbc1 : (FB &&& obj.MDB_PTR_MASK) = 0#u64 := by unfold obj.MDB_PTR_MASK; rfl
theorem fbc2 : (~~~ FB &&& obj.MDB_PTR_MASK) = obj.MDB_PTR_MASK := by unfold obj.MDB_PTR_MASK; rfl
theorem fbc3 : (0#u64 &&& obj.MDB_PTR_MASK) = 0#u64 := by unfold obj.MDB_PTR_MASK; rfl

theorem fb_val : obj.MDB_FIRST_BADGED = ok FB := by
  unfold obj.MDB_FIRST_BADGED
  rw [SFF.shl_eq _ _ (by decide) (by decide)]
  rfl

theorem sx_val (w : U64) : obj.sext48 w =
    if ((w &&& 281474976710655#u64) &&& 140737488355328#u64 != 0#u64) = true
    then ok ((w &&& 281474976710655#u64) ||| 18446462598732840960#u64) else ok (w &&& 281474976710655#u64) := by
  unfold obj.sext48; simp only [lift, bind_ok, obj.MDB_PTR_MASK]

theorem hiM : (18446462598732840960#u64 &&& 281474976710655#u64) = 0#u64 := by rfl

/-- `sext48` is idempotent on its values. -/
theorem sx_idem (w n : U64) (h : obj.sext48 w = ok n) : obj.sext48 n = ok n := by
  rw [sx_val] at h ⊢
  split at h <;> rename_i h0 <;> have h' := okinj h <;> subst h'
  · rw [or_and_eq _ _ _ hiM, and_and_self', if_pos h0]
  · rw [and_and_self', if_neg h0]

/-- `sext48` reads the 48 pointer bits only. -/
theorem sx_mask (w : U64) : obj.sext48 (w &&& obj.MDB_PTR_MASK) = obj.sext48 w := by
  rw [sx_val, sx_val]; simp only [obj.MDB_PTR_MASK, and_and_self']

theorem sx0 : obj.sext48 0#u64 = ok 0#u64 := by
  rw [sx_val]; first | rfl | decide | simp

/-! ## Decodes -/

/-- `Cap::decode (0, w1)` is `Null` (tag 0: the wildcard arm, capability.rs:160–213). -/
theorem decode_zero (w1 : U64) : capability.Cap.decode 0#u64 w1 = ok .Null := by
  obtain ⟨p, hp⟩ := DPF.spec_tot (Fl4ProofsA64.P0.capability.unpack_ptr.p0 0#u64)
  have ht : (0#u64 : U64).bv >>> 59 = 0#64 := by first | rfl | decide
  unfold capability.Cap.decode
  simp only [DPF.shr_eq _ 59#i32 (by decide) (by decide), hp, bind_ok]
  first
  | rfl
  | (split <;> rename_i heq <;> first
      | rfl
      | (exfalso; have := congrArg UScalar.bv heq; simp [ht] at this; done)
      | (exfalso; simp_all))

/-- The first word of a `Domain` cap (tag 10). -/
abbrev domW : U64 := 5764607523034234880#u64

/-- `Cap::decode (10 << 59, w1)` is `Domain`. -/
theorem decode_dom (w1 : U64) : capability.Cap.decode domW w1 = ok .Domain := by
  obtain ⟨p, hp⟩ := DPF.spec_tot (Fl4ProofsA64.P0.capability.unpack_ptr.p0 domW)
  have ht : (domW : U64).bv >>> 59 = 10#64 := by first | rfl | decide
  unfold capability.Cap.decode
  simp only [DPF.shr_eq _ 59#i32 (by decide) (by decide), hp, bind_ok]
  first
  | rfl
  | (split <;> rename_i heq <;> first
      | rfl
      | (exfalso; have := congrArg UScalar.bv heq; simp [ht] at this; done)
      | (exfalso; simp_all))

/-! ## The invariant -/

/-- An MDB link: null or a slot of `OS`. -/
def LinkOK (OS : Set U64) (n : U64) : Prop := n = 0#u64 ∨ n ∈ OS

/-- A `NEXT` word whose 48-bit pointer is an MDB link. -/
def NextOK (OS : Set U64) (w : U64) : Prop := ∀ n, obj.sext48 w = ok n → LinkOK OS n

/-- A cap's slots (CNode, Zombie) lie in `OS`. -/
def CapIn (OS : Set U64) (c : capability.Cap) : Prop :=
  (∀ p r g b, c = .CNode p r g b → ∀ i : U64, i.val < 2 ^ (r.val % 64) → slotIdx p i ∈ OS) ∧
  (∀ p t n, c = .Zombie p t n → ∀ i : U64, i.val < n.val → slotIdx p i ∈ OS)

/-- **A slot cap's typing**: `W7.R.A5.I.DelCapOK` (the A64 IRQ bound, `< 5376`) and `CapIn`. -/
def CapTy (T Ω Sg : Set U64) (H : Heap) (Rp Nt OS : Set U64) (c : capability.Cap) : Prop :=
  A5.I.DelCapOK T Ω Sg H Rp Nt c ∧ CapIn OS c

/-- One slot of `OS` typed at `s`: its cap (`CapTy`), its `PREV` word (`LinkOK`), its `NEXT` word (`NextOK`). -/
def SlotOK (st : machine.Store S) [L : LawfulStore st] (T Ω Sg : Set U64) (H : Heap) (Rp Nt OS : Set U64)
    (s : S) (x : U64) : Prop :=
  (∀ c, capability.Cap.decode (L.mem s x) (L.mem s (wa x 8#u64)) = ok c → CapTy T Ω Sg H Rp Nt OS c) ∧
  LinkOK OS (L.mem s (wa x 16#u64)) ∧ NextOK OS (L.mem s (wa x 24#u64))

/-- **`SlotTy`: every slot of `OS` typed at `s`** (module docstring). -/
def SlotTy (st : machine.Store S) [L : LawfulStore st] (T Ω Sg : Set U64) (H : Heap) (Rp Nt OS : Set U64)
    (s : S) : Prop :=
  ∀ x ∈ OS, SlotOK st T Ω Sg H Rp Nt OS s x

/-- **The ghost slot set's placement** (module docstring). -/
structure OSOK (T Ω Sg : Set U64) (OS : Set U64) : Prop where
  slot : ∀ x ∈ OS, W7.SlotW T Ω Sg x
  fit : ∀ x ∈ OS, x.val + 32 ≤ 2 ^ 64
  disj : ∀ x ∈ OS, ∀ y ∈ OS, x ≠ y → x.val + 32 ≤ y.val ∨ y.val + 32 ≤ x.val
  /-- (gen 49, Architect ruling) No slot at address 0: kernel objects lie in the kernel window
  `PPTR_BASE + paddr` (crates/fl4-core/src/arch/aarch64/layout.rs:5), and `Slot::is_null` / `is_final_capability`
  read a 0 link as "none" (obj.rs:297–299, cdt.rs:163–174). Established at boot and by retype (where `OS` grows). -/
  nz : ∀ x ∈ OS, x ≠ 0#u64

/-- The deletion's step relation with the slot typing: `Cur0R` and `SlotTy`. -/
def J (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac OS : Set U64) (s0 s : S) : Prop :=
  Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s ∧ SlotTy st T Ω Sg H Rp Nt OS s

theorem CapIn.ctrl {OS : Set U64} {c : capability.Cap} (h1 : ∀ p r g b, c ≠ .CNode p r g b)
    (h2 : ∀ p t n, c ≠ .Zombie p t n) : CapIn OS c :=
  And.intro (fun p r g b e => absurd e (h1 p r g b)) (fun p t n e => absurd e (h2 p t n))

theorem CapTy.null {OS : Set U64} : CapTy T Ω Sg H Rp Nt OS .Null :=
  And.intro A5.I.DelCapOK.null (CapIn.ctrl (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))

theorem CapTy.domain {OS : Set U64} : CapTy T Ω Sg H Rp Nt OS .Domain := by
  refine And.intro ?_ (CapIn.ctrl (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

/-! ## Words of `OS` slots -/

section words
variable {OS : Set U64}

theorem wv {x k : U64} (hf : x.val + 32 ≤ 2 ^ 64) (hk : k.val < 32) : (wa x k).val = x.val + k.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem OSOK.al (hO : OSOK T Ω Sg OS) {x : U64} (hx : x ∈ OS) {k : U64} (hk : k.val < 32) (h8 : k.val % 8 = 0) :
    Aligned (wa x k) := by
  have := (hO.slot x hx).1
  unfold Aligned at *; rw [wv (hO.fit x hx) hk]; omega

theorem OSOK.al0 (hO : OSOK T Ω Sg OS) {x : U64} (hx : x ∈ OS) : Aligned x := (hO.slot x hx).1

theorem OSOK.cw (hO : OSOK T Ω Sg OS) {x : U64} (hx : x ∈ OS) {k : U64} (hk : k.val < 32) (h8 : k.val % 8 = 0) :
    W7.CapW T Ω Sg (wa x k) := (hO.slot x hx).2 k hk h8

theorem OSOK.cw0 (hO : OSOK T Ω Sg OS) {x : U64} (hx : x ∈ OS) : W7.CapW T Ω Sg x := by
  have := hO.cw hx (k := 0#u64) (by simp) (by simp); rwa [SFF.wadd0'] at this

/-- `SlotOK` reads the four words only. -/
theorem SlotOK.of_eq {s s' : S} {x : U64} (h : SlotOK st T Ω Sg H Rp Nt OS s x)
    (e0 : L.mem s' x = L.mem s x) (e8 : L.mem s' (wa x 8#u64) = L.mem s (wa x 8#u64))
    (e16 : L.mem s' (wa x 16#u64) = L.mem s (wa x 16#u64))
    (e24 : L.mem s' (wa x 24#u64) = L.mem s (wa x 24#u64)) : SlotOK st T Ω Sg H Rp Nt OS s' x := by
  unfold SlotOK; rw [e0, e8, e16, e24]; exact h

/-- **Frame**: the other slots' words kept and the written slot typed. -/
theorem SlotTy.frame {s s' : S} {x : U64} (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hk : ∀ y ∈ OS, y ≠ x → L.mem s' y = L.mem s y ∧ L.mem s' (wa y 8#u64) = L.mem s (wa y 8#u64) ∧
      L.mem s' (wa y 16#u64) = L.mem s (wa y 16#u64) ∧ L.mem s' (wa y 24#u64) = L.mem s (wa y 24#u64))
    (hself : SlotOK st T Ω Sg H Rp Nt OS s' x) : SlotTy st T Ω Sg H Rp Nt OS s' := by
  intro y hy
  by_cases e : y = x
  · subst e; exact hself
  · obtain ⟨e0, e8, e16, e24⟩ := hk y hy e
    exact (hT y hy).of_eq e0 e8 e16 e24

theorem vals (hO : OSOK T Ω Sg OS) {x : U64} (hx : x ∈ OS) :
    (wa x 8#u64).val = x.val + 8 ∧ (wa x 16#u64).val = x.val + 16 ∧ (wa x 24#u64).val = x.val + 24 := by
  have f := hO.fit x hx
  refine ⟨?_, ?_, ?_⟩ <;> (rw [wv f (by simp)]; simp)

/-- A write inside slot `x` keeps every other slot's words. -/
theorem other_keep (hO : OSOK T Ω Sg OS) {s : S} {x y b v : U64} (hx : x ∈ OS) (hy : y ∈ OS) (hne : y ≠ x)
    (hb : Aligned b) (hbv : x.val ≤ b.val ∧ b.val < x.val + 32) :
    L.mem (L.wr s b v) y = L.mem s y ∧ L.mem (L.wr s b v) (wa y 8#u64) = L.mem s (wa y 8#u64) ∧
      L.mem (L.wr s b v) (wa y 16#u64) = L.mem s (wa y 16#u64) ∧
      L.mem (L.wr s b v) (wa y 24#u64) = L.mem s (wa y 24#u64) := by
  have hd := hO.disj y hy x hx hne
  obtain ⟨v8, v16, v24⟩ := vals hO hy
  refine ⟨L.mem_wr_ne hb (hO.al0 hy) (by omega), L.mem_wr_ne hb (hO.al hy (by simp) (by simp)) (by omega),
    L.mem_wr_ne hb (hO.al hy (by simp) (by simp)) (by omega), L.mem_wr_ne hb (hO.al hy (by simp) (by simp)) (by omega)⟩

end words

/-! ## The store operations of `empty_slot` -/

theorem slot_prev_eq (s : S) (x : U64) : obj.Slot.prev st x s = ok (L.mem s (wa x 16#u64)) := by
  unfold obj.Slot.prev; simp only [lift, bind_ok, cte_prev, L.read_eq]

theorem slot_next_of {s : S} {x n : U64} (h : obj.sext48 (L.mem s (wa x 24#u64)) = ok n) :
    obj.Slot.next st x s = ok n := by
  unfold obj.Slot.next obj.Slot.next_word; simp only [lift, bind_ok, cte_next, L.read_eq, h]

theorem set_next_eq (s : S) (x n : U64) : obj.Slot.set_next st x s n =
    ok (L.wr s (wa x 24#u64) ((L.mem s (wa x 24#u64) &&& ~~~ obj.MDB_PTR_MASK) ||| (n &&& obj.MDB_PTR_MASK))) := by
  unfold obj.Slot.set_next obj.Slot.next_word; simp only [lift, bind_ok, cte_next, L.read_eq, L.write_eq]

theorem set_prev_eq (s : S) (x p : U64) : obj.Slot.set_prev st x s p = ok (L.wr s (wa x 16#u64) p) := by
  unfold obj.Slot.set_prev; simp only [lift, bind_ok, cte_prev, L.write_eq]

theorem set_fb_eq_t (s : S) (x : U64) : obj.Slot.set_first_badged st x s true =
    ok (L.wr s (wa x 24#u64) ((L.mem s (wa x 24#u64) &&& ~~~ FB) ||| FB)) := by
  unfold obj.Slot.set_first_badged obj.Slot.next_word
  first
  | simp only [lift, bind_ok, cte_next, L.read_eq, fb_val, L.write_eq, ↓reduceIte]
  | simp [lift, bind_ok, cte_next, L.read_eq, fb_val, L.write_eq]

theorem set_fb_eq_f (s : S) (x : U64) : obj.Slot.set_first_badged st x s false =
    ok (L.wr s (wa x 24#u64) ((L.mem s (wa x 24#u64) &&& ~~~ FB) ||| 0#u64)) := by
  unfold obj.Slot.set_first_badged obj.Slot.next_word
  first
  | simp only [lift, bind_ok, cte_next, L.read_eq, fb_val, L.write_eq, Bool.false_eq_true, ↓reduceIte]
  | simp [lift, bind_ok, cte_next, L.read_eq, fb_val, L.write_eq]

theorem clear_eq (s : S) (x : U64) : obj.Slot.clear st x s =
    ok (L.wr (L.wr (L.wr (L.wr s x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (wa x 24#u64) 0#u64) := by
  unfold obj.Slot.clear; simp only [lift, bind_ok, L.write_eq]

theorem pcd_null {A : Type _} (ar : machine.Arch A) (s : S) (a : A) :
    objects.post_cap_deletion st ar s a .Null = ok (s, a) := by
  first | rfl | simp [objects.post_cap_deletion] | (unfold objects.post_cap_deletion; rfl)

/-! ## `J` across each write -/

section steps
variable {OS : Set U64} {s0 : S}

/-- **`set_next` of a slot of `OS` to an MDB link** keeps `J`. -/
theorem J.next (hO : OSOK T Ω Sg OS) {s : S} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) {p n : U64}
    (hp : p ∈ OS) (hn : LinkOK OS n) (hni : obj.sext48 n = ok n) :
    J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0
      (L.wr s (wa p 24#u64) ((L.mem s (wa p 24#u64) &&& ~~~ obj.MDB_PTR_MASK) ||| (n &&& obj.MDB_PTR_MASK))) := by
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
    rw [← sx_mask, link_bits, sx_mask, hni] at hm
    exact (okinj hm) ▸ hn

/-- **`set_prev` of a slot of `OS` to an MDB link** keeps `J`. -/
theorem J.prev (hO : OSOK T Ω Sg OS) {s : S} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) {n v : U64}
    (hn : n ∈ OS) (hv : LinkOK OS v) :
    J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 (L.wr s (wa n 16#u64) v) := by
  have ha := hO.al hn (k := 16#u64) (by simp) (by simp)
  obtain ⟨v8, v16, v24⟩ := vals hO hn
  refine ⟨h.1.capw7 (writesIn_wr ha) fun b e => by subst e; exact hO.cw hn (by simp) (by simp), ?_⟩
  refine h.2.frame (x := n) (fun y hy hne => other_keep hO hn hy hne ha (by omega)) ?_
  have hs := h.2 n hn
  unfold SlotOK at hs ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [L.mem_wr_ne ha (hO.al0 hn) (by omega), L.mem_wr_ne ha (hO.al hn (by simp) (by simp)) (by omega)]
    exact hs.1
  · rw [L.mem_wr_same ha]; exact hv
  · rw [L.mem_wr_ne ha (hO.al hn (by simp) (by simp)) (by omega)]; exact hs.2.2

/-- **`set_first_badged` of a slot of `OS`** keeps `J` (the flag bit 49 is outside the 48 pointer bits). -/
theorem J.fb (hO : OSOK T Ω Sg OS) {s : S} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) {n v : U64}
    (hn : n ∈ OS) (hv : v = 0#u64 ∨ v = FB) :
    J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 (L.wr s (wa n 24#u64) ((L.mem s (wa n 24#u64) &&& ~~~ FB) ||| v)) := by
  have ha := hO.al hn (k := 24#u64) (by simp) (by simp)
  obtain ⟨v8, v16, v24⟩ := vals hO hn
  refine ⟨h.1.capw7 (writesIn_wr ha) fun b e => by subst e; exact hO.cw hn (by simp) (by simp), ?_⟩
  refine h.2.frame (x := n) (fun y hy hne => other_keep hO hn hy hne ha (by omega)) ?_
  have hs := h.2 n hn
  unfold SlotOK at hs ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [L.mem_wr_ne ha (hO.al0 hn) (by omega), L.mem_wr_ne ha (hO.al hn (by simp) (by simp)) (by omega)]
    exact hs.1
  · rw [L.mem_wr_ne ha (hO.al hn (by simp) (by simp)) (by omega)]; exact hs.2.1
  · rw [L.mem_wr_same ha]
    intro m hm
    have hv0 : v &&& obj.MDB_PTR_MASK = 0#u64 := by rcases hv with rfl | rfl; exacts [fbc3, fbc1]
    rw [← sx_mask, fb_bits _ _ _ _ hv0 fbc2, sx_mask] at hm
    exact hs.2.2 m hm

/-- **`clear` of a slot of `OS`** keeps `J` (the slot then holds `Null` with null links). -/
theorem J.clear (hO : OSOK T Ω Sg OS) {s : S} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) {x : U64}
    (hx : x ∈ OS) :
    J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0
      (L.wr (L.wr (L.wr (L.wr s x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (wa x 24#u64) 0#u64) := by
  have a0 := hO.al0 hx
  have a8 := hO.al hx (k := 8#u64) (by simp) (by simp)
  have a16 := hO.al hx (k := 16#u64) (by simp) (by simp)
  have a24 := hO.al hx (k := 24#u64) (by simp) (by simp)
  obtain ⟨v8, v16, v24⟩ := vals hO hx
  have c1 := h.1.capw7 (writesIn_wr (v := 0#u64) a0) fun b e => by subst e; exact hO.cw0 hx
  have c2 := c1.capw7 (writesIn_wr (v := 0#u64) a8) fun b e => by subst e; exact hO.cw hx (by simp) (by simp)
  have c3 := c2.capw7 (writesIn_wr (v := 0#u64) a16) fun b e => by subst e; exact hO.cw hx (by simp) (by simp)
  have c4 := c3.capw7 (writesIn_wr (v := 0#u64) a24) fun b e => by subst e; exact hO.cw hx (by simp) (by simp)
  refine ⟨c4, h.2.frame (x := x) (fun y hy hne => ?_) ?_⟩
  · obtain ⟨d1, d2, d3, d4⟩ := other_keep (st := st) (s := L.wr (L.wr (L.wr s x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64)
      (v := 0#u64) hO hx hy hne a24 (by omega)
    obtain ⟨e1, e2, e3, e4⟩ := other_keep (st := st) (s := L.wr (L.wr s x 0#u64) (wa x 8#u64) 0#u64) (v := 0#u64) hO hx hy hne
      a16 (by omega)
    obtain ⟨f1, f2, f3, f4⟩ := other_keep (st := st) (s := L.wr s x 0#u64) (v := 0#u64) hO hx hy hne a8 (by omega)
    obtain ⟨g1, g2, g3, g4⟩ := other_keep (st := st) (s := s) (v := 0#u64) hO hx hy hne a0 (by omega)
    exact ⟨d1.trans (e1.trans (f1.trans g1)), d2.trans (e2.trans (f2.trans g2)),
      d3.trans (e3.trans (f3.trans g3)), d4.trans (e4.trans (f4.trans g4))⟩
  · have m24 : ∀ (s' : S) (v : U64), L.mem (L.wr s' (wa x 24#u64) v) (wa x 24#u64) = v := fun _ _ => L.mem_wr_same a24
    unfold SlotOK
    have m16 : L.mem (L.wr (L.wr (L.wr (L.wr s x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (wa x 24#u64) 0#u64)
        (wa x 16#u64) = 0#u64 := by
      rw [L.mem_wr_ne a24 a16 (by omega), L.mem_wr_same a16]
    have m8 : L.mem (L.wr (L.wr (L.wr (L.wr s x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (wa x 24#u64) 0#u64)
        (wa x 8#u64) = 0#u64 := by
      rw [L.mem_wr_ne a24 a8 (by omega), L.mem_wr_ne a16 a8 (by omega), L.mem_wr_same a8]
    have m0 : L.mem (L.wr (L.wr (L.wr (L.wr s x 0#u64) (wa x 8#u64) 0#u64) (wa x 16#u64) 0#u64) (wa x 24#u64) 0#u64)
        x = 0#u64 := by
      rw [L.mem_wr_ne a24 a0 (by omega), L.mem_wr_ne a16 a0 (by omega), L.mem_wr_ne a8 a0 (by omega),
        L.mem_wr_same a0]
    refine ⟨?_, ?_, ?_⟩
    · rw [m0, m8, decode_zero]; intro c hc; rw [← okinj hc]; exact CapTy.null
    · rw [m16]; exact Or.inl rfl
    · rw [m24]; intro n hn; rw [sx0] at hn; rw [← okinj hn]; exact Or.inl rfl

end steps

/-! ## `empty_slot` -/

set_option maxHeartbeats 2000000 in
/-- **`empty_slot` of a slot of `OS`, null cleanup**, keeps `J` (`Cur0R` and `SlotTy`). -/
theorem cdt.empty_slot.ty {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {s0 s : S} {a : A} {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hx : x ∈ OS) :
    cdt.empty_slot st ar s a x .Null ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h
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
  exact J.clear hO h2 hx

/-! ## The trivial kinds -/

/-- **The kinds whose `finalise_cap` (with `exposed = false`) changes nothing and returns `(Null, Null)`**
(objects.rs `finalise_cap` / `finalise_cap_object`; Funs.lean 19223–19261, 18719–18940): always for `Null`,
`Untyped`, `IrqControl`, `Domain`, `SchedControl`, `AsidControl`, `IoPortControl`, `TdxControl`; for unmapped
`PageTable` / `PageDirectory` / `Pdpt` / `Pml4` / `HighVSpace` caps, final or not. -/
def TrivK (c : capability.Cap) : Prop :=
  c = .Null ∨ (∃ p b f d, c = .Untyped p b f d) ∨ c = .IrqControl ∨ c = .Domain ∨ (∃ w, c = .SchedControl w) ∨
  c = .AsidControl ∨ c = .IoPortControl ∨ c = .TdxControl ∨
  (∃ p a v, c = .PageTable p false a v) ∨ (∃ p a v, c = .PageDirectory p false a v) ∨
  (∃ p a v, c = .Pdpt p false a v) ∨ (∃ p a, c = .Pml4 p false a) ∨ (∃ p a, c = .HighVSpace p false a)

theorem finalise_cap.triv {A : Type _} (ar : machine.Arch A) (s : S) (a : A) {c : capability.Cap} (hk : TrivK c)
    (fin : Bool) : objects.finalise_cap st ar s a c fin false = ok ((.Null, .Null), s, a) := by
  rcases hk with rfl | ⟨_, _, _, _, rfl⟩ | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | ⟨_, _, _, rfl⟩ |
    ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
  cases fin <;>
  first
  | rfl
  | simp [objects.finalise_cap, objects.finalise_cap_object]
  | (simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]; rfl)

/-- The cap in slot `x` is of a trivial kind. -/
def CapTrivAt (st : machine.Store S) [L : LawfulStore st] (x : U64) (s : S) : Prop :=
  ∀ c, obj.Slot.cap st x s = ok c → TrivK c

set_option maxHeartbeats 4000000 in
/-- `finalise_slot_immediate` of a slot holding a trivial-kind cap: the state unchanged, a null cleanup. -/
theorem cdt.finalise_slot_immediate.triv {A : Type _} {ar : machine.Arch A} {s : S} {a : A} {x : U64}
    (hk : CapTrivAt st x s) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r => r.2.1 = s ∧ ∀ v, r.1 = .Ok v → v.cleanup = .Null ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val) (inv := fun y => y.1 = s)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    have hk1 : CapTrivAt st x s1 := h1 ▸ hk
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, by intro v hv; simp_all⟩
    step as ⟨fuel1, hf1⟩
    obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st x s1 hS)
    have hkc := hk1 c hc
    rw [hc, bind_ok]
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; rfl⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    rw [finalise_cap.triv ar s1 a1 hkc fin, bind_ok]
    try dsimp only
    first
    | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte]; exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; rfl⟩)
    | (simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]; exact ⟨h1, fun v hv => by cases hv; rfl⟩)
    | (simp [cdt.cap_removable, WP.spec_ok]; exact h1)
    | (simp [cdt.cap_removable, WP.spec_ok, h1])
  · rfl

set_option maxHeartbeats 2000000 in
/-- **The first deletion top over `SlotTy`**: the exposed `cdt.delete` of a slot of `OS` holding a trivial-kind
cap keeps `Cur0R` and `SlotTy` (covers exactly the `TrivK` kinds). -/
theorem cdt.delete.triv {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {s0 s : S} {a : A} {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hx : x ∈ OS)
    (hk : CapTrivAt st x s) :
    cdt.delete st ar s a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.triv (ar := ar) (a := a) hk) ?_
  rintro ⟨r, s1, a1⟩ ⟨e1, hv1⟩
  try simp only [uncurry_apply_pair] at e1 hv1 ⊢
  subst e1
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [hv1 v rfl]
    refine WP.spec_bind (cdt.empty_slot.ty hO h hx) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h

/-! ## Non-vacuity -/

/-- **Witness**: from any `Cur0R` state and any thread `t`, a `Domain` cap with null links written into `t`'s
first cap slot (four `W7.CapW` words) gives a state satisfying every premise of `cdt.delete.triv` with
`OS = {t}`. -/
theorem J.witness {s0 s : S} (h : Cur0R st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) {t : U64} (ht : t ∈ T) :
    ∃ s', J st T Cs Ω H Sg Rp Scs Nt Z Ac {t} s0 s' ∧ OSOK T Ω Sg {t} ∧ CapTrivAt st t s' ∧
      obj.Slot.cap st t s' = ok .Domain := by
  obtain ⟨Ac', hb⟩ := h.bxi
  have hpl := hb.1.choose_spec.choose_spec.tcbs t ht
  have hW : W7.SlotW T Ω Sg t := by
    have ha0 : Aligned t := by
      have := field_aligned (K := 0#u64) hpl (by simp) (by simp); rwa [SFF.wadd0'] at this
    exact ⟨ha0, fun o h1 _ => Or.inl ⟨t, ht, o, by omega, rfl⟩⟩
  have hO : OSOK T Ω Sg {t} :=
    ⟨fun x e => by rw [Set.mem_singleton_iff.1 e]; exact hW, fun x e => by
      rw [Set.mem_singleton_iff.1 e]; exact le_trans (Nat.add_le_add_left (by norm_num) _) hpl.fits,
     fun x ex y ey hne => absurd ((Set.mem_singleton_iff.1 ex).trans (Set.mem_singleton_iff.1 ey).symm) hne,
     fun x e h0 => hpl.ne0 (by rw [← Set.mem_singleton_iff.1 e, h0]; first | rfl | simp)⟩
  have htO : t ∈ ({t} : Set U64) := Set.mem_singleton t
  have a0 := hO.al0 htO
  have a8 := hO.al htO (k := 8#u64) (by simp) (by simp)
  have a16 := hO.al htO (k := 16#u64) (by simp) (by simp)
  have a24 := hO.al htO (k := 24#u64) (by simp) (by simp)
  obtain ⟨v8, v16, v24⟩ := vals hO htO
  have c1 := h.capw7 (writesIn_wr (v := domW) a0) fun b e => by subst e; exact hO.cw0 htO
  have c2 := c1.capw7 (writesIn_wr (v := 0#u64) a8) fun b e => by subst e; exact hO.cw htO (by simp) (by simp)
  have c3 := c2.capw7 (writesIn_wr (v := 0#u64) a16) fun b e => by subst e; exact hO.cw htO (by simp) (by simp)
  have c4 := c3.capw7 (writesIn_wr (v := 0#u64) a24) fun b e => by subst e; exact hO.cw htO (by simp) (by simp)
  have m0 : L.mem (L.wr (L.wr (L.wr (L.wr s t domW) (wa t 8#u64) 0#u64) (wa t 16#u64) 0#u64) (wa t 24#u64) 0#u64)
      t = domW := by
    rw [L.mem_wr_ne a24 a0 (by omega), L.mem_wr_ne a16 a0 (by omega), L.mem_wr_ne a8 a0 (by omega),
      L.mem_wr_same a0]
  have m8 : L.mem (L.wr (L.wr (L.wr (L.wr s t domW) (wa t 8#u64) 0#u64) (wa t 16#u64) 0#u64) (wa t 24#u64) 0#u64)
      (wa t 8#u64) = 0#u64 := by
    rw [L.mem_wr_ne a24 a8 (by omega), L.mem_wr_ne a16 a8 (by omega), L.mem_wr_same a8]
  have m16 : L.mem (L.wr (L.wr (L.wr (L.wr s t domW) (wa t 8#u64) 0#u64) (wa t 16#u64) 0#u64) (wa t 24#u64) 0#u64)
      (wa t 16#u64) = 0#u64 := by
    rw [L.mem_wr_ne a24 a16 (by omega), L.mem_wr_same a16]
  have m24 : L.mem (L.wr (L.wr (L.wr (L.wr s t domW) (wa t 8#u64) 0#u64) (wa t 16#u64) 0#u64) (wa t 24#u64) 0#u64)
      (wa t 24#u64) = 0#u64 := L.mem_wr_same a24
  have hcap : obj.Slot.cap st t
      (L.wr (L.wr (L.wr (L.wr s t domW) (wa t 8#u64) 0#u64) (wa t 16#u64) 0#u64) (wa t 24#u64) 0#u64) =
      ok .Domain := by
    rw [DPF.slot_cap_dec, m0, m8, decode_dom]
  refine ⟨_, ⟨c4, fun y hy => ?_⟩, hO, fun c hc => ?_, hcap⟩
  · rw [Set.mem_singleton_iff.1 hy]
    unfold SlotOK
    refine ⟨?_, ?_, ?_⟩
    · rw [m0, m8, decode_dom]; intro c hc; rw [← okinj hc]; exact CapTy.domain
    · rw [m16]; exact Or.inl rfl
    · rw [m24]; intro n hn; rw [sx0] at hn; rw [← okinj hn]; exact Or.inl rfl
  · rw [hcap] at hc; rw [← okinj hc]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/-! ## The entry fact -/

/-- No word of an `OS` slot is written by the entry prefix from `e` (`EntW e`). -/
def EntApart (st : machine.Store S) [L : LawfulStore st] (e : S) (OS : Set U64) : Prop :=
  ∀ b, EntW st e b → ∀ y ∈ OS, ¬ (y.val ≤ b.val ∧ b.val < y.val + 32)

/-- **[J] (a64) `SlotTyEnt`** (module docstring): at every `P3Ok` kernel entry state there is a ghost slot set
`OS` placed (`OSOK`), typed (`SlotTy`) and apart from the entry prefix's words (`EntApart`). Source: the boot's
CNodes and TCB slots hold the boot caps typed (IRQ handler caps only from `IRQControl_Get` on IRQs below the
GIC's 5376, interrupt.rs `decode_irq_control`); every kernel step keeps it (the cap writes are `set_cap` of
derived / copied / minted caps and `empty_slot` / `swap` / Zombie writes over slots of `OS`, retype adds the new
objects' slots to `OS`, and the user-writable `Ω \ Sg` words — the VCPU registers of `ARMVCPUWriteRegisters`,
vcpu.rs:475–512 — are words of VCPU objects, which lie in no CNode or TCB slot, so outside `OS`). -/
def SlotTyEnt (st : machine.Store S) [L : LawfulStore st] (T Ω Sg : Set U64) (H : Heap) (Rp Nt : Set U64)
    (P3Ok : S → Prop) : Prop :=
  ∀ e, P3Ok e → ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS e ∧ EntApart st e OS

/-- **`SlotTyEnt` carried to every `EntAt` state** (the entry prefix writes no `OS` word). -/
theorem SlotTyEnt.entAt (hJ : SlotTyEnt st T Ω Sg H Rp Nt P3Ok) {s : S} (hE : EntAt st P3Ok s) :
    ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s := by
  obtain ⟨e, he, hw⟩ := hE
  obtain ⟨OS, hO, hT, hA⟩ := hJ e he
  refine ⟨OS, hO, fun y hy => ?_⟩
  obtain ⟨v8, v16, v24⟩ := vals hO hy
  have k : ∀ b, Aligned b → y.val ≤ b.val → b.val < y.val + 32 → L.mem s b = L.mem e b :=
    fun b hb h1 h2 => hw.mem_eq hb fun hb' => hA b hb' y hy ⟨h1, h2⟩
  exact (hT y hy).of_eq (k _ (hO.al0 hy) (by omega) (by omega)) (k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega))
    (k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega)) (k _ (hO.al hy (by simp) (by simp)) (by omega) (by omega))

end ST
end R
end W7

end

end Fl4ProofsA64.P1

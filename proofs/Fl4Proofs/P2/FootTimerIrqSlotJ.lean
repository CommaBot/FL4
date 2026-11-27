/-
# P2 (p2lf gen13): the timer interrupt's slot layout from P3's joint invariant

* `LayP.region_slotW`: the region of any word of a slot of a placed layout is that slot (as line slj's
  `LayP.slj_region_slot`, which is not on this branch).
* `slotLayV_of_JAtZ`: `SlotLayV` (slot 1's two words of every thread homed here lie in a TCB slot region) for P3's
  layout `layoutJ Zx H (L.ksb s) n` at a `JAtZ` state, for any thread set `T` of `H`'s TCBs: slot 1 of a TCB is
  `IsSlotAt Zx.th y 1` (`JPlaced.tcb`, `tcbSlots = 6`), placed at `y + 32` (`IsSlotAt.val`).
* `SlotJ K st T H s` [J]: `JAtZ` at `s` at some ghosts, with `K` the layout read off that state (`layoutJ`) and the
  layout's cores in `JAtZ`'s `Cs` (the shape of line slj's `SlJAt` bundle, without its scheduler-action field).
* `irq_localPathP3J`: `irq_localPathP3` with `hSL` [J] replaced by `hSJ` [J] (`SlotJ` at every entry) and `hTH` [J]
  (`T` holds `H`'s TCBs: P1's set convention `T = H.tcbs`, `JAtZ.blk`).

Finding (gen13): `SlotLay` and `IrqLay.cs` quantify over offsets below 256 (eight 32-byte slots), but a TCB has
`tcbSlots = 6` slots in P3 (`LayP.slot`: TCB slots end below `+192`), so under `layoutJ` both are false for slots 6
and 7; `SlotLayV` (slot 1 only) is what the switch block needs and what P3 gives.

* `LayP.region_objW`, `objLay_of_layP`, `SlotJ.objLay`: `ObjLay` (endpoints' and replies' words in their object
  regions) for a placed layout, hence at a `SlotJ` entry given `Rp ⊆ H`'s replies.
* `irq_localPathP3J2`: `irq_localPathP3J` with `hOL` [J] replaced by `hRp` [J] (P1's convention `Rp = H.replies`).

Premises of `irq_localPathP3J`: as `irq_localPathP3` with `hSJ` [J] and `hTH` [J] in place of `hSL`.
Premises of `irq_localPathP3J2`: `hp` [P], `hz` [W], `hm` [P], `hro` [W], `IrqEnt`'s [J] parts, `hEU` [J], `hlk` [P],
`hPL` [P], `hUB` [J], `hSJ` [J], `hTH` [J], `hRp` [J].
-/
import Fl4Proofs.P2.FootTimerIrqLPP3
import Fl4Proofs.P2.OwnJAtZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section lay
variable {K : KLayout}

/-- Two slots holding one word are one (slots are 32-aligned). -/
theorem _root_.Fl4Proofs.P2.OwnMap.LayP.slot_uniqW (h : LayP K) {p q b : U64} (hp : p ∈ K.slots) (hq : q ∈ K.slots)
    (hb : InW p 32 b) (hb' : InW q 32 b) : p = q := by
  have e1 := (h.slot p hp).1
  have e2 := (h.slot q hq).1
  obtain ⟨b1, b2⟩ := hb
  obtain ⟨b3, b4⟩ := hb'
  exact UScalar.eq_of_val_eq (by omega)

/-- **The region of a word of a slot is that slot.** -/
theorem _root_.Fl4Proofs.P2.OwnMap.LayP.region_slotW (h : LayP K) {p b : U64} (hp : p ∈ K.slots) (hb : InW p 32 b) :
    region K b = .slot p := by
  have hex : ∃ q ∈ K.slots, InW q 32 b := ⟨p, hp, hb⟩
  obtain ⟨q, k, hq, hqb, -, -⟩ := h.slot_obj hp hb
  unfold region
  rw [dif_neg (h.no_node hq hqb), dif_pos hex]
  have hc := Classical.choose_spec hex
  rw [h.slot_uniqW hc.1 hp hc.2 hb]

/-- **The region of a word of an endpoint or reply object** (as line slj's `LayP.slj_region_obj`). -/
theorem _root_.Fl4Proofs.P2.OwnMap.LayP.region_objW (h : LayP K) {p b : U64} {k : HKind} (hp : K.heap p = some k)
    (hk : k = .ep ∨ k = .reply) (hb : InW p (2 ^ k.bits) b) : region K b = .obj p := by
  have hk1 : ∀ z, k ≠ .other z := by intro z e; rcases hk with rfl | rfl <;> cases e
  have hk2 : k ≠ .tcb := by intro e; rcases hk with rfl | rfl <;> cases e
  have hex : ∃ p, (K.heap p = some .ep ∧ InW p (2 ^ 4) b) ∨ (K.heap p = some .reply ∧ InW p (2 ^ 5) b) := by
    rcases hk with rfl | rfl
    · exact ⟨p, Or.inl ⟨hp, hb⟩⟩
    · exact ⟨p, Or.inr ⟨hp, hb⟩⟩
  unfold region
  rw [dif_neg (h.no_node hp hb), dif_neg (h.no_slot hp hb hk1 (fun e => absurd e hk2)), dif_neg, dif_neg,
    dif_pos hex]
  · have hc := Classical.choose_spec hex
    rcases hc with ⟨hq, hqb⟩ | ⟨hq, hqb⟩
    · exact congrArg Region.obj (h.uniq hq hp hqb hb).1
    · exact congrArg Region.obj (h.uniq hq hp hqb hb).1
  · rintro ⟨q, hq, hqb⟩
    have := (h.uniq hq hp hqb hb).2
    subst this; rcases hk with e | e <;> cases e
  · rintro ⟨t, ht, htb⟩
    have := (h.uniq ht hp htb hb).2
    subst this; rcases hk with e | e <;> cases e

/-- **`ObjLay` from a placed layout** whose heap holds the replies `Rp`. -/
theorem objLay_of_layP (h : LayP K) {Rp : Set U64} (hRp : ∀ r ∈ Rp, K.heap r = some .reply) :
    ObjLay K K.heap Rp := by
  have one : ∀ p k (kd : HKind), K.heap p = some kd → (kd = .ep ∨ kd = .reply) → k.val < 2 ^ kd.bits →
      region K (core.num.U64.wrapping_add p k) = .obj p := fun p k kd hp hkd hk => by
    have hf := h.heap.fits p _ hp
    refine h.region_objW hp hkd ⟨?_, ?_⟩ <;>
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] <;>
      rw [Nat.mod_eq_of_lt (by omega)] <;> omega
  exact ⟨fun e he k hk => one e k _ he (Or.inl rfl) (by simp [HKind.bits]; omega),
    fun r hr k hk => one r k _ (hRp r hr) (Or.inr rfl) (by simp [HKind.bits]; omega)⟩

end lay

section j
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`SlotLayV` from P3's joint invariant** for its layout (module docstring). -/
theorem slotLayV_of_JAtZ {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : Fl4Proofs.P3.XSets} {H : Heap} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S}
    {a' : A'} {σ : Fl4Spec.State Unit} (J : Fl4Proofs.P3.JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a' σ) {n : Nat}
    (hn : ∀ c : U64, c.val < n → c ∈ Cx) {T : Set U64} (hTH : ∀ y ∈ T, H y = some .tcb) :
    SlotLayV (layoutJ Zx H (L.ksb s) n) st T s := by
  have hP := layP_of_JAtZ J hn
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  intro y hy k hk
  have hyH := hTH y hy.1
  have hth : Zx.th y = some .tcb := (hJ.tcb y).2 hyH
  have hf := hJ.heap.fits y _ hyH
  simp only [HKind.bits] at hf
  have hsa : Fl4Proofs.P3.IsSlotAt Zx.th y 1 := Or.inr ⟨hth, by unfold Fl4Proofs.P3.tcbSlots; omega⟩
  have hpv : (Fl4Proofs.P3.slotOf y 1).val = y.val + 32 := by have := hsa.val hJ.pl; omega
  have hps : Fl4Proofs.P3.slotOf y 1 ∈ (layoutJ Zx H (L.ksb s) n).slots := by
    show Fl4Proofs.P3.IsSlot Zx.th _
    exact ⟨y, 1, hsa, rfl⟩
  have hkv : (core.num.U64.wrapping_add y k).val = y.val + k.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hin : InW (Fl4Proofs.P3.slotOf y 1) 32 (core.num.U64.wrapping_add y k) := by
    unfold InW; rw [hpv, hkv]; omega
  refine ⟨_, hP.region_slotW hps hin, ⟨y, hyH, ?_⟩, by rw [hpv, hkv]; omega⟩
  unfold InW; rw [hpv]
  constructor <;> omega

/-- **[J] The entry as a state of P3's joint invariant, with `K` its layout** (module docstring). -/
def SlotJ (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (H : Heap) (s : S) : Prop :=
  ∃ (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Cx Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    Fl4Proofs.P3.JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a' σ ∧ (∀ c : U64, c.val < K.ncores → c ∈ Cx) ∧
      layoutJ Zx H (L.ksb s) K.ncores = K

theorem SlotJ.slotLayV {K : KLayout} {H : Heap} {s : S} (h : SlotJ K st H s) {T : Set U64}
    (hTH : ∀ y ∈ T, H y = some .tcb) : SlotLayV K st T s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, J, hn, hK⟩ := h
  have := slotLayV_of_JAtZ J hn hTH
  rwa [hK] at this

theorem SlotJ.layP {K : KLayout} {H : Heap} {s : S} (h : SlotJ K st H s) : LayP K ∧ K.heap = H := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, J, hn, hK⟩ := h
  have := layP_of_JAtZ J hn
  rw [hK] at this
  exact ⟨this, by rw [← hK]; rfl⟩

theorem SlotJ.objLay {K : KLayout} {H : Heap} {s : S} (h : SlotJ K st H s) {Rp : Set U64}
    (hRp : ∀ r ∈ Rp, H r = some .reply) : ObjLay K H Rp := by
  obtain ⟨hP, hH⟩ := h.layP
  have := objLay_of_layP hP (Rp := Rp) (by rw [hH]; exact hRp)
  rwa [hH] at this

end j

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- **The timer interrupt is a local path, `hBA` proved and the slot layout from P3** (module docstring). -/
noncomputable def irq_localPathP3J (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR K st lk))
    (hEU : ∀ s b v, IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ K.user → Aligned b →
      IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) (hOL : ObjLay K H Rp)
    (hUB : ∀ s, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s →
      ∃ U : Set U64, UserOK st T Cs Ω H U s ∧ ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hSJ : ∀ s, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → SlotJ K st H s)
    (hTH : ∀ y ∈ T, H y = some .tcb) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  irq_localPathP3 ar hA hK hUO hp hz hm hro hEU hlk hPL hOL hUB fun s hE => (hSJ s hE).slotLayV hTH

/-- **The timer interrupt is a local path, `hBA` proved, the slot and object layouts from P3** (module docstring):
`irq_localPathP3J` with `hOL` [J] replaced by `hRp` [J] (`Rp` holds `H`'s replies: P1's convention
`Rp = H.replies`); `ObjLay` comes from `SlotJ` at each entry (`SlotJ.objLay`). -/
noncomputable def irq_localPathP3J2 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR K st lk))
    (hEU : ∀ s b v, IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ K.user → Aligned b →
      IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl)
    (hUB : ∀ s, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s →
      ∃ U : Set U64, UserOK st T Cs Ω H U s ∧ ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hSJ : ∀ s, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → SlotJ K st H s)
    (hTH : ∀ y ∈ T, H y = some .tcb) (hRp : ∀ r ∈ Rp, H r = some .reply) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  irq_localPathW ar hA hK hUO hp hz hm hro hEU hlk
    (fun s a s1 a1 hE hf hw h => by
      obtain ⟨U, hU, hb⟩ := hUB s hE
      exact irq_acc_fire_wk2 ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth ((hSJ s hE).objLay hRp) hPL
        (irq_bufAt_run ar hA hE.ent.inv hU hb hf h) ((hSJ s hE).slotLayV hTH) hf hw h)
    (fun s a s1 a1 hE hf hw h => by
      obtain ⟨U, hU, hb⟩ := hUB s hE
      exact irq_move_fire_wk2 ar hA hK hUO hp hE.k hE.ent.ly hE.ent.aff hE.ent.nth ((hSJ s hE).objLay hRp) hPL
        (irq_bufAt_run ar hA hE.ent.inv hU hb hf h) hf hw h)

end

end Fl4Proofs.P2

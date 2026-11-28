/-
P1 (aarch64, gen 57): **`MdbST ∧ UtRev` through the `LoopMZ` deletion loops** — a `LoopMZ` field (QueueZombieQ,
gen 50) for `M := MdbST ∧ UtRev` with `Zr := ZrA ∧ ZrT`, so gen 41's exposed deletion and gen 39's deferred deletion
(and gen 45's reachable-typing tops) carry the tree and the revocable bit (new tops; existing statements untouched).

* **`ZrT st s x p t`**: slot `x` holds `CNode p t _ _` (`t < 64`), `Thread p` (`t = ZOMBIE_TCB`) or `Zombie p t _`
  — what the `Zombie p t _` write needs for `UA` (`UA.zombie_cnode`, `UA.zombie_threadP`, `UA.zombie`, MdbTreeD).
  `finalise_cap` produces a `Zombie p t _` remainder only from these (objects.rs `finalise_cap_object`: CNode radix,
  TCB `ZOMBIE_TCB`, a Zombie returned as is).
* `MdbST.keepO` (an `OSKeep` step); **`obj.Slot.set_cap.trZ`** (`setz`: `TreeA.set_cap` with that `UA`; the new cap
  is no `Untyped`, the `NEXT` words are kept, `UtRev`).
* **`cdt.swap.treeN`** / **`cdt.cap_swap_for_delete.treeN`**: the tree along a swap whose first slot is a member or a
  null linkless slot (`NullLk`; MdbNull's `swap_post` argument, `LkAbs.sw_null`, for `MdbLk.renN` and
  `UtInvA.ren`) — the deletion loops' `cap_swap_for_delete(Slot(ptr), slot)`; x86 swaps members only.
* **`cdt.delete_one.tr`**, **`finalise_cap.irq_tr`**, **`finXQT`** (`fin`: gen 50's `finXQM` case split, `TR` kept
  by `OSKeep` cases, the state returned for CNode / Zombie, `empty_slot.tree` / `.utRev` on the IRQ-node slot; a
  `Zombie` remainder leaves `ZrT`), **`cdt.empty_slot.trJ`** (`emp`, the cleanup cases of MdbLoop's
  `cdt.empty_slot.mdbS`).
* **`LoopMZ.mdbSTR`** (with gen 50's `LoopMZ.mdb` for the `MdbS` half, `MdbST.of`), **`cdt.delete.zqIGTmdbSTR`**,
  **`cdt.delete_deferred.zqGmdbSTR`**, **`cdt.delete.zqETMR`** / **`zqETRMR`** / **`threadQETMR`** /
  **`threadQETRMR`** (gen 50's MdbFinR tops with `MdbST ∧ UtRev`; since gen 61 instances of MdbFinR's
  field-generic `zqETG` / `threadQETG` / `zqETRG` / `threadQETRG`).

No named premise; hypotheses those of the existing tops with `MdbST ∧ UtRev` for `MdbS`.
-/
import Fl4ProofsA64.P1.MdbTreeC
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **The slot shapes a `Zombie p t _` write rewrites** (module docstring). -/
def ZrT (st : machine.Store S) [L : LawfulStore st] (s : S) (x p t : U64) : Prop :=
  (∃ g b, capA st s x = .CNode p t g b ∧ t.val < 64) ∨ (capA st s x = .Thread p ∧ t = capability.ZOMBIE_TCB) ∨
    ∃ n, capA st s x = .Zombie p t n

theorem UA.zombie_threadP (p n : U64) : UA (.Zombie p capability.ZOMBIE_TCB n) (.Thread p) := by
  have h := UA.zombie_thread p n
  have e0 : core.num.U64.wrapping_add p (core.num.U64.wrapping_mul layout.tcb.SLOT_CTABLE layout.cte.SIZE) = p := by
    apply UScalar.eq_of_val_eq
    simp [layout.tcb.SLOT_CTABLE, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq,
      U64.size_def, U64.numBits]
    try (have := p.hBounds; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits] at this; omega)
  rw [e0] at h; exact h

variable {OS : Set U64}

theorem MdbST.keepO (hO : OSOK T Ω Sg OS) {s s' : S} (h : MdbST st OS s) (k : OSKeep st OS s s') :
    MdbST st OS s' := by
  obtain ⟨G, par, hT⟩ := h.tu
  exact MdbST.of hO.nz (h.mdbS.keep k) ⟨G, par, hT.keepO k⟩

/-! ## `setz` -/

/-- **The `Zombie` write into a `ZrT` slot keeps `TR`.** -/
theorem obj.Slot.set_cap.trZ (hO : OSOK T Ω Sg OS) {s : S} (hm : MdbST st OS s ∧ UtRev st OS s) {x p t n : U64}
    (hx : x ∈ OS) (hp : Canon p) (hz : ZrT st s x p t) :
    obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => MdbTU st OS s' ∧ UtRev st OS s' ⦄ := by
  rw [set_cap_zombie, WP.spec_ok]
  have hd := decode_zw p t n hp
  have hw : CapRt.EncWf (capA st s x) := CapRt.decodeF_encWf _ _
  have ht : t &&& 255#u64 = t := by
    rcases hz with ⟨g, b, e, h64⟩ | ⟨-, e⟩ | ⟨n0, e⟩
    · exact and255 (by omega)
    · rw [e]; exact t255
    · rw [e] at hw; exact and255 hw.2
  rw [ht] at hd
  have hc0 : capA st s x ≠ .Null := by
    rcases hz with ⟨g, b, e, -⟩ | ⟨e, -⟩ | ⟨n0, e⟩ <;> rw [e] <;> exact fun h => by cases h
  have ha : UA (.Zombie p t n) (capA st s x) := by
    rcases hz with ⟨g, b, e, h64⟩ | ⟨e, et⟩ | ⟨n0, e⟩
    · rw [e]; exact UA.zombie_cnode p t g b n h64
    · rw [e, et]; exact UA.zombie_threadP p n
    · rw [e]; exact UA.zombie p t n0 n
  obtain ⟨G, par, hT, -, -⟩ := hm.1.tree
  refine ⟨⟨G, par, hT.set_cap hO hx hd (fun e => by cases e) hc0 ha⟩, fun u hu hc => ?_⟩
  rw [revocable_congr ((set_cap_links (st := st) (s := s) (w0 := zw p t) (w1 := n) hO hx u hu).2)]
  by_cases e : u = x
  · rw [e, capA_wr2_self hO hx hd] at hc; simp [isUtA] at hc
  · rw [capA_wr2_other hO hx hu e] at hc; exact hm.2 u hu hc

/-! ## `swap` with a null first slot -/

section swn
variable {G : List (List U64)} {par : U64 → Option U64}

set_option maxHeartbeats 1000000 in
/-- **`swap` of the slots' own caps, `x1` a member or a null linkless slot, `x2` a member, keeps the tree**
(ghost and parent map renamed by `Equiv.swap x1 x2`). -/
theorem cdt.swap.treeN (hO : OSOK T Ω Sg OS) {s : S} (hT : TreeA st OS G par s) (hN : NullLk st OS s)
    {x1 x2 : U64} {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ G.flatten) (hne : x1 ≠ x2)
    (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) (hc1 : capA st s x1 = c1)
    (hc2 : capA st s x2 = c2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => TreeA st OS (renG x1 x2 G) (Mdb.conjPar (Equiv.swap x1 x2) par) s' ⦄ := by
  have hM := hT.lk
  have h0 : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have o2 := inOS x2 hx2
  have nm : ∀ y ∈ OS, y ∉ G.flatten → capA st s y = .Null := fun y hy hn => by
    by_contra h; exact hn ((hM.members y).2 ⟨hy, h⟩)
  refine WP.spec_mono (cdt.swap.lrN hO h0 hM hN hx1 hx2 hne hs1 hs2 hc1 hc2) ?_
  rintro s' ⟨hL, e1, e2, ek⟩
  have hc : ∀ y ∈ OS, capA st s' (swp x1 x2 y) = capA st s y := by
    intro y hy
    unfold swp
    by_cases a1 : y = x1
    · rw [a1, if_pos rfl, e2, hc1]
    · rw [if_neg a1]
      by_cases a2 : y = x2
      · rw [a2, if_pos rfl, e1, hc2]
      · rw [if_neg a2]; exact ek y hy a1 a2
  have sw : ∀ y ∈ G.flatten, swp x1 x2 y ∈ OS := fun y hy => swp_os hx1 o2 (inOS y hy)
  have r1 : x1 ∉ G.flatten → ∀ y, y ∈ G.flatten → NxA st s y ≠ x1 ∧ L.mem s (wa y 16#u64) ≠ x1 :=
    fun n1 y hy => ⟨fun e => n1 (by rw [← e]; exact F.nxm y hy (by rw [e]; exact h0 x1 hx1)),
      fun e => n1 (by rw [← e]; exact F.pvm y hy (by rw [e]; exact h0 x1 hx1))⟩
  have key : ∀ y ∈ G.flatten,
      LkAbs.sN 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) x1 x2 (LkAbs.tr x1 x2 y) =
        LkAbs.tr x1 x2 (NxA st s y) ∧
      LkAbs.sP 0#u64 (fun z => L.mem s (wa z 16#u64)) (NxA st s) x1 x2 (LkAbs.tr x1 x2 y) =
        LkAbs.tr x1 x2 (L.mem s (wa y 16#u64)) := by
    intro y hy
    by_cases m1 : x1 ∈ G.flatten
    · exact LkAbs.sw_ok F m1 hx2 hne hy
    · obtain ⟨p1, q1⟩ := hN x1 hx1 (nm x1 hx1 m1)
      obtain ⟨a, b, -, -⟩ := LkAbs.sw_null F m1 (h0 x1 hx1) p1 q1 (r1 m1) hx2 hy
      exact ⟨a, b⟩
  refine ⟨hM.renN h0 hx1 o2 (fun y hy => by rw [hc y hy]) (fun y hy => ?_) (fun y hy => ?_),
    by rw [renG_eq]; exact hT.tree.conj _, ?_⟩
  · rw [(hL _ (sw y hy)).2, swp_tr, swp_tr]; exact (key y hy).1
  · rw [(hL _ (sw y hy)).1, swp_tr, swp_tr]; exact (key y hy).2
  · refine hT.ut.ren hT.parIn (Equiv.swap x1 x2) (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
    · rw [swap_eq_swp]; exact swp_os hx1 o2 hy
    · rw [Equiv.symm_swap, swap_eq_swp]; exact swp_os hx1 o2 hy
    · rw [swap_eq_swp, hc y hy]; exact UA.refl _

/-- **`cap_swap_for_delete`** with `x1` any `OS` slot (null ones linkless) and `x2` a member keeps a tree. -/
theorem cdt.cap_swap_for_delete.treeN (hO : OSOK T Ω Sg OS) {s : S} (hT : TreeA st OS G par s)
    (hN : NullLk st OS s) {x1 x2 : U64} (hx1 : x1 ∈ OS) (hx2 : x2 ∈ G.flatten) (hs1 : obj.sext48 x1 = ok x1)
    (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => ∃ G' : List (List U64), ∃ par' : U64 → Option U64,
      TreeA st OS G' par' s' ⦄ := by
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 ⟨G, par, hT⟩
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    exact WP.spec_mono (cdt.swap.treeN hO hT hN hx1 hx2 hne hs1 hs2 rfl rfl) fun s' h => ⟨_, _, h⟩

end swn

section zq
variable {Vc Ub D Fp : Set U64} {kb : U64} {Pt : Set U64} {K : capability.Cap → Prop} {Ty : S → Prop}
variable {A : Type _} {ar : machine.Arch A}

/-- **`swap`**: `cap_swap_for_delete` of two canonical domain slots, the second holding a `Zombie`, keeps `TR`. -/
theorem cdt.cap_swap_for_delete.trD (hO : OSOK T Ω Sg OS) (hDO : D ⊆ OS) (hDC : DCan D) {s : S}
    (hm : MdbST st OS s ∧ UtRev st OS s) {p y : U64} (hp : p ∈ D) (hy : y ∈ D)
    (hz : ∃ p' t n, obj.Slot.cap st y s = ok (.Zombie p' t n)) :
    cdt.cap_swap_for_delete st s p y ⦃ s' => MdbTU st OS s' ∧ UtRev st OS s' ⦄ := by
  obtain ⟨G, par, hM, -, -, hN, -, hTr, hU⟩ := hm.1
  have hT : TreeA st OS G par s := ⟨hM, hTr, hU⟩
  obtain ⟨p', t, n, hc⟩ := hz
  have hyc : capA st s y = .Zombie p' t n := okinj ((capA_eq s y).symm.trans hc)
  have hyG : y ∈ G.flatten := (hM.members y).2 ⟨hDO hy, by rw [hyc]; exact fun e => by cases e⟩
  exact WP.spec_mono (WP.spec_and (cdt.cap_swap_for_delete.treeN hO hT hN (hDO hp) hyG (hDC p hp) (hDC y hy))
    (cdt.cap_swap_for_delete.utRevN hO hO.nz hM hN hm.2 (hDO hp) hyG (hDC p hp) (hDC y hy)))
    fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩

set_option maxHeartbeats 1000000 in
/-- **`emp`**: `empty_slot` with a `ClOK` cleanup keeps `TR` under `JV` and `IrqStApart OS (ks s0)`. -/
theorem cdt.empty_slot.trJ (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hap : IrqStApart OS (L.ksb s0))
    (hm : MdbST st OS s ∧ UtRev st OS s) {a : A} {x : U64} (hx : x ∈ OS) {cl : capability.Cap} (hcl : ClOK cl) :
    cdt.empty_slot st ar s a x cl ⦃ r => MdbTU st OS r.1 ∧ UtRev st OS r.1 ⦄ := by
  obtain ⟨G, par, hT, hRO, hK⟩ := hm.1.tree
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hk : L.ksb s = L.ksb s0 := h.ksb
  rcases hcl with rfl | ⟨irq, rfl, hi⟩
  · have hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
        objects.post_cap_deletion st ar s1 a1 .Null ⦃ r => WritesIn st s1 r.1 (fun _ => False) ⦄ :=
      fun s1 a1 _ => by rw [pcd_null]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    exact WP.spec_mono (WP.spec_and (cdt.empty_slot.tree hO hT hRO hK hx (fun _ e => e.elim) hpcd)
      (cdt.empty_slot.utRev hO hO.nz hT.lk hRO hK hm.2 hx (fun _ e => e.elim) hpcd))
      fun _ ⟨⟨G', par', h1⟩, h2⟩ => ⟨⟨G', par', h1⟩, h2⟩
  · have hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
        objects.post_cap_deletion st ar s1 a1 (.IrqHandler irq) ⦃ r =>
          WritesIn st s1 r.1 (IrqStW (L.ksb s) irq) ⦄ :=
      fun s1 a1 k1 => WP.spec_mono (pcd_irq.wr hP s1 a1 irq hi) fun r ⟨o, ho, v, e⟩ => by
        rw [e]
        have al := ks_aligned (o := o) q (by omega) (by omega)
        rw [← k1] at al
        exact (writesIn_wr al).mono fun b eb => ⟨o, ho, by rw [eb, k1]⟩
    have hpw : ∀ b, IrqStW (L.ksb s) irq b → ¬ InOS OS b := by
      rintro b ⟨o, ho, eb⟩ ⟨y, hy, h1, h2⟩
      exact hap o (by omega) (by omega) y hy ⟨by rw [← hk, ← eb]; exact h1, by rw [← hk, ← eb]; exact h2⟩
    exact WP.spec_mono (WP.spec_and (cdt.empty_slot.tree hO hT hRO hK hx hpw hpcd)
      (cdt.empty_slot.utRev hO hO.nz hT.lk hRO hK hm.2 hx hpw hpcd))
      fun _ ⟨⟨G', par', h1⟩, h2⟩ => ⟨⟨G', par', h1⟩, h2⟩

set_option maxHeartbeats 4000000 in
/-- **`delete_one` of an IRQ-node slot holding a notification or `Null` keeps `TR`** (`cdt.delete_one.mdbS`'s
proof, the `empty_slot` step by `empty_slot.tree` / `.utRev`). -/
theorem cdt.delete_one.tr (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    {isl : U64} (hisl : isl ∈ OS) (hN : ∀ c, obj.Slot.cap st isl s = ok c → IrqNt c)
    (hm : MdbST st OS s ∧ UtRev st OS s) :
    cdt.delete_one st ar s a isl ⦃ r => MdbTU st OS r.1 ∧ UtRev st OS r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.delete_one
  obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st isl s hS)
  rw [hc, bind_ok]
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 ⟨hm.1.tu, hm.2⟩
  refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s isl c hS) fun fin _ => ?_
  have hl : ZL c := by
    rcases hN c hc with ⟨n, b0, b1, b2, rfl⟩ | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨n, b0, b1, b2, rfl⟩))
    · exact zl_null
  have hnI : ∀ i, c ≠ .IrqHandler i := by
    rcases hN c hc with ⟨n, b0, b1, b2, rfl⟩ | rfl <;> intro i e <;> cases e
  rw [← fc_eq_fco ar s a fin hnI]
  refine WP.spec_bind (finL hP hO hA hV h hisl hc hl a fin) ?_
  rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨e2, h2, k2⟩
  try simp only at e2 h2 k2
  try dsimp only
  have m2 := MdbST.keepO hO hm.1 k2
  have r2 := hm.2.keep k2
  obtain ⟨G, par, hT, hRO, hK⟩ := m2.tree
  have hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s2 →
      objects.post_cap_deletion st ar s1 a1 .Null ⦃ r => WritesIn st s1 r.1 (fun _ => False) ⦄ :=
    fun s1 a1 _ => by rw [pcd_null]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  exact WP.spec_mono (WP.spec_and (cdt.empty_slot.tree hO hT hRO hK hisl (fun _ e => e.elim) hpcd)
    (cdt.empty_slot.utRev hO hO.nz hT.lk hRO hK r2 hisl (fun _ e => e.elim) hpcd))
    fun _ ⟨⟨G', par', h1⟩, h3⟩ => ⟨⟨G', par', h1⟩, h3⟩

set_option maxHeartbeats 2000000 in
/-- **A final `IrqHandler` cap's `finalise_cap` keeps `TR`** (`finalise_cap.irq_mdbS`'s proof). -/
theorem finalise_cap.irq_tr (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    {irq kb' : U64} (hIO : irqSlotA kb' irq ∈ OS)
    (hN : ∀ c, obj.Slot.cap st (irqSlotA kb' irq) s = ok c → IrqNt c) (hk : L.ksb s = kb')
    (hm : MdbST st OS s ∧ UtRev st OS s) :
    objects.finalise_cap st ar s a (.IrqHandler irq) true false ⦃ r => r.1 = (.Null, .IrqHandler irq) ∧
      (MdbTU st OS r.2.1 ∧ UtRev st OS r.2.1) ⦄ := by
  unfold objects.finalise_cap
  simp only [↓reduceIte]
  unfold interrupt.deleting_irq_handler
  refine WP.spec_bind (Pₘ := fun r : S × A => MdbTU st OS r.1 ∧ UtRev st OS r.1) ?_ ?_
  · refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl e => ?_
    subst e
    rw [hk]
    exact cdt.delete_one.tr hP hO hA hV h hIO hN hm
  · rintro ⟨s2, a2⟩ h2
    first
    | (simp only [objects.finalise_cap_object, ↓reduceIte, WP.spec_ok]; exact ⟨rfl, h2⟩)
    | (simp only [objects.finalise_cap_object, ↓reduceIte]; exact (WP.spec_ok _).2 ⟨rfl, h2⟩)
    | (simp [objects.finalise_cap_object, WP.spec_ok]; exact h2)

set_option maxHeartbeats 4000000 in
/-- **`fin`** for `TR` (`finXQM`'s case split): the finalisation of a `ZQ` cap keeps `TR`, and a `Zombie` remainder
leaves the slot `ZrT`. -/
theorem finXQT (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hK : FinKT st ar kb Pt Ty K) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hIO : IrqOK OS D (L.ksb s0))
    (hN : IrqN st (L.ksb s0) s) (hY : Ty s) (hk : L.ksb s = kb) {x : U64} (hx : x ∈ OS)
    {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c)
    (hX : ZQ K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x c) (a : A) (fin : Bool)
    (hm : MdbST st OS s ∧ UtRev st OS s) :
    objects.finalise_cap st ar s a c fin false ⦃ r => (MdbTU st OS r.2.1 ∧ UtRev st OS r.2.1) ∧
      ∀ p t n, r.1.1 = .Zombie p t n → ZrT st r.2.1 x p t ⦄ := by
  have hcx : capA st s x = c := okinj ((capA_eq s x).symm.trans hc)
  have h00 : MdbTU st OS s ∧ UtRev st OS s := ⟨hm.1.tu, hm.2⟩
  have hk0 : ∀ {s' : S}, OSKeep st OS s s' → MdbTU st OS s' ∧ UtRev st OS s' := fun k => TR.keep h00 k
  rcases hX with ⟨hz, -⟩ | ⟨-, hk'⟩
  swap
  · refine WP.spec_mono (hK s a c fin hY hk hk') ?_
    rintro r ⟨e, w, -⟩
    obtain ⟨-, k2, -, -⟩ := JV.vsr hO hV hR h w
    exact ⟨hk0 k2, fun p t n e' => by simp [e] at e'⟩
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  rcases hz with ((hl | ⟨p, r, g, b, rfl, -⟩ | ⟨p, t, n, rfl, -⟩) | ⟨p, rfl, hid, hcov⟩ | ⟨v, rfl, hvV⟩) |
    ⟨p, b, rfl, hp, hp0, hpI⟩ | ⟨irq, rfl⟩
  · exact WP.spec_mono (finL hP hO hA hV h hx hc hl a fin) fun r ⟨e, _, k2⟩ =>
      ⟨hk0 k2, fun p t n e' => by simp [e] at e'⟩
  · cases fin
    · rw [fin_cnode.f, WP.spec_ok]
      exact ⟨h00, fun p' t' n' e' => by simp at e'⟩
    · refine WP.spec_mono (fin_cnode.z ar s a p r g b true) ?_
      rintro q ⟨e1, -, e3⟩
      rw [e1]
      refine ⟨h00, fun p' t' n' e' => ?_⟩
      have hw : CapRt.EncWf (capA st s x) := CapRt.decodeF_encWf _ _
      rw [hcx] at hw
      rcases e3 with e3 | ⟨n, e3, -⟩
      · rw [e3] at e'; cases e'
      · rw [e3] at e'
        simp only [capability.Cap.Zombie.injEq] at e'
        obtain ⟨rfl, rfl, -⟩ := e'
        exact Or.inl ⟨g, b, hcx, hw.2.1⟩
  · rw [fin_zombie.z, WP.spec_ok]
    refine ⟨h00, fun p' t' n' e' => ?_⟩
    simp only [capability.Cap.Zombie.injEq] at e'
    obtain ⟨rfl, rfl, -⟩ := e'
    exact Or.inr (Or.inr ⟨n, hcx⟩)
  · have e := fin_cap_eq_obj (st := st) (ar := ar) (s := s) (a := a) (c := .Thread p) (fin := fin) (ex := false)
      (by simp)
    have R := fin_thread.rem (st := st) hP s a p fin
    rw [← e] at R
    refine WP.spec_mono (WP.spec_and (finXT hP hO hA hV h hx hc (Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩)) a fin) R) ?_
    rintro r ⟨⟨-, -, k2, -, -⟩, e2⟩
    refine ⟨hk0 k2, fun p' t n e' => ?_⟩
    rw [e2] at e'
    cases fin
    · simp at e'
    · simp only [↓reduceIte, capability.Cap.Zombie.injEq] at e'
      obtain ⟨rfl, rfl, -⟩ := e'
      exact Or.inr (Or.inl ⟨by rw [k2.capA hx, hcx], rfl⟩)
  · refine WP.spec_mono (WP.spec_and (finXT (D := D) hP hO hA hV h hx hc (Or.inr (Or.inr ⟨v, rfl, hvV⟩)) a fin)
      (finJV_vcpu hP hO hV h hc hvV a _ fin hc)) ?_
    rintro r ⟨⟨-, -, k2, -, -⟩, e2, -⟩
    exact ⟨hk0 k2, fun p t n e' => by simp [e2] at e'⟩
  · have hk2 := scpl_of h hc hp hp0 hpI rfl
    refine WP.spec_mono (WP.spec_and (osk_sc hP hO hA h a fin hk2 hc) (finJV_sc hP hO hA hV h hk2 a _ fin hc)) ?_
    rintro r ⟨⟨k2, -, -⟩, e2, -⟩
    exact ⟨hk0 k2, fun p t n e' => by simp [e2] at e'⟩
  · have hi : irq.val < 5376 := hty.1.2.1 irq rfl
    cases fin
    · rw [finalise_cap.nonfin ar s a (irqH_nonfin irq), WP.spec_ok]
      exact ⟨h00, fun _ _ _ e' => by simp at e'⟩
    · refine WP.spec_mono (finalise_cap.irq_tr hP hO hA hV h (hIO.1 irq hi) (hN irq hi) h.ksb hm) ?_
      rintro r ⟨e, m2⟩
      exact ⟨m2, fun p t n e' => by simp [e] at e'⟩

/-! ## The field and the deletions -/

/-- **The loop field for `MdbST ∧ UtRev`** (module docstring). -/
theorem LoopMZ.mdbSTR (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D) {s0 : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0))
    (hap : IrqStApart OS (L.ksb s0)) :
    LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) (XQF st K Vc D Scs Fp Ty (L.ksb s0))
      (fun s x p t => ZrA st OS s x p t ∧ ZrT st s x p t) (fun s => MdbST st OS s ∧ UtRev st OS s) where
  fin s a x c f hC m hx hc hX hf := WP.spec_mono (WP.spec_and
    (finXQM hP hO hA hV hR hK hC hIO hX.2.2 hX.2.1 hC.ksb hx hc hX.1 a f m.1.mdbS hf)
    (finXQT hP hO hA hV hR hK hC hIO hX.2.2 hX.2.1 hC.ksb hx hc hX.1 a f m))
    fun _ ⟨⟨m1, z1⟩, ⟨m2, z2⟩⟩ => ⟨⟨MdbST.of hO.nz m1 m2.1, m2.2⟩, fun p t n e => ⟨z1 p t n e, z2 p t n e⟩⟩
  zz _ _ _ _ _ hc := ⟨zr_z hc, Or.inr (Or.inr ⟨_, okinj ((capA_eq _ _).symm.trans hc)⟩)⟩
  setz _ _ _ _ _ _ m hx hp hz := WP.spec_mono (WP.spec_and (obj.Slot.set_cap.mdbZ hO m.1.mdbS hx hp hz.1)
    (obj.Slot.set_cap.trZ hO m hx hp hz.2)) fun _ ⟨h1, h2⟩ => ⟨MdbST.of hO.nz h1 h2.1, h2.2⟩
  swap _ _ _ _ m hp hy _ hz := WP.spec_mono (WP.spec_and (cdt.cap_swap_for_delete.mdbS hO hDO hDC m.1.mdbS hp hy hz)
    (cdt.cap_swap_for_delete.trD hO hDO hDC m hp hy hz)) fun _ ⟨h1, h2⟩ => ⟨MdbST.of hO.nz h1 h2.1, h2.2⟩
  pre _ _ h m := WP.spec_mono (sched.preemption_point.jv hP hO hV h (by rw [h.ksb]; exact hW))
    fun _ ⟨_, k, _⟩ => ⟨MdbST.keepO hO m.1 k, m.2.keep k⟩
  emp _ _ _ _ h m hx hcl := WP.spec_mono (WP.spec_and (cdt.empty_slot.mdbS hP hO h hap m.1.mdbS hx hcl)
    (cdt.empty_slot.trJ hP hO h hap m hx hcl)) fun _ ⟨h1, h2⟩ => ⟨MdbST.of hO.nz h1 h2.1, h2.2⟩

set_option maxHeartbeats 1000000 in
/-- **`MdbST ∧ UtRev` through gen 41's exposed deletion** (`cdt.delete.zqIGTMZ` at `LoopMZ.mdbSTR`). -/
theorem cdt.delete.zqIGTmdbSTR (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    (hm : MdbST st OS s ∧ UtRev st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧
      (MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ⦄ :=
  cdt.delete.zqIGTMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY
    (LoopMZ.mdbSTR hP hO hA hV hDO hDC hR hK hW hIO hap) hm

set_option maxHeartbeats 1000000 in
/-- **`MdbST ∧ UtRev` through gen 39's deferred deletion** (`cdt.delete_deferred.zqGMZ` at `LoopMZ.mdbSTR`). -/
theorem cdt.delete_deferred.zqGmdbSTR (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    (hm : MdbST st OS s ∧ UtRev st OS s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ (MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ⦄ :=
  cdt.delete_deferred.zqGMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY
    (LoopMZ.mdbSTR hP hO hA hV hDO hDC hR hK hW hIO hap) hm

end zq

section del
variable {Vc Ub D Fp : Set U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **`cdt.delete.zqETM` with `MdbST ∧ UtRev`** (MdbFinR's instantiation). -/
theorem cdt.delete.zqETMR (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (hm : MdbST st OS s ∧ UtRev st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
      (MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ⦄ :=
  cdt.delete.zqETG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hX hN hY h2
    (LoopMZ.mdbSTR hP hO hA hV hDO hDC hR (finKT_s2 hP hPl hR hPp hTb hTe hH hS) hW hIO hap) hm

set_option maxHeartbeats 1000000 in
/-- **`cdt.delete.threadQETM` with `MdbST ∧ UtRev`.** -/
theorem cdt.delete.threadQETMR (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) (hm : MdbST st OS s ∧ UtRev st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
      (MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ⦄ :=
  cdt.delete.threadQETG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hN hY h2 hc hid hpF hcov
    (LoopMZ.mdbSTR hP hO hA hV hDO hDC hR (finKT_s2 hP hPl hR hPp hTb hTe hH hS) hW hIO hap) hm

/-- **`cdt.delete.zqETRM` with `MdbST ∧ UtRev`.** -/
theorem cdt.delete.zqETRMR (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTyR st (L.ksb s0) Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hm : MdbST st OS s ∧ UtRev st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
      (MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ⦄ :=
  cdt.delete.zqETRG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hX hN hY h2
    (LoopMZ.mdbSTR hP hO hA hV hDO hDC hR (finKT_s2 hP hPl hR hPp (VsRt_sub.trans hTb) ((gran_mono S2Rt_sub).trans hTe)
      (hH.mono VsRt_sub (hr_rt hH.sub)) (S2OK.sub hS S2Rt_sub)) hW hIO hap) hm

/-- **`cdt.delete.threadQETRM` with `MdbST ∧ UtRev`.** -/
theorem cdt.delete.threadQETRMR (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTyR st (L.ksb s0) Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) (hm : MdbST st OS s ∧ UtRev st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
      (MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ⦄ :=
  cdt.delete.threadQETRG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hN hY h2 hc hid hpF hcov
    (LoopMZ.mdbSTR hP hO hA hV hDO hDC hR (finKT_s2 hP hPl hR hPp (VsRt_sub.trans hTb) ((gran_mono S2Rt_sub).trans hTe)
      (hH.mono VsRt_sub (hr_rt hH.sub)) (S2OK.sub hS S2Rt_sub)) hW hIO hap) hm

end del

end ST
end R
end W7

end

end Fl4ProofsA64.P1

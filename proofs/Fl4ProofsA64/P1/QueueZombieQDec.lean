/-
P1 (aarch64, gen 38): **the CNode `Delete` decode over the generic `ZQ` loop, and the entry-fact forms** of the
`ZS`, `ZP` and `ZQ` decodes.

* **`syscall.decode_invocation.del_zq`**: QueueZombiePDec's `del_zp` text over any finaliser class `K` / typing
  `Ty` (QueueZombieQ); `Ty` at the decode start is kept by the restart (a `VsZ` step: the restart writes only words
  inside the TCBs and nodes, and `VrOK` places the `VsR` words in `Ω`).
* **`syscall.decode_invocation.del_zs_ent`**: gen 36/37's `ZS` decode from [J] `SlotTyEntZ` at an `EntAt` start —
  no new premise (all of `del_zs`'s placement facts are fields of `SlotTyEntZ`).
* **[J] `SlotTyEntP`** (new, named): [J] `SlotTyEntZ`'s fields and, for the same `OS`, `Vc`, `Ub`, ghost VSpace
  sets `Pp ⊆ Pt`, `Tb ⊆ Pt`, a level `Lv`, with `VrOK … (ks e) Pt` (QueueVsWs), `VsTy (ks e) Pp Tb Lv e`
  (QueueVsTy) and `VsEntApart` (no word the entry prefix writes is a `VsR` word). **`SlotTyEntP.entAt`**: its facts
  at every `EntAt` state. Consumers: **`del_zp_ent`**, **`del_zqV_ent`**, **`del_zqT_ent`**.

**Source for [J] `SlotTyEntP`** (crates/fl4-core/src/…):
* `VrOK` (placement of the `VsR` words): page tables, VSpace roots and ASID pools are objects of their own,
  retyped from untyped memory by `create_new_objects` (objects.rs:528), disjoint from CNodes / TCBs / SCs / VCPUs /
  endpoints / frames; the ASID table is the kernel-global block `ks + ASID_TABLE` (arch/aarch64/vspace.rs:219–222,
  `asid_table`), after the 128 nodes and above the scalar area and the IRQ node (`VrOK.ks`: `o ≥ 223488`).
* `VsTy`: pool entries are written only by the ASID assignment with a root of tag 0 (`Pml4`), 1 (`Ept`) or 2
  (`HighVSpace`) (arch/aarch64/vspace.rs:1239–1241) and cleared by `delete_asid` (529–549); `VsTy.pool` asks
  nothing of tag-1 entries (Stage-2 roots are not in `Tb`). Table descriptors are written only by the page-table
  map paths (1134–1145, 1150–1166: at the slot `lookup_pt_slot` reached, only when that slot is invalid, with an
  unmapped cap's table — so a table is mapped once, at one level) and by `init_high_vspace` (283–297: entry 511 of a
  `HighVSpace` root, its own level-1 table at `base + 4096`, and the kernel's TTBR1 level-0 entries 0..510 — so `Tb`
  holds those kernel tables at level 1, `Pt` their objects); they are cleared by `unmap_page_table` (474–517).
  Leaf descriptors with `e & 3 = 3` sit at level 3 only, where `desc` asks nothing.
* `VsEntApart`: the entry prefix writes the current thread's `FAULT_IP` register word and the current node's words
  (QueueEntry `EntW`) — TCB and node words, none of them a page-table / pool word or an ASID-table word.
Checked not false on reachable states as far as the source shows: the ghost sets are chosen per entry state (the
live pools, the tables reachable from tag-0 / tag-2 pool entries with their depth, `Pt` their 4 KiB objects).
`VsS1` (QueuePtTy: Stage-1 pools only) is **not** part of the [J] (false once a Stage-2 VSpace is assigned); the
page-table decode `del_zqT_ent` takes it as a case hypothesis of the decode start.
-/
import Fl4ProofsA64.P1.QueueVsK
import Fl4ProofsA64.P1.QueueZombiePDec
import Fl4ProofsA64.P1.QueueZombieS
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

section deq
variable {OS Vc Ub : Set U64} {Dm Fp : Set U64}

/-- **The generic `ZQ` loop at decode level** (domain and target stated at the decode start, its idle word and idle
`SC` field; `Ty` at the decode start). -/
theorem syscall.decode_invocation.del_zq {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : Dm ⊆ OS) (hDC : DCan Dm)
    {Pt : Set U64} {K : capability.Cap → Prop} {Ty : S → Prop}
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s) Pt)
    (hK : FinK st ar (L.ksb s) Pt Ty K) (hTy : TyZ st (L.ksb s) Pt Ty)
    (hW : WuApart OS (L.ksb s)) (hIO : IrqOK OS Dm (L.ksb s))
    (hap : IrqStApart OS (L.ksb s)) (hN : IrqN st (L.ksb s) s) (hY : Ty s)
    (hD : DomQ st K Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => XQ st K Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧
      ¬ IslN (L.ksb s) x) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ :=
  syscall.decode_invocation.del_genS hO hV a len slot cap blk call don fp buf extra D hT hv hf hslot hcap hk
    fun x hx hkx s1 h1 k1 o1 i1 K1 => by
      have q := D.bxi.1.choose_spec.choose_spec
      have hIT : L.idleW s ∈ T := q.idleT
      have hY1 : Ty s1 := hTy _ _ hY (VsZ.of_keep fun b hb => o1 b (q.omega _ (hR.om b hb)))
      exact cdt.delete.zqI hP hO hA hV hDO hDC hR hK hTy hW hIO hap h1 hx hkx.2
        (hD.oka hIO.2 hDO (OKA.of_osk k1)) (hkx.1.oka hx hkx.2 (OKA.of_osk k1)) i1 (K1 _ hIT)
        (hN.oka hIO (OKA.of_osk k1)) hY1

/-- **The `ZS` decode on [J] `SlotTyEntZ`**: at an `EntAt` decode start the placement facts come from the entry
fact; the domain facts remain case hypotheses of the decode start. -/
theorem syscall.decode_invocation.del_zs_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntZ st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64) (Dm : Set U64),
        Dm ⊆ OS → DCan Dm → IrqOK OS Dm (L.ksb s) → IrqN st (L.ksb s) s →
        DomS st Vc Dm Scs (L.idleW s) (L.mem s (scA (L.idleW s))) s →
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => XS st Vc Dm Scs (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧ ¬ IslN (L.ksb s) x) s
          cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
            VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, hO, hT, -, hap, hA, hV, hv, hW⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, fun a len slot blk call don fp buf Dm hDO hDC hIO hN hD hf hs hc hk =>
    syscall.decode_invocation.del_zs hP hO hA hV hDO hDC a len slot cap blk call don fp buf extra D hT hv hW hIO
      hap hN hD hf hs hc hk⟩

/-! ## The entry fact with the VSpace typing -/

/-- No word the entry prefix writes is a `VsR` word. -/
def VsEntApart (st : machine.Store S) [L : LawfulStore st] (e : S) (kb : U64) (Pt : Set U64) : Prop :=
  ∀ b, EntW st e b → ¬ VsR kb Pt b

/-- **[J] (a64) `SlotTyEntP`**: [J] `SlotTyEntZ`'s fields and, for the same `OS`, `Vc`, `Ub`, ghost VSpace sets
`Pp ⊆ Pt`, `Tb ⊆ Pt` and a level `Lv` with `VrOK … (ks e) Pt`, `VsTy (ks e) Pp Tb Lv e` and `VsEntApart` (module
docstring for the source, file:line). At `P3Ok` states only, over ghost sets, not over a word class. -/
def SlotTyEntP (st : machine.Store S) [L : LawfulStore st] (T Cs Ω Sg : Set U64) (H : Heap) (Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ e, P3Ok e → ∃ OS Vc Ub Pp Tb Pt : Set U64, ∃ Lv : U64 → Nat,
    OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS e ∧ EntApart st e OS ∧
    (∀ t ∈ T, t ∈ OS) ∧ IrqStApart OS (L.ksb e) ∧ ScApart Scs Z OS ∧ VcOK T Scs Z OS Vc Ub ∧
    VcTy st T Cs Ω H Sg Scs Z Vc Ub e ∧ VcEntApart st T e Vc ∧ WuApart OS (L.ksb e) ∧
    Pp ⊆ Pt ∧ Tb ⊆ Pt ∧ VrOK Ω Sg Scs Z OS Vc Ub (L.ksb e) Pt ∧ VsTy st (L.ksb e) Pp Tb Lv e ∧
    VsEntApart st e (L.ksb e) Pt

/-- `SlotTyEntP` implies `SlotTyEntZ` (fields dropped). -/
theorem SlotTyEntP.toZ (h : SlotTyEntP st T Cs Ω Sg H Rp Scs Nt Z P3Ok) :
    SlotTyEntZ st T Cs Ω Sg H Rp Scs Nt Z P3Ok := fun e he => by
  obtain ⟨OS, Vc, Ub, -, -, -, -, a, b, c, d, f, g, i, j, k, l, -⟩ := h e he
  exact ⟨OS, Vc, Ub, a, b, c, d, f, g, i, j, k, l⟩

/-- **`SlotTyEntP` at every `EntAt` state** (QueueZombieV's `SlotTyEntZ.entAt` text, with `VrOK` and `VsTy`
carried: the entry prefix writes no `VsR` word, the `ks` base is kept). -/
theorem SlotTyEntP.entAt (hJ : SlotTyEntP st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s)
    (hTP : TcbPlaced T) :
    ∃ OS Vc Ub Pp Tb Pt : Set U64, ∃ Lv : U64 → Nat,
      OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ (∀ t ∈ T, t ∈ OS) ∧ IrqStApart OS (L.ksb s) ∧
      ScApart Scs Z OS ∧ VcOK T Scs Z OS Vc Ub ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧ WuApart OS (L.ksb s) ∧
      Pp ⊆ Pt ∧ Tb ⊆ Pt ∧ VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s) Pt ∧ VsTy st (L.ksb s) Pp Tb Lv s := by
  obtain ⟨e, he, hw⟩ := hE
  obtain ⟨OS'', Vc', Ub', Pp, Tb, Pt, Lv, hO', hT', hA', hc', hap', hsc', hV', hv', hVA', hwu, hPp, hTb, hR, hY,
    hVE⟩ := hJ e he
  have hY' : VsTy st (L.ksb e) Pp Tb Lv s :=
    hY.keepZ hPp hTb (VsZ.of_keep fun b hb => hw.mem_eq (hR.al b hb) fun hb' => hVE b hb' hb)
  refine ⟨OS'', Vc', Ub', Pp, Tb, Pt, Lv, hO', fun y hy => ?_, hc', by rw [hw.1]; exact hap', hsc', hV', hv'.keep ?_,
    by rw [hw.1]; exact hwu, hPp, hTb, by rw [hw.1]; exact hR, by rw [hw.1]; exact hY'⟩
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

/-- **The `ZP` decode on [J] `SlotTyEntP`** (gen 37's frames and VSpace roots at frame positions): the placement
facts and `VsTy` come from the entry fact; the domain facts remain case hypotheses of the decode start. -/
theorem syscall.decode_invocation.del_zp_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntP st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64) (Dm Fp : Set U64),
        Dm ⊆ OS → DCan Dm → IrqOK OS Dm (L.ksb s) → IrqN st (L.ksb s) s →
        DomP st Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s →
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => XP st Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧ ¬ IslN (L.ksb s) x) s
          cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
            VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, Pp, Tb, Pt, Lv, hO, hT, -, hap, hA, hV, hv, hW, hPp, hTb, hR, hY⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, fun a len slot blk call don fp buf Dm Fp hDO hDC hIO hN hD hf hs hc hk =>
    syscall.decode_invocation.del_zp hP hO hA hV hDO hDC hPp hTb a len slot cap blk call don fp buf extra D hT hv
      hR hW hIO hap hN hY hD hf hs hc hk⟩

/-- **The `ZQ VsQ` decode on [J] `SlotTyEntP`** (ASID pools, device frames, frames and VSpace roots at frame
positions). -/
theorem syscall.decode_invocation.del_zqV_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntP st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64) (Dm Fp : Set U64),
        Dm ⊆ OS → DCan Dm → IrqOK OS Dm (L.ksb s) → IrqN st (L.ksb s) s →
        DomQ st VsQ Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s →
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => XQ st VsQ Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧
          ¬ IslN (L.ksb s) x) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
            VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, Pp, Tb, Pt, Lv, hO, hT, -, hap, hA, hV, hv, hW, hPp, hTb, hR, hY⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, fun a len slot blk call don fp buf Dm Fp hDO hDC hIO hN hD hf hs hc hk =>
    syscall.decode_invocation.del_zq hP hO hA hV hDO hDC a len slot cap blk call don fp buf extra D hT hv hR
      (finK_vs hP hR hPp hTb) (tyz_vs hPp hTb) hW hIO hap hN hY hD hf hs hc hk⟩

/-- **The `ZQ PtQ` decode on [J] `SlotTyEntP`** (page-table caps as well): the entry fact's pools `Pp` are
exposed, and Stage-1 pools only (`VsS1 st Pp s`) is a case hypothesis of the decode start. -/
theorem syscall.decode_invocation.del_zqT_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntP st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub Pp : Set U64, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64) (Dm Fp : Set U64),
        VsS1 st Pp s → Dm ⊆ OS → DCan Dm → IrqOK OS Dm (L.ksb s) → IrqN st (L.ksb s) s →
        DomQ st PtQ Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s →
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => XQ st PtQ Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧
          ¬ IslN (L.ksb s) x) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
            VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, Pp, Tb, Pt, Lv, hO, hT, -, hap, hA, hV, hv, hW, hPp, hTb, hR, hY⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, Pp, hO, hT, hv, fun a len slot blk call don fp buf Dm Fp h1 hDO hDC hIO hN hD hf hs hc hk =>
    syscall.decode_invocation.del_zq (Ty := fun s' => VsTy st (L.ksb s) Pp Tb Lv s' ∧ VsS1 st Pp s') hP hO hA hV
      hDO hDC a len slot cap blk call don fp buf extra D hT hv hR (finK_pt hP hR hPp hTb) (tyz_s1 hPp hTb) hW hIO
      hap hN ⟨hY, h1⟩ hD hf hs hc hk⟩

end deq

end ST
end R
end W7

end

end Fl4ProofsA64.P1

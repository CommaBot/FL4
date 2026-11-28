/-
P1 (aarch64, gen 40): **the Stage-2 finalisers as an instance of the generic Zombie loop** (QueueZombieQ's
`FinKT` / `TyK`): `Ept` caps, Stage-2-mapped frames and page tables of Stage-2 VSpaces — inside covered slots, as
direct targets, and at decode level (from the decode start and from gen 38's [J] `SlotTyEntP`).

* **`S2Q`** = QueueVsK's `PtQ` (frames, VSpace roots, `HighVSpace` roots, ASID pools, device frames, page tables)
  ∨ `Ept` caps (any level) ∨ Stage-2-mapped frames (`is_ept`, device or not). Page-table caps now run through all
  three branches of `unmap_page_table` (QueueS2Ty's `vspace.unmap_page_table.s2`), the Stage-2 one included.
* Typing `VsTy ∧ S2Ty` over one 4 KiB word set `Pt` (the loop's `VsR kb Pt`) with `Pp ⊆ Pt`, `Tb ⊆ Pt` and the
  granules of the sized Stage-2 objects `Gran Te bits ⊆ Pt`; `n = hPl.ipa` (the [P] constant of `ArchPlat`).
* **`finKT_s2`**, **`tyk_s2`** (the class facts, proved); tops **`cdt.delete.zqE`** (the loop: Zombie / final thread
  / CNode deletions whose covered slots hold `S2Q` caps at frame positions), **`cdt.delete.threadQE`** (e.g. a VCPU
  thread whose Stage-2 VSpace, Stage-2 tables and frames sit in its domain), **`cdt.delete.s2P`** (a direct target:
  any `S2Q` cap, via `finJV_kt`).
* Decode: **`syscall.decode_invocation.del_zqE`** (from the decode start) and **`del_zqE_ent`** (on [J]
  `SlotTyEntP`: its `Pp`, `Tb`, `Lv`, `Pt` exposed; the Stage-2 objects' placement `VrOK … (Gran Te bits)`
  (`VrOK.union`), `HrOK`, `S2OK` state-free case hypotheses, `S2Ty` a case hypothesis of the decode start) — **no
  new [J]**.

Named premises: [P] `ArchPlat.s2_ipa_bits_const` (QueueS2Ty), consumed by every theorem here through `hPl`. Case
hypotheses (state-free, or facts of the start state): `HrOK (ks) Pp Tb Lv Hr`, `S2OK Te bits Hr`,
`Gran Te bits ⊆ Pt`, `VrOK … (ks) Pt`, `VsTy`, `S2Ty` at the start state; justification in QueueS2Ty's docstring
(objects retyped disjointly, objects.rs `create_new_objects`; pool / descriptor writers in vspace.rs / ept.rs).
-/
import Fl4ProofsA64.P1.QueueS2Ty
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **The VSpace class with the Stage-2 kinds** (module docstring). -/
def S2Q (c : capability.Cap) : Prop :=
  PtQ c ∨ (∃ p l m ad v, c = .Ept p l m ad v) ∨
    (∃ ptr size rights dev mapped asid vaddr, c = .Frame ptr size rights dev mapped true asid vaddr)

section s2k
variable {OS Vc Ub D Fp : Set U64} {kb : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **A `Wr0` step of words other than the `R + 4088` words keeps `VsTy ∧ S2Ty`** and writes only `VsR` words. -/
theorem ty_wr0s {n : U64} (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hO : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    {X : Set U64} (hX : X ⊆ Pt) (hne : ∀ b, PtW X b → ∀ R ∈ Hr, b ≠ wa R 4088#u64) {s s' : S}
    (hY : VsTy st kb Pp Tb Lv s ∧ S2Ty st n Pp Hr Te Re bits s) (z : Wr0 st X s s') :
    WritesIn st s s' (VsR kb Pt) ∧ (VsTy st kb Pp Tb Lv s' ∧ S2Ty st n Pp Hr Te Re bits s') := by
  have z' := Wr0.mono hX z
  obtain ⟨w, v⟩ := wr0_vs hR z'
  have k : HrW st Hr s s' := Wr0.hrw (fun b hb => hR.al b (Or.inl (ptw_mono hX hb)))
    (fun R hRm => hR.al _ (hr_vsr hTb hO hRm)) hne z
  exact ⟨w, hY.1.keepZ hPp hTb v, hY.2.keep hPp hTe hS v k⟩

/-- Words of Stage-1 tables outside `Hr` and of Stage-2 objects are no `R + 4088` word. -/
theorem s2_ne (hO : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) {b : U64} (hb : PtW (TbO Tb Hr ∪ Gran Te bits) b) :
    ∀ R ∈ Hr, b ≠ wa R 4088#u64 := by
  rcases ptw_union hb with h | h
  · exact hO.tbo h
  · exact hS.hr b (gran_ptwb hS.sz h)

/-- **`FinKT` of `S2Q` over `VsTy ∧ S2Ty`**: every VSpace kind, Stage-2 ones included. -/
theorem finKT_s2 (hP : P0.ArchTotal ar) (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hPp : Pp ⊆ Pt)
    (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hO : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) :
    FinKT st ar kb Pt (fun s => VsTy st kb Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) S2Q := by
  intro s a c fin hY hk hc
  have hTO : TbO Tb Hr ⊆ Pt := fun _ h => hTb h.1
  have hU : TbO Tb Hr ∪ Gran Te bits ⊆ Pt := fun _ h => h.elim (fun h' => hTO h') (fun h' => hTe h')
  have tW : ∀ (X : Set U64), X ⊆ Pt → (∀ b, PtW X b → ∀ R ∈ Hr, b ≠ wa R 4088#u64) →
      ∀ r : (capability.Cap × capability.Cap) × S × A,
      r.1 = (.Null, .Null) ∧ Wr0 st X s r.2.1 → r.1 = (.Null, .Null) ∧
        WritesIn st s r.2.1 (VsR kb Pt) ∧
          (VsTy st kb Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1) :=
    fun X hX hne r ⟨e, z⟩ => ⟨e, ty_wr0s hR hPp hTb hTe hO hS hX hne hY z⟩
  have tT := tW _ hTO fun b hb => hO.tbo hb
  have tP := tW _ hPp fun b hb => hO.ppw hb
  have tU := tW _ hU fun b hb => s2_ne hO hS hb
  have tG := tW _ hTe fun b hb => hS.hr b (gran_ptwb hS.sz hb)
  have hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64) := fun R hRm => hR.al _ (hr_vsr hTb hO hRm)
  rcases hc with ((((⟨ptr, size, rights, mapped, asid, vaddr, rfl⟩ | ⟨p, m, ad, rfl⟩ | ⟨p, m, ad, rfl⟩) |
    ⟨p, b, rfl⟩ | ⟨ptr, size, rights, mapped, asid, vaddr, rfl⟩) | ⟨p, m, ad, v, rfl⟩ | ⟨p, m, ad, v, rfl⟩ |
    ⟨p, m, ad, v, rfl⟩) | ⟨p, l, m, ad, v, rfl⟩ | ⟨ptr, size, rights, dev, mapped, asid, vaddr, rfl⟩)
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_frame.hr (Hr := Hr) hP hO s a ptr size rights mapped asid vaddr fin hY.1 hk) tT
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_root.z hP s a p m ad fin (VsTy.ptPool (Pt := Pp) (fun _ h => h) hY.1 hk ad)) tP
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_hvs.z hP s a p m ad fin (VsTy.ptPool (Pt := Pp) (fun _ h => h) hY.1 hk ad)) tP
  · rw [fin_cap_eq_obj (by simp)]
    refine WP.spec_mono (fin_pool.hr hP hR hO hRal s a p b fin hk) fun r ⟨e, w, v, k⟩ => ?_
    exact ⟨e, w, hY.1.keepZ hPp hTb v, hY.2.keep hPp hTe hS v k⟩
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_dframe.hr (Hr := Hr) hP hO s a ptr size rights mapped asid vaddr fin hY.1 hk) tT
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_pt.s2 hP hPl hO hS s a p m ad v fin hY.1 hY.2 hk) tU
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_pd.s2 hP hPl hO hS s a p m ad v fin hY.1 hY.2 hk) tU
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_pdpt.s2 hP hPl hO hS s a p m ad v fin hY.1 hY.2 hk) tU
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_ept.s2 hP s a p l m ad v fin (VsTy.ptPool (Pt := Pp) (fun _ h => h) hY.1 hk ad)) tP
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_eframe.s2 hP hPl hS s a ptr size rights dev mapped asid vaddr fin hY.1 hY.2 hk) tG

/-- **`TyK` of `VsTy ∧ S2Ty`**: a step keeping every `VsR` word keeps both. -/
theorem tyk_s2 {n : U64} (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hO : HrOK kb Pp Tb Lv Hr)
    (hS : S2OK Te bits Hr) :
    TyK st kb Pt (fun s => VsTy st kb Pp Tb Lv s ∧ S2Ty st n Pp Hr Te Re bits s) :=
  fun _ _ h k => ⟨h.1.keepZ hPp hTb k.vsz, h.2.keep hPp hTe hS k.vsz fun R hRm => k _ (hr_vsr hTb hO hRm)⟩

/-- **A `FinKT` class gives `FinJV` of a slot holding one of its caps** (at a `Ty` state). -/
theorem finJV_kt (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    {K : capability.Cap → Prop} {Ty : S → Prop} (hK : FinKT st ar kb Pt Ty K) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hY : Ty s) (hk : L.ksb s = kb) {x : U64}
    {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c) (hKc : K c) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c' fin hc'
  rw [hc] at hc'
  obtain rfl := okinj hc'
  exact WP.spec_mono (hK s a c fin hY hk hKc) fun r hr => ⟨hr.1, (JV.vsr hO hV hR h hr.2.1).1⟩

/-! ## The tops -/

/-- **The exposed `cdt.delete` of an `S2Q` slot of `OS` keeps `JV`** (a direct target: `Ept` caps, Stage-2 frames
and tables, and every other VSpace kind; `VsTy ∧ S2Ty` at the start state). -/
theorem cdt.delete.s2P (hP : P0.ArchTotal ar) (hPl : ArchPlat ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S} {a : A}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s) Pt) (hH : HrOK (L.ksb s) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64} {c : capability.Cap} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok c) (hKc : S2Q c)
    (hY : VsTy st (L.ksb s) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.finJV hO hV h hx (finJV_kt hO hV hR (finKT_s2 hP hPl hR hPp hTb hTe hH hS) h ⟨hY, h2⟩ rfl hc hKc)

/-- **The exposed `cdt.delete` of a slot of `OS` whose cap is `ZQ S2Q` over a domain of `ZQ S2Q` caps keeps `JV`**
(Stage-2 VSpaces, their tables and frames alongside Stage-1 and `HighVSpace` ones; `VsTy ∧ S2Ty` at the start
state). -/
theorem cdt.delete.zqE (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zqG (Ty := fun s => VsTy st (L.ksb s0) Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) hP hO hA hV
    hDO hDC hR (finKT_s2 hP hPl hR hPp hTb hTe hH hS) (tyk_s2 hPp hTb hTe hH hS) hW hIO hap h hx hxI hD hX hN
    ⟨hY, h2⟩

/-- **The thread kind over a domain of `ZQ S2Q` caps** (e.g. a VCPU thread whose Stage-2 VSpace, Stage-2 tables
and frames sit at frame positions of its domain). -/
theorem cdt.delete.threadQE (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.threadQG (Ty := fun s => VsTy st (L.ksb s0) Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s) hP hO hA
    hV hDO hDC hR (finKT_s2 hP hPl hR hPp hTb hTe hH hS) (tyk_s2 hPp hTb hTe hH hS) hW hIO hap h hx hxI hD hN
    ⟨hY, h2⟩ hc hid hpF hcov

end s2k

/-! ## Decode level -/

section deqe
variable {OS Vc Ub : Set U64} {Dm Fp : Set U64} {kb : U64}

theorem vsr_union {P Q : Set U64} {b : U64} (h : VsR kb (P ∪ Q) b) : VsR kb P b ∨ VsR kb Q b := by
  rcases h with h | h
  · exact (ptw_union h).imp Or.inl Or.inl
  · exact Or.inl (Or.inr h)

/-- **`VrOK` of a union of word sets.** -/
theorem VrOK.union {P Q : Set U64} (h1 : VrOK Ω Sg Scs Z OS Vc Ub kb P) (h2 : VrOK Ω Sg Scs Z OS Vc Ub kb Q) :
    VrOK Ω Sg Scs Z OS Vc Ub kb (P ∪ Q) :=
  ⟨fun b hb => (vsr_union hb).elim (h1.al b) (h2.al b), fun b hb => (vsr_union hb).elim (h1.om b) (h2.om b),
    fun b hb => (vsr_union hb).elim (h1.sg b) (h2.sg b), fun b hb => (vsr_union hb).elim (h1.sc b) (h2.sc b),
    fun b hb => (vsr_union hb).elim (h1.os b) (h2.os b), fun b hb => (vsr_union hb).elim (h1.vc b) (h2.vc b),
    fun b hb => (vsr_union hb).elim (h1.ub b) (h2.ub b), fun b hb => (vsr_union hb).elim (h1.ks b) (h2.ks b)⟩

/-- **The `ZQ S2Q` loop at decode level** (from the decode start; QueueHiTy's `del_zqG`). -/
theorem syscall.decode_invocation.del_zqE {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hPl : ArchPlat ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : Dm ⊆ OS)
    (hDC : DCan Dm) {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s) Pt)
    (hH : HrOK (L.ksb s) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s)) (hIO : IrqOK OS Dm (L.ksb s))
    (hap : IrqStApart OS (L.ksb s)) (hN : IrqN st (L.ksb s) s)
    (hY : VsTy st (L.ksb s) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (hD : DomQ st S2Q Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => XQ st S2Q Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧
      ¬ IslN (L.ksb s) x) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ :=
  syscall.decode_invocation.del_zqG (Ty := fun s' => VsTy st (L.ksb s) Pp Tb Lv s' ∧
    S2Ty st hPl.ipa Pp Hr Te Re bits s') hP hO hA hV hDO hDC a len slot cap blk call don fp buf extra D hT hv hR
    (finKT_s2 hP hPl hR hPp hTb hTe hH hS) (tyk_s2 hPp hTb hTe hH hS) hW hIO hap hN ⟨hY, h2⟩ hD hf hslot hcap hk

/-- **The `ZQ S2Q` decode on [J] `SlotTyEntP`** (no new premise beyond the [P] of `ArchPlat`): the entry fact's
`Pp`, `Tb`, `Lv`, `Pt` are exposed; the Stage-2 objects' placement (`VrOK` of their granules, `S2OK`), `HrOK` are
state-free case hypotheses, `S2Ty` a case hypothesis of the decode start. -/
theorem syscall.decode_invocation.del_zqE_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hPl : ArchPlat ar) (hJ : SlotTyEntP st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s)
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub Pp Tb Pt : Set U64, ∃ Lv : U64 → Nat, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧
      VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧ Pp ⊆ Pt ∧ Tb ⊆ Pt ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64) (Dm Fp Hr Te : Set U64)
        (Re bits : U64 → Nat),
        VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s) (Gran Te bits) → HrOK (L.ksb s) Pp Tb Lv Hr → S2OK Te bits Hr →
        S2Ty st hPl.ipa Pp Hr Te Re bits s → Dm ⊆ OS → DCan Dm → IrqOK OS Dm (L.ksb s) →
        IrqN st (L.ksb s) s →
        DomQ st S2Q Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s →
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => XQ st S2Q Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧
          ¬ IslN (L.ksb s) x) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
            VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, Pp, Tb, Pt, Lv, hO, hT, -, hap, hA, hV, hv, hW, hPp, hTb, hR, hY⟩ := hJ.entAt hE q.tcbs
  refine ⟨OS, Vc, Ub, Pp, Tb, Pt, Lv, hO, hT, hv, hPp, hTb,
    fun a len slot blk call don fp buf Dm Fp Hr Te Re bits hRe hH hS h2 hDO hDC hIO hN hD hf hs hc hk => ?_⟩
  exact syscall.decode_invocation.del_zqE (Pt := Pt ∪ Gran Te bits) hP hPl hO hA hV hDO hDC
    (fun _ h => Or.inl (hPp h)) (fun _ h => Or.inl (hTb h)) (fun _ h => Or.inr h) a len slot cap blk call don fp
    buf extra D hT hv (hR.union hRe) hH hS hW hIO hap hN hY h2 hD hf hs hc hk

end deqe

end ST
end R
end W7

end

end Fl4ProofsA64.P1

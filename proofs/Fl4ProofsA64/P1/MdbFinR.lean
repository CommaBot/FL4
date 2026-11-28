/-
P1 (aarch64, gen 50): **the MDB facts through gen 41 / 45's deletion tops** — new tops beside the existing ones
(their statements unchanged): the exposed `cdt.delete` of a `ZQ S2Q` slot and its thread kind keep `JV`, the
VSpace typings and `MdbS` (`MdbLk ∧ RngOneA64 ∧ KindA ∧ NullLk ∧ ClsA` over some ghost), via MdbFin's
`cdt.delete.zqIGTmdbF` (no MDB obligation left as a hypothesis).

* **`cdt.delete.zqETM`** / **`cdt.delete.threadQETM`**: gen 41's `zqET` / `threadQET` (QueueS2Inv) with `MdbS` from
  start to end;
* **`cdt.delete.zqETRM`** / **`cdt.delete.threadQETRM`**: gen 45's `zqETR` / `threadQETR` (QueueReach, the typings
  narrowed to reachable tables) with `MdbS` from start to end.

* (gen 61) **`cdt.delete.zqETG`** / **`threadQETG`** / **`zqETRG`** / **`threadQETRG`**: the four tops for any
  `LoopMZ` field `M` at the VSpace typing's `Ty` (the proofs that were here, the field abstracted); the four `…M`
  tops above, MdbTreeZ's `…MR` and MdbUZD's `…VZ` tops are their instances.

Named premises: none; hypotheses those of the existing tops plus `MdbS` at the start state.
-/
import Fl4ProofsA64.P1.MdbFin
import Fl4ProofsA64.P1.QueueReach
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

namespace W7
namespace R
namespace ST

section del
variable {OS Vc Ub D Fp : Set U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- (gen 61) **`cdt.delete.zqET` with any `LoopMZ` field `M`** (module docstring). -/
theorem cdt.delete.zqETG (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    {M : S → Prop} {Zr : S → U64 → U64 → U64 → Prop}
    (hM : LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0)
      (XQF st S2Q Vc D Scs Fp (fun s => VsTy st (L.ksb s0) Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s)
        (L.ksb s0)) Zr M) (hm : M s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ∧ M r.2.1 ⦄ :=
  WP.spec_mono (cdt.delete.zqIGTMZ (Ty := fun s => VsTy st (L.ksb s0) Pp Tb Lv s ∧
      S2Ty st hPl.ipa Pp Hr Te Re bits s) hP hO hA hV hDO hDC hR (finKT_s2 hP hPl hR hPp hTb hTe hH hS)
    (tyk_s2 hPp hTb hTe hH hS) hW hIO hap h hx hxI hD hX rfl rfl hN ⟨hY, h2⟩ hM hm)
    fun _ ⟨j, ⟨y, z⟩, m⟩ => ⟨j, y, z, m⟩

set_option maxHeartbeats 1000000 in
/-- (gen 61) **`cdt.delete.threadQET` with any `LoopMZ` field `M`** (module docstring). -/
theorem cdt.delete.threadQETG (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D)
    {M : S → Prop} {Zr : S → U64 → U64 → U64 → Prop}
    (hM : LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0)
      (XQF st S2Q Vc D Scs Fp (fun s => VsTy st (L.ksb s0) Pp Tb Lv s ∧ S2Ty st hPl.ipa Pp Hr Te Re bits s)
        (L.ksb s0)) Zr M) (hm : M s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ∧ M r.2.1 ⦄ :=
  cdt.delete.zqETG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD (fun c hc' => by
    rw [hc] at hc'; rw [← okinj hc']
    refine Or.inl ⟨Or.inl (Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩)), ?_⟩
    rintro p' (⟨r, g, b, e⟩ | e | ⟨t', n', e⟩)
    · cases e
    · cases e; exact hpF
    · cases e) hN hY h2 hM hm

/-- (gen 61) **`cdt.delete.zqETR` with any `LoopMZ` field `M`** (module docstring). -/
theorem cdt.delete.zqETRG (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTyR st (L.ksb s0) Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    {M : S → Prop} {Zr : S → U64 → U64 → U64 → Prop}
    (hM : LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0)
      (XQF st S2Q Vc D Scs Fp (fun s1 => VsTy st (L.ksb s0) Pp (VsRt st Pp Hr Tb Lv s) Lv s1 ∧
        S2Ty st hPl.ipa Pp Hr (S2Rt st Pp Te Re bits s) Re bits s1) (L.ksb s0)) Zr M) (hm : M s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧ M r.2.1 ⦄ :=
  WP.spec_mono (cdt.delete.zqETG hP hPl hO hA hV hDO hDC hPp (VsRt_sub.trans hTb) ((gran_mono S2Rt_sub).trans hTe)
    hR (hH.mono VsRt_sub (hr_rt hH.sub)) (S2OK.sub hS S2Rt_sub) hW hIO hap h hx hxI hD hX hN hY.sub h2.sub hM hm)
    fun _ ⟨j, y, z, m⟩ => ⟨j, y.toRsub VsRt_sub (hr_rt hH.sub), z.toRsub S2Rt_sub, m⟩

/-- (gen 61) **`cdt.delete.threadQETR` with any `LoopMZ` field `M`** (module docstring). -/
theorem cdt.delete.threadQETRG (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTyR st (L.ksb s0) Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D)
    {M : S → Prop} {Zr : S → U64 → U64 → U64 → Prop}
    (hM : LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0)
      (XQF st S2Q Vc D Scs Fp (fun s1 => VsTy st (L.ksb s0) Pp (VsRt st Pp Hr Tb Lv s) Lv s1 ∧
        S2Ty st hPl.ipa Pp Hr (S2Rt st Pp Te Re bits s) Re bits s1) (L.ksb s0)) Zr M) (hm : M s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧ M r.2.1 ⦄ :=
  WP.spec_mono (cdt.delete.threadQETG hP hPl hO hA hV hDO hDC hPp (VsRt_sub.trans hTb)
    ((gran_mono S2Rt_sub).trans hTe) hR (hH.mono VsRt_sub (hr_rt hH.sub)) (S2OK.sub hS S2Rt_sub) hW hIO hap h hx hxI hD
    hN hY.sub h2.sub hc hid hpF hcov hM hm)
    fun _ ⟨j, y, z, m⟩ => ⟨j, y.toRsub VsRt_sub (hr_rt hH.sub), z.toRsub S2Rt_sub, m⟩

set_option maxHeartbeats 1000000 in
/-- **`cdt.delete.zqET` with `MdbS`** (module docstring). -/
theorem cdt.delete.zqETM (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s) (hm : MdbS st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ∧ MdbS st OS r.2.1 ⦄ :=
  cdt.delete.zqETG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hX hN hY h2
    (LoopMZ.mdb hP hO hA hV hDO hDC hR (finKT_s2 hP hPl hR hPp hTb hTe hH hS) hW hIO hap) hm

set_option maxHeartbeats 1000000 in
/-- **`cdt.delete.threadQET` with `MdbS`** (module docstring). -/
theorem cdt.delete.threadQETM (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) (hm : MdbS st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ∧ MdbS st OS r.2.1 ⦄ :=
  cdt.delete.threadQETG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hN hY h2 hc hid hpF hcov
    (LoopMZ.mdb hP hO hA hV hDO hDC hR (finKT_s2 hP hPl hR hPp hTb hTe hH hS) hW hIO hap) hm

/-- **`cdt.delete.zqETR` with `MdbS`** (module docstring). -/
theorem cdt.delete.zqETRM (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTyR st (L.ksb s0) Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s) (hm : MdbS st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧ MdbS st OS r.2.1 ⦄ :=
  cdt.delete.zqETRG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hX hN hY h2
    (LoopMZ.mdb hP hO hA hV hDO hDC hR (finKT_s2 hP hPl hR hPp (VsRt_sub.trans hTb) ((gran_mono S2Rt_sub).trans hTe)
      (hH.mono VsRt_sub (hr_rt hH.sub)) (S2OK.sub hS S2Rt_sub)) hW hIO hap) hm

/-- **`cdt.delete.threadQETR` with `MdbS`** (module docstring). -/
theorem cdt.delete.threadQETRM (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTyR st (L.ksb s0) Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) (hm : MdbS st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧ MdbS st OS r.2.1 ⦄ :=
  cdt.delete.threadQETRG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hN hY h2 hc hid hpF hcov
    (LoopMZ.mdb hP hO hA hV hDO hDC hR (finKT_s2 hP hPl hR hPp (VsRt_sub.trans hTb) ((gran_mono S2Rt_sub).trans hTe)
      (hH.mono VsRt_sub (hr_rt hH.sub)) (S2OK.sub hS S2Rt_sub)) hW hIO hap) hm

end del

end ST
end R
end W7

end

end Fl4ProofsA64.P1

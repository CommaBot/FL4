/-
P1 (aarch64, gen 61): **`ValidUntypedA ∧ UtZeroA` through `empty_slot` and the deletion tops**, and **the kernel
state block off the RAM untypeds** (`KsOffA`, the fact the node-word case hypotheses come from).

* **`KsOffA st Cs OS s`**: every RAM `Untyped p b _ false` cap of `OS` has its region `[p, p + 2^b)` off the kernel
  state block and every core's node (`RegionOffNodes`, P3's "kernel memory is never untyped memory"; l4v
  Invariants_AI `valid_global_refs` / `kernel_window`: no cap's range covers the kernel's global data; FL4: the
  boot hands out RAM untypeds only outside the kernel image, whose statics hold `KS` and the nodes —
  fl4-kernel-aarch64/src/lib.rs, boot.rs; device untypeds may cover the image since FL4#34, hence RAM only, as
  `ValidUntypedA`). Boot `KsOffA.empty`; transfer **`KsOffA.of_ub`** (any step whose cap map is `UBm` and which keeps
  `ksb`: a RAM untyped after comes from a RAM untyped of the same region). Uses: **`KsOffA.ks`** (a word of the state
  block, offset `< 223488`) and **`KsOffA.node`** (a node word) are `NodeOffA` (off every RAM free part).
* **`cdt.empty_slot.uz`**: `empty_slot` keeps `UtZeroA` — its writes are cap-slot words (`cdt.empty_slot.gw`, off the
  free parts by `capw_off`) and `post_cap_deletion`'s, given off the free parts (`hPf`; the IRQ state words are
  `KsOffA.ks` words), its cap map `cdt.empty_slot.ubm` (MdbVUZ).
* **The deletion tops.** `finalise_cap` has no write frame of its own here; the deletion's step relation `JV` carries
  the cumulative frame from the decode start `s0` (`Cur0R.fr`: only `Cur0W s0` words change). So: the loop carries
  the cap map from the deletion's start (`LoopMZ.mdbSTQ` at `Q := UBm st OS s`, MdbVUZ), and at the end
  `ValidUntypedA` follows by `of_ub` and `UtZeroA` by `UtZeroA.ofJV` (`UtZeroA.writes` over the frame between the two
  `JV` states, `WritesIn.base`) given **`hFw`: every `Cur0W s0` word is `NodeOffA` at the start**. Tops
  **`cdt.delete.zqIGTmdbSTVZ`**, **`cdt.delete_deferred.zqGmdbSTVZ`**, and the MdbFinR tops
  **`cdt.delete.zqETMVZ`** / **`threadQETMVZ`** / **`zqETRMVZ`** / **`threadQETRMVZ`** (instances of MdbFinR's
  field-generic `zqETG` …): `(MdbST ∧ UtRev) ∧ ValidUntypedA Hv ∧ UtZeroA` before ⇒ after.
* `hFw`'s parts: the TCB / endpoint / frame / SC / `Ω` words are heap words (off by `ValidUntypedA`), the node and
  state-block words `KsOffA` words; the user-memory words `UserW` (`vcpu.cancel_run`'s `RUN_CALLER` word in the run
  buffer's frame) need a fact placing user frames off the free parts (l4v `valid_untyped` over frame caps) — owed.

No named premise. New case hypotheses: `hFw` (above), `hPf` (`empty_slot.uz`).
-/
import Fl4ProofsA64.P1.MdbUZS
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

variable {OS : Set U64}

/-! ## The kernel state block off the RAM untypeds -/

/-- **Every RAM untyped region misses the kernel state block and the nodes** (module docstring). -/
def KsOffA (st : machine.Store S) [L : LawfulStore st] (Cs OS : Set U64) (s : S) : Prop :=
  ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false → RegionOffNodes st Cs s p.val (p.val + 2 ^ b.val)

/-- **Boot**: null `OS` slots. -/
theorem KsOffA.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null) : KsOffA st Cs OS s :=
  fun u hu p b i hc => by rw [h u hu] at hc; cases hc

/-- **Transfer** along a cap map keeping the state block. -/
theorem KsOffA.of_ub {s s' : S} (h : KsOffA st Cs OS s) (hk : L.ksb s' = L.ksb s) (hc : UBm st OS s s') :
    KsOffA st Cs OS s' := by
  intro u hu p b i hcu
  obtain ⟨y0, hy0, hb⟩ := hc u hu
  obtain ⟨i0, hc0, -⟩ := hb p b i hcu
  have g := h y0 hy0 p b i0 hc0
  unfold RegionOffNodes LawfulStore.nodeBase at g ⊢
  rw [hk]; exact g

/-- **A word of the kernel state block lies off every RAM free part.** -/
theorem KsOffA.ks {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (h : KsOffA st Cs OS s) (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) {o : U64} (ho : o.val < 223488) :
    NodeOffA st OS s (wa (L.ksb s) o) := by
  intro u hu p b i hc
  have g := (h u hu p b i hc).2
  rw [ks_val q ho]
  rcases g with g | g
  · left; omega
  · right; omega

/-- **A node word lies off every RAM free part.** -/
theorem KsOffA.node {s : S} (h : KsOffA st Cs OS s) {c off : U64} (hc : c ∈ Cs) (hN : NodePlaced st T s c)
    (ho : off.val < 4288) : NodeOffA st OS s (L.nodeAt s c off) := by
  intro u hu p b i hcu
  have g := (h u hu p b i hcu).1 c hc
  rw [nodeAt_val hN ho]
  rcases g with g | g
  · left; omega
  · right; omega

/-! ## `empty_slot` -/

section emp
variable {A : Type _} {ar : machine.Arch A}

/-- **`empty_slot` keeps `UtZeroA`** (module docstring). -/
theorem cdt.empty_slot.uz (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S}
    (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s) (hS : MdbS st OS s) (h : UtZeroA st OS s)
    (hV : ValidUntypedA st H OS s) {a : A} {x : U64} (hx : x ∈ OS) {cl : capability.Cap} {Pw : U64 → Prop}
    (hpw : ∀ b, Pw b → ¬ InOS OS b)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 Pw ⦄)
    (hPf : ∀ b, Pw b → NodeOffA st OS s b) :
    cdt.empty_slot st ar s a x cl ⦃ r => UtZeroA st OS r.1 ⦄ :=
  WP.spec_mono (WP.spec_and (cdt.empty_slot.gw hO hT hx hpcd fun y hy b h1 h2 hb => hpw b hb ⟨y, hy, h1, h2⟩)
    (cdt.empty_slot.ubm hO hS hx hpw hpcd)) fun _ ⟨⟨w, _, _⟩, u⟩ =>
    h.writes w (fun y0 hy0 p b i hc w' hw' =>
      hw'.elim (fun e => capw_off hH hV hy0 hc e) (fun e => hPf w' e y0 hy0 p b i hc)) u

end emp

/-! ## The deletion tops -/

/-- Two frames from one base state give the frame between the two states. -/
theorem WritesIn.base {s0 s s' : S} {F : U64 → Prop} (h1 : WritesIn st s0 s F) (h2 : WritesIn st s0 s' F) :
    WritesIn st s s' F :=
  ⟨h2.1.trans h1.1.symm, h2.2.1.trans h1.2.1.symm, fun b ha hb => (h2.2.2 b ha hb).trans (h1.2.2 b ha hb).symm⟩

/-- **`UtZeroA` from one `JV` state to a later one**: the cumulative frame and the cap map (module docstring). -/
theorem UtZeroA.ofJV {Vc Ub : Set U64} {s0 s s' : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    (h' : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s') (hz : UtZeroA st OS s)
    (hFw : ∀ b, Cur0W st T Cs Ω H Sg Scs Z s0 b → NodeOffA st OS s b) (u : UBm st OS s s') : UtZeroA st OS s' :=
  hz.writes (WritesIn.base (Cur0R.fr h.1.1) (Cur0R.fr h'.1.1))
    (fun y0 hy0 p b i hc w hw => hFw w hw y0 hy0 p b i hc) u

section zq
variable {Vc Ub D Fp : Set U64} {Pt : Set U64} {K : capability.Cap → Prop} {Ty : S → Prop}
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **`(MdbST ∧ UtRev) ∧ ValidUntypedA ∧ UtZeroA` through gen 41's exposed deletion** (module docstring). -/
theorem cdt.delete.zqIGTmdbSTVZ {Hv : Heap} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    (hm : MdbST st OS s ∧ UtRev st OS s) (hv : ValidUntypedA st Hv OS s) (hz : UtZeroA st OS s)
    (hFw : ∀ b, Cur0W st T Cs Ω H Sg Scs Z s0 b → NodeOffA st OS s b) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧
      ((MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ∧ ValidUntypedA st Hv OS r.2.1 ∧ UtZeroA st OS r.2.1) ⦄ :=
  WP.spec_mono (cdt.delete.zqIGTMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY
    (LoopMZ.mdbSTQ (Q := UBm st OS s) hP hO hA hV hDO hDC hR hK hTy hW hIO hap fun _ _ h1 h2 => h1.trans h2)
    ⟨hm, UBm.refl s⟩)
    fun _ ⟨j, y, m, u⟩ => ⟨j, y, m, hv.of_ub (fun _ _ e => e) u, UtZeroA.ofJV h j hz hFw u⟩

set_option maxHeartbeats 1000000 in
/-- **`(MdbST ∧ UtRev) ∧ ValidUntypedA ∧ UtZeroA` through gen 39's deferred deletion** (module docstring). -/
theorem cdt.delete_deferred.zqGmdbSTVZ {Hv : Heap} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    (hm : MdbST st OS s ∧ UtRev st OS s) (hv : ValidUntypedA st Hv OS s) (hz : UtZeroA st OS s)
    (hFw : ∀ b, Cur0W st T Cs Ω H Sg Scs Z s0 b → NodeOffA st OS s b) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧
      ((MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ∧ ValidUntypedA st Hv OS r.2.1 ∧ UtZeroA st OS r.2.1) ⦄ :=
  WP.spec_mono (cdt.delete_deferred.zqGMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY
    (LoopMZ.mdbSTQ (Q := UBm st OS s) hP hO hA hV hDO hDC hR hK hTy hW hIO hap fun _ _ h1 h2 => h1.trans h2)
    ⟨hm, UBm.refl s⟩)
    fun _ ⟨j, d, o, i, is, y, m, u⟩ => ⟨j, d, o, i, is, y, m, hv.of_ub (fun _ _ e => e) u, UtZeroA.ofJV h j hz hFw u⟩

end zq

section del
variable {Vc Ub D Fp : Set U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **MdbFinR's `zqETM` with `(MdbST ∧ UtRev) ∧ ValidUntypedA ∧ UtZeroA`** (module docstring). -/
theorem cdt.delete.zqETMVZ {Hv : Heap} (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (hm : MdbST st OS s ∧ UtRev st OS s) (hv : ValidUntypedA st Hv OS s) (hz : UtZeroA st OS s)
    (hFw : ∀ b, Cur0W st T Cs Ω H Sg Scs Z s0 b → NodeOffA st OS s b) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
      ((MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ∧ ValidUntypedA st Hv OS r.2.1 ∧ UtZeroA st OS r.2.1) ⦄ :=
  WP.spec_mono (cdt.delete.zqETG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hX hN hY h2
    (LoopMZ.mdbSTQ (Q := UBm st OS s) hP hO hA hV hDO hDC hR (finKT_s2 hP hPl hR hPp hTb hTe hH hS)
      (tyk_s2 hPp hTb hTe hH hS) hW hIO hap fun _ _ h1 h2 => h1.trans h2) ⟨hm, UBm.refl s⟩)
    fun _ ⟨j, y, z, m, u⟩ => ⟨j, y, z, m, hv.of_ub (fun _ _ e => e) u, UtZeroA.ofJV h j hz hFw u⟩

set_option maxHeartbeats 1000000 in
/-- **MdbFinR's `threadQETM` with `(MdbST ∧ UtRev) ∧ ValidUntypedA ∧ UtZeroA`.** -/
theorem cdt.delete.threadQETMVZ {Hv : Heap} (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
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
    (hm : MdbST st OS s ∧ UtRev st OS s) (hv : ValidUntypedA st Hv OS s) (hz : UtZeroA st OS s)
    (hFw : ∀ b, Cur0W st T Cs Ω H Sg Scs Z s0 b → NodeOffA st OS s b) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTy st (L.ksb s0) Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
      ((MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ∧ ValidUntypedA st Hv OS r.2.1 ∧ UtZeroA st OS r.2.1) ⦄ :=
  WP.spec_mono (cdt.delete.threadQETG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hN hY h2
    hc hid hpF hcov
    (LoopMZ.mdbSTQ (Q := UBm st OS s) hP hO hA hV hDO hDC hR (finKT_s2 hP hPl hR hPp hTb hTe hH hS)
      (tyk_s2 hPp hTb hTe hH hS) hW hIO hap fun _ _ h1 h2 => h1.trans h2) ⟨hm, UBm.refl s⟩)
    fun _ ⟨j, y, z, m, u⟩ => ⟨j, y, z, m, hv.of_ub (fun _ _ e => e) u, UtZeroA.ofJV h j hz hFw u⟩

set_option maxHeartbeats 1000000 in
/-- **MdbFinR's `zqETRM` with `(MdbST ∧ UtRev) ∧ ValidUntypedA ∧ UtZeroA`.** -/
theorem cdt.delete.zqETRMVZ {Hv : Heap} (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTyR st (L.ksb s0) Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hm : MdbST st OS s ∧ UtRev st OS s) (hv : ValidUntypedA st Hv OS s) (hz : UtZeroA st OS s)
    (hFw : ∀ b, Cur0W st T Cs Ω H Sg Scs Z s0 b → NodeOffA st OS s b) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
      ((MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ∧ ValidUntypedA st Hv OS r.2.1 ∧ UtZeroA st OS r.2.1) ⦄ :=
  WP.spec_mono (cdt.delete.zqETRG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hX hN hY h2
    (LoopMZ.mdbSTQ (Q := UBm st OS s) hP hO hA hV hDO hDC hR
      (finKT_s2 hP hPl hR hPp (VsRt_sub.trans hTb) ((gran_mono S2Rt_sub).trans hTe) (hH.mono VsRt_sub (hr_rt hH.sub))
        (S2OK.sub hS S2Rt_sub))
      (tyk_s2 hPp (VsRt_sub.trans hTb) ((gran_mono S2Rt_sub).trans hTe) (hH.mono VsRt_sub (hr_rt hH.sub))
        (S2OK.sub hS S2Rt_sub)) hW hIO hap fun _ _ h1 h2 => h1.trans h2) ⟨hm, UBm.refl s⟩)
    fun _ ⟨j, y, z, m, u⟩ => ⟨j, y, z, m, hv.of_ub (fun _ _ e => e) u, UtZeroA.ofJV h j hz hFw u⟩

set_option maxHeartbeats 1000000 in
/-- **MdbFinR's `threadQETRM` with `(MdbST ∧ UtRev) ∧ ValidUntypedA ∧ UtZeroA`.** -/
theorem cdt.delete.threadQETRMVZ {Hv : Heap} (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
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
    (hm : MdbST st OS s ∧ UtRev st OS s) (hv : ValidUntypedA st Hv OS s) (hz : UtZeroA st OS s)
    (hFw : ∀ b, Cur0W st T Cs Ω H Sg Scs Z s0 b → NodeOffA st OS s b) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
      ((MdbST st OS r.2.1 ∧ UtRev st OS r.2.1) ∧ ValidUntypedA st Hv OS r.2.1 ∧ UtZeroA st OS r.2.1) ⦄ :=
  WP.spec_mono (cdt.delete.threadQETRG hP hPl hO hA hV hDO hDC hPp hTb hTe hR hH hS hW hIO hap h hx hxI hD hN hY h2
    hc hid hpF hcov
    (LoopMZ.mdbSTQ (Q := UBm st OS s) hP hO hA hV hDO hDC hR
      (finKT_s2 hP hPl hR hPp (VsRt_sub.trans hTb) ((gran_mono S2Rt_sub).trans hTe) (hH.mono VsRt_sub (hr_rt hH.sub))
        (S2OK.sub hS S2Rt_sub))
      (tyk_s2 hPp (VsRt_sub.trans hTb) ((gran_mono S2Rt_sub).trans hTe) (hH.mono VsRt_sub (hr_rt hH.sub))
        (S2OK.sub hS S2Rt_sub)) hW hIO hap fun _ _ h1 h2 => h1.trans h2) ⟨hm, UBm.refl s⟩)
    fun _ ⟨j, y, z, m, u⟩ => ⟨j, y, z, m, hv.of_ub (fun _ _ e => e) u, UtZeroA.ofJV h j hz hFw u⟩

end del

end ST
end R
end W7

end

end Fl4ProofsA64.P1

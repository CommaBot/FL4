/-
P1 (aarch64, gen 38): **ASID pools, device frames and page-table caps inside covered slots** — the instances of the
generic Zombie loop over a VSpace-finaliser class (QueueZombieQ).

* **`VsQ`** = gen 37's `VsCap` (non-device, non-EPT frames; `Pml4` / `HighVSpace` roots) ∨ `AsidPool` ∨ non-EPT
  **device** frames (mapped or not); typing `VsTy` (QueueVsTy). **`finK_vs`**: its `FinK` — frames by `fin_frame.z`
  / `fin_dframe.z` with `VsTy.ptWalk`, roots by `fin_root.z` / `fin_hvs.z` with `VsTy.ptPool`, pools by
  **`fin_pool.z`** (`delete_asid_pool` with a generic post, `vspace.delete_asid_pool.q`: the one write is the
  ASID-table word written `0`) — and `tyz_vs` (`VsTy.keepZ`).
* **`PtQ`** = `VsQ` ∨ `PageTable` / `PageDirectory` / `Pdpt` (mapped or not); typing `VsTy ∧ VsS1` (QueuePtTy:
  Stage-1 pools only). **`finK_pt`** (page-table caps by QueuePtTy's `fin_pt.z` / `fin_pd.z` / `fin_pdpt.z` at
  `PtTy.of_s1`), `tyz_s1` (`VsTy.keepZ`, `VsS1.keepZ`).
* Tops: **`cdt.delete.zqV`**, **`cdt.delete.threadQV`** (class `VsQ`), **`cdt.delete.zqT`**,
  **`cdt.delete.threadQT`** (class `PtQ`).

Why `VsS1` in the loop with page tables: `PtTy`'s `high` clause (a `HighVSpace` root's entry 511 is a table
descriptor) is a fact of one state but is not kept by an abstract `VsZ` step (a `VsZ` step may zero any `VsR`
word); `VsS1` is. The top-level page-table target (QueuePtTy `cdt.delete.ptP`) needs only `PtTy` at its start state.

Case hypotheses as QueueZombieP's (state-free, or facts of the start state), with `VsS1 st Pp s` at the start
state for the page-table instance. No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueZombieQ
import Fl4ProofsA64.P1.QueuePtTy
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

/-- **`delete_asid_pool` with a generic post** of its one `set_asid_table(_, 0)` (QueueVsFin's
`delete_asid_pool.vs` text). -/
theorem vspace.delete_asid_pool.q {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (base pool : U64) {Q : S → Prop} (h0 : Q s)
    (hset : ∀ hi, vspace.set_asid_table st s hi 0#u64 ⦃ s1 => Q s1 ⦄) :
    vspace.delete_asid_pool st ar s a base pool ⦃ r => Q r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vspace.delete_asid_pool
  step as ⟨i, _⟩
  refine WP.spec_bind (P0.vspace.asid_table.p0 st s i hS) fun p1 _ => ?_
  split
  · exact (WP.spec_ok _).2 h0
  refine WP.spec_bind (P0.vspace.delete_asid_pool_loop.p0 st ar s a base pool 0#u64 hS hA) fun a1 _ => ?_
  step as ⟨i2, _⟩
  refine WP.spec_bind (hset i2) fun s1 w1 => ?_
  step with sched.cur_thread.spec as ⟨ct, _⟩
  exact WP.spec_mono (vspace.set_vm_root.same hA s1 a1 ct) fun r e => by rw [e]; exact w1

namespace W7
namespace R
namespace ST

section vsk
variable {OS Vc Ub D Fp : Set U64} {kb : U64} {Pp Tb Pt : Set U64} {Lv : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **An ASID-pool cap's finalisation** (any finality): `(Null, Null)`, writes only `VsR` words, a `VsZ` step. -/
theorem fin_pool.z (hA : P0.ArchTotal ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (s : S) (a : A) (ptr base : U64) (fin : Bool) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.AsidPool ptr base) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ WritesIn st s r.2.1 (VsR kb Pt) ∧ VsZ st kb Pt s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  have hset : ∀ hi, vspace.set_asid_table st s hi 0#u64 ⦃ s1 =>
      WritesIn st s s1 (VsR kb Pt) ∧ VsZ st kb Pt s s1 ⦄ := fun hi =>
    WP.spec_mono (vspace.set_asid_table.as s hi 0#u64) fun s1 ⟨o, h1, h2, h8, e⟩ => by
      have hb : VsR kb Pt (wa (L.ksb s) o) := Or.inr ⟨o, h1, h2, h8, by rw [hk]⟩
      rw [e]
      exact ⟨(writesIn_wr (hR.al _ hb)).mono fun b eb => by rw [eb]; exact hb, VsZ.wr0 hR.al (hR.al _ hb)⟩
  split
  · refine WP.spec_bind (vspace.delete_asid_pool.q hA s a base ptr ⟨WritesIn.refl _ _, VsZ.refl _⟩ hset) ?_
    rintro ⟨s1, a1⟩ w1
    exact (WP.spec_ok _).2 ⟨rfl, w1⟩
  · exact (WP.spec_ok _).2 ⟨rfl, WritesIn.refl _ _, VsZ.refl _⟩

/-- **The VSpace class without page tables**: gen 37's `VsCap`, ASID pools, non-EPT device frames. -/
def VsQ (c : capability.Cap) : Prop :=
  VsCap c ∨ (∃ p b, c = .AsidPool p b) ∨
    (∃ ptr size rights mapped asid vaddr, c = .Frame ptr size rights true mapped false asid vaddr)

/-- **The VSpace class with page tables.** -/
def PtQ (c : capability.Cap) : Prop :=
  VsQ c ∨ (∃ p m ad v, c = .PageTable p m ad v) ∨ (∃ p m ad v, c = .PageDirectory p m ad v) ∨
    (∃ p m ad v, c = .Pdpt p m ad v)

/-- A `Wr0` step writes only `VsR` words and is a `VsZ` step. -/
theorem wr0_vs (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s s' : S} (z : Wr0 st Pt s s') :
    WritesIn st s s' (VsR kb Pt) ∧ VsZ st kb Pt s s' :=
  ⟨(Wr0.w (fun b hb => hR.al b (Or.inl hb)) z).mono fun b hb => Or.inl hb, Wr0.vsz hR.al z⟩

/-- **`FinK` of `VsQ` over `VsTy`.** -/
theorem finK_vs (hP : P0.ArchTotal ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) :
    FinK st ar kb Pt (VsTy st kb Pp Tb Lv) VsQ := by
  intro s a c fin hY hk hc
  rcases hc with ((⟨ptr, size, rights, mapped, asid, vaddr, rfl⟩ | ⟨p, m, ad, rfl⟩ | ⟨p, m, ad, rfl⟩) |
    ⟨p, b, rfl⟩ | ⟨ptr, size, rights, mapped, asid, vaddr, rfl⟩)
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_frame.z hP s a ptr size rights mapped asid vaddr fin (hY.ptWalk hTb hk asid vaddr))
      fun r ⟨e, z⟩ => ⟨e, wr0_vs hR z⟩
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_root.z hP s a p m ad fin (hY.ptPool hPp hk ad)) fun r ⟨e, z⟩ => ⟨e, wr0_vs hR z⟩
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_hvs.z hP s a p m ad fin (hY.ptPool hPp hk ad)) fun r ⟨e, z⟩ => ⟨e, wr0_vs hR z⟩
  · rw [fin_cap_eq_obj (by simp)]
    exact fin_pool.z hP hR s a p b fin hk
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_dframe.z hP s a ptr size rights mapped asid vaddr fin (hY.ptWalk hTb hk asid vaddr))
      fun r ⟨e, z⟩ => ⟨e, wr0_vs hR z⟩

theorem tyz_vs (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) : TyZ st kb Pt (VsTy st kb Pp Tb Lv) :=
  fun _ _ h k => h.keepZ hPp hTb k

/-- **`FinK` of `PtQ` over `VsTy ∧ VsS1`.** -/
theorem finK_pt (hP : P0.ArchTotal ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) :
    FinK st ar kb Pt (fun s => VsTy st kb Pp Tb Lv s ∧ VsS1 st Pp s) PtQ := by
  intro s a c fin hY hk hc
  have hT : PtTy st kb Pp Tb Lv s := PtTy.of_s1 hY.1 hY.2
  rcases hc with hv | ⟨p, m, ad, v, rfl⟩ | ⟨p, m, ad, v, rfl⟩ | ⟨p, m, ad, v, rfl⟩
  · exact finK_vs hP hR hPp hTb s a c fin hY.1 hk hv
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_pt.z hP s a p m ad v fin hT hk) fun r ⟨e, z⟩ => ⟨e, wr0_vs hR (Wr0.mono hTb z)⟩
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_pd.z hP s a p m ad v fin hT hk) fun r ⟨e, z⟩ => ⟨e, wr0_vs hR (Wr0.mono hTb z)⟩
  · rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (fin_pdpt.z hP s a p m ad v fin hT hk) fun r ⟨e, z⟩ => ⟨e, wr0_vs hR (Wr0.mono hTb z)⟩

theorem tyz_s1 (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) :
    TyZ st kb Pt (fun s => VsTy st kb Pp Tb Lv s ∧ VsS1 st Pp s) :=
  fun _ _ h k => ⟨h.1.keepZ hPp hTb k, h.2.keepZ hPp k⟩

/-! ## The tops -/

/-- **The exposed `cdt.delete` of a slot of `OS` whose cap is `ZQ VsQ` over a domain of `ZQ VsQ` caps keeps `JV`**
(covered slots may hold, at frame positions, frames — device or not —, VSpace roots and ASID pools). -/
theorem cdt.delete.zqV (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st VsQ Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st VsQ Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zq hP hO hA hV hDO hDC hR (finK_vs hP hR hPp hTb) (tyz_vs hPp hTb) hW hIO hap h hx hxI hD hX hN hY

/-- **The thread kind over a domain of `ZQ VsQ` caps.** -/
theorem cdt.delete.threadQV (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st VsQ Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.threadQ hP hO hA hV hDO hDC hR (finK_vs hP hR hPp hTb) (tyz_vs hPp hTb) hW hIO hap h hx hxI hD hN hY
    hc hid hpF hcov

/-- **The exposed `cdt.delete` of a slot of `OS` whose cap is `ZQ PtQ` over a domain of `ZQ PtQ` caps keeps `JV`**
(covered slots may also hold page-table caps, mapped or not; Stage-1 pools only, `VsS1`, at the start state). -/
theorem cdt.delete.zqT (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st PtQ Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st PtQ Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h1 : VsS1 st Pp s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.zq (Ty := fun s => VsTy st (L.ksb s0) Pp Tb Lv s ∧ VsS1 st Pp s) hP hO hA hV hDO hDC hR
    (finK_pt hP hR hPp hTb) (tyz_s1 hPp hTb) hW hIO hap h hx hxI hD hX hN ⟨hY, h1⟩

/-- **The thread kind over a domain of `ZQ PtQ` caps** (Stage-1 pools only at the start state). -/
theorem cdt.delete.threadQT (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st PtQ Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTy st (L.ksb s0) Pp Tb Lv s) (h1 : VsS1 st Pp s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.threadQ (Ty := fun s => VsTy st (L.ksb s0) Pp Tb Lv s ∧ VsS1 st Pp s) hP hO hA hV hDO hDC hR
    (finK_pt hP hR hPp hTb) (tyz_s1 hPp hTb) hW hIO hap h hx hxI hD hN ⟨hY, h1⟩ hc hid hpF hcov

end vsk

end ST
end R
end W7

end

end Fl4ProofsA64.P1

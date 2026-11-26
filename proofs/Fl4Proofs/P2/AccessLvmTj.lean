/-
# P2 (line lvm, gen 9): **the VM paths' entry facts from P3's bundle and line vlift's heap facts**

The layout parts of `VtmEnt` (`local_vm_timer_irq`), `VexitEnt` (`local_vm_exit`) and `VexitPEnt` (its pending
case) that P1 / P3 / vlift already give, at a P3-related entry (`SlJAt K s`, P2/SlJEnt.lean) and vlift gen 4's
VCPU layout premises (`P2/E2EVHeap.lean`):

* `tabNoVcpu_of`: the ASID-table and pool words are in no VCPU (`tabNoV_of`'s proof, without the `VData`
  weakening), from `HeapOK`, `VcpuHeap` [J], `VcpuTabOff` [J], `PoolObj` [J];
* **`vtmLay_of`**: `VtmEnt.iq` / `.kr` / `.tab` from `SlJAt` (`SlJAtZ.irqStNone`, `irqLayK_of_slJAt`), `VcpuKs` /
  the block's fit / `HeapOK` (`slJAt_vfacts`, from `JKern` and `VcpuHeap` [J]) and `tabNoVcpu_of`;
* **`vtmEnt_of`**: `VtmEnt` from `VexitEnt`, `SlJAt`, the three vlift [J]s and `AsidOff` (P1, [J] as
  `IrqEntK.asid`);
* **`vexitEnt_of`**: `VexitEnt` with `ksv` (`ksv_of`), `vin` (`vin_of`), `vfar` (`vfar_pending`) and `nfar`
  (`vfar_ntfn`) derived, at P1's sets convention (`T = H.tcbs`, `Ω = H.omega`, `K.heap = H`, the SCs and
  notifications typed), from `SlJAt` (`JKern.hksIn`, `LayP.heap`), `VcpuHeap` [J] and `v ≠ 0 → v ∈ K.vcpus` [J];
* **`vexitPEnt_of`**: `VexitPEnt` with `vfit` / `pusr` from vlift's `vfit_ofK` / `pusr_ofK`.

Named premises left (each [J] unless said): `VcpuHeap`, `VcpuTabOff`, `PoolObj` (vlift's layout [J]s), `hvK`
(the bound / exiting VCPU is one of the layout's), `AsidOff`; `VexitEnt`'s `inv` / `lay` / `ntw` / `cs` / `aff` /
`curAff` / `cscCore` and [P] `vlk`; `VexitPEnt`'s `usr`, [P] `buf`, `aff0`. `SlJAt` itself is P3's bundle [J] as in
every `SlJ*` path.
-/
import Fl4Proofs.P2.AccessLvmTl
import Fl4Proofs.P2.E2EVSlD
import Fl4Proofs.P2.E2EVLvmP
import Fl4Proofs.P2.E2EVTimerLay
import Fl4Proofs.P2.FootTimerIrqJ3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMapV (KLayoutV InVcpu)
open Fl4Proofs.P2.E2EV (VcpuHeap VcpuTabOff PoolObj noVcpu_ks noVcpu_of_obj slJAt_vfacts ksv_of vin_of
  vfar_pending vfar_ntfn vfit_ofK pusr_ofK irqOff_val)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV} {s : S}

/-- **The ASID-table and pool words lie in no VCPU** (`tabNoV_of`'s proof). -/
theorem tabNoVcpu_of (hH : HeapOK K.heap) (hV : VcpuHeap K) (hT : VcpuTabOff K) (hP : PoolObj (L := L) K s)
    (hk : K.ksb = L.ksb s) :
    ∀ hi : U64, hi.val < 2048 → (¬ ∃ w, InVcpu K w (atAF (L.ksb s) hi)) ∧
      ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
        ¬ ∃ w, InVcpu K w (peAF (L.mem s (atAF (L.ksb s) hi)) lo) := by
  intro hi hh
  obtain ⟨hf, hoff⟩ := hT
  rw [hk] at hf hoff
  refine ⟨?_, fun lo hl hn => ?_⟩
  · rintro ⟨v, hv, h1, h2⟩
    have e : (atAF (L.ksb s) hi).val = (L.ksb s).val + 288000 + 8 * hi.val := by
      unfold atAF
      simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
      omega
    rw [e] at h1 h2
    rcases hoff v hv with h | h <;> omega
  · obtain ⟨z, hz, hp, hpv⟩ := hP hi hh hn
    generalize L.mem s (atAF (L.ksb s) hi) = p at hp hpv ⊢
    have hfit := hH.fits p _ hp
    have hz' : 4096 ≤ 2 ^ z := by
      calc 4096 = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have ebits : (HKind.other z).bits = z := rfl
    rw [ebits] at hfit
    have e : (peAF p lo).val = p.val + 8 * lo.val := by
      unfold peAF
      simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
      omega
    refine noVcpu_of_obj hH hV hp hpv ?_
    unfold Fl4Proofs.P1.InObj; rw [ebits, e]; omega

/-- **`VtmEnt.iq` / `.kr` / `.tab` at a P3-related entry** (module docstring). -/
theorem vtmLay_of {irq : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hJ : SlJAt (L := L) K.toKLayout s)
    (hV : VcpuHeap K) (hT : VcpuTabOff K) (hPo : PoolObj (L := L) K s) :
    (irq.val < 128 → ∀ i, interrupt.state_off irq = ok i →
      Aligned (core.num.U64.wrapping_add (L.ksb s) i) ∧
        region K.toKLayout (core.num.U64.wrapping_add (L.ksb s) i) = .none ∧
        ¬ ∃ w, InVcpu K w (core.num.U64.wrapping_add (L.ksb s) i)) ∧
    (Aligned (krA (L := L) s) ∧ region K.toKLayout (krA (L := L) s) = .none ∧
      ¬ ∃ w, InVcpu K w (krA (L := L) s)) ∧
    (∀ hi : U64, hi.val < 2048 →
      (Aligned (atAF (L.ksb s) hi) ∧ region K.toKLayout (atAF (L.ksb s) hi) = .none ∧
        ¬ ∃ w, InVcpu K w (atAF (L.ksb s) hi)) ∧
      ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
        Aligned (peAF (L.mem s (atAF (L.ksb s) hi)) lo) ∧
          region K.toKLayout (peAF (L.mem s (atAF (L.ksb s) hi)) lo) = .none ∧
          ¬ ∃ w, InVcpu K w (peAF (L.mem s (atAF (L.ksb s) hi)) lo)) := by
  obtain ⟨hks, hf, hH, -⟩ := slJAt_vfacts hJ hV hT hPo
  have hY := irqLayK_of_slJAt hI hJ
  have hTV := tabNoVcpu_of hH hV hT hPo
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
  have hk : K.ksb = L.ksb s := B.ksb.symm
  refine ⟨fun hb i hi => ?_, ⟨hY.kr.1, hY.kr.2, ?_⟩, fun hi hhi => ⟨⟨(hY.tab hi hhi).1.1, (hY.tab hi hhi).1.2,
    (hTV hk hi hhi).1⟩, fun lo hlo hne => ⟨((hY.tab hi hhi).2 lo hlo hne).1, ((hY.tab hi hhi).2 lo hlo hne).2,
    (hTV hk hi hhi).2 lo hlo hne⟩⟩⟩
  · rw [Fl4Proofs.P3.state_off_eq] at hi
    have hi' := ok_inj_ff hi
    subst hi'
    obtain ⟨h1, h2⟩ := B.irqStNone hb
    have hn := noVcpu_ks hks hf (o := Fl4Proofs.P3.irqOff irq) (by rw [irqOff_val hb]; omega)
    rw [hk] at hn
    exact ⟨h1, h2, hn⟩
  · have hn := noVcpu_ks hks hf (o := layout.ks.KERNEL_ROOT) (by simp [layout.ks.KERNEL_ROOT])
    rw [hk] at hn
    unfold krA
    exact hn

/-- **`VtmEnt` from `VexitEnt`, P3's bundle and vlift's VCPU layout premises** (module docstring). -/
theorem vtmEnt_of {lk : S → U64 → Prop} {irq n : U64}
    (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk (vOf st s) n s) (hJ : SlJAt (L := L) K.toKLayout s)
    (hV : VcpuHeap K) (hT : VcpuTabOff K) (hPo : PoolObj (L := L) K s) (hAs : AsidOff (L := L) Ω Sg s) :
    VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s := by
  obtain ⟨hiq, hkr, htab⟩ := vtmLay_of (irq := irq) hE.inv hJ hV hT hPo
  exact ⟨hE, hiq, hkr, htab, hAs⟩

/-- **`VexitEnt` with its VCPU / notification placement fields derived** (module docstring), at P1's sets
convention. -/
theorem vexitEnt_of {lk : S → U64 → Prop} {v n : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
      region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ TcbSlot K.toKLayout p ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16)
    (aff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (curAff : L.mem s (affA (L.curW s)) = L.cpu s) (cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s)
    (vlk : v ≠ 0#u64 → lk s v)
    (hJ : SlJAt (L := L) K.toKLayout s) (hV : VcpuHeap K) (hKH : K.heap = H) (hTs : T = H.tcbs)
    (hΩ : Ω = H.omega) (hScs : ∀ c ∈ Scs, H c = some (.sc (Z c))) (hNt : ∀ q ∈ Nt, H q = some .ntfn)
    (hvK : v ≠ 0#u64 → v ∈ K.vcpus) :
    VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
  have hk : K.ksb = L.ksb s := B.ksb.symm
  have hH : HeapOK K.heap := B.layP.heap
  have hf := B.j.kern.ksbFit
  rw [← hk] at hf
  have hks := Fl4Proofs.P2.E2EV.vcpuKs_of_jkern B.j.kern rfl hk hV
  have hKI := B.j.kern.hksIn
  subst hKH
  have ksv := ksv_of hks hf
  rw [hk] at ksv
  have hX := hI.2.2.1
  have hcT : L.curW s ∈ T := hI.1.choose_spec.choose_spec.curT
  exact ⟨hI, hL, ntw, cs, aff, curAff, cscCore, ksv, fun h0 => vin_of hH hV (hvK h0), vlk,
    fun h0 => vfar_pending hI hTs hΩ hH hScs hKI (hV v (hvK h0)),
    fun n' hb hn => by
      rw [← hb] at hn ⊢
      have hNn := hX.2.2.bnd _ hcT hn
      exact vfar_ntfn hI hNn (hNt _ hNn)⟩

/-- **`VexitPEnt` with `vfit` / `pusr` from vlift's `vfit_ofK` / `pusr_ofK`** (module docstring). -/
theorem vexitPEnt_of {m : U64 → U64} {v : U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (usr : ∀ x, x ∈ K.user → Aligned x → UsrW st T Cs H Sg Scs Z s x)
    (buf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK {x | x ∈ K.user ∧ Aligned x} b ⦄)
    (aff0 : m (fld (L.curW s) oAFFINITY) = L.mem s (affA (L.curW s)))
    (hJ : SlJAt (L := L) K.toKLayout s) (hV : VcpuHeap K) (hKH : K.heap = H) (hTs : T = H.tcbs)
    (hΩ : Ω = H.omega) (hSg : Sg = H.frame) (hScs : ∀ c ∈ Scs, H c = some (.sc (Z c)))
    (hvK : v ≠ 0#u64 → v ∈ K.vcpus) :
    VexitPEnt K st T Cs H Sg Scs Z m v s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
  have hH : HeapOK K.heap := B.layP.heap
  have hKI := B.j.kern.hksIn
  subst hKH
  exact ⟨usr, pusr_ofK hI hTs hΩ hSg hH hScs hKI rfl hV hvK, buf, vfit_ofK hH rfl hV hvK, aff0⟩

end

end Fl4Proofs.P2

/-
P2 (line vlift): **`NoVcpuRW` of the three `IoRS` paths** (VM fault, VM ReplyRecv, I/O port), so that
`E2EV.PathsV.ofPathsU` / `serializable_e2eV_liftU` take them at `userV K` with no re-walk of their runs.

* `ioRS_noV`, `ioWS_noV`, `safeW_noV`: an `IoRS (userV K)` word is not a VCPU data word (it is no `userV K`
  user word, by definition); an `IoWS` word neither (`own` gives every VCPU word to the gate,
  `OwnMapV.own_vcpu`, which no path holds); a `SafeW` word (each word of `IoDS`, the decline's writes) lies
  in a node / TCB / SC region, so outside every VCPU (`RegionOKV.none`).
* **`vm_noVcpuRW`**, **`rr_noVcpuRW`**, **`io_noVcpuRW`**: `NoVcpuRW` of `vm_localPath`, `rr_localPath`,
  `io_localPath` built at `userV K`, for any of their arguments.
* The paths' own layout premise at `userV K`: `ioLay_userV` / `vmLay_userV` (`IoLay` / `VmLay` of `userV K`
  from `K`'s and `VcpuKs` [J]: no VCPU word lies in the kernel-state block `[ksb, ksb + 13568)`).
  `IoLayA`, `RegionOK` (`E2EV.regionOK_userV`) and `UserOK` (`E2EV.userOK_userV`) carry over.

Premises: `VcpuKs` [J] (for `IoLay.user` at `userV K`; from P1's heap disjointness: a VCPU is a heap
object, the kernel-state block is not heap). What the paths' other `Pre` fields need at `userV K` (`RdTab`'s
ASID words outside every VCPU, `huf` for VCPU data words) is listed in handoff `vlift.md`.
-/
import Fl4Proofs.P2.E2EVUser
import Fl4Proofs.P2.AccessVmLP
import Fl4Proofs.P2.AccessIoLP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY)

noncomputable section
open Classical

section sets
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV} {Locks : S → U64 → Prop}
  {s : S} {x : U64}

theorem ioRS_noV (h : IoRS (st := st) (userV K) Locks s x) : ¬ VData K x ∨ x ∈ K.user :=
  Or.inl fun hv => h.2.1 (Or.inr hv)

theorem ioWS_noV (hK : RegionOKV K) (h : IoWS (st := st) (userV K) Locks s x) : ¬ VData K x ∨ x ∈ K.user := by
  refine Or.inl fun ⟨v, hv, _⟩ => ?_
  have h2 := h.2
  unfold WPerm at h2
  rw [show OwnMap.own (userV K) = OwnMap.own K.toKLayout from rfl, own_vcpu hK hv] at h2
  exact h2

theorem safeW_noV (hK : RegionOKV K) {b : U64} (h : SafeW (userV K) b) : ¬ VData K b := by
  apply notVData_of_region' hK
  rw [← region_userV]
  rcases h with ⟨c, hc⟩ | ⟨t, off, -, ht, -⟩ | ⟨p, hp, -⟩
  · rw [hc]; intro e; cases e
  · rw [ht]; intro e; cases e
  · rw [hp]; intro e; cases e

end sets

/-! ## The layout premise at `userV K` -/

/-- **`VcpuKs`** [J]: no VCPU word lies in the kernel-state block (`ks_base` and its 13568 bytes of global
state: `CUR_DOMAIN`, `DOMAIN_TIME`, the IRQ state, ...). From P1's heap disjointness (a VCPU is a heap object of
type 15, the block is not heap); not a field of `RegionOKV`, kept separate so that `RegionOKV` users are
unchanged. -/
def VcpuKs (K : KLayoutV) : Prop :=
  ∀ v b, InVcpu K v b → ¬ (K.ksb.val ≤ b.val ∧ b.val < K.ksb.val + 13568)

section lay
variable {K : KLayoutV}

theorem ioLay_userV (hK : RegionOKV K) (hks : VcpuKs K) (h : IoLay K.toKLayout) : IoLay (userV K) where
  node := h.node
  tcbw := h.tcbw
  slotw := h.slotw
  slot8 := h.slot8
  tslot := h.tslot
  scw := h.scw
  ks := h.ks
  ksf := h.ksf
  user b hb := by
    rcases hb with hb | ⟨v, hv, _⟩
    · exact h.user b hb
    · exact ⟨hK.none v b hv, hks v b hv⟩

theorem vmLay_userV (hK : RegionOKV K) (hks : VcpuKs K) (h : VmLay K.toKLayout) : VmLay (userV K) where
  io := ioLay_userV hK hks h.io
  epw := h.epw
  rpw := h.rpw

end lay

/-! ## The three paths -/

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} (ar : machine.Arch A)

/-- **`NoVcpuRW` of the VM-fault path at `userV K`.** -/
theorem vm_noVcpuRW (hKV : RegionOKV K) (hA : P0.ArchTotal ar) (hK : OwnMap.RegionOK (userV K))
    (hU : E2E.UserOK (userV K)) (hLA : IoLayA (userV K)) {addr code : U64} (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmPre st ar (userV K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s →
      ∀ d, (userV K).heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, VmPre st ar (userV K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → b ∈ (userV K).user →
      Aligned b →
      VmPre st ar (userV K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) (userV K) Locks (L.wr s b v) = IoRS (st := st) (userV K) Locks s ∧
        IoWS (st := st) (userV K) Locks (L.wr s b v) = IoWS (st := st) (userV K) Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ p : SProg Bool, IsProg (vmBody S addr code) p ∧ NoZero p ∧
      ∀ s s' a r, VmPre st ar (userV K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → (∃ b, VmRep st ar s a b) →
        Alt st (IoRS (st := st) (userV K) Locks s) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m0)
          (· ∈ (userV K).user) s s' →
        interp st ar p s' a = ok r →
          Once st ar (IoRS (st := st) (userV K) Locks s) (· ∈ (userV K).user) ∅ ∅ p s' a) :
    NoVcpuRW K (vm_localPath ar hA hK hU hLA hm hmA huf hpz) where
  rd _ _ _ hr := ioRS_noV hr
  wr s _ hp hw := hw.elim (ioWS_noV hKV) fun hd =>
    Or.inl (safeW_noV hKV (VmBase.dsSafe (show VmPre st ar (userV K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s
      from hp).1.base hd).2)

/-- **`NoVcpuRW` of the VM ReplyRecv path at `userV K`.** -/
theorem rr_noVcpuRW (hKV : RegionOKV K) (hA : P0.ArchTotal ar) (hK : OwnMap.RegionOK (userV K))
    (hU : E2E.UserOK (userV K)) (hLA : IoLayA (userV K)) {rptr ep : U64} (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmRRPre st ar (userV K) T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s →
      ∀ d, (userV K).heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, VmRRPre st ar (userV K) T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s →
      b ∈ (userV K).user → Aligned b →
      VmRRPre st ar (userV K) T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep (L.wr s b v) ∧
        Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) (userV K) Locks (L.wr s b v) = IoRS (st := st) (userV K) Locks s ∧
        IoWS (st := st) (userV K) Locks (L.wr s b v) = IoWS (st := st) (userV K) Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ p : SProg Bool, IsProg (rrBody S rptr ep) p ∧ NoZero p ∧
      ∀ s s' a r, VmRRPre st ar (userV K) T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s →
        (∃ b, RrRep st rptr s b) →
        Alt st (IoRS (st := st) (userV K) Locks s) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m0)
          (· ∈ (userV K).user) s s' →
        interp st ar p s' a = ok r →
          Once st ar (IoRS (st := st) (userV K) Locks s) (· ∈ (userV K).user) ∅ ∅ p s' a) :
    NoVcpuRW K (rr_localPath ar hA hK hU hLA hm hmA huf hpz) where
  rd _ _ _ hr := ioRS_noV hr
  wr s _ hp hw := hw.elim (ioWS_noV hKV) fun hd =>
    Or.inl (safeW_noV hKV (VmBase.dsSafe (show VmRRPre st ar (userV K) T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s
      from hp).1.base hd).2)

/-- **`NoVcpuRW` of the I/O port path at `userV K`.** -/
theorem io_noVcpuRW (hKV : RegionOKV K) (hA : P0.ArchTotal ar) (hK : OwnMap.RegionOK (userV K))
    (hU : E2E.UserOK (userV K)) (hLA : IoLayA (userV K)) {number : I64} (hm : E2E.MasksWr st)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st (userV K) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hmA : ∀ s, P s → ∀ d, (userV K).heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, P s → b ∈ (userV K).user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) (userV K) Locks (L.wr s b v) = IoRS (st := st) (userV K) Locks s ∧
        IoWS (st := st) (userV K) Locks (L.wr s b v) = IoWS (st := st) (userV K) Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ p : SProg Bool, IsProg (ioBodyP S number) p ∧ NoZero p ∧
      ∀ s s' a r, P s → (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
        Alt st (IoRS (st := st) (userV K) Locks s) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m0)
          (· ∈ (userV K).user) s s' →
        interp st ar p s' a = ok r →
          Once st ar (IoRS (st := st) (userV K) Locks s) (· ∈ (userV K).user) ∅ ∅ p s' a) :
    NoVcpuRW K (io_localPath ar hA hK hU hLA hm hPE hmA huf hpz) where
  rd _ _ _ hr := ioRS_noV hr
  wr s _ hp hw := hw.elim (ioWS_noV hKV) fun hd => Or.inl (safeW_noV hKV (IoDS.safe (hPE s hp) hd).2)

end paths

end
end Fl4Proofs.P2.E2EV

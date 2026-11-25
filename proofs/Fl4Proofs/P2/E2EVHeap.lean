/-
P2 (line vlift, gen 2): **the VCPU layout facts from P1's typed heap and P3's kernel-state placement**.

`KLayoutV.vcpus` is a free set of the layout; the only link to P1's heap the proofs need is the layout convention
**`VcpuHeap`** [J]: every VCPU of the layout is a heap object of kind `.other 15` (`KLayoutV`'s docstring; the
analogue of `K.heap = H`, `SlSets`). From it and facts P1 / P3 already carry:

* **`vcpuKs_of`**: `VcpuKs` (no VCPU word in `[ksb, ksb + 13568)`) from `KsInK` (`H`'s `other` objects lie off
  the kernel-state block or inside it), which is P3's `JKern.hksIn` (`ksInK_of_jkern`) and P2's
  `Stall.VcpuEnt.ksIn` (`ksInK_of_ent`) read at `K.heap = H`, `K.ksb = L.ksb s`: a 2^15-byte VCPU does not fit
  in the 13568-byte block. So `VcpuKs` [J] of gen 1 is **derived**; only `VcpuHeap` [J] remains.
* **`noVcpu_of_obj`** / `noVcpu_of_kind`: a word of any other heap object (by pointer, or of a kind other than
  `.other 15`) is no VCPU word (`HeapOK.disj`). `notVData_of_noVcpu`.
* lvm gen 6's `VexitEnt` layout fields (`P2/AccessLvmOwn.lean` on `par/lvm3`):
  - **`ksv_of`**: `ksv` (no VCPU covers `CUR_DOMAIN` / `DOMAIN_TIME`) from `VcpuKs` (offsets 8, 16 < 13568);
  - **`vin_of`** (`inVcpu_off`): `vin` (`PENDING` lies in `v`) from `v ∈ K.vcpus`, `VcpuHeap`, `HeapOK`;
  - **`vfar_pending`**: `vfar` (`VFar` unfolded: outside every TCB, node, SC) of `v.PENDING` from `BXI` with
    P1's sets convention (`T = H.tcbs`, `Ω = H.omega`, the SCs typed), `HeapOK H`, `H`'s `ksIn`, and
    `H v = some (.other 15)` (via `Stall.usrW_vcpu`);
  - **`vfar_ntfn`**: `nfar` (`TAIL_STATE` of a notification) from `BXI`, `n ∈ Nt` and `H n = some .ntfn`.
* **The VM paths' `Pre` at `userV K`**: `TabNoV` (the ASID-table words and the pool words `set_vm_root` reads are
  no VCPU data words), `rdTab_userV`, **`vmPre_userV`**, **`vmRRPre_userV`**. `TabNoV` is derived
  (`tabNoV_of`) from `VcpuHeap`, `HeapOK`, **`VcpuTabOff`** [J] (no VCPU meets the ASID-table area
  `[ksb + 288000, ksb + 304384)`) and **`PoolObj`** [J] (each nonzero table entry is a heap `other` object of at
  least a page that is not a VCPU of the layout).
* **User words**: **`UserObj`** [J] (each user word lies in a heap object that is not a VCPU of the layout),
  `user_noVcpu`.

Premises, each [J] (and what P1 / P3 would have to state for it):
* `VcpuHeap`: layout convention (`K.vcpus` chosen among `H`'s `.other 15` objects; P1's `VcpuPl.bound` /
  `listed` already type every bound / listed VCPU `.other 15`).
* `VcpuTabOff`: P3 has no apartness of `H`'s `other` objects from the ASID-table area (`JKern.hks` excludes
  `other`, `hksIn` covers only the 13568-byte block; `UtKsApart` covers untyped ranges, not objects).
* `PoolObj`, `UserObj`: P3's `SpecCover.arch` makes every spec arch object (pool, frame, VCPU) an `H` `other`
  object of at least a page, and `VsRel` / `JAtZ.fcap` place the table's pools and the buffers' frames in spec
  arch objects; what is missing is that a pool / frame is not one of `K.vcpus` (`K.vcpus` = the spec's VCPU
  objects, a type distinction `H`'s kinds do not make).
-/
import Fl4Proofs.P2.E2EVUserIo
import Fl4Proofs.P2.EntryVcpu
import Fl4Proofs.P3.JointAt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV

noncomputable section
open Classical

/-! ## The layout convention and the derivation of `VcpuKs` -/

/-- **`VcpuHeap`** [J]: every VCPU of the layout is a heap object of kind `.other 15` (module docstring). -/
def VcpuHeap (K : KLayoutV) : Prop := ∀ v ∈ K.vcpus, K.heap v = some (.other 15)

/-- `K`'s heap's `other` objects lie off the kernel-state block or inside it (P3 `JKern.hksIn`). -/
def KsInK (K : KLayoutV) : Prop :=
  ∀ p z, K.heap p = some (.other z) → p.val + 2 ^ z ≤ K.ksb.val ∨ K.ksb.val + 13568 ≤ p.val ∨
    (K.ksb.val ≤ p.val ∧ p.val + 2 ^ z ≤ K.ksb.val + 13568)

section lay
variable {K : KLayoutV}

theorem two15 : (2 : ℕ) ^ 15 = 32768 := by norm_num

/-- **`VcpuKs` derived** from the layout convention and `KsInK`. -/
theorem vcpuKs_of (hV : VcpuHeap K) (hI : KsInK K) : VcpuKs K := by
  rintro v b ⟨hv, h1, h2⟩ ⟨h3, h4⟩
  rcases hI v 15 (hV v hv) with h | h | h
  · rw [two15] at h; omega
  · omega
  · rw [two15] at h; omega

/-- A word of a heap object other than a VCPU of the layout is no VCPU word (`HeapOK.disj`). -/
theorem noVcpu_of_obj (hH : HeapOK K.heap) (hV : VcpuHeap K) {p : U64} {k : HKind} (hp : K.heap p = some k)
    (hpv : p ∉ K.vcpus) {b : U64} (hb : Fl4Proofs.P1.InObj p k b) : ¬ ∃ v, InVcpu K v b := by
  rintro ⟨v, hv, h1, h2⟩
  have hne : p ≠ v := fun e => hpv (e ▸ hv)
  have h := hH.disj p k v _ hp (hV v hv) hne
  have e15 : (HKind.other 15).bits = 15 := rfl
  rw [e15, two15] at h
  unfold Fl4Proofs.P1.InObj at hb
  omega

/-- The same for a heap object of a kind other than `.other 15`. -/
theorem noVcpu_of_kind (hH : HeapOK K.heap) (hV : VcpuHeap K) {p : U64} {k : HKind} (hp : K.heap p = some k)
    (hk : k ≠ .other 15) {b : U64} (hb : Fl4Proofs.P1.InObj p k b) : ¬ ∃ v, InVcpu K v b :=
  noVcpu_of_obj hH hV hp (fun hv => hk (Option.some.inj ((hV p hv).symm.trans hp)).symm) hb

theorem notVData_of_noVcpu {b : U64} (h : ¬ ∃ v, InVcpu K v b) : ¬ VData K b :=
  fun ⟨v, hv, _⟩ => h ⟨v, hv⟩

/-- A word of the kernel-state block is no VCPU word. -/
theorem noVcpu_ks (hks : VcpuKs K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {o : U64} (ho : o.val < 13568) :
    ¬ ∃ v, InVcpu K v (core.num.U64.wrapping_add K.ksb o) := by
  rintro ⟨v, hv⟩
  have e : (core.num.U64.wrapping_add K.ksb o).val = K.ksb.val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  exact hks v _ hv ⟨by rw [e]; omega, by rw [e]; omega⟩

/-- **lvm's `ksv`** (`VexitEnt.ksv`) from `VcpuKs`. -/
theorem ksv_of (hks : VcpuKs K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) :
    (¬ ∃ w, InVcpu K w (core.num.U64.wrapping_add K.ksb layout.ks.CUR_DOMAIN)) ∧
      ¬ ∃ w, InVcpu K w (core.num.U64.wrapping_add K.ksb layout.ks.DOMAIN_TIME) :=
  ⟨noVcpu_ks hks hf (by simp [layout.ks.CUR_DOMAIN]), noVcpu_ks hks hf (by simp [layout.ks.DOMAIN_TIME])⟩

/-- A word at offset `o < 0x8000` of a VCPU of the layout lies in it. -/
theorem inVcpu_off (hH : HeapOK K.heap) (hV : VcpuHeap K) {v : U64} (hv : v ∈ K.vcpus) {o : U64}
    (ho : o.val < 32768) : InVcpu K v (core.num.U64.wrapping_add v o) := by
  have hf := hH.fits v _ (hV v hv)
  have e15 : (HKind.other 15).bits = 15 := rfl
  rw [e15, two15] at hf
  have e : (core.num.U64.wrapping_add v o).val = v.val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  exact ⟨hv, by rw [e]; omega, by rw [e]; omega⟩

/-- **lvm's `vin`** (`VexitEnt.vin`) for a VCPU of the layout. -/
theorem vin_of (hH : HeapOK K.heap) (hV : VcpuHeap K) {v : U64} (hv : v ∈ K.vcpus) :
    InVcpu K v (core.num.U64.wrapping_add v vcpu.PENDING) :=
  inVcpu_off hH hV hv (by simp [vcpu.PENDING])

end lay

/-! ## `KsInK` from P3's `JKern` and P2's `VcpuEnt` -/

section src
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}

theorem ksInK_of_jkern {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs D : Set U64}
    {th : Fl4Proofs.P3.TypedHeap} {s : S} {σ : Fl4Spec.State Unit}
    (J : Fl4Proofs.P3.JKern (L := L) arI H Cs D th s σ) (hH : K.heap = H) (hk : K.ksb = L.ksb s) : KsInK K := by
  intro p z hp
  rw [hH] at hp; rw [hk]
  exact J.hksIn p z hp

/-- **`VcpuKs` from P3's `JKern`** at a state whose heap and kernel-state base are the layout's. -/
theorem vcpuKs_of_jkern {A' : Type} {arI : machine.Arch A'} {H : Heap} {Cs D : Set U64}
    {th : Fl4Proofs.P3.TypedHeap} {s : S} {σ : Fl4Spec.State Unit}
    (J : Fl4Proofs.P3.JKern (L := L) arI H Cs D th s σ) (hH : K.heap = H) (hk : K.ksb = L.ksb s)
    (hV : VcpuHeap K) : VcpuKs K :=
  vcpuKs_of hV (ksInK_of_jkern J hH hk)

theorem ksInK_of_ent {T Cs Ω Sg Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat} {s0 : S}
    (V : Stall.VcpuEnt st T Cs Ω H Sg Rp Scs Nt Z s0) (hH : K.heap = H) (hk : K.ksb = L.ksb s0) : KsInK K := by
  intro p z hp
  rw [hH] at hp; rw [hk]
  exact V.ksIn p z hp

/-- **`VcpuKs` from P2's `VcpuEnt`** (the entry placement the exit wrappers already ask). -/
theorem vcpuKs_of_ent {T Cs Ω Sg Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat} {s0 : S}
    (V : Stall.VcpuEnt st T Cs Ω H Sg Rp Scs Nt Z s0) (hH : K.heap = H) (hk : K.ksb = L.ksb s0)
    (hV : VcpuHeap K) : VcpuKs K :=
  vcpuKs_of hV (ksInK_of_ent V hH hk)

end src

/-! ## lvm's `vfar` / `nfar` from P1's invariant -/

section far
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

/-- **lvm's `vfar`** (`VFar` unfolded) of a VCPU object's `PENDING` word, from P1's invariant with P1's sets
convention (`Stall.usrW_vcpu`). -/
theorem vfar_pending (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hT : T = H.tcbs) (hΩ : Ω = H.omega)
    (hH : HeapOK H) (hScs : ∀ c ∈ Scs, H c = some (.sc (Z c)))
    (hKI : ∀ p z, H p = some (.other z) → p.val + 2 ^ z ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val ∨
      ((L.ksb s).val ≤ p.val ∧ p.val + 2 ^ z ≤ (L.ksb s).val + 13568))
    {v : U64} (hv : H v = some (.other 15)) :
    OutsideObjs st T Cs s (core.num.U64.wrapping_add v vcpu.PENDING) ∧
      ∀ c ∈ Scs, ¬ InSC c (Z c) (core.num.U64.wrapping_add v vcpu.PENDING) := by
  subst hT hΩ
  obtain ⟨⟨Q, R, hq⟩, -⟩ := hI
  have h := Stall.usrW_vcpu hH hScs hKI hq hv
  exact ⟨h.out, h.sc⟩

/-- **lvm's `nfar`** (`VFar` unfolded) of a notification's `TAIL_STATE` word, from P1's invariant: the
notification is one of the placed endpoint / notification objects (`EpsWit`), outside the TCBs and nodes, and
apart from the SCs (`ObjsOK.ntOSc`). -/
theorem vfar_ntfn (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) {n : U64} (hn : n ∈ Nt)
    (hnH : H n = some .ntfn) :
    OutsideObjs st T Cs s (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) ∧
      ∀ c ∈ Scs, ¬ InSC c (Z c) (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE) := by
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -⟩ := hI
  obtain ⟨E, EQ, w1, -, -, -, -, ty⟩ := hq.eps
  have hE : n ∈ E := (ty.2.2.1 n).2 (Or.inr hnH)
  obtain ⟨hP, hON, -⟩ := w1 n hE
  have hO := hX.1
  obtain ⟨hal, hfit⟩ := hO.ntP n hn
  have e8 : layout.ntfn.TAIL_STATE.val = 8 := by simp [layout.ntfn.TAIL_STATE]
  have hb : (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE).val = n.val + 8 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, e8]; omega
  have p12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  refine ⟨⟨?_, fun t ht => ?_, fun c hc => ?_⟩, fun c hc hin => ?_⟩
  · show (core.num.U64.wrapping_add n layout.ntfn.TAIL_STATE).val % 8 = 0
    rw [hb]; omega
  · rw [hb, p12]
    rcases hP.disj t ht with h | h
    · rw [p12] at h; exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · rw [hb]
    rcases hON.1 c hc with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · have h := hO.ntOSc n hn c hc
    unfold InSC at hin
    rw [hb] at hin
    omega

end far

/-! ## The ASID words and the user words -/

section tab
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}

/-- **`VcpuTabOff`** [J]: no VCPU of the layout meets the ASID-table area `[ksb + 288000, ksb + 304384)`, which
fits below 2^64 (module docstring: P3 has this for untyped ranges, `UtKsApart`, not for `H`'s `other` objects). -/
def VcpuTabOff (K : KLayoutV) : Prop :=
  K.ksb.val + 304384 ≤ 2 ^ 64 ∧
    ∀ v ∈ K.vcpus, v.val + 32768 ≤ K.ksb.val + 288000 ∨ K.ksb.val + 304384 ≤ v.val

/-- **`PoolObj`** [J]: each nonzero ASID-table entry names a heap `other` object of at least a page that is not a
VCPU of the layout (module docstring). -/
def PoolObj (K : KLayoutV) (s : S) : Prop :=
  ∀ hi : U64, hi.val < 2048 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
    ∃ z, 12 ≤ z ∧ K.heap (L.mem s (atAF (L.ksb s) hi)) = some (.other z) ∧ L.mem s (atAF (L.ksb s) hi) ∉ K.vcpus

/-- **`UserObj`** [J]: each user word lies in a heap object that is not a VCPU of the layout. -/
def UserObj (K : KLayoutV) : Prop :=
  ∀ b ∈ K.user, ∃ p k, K.heap p = some k ∧ p ∉ K.vcpus ∧ Fl4Proofs.P1.InObj p k b

/-- The ASID words `set_vm_root` may read (`RdTab`) are no VCPU data words. -/
def TabNoV (K : KLayoutV) (s : S) : Prop :=
  ∀ hi : U64, hi.val < 2048 → ¬ VData K (atAF (L.ksb s) hi) ∧
    ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      ¬ VData K (peAF (L.mem s (atAF (L.ksb s) hi)) lo)

/-- **`TabNoV` from the heap**: the table words by `VcpuTabOff`, the pool words by `PoolObj` and `HeapOK`. -/
theorem tabNoV_of (hH : HeapOK K.heap) (hV : VcpuHeap K) (hT : VcpuTabOff K) (hP : PoolObj (L := L) K s)
    (hk : K.ksb = L.ksb s) : TabNoV (L := L) K s := by
  intro hi hh
  obtain ⟨hf, hoff⟩ := hT
  rw [hk] at hf hoff
  refine ⟨notVData_of_noVcpu ?_, fun lo hl hn => notVData_of_noVcpu ?_⟩
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

/-- No user word is a VCPU word, from `UserObj`. -/
theorem user_noVcpu (hH : HeapOK K.heap) (hV : VcpuHeap K) (hU : UserObj K) {b : U64} (hb : b ∈ K.user) :
    ¬ ∃ v, InVcpu K v b := by
  obtain ⟨p, k, hp, hpv, hin⟩ := hU b hb
  exact noVcpu_of_obj hH hV hp hpv hin

theorem ioRS_userV {Locks : S → U64 → Prop} {s : S} {x : U64} (h : IoRS (st := st) K.toKLayout Locks s x)
    (hv : ¬ VData K x) : IoRS (st := st) (userV K) Locks s x :=
  ⟨h.1, fun h' => h'.elim h.2.1 hv, h.2.2⟩

theorem rdTab_userV {Locks : S → U64 → Prop} {s : S} (hT : TabNoV (L := L) K s)
    (h : RdTab (L := L) (IoRS (st := st) K.toKLayout Locks s) s) :
    RdTab (L := L) (IoRS (st := st) (userV K) Locks s) s :=
  fun hi hh => ⟨ioRS_userV (h hi hh).1 (hT hi hh).1,
    fun lo hl hn => ioRS_userV ((h hi hh).2 lo hl hn) ((hT hi hh).2 lo hl hn)⟩

end tab

/-! ## The VM paths' `Pre` at `userV K` -/

section pre
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {Locks : S → U64 → Prop} {A : Type} {ar : machine.Arch A} {s : S}

theorem vmBase_userV (hK : RegionOKV K) (hks : VcpuKs K) (h : VmBase st K.toKLayout T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    VmBase st (userV K) T Cs Ω H Sg Rp Scs Nt Z Ac s :=
  { h with lay := vmLay_userV hK hks h.lay }

/-- **`VmPre K → VmPre (userV K)`** (VM fault path), given `VcpuKs` and `TabNoV`. -/
theorem vmPre_userV (hK : RegionOKV K) (hks : VcpuKs K) (hT : TabNoV (L := L) K s)
    (h : VmPre st ar K.toKLayout T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s) :
    VmPre st ar (userV K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s :=
  ⟨{ h.1 with base := vmBase_userV hK hks h.1.base }, h.2.1, rdTab_userV hT h.2.2⟩

/-- **`VmRRPre K → VmRRPre (userV K)`** (VM ReplyRecv path), given `VcpuKs` and `TabNoV`. -/
theorem vmRRPre_userV (hK : RegionOKV K) (hks : VcpuKs K) (hT : TabNoV (L := L) K s) {rptr ep : U64}
    (h : VmRRPre st ar K.toKLayout T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s) :
    VmRRPre st ar (userV K) T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s :=
  ⟨{ h.1 with base := vmBase_userV hK hks h.1.base }, h.2.1, h.2.2.1, rdTab_userV hT h.2.2.2⟩

end pre

end
end Fl4Proofs.P2.E2EV

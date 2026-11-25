/-
# P2 (line lvm, gen 3): **rule 7 of the ownership map**, the words of a bound VCPU, and the hardware-write premise

`OwnMap.own` (rules 1–6) gives every VCPU word to the gate ("everything else"). #104's local VM paths
(`localvm.handle_vcpu_exit_local`, `handle_vm_timer_irq_local`, `handle_vm_enter_local`,
`handle_vcpu_invocation_local`) write VCPU words (`vcpu.report`'s `PENDING`/`VALID`, `vcpu.enter`'s guest RIP /
intercepts / event-inject, `vcpu.decode`'s state words), so `PathObl.write_own` cannot hold for them under `own`.
This module adds, **beside** `own` (which stays as it is, with all its users):

* `KLayoutV`: `KLayout` plus the set of VCPU objects (`vcpus`, x86 layout `crates/fl4-core/src/vcpu.rs`:
  0x8000 bytes, `heap v = some (.other 15)`);
* **rule 7**, `vcpuOwner`: of a VCPU `v`, the binding word `TCB` (0x5000) and the list links `NEXT` / `PREV`
  (0x5008 / 0x5010) are the gate's (binding and unbinding, `TCBSetVCPU` / `vcpu.detach` / `finalise` / retype,
  run only under the gate); every other word is **`lock v`'s while `v` is bound** (`TCB` word ≠ 0), the gate's
  while unbound. fl4-sync's local VM entries lock `v` (`vm_locks` / `vm_timer_locks` / `vcpu_locks`: the object
  `(v, VCPU_BYTES)`) before calling the body, so an accepted path holds every rule-7 word it touches;
* `ownV K m b`: `vcpuOwner` on a VCPU word, `own K m b` elsewhere (`ownV_off`).

The owner of a rule-7 word is decided by one gate-owned word (`v.TCB`), so the usual carry-over facts hold:

* `ownV_congr` / `ownV_upd_nondec`: owners read only `DecV` words (`own`'s `DecW` and the VCPUs' `TCB` words);
* **`moveHeldV`**: `Serial.MoveHeld (ownV K)` (from `OwnMap.moveHeld` off the VCPUs);
* **`ownDepV`**: `E2E.OwnDep (ownV K) (· ∈ K.user)`;
* per-write checks: `stepOKV_vcpu` (a write of a non-binding word of a VCPU moves no owner and has a free
  class), `stepOKV_of_own` (any `StepOK` for `own` of a write off the VCPUs is one for `ownV`),
  `rpermV_of_own` / `wpermV_of_own` (off the VCPUs the permissions are `own`'s), `wpermV_vcpu` (a bound VCPU's
  non-binding word is held by a path holding `lock v`), `rpermV_vtcb` (the binding word is readable).

**The hardware-write premise** `VmRunFrame K v m m'` [P], stated on the store (memory before / after):
every changed word is user memory or a word of `v` whose owner is `lock v` (bound, non-binding). Its two
sources, both trusted code (`TRUSTED`):
* `fl4_arch_x86_64::vm::run` / `vm::vmx_exit` and `check_vm_asm.py`'s entry/exit ordering: between two kernel
  entries on core `c`, which runs `v`'s bound thread in the guest with no lock held, the hardware changes only
  `v`'s exit frame / `REGS` / `PENDING` / `SVM_CPU` / VMCB/VMCS words (and user memory);
* `Arch::vcpu_sync(v, f)` (#106), called from `vcpu.decode` with `lock v` held (local) or `v` stalled (gate):
  P1's trusted contract `Cur0.vcpu_sync` writes only `v`'s shadow word of field `f`, a rule-7 word.
What it gives (proved): owners are unchanged (`VmRunFrame.ownV_eq`), no gate-owned kernel word changes
(`VmRunFrame.gate`), no kernel word another core may read without `lock v` changes (`VmRunFrame.held`), and every
changed kernel word is, from any core not holding `lock v`, a `Serial.Foreign` write (`VmRunFrame.foreign`): the
hardware's writes look to every other local path exactly as another core's permitted writes do. Why no other
core holds `lock v` while `v` runs: a local path locks `v` only for `v` bound to its own current thread
(`handle_vcpu_invocation_local` checks `v.TCB = ct` after the lock and reads only gate words before it), and a
thread runs on one core. Wiring the hardware step into `Serial.Step` as its own step kind (a batch of `Foreign`
writes) is the remaining part.

Layout facts (`RegionOKV`, `UserOKV`) [J], from P1's typed heap (`HeapOK`: a VCPU's 0x8000 bytes overlap no other
object, slot or node, and VCPUs are 0x8000-aligned so their `TCB` word is aligned and in range): VCPU words lie in
`own`'s `.none` region, two VCPUs do not overlap, and `v + 0x5000` does not wrap.

Existing users are unchanged: nothing here edits `OwnMap.own`, `E2E.Paths` or `Exec`. Moving `E2E.Paths` to
`ownV` (so that the VM paths can be listed) is the lead's step: every existing `LocalPath` lifts by
`rpermV_of_own` / `wpermV_of_own` / `stepOKV_of_own` since no non-VM path touches a VCPU word.
-/
import Fl4Proofs.P2.MoveOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.OwnMapV
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO MoveHeld Foreign)
open Fl4Proofs.P2.OwnMap (KLayout InW fld own region RegionOK DecW)

noncomputable section
open Classical

/-- `KLayout` with the VCPU objects. -/
structure KLayoutV extends KLayout where
  /-- The VCPU objects (`heap v = some (.other 15)` on x86). -/
  vcpus : Set U64

/-- VCPU offsets (`crates/fl4-core/src/vcpu.rs`): `TCB` 0x5000, `PENDING` 0x5028. -/
def oVTCB : U64 := 20480#u64
def oVPENDING : U64 := 20520#u64

/-- The gate's words of a VCPU: `TCB` (0x5000), `NEXT` (0x5008), `PREV` (0x5010). -/
def VcpuGate (o : Nat) : Prop := o = 20480 ∨ o = 20488 ∨ o = 20496

/-- `b` is a word of the VCPU `v`. -/
def InVcpu (K : KLayoutV) (v b : U64) : Prop := v ∈ K.vcpus ∧ InW v 32768 b

/-- **Rule 7**: binding words the gate's; the rest `lock v`'s while bound, the gate's while unbound. -/
def vcpuOwner (m : U64 → U64) (v : U64) (o : Nat) : Owner U64 U64 :=
  if VcpuGate o then .gate else if m (fld v oVTCB) ≠ 0#u64 then .lock v else .gate

/-- **The ownership map with rule 7**: `vcpuOwner` on VCPU words, `own` elsewhere. -/
def ownV (K : KLayoutV) (m : U64 → U64) (b : U64) : Owner U64 U64 :=
  if h : ∃ v, InVcpu K v b then vcpuOwner m (Classical.choose h) (b.val - (Classical.choose h).val)
  else own K.toKLayout m b

/-- **Layout facts for rule 7** [J] (module docstring). -/
structure RegionOKV (K : KLayoutV) : Prop where
  base : RegionOK K.toKLayout
  none : ∀ v b, InVcpu K v b → region K.toKLayout b = .none
  disj : ∀ v w b, InVcpu K v b → InVcpu K w b → v = w
  tcbw : ∀ v ∈ K.vcpus, (fld v oVTCB).val = v.val + 20480

/-- **User memory lies outside the VCPUs' binding words** [J] (as `E2E.UserOK`). -/
structure UserOKV (K : KLayoutV) : Prop where
  base : E2E.UserOK K.toKLayout
  tcbw : ∀ v ∈ K.vcpus, Aligned (fld v oVTCB) ∧ fld v oVTCB ∉ K.user

variable {K : KLayoutV}

theorem ownV_off {m : U64 → U64} {b : U64} (h : ¬ ∃ v, InVcpu K v b) : ownV K m b = own K.toKLayout m b := by
  unfold ownV; rw [dif_neg h]

theorem ownV_on (hK : RegionOKV K) {m : U64 → U64} {v b : U64} (h : InVcpu K v b) :
    ownV K m b = vcpuOwner m v (b.val - v.val) := by
  have h' : ∃ v, InVcpu K v b := ⟨v, h⟩
  unfold ownV; rw [dif_pos h']
  rw [hK.disj _ _ _ (Classical.choose_spec h') h]

theorem vtcb_in (hK : RegionOKV K) {v : U64} (hv : v ∈ K.vcpus) : InVcpu K v (fld v oVTCB) :=
  ⟨hv, by have := hK.tcbw v hv; unfold InW; omega⟩

/-- A VCPU's binding word is the gate's. -/
theorem ownV_vtcb (hK : RegionOKV K) {v : U64} (hv : v ∈ K.vcpus) (m : U64 → U64) :
    ownV K m (fld v oVTCB) = .gate := by
  rw [ownV_on hK (vtcb_in hK hv), hK.tcbw v hv]
  have e : v.val + 20480 - v.val = 20480 := by omega
  rw [e]; simp [vcpuOwner, VcpuGate]

/-- A bound VCPU's non-binding word is `lock v`'s. -/
theorem ownV_bound (hK : RegionOKV K) {m : U64 → U64} {v b : U64} (h : InVcpu K v b)
    (ho : ¬ VcpuGate (b.val - v.val)) (hb : m (fld v oVTCB) ≠ 0#u64) : ownV K m b = .lock v := by
  rw [ownV_on hK h]; simp only [vcpuOwner, if_neg ho, if_pos hb]

/-- A VCPU word decides no `own` owner. -/
theorem vcpu_nondec (hK : RegionOKV K) {v b : U64} (h : InVcpu K v b) : ¬ DecW K.toKLayout b :=
  OwnMap.nondec_of_region hK.base (Or.inr (Or.inr (Or.inr (Or.inl (hK.none v b h)))))

/-- The words `ownV` reads. -/
def DecV (K : KLayoutV) (d : U64) : Prop := DecW K.toKLayout d ∨ ∃ v ∈ K.vcpus, d = fld v oVTCB

/-- A non-binding word of a VCPU decides no `ownV` owner. -/
theorem vcpu_nondecV (hK : RegionOKV K) {w a : U64} (h : InVcpu K w a) (ho : a.val - w.val ≠ 20480) :
    ¬ DecV K a := by
  rintro (hd | ⟨v, hv, rfl⟩)
  · exact vcpu_nondec hK h hd
  · have h1 := hK.tcbw v hv
    have e := hK.disj _ _ _ (vtcb_in hK hv) h
    rw [← e] at ho
    omega

/-- `ownV` reads only `DecV` words. -/
theorem ownV_congr (hK : RegionOKV K) {m m' : U64 → U64} (h : ∀ d, DecV K d → m d = m' d) :
    ownV K m = ownV K m' := by
  funext b
  by_cases hb : ∃ v, InVcpu K v b
  · obtain ⟨v, hv⟩ := hb
    rw [ownV_on hK hv, ownV_on hK hv]
    simp only [vcpuOwner, h _ (Or.inr ⟨v, hv.1, rfl⟩)]
  · rw [ownV_off hb, ownV_off hb, OwnMap.own_congr hK.base (fun d hd => h d (Or.inl hd))]

theorem ownV_upd_nondec (hK : RegionOKV K) {a : U64} (ha : ¬ DecV K a) (m : U64 → U64) (v : U64) :
    ownV K (Function.update m a v) = ownV K m :=
  ownV_congr hK fun d hd => Function.update_of_ne (fun e : d = a => ha (e ▸ hd)) _ _

/-! ## `MoveHeld` and `OwnDep` -/

/-- **`MoveHeld` for `ownV`.** A VCPU word's owner moves only with its gate-owned binding word, which no held
write changes; off the VCPUs `OwnMap.moveHeld` applies (VCPU words decide no `own` owner). -/
theorem moveHeldV (hK : RegionOKV K) : MoveHeld (ownV K) := by
  intro c hs m m' a v x ha hag hx
  by_cases hxv : ∃ w, InVcpu K w x
  · exfalso
    obtain ⟨w, hw⟩ := hxv
    apply hx
    rw [ownV_on hK hw, ownV_on hK hw]
    have hne : fld w oVTCB ≠ a := by
      rintro rfl; rw [ownV_vtcb hK hw.1] at ha; exact ha
    simp only [vcpuOwner, Function.update_of_ne hne]
  · simp only [ownV_off hxv] at hx ⊢
    by_cases hav : ∃ w, InVcpu K w a
    · exfalso; obtain ⟨w, hw⟩ := hav
      exact hx (by rw [OwnMap.own_upd_nondec hK.base (vcpu_nondec hK hw)])
    · rw [ownV_off hav] at ha
      let m'' : U64 → U64 := fun y => if ∃ w, InVcpu K w y then m y else m' y
      have hag'' : ∀ y, PO c hs (own K.toKLayout m y) → m'' y = m y := by
        intro y hy
        by_cases hy' : ∃ w, InVcpu K w y
        · simp only [m'', if_pos hy']
        · simp only [m'', if_neg hy']; exact hag y (by rw [ownV_off hy']; exact hy)
      obtain ⟨h1, h2⟩ := OwnMap.moveHeld hK.base c hs m m'' a v x ha hag'' hx
      have nd : ∀ d, DecW K.toKLayout d → ¬ ∃ w, InVcpu K w d := fun d hd ⟨w, hw⟩ => vcpu_nondec hK hw hd
      have e1 : own K.toKLayout m'' = own K.toKLayout m' := OwnMap.own_congr hK.base fun d hd => by
        simp only [m'', if_neg (nd d hd)]
      have e2 : own K.toKLayout (Function.update m'' a v) = own K.toKLayout (Function.update m' a v) :=
        OwnMap.own_congr hK.base fun d hd => by
          by_cases hda : d = a
          · subst hda; simp only [Function.update_self]
          · simp only [Function.update_of_ne hda, m'', if_neg (nd d hd)]
      rw [← e1, ← e2]; exact ⟨h1, h2⟩

/-- **`OwnDep` for `ownV`**: owners depend on aligned kernel words only. -/
theorem ownDepV (hK : RegionOKV K) (hU : UserOKV K) : E2E.OwnDep (ownV K) (· ∈ K.user) := by
  intro m m' h
  apply ownV_congr hK
  rintro d (hd | ⟨v, hv, rfl⟩)
  · exact h d (OwnMap.decW_ok hU.base hd).1 (OwnMap.decW_ok hU.base hd).2
  · exact h _ (hU.tcbw v hv).1 (hU.tcbw v hv).2

/-- `DecV` words are aligned kernel words. -/
theorem decV_ok (hK : RegionOKV K) (hU : UserOKV K) {d : U64} (h : DecV K d) : Aligned d ∧ d ∉ K.user := by
  rcases h with hd | ⟨v, hv, rfl⟩
  · exact OwnMap.decW_ok hU.base hd
  · exact hU.tcbw v hv

/-! ## Classes and the per-write check -/

/-- A VCPU word's value class is untracked. -/
theorem ko_vcpu (hK : RegionOKV K) {v b : U64} (h : InVcpu K v b) (m0 : U64 → U64) :
    OwnMap.ko K.toKLayout m0 b = .free :=
  OwnMap.ko_free_of_nondec hK.base (vcpu_nondec hK h) m0

/-- **The per-write check of a write to non-binding VCPU words**: changing only such words moves no owner and
keeps every tracked class. -/
theorem stepOKV_vcpu (hK : RegionOKV K) {m m' : U64 → U64}
    (h : ∀ y, m' y ≠ m y → ∃ w, InVcpu K w y ∧ y.val - w.val ≠ 20480)
    (m0 : U64 → U64) (User : U64 → Prop) (c : U64) (lk : U64 → Prop) :
    PathObl.StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) User c lk m m' := by
  have e : ownV K m' = ownV K m := ownV_congr hK fun d hd => by
    by_contra hne
    obtain ⟨w, hw, ho⟩ := h d hne
    exact vcpu_nondecV hK hw ho hd
  refine ⟨fun x hx => absurd (by rw [e]) hx, fun x hx _ => ?_⟩
  obtain ⟨w, hw, -⟩ := h x hx
  exact Or.inr (Or.inr (ko_vcpu hK hw m0))

/-- **Off the VCPUs, `own`'s per-write check is `ownV`'s**: a `StepOK` for `own` of a step that changes no
VCPU word is one for `ownV`. -/
theorem stepOKV_of_own (hK : RegionOKV K) {m m' : U64 → U64} (h : ∀ y, (∃ w, InVcpu K w y) → m' y = m y)
    {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop} {c : U64} {lk : U64 → Prop}
    (hs : PathObl.StepOK (own K.toKLayout) cls ko User c lk m m') :
    PathObl.StepOK (ownV K) cls ko User c lk m m' := by
  refine ⟨fun x hx => ?_, hs.2⟩
  by_cases hxv : ∃ w, InVcpu K w x
  · exfalso
    obtain ⟨w, hw⟩ := hxv
    apply hx
    rw [ownV_on hK hw, ownV_on hK hw]
    simp only [vcpuOwner, h _ ⟨w, vtcb_in hK hw.1⟩]
  · simp only [ownV_off hxv] at hx ⊢
    exact hs.1 x hx

theorem rpermV_of_own {m : U64 → U64} {x c : U64} {lk : U64 → Prop} (hx : ¬ ∃ w, InVcpu K w x)
    (h : PathObl.RPerm (own K.toKLayout) c lk m x) : PathObl.RPerm (ownV K) c lk m x := by
  unfold PathObl.RPerm PathObl.GateOnly at *; rw [ownV_off hx]; exact h

theorem wpermV_of_own {m : U64 → U64} {x c : U64} {lk : U64 → Prop} (hx : ¬ ∃ w, InVcpu K w x)
    (h : PathObl.WPerm (own K.toKLayout) c lk m x) : PathObl.WPerm (ownV K) c lk m x := by
  unfold PathObl.WPerm at *; rw [ownV_off hx]; exact h

/-- A path holding `lock v` may write (and read) the non-binding words of the bound VCPU `v`. -/
theorem wpermV_vcpu (hK : RegionOKV K) {m : U64 → U64} {v b c : U64} {lk : U64 → Prop} (h : InVcpu K v b)
    (ho : ¬ VcpuGate (b.val - v.val)) (hb : m (fld v oVTCB) ≠ 0#u64) (hl : lk v) :
    PathObl.WPerm (ownV K) c lk m b := by
  unfold PathObl.WPerm; rw [ownV_bound hK h ho hb]; exact hl

theorem rpermV_vcpu (hK : RegionOKV K) {m : U64 → U64} {v b c : U64} {lk : U64 → Prop} (h : InVcpu K v b)
    (ho : ¬ VcpuGate (b.val - v.val)) (hb : m (fld v oVTCB) ≠ 0#u64) (hl : lk v) :
    PathObl.RPerm (ownV K) c lk m b :=
  Or.inl (wpermV_vcpu hK h ho hb hl)

/-- The binding word is readable by every path (gate-owned). -/
theorem rpermV_vtcb (hK : RegionOKV K) {m : U64 → U64} {v c : U64} {lk : U64 → Prop} (hv : v ∈ K.vcpus) :
    PathObl.RPerm (ownV K) c lk m (fld v oVTCB) :=
  Or.inr (ownV_vtcb hK hv m)

/-- `PENDING` (0x5028) is a non-binding word of the VCPU. -/
theorem vpending_in (hK : RegionOKV K) {v : U64} (hv : v ∈ K.vcpus) (hp : (fld v oVPENDING).val = v.val + 20520) :
    InVcpu K v (fld v oVPENDING) ∧ ¬ VcpuGate ((fld v oVPENDING).val - v.val) := by
  refine ⟨⟨hv, ?_⟩, ?_⟩
  · unfold InW; omega
  · unfold VcpuGate; omega

/-! ## The hardware-write premise -/

/-- **`VmRunFrame`** [P] (module docstring): from `m` to `m'` only user words and words of `v` that `ownV`
gives to `lock v` (bound, non-binding) change. Sources: `fl4_arch_x86_64::vm::run` / `vm::vmx_exit` (the guest
runs `v` between kernel entries, no lock held) and `Arch::vcpu_sync` (`lock v` held or `v` stalled), both in
`TRUSTED`; `check_vm_asm.py` checks the entry/exit ordering. -/
def VmRunFrame (K : KLayoutV) (v : U64) (m m' : U64 → U64) : Prop :=
  ∀ b, m' b ≠ m b → b ∈ K.user ∨ (InVcpu K v b ∧ ownV K m b = .lock v)

theorem VmRunFrame.refl (v : U64) (m : U64 → U64) : VmRunFrame K v m m := fun _ h => absurd rfl h

/-- A changed kernel word is a non-binding word of `v`. -/
theorem VmRunFrame.kernel (hK : RegionOKV K) {v : U64} {m m' : U64 → U64} (h : VmRunFrame K v m m') {b : U64}
    (hb : m' b ≠ m b) (hu : b ∉ K.user) : InVcpu K v b ∧ b.val - v.val ≠ 20480 ∧ ownV K m b = .lock v := by
  rcases h b hb with h1 | ⟨h1, h2⟩
  · exact absurd h1 hu
  · refine ⟨h1, fun e => ?_, h2⟩
    rw [ownV_on hK h1, e] at h2
    simp [vcpuOwner, VcpuGate] at h2

/-- **The hardware changes no owner.** -/
theorem VmRunFrame.ownV_eq (hK : RegionOKV K) (hU : UserOKV K) {v : U64} {m m' : U64 → U64}
    (h : VmRunFrame K v m m') : ownV K m' = ownV K m :=
  ownV_congr hK fun d hd => by
    by_contra hne
    obtain ⟨hw, ho, -⟩ := h.kernel hK hne (decV_ok hK hU hd).2
    exact vcpu_nondecV hK hw ho hd

/-- **The hardware changes no gate-owned kernel word.** -/
theorem VmRunFrame.gate (hK : RegionOKV K) {v : U64} {m m' : U64 → U64} (h : VmRunFrame K v m m') {x : U64}
    (hu : x ∉ K.user) (hg : ownV K m x = .gate) : m' x = m x := by
  by_contra hne
  have := (h.kernel hK hne hu).2.2
  rw [hg] at this; cases this

/-- **The hardware changes no kernel word a core may read without `lock v`.** -/
theorem VmRunFrame.held (hK : RegionOKV K) {v : U64} {m m' : U64 → U64} (h : VmRunFrame K v m m') {d : U64}
    {hs : U64 → Prop} (hv : ¬ hs v) {x : U64} (hu : x ∉ K.user) (hx : PO d hs (ownV K m x)) : m' x = m x := by
  by_contra hne
  have e := (h.kernel hK hne hu).2.2
  rw [e] at hx
  rcases hx with hx | hx
  · exact hv hx
  · cases hx

/-- **Each hardware write of a kernel word is `Foreign` to every core not holding `lock v`**: what the
hardware does to memory looks, to every other local path, like another core's permitted write. -/
theorem VmRunFrame.foreign (hK : RegionOKV K) {v : U64} {m m' : U64 → U64} (h : VmRunFrame K v m m') {d : U64}
    {hs : U64 → Prop} (hv : ¬ hs v) {b : U64} (hb : m' b ≠ m b) (hu : b ∉ K.user) (m0 : U64 → U64) (x : U64) :
    Foreign (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) d hs m b x := by
  obtain ⟨hw, ho, he⟩ := h.kernel hK hb hu
  refine ⟨?_, fun y hy => absurd (by rw [ownV_upd_nondec hK (vcpu_nondecV hK hw ho)]) hy, ?_⟩
  · rw [he]; rintro (h1 | h1)
    · exact hv h1
    · cases h1
  · rw [ko_vcpu hK hw m0]; exact Or.inr ⟨(fun e => by cases e), (fun e => by cases e)⟩

end

end Fl4Proofs.P2.OwnMapV

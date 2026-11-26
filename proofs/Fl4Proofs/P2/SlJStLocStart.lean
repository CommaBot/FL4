/-
# P2 (line stpost, generation 10): `StartAt` of the VM local paths on the chain; `huf` of `io_pathsK` / `tm_pathsK`

`loc_chain_all` (P2/SlJStLocTop.lean) closes the chain `R` under every stable local entry, and its clause 7 puts
the layout bundle `SlJAt (layoutJ Z H (L.ksb s0) nc)` at every `R` state. This file reads that clause for the
local paths of the entries chained in generations 8–9, and removes the user-write premise `huf` of the I/O port
and `TCB_SetTimer` paths.

## 1. `StartAt` for the newly chained entries
* VM fault (`LocVmf`, clause 9): **`vm_localPathG_startAt`** / **`vm_localPathG2_startAt`**: at an `R` state `σ`,
  ProgGenVmLP's `vm_localPathG` (resp. VmOnce's `vm_localPathG2`) at the chain layout `K`, **with its layout
  premise `hLA : IoLayA K` [J] discharged** from clause 7 (`SlJAt.ioLayA`, as `io_pathsK` since generation 6), starts
  at `σ` given the path's entry facts `VmPre … σ` (VmFPre, `VmGlue` [P], `RdTab` [J]) and the glue's core / locks /
  memory link.
* VM ReplyRecv (`LocRrVm`, clause 10): **`rr_localPathJ_startAt`**: slhuf's `rr_localPathJ` (P2/SlJVm.lean) at the
  chain layout, `hLA` discharged from clause 7. Its `Pre` is `VmRRPreJ = SlJAt K ∧ (K.heap ep = .ep → VmRPre) ∧
  RdTab ∧ VmFoundC`: the `SlJAt K` conjunct is clause 7, and **`VmFoundC` is clause 10's own fl4-sync input `hfd`**
  (`∀ t, cur_thread s = ok t → reply_caps s t = ok (some found)`, word for word, `found = (rptr, ep)`). Left: the
  `VmRPre` part and `RdTab`.
* Frame-cap invocation (`LocInv`, clause 8): **no P2 local path exists** for `handle_invocation_local` on this
  base (no `E2E.LocalPath` over it in P2), so there is no `StartAt` to state; skipped.

## 2. `huf` of `io_pathsK` / `tm_pathsK`
`huf` [J] of both is `PathSide.user_free` at `Pre := SlJAt K ∧ Q K m`. Its `SlJAt` part is slhuf's
`SlJAt.userWr` (P2/SlJHuf.lean). The I/O port's read / write / decline sets `IoRS`, `IoWS`, `IoDS` are kept
(**`SlJAt.ioRWDS_wrSt`**: `own K` reads no user word, `E2E.ownDep` from the bundle's `RegionOK` / `UserOK`; the
current thread is kept, `SlJAt.curW_wr`; the core is kept). What is left is about the caller's `Q` and the glue's
locks only, exactly as slhuf's `sl_huf`:
* `hQ` [J]: `∀ K m s b v, SlJAt K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v)`;
* `hlk` [P] (I/O port only; `tm_pathsK` has its own `hlk` already): `∀ K s b v, SlJAt K s → b ∈ K.user →
  Aligned b → Locks (L.wr s b v) = Locks s` (the form slhuf's `hlk_of_kernelDet` produces).

* **`io_huf`**, **`io_pathsKU`**, **`io_pathsKU_startAt`**: `io_pathsK` / `_startAt` with `huf := io_huf hQ hlk`.
* **`tm_huf`**, **`tm_pathsKU`**, **`tm_pathsKU_startAt`**: `tm_pathsK` / `_startAt` with `huf := tm_huf hQ`.

No statement of an existing declaration changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.SlJStLocTop
import Fl4Proofs.P2.SlJHuf
import Fl4Proofs.P2.SlJVm
import Fl4Proofs.P2.VmOnce
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap

/-! ## 1. `StartAt` of the VM local paths at a chain state -/

section vm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} (ar : machine.Arch A)
variable {A3 : Type} {Rc : S → A3 → Fl4Spec.State Unit → Prop}

/-- (stpost gen 10) **`StartAt` of the VM-fault local path `vm_localPathG` at a chain state** (module docstring):
the layout premise `hLA` is read off the chain's layout clause `h7` (`loc_chain_all`'s clause 7) at the state. -/
theorem vm_localPathG_startAt (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) {addr code : U64}
    (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → b ∈ K.user → Aligned b →
      VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hro : ∀ s s' a r, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → (∃ b, VmRep st ar s a b) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar (R.syscall.handle_vm_fault_local addr code) s' a = ok r →
      E2E.Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_vm_fault_local addr code) s' a)
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), Rc σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : Rc σ a3 τ) (a : A)
    (hV : VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (vm_localPathG ar hA hK hU (h7 σ a3 τ hR).ioLayA (addr := addr) (code := code) hm hmA huf hro)
      c hs μ ((vm_localPathG ar hA hK hU (h7 σ a3 τ hR).ioLayA (addr := addr) (code := code) hm hmA huf hro).body
        σ a) :=
  ⟨σ, a, hV, hc, hl, hμ, rfl⟩

/-- (stpost gen 10) **`StartAt` of the VM-fault local path `vm_localPathG2` at a chain state** (module docstring):
`IsProg` / `NoZero` / `ReadOnce` discharged by the path (hpzg), `hLA` by the chain's layout clause `h7`. -/
theorem vm_localPathG2_startAt (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) {addr code : U64}
    (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → b ∈ K.user → Aligned b →
      VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), Rc σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : Rc σ a3 τ) (a : A)
    (hV : VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (vm_localPathG2 ar hA hK hU (h7 σ a3 τ hR).ioLayA (addr := addr) (code := code) hm hmA huf)
      c hs μ ((vm_localPathG2 ar hA hK hU (h7 σ a3 τ hR).ioLayA (addr := addr) (code := code) hm hmA huf).body
        σ a) :=
  ⟨σ, a, hV, hc, hl, hμ, rfl⟩

/-- (stpost gen 10) **`StartAt` of the VM ReplyRecv local path `rr_localPathJ` at a chain state** (module
docstring): `hLA` and the `SlJAt K` conjunct of `VmRRPreJ` by the chain's layout clause `h7`; `VmFoundC` is
`hfd`, the fl4-sync `found` input of `loc_chain_all`'s clause 10 (word for word). -/
theorem rr_localPathJ_startAt (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    {rptr ep : U64} (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hufR : ∀ s b v, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s → b ∈ K.user → Aligned b →
      ((K.heap ep = some .ep →
          VmRPre st ar K T Cs Ω K.heap Sg (Heap.replies K.heap) Scs Nt Z Ac Locks (L.wr s b v) rptr ep) ∧
        RdTab (L := L) (IoRS (st := st) K Locks (L.wr s b v)) (L.wr s b v)) ∧
      Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ p : SProg Bool, IsProg (rrBody S rptr ep) p ∧ NoZero p ∧
      ∀ s s' a r, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s → (∃ b, RrRep st rptr s b) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r → E2E.Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a)
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), Rc σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : Rc σ a3 τ) (a : A)
    (hfd : ∀ t, sched.cur_thread st σ = ok t → fastpath.reply_caps st σ t = ok (some (rptr, ep)))
    (hV : K.heap ep = some .ep →
      VmRPre st ar K T Cs Ω K.heap Sg (Heap.replies K.heap) Scs Nt Z Ac Locks σ rptr ep)
    (hT : RdTab (L := L) (IoRS (st := st) K Locks σ) σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (rr_localPathJ ar hA hK hU (h7 σ a3 τ hR).ioLayA hm hmA hufR hpz) c hs μ
      ((rr_localPathJ ar hA hK hU (h7 σ a3 τ hR).ioLayA hm hmA hufR hpz).body σ a) :=
  ⟨σ, a, ⟨h7 σ a3 τ hR, hV, hT, hfd⟩, hc, hl, hμ, rfl⟩

end vm

/-! ## 2. `huf` of the I/O port and `TCB_SetTimer` paths -/

section huf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (stpost gen 10) **`IoRS`, `IoWS`, `IoDS` are kept by a user-word write** at a bundle state, the locks kept
(module docstring; `own K` reads no user word, the current thread and core are kept). -/
theorem SlJAt.ioRWDS_wrSt {K : KLayout} {Locks : S → U64 → Prop} {s : S} (B : SlJAt (L := L) K s) {b : U64}
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) (hl : Locks (L.wr s b v) = Locks s) :
    IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
      IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
      IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  have eo : own K (L.mem (L.wr s b v)) = own K (L.mem s) :=
    E2E.ownDep B.regionOK B.userOK _ _ (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))
  have ecur := B.curW_wr hb hba v
  refine ⟨?_, ?_, ?_⟩ <;> funext w
  · simp only [IoRS, RPerm, GateOnly, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoWS, WPerm, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoDS, ecur, LawfulStore.cpu_wr, nodeAt_wr]

/-- (stpost gen 10) **`huf` in `io_pathsK`'s form** (module docstring), from `hQ` [J] (the caller's `Q` survives
a user-word write at a bundle state) and `hlk` [P] (the glue's locks are not changed by a user-word write). -/
theorem io_huf (Locks : S → U64 → Prop) (Q : KLayout → (U64 → U64) → S → Prop)
    (hQ : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro K m s b v hJ hq hb hba
  have hl := hlk K s b v hJ hb hba
  have e := hJ.ioRWDS_wrSt (st := st) hb hba v hl
  exact ⟨⟨hJ.userWr hb v, hQ K m s b v hJ hq hb hba⟩, hl, e.1, e.2.1, e.2.2⟩

/-- (stpost gen 10) **`huf` in `tm_pathsK`'s form** (module docstring), from `hQ` [J] alone. -/
theorem tm_huf (Q : KLayout → (U64 → U64) → S → Prop)
    (hQ : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v)) :
    ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v) :=
  fun K m s b v hJ hq hb hba => ⟨hJ.userWr hb v, hQ K m s b v hJ hq hb hba⟩

end huf

section io
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (stpost gen 10) **The I/O port local path with `huf` discharged** (module docstring): `io_pathsK` with
`huf := io_huf Locks Q hQ hlk`. Premises: `hA`, `hm` [P], `hPE`, `hmA` [J], `hQ` [J], `hlk` [P], `hpz`. -/
noncomputable def io_pathsKU (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hmA : ∀ K m s, SlJAt (L := L) K s → Q K m s → ∀ d, K.heap d = some .tcb →
      m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hQ : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (ioBodyP S number) p ∧ NoZero p ∧
      ∀ s s' a r, (SlJAt (L := L) K s ∧ Q K m s) →
        (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r →
        Fl4Proofs.P2.E2E.Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  io_pathsK (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number hm Q hPE hmA
    (io_huf Locks Q hQ hlk) hpz

/-- (stpost gen 10) **`StartAt` for `io_pathsKU`** at a layout `K` from `SlJAt K σ ∧ Q K m σ` (with
`loc_chain_all`'s clause 7 for `SlJAt K σ` at a chain state). -/
theorem io_pathsKU_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hmA : ∀ K m s, SlJAt (L := L) K s → Q K m s → ∀ d, K.heap d = some .tcb →
      m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hQ : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (ioBodyP S number) p ∧ NoZero p ∧
      ∀ s s' a r, (SlJAt (L := L) K s ∧ Q K m s) →
        (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r →
        Fl4Proofs.P2.E2E.Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : Q K m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (io_pathsKU (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number hm Q hPE hmA hQ hlk hpz
        () K m hK hU) c hs μ
      ((io_pathsKU (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number hm Q hPE hmA hQ hlk hpz
        () K m hK hU).body σ a) :=
  io_pathsK_startAt ar hA number hm Q hPE hmA (io_huf Locks Q hQ hlk) hpz K m hK hU a hJ hq hc hl hμ

end io

section tm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {lk : S → U64 → Prop}
variable {A : Type}

/-- (stpost gen 10) **The `TCB_SetTimer` local path with `huf` discharged** (module docstring): `tm_pathsK` with
`huf := tm_huf Q hQ`. Premises: `hA`, `hm` [P], `hPE`, `hpz`, `hEU`, `hlk`, `hNU` (as `tm_pathsK`), `hQ` [J]. -/
noncomputable def tm_pathsKU (ar : machine.Arch A) (hA : P0.ArchTotal ar) (n : I64) (target : U64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s → StEntKK K st Cs Ω Sg Ac target m s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (Fl4Proofs.P2.stBody S n target) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (StEntKK K st Cs Ω Sg Ac target m) (Fl4Proofs.P2.MaxR K st lk))
    (hEU : ∀ K s b v, Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → b ∈ K.user → Aligned b →
      Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target (L.wr s b v))
    (hlk : ∀ (K : KLayout) s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hNU : ∀ K s, Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ K.user)
    (hQ : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v)) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  tm_pathsK (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE hpz hEU hlk hNU
    (tm_huf Q hQ)

/-- (stpost gen 10) **`StartAt` for `tm_pathsKU`** at a layout `K` from `SlJAt K σ ∧ Q K m σ`. -/
theorem tm_pathsKU_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (n : I64) (target : U64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s → StEntKK K st Cs Ω Sg Ac target m s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (Fl4Proofs.P2.stBody S n target) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (StEntKK K st Cs Ω Sg Ac target m) (Fl4Proofs.P2.MaxR K st lk))
    (hEU : ∀ K s b v, Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → b ∈ K.user → Aligned b →
      Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target (L.wr s b v))
    (hlk : ∀ (K : KLayout) s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hNU : ∀ K s, Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ K.user)
    (hQ : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : Q K m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (tm_pathsKU (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE hpz hEU hlk hNU hQ
        () K m hK hU) c hs μ
      ((tm_pathsKU (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE hpz hEU hlk hNU hQ
        () K m hK hU).body σ a) :=
  tm_pathsK_startAt ar hA n target hm Q hPE hpz hEU hlk hNU (tm_huf Q hQ) K m hK hU a hJ hq hc hl hμ

end tm

end Fl4Proofs.P2.PathObl

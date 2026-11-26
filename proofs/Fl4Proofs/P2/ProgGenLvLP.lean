/-
# P2: the program premises of VM ReplyRecv, `local_vm_exit` and `local_vm_timer_irq` (line hpzg, gen 5)

The generated trees (`P2/ProgGenLv*.lean`, `xtask/scripts/gen_prog.py Lv` on top of the L / Io / Tm chains: 9
functions beyond them) give, on every store and Arch instance:

* `rr_isProg` / `rr_noZero`: `syscall.handle_reply_recv_vm_local` is `R.syscall.handle_reply_recv_vm_local (rptr, ep)`,
  without `zero` / `clr`;
* `vexit_isProg` / `vexit_noZero`: `localvm.handle_vcpu_exit_local` is `R.localvm.handle_vcpu_exit_local v n`;
* `vtimer_isProg` / `vtimer_noZero`: `localvm.handle_vm_timer_irq_local` is
  `R.localvm.handle_vm_timer_irq_local irq pl n`.

So the [P] `IsProg` and [W] `NoZero` premises of these paths hold for the concrete trees, and what is left of the
program premise is `ReadOnce` of the same tree (`hro` [W]):

* `rr_localPathG` / `rr_localPathJG`: `rr_localPath` / `rr_localPathJ` with `hpz := ⟨tree, rr_isProg, rr_noZero, hro⟩`;
* `vexit_localPathG` / `vexit_localPathPG`: `vexit_localPath` / `vexit_localPathP` without `hp` / `hz`;
* `vtimer_localPathG`: `vtimer_localPath` without `hp` / `hz`.

Premises: the paths' own minus `hp` / `hz` (`hpz`'s first two parts); `hro` [W] stays (discharged in
`P2/RrOnce.lean` / `P2/LvmOnce.lean` where it is).
-/
import Fl4Proofs.P2.ProgGenLvTop
import Fl4Proofs.P2.SlJVm
import Fl4Proofs.P2.AccessLvmPo
import Fl4Proofs.P2.AccessLvmTl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout fld own RegionOK oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-- **`IsProg` for the VM ReplyRecv body**: it is the generated tree on every store and Arch instance. -/
theorem rr_isProg (S : Type) (rptr ep : U64) :
    IsProg (rrBody S rptr ep) (R.syscall.handle_reply_recv_vm_local (rptr, ep)) := by
  intro A ar st
  funext s a
  show syscall.handle_reply_recv_vm_local st ar s a (rptr, ep) = _
  rw [R.syscall.handle_reply_recv_vm_local_eq st ar, bind_proj3]

theorem rr_noZero (rptr ep : U64) : NoZero (R.syscall.handle_reply_recv_vm_local (rptr, ep)) :=
  R.syscall.handle_reply_recv_vm_local_nz (rptr, ep)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} (ar : machine.Arch A)

/-- **The VM ReplyRecv local path at the generated tree** (module docstring): `rr_localPath` with `hpz`'s
`IsProg` / `NoZero` discharged; `hro` [W] left. -/
noncomputable def rr_localPathG (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {rptr ep : U64} (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s → b ∈ K.user → Aligned b →
      VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hro : ∀ s s' a r, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s → (∃ b, RrRep st rptr s b) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
        interp st ar (R.syscall.handle_reply_recv_vm_local (rptr, ep)) s' a = ok r →
        Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_reply_recv_vm_local (rptr, ep))
          s' a) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  rr_localPath ar hA hK hU hLA hm hmA huf ⟨_, rr_isProg S rptr ep, rr_noZero rptr ep, hro⟩

/-- **`rr_localPathJ` at the generated tree** (module docstring); `hro` [W] left. -/
noncomputable def rr_localPathJG (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {rptr ep : U64} (hm : E2E.MasksWr st)
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
    (hro : ∀ s s' a r, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s → (∃ b, RrRep st rptr s b) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
        interp st ar (R.syscall.handle_reply_recv_vm_local (rptr, ep)) s' a = ok r →
        Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_reply_recv_vm_local (rptr, ep))
          s' a) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  rr_localPathJ ar hA hK hU hLA hm hmA hufR ⟨_, rr_isProg S rptr ep, rr_noZero rptr ep, hro⟩

end

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV RegionOKV UserOKV)

/-- **`IsProg` for the VM-exit body**: the generated tree on every store and Arch instance. -/
theorem vexit_isProg (S : Type) (v n : U64) :
    IsProg (vexitBody S v n) (R.localvm.handle_vcpu_exit_local v n) := by
  intro A ar st
  funext s a
  show localvm.handle_vcpu_exit_local st ar s a v n = _
  rw [R.localvm.handle_vcpu_exit_local_eq st ar, bind_proj3]

theorem vexit_noZero (v n : U64) : NoZero (R.localvm.handle_vcpu_exit_local v n) :=
  R.localvm.handle_vcpu_exit_local_nz v n

/-- **`IsProg` for the VM-timer body**: the generated tree on every store and Arch instance. -/
theorem vtimer_isProg (S : Type) (irq : U64) (pl : localtimer.TimerIrqPlan) (n : U64) :
    IsProg (vtimerBody S irq pl n) (R.localvm.handle_vm_timer_irq_local irq pl n) := by
  intro A ar st
  funext s a
  show localvm.handle_vm_timer_irq_local st ar s a irq pl n = _
  rw [R.localvm.handle_vm_timer_irq_local_eq st ar, bind_proj3]

theorem vtimer_noZero (irq : U64) (pl : localtimer.TimerIrqPlan) (n : U64) :
    NoZero (R.localvm.handle_vm_timer_irq_local irq pl n) :=
  R.localvm.handle_vm_timer_irq_local_nz irq pl n

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} (ar : machine.Arch A) {v n : U64} {lk : S → U64 → Prop} {m : U64 → U64} {Px : S → Prop}

/-- **`vexit_localPath` at the generated tree** (module docstring): `hp` / `hz` discharged, `hro` [W] left. -/
noncomputable def vexit_localPathG (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar (R.localvm.handle_vcpu_exit_local v n) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout m) (· ∈ K.user)
      (fun s => VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ Px s) (VexitRS K st lk))
    (hEU : ∀ s b v', VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ Px s → b ∈ K.user → Aligned b →
      VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n (L.wr s b v') ∧ Px (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → lk (L.wr s b v') = lk s)
    (hP : ∀ s a s1 a1, VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s → Px s → VPend st v s →
      localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s1, a1) →
      localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a v n =
        ok (true, s1, a1))
    (hPm : ∀ s a s1 a1, VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s → Px s → VPend st v s →
      localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s1, a1) →
      localvm.handle_vcpu_exit_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s a v n = ok (true, s1, a1)) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  vexit_localPath ar hA hK hU (vexit_isProg S v n) (vexit_noZero v n) hm hro hEU hlk hP hPm

/-- **`vexit_localPathP` at the generated tree** (module docstring): `hp` / `hz` discharged, `hro` [W] left. -/
noncomputable def vexit_localPathPG (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar (R.localvm.handle_vcpu_exit_local v n) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout m) (· ∈ K.user)
      (fun s => VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ VexitPEnt K st T Cs H Sg Scs Z m v s)
      (VexitRS K st lk))
    (hEU : ∀ s b v', VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ VexitPEnt K st T Cs H Sg Scs Z m v s →
      b ∈ K.user → Aligned b →
      VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n (L.wr s b v') ∧
        VexitPEnt K st T Cs H Sg Scs Z m v (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → lk (L.wr s b v') = lk s) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  vexit_localPathP ar hA hK hU (vexit_isProg S v n) (vexit_noZero v n) hm hro hEU hlk

variable {irq : U64} {pl : localtimer.TimerIrqPlan}

/-- **`vtimer_localPath` at the generated tree** (module docstring): `hp` / `hz` discharged, `hro` [W] left. -/
noncomputable def vtimer_localPathG (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar (R.localvm.handle_vm_timer_irq_local irq pl n) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout m) (· ∈ K.user)
      (VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n) (VexitRS K st lk))
    (hEU : ∀ s b v', VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → b ∈ K.user → Aligned b →
      VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → lk (L.wr s b v') = lk s)
    (hF : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1))
    (hFm : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s a irq pl n = ok (true, s1, a1))
    (hD : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (false, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (IrqDec st s)) ar s a irq pl n =
        ok (false, s1, a1)) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  vtimer_localPath ar hA hK hU (vtimer_isProg S irq pl n) (vtimer_noZero irq pl n) hm hro hEU hlk hF hFm hD

end

end Fl4Proofs.P2

/-
# P2: `PathObl.move` for the accepted VM-fault local path (line p2e, VM paths)

`vm_move`: an accepted run of `syscall.handle_vm_fault_local` passes `StepOK` at every write (the
run on `mguard st (StepOK …)` ends as the real one), as `io_move` for the I/O port path
(`P2/AccessIoMv.lean`). The VM-fault chain (`AccessVmF` … `AccessVmTail`, `vm_accG`) is stated for
any store answering `IoRS K Locks s` words as `st` (`GRd`), the `VmWd` words of `IoWS K Locks s` as
`st` (`hW`), and the `STATE` writes of homed threads with the values `INACTIVE` / `RUNNING` /
`BLOCKED_ON_REPLY` as `st` (`VmSW`). Here it runs on p2sl's checked store `gd st IoRS (PW …)`
(`P2/MoveSl.lean`):

* `vmWd_notDecW`: a `VmWd` word (node, endpoint / reply object, TCB word off the deciding offsets,
  SC word other than offset 16) is not `DecW`, so `PW` lets every state write it with any value
  (`wall_nondec`);
* `vm_acc_gd`: the `STATE` writes are `PW`-writes (`gd_write_state`): the thread is homed here and
  queued at the entry only on a held lock (`VmSW`'s hypotheses: the handler is queued on the fault
  endpoint, whose lock `local_vm_fault` holds; the faulting thread is `RUNNING` / `RESTART`), and none
  of the three values is a queued state; so the accepted run on `gd` ends as the real run (`vm_accG`);
* `vm_move`: by `run_gd_mguard`; `vm_pathObl_mv`: `vm_pathObl` with `hmv` discharged.

Premises: `RegionOK` [J], `UserOK` [J] of the layout; `VmPre`'s (`P2/AccessVmObl.lean`); `hp` [P]
(`IsProg`: the body is the tree `p`); `hmA` [J]: `ko`'s memory `m0` agrees with the entry state on
every TCB's `AFFINITY` (gate-owned, as p2sl's `move_of_gd` and `io_move`).
-/
import Fl4Proofs.P2.AccessVmObl
import Fl4Proofs.P2.MoveSl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld region oAFFINITY)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **A `VmWd` word decides no owner** (`DecW` is the deciding TCB words, slots, notification
words 24 and SC words 16, each in its own region). -/
theorem vmWd_notDecW (hK : RegionOK K) {b : U64} (h : VmWd K b) : ¬ OwnMap.DecW K b := by
  rintro (⟨t, off, ht, ho, rfl⟩ | hs | ⟨p, hp, rfl⟩ | ⟨q, x, hx, rfl⟩)
  · obtain ⟨hr, hv⟩ := hK.tcb t ht off ho.reg
    rcases h with ⟨c, h⟩ | ⟨p, h⟩ | ⟨t', h, h1, h2, h3, h4, h5⟩ | ⟨p, h, -⟩
    · rw [hr] at h; cases h
    · rw [hr] at h; cases h
    · rw [hr] at h
      cases h
      rcases ho with e | e | e | e | e <;> subst e <;>
        simp only [OwnMap.oAFF_val, OwnMap.oSTATE_val, OwnMap.oBOBJ_val, OwnMap.oDL_val, OwnMap.oHT_val] at hv <;>
        omega
    · rw [hr] at h; cases h
  · have hr := hK.slot b hs
    rcases h with ⟨c, h⟩ | ⟨p, h⟩ | ⟨t', h, -⟩ | ⟨p, h, -⟩
    · rw [hr] at h; cases h
    · rw [hr] at h; cases h
    · rw [hr] at h; cases h
    · rw [hr] at h; cases h
  · have hr := (hK.ntfn p hp).1
    rcases h with ⟨c, h⟩ | ⟨p', h⟩ | ⟨t', h, -⟩ | ⟨p', h, -⟩
    · rw [hr] at h; cases h
    · rw [hr] at h; cases h
    · rw [hr] at h; cases h
    · rw [hr] at h; cases h
  · obtain ⟨hr, hv⟩ := hK.scw q x hx
    rcases h with ⟨c, h⟩ | ⟨p, h⟩ | ⟨t', h, -⟩ | ⟨p, h, h16⟩
    · rw [hr] at h; cases h
    · rw [hr] at h; cases h
    · rw [hr] at h; cases h
    · rw [hr] at h
      cases h
      exact h16 hv

/-- **The accepted VM-fault local path on the checked store `gd` ends as the real run.** -/
theorem vm_acc_gd (hA : P0.ArchTotal ar) (hK : RegionOK K) {s s' : S} {a a' : A} {addr code : U64}
    (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s)
    (hTab : RdTab (L := L) (IoRS (st := st) K Locks s) s)
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (true, s', a')) :
    syscall.handle_vm_fault_local
      (gd st (IoRS (st := st) K Locks s) (OwnMap.PW (L := L) K (L.cpu s) (Locks s) (L.mem s)))
      ar s a addr code = ok (true, s', a') := by
  have nv : ∀ v : U64, (v = sched.TS_INACTIVE ∨ v = sched.TS_RUNNING ∨ v = sched.TS_BLOCKED_ON_REPLY) →
      ¬ OwnMap.QueuedState v := by
    rintro v (rfl | rfl | rfl) <;> unfold OwnMap.QueuedState <;>
      simp [sched.TS_INACTIVE, sched.TS_RUNNING, sched.TS_BLOCKED_ON_REPLY]
  refine vm_accG (gS := gd st (IoRS (st := st) K Locks s) (OwnMap.PW (L := L) K (L.cpu s) (Locks s) (L.mem s)))
    hA P hTab (fun b hw hb => OwnMap.wall_nondec hb.1 (vmWd_notDecW hK hw)) ?_ h
  intro d v hd haff hq hv X
  exact OwnMap.gd_write_state (P.base.hT d hd) ⟨by exact haff, by rw [← OwnMap.stA_fld]; exact hq⟩
    (fun h' => absurd h' (nv v hv))

/-- **`PathObl.move` of an accepted VM-fault run** (module docstring). -/
theorem vm_move (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) {s s1 : S} {a a1 : A}
    {addr code : U64} (P : VmFPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s)
    (hTab : RdTab (L := L) (IoRS (st := st) K Locks s) s)
    (hmA : ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_vm_fault_local m ar x a addr code = interp m ar p x a)
    (h : syscall.handle_vm_fault_local st ar s a addr code = ok (true, s1, a1)) :
    syscall.handle_vm_fault_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
      (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s a addr code = ok (true, s1, a1) := by
  have hg := vm_acc_gd hA hK P hTab h
  rw [hp] at hg ⊢
  exact OwnMap.run_gd_mguard hK hU hmA p hg

/-- **`PathObl` for the VM-fault local path, `move` proved** (`vm_pathObl` with `vm_move`). -/
theorem vm_pathObl_mv (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) (hLA : IoLayA K)
    {addr code : U64}
    (hmA : ∀ s, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_vm_fault_local m ar x a addr code = interp m ar p x a) :
    PathObl st (fun m s a => syscall.handle_vm_fault_local m ar s a addr code) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks
      (VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks)
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) :=
  vm_pathObl hA hK hLA fun s _ _ _ hE h => vm_move hA hK hU hE.1 hE.2.2 (hmA s hE) hp h

end

end Fl4Proofs.P2.PathObl

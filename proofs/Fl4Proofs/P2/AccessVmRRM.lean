/-
# P2: `PathObl.move` for the accepted VM ReplyRecv local path (line p2e, VM paths)

`rr_move`: an accepted run of `syscall.handle_reply_recv_vm_local` passes `StepOK` at every write
(the run on `mguard st (StepOK …)` ends as the real one), as `vm_move` for the VM-fault path
(`P2/AccessVmMv.lean`). `rr_vm_accG` (`P2/AccessVmRRA.lean`) runs on p2sl's checked store
`gd st IoRS (PW …)` (`P2/MoveSl.lean`):

* the `VmWd` words are written by any state with any value (`vmWd_notDecW`, `wall_nondec`); the
  caller's `REPLY_OBJ` (offset 3360) is one: `OwnMap.DecOff` (the move's deciding offsets) has
  `AFFINITY`, `STATE`, `BLOCK_OBJ` and the timer ends, not `REPLY_OBJ` (only the I/O line's
  `Dec` of `AccessIoStep` lists it);
* `rr_acc_gd`: the `STATE` / `BLOCK_OBJ` writes (`RrSW`) are `PW`-writes (`gd_write_state` /
  `gd_write_bobj`): the caller and the receiver are homed here and not queued at the entry (the
  caller `RUNNING` / `RESTART`, the receiver `BLOCKED_ON_REPLY`); of the values only the caller's
  `BLOCKED_ON_RECV` is a queued state, written after its `BLOCK_OBJ := ep`, the endpoint whose lock
  `local_syscall` holds; so the accepted run on `gd` ends as the real run;
* `rr_move`: by `run_gd_mguard`.

Premises: `RegionOK` [J], `UserOK` [J] of the layout; `VmRPre`'s and `hTab` [J]
(`P2/AccessVmRRA.lean`); `hp` [P] (`IsProg`: the body is the tree `p`); `hmA` [J]: `ko`'s memory
`m0` agrees with the entry state on every TCB's `AFFINITY` (as `vm_move`).
-/
import Fl4Proofs.P2.AccessVmRRA
import Fl4Proofs.P2.AccessVmMv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld region oAFFINITY)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **The accepted VM ReplyRecv local path on the checked store `gd` ends as the real run.** -/
theorem rr_acc_gd (hA : P0.ArchTotal ar) (hK : RegionOK K) {s s' : S} {a a' : A} {rptr ep : U64}
    (Q : VmRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep)
    (hTab : RdTab (L := L) (IoRS (st := st) K Locks s) s)
    (h : syscall.handle_reply_recv_vm_local st ar s a (rptr, ep) = ok (true, s', a')) :
    syscall.handle_reply_recv_vm_local
      (gd st (IoRS (st := st) K Locks s) (OwnMap.PW (L := L) K (L.cpu s) (Locks s) (L.mem s)))
      ar s a (rptr, ep) = ok (true, s', a') := by
  have nq : ∀ v : U64, (v = sched.TS_INACTIVE ∨ v = sched.TS_RUNNING ∨ v = sched.TS_RESTART ∨
      v = sched.TS_BLOCKED_ON_REPLY) → ¬ OwnMap.QueuedState v := by
    rintro v (rfl | rfl | rfl | rfl) <;> unfold OwnMap.QueuedState <;>
      simp [sched.TS_INACTIVE, sched.TS_RUNNING, sched.TS_RESTART, sched.TS_BLOCKED_ON_REPLY]
  have P := Q.base
  have hcK : K.heap (L.curW s) = some .tcb := P.hT _ P.cT
  have nqc : ¬ OwnMap.QueuedState (L.mem s (stA (L.curW s))) := by
    rcases P.run with e | e
    · rw [e]; exact nq _ (Or.inr (Or.inr (Or.inl rfl)))
    · rw [e]; exact nq _ (Or.inr (Or.inl rfl))
  have S0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) :=
    ⟨by exact P.curAff, by rw [← OwnMap.stA_fld]; exact fun hq => absurd hq nqc⟩
  refine rr_vm_accG (gS := gd st (IoRS (st := st) K Locks s) (OwnMap.PW (L := L) K (L.cpu s) (Locks s) (L.mem s)))
    hA Q hTab (fun b hw hb => OwnMap.wall_nondec hb.1 (vmWd_notDecW hK hw)) ?_ h
  intro u hu haff hst
  have hu0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) u :=
    ⟨by exact haff, by
      rw [← OwnMap.stA_fld, hst]
      exact fun hq => absurd hq (nq _ (Or.inr (Or.inr (Or.inr rfl))))⟩
  have huK : K.heap u = some .tcb := P.hT _ hu
  exact
    { tR := fun X => OwnMap.gd_write_state hcK S0 (fun h' => absurd h' (nq _ (Or.inr (Or.inr (Or.inl rfl)))))
      tN := fun X => OwnMap.gd_write_state hcK S0 (fun h' => absurd h' (nq _ (Or.inr (Or.inl rfl))))
      tB := fun X hb => OwnMap.gd_write_state hcK S0 (fun _ => by
        show Locks s (L.mem X (blockA (L.curW s))); rw [hb]; exact Q.lk.2)
      bl := fun X => OwnMap.gd_write_bobj hcK S0 (fun _ => Q.lk.2)
      uI := fun X => OwnMap.gd_write_state huK hu0 (fun h' => absurd h' (nq _ (Or.inl rfl)))
      uR := fun X => OwnMap.gd_write_state huK hu0 (fun h' => absurd h' (nq _ (Or.inr (Or.inr (Or.inl rfl)))))
      uN := fun X => OwnMap.gd_write_state huK hu0 (fun h' => absurd h' (nq _ (Or.inr (Or.inl rfl)))) }

/-- **`PathObl.move` of an accepted VM ReplyRecv local run** (module docstring). -/
theorem rr_move (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) {s s1 : S} {a a1 : A}
    {rptr ep : U64} (Q : VmRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep)
    (hTab : RdTab (L := L) (IoRS (st := st) K Locks s) s)
    (hmA : ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_reply_recv_vm_local m ar x a (rptr, ep) = interp m ar p x a)
    (h : syscall.handle_reply_recv_vm_local st ar s a (rptr, ep) = ok (true, s1, a1)) :
    syscall.handle_reply_recv_vm_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
      (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s a (rptr, ep) = ok (true, s1, a1) := by
  have hg := rr_acc_gd hA hK Q hTab h
  rw [hp] at hg ⊢
  exact OwnMap.run_gd_mguard hK hU hmA p hg

end

end Fl4Proofs.P2.PathObl

/-
# P2 (line stpost, generation 5): the syscall local path's layout chain, closed

Lines lstab / locmv reduced the layout requirement of `sl_pathsK`'s `StartAt` (`Fl4Step.start`)
to the [J] premise `LocKeepSt Loc Z.th Z.B H Cx` (`sl_pathsK_startAt_stab'`); line stpost proved
that both arms of an accepted `handle_syscall_local` keep the chain's stable ghosts
(SlJStPost's `jreachSt_sysUStK`, the trap arm; SlJStPostRR's `jreachSt_rrSt`, the ReplyRecv fast
path), each as a `LocSt` step. This file composes them; no `LocKeepSt` / `LocRunMv` premise is left.

* `LocSysSt th B H Cs`: the chain's step relation, `LocSt (LocSys) th B H Cs` — an accepted
  `handle_syscall_local` run with its spec outcome, the kernel-state base kept and `JAtZ` at the
  chain's `th`, `B`, `H`, `Cs` at the end. `LocKeepSt` of it is `locKeepSt_st` (no premise).
* **`sl_pathsK_startAt_loc`** (the top): from a serial exit (`JReachU17`), ONE choice of ghosts
  `Z H Cx nc` gives SerExit's `Fl4Step.ser` facts for `layoutJ Z H (L.ksb s0) nc` (`RegionOK`,
  `UserOK`, `Maps`) and a set `R` of joint states (`JReachSt` over `LocSysSt` at those ghosts) with
  1. `R` holds at the exit;
  2. `R` is closed under the accepted trap arm (`fastpath.fault`), at a spec outcome, given U29S's
     unknown-syscall clause inputs at the run's start (`hct`, `UnkSys`, `NoDbgSys`, `hFin`);
  3. `R` is closed under the accepted ReplyRecv fast path, at a spec outcome, given U29S's syscall
     clause inputs that route reads at `SysReplyRecv` (`hct`, `hflag`, `hFin`, `hfd`);
  4. at every `R` state, `StartAt` for `sl_pathsK` at the exit's layout `layoutJ Z H (L.ksb s0) nc`
     (given the path's `Q` and the glue's core / locks / memory link there).

Premises: U29S's platform inputs (`PlainStore`, `hARI hA hnd hM hKD hPA hT hmax htu hRef hSX hDR`,
all already premises of `kernel_entry_reachU29S`) and `sl_pathsK`'s own path premises
(`hSt hA' hm a0 Q hPE hEr hHr hAr huf hpz`). No [J] layout premise. The per-step inputs in 2. and 3.
are U29S's clause inputs verbatim (a subset: neither `hK` nor `hDL`). The glue identifying an
execution's body start with an `R` state stays `Fl4Step.start` [P] (as in SlJStab).
-/
import Fl4Proofs.P2.SlJStPostRR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop)

/-- **The chain's step relation** (module docstring): an accepted syscall local run with its
spec outcome, keeping the chain's stable ghosts. -/
abbrev LocSysSt (th : TypedHeap) (B : Set (U64 × Fl4Spec.Word)) (H : Heap) (Cs : Set U64) :
    S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop :=
  LocSt (L := L) arI AR (LocSys (st := st) arI) th B H Cs

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Locks : S → U64 → Prop}
variable {A : Type}
variable {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The syscall local path's layout chain, closed** (module docstring): from a serial exit,
one ghost choice gives `Fl4Step.ser`'s facts for the exit's layout and a set of joint states,
containing the exit, closed under both accepted arms of `handle_syscall_local`, at every one of
which `sl_pathsK` meets `StartAt` at that layout. No `LocKeepSt` / `LocRunMv` premise. -/
theorem sl_pathsK_startAt_loc [Fl4Proofs.P1.PlainStore st] {A3 : Type} {arI : machine.Arch A3}
    {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
    (hARI : ARIface arI AR) (hA3 : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A3) MR)
    (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlEntR (st := st) K Locks found s)
    (hHr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlHereR (st := st) K found s)
    (hAr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlAccR (st := st) ar K Locks found s)
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ Q K m s) (SlRS (st := st) K Locks))
    {s0 : S} {a3 : A3} {σ0 : Fl4Spec.State Unit} (h0 : JReachU17 (L := L) arI AR MR s0 a3 σ0) :
    ∃ (Z : XSets) (H : Heap) (Cx : Set U64) (nc : Nat), (∀ c : U64, c ∈ Cx ↔ c.val < nc) ∧
      ∃ (hK : OwnMap.RegionOK (layoutJ Z H (L.ksb s0) nc)) (hU : E2E.UserOK (layoutJ Z H (L.ksb s0) nc)),
      (∀ c : Serial.Cfg U64 U64 U64 U64, SerExit.ExitGhost (L := L) (layoutJ Z H (L.ksb s0) nc) s0 c →
        E2E.Maps (layoutJ Z H (L.ksb s0) nc) c) ∧
      -- 1. the exit
      JReachSt (L := L) arI AR MR (LocSysSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s0 a3 σ0 ∧
      -- 2. the trap arm
      (∀ (s : S) (a : A3) (σ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocSysSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s a σ →
        ∀ (n' : I64) (found' : U64 × U64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n' s →
          NoDbgSys (L := L) arI n' s a →
          (∀ ev, KEvSpec (.sysU n') true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
            KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n' s a) w.2) →
          ∀ s' a', syscall.handle_syscall_local st arI s a n' found' = ok (true, s', a') →
            ∃ ev σ', KEvSpec (.sysU n') true ev ∧ EvOut true ev σ σ' ∧
              JReachSt (L := L) arI AR MR (LocSysSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0)
                s' a' σ') ∧
      -- 3. the ReplyRecv fast path
      (∀ (s : S) (a : A3) (σ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocSysSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s a σ →
        ∀ (found' : U64 × U64), σ.curThread ≠ σ.idleThread →
          (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
            ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
          (∀ x ∈ (specFront .sysReplyRecv σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
            (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A3),
              KFrontF (L := L) arI fl4_abi.syscall.SysReplyRecv s a s' a' →
              JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
              KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
          (∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
            (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 →
            fl4_abi.syscall.SysReplyRecv = fl4_abi.syscall.SysReplyRecv →
            fastpath.reply_caps st s t = ok (some found')) →
          ∀ s' a', syscall.handle_syscall_local st arI s a fl4_abi.syscall.SysReplyRecv found' = ok (true, s', a') →
            ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysReplyRecv σ).1 ∧
              JReachSt (L := L) arI AR MR (LocSysSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0)
                s' a' σ') ∧
      -- 4. `StartAt` at every chain state
      (∀ (m : U64 → U64) (σ : S) (a3' : A3) (τ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocSysSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) σ a3' τ →
        ∀ (a : A), Q (layoutJ Z H (L.ksb s0) nc) m σ → ∀ (c : U64) (hs : U64 → Prop),
          L.cpu σ = c → Locks σ = hs → ∀ (μ : U64 → U64),
          (∀ x, Aligned x → x ∉ (layoutJ Z H (L.ksb s0) nc).user → L.mem σ x = μ x) →
          Fl4Proofs.P2.E2E.StartAt
            (sl_pathsK (Locks := Locks) ar hSt hA hm a0 Q hPE hEr hHr hAr huf hpz () (layoutJ Z H (L.ksb s0) nc)
              m hK hU) c hs μ
            ((sl_pathsK (Locks := Locks) ar hSt hA hm a0 Q hPE hEr hHr hAr huf hpz () (layoutJ Z H (L.ksb s0) nc)
              m hK hU).body σ a)) := by
  obtain ⟨Z, H, Cx, Ac0, Lst0, D0, J, -, -, -, -, -, -, -, hvx⟩ := jreach_invU3 hnd h0.1
  obtain ⟨nc, hnc, hK, hU, hMaps⟩ := SerExit.ser_of_JAtZN J
  have hKS : LocKeepSt (L := L) arI AR (LocSysSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx :=
    locKeepSt_st _ _ _ _ _
  have hsub : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocSys (st := st) arI) Z.th Z.B H Cx s a σ s' a' σ' →
      LocSysSt (L := L) arI AR Z.th Z.B H Cx s a σ s' a' σ' := fun _ _ _ _ _ _ h => h
  have hNS : NativeSys fl4_abi.syscall.SysReplyRecv .sysReplyRecv := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  refine ⟨Z, H, Cx, nc, hnc, hK, hU, hMaps, .exit h0 ⟨Z, Ac0, Lst0, D0, rfl, rfl, rfl, J, hvx⟩, ?_, ?_, ?_⟩
  · intro s a σ hJ n' found' hct hUn hND hFin s' a' hrun
    exact jreachSt_sysUStK hARI hA3 hnd hM hKD hPA hT hmax htu hRef hSX hDR hKS hsub hJ n' found' hct hUn hND
      hFin hrun
  · intro s a σ hJ found' hct hflag hFin hfd s' a' hrun
    exact jreachSt_rrSt hARI hA3 hnd hM hKD hPA hT hmax htu hRef hSX hDR hKS hsub hJ found' hct hNS hflag hFin
      hfd hrun
  · intro m σ a3' τ hR a hQ c hs hc hl μ hμ
    exact sl_pathsK_startAt_stab' hnd ar hSt hA hm a0 Q hPE hEr hHr hAr huf hpz hnc hKS m hK hU hR a hQ hc hl hμ

end

end Fl4Proofs.P2.PathObl

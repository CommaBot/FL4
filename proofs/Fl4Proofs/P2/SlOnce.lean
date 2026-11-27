/-
# P2 (line slhuf, gen 7): `ReadOnce` of the syscall entry's tree

`hro` [W] of `sl_pathsKCG` / `sl_pathsKC5` (`ReadOnce` of `R.syscall.handle_syscall_local n found` at the
bundle states with the canonical `Q`), by cases on the entry state `s`'s own run and the decided thread's home:

* **accepted, trap arm**: the run is guarded on `SlRS s ∧ NU K` (`sl_acc` met with `sl_trap_acc_guardN`), so
  every alternative's run is the same guarded run and reads no racy word (`sl_once_accN`);
* **declined, decided thread homed here**: the same with `sl_home` met with `sl_dec_guardN`;
* **decided thread homed elsewhere** (accepting is then impossible): the walks `sl_once_trap_away` /
  `sl_once_rr_away` (one racy read of the trap arm's receiver, three of distinct words of the replied thread);
* **accepted, ReplyRecv arm**: the run reads the handler's IPC buffer (user words, racy whatever the read set),
  in `copy_mrs_fault_reply_loop1`, each word once (`loop1_once_iter`, `hfr_once`). An alternative's run is the
  entry's run (`interp_agree` on `SlRS s`), so `Once` there is `Once` at the entry (`once_agree`): **`hRR`** [W],
  `Once` of an accepted ReplyRecv run at its own entry state, the one case not yet walked (`SlRROnce`).

* **`sl_hro`**: `hro` from `hRR` [W] (and `hSt`, `hA`, `a0`, `hm`).
* **`sl_pathsKC6`**, `sl_pathsKC6_startAt`: `sl_pathsKC5` with `hpz` built from the generated tree
  (`sl_isProg`, `sl_noZero`) and `sl_hro`. Premises: `hSt`, `hA`, `hm`, `a0`, `hCs` [P], `hKD` [P], `hRR` [W].

Where the user words are (call closure of `syscall.handle_syscall_local`): reads only in
`faults.copy_mrs_fault_reply_loop1` (ReplyRecv arm), writes only through `msg.buf_set` (trap arm's
`copy_mrs_fault`, `set_mr`); `msg.copy_mrs` is not in the closure, so no user word is read after a user write.
-/
import Fl4Proofs.P2.SlOnceB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once ReadOnce)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {Locks : S → U64 → Prop} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

variable (st) in
/-- **`Once` of an accepted ReplyRecv run at its own entry state** [W] (the case of `sl_hro` that reads user
words: the handler's IPC buffer in `copy_mrs_fault_reply_loop1`; `hfr_once` / `loop1_once_iter` give the loop
and the fault reply, the checks before and the switch after are still to be walked on `SlRS s ∧ NU K`). -/
def SlRROnce (Locks : S → U64 → Prop) (n : I64) (found : U64 × U64) (Cs Ω Sg Ac : Set U64) (K : KLayout)
    (m : U64 → U64) : Prop :=
  ∀ s a s1 a1, SlJAt (L := L) K s → SlQ st ar Locks n found Cs Ω Sg Ac K m s → ¬ SlTrap st s →
    syscall.handle_syscall_local st ar s a n found = ok (true, s1, a1) →
    Once st ar (SlRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_syscall_local n found) s a

set_option maxHeartbeats 4000000 in
/-- **`hro` of `sl_pathsKCG` / `sl_pathsKC5`** (module docstring). Premise `hRR` [W] (`SlRROnce`). -/
theorem sl_hro (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (a0 : A)
    (hRR : ∀ K m, SlRROnce st ar Locks n found Cs Ω Sg Ac K m) :
    ∀ K m, ReadOnce st ar (R.syscall.handle_syscall_local n found) (OwnMap.cls K) (OwnMap.ko K m)
      (· ∈ K.user) (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
      (SlRS (st := st) K Locks) := by
  intro K m s s' a r ⟨hJ, hq⟩ Al h
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local mm ar x a n found = interp mm ar (R.syscall.handle_syscall_local n found) x a :=
    fun mm x a => congrFun (congrFun (sl_isProg S n found A ar mm) x) a
  have F := slOF_of ar hSt hA a0 hJ hq
  have E := F.E
  obtain ⟨⟨b0, s1, a1⟩, h0, -⟩ := spec_ex_fd (Fl4Proofs.P0.syscall.handle_syscall_local.p0 st ar s a n found L.total hA)
  cases b0
  · -- declined at the entry
    by_cases hh : L.mem s (affA (slThr st found.1 s)) = L.cpu s
    · have g1 := sl_home ar hA F.P F.I F.D h0 Bool.false_ne_true hh
      have g2 := sl_dec_guardN ar hA F h0 Bool.false_ne_true
      rw [hp] at g1 g2
      exact sl_once_accN ar hm (W0 := fun q => SlDS (L := L) s q ∧ True)
        (fun w hw => (SlDS.ws F.P.preG hw.1).1) Al
        (interp_guard_meet _ (sl_noZero n found) s a _ g1 g2)
    · obtain ⟨rp, ep⟩ := found
      by_cases hS : SlTrap st s
      · exact sl_once_trap_away ar hA F Al hS hh h
      · exact sl_once_rr_away ar hA F Al hS hh h
  · -- accepted at the entry
    by_cases hS : SlTrap st s
    · have g1 := sl_acc ar hA F.P h0
      have g2 := sl_trap_acc_guardN ar hA F hS h0
      rw [hp] at g1 g2
      exact sl_once_accN ar hm (W0 := fun q => SlWS (st := st) K Locks s q ∧ True)
        (fun w hw => hw.1.1) Al (interp_guard_meet _ (sl_noZero n found) s a _ g1 g2)
    · have g1 := sl_acc ar hA F.P h0
      rw [hp] at g1
      exact once_agree hm (R0 := SlRS (st := st) K Locks s) (W0 := SlWS (st := st) K Locks s)
        (fun w hw => hw.1) (fun w hw => hw.1) _ (sl_noZero n found) s s' a _ ∅ ∅ Al.ksb Al.cpu Al.masks Al.read g1
        (hRR K m s a s1 a1 hJ hq hS h0)

/-- **The syscall local path with `hpz` built from the generated tree** (`sl_pathsKC5` with `IsProg` /
`NoZero` from `sl_isProg` / `sl_noZero` and `ReadOnce` from `sl_hro`). Premises: `hSt`, `hA`, `hm`, `a0`,
`hCs` [P], `hKD` [P], `hRR` [W]. -/
noncomputable def sl_pathsKC6 (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hKD : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K Locks s)
    (hRR : ∀ K m, SlRROnce st ar Locks n found Cs Ω Sg Ac K m) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  sl_pathsKC5 (Locks := Locks) ar hSt hA hm a0 hCs hKD
    (fun K m => ⟨_, sl_isProg S n found, sl_noZero n found, sl_hro ar hSt hA hm a0 hRR K m⟩)

/-- **`StartAt` for `sl_pathsKC6`**. -/
theorem sl_pathsKC6_startAt (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hKD : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K Locks s)
    (hRR : ∀ K m, SlRROnce st ar Locks n found Cs Ω Sg Ac K m)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : SlQ st ar Locks n found Cs Ω Sg Ac K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsKC6 (Locks := Locks) ar hSt hA hm a0 hCs hKD hRR () K m hK hU) c hs μ
      ((sl_pathsKC6 (Locks := Locks) ar hSt hA hm a0 hCs hKD hRR () K m hK hU).body σ a) :=
  sl_pathsKC5_startAt ar hSt hA hm a0 hCs hKD _ K m hK hU a hJ hq hc hl hμ

end

end Fl4Proofs.P2.PathObl

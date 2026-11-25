/-
# P2 (line p2sl): the syscall entry beside the gate as an `E2E.LocalPath` value

`sl_localPath` (`syscall.handle_syscall_local`, syscall number `n`, fl4-sync's `found`), assembled as p2lt's
`irq_localPath` (`P2/FootTimerIrqObl.lean`) and p2e's `vm_localPath` (`P2/AccessVmLP.lean`, par/p2vm-m):
`obl` = `sl_pathObl_e`, `side` = `sl_pathSide_e`, `total` = `sl_total`, `once` from the program premise,
with `Pre` any `P` giving `SlPreB` / `SlEntJ` / `SlHereJ` / `SlAccK`, the sets `SlRS` / `SlWS` and
`DS = SlDS`. `slBody`: the extracted body is already generic in the Arch instance, so it is `F` as is.

**The program premise** (`hpz`, one [P]/[W] premise instead of `hFp` / `hz` / `ReadOnce`): there is a tree `p`
with
* `IsProg F p` [P]: the body is `p` on every store and Arch instance;
* `NoZero p` [W]: `p` has no `zero` / `clr` node (not provable for an arbitrary `p` with `IsProg`,
  `handoff/p2io-state.md`; the extracted text reaches no `zero` / `clear_free`, `P2/SlObl.lean`);
* `ReadOnce` [W] for `p`, whole: no part of it is proved on this line. Unlike `IoRS` (p2io's
  `io_readOnce`, whose accepting entries follow from `once_of_guardG`), `SlRS` holds user words, which are
  always racy (`E2E.Racy`), so a run on `guard st (SlRS s) (SlWS s)` does not give `Once`; it is a fact
  about `p`'s reads (no store counts reads, `P2/ReadGap.lean`). Checked true of the extracted body
  (`proofs/Fl4Core/Funs.lean`), each racy word read at most once and no user word read after a write:
  - trap arm, `fastpath.fault` (l.15890): reads no user word. Its only user accesses are writes to the
    receiver's IPC buffer (`faults.set_mrs_fault` l.13103 -> `msg.set_mr` l.7225 -> `msg.buf_set`);
    `msg.lookup_ipc_buffer` (l.7428) reads TCB / slot words only.
  - ReplyRecv arm, `fastpath.reply_recv_found` (l.28507): the user words read are the replier's buffer words
    in `faults.copy_mrs_fault_reply` (l.28423), `copy_mrs_fault_reply_loop1.body` (l.28385):
    `msg.buf_get buf (i + 1)` for strictly increasing `i < n ≤ 18`, so distinct words, each read once;
    the arm writes no user word (the copy targets the receiver's TCB registers).
  - homed elsewhere (declining): the words of the decided thread read before `schedulable_here`
    (l.15742, which reads the core's node words and the gate-owned `AFFINITY` before any other word
    of the thread) are read once each: trap arm `REPLY_OBJ` of the endpoint head; ReplyRecv arm
    `STATE`, `FAULT_TYPE` of the reply's TCB (its `SC` is gate-owned, in `SlRS`). Every decline
    happens before the message copy, so declining runs read no user word.
  The remaining reads are of `SlRS` words that are not user words, which are not racy.
`p` is `hpz.choose`.

Premises (besides `hpz`): `hSt` [P] (`StoreTotal`), `hA` (Arch totality), `a0` (an Arch state), `hK` [J]
(`RegionOK`), `hX` [J] (`RegionOKX`), `hU` [J] (`UserOK`), `hm` [P] (`MasksWr`), `hSe` [J] (`SlSets`),
`hUu` [J] (`U ⊆ K.user`), `hPE` / `hEj` / `hHj` / `hAk` (`SlPreB`, `SlEntJ`, `SlHereJ`, `SlAccK`, fields
tagged there), `huf` [J] (`PathSide.user_free`).
-/
import Fl4Proofs.P2.SlEntJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap

/-- The syscall body as `E2E.LocalPath.F`. -/
abbrev slBody (S : Type) (n : I64) (found : U64 × U64) : ∀ {A : Type}, machine.Arch A → machine.Store S → S →
    A → Result (Bool × S × A) :=
  fun ar m s a => syscall.handle_syscall_local m ar s a n found

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}
variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type}
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω U Sg Ac : Set U64}

/-- P0's totality of the body. -/
theorem sl_total {ar : machine.Arch A} (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (n : I64)
    (found : U64 × U64) (s : S) (a : A) :
    ∃ r, syscall.handle_syscall_local st ar s a n found = ok r := by
  obtain ⟨r, e, -⟩ := spec_ex_fd (Fl4Proofs.P0.syscall.handle_syscall_local.p0 st ar s a n found hSt hA)
  exact ⟨r, e⟩

/-- **The syscall entry beside the gate as a local path** (module docstring); `hpz` is the program premise
([P] `IsProg`, [W] `NoZero`, [W] `ReadOnce`). -/
noncomputable def sl_localPath (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hK : RegionOK K) (hX : RegionOKX K) (hU : Fl4Proofs.P2.E2E.UserOK K) (hm : Fl4Proofs.P2.E2E.MasksWr st)
    (hSe : SlSets K T Rp Scs Nt H Z) (hUu : ∀ b ∈ U, b ∈ K.user) (a0 : A)
    {P : S → Prop} (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hEj : ∀ s, P s → SlEntJ (st := st) K Locks found s)
    (hHj : ∀ s, P s → SlHereJ (st := st) K Z Scs found s)
    (hAk : ∀ s, P s → SlAccK (st := st) ar K Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) P
        (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := slBody S n found
  p := hpz.choose
  Acc := fun b => b = true
  Locks := Locks
  Pre := P
  RS := SlRS (st := st) K Locks
  WS := SlWS (st := st) K Locks
  DS := SlDS (L := L)
  isProg := hpz.choose_spec.1
  obl := sl_pathObl_e ar hSt hA hK hX hU hpz.choose_spec.1 hpz.choose_spec.2.1 hm hSe hUu a0 hPE hEj hHj hAk
  side := sl_pathSide_e ar hSt hA hK hX hU hpz.choose_spec.1 hpz.choose_spec.2.1 hm hSe hUu a0 hPE hEj hHj hAk
    huf
  once := hpz.choose_spec.2.2
  total := fun s a => sl_total hSt hA n found s a
  masks := hm

end

end Fl4Proofs.P2.PathObl

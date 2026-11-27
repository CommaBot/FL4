/-
# P2 (line p2sl): `move` of `handle_syscall_local`'s trap arm

**`syscall.handle_syscall_local.move_trap`**: an accepted run of the syscall
entry beside the gate, for a thread that traps its syscalls (`SlTrap`: the
`fastpath.fault` arm), passes the per-write check `StepOK` of FL4's ownership
map (`OwnMap.own K`, `cls K`, `ko K m`) at every write: the run on
`mguard st Q` succeeds as the real run (`PathObl.move` for accepted runs).

Proof: `guard_acc` on the checked store `gd st ⊤ (PW K c lk m0)`
(`P2/MoveSl.lean`), with `R := ⊤` and `W := WAll (PW …)`: the words the arm
writes other than `STATE` are aligned and decide no owner (`NonDec`, so
`wall_nondec`), the two threads whose `STATE` it writes (the current thread
`t := BLOCKED_ON_REPLY`, the handler `dest := INACTIVE, RUNNING`) are `Safe0`
and the values are not queued states (`gd_write_state`); then `move_of_gd`
through `IsProg` [P].

Premises (besides `guard_acc`'s, at the prefix's end state):

* `hRWf`: `FltAcc` with the write set `NonDec K` (every word the arm writes,
  other than the two `STATE`s, is aligned and decides no owner) [W] (by
  region, from `LayP`: per-word layout work still to do);
* `hSt` [J]: the current thread is a TCB of the layout, homed on this core and
  not queued (it runs);
* `hSd` [J]/[P]: the handler is a TCB of the layout homed on this core
  (`schedulable_here`), and, queued (`BLOCKED_ON_RECV`), on a held lock (its
  `BLOCK_OBJ` is the fault endpoint, which the glue has locked);
* `hm`: `ko`'s memory agrees with the entry state on every `AFFINITY`;
* `RegionOK` [J], `UserOK` [J]; `IsProg` [P].

**`syscall.handle_syscall_local.move_rr`**: the same for the ReplyRecv arm
(`fastpath.reply_recv_found`): the writes other than `STATE` / `BLOCK_OBJ` are
`NonDec` (`hRWr` with `RrAcc`, [W] as `hRWf`); the caller `t` goes Restart,
Running, `BLOCK_OBJ := ep`, then blocked on receive, the receiver `u` Inactive,
Restart / Inactive and Running (`rrSW_gd`). Premises besides `guard_acc`'s:
`hSt` [J] as above; `hSu` [J]/[P]: the reply's thread `u` is a TCB of the layout
homed on this core (`schedulable_here`) and not queued (blocked on reply);
`hlk` [P]: the glue holds the endpoint's lock (`local_syscall` locks the
`found` endpoint), so the caller blocked on it is queued on a held lock.
-/
import Fl4Proofs.P2.AccessSyscall
import Fl4Proofs.P2.MoveSl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2.OwnMap Fl4Proofs.P2.E2E

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- Aligned words that decide no owner: written as by `st` on the checked
store at any state with any value. -/
def NonDec (K : KLayout) (b : U64) : Prop := Aligned b ∧ ¬ DecW K b

theorem PreAcc.wmono {R W W' : U64 → Prop} (hW : ∀ b, W b → W' b) {s : S}
    (K : PreAcc (L := L) R W s) : PreAcc (L := L) R W' s where
  nd o h1 h2 := ⟨(K.nd o h1 h2).1, hW _ (K.nd o h1 h2).2⟩
  fl := K.fl
  nx := K.nx
  fi := hW _ K.fi

theorem ScAcc.wmono {R W W' : U64 → Prop} (hW : ∀ b, W b → W' b) {sc : U64} {sb : Nat}
    (K : ScAcc R W sc sb) : ScAcc R W' sc sb :=
  ⟨K.rd, fun b hb hi => hW _ (K.wr b hb hi), hW _ K.cons⟩

theorem FltAcc.wmono {Z : U64 → Nat} {R W W' : U64 → Prop} (hW : ∀ b, W b → W' b) {s : S}
    {t ptr dest r : U64} (K : FltAcc (L := L) Z R W s t ptr dest r) :
    FltAcc (L := L) Z R W' s t ptr dest r where
  nd o h1 h2 := ⟨(K.nd o h1 h2).1, hW _ (K.nd o h1 h2).2⟩
  dt := K.dt
  cd := K.cd
  kr := K.kr
  tab := K.tab
  fh := K.fh
  eph := ⟨K.eph.1, hW _ K.eph.2⟩
  ept := ⟨K.ept.1, hW _ K.ept.2⟩
  tf k hk := ⟨(K.tf k hk).1, hW _ (K.tf k hk).2⟩
  treg := K.treg
  trp := hW _ K.trp
  drp := K.drp
  daf := K.daf
  ddo := K.ddo
  dsc0 := K.dsc0
  diq := K.diq
  dpr := K.dpr
  dyt := K.dyt
  dst := K.dst
  dfi := K.dfi
  den := K.den
  dib := K.dib
  dvt := K.dvt
  dbs := K.dbs
  dw := ⟨hW _ K.dw.1, hW _ K.dw.2.1, hW _ K.dw.2.2.1, hW _ K.dw.2.2.2⟩
  dreg r hr := hW _ (K.dreg r hr)
  nxt h := hW _ (K.nxt h)
  buf rb hrb hb i hi := hW _ (K.buf rb hrb hb i hi)
  rt := hW _ K.rt
  spo := K.spo
  dsc := K.dsc.wmono hW
  csc := K.csc.wmono hW
  tm := K.tm
  rh := K.rh

theorem RrAcc.wmono {Z : U64 → Nat} {R W W' : U64 → Prop} (hW : ∀ b, W b → W' b) {s : S}
    {t rptr ep u usc : U64} (K : RrAcc (L := L) Z R W s t rptr ep u usc) :
    RrAcc (L := L) Z R W' s t rptr ep u usc where
  nd o h1 h2 := ⟨(K.nd o h1 h2).1, hW _ (K.nd o h1 h2).2⟩
  dt := K.dt
  cd := K.cd
  kr := K.kr
  tab := K.tab
  tSt := K.tSt
  tSc := K.tSc
  tMx := K.tMx
  tIq := K.tIq
  tMi := K.tMi
  tBn := K.tBn
  tPr := K.tPr
  tReg := K.tReg
  tBuf := K.tBuf
  tBw := K.tBw
  ntf := K.ntf
  wRp := hW _ K.wRp
  wEn := hW _ K.wEn
  wEp := hW _ K.wEp
  rRt := K.rRt
  rNx := K.rNx
  rPv := K.rPv
  wNx := hW _ K.wNx
  wPv := hW _ K.wPv
  wRt := hW _ K.wRt
  uSt := K.uSt
  uFt := ⟨K.uFt.1, hW _ K.uFt.2⟩
  uSc := K.uSc
  uPr := K.uPr
  uAf := K.uAf
  uDo := K.uDo
  uIq := K.uIq
  uMx := K.uMx
  uReg r hr := hW _ (K.uReg r hr)
  uYt := K.uYt
  uFi := K.uFi
  uVt := K.uVt
  eTS := K.eTS
  wEh := hW _ K.wEh
  wEt := hW _ K.wEt
  spo := K.spo
  cor := K.cor
  ccs := K.ccs
  uHd := K.uHd
  uscA := K.uscA.wmono hW
  csc := K.csc.wmono hW
  tm := K.tm
  rh := K.rh

theorem not_queued_bor : ¬ QueuedState sched.TS_BLOCKED_ON_REPLY := by
  unfold QueuedState; rw [sched.TS_BLOCKED_ON_REPLY.val_eq]; omega

theorem not_queued_ir {v : U64} (hv : v = sched.TS_INACTIVE ∨ v = sched.TS_RUNNING) : ¬ QueuedState v := by
  unfold QueuedState
  rcases hv with rfl | rfl
  · rw [sched.TS_INACTIVE.val_eq]; omega
  · rw [sched.TS_RUNNING.val_eq]; omega

theorem not_queued_rst : ¬ QueuedState sched.TS_RESTART := by
  unfold QueuedState; rw [sched.TS_RESTART.val_eq]; omega

/-- The ReplyRecv arm's `STATE` / `BLOCK_OBJ` writes on the checked store:
the caller `t` and the receiver `u` are `Safe0`, and the endpoint's lock is
held. -/
theorem rrSW_gd {K : KLayout} {c : U64} {lk : U64 → Prop} {m0 : U64 → U64} {R : U64 → Prop}
    {t ep u : U64} (ht : K.heap t = some .tcb ∧ Safe0 c lk m0 t)
    (hu : K.heap u = some .tcb ∧ Safe0 c lk m0 u) (hlk : lk ep) :
    RrSW (L := L) (gd st R (PW (L := L) K c lk m0)) t ep u where
  tR _ := gd_write_state ht.1 ht.2 fun hq => absurd hq not_queued_rst
  tN _ := gd_write_state ht.1 ht.2 fun hq => absurd hq (not_queued_ir (Or.inr rfl))
  tB X hX := gd_write_state ht.1 ht.2 fun _ => by
    show lk (L.mem X (blockA t)); rw [hX]; exact hlk
  bl _ := gd_write_bobj ht.1 ht.2 fun _ => hlk
  uI _ := gd_write_state hu.1 hu.2 fun hq => absurd hq (not_queued_ir (Or.inl rfl))
  uR _ := gd_write_state hu.1 hu.2 fun hq => absurd hq not_queued_rst
  uN _ := gd_write_state hu.1 hu.2 fun hq => absurd hq (not_queued_ir (Or.inr rfl))

variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **`move` of the accepted trap arm** (module docstring). -/
theorem syscall.handle_syscall_local.move_trap {K : KLayout} (hK : RegionOK K) (hU : UserOK K)
    {lk : U64 → Prop} {m : U64 → U64}
    {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap}
    {Z : U64 → Nat} (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64} {found : U64 × U64}
    {p : SProg Bool}
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p)
    (hm : ∀ d, K.heap d = some .tcb → m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hS : SlTrap st s)
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hpre : PreAcc (L := L) (fun _ => True) (NonDec K) s)
    (hI : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X)
    (hAs : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → AsidOff (L := L) Ω Sg X)
    (hrecv : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (stA dest) = sched.TS_BLOCKED_ON_RECV)
    (hF : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → FaultEntAt (L := L) T Cs Ω U Sg Rp X (L.curW s))
    (hy0f : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (yieldA dest) = 0#u64)
    (hTm : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → TimerOK st T Cs X)
    (hRWf : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r →
        FltAcc (L := L) Z (fun _ => True) (NonDec K) X (L.curW s) ptr dest r)
    (hSt : K.heap (L.curW s) = some .tcb ∧ Safe0 (L.cpu s) lk (L.mem s) (L.curW s))
    (hSd : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r →
        K.heap dest = some .tcb ∧ Safe0 (L.cpu s) lk (L.mem s) dest)
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s', a')) :
    syscall.handle_syscall_local
        (mguard st fun x y => StepOK (own K) (cls K) (ko K m) (· ∈ K.user) (L.cpu s) lk (L.mem x) (L.mem y))
        ar s a n found = ok (true, s', a') := by
  have wn : ∀ b, NonDec K b → WAll (PW (L := L) K (L.cpu s) lk (L.mem s)) b :=
    fun _ hb => wall_nondec hb.1 hb.2
  have hg := syscall.handle_syscall_local.guard_acc
    (gS := gd st (fun _ => True) (PW (L := L) K (L.cpu s) lk (L.mem s)))
    (R := fun _ => True) (W := WAll (PW (L := L) K (L.cpu s) lk (L.mem s))) ar hA hT hN hcT
    (hpre.wmono wn) (fun _ _ _ _ _ => by unfold RdHead; exact ⟨trivial, trivial, trivial⟩) hI hAs
    (fun _ => hrecv) (fun _ => hF) (fun _ => hy0f) (fun _ => hTm)
    (fun _ X a1 hP {_p _b _d _r} hc => (hRWf X a1 hP hc).wmono wn)
    (fun _ X a1 hP {_p _b _d _r} hc =>
      ⟨fun _ => gd_write_state hSt.1 hSt.2 (fun hq => absurd hq not_queued_bor),
        fun _ hv _ => gd_write_state (hSd X a1 hP hc).1 (hSd X a1 hP hc).2
          (fun hq => absurd hq (not_queued_ir hv))⟩)
    (fun h' => absurd hS h') (fun h' => absurd hS h') (fun h' => absurd hS h') (fun h' => absurd hS h')
    (fun h' => absurd hS h') h
  exact move_of_gd hK hU hFp ar hm hg

set_option maxHeartbeats 4000000 in
/-- **`move` of the accepted ReplyRecv arm** (module docstring). -/
theorem syscall.handle_syscall_local.move_rr {K : KLayout} (hK : RegionOK K) (hU : UserOK K)
    {lk : U64 → Prop} {m : U64 → U64}
    {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap}
    {Z : U64 → Nat} (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64} {found : U64 × U64}
    {p : SProg Bool}
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p)
    (hm : ∀ d, K.heap d = some .tcb → m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hS : ¬ SlTrap st s)
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hpre : PreAcc (L := L) (fun _ => True) (NonDec K) s)
    (hI : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X)
    (hAs : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → AsidOff (L := L) Ω Sg X)
    (hPl : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
      RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X (L.curW s) found.1 found.2 u usc)
    (hrz : ∀ X a1, LocalPre (st := st) ar s a (X, a1) →
      L.mem X (rNextA found.1) &&& ~~~1#u64 = 0#u64 ∧ L.mem X (rPrevA found.1) &&& ~~~1#u64 = 0#u64)
    (hy0r : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc → L.mem X (yieldA u) = 0#u64)
    (hRWr : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
      RrAcc (L := L) Z (fun _ => True) (NonDec K) X (L.curW s) found.1 found.2 u usc)
    (hSt : K.heap (L.curW s) = some .tcb ∧ Safe0 (L.cpu s) lk (L.mem s) (L.curW s))
    (hSu : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
        K.heap u = some .tcb ∧ Safe0 (L.cpu s) lk (L.mem s) u)
    (hlk : lk found.2)
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s', a')) :
    syscall.handle_syscall_local
        (mguard st fun x y => StepOK (own K) (cls K) (ko K m) (· ∈ K.user) (L.cpu s) lk (L.mem x) (L.mem y))
        ar s a n found = ok (true, s', a') := by
  have wn : ∀ b, NonDec K b → WAll (PW (L := L) K (L.cpu s) lk (L.mem s)) b :=
    fun _ hb => wall_nondec hb.1 hb.2
  have hg := syscall.handle_syscall_local.guard_acc (U := ∅)
    (gS := gd st (fun _ => True) (PW (L := L) K (L.cpu s) lk (L.mem s)))
    (R := fun _ => True) (W := WAll (PW (L := L) K (L.cpu s) lk (L.mem s))) ar hA hT hN hcT
    (hpre.wmono wn) (fun _ _ _ _ _ => by unfold RdHead; exact ⟨trivial, trivial, trivial⟩) hI hAs
    (fun h' => absurd h' hS) (fun h' => absurd h' hS) (fun h' => absurd h' hS) (fun h' => absurd h' hS)
    (fun h' => absurd h' hS) (fun h' => absurd h' hS)
    (fun _ => hPl) (fun _ => hrz) (fun _ => hy0r)
    (fun _ X a1 hP u usc hc => (hRWr X a1 hP u usc hc).wmono wn)
    (fun _ X a1 hP u usc hc => rrSW_gd hSt (hSu X a1 hP u usc hc) hlk) h
  exact move_of_gd hK hU hFp ar hm hg

end

end

end Fl4Proofs.P2.PathObl

/-
# P2: `PathObl.move` for the accepted I/O port path (line p2io)

`io_move`: an accepted run of `syscall.handle_ioport_local` passes `StepOK` at
every write (the run on `mguard st (StepOK …)` ends as the real one). The
IoPort chain (`AccessIoDec` … `AccessIoEnt`) is stated for any store answering
as `st` on given words (`GRd` / `GWr`, `P2/GSt.lean`) with the two `STATE`
writes of the current thread (`RESTART`, `RUNNING`) a hypothesis of their own
(`IoSW`). Here it runs on p2sl's checked store `gd st IoRS (PW …)`
(`P2/MoveSl.lean`):

* `safe_notDecW` / `wall_safe`: a word no owner depends on (`SafeW`) decides
  nothing (`¬ DecW`), so `PW` lets every state write it with any value;
* `IoPre.mvWr`: the words an accepted run writes besides `STATE` (the node's,
  the current thread's registers, the current SC's ring and `CONSUMED`) are
  such words (`IoWr` for `WAll PW`);
* `IoPre.mvSW`: the current thread is `Safe0` (homed here, `RUNNING` or
  `RESTART`, so not queued), and `RESTART` / `RUNNING` are not queued states:
  `PW` allows both `STATE` writes in every state (`IoSW`);
* `io_acc_gd`: the accepted run on `gd` ends as the real run (`guard_ent`);
* `io_move`: by `run_gd_mguard`; `io_pathObl_mv`: `io_pathObl` with `hmv`
  discharged.

Premises: `RegionOK` [J], `UserOK` [J], `IoLayA` [J] of the layout; `IoPre`'s;
`hp` [P] (`IsProg`: the body is the tree `p`); `hmA` [J]: `ko`'s memory `m0`
agrees with the entry state on every TCB's `AFFINITY` (gate-owned, as p2sl's
`move_of_gd`).
-/
import Fl4Proofs.P2.AccessIoObl
import Fl4Proofs.P2.MoveSl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld oAFFINITY oSTATE GateField TimerField)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A} {number : I64} {p : SProg (Bool)}

/-- **A word no owner depends on decides nothing** (`DecW` is `Dec` and the threads'
`STATE` words). -/
theorem safe_notDecW (hK : RegionOK K) (hA : IoLayA K) {b : U64} (h : SafeW K b) : ¬ OwnMap.DecW K b := by
  rintro (⟨t, off, ht, ho, rfl⟩ | hs | hn | ⟨q, x, hx, e⟩)
  · rcases ho with e | e | e | e | e
    · exact h.notDec hK hA (Or.inr (Or.inl ⟨t, off, ht, Or.inl e, rfl⟩))
    · subst e; exact h.notSt hK hA ht (fld_state t)
    · exact h.notDec hK hA (Or.inr (Or.inl ⟨t, off, ht, Or.inr (Or.inl e), rfl⟩))
    · exact h.notDec hK hA (Or.inr (Or.inl ⟨t, off, ht, Or.inr (Or.inr (Or.inr (Or.inl e))), rfl⟩))
    · exact h.notDec hK hA (Or.inr (Or.inl ⟨t, off, ht, Or.inr (Or.inr (Or.inr (Or.inr e))), rfl⟩))
  · exact h.notDec hK hA (Or.inl hs)
  · exact h.notDec hK hA (Or.inr (Or.inr (Or.inl hn)))
  · exact h.notDec hK hA (Or.inr (Or.inr (Or.inr ⟨q, x, hx, e⟩)))

/-- An aligned word no owner depends on: `PW` lets every state write it. -/
theorem wall_safe (hK : RegionOK K) (hA : IoLayA K) {c : U64} {lk : U64 → Prop} {m : U64 → U64} {b : U64}
    (ha : Aligned b) (h : SafeW K b) : WAll (OwnMap.PW (L := L) K c lk m) b :=
  OwnMap.wall_nondec ha (safe_notDecW hK hA h)

section
variable {s : S} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
include P

/-- **The accepted run's writes besides `STATE`** are `PW`-writes in every state. -/
theorem IoPre.mvWr (hK : RegionOK K) (hA : IoLayA K) {c : U64} {lk : U64 → Prop} {m : U64 → U64} :
    IoWr st (WAll (OwnMap.PW (L := L) K c lk m)) Z s where
  nd o h1 h2 :=
    wall_safe hK hA (nodeAt_aligned P.np h1 h2) (Or.inl ⟨L.cpu s, P.lay.node _ _ (P.inNode o h1)⟩)
  reg r hr := by
    obtain ⟨k, hk, e⟩ := regA_eq P.tA hr
    have hk4 : k.val < 4096 := by omega
    rw [e]
    exact wall_safe hK hA (field_aligned P.tA hk4 (by omega))
      (Or.inr (Or.inl ⟨L.curW s, k.val, P.hT _ P.cT, P.lay.tcbw _ (P.hT _ P.cT) k (by omega) hk4, hk4,
        tcb_wadd_val P.tA hk4, by omega, by omega, by omega, by omega, by omega, by omega⟩))
  ring b ha hb :=
    wall_safe hK hA ha (Or.inr (Or.inr ⟨L.cscW s, P.lay.scw _ _ (P.hSc _ P.cscS) b hb.inSC,
      by have := hb.1; omega⟩))
  cons := by
    obtain ⟨hP, hz⟩ := P.bxi.2.2.1.1.sc _ P.cscS
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    exact wall_safe hK hA (by unfold Aligned; rw [hv, hcv]; omega)
      (Or.inr (Or.inr ⟨L.cscW s, P.lay.scw _ _ (P.hSc _ P.cscS) _ ⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩,
        by rw [hv, hcv]; omega⟩))

/-- **The two `STATE` writes** of the current thread are `PW`-writes in every state:
it is `Safe0` (homed here; `RUNNING` / `RESTART` at the entry, not queued), and
neither value is a queued state. -/
theorem IoPre.mvSW {R : U64 → Prop} {lk : U64 → Prop} :
    IoSW (gd st R (OwnMap.PW (L := L) K (L.cpu s) lk (L.mem s))) st (L.curW s) := by
  have nq : ∀ v, Calm v → ¬ OwnMap.QueuedState v := fun v h => by
    have := h.val; unfold OwnMap.QueuedState; omega
  have hS : OwnMap.Safe0 (L.cpu s) lk (L.mem s) (L.curW s) :=
    ⟨P.curAff, fun hq => absurd hq (by rw [← OwnMap.stA_fld]; exact nq _ P.run)⟩
  exact ⟨fun _ => OwnMap.gd_write_state (P.hT _ P.cT) hS (fun hq => absurd hq (nq _ (Or.inl rfl))),
    fun _ => OwnMap.gd_write_state (P.hT _ P.cT) hS (fun hq => absurd hq (nq _ (Or.inr rfl)))⟩

end

/-- **The accepted I/O port path on the checked store `gd` ends as the real run.** -/
theorem io_acc_gd (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K) {s s' : S} {a a' : A}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {lk : U64 → Prop}
    (h : syscall.handle_ioport_local st ar s a number = ok (true, s', a')) :
    syscall.handle_ioport_local (gd st (IoRS (st := st) K Locks s) (OwnMap.PW (L := L) K (L.cpu s) lk (L.mem s)))
      ar s a number = ok (true, s', a') := by
  obtain ⟨info, -, -, -, ht⟩ := handle_ioport_inv h
  obtain ⟨nx, s1, s2, a1, -, -, hs1, hu, -, -, -, -, -, hh⟩ := ioTail_inv ht
  have hsc2 := (here_facts hh).sc
  have w := prefix_writes ar hA P.tp P.np P.cT hs1 hu
  have e1 : L.mem s2 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (field_aligned P.tA (by simp) (by simp)) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s := (P.hcsc (by rw [← e1]; exact hsc2)).symm
  have hW := P.mvWr hK hLA (c := L.cpu s) (lk := lk) (m := L.mem s)
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  exact syscall.handle_ioport_local.guard_ent ar hA (P.ent (Locks := Locks) hW)
    (P.mid (Locks := Locks) hW hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2)
    (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1
    (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField])).1
    (P.reg (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1 (hW.reg _ (by simp [layout.reg.FAULT_IP]))
    P.mvSW h

/-- **`PathObl.move` of an accepted I/O port run** (module docstring). -/
theorem io_move (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) (hLA : IoLayA K) {s s1 : S}
    {a a1 : A} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hmA : ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_ioport_local m ar x a number = interp m ar p x a)
    (h : syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) :
    syscall.handle_ioport_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
      (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s a number = ok (true, s1, a1) := by
  have hg := io_acc_gd (Locks := Locks) (lk := Locks s) hA hK hLA P h
  rw [hp] at hg ⊢
  exact OwnMap.run_gd_mguard hK hU hmA p hg

/-- **`PathObl` for the I/O port path, `move` proved** (`io_pathObl` with `io_move`). -/
theorem io_pathObl_mv (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) (hLA : IoLayA K)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hmA : ∀ s, P s → ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_ioport_local m ar x a number = interp m ar p x a) :
    PathObl st (fun m s a => syscall.handle_ioport_local m ar s a number) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) :=
  io_pathObl hA hK hLA hPE fun s _ _ _ hE h => io_move hA hK hU hLA (hPE s hE) (hmA s hE) hp h

end

end Fl4Proofs.P2.PathObl

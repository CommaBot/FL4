/-
# P2 (line p2sl): `PathObl` and `PathSide` of the syscall entry beside the gate

`sl_pathObl` / `sl_pathSide`: the per-path obligation of `syscall.handle_syscall_local` (its
two accepted arms: the trap arm `fastpath.fault`, the ReplyRecv arm
`fastpath.reply_recv_found`) with the maximal sets `SlRS` / `SlWS` (aligned words that are
user words or that the path may read / write by `OwnMap.own` at the entry state) and
`DecSet = SlDS` (`FAULT_IP`, `CUR_TIME`, `CONSUMED`), for the ownership map `OwnMap.own K`, the
class maps `OwnMap.cls K` / `OwnMap.ko K m0` and user memory `K.user`.

* `acc`: `guard_acc` on `guard st (SlRS s) (SlWS s)`;
* `dec_alt`: a declined run declines at every alternative (`hna` [W]) and then runs the same on
  the store guarded to `SlDS s` and on `mguard` (`sl_dec_at`: the alternative has the entry's
  core, kernel base and current thread, the node's `CUR_THREAD` being in `SlRS`);
* `read_own` / `write_own` / `aligned`: by the sets' definitions, `SlDS ⊆ SlWS` by `PreAcc`;
* `move`: `syscall.handle_syscall_local.move` (`P2/DecSl.lean`);
* `PathSide.read_aligned`: an accepting entry by `acc` and agreement of the guarded tree
  (`interp_agree`, `P2/PathAgree.lean`); otherwise `hra` [W]; `ko_aligned` by `OwnMap`.

Premises:
* `SlPre` (`hPE`: `Pre` gives the entry facts): `guard_acc`'s and `move`'s premises at the entry
  state, each tagged there ([J] P1/entry facts, [W] per-word layout work `FltAcc` / `RrAcc` /
  `PreAcc` for the two pairs of sets, [P] the glue's locks); `aff` [J]: `ko`'s memory `m0`
  agrees with the entry state on every `AFFINITY` (gate-owned);
* `hK`, `hU` [J] (`RegionOK`, `UserOK`); `hFp` [P] (`IsProg`), `hz` [P] (`NoZero p`: the same commitment as `IsProg`, `p` is the body's own
  call tree; `NoZero` is not derivable from the extensional `IsProg`. Checked on the extracted text by
  `python3 proofs/scratch/callgraph.py syscall.handle_syscall_local`: 410 definitions reachable, Store methods
  used exactly `cur_cpu`, `ks_base`, `read`, `read_pair`, `write`, no `zero` / `clear_free`), `hm` [P]
  (writes leave `frame_masks`);
* `hna` [W]: a run that declines at the entry state declines at every alternative;
* `hra` [W]: `read_aligned` from the alternatives of an entry state that does not accept;
* `huf` [J] (`PathSide.user_free`).

`sl_pathObl_dr` / `sl_pathSide_dr` discharge `hna` / `hra` (`sl_hna`, `sl_hra`) from `SlThr`
[W], facts about the *decided thread* of each arm (the trap arm's receiver, the ReplyRecv
arm's replied thread), split on its `AFFINITY` (gate-owned, in the read set, so equal at every
alternative): homed here, a declining run reads only `SlRS s` and writes only `SlDS s` and the
guarded run agrees at alternatives (`interp_agree`); homed elsewhere, an accepting run would
need `schedulable_here` on it, so every alternative declines. `hra` also uses P0 totality
(`StoreTotal` [P]). The case split is needed because both arms read home-owned words of that
thread (`REPLY_OBJ`; `STATE`, `fault_type`, `SC`) before `schedulable_here` checks it; a
kernel reorder (`schedulable_here` right after reading the thread pointer in `fastpath.fault`,
`reply_recv_found`, `reply_recv_vm_found`) would make the "homed elsewhere" case trivial
(possible later PR; not done, to avoid another re-extraction).
-/
import Fl4Proofs.P2.DecSl
import Fl4Proofs.P2.PathAgree
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- What the path may read: aligned user words and words it may read by `own`. -/
def SlRS (K : KLayout) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ (x ∈ K.user ∨ RPerm (own K) (L.cpu s) (Locks s) (L.mem s) x)

/-- What an accepted run may write: aligned user words and words it may write by `own`
(mirrors `SlRS`; user memory is outside `own`'s domain, `PathObl.write_own` asks `WPerm` only of
non-user words, `PathSide.user_free` covers user-word writes). -/
def SlWS (K : KLayout) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ (x ∈ K.user ∨ WPerm (own K) (L.cpu s) (Locks s) (L.mem s) x)

variable {A : Type} (ar : machine.Arch A)

/-- **The entry facts of the syscall entry beside the gate, without the per-word access facts**
(`SlPre` adds `preG`, `hhd`, `pre`, `hRWf(G)`, `hRWr(G)`; P2/SlDecL.lean and P2/SlAccL.lean derive
those from the layout). -/
structure SlPreB (K : KLayout) (Locks : S → U64 → Prop) (m0 : U64 → U64) (n : I64) (found : U64 × U64)
    (T Cs Ω U Sg Rp Scs Nt Ac : Set U64) (H : Heap) (Z : U64 → Nat) (s : S) : Prop where
  hT : TcbPlaced T
  hN : NodePlaced st T s (L.cpu s)
  hcT : L.curW s ∈ T
  hI : ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X
  hAs : ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → AsidOff (L := L) Ω Sg X
  aff : ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY)
  hSt : K.heap (L.curW s) = some .tcb ∧ Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s)
  -- the trap arm
  hrecv : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (stA dest) = sched.TS_BLOCKED_ON_RECV
  hF : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) →
    FaultEntAt (L := L) T Cs Ω U Sg Rp X (L.curW s)
  hy0f : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (yieldA dest) = 0#u64
  hTm : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → TimerOK st T Cs X
  hSd : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r →
      K.heap dest = some .tcb ∧ Safe0 (L.cpu s) (Locks s) (L.mem s) dest ∧
        SlWS (st := st) K Locks s (stA (L.curW s)) ∧ SlWS (st := st) K Locks s (stA dest)
  -- the ReplyRecv arm
  hPl : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
    RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X (L.curW s) found.1 found.2 u usc
  hrz : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) →
    L.mem X (rNextA found.1) &&& ~~~1#u64 = 0#u64 ∧ L.mem X (rPrevA found.1) &&& ~~~1#u64 = 0#u64
  hy0r : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc → L.mem X (yieldA u) = 0#u64
  hSu : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
      K.heap u = some .tcb ∧ Safe0 (L.cpu s) (Locks s) (L.mem s) u ∧
        SlWS (st := st) K Locks s (stA (L.curW s)) ∧ SlWS (st := st) K Locks s (blockA (L.curW s)) ∧ SlWS (st := st) K Locks s (stA u)
  hlk : ¬ SlTrap st s → Locks s found.2

/-- **The entry facts of the syscall entry beside the gate** (module docstring): the premises
of `guard_acc` for the sets `SlRS` / `SlWS`, and those of `move`, at the entry state `s`, for
every Arch state `a`. `preG`, `hhd`, `pre`, `hRWf(G)`, `hRWr(G)` [W] here (per-word layout:
`PreAcc` / `FltAcc` / `RrAcc` for the read / write sets and, for `move`, for `NonDec`); `slPre_of`
(P2/SlAccL.lean) gives them from the layout, `SlHere` and `SlAccIn` [J]. -/
structure SlPre (K : KLayout) (Locks : S → U64 → Prop) (m0 : U64 → U64) (n : I64) (found : U64 × U64)
    (T Cs Ω U Sg Rp Scs Nt Ac : Set U64) (H : Heap) (Z : U64 → Nat) (s : S) : Prop
    extends SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s where
  preG : PreAcc (L := L) (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) s
  hhd : ∀ a X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
    RdHead (L := L) (SlRS (st := st) K Locks s) X csc
  pre : PreAcc (L := L) (fun _ => True) (NonDec K) s
  hRWf : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r →
      FltAcc (L := L) Z (fun _ => True) (NonDec K) X (L.curW s) ptr dest r
  hRWfG : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r →
      FltAcc (L := L) Z (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) X (L.curW s) ptr dest r
  hRWr : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
    RrAcc (L := L) Z (fun _ => True) (NonDec K) X (L.curW s) found.1 found.2 u usc
  hRWrG : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
    RrAcc (L := L) Z (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) X (L.curW s) found.1 found.2 u usc

/-- The prefix words are in `SlWS` (`PreAcc`). -/
theorem SlDS.ws {K : KLayout} {Locks : S → U64 → Prop} {s : S}
    (hp : PreAcc (L := L) (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) s) {x : U64} (hx : SlDS (L := L) s x) :
    SlWS (st := st) K Locks s x := by
  rcases hx with rfl | rfl | rfl
  · exact hp.fi
  · exact (hp.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2
  · exact (hp.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2

/-- An alternative of the entry state has its current thread (the node's `CUR_THREAD` is in
`SlRS`). -/
theorem sl_alt_cur {K : KLayout} {Locks : S → U64 → Prop} {cl : U64 → U64 → U64}
    {ko' : U64 → Fl4Proofs.P2.Serial.ClsOwner U64} {s s' : S}
    (hp : PreAcc (L := L) (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) s)
    (Al : Alt st (SlRS (st := st) K Locks s) cl ko' (· ∈ K.user) s s') : L.curW s' = L.curW s := by
  unfold LawfulStore.curW
  rw [slDS_node Al.ksb Al.cpu]
  exact Al.read _ (hp.nd _ (by rw [curth0]; omega) (by rw [curth0])).1

variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {p : SProg Bool}

/-- **`acc`**: an accepted run is the same run on `guard st (SlRS s) (SlWS s)`. -/
theorem sl_acc (hA : P0.ArchTotal ar) {s s1 : S} {a a1 : A}
    (E : SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s1, a1)) :
    syscall.handle_syscall_local (guard st (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s)) ar s a n found =
      ok (true, s1, a1) := by
  exact syscall.handle_syscall_local.guard_acc (gS := guard st (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s))
    (R := SlRS (st := st) K Locks s) (W := SlWS (st := st) K Locks s) ar hA E.hT E.hN E.hcT E.preG (E.hhd a) (E.hI a) (E.hAs a)
    (fun h' => E.hrecv h' a) (fun h' => E.hF h' a) (fun h' => E.hy0f h' a) (fun h' => E.hTm h' a)
    (fun h' => E.hRWfG h' a)
    (fun h' X a1 hP {_p _b _d _r} hc =>
      ⟨SWr.of_W (W := SlWS (st := st) K Locks s) (E.hSd h' a X a1 hP hc).2.2.1,
        fun _ _ => SWr.of_W (W := SlWS (st := st) K Locks s) (E.hSd h' a X a1 hP hc).2.2.2⟩)
    (fun h' => E.hPl h' a) (fun h' => E.hrz h' a) (fun h' => E.hy0r h' a) (fun h' => E.hRWrG h' a)
    (fun h' X a1 hP u usc hc =>
      have hw := E.hSu h' a X a1 hP u usc hc
      { tR := SWr.of_W (W := SlWS (st := st) K Locks s) hw.2.2.1
        tN := SWr.of_W (W := SlWS (st := st) K Locks s) hw.2.2.1
        tB := fun _ _ => gst_write (W := SlWS (st := st) K Locks s) hw.2.2.1
        bl := fun _ => gst_write (W := SlWS (st := st) K Locks s) hw.2.2.2.1
        uI := SWr.of_W (W := SlWS (st := st) K Locks s) hw.2.2.2.2
        uR := SWr.of_W (W := SlWS (st := st) K Locks s) hw.2.2.2.2
        uN := SWr.of_W (W := SlWS (st := st) K Locks s) hw.2.2.2.2 })
    h

/-- **`PathObl` for the syscall entry beside the gate** (module docstring). -/
theorem sl_pathObl (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p)
    {P : S → Prop} (hPE : ∀ s, P s → SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hna : ∀ s a r s' r', P s → syscall.handle_syscall_local st ar s a n found = ok r → r.1 ≠ true →
      Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      syscall.handle_syscall_local st ar s' a n found = ok r' → r'.1 ≠ true) :
    PathObl st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact sl_acc ar hA (hPE s hE) h
  · intro s a r hE h hn s' r' Al h'
    have E := hPE s hE
    have hn' := hna s a r s' r' hE h hn Al h'
    exact ⟨hn', sl_dec_at (ar := ar) hK hU Al.ksb Al.cpu (sl_alt_cur E.preG Al) E.pre h' hn'⟩
  · intro s x _ hx hu
    exact hx.2.resolve_left hu
  · intro s x hE hx hu
    rcases hx with hx | hx
    · exact hx.2.resolve_left hu
    · exact (SlDS.ws (hPE s hE).preG hx).2.resolve_left hu
  · intro s x hE hx
    rcases hx with hx | hx
    · exact hx.1
    · exact (SlDS.ws (hPE s hE).preG hx).1
  · intro s a r hE h
    have E := hPE s hE
    exact syscall.handle_syscall_local.move hK hU hA hFp E.aff E.hT E.hN E.hcT E.pre (E.hI a) (E.hAs a)
      E.hSt (fun h' => E.hrecv h' a) (fun h' => E.hF h' a) (fun h' => E.hy0f h' a) (fun h' => E.hTm h' a)
      (fun h' => E.hRWf h' a) (fun h' X a1 hP {_p _b _d _r} hc => ⟨(E.hSd h' a X a1 hP hc).1, (E.hSd h' a X a1 hP hc).2.1⟩)
      (fun h' => E.hPl h' a) (fun h' => E.hrz h' a) (fun h' => E.hy0r h' a) (fun h' => E.hRWr h' a)
      (fun h' X a1 hP u usc hc => ⟨(E.hSu h' a X a1 hP u usc hc).1, (E.hSu h' a X a1 hP u usc hc).2.1⟩)
      E.hlk h

/-- **`PathSide` for the syscall entry beside the gate** (module docstring). -/
theorem sl_pathSide (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {P : S → Prop} (hPE : ∀ s, P s → SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hra : ∀ s s' a r, P s →
      Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      (¬ ∃ s1 a1, syscall.handle_syscall_local st ar s a n found = ok (true, s1, a1)) →
      syscall.handle_syscall_local st ar s' a n found = ok r →
      syscall.handle_syscall_local (guard st (fun b => Aligned b) (fun _ => True)) ar s' a n found = ok r)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s) :
    PathSide st (fun m s a => syscall.handle_syscall_local m ar s a n found)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) := by
  have hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local m ar x a n found = interp m ar p x a :=
    fun m x a => congrFun (congrFun (hFp A ar m) x) a
  refine ⟨?_, fun s x _ hx => hx.1, ko_aligned hK hU m0, huf⟩
  intro s s' a r hE Al h
  by_cases hac : ∃ s1 a1, syscall.handle_syscall_local st ar s a n found = ok (true, s1, a1)
  · obtain ⟨s1, a1, h0⟩ := hac
    have hg := sl_acc ar hA (hPE s hE) h0
    rw [hp] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) p hz s s' a true s1 a1
      Al.ksb Al.cpu Al.masks Al.read hg
    have hs := interp_to (st := st) (st' := st) (fun _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      rfl rfl rfl p hz s' a _ hg'
    show syscall.handle_syscall_local _ ar s' a n found = ok r
    rw [hp] at h ⊢
    rw [hs] at h
    rw [← h]
    exact interp_mono (fun _ hw => hw.1) (fun _ _ => trivial) p hz s' a _ hg'
  · exact hra s s' a r hE Al hac h

/-- **The decided thread** [W] (module docstring): `thr s` is the thread on whose home core an
arm's acceptance depends (the trap arm's receiver, the handler endpoint's head; the ReplyRecv
arm's replied thread, `Reply.tcb found.1`), `TW t` the words of `t` a run reads before
`schedulable_here` checks `t`. Each field is a statement about the code of one arm:
* `alt`: `thr` is read from the read set, so it is the same at every alternative;
* `acc`: an accepting run at an alternative passes `schedulable_here` on it (`AFFINITY = cur_cpu`),
  and its `AFFINITY` (gate-owned) is a read-set word, so it is this core at the entry state;
* `home`: homed here, a declining run reads only `SlRS s` and writes only `SlDS s` (its words
  are then this core's);
* `away`: homed elsewhere, a run at an alternative reads only `SlRS s` and `TW (thr s)`
  (aligned, `twA`) before it declines at `schedulable_here`. -/
structure SlThr (P : S → Prop) (K : KLayout) (Locks : S → U64 → Prop) (thr : S → U64)
    (TW : U64 → U64 → Prop) : Prop where
  alt : ∀ s s', P s →
    Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' → thr s' = thr s
  acc : ∀ s s' a r, P s →
    Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
    syscall.handle_syscall_local st ar s' a n found = ok r → r.1 = true →
    L.mem s (affA (thr s)) = L.cpu s
  home : ∀ s a r, P s → syscall.handle_syscall_local st ar s a n found = ok r → r.1 ≠ true →
    L.mem s (affA (thr s)) = L.cpu s →
    syscall.handle_syscall_local (guard st (SlRS (st := st) K Locks s) (SlDS (L := L) s)) ar s a n found = ok r
  twA : ∀ t b, TW t b → Aligned b
  away : ∀ s s' a r, P s →
    Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
    L.mem s (affA (thr s)) ≠ L.cpu s → syscall.handle_syscall_local st ar s' a n found = ok r →
    syscall.handle_syscall_local (guard st (fun b => SlRS (st := st) K Locks s b ∨ TW (thr s) b) (fun _ => True))
      ar s' a n found = ok r

/-- A declined run at `s` is, at every alternative `s'`, a run on `guard st (SlRS s) (SlDS s)`
declining with the same flag and Arch state (`interp_agree`), and then on `st` (`interp_to`). -/
theorem sl_dec_alt_run (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {s s' : S} {a : A} {b : Bool} {s1 : S} {a1 : A}
    (hpre : PreAcc (L := L) (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    (hg : syscall.handle_syscall_local (guard st (SlRS (st := st) K Locks s) (SlDS (L := L) s)) ar s a n found =
      ok (b, s1, a1)) :
    ∃ s1', syscall.handle_syscall_local (guard st (SlRS (st := st) K Locks s) (SlDS (L := L) s)) ar s' a n found =
        ok (b, s1', a1) ∧ syscall.handle_syscall_local st ar s' a n found = ok (b, s1', a1) := by
  have hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local m ar x a n found = interp m ar p x a :=
    fun m x a => congrFun (congrFun (hFp A ar m) x) a
  rw [hp] at hg
  obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => (SlDS.ws hpre hw).1) p hz s s' a b s1 a1
    Al.ksb Al.cpu Al.masks Al.read hg
  refine ⟨s1', by rw [hp]; exact hg', ?_⟩
  rw [hp]
  exact interp_to (st := st) (st' := st) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    rfl rfl rfl p hz s' a _ hg'

/-- **`hna` from `SlThr`**: a run declining at the entry state declines at every alternative
(decided thread homed here: the guarded run agrees; elsewhere: an accepting run would need
its `AFFINITY`, a read-set word, to be this core). -/
theorem sl_hna (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {P : S → Prop} (hPE : ∀ s, P s → SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    {thr : S → U64} {TW : U64 → U64 → Prop}
    (Th : SlThr (st := st) ar (n := n) (found := found) (m0 := m0) P K Locks thr TW) :
    ∀ s a r s' r', P s → syscall.handle_syscall_local st ar s a n found = ok r → r.1 ≠ true →
      Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      syscall.handle_syscall_local st ar s' a n found = ok r' → r'.1 ≠ true := by
  intro s a r s' r' hP h hn Al h'
  by_cases hh : L.mem s (affA (thr s)) = L.cpu s
  · obtain ⟨b, s1, a1⟩ := r
    obtain ⟨s1', -, h2⟩ := sl_dec_alt_run ar hFp hz hm (hPE s hP).preG Al (Th.home s a _ hP h hn hh)
    rw [h2] at h'
    obtain rfl := Result.ok_injective h'
    exact hn
  · exact fun e => hh (Th.acc s s' a r' hP Al h' e)

/-- **`hra` from `SlThr`** and P0 totality: at an alternative of an entry state that does not
accept, the run reads only aligned words. -/
theorem sl_hra (hS : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {P : S → Prop} (hPE : ∀ s, P s → SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    {thr : S → U64} {TW : U64 → U64 → Prop}
    (Th : SlThr (st := st) ar (n := n) (found := found) (m0 := m0) P K Locks thr TW) :
    ∀ s s' a r, P s →
      Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      (¬ ∃ s1 a1, syscall.handle_syscall_local st ar s a n found = ok (true, s1, a1)) →
      syscall.handle_syscall_local st ar s' a n found = ok r →
      syscall.handle_syscall_local (guard st (fun b => Aligned b) (fun _ => True)) ar s' a n found = ok r := by
  intro s s' a r hP Al hna h
  have hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local m ar x a n found = interp m ar p x a :=
    fun m x a => congrFun (congrFun (hFp A ar m) x) a
  by_cases hh : L.mem s (affA (thr s)) = L.cpu s
  · obtain ⟨⟨b, s1, a1⟩, h0, -⟩ := spec_ex_fd (Fl4Proofs.P0.syscall.handle_syscall_local.p0 st ar s a n found hS hA)
    have hb : b ≠ true := fun e => hna ⟨s1, a1, by rw [h0, e]⟩
    obtain ⟨s1', hg, h2⟩ := sl_dec_alt_run ar hFp hz hm (hPE s hP).preG Al (Th.home s a _ hP h0 hb hh)
    rw [h2] at h
    obtain rfl := Result.ok_injective h
    rw [hp] at hg ⊢
    exact interp_mono (fun _ hq => hq.1) (fun _ _ => trivial) p hz s' a _ hg
  · have hg := Th.away s s' a r hP Al hh h
    rw [hp] at hg ⊢
    exact interp_mono (fun q hq => hq.elim (fun h1 => h1.1) (Th.twA _ q)) (fun _ _ => trivial) p hz s' a _ hg

/-- **`PathObl` of the syscall entry from `SlThr`** (`sl_pathObl` with `hna := sl_hna`). -/
theorem sl_pathObl_dr (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {P : S → Prop} (hPE : ∀ s, P s → SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    {thr : S → U64} {TW : U64 → U64 → Prop}
    (Th : SlThr (st := st) ar (n := n) (found := found) (m0 := m0) P K Locks thr TW) :
    PathObl st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathObl ar hA hK hU hFp hPE (sl_hna ar hFp hz hm hPE Th)

/-- **`PathSide` of the syscall entry from `SlThr`** (`sl_pathSide` with `hra := sl_hra`). -/
theorem sl_pathSide_dr (hS : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {P : S → Prop} (hPE : ∀ s, P s → SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    {thr : S → U64} {TW : U64 → U64 → Prop}
    (Th : SlThr (st := st) ar (n := n) (found := found) (m0 := m0) P K Locks thr TW)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s) :
    PathSide st (fun m s a => syscall.handle_syscall_local m ar s a n found)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathSide ar hA hK hU hFp hz hm hPE (sl_hra ar hS hA hFp hz hm hPE Th) huf

end

end Fl4Proofs.P2.PathObl

/-
# P2 (line stpost, generation 11): the frame-cap invocation local path `handle_invocation_local` as an `E2E.LocalPath`

`syscall.handle_invocation_local` (fl4-sync's `local_invocation`, with the plan `p` that `localinv.plan` computed
before the glue took `p`'s locks) assembled as an `E2E.LocalPath` value in the I/O port path's shape
(`P2/AccessIoLP.lean`): the **maximal** sets `RS = IoRS` (aligned kernel words this core may read by `own`),
`WS = IoWS` (words it may write), `DS = IoDS` (`FAULT_IP`, `CUR_TIME`, `CONSUMED`: a declined run writes only the
prefix, exactly as the I/O port path's; `handle_invocation_local` declines before or after the same prefix,
`still_holds` included, Rust `syscall.rs` l.448–492).

## Scope (findings, generation 11)
Which arms fit the current framework, from the extracted text (`crates/fl4-core/src/cnode.rs`, `localinv.rs`,
`msg.rs`) against `OwnMap.own` (P2/OwnMap.lean rules 1–6) and `IoRS`:
* **CNodeDelete of a small RAM frame whose plan holds no page-table entry** (`p.n ≤ p.pte`): reads the caller's
  registers (args 0, 1: `msg::syscall_arg` below `N_MSG_REGISTERS = 4`), the CSpace walk (CNode cap words: gate's,
  `RPerm` by `GateOnly`), the locked slot and its CDT neighbours (rule 2: `lock <slot>`), this core's node / SC /
  caller TCB; writes the locked slots' cap / link words (Null / Frame kept: rule 2) and the caller. Fits `IoRS` /
  `IoWS` as is. **This is the arm set the canonical `InvArm` admits.**
* **CNodeCopy / CNodeMint** do **not** fit `IoRS`: `cnode::copied_cap` reads `rights` as argument 4 (Mint also the
  badge, argument 5), i.e. `msg::buf_get` of the caller's IPC buffer (`syscall_arg`, `i ≥ N_MSG_REGISTERS`), a
  **user word**, whenever the buffer is set. `IoRS` holds no user word, so `acc` on `guard st IoRS IoWS` is false
  for them; they need a read set `IoRS ∪ {the two buffer words}` and a `ReadOnce` argument for an accepted run
  reading a user word (the generic `once_of_guardG` needs `RS` user-free). Framework decision, not done here.
* **X86PageMap**, and **CNodeDelete with a page-table entry**, write a PTE; `OwnMap.region` has no page-table
  region, so a PTE is `.none`, i.e. **gate-owned** (rule 6): `write_own` / `acc` are false for these runs under the
  current `own`. They need an ownership rule for the planned PTE (`lock <pte>`, as `plan` locks it) in `OwnMap.own`
  (and its `MoveHeld` / `OwnDep` proofs). Lead decision.

## What is proved here
* `inv_total` (P0), `inv_pathObl` (`read_own`, `write_own`, `aligned` proved; `acc`, `dec_alt`, `move` from the
  named premises), `inv_pathSide` (`rs_aligned`, `ko_aligned` proved; `read_aligned` of accepting entries from
  `acc` + `IsProgOn` + `NoZero` by `interp_agree`, declining ones the premise `hra`; `user_free` the premise `huf`),
  `inv_readOnce` (accepting entries from `acc` by `once_of_guardG`; declining ones `hro`), **`inv_localPath`**.
* `InvArm`, `InvPlanD` (`plan_with` on the plan's slot; `planD_of_plan` derives it from `loc_chain_all` clause
  8's input `hp`; `localinv.plan` itself reads the IPC buffer, a user word, so it cannot sit in `Pre`), `InvQ` (the
  canonical `Q`: `IoQ` + `InvPlanD` + the arm + the plan's locks held), `invQ_intro`, **`inv_pathsK`** (`E2E.Paths` member at `Pre := SlJAt K ∧ InvQ …`),
  **`inv_pathsK_startAt`** (at a chain state: `SlJAt` from clause 7, the plan from clause 8's input).

## Named premises (exact statements: the `Inv*W` definitions below)
* [W] `hacc : InvAccW` — an accepted run on `guard st (IoRS s) (IoWS s)` ends as the real one;
* [W] `hdec : InvDecW` — `PathObl.dec_alt` (a run declining at `s` declines at every alternative, writing `IoDS s`
  only, every write `StepOK`);
* [W] `hmv : InvMoveW` — `PathObl.move` of accepted runs;
* [W] `hra : InvRaW` — `PathSide.read_aligned` of declining entries;
* [P] `hp` (`IsProgOn` of the body), [W] `hz` (`NoZero`), [W] `hro : InvRoW` (`ReadOnce` at declining entries).
  `hpz` cannot be the I/O port's generated form as is: the unpruned body calls all of `decode_invocation`, whose
  closure has `zero` / `clear_free` (retype), so `NoZero` of its tree is false (`handoff/hpz.md`); a pruned body
  (decode cut to the CNode Delete arm, as `P2/IoPrune.lean`) and `xtask/scripts/gen_prog.py` on it are needed;
* [J] `hK` (`RegionOK`), `hU` (`UserOK`), [P] `hm` (`MasksWr`),
  [J] `huf` (`PathSide.user_free`), `hPE` (`Pre` gives `IoPre`).

No statement of an existing declaration changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.SlJStLocStart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-- The frame-cap invocation body as `E2E.LocalPath.F` (syscall number `number`, plan `p`). -/
abbrev invBody (S : Type) (number : I64) (p : localinv.Plan) : ∀ {A : Type}, machine.Arch A → machine.Store S → S →
    A → Result (Bool × S × A) :=
  fun ar m s a => syscall.handle_invocation_local m ar s a number p

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A} {number : I64} {p : localinv.Plan}

/-- [W] **`acc`** of the frame-cap invocation path: an accepted run on the store guarded to `IoRS s` / `IoWS s`
ends as the real one. -/
def InvAccW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop)
    (P : S → Prop) : Prop :=
  ∀ s a s1 a1, P s → syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) →
    syscall.handle_invocation_local (guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) ar s a
      number p = ok (true, s1, a1)

/-- [W] **`move`** of accepted runs: every write passes `StepOK`. -/
def InvMoveW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop)
    (m0 : U64 → U64) (P : S → Prop) : Prop :=
  ∀ s a s1 a1, P s → syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) →
    syscall.handle_invocation_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
      (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s a number p = ok (true, s1, a1)

/-- [W] **`dec_alt`**: a run declining at `s` declines at every alternative, writing only `IoDS s`, every write
`StepOK`. -/
def InvDecW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop)
    (m0 : U64 → U64) (P : S → Prop) : Prop :=
  ∀ s a (r : Bool × S × A), P s → syscall.handle_invocation_local st ar s a number p = ok r → r.1 ≠ true →
    ∀ s' (r' : Bool × S × A), Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      syscall.handle_invocation_local st ar s' a number p = ok r' →
      r'.1 ≠ true ∧
        syscall.handle_invocation_local (guard st (fun _ => True) (IoDS (st := st) s)) ar s' a number p = ok r' ∧
        syscall.handle_invocation_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
          (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s' a number p = ok r'

/-- [W] **`read_aligned` of declining entries**: at every alternative of an entry that declines, the run reads
only aligned words. -/
def InvRaW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop)
    (m0 : U64 → U64) (P : S → Prop) : Prop :=
  ∀ s s' a (r0 r : Bool × S × A), P s →
    Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
    syscall.handle_invocation_local st ar s a number p = ok r0 → r0.1 ≠ true →
    syscall.handle_invocation_local st ar s' a number p = ok r →
    syscall.handle_invocation_local (guard st (fun b => Aligned b) (fun _ => True)) ar s' a number p = ok r

/-- [W] **`ReadOnce` at declining entries**, of the tree `q`. -/
def InvRoW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop)
    (m0 : U64 → U64) (q : SProg Bool) (P : S → Prop) : Prop :=
  ∀ s s' a r, P s → (¬ ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)) →
    Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
    interp st ar q s' a = ok r → Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ q s' a

/-- P0's totality of the body. -/
theorem inv_total (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan) (s : S) (a : A) :
    ∃ r, syscall.handle_invocation_local st ar s a number p = ok r := by
  obtain ⟨r, e, -⟩ := spec_ex_fd (P0.syscall.handle_invocation_local.p0 st ar s a number p L.total hA)
  exact ⟨r, e⟩

/-- `IsProgOn` of the body, beta-reduced (for `rw`). -/
theorem inv_hp {G : S → Prop} {q : SProg Bool}
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st G q)
    {m : machine.Store S} (N : Narrow st m) {s : S} (hG : G s) (a : A) :
    syscall.handle_invocation_local m ar s a number p = interp m ar q s a := hp m N s hG a

/-- **`PathObl` of the frame-cap invocation path** (module docstring): `read_own`, `write_own`, `aligned` proved;
`acc`, `dec_alt`, `move` from `hacc`, `hdec`, `hmv` [W]. -/
theorem inv_pathObl {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : InvAccW st ar number p K Locks P) (hdec : InvDecW st ar number p K Locks m0 P)
    (hmv : InvMoveW st ar number p K Locks m0 P) :
    PathObl st (fun m s a => syscall.handle_invocation_local m ar s a number p) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact hacc s a s1 a1 hE h
  · intro s a r hE h hn s' r' Al h'
    exact hdec s a r hE h hn s' r' Al h'
  · intro s x _ hx _; exact hx.2.2
  · intro s x hE hx _
    rcases hx with hx | hx
    · exact hx.2
    · rcases hx with rfl | rfl | rfl
      · exact ((hPE s hE).reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).2.2
      · exact ((hPE s hE).nd (Locks := Locks) _ (by simp [layout.node.CUR_TIME])
          (by simp [layout.node.CUR_TIME])).2.2
      · exact ((hPE s hE).nd (Locks := Locks) _ (by simp [layout.node.CONSUMED])
          (by simp [layout.node.CONSUMED])).2.2
  · intro s x hE hx
    rcases hx with hx | hx
    · exact hx.1
    · exact (IoDS.safe (hPE s hE) hx).1
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (hdec s a _ hE h Bool.false_ne_true s _ (Alt.refl s) h).2.2
    · exact hmv s a s1 a1 hE h

/-- **`PathSide` of the frame-cap invocation path** (module docstring). -/
theorem inv_pathSide (hK : RegionOK K) (hU : E2E.UserOK K) {P : S → Prop} {q : SProg Bool}
    (hacc : InvAccW st ar number p K Locks P)
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q) (hz : NoZero q)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hra : InvRaW st ar number p K Locks m0 P) (hA : P0.ArchTotal ar)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    PathSide st (fun m s a => syscall.handle_invocation_local m ar s a number p)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, fun s x _ hx => hx.1, fun x hx => Fl4Proofs.P2.ko_aligned hK hU x hx, huf⟩
  · intro s s' a r hE Al h
    by_cases hac : ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)
    · obtain ⟨s1, a1, h0⟩ := hac
      have hg := hacc s a s1 a1 hE h0
      rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
      obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) q hz s s' a true s1 a1
        Al.ksb Al.cpu Al.masks Al.read hg
      have hs := interp_to (st := st) (st' := st) (fun _ _ _ => rfl)
        (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
        rfl rfl rfl q hz s' a _ hg'
      show syscall.handle_invocation_local _ ar s' a number p = ok r
      rw [inv_hp hp (Narrow.self st) ⟨s, hE, Al⟩ a] at h
      rw [inv_hp hp (Narrow.guard _ _ _) ⟨s, hE, Al⟩ a]
      rw [hs] at h
      rw [← h]
      exact interp_mono (fun _ hw => hw.1) (fun _ _ => trivial) q hz s' a _ hg'
    · obtain ⟨r0, h0⟩ := inv_total (st := st) hA number p s a
      have hr0 : r0.1 ≠ true := by
        obtain ⟨b, z, c⟩ := r0
        intro e
        change b = true at e
        subst e
        exact hac ⟨z, c, h0⟩
      exact hra s s' a r0 r hE Al h0 hr0 h

/-- **`ReadOnce` of the frame-cap invocation path** (accepting entries proved, declining ones `hro` [W]). -/
theorem inv_readOnce {P : S → Prop} {q : SProg Bool} (hacc : InvAccW st ar number p K Locks P)
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q) (hz : NoZero q)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hro : InvRoW st ar number p K Locks m0 q P) :
    ReadOnce st ar q (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) P (IoRS (st := st) K Locks) := by
  intro s s' a r hE Al h
  by_cases hac : ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)
  · obtain ⟨s1, a1, h0⟩ := hac
    have hg := hacc s a s1 a1 hE h0
    rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) q hz s s' a true s1 a1
      Al.ksb Al.cpu Al.masks Al.read hg
    exact once_of_guardG (fun w hw => hw.2.1) q hz ∅ ∅ s' a _ hg'
  · exact hro s s' a r hE hac Al h

/-- **The frame-cap invocation local path** (module docstring), for any `Pre` `P` giving `IoPre`. Premises:
`hA`, `hK` [J], `hU` [J], `hm` [P], `hPE`, `hacc` [W], `hdec` [W], `hmv` [W], `hra` [W], `huf` [J],
and the program premise `hpz` (`IsProgOn` [P], `NoZero` [W], `hro` [W]). -/
noncomputable def inv_localPath (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hU : E2E.UserOK K) (number : I64) (p : localinv.Plan) (hm : E2E.MasksWr st)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : InvAccW st ar number p K Locks P) (hdec : InvDecW st ar number p K Locks m0 P)
    (hmv : InvMoveW st ar number p K Locks m0 P) (hra : InvRaW st ar number p K Locks m0 P)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m0 q P) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := invBody S number p
  p := hpz.choose
  Acc := fun b => b = true
  Locks := Locks
  Pre := P
  RS := IoRS (st := st) K Locks
  WS := IoWS (st := st) K Locks
  DS := IoDS (st := st)
  isProg := hpz.choose_spec.1
  obl := inv_pathObl hPE hacc hdec hmv
  side := inv_pathSide hK hU hacc hpz.choose_spec.1 hpz.choose_spec.2.1 hm hra hA huf
  once := inv_readOnce hacc hpz.choose_spec.1 hpz.choose_spec.2.1 hm hpz.choose_spec.2.2
  total := fun s a => inv_total hA number p s a
  masks := hm

end

/-! ## The canonical `Q` and the path at chain states -/

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

variable (st) in
/-- **The arm set of this path** (module docstring, scope): the current thread's label is `CNodeDelete` and the
plan holds no page-table entry (`p.n ≤ p.pte`; `plan_with`'s `add_pte` sets `pte := n` before adding the entry).
Copy / Mint (a user-word read) and X86PageMap / Delete with a PTE (a gate-owned PTE write) are outside it. -/
def InvArm (p : localinv.Plan) (s : S) : Prop :=
  ∀ t info, sched.cur_thread st s = ok t → msg.msg_info st s t = ok info →
    info.label = fl4_abi.label.CNodeDelete ∧ p.n.val ≤ p.pte.val

variable (st) in
/-- **The plan, user-write-independently**: `plan_with` of the current thread's label on the plan's slot gives
`p`, for some extra caps. (`localinv.plan` itself reads the caller's IPC buffer through `lookup_extra_caps`, a
user word, so it is not stable under user writes and cannot sit in `Pre` (`PathSide.user_free`); the Delete arm of
`plan_with` does not read the extra caps.) From clause 8's `hp` by `planD_of_plan`. -/
def InvPlanD (p : localinv.Plan) (s : S) : Prop :=
  ∃ t info ex, sched.cur_thread st s = ok t ∧ msg.msg_info st s t = ok info ∧
    localinv.plan_with st s t info.label p.slot ex = ok (some p)

/-- **`InvPlanD` from the plan at the entry** (`loc_chain_all` clause 8's input `hp`). -/
theorem planD_of_plan {s : S} {n : I64} {p : localinv.Plan} (h : localinv.plan st s n = ok (some p)) :
    InvPlanD st p s := by
  unfold localinv.plan at h
  split at h
  · simp at h
  obtain ⟨t, et, h⟩ := Fl4Proofs.P1.bind_eq_ok h
  obtain ⟨info, ei, h⟩ := Fl4Proofs.P1.bind_eq_ok h
  obtain ⟨b, -, h⟩ := Fl4Proofs.P1.bind_eq_ok h
  split at h
  swap
  · simp at h
  obtain ⟨cptr, -, h⟩ := Fl4Proofs.P1.bind_eq_ok h
  obtain ⟨r, -, h⟩ := Fl4Proofs.P1.bind_eq_ok h
  cases r with
  | Err _ => simp at h
  | Ok r1 =>
    try simp only at h
    obtain ⟨buf, -, h⟩ := Fl4Proofs.P1.bind_eq_ok h
    obtain ⟨r2, -, h⟩ := Fl4Proofs.P1.bind_eq_ok h
    cases r2 with
    | Err _ => simp at h
    | Ok e =>
      try simp only at h
      obtain ⟨h1, -⟩ := plan_with_kp h
      refine ⟨t, info, e, et, ei, ?_⟩
      rw [h1]; exact h

variable (st) in
/-- **The canonical `Q` of the frame-cap invocation path**: the I/O port's entry facts (`IoQ`), the plan
(`InvPlanD`, from `loc_chain_all` clause 8's input `hp`), the arm (`InvArm`), and the plan's locks held by the
glue. -/
def InvQ (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayout)
    (m : U64 → U64) (s : S) : Prop :=
  IoQ st Cs Ω Sg Ac K m s ∧ InvPlanD st p s ∧ InvArm st p s ∧
    ∀ (i : Nat) (x : U64), i < p.n.val → p.locks.val[i]? = some x → Locks s x

/-- (stpost gen 11) **The frame-cap invocation local path as an `E2E.Paths` member**: `inv_localPath` at every
layout `K` and memory `m`, `Pre := SlJAt K ∧ Q K m`. The `[W]` / `[J]` / `[P]`
premises of `inv_localPath` are taken for every `K m` at that `Pre`. -/
noncomputable def inv_pathsK (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hacc : ∀ K m, InvAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hdec : ∀ K m, InvDecW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hmv : ∀ K m, InvMoveW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hra : ∀ K m, InvRaW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∀ K m, ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (fun s => SlJAt (L := L) K s ∧ Q K m s) (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m)
        (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ Q K m s)) :
    E2E.Paths Unit :=
  fun _ K m hK hU =>
    inv_localPath (K := K) (m0 := m) (Locks := Locks) ar hA hK hU number p hm
      (P := fun s => SlJAt (L := L) K s ∧ Q K m s) (fun s h => hPE K m s h.1 h.2)
      (hacc K m) (hdec K m) (hmv K m) (hra K m) (fun s b v h => huf K m s b v h.1 h.2) (hpz K m)

/-- (stpost gen 11) **`StartAt` of `inv_pathsK` at a chain state** `σ` (`hR : Rc σ a3 τ`): the `SlJAt K` conjunct of
`Pre` is the chain's layout clause `h7` (`loc_chain_all` clause 7); `hq` is `Q K m σ` (for `Q := InvQ …`, built by
`invQ_intro` from the entry facts and clause 8's input `hp`). -/
theorem inv_pathsK_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hacc : ∀ K m, InvAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hdec : ∀ K m, InvDecW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hmv : ∀ K m, InvMoveW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (hra : ∀ K m, InvRaW st ar number p K Locks m (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∀ K m, ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (fun s => SlJAt (L := L) K s ∧ Q K m s) (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m)
        (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ Q K m s))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {A3 : Type} {Rc : S → A3 → Fl4Spec.State Unit → Prop}
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), Rc σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : Rc σ a3 τ) (a : A) (hq : Q K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (inv_pathsK ar hA number p hm Q hPE hacc hdec hmv hra huf hpz () K m hK hU) c hs μ
      ((inv_pathsK ar hA number p hm Q hPE hacc hdec hmv hra huf hpz () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨h7 σ a3 τ hR, hq⟩, hc, hl, hμ, rfl⟩

/-- (stpost gen 11) **`InvQ` at an entry state** from its pieces: `IoPre`, the affinity words of `m`, the plan at
the entry (`loc_chain_all` clause 8's input `hp`), the arm, and the plan's locks held. -/
theorem invQ_intro {number : I64} {p : localinv.Plan} {K : KLayout} {m : U64 → U64} {s : S}
    (hP : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hmA : ∀ d, K.heap d = some .tcb → m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hp : localinv.plan st s number = ok (some p)) (harm : InvArm st p s)
    (hlk : ∀ (i : Nat) (x : U64), i < p.n.val → p.locks.val[i]? = some x → Locks s x) :
    InvQ st Cs Ω Sg Ac Locks p K m s :=
  ⟨⟨hP, hmA⟩, planD_of_plan hp, harm, hlk⟩

end paths


/-! ## `still_holds` on another store (a first `acc` / `dec_alt` building block) -/

section sh
variable {S : Type}

/-- The words `still_holds` reads: the recorded addresses of the plan's seen array (index below `nseen` and
`MAX_LOCKS`). -/
def SeenW (p : localinv.Plan) (x : U64) : Prop :=
  ∃ (i : Usize) (q : U64 × U64), i < p.nseen ∧ i < localinv.MAX_LOCKS ∧
    Array.index_usize p.seen i = ok q ∧ q.1 = x

/-- (stpost gen 11) **`still_holds` answers alike on two stores reading the seen words alike.** -/
theorem still_holds_congr {st m : machine.Store S} (p : localinv.Plan) (s : S)
    (h : ∀ x, SeenW p x → m.read s x = st.read s x) :
    localinv.Plan.still_holds m p s = localinv.Plan.still_holds st p s := by
  have hb : (fun i1 => localinv.Plan.still_holds_loop.body m p s i1) =
      (fun i1 => localinv.Plan.still_holds_loop.body st p s i1) := by
    funext i
    unfold localinv.Plan.still_holds_loop.body
    by_cases h1 : i < p.nseen
    · by_cases h2 : i < localinv.MAX_LOCKS
      · have hM : localinv.MAX_LOCKS.val = 4 := by unfold localinv.MAX_LOCKS; rfl
        have h2v : i.val < localinv.MAX_LOCKS.val := h2
        have hl : i.val < p.seen.val.length := by rw [p.seen.property]; simp only [hM] at h2v; simpa using h2v
        obtain ⟨⟨a0, v0⟩, hq, -⟩ := spec_ex_fd (Aeneas.Std.Array.index_usize_spec p.seen i hl)
        simp only [h1, h2, if_true, hq, bind_ok, bind_tc_ok]
        try simp only [uncurry_apply_pair]
        try dsimp only
        rw [h a0 ⟨i, (a0, v0), h1, h2, hq, rfl⟩]
      · simp only [h1, h2, if_true, if_false]
    · simp only [h1, if_false]
  unfold localinv.Plan.still_holds localinv.Plan.still_holds_loop
  rw [hb]

/-- (stpost gen 11) **`still_holds` on a guarded store** whose read set holds the seen words. -/
theorem still_holds_guard {st : machine.Store S} {R W : U64 → Prop} (p : localinv.Plan) (s : S)
    (hR : ∀ x, SeenW p x → R x) :
    localinv.Plan.still_holds (guard st R W) p s = localinv.Plan.still_holds st p s :=
  still_holds_congr p s fun x hx => guard_read (hR x hx)

end sh

end Fl4Proofs.P2.PathObl

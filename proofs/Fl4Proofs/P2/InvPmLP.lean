/-
# P2 (line pte, generation 10): the PageMap invocation local path under rule 8 (`ownP`)

`syscall.handle_invocation_local` on the PageMap arm (`X86PageMap` of a small RAM frame cap; the plan locks the
slot and the leaf entry `e`, `plan_with_mapF`) as an `E2E.LocalPath (ownP K)`, in the shape of the CNode-Delete
path `inv_localPath` (`P2/InvLP.lean`), with the sets taken **maximal for `ownP`**:

* `PmRS K Locks s`: aligned non-user words this core may read under `ownP K` (gate-only words, held words; so the
  locked leaf entry `e` when `e ∈ K.ptes` (`rpermP_pte`), and no unlocked PTE word (`not_rpermP_pte`));
* `PmWS K Locks s`: aligned words it may write under `ownP K` (held words: the locked slot, the caller's words, and
  the locked leaf entry, `wpermP_pte`);
* `DS := IoDS` (a declined run writes only the I/O-port prefix: `FAULT_IP`, `CUR_TIME`, `CONSUMED`).

So `read_own`, `write_own` of accepted runs and `rs_aligned` hold by definition; the declined writes are `ownP`
writes by `wpermP_of_V` / `wpermV_of_own'` (no new premise). The walk words the decode reads (ASID table / pool,
PML4 / PDPT / PD entries) are gate words (`GateW`, `P2/E2EPJEp.lean`), in `PmRS` by `rpermP_gate`
(`P2/PteLockRS.lean`) — that is the content of `acc` [W] below, not an extra premise.

**Modelling gap (documented, not a premise)**: `write_mapping`'s TLB invalidation (`Arch.invalidate_page`,
`Arch.invalidate_asid`; x86: a remote shootdown) returns only an `Arch` value in the extracted interface, so in the
model it changes no store word, as the remote stall (`P2/InvStall.lean`). The hardware walkers' A/D-bit updates of
the PTE are outside the model as before rule 8 (`P2/E2EP.lean`).

* `PmAccW`, `PmDecW`, `PmMoveW`, `PmRaW`, `PmRoW` [W]: the run-level obligations (`acc`, `dec_alt`, `move`,
  `read_aligned` of declining entries, `ReadOnce` of declining entries) at these sets, stated as `InvLP`'s;
* `pm_pathObl`, `pm_pathSide`, `pm_readOnce`, **`pm_localPath`** (for any `Pre` giving `IoPre`);
* `PmArm` (label `X86PageMap`, message length ≥ 3: with fewer words the decode's error reply writes the caller's
  IPC buffer, a user word, as Delete's `InvLen` finding), `PmQ` (the canonical entry facts: `IoQ`, the plan
  `InvPlanD`, `PmArm`, the plan's locks held), `GateEp` (the epoch data: the PTE set is the reachability convention
  of a memory `m1` that agrees with `s` on the aligned non-user gate words), `gateEp_userWr` (it survives user
  writes), `gateAg_of_ep` (it gives `PteReach.GateAg`, the input of `ptesR_of_run`);
* **`pmPaths`**: the PageMap slot family `PathsP (I64 × localinv.Plan)` (syscall number, plan) at
  `Pre := SlJAt K ∧ PmQ ∧ GateEp`, every premise taken per layout.

Named premises (of `pmPaths`): [W] `hacc`, `hdec`, `hmv`, `hra`; [J] `huf` (user writes keep `SlJAt ∧ PmQ` and the locks:
`GateEp` is discharged here, `gateEp_userWr`), [P] `hm` (`MasksWr`), [J] `hpr` (`PmPrune`: the body is the pruned
`invBodyPmG` from the entries and their alternatives) and [W] `hro` (`PmRoW` of the tree). The program tree and
its `NoZero` are proved (`pm_isProg`, `pm_noZero`, `pm_hpz`: the tree `R.invBodyPmG` of `ProgGenPm*`). No existing statement changes.
-/
import Fl4Proofs.P2.E2EPW11R
import Fl4Proofs.P2.InvPmPlan
import Fl4Proofs.P2.ProgGenPmTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)

noncomputable section

section path
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutP}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A} {number : I64} {p : localinv.Plan}

variable (st) in
/-- What the PageMap path may read: aligned non-user words this core may read under `ownP K`. -/
def PmRS (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ x ∉ K.user ∧ RPerm (ownP K) (L.cpu s) (Locks s) (L.mem s) x

variable (st) in
/-- What an accepted PageMap run may write: aligned words it may write under `ownP K`. -/
def PmWS (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ WPerm (ownP K) (L.cpu s) (Locks s) (L.mem s) x

variable (st) in
/-- [W] **`acc`** of the PageMap path: an accepted run on the store guarded to `PmRS s` / `PmWS s` ends as the real
one. -/
def PmAccW {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayoutP)
    (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s a s1 a1, P s → syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) →
    syscall.handle_invocation_local (guard st (PmRS st K Locks s) (PmWS st K Locks s)) ar s a number p =
      ok (true, s1, a1)

variable (st) in
/-- [W] **`move`** of accepted PageMap runs: every write passes `StepOK` for `ownP K`. -/
def PmMoveW {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayoutP)
    (Locks : S → U64 → Prop) (m0 : U64 → U64) (P : S → Prop) : Prop :=
  ∀ s a s1 a1, P s → syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) →
    syscall.handle_invocation_local (mguard st (fun x y => StepOK (ownP K) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout m0) (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s a number p =
      ok (true, s1, a1)

variable (st) in
/-- [W] **`dec_alt`** of the PageMap path. -/
def PmDecW {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayoutP)
    (Locks : S → U64 → Prop) (m0 : U64 → U64) (P : S → Prop) : Prop :=
  ∀ s a (r : Bool × S × A), P s → syscall.handle_invocation_local st ar s a number p = ok r → r.1 ≠ true →
    ∀ s' (r' : Bool × S × A), Alt st (PmRS st K Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0)
      (· ∈ K.user) s s' →
      syscall.handle_invocation_local st ar s' a number p = ok r' →
      r'.1 ≠ true ∧
        syscall.handle_invocation_local (guard st (fun _ => True) (IoDS (st := st) s)) ar s' a number p = ok r' ∧
        syscall.handle_invocation_local (mguard st (fun x y => StepOK (ownP K) (OwnMap.cls K.toKLayout)
          (OwnMap.ko K.toKLayout m0) (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s' a number p = ok r'

variable (st) in
/-- [W] **`read_aligned` of declining PageMap entries**. -/
def PmRaW {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayoutP)
    (Locks : S → U64 → Prop) (m0 : U64 → U64) (P : S → Prop) : Prop :=
  ∀ s s' a (r0 r : Bool × S × A), P s →
    Alt st (PmRS st K Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) s s' →
    syscall.handle_invocation_local st ar s a number p = ok r0 → r0.1 ≠ true →
    syscall.handle_invocation_local st ar s' a number p = ok r →
    syscall.handle_invocation_local (guard st (fun b => Aligned b) (fun _ => True)) ar s' a number p = ok r

variable (st) in
/-- [W] **`ReadOnce` at declining PageMap entries**, of the tree `q`. -/
def PmRoW {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayoutP)
    (Locks : S → U64 → Prop) (m0 : U64 → U64) (q : SProg Bool) (P : S → Prop) : Prop :=
  ∀ s s' a r, P s → (¬ ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)) →
    Alt st (PmRS st K Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) s s' →
    interp st ar q s' a = ok r → Once st ar (PmRS st K Locks s) (· ∈ K.user) ∅ ∅ q s' a

/-- **`PathObl` of the PageMap path**: `read_own`, `write_own`, `aligned` proved; `acc`, `dec_alt`, `move` from
`hacc`, `hdec`, `hmv` [W]. -/
theorem pm_pathObl (hK : RegionOKP K) {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K.toKLayout T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : PmAccW st ar number p K Locks P) (hdec : PmDecW st ar number p K Locks m0 P)
    (hmv : PmMoveW st ar number p K Locks m0 P) :
    PathObl st (fun m s a => syscall.handle_invocation_local m ar s a number p) (fun b => b = true)
      (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) Locks P
      (PmRS st K Locks) (PmWS st K Locks) (IoDS (st := st)) := by
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
    · refine wpermP_of_V hK (wpermV_of_own' hK.base ?_)
      rcases hx with rfl | rfl | rfl
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

/-- **`PathSide` of the PageMap path** (as `inv_pathSide`). -/
theorem pm_pathSide (hK : RegionOKP K) (hU : UserOKP K) {P : S → Prop} {q : SProg Bool}
    (hacc : PmAccW st ar number p K Locks P)
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (PmRS st K Locks) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user)) q)
    (hz : NoZero q) (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hra : PmRaW st ar number p K Locks m0 P) (hA : P0.ArchTotal ar)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        PmRS st K Locks (L.wr s b v) = PmRS st K Locks s ∧
        PmWS st K Locks (L.wr s b v) = PmWS st K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    PathSide st (fun m s a => syscall.handle_invocation_local m ar s a number p)
      (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) Locks P
      (PmRS st K Locks) (PmWS st K Locks) (IoDS (st := st)) := by
  refine ⟨?_, fun s x _ hx => hx.1,
    fun x hx => Fl4Proofs.P2.ko_aligned hK.base.base hU.base.base x hx, huf⟩
  intro s s' a r hE Al h
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

/-- **`ReadOnce` of the PageMap path** (accepting entries proved, declining ones `hro` [W]). -/
theorem pm_readOnce {P : S → Prop} {q : SProg Bool} (hacc : PmAccW st ar number p K Locks P)
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (PmRS st K Locks) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user)) q)
    (hz : NoZero q) (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hro : PmRoW st ar number p K Locks m0 q P) :
    ReadOnce st ar q (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P (PmRS st K Locks) := by
  intro s s' a r hE Al h
  by_cases hac : ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)
  · obtain ⟨s1, a1, h0⟩ := hac
    have hg := hacc s a s1 a1 hE h0
    rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) q hz s s' a true s1 a1
      Al.ksb Al.cpu Al.masks Al.read hg
    exact once_of_guardG (fun w hw => hw.2.1) q hz ∅ ∅ s' a _ hg'
  · exact hro s s' a r hE hac Al h

/-- **The PageMap invocation local path under `ownP`** (module docstring), for any `Pre` `P` giving `IoPre`. -/
def pm_localPath (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOKP K) (hU : UserOKP K)
    (number : I64) (p : localinv.Plan) (hm : E2E.MasksWr st)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K.toKLayout T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : PmAccW st ar number p K Locks P) (hdec : PmDecW st ar number p K Locks m0 P)
    (hmv : PmMoveW st ar number p K Locks m0 P) (hra : PmRaW st ar number p K Locks m0 P)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        PmRS st K Locks (L.wr s b v) = PmRS st K Locks s ∧
        PmWS st K Locks (L.wr s b v) = PmWS st K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (PmRS st K Locks) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user)) q ∧
      NoZero q ∧ PmRoW st ar number p K Locks m0 q P) :
    E2E.LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) where
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
  RS := PmRS st K Locks
  WS := PmWS st K Locks
  DS := IoDS (st := st)
  isProg := hpz.choose_spec.1
  obl := pm_pathObl hK hPE hacc hdec hmv
  side := pm_pathSide hK hU hacc hpz.choose_spec.1 hpz.choose_spec.2.1 hm hra hA huf
  once := pm_readOnce hacc hpz.choose_spec.1 hpz.choose_spec.2.1 hm hpz.choose_spec.2.2
  total := fun s a => inv_total hA number p s a
  masks := hm

/-- **`IsProg` for the pruned PageMap body**: it is the generated tree `R.invBodyPmG` (`ProgGenPm*`). -/
theorem pm_isProg (S : Type) (number : I64) (p : localinv.Plan) :
    IsProg (invBodyPmP S number p) (R.invBodyPmG number p) := by
  intro A ar st
  funext s a
  show invBodyPmG st ar s a number p = _
  rw [R.invBodyPmG_eq st ar, bind_proj3]

theorem pm_noZero (number : I64) (p : localinv.Plan) : NoZero (R.invBodyPmG number p) :=
  R.invBodyPmG_nz number p

variable (st) in
/-- [J] **The PageMap body is the pruned one** on the stores narrowing `st`, from the entry states and their
alternatives (the cap at `p.slot` read after the prefix is the entry's Frame cap, the label `X86PageMap`: as
`InvPrune.inv_prune` for the CNode arm). -/
def PmPrune {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayoutP)
    (Locks : S → U64 → Prop) (m0 : U64 → U64) (P : S → Prop) : Prop :=
  ∀ (m : machine.Store S), Narrow st m → ∀ s',
    AltOf st P (PmRS st K Locks) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) s' →
    ∀ a, syscall.handle_invocation_local m ar s' a number p = invBodyPmG m ar s' a number p

/-- **The program premise of `pm_localPath`** for the tree `R.invBodyPmG` (tree and `NoZero` proved), from
[J] `hpr` and [W] `hro`. -/
theorem pm_hpz {P : S → Prop} (hpr : PmPrune st ar number p K Locks m0 P)
    (hro : PmRoW st ar number p K Locks m0 (R.invBodyPmG number p) P) :
    ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (PmRS st K Locks) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user)) q ∧
      NoZero q ∧ PmRoW st ar number p K Locks m0 q P :=
  ⟨R.invBodyPmG number p, fun m N s' hG a => (hpr m N s' hG a).trans
      (congrFun (congrFun (pm_isProg S number p A ar m) s') a),
    pm_noZero number p, hro⟩

end path

/-! ## The entry facts, the epoch data, the slot family -/

section fam
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

variable (st) in
/-- **The PageMap arm**: the current thread's label is `X86PageMap` and the message has at least three words
(`vaddr`, rights, attributes: all three message registers). -/
def PmArm (s : S) : Prop :=
  ∀ t info, sched.cur_thread st s = ok t → msg.msg_info st s t = ok info →
    info.label = fl4_abi.label.X86PageMap ∧ ¬ info.length < 3#u64

variable (st) in
/-- **The canonical entry facts of the PageMap path**: the I/O port's (`IoQ`), the plan (`InvPlanD`), the arm,
and the plan's locks (slot and leaf entry) held by the glue. -/
def PmQ (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayoutP) (m : U64 → U64)
    (s : S) : Prop :=
  IoQ st Cs Ω Sg Ac K.toKLayout m s ∧ InvPlanD st p s ∧ PmArm st s ∧
    ∀ (i : Nat) (x : U64), i < p.n.val → p.locks.val[i]? = some x → Locks s x

variable (st) in
/-- **The epoch data at a start state**: no VCPU, the PTE set is the reachability convention of a memory `m1`,
and `s` agrees with `m1` on the aligned non-user gate words. -/
def GateEp (K : KLayoutP) (s : S) : Prop :=
  ∃ m1 : U64 → U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K m1) ∧
    ∀ x, GateW K x → Aligned x → x ∉ K.user → L.mem s x = m1 x

/-- `GateEp` survives a write of an aligned user word. -/
theorem gateEp_userWr {K : KLayoutP} {s : S} (h : GateEp st K s) {b v : U64} (hb : b ∈ K.user)
    (ha : Aligned b) : GateEp st K (L.wr s b v) := by
  obtain ⟨m1, hc, hg⟩ := h
  refine ⟨m1, hc, fun x hx hxa hxu => ?_⟩
  have hne : ¬ b = x := fun e => hxu (by rw [← e]; exact hb)
  rw [L.mem_wr s b v x ha hxa, if_neg hne]
  exact hg x hx hxa hxu

/-- **`GateEp` gives `GateAg`** (the input of `ptesR_of_run`), for the convention's memory. -/
theorem gateAg_of_ep {K : KLayoutP} {s : S} (h : GateEp st K s) :
    ∃ m1, (K.vcpus = ∅ ∧ K.ptes = ptesR K m1) ∧ GateAg st K m1 s := by
  obtain ⟨m1, ⟨nv, he⟩, hg⟩ := h
  refine ⟨m1, ⟨nv, he⟩, fun w hr hp hu ha => hg w (gateW_of_region hr (by rw [he]; exact hp) nv) ha hu⟩

/-- **The write leaf of a writing run is a PTE word of `K`** at a start state with the epoch data. -/
theorem pm_leaf_pte {K : KLayoutP} {s : S} (hJ : SlJAt (L := L) K.toKLayout s) (h : GateEp st K s)
    {asid r v e : U64} (hf : vspace.find_vspace_for_asid st s asid = ok (.Ok r))
    (hv : Fl4Proofs.P3.Vs.UserV v) (hl : vspace.lookup_pt_slot st s r v = ok (.Ok e)) : e ∈ K.ptes := by
  obtain ⟨m1, ⟨nv, he⟩, hag⟩ := gateAg_of_ep h
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', τ, B⟩ := hJ
  rw [he]
  exact ptesR_of_run B hag nv hf hv hl

/-- **The planned leaf is a locked PTE word the path may read and write**, at a `PmPre` state whose PML4 root is the
one `find_vspace_for_asid` names (what the decode's `check_vspace` establishes before `write_mapping`): the start
facts are consistent with the PTE write (satisfiability of the leaf half). `e ≠ 0` is the plan's lock condition
(`Plan.add` skips the null address). -/
theorem pm_leaf_locked {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP}
    {m : U64 → U64} {s : S} (hJ : SlJAt (L := L) K.toKLayout s) (hQ : PmQ st Cs Ω Sg Ac Locks p K m s)
    (hE : GateEp st K s) :
    ∃ (root rasid e : U64), (∃ x, Array.index_usize p.extra 0#usize = ok x ∧ x ≠ 0#u64 ∧
        obj.Slot.cap st x s = ok (.Pml4 root true rasid)) ∧
      ∀ asid, vspace.find_vspace_for_asid st s asid = ok (.Ok root) → e ≠ 0#u64 →
        e ∈ K.ptes ∧ Locks s e ∧ WPerm (ownP K) (L.cpu s) (Locks s) (L.mem s) e ∧
          PmRS st K Locks s e ∧ PmWS st K Locks s e := by
  obtain ⟨-, ⟨t, info, ex, ht, hi, hpl⟩, harm, hlk⟩ := hQ
  obtain ⟨hlb, -⟩ := harm t info ht hi
  rw [hlb] at hpl
  obtain ⟨fp, rt, asid0, va, root, rasid, mp, x, e, -, hx, hx0, hcx, hpe, -, hpte, -⟩ := plan_with_mapF hpl
  refine ⟨root, rasid, e, ⟨x, ?_, hx0, hcx⟩, fun asid hf he0 => ?_⟩
  · rw [(plan_with_kp hpl).2]; exact hx
  unfold localinv.page_entry at hpe
  by_cases hu : L.mem s (regA t layout.reg.R10) > fl4_abi.consts.USER_TOP
  · rw [if_pos hu] at hpe; simp at hpe
  rw [if_neg hu] at hpe
  unfold vspace.small_page_entry at hpe
  obtain ⟨r, hr, hpe⟩ := bind_eq_ok hpe
  have hl : vspace.lookup_pt_slot st s root (L.mem s (regA t layout.reg.R10)) = ok (.Ok e) := by
    cases r with
    | Ok y =>
      have : y = e := by simpa [core.result.Result.ok] using hpe
      rw [hr, this]
    | Err _ => simp [core.result.Result.ok] at hpe
  have hpt := pm_leaf_pte hJ hE hf (userV_of_not_gt hu) hl
  obtain ⟨hn, hle⟩ := hpte he0
  have hlk' := hlk _ e hn hle
  obtain ⟨m1, ⟨-, hpe1⟩, -⟩ := hE
  have hR : e ∈ ptesR K m1 := hpe1 ▸ hpt
  exact ⟨hpt, hlk', wpermP_pte hpt hlk', ⟨hR.2.2.2.1, hR.2.2.2.2.1, rpermP_pte hpt hlk'⟩,
    ⟨hR.2.2.2.1, wpermP_pte hpt hlk'⟩⟩

/-- The PageMap path's `Pre` at a layout. -/
def PmPre (st : machine.Store S) [L : LawfulStore st] (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop)
    (p : localinv.Plan) (K : KLayoutP) (m : U64 → U64) (s : S) : Prop :=
  SlJAt (L := L) K.toKLayout s ∧ PmQ st Cs Ω Sg Ac Locks p K m s ∧ GateEp st K s

/-- **The PageMap slot family** (module docstring): `pm_localPath` at every layout, indexed by the syscall number
and the plan, `Pre := PmPre`. -/
def pmPaths (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)
    (hacc : ∀ (j : I64 × localinv.Plan) K m, PmAccW st ar j.1 j.2 K Locks (PmPre st Cs Ω Sg Ac Locks j.2 K m))
    (hdec : ∀ (j : I64 × localinv.Plan) K m, PmDecW st ar j.1 j.2 K Locks m (PmPre st Cs Ω Sg Ac Locks j.2 K m))
    (hmv : ∀ (j : I64 × localinv.Plan) K m, PmMoveW st ar j.1 j.2 K Locks m (PmPre st Cs Ω Sg Ac Locks j.2 K m))
    (hra : ∀ (j : I64 × localinv.Plan) K m, PmRaW st ar j.1 j.2 K Locks m (PmPre st Cs Ω Sg Ac Locks j.2 K m))
    (huf : ∀ (j : I64 × localinv.Plan) (K : KLayoutP) m s b v, PmPre st Cs Ω Sg Ac Locks j.2 K m s →
      b ∈ K.user → Aligned b →
      (SlJAt (L := L) K.toKLayout (L.wr s b v) ∧ PmQ st Cs Ω Sg Ac Locks j.2 K m (L.wr s b v)) ∧
        Locks (L.wr s b v) = Locks s ∧
        PmRS st K Locks (L.wr s b v) = PmRS st K Locks s ∧
        PmWS st K Locks (L.wr s b v) = PmWS st K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpr : ∀ (j : I64 × localinv.Plan) K m, PmPrune st ar j.1 j.2 K Locks m (PmPre st Cs Ω Sg Ac Locks j.2 K m))
    (hro : ∀ (j : I64 × localinv.Plan) K m,
      PmRoW st ar j.1 j.2 K Locks m (R.invBodyPmG j.1 j.2) (PmPre st Cs Ω Sg Ac Locks j.2 K m)) :
    PathsP (I64 × localinv.Plan) :=
  fun j K m hK hU =>
    pm_localPath (K := K) (m0 := m) (Locks := Locks) ar hA hK hU j.1 j.2 hm
      (P := PmPre st Cs Ω Sg Ac Locks j.2 K m) (fun _ h => h.2.1.1.1)
      (hacc j K m) (hdec j K m) (hmv j K m) (hra j K m)
      (fun s b v h hb ha => by
        obtain ⟨⟨h1, h2⟩, h3⟩ := huf j K m s b v h hb ha
        exact ⟨⟨h1, h2, gateEp_userWr h.2.2 hb ha⟩, h3⟩)
      (pm_hpz (hpr j K m) (hro j K m))

end fam

end
end Fl4Proofs.P2.E2EP

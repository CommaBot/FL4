/-
# P2: the CNodeCopy / CNodeMint arms of the frame-cap invocation path (slhuf gen 9)

Copy and Mint read their 4th / 5th arguments (rights, badge) from the caller's IPC buffer
(`cnode.copied_cap`: `msg.syscall_arg … buf 4` / `… buf 5`, the words `buf + 40` / `buf + 48`; a `Sys` error's
`syscall.reply_error` reads and writes `buf + 56`), user words that `IoRS` excludes. This module states the
path over a read set that admits user words, leaving `IoRS` / `IoWS` / `InvLP` untouched:

* `InvCMRS K Locks s x := Aligned x ∧ (x ∈ K.user ∨ IoRS s x)` and `InvCMWS` alike over `IoWS` (the shape of
  `SlRS` / `SlWS`). On non-user words they are `IoRS` / `IoWS`, so `PathObl.read_own` / `write_own` / `aligned`
  carry over, and `Racy` (which reads `R` only at non-user words) is the same for both sets.
* `alt_cm_io`: an alternative for `InvCMRS s` is one for `IoRS s` (it fixes more words, and the `clsEq` words are
  the same). Hence the declining-side premises of `InvLP` (`InvDecW`, `InvRaW`, `InvRoW`, all over `IoRS`) serve
  the new sets unchanged, and so does `InvMoveW` (no read set).
* `acc` on `guard st (InvCMRS s) (InvCMWS s)`: `invCMAccW_of` from stpost's generic `inv_acc_gen` (the guarded
  store reads `IoRS` words as `st`, `grd_sub`; `IoPre.ioWr` widened, `IoWr.mono`), leaving the Copy/Mint decode
  block `InvCMBlkW` [W] (the `InvBlkW` analogue on the new guard).
* `ReadOnce`: declining entries from `InvRoW` by `once_monoR`; accepting entries `InvCMRoAccW` [W] (the walk over
  the program tree, which needs hpzg's `ProgGenCd` tree of `handle_invocation_local`: see the gen 9 handoff).
* `inv_localPathCM` / `inv_pathsKCM`: the `E2E.LocalPath` / `E2E.Paths` member, with `InvQCM` (arm
  `InvCMArm`: label `CNodeCopy` or `CNodeMint`).

The plan's extra caps (`localinv.plan` → `lookup_extra_caps`, a user-word read) enter the body only as the value
`p.extra` (`invTail` → `decode_invocation … buf p.extra`): the body does not re-read them, and `InvPlanD` (some
extra caps) stays user-write independent.

Premises (named, tagged in their docstrings): `InvCMBlkW` [W], `InvCMRoAccW` [W]; and, passed through as in
`inv_localPath`: `hK` [J], `hU` [J], `hm` [P], `hdec` [W], `hmv` [W], `hra` [W], `huf` [J], `hpz` (`IsProgOn` [P],
`NoZero` [W], `InvRoW` [W]), `hSeen` [J], `hps` [J].
-/
import Fl4Proofs.P2.InvAcc
import Fl4Proofs.P2.InvCMSets
import Fl4Proofs.P2.SlOnceL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-! ## The sets -/

-- (gen 12) The `sets` section (InvCMRS, InvCMWS, ioRS_cm, …, IsProgOn.mono) moved verbatim to `P2/InvCMSets.lean`
-- (stpost gen 14), shared with the uncut CNodeDelete path.

/-! ## The arm and the premises -/

section prem
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- **The arm set of this path**: the current thread's label is `CNodeCopy` or `CNodeMint`. -/
def InvCMArm (s : S) : Prop :=
  ∀ t info, sched.cur_thread st s = ok t → msg.msg_info st s t = ok info →
    info.label = fl4_abi.label.CNodeCopy ∨ info.label = fl4_abi.label.CNodeMint

/-- [W] **`acc`** of the Copy / Mint path: an accepted run on the store guarded to `InvCMRS s` / `InvCMWS s` ends
as the real one. -/
def InvCMAccW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64)
    (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s a s1 a1, P s → syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) →
    syscall.handle_invocation_local (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) ar s a
      number p = ok (true, s1, a1)

/-- [W] **The Copy / Mint decode block on the guarded store** `guard st (InvCMRS s) (InvCMWS s)` (as `InvBlkW`, on
the new guard; `FinOK` with read set `IoRS s` and write set `InvCMWS s`): `cnode.decode` → `lookup_target_slot` →
`decode_copy` (`ensure_empty_slot`, `lookup_source_slot`, `copied_cap`: the buffer words `buf + 40` and, for Mint,
`buf + 48`; `derive_cap`, `update_cap_data`; `set_thread_state RESTART`; `insert_with_cap`), then `invRep`
(`reply_success_empty`, or `reply_error` on a `Sys` error: `buf + 56`). -/
def InvCMBlkW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (p : localinv.Plan)
    (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) ar s2 a1
          info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) (L.curW s) y.2.1 y.2.2 y.1
          = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))
          (IoRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s) ar s z.1 z.2.1

/-- [W] **`ReadOnce` at accepting entries**, of the tree `q`, for `InvCMRS`: along the run from every alternative
each user word (the caller's buffer words `buf + 40`, `buf + 48`, `buf + 56`) is read at most once and not after
a user write of it. -/
def InvCMRoAccW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64)
    (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop) (m0 : U64 → U64) (q : SProg Bool)
    (P : S → Prop) : Prop :=
  ∀ s s' a r, P s → (∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)) →
    Alt st (InvCMRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
    interp st ar q s' a = ok r → Once st ar (InvCMRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ q s' a

end prem

/-! ## `acc` from the decode block -/

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- **`InvCMAccW` from the decode block** (stpost's `inv_acc_gen` on `guard st (InvCMRS s) (InvCMWS s)`): `hA`,
`hPE` (`IoPre` at `Pre`), [J] `hSeen`, [J] `hps` (as `invAccW_of`), and [W] `hblk : InvCMBlkW`. -/
theorem invCMAccW_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : InvCMBlkW st ar p K Locks P) :
    InvCMAccW st ar number p K Locks P := fun s a _ _ hE h => by
  haveI : GRd (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) st
      (IoRS (st := st) K Locks s) := grd_sub (fun _ hy => ioRS_cm hy)
  exact inv_acc_gen (W := InvCMWS (st := st) K Locks s) hA (hPE s hE)
    (((hPE s hE).ioWr (Locks := Locks)).mono (fun _ hy => ioWS_cm hy)) (hSeen s hE) (hps s hE)
    (fun info nx s1 s2 a1 buf length cap emi hc => hblk s a info nx s1 s2 a1 buf length cap hE emi hc) h

end acc

/-! ## The path -/

section path
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A} {number : I64} {p : localinv.Plan}

/-- **`PathObl` of the Copy / Mint path** over `InvCMRS` / `InvCMWS` / `IoDS`: `read_own`, `write_own`, `aligned`
proved; `acc` from `hacc` [W]; `dec_alt` and `move` from stpost's `hdec`, `hmv` [W] (over `IoRS`, by `alt_cm_io`). -/
theorem invCM_pathObl {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : InvCMAccW st ar number p K Locks P) (hdec : InvDecW st ar number p K Locks m0 P)
    (hmv : InvMoveW st ar number p K Locks m0 P) :
    PathObl st (fun m s a => syscall.handle_invocation_local m ar s a number p) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (InvCMRS (st := st) K Locks) (InvCMWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact hacc s a s1 a1 hE h
  · intro s a r hE h hn s' r' Al h'
    exact hdec s a r hE h hn s' r' (alt_cm_io Al) h'
  · intro s x _ hx hu; exact (cmRS_nu hx hu).2.2
  · intro s x hE hx hu
    rcases hx with hx | hx
    · exact (cmWS_nu hx hu).2
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

/-- **`PathSide` of the Copy / Mint path**: `huf` [J] in `inv_localPath`'s form (over `IoRS` / `IoWS`, carried to
`InvCMRS` / `InvCMWS` by `cmRS_eq` / `cmWS_eq`), `hra` [W] over `IoRS` (by `alt_cm_io`). -/
theorem invCM_pathSide (hK : RegionOK K) (hU : E2E.UserOK K) {P : S → Prop} {q : SProg Bool}
    (hacc : InvCMAccW st ar number p K Locks P)
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (InvCMRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q) (hz : NoZero q)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hra : InvRaW st ar number p K Locks m0 P) (hA : P0.ArchTotal ar)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    PathSide st (fun m s a => syscall.handle_invocation_local m ar s a number p)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (InvCMRS (st := st) K Locks) (InvCMWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, fun s x _ hx => hx.1, fun x hx => Fl4Proofs.P2.ko_aligned hK hU x hx, ?_⟩
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
      exact hra s s' a r0 r hE (alt_cm_io Al) h0 hr0 h
  · intro s b v hE hb hA'
    obtain ⟨h1, h2, h3, h4, h5⟩ := huf s b v hE hb hA'
    exact ⟨h1, h2, cmRS_eq h3, cmWS_eq h4, h5⟩

/-- **`ReadOnce` of the Copy / Mint path**: accepting entries from `hroA` [W], declining ones from stpost's `hro`
[W] (over `IoRS`, widened by `once_monoR`). -/
theorem invCM_readOnce {P : S → Prop} {q : SProg Bool} (hroA : InvCMRoAccW st ar number p K Locks m0 q P)
    (hro : InvRoW st ar number p K Locks m0 q P) :
    ReadOnce st ar q (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) P (InvCMRS (st := st) K Locks) := by
  intro s s' a r hE Al h
  by_cases hac : ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)
  · exact hroA s s' a r hE hac Al h
  · exact once_monoR (fun _ hb => ioRS_cm hb) q ∅ ∅ ∅ s' a (hro s s' a r hE hac (alt_cm_io Al) h) subset_rfl

/-- **The Copy / Mint local path**, for any `Pre` `P` giving `IoPre`. Premises: `hA`, `hK` [J], `hU` [J], `hm` [P],
`hPE`, `hacc` [W] (`invCMAccW_of` from `InvCMBlkW` [W]), stpost's `hdec` [W], `hmv` [W], `hra` [W], `huf` [J], and
the program premise `hpz` (`IsProgOn` [P] on `IoRS`'s alternatives, as hpzg delivers it; `NoZero` [W]; `InvRoW` [W];
`InvCMRoAccW` [W]). -/
noncomputable def inv_localPathCM (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hU : E2E.UserOK K) (number : I64) (p : localinv.Plan) (hm : E2E.MasksWr st)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : InvCMAccW st ar number p K Locks P) (hdec : InvDecW st ar number p K Locks m0 P)
    (hmv : InvMoveW st ar number p K Locks m0 P) (hra : InvRaW st ar number p K Locks m0 P)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m0 q P ∧ InvCMRoAccW st ar number p K Locks m0 q P) :
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
  RS := InvCMRS (st := st) K Locks
  WS := InvCMWS (st := st) K Locks
  DS := IoDS (st := st)
  isProg := hpz.choose_spec.1.mono (fun _ hy => altOf_cm_io hy)
  obl := invCM_pathObl hPE hacc hdec hmv
  side := invCM_pathSide hK hU hacc (hpz.choose_spec.1.mono (fun _ hy => altOf_cm_io hy))
    hpz.choose_spec.2.1 hm hra hA huf
  once := invCM_readOnce hpz.choose_spec.2.2.2 hpz.choose_spec.2.2.1
  total := fun s a => inv_total hA number p s a
  masks := hm

end path

/-! ## The canonical `Q` and the `E2E.Paths` member -/

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

variable (st) in
/-- **The canonical `Q` of the Copy / Mint path**: as `InvQ` with the arm `InvCMArm`. (`InvPlanD` keeps the plan's
extra caps existential, so it does not depend on the user words `lookup_extra_caps` reads.) -/
def InvQCM (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayout)
    (m : U64 → U64) (s : S) : Prop :=
  IoQ st Cs Ω Sg Ac K m s ∧ InvPlanD st p s ∧ InvCMArm st s ∧
    ∀ (i : Nat) (x : U64), i < p.n.val → p.locks.val[i]? = some x → Locks s x

/-- **`InvQCM` at an entry state** from its pieces (as `invQ_intro`). -/
theorem invQCM_intro {number : I64} {p : localinv.Plan} {K : KLayout} {m : U64 → U64} {s : S}
    (hP : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hmA : ∀ d, K.heap d = some .tcb → m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hp : localinv.plan st s number = ok (some p)) (harm : InvCMArm st s)
    (hlk : ∀ (i : Nat) (x : U64), i < p.n.val → p.locks.val[i]? = some x → Locks s x) :
    InvQCM st Cs Ω Sg Ac Locks p K m s :=
  ⟨⟨hP, hmA⟩, planD_of_plan hp, harm, hlk⟩

/-- **The Copy / Mint local path as an `E2E.Paths` member**: `inv_localPathCM` at every layout `K` and memory `m`,
`Pre := SlJAt K ∧ Q K m` (as `inv_pathsK`; `hacc` over the new guard, the other premises as there plus
`InvCMRoAccW` in `hpz`). -/
noncomputable def inv_pathsKCM (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hacc : ∀ K m, InvCMAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
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
      InvRoW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ Q K m s) ∧
      InvCMRoAccW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ Q K m s)) :
    E2E.Paths Unit :=
  fun _ K m hK hU =>
    inv_localPathCM (K := K) (m0 := m) (Locks := Locks) ar hA hK hU number p hm
      (P := fun s => SlJAt (L := L) K s ∧ Q K m s) (fun s h => hPE K m s h.1 h.2)
      (hacc K m) (hdec K m) (hmv K m) (hra K m) (fun s b v h => huf K m s b v h.1 h.2) (hpz K m)

end paths

end Fl4Proofs.P2.PathObl

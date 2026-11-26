/-
# P2 (line pte, generation 12): the PageMap slot over the user-word sets (option (a) of the `acc` finding)

Gen 11 found `PmAccW` false: `decode_page_map` can still fail after the plan's checks (a mapped frame with another
ASID / `vaddr`, `vaddr + 4096 > USER_TOP`, an unaligned `vaddr`, `check_vspace` finding another root), and the error
reply `syscall.reply_error` (`KERNEL_INVOCATION_REPORT_ERROR_IPC`) then reads and writes the caller's IPC-buffer
word `DEBUG_MESSAGE_START + 1`, a user word outside `PmRS` / `PmWS`. Coordinator's decision: keep every accepted
run and add the user words to the sets, as the uncut CNodeDelete path (`InvCMRS` / `InvCMWS`, `P2/InvCMSets.lean`)
and invj's ownP Delete path (`InvRSP` / `InvWSP`) do:

* **`PmRSU` / `PmWSU`**: aligned user words or `PmRS` / `PmWS`. **Ownership** (`PathObl.read_own` / `write_own`
  constrain only non-user words, `x ∉ User`): a non-user word of `PmRSU` / `PmWSU` is a `PmRS` / `PmWS` word
  (`pmRSU_nu`, `pmWSU_nu`), so `RPerm` / `WPerm` under `ownP K` hold as before — no conflict with `ownP`;
* `alt_pmU` / `altOf_pmU` (an alternative over `PmRSU` is one over `PmRS`), so gen 11's declining-side theorems
  (`pm_dec`, `pm_ra`, `pm_ro`, `pm_isProgOn`) carry over; `onceU_monoR` lifts `pm_ro`'s `Once` to `PmRSU`;
* `pmWS_of_ptU` (`IoWS (ptU K) ⊆ PmWS K`), `pmRSU_ioRS`, `pmWSU_ioWS`;
* `PmAccUW` [W] (`acc` at the new sets), `PmRoAccW` [W] (**`ReadOnce` of accepting runs**: before, accepted runs
  read no user word on the guarded store, so `once_of_guardG` gave it from `acc`; an accepted run whose decode
  errors now reads the buffer word once, then writes it — `Once` allows that, but it has to be shown along the
  tree, as invj gen 2's `invURoTrW_of` does for truncated Deletes). This is the obligation option (a) moves out of
  the old (false) `acc`, not a new claim;
* `PmBlkUW` (the decode block on `guard st (PmRSU s) (PmWSU s)`, `InvBlkW`'s shape at `ptU K`) and
  **`pm_accU_of_blk`**: `PmAccUW` from it (`inv_acc_gen` at `ptU K`: the entry reads, prefix, checks,
  `still_holds`, the slot cap, `after_invocation` and `finish` proved; seen words and slot words by `pm_seen` /
  `pm_slotRS`);
* `pm_pathOblU`, `pm_pathSideU`, `pm_readOnceU`, **`pm_localPathU`**, `pm_hufU`;
* **`pm_iw`**: gen 11's [J] `PmIw` from iolay's `ioPre_wr_hIw` at a core set below 64 ([P] `hCs`, a fact of the
  fixed core set: P3's `JKern.csLt` at every bundle state with that ghost, `IoPremW9.hCs`);
* `PmObl3`, `pmPathsU`, `StartPmU`, `pm_hSFQU`, **`serializable_fl4_localW11PRIPmU`**.

Premises of `serializable_fl4_localW11PRIPmU` beyond `serializable_fl4_localW11PR`'s (`B : PmObl3`): [W] `blk`
(`PmBlkUW`, the decode block — what remains of `acc`), [W] `mv`, [W] `roA` (`PmRoAccW`), [P] `cs`, [J] `pdw`,
[P] `lk`.

**Leaf address 0 (gen 11's question)**: `table_of e = (e &&& ADDR_MASK) + PPTR_BASE` wraps (`PPTR_BASE = 2^64 − 2^39`,
`ADDR_MASK` reaches `2^52`), so `lookup_pt_slot` returns `0` exactly when the PD entry names physical page `2^39`
and the PT index of `vaddr` is 0. At such a state the plan takes no lock on the leaf (`Plan.add` skips `0`) and the
decode writes word `0` unlocked. At P3 states the leaf is a word of a page table of `Zx.L1` (`walk3_leaf`), and those
are 4 KiB-aligned (`PtPlaced`) but P3 carries no fact that they are non-zero (`JKern.h0` is about the P1 heap, which
has no page tables; `UtCapP3.high` puts RAM untyped regions at `≥ 2^64 − 2^47`, so a table retyped from one is
non-zero, but no invariant on `Zx.L1` records it). So `e ≠ 0` is true at reachable states (tables come from RAM
untypeds or boot memory in the kernel window) but not derivable here; it is not used yet (it enters with `blk`).

No existing statement or file changed.
-/
import Fl4Proofs.P2.InvPmTop2
import Fl4Proofs.P2.InvCMSets
import Fl4Proofs.P2.E2EVFl4W9
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

/-! ## The sets -/

section sets
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- **What the PageMap path may read**: aligned user words (the caller's IPC buffer among them) and `PmRS`. -/
def PmRSU (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ (x ∈ K.user ∨ PmRS st K Locks s x)

variable (st) in
/-- **What an accepted PageMap run may write**: aligned user words (an error reply writes the caller's buffer) and
`PmWS`. -/
def PmWSU (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ (x ∈ K.user ∨ PmWS st K Locks s x)

variable {K : KLayoutP} {Locks : S → U64 → Prop} {s : S} {x : U64}

theorem pmRS_U (h : PmRS st K Locks s x) : PmRSU st K Locks s x := ⟨h.1, Or.inr h⟩

theorem pmWS_U (h : PmWS st K Locks s x) : PmWSU st K Locks s x := ⟨h.1, Or.inr h⟩

theorem pmRSU_nu (h : PmRSU st K Locks s x) (hu : x ∉ K.user) : PmRS st K Locks s x := h.2.resolve_left hu

theorem pmWSU_nu (h : PmWSU st K Locks s x) (hu : x ∉ K.user) : PmWS st K Locks s x := h.2.resolve_left hu

/-- **An alternative over `PmRSU` is one over `PmRS`.** -/
theorem alt_pmU {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {s' : S}
    (Al : Alt st (PmRSU st K Locks s) cls ko (· ∈ K.user) s s') :
    Alt st (PmRS st K Locks s) cls ko (· ∈ K.user) s s' :=
  ⟨Al.cpu, Al.ksb, Al.masks, fun y hy => Al.read y (pmRS_U hy),
    fun y hy hu ho => Al.clsEq y (fun h => hy (pmRSU_nu h hu)) hu ho⟩

theorem altOf_pmU {P : S → Prop} {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {s' : S}
    (h : AltOf st P (PmRSU st K Locks) cls ko (· ∈ K.user) s') :
    AltOf st P (PmRS st K Locks) cls ko (· ∈ K.user) s' :=
  let ⟨s0, hP, Al⟩ := h; ⟨s0, hP, alt_pmU Al⟩

/-- **`IoWS (ptU K) ⊆ PmWS K`** (the layout's region facts). -/
theorem pmWS_of_ptU (hK : RegionOKP K) (hx : IoWS (st := st) K.ptU Locks s x) : PmWS st K Locks s x :=
  ⟨hx.1, wpermP_of_V hK (wpermV_of_own' hK.base hx.2)⟩

theorem pmRSU_ioRS (h : GateEp st K s) (hx : IoRS (st := st) K.ptU Locks s x) : PmRSU st K Locks s x :=
  pmRS_U (pmRS_of_ptU h hx)

theorem pmWSU_ioWS (hK : RegionOKP K) (hx : IoWS (st := st) K.ptU Locks s x) : PmWSU st K Locks s x :=
  pmWS_U (pmWS_of_ptU hK hx)

end sets

/-! ## The obligations at the new sets -/

section obl
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- [W] **`acc`** of the PageMap path at the user-word sets. -/
def PmAccUW {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayoutP)
    (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s a s1 a1, P s → syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) →
    syscall.handle_invocation_local (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) ar s a number p =
      ok (true, s1, a1)

variable (st) in
/-- [W] **`ReadOnce` at accepting PageMap entries**, of the tree `q`, for `PmRSU` (module docstring). -/
def PmRoAccW {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayoutP)
    (Locks : S → U64 → Prop) (m0 : U64 → U64) (q : SProg Bool) (P : S → Prop) : Prop :=
  ∀ s s' a r, P s → (∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)) →
    Alt st (PmRSU st K Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) s s' →
    interp st ar q s' a = ok r → Once st ar (PmRSU st K Locks s) (· ∈ K.user) ∅ ∅ q s' a

variable (st) in
/-- [W] **The decode block of an accepted PageMap run on the guarded store** (`InvBlkW`'s shape, at the user-word
sets and the read set `IoRS (ptU K)` of `FinOK`): `decode_invocation` (→ `decode_page_map`) and the reply run as
on `st`, the reply's result is `Ok ()`, and `FinOK` holds after it. -/
def PmBlkUW {A : Type} (ar : machine.Arch A) (p : localinv.Plan) (K : KLayoutP) (Locks : S → U64 → Prop)
    (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) ar s2 a1
          info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (guard st (PmRSU st K Locks s) (PmWSU st K Locks s))
          (IoRS (st := st) K.ptU Locks s) (PmWSU st K Locks s) ar s z.1 z.2.1

variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`acc` from the decode block** (`inv_acc_gen` at `ptU K` on `guard st (PmRSU s) (PmWSU s)`). -/
theorem pm_accU_of_blk (hA : P0.ArchTotal ar) (hK : RegionOKP K) {number : I64}
    (hblk : PmBlkUW st ar p K Locks (PmPreF st Cs Ω Sg Ac Locks p K μ)) :
    PmAccUW st ar number p K Locks (PmPreF st Cs Ω Sg Ac Locks p K μ) := fun s a _ _ hE h => by
  obtain ⟨hJ, hq, hG⟩ := hE
  have P := hq.1.1.1.ptU hG
  obtain ⟨-, -, -, -, -, -, hsl, -, -, -⟩ := pm_core hq
  obtain ⟨-, hf⟩ := P.lay.slot8 _ hsl
  have r0 : IoRS (st := st) K.ptU Locks s p.slot := by
    have := pm_slotRS hJ hq P (o := 0#u64) (by simp) (by simp)
    rwa [wadd_zero hf] at this
  have r8 := pm_slotRS hJ hq P (o := 8#u64) (by simp) (by simp)
  haveI : GRd (guard st (PmRSU st K Locks s) (PmWSU st K Locks s)) st (IoRS (st := st) K.ptU Locks s) :=
    grd_sub (fun _ hy => pmRSU_ioRS hG hy)
  exact inv_acc_gen (W := PmWSU st K Locks s) hA P ((P.ioWr (Locks := Locks)).mono (fun _ hy => pmWSU_ioWS hK hy))
    (pm_seen hJ hq P) ⟨r0, r8⟩
    (fun info nx s1 s2 a1 buf length cap emi hc => hblk s a info nx s1 s2 a1 buf length cap ⟨hJ, hq, hG⟩ emi hc) h

end obl

/-! ## The path -/

section path
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutP}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A} {number : I64} {p : localinv.Plan}

/-- **`PathObl` of the PageMap path at the user-word sets**: `read_own`, `write_own` (non-user words are `PmRS` /
`PmWS` words), `aligned` proved; `dec_alt` from `hdec` over `PmRS` (`alt_pmU`). -/
theorem pm_pathOblU (hK : RegionOKP K) {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K.toKLayout T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : PmAccUW st ar number p K Locks P) (hdec : PmDecW st ar number p K Locks m0 P)
    (hmv : PmMoveW st ar number p K Locks m0 P) :
    PathObl st (fun m s a => syscall.handle_invocation_local m ar s a number p) (fun b => b = true)
      (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) Locks P
      (PmRSU st K Locks) (PmWSU st K Locks) (IoDS (st := st)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact hacc s a s1 a1 hE h
  · intro s a r hE h hn s' r' Al h'
    exact hdec s a r hE h hn s' r' (alt_pmU Al) h'
  · intro s x _ hx hu; exact (pmRSU_nu hx hu).2.2
  · intro s x hE hx hu
    rcases hx with hx | hx
    · exact (pmWSU_nu hx hu).2
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

/-- **`PathSide` of the PageMap path at the user-word sets** (as `pm_pathSide`). -/
theorem pm_pathSideU (hK : RegionOKP K) (hU : UserOKP K) {P : S → Prop} {q : SProg Bool}
    (hacc : PmAccUW st ar number p K Locks P)
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (PmRSU st K Locks) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user)) q)
    (hz : NoZero q) (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hra : PmRaW st ar number p K Locks m0 P) (hA : P0.ArchTotal ar)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        PmRSU st K Locks (L.wr s b v) = PmRSU st K Locks s ∧
        PmWSU st K Locks (L.wr s b v) = PmWSU st K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    PathSide st (fun m s a => syscall.handle_invocation_local m ar s a number p)
      (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) Locks P
      (PmRSU st K Locks) (PmWSU st K Locks) (IoDS (st := st)) := by
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
    exact hra s s' a r0 r hE (alt_pmU Al) h0 hr0 h

/-- **`ReadOnce` of the PageMap path at `PmRSU`**: accepting entries `hroA` [W], declining ones from `hro` (over
`PmRS`) by `onceU_monoR`. -/
theorem pm_readOnceU {P : S → Prop} {q : SProg Bool} (hroA : PmRoAccW st ar number p K Locks m0 q P)
    (hro : PmRoW st ar number p K Locks m0 q P) :
    ReadOnce st ar q (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P (PmRSU st K Locks) := by
  intro s s' a r hE Al h
  by_cases hac : ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)
  · exact hroA s s' a r hE hac Al h
  · exact onceU_monoR (fun _ hb => pmRS_U hb) q ∅ ∅ ∅ s' a (hro s s' a r hE hac (alt_pmU Al) h) subset_rfl

/-- **The PageMap invocation local path under `ownP` at the user-word sets**, for the tree `q`. -/
def pm_localPathU (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOKP K) (hU : UserOKP K)
    (number : I64) (p : localinv.Plan) (hm : E2E.MasksWr st)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K.toKLayout T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : PmAccUW st ar number p K Locks P) (hdec : PmDecW st ar number p K Locks m0 P)
    (hmv : PmMoveW st ar number p K Locks m0 P) (hra : PmRaW st ar number p K Locks m0 P)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        PmRSU st K Locks (L.wr s b v) = PmRSU st K Locks s ∧
        PmWSU st K Locks (L.wr s b v) = PmWSU st K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (q : SProg Bool)
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (PmRSU st K Locks) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user)) q)
    (hz : NoZero q) (hroA : PmRoAccW st ar number p K Locks m0 q P) (hro : PmRoW st ar number p K Locks m0 q P) :
    E2E.LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := invBody S number p
  p := q
  Acc := fun b => b = true
  Locks := Locks
  Pre := P
  RS := PmRSU st K Locks
  WS := PmWSU st K Locks
  DS := IoDS (st := st)
  isProg := hp
  obl := pm_pathOblU hK hPE hacc hdec hmv
  side := pm_pathSideU hK hU hacc hp hz hm hra hA huf
  once := pm_readOnceU hroA hro
  total := fun s a => inv_total hA number p s a
  masks := hm

end path

/-! ## `uf` and `iw` -/

section huf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- **`PmIw` from a core set below 64** (gen 11's [J] `iw`; [P] `hCs`, iolay's `ioPre_wr_hIw`). -/
theorem pm_iw (hCs : ∀ c ∈ Cs, c.val < 64) : PmIw st Cs Ω Sg Ac := ioPre_wr_hIw hCs

/-- **`uf` of the PageMap slot at the user-word sets** (`pm_huf`; the user part of the sets is fixed). -/
theorem pm_hufU (hIw : PmIw st Cs Ω Sg Ac) (hPDw : PmPdw st Cs Ω Sg Ac Locks) (hlk : PmLk st Locks) :
    ∀ (j : I64 × localinv.Plan) (K : KLayoutP) m s b v, PmPreF st Cs Ω Sg Ac Locks j.2 K m s →
      b ∈ K.user → Aligned b →
      PmPreF st Cs Ω Sg Ac Locks j.2 K m (L.wr s b v) ∧
        Locks (L.wr s b v) = Locks s ∧
        PmRSU st K Locks (L.wr s b v) = PmRSU st K Locks s ∧
        PmWSU st K Locks (L.wr s b v) = PmWSU st K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro j K m s b v h hb ha
  obtain ⟨⟨h1, h2⟩, el, eR, eW, eD⟩ := pm_huf hIw hPDw hlk j K m s b v h hb ha
  refine ⟨⟨h1, h2, gateEp_userWr h.2.2 hb ha⟩, el, ?_, ?_, eD⟩
  · funext y; unfold PmRSU; rw [eR]
  · funext y; unfold PmWSU; rw [eW]

end huf

/-! ## The slot -/

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **What is left of the PageMap slot's obligations at the user-word sets** (module docstring). -/
structure PmObl3 (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop where
  /-- [W] the decode block (what remains of `acc`). -/
  blk : ∀ (j : I64 × localinv.Plan) K m, PmBlkUW st ar j.2 K Locks (PmPreF st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `move`. -/
  mv : ∀ (j : I64 × localinv.Plan) K m, PmMoveW st ar j.1 j.2 K Locks m (PmPreF st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `ReadOnce` of accepting runs (the buffer word read once before its write). -/
  roA : ∀ (j : I64 × localinv.Plan) K m,
    PmRoAccW st ar j.1 j.2 K Locks m (R.invBodyPmG j.1 j.2) (PmPreF st Cs Ω Sg Ac Locks j.2 K m)
  /-- [P] the core set is below 64. -/
  cs : ∀ c ∈ Cs, c.val < 64
  /-- [J] the plan survives a user write. -/
  pdw : PmPdw st Cs Ω Sg Ac Locks
  /-- [P] the locks survive a user write. -/
  lk : PmLk st Locks

variable {st ar}

/-- **The PageMap slot family at the user-word sets.** -/
def pmPathsU {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl3 st ar Cs Ω Sg Ac Locks) :
    PathsP (I64 × localinv.Plan) :=
  fun j K m hK hU =>
    pm_localPathU (K := K) (m0 := m) (Locks := Locks) ar hA hK hU j.1 j.2 hm
      (P := PmPreF st Cs Ω Sg Ac Locks j.2 K m) (fun _ h => h.2.1.1.1.1)
      (pm_accU_of_blk hA hK (B.blk j K m)) (pm_dec hA j.1) (B.mv j K m) (pm_ra hA j.1)
      (pm_hufU (pm_iw B.cs) B.pdw B.lk j K m)
      (R.invBodyPmG j.1 j.2) ((pm_isProgOn hA j.1).mono (fun _ hy => altOf_pmU hy))
      (pm_noZero j.1 j.2) (B.roA j K m) (pm_ro hA j.1)

/-- **The PageMap slot's start fact** (as `StartPmF`). -/
def StartPmU {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl3 st ar Cs Ω Sg Ac Locks)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) (j : I64 × localinv.Plan) : Prop :=
  ∃ (σ : S) (a : A), Ch σ ∧ PmQF st Cs Ω Sg Ac Locks j.2 K m σ ∧ L.cpu σ = c ∧ Locks σ = hs ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x) ∧ q = (pmPathsU hA hm B j K m hK hU).body σ a

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **`hSFQ` of `serializable_fl4_localW11PRI` for the PageMap slot at the user-word sets.** -/
theorem pm_hSFQU {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl3 st ar Cs Ω Sg Ac Locks) :
    ∀ Ch K m hK hU c hs q j, (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → m x = s1.mem x) →
      StartPmU hA hm B Ch K m hK hU c hs q j → StartAt (pmPathsU hA hm B j K m hK hU) c hs m q := by
  rintro Ch K m hK hU c hs q j ⟨σe, hC⟩ ⟨s1, hc1, hg⟩ ⟨σ, a, hCh, hQ, hc, hl, hμ, rfl⟩
  obtain ⟨Z, H, Cx, nc, -, -, -, hCL, -⟩ := hC
  exact ⟨σ, a, ⟨hCL.bun σ hCh, hQ, s1.mem, hc1, fun x hx ha hu => (hμ x ha hu).trans (hg x hx)⟩, hc, hl, hμ,
    rfl⟩

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end over W11's slots and the PageMap slot at the user-word sets** (module docstring). -/
theorem serializable_fl4_localW11PRIPmU (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl3 st ar Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPR (PathsP.sum (fl4LocW11J st ar hA hm hSt a0) (pmPathsU hA hm B))
      (StartW11RI st ar hA hm hSt a0 arI AR MR (StartPmU hA hm B)) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localW11PRI st ar hA hm hSt a0 P hIoa (pmPathsU hA hm B) (pm_hSFQU hA hm B) h0 hA0 hB hc0 hM0
    h hq

end top

end
end Fl4Proofs.P2.E2EP

/-
# P2 (line stpost, generation 14): the uncut CNodeDelete path (truncated Deletes included) over the user-word sets

Truncated Deletes (`length < 2`) are accepted by `localinv.plan`; their error reply writes the caller's IPC buffer.
Instead of cutting them (`InvLen`, gen 13; `InvQL` / `inv_pathsKF` stay), the path is stated over slhuf's
user-word read / write sets `InvCMRS` / `InvCMWS` (`P2/InvCMSets.lean`, shared with the Copy / Mint path), at the
canonical `Q := InvQF` (shape unchanged):

* `InvUAccW`, `InvURoAccW` [W], `invU_pathObl`, `invU_pathSide`, `invU_readOnce`, `inv_localPathU`,
  `inv_pathsKDelU`: slhuf gen 9's `InvCMAccW` / `InvCMRoAccW` / `invCM_*` / `inv_localPathCM` / `inv_pathsKCM`,
  renamed (the declining-side premises over `IoRS` carry over by `alt_cm_io`; `onceU_monoR`);
* `InvBlkUW2` (the decode block on `guard st (InvCMRS s) (InvCMWS s)`, with the cap / length hypotheses),
  `invUAccW_of2`, **`invBlkUW2_of`**: both arms proved — `length ≥ 2` by `delAcc` / `delFin`, `length < 2` by
  `truncAcc` / `truncFin` (`InvTrunc`, [J] `InvBufJ`);
* `gdr_sub`, `InvBlkGdUW2` (the decode block on `gd st (InvCMRS s) (PWs …)`), **`invBlkGdUW2_of`**,
  **`invMoveW_ofU`** (`move`: the user-word write of a truncated run passes `PW` as a non-deciding aligned word);
* **`inv_pathsKFU`** / `inv_pathsKFU_startAt`: the path at `Q := InvQF`, `acc` / `move` / `dec_alt` /
  `read_aligned` / `hSeen` / `hps` discharged. Premises: `hA`, [P] `hm`, [J] `hvs : InvVsJ`, [J] `hcdt : InvCdtJ`,
  [J] `hz`, [J] `hbuf : InvBufJ` (at `Pre`), [J] `huf`, `hpz` ([P] IsProgOn ∧ [W] NoZero ∧ [W] InvRoW ∧
  [W] `InvURoAccW`: `ReadOnce` of accepting runs, which now read a user word when truncated).

No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvCMSets
import Fl4Proofs.P2.InvMove
import Fl4Proofs.P2.InvTrunc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-! ## The premises (slhuf's Copy / Mint shape) -/

section prem
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- [W] **`acc`** of the uncut CNodeDelete path (as slhuf's Copy / Mint): an accepted run on the store guarded to `InvCMRS s` / `InvCMWS s` ends
as the real one. -/
def InvUAccW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64)
    (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s a s1 a1, P s → syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) →
    syscall.handle_invocation_local (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) ar s a
      number p = ok (true, s1, a1)


/-- [W] **`ReadOnce` at accepting entries**, of the tree `q`, for `InvCMRS`: along the run from every alternative
each user word (the caller's buffer words `buf + 40`, `buf + 48`, `buf + 56`) is read at most once and not after
a user write of it. -/
def InvURoAccW (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (number : I64)
    (p : localinv.Plan) (K : KLayout) (Locks : S → U64 → Prop) (m0 : U64 → U64) (q : SProg Bool)
    (P : S → Prop) : Prop :=
  ∀ s s' a r, P s → (∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)) →
    Alt st (InvCMRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
    interp st ar q s' a = ok r → Once st ar (InvCMRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ q s' a



variable {K : KLayout} {Locks : S → U64 → Prop}

/-- [W] (stpost gen 14) **The decode block on the store guarded to the user-word sets** (`InvBlkW2` on
`guard st (InvCMRS s) (InvCMWS s)`, `FinOK` with read set `IoRS s` and write set `InvCMWS s`). Proved for the
uncut CNodeDelete arm by `invBlkUW2_of`. -/
def InvBlkUW2 (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (p : localinv.Plan)
    (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
      obj.Slot.cap st p.slot s2 = ok cap →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) ar s2 a1
          info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))
          (IoRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s) ar s z.1 z.2.1

/-- [W] (stpost gen 14) **The decode block on p2sl's checked store with slot `CAP0` writes, reading the user-word
set** `gd st (InvCMRS s) (PWs …)`. Proved for the uncut arm by `invBlkGdUW2_of`. -/
def InvBlkGdUW2 (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A) (p : localinv.Plan)
    (K : KLayout) (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap, P s → msg.msg_info st s (L.curW s) = ok info →
    InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
      obj.Slot.cap st p.slot s2 = ok cap →
    ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
      syscall.decode_invocation (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) ar s2 a1
          info.label length p.slot cap true true true false buf p.extra = ok y ∧
      ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
        invRep (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
        z.2.2 = core.result.Result.Ok () ∧
        FinOK (L := L) (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))
          (IoRS (st := st) K Locks s) (WAll (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) ar s z.1 z.2.1

/-- The checked store reading `R` reads every word of a smaller `R'` as `st`. -/
theorem gdr_sub {R R' : U64 → Prop} {Pw : S → U64 → U64 → Prop} (h : ∀ y, R' y → R y) :
    GRd (gd st R Pw) st R' where
  read hy s := (GRd.gd st R Pw).read (h _ hy) s
  read_pair hy h8 s := (GRd.gd st R Pw).read_pair (h _ hy) (h _ h8) s
  ks_base := rfl
  cur_cpu := rfl
  frame_masks := rfl

end prem

/-! ## `acc` and `move` from the decode blocks -/

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- (stpost gen 14) **`InvUAccW` from the decode block** (`inv_acc_gen2` on `guard st (InvCMRS s) (InvCMWS s)`). -/
theorem invUAccW_of2 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : InvBlkUW2 st ar p K Locks P) :
    InvUAccW st ar number p K Locks P := fun s a _ _ hE h => by
  haveI : GRd (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) st
      (IoRS (st := st) K Locks s) := grd_sub (fun _ hy => ioRS_cm hy)
  exact inv_acc_gen2 (W := InvCMWS (st := st) K Locks s) hA (hPE s hE)
    (((hPE s hE).ioWr (Locks := Locks)).mono (fun _ hy => ioWS_cm hy)) (hSeen s hE) (hps s hE)
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk => hblk s a info nx s1 s2 a1 buf length cap hE emi hc hl hk) h

/-- (stpost gen 14) **`InvMoveW` from the decode block on `gd st (InvCMRS s) (PWs …)`** (`invMoveW_of2` with the
user-word read set). -/
theorem invMoveW_ofU {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {m0 : U64 → U64} {P : S → Prop} (hK : ∀ s, P s → RegionOK K) (hU : ∀ s, P s → E2E.UserOK K)
    (hLA : ∀ s, P s → IoLayA K) (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (hps : ∀ s, P s → IoRS (st := st) K Locks s p.slot ∧
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hmA : ∀ s, P s → ∀ d, K.heap d = some .tcb → m0 (fld d OwnMap.oAFFINITY) = L.mem s (fld d OwnMap.oAFFINITY))
    {q : SProg Bool}
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q)
    (hblk : InvBlkGdUW2 st ar p K Locks P) :
    InvMoveW st ar number p K Locks m0 P := by
  intro s a s1 a1 hE h
  haveI : GRd (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st
      (IoRS (st := st) K Locks s) := gdr_sub (fun _ hy => ioRS_cm hy)
  have hg := inv_acc_gen2 (gS := (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))))
    hA (hPE s hE) (mvWrS (hPE s hE) (hK s hE) (hLA s hE)) (hSeen s hE) (hps s hE)
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk => hblk s a info nx s1 s2 a1 buf length cap hE emi hc hl hk) h
  rw [inv_hp hp (Narrow.gd _ _ _) (AltOf.pre hE) a] at hg
  rw [inv_hp hp (Narrow.mguard _ _) (AltOf.pre hE) a]
  exact OwnMap.run_gds_mguard (hK s hE) (hU s hE) (hmA s hE) q hg

end acc

/-! ## Both arms of the uncut decode block -/

section arm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (stpost gen 14) **`InvBlkUW2` for the uncut CNodeDelete arm** at `Pre := SlJAt K ∧ InvQF`: `length ≥ 2` by
`delAcc` / `delFin` (the `IoRS` / `IoWS` words are user-word-set words), `length < 2` by `truncAcc` / `truncFin`;
from [J] `hvs`, [J] `hcdt`, [J] `hz`, [J] `hbuf`. -/
theorem invBlkUW2_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hvs : InvVsJ st K (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s))
    (hcdt : InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, SlJAt (L := L) K s → (0#u64) ∉ K.slots)
    (hbuf : ∀ s, SlJAt (L := L) K s → InvQF st Cs Ω Sg Ac Locks p K μ s → InvBufJ st K s) :
    InvBlkUW2 st ar p K Locks (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hl hcap y hy
  have hqf := hE.2
  have PE := hqf.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_core hqf
  have hlbl := (hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  by_cases hlen : length < 2#u64
  · obtain ⟨hdec, hrep⟩ := truncAcc (gS := (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))) hA PE
      (fun _ h => ioRS_cm h) (fun _ h => ⟨h.1, Or.inl h.2⟩) (PE.ioWr.mono (fun _ h => ioWS_cm h))
      (fun _ h => ⟨h.1, Or.inl h.2⟩) hcs hsK (hbuf s hE.1 hqf) C hcap hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) st
        (IoRS (st := st) K Locks s) := grd_sub (fun _ hy => ioRS_cm hy)
    obtain ⟨h1, h2⟩ := truncFin (gS := (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))) hA PE
      (PE.ioWr.mono (fun _ h => ioWS_cm h)) (SWr.of_W (ioWS_cm PE.stw.2)) hcs hsK (hbuf s hE.1 hqf) C hcap hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · have E := delEnt_of (P := fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s) hE hqf hvs hcdt
      (hz s hE.1)
    haveI : GRd (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) st
        (IoRS (st := st) K Locks s) := grd_sub (fun _ hy => ioRS_cm hy)
    obtain ⟨hdec, hrep⟩ := delAcc (gS := (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))) hA PE
      (PE.ioWr.mono (fun _ h => ioWS_cm h)) (fun _ h => ioWS_cm h) E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := delFin (gS := (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))) hA PE
      (PE.ioWr.mono (fun _ h => ioWS_cm h)) (ioWS_cm PE.stw.2) E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- (stpost gen 14) **`InvBlkGdUW2` for the uncut CNodeDelete arm** (as `invBlkUW2_of`, on
`gd st (InvCMRS s) (PWs …)`: `delAcc2` / `delFin2`, `truncAcc` / `truncFin`; a user word is an aligned word deciding
no owner, so `PW` allows its write). -/
theorem invBlkGdUW2_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hvs : InvVsJ st K (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s))
    (hcdt : InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, SlJAt (L := L) K s → (0#u64) ∉ K.slots)
    (hbuf : ∀ s, SlJAt (L := L) K s → InvQF st Cs Ω Sg Ac Locks p K μ s → InvBufJ st K s) :
    InvBlkGdUW2 st ar p K Locks (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hl hcap y hy
  have hqf := hE.2
  have PE := hqf.1.1.1
  have hK := hE.1.regionOK
  have hU := hE.1.userOK
  have hLA := hE.1.ioLayA
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_core hqf
  have hlbl := (hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  have hW := mvWrS PE hK hLA (c := L.cpu s) (lk := Locks s) (m := L.mem s)
  have hS0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) := by
    refine ⟨?_, fun hq => absurd hq ?_⟩
    · rw [← OwnMap.affA_fld]; exact PE.curAff
    · rw [← OwnMap.stA_fld]; exact nq_run PE.run
  have hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      SWr (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st (L.curW s) v :=
    fun v hv X => OwnMap.gds_write_state (PE.hT _ PE.cT) hS0 (fun hq => absurd hq (nq_run hv))
  have hWu : ∀ b, UserW K b → WAll (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)) b :=
    fun b hb _ _ => Or.inl (Or.inl ⟨hb.1, fun hd => (OwnMap.decW_ok hU hd).2 hb.2⟩)
  by_cases hlen : length < 2#u64
  · obtain ⟨hdec, hrep⟩ := truncAcc (gS := (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))) hA PE
      (fun _ h => ioRS_cm h) (fun _ h => ⟨h.1, Or.inl h.2⟩) hW hWu hcs hsK (hbuf s hE.1 hqf) C hcap hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st
        (IoRS (st := st) K Locks s) := gdr_sub (fun _ hy => ioRS_cm hy)
    obtain ⟨h1, h2⟩ := truncFin (gS := (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))) hA PE
      hW (hst _ (Or.inr rfl)) hcs hsK (hbuf s hE.1 hqf) C hcap hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · have E := delEnt_of (P := fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s) hE hqf hvs hcdt
      (hz s hE.1)
    haveI : GRd (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st
        (IoRS (st := st) K Locks s) := gdr_sub (fun _ hy => ioRS_cm hy)
    have hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
        (16 ≤ o.val ∨ (¬ TcbSlot K q ∧ NullOrFrame (L.mem s q))) →
        WAll (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)) (core.num.U64.wrapping_add q o) := by
      intro q o hq _ ho h8 h8' _
      obtain ⟨q8, qf⟩ := PE.lay.slot8 q hq
      have hv := slot_word_val qf ho
      have hr := PE.lay.slotw q hq _ (slot_inW qf ho)
      have hne : core.num.U64.wrapping_add q o ≠ q := fun e => by
        have := congrArg UScalar.val e; rw [hv] at this; omega
      have ha : Aligned (core.num.U64.wrapping_add q o) := by unfold Aligned; rw [hv]; omega
      exact fun _ _ => Or.inl (Or.inl ⟨ha, OwnMap.nondec_slotw hK hr hne⟩)
    have hw0 : ∀ q, q ∈ K.slots → Locks s q → ¬ TcbSlot K q → NullOrFrame (L.mem s q) →
        ∀ x, (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))).write x q 0#u64 = st.write x q 0#u64 :=
      fun q hq hl hT hn x => OwnMap.gds_write_cap0 hq hT hl hn OwnMap.nof_zero
    obtain ⟨hdec, hrep⟩ := delAcc2 (gS := (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))) hA PE hW hwS hw0 hst E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := delFin2 (gS := (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))) hA PE hW (hst _ (Or.inr rfl)) E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩

end arm

/-! ## The path (slhuf's assembly, renamed) -/

/-! ## The path -/

section path
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A} {number : I64} {p : localinv.Plan}

/-- **`PathObl` of the uncut CNodeDelete path (as slhuf's Copy / Mint)** over `InvCMRS` / `InvCMWS` / `IoDS`: `read_own`, `write_own`, `aligned`
proved; `acc` from `hacc` [W]; `dec_alt` and `move` from stpost's `hdec`, `hmv` [W] (over `IoRS`, by `alt_cm_io`). -/
theorem invU_pathObl {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : InvUAccW st ar number p K Locks P) (hdec : InvDecW st ar number p K Locks m0 P)
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

/-- **`PathSide` of the uncut CNodeDelete path (as slhuf's Copy / Mint)**: `huf` [J] in `inv_localPath`'s form (over `IoRS` / `IoWS`, carried to
`InvCMRS` / `InvCMWS` by `cmRS_eq` / `cmWS_eq`), `hra` [W] over `IoRS` (by `alt_cm_io`). -/
theorem invU_pathSide (hK : RegionOK K) (hU : E2E.UserOK K) {P : S → Prop} {q : SProg Bool}
    (hacc : InvUAccW st ar number p K Locks P)
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

/-- **`ReadOnce` of the uncut CNodeDelete path (as slhuf's Copy / Mint)**: accepting entries from `hroA` [W], declining ones from stpost's `hro`
[W] (over `IoRS`, widened by `onceU_monoR`). -/
theorem invU_readOnce {P : S → Prop} {q : SProg Bool} (hroA : InvURoAccW st ar number p K Locks m0 q P)
    (hro : InvRoW st ar number p K Locks m0 q P) :
    ReadOnce st ar q (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) P (InvCMRS (st := st) K Locks) := by
  intro s s' a r hE Al h
  by_cases hac : ∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)
  · exact hroA s s' a r hE hac Al h
  · exact onceU_monoR (fun _ hb => ioRS_cm hb) q ∅ ∅ ∅ s' a (hro s s' a r hE hac (alt_cm_io Al) h) subset_rfl

/-- **The uncut CNodeDelete local path** (slhuf's `inv_localPathCM`, renamed), for any `Pre` `P` giving `IoPre`. Premises: `hA`, `hK` [J], `hU` [J], `hm` [P],
`hPE`, `hacc` [W] (`invCMAccW_of` from `InvCMBlkW` [W]), stpost's `hdec` [W], `hmv` [W], `hra` [W], `huf` [J], and
the program premise `hpz` (`IsProgOn` [P] on `IoRS`'s alternatives, as hpzg delivers it; `NoZero` [W]; `InvRoW` [W];
`InvURoAccW` [W]). -/
noncomputable def inv_localPathU (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hU : E2E.UserOK K) (number : I64) (p : localinv.Plan) (hm : E2E.MasksWr st)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : InvUAccW st ar number p K Locks P) (hdec : InvDecW st ar number p K Locks m0 P)
    (hmv : InvMoveW st ar number p K Locks m0 P) (hra : InvRaW st ar number p K Locks m0 P)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m0 q P ∧ InvURoAccW st ar number p K Locks m0 q P) :
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
  obl := invU_pathObl hPE hacc hdec hmv
  side := invU_pathSide hK hU hacc (hpz.choose_spec.1.mono (fun _ hy => altOf_cm_io hy))
    hpz.choose_spec.2.1 hm hra hA huf
  once := invU_readOnce hpz.choose_spec.2.2.2 hpz.choose_spec.2.2.1
  total := fun s a => inv_total hA number p s a
  masks := hm

end path



section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- **The Copy / Mint local path as an `E2E.Paths` member**: `inv_localPathU` at every layout `K` and memory `m`,
`Pre := SlJAt K ∧ Q K m` (as `inv_pathsK`; `hacc` over the new guard, the other premises as there plus
`InvURoAccW` in `hpz`). -/
noncomputable def inv_pathsKDelU (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hacc : ∀ K m, InvUAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ Q K m s))
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
      InvURoAccW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ Q K m s)) :
    E2E.Paths Unit :=
  fun _ K m hK hU =>
    inv_localPathU (K := K) (m0 := m) (Locks := Locks) ar hA hK hU number p hm
      (P := fun s => SlJAt (L := L) K s ∧ Q K m s) (fun s h => hPE K m s h.1 h.2)
      (hacc K m) (hdec K m) (hmv K m) (hra K m) (fun s b v h => huf K m s b v h.1 h.2) (hpz K m)


/-- (stpost gen 14) **The uncut CNodeDelete local path** (`Q := InvQF`, truncated Deletes included): `inv_pathsKDelU`
with `hacc` from `invUAccW_of2` + `invBlkUW2_of`, `hdec` / `hra` from `invDecW_of` / `invRaW_of` (`hSeen` from
`invSeen_of`), `hmv` from `invMoveW_ofU` + `invBlkGdUW2_of`, `hps` from `invPs_of`. Premises: `hA`, [P] `hm`,
[J] `hvs : InvVsJ`, [J] `hcdt : InvCdtJ`, [J] `hz`, [J] `hbuf : InvBufJ`, [J] `huf`, `hpz` ([P] IsProgOn ∧ [W] NoZero ∧
[W] InvRoW ∧ [W] InvURoAccW). -/
noncomputable def inv_pathsKFU (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st)
    (hvs : ∀ K m, InvVsJ st K (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s))
    (hcdt : ∀ K m, InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s))
    (hz : ∀ K s, SlJAt (L := L) K s → (0#u64) ∉ K.slots)
    (hbuf : ∀ K m s, SlJAt (L := L) K s → InvQF st Cs Ω Sg Ac Locks p K m s → InvBufJ st K s)
    (huf : ∀ K m s b v, SlJAt (L := L) K s → InvQF st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ InvQF st Cs Ω Sg Ac Locks p K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∀ K m, ∃ q : SProg Bool, IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) (IoRS (st := st) K Locks)
        (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)) q ∧ NoZero q ∧
      InvRoW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) ∧
      InvURoAccW st ar number p K Locks m q (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s)) :
    E2E.Paths Unit :=
  inv_pathsKDelU ar hA number p hm (InvQF st Cs Ω Sg Ac Locks p) (fun _ _ _ _ hq => hq.1.1.1)
    (fun K m => invUAccW_of2 hA (fun _ h => h.2.1.1.1)
      (fun s h => invSeen_of (fun K _ s hJ _ => hz K s hJ) K m s h.1 h.2)
      (fun s h => invPs_of K m s h.1 h.2) (invBlkUW2_of hA (hvs K m) (hcdt K m) (hz K) (hbuf K m)))
    (fun K m => invDecW_of hA (fun _ h => h.1.regionOK) (fun _ h => h.1.ioLayA) (fun _ h => h.2.1.1.1)
      (fun s h => invSeen_of (fun K _ s hJ _ => hz K s hJ) K m s h.1 h.2))
    (fun K m => invMoveW_ofU hA (fun _ h => h.1.regionOK) (fun _ h => h.1.userOK) (fun _ h => h.1.ioLayA)
      (fun _ h => h.2.1.1.1) (fun s h => invSeen_of (fun K _ s hJ _ => hz K s hJ) K m s h.1 h.2)
      (fun s h => invPs_of K m s h.1 h.2) (fun _ h => h.2.1.1.2) (hpz K m).choose_spec.1
      (invBlkGdUW2_of hA (hvs K m) (hcdt K m) (hz K) (hbuf K m)))
    (fun K m => invRaW_of hA (fun _ h => h.2.1.1.1)
      (fun s h => invSeen_of (fun K _ s hJ _ => hz K s hJ) K m s h.1 h.2))
    huf hpz

end paths

end Fl4Proofs.P2.PathObl

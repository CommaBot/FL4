/-
# P2 (line unify, gen 2): the CNodeDelete (no PTE lock) path reads no PTE word (`avoidE_delE`)

gen 1's `AvInvW` [W] (P2/E2EPU1W.lean) asks `AvoidP` of the cut `ownV` lift of invj's `invSlotW` path at `QPs`
states, for **every** layout `K` with `RegionOKP` / `UserOKP`. Two findings make that statement unprovable as it
stands, though nothing reads a PTE word at a reachable start:

1. **The program tree is a choice.** `inv_localPathU`'s tree is `hpz.choose`, known only to agree with the body on
   `IoRS`'s alternatives. `AvoidE.prog` asks the agreement on the *cut* set's alternatives (states that may differ at
   PTE words), which a chosen tree need not satisfy. Fix: **`inv_localPathUq`**, the same path with the tree
   `R.invBodyG number p` given explicitly (its four facts are exactly what `inv_pathsKFU2` packs into `hpz`), and
   **`inv_pathDelE`**, the CNodeDelete path (`inv_pathsKFU4`'s arguments) with it.
2. **`QPs` does not keep upper page-table entries out of `K.ptes`.** A stale-mapped frame cap's `unmap_page` walks
   the ASID table and the `L4` / `L3` / `L2` entries (`unmap_nop`). `QPs` excludes the ASID-table / pool words
   (`QPs.tab`) and the kernel globals (`QPs.ks`), but `RegionOKP` / `UserOKP` allow an upper-level entry in
   `K.ptes`; at such a layout the accepted run on the cut store panics. So `AvInvW` is false for such (unreachable)
   layouts. Under pte's reachability convention `K.ptes = ptesR K m1` with `GateAg` (`CvP`, invj's), every PTE word
   is a leaf entry of the current bundle (`ptesR_sub`), and the walk reads no leaf (`SlJAtZ.vsRdX`). Fix: the slot is
   restricted to **`QU := QPs ∧ CvP`** states (`CvP` is kept by user writes, `qU_stab`; at a glue start it follows
   from the epoch data, as for invj's `delPteSlot`).

With these:

* `invSeenRN`, `invPsRN`: the no-PTE plan's seen / invoked-slot words are `IoRSR` words;
* `ioRSR_rsE`: an `IoRSR` word is an `InvCMRS` word off `K.ptes` (`RegionOKP.none`, `KsNoE`);
* **`invBlkN`** (both arms of the decode block on `guard st (rsE ptes InvCMRS s) (InvCMWS s)`: `delAccN` /
  `delFinN` for `length ≥ 2`, invj's `truncAccR` / `truncFinR` otherwise), **`invAccN`** (`inv_acc_genR`);
* **`avoidE_delE`**: `AvoidE (· ∈ K.ptes)` of `inv_pathDelE` restricted to `QU` — acc by `invAccN`, declines by
  invj's `inv_dec_guardRSR` (+ `interp_mono` over the tree), prog by `inv_isProgOnR`. **No premise.**

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelNoPteR
import Fl4Proofs.P2.E2EPU1
import Fl4Proofs.P2.E2EVFl4WIC
import Fl4Proofs.P2.InvCMPathZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section pathq
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type}

/-- (unify gen 2) **`inv_localPathU` with an explicit tree `q`** (its facts as separate hypotheses). -/
noncomputable def inv_localPathUq (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hU : E2E.UserOK K) (number : I64) (p : localinv.Plan) (hm : E2E.MasksWr st)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : InvUAccW st ar number p K Locks P) (hdec : InvDecW st ar number p K Locks m0 P)
    (hmv : InvMoveW st ar number p K Locks m0 P) (hra : InvRaW st ar number p K Locks m0 P)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (q : SProg Bool)
    (hq1 : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q)
    (hq2 : NoZero q) (hq3 : InvRoW st ar number p K Locks m0 q P)
    (hq4 : InvURoAccW st ar number p K Locks m0 q P) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
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
  RS := InvCMRS (st := st) K Locks
  WS := InvCMWS (st := st) K Locks
  DS := IoDS (st := st)
  isProg := hq1.mono (fun _ hy => altOf_cm_io hy)
  obl := invU_pathObl hPE hacc hdec hmv
  side := invU_pathSide hK hU hacc (hq1.mono (fun _ hy => altOf_cm_io hy)) hq2 hm hra hA huf
  once := invU_readOnce hq4 hq3
  total := fun s a => inv_total hA number p s a
  masks := hm

end pathq

section pathD
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (unify gen 2) **The CNodeDelete (no PTE lock) path with the explicit tree `R.invBodyG`**: `inv_pathsKFU4`'s
arguments (`inv_pathsKFU2` / `inv_pathsKFU8` / `inv_pathsKDelU`), `inv_localPathUq` in place of
`inv_localPathU`. Premises as `inv_pathsKFU4`: `hA`, [P] `hm`, `hCs`, [P] `hlk`. -/
noncomputable def inv_pathDelE (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  have hp := inv_isProgOn (Locks := Locks) (m0 := m) hA (P := fun s => SlJAt (L := L) K s ∧
      InvQF st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1)
      (invSlotCNK_of (Q := InvQF st Cs Ω Sg Ac Locks p) (fun _ _ _ _ hq => hq) K m)
      (inv_isProg S number p)
  inv_localPathUq (K := K) (m0 := m) (Locks := Locks) ar hA hK hU number p hm
    (P := fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1)
    (invUAccW_of2 hA (fun _ h => h.2.1.1.1)
      (fun s h => invSeen_of (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2)
      (fun s h => invPs_of K m s h.1 h.2)
      (invBlkUW2_of8 hA (invVsJ_of (fun _ h => h.1)) (invCdtJ_of (fun _ h => h.1)) (hz_of K)
        (fun _ hJ _ => invBufJ8_of hJ)))
    (invDecW_of hA (fun _ h => h.1.regionOK) (fun _ h => h.1.ioLayA) (fun _ h => h.2.1.1.1)
      (fun s h => invSeen_of (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2))
    (invMoveW_ofU hA (fun _ h => h.1.regionOK) (fun _ h => h.1.userOK) (fun _ h => h.1.ioLayA)
      (fun _ h => h.2.1.1.1) (fun s h => invSeen_of (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2)
      (fun s h => invPs_of K m s h.1 h.2) (fun _ h => h.2.1.1.2) hp
      (invBlkGdUW2_of8 hA (invVsJ_of (fun _ h => h.1)) (invCdtJ_of (fun _ h => h.1)) (hz_of K)
        (fun _ hJ _ => invBufJ8_of hJ)))
    (invRaW_of hA (fun _ h => h.2.1.1.1)
      (fun s h => invSeen_of (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2))
    (fun s b v h => hufQF_of2 (ioPre_wr_hIw (Ω := Ω) (Sg := Sg) (Ac := Ac) hCs) hlk K m s b v h.1 h.2)
    (R.invBodyG number p) hp (inv_noZero number p)
    (invRoW_of hA (fun _ h => h.2.1.1.1)
      (fun s h => invSeen_of (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2) hp (inv_noZero number p))
    (invURoAccW_of hm (PL := fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s)
      (fun _ h hL => ⟨h.1, h.2, hL⟩) hp (inv_noZero number p)
      (invAccW_of2 hA (fun _ h => h.2.1.1.1.1)
        (fun s h => invSeen_of (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2.1)
        (fun s h => invPs_of K m s h.1 h.2.1)
        (invBlkW2_of hA (invVsJ_of (fun _ h => h.1)) (invCdtJ_of (fun _ h => h.1)) (hz_of K)))
      (invURoTrW_of hA hm K m))

end pathD

section seenN
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64} {s : S}

/-- The no-PTE plan's seen words are `IoRSR` words (`invSeen_of` with `IoPre.lockSlotR`). -/
theorem invSeenRN (hJ : SlJAt (L := L) K s) (hq : InvQF st Cs Ω Sg Ac Locks p K μ s) :
    ∀ x, SeenW p x → IoRSR st K Locks s x := by
  intro x hx
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, C, -, -, -, -, -, -, -, hdK, -, hLd, -, -, hSn, -⟩ :=
    del_core hq
  have hd0 : dest ≠ 0#u64 := fun e => hz_of K s hJ (e ▸ hdK)
  obtain ⟨o, ho, rfl⟩ := hSn x hx
  have hov : o.val < 32 ∧ o.val % 8 = 0 := by
    rcases ho with rfl | rfl | rfl | rfl <;> simp [layout.cte.CAP0, layout.cte.CAP1, layout.cte.PREV, layout.cte.NEXT]
  exact PE.lockSlotR hdK (hLd hd0) hov.1 hov.2

/-- The no-PTE plan's invoked slot's cap words are `IoRSR` words. -/
theorem invPsRN (hq : InvQF st Cs Ω Sg Ac Locks p K μ s) :
    IoRSR st K Locks s p.slot ∧ IoRSR st K Locks s (core.num.U64.wrapping_add p.slot 8#u64) := by
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcap, hsK, -⟩ := del_core hq
  exact PE.slotR hsK (Or.inr (cap_not_nof hcap (Or.inl ⟨_, _, _, _, rfl⟩)))

end seenN

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame)

section rs
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutP} {Locks : S → U64 → Prop} {s : S}

/-- **An `IoRSR` word is an `InvCMRS` word off the PTE set.** -/
theorem ioRSR_rsE (hK : RegionOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) {x : U64}
    (h : IoRSR st K.toKLayout Locks s x) :
    rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s x := by
  refine ⟨ioRS_cm h.1, fun hx => ?_⟩
  rcases h.2 with hr | ⟨o, ho, rfl⟩
  · exact hr (hK.none _ hx)
  · exact hks o ho hx

/-- **An aligned user word is an `InvCMRS` word off the PTE set.** -/
theorem userW_rsE (hU : UserOKP K) {x : U64} (h : UserW K.toKLayout x) :
    rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s x :=
  ⟨⟨h.1, Or.inl h.2⟩, fun hp => (hU.kern _ hp).2 h.2⟩

end rs

section blk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (unify gen 2) **Both arms of the no-PTE Delete decode block on the store guarded to `InvCMRS` off the PTE set**
(module docstring). No premise. -/
theorem invBlkN {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) {s : S}
    (hE : SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s)
    (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) (hcv : CvP st K s)
    {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A} {buf length : U64}
    {cap : capability.Cap} (emi : msg.msg_info st s (L.curW s) = ok info)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hl : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (y : (core.result.Result Unit error.Exc) × S × A)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) ar s2 a1
        info.label length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
      z.2.2 = core.result.Result.Ok () ∧
      FinOK (L := L) (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s))
        (IoRSR st K.toKLayout Locks s) (InvCMWS (st := st) K.toKLayout Locks s) ar s z.1 z.2.1 := by
  obtain ⟨hJ, hq⟩ := hE
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_core hq
  have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  have hW : IoWr st (InvCMWS (st := st) K.toKLayout Locks s) K.heap.scBits s := PE.ioWr.mono (fun _ h => ioWS_cm h)
  by_cases hlen : length < 2#u64
  · obtain ⟨hdec, hrep⟩ := truncAccR (R := rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
      (gS := guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) hA PE
      (fun _ h => ioRSR_rsE hK hks h) (fun _ h => userW_rsE hU h) hW
      (fun _ h => ⟨h.1, Or.inl h.2⟩) hcs hsK (invBufJ8_of hJ) C hcap hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
          (InvCMWS (st := st) K.toKLayout Locks s)) st (IoRSR st K.toKLayout Locks s) :=
      grd_sub (fun _ h => ioRSR_rsE hK hks h)
    obtain ⟨h1, h2⟩ :=
      truncFinR (gS := guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) hA PE hW
      (SWr.of_W (ioWS_cm PE.stw.2)) hcs hsK (invBufJ8_of hJ) C hcap hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · have hvsP := invVsJ_of (st := st)
      (P := fun s => SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) (fun _ h => h.1)
    have E := delEnt_of (P := fun s => SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s)
      ⟨hJ, hq⟩ hq hvsP (invCdtJ_of (fun _ h => h.1)) (hz_of _ s hJ)
    obtain ⟨m1, hconv, hag⟩ := hcv
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
    have hsub : ∀ b, b ∈ K.ptes → Fl4Proofs.P3.Vs.PtW Zx.L1 b := fun b hb =>
      ptesR_sub B hag b (by rw [← hconv]; exact hb)
    obtain ⟨hdec, hrep⟩ := delAccN (R := rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
      (X := (· ∈ K.ptes))
      (gS := guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) hA PE hW (fun _ h => ioWS_cm h) E hsK hlen (B.vsJX hsub)
      (fun b hb => ⟨(hU.kern b hb).1, hK.none b hb, (hU.kern b hb).2⟩)
      (fun b h hx => ⟨ioRS_cm h, hx⟩) C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
          (InvCMWS (st := st) K.toKLayout Locks s)) st (IoRSR st K.toKLayout Locks s) :=
      grd_sub (fun _ h => ioRSR_rsE hK hks h)
    obtain ⟨h1, h2⟩ :=
      delFinN (gS := guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) hA PE hW (ioWS_cm PE.stw.2) E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvsP s sl fp rt asid va
        ⟨⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩, hq⟩ hsl hc hA)
      C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- (unify gen 2) **The accepted no-PTE Delete run reads no PTE word**: it runs on
`guard st (rsE ptes InvCMRS s) (InvCMWS s)` as on `st`. No premise. -/
theorem invAccN {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) {s s' : S} {a a' : A}
    (hE : SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s)
    (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) (hcv : CvP st K s)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) ar s a number p = ok (true, s', a') := by
  have PE := hE.2.1.1.1
  haveI : GRd (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) st (IoRSR st K.toKLayout Locks s) :=
    grd_sub (fun _ h => ioRSR_rsE hK hks h)
  exact inv_acc_genR (W := InvCMWS (st := st) K.toKLayout Locks s) hA PE (PE.ioWr.mono (fun _ h => ioWS_cm h))
    (invSeenRN hE.1 hE.2) (invPsRN hE.2)
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => invBlkN hA hK hU hE hks hcv emi hc hl hk y hy) h

end blk

section av
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- **The restriction of the no-PTE invocation slots**: `QPs` and pte's reachability convention `CvP`. -/
def QU (K : KLayoutP) (s : S) : Prop := QPs K st s ∧ CvP st K s

/-- `QU` is kept by an aligned user-word write. -/
theorem qU_wr {K : KLayoutP} {s : S} {b v : U64} (h : QU st K s) (hb : b ∈ K.user) (ha : Aligned b) :
    QU st K (L.wr s b v) := by
  obtain ⟨hq, m1, hc, hag⟩ := h
  refine ⟨hq.wr (Or.inl hb) ha, m1, hc, fun w hr hn hu hw => ?_⟩
  rw [Fl4Proofs.P3.Notif.rd_wr_ne ha hw (fun e => hu (e ▸ hb))]
  exact hag w hr hn hu hw

variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar)

/-- (unify gen 2) **The no-PTE CNodeDelete path, restricted to `QU`, reads no PTE word** (module docstring).
No premise. -/
theorem avoidE_delE {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) :
    AvoidE (· ∈ K.ptes) ((inv_pathDelE (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number p
      hm hCs hlk K.toKLayout m hK.base.base hU.base.base).restrQ (fun s => QU st K s)
      (fun _ _ _ _ h hb ha => qU_wr h hb ha)) := by
  have hSC : InvSlotCN st K.toKLayout p
      (fun s => (SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QU st K s) :=
    fun s h => invSlotCNK_of (Q := InvQF st Cs Ω Sg Ac Locks p) (fun _ _ _ _ hq => hq) K.toKLayout m s h.1
  have hpR := inv_isProgOnR (Locks := Locks) (m0 := m) hA
    (P := fun s => (SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QU st K s)
    (fun _ h => h.1.2.1.1.1) hSC (inv_isProg S number p)
  refine ⟨?_, ?_, ?_⟩
  · intro s a r hs hr hb
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hs' : (SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QU st K s := hs
    have hr' : syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) := hr
    show syscall.handle_invocation_local (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) ar s a number p = ok (true, s1, a1)
    exact invAccN hA hK hU hs'.1 hs'.2.1.ks hs'.2.2 hr'
  · intro s a r hs0 hr hn s' r' hA' h'
    have hs : (SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QU st K s := hs0
    have Al : Alt st (InvCMRS (st := st) K.toKLayout Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' := hA'
    have AlR := Al.anti (R' := IoRSR st K.toKLayout Locks s) (fun x hx => ioRS_cm hx.1)
    have hr' : syscall.handle_invocation_local st ar s a number p = ok r := hr
    have h'' : syscall.handle_invocation_local st ar s' a number p = ok r' := h'
    have g := inv_dec_guardRSR hA hs.1.2.1.1.1 (invSeenRN hs.1.1 hs.1.2) AlR hr' hn h''
    have e := fun (st' : machine.Store S) (N : Narrow st st') => hpR st' N s' ⟨s, hs, AlR⟩ a
    show syscall.handle_invocation_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a number p = ok r'
    exact (e _ (Narrow.guard _ _ _)).trans (interp_mono (st := st)
      (fun q hq hp => (ioRSR_rsE hK hs.2.1.ks hq).2 hp)
      (fun _ h => h) _ (inv_noZero number p) s' a r' ((e _ (Narrow.guard _ _ _)).symm.trans g))
  · intro st' N σ g a
    obtain ⟨s, hs0, hAc⟩ := g
    have hs : (SlJAt (L := L) K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QU st K s := hs0
    have hAc' : Alt st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user) s σ := hAc
    exact hpR st' N σ ⟨s, hs, hAc'.anti (R' := IoRSR st K.toKLayout Locks s)
      (fun x hx => ioRSR_rsE hK hs.2.1.ks hx)⟩ a

end av

end Fl4Proofs.P2.E2EP

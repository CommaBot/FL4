/-
# P2 (line unify, gen 2): the Copy / Mint path reads no PTE word (`avoidE_cmE`)

As for the CNodeDelete path (P2/E2EPU2D.lean): slhuf's `inv_localPathCM` takes its tree by choice (`hpz.choose`),
so gen 1's `AvCMW` [W] cannot be shown for the program premise on the cut set's alternatives. **`inv_localPathCMq`**
is the same path with the tree `R.invBodyG number p` explicit (its facts are `inv_hpzCM`'s), **`inv_pathCME`** the
Copy / Mint path at `inv_pathsKCM7`'s arguments with it. The Copy / Mint run walks no page table; its reads are
`IoRSR` words and aligned user words, so no PTE word (`ioRSR_rsE`, `userW_rsE`):

* `cmSeenRN`, `cmPsRN`: the Copy / Mint plan's seen / invoked-slot words are `IoRSR` words;
* **`invCMBlkN`** (the decode block on `guard st (rsE ptes InvCMRS s) (InvCMWS s)`: `cmAccZR` / `cmFin8R`),
  **`invCMAccN`** (`inv_acc_gen3R`);
* **`avoidE_cmE`**: `AvoidE (· ∈ K.ptes)` of `inv_pathCME` restricted to `QU` (acc `invCMAccN`; declines
  `inv_dec_guardRSR`; prog `inv_isProgOnR`). The `CvP` half of `QU` is not used here (only `QPs.ks`); the
  restriction is the Delete slot's so both slots share their start lemma. **No premise.**

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvCMNoPteR
import Fl4Proofs.P2.E2EPU2D
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

/-- (unify gen 2) **`inv_localPathCM` with an explicit tree `q`**. -/
noncomputable def inv_localPathCMq (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hU : E2E.UserOK K) (number : I64) (p : localinv.Plan) (hm : E2E.MasksWr st)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hacc : InvCMAccW st ar number p K Locks P) (hdec : InvDecW st ar number p K Locks m0 P)
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
    (hq4 : InvCMRoAccW st ar number p K Locks m0 q P) :
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
  obl := invCM_pathObl hPE hacc hdec hmv
  side := invCM_pathSide hK hU hacc (hq1.mono (fun _ hy => altOf_cm_io hy)) hq2 hm hra hA huf
  once := invCM_readOnce hq4 hq3
  total := fun s a => inv_total hA number p s a
  masks := hm

end pathq

section pathC
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (unify gen 2) **The Copy / Mint path with the explicit tree `R.invBodyG`**: `inv_pathsKCM7`'s arguments
(`inv_pathsKCM6` / `inv_pathsKCM2` / `inv_pathsKCM`, `inv_hpzCM`'s facts), `inv_localPathCMq` in place of
`inv_localPathCM`. Premises as `inv_pathsKCM7`: `hA`, [P] `hm`, `hCs`, [P] `hlk`. -/
noncomputable def inv_pathCME (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  have hp := inv_isProgOn (Locks := Locks) (m0 := m) hA (P := fun s => SlJAt (L := L) K s ∧
      InvQCMW st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1) (cmSC_ofZ K m) (inv_isProg S number p)
  have hacc : InvCMAccW st ar number p K Locks (fun s => SlJAt (L := L) K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K m s) :=
    invUAccW_of3 hA (fun _ h => h.2.1.1.1)
      (fun s h => cmSeen_ofW (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2)
      (fun s h => cmPs_ofW K m s h.1 h.2)
      (invCMBlkUW3_ofZ hA (invCdtJ_of (fun _ h => h.1)) (hz_of K) (fun _ h _ => invBufJ8_of h)
        (fun _ h _ => invBufSJ8_of h))
  have hcdt : InvCdtJ st K (fun s => SlJAt (L := L) K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K m s) :=
    invCdtJ_of (fun _ h => h.1)
  have hdo := invCMDecOnceW_of (number := number) hA
    (P := fun s => SlJAt (L := L) K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1)
    (fun _ h => h.2.1.2.2.1)
    (fun s h => cmEnt_ofW h h.2 hcdt (hz_of K s h.1)) (fun _ h => cmSl_ofW h.2)
    (invCMTailW_of8 hA (fun _ h => h.2.1.1.1) (fun _ h => h.2.1.2.2.1)
      (fun s h => cmEnt_ofW h h.2 hcdt (hz_of K s h.1)) (fun _ h => cmSl_ofW h.2)
      (fun s h => invBufJ8_of h.1))
  inv_localPathCMq (K := K) (m0 := m) (Locks := Locks) ar hA hK hU number p hm
    (P := fun s => SlJAt (L := L) K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1)
    hacc
    (invDecW_of hA (fun _ h => h.1.regionOK) (fun _ h => h.1.ioLayA) (fun _ h => h.2.1.1.1)
      (fun s h => cmSeen_ofW (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2))
    (invMoveW_ofU3 hA (fun _ h => h.1.regionOK) (fun _ h => h.1.userOK) (fun _ h => h.1.ioLayA)
      (fun _ h => h.2.1.1.1) (fun s h => cmSeen_ofW (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2)
      (fun s h => cmPs_ofW K m s h.1 h.2) (fun _ h => h.2.1.1.2) hp
      (invCMBlkGdUW3_ofZ hA (invCdtJ_of (fun _ h => h.1)) (hz_of K) (fun _ h _ => invBufJ8_of h)
        (fun _ h _ => invBufSJ8_of h)))
    (invRaW_of hA (fun _ h => h.2.1.1.1)
      (fun s h => cmSeen_ofW (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2))
    (fun s b v h => hufQCMW_of (ioPre_wr_hIw (Ω := Ω) (Sg := Sg) (Ac := Ac) hCs) hlk K m s b v h.1 h.2)
    (R.invBodyG number p) hp (inv_noZero number p)
    (invRoW_of hA (fun _ h => h.2.1.1.1)
      (fun s h => cmSeen_ofW (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2) hp (inv_noZero number p))
    (invCMRoAccW_of_ent hm hacc (hp.mono fun _ hy => altOf_cm_io hy) (inv_noZero number p)
      (invCM_entOnce hA (fun _ h => h.2.1.1.1)
        (fun s h => cmSeen_ofW (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2)
        (fun s h => cmPs_ofW K m s h.1 h.2) hdo))

end pathC

section seenC
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64} {s : S}

/-- The Copy / Mint plan's seen words are `IoRSR` words (`cmSeen_ofW` with `IoPre.lockSlotR`). -/
theorem cmSeenRN (hJ : SlJAt (L := L) K s) (hq : InvQCMW st Cs Ω Sg Ac Locks p K μ s) :
    ∀ x, SeenW p x → IoRSR st K Locks s x := by
  intro x hx
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, hdK, -, hLd, hsK, -, hLs, -, hSn⟩ := cm_coreW hq
  have hd0 : dest ≠ 0#u64 := fun e => hz_of K s hJ (e ▸ hdK)
  have hsr0 : src ≠ 0#u64 := fun e => hz_of K s hJ (e ▸ hsK)
  rcases hSn x hx with rfl | rfl | rfl | rfl
  · exact (PE.lockSlotR hdK (hLd hd0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0]))
  · exact (PE.lockSlotR hsK (hLs hsr0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0]))
  · exact (PE.lockSlotR hsK (hLs hsr0) (by simp [layout.cte.CAP1]) (by simp [layout.cte.CAP1]))
  · exact (PE.lockSlotR hsK (hLs hsr0) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]))

/-- The Copy / Mint plan's invoked slot's cap words are `IoRSR` words. -/
theorem cmPsRN (hq : InvQCMW st Cs Ω Sg Ac Locks p K μ s) :
    IoRSR st K Locks s p.slot ∧ IoRSR st K Locks s (core.num.U64.wrapping_add p.slot 8#u64) := by
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcap, hsK, -⟩ := cm_coreW hq
  exact PE.slotR hsK (Or.inr (cap_not_nof hcap (Or.inl ⟨_, _, _, _, rfl⟩)))

end seenC

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame)

section blk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (unify gen 2) **The Copy / Mint decode block on the store guarded to `InvCMRS` off the PTE set** (module
docstring). No premise. -/
theorem invCMBlkN {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) {s : S}
    (hE : SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s)
    (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV)
    {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A} {buf length : U64}
    {cap : capability.Cap} (emi : msg.msg_info st s (L.curW s) = ok info)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hb : msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf)
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
  obtain ⟨hJ, hqf⟩ := hE
  have PE := hqf.1.1.1
  have hlb := hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi
  have E := cmEnt_ofW (P := fun s => SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s)
    ⟨hJ, hqf⟩ hqf (invCdtJ_of (fun _ h => h.1)) (hz_of _ s hJ)
  have hsl := cmSl_ofW hqf
  have hbC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K.toKLayout (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) :=
    invBufSJ8_of hJ buf (by rw [← lib_prefix hA PE C false]; exact hb)
  have hW : IoWr st (InvCMWS (st := st) K.toKLayout Locks s) K.heap.scBits s := PE.ioWr.mono (fun _ h => ioWS_cm h)
  obtain ⟨hdec, hrep⟩ := cmAccZR (R := rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
    (gS := guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) hA PE
    (fun _ h => ioRSR_rsE hK hks h) (fun _ h => userW_rsE hU h) hW (fun _ h => ⟨h.1, Or.inl h.2⟩)
    (fun q o hq hlk ho h8 _ hw => ioWS_cm ((PE.lockSlot hq hlk ho h8).2 hw))
    (fun q hq hlk hT hn x v _ => by
      have h := (PE.lockSlot hq hlk (o := 0#u64) (by simp) (by simp)).2 (Or.inr ⟨hT, hn⟩)
      rw [wadd_zero (PE.lay.slot8 q hq).2] at h
      exact gst_write (ioWS_cm h))
    (fun _ _ => SWr.of_W (ioWS_cm PE.stw.2)) E hsl (cmDestZ_of hqf) hbC (invBufJ8_of hJ) hlb C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  haveI : GRd (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) st (IoRSR st K.toKLayout Locks s) :=
    grd_sub (fun _ h => ioRSR_rsE hK hks h)
  obtain ⟨h1, h2⟩ :=
    cmFin8R (gS := guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) hA PE hW (SWr.of_W (ioWS_cm PE.stw.2)) E hsl (invBufJ8_of hJ)
      hlb C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

/-- (unify gen 2) **The accepted Copy / Mint run reads no PTE word**. No premise. -/
theorem invCMAccN {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) {s s' : S} {a a' : A}
    (hE : SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s)
    (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) ar s a number p = ok (true, s', a') := by
  have PE := hE.2.1.1.1
  haveI : GRd (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) st (IoRSR st K.toKLayout Locks s) :=
    grd_sub (fun _ h => ioRSR_rsE hK hks h)
  exact inv_acc_gen3R (W := InvCMWS (st := st) K.toKLayout Locks s) hA PE (PE.ioWr.mono (fun _ h => ioWS_cm h))
    (cmSeenRN hE.1 hE.2) (cmPsRN hE.2)
    (fun info nx s1 s2 a1 buf length cap emi hc hb hl hk y hy => invCMBlkN hA hK hU hE hks emi hc hb hl hk y hy) h

end blk

section av
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar)

/-- (unify gen 2) **The Copy / Mint path, restricted to `QU`, reads no PTE word** (module docstring). No premise. -/
theorem avoidE_cmE {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) :
    AvoidE (· ∈ K.ptes) ((inv_pathCME (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number p
      hm hCs hlk K.toKLayout m hK.base.base hU.base.base).restrQ (fun s => QU st K s)
      (fun _ _ _ _ h hb ha => qU_wr h hb ha)) := by
  have hSC : InvSlotCN st K.toKLayout p
      (fun s => (SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QU st K s) :=
    fun s h => cmSC_ofZ K.toKLayout m s h.1
  have hpR := inv_isProgOnR (Locks := Locks) (m0 := m) hA
    (P := fun s => (SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QU st K s)
    (fun _ h => h.1.2.1.1.1) hSC (inv_isProg S number p)
  refine ⟨?_, ?_, ?_⟩
  · intro s a r hs hr hb
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hs' : (SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QU st K s := hs
    have hr' : syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) := hr
    show syscall.handle_invocation_local (guard st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) ar s a number p = ok (true, s1, a1)
    exact invCMAccN hA hK hU hs'.1 hs'.2.1.ks hr'
  · intro s a r hs0 hr hn s' r' hA' h'
    have hs : (SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QU st K s := hs0
    have Al : Alt st (InvCMRS (st := st) K.toKLayout Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' := hA'
    have AlR := Al.anti (R' := IoRSR st K.toKLayout Locks s) (fun x hx => ioRS_cm hx.1)
    have hr' : syscall.handle_invocation_local st ar s a number p = ok r := hr
    have h'' : syscall.handle_invocation_local st ar s' a number p = ok r' := h'
    have g := inv_dec_guardRSR hA hs.1.2.1.1.1 (cmSeenRN hs.1.1 hs.1.2) AlR hr' hn h''
    have e := fun (st' : machine.Store S) (N : Narrow st st') => hpR st' N s' ⟨s, hs, AlR⟩ a
    show syscall.handle_invocation_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a number p = ok r'
    exact (e _ (Narrow.guard _ _ _)).trans (interp_mono (st := st)
      (fun q hq hp => (ioRSR_rsE hK hs.2.1.ks hq).2 hp)
      (fun _ h => h) _ (inv_noZero number p) s' a r' ((e _ (Narrow.guard _ _ _)).symm.trans g))
  · intro st' N σ g a
    obtain ⟨s, hs0, hAc⟩ := g
    have hs : (SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QU st K s := hs0
    have hAc' : Alt st (rsE (· ∈ K.ptes) (InvCMRS (st := st) K.toKLayout Locks) s) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user) s σ := hAc
    exact hpR st' N σ ⟨s, hs, hAc'.anti (R' := IoRSR st K.toKLayout Locks s)
      (fun x hx => ioRSR_rsE hK hs.2.1.ks hx)⟩ a

end av

end Fl4Proofs.P2.E2EP

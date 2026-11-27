/-
# P2 (line invj, generation 7): `acc` of the Delete PTE-arm path under rule 8 (`invAccPP`)

The ownP path's read / write sets and entry states, and its `PathObl.acc`:

* **`InvRSP` / `InvWSP`**: slhuf's user-word sets `InvCMRS` / `InvCMWS` with `IoRSP` / `IoWSP` in place of
  `IoRS` / `IoWS` (aligned user words — a truncated Delete's error reply writes the caller's IPC buffer — and the
  read set without the unlocked leaves, the write set with the locked ones);
* **`CvP`**: pte's reachability convention at the entry state (`K.ptes = ptesR K m1` and `GateAg` for some `m1`);
  **`PreP`**: `SlJAt K ∧ InvQFP … ∧ CvP` (the PTE arm's plan facts, gen 4–5);
* `invSeenR_of`, `invPsR_of`: the seen words (`dest`'s four words, locked) and the invoked slot's cap words are
  `IoRSR` words;
* **`invBlkPP`**: both arms of the decode block on `guard st (InvRSP s) (InvWSP s)`, `FinOK` over `IoRSR s` —
  `length ≥ 2` by `delAccPP` (gen 6) / `delFinR`, `length < 2` by `truncAccR` / `truncFinR` (`InvBufJ8` from
  `invBufJ8_of`);
* **`invAccPP`**: the accepted run on `guard st (InvRSP s) (InvWSP s)` ends as the real one (`inv_acc_genR`).

Inputs: `RegionOKP K`, `UserOKP K`, `K.vcpus = ∅` (the `PathsP` layout facts) and `PreP`. No named premise. New
module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteAccR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame)

section sets
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- **The ownP path's read set**: aligned user words and `IoRSP`. -/
def InvRSP (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ (x ∈ K.user ∨ IoRSP st K Locks s x)

variable (st) in
/-- **The ownP path's write set**: aligned user words and `IoWSP`. -/
def InvWSP (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  Aligned x ∧ (x ∈ K.user ∨ IoWSP st K Locks s x)

variable (st) in
/-- **pte's reachability convention at the entry state** (module docstring). -/
def CvP (K : KLayoutP) (s : S) : Prop := ∃ m1 : U64 → U64, K.ptes = ptesR K m1 ∧ GateAg st K m1 s

variable (st) in
/-- **The entry states of the PTE-arm path** at `(K, m)`. -/
def PreP (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayoutP) (m : U64 → U64)
    (s : S) : Prop :=
  SlJAt (L := L) K.toKLayout s ∧ InvQFP st Cs Ω Sg Ac Locks p K.toKLayout m s ∧ CvP st K s

variable {K : KLayoutP} {Locks : S → U64 → Prop} {s : S} {x : U64}

theorem ioRSP_inv (h : IoRSP st K Locks s x) : InvRSP st K Locks s x := ⟨h.1.1, Or.inr h⟩

theorem ioWS_inv (h : IoWS (st := st) K.toKLayout Locks s x) : InvWSP st K Locks s x := ⟨h.1, Or.inr (Or.inl h)⟩

end sets

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64} {s : S}

/-- The seen words of the PTE arm's plan are `IoRSR` words (`dest`'s four words, `dest` locked). -/
theorem invSeenR_of (hJ : SlJAt (L := L) K s) (hq : InvQFP st Cs Ω Sg Ac Locks p K μ s) :
    ∀ x, SeenW p x → IoRSR st K Locks s x := by
  intro x hx
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, e, C, -, -, -, -, -, -, -, hdK, -, hLd, -, -, hSn, -⟩ :=
    del_coreP hq
  have hd0 : dest ≠ 0#u64 := fun e => hz_of K s hJ (e ▸ hdK)
  obtain ⟨o, ho, rfl⟩ := hSn x hx
  have hov : o.val < 32 ∧ o.val % 8 = 0 := by
    rcases ho with rfl | rfl | rfl | rfl <;> simp [layout.cte.CAP0, layout.cte.CAP1, layout.cte.PREV, layout.cte.NEXT]
  exact PE.lockSlotR hdK (hLd hd0) hov.1 hov.2

/-- The invoked slot's cap words are `IoRSR` words. -/
theorem invPsR_of (hq : InvQFP st Cs Ω Sg Ac Locks p K μ s) :
    IoRSR st K Locks s p.slot ∧ IoRSR st K Locks s (core.num.U64.wrapping_add p.slot 8#u64) := by
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcap, hsK, -⟩ := del_coreP hq
  exact PE.slotR hsK (Or.inr (cap_not_nof hcap (Or.inl ⟨_, _, _, _, rfl⟩)))

end ent

section blk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (invj gen 7) **Both arms of the PTE-arm decode block on `guard st (InvRSP s) (InvWSP s)`** (module
docstring). No premise. -/
theorem invBlkPP {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) {s : S} (hE : PreP st Cs Ω Sg Ac Locks p K m s)
    {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A} {buf length : U64}
    {cap : capability.Cap} (emi : msg.msg_info st s (L.curW s) = ok info)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hl : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (y : (core.result.Result Unit error.Exc) × S × A)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (guard st (InvRSP st K Locks s) (InvWSP st K Locks s)) ar s2 a1
        info.label length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (guard st (InvRSP st K Locks s) (InvWSP st K Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
      z.2.2 = core.result.Result.Ok () ∧
      FinOK (L := L) (guard st (InvRSP st K Locks s) (InvWSP st K Locks s))
        (IoRSR st K.toKLayout Locks s) (InvWSP st K Locks s) ar s z.1 z.2.1 := by
  obtain ⟨hJ, hq, m1, hc, hag⟩ := hE
  have PE := hq.1.1.1
  have hks := ksNoE_conv hc
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hq
  have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  have hW : IoWr st (InvWSP st K Locks s) K.heap.scBits s := PE.ioWr.mono (fun _ h => ioWS_inv h)
  by_cases hlen : length < 2#u64
  · obtain ⟨hdec, hrep⟩ := truncAccR (R := InvRSP st K Locks s) (gS := guard st (InvRSP st K Locks s) (InvWSP st K Locks s)) hA PE
      (fun _ h => ioRSP_inv (ioRSR_P hK hks h)) (fun _ h => ⟨h.1, Or.inl h.2⟩) hW
      (fun _ h => ⟨h.1, Or.inl h.2⟩) hcs hsK (invBufJ8_of hJ) C hcap hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := haveI : (GRd (guard st (InvRSP st K Locks s) (InvWSP st K Locks s)) st
        (IoRSR st K.toKLayout Locks s)) := grd_sub (fun _ h => ioRSP_inv (ioRSR_P hK hks h))
      truncFinR (gS := guard st (InvRSP st K Locks s) (InvWSP st K Locks s)) hA PE hW
      (SWr.of_W (ioWS_inv PE.stw.2)) hcs hsK (invBufJ8_of hJ) C hcap hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · have E := delEntP_of (P := fun s => SlJAt (L := L) K.toKLayout s) hJ hq (invCdtJ_of (fun _ h => h))
      (hz_of _ s hJ)
    have hvs := invVsJ_of (st := st) (P := fun s => SlJAt (L := L) K.toKLayout s) (fun _ h => h)
    have hlf := invLeafJ_of (st := st) (P := fun s => SlJAt (L := L) K.toKLayout s) (fun _ h => h) s hJ
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
    obtain ⟨hdec, hrep⟩ := haveI : (GRd (guard st (InvRSP st K Locks s) (InvWSP st K Locks s)) st
        (IoRSP st K Locks s)) := grd_sub (fun _ h => ioRSP_inv h)
      delAccPP (gS := guard st (InvRSP st K Locks s) (InvWSP st K Locks s)) hA B hag hc nv
      hK hU PE hW (fun b h => ⟨ioWSP_aligned hU h, Or.inr h⟩) E hsK hlen C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := haveI : (GRd (guard st (InvRSP st K Locks s) (InvWSP st K Locks s)) st
        (IoRSR st K.toKLayout Locks s)) := grd_sub (fun _ h => ioRSP_inv (ioRSR_P hK hks h))
      delFinR (gS := guard st (InvRSP st K Locks s) (InvWSP st K Locks s)) hA PE hW
      (ioWS_inv PE.stw.2) E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ hsl hc hA)
      hlf C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- (invj gen 7) **`acc` of the PTE-arm path under rule 8**: an accepted run on `guard st (InvRSP s) (InvWSP s)`
ends as the real one (module docstring). No premise. -/
theorem invAccPP {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) {s s' : S} {a a' : A}
    (hE : PreP st Cs Ω Sg Ac Locks p K m s)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local (guard st (InvRSP st K Locks s) (InvWSP st K Locks s)) ar s a number p =
      ok (true, s', a') := by
  have hq := hE.2.1
  have PE := hq.1.1.1
  have hks := ksNoE_conv hE.2.2.choose_spec.1
  haveI : GRd (guard st (InvRSP st K Locks s) (InvWSP st K Locks s)) st (IoRSR st K.toKLayout Locks s) :=
    grd_sub (fun _ h => ioRSP_inv (ioRSR_P hK hks h))
  exact inv_acc_genR (W := InvWSP st K Locks s) hA PE (PE.ioWr.mono (fun _ h => ioWS_inv h))
    (invSeenR_of hE.1 hq) (invPsR_of hq)
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => invBlkPP hA hK hU nv hE emi hc hl hk y hy) h

end blk

end Fl4Proofs.P2.E2EP

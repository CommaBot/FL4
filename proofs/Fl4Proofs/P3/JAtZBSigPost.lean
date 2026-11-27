/-
P3 (line mmuAD, gen 35): **the badge-only notification write over `JAtZB`** — ScSignalJ's `JAtZ.signal_badge_post`
with `JAtZ` → `JAtZB` (the joint invariant without `JExt`), produced by `scratch/mmu32_jatzb_gen.py
signal_badge_post` and filtered to the declarations not yet stated over `JAtZB`: `JAtZB.deadP_nfr` (XTopJointFin),
`JAtZB.nwrite_notDbg` (LiveFrame), **`JAtZB.signal_badge_post`**. Edits: the post `JAtZ (Z.mv Z.G V')` → `JAtZB Z` (the original's witness is `Z.vs`, and `Z.mv Z.G Z.vs` is `Z` by structure eta, as gen 31's `reg_frameFZ`); the proofs are
the originals' (`JAtZB.cs_frameI` of P3/JAtZV3Sched takes the same arguments as `JAtZ.cs_frameI` here).

It is the common step of the notification writes the VM epoch needs: `send_signal`'s badge-only branches (incl.
the `RunningVM` thread whose VMEnter the signal does not complete, P3/JAtZV3SigVm) and `vcpu::check`'s bound
notification made idle (P3/JAtZV3Check). No premise; no existing statement changed.
-/
import Fl4Proofs.P3.JAtZBFire
import Fl4Proofs.P3.ScSignalJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
variable {Lst : U64 → List U64} {D : Set U64}

-- from Fl4Proofs/P3/XTopJointFin.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across a step with the spec frame `NFr`** and the
footprint `FinW` (`deadP_keep`'s facts: a dead TCB's state and null bound
notification kept, a dead notification not waiting and unbound). -/
theorem JAtZB.deadP_nfr {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {qq : Bool} {r : Fl4Spec.ObjRef} {s3 : S}
    {σ3 : Fl4Spec.State Unit} (F : Sched.NFr qq r σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx h0 => ?_)
    (fun x hx => F.othF hx (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e))
    (fun x hx => ?_)
    (fun x hx => ⟨x, F.othF hx (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e), rfl⟩)
    (fun x n hx => ?_) (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.finW_scOut hw hz hqC hK8 hK)
    F.sk.idle hAS hY3 (hYK.dk q.bv) hd
  · -- a dead TCB: its state and (null) bound notification kept
    obtain ⟨t, ht, e⟩ := J.obj.tcb q.bv x hx
    have htq : t = q := P1.eq_of_bv e
    subst htq
    obtain ⟨-, -, d3, -, -⟩ := hd.1 (J.zH.1 t ht)
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb t ht
    rw [hx] at hk'; cases hk'
    have hbn : x.tcbBoundNotification = none := by
      rw [hR.bound, show tBoundA t = P1.boundA t from rfl, d3, optRef_zero]
    obtain ⟨st', bn, ar, hk3, hs, hbb⟩ := F.tcbF hx
    refine ⟨_, hk3, ?_, ?_, Or.inl rfl⟩
    · show st' = x.tcbState
      rcases hs with ⟨e, -⟩ | ⟨-, e, -⟩
      · exact e
      · rw [e] at h0; simp [tsCode] at h0
    · show bn = x.tcbBoundNotification
      rcases hbb with e | e
      · exact e
      · rw [e, hbn]
  · -- a dead notification: not waiting, unbound
    obtain ⟨n', hn', e⟩ := J.obj.ntfn q.bv x hx
    have hnq : n' = q := P1.eq_of_bv e
    subst hnq
    obtain ⟨d1, d2, -⟩ := hd.2.2.1 (J.zH.2.2.2 n' hn')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.toN.ntfn n' hn'
    rw [hx] at hk'; cases hk'
    obtain ⟨y, hy, -, hobj, hbd, hsc'⟩ := F.ntfnF hx
    have hbn : x.ntfnBoundTcb = none := by
      rw [hR.bound, show nBoundA n' = P1.ntfnBtA n' from rfl, d2, optRef_zero]
    have hnw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := by
      intro l e
      have hO := hR.obj
      rw [e] at hO
      exact d1 (by rw [epState_eq]; exact hO.1)
    refine ⟨y, hy, (hobj hnw).imp id And.right, ?_, hsc'⟩
    rcases hbd with e | e
    · exact e
    · rw [e, hbn]
  · -- an SC: its thread kept, its notification kept or cut
    obtain ⟨rf, nt, hk3, -, hn⟩ := F.scF hx
    exact ⟨_, hk3, Or.inl rfl, hn⟩

end

-- from Fl4Proofs/P3/LiveFrame.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **A notification step's word (`NWrite`) is no debug word.** -/
theorem JAtZB.nwrite_notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : Notif.NWrite Z.N Z.T b) :
    ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  have hT : P1.TcbPlaced Z.T := J.ip.e.tcb
  have hH := J.kern.heap
  rcases hb with ⟨n, hn, g1, g2⟩ | ⟨t, ht, h⟩
  · have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
    refine J.notDbg (fun p hp => ?_) (fun c hc => ?_)
    · have hpn : p ≠ n := fun e => by rw [e, hHn] at hp; cases hp
      have e := hH.disj p _ n _ hp hHn hpn
      simp only [P1.HKind.bits] at e ⊢
      omega
    · have := J.kern.hnd n _ hHn c hc
      simp only [P1.HKind.bits] at this
      omega
  · have hv := nfootT_val (hT t ht) (b := b) (by
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    refine J.notDbg_tw (fun y hy w K hwv h1 h2 => ?_) (fun c hc => ?_)
    · rcases hv with e | e | e | e | e | e <;> exact tcbOff_ne hT ht hy e hwv (by omega) (by omega) (by omega)
    · intro e
      have hN : P1.NodePlaced st Z.T s c := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk c hc
      have hnv := P1.nodeAt_val hN (off := layout.node.DEBUG_TCBS) (by simp)
      have := J.kern.hnd t _ (J.zH.1 t ht) c hc
      simp only [P1.HKind.bits] at this
      rw [← e] at hnv
      have hd88 : layout.node.DEBUG_TCBS.val = 88 := P1.debug_val
      rcases hv with e' | e' | e' | e' | e' | e' <;> omega

end

-- from Fl4Proofs/P3/ScSignalJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **A badge-only signal keeps `JAtZ`** (module docstring): the spec's
outcome `updK σ n (.notification y)`, `y` the notification with a non-waiting
object (it was non-waiting), FL4's side `SingleRelI` at that outcome. -/
theorem JAtZB.signal_badge_post {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N)
    {x y : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hxw : ∀ l, x.ntfnObj ≠ .waitingNtfn l) (hyw : ∀ l, y.ntfnObj ≠ .waitingNtfn l)
    (hyb : y.ntfnBoundTcb = x.ntfnBoundTcb) (hys : y.ntfnSc = x.ntfnSc)
    {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hspec : spec = ({((), updK σ n.bv (.notification y))}, False))
    {s' : S} (hrel : SingleRelI (st := st) Z.N Z.T Z.E Z.R Z.B s σ spec s')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s') :
    ∃ σ' : Fl4Spec.State Unit, spec = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZB (L := L) arI AR Z H Cs Ac Lst D s' a σ' := by
  obtain ⟨σ3, hsp, hIR3, hNS, hW, -⟩ := hrel
  have e3 : σ3 = updK σ n.bv (.notification y) := by
    have h1 := (Prod.mk.inj (hsp.symm.trans hspec)).1
    exact congrArg Prod.snd (Set.singleton_injective h1)
  subst e3
  set σ3 := updK σ n.bv (.notification y) with hσ3
  -- the spec's frame
  have hN : NObj x.ntfnObj y.ntfnObj := Or.inr ⟨hxw, hyw⟩
  have F : NFr true n.bv σ σ3 := NFr.upd hk (Or.inr (Or.inr ⟨x, y, rfl, rfl, rfl, hN.queue, fun _ => hN,
    Or.inl hys, fun _ => hN, Or.inl hyb⟩))
  have hI3 : Inv σ3 := J.inv.updNtfn hk fun p hp => J.inv.ntfnSc n.bv x p hk (hys ▸ hp)
  -- FL4's side: `IRel` after
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT := hS.placed.tcb
  have h := hI.2
  have hSRT : SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c) s' σ3 :=
    ⟨h.1.stableN h.2.1.placed hW hNS, h.2.1.stable hW hNS, h.2.2.mono hW.1 (SzKeep.ntfnStep hNS)⟩
  have hI3' : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ3 := ⟨hIR3, hSRT⟩
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ3 := hSRT.2.1
  have hks : L.ksb s' = L.ksb s := hW.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    slotsSame_of_iw J.xtop.rel.1 J.xtop.rel.2.2.2.2.2.1 J.xtop.rel.2.2.2.2.2.2 hW
      fun b hb => Or.inl (NWrite.iwords hT hb)
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3' hAR hSS F.sk.cdt F.sk.orig F.ksub hks
  have hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hW.mono fun b hb => NWrite.finW hT hb
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hw
  have ck := F.ckeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  -- core 0's debug word: no notification or TCB word
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk 0#u64 J.kern.cs0
    have hv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp)
    have hd88 : layout.node.DEBUG_TCBS.val = 88 := P1.debug_val
    refine hW.mem_eq J.kern.dwAl fun hb => ?_
    rcases NWrite.iwords (E := Z.E) (R := Z.R) (B := Z.B) hT hb with ⟨t, ht, g1, g2⟩ | ⟨e, he, g1, g2⟩ |
      ⟨r, hr, g1, g2⟩ | ⟨m, hm, g1, g2⟩ | ⟨wp, hwp, g1, g2⟩
    · have := J.kern.hnd t _ (J.zH.1 t ht) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd e _ (J.zH.2.1 e he) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd r _ (J.zH.2.2.1 r hr) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.kern.hnd m _ (J.zH.2.2.2 m hm) 0#u64 J.kern.cs0
      simp only [P1.HKind.bits] at this; omega
    · have := J.nodeB wp hwp 0#u64 (by simp); omega
  -- the scheduler fields
  have hAI3 : ActIdle σ3 := F.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_nfr F hS3 hIR3 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ3 := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.finW_irq hw) (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' :=
    dbgKeep_of_writes J.blk hW fun b hb => J.nwrite_notDbg hb
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ3 :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hSS hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc)
        (DXKeep.of_dbg hKd (J.tdkeep_of hw fun _ hb => Ipc.FinW.ntd J.xtop.fin.1.1.1 hb)), hkern,
      J.finW_utc hw hSS F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, hI3,
      J.cur.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curInv, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa, F.isorted J.isorted,
      J.curRun.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curRunW, hblk⟩
  have hC0 := JCs.sameB J hSS F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ3 := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨σ3, hspec, rfl, J.cs_frameI hks hX3 hw (fun b hb => Ipc.FinW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => Ipc.FinW.nv J.xtop.fin.1.1.1 hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) F.szKeep hSS F.kback F.ipcFr hC R
    hKd F.sk.orig (XTopAt.idleW_eqS J.xtop hX3 F.sk.idle) J.zD⟩

end



end

end

end Fl4Proofs.P3

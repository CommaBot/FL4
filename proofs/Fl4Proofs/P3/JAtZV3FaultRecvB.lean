/-
P3 (line mmuAD, gen 42a2): **the pieces of the fault IPC to a waiting receiver at `JAtZV3`** (toward the receiver half
of gen 42a2's [W] `ZvFaultEpHyp`; the arms are P3/JAtZV3FaultRecv).

* **Copies over `JAtZB`** (generator `scratch/mmu32_jatzb_gen.py` with the receiver pattern widened to `J[0-9a-z]*.`
  and undotted `JAtZ`-parametrised names followed, filtered to the declarations not yet over `JAtZB`; none reads
  `JAtZ.ext`): `JAtZB.xferH` (P3/BufJ; its `bufPlacedJ` read as gen 34's `JAtZB.bufPlacedJ`), `deadP_dfrCI`, **`wake_postCI`**
  (P3/XTopJointSendCall), **`wake_postGR`** (P3/XTopJointSendPush), **`fin_frameF`**, **`setFaultCapJ`**
  (P3/XTopJointFaultRecv). Proofs verbatim except: the posts `∃ V', JAtZ (Z.mv Z.G V') …` of `wake_postCI` /
  `wake_postGR` / `fin_frameF` are stated as `JAtZB Z …` (their witness is `Z.vs`, `Z.mv Z.G Z.vs` = `Z`; the last
  line without the pair, as gen 42a2's `JAtZB.wake_postD`); `setFaultCapJ`'s post is `JAtZB Z` plus the `FinW`
  footprint (a `have` of its proof). Heartbeats 4M (sources 4M–16M). `JAtZB.recvReplyB`: ScSignalBoundJ's
  `recvReplyHyp_holds` at one `JAtZB` state (same proof).
* **`ZvK σ σ'`** (`JAtZV3.ofBS`'s spec side: arch objects kept, sizes kept, no new `runningVM`, no new or changed
  VCPU object), `ZvK.trans`, `ZvK.of_kheap`, `zvk_upd` (one object rewritten), **`zvk_dwfr`** (a wake frame `DWFr`:
  `DChg` changes TCB state only within `TCX`, which makes no `runningVM` — `tcx_runVM`), `zvk_ciSt`, `zvk_pushSt`.
  **`JAtZV3.ofBSK`** (`ofBS` with `ZvK`), **`JAtZV3.ofCnW`** (the `CnW` footprint: `CnW.oobj`, `cnW_nh`, `cnW_nv`).
* **`JAtZV3.bufWrites3`** / **`bufRebase3`** / **`bufRebaseX3`**: P3/XTopJointXferB's buffer rebase at `JAtZV3`
  (each buffer word by gen 33's `JAtZV3.userWr`, the rest of the proof verbatim over `J3.z2.zv.base`).
* **`JAtZV3.setFaultCapJ3`**: `set_fault` of a cap fault (`JAtZB.setFaultCapJ`, lifted by `ofBS`, `zvk_upd`).
* **The receiver's tail at `JAtZV3`**: `JAtZV3.unblockRJ3` (gen 42a's `JAtZB.unblockJR` + `ofTK`, the spec facts by
  `unblock_result`), `sendUnblockJ3`, `sendSwitchJ3` (`JAtZV3.switchJ`), **`sendTailJ3`** — P3/XTopJointSendRecv's
  `JAtZ.sendUnblockJ` / `sendSwitchJ` / `sendTailJ` with the same proofs.

No named premise. No existing statement changed.

(mmuAD gen 42b17) Copies removed (the originals are now stated over `JAtZB` in place): P3/XTopJointSendCall
`deadP_dfrCI`.

(mmuAD gen 42b18) Removed (the originals are stated over `JAtZB` in place, the `JAtZ` names their corollaries with
`ext` rebuilt): P3/BufJ `xferH`; P3/XTopJointSendCall `wake_postCI`; P3/XTopJointSendPush `wake_postGR`;
P3/XTopJointFaultRecv `fin_frameF`, `setFaultCapJ` (each original now has the copy's statement).
-/
import Fl4Proofs.P3.JAtZV3FaultBlk
import Fl4Proofs.P3.JAtZV3SigTail
import Fl4Proofs.P3.JAtZV3RegW
import Fl4Proofs.P3.XTopJointFaultRecv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## The spec side of `JAtZV3.ofBS` -/

section
open Fl4Proofs.P3.Sched

/-- **What `JAtZV3.ofBS` asks of the spec step** (module docstring). -/
def ZvK (σ σ' : Fl4Spec.State Unit) : Prop :=
  (∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = σ.kheap p) ∧
  (∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko) ∧
  (∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
    ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM) ∧
  (∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
    σ.kheap p = some (.archObj (.vcpu vs)))

variable {σ σ1 σ2 σ3 : Fl4Spec.State Unit}

theorem ZvK.trans (h1 : ZvK σ1 σ2) (h2 : ZvK σ2 σ3) : ZvK σ1 σ3 := by
  obtain ⟨a1, b1, c1, d1⟩ := h1
  obtain ⟨a2, b2, c2, d2⟩ := h2
  refine ⟨fun p ao hp => ?_, fun o ko hk => ?_, fun o x hk hx => ?_, fun p vs hp => d1 p vs (d2 p vs hp)⟩
  · have e1 := a1 p ao hp
    rw [a2 p ao (by rw [e1]; exact hp), e1]
  · obtain ⟨k2, hk2, e2⟩ := b2 o ko hk
    obtain ⟨k1, hk1, e1⟩ := b1 o k2 hk2
    exact ⟨k1, hk1, e2.trans e1⟩
  · obtain ⟨x2, hk2, hx2⟩ := c2 o x hk hx
    exact c1 o x2 hk2 hx2

theorem ZvK.of_kheap (h : σ2.kheap = σ1.kheap) : ZvK σ1 σ2 :=
  ⟨fun _ _ _ => by rw [h], fun o ko hk => ⟨ko, by rw [← h]; exact hk, rfl⟩,
    fun o x hk hx => ⟨x, by rw [← h]; exact hk, hx⟩, fun p vs hp => by rw [← h]; exact hp⟩

/-- One object rewritten (module docstring). -/
theorem zvk_upd {c : Fl4Spec.ObjRef} {o o' : Fl4Spec.KernelObject} (hk : σ.kheap c = some o)
    (hb : Fl4Spec.objBits o' = Fl4Spec.objBits o) (hna : ∀ ao, o ≠ .archObj ao) (hno : ∀ ao, o' ≠ .archObj ao)
    (hr : ∀ y, o' = .tcb y → y.tcbState = .runningVM → ∃ x, o = .tcb x ∧ x.tcbState = .runningVM) :
    ZvK σ (Notif.updK σ c o') := by
  refine ⟨fun p ao hp => ?_, fun q ko hq => ?_, fun q x' hq hx => ?_, fun p vs hp => ?_⟩
  · have hpc : p ≠ c := fun e => by rw [e, hk] at hp; exact hna ao (Option.some.inj hp)
    simp [Notif.updK, hpc]
  · by_cases e : q = c
    · subst e
      simp only [Notif.updK, Function.update_self, Option.some.injEq] at hq
      subst hq
      exact ⟨o, hk, hb⟩
    · exact ⟨ko, by simpa [Notif.updK, e] using hq, rfl⟩
  · by_cases e : q = c
    · subst e
      simp only [Notif.updK, Function.update_self, Option.some.injEq] at hq
      obtain ⟨x, rfl, hx0⟩ := hr x' hq hx
      exact ⟨x, hk, hx0⟩
    · exact ⟨x', by simpa [Notif.updK, e] using hq, hx⟩
  · by_cases e : p = c
    · subst e
      simp only [Notif.updK, Function.update_self, Option.some.injEq] at hp
      exact absurd hp (hno _)
    · simpa [Notif.updK, e] using hp

/-- A `TCX` change makes no `runningVM` thread. -/
theorem tcx_runVM {r t p : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb} {st : Fl4Spec.ThreadState}
    {bn : Option Fl4Spec.ObjRef} {fl : Option Fl4Spec.Fault} {ar : Fl4Spec.ArchTcb} (h : TCX r t p x st bn fl ar)
    (hs : st = .runningVM) : x.tcbState = .runningVM := by
  subst hs
  rcases h with ⟨⟨e, -⟩ | ⟨-, -, h | h⟩, -⟩ | ⟨-, -, -, h | h | h⟩
  · exact e.symm
  · cases h
  · cases h
  · cases h
  · cases h
  · exact h.symm

/-- **A wake frame keeps the VM epoch's spec side** (module docstring). -/
theorem zvk_dwfr {r t : Fl4Spec.ObjRef} (F : DWFr r t σ1 σ2) : ZvK σ1 σ2 := by
  refine ⟨fun p ao hp => ?_, fun o ko' ho => ?_, fun o x' ho hx => ?_, fun p vs hp => ?_⟩
  · rcases F.kh p with k | ⟨o1, o2, h1, -, hc⟩
    · exact k
    · rw [hp] at h1
      cases h1
      rcases hc with ⟨_, _, _, _, _, _, e, -⟩ | ⟨_, _, _, _, _, e, -⟩ | ⟨_, _, e, -⟩ | ⟨_, _, e, -⟩ | ⟨_, e, -⟩ <;>
        cases e
  · rcases F.kh o with k | ⟨o1, o2, h1, h2, hc⟩
    · exact ⟨ko', by rw [← k]; exact ho, rfl⟩
    · rw [ho] at h2
      cases h2
      rcases hc with ⟨_, _, _, _, _, _, rfl, rfl, -⟩ | ⟨_, _, _, _, _, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, -⟩ |
        ⟨_, _, rfl, rfl, -⟩ | ⟨_, rfl, rfl, -⟩ <;> exact ⟨_, h1, rfl⟩
  · rcases F.kh o with k | ⟨o1, o2, h1, h2, hc⟩
    · exact ⟨x', by rw [← k]; exact ho, hx⟩
    · rw [ho] at h2
      cases h2
      rcases hc with ⟨x, st, bn, fl, ar, sc, rfl, e, htc⟩ | ⟨_, _, _, _, _, _, e, -⟩ | ⟨_, _, _, e, -⟩ |
        ⟨_, _, _, e, -⟩ | ⟨_, _, e, -⟩
      · cases e
        exact ⟨x, h1, tcx_runVM htc hx⟩
      all_goals cases e
  · rcases F.kh p with k | ⟨o1, o2, h1, h2, hc⟩
    · rw [← k]; exact hp
    · rw [hp] at h2
      cases h2
      rcases hc with ⟨_, _, _, _, _, _, _, e, -⟩ | ⟨_, _, _, _, _, _, e, -⟩ | ⟨_, _, _, e, -⟩ | ⟨_, _, _, e, -⟩ |
        ⟨_, _, e, -⟩ <;> cases e

theorem zvk_ciSt {c : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb} (hk : σ.kheap c = some (.tcb x)) : ZvK σ (ciSt σ c x) :=
  (zvk_upd (o' := .tcb { x with tcbState := .inactive }) hk rfl (fun _ e => by cases e) (fun _ e => by cases e)
    (fun y e hy => by simp only [Fl4Spec.KernelObject.tcb.injEq] at e; subst e; simp at hy)).trans
    (ZvK.of_kheap (by unfold ciSt; exact Notif.stsAct_kheap _ _))

theorem zvk_pushSt {t r : Fl4Spec.ObjRef} {xr : Fl4Spec.Reply} {xt : Fl4Spec.Tcb}
    (hkr : σ.kheap r = some (.reply xr)) (hkt : σ.kheap t = some (.tcb xt)) (htr : t ≠ r) :
    ZvK σ (Endp.pushSt σ t r xr xt) := by
  have h1 : ZvK σ (Notif.updK σ r (.reply { xr with replyTcb := some t })) :=
    zvk_upd hkr rfl (fun _ e => by cases e) (fun _ e => by cases e) (fun y e _ => by cases e)
  have hkt' : (Notif.updK σ r (.reply { xr with replyTcb := some t })).kheap t = some (.tcb xt) := by
    simp [Notif.updK, htr, hkt]
  have h2 := zvk_upd (o' := .tcb { xt with tcbState := .blockedOnReply r }) hkt' rfl (fun _ e => by cases e)
    (fun _ e => by cases e) (fun y e hy => by simp only [Fl4Spec.KernelObject.tcb.injEq] at e; subst e; simp at hy)
  exact (h1.trans h2).trans (ZvK.of_kheap (Notif.stsAct_kheap _ _))

end

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- `JAtZV3.ofBS` with the spec side as `ZvK` (module docstring). -/
theorem JAtZV3.ofBSK (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ') {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hh : ∀ b, W b → b ≠ P1.vHeadA st s)
    (hv : VKeep (L := L) Z.th s s') (hK : ZvK σ σ') :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' :=
  J.ofBS B' hw hO hh hv (fun u hu => by obtain ⟨vu, hvu⟩ := J.z2.zv.vm.spec u hu; exact hK.1 _ _ hvu)
    hK.2.1 hK.2.2.1 hK.2.2.2

/-- **`JAtZV3` across a `CnW` step** (module docstring). -/
theorem JAtZV3.ofCnW (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    (B' : JAtZB (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ')
    (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ)) (hK : ZvK σ σ') :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D' s' a' σ' :=
  J.ofBSK B' hw (fun b hb => CnW.oobj J.z2.zv.base.xtop.fin.1.1.1 hb) (fun b hb => J.z2.zv.base.cnW_nh hb)
    (J.z2.zv.base.vkeep_of hw fun b hb => J.z2.zv.base.cnW_nv hb) hK

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- ScSignalBoundJ's `recvReplyHyp_holds` at one `JAtZB` state (module docstring). -/
theorem JAtZB.recvReplyB (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ d ∈ Z.R, ∀ xr t xt, σ.kheap d.bv = some (.reply xr) →
      xr.replyTcb = some t → σ.kheap t = some (.tcb xt) → Fl4Spec.receiveBlocked xt.tcbState = true →
      Detached Z.C Lst d ∧ L.mem s (rNextA d) = 0#u64 ∧ L.mem s (rPrevA d) = 0#u64 := by
  intro d hd xr t xt hx ht hxt hrb
  obtain ⟨hn, hp⟩ := J.rrecv d hd ⟨xr, t, xt, hx, ht, hxt, hrb⟩
  exact ⟨detached_of_next0 J.call (fun r hr => (J.rp.align r hr).2.1) hn, hn, hp⟩

end

end

/-! ## At `JAtZV3` -/

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- The receiver's buffer words of a list written at `JAtZV3` (P3/XTopJointXferB's `JAtZ.bufWrites`, each word by
`JAtZV3.userWr`). -/
theorem JAtZV3.bufWrites3 {d : U64} (hdT : d ∈ Z.T) (hdth : Z.th d = some .tcb)
    {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) {rp : Fl4Spec.ObjRef}
    (hrp : Endp.ipcBufOf true xd = some rp) (t : S) :
    ∀ (l : List U64), (∀ b ∈ l, RBufW ⟨rp⟩ b) → ∀ (s0 : S) (um : Fl4Spec.Word → Fl4Spec.Word8),
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s0 a (Endp.setUm σ um) →
      ∃ um', JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (mixS (L := L) s0 t l) a (Endp.setUm σ um') := by
  intro l
  induction l with
  | nil => intro _ s0 um J0; exact ⟨um, J0⟩
  | cons b l ih =>
    intro hl s0 um J0
    obtain ⟨i, hi, rfl⟩ := hl _ (List.mem_cons_self ..)
    obtain ⟨hOK, hBC, hBP⟩ := J0.z2.zv.base.xferH
    have hkd' : (Endp.setUm σ um).kheap d.bv = some (.tcb xd) := hkd
    have hwB : (Endp.fl4BufA ⟨rp⟩ i, Endp.bufAddr rp i.val) ∈ Z.B := hBC d hdT xd true rp hkd' hrp ⟨rp⟩ rfl i hi
    obtain ⟨hAp, hObj⟩ := J0.z2.zv.base.bufWordG hOK hdth hkd' hrp i.val hi (b := Endp.fl4BufA ⟨rp⟩ i)
      (by rw [fl4BufA_bv])
    have J1 := J0.userWr hBP hwB hAp hObj (L.mem t (Endp.fl4BufA ⟨rp⟩ i))
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ _ J1

set_option maxHeartbeats 4000000 in
/-- **Back to `JAtZV3` across the receiver's buffer words** (P3/XTopJointXferB's `JAtZ.bufRebase`). -/
theorem JAtZV3.bufRebase3 (J3 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {d : U64}
    (hdT : d ∈ Z.T) (hdth : Z.th d = some .tcb) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd))
    {rp : Fl4Spec.ObjRef} (hrp : Endp.ipcBufOf true xd = some rp) {s' : S}
    (hw : P1.WritesIn st s s' (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RBufW ⟨rp⟩ b))
    (hfoot : P1.WritesIn st s s' (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s b ∨ RBufW ⟨rp⟩ b)) :
    ∃ (su : S) (um : Fl4Spec.Word → Fl4Spec.Word8),
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D su a (Endp.setUm σ um) ∧
      P1.WritesIn st su s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c su (Endp.setUm σ um)) ∧
      P1.WritesIn st su s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
        (P1.EH H) su) ∧
      L.ksb su = L.ksb s ∧ (∀ b, P1.Aligned b → ¬ RBufW ⟨rp⟩ b → L.mem su b = L.mem s b) := by
  have J := J3.z2.zv.base
  obtain ⟨-, hBC, -⟩ := J.xferH
  have hal : ∀ b ∈ rbList ⟨rp⟩, P1.Aligned b := fun b hb => by
    obtain ⟨i, hi, rfl⟩ := mem_rbList.1 hb
    exact (J.xtop.fin.1.2.ep.balign _ (hBC d hdT xd true rp hkd hrp ⟨rp⟩ rfl i hi)).1
  obtain ⟨um, Ju⟩ := JAtZV3.bufWrites3 hdT hdth hkd hrp s' (rbList ⟨rp⟩) (fun b hb => mem_rbList.1 hb) s
    σ.machineState.underlyingMemory J3
  have hks : L.ksb (mixS (L := L) s s' (rbList ⟨rp⟩)) = L.ksb s := mixS_ksb _ _ _
  refine ⟨_, um, Ju, ?_, ?_, hks, fun b hb hn => ?_⟩
  · refine (mixS_writes hal (hw.mono fun b hb => hb.imp_right mem_rbList.2)).mono fun b hb => ?_
    exact cnW_back (s := mixS (L := L) s s' (rbList ⟨rp⟩)) (s' := s) (σ := Endp.setUm σ um) (σ' := σ) hks.symm
      (fun sc _ x n hk => ⟨x, hk⟩) hb
  · refine (mixS_writes hal (hfoot.mono fun b hb => hb.imp_right mem_rbList.2)).mono fun b hb => ?_
    have e : ∀ c o, L.nodeAt (mixS (L := L) s s' (rbList ⟨rp⟩)) c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
    unfold P1.KW at hb ⊢
    simp only [e]; exact hb
  · rw [mixS_mem s s' _ hal hb, if_neg (fun h => hn (mem_rbList.1 h))]

set_option maxHeartbeats 4000000 in
/-- `JAtZV3.bufRebase3` for the receiver's buffer words, none or some (P3/XTopJointXferB's `JAtZ.bufRebaseX`). -/
theorem JAtZV3.bufRebaseX3 (J3 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {d : U64}
    (hdT : d ∈ Z.T) (hdth : Z.th d = some .tcb) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) {s' : S}
    (hw : P1.WritesIn st s s' (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b))
    (hfoot : P1.WritesIn st s s' (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s b ∨ RcvBufW xd b)) :
    ∃ (su : S) (um : Fl4Spec.Word → Fl4Spec.Word8),
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D su a (Endp.setUm σ um) ∧
      P1.WritesIn st su s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c su (Endp.setUm σ um)) ∧
      P1.WritesIn st su s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
        (P1.EH H) su) ∧ L.ksb su = L.ksb s ∧ (∀ b, P1.Aligned b → ¬ RcvBufW xd b → L.mem su b = L.mem s b) := by
  cases hrp : Endp.ipcBufOf true xd with
  | none =>
    have hn : ∀ b, ¬ RcvBufW xd b := fun b ⟨rp, h, _⟩ => by rw [hrp] at h; cases h
    exact ⟨s, σ.machineState.underlyingMemory, J3, hw.mono fun b hb => hb.resolve_right (hn b),
      hfoot.mono fun b hb => hb.resolve_right (hn b), rfl, fun _ _ _ => rfl⟩
  | some rp =>
    have hc : ∀ b, RcvBufW xd b → RBufW ⟨rp⟩ b := fun b ⟨rp', h, hb⟩ => by rw [hrp] at h; cases h; exact hb
    obtain ⟨su, um, Ju, h1, h2, h3, h4⟩ := J3.bufRebase3 hdT hdth hkd hrp
      (hw.mono fun b hb => hb.imp_right (hc b)) (hfoot.mono fun b hb => hb.imp_right (hc b))
    exact ⟨su, um, Ju, h1, h2, h3, fun b hb hn => h4 b hb fun h => hn ⟨rp, hrp, h⟩⟩

/-- **`set_fault` of a cap fault at `JAtZV3`** (module docstring). -/
theorem JAtZV3.setFaultCapJ3 (J3 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hns : ∀ e d, x.tcbState ≠ .blockedOnSend e d)
    {t0 : U64} (hcb : P1.CanBlock st (P1.Heap.tcbs H) Ac s t0)
    {f : error.Fault} {f' : Fl4Spec.Fault} (hf : CapFaultCorr f f') :
    faults.set_fault st s t f ⦃ s' => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s' a
      (updK σ t.bv (.tcb { x with tcbFault := some f' })) ∧ P1.CanBlock st (P1.Heap.tcbs H) Ac s' t0 ⦄ := by
  have B := J3.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  refine WP.spec_mono (B.setFaultCapJ ht hk hns hcb hf) ?_
  rintro s' ⟨B', hcb', hwF⟩
  refine ⟨J3.ofBSK B' hwF (fun b hb => Ipc.FinW.oobj hS hb) (fun b hb => B.finW_nh hb)
    (B.vkeep_of hwF fun b hb => Ipc.FinW.nv hS hb) ?_, hcb'⟩
  exact zvk_upd hk rfl (fun _ e => by cases e) (fun _ e => by cases e) (fun y e hy => ⟨x, rfl, by simp only [Fl4Spec.KernelObject.tcb.injEq] at e; subst e; exact hy⟩)

set_option maxHeartbeats 4000000 in
/-- **`unblock_check` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.unblockRJ3 (J3 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hnr : t.bv ∉ σ.releaseQueue)
    {p : U64} (hp : p ∈ Z.C) (hxsc : x.tcbSchedContext = some p.bv) (hpc : p.bv ≠ σ.curSc)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap p.bv = some (.schedContext y n))
    (hya : Fl4Spec.scActive y = true) :
    sporadic.unblock_check st s p ⦃ s' => ∃ σ', Fl4Spec.refillUnblockCheck (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      (∀ q, q ≠ p.bv → σ'.kheap q = σ.kheap q) ∧ σ'.curThread = σ.curThread ∧
      σ'.idleThread = σ.idleThread ∧ σ'.releaseQueue = σ.releaseQueue ∧
      (∃ z, σ'.kheap p.bv = some (.schedContext z n) ∧ z.scRefillMax = y.scRefillMax ∧ z.scTcb = y.scTcb) ∧
      ∃ Lst' : U64 → List U64, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have B := J3.z2.zv.base
  refine WP.spec_mono (B.unblockJR ht hk hnr hp hxsc hpc hky hya) ?_
  rintro s' ⟨σ', he, hkp, -, hK, hw, Lst', B'⟩
  have mem : ((), σ') ∈ (Fl4Spec.refillUnblockCheck (Z := Unit) p.bv σ).1 := by rw [he]; exact Set.mem_singleton _
  have hne : y.scRefills ≠ [] := B.inv.ne _ y n hky hya
  have hF : σ'.curThread = σ.curThread ∧ σ'.idleThread = σ.idleThread ∧ σ'.releaseQueue = σ.releaseQueue ∧
      ∃ z, σ'.kheap p.bv = some (.schedContext z n) ∧ z.scRefillMax = y.scRefillMax ∧ z.scTcb = y.scTcb := by
    rcases unblock_result hky hne mem with ⟨rfl, -⟩ | ⟨z, rfl, -, -, hz, -⟩
    · exact ⟨rfl, rfl, rfl, y, hky, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, z, by simp [updK], by rw [hz], by rw [hz]⟩
  obtain ⟨e_ct, e_idle, e_rel, hz⟩ := hF
  exact ⟨σ', he, hkp, e_ct, e_idle, e_rel, hz, Lst', J3.ofTK B' hw hK⟩

set_option maxHeartbeats 4000000 in
/-- **`unblock_sporadic` at `J`** (module docstring). -/
theorem JAtZV3.sendUnblockJ3 (J3 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hnr : t.bv ∉ σ.releaseQueue) :
    endpoint.unblock_sporadic st s t ⦃ s' => ∃ (σ' : Fl4Spec.State Unit) (Lst' : U64 → List U64),
      Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σ = ({((), σ')}, False) ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σ' ∧ UnblockKeep σ σ' ⦄ := by
  have J := J3.z2.zv.base
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc0, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  rw [hk] at hkt; cases hkt
  have skip : Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
      ({((), σ)}, False) → ∃ (σ' : Fl4Spec.State Unit) (Lst' : U64 → List U64),
        Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σ = ({((), σ')}, False) ∧
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s a σ' ∧ UnblockKeep σ σ' := fun h =>
    ⟨σ, Lst, by rw [hsct]; exact h, J3, fun _ _ h => h, rfl, rfl, rfl, fun _ y _ h => ⟨y, h, rfl, rfl⟩⟩
  unfold endpoint.unblock_sporadic
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
  step with sporadic.sc_sporadic.spec' as ⟨b, b_post⟩
  subst hi2
  by_cases h0 : L.mem s (scA t) = 0#u64
  · have hb : b = false := by rw [b_post]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [h0, optRef_zero]; rfl)
  have hscC := hs.scMem t ht h0
  obtain ⟨y, n, hky, hy⟩ := hs.scs _ hscC
  have hsp : (y.scSporadic = true) ↔ L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64 := by
    rw [hy.sporadic]; simp
  have hif : Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
      (if y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc then
        Fl4Spec.refillUnblockCheck (L.mem s (scA t)).bv σ else ({((), σ)}, False)) := by
    rw [Notif.optRef_ne h0]
    unfold Fl4Spec.ifSporadicCurScTestRefillUnblockCheck Fl4Spec.ifCondRefillUnblockCheck
    simp only [Fl4Spec.NonDet.maybeM]
    rw [nd_bind_one (getSchedContext_eq hky), nd_gets_bind, nd_pure_bind']
    simp only [Fl4Spec.NonDet.when]
    by_cases e : y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc
    · simp only [e, ne_eq, not_false_eq_true, forall_const, and_self, ↓reduceIte, Option.some.injEq,
        Bool.false_eq_true, IsEmpty.forall_iff]
    · simp only [ne_eq, forall_const, ↓reduceIte, Option.some.injEq]
      rw [ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e),
        ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e)]
      rfl
  by_cases hsp' : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
  swap
  · have hb : b = false := by rw [b_post]; simp [h0]; simpa using hsp'
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [hif, ite_f (fun h => hsp' (hsp.1 h.1))])
  have hb : b = true := by rw [b_post]; simp [h0, hsp']
  simp only [hb, ↓reduceIte]
  step with sched.cur_sc.spec' as ⟨s1, s1_post⟩
  rw [sc_ne_eq]
  simp only [bind_ok]
  rw [s1_post, hc0.cur]
  by_cases e : L.mem s (scA t) = nodeW st s Z.c layout.node.CUR_SC
  · simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact skip (by rw [hif, ite_f]; rw [e, ← hs.curSc]; simp)
  · simp only [e, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    have hpc : (L.mem s (scA t)).bv ≠ σ.curSc := by rw [hs.curSc]; exact bv_ne e
    have hxsc : x.tcbSchedContext = some (L.mem s (scA t)).bv := by
      rw [hsct, Notif.optRef_ne h0]
    have hya : Fl4Spec.scActive y = true := hy.active_of_rmax (hy.spor hsp')
    refine WP.spec_mono (J3.unblockRJ3 ht hk hnr hscC hxsc hpc hky hya) ?_
    rintro s' ⟨σ', he, hkp, hct, hid, hrl, ⟨z, hkz, hzm, hzt⟩, Lst', J'⟩
    refine ⟨σ', Lst', ?_, J', fun q xq hq => ?_, hct, hid, hrl, fun q y' n' hq => ?_⟩
    · rw [hsct, hif, ite_t ⟨hsp.2 hsp', hpc⟩, he]
    · by_cases eq : q = (L.mem s (scA t)).bv
      · rw [eq, hky] at hq; cases hq
      · rw [hkp q eq]; exact hq
    · by_cases eq : q = (L.mem s (scA t)).bv
      · rw [eq, hkz] at hq; cases hq
        exact ⟨y, by rw [eq]; exact hky, hzm, hzt⟩
      · rw [hkp q eq] at hq; exact ⟨y', hq, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **`possible_switch_to` at `J`** of a runnable thread in no release queue
with an active SC or none (module docstring). -/
theorem JAtZV3.sendSwitchJ3 (J3 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hnr : t.bv ∉ σ.releaseQueue)
    (hact : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → Fl4Spec.scActive y = true)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have J := J3.z2.zv.base
  cases hsc : x.tcbSchedContext with
  | some p =>
    obtain ⟨y, n, hky, -⟩ := J.inv.back _ _ _ hk hsc
    exact J3.switchJ ht hti htc (schedulable_of hk hsc hrun hky (hact p y n hsc hky) hnr)
  | none =>
    have hS := J.xtop.fin.1.1.1
    obtain ⟨Q, R0, hc0, hs⟩ := hS.lists
    obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
    rw [hk] at hkt; cases hkt
    have h0 : L.mem s (scA t) = 0#u64 := by
      by_contra h0
      rw [Notif.optRef_ne h0] at hsct
      rw [hsc] at hsct; cases hsct
    unfold sched.possible_switch_to
    step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i, hi⟩
    rw [hi, h0]
    simp only [↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, Lst, J3⟩
    unfold Fl4Spec.possibleSwitchTo Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hk)]
    simp only [hsc, nd_gets_bind]
    rw [nd_when_false (by simp)]
    rfl

set_option maxHeartbeats 4000000 in
/-- **The receiver's tail of `send_ipc` at `J`** (module docstring). -/
theorem JAtZV3.sendTailJ3 (J3 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hrun : Fl4Spec.runnable x.tcbState = true)
    (hnr : t.bv ∉ σ.releaseQueue)
    (hact : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → Fl4Spec.scActive y = true)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) :
    (do
      let s6 ← endpoint.unblock_sporadic st s t
      let s7 ← sched.possible_switch_to st s6 t
      ok (s7, a)) ⦃ r => r.2 = a ∧ ∃ σ', Endp.specWakeTailE t.bv σ = ({((), σ')}, False) ∧
        ∃ Lst' : U64 → List U64, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D r.1 a σ' ⦄ := by
  refine WP.spec_bind (J3.sendUnblockJ3 ht hk hnr) ?_
  rintro s6 ⟨σ6, Lst6, hU, J6, hkt6, hct6, hid6, hrl6, hsc6⟩
  have hk6 := hkt6 _ _ hk
  have hact6 : ∀ p y n, x.tcbSchedContext = some p → σ6.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    obtain ⟨y0, hy0, hm, -⟩ := hsc6 p y n hy
    have := hact p y0 n hp hy0
    simp only [Fl4Spec.scActive] at this ⊢
    rw [hm]; exact this
  refine WP.spec_bind (J6.sendSwitchJ3 ht hk6 hrun (by rw [hrl6]; exact hnr) hact6 (by rw [hid6]; exact hti)
    (by rw [hct6]; exact htc)) ?_
  rintro s7 ⟨σ7, h7, Lst7, J7⟩
  refine (WP.spec_ok _).2 ⟨rfl, σ7, ?_, Lst7, J7⟩
  unfold Endp.specWakeTailE Fl4Spec.getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hk), nd_bind_one hU, h7]
end

end

end Fl4Proofs.P3

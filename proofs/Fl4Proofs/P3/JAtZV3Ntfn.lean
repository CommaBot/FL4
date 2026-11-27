/-
P3 (line mmuAD, gen 35): **badge-only notification writes at `JAtZV3`** (the VM-epoch invariant with the VCPU
relation).

* `zv_updN`: replacing a notification object of the spec heap by another notification keeps every VCPU object,
  every object size, creates no `runningVM` thread and no VCPU (the four spec-side arguments of
  `JAtZV3.ofBS`).
* **`JAtZV3.ntfnPost`**: P3/JAtZBSigPost's `JAtZB.signal_badge_post` at `JAtZV3` (same hypotheses: FL4's side
  `SingleRelI` at the outcome `updK σ n (.notification y)`, `x`/`y` not waiting, bound thread and SC kept, P1's
  `BlkOK` after), lifted by `JAtZV3.ofBS` with the footprint `NWrite ⊆ FinW` (`FinW.oobj`, `JAtZB.finW_nh`,
  `JAtZB.vkeep_of` with `FinW.nv`).
* **`JAtZV3.ntfnIdle`**: FL4's `obj.Ntfn.set_state n NTFN_IDLE` of an active notification (what `vcpu::check` does
  before its report) ↔ the spec's `setNotification n (ntfnObjUpdate idle x)` = `updK`; IpcNtfnRecv's
  `set_idle_relI`, P1's `ntfn_idle_all` for `BlkOK` after.

No premise; no existing statement changed.
-/
import Fl4Proofs.P3.JAtZBSigPost
import Fl4Proofs.P3.IpcNtfnRecv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- Replacing a notification by a notification: the spec-side frame of `JAtZV3.ofBS`. -/
theorem zv_updN {σ : Fl4Spec.State Unit} {n : U64} {x y : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) :
    (∀ o (vs : Fl4Spec.VcpuState), σ.kheap o = some (.archObj (.vcpu vs)) →
      (Notif.updK σ n.bv (.notification y)).kheap o = σ.kheap o) ∧
    (∀ o ko', (Notif.updK σ n.bv (.notification y)).kheap o = some ko' →
      ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko) ∧
    (∀ o x', (Notif.updK σ n.bv (.notification y)).kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM) ∧
    (∀ p (vs : Fl4Spec.VcpuState), (Notif.updK σ n.bv (.notification y)).kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs))) := by
  refine ⟨fun o vs ho => ?_, fun o ko' ho => ?_, fun o x' ho _ => ?_, fun p vs hp => ?_⟩
  · have e : o ≠ n.bv := by intro e; rw [e, hk] at ho; cases ho
    simp [Notif.updK, Function.update_of_ne e]
  · by_cases e : o = n.bv
    · subst e
      simp only [Notif.updK_kheap, Function.update_self, Option.some.injEq] at ho
      subst ho
      exact ⟨_, hk, rfl⟩
    · simp only [Notif.updK_kheap, Function.update_of_ne e] at ho
      exact ⟨ko', ho, rfl⟩
  · by_cases e : o = n.bv
    · subst e
      simp only [Notif.updK_kheap, Function.update_self, Option.some.injEq] at ho
      cases ho
    · simp only [Notif.updK_kheap, Function.update_of_ne e] at ho
      exact ⟨x', ho, by assumption⟩
  · by_cases e : p = n.bv
    · subst e
      simp only [Notif.updK_kheap, Function.update_self, Option.some.injEq] at hp
      cases hp
    · simpa only [Notif.updK_kheap, Function.update_of_ne e] using hp

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **A badge-only notification write keeps `JAtZV3`** (module docstring). -/
theorem JAtZV3.ntfnPost (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N)
    {x y : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hxw : ∀ l, x.ntfnObj ≠ .waitingNtfn l) (hyw : ∀ l, y.ntfnObj ≠ .waitingNtfn l)
    (hyb : y.ntfnBoundTcb = x.ntfnBoundTcb) (hys : y.ntfnSc = x.ntfnSc)
    {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hspec : spec = ({((), updK σ n.bv (.notification y))}, False))
    {s' : S} (hrel : SingleRelI (st := st) Z.N Z.T Z.E Z.R Z.B s σ spec s')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s') :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s' a (updK σ n.bv (.notification y)) := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hT := hS.placed.tcb
  obtain ⟨σ3, hsp, -, -, hW, -⟩ := id hrel
  obtain ⟨σ', h1, -, B'⟩ := B.signal_badge_post hn hk hxw hyw hyb hys hspec hrel hblk
  have e' : σ' = updK σ n.bv (.notification y) := by
    have h2 := (Prod.mk.inj (h1.symm.trans hspec)).1
    exact congrArg Prod.snd (Set.singleton_injective h2)
  subst e'
  have hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hW.mono fun b hb => NWrite.finW hT hb
  obtain ⟨u1, u2, u3, u4⟩ := zv_updN (y := y) hk
  exact J.ofBS B' hw (fun b hb => Ipc.FinW.oobj hS hb) (fun b hb => B.finW_nh hb)
    (B.vkeep_of hw fun b hb => Ipc.FinW.nv hS hb)
    (fun u hu => by obtain ⟨vu, hvu⟩ := J.z2.zv.vm.spec u hu; exact u1 _ _ hvu) u2 u3 u4

set_option maxHeartbeats 4000000 in
/-- **An active notification made idle at `JAtZV3`** (module docstring): FL4's `set_state(NTFN_IDLE)`. -/
theorem JAtZV3.ntfnIdle (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x)) {b0 : Fl4Spec.Badge}
    (hact : x.ntfnObj = .activeNtfn b0) :
    obj.Ntfn.set_state st n s obj.NTFN_IDLE ⦃ s1 =>
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a
        (updK σ n.bv (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) ⦄ := by
  have B := J.z2.zv.base
  have hI := B.xtop.irelK B.ks B.buf
  refine WP.spec_mono (P1.obj.Ntfn.set_state.val s n _) fun s1 e1 => ?_
  subst e1
  obtain ⟨hR2, hW2, hS2⟩ := set_idle_relI B.ip hI.1 hn hk hact
  -- P1's `BlkOK` after
  have hnH : n ∈ P1.Heap.ntfns H := B.zH.2.2.2 n hn
  have hx := hI.1.toN.at_ntfn hn hk
  have hst : L.epState s n = 2#u64 := by
    rw [epState_eq, stOf_active hx.obj hact, P1.ntfn_active_val]
  obtain ⟨⟨Q0, R0, h0'⟩, hB0, hX0, hS0, hSg0⟩ := B.blk
  obtain ⟨h2, hB2, hX2, hS2', hSg2, -⟩ := P1.ntfn_idle_all h0' hB0 hX0 hS0 hSg0 hnH hst
  exact J.ntfnPost (y := Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x) hn hk (by rw [hact]; intro l e; cases e) (fun l e => by simp [Fl4Spec.ntfnObjUpdate] at e) rfl rfl
    rfl ⟨_, rfl, hR2, hS2, hW2, NoBlock.ntfnUpd _ _ _⟩ ⟨⟨Q0, R0, h2⟩, hB2, hX2, hS2', hSg2⟩

end

end

end Fl4Proofs.P3

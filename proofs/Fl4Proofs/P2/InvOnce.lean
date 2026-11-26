/-
# P2 (line hpzg, generation 6): `ReadOnce` of the frame-cap invocation path at declining entries (`InvRoW`)

`InvLP.inv_readOnce` proves `ReadOnce` at accepting entries; the declining ones are the named premise
`InvRoW` [W] (`hro`). A run that declines at the entry `s` declines at every alternative `s'`
(`InvDec.inv_alt_not_acc`), and a declining run reads only the prefix's and the checks' words (the I/O port
path's minus the CSpace walk) and the plan's seen words: all in `IoRS s`, which holds no user word. So the run
works on the store guarded to `IoRS s` (`inv_dec_guardRS`), and `once_of_guardG` gives `Once` for every tree that
is the body there (`IsProgOn`) and has no `zero` (`NoZero`): no tree walk is needed.

* `invTail.guardR`: `InvDec.invTail.guardD` with the post-prefix facts as `IoMidR` (`io_alt_midR`);
* `inv_dec_guardRS`: a run declining at `s` runs at every alternative on `guard st (IoRS s) ⊤` as on `st`;
* **`invRoW_of`**: the named premise `InvRoW` of `inv_localPath`, discharged for any tree `q` with `IsProgOn`
  and `NoZero`.

Premises of `invRoW_of`: `hA` (Arch totality), `hPE` (`Pre` gives `IoPre`), [J] `hSeen` (the words
`still_holds` reads are in `IoRS` at a `Pre` state: `InvDec`'s `InvSeenRS`), and the tree's `IsProgOn` [P] /
`NoZero`. No statement of an existing declaration changes.
-/
import Fl4Proofs.P2.InvPrune
import Fl4Proofs.P2.IoOnceB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section ra
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

/-- **A declining frame-cap invocation tail on the guarded store**, `invTail.guardD` with the post-prefix facts
as `IoMidR` (`P2/IoOnceB.lean`: no found-slot field), which `io_alt_midR` gives for `R = IoRS s`. -/
theorem invTail.guardR {A : Type} (ar : machine.Arch A) {s : S} {a : A} {t : U64}
    {info : msginfo.MessageInfo} {p : localinv.Plan} {r : Bool × S × A}
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (hnx : R (regA t layout.reg.NEXT_IP)) (hfi : W (regA t layout.reg.FAULT_IP))
    (hmid : ∀ nx s1 s2 a1, obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) →
      ∃ C sl, IoMidR (L := L) R s2 t C sl)
    (hsh : ∀ x, localinv.Plan.still_holds gS p x = localinv.Plan.still_holds st p x)
    (hr : r.1 ≠ true)
    (h : invTail st ar s a t info p = ok r) :
    invTail gS ar s a t info p = ok r := by
  unfold invTail at h ⊢
  revert h
  refine tr_bind_same (fun b _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  refine tr_bind (fun x hx _ => by rw [obj.Tcb.reg.guard t s _ hnx]; exact hx) (fun nx enx => ?_)
  simp only [lift, bind_ok]
  refine tr_bind (fun x hx _ => by rw [obj.Tcb.set_reg.guard t s _ _ hfi]; exact hx) (fun s1 es1 => ?_)
  have e1 : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have k1 : L.ksb s1 = L.ksb s := by rw [e1, L.ksb_wr]
  have c1 : L.cpu s1 = L.cpu s := by rw [e1, LawfulStore.cpu_wr]
  refine tr_bind (fun x hx _ => by
      rw [sched.update_timestamp.guard ar s1 a (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
        (nd_at hNd k1 c1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2]; exact hx)
    (fun x eu => ?_)
  obtain ⟨s2, a1⟩ := x
  simp only [uncurry_apply_pair]
  obtain ⟨C, sl, M⟩ := hmid nx s1 s2 a1 enx es1 eu
  have nd2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s2 (L.cpu s2) o) := M.nd
  have Mc := M.cur
  subst Mc
  rw [sched.cur_sc.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.action.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
  refine tr_bind_same (fun i3 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.yield_to.guard (gS := gS) (L.curW s2) s2 M.yld]
  refine tr_bind_same (fun i4 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [sched.consumed.guard (gS := gS) s2 (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
  refine tr_bind_same (fun i5 _ => ?_)
  have ecsc' : csc = L.cscW s2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s2)] at ecsc; exact (ok_inj_ff ecsc).symm
  subst ecsc'
  rw [sporadic.sufficient.guard (gS := gS) ar s2 a1 _ i5 M.rh]
  refine tr_bind_same (fun b1 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [fastpath.schedulable_here.guard (gS := gS) s2 (L.curW s2) (nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    (nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) (nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
    M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
  refine tr_bind_same (fun b2 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [hsh s2]
  refine tr_bind_same (fun b3 _ => ?_)
  beta_reduce
  refine tr_ite (fun _ h => ?_) (fun _ h => h)
  -- all checks passed: a run that returns is accepted
  exfalso
  apply hr
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]


end ra

section ro
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s' : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}

/-- **A run declining at `s` runs at every alternative `s'` on the store guarded to `IoRS s`** (reads; writes
unguarded) as on `st` (`hSeen` [J]). -/
theorem inv_dec_guardRS {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64}
    {p : localinv.Plan} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ x, SeenW p x → IoRS (st := st) K Locks s x)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {r0 r : Bool × S × A} (h0 : syscall.handle_invocation_local st ar s a number p = ok r0)
    (hr0 : r0.1 ≠ true) (h : syscall.handle_invocation_local st ar s' a number p = ok r) :
    syscall.handle_invocation_local (guard st (IoRS (st := st) K Locks s) (fun _ => True)) ar s' a number p =
      ok r := by
  have hr : r.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r
    intro hb
    change b = true at hb
    subst hb
    exact inv_alt_not_acc hA P hSeen Al h0 hr0 h
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (L.nodeAt s' (L.cpu s') o) ∧ True := fun o h1 h2 =>
    ⟨by rw [G.node]; exact (P.nd (Locks := Locks) o h1 h2).1, trivial⟩
  rw [handle_invocation_local_eq] at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := guard st (IoRS (st := st) K Locks s) (fun _ => True)) s'
    (hNd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1, cur_thread_ok]
  simp only [bind_ok]
  rw [hcur, msg.msg_info.guard (gS := guard st (IoRS (st := st) K Locks s) (fun _ => True)) s' _
    (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1]
  refine tr_bind_same (fun info _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard (gS := guard st (IoRS (st := st) K Locks s) (fun _ => True)) (L.curW s) s'
    (P.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField])).1]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ ht => ?_)
  exact invTail.guardR (gS := guard st (IoRS (st := st) K Locks s) (fun _ => True)) ar hNd
    (P.reg (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1 trivial
    (fun nx s1 s2 a1 _ e1 e2 => io_alt_midR (nx := nx) hA P Al e1 e2)
    (fun x => still_holds_guard p x (fun w hw => hSeen w hw)) hr ht

/-- **The named premise `InvRoW` of `inv_localPath`, discharged** for every tree `q` that is the body on the
bridge's stores and states (`hp`, [P]) and has no `zero` (`hz`): from `hA`, and at every `Pre` state `hPE`
(`IoPre`) and [J] `hSeen`. -/
theorem invRoW_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x) {q : SProg Bool}
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q) (hz : NoZero q) :
    InvRoW st ar number p K Locks m0 q P := by
  intro s s' a r hE hac Al h
  obtain ⟨r0, h0⟩ := inv_total (st := st) hA number p s a
  have hr0 : r0.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r0
    intro e
    change b = true at e
    subst e
    exact hac ⟨z, c, h0⟩
  have h' : syscall.handle_invocation_local st ar s' a number p = ok r := by
    rw [inv_hp hp (Narrow.self st) ⟨s, hE, Al⟩ a]; exact h
  have hg := inv_dec_guardRS hA (hPE s hE) (hSeen s hE) Al h0 hr0 h'
  rw [inv_hp hp (Narrow.guard _ _ _) ⟨s, hE, Al⟩ a] at hg
  exact once_of_guardG (fun w hw => hw.2.1) q hz ∅ ∅ s' a _ hg

end ro

end Fl4Proofs.P2.PathObl

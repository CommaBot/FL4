/-
P2 (p2j4): **`smp.stall` (whole) and `send_pending` keep P1's invariants of
the executing core**, for any `LawfulStore` (so at the stalled core's view,
`P2/StallAt.lean`), with a frame for the other cores.

* `IdleSc c`: core `c`'s node word `IDLE_SC` is its idle thread's SC (new
  per-core invariant; boot establishes it, `create_idle_thread`).
* `StKeep d s s'`: what a stall of core `d` keeps: every core's `IDLE_THREAD`
  and `IDLE_SC`, every other core's `CUR_THREAD`, `SCHED_ACTION`, `CUR_SC`,
  the states of the protected threads `Kp`, every thread's `SC` word, every
  SC's `REPLY` and `TCB` words.
* `node_blk`, `csc_blk`: the node writes of the second half.
* `stall2.blk`: the second half of `smp.stall` (`P2/StallFull.lean` has the whole).

No premise.
-/
import Fl4Proofs.P2.FootN5
import Fl4Proofs.P1.QueueInvoke
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64} {Kp : Set U64}
variable {P3Ok : S → Prop}

/-- Core `c`'s node word `IDLE_SC` is its idle thread's SC. -/
def IdleSc (st : machine.Store S) [L : LawfulStore st] (c : U64) (s : S) : Prop :=
  L.mem s (L.nodeAt s c layout.node.IDLE_SC) = L.mem s (scA (L.mem s (L.nodeAt s c layout.node.IDLE_THREAD)))

/-- What a stall of core `d` keeps. -/
structure StKeep (st : machine.Store S) [L : LawfulStore st] (T Cs Scs Kp : Set U64) (d : U64) (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  cpu : L.cpu s' = L.cpu s
  nd : ∀ c ∈ Cs, ∀ o : U64, (o.val = 8 ∨ o.val = 32 ∨ (c ≠ d ∧ (o.val = 0 ∨ o.val = 16 ∨ o.val = 24))) →
    L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)
  kp : ∀ y ∈ Kp, L.mem s' (stA y) = L.mem s (stA y)
  iq : ∀ y ∈ Kp, L.mem s' (inqA y) = L.mem s (inqA y)
  af : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y)
  sc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y)
  lk : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c) ∧ L.mem s' (scTcbA c) = L.mem s (scTcbA c)

theorem StKeep.refl {d : U64} (s : S) : StKeep st T Cs Scs Kp d s s :=
  ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem StKeep.trans {d : U64} {s1 s2 s3 : S} (h : StKeep st T Cs Scs Kp d s1 s2) (k : StKeep st T Cs Scs Kp d s2 s3) :
    StKeep st T Cs Scs Kp d s1 s3 :=
  ⟨k.ksb.trans h.ksb, k.cpu.trans h.cpu, fun c hc o ho => by
      have e := k.nd c hc o ho
      rw [nodeAt_of_ksb h.ksb] at e
      exact e.trans (h.nd c hc o ho),
    fun y hy => (k.kp y hy).trans (h.kp y hy), fun y hy => (k.iq y hy).trans (h.iq y hy),
    fun y hy => (k.af y hy).trans (h.af y hy), fun y hy => (k.sc y hy).trans (h.sc y hy),
    fun c hc => ⟨(k.lk c hc).1.trans (h.lk c hc).1, (k.lk c hc).2.trans (h.lk c hc).2⟩⟩

/-- The SC link words are aligned words of their SC. -/
theorem sclink_in {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c : U64} (hc : c ∈ Scs) :
    (Aligned (scReplyA c) ∧ InSC c (Z c) (scReplyA c)) ∧ (Aligned (scTcbA c) ∧ InSC c (Z c) (scTcbA c)) := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hr := scReplyA_val hP hz
  have ht := scTcbA_val hP hz
  exact ⟨⟨by unfold Aligned; omega, by omega, by omega⟩, ⟨by unfold Aligned; omega, by omega, by omega⟩⟩

/-- An `IpcFootN` footprint (no-donation mode) is an `StKeep`. -/
theorem StKeep.ofI {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hKT : ∀ y ∈ Kp, y ∈ T)
    (f : IpcFootN st Kp True T Cs Ω Sg Scs Z Es U s s') : StKeep st T Cs Scs Kp (L.cpu s) s s' where
  ksb := f.1
  cpu := f.2.1
  nd := fun c hc o ho => f.idKeep
    (nodeAt_aligned (h.nodes c hc) (by omega) (by omega))
    (Or.inl ⟨c, hc, o, by
      rcases ho with e | e | ⟨hne, e⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl ⟨hne, e⟩)), rfl⟩)
  kp := fun y hy => f.stK h.tcbs (hKT y hy) hy
  iq := fun y hy => f.iqK h.tcbs (hKT y hy) hy
  af := fun y hy => f.idKeep (by rw [affA_eq]; exact field_aligned (h.tcbs y hy) (by simp) (by simp))
    (Or.inr (Or.inr ⟨trivial, Or.inl ⟨y, hy, h.tcbs y hy, Or.inr rfl⟩⟩))
  sc := fun y hy => f.idKeep (scA_aligned (h.tcbs y hy))
    (Or.inr (Or.inr ⟨trivial, Or.inl ⟨y, hy, h.tcbs y hy, Or.inl rfl⟩⟩))
  lk := fun c hc => by
    obtain ⟨⟨a1, i1⟩, ⟨a2, i2⟩⟩ := sclink_in hO hc
    exact ⟨f.idKeep a1 (Or.inr (Or.inr ⟨trivial, Or.inr ⟨c, hc, Or.inl rfl, h.omega _ (hO.scW c hc _ a1 i1)⟩⟩)),
      f.idKeep a2 (Or.inr (Or.inr ⟨trivial, Or.inr ⟨c, hc, Or.inr rfl, h.omega _ (hO.scW c hc _ a2 i2)⟩⟩))⟩

/-- A `FootN` footprint in no-donation mode is an `StKeep`, from `BlkOK`. -/
theorem StKeep.ofN {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hKT : ∀ y ∈ Kp, y ∈ T)
    (f : FootN st Kp True T Cs Sg Scs Z Es s s') : StKeep st T Cs Scs Kp (L.cpu s) s s' :=
  StKeep.ofI (Ω := Ω) (U := ∅) h.1.choose_spec.choose_spec h.2.2.1.1 hKT (FootN.ipc f)

/-- A `FootN` footprint in donation mode that is a `Fr` is an `StKeep`. -/
theorem StKeep.ofFr {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hKT : ∀ y ∈ Kp, y ∈ T)
    (f : FootN st Kp False T Cs Sg Scs Z Es s s') (fr : Fr st T Sg s s')
    (haf : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y)) :
    StKeep st T Cs Scs Kp (L.cpu s) s s' where
  ksb := f.1
  cpu := f.2.1
  nd := fun c hc o ho => f.idKeep
    (nodeAt_aligned (h.1.choose_spec.choose_spec.nodes c hc) (by omega) (by omega))
    (Or.inl ⟨c, hc, o, by
      rcases ho with e | e | ⟨hne, e⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl ⟨hne, e⟩)), rfl⟩)
  kp := fun y hy => fr.st y (hKT y hy)
  iq := fun y hy => f.idKeep (by
      rw [inqA_eq]; exact field_aligned (h.1.choose_spec.choose_spec.tcbs y (hKT y hy)) (by simp) (by simp))
    (Or.inr (Or.inl ⟨y, hKT y hy, h.1.choose_spec.choose_spec.tcbs y (hKT y hy), hy, Or.inr rfl⟩))
  af := haf
  sc := fr.sc
  lk := fun c hc => ⟨fr.sig _ (h.2.2.1.1.repW c hc), fr.sig _ (h.2.2.1.1.fixW c hc).1⟩

/-- The current core's `IdleSc` is kept by an `StKeep`. -/
theorem StKeep.idle {d c : U64} {s s' : S} (k : StKeep st T Cs Scs Kp d s s') (hc : c ∈ Cs)
    (hiT : L.mem s (L.nodeAt s c layout.node.IDLE_THREAD) ∈ T) (h : IdleSc st c s) : IdleSc st c s' := by
  unfold IdleSc at h ⊢
  rw [nodeAt_of_ksb k.ksb, nodeAt_of_ksb k.ksb, k.nd c hc _ (Or.inr (Or.inl (by simp [layout.node.IDLE_SC]))),
    k.nd c hc _ (Or.inl idle8), k.sc _ hiT]
  exact h

/-- `SgOK` at equal kernel-global base. -/
theorem SgOK.ksb {s s' : S} (h : SgOK st Ω Sg s) (e : L.ksb s' = L.ksb s) : SgOK st Ω Sg s' :=
  ⟨h.sub, fun b hb => by rw [e]; exact h.ks b hb, fun o h1 h2 => by rw [e]; exact h.ksΩ o h1 h2⟩

/-- **A write of one current-node word the invariants do not read** (not
`CUR_SC`). -/
theorem node_blk {s s' : S} {o : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ho : LowFree o.val) (h24 : o.val ≠ 24) (hto : o.val ≠ 88 ∧ o.val ≠ 104 ∧ o.val ≠ 112)
    (w : WritesIn st s s' (· = L.nodeAt s (L.cpu s) o)) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧
      L.idleW s' = L.idleW s ∧ L.cscW s' = L.cscW s := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hN := h0.nodes _ h0.cur
  have ho' : o.val < 4288 := by unfold LowFree at ho; omega
  have h8 : o.val % 8 = 0 := ho.2.1
  have hi8 : o.val ≠ 8 := ho.2.2.2.1
  have wF : WritesIn st s s' (L.Free s Ω Cs) := w.mono fun b hb => hb ▸ free_cur_node h0.cur ho
  obtain ⟨ka, kc, ki, ks⟩ := free_keys h0 wF
  have cs : L.cscW s' = L.cscW s := by
    unfold LawfulStore.cscW; rw [cscW_eq w.1 w.2.1]; unfold LawfulStore.nodeA
    refine w.mem_eq (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])) ?_
    intro e; have := congrArg UScalar.val e
    rw [nodeAt_val hN (by simp [layout.node.CUR_SC]), nodeAt_val hN ho'] at this
    simp [layout.node.CUR_SC] at this; omega
  obtain ⟨h1, hB1⟩ := free_step h0 hB wF
  refine ⟨⟨⟨Q, R, h1⟩, hB1, ?_, SCsOK.node h0 hS ho' h8 h24 hto w hi8, hSg.ksb w.1⟩, ka, kc, ki, cs⟩
  exact hX.writes h0.tcbs w (fun b hb => hb ▸ not_prot_node h0 hX.1 hSg.sub h0.cur ho') (by rw [cs]; exact hX.2.2.cur)
    (hX.tn_writes h0 w (fun b _ e => by
      subst e
      exact notTmW_node h0.tcbs h0.nodes (fun n hn => h0.omega _ (hSg.sub _ (hX.1.ntB n hn).2)) h0.cur ho' hto)) ki

/-- **`CUR_SC := the current thread's SC`.** -/
theorem csc_blk {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hb : L.mem s (scA (L.curW s)) ≠ 0#u64)
    (w : WritesIn st s s' (· = L.nodeAt s (L.cpu s) layout.node.CUR_SC))
    (e : L.mem s' (L.nodeAt s (L.cpu s) layout.node.CUR_SC) = L.mem s (scA (L.curW s))) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧
      L.idleW s' = L.idleW s ∧ L.cscW s' = L.mem s (scA (L.curW s)) ∧
      ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hN := h0.nodes _ h0.cur
  have c24 : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]
  have wF : WritesIn st s s' (L.Free s Ω Cs) := w.mono fun b hb =>
    hb ▸ free_cur_node h0.cur (by simp [layout.node.CUR_SC, LowFree])
  obtain ⟨ka, kc, ki, ks⟩ := free_keys h0 wF
  have hcT := h0.curT
  have hts : L.mem s (scA (L.curW s)) ∈ Scs := (hX.2.2.bound _ hcT hb).1
  have cs : L.cscW s' = L.mem s (scA (L.curW s)) := by
    unfold LawfulStore.cscW; rw [cscW_eq w.1 w.2.1]; exact e
  have hsig : ∀ b ∈ Sg, L.mem s' b = L.mem s b := fun b hb' =>
    w.mem_eq (h0.omega _ (hSg.sub b hb')).1 (fun e => out_ne_node (h0.omega _ (hSg.sub b hb')) h0.cur hN
      (by rw [c24]; omega) (congrArg UScalar.val e).symm)
  have hwf : ∀ c ∈ Scs, L.rmax s c ≠ 0#u64 → RefillsWF st s' c (Z c) := fun c hc hm =>
    ((hS.all c hc).agree hsig).1 (by
      rw [show L.rmax s' c = L.rmax s c from hsig _ (hS.all c hc).2.1]; exact hm)
  have hAts : L.rmax s (L.mem s (scA (L.curW s))) ≠ 0#u64 ∨ L.rmax s (L.mem s (scA (L.curW s))) = 0#u64 := by
    by_cases x : L.rmax s (L.mem s (scA (L.curW s))) = 0#u64
    · exact Or.inr x
    · exact Or.inl x
  obtain ⟨h1, hB1⟩ := free_step h0 hB wF
  refine ⟨⟨⟨Q, R, h1⟩, hB1, ?_, ?_, hSg.ksb w.1⟩, ka, kc, ki, cs, ks⟩
  · exact hX.writes h0.tcbs w (fun b hb => hb ▸ not_prot_node h0 hX.1 hSg.sub h0.cur (by rw [c24]; omega))
      (by rw [cs]; exact hts)
      (hX.tn_writes h0 w (fun b _ e => by
        subst e
        exact notTmW_node h0.tcbs h0.nodes (fun n hn => h0.omega _ (hSg.sub _ (hX.1.ntB n hn).2)) h0.cur
          (by rw [c24]; omega) (by rw [c24]; omega))) ki
  · refine ⟨hS.sub, fun b hb => by rw [w.1]; exact hS.ks b hb, fun o h1 h2 => by rw [w.1]; exact hS.ksΩ o h1 h2,
      fun t ht hb1 hne b hin => ?_, fun c hc => (hS.all c hc).agree hsig, fun c hc => ?_, fun c hc hs => ?_, hS.spSg,
      fun c hc hr => ?_, hS.repSg⟩
    · rw [cs]
      rw [ks t ht] at hb1 hne hin
      rw [cs] at hne
      have ht1 := (hX.2.2.bound t ht hb1).1
      have hd := hX.1.scDisj _ ht1 _ hts hne
      obtain ⟨i1, i2⟩ := hin
      unfold Outside
      omega
    · rw [show L.rmax s' c = L.rmax s c from hsig _ (hS.all c hc).2.1]; exact hS.act c hc
    · rw [hsig _ (hS.spSg c hc)] at hs; exact hS.spor c hc hs
    · rw [hsig _ (hS.repSg c hc)] at hr; exact hS.rep c hc hr

/-- `IDLE_SC`'s value. -/
theorem sched.idle_sc.valEq (s : S) :
    sched.idle_sc st s ⦃ v => v = L.mem s (L.nodeAt s (L.cpu s) layout.node.IDLE_SC) ⦄ := by
  unfold sched.idle_sc
  step with LawfulStore.cur_cpu_spec as ⟨c, c_post⟩
  subst c_post
  step with obj.node_get.spec as ⟨v, hv⟩
  try exact hv

theorem tcb_ne.spec' (a b : obj.Tcb) :
    core.cmp.PartialEq.ne.trait_default obj.Tcb.Insts.CoreCmpPartialEqTcb a b ⦃ r => r = true ↔ a ≠ b ⦄ := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  simp [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]

theorem StKeep.next {s1 s2 s3 : S} (k : StKeep st T Cs Scs Kp (L.cpu s1) s1 s2)
    (k' : StKeep st T Cs Scs Kp (L.cpu s2) s2 s3) : StKeep st T Cs Scs Kp (L.cpu s1) s1 s3 :=
  k.trans (by rw [k.cpu] at k'; exact k')

theorem Post.blk {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (P : Post st T Cs Ω H Sg Ac s s') :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' :=
  ⟨P.inv, P.bnd, h.2.2.1.fr P.fr, h.2.2.2.1.fr P.fr, h.2.2.2.2.ksb P.fr.ksb⟩

/-- The executing core's clauses after a stall: it idles on its idle SC, with
nothing to switch to. -/
structure Stalled0 (st : machine.Store S) [L : LawfulStore st] (Ac : Set U64) (s : S) : Prop where
  act : L.actionW s = 0#u64
  cur : L.curW s = L.idleW s
  csc : L.cscW s = L.mem s (scA (L.curW s))
  ac : L.cscW s ∈ Ac

variable {A : Type _} {ar : machine.Arch A}

/-- `Running → Restart` of the stalled thread. -/
theorem stall_restart (s : S) (ct : obj.Tcb) (i : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hct : ct ∈ T)
    (hcK : ct ∉ Kp) (hKT : ∀ y ∈ Kp, y ∈ T) (hi : i = L.mem s (stA ct)) :
    (if i = sched.TS_RUNNING then sched.set_thread_state st s ct sched.TS_RESTART else ok s)
      ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ StKeep st T Cs Scs Kp (L.cpu s) s s' ⦄ := by
  split
  · rename_i e
    have e' : L.mem s (stA ct) = sched.TS_RUNNING := hi ▸ e
    refine WP.spec_mono (WP.spec_and (sched.set_thread_state.restart_blk (Es := ∅) s ct h hct
      (by rw [e']; exact not_blocked_running) (by rw [e']; exact running_ne.1))
      (sched.set_thread_state.kwN (Kp := Kp) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s ct _
        h.1.choose_spec.choose_spec hct hcK)) fun s' hh => ?_
    exact ⟨hh.1.1, StKeep.ofN h hKT hh.2⟩
  · exact (WP.spec_ok _).2 ⟨h, StKeep.refl s⟩

/-- Enqueue of the stalled thread, if schedulable. -/
theorem stall_enqueue (s : S) (ct : obj.Tcb) (b : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hct : ct ∈ T)
    (hcK : ct ∉ Kp) (hKT : ∀ y ∈ Kp, y ∈ T)
    (hb : b = true → Runnable (L.mem s (stA ct)) ∧ L.mem s (scA ct) ≠ 0#u64 ∧
      (L.mem s (inqA ct) &&& sched.Q_RELEASE) = 0#u64 ∧ L.rmax s (L.mem s (scA ct)) ≠ 0#u64) :
    (if b then sched.enqueue st s ct else ok s)
      ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ StKeep st T Cs Scs Kp (L.cpu s) s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := id h
  split
  · rename_i e
    obtain ⟨b1, b2, b3, b4⟩ := hb e
    refine WP.spec_mono (WP.spec_and (sched.enqueue.sch s ct Q R h0 hB hSg hct (fun _ => b3) (fun _ => b1) (fun _ => b2)
      (fun _ => (hS.act _ (hX.2.2.bound _ hct b2).1).2 b4))
      (sched.enqueue.kwN (Kp := Kp) (Nd := True) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s ct h0 hct hcK)) fun s' hh => ?_
    exact ⟨Post.blk h hh.1.1, StKeep.ofN h hKT hh.2⟩
  · exact (WP.spec_ok _).2 ⟨h, StKeep.refl s⟩

/-- `switch_to_idle_thread`. -/
theorem stall_idle (hA : P0.ArchTotal ar) (s : S) (a : A) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hKT : ∀ y ∈ Kp, y ∈ T) :
    sched.switch_to_idle_thread st ar s a
      ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ StKeep st T Cs Scs Kp (L.cpu s) s s' ∧
        L.curW s' = L.idleW s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := id h
  unfold sched.switch_to_idle_thread
  step with sched.idle_thread.spec' as ⟨idle, idle_post⟩
  refine WP.spec_bind (set_kernel_vm_root_same (st := st) hA s a) ?_
  rintro ⟨s1, a1⟩ e
  simp only [WP.uncurry'_pair] at e
  subst s1
  have hiT : idle ∈ T := by rw [idle_post]; exact h0.idleT
  have hbd : L.mem s (scA idle) ≠ 0#u64 := by rw [idle_post]; exact hB.idle
  have hw0 : sched.set_cur_thread st s idle
      ⦃ s' => WritesIn st s s' (· = L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) ⦄ :=
    WP.spec_mono (sched.set_cur_thread.spec s idle) fun s' e => by
      subst e
      exact writesIn_wr (nodeAt_aligned (h0.nodes _ h0.cur) (by rw [curth0]; omega) (by rw [curth0]))
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.set_cur_thread.sch s idle Q R h0 hB hSg hiT (fun _ => hbd)
    (fun _ => by rw [idle_post]; exact hB.idleA h0.idleT))
    (sched.set_cur_thread.kwN (Kp := Kp) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) (T := T) s idle
      h0.nodes h0.cur id)) hw0) ?_
  rintro s2 ⟨⟨⟨P, ec, -⟩, f⟩, hw⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  have haf : ∀ y ∈ T, L.mem s2 (affA y) = L.mem s (affA y) := fun y hy => by
    refine hw.mem_eq (by rw [affA_eq]; exact field_aligned (h0.tcbs y hy) (by simp) (by simp)) fun e => ?_
    rw [affA_eq] at e
    exact node_ne_field (h0.nodes _ h0.cur) (by rw [curth0]; omega) hy (h0.tcbs y hy) (by simp) e.symm
  have k := StKeep.ofFr (Es := ∅) h hKT f P.fr haf
  refine ⟨Post.blk h P, k, ?_⟩
  rw [ec, idle_post]
  unfold LawfulStore.idleW
  rw [k.cpu, nodeAt_of_ksb k.ksb, k.nd _ h0.cur _ (Or.inl idle8)]

/-- A write of one own node word is an `StKeep`. -/
theorem StKeep.own {s : S} {o v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hKT : ∀ y ∈ Kp, y ∈ T)
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h88 : o.val ≠ 88) (hi8 : o.val ≠ 8) (h32 : o.val ≠ 32) (h0 : o.val ≠ 0) (h16 : o.val ≠ 16) :
    StKeep st T Cs Scs Kp (L.cpu s) s (L.wr s (L.nodeAt s (L.cpu s) o) v) :=
  StKeep.ofN (Es := ∅) h hKT (footN_node h.1.choose_spec.choose_spec.nodes h.1.choose_spec.choose_spec.cur ho h8 h88
    (idOff_cur hi8 h32 (fun _ => h0)) h.1.choose_spec.choose_spec.cur h16)

theorem own_w {s : S} {o v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    WritesIn st s (L.wr s (L.nodeAt s (L.cpu s) o) v) (· = L.nodeAt s (L.cpu s) o) :=
  writesIn_wr (nodeAt_aligned (h.1.choose_spec.choose_spec.nodes _ h.1.choose_spec.choose_spec.cur) ho h8)

/-- **The second half of `smp.stall`.** -/
theorem stall2.blk (hA : P0.ArchTotal ar) (s : S) (a : A) (ct : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hct : ct ∈ T) (hcK : ct ∉ Kp) (hKT : ∀ y ∈ Kp, y ∈ T) (hI : IdleSc st (L.cpu s) s) :
    (do
      let i ← obj.Tcb.state st ct s
      let s4 ← if i = sched.TS_RUNNING then sched.set_thread_state st s ct sched.TS_RESTART else ok s
      let b1 ← sched.is_schedulable st s4 ct
      let s5 ← if b1 then sched.enqueue st s4 ct else ok s4
      let (s6, a3) ← sched.switch_to_idle_thread st ar s5 a
      let cpu ← st.cur_cpu s6
      let idle_sc ← sched.idle_sc st s6
      let s7 ← obj.node_set st s6 cpu layout.node.CUR_SC idle_sc
      let s8 ← obj.node_set st s7 cpu layout.node.CONSUMED 0#u64
      let s9 ← sched.set_reprogram st s8
      let s10 ← sched.set_action st s9 sched.ACTION_RESUME_CURRENT
      ok (s10, a3)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ StKeep st T Cs Scs Kp (L.cpu s) s s' ∧
        Stalled0 st Ac s' ⦄ := by
  step with obj.Tcb.state.spec as ⟨i, hi⟩
  refine WP.spec_bind (stall_restart s ct i h hct hcK hKT hi) ?_
  rintro s4 ⟨h4, k4⟩
  refine WP.spec_bind (sched.is_schedulable.spec' s4 ct) ?_
  intro b1 hb1
  refine WP.spec_bind (stall_enqueue s4 ct b1 h4 hct hcK hKT hb1) ?_
  rintro s5 ⟨h5, k5⟩
  refine WP.spec_bind (stall_idle hA s5 a h5 hKT) ?_
  rintro ⟨s6, a3⟩ hh6
  simp only [WP.uncurry'_pair] at hh6 ⊢
  obtain ⟨h6, k6, ci6⟩ := hh6
  have k06 := (k4.next k5).next k6
  have q0 := h.1.choose_spec.choose_spec
  have hI6 : IdleSc st (L.cpu s6) s6 := by rw [k06.cpu]; exact k06.idle q0.cur q0.idleT hI
  have q6 := h6.1.choose_spec.choose_spec
  step with LawfulStore.cur_cpu_spec as ⟨cpu, hcpu⟩
  subst hcpu
  step with sched.idle_sc.valEq as ⟨isc, hisc⟩
  have hv : isc = L.mem s6 (scA (L.curW s6)) := by rw [hisc, ci6]; exact hI6
  have c24 : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]
  have c40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have c56 : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have hidle6 : L.mem s6 (scA (L.curW s6)) ≠ 0#u64 := by rw [ci6]; exact h6.2.1.idle
  have hidA : L.mem s6 (scA (L.curW s6)) ∈ Ac := by rw [ci6]; exact h6.2.1.idleA q6.idleT
  refine WP.spec_bind (obj.node_set.spec s6 _ _ _) ?_
  intro s7 e7
  have w7 : WritesIn st s6 s7 (· = L.nodeAt s6 (L.cpu s6) layout.node.CUR_SC) := by
    rw [e7]; exact own_w h6 (by omega) (by omega)
  obtain ⟨h7, ka7, kc7, ki7, cs7, sc7⟩ := csc_blk h6 hidle6 w7 (by
    rw [e7, hv]
    exact L.mem_wr_same (nodeAt_aligned (q6.nodes _ q6.cur) (by omega) (by omega)))
  have k7 : StKeep st T Cs Scs Kp (L.cpu s6) s6 s7 := by
    rw [e7]; exact StKeep.own h6 hKT (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine WP.spec_bind (obj.node_set.spec s7 _ _ _) ?_
  intro s8 e8
  rw [← k7.cpu] at e8
  have w8 : WritesIn st s7 s8 (· = L.nodeAt s7 (L.cpu s7) layout.node.CONSUMED) := by
    rw [e8]; exact own_w h7 (by omega) (by omega)
  obtain ⟨h8, ka8, kc8, ki8, cs8⟩ := node_blk h7 (by unfold LowFree; omega) (by omega) (by omega) w8
  have k8 : StKeep st T Cs Scs Kp (L.cpu s7) s7 s8 := by
    rw [e8]; exact StKeep.own h7 hKT (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine WP.spec_bind (sched.set_reprogram.spec s8) ?_
  intro s9 e9
  have w9 : WritesIn st s8 s9 (· = L.nodeAt s8 (L.cpu s8) layout.node.REPROGRAM) := by
    rw [e9]; exact own_w h8 (by omega) (by omega)
  obtain ⟨h9, ka9, kc9, ki9, cs9⟩ := node_blk h8 (by unfold LowFree; omega) (by omega) (by omega) w9
  have k9 : StKeep st T Cs Scs Kp (L.cpu s8) s8 s9 := by
    rw [e9]; exact StKeep.own h8 hKT (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have cT6 : L.curW s6 ∈ T := q6.curT
  have kcur : L.curW s9 = L.curW s6 := kc9.trans (kc8.trans kc7)
  have kidl : L.idleW s9 = L.idleW s6 := ki9.trans (ki8.trans ki7)
  have kcs : L.cscW s9 = L.mem s6 (scA (L.curW s6)) := cs9.trans (cs8.trans cs7)
  have k69 := (k7.next k8).next k9
  have hsc9 : L.mem s9 (scA (L.curW s9)) = L.mem s6 (scA (L.curW s6)) := by rw [kcur]; exact k69.sc _ cT6
  obtain ⟨⟨Q9, R9, q9⟩, hB9, hX9, hS9, hSg9⟩ := id h9
  rw [resume_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s9 0#u64 Q9 R9 q9 hB9 hSg9 (Or.inl rfl)
    (fun hT => absurd hT (notT_small q9.tcbs (by simp))) (fun hT => absurd hT (notT_small q9.tcbs (by simp)))
    (fun _ => by rw [hsc9]; exact ⟨hidle6, hidA⟩) (fun hT => absurd hT (notT_small q9.tcbs (by simp))))
    (sched.set_action.kwN (Kp := Kp) (Nd := True) (T := T) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s9 0#u64
      q9.nodes q9.cur (small_out q9.tcbs (by simp)))) ?_
  rintro s10 ⟨⟨P, ea, ec, -⟩, f10⟩
  have k10 : StKeep st T Cs Scs Kp (L.cpu s9) s9 s10 := StKeep.ofN h9 hKT f10
  have ki10 : L.idleW s10 = L.idleW s9 := by
    unfold LawfulStore.idleW; rw [k10.cpu, nodeAt_of_ksb k10.ksb, k10.nd _ q9.cur _ (Or.inl idle8)]
  simp only [WP.spec_ok, WP.uncurry'_pair]
  have hcs10 : L.cscW s10 = L.mem s6 (scA (L.curW s6)) := by rw [P.fr.csc, kcs]
  refine ⟨Post.blk h9 P, (k06.next k69).next k10, ea, ?_, ?_, ?_⟩
  · rw [ec, kcur, ki10, kidl, ci6]
  · rw [hcs10, ec, P.fr.sc _ (by rw [kcur]; exact cT6), hsc9]
  · rw [hcs10]; exact hidA

end

end Fl4Proofs.P1

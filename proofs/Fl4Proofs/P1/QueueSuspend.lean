/-
P1: `suspend` (seL4 `suspend`, MCS) keeps the queue invariant together with
`BoundInv` (the threads the scheduler can make current are bound) and
`XInv` (reply objects and SCs).
-/
import Fl4Proofs.P1.QueueObjs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- A write away from the words `BoundInv` and `XInv` read. -/
theorem bx_wr {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (ha : Aligned a) (hP : ¬ Prot T Rp Scs Nt a) (hsi : ∀ y ∈ T, a.val ≠ (scA y).val ∧ a.val ≠ (inqA y).val)
    (hn : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16 ∨ o.val = 24) → a.val ≠ (L.nodeAt s (L.cpu s) o).val)
    (htn : TimerOK st T Cs (L.wr s a v) ∧ NtbOK st T Nt (L.wr s a v)) :
    BoundInv st T (L.wr s a v) ∧ XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s a v) := by
  have hN' := h.nodes _ h.cur
  have nd : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16 ∨ o.val = 24) →
      L.mem (L.wr s a v) (L.nodeAt (L.wr s a v) (L.cpu (L.wr s a v)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o ho => by
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne ha (nodeAt_aligned hN' (by omega) (by omega)) (hn o ho)
  have hsc : ∀ y ∈ T, L.mem (L.wr s a v) (scA y) = L.mem s (scA y) := fun y hy =>
    L.mem_wr_ne ha (scA_aligned (h.tcbs y hy)) (hsi y hy).1
  have hiq : ∀ y ∈ T, L.mem (L.wr s a v) (inqA y) = L.mem s (inqA y) := fun y hy =>
    L.mem_wr_ne ha (by rw [inqA_eq]; exact field_aligned (h.tcbs y hy) (by simp) (by simp)) (hsi y hy).2
  have ea : L.actionW (L.wr s a v) = L.actionW s := by
    unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega)
  have ec : L.curW (L.wr s a v) = L.curW s := by unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega)
  have ei : L.idleW (L.wr s a v) = L.idleW s := by unfold LawfulStore.idleW; exact nd _ (by rw [idle8]; omega)
  refine ⟨hB.mk' hsc (fun y hy hf => Or.inl (by rw [← hiq y hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← hiq y hy]; exact hf))) (fun haT => ?_)
    (by rw [ei]; exact ⟨h.idleT, hB.idle⟩) (fun h0 => ?_)
    (hB.nb ei (L.mem_wr_ne ha (by rw [stA_eq]; exact field_aligned (h.tcbs _ h.idleT) (by simp) (by simp))
      (fun e => hP (Or.inr (Or.inr (Or.inl ⟨_, h.idleT, Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq e)))⟩)))))), ?_⟩
  · rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩
  · rw [ea] at h0; rw [ec]; exact ⟨h.curT, hB.resume h0⟩
  · refine hX.writes h.tcbs (writesIn_wr (v := v) ha) (fun b hb => hb ▸ hP) ?_ htn
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [nd _ (by simp [layout.node.CUR_SC])]; exact hX.2.2.cur

/-- A TCB field other than the SC, reply, state and `IN_QUEUES` fields, given
the timer-tree typing after the write. -/
theorem bx_field' {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {y K v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKn : K.val ≠ 3464 ∧ K.val ≠ 3360 ∧ K.val ≠ 3328 ∧ K.val ≠ 3592 ∧ K.val ≠ 3368)
    (htn : TimerOK st T Cs (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      NtbOK st T Nt (L.wr s (core.num.U64.wrapping_add y K) v)) :
    BoundInv st T (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (core.num.U64.wrapping_add y K) v) := by
  have hya := h.tcbs y hy
  have hN' := h.nodes _ h.cur
  refine bx_wr h hB hX (field_aligned hya hK hK8) ?_ (fun y' hy' => ⟨?_, ?_⟩) (fun o ho => ?_) htn
  · intro hp
    rcases hX.1.prot_cases hsub hp with hm | ⟨t', ht', K', hK', e⟩
    · exact out_ne_field (h.omega _ hm) hy hya hK rfl
    · rcases hp with ⟨r, hr, e'⟩ | ⟨c, hc, e'⟩ | ⟨u, hu, e'⟩ | ⟨n, hn, e'⟩
      rotate_right
      · have hm : core.num.U64.wrapping_add y K ∈ Ω := by rw [e']; exact hsub _ (hX.1.ntW n hn)
        exact out_ne_field (h.omega _ hm) hy hya hK rfl
      · have hm : core.num.U64.wrapping_add y K ∈ Ω := by
          rcases e' with e' | e' | e' <;> rw [e']
          · exact hsub _ (hX.1.tcbW hr)
          · exact hsub _ (hX.1.prevW hr)
          · exact hsub _ (hX.1.nextW hr)
        exact out_ne_field (h.omega _ hm) hy hya hK rfl
      · have hm : core.num.U64.wrapping_add y K ∈ Ω := by
          rcases e' with e' | e' | e' | e' <;> rw [e']
          · exact hsub _ (hX.1.fixW c hc).1
          · exact hsub _ (hX.1.fixW c hc).2
          · exact hsub _ (hX.1.repW c hc)
          · exact hsub _ (hX.1.snW c hc)
        exact out_ne_field (h.omega _ hm) hy hya hK rfl
      · rcases e' with e' | e' | e' | e'
        · rw [scA_eq] at e'
          exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
        · exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
        · rw [stA_eq] at e'
          exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
        · exact field_ne hya (h.tcbs u hu) hK (by simp) (fun _ => by simp; omega) e'
  · rw [scA_eq]
    exact fun e => field_ne hya (h.tcbs y' hy') hK (by simp) (fun _ => by simp; omega) (UScalar.eq_of_val_eq e)
  · rw [inqA_eq]
    exact fun e => field_ne hya (h.tcbs y' hy') hK (by simp) (fun _ => by simp; omega) (UScalar.eq_of_val_eq e)
  · exact fun e => node_ne_field hN' (by omega) hy hya hK (UScalar.eq_of_val_eq e).symm

/-- A TCB field other than the SC, reply, state, `IN_QUEUES` and timer fields. -/
theorem bx_field {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {y K v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hKn : K.val ≠ 3464 ∧ K.val ≠ 3360 ∧ K.val ≠ 3328 ∧ K.val ≠ 3592 ∧ K.val ≠ 3368)
    (hKt : K.val < 3528 ∨ 3576 ≤ K.val) :
    BoundInv st T (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (core.num.U64.wrapping_add y K) v) :=
  bx_field' h hB hX hsub hy hK hK8 hKn (hX.tn_wr h (field_aligned (h.tcbs y hy) hK hK8)
    (notTmW_field h.tcbs h.nodes (fun n hn => h.omega _ (hsub _ (hX.1.ntB n hn).2)) hy hK hKt))

/-- A queue step on `t` that only clears `t`'s flags. -/
theorem bx_qfoot {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {W : List U64}
    {c t : U64} {P : Nat → Prop} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s) (hW : ∀ w ∈ W, w ∈ T) (hc : c ∈ Cs) (ht : t ∈ T)
    (hP : ∀ o, P o → o ≠ 0 ∧ o ≠ 8 ∧ o ≠ 16 ∧ o ≠ 24 ∧ o ≠ 104 ∧ o ≠ 112) (hw : WritesIn st s s' (L.QFoot s W c P t))
    (hq : (L.mem s' (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 →
      (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
        L.mem s (scA t) ≠ 0#u64)
    (hr : (L.mem s' (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 →
      (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ∨ (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ∨
        L.mem s (scA t) ≠ 0#u64) :
    BoundInv st T s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ Fr st T Sg s s' ∧ L.actionW s' = L.actionW s ∧
      L.curW s' = L.curW s ∧ ∀ y ∈ T, y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y) := by
  obtain ⟨f, hi, ea, ec, ei⟩ := qfoot_keep h hSg hW hc ht hP hw
  exact ⟨hB.qstep h f.sc hi ea ec ei hq hr (f.st _ h.idleT), hX.fr f, f, ea, ec, hi⟩

/-! ## `SCsOK` across scheduler steps -/

theorem SCsOK.keepT {s s' : S} {t : U64} (hS : SCsOK st T Ω Sg Scs Z s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (k : KeepT st T Cs Rp Scs Nt t s s') : SCsOK st T Ω Sg Scs Z s' := by
  have wf : ∀ c ∈ Scs, RefillsWF st s c (Z c) → RefillsWF st s' c (Z c) := fun c hc hW => by
    obtain ⟨-, -, f3, f4, f5⟩ := k.fix c hc
    exact hW.of_hdr f3 (by rw [show L.rhead s' c = L.mem s' (headA c) from rfl, f4]; exact hW.head_lt)
      (by rw [show L.rtail s' c = L.mem s' (tailA c) from rfl, f5]; exact hW.tail_lt)
  refine ⟨hS.sub, fun b hb => by rw [k.ksb]; exact hS.ks b hb, fun o h1 h2 => by rw [k.ksb]; exact hS.ksΩ o h1 h2,
    fun y hy hb => ?_, ?_, fun y hy hb hne => ?_, fun c hc => ⟨wf c hc (hS.all c hc).1, (hS.all c hc).2⟩⟩
  · rw [k.scf hy] at hb ⊢
    exact ⟨wf _ (hX.2.2.bound y hy hb).1 (hS.bound y hy hb).1, (hS.bound y hy hb).2⟩
  · rw [k.cscW]; exact ⟨wf _ hX.2.2.cur hS.cur.1, hS.cur.2⟩
  · rw [k.scf hy] at hb hne ⊢; rw [k.cscW] at hne ⊢; exact hS.disj y hy hb hne

/-- `SCsOK` after writes to the ring of the SC object `i` (kept well formed)
and to the current node's `REPROGRAM`. -/
theorem SCsOK.ring {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {i : U64}
    {X : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SCsOK st T Ω Sg Scs Z s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hi : i ∈ Scs) (w : WritesIn st s s' (fun b => InRing i (Z i) b ∨ b = L.nodeA s layout.node.REPROGRAM))
    (hwi : RefillsWF st s' i (Z i)) : SCsOK st T Ω Sg Scs Z s' := by
  obtain ⟨hO, -, hE⟩ := hX
  have hN' := h.nodes _ h.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have nr : ∀ b, Aligned b → (InRing i (Z i) b ∨ b = L.nodeA s layout.node.REPROGRAM) →
      ∀ y ∈ T, ∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add y K := by
    rintro b hb (hh | rfl) y hy K hK e
    · exact out_ne_field (h.omega _ (hO.scW i hi b hb hh.inSC)) hy (h.tcbs y hy) hK (by rw [e])
    · exact node_ne_field hN' (by rw [rp]; omega) hy (h.tcbs y hy) hK e
  have fld : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy =>
    w.mem_eq (scA_aligned (h.tcbs y hy)) fun hh => nr _ (scA_aligned (h.tcbs y hy)) hh y hy _ (by simp) (scA_eq y)
  have csc : L.cscW s' = L.cscW s := by
    unfold LawfulStore.cscW; rw [cscW_eq w.1 w.2.1]
    have aC : Aligned (L.nodeA s layout.node.CUR_SC) :=
      nodeAt_aligned hN' (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
    refine w.mem_eq aC ?_
    rintro (hh | hh)
    · exact out_ne_node (h.omega _ (hO.scW i hi _ aC hh.inSC)) h.cur hN' (by simp [layout.node.CUR_SC]) rfl
    · have := congrArg UScalar.val hh
      simp only [LawfulStore.nodeA] at this
      rw [nodeAt_val hN' (by simp [layout.node.CUR_SC]), nodeAt_val hN' (by rw [rp]; omega), rp] at this
      simp [layout.node.CUR_SC] at this
  have wf : ∀ c ∈ Scs, RefillsWF st s c (Z c) → RefillsWF st s' c (Z c) := by
    intro c hc hW
    by_cases e : c = i
    · subst e; exact hwi
    refine hW.writesIn w fun b hb hh => ?_
    rcases hh with hh | rfl
    · have := hO.scDisj c hc i hi e; unfold Outside; unfold InRing at hh; omega
    · exact SCin.node_out ⟨hW, hO.scW c hc⟩ h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
  refine ⟨hS.sub, fun b hb => by rw [w.1]; exact hS.ks b hb, fun o h1 h2 => by rw [w.1]; exact hS.ksΩ o h1 h2,
    fun y hy hb => ?_, ?_, fun y hy hb hne => ?_, fun c hc => ⟨wf c hc (hS.all c hc).1, (hS.all c hc).2⟩⟩
  · rw [fld y hy] at hb ⊢
    exact ⟨wf _ (hE.bound y hy hb).1 (hS.bound y hy hb).1, (hS.bound y hy hb).2⟩
  · rw [csc]; exact ⟨wf _ hE.cur hS.cur.1, hS.cur.2⟩
  · rw [fld y hy] at hb hne ⊢; rw [csc] at hne ⊢; exact hS.disj y hy hb hne


/-- One write away from the TCBs' SC fields, the current SC word and the SC
objects' ring headers keeps `SCsOK`. -/
theorem SCsOK.wr {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    {X : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SCsOK st T Ω Sg Scs Z s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (ha : Aligned a) (hsc : ∀ y ∈ T, a.val ≠ (scA y).val) (hcs : a.val ≠ (L.nodeA s layout.node.CUR_SC).val)
    (hh : ∀ c ∈ Scs, a.val ≠ (maxA c).val ∧ a.val ≠ (headA c).val ∧ a.val ≠ (tailA c).val) :
    SCsOK st T Ω Sg Scs Z (L.wr s a v) := by
  have hN' := h.nodes _ h.cur
  have al : ∀ c ∈ Scs, ∀ o : U64, o.val < 128 → o.val % 8 = 0 → Aligned (core.num.U64.wrapping_add c o) :=
    fun c hc o ho h8 => by
      obtain ⟨hP, hz⟩ := hX.1.sc c hc
      have := (sc_lo hP hz).1
      unfold Aligned; rw [sc_word_val hP hz ho]; omega
  have fix : ∀ c ∈ Scs, L.mem (L.wr s a v) (maxA c) = L.mem s (maxA c) ∧
      L.mem (L.wr s a v) (headA c) = L.mem s (headA c) ∧ L.mem (L.wr s a v) (tailA c) = L.mem s (tailA c) :=
    fun c hc => ⟨L.mem_wr_ne ha (al c hc _ (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])) (hh c hc).1,
      L.mem_wr_ne ha (al c hc _ (by simp [layout.sc.REFILL_HEAD]) (by simp [layout.sc.REFILL_HEAD])) (hh c hc).2.1,
      L.mem_wr_ne ha (al c hc _ (by simp [layout.sc.REFILL_TAIL]) (by simp [layout.sc.REFILL_TAIL])) (hh c hc).2.2⟩
  have wf : ∀ c ∈ Scs, RefillsWF st s c (Z c) → RefillsWF st (L.wr s a v) c (Z c) := fun c hc hW => by
    obtain ⟨f3, f4, f5⟩ := fix c hc
    exact hW.of_hdr f3 (by rw [show L.rhead (L.wr s a v) c = L.mem (L.wr s a v) (headA c) from rfl, f4]; exact hW.head_lt)
      (by rw [show L.rtail (L.wr s a v) c = L.mem (L.wr s a v) (tailA c) from rfl, f5]; exact hW.tail_lt)
  have fld : ∀ y ∈ T, L.mem (L.wr s a v) (scA y) = L.mem s (scA y) := fun y hy =>
    L.mem_wr_ne ha (scA_aligned (h.tcbs y hy)) (hsc y hy)
  have csc : L.cscW (L.wr s a v) = L.cscW s := by
    unfold LawfulStore.cscW; rw [nodeA_wr]
    exact L.mem_wr_ne ha (nodeAt_aligned hN' (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])) hcs
  refine ⟨hS.sub, fun b hb => by rw [L.ksb_wr]; exact hS.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hS.ksΩ o h1 h2,
    fun y hy hb => ?_, ?_, fun y hy hb hne => ?_, fun c hc => ⟨wf c hc (hS.all c hc).1, (hS.all c hc).2⟩⟩
  · rw [fld y hy] at hb ⊢
    exact ⟨wf _ (hX.2.2.bound y hy hb).1 (hS.bound y hy hb).1, (hS.bound y hy hb).2⟩
  · rw [csc]; exact ⟨wf _ hX.2.2.cur hS.cur.1, hS.cur.2⟩
  · rw [fld y hy] at hb hne ⊢; rw [csc] at hne ⊢; exact hS.disj y hy hb hne

/-- A TCB field other than the SC field keeps `SCsOK`. -/
theorem SCsOK.field {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {y K v : U64}
    {X : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SCsOK st T Ω Sg Scs Z s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (hKs : K.val ≠ 3464) :
    SCsOK st T Ω Sg Scs Z (L.wr s (core.num.U64.wrapping_add y K) v) := by
  have hya := h.tcbs y hy
  have hN' := h.nodes _ h.cur
  obtain ⟨-, hc⟩ := objs_omega hX.1 hS.sub
  refine SCsOK.wr h hS hX (field_aligned hya hK hK8) (fun y' hy' => ?_) ?_ (fun c hc' => ?_)
  · rw [scA_eq]; exact fun e => field_ne hya (h.tcbs y' hy') hK (by simp) (fun _ => by simp; omega) (UScalar.eq_of_val_eq e)
  · exact fun e => node_ne_field hN' (by simp [layout.node.CUR_SC]) hy hya hK (UScalar.eq_of_val_eq e).symm
  · obtain ⟨-, -, c3, c4, c5⟩ := hc c hc'
    exact ⟨out_ne_field (h.omega _ c3) hy hya hK, out_ne_field (h.omega _ c4) hy hya hK,
      out_ne_field (h.omega _ c5) hy hya hK⟩

/-- An SC object's `YIELD_FROM` or `REPLY` word keeps `SCsOK`. -/
theorem SCsOK.scword {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {c a v : U64}
    {X : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hS : SCsOK st T Ω Sg Scs Z s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hc : c ∈ Scs) (ha : a = scReplyA c ∨ a = core.num.U64.wrapping_add c layout.sc.YIELD_FROM) :
    SCsOK st T Ω Sg Scs Z (L.wr s a v) := by
  have hN' := h.nodes _ h.cur
  have haΩ := scword_omega hX.1 hc ha
  have ho := h.omega _ haΩ
  obtain ⟨h128, -, -, -, -, -, e6, e7⟩ := sc_facts hX.1 hc
  have hv : a.val = c.val + 32 ∨ a.val = c.val + 56 := by
    rcases ha with rfl | rfl
    · exact Or.inl e6
    · exact Or.inr e7
  refine SCsOK.wr h hS hX ho.1 (fun y hy => ?_) ?_ (fun c' hc' => ?_)
  · rw [scA_eq]; exact (out_ne_field ho hy (h.tcbs y hy) (by simp)).symm
  · exact (out_ne_node ho h.cur hN' (by simp [layout.node.CUR_SC])).symm
  · obtain ⟨h128', -, -, f3, f4, f5, -, -⟩ := sc_facts hX.1 hc'
    rw [f3, f4, f5]
    by_cases e : c = c'
    · subst e; omega
    · have := hX.1.scDisj c hc c' hc' e; omega

/-- seL4 `suspend` (MCS) keeps the queue invariant, `BoundInv` and `XInv`,
for a thread that is not the switch-to candidate; the yield-to SC of the
thread, if any, is an SC object. -/
theorem sched.suspend.all {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s)
    (hS : SCsOK st T Ω Sg Scs Z s) (hna : L.actionW s ≠ t)
    (hyield : L.mem s (yieldA t) ≠ 0#u64 → L.mem s (yieldA t) ∈ Scs) :
    sched.suspend st ar s a t ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ∧ BoundInv st T s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z s' ∧ TmFr st T Cs Nt s s' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  have hsub := hSg.sub
  unfold sched.suspend
  refine WP.spec_bind (ipc.cancel_ipc.all s a t Q R h ht hB hX hsub) ?_
  rintro ⟨s1, a1⟩ ⟨h1, hB1, hX1, nb1, nr1, hst1, k1, -⟩
  try simp only [WP.uncurry'_pair]
  have hSg1 : SgOK st Ω Sg s1 := ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb,
    fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩
  have na1 : L.actionW s1 ≠ t := by
    rcases hst1 with e | ⟨-, e⟩
    · intro ea
      have := (h1.actOK (ea ▸ ht)).1; rw [ea, e] at this; exact not_runnable_inactive this
    · rw [e]; exact hna
  have y1 : L.mem s1 (yieldA t) = L.mem s (yieldA t) :=
    k1.fld t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  have hS1 := hS.keepT hX k1
  have tm1 : TmFr st T Cs Nt s s1 := TmFr.of_keepT k1
  step with obj.Tcb.state.spec as ⟨i, i_post⟩
  -- the fault-IP copy
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω H s2 Q R ∧ ¬ Blocked (L.mem s2 (stA t)) ∧
      L.actionW s2 ≠ t ∧ L.mem s2 (yieldA t) = L.mem s (yieldA t) ∧ BoundInv st T s2 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s2 ∧ SgOK st Ω Sg s2 ∧ SCsOK st T Ω Sg Scs Z s2 ∧
      L.mem s2 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ TmFr st T Cs Nt s s2) ?_ ?_
  · split
    · step with obj.Tcb.reg.spec as ⟨ip⟩
      refine WP.spec_mono (obj.Tcb.set_reg.fault_ip s1 t ip hta) fun s2 e => ?_
      subst e
      obtain ⟨h2, f2, a2⟩ := field_wr_keep (K := 392#u64) (v := ip) h1 ht (by simp) (by simp) (by simp)
      obtain ⟨hB2, hX2⟩ := bx_field (K := 392#u64) (v := ip) h1 hB1 hX1 hsub ht (by simp) (by simp) (by simp) (by simp)
      refine ⟨h2, ?_, by rw [a2]; exact na1, by rw [← y1]; exact f2 _ (by simp) (by simp) (by simp), hB2, hX2,
        ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg1.ks b hb, fun o h1' h2' => by
          rw [L.ksb_wr]; exact hSg1.ksΩ o h1' h2'⟩, SCsOK.field (K := 392#u64) h1 hS1 hX1 ht (by simp) (by simp) (by simp), ?_,
        tm1.trans (TmFr.wr hT h1.nodes hX1.1 (field_aligned hta (by simp) (by simp))
          (notTmW_field hT h1.nodes (fun n hn => h1.omega _ (hsub _ (hX1.1.ntB n hn).2)) ht (by simp) (by simp)))⟩
      · rw [stA_eq, f2 _ (by simp) (by simp) (by simp), ← stA_eq]; exact nb1
      · rw [stA_eq, f2 _ (by simp) (by simp) (by simp), ← stA_eq]; exact nr1
    · exact (WP.spec_ok _).2 ⟨h1, nb1, na1, y1, hB1, hX1, hSg1, hS1, nr1, tm1⟩
  rintro s2 ⟨h2, nb2, na2, y2, hB2, hX2, hSg2, hS2, nr2, tm2⟩
  -- out of the ready queue
  have hc2 := h2.aff t ht
  have hp2 := h2.prio t ht
  have hW2 : ∀ w ∈ Q (L.mem s2 (affA t)) (L.mem s2 (prioA t)), w ∈ T := fun w hw => h2.memT hc2 hp2 hw
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s2 t Q R h2 ht)
    (sched.dequeue.foot s2 t _ hT ht hp2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ((h2.ready _ hc2).1.rel _ hp2)
      (h2.queued t ht).1)) ?_
  rintro s3 ⟨h3, hw3, hinq3⟩
  obtain ⟨hB3, hX3, fr3, -⟩ := bx_qfoot h2 hB2 hX2 hSg2 hW2 hc2 ht p128 hw3
    (fun hf => by rw [hinq3] at hf; split_ifs at hf with e
                  · rw [andn_qq_qq] at hf; exact absurd rfl hf
                  · exact Or.inl hf)
    (fun hf => by rw [hinq3] at hf; split_ifs at hf with e
                  · rw [andn_qq_qr] at hf; exact Or.inr (Or.inl hf)
                  · exact Or.inr (Or.inl hf))
  have hSg3 := hSg2.fr fr3
  have hS3 := hS2.fr fr3
  have tm3 : TmFr st T Cs Nt s s3 := tm2.trans (TmFr.of_fr fr3 hX2.1 h2.nodes)
  have a3 := qfoot_act h2 hW2 hc2 ht (by omega) hw3
  have f3 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      (K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) → K.val ≠ 3592 →
      L.mem s3 (core.num.U64.wrapping_add t K) = L.mem s2 (core.num.U64.wrapping_add t K) :=
    fun K a b c d => field_qfoot hT hW2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ht hw3 ht a b c (fun _ => d)
  set Q3 := (if (L.mem s2 (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
       then Function.update Q (L.mem s2 (affA t)) (Function.update (Q (L.mem s2 (affA t))) (L.mem s2 (prioA t))
         ((Q (L.mem s2 (affA t)) (L.mem s2 (prioA t))).erase t)) else Q) with hQ3
  have nQ3 : ∀ c ∈ Cs, ∀ p : U64, p.val < 256 → t ∉ Q3 c p := by
    intro c hc p hp hm
    rw [hQ3] at hm
    split_ifs at hm with hf
    · rcases mem_upd2.1 hm with ⟨-, -, hm⟩ | ⟨hne, hm⟩
      · exact ((h2.ready _ hc2).1.rel _ hp2).nodup.not_mem_erase hm
      · obtain ⟨e1, e2⟩ := h2.inQ c hc p hp t hm
        exact hne ⟨e1.symm, e2.symm⟩
    · exact h2.notQ ht (not_not.1 hf) hc hp hm
  -- out of the release queue
  have hc3 := h3.aff t ht
  have hW3 : ∀ w ∈ R (L.mem s3 (affA t)), w ∈ T := fun w hw => h3.memTR hc3 hw
  refine WP.spec_bind (WP.spec_and (sched.release_remove.inv s3 t Q3 R h3 ht)
    (sched.release_remove.foot s3 t _ hT ht (h3.nodes _ hc3) (h3.nodes _ h3.cur) (h3.release _ hc3)
      (h3.released t ht).1)) ?_
  rintro s4 ⟨h4, hw4, hinq4⟩
  obtain ⟨hB4, hX4, fr4, -⟩ := bx_qfoot h3 hB3 hX3 hSg3 hW3 hc3 ht prel hw4
    (fun hf => by rw [hinq4] at hf; split_ifs at hf with e
                  · rw [andn_qr_qq] at hf; exact Or.inl hf
                  · exact Or.inl hf)
    (fun hf => by rw [hinq4] at hf; split_ifs at hf with e
                  · rw [andn_qr_qr] at hf; exact absurd rfl hf
                  · exact Or.inr (Or.inl hf))
  have hSg4 := hSg3.fr fr4
  have hS4 := hS3.fr fr4
  have tm4 : TmFr st T Cs Nt s s4 := tm3.trans (TmFr.of_fr fr4 hX3.1 h3.nodes)
  have a4 := qfoot_act h3 hW3 hc3 ht (by unfold RelOffs; omega) hw4
  have f4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      (K.val ≠ 3480 ∧ K.val ≠ 3488 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) → K.val ≠ 3592 →
      L.mem s4 (core.num.U64.wrapping_add t K) = L.mem s3 (core.num.U64.wrapping_add t K) :=
    fun K a b c d => field_qfoot hT hW3 (h3.nodes _ hc3) (h3.nodes _ h3.cur) ht hw4 ht a b c (fun _ => d)
  set R4 := (if (L.mem s3 (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
       then Function.update R (L.mem s3 (affA t)) ((R (L.mem s3 (affA t))).erase t) else R) with hR4
  have nR4 : ∀ c ∈ Cs, t ∉ R4 c := by
    intro c hc hm
    rw [hR4] at hm
    split_ifs at hm with hf
    · by_cases e : c = L.mem s3 (affA t)
      · subst e; rw [Function.update_self] at hm
        exact (h3.release _ hc3).nodup.not_mem_erase hm
      · rw [Function.update_of_ne e] at hm
        exact e (h3.inR c hc t hm).symm
    · exact h3.notR ht (not_not.1 hf) hc hm
  have st4 : L.mem s4 (stA t) = L.mem s2 (stA t) := by
    rw [stA_eq, f4 _ (by simp) (by simp) (by simp) (by simp), f3 _ (by simp) (by simp) (by simp) (by simp)]
  have y4 : L.mem s4 (yieldA t) = L.mem s (yieldA t) := by
    rw [← y2]; exact (f4 _ (by simp) (by simp) (by simp) (by simp)).trans (f3 _ (by simp) (by simp) (by simp) (by simp))
  have na4 : L.actionW s4 ≠ t := by rw [a4, a3]; exact na2
  -- `cancel_yield_to`
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  have hb0 : b = false := by
    rw [b_post]; simp only [decide_eq_false_iff_not]; intro e; exact hta.ne0 (by rw [e]; rfl)
  subst hb0
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨yt, yt_post⟩
  refine WP.spec_bind (Pₘ := fun s5 => SchedQueuesInv st T Cs Ω H s5 Q3 R4 ∧ L.mem s5 (stA t) = L.mem s4 (stA t) ∧
      L.actionW s5 = L.actionW s4 ∧ BoundInv st T s5 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s5 ∧ L.ksb s5 = L.ksb s4 ∧
      SCsOK st T Ω Sg Scs Z s5 ∧ TmFr st T Cs Nt s4 s5) ?_ ?_
  · split
    · rename_i hy
      have hyS : yt ∈ Scs := by rw [yt_post, y4]; exact hyield (by rw [← y4, ← yt_post]; simpa using hy)
      have hyΩ : scYieldFromA yt ∈ Ω := scword_omega hX4.1 hyS (Or.inr rfl)
      step with obj.Sc.set_yield_from.spec as ⟨s5, s5_post⟩
      subst s5_post
      obtain ⟨h5, e5⟩ := wr_omega (v := 0#u64) h4 hyΩ
      have ho := h4.omega _ hyΩ
      obtain ⟨-, -, -, -, -, -, -, e56⟩ := sc_facts hX4.1 hyS
      obtain ⟨fr1, fr2⟩ := scword_facts hX4.1 hyS (Or.inr e56)
      have tmA : TmFr st T Cs Nt s4 (L.wr s4 (scYieldFromA yt) 0#u64) :=
        TmFr.wr hT h4.nodes hX4.1 ho.1 (notTmW_omega hT h4.nodes ho
          (fun n hn e => by
            rw [show scYieldFromA yt = core.num.U64.wrapping_add yt layout.sc.YIELD_FROM from rfl, e56,
              ntfnBtA_val (hX4.1.ntP n hn)] at e
            have := hX4.1.ntOSc n hn yt hyS; have := (sc_facts hX4.1 hyS).1; omega))
      obtain ⟨hB5, hX5⟩ := bx_wr (v := 0#u64) h4 hB4 hX4 ho.1 (by
          rintro (⟨r, hr, e'⟩ | ⟨c, hc, e'⟩ | ⟨u, hu, e'⟩ | ⟨n, hn, e'⟩)
          rotate_right
          · have := hX4.1.ntSc n hn yt hyS
            have := congrArg UScalar.val e'
            obtain ⟨h128y, -⟩ := sc_facts hX4.1 hyS
            rw [show scYieldFromA yt = core.num.U64.wrapping_add yt layout.sc.YIELD_FROM from rfl, e56] at this
            omega
          · rcases e' with e' | e' | e' <;> have := congrArg UScalar.val e'
            · exact (fr1 r hr).1 this
            · exact (fr1 r hr).2.1 this
            · exact (fr1 r hr).2.2 this
          · rcases e' with e' | e' | e' | e' <;> have := congrArg UScalar.val e'
            · exact (fr2 c hc).1 this
            · exact (fr2 c hc).2.1 this
            · obtain ⟨h128c, -, -, -, -, -, e6c, -⟩ := sc_facts hX4.1 hc
              obtain ⟨h128y, -⟩ := sc_facts hX4.1 hyS
              rw [show scYieldFromA yt = core.num.U64.wrapping_add yt layout.sc.YIELD_FROM from rfl, e56, e6c] at this
              by_cases hcy : c = yt
              · rw [hcy] at this; omega
              · have := hX4.1.scDisj c hc _ hyS hcy; omega
            · obtain ⟨hPc, hzc⟩ := hX4.1.sc c hc
              obtain ⟨h128c, -⟩ := sc_facts hX4.1 hc
              obtain ⟨h128y, -⟩ := sc_facts hX4.1 hyS
              rw [show scYieldFromA yt = core.num.U64.wrapping_add yt layout.sc.YIELD_FROM from rfl, e56,
                scNtfnA_val hPc hzc] at this
              by_cases hcy : c = yt
              · rw [hcy] at this; omega
              · have := hX4.1.scDisj c hc _ hyS hcy; omega
          · rcases e' with e' | e' | e' | e'
            · rw [scA_eq] at e'; exact out_ne_field ho hu (hT u hu) (by simp) (congrArg UScalar.val e').symm
            · exact out_ne_field ho hu (hT u hu) (by simp) (congrArg UScalar.val e').symm
            · rw [stA_eq] at e'; exact out_ne_field ho hu (hT u hu) (by simp) (congrArg UScalar.val e').symm
            · exact out_ne_field ho hu (hT u hu) (by simp) (congrArg UScalar.val e').symm)
        (fun y hy => ⟨by rw [scA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm,
          by rw [inqA_eq]; exact (out_ne_field ho hy (hT y hy) (by simp)).symm⟩)
        (fun o ho' => (out_ne_node ho h4.cur (h4.nodes _ h4.cur) (by omega)).symm) (hX4.tn tmA)
      have a5 : L.actionW (L.wr s4 (scYieldFromA yt) 0#u64) = L.actionW s4 := by
        unfold LawfulStore.actionW
        simp only [LawfulStore.cpu_wr, nodeAt_wr]
        exact L.mem_wr_ne (h4.omega _ hyΩ).1 (nodeAt_aligned (h4.nodes _ h4.cur) (by rw [act_val]; omega)
          (by rw [act_val])) (fun e => out_ne_node (h4.omega _ hyΩ) h4.cur (h4.nodes _ h4.cur)
            (by rw [act_val]; omega) e.symm)
      refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
      subst e
      obtain ⟨h6, f6, a6⟩ := field_wr_keep (K := 3472#u64) (v := 0#u64) h5 ht (by simp) (by simp) (by simp)
      obtain ⟨hB6, hX6⟩ := bx_field (K := 3472#u64) (v := 0#u64) h5 hB5 hX5 hsub ht (by simp) (by simp)
        (by simp) (by simp)
      have hS5 := SCsOK.scword (v := 0#u64) h4 hS4 hX4 hyS (Or.inr rfl)
      have tmB : TmFr st T Cs Nt (L.wr s4 (scYieldFromA yt) 0#u64)
          (L.wr (L.wr s4 (scYieldFromA yt) 0#u64) (yieldA t) 0#u64) :=
        TmFr.wr hT h5.nodes hX5.1 (field_aligned (K := 3472#u64) hta (by simp) (by simp))
          (notTmW_field (K := 3472#u64) hT h5.nodes (fun n hn => h5.omega _ (hsub _ (hX5.1.ntB n hn).2)) ht
            (by simp) (by simp))
      refine ⟨h6, ?_, a6.trans a5, hB6, hX6, by simp only [L.ksb_wr],
        SCsOK.field (K := 3472#u64) h5 hS5 hX5 ht (by simp) (by simp) (by simp), tmA.trans tmB⟩
      rw [stA_eq, show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl,
        f6 _ (by simp) (by simp) (by simp), ← stA_eq, e5 t ht]
    · exact (WP.spec_ok _).2 ⟨h4, rfl, rfl, hB4, hX4, rfl, hS4, TmFr.refl (L := L) _⟩
  rintro s5 ⟨h5, st5, a5, hB5, hX5, k5, hS5, tm5⟩
  have hnr5 : ¬ Blocked (L.mem s5 (stA t)) := by rw [st5, st4]; exact nb2
  have hrp5 : L.mem s5 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := by rw [st5, st4]; exact nr2
  refine WP.spec_bind (WP.spec_and (sched.set_thread_state.inv s5 t _ Q3 R4 h5 ht not_blocked_inactive (Or.inr hnr5)
    ⟨fun c hc p hp hm => absurd hm (nQ3 c hc p hp), fun c hc hm => absurd hm (nR4 c hc),
     fun e => absurd e (by rw [a5]; exact na4)⟩) (sched.set_thread_state.state s5 t _ Q3 R4 h5 ht hX5.1 hsub)) ?_
  rintro s6 ⟨h6, e6, k6⟩
  simp only [WP.spec_ok, WP.uncurry'_pair]
  have nrr : sched.TS_INACTIVE ≠ sched.TS_BLOCKED_ON_REPLY ∧ sched.TS_INACTIVE ≠ sched.TS_BLOCKED_ON_RECV := by
    obtain ⟨-, -, h3', -⟩ := ts_vals
    rw [ts_inactive, ts_reply, h3']; decide
  exact ⟨Q3, R4, h6.congrX empty_congr, hB5.keepT h5 k6 (by rw [e6]; exact not_blocked_inactive), hX5.keepT k6 (by rw [e6]; exact nrr)
    (fun r hr e => absurd e (hX5.noref hta hrp5 (fun e' => hnr5 (Or.inr (Or.inl e'))) r hr)), hS5.keepT hX5 k6,
    tm4.trans (tm5.trans (TmFr.of_keepT k6))⟩


/-- `cancel_ipc` keeps `SCsOK`. -/
theorem ipc.cancel_ipc.scs {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z s) :
    ipc.cancel_ipc st ar s a t ⦃ s' _ => SCsOK st T Ω Sg Scs Z s' ⦄ :=
  WP.spec_mono (ipc.cancel_ipc.all s a t Q R h ht hB hX hS.sub) fun r hr => by
    obtain ⟨s', a'⟩ := r
    exact hS.keepT hX hr.2.2.2.2.2.2.1

end

end Fl4Proofs.P1

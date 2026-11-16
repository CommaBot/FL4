/-
P1: the endpoint and notification queues are sorted by priority, highest
first (`EpSorted`, seL4 `tcbEPAppend`'s order), an invariant beside
`BlkOK`.  The general step (`EpSorted.step`: the queues other than one are
untouched, and that one ends sorted), and its instances: `ep_append` and
`ntfn_append` (`insPrio_sorted`), `ep_dequeue` and `ntfn_dequeue` (a
sublist), `reorder_ep` / `reorder_ntfn` after a priority change, and any
step that leaves the queue words, the `Ep` links and the priorities alone
(`EpSorted.frame`).
-/
import Fl4Proofs.P1.QueueEntryGaps4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **The IPC queues are sorted by priority**: the queue of every heap
endpoint and notification. -/
def EpSorted (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (H : Heap) (s : S) : Prop :=
  ∀ e, (H e = some .ep ∨ H e = some .ntfn) → ∀ xs, QueueRel (L.mem s) T .Ep (L.epQ s e) xs →
    PrioSorted (fun y => L.mem s (prioA y)) xs

theorem prioSorted_congr' {pr pr' : U64 → U64} {xs : List U64} (h : PrioSorted pr xs)
    (he : ∀ y ∈ xs, pr' y = pr y) : PrioSorted pr' xs :=
  h.imp_of_mem fun ha hb hab => by rw [he _ ha, he _ hb]; exact hab

/-- The witness lists of `EpsWit` are sorted (for P3's `qSorted_of_eps`). -/
theorem EpSorted.wit {X : Set U64} {s : S} {E : Set U64} {EQ : U64 → List U64} (h : EpSorted st T H s)
    (hW : EpsWit st T Cs Ω H X s E EQ) : ∀ e ∈ E, PrioSorted (fun y => L.mem s (prioA y)) (EQ e) :=
  fun e he => h e ((hW.2.2.2.2.2.2.2.1 e).1 he) _ (hW.1 e he).2.2

/-- **The general step**: the queues other than `ep`'s keep their words,
their members' links and priorities, and `ep`'s queue is a sorted `ys`. -/
theorem EpSorted.step {X : Set U64} {s s' : S} {E : Set U64} {EQ : U64 → List U64} {ep : U64} {ys : List U64}
    (hT : TcbPlaced T) (h : EpSorted st T H s) (hW : EpsWit st T Cs Ω H X s E EQ) (hep : ep ∈ E)
    (hq : ∀ e ∈ E, e ≠ ep → L.epQ s' e = L.epQ s e)
    (hl : ∀ e ∈ E, e ≠ ep → ∀ y ∈ EQ e, L.mem s' (prevA .Ep y) = L.mem s (prevA .Ep y) ∧
      L.mem s' (nextA .Ep y) = L.mem s (nextA .Ep y))
    (hpr : ∀ e ∈ E, e ≠ ep → ∀ y ∈ EQ e, L.mem s' (prioA y) = L.mem s (prioA y))
    (hys : QueueRel (L.mem s') T .Ep (L.epQ s' ep) ys) (hs : PrioSorted (fun y => L.mem s' (prioA y)) ys) :
    EpSorted st T H s' := by
  intro e he xs hx
  have heE : e ∈ E := (hW.2.2.2.2.2.2.2.1 e).2 he
  by_cases e0 : e = ep
  · subst e0; rw [hx.unique hT hys]; exact hs
  · have hq0 := (hW.1 e heE).2.2
    have hq' : QueueRel (L.mem s') T .Ep (L.epQ s' e) (EQ e) :=
      ⟨hq0.nodup, hq0.mem, by rw [hq e heE e0]; exact hq0.head, by rw [hq e heE e0]; exact hq0.last,
        hq0.seg.congr fun y hy => hl e heE e0 y hy⟩
    rw [hx.unique hT hq']
    exact prioSorted_congr' (h e he _ hq0) fun y hy => hpr e heE e0 y hy

/-- **A step that leaves the queues alone**: no queue word of a heap object,
no `Ep` link and no priority of a TCB is written. -/
theorem EpSorted.frame {s s' : S} (h : EpSorted st T H s)
    (hq : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → L.epQ s' e = L.epQ s e)
    (hl : ∀ y ∈ T, L.mem s' (prevA .Ep y) = L.mem s (prevA .Ep y) ∧ L.mem s' (nextA .Ep y) = L.mem s (nextA .Ep y))
    (hpr : ∀ y ∈ T, L.mem s' (prioA y) = L.mem s (prioA y)) : EpSorted st T H s' := by
  intro e he xs hx
  have hx' : QueueRel (L.mem s) T .Ep (L.epQ s e) xs :=
    ⟨hx.nodup, hx.mem, by rw [← hq e he]; exact hx.head, by rw [← hq e he]; exact hx.last,
      hx.seg.congr fun y hy => ⟨(hl y (hx.mem y hy)).1.symm, (hl y (hx.mem y hy)).2.symm⟩⟩
  exact prioSorted_congr' (h e he xs hx') fun y hy => hpr y (hx.mem y hy)

/-! ## `EpFoot` steps -/

theorem epfoot_kept {s s' : S} {W : List U64} {ep b : U64} (hT : TcbPlaced T) (hWT : ∀ w ∈ W, w ∈ T)
    (w : WritesIn st s s' (EpFoot W ep)) (ha : Aligned b)
    (hlink : ∀ x ∈ W, b.val ≠ x.val + 3496 ∧ b.val ≠ x.val + 3504) (hep : b.val ≠ ep.val ∧ b.val ≠ ep.val + 8)
    (hE : EpPlaced T ep) : L.mem s' b = L.mem s b := by
  refine w.mem_eq ha ?_
  rintro (⟨x, hx, e | e⟩ | e | e) <;> have hv := congrArg UScalar.val e
  · rw [nextA_val (hT x (hWT x hx))] at hv; simp [nextOff] at hv; exact (hlink x hx).1 hv
  · rw [prevA_val (hT x (hWT x hx))] at hv; simp [prevOff] at hv; exact (hlink x hx).2 hv
  · rw [epHeadA_val] at hv; exact hep.1 hv
  · rw [epTSA_val hE] at hv; exact hep.2 hv

theorem tcb_far {x y : U64} (hx : TcbAddr x) (hy : TcbAddr y) (hne : x ≠ y) :
    x.val + 4096 ≤ y.val ∨ y.val + 4096 ≤ x.val := by
  have := hx.align; have := hy.align
  have : x.val ≠ y.val := fun e => hne (UScalar.eq_of_val_eq e)
  omega

theorem epfoot_prio {s s' : S} {W : List U64} {ep : U64} (hT : TcbPlaced T) (hWT : ∀ w ∈ W, w ∈ T)
    (w : WritesIn st s s' (EpFoot W ep)) (hE : EpPlaced T ep) :
    ∀ y ∈ T, L.mem s' (prioA y) = L.mem s (prioA y) := fun y hy => by
  have hya := hT y hy
  refine epfoot_kept hT hWT w (by unfold Aligned; rw [prioA_val hya]; have := hya.align; omega)
    (fun x hx => ?_) ?_ hE
  · rw [prioA_val hya]
    by_cases e : x = y
    · subst e; omega
    · have := tcb_far (hT x (hWT x hx)) hya e; omega
  · rw [prioA_val hya]; have := hE.disj y hy; omega

theorem epfoot_epQ {s s' : S} {W : List U64} {ep e : U64} (hT : TcbPlaced T) (hWT : ∀ w ∈ W, w ∈ T)
    (w : WritesIn st s s' (EpFoot W ep)) (hE : EpPlaced T ep) (hE' : EpPlaced T e)
    (hsep : e.val + 16 ≤ ep.val ∨ ep.val + 16 ≤ e.val) : L.epQ s' e = L.epQ s e := by
  have ke : ∀ b, (b = epHeadA e ∨ b = epTSA e) → L.mem s' b = L.mem s b := fun b hb => by
    rcases hb with rfl | rfl
    · refine epfoot_kept hT hWT w (ep_aligned hE').1 (fun x hx => ?_) ?_ hE
      · rw [epHeadA_val]; have := hE'.disj x (hWT x hx); omega
      · rw [epHeadA_val]; omega
    · refine epfoot_kept hT hWT w (ep_aligned hE').2 (fun x hx => ?_) ?_ hE
      · rw [epTSA_val hE']; have := hE'.disj x (hWT x hx); omega
      · rw [epTSA_val hE']; omega
  simp only [LawfulStore.epQ, ke _ (Or.inl rfl), ke _ (Or.inr rfl)]

theorem epfoot_link {s s' : S} {W : List U64} {ep y : U64} (hT : TcbPlaced T) (hWT : ∀ w ∈ W, w ∈ T)
    (w : WritesIn st s s' (EpFoot W ep)) (hE : EpPlaced T ep) (hyT : y ∈ T) (hyW : y ∉ W) :
    L.mem s' (prevA .Ep y) = L.mem s (prevA .Ep y) ∧ L.mem s' (nextA .Ep y) = L.mem s (nextA .Ep y) := by
  have hya := hT y hyT
  have kl : ∀ K : U64, (K.val = 3496 ∨ K.val = 3504) →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := fun K hK => by
    refine epfoot_kept hT hWT w (field_aligned hya (by omega) (by omega)) (fun x hx => ?_) ?_ hE
    · rw [field_val hya (by omega)]
      have hxy : x ≠ y := fun e => hyW (e ▸ hx)
      have := tcb_far (hT x (hWT x hx)) hya hxy; omega
    · rw [field_val hya (by omega)]; have := hE.disj y hyT; omega
  exact ⟨kl (prevOff .Ep) (by simp [prevOff]), kl (nextOff .Ep) (by simp [nextOff])⟩

/-- **An `EpFoot` step on `ep`'s queue** ending in a sorted list. -/
theorem EpSorted.epfoot {X : Set U64} {s s' : S} {E : Set U64} {EQ : U64 → List U64} {ep : U64}
    {W ys : List U64} (hT : TcbPlaced T) (h : EpSorted st T H s) (hW : EpsWit st T Cs Ω H X s E EQ)
    (hep : ep ∈ E) (hWT : ∀ w ∈ W, w ∈ T) (hWq : ∀ e ∈ E, e ≠ ep → ∀ y ∈ EQ e, y ∉ W)
    (w : WritesIn st s s' (EpFoot W ep))
    (hys : QueueRel (L.mem s') T .Ep (L.epQ s' ep) ys) (hs : PrioSorted (fun y => L.mem s (prioA y)) ys) :
    EpSorted st T H s' := by
  have hE := (hW.1 ep hep).1
  have hpr := epfoot_prio hT hWT w hE
  exact EpSorted.step hT h hW hep (fun e he hne => epfoot_epQ hT hWT w hE (hW.1 e he).1 (hW.2.1 e he ep hep hne))
    (fun e he hne y hy => epfoot_link hT hWT w hE ((hW.1 e he).2.2.mem y hy) (hWq e he hne y hy))
    (fun e he hne y hy => hpr y ((hW.1 e he).2.2.mem y hy)) hys
    (prioSorted_congr' hs fun y hy => hpr y (hys.mem y hy))

theorem endpoint.ep_append.sorted {X : Set U64} {s : S} {E : Set U64} {EQ : U64 → List U64} {ep t state : U64}
    (hT : TcbPlaced T) (h : EpSorted st T H s) (hW : EpsWit st T Cs Ω H X s E EQ) (hep : ep ∈ E) (ht : t ∈ T)
    (hnq : ∀ e ∈ E, t ∉ EQ e) :
    endpoint.ep_append st s ep t state ⦃ s' => EpSorted st T H s' ⦄ := by
  obtain ⟨hE, -, hq⟩ := hW.1 ep hep
  refine WP.spec_mono (WP.spec_and (endpoint.ep_append.rel s ep t state _ hT hE hq ht (hnq ep hep))
    (endpoint.ep_append.foot s ep t state _ hT hE hq ht (hnq ep hep))) fun s' ⟨⟨hr, _⟩, w⟩ => ?_
  refine EpSorted.epfoot hT h hW hep (fun y hy => ?_) (fun e he hne y hy hyW => ?_) w hr
    (insPrio_sorted _ _ t _ (h ep ((hW.2.2.2.2.2.2.2.1 ep).1 hep) _ hq) rfl)
  · rcases List.mem_cons.1 hy with rfl | hy
    · exact ht
    · exact hq.mem y hy
  · rcases List.mem_cons.1 hyW with rfl | hyW
    · exact hnq e he hy
    · have h1 := (hW.2.2.2.1 e he y hy).2.1
      have h2 := (hW.2.2.2.1 ep hep y hyW).2.1
      exact hne (h1.symm.trans h2)

theorem notification.ntfn_append.sorted {X : Set U64} {s : S} {E : Set U64} {EQ : U64 → List U64} {n t : U64}
    (hT : TcbPlaced T) (h : EpSorted st T H s) (hW : EpsWit st T Cs Ω H X s E EQ) (hn : n ∈ E) (ht : t ∈ T)
    (hnq : ∀ e ∈ E, t ∉ EQ e) :
    notification.ntfn_append st s n t ⦃ s' => EpSorted st T H s' ⦄ := by
  obtain ⟨hE, -, hq⟩ := hW.1 n hn
  refine WP.spec_mono (WP.spec_and (notification.ntfn_append.rel s n t _ hT hE hq ht (hnq n hn))
    (notification.ntfn_append.foot s n t _ hT hE hq ht (hnq n hn))) fun s' ⟨⟨hr, _⟩, w⟩ => ?_
  refine EpSorted.epfoot hT h hW hn (fun y hy => ?_) (fun e he hne y hy hyW => ?_) w hr
    (insPrio_sorted _ _ t _ (h n ((hW.2.2.2.2.2.2.2.1 n).1 hn) _ hq) rfl)
  · rcases List.mem_cons.1 hy with rfl | hy
    · exact ht
    · exact hq.mem y hy
  · rcases List.mem_cons.1 hyW with rfl | hyW
    · exact hnq e he hy
    · have h1 := (hW.2.2.2.1 e he y hy).2.1
      have h2 := (hW.2.2.2.1 n hn y hyW).2.1
      exact hne (h1.symm.trans h2)

theorem endpoint.ep_dequeue.sorted {X : Set U64} {s : S} {E : Set U64} {EQ : U64 → List U64} {ep t : U64}
    (hT : TcbPlaced T) (h : EpSorted st T H s) (hW : EpsWit st T Cs Ω H X s E EQ) (hep : ep ∈ E)
    (ht : t ∈ EQ ep) :
    endpoint.ep_dequeue st s ep t ⦃ s' => EpSorted st T H s' ⦄ := by
  obtain ⟨hE, -, hq⟩ := hW.1 ep hep
  refine WP.spec_mono (WP.spec_and (endpoint.ep_dequeue.rel s ep t _ hT hE hq ht)
    (endpoint.ep_dequeue.foot s ep t _ hT hE hq ht)) fun s' ⟨⟨hr, _⟩, w⟩ => ?_
  refine EpSorted.epfoot hT h hW hep (fun y hy => hq.mem y hy) (fun e he hne y hy hyW => ?_) w hr
    ((h ep ((hW.2.2.2.2.2.2.2.1 ep).1 hep) _ hq).sublist (List.erase_sublist))
  have h1 := (hW.2.2.2.1 e he y hy).2.1
  have h2 := (hW.2.2.2.1 ep hep y hyW).2.1
  exact hne (h1.symm.trans h2)

theorem notification.ntfn_dequeue.sorted {X : Set U64} {s : S} {E : Set U64} {EQ : U64 → List U64} {n t : U64}
    (hT : TcbPlaced T) (h : EpSorted st T H s) (hW : EpsWit st T Cs Ω H X s E EQ) (hn : n ∈ E)
    (ht : t ∈ EQ n) :
    notification.ntfn_dequeue st s n t ⦃ s' => EpSorted st T H s' ⦄ := by
  obtain ⟨hE, -, hq⟩ := hW.1 n hn
  refine WP.spec_mono (WP.spec_and (notification.ntfn_dequeue.rel s n t _ hT hE hq ht)
    (notification.ntfn_dequeue.foot s n t _ hT hE hq ht)) fun s' ⟨⟨hr, _⟩, w⟩ => ?_
  refine EpSorted.epfoot hT h hW hn (fun y hy => hq.mem y hy) (fun e he hne y hy hyW => ?_) w hr
    ((h n ((hW.2.2.2.2.2.2.2.1 n).1 hn) _ hq).sublist (List.erase_sublist))
  have h1 := (hW.2.2.2.1 e he y hy).2.1
  have h2 := (hW.2.2.2.1 n hn y hyW).2.1
  exact hne (h1.symm.trans h2)

/-! ## `set_priority`

The running path touches the ready queues, the thread's priority and
scheduler words, never an `Ep` link, an endpoint word or the priority of
another thread (`NoEp`); the blocked path changes the thread's priority and
moves it to its place in its queue (`reorder_ep` / `reorder_ntfn`). -/

/-- No `Ep` link of a TCB and no priority except `u`'s changes. -/
def NoEp (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (u : U64) (s s' : S) : Prop :=
  ∀ y ∈ T, L.mem s' (prevA .Ep y) = L.mem s (prevA .Ep y) ∧ L.mem s' (nextA .Ep y) = L.mem s (nextA .Ep y) ∧
    (y ≠ u → L.mem s' (prioA y) = L.mem s (prioA y))

theorem NoEp.refl (u : U64) (s : S) : NoEp st T u s s := fun _ _ => ⟨rfl, rfl, fun _ => rfl⟩

theorem NoEp.trans {u : U64} {s₁ s₂ s₃ : S} (h₁ : NoEp st T u s₁ s₂) (h₂ : NoEp st T u s₂ s₃) :
    NoEp st T u s₁ s₃ := fun y hy =>
  ⟨(h₂ y hy).1.trans (h₁ y hy).1, (h₂ y hy).2.1.trans (h₁ y hy).2.1,
    fun hne => ((h₂ y hy).2.2 hne).trans ((h₁ y hy).2.2 hne)⟩

/-- The protected words of `y`: its `Ep` links and, unless `y = u`, its priority. -/
abbrev EpK (u y K : U64) : Prop := K.val = 3496 ∨ K.val = 3504 ∨ (y ≠ u ∧ K.val = 3448)

theorem epK_val {u y K : U64} (h : EpK u y K) : K.val = 3496 ∨ K.val = 3504 ∨ K.val = 3448 := by
  rcases h with h | h | ⟨_, h⟩ <;> simp [h]

theorem NoEp.of {u : U64} {s s' : S} {A : U64 → Prop} (hT : TcbPlaced T) (w : WritesIn st s s' A)
    (hA : ∀ b, A b → ∀ y ∈ T, ∀ K : U64, EpK u y K → b ≠ core.num.U64.wrapping_add y K) : NoEp st T u s s' := by
  intro y hy
  have k : ∀ K : U64, EpK u y K →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := fun K hK => by
    have := epK_val hK
    exact w.mem_eq (field_aligned (hT y hy) (by omega) (by omega)) fun hb => hA _ hb y hy K hK rfl
  exact ⟨k (prevOff .Ep) (Or.inr (Or.inl (by simp [prevOff]))), k (nextOff .Ep) (Or.inl (by simp [nextOff])),
    fun hne => k 3448#u64 (Or.inr (Or.inr ⟨hne, by simp⟩))⟩

theorem qfoot_noEp {s : S} {W : List U64} {c t b : U64} {P : Nat → Prop} (hT : TcbPlaced T)
    (hW : ∀ w ∈ W, w ∈ T) (hN : NodePlaced st T s c) (hN' : NodePlaced st T s (L.cpu s)) (ht : t ∈ T)
    (h : L.QFoot s W c P t b) {u : U64} : ∀ y ∈ T, ∀ K : U64, EpK u y K → b ≠ core.num.U64.wrapping_add y K := by
  intro y hy K hK
  have hK' := epK_val hK
  rcases h with ⟨w, hw, rfl | rfl⟩ | ⟨o, -, ho, -, rfl⟩ | rfl | ⟨o, -, ho, -, rfl⟩
  · show core.num.U64.wrapping_add w (nextOff .Sched) ≠ _
    exact field_ne (hT w (hW w hw)) (hT y hy) (by simp [nextOff]) (by omega) (fun _ => by simp [nextOff]; omega)
  · show core.num.U64.wrapping_add w (prevOff .Sched) ≠ _
    exact field_ne (hT w (hW w hw)) (hT y hy) (by simp [prevOff]) (by omega) (fun _ => by simp [prevOff]; omega)
  · exact node_ne_field hN ho hy (hT y hy) (by omega)
  · show core.num.U64.wrapping_add t 3592#u64 ≠ _
    exact field_ne (hT t ht) (hT y hy) (by simp) (by omega) (fun _ => by simp; omega)
  · exact node_ne_field hN' ho hy (hT y hy) (by omega)

section noep
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem sched.dequeue.noEp (u : U64) (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => NoEp st T u s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  exact WP.spec_mono (sched.dequeue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (h.queued t ht).1) fun s' hh => NoEp.of h.tcbs hh.1 fun b hb =>
      qfoot_noEp h.tcbs (hR1.1.rel _ hp).mem (h.nodes _ hc) (h.nodes _ h.cur) ht hb

theorem sched.enqueue.noEp (u : U64) (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.enqueue st s t ⦃ s' => NoEp st T u s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => NoEp.of h.tcbs hh.1 fun b hb =>
      qfoot_noEp h.tcbs ?_ (h.nodes _ hc) (h.nodes _ h.cur) ht hb
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

theorem sched.set_action.noEp (u : U64) (s : S) (v : U64) (hN : NodePlaced st T s (L.cpu s)) (hT : TcbPlaced T) :
    sched.set_action st s v ⦃ s' => NoEp st T u s s' ⦄ :=
  WP.spec_mono (sched.set_action.spec s v) fun s' e => by
    subst e
    exact NoEp.of hT (writesIn_wr (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val])))
      fun b hb y hy K hK => by
        subst hb; have := epK_val hK; exact node_ne_field hN (by rw [act_val]; omega) hy (hT y hy) (by omega)

theorem sched.reschedule_required.noEp (u : U64) (s : S) (h : SchedQueuesInvX st T Cs Ω H X s Q R) :
    sched.reschedule_required st s ⦃ s' => NoEp st T u s s' ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  have hpart : (if (act != sched.ACTION_RESUME_CURRENT) = true then
      if (act != sched.ACTION_CHOOSE_NEW) = true then do
        let b ← sched.is_schedulable st s act
        if b = true then sched.enqueue st s act else ok s
      else ok s
    else ok s) ⦃ s1 => NoEp st T u s s1 ∧ WritesIn st s s1 (fun _ => True) ⦄ := by
    split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · exact WP.spec_and (sched.enqueue.noEp u s act h hT)
            (WP.spec_mono (sched.enqueue.kw (Sg := ∅) (Scs := ∅) (Z := fun _ => 0) (Es := ∅) s act h hT)
              fun s' f => ⟨f.1, f.2.1, fun b _ hn => absurd trivial hn⟩)
        · exact (WP.spec_ok _).2 ⟨NoEp.refl _ _, WritesIn.refl _ _⟩
      · exact (WP.spec_ok _).2 ⟨NoEp.refl _ _, WritesIn.refl _ _⟩
    · exact (WP.spec_ok _).2 ⟨NoEp.refl _ _, WritesIn.refl _ _⟩
  refine WP.spec_bind hpart fun s1 ⟨f1, w1⟩ => ?_
  exact WP.spec_mono (sched.set_action.noEp u s1 _ (by rw [w1.2.1]; exact (h.nodes _ h.cur).ksb w1.1) h.tcbs)
    fun s2 f2 => f1.trans f2

theorem wr_prio_noEp {s : S} {t v : U64} (hT : TcbPlaced T) (ht : t ∈ T) :
    NoEp st T t s (L.wr s (prioA t) v) :=
  NoEp.of hT (writesIn_wr (field_aligned (hT t ht) (by simp) (by simp))) fun b hb y hy K hK => by
    subst hb; have := epK_val hK
    exact field_ne (hT t ht) (hT y hy) (by simp) (by omega) fun e => by
      subst e; rcases hK with h | h | ⟨hne, _⟩
      · simp [h]
      · simp [h]
      · exact absurd rfl hne

theorem dpe_noEp (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hnr : ∀ c ∈ Cs, t ∉ R c) (hrun : Runnable (L.mem s (stA t))) :
    (do
      let s1 ← sched.dequeue st s t
      let s2 ← obj.Tcb.set_prio st t s1 prio
      let s3 ← sched.enqueue st s2 t
      sched.reschedule_required st s3) ⦃ s' => NoEp st T t s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
      (h.queued t ht).1)) (sched.dequeue.noEp t s t h ht)) ?_
  rintro s1 ⟨⟨h1, hw1, -⟩, f1⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  obtain ⟨hsb1, -, -⟩ := ext_qfoot h.tcbs hW1 (h.nodes _ hc) (h.nodes _ h.cur) ht hc h.cur hw1
  have hq1 : (L.mem s1 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hcn
    exact notQ_after_dequeue h ht _ (h1.aff t ht) _ (h1.prio t ht) ((h1.queued t ht).1 hcn)
  step with obj.Tcb.set_prio.spec as ⟨s2, s2_post⟩
  subst s2_post
  have f2 : NoEp st T t s1 (L.wr s1 (prioA t) prio) := wr_prio_noEp h1.tcbs ht
  have h2 := inv_wr_prio h1 ht hq1 hv
  have hr2 : (L.mem (L.wr s1 (prioA t) prio) (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact hnr _ (h2.aff t ht) ((h2.released t ht).1 hcn)
  have hrun2 : Runnable (L.mem (L.wr s1 (prioA t) prio) (stA t)) := by
    rw [(prio_wr_eps (prio := prio) h1 ht).2, (hsb1 t ht).1]
    exact hrun
  refine WP.spec_bind (WP.spec_and (sched.enqueue.inv _ t _ R h2 ht (fun _ => hr2) (fun _ => hrun2))
    (sched.enqueue.noEp t _ t h2 ht)) ?_
  rintro s3 ⟨h3, f3⟩
  exact WP.spec_mono (sched.reschedule_required.noEp t s3 h3)
    fun s' f4 => f1.trans (f2.trans (f3.trans f4))

theorem running_noEp (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hv : prio.val < 256)
    (hrun : Runnable (L.mem s (stA t)))
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    (do
      let b ← sched.queued st s t
      if b = true then do
        let s1 ← sched.dequeue st s t
        let s2 ← obj.Tcb.set_prio st t s1 prio
        let s3 ← sched.enqueue st s2 t
        sched.reschedule_required st s3
      else do
        let t1 ← sched.cur_thread st s
        let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1
        if b1 = true then do
          let s1 ← sched.dequeue st s t
          let s2 ← obj.Tcb.set_prio st t s1 prio
          let s3 ← sched.enqueue st s2 t
          sched.reschedule_required st s3
        else obj.Tcb.set_prio st t s prio) ⦃ s' => NoEp st T t s s' ⦄ := by
  step with sched.queued.spec as ⟨b, b_post⟩
  split
  · have hq1 : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 := by
      intro hc; have := ‹b = true›; rw [b_post] at this; exact of_decide_eq_true this hc
    have htq := (h.queued t ht).1 hq1
    exact dpe_noEp s t prio Q R h ht hv (fun c hc => h.QR (h.aff t ht) (h.prio t ht) htq hc) hrun
  · step with sched.cur_thread.spec as ⟨t1, t1_post⟩
    step with tcb_eq.blk as ⟨b1, b1_post⟩
    split
    · have e : t = t1 := by simpa [b1_post] using ‹b1 = true›
      have hr0 := hcur (e.trans t1_post)
      exact dpe_noEp s t prio Q R h ht hv (fun c hc => h.notR ht hr0 hc) hrun
    · step with obj.Tcb.set_prio.spec as ⟨s1, s1_post⟩
      subst s1_post
      exact wr_prio_noEp h.tcbs ht

end noep

/-- **A step that keeps the queue words and links**, and every priority but
that of a thread `u` in no queue. -/
theorem EpSorted.keep {s s' : S} {u : U64} (h : EpSorted st T H s)
    (hq : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → L.epQ s' e = L.epQ s e) (hk : NoEp st T u s s')
    (hu : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → ∀ xs, QueueRel (L.mem s) T .Ep (L.epQ s e) xs → u ∉ xs) :
    EpSorted st T H s' := by
  intro e he xs hx
  have hx' : QueueRel (L.mem s) T .Ep (L.epQ s e) xs :=
    ⟨hx.nodup, hx.mem, by rw [← hq e he]; exact hx.head, by rw [← hq e he]; exact hx.last,
      hx.seg.congr fun y hy => ⟨(hk y (hx.mem y hy)).1.symm, (hk y (hx.mem y hy)).2.1.symm⟩⟩
  exact prioSorted_congr' (h e he xs hx') fun y hy =>
    (hk y (hx.mem y hy)).2.2 fun e' => hu e he xs hx' (e' ▸ hy)

theorem not_runnable_blocked {v : U64} (hr : Runnable v) (hb : Blocked v) : False := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := ts_vals
  rcases hr with e | e | e <;> rcases hb with e' | e' | e' <;> rw [e'] at e <;>
    simp_all [sched.TS_RUNNING_VM]

/-- The blocked path: the priority is written, and `reorder` (`reorder_ep` or
`reorder_ntfn`) puts the thread back in priority order. -/
theorem blocked_sorted (s : S) (t : obj.Tcb) (prio : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T) (hb : Blocked (L.mem s (stA t))) (hS : EpSorted st T H s)
    (reorder : S → U64 → obj.Tcb → Result S)
    (hrel : ∀ (s : S) (ep : U64) (xs : List U64), TcbPlaced T → EpPlaced T ep →
      QueueRel (L.mem s) T .Ep (L.epQ s ep) xs → t ∈ xs → reorder s ep t ⦃ s' =>
        QueueRel (L.mem s') T .Ep (L.epQ s' ep) (insPrio (fun y => L.mem s (prioA y)) (L.mem s (prioA t)) t (xs.erase t)) ∧
        L.epState s' ep = L.epState s ep ⦄)
    (hfoot : ∀ (s : S) (ep : U64) (xs : List U64), TcbPlaced T → EpPlaced T ep →
      QueueRel (L.mem s) T .Ep (L.epQ s ep) xs → t ∈ xs → reorder s ep t ⦃ s' => WritesIn st s s' (EpFoot xs ep) ⦄) :
    (do
      let s1 ← obj.Tcb.set_prio st t s prio
      let i ← obj.Tcb.block_obj st t s1
      reorder s1 i t) ⦃ s' => EpSorted st T H s' ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  obtain ⟨E, EQ, hEW⟩ := h.eps
  obtain ⟨heE, htm⟩ := hEW.2.2.2.2.1 t ht (by simp) hb
  set ep := L.mem s (blockA t)
  obtain ⟨hE, -, hq⟩ := hEW.1 ep heE
  step with obj.Tcb.set_prio.spec as ⟨s1, s1_post⟩
  subst s1_post
  have hpa : Aligned (prioA t) := field_aligned hta (by simp) (by simp)
  have k1 : ∀ b, Aligned b → (prioA t).val ≠ b.val → L.mem (L.wr s (prioA t) prio) b = L.mem s b :=
    fun b hb hne => L.mem_wr_ne hpa hb hne
  have hpv := prioA_val hta
  have hq1e : ∀ e ∈ E, L.epQ (L.wr s (prioA t) prio) e = L.epQ s e := fun e he => by
    have hE' := (hEW.1 e he).1
    have := hE'.disj t ht
    simp only [LawfulStore.epQ, k1 _ (ep_aligned hE').1 (by rw [epHeadA_val]; omega),
      k1 _ (ep_aligned hE').2 (by rw [epTSA_val hE']; omega)]
  have hl1 : ∀ y ∈ T, L.mem (L.wr s (prioA t) prio) (prevA .Ep y) = L.mem s (prevA .Ep y) ∧
      L.mem (L.wr s (prioA t) prio) (nextA .Ep y) = L.mem s (nextA .Ep y) := fun y hy =>
    ⟨((wr_prio_noEp (v := prio) hT ht) y hy).1, ((wr_prio_noEp (v := prio) hT ht) y hy).2.1⟩
  have hpr1 : ∀ y ∈ T, y ≠ t → L.mem (L.wr s (prioA t) prio) (prioA y) = L.mem s (prioA y) :=
    fun y hy hne => ((wr_prio_noEp (v := prio) hT ht) y hy).2.2 hne
  have hq' : QueueRel (L.mem (L.wr s (prioA t) prio)) T .Ep (L.epQ (L.wr s (prioA t) prio) ep) (EQ ep) :=
    ⟨hq.nodup, hq.mem, by rw [hq1e ep heE]; exact hq.head, by rw [hq1e ep heE]; exact hq.last,
      hq.seg.congr fun y hy => hl1 y (hq.mem y hy)⟩
  have hbl : L.mem (L.wr s (prioA t) prio) (blockA t) = ep := (prio_wr_eps (prio := prio) h ht).1
  step with obj.Tcb.block_obj.spec as ⟨i, i_post⟩
  subst i_post
  rw [hbl]
  refine WP.spec_mono (WP.spec_and (hrel _ ep _ hT hE hq' htm) (hfoot _ ep _ hT hE hq' htm)) ?_
  rintro s2 ⟨⟨hr2, _⟩, w2⟩
  have hWT : ∀ w ∈ EQ ep, w ∈ T := hq.mem
  have hpr2 := epfoot_prio hT hWT w2 hE
  have hmem : ∀ e ∈ E, ∀ y ∈ EQ e, L.mem s (blockA y) = e := fun e he y hy => (hEW.2.2.2.1 e he y hy).2.1
  have hsrt : PrioSorted (fun y => L.mem (L.wr s (prioA t) prio) (prioA y)) ((EQ ep).erase t) :=
    prioSorted_congr' ((hS ep ((hEW.2.2.2.2.2.2.2.1 ep).1 heE) _ hq).sublist List.erase_sublist)
      fun y hy => hpr1 y (hq.mem y (List.mem_of_mem_erase hy)) fun e => by
        subst e; exact hq.nodup.not_mem_erase hy
  refine EpSorted.step hT hS hEW heE (fun e he hne => ?_) (fun e he hne y hy => ?_) (fun e he hne y hy => ?_) hr2
    (prioSorted_congr' (insPrio_sorted _ _ t _ hsrt rfl) fun y hy => hpr2 y (hr2.mem y hy))
  · rw [epfoot_epQ hT hWT w2 hE (hEW.1 e he).1 (hEW.2.1 e he ep heE hne), hq1e e he]
  · have hyT := (hEW.1 e he).2.2.mem y hy
    have hyW : y ∉ EQ ep := fun hy' => hne ((hmem e he y hy).symm.trans (hmem ep heE y hy'))
    obtain ⟨a1, a2⟩ := epfoot_link hT hWT w2 hE hyT hyW
    exact ⟨a1.trans (hl1 y hyT).1, a2.trans (hl1 y hyT).2⟩
  · have hyT := (hEW.1 e he).2.2.mem y hy
    have hyt : y ≠ t := fun e' => hne ((hmem e he y hy).symm.trans (e' ▸ hmem ep heE t htm))
    rw [hpr2 y hyT, hpr1 y hyT hyt]

/-- **`set_priority` keeps the queues sorted**: a running thread is in no IPC
queue and the scheduler work touches none; a blocked thread is moved to its
place for the new priority. -/
theorem sched.set_priority.sorted (s : S) (t : obj.Tcb) (prio : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hv : prio.val < 256)
    (hcur : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) →
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) (hS : EpSorted st T H s) :
    sched.set_priority st s t prio ⦃ s' => EpSorted st T H s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, hSg⟩ := h
  obtain ⟨r1, r2, r3, r4, r5⟩ := ts_vals
  have run : Runnable (L.mem s (stA t)) →
      (do
        let b ← sched.queued st s t
        if b = true then do
          let s1 ← sched.dequeue st s t
          let s2 ← obj.Tcb.set_prio st t s1 prio
          let s3 ← sched.enqueue st s2 t
          sched.reschedule_required st s3
        else do
          let t1 ← sched.cur_thread st s
          let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1
          if b1 = true then do
            let s1 ← sched.dequeue st s t
            let s2 ← obj.Tcb.set_prio st t s1 prio
            let s3 ← sched.enqueue st s2 t
            sched.reschedule_required st s3
          else obj.Tcb.set_prio st t s prio) ⦃ s' => EpSorted st T H s' ⦄ := fun hrun =>
    WP.spec_mono (WP.spec_and (running_kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s t prio Q R h0 ht hv hrun hcur)
      (running_noEp s t prio Q R h0 ht hv hrun hcur)) fun s' ⟨f, k⟩ => by
      refine EpSorted.keep hS (fun e he => ?_) k fun e he xs hx hm => ?_
      · obtain ⟨a1, a2⟩ := Foot.epQ f h0 hX.1 hSg.sub he
        simp only [LawfulStore.epQ, a1, a2]
      · obtain ⟨E, EQ, hEW⟩ := h0.eps
        have heE := (hEW.2.2.2.2.2.2.2.1 e).2 he
        rw [hx.unique h0.tcbs (hEW.1 e heE).2.2] at hm
        exact not_runnable_blocked hrun (hEW.2.2.2.1 e heE t hm).2.2
  unfold sched.set_priority
  step with obj.Tcb.state.spec as ⟨sv, sv_post⟩
  subst sv_post
  split
  · exact run (Or.inl ‹_›)
  · split
    · exact run (Or.inr (Or.inl ‹_›))
    · split
      · exact run (Or.inr (Or.inr ‹_›))
      · have fe := fun (s : S) ep xs hT hE hq hm => endpoint.reorder_ep.foot (st := st) (T := T) s ep t xs hT hE hq hm
        have re := fun (s : S) ep xs hT hE hq hm => endpoint.reorder_ep.rel (st := st) (T := T) s ep t xs hT hE hq hm
        have fn := fun (s : S) ep xs hT hE hq hm =>
          notification.reorder_ntfn.foot (st := st) (T := T) s ep t xs hT hE hq hm
        have rn := fun (s : S) ep xs hT hE hq hm =>
          notification.reorder_ntfn.rel (st := st) (T := T) s ep t xs hT hE hq hm
        split
        · exact blocked_sorted s t prio Q R h0 ht (Or.inr (Or.inl ‹_›)) hS _ re fe
        · split
          · exact blocked_sorted s t prio Q R h0 ht (Or.inl ‹_›) hS _ re fe
          · split
            · exact blocked_sorted s t prio Q R h0 ht (Or.inr (Or.inr ‹_›)) hS _ rn fn
            · have hnr : ¬ Runnable (L.mem s (stA t)) := by rintro (e | e | e) <;> contradiction
              have hnb : ¬ Blocked (L.mem s (stA t)) := by rintro (e | e | e) <;> contradiction
              step with obj.Tcb.set_prio.spec as ⟨s1, s1_post⟩
              subst s1_post
              refine EpSorted.keep hS (fun e he => ?_) (wr_prio_noEp h0.tcbs ht) fun e he xs hx hm => ?_
              · obtain ⟨E, EQ, hEW⟩ := h0.eps
                have hE' := (hEW.1 e ((hEW.2.2.2.2.2.2.2.1 e).2 he)).1
                have := hE'.disj t ht
                have hpv := prioA_val (h0.tcbs t ht)
                have hpa : Aligned (prioA t) := field_aligned (h0.tcbs t ht) (by simp) (by simp)
                simp only [LawfulStore.epQ, L.mem_wr_ne hpa (ep_aligned hE').1 (by rw [epHeadA_val]; omega),
                  L.mem_wr_ne hpa (ep_aligned hE').2 (by rw [epTSA_val hE']; omega)]
              · obtain ⟨E, EQ, hEW⟩ := h0.eps
                have heE := (hEW.2.2.2.2.2.2.2.1 e).2 he
                rw [hx.unique h0.tcbs (hEW.1 e heE).2.2] at hm
                exact hnb (hEW.2.2.2.1 e heE t hm).2.2

end

end Fl4Proofs.P1

/-
P3 (DESIGN.md §9), untyped: **`XTopAt` with fresh TCBs added to `T`**
(handoff/utj.md "uttypes", ut39; l4v `retype_region` of `TCBObject`s: the
new TCBs join the relation's TCB set, as `XTopAt.addE`/`addN` for
endpoints and notifications).

* `specDropT`, `ostep_dropT`, `specAdd_dropT`: the spec's state with the new
  TCBs removed, an `OStep` over them and the `SpecAdd` back;
* `Sched.SchedRel.add_tcbsAt`: `SchedRel.add_tcbs` at one state (the TCBs
  already in the spec's heap, `default_tcb 0`), through `specDropT`;
* `oobj_unionT`: an `OObj` word of `T ∪ W` is an old one or in a new TCB;
* `XTopAt.addT`: `XTopAt` at `T ∪ W` from `XTopAt` at `T` with the new TCBs
  `default_tcb 0` in the spec, their scheduler, state, fault, bound,
  priority and badge words zero, their registers `new_context`'s, apart from
  the core's node and the kernel-state block, their blocks holding no `OObj`
  word of the old sets and their words past the slots no `VObj` word.
-/
import Fl4Proofs.P3.UtEpXTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Drop
variable {σ : Fl4Spec.State Unit}

/-- The spec's state with the TCBs at `W` removed. -/
def specDropT (σ : Fl4Spec.State Unit) (W : Set U64) : Fl4Spec.State Unit :=
  { σ with kheap := fun p => if Sched.TW W p then none else σ.kheap p }

theorem ostep_dropT (W : Set U64) : OStep (Sched.TW W) σ (specDropT σ W) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q hq => ?_⟩
  by_cases h : Sched.TW W q
  · exact ⟨Or.inl h, Or.inl (by simp [specDropT, h])⟩
  · exact absurd (by simp [specDropT, h]) hq

theorem specAdd_dropT {W : Set U64} (hkt : ∀ t ∈ W, σ.kheap t.bv = some (.tcb (Fl4Spec.defaultTcb 0))) :
    Sched.SpecAdd (specDropT σ W) σ (Sched.TW W) (fun _ => .tcb (Fl4Spec.defaultTcb 0)) := by
  refine ⟨rfl, rfl, fun p hp => ⟨by simp [specDropT, hp], ?_⟩, fun p hp => by simp [specDropT, hp]⟩
  obtain ⟨t, ht, rfl⟩ := hp
  exact hkt t ht

theorem specDropT_sub {W : Set U64} {p : Fl4Spec.ObjRef} {k : Fl4Spec.KernelObject}
    (h : (specDropT σ W).kheap p = some k) : σ.kheap p = some k := by
  unfold specDropT at h
  dsimp only at h
  split_ifs at h
  exact h

end Drop

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {σ : Fl4Spec.State Unit}

/-- **The scheduler relation over TCBs already in the spec's heap**
(`SchedRel.add_tcbs` at one state). -/
theorem Sched.SchedRel.add_tcbsAt {N T C W : Set U64} {c : U64} {s : S}
    (hS : Sched.SchedRel st N T C c s σ)
    (hkt : ∀ t ∈ W, σ.kheap t.bv = some (.tcb (Fl4Spec.defaultTcb 0)))
    (hW : ∀ t ∈ W, P1.TcbAddr t ∧ t ∉ T) (hWC : ∀ t ∈ W, t ∉ C) (hc0 : c = 0#u64)
    (hnd : ∀ t ∈ W, t.val + 2 ^ 12 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ t.val)
    (hks : ∀ t ∈ W, t.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val)
    (hnt : ∀ n ∈ N, ∀ t ∈ W, t.val + 4096 ≤ n.val ∨ n.val + 64 ≤ t.val)
    (hsc : ∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → ∀ a : U64, Sched.ScObj sc n a →
      ∀ t ∈ W, a.val < t.val ∨ t.val + 4096 ≤ a.val)
    (hm : ∀ t ∈ W, ∀ K, Sched.SchedField K → L.mem s (core.num.U64.wrapping_add t K) = 0#u64) :
    Sched.SchedRel st N (T ∪ W) C c s σ := by
  have h0 := Vs.SchedRel.specFrame hS (ostep_dropT (σ := σ) W)
    (fun t ht h => by
      obtain ⟨t', ht', e⟩ := h
      exact (hW t' ht').2 (P1.eq_of_bv e ▸ ht))
    (fun sc hsc h => by
      obtain ⟨t', ht', e⟩ := h
      exact hWC t' ht' (P1.eq_of_bv e ▸ hsc))
  have ha : Sched.SAgree st T C c s s :=
    ⟨rfl, rfl, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩
  exact Sched.SchedRel.add_tcbs h0 ha rfl rfl hW hc0 hnd hks hnt
    (fun sc hsc' x n hx => hsc sc hsc' x n (specDropT_sub hx)) hm (specAdd_dropT hkt)

variable {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- An `OObj` word of the sets with `T ∪ W` is one of the old sets' or in a
new TCB past its slots. -/
theorem oobj_unionT {s : S} {W : Set U64} {b : U64} (h : OObj st N (T ∪ W) C E R B c s σ b) :
    OObj st N T C E R B c s σ b ∨ ∃ t ∈ W, t.val + 256 ≤ b.val ∧ b.val < t.val + 4096 := by
  unfold OObj at h
  rcases h with h | h | ⟨t, ht, h1, h2⟩ | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · rcases ht with ht | ht
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, h1, h2⟩)))
    · exact Or.inr ⟨t, ht, h1, h2⟩
  · exact Or.inl (Or.inr (Or.inr (Or.inr h)))

set_option maxHeartbeats 2000000 in
/-- **`XTopAt` with fresh TCBs added to `T`** (module docstring). -/
theorem XTopAt.addT {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A}
    (hX : XTopAt (L := L) AR Z s a σ) {W : Set U64}
    (hkt : ∀ t ∈ W, σ.kheap t.bv = some (.tcb (Fl4Spec.defaultTcb 0)))
    (hW : ∀ t ∈ W, P1.TcbAddr t ∧ t ∉ Z.T) (hWC : ∀ t ∈ W, t ∉ Z.C) (hc0 : Z.c = 0#u64)
    (hm : ∀ t ∈ W, ∀ K, Sched.SchedField K → L.mem s (core.num.U64.wrapping_add t K) = 0#u64)
    (hmt : ∀ t ∈ W, L.mem s (Notif.tStA t) = 0#u64 ∧ L.mem s (P1.prioA t) = 0#u64 ∧
      L.mem s (Endp.tFaultA t) = 0#u64 ∧ L.mem s (Endp.tBoundA t) = 0#u64 ∧
      L.mem s (Notif.badgeRegA t) = 0#u64 ∧
      ∀ r, (L.mem s (Endp.regA t (Endp.regIdx r))).bv = Fl4Spec.newContext.userRegs r)
    (hnd : ∀ t ∈ W, t.val + 2 ^ 12 ≤ L.nodeBase s Z.c ∨ L.nodeBase s Z.c + 4288 ≤ t.val)
    (hks : ∀ t ∈ W, t.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val)
    (hfrO : ∀ t ∈ W, ∀ b : U64, t.val ≤ b.val → b.val < t.val + 4096 →
      ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b)
    (hfrV : ∀ t ∈ W, ∀ b : U64, t.val + 256 ≤ b.val → b.val < t.val + 4096 →
      ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b) :
    XTopAt (L := L) AR { Z with T := Z.T ∪ W } s a σ := by
  obtain ⟨⟨⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩, hV, hPt, hPI, hCO⟩, ⟨hPl, hCR, hFI, hD, hMO, hIA, hSA⟩,
    -, hE⟩ := hX
  have hEP := hP.ep
  have hTW : P1.TcbPlaced (Z.T ∪ W) := fun t ht => by
    rcases ht with ht | ht
    · exact hEP.tcb t ht
    · exact (hW t ht).1
  -- the relations
  have hSch' : Sched.SchedRel st Z.N (Z.T ∪ W) Z.C Z.c s σ := by
    refine Sched.SchedRel.add_tcbsAt hSch hkt hW hWC hc0 hnd hks (fun n hn t ht => ?_)
      (fun sc hsc x n hx b hb t ht => ?_) hm
    · have := range_apart (k := 64) (w := 4096) (by omega) (by omega) (OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ)
        (fun b h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h1, h2⟩)))))) (hfrO t ht)
      omega
    · by_contra hc
      push_neg at hc
      exact hfrO t ht b hc.1 hc.2
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, n, hx, hb⟩)))))))
  have hEp' : Endp.EpStateRel (Z.T ∪ W) Z.E Z.R Z.B (L.mem s) σ := by
    have h := Sched.EpStateRel.add (En := ∅) (Rn := ∅) hEp (fun e h => h.elim) (fun r h => h.elim) hkt
      (fun e h => h.elim) (fun r h => h.elim)
      (fun t ht => ⟨(hmt t ht).1, (hmt t ht).2.1, (hmt t ht).2.2.1, (hmt t ht).2.2.2.1, (hmt t ht).2.2.2.2.2⟩)
    simpa only [Set.union_empty] using h
  have hNt' : Notif.NtfnStateRel Z.N (Z.T ∪ W) (L.mem s) σ := by
    have h := Sched.NtfnStateRel.add (Nn := ∅) hNt hSch.placed (fun _ _ _ => rfl) (fun _ _ h => h)
      (fun n h => h.elim) hkt (fun n h => h.elim)
      (fun t ht => ⟨(hmt t ht).1, (hmt t ht).2.2.2.2.1, (hmt t ht).2.1⟩)
    simpa only [Set.union_empty] using h
  -- the placement
  have hEP' : Endp.EPlaced (Z.T ∪ W) Z.E Z.R Z.B := by
    refine ⟨hTW, hEP.ep, hEP.rep, fun e he t ht => ?_, fun r hr t ht => ?_, hEP.er, hEP.balign,
      fun wp hw t ht => ?_, hEP.be, hEP.br, hEP.binj⟩
    · rcases ht with ht | ht
      · exact hEP.et e he t ht
      · have := range_apart (k := 16) (w := 4096) (by omega) (by omega) (OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ)
          (fun b h1 h2 => Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, h1, h2⟩)))) (hfrO t ht)
        omega
    · rcases ht with ht | ht
      · exact hEP.rt r hr t ht
      · have := range_apart (k := 32) (w := 4096) (by omega) (by omega) (OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ)
          (fun b h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, h1, h2⟩))))) (hfrO t ht)
        omega
    · rcases ht with ht | ht
      · exact hEP.bt wp hw t ht
      · have := range_apart (k := 8) (w := 4096) (by omega) (by omega) (OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ)
          (fun b h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, h1, h2⟩)))))))
          (hfrO t ht)
        omega
  -- a new TCB's `EFoot`/`EWrite` word is in its block past the slots
  have hfoot : ∀ b : U64, Endp.EFoot (Z.T ∪ W) Z.E Z.R Z.B b →
      Endp.EFoot Z.T Z.E Z.R Z.B b ∨ ∃ t ∈ W, t.val + 256 ≤ b.val ∧ b.val < t.val + 4096 := by
    rintro b (h | h | ⟨t, ht, h⟩ | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · rcases ht with ht | ht
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, h⟩)))
      · refine Or.inr ⟨t, ht, ?_⟩
        rcases h with h | h
        · have := h.range; omega
        · unfold Endp.TL at h; omega
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
  have hwrite : ∀ b : U64, Endp.EWrite (Z.T ∪ W) Z.E Z.R Z.B b →
      Endp.EWrite Z.T Z.E Z.R Z.B b ∨ ∃ t ∈ W, t.val + 256 ≤ b.val ∧ b.val < t.val + 4096 := by
    rintro b (h | h | ⟨t, ht, h⟩ | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · rcases ht with ht | ht
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, h⟩)))
      · refine Or.inr ⟨t, ht, ?_⟩
        rcases h with h | h
        · have := h.tf.range; omega
        · unfold Endp.TL at h; omega
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
  have hnodeE : ∀ b : U64, L.nodeBase s Z.c ≤ b.val → b.val < L.nodeBase s Z.c + 4288 →
      ¬ Endp.EFoot (Z.T ∪ W) Z.E Z.R Z.B b := by
    intro b h1 h2 hf
    rcases hfoot b hf with hf | ⟨t, ht, g1, g2⟩
    · exact hP.nodeE b h1 h2 hf
    · exact hfrO t ht b (by omega) g2 (Or.inl ⟨h1, h2⟩)
  have hP' : TopPlaced st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N (Z.T ∪ W) Z.C Z.E Z.R Z.B Z.c s σ := by
    refine { hP with ep := hEP', disj := fun b hb => ?_, nodeE := hnodeE }
    rcases oobj_unionT hb with hb | ⟨t, ht, g1, g2⟩
    · exact hP.disj b hb
    · exact hfrV t ht b g1 g2
  have hIA' : IpcApart Z.th Z.N (Z.T ∪ W) Z.E Z.R Z.B (L.ksb s) Z.c := by
    have hiw : ∀ b, IWords Z.N (Z.T ∪ W) Z.E Z.R Z.B b →
        IWords Z.N Z.T Z.E Z.R Z.B b ∨ ∃ t ∈ W, t.val + 256 ≤ b.val ∧ b.val < t.val + 4096 := by
      rintro b (⟨t, ht, h1, h2⟩ | h)
      · rcases ht with ht | ht
        · exact Or.inl (Or.inl ⟨t, ht, h1, h2⟩)
        · exact Or.inr ⟨t, ht, h1, h2⟩
      · exact Or.inl (Or.inr h)
    refine { hIA with slot := fun b hb x hx hin => ?_, dom := fun b hb => ?_ }
    · rcases hiw b hb with hb | ⟨t, ht, g1, g2⟩
      · exact hIA.slot b hb x hx hin
      · exact hfrV t ht b g1 g2 (Vs.vobj_of_slot hPl _ _ _ _ _ _ hx hin.1 hin.2)
    · rcases hiw b hb with hb | ⟨t, ht, g1, g2⟩
      · exact hIA.dom b hb
      · have := hks t ht; omega
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  have hE' : EpSchedApart st (Z.T ∪ W) Z.C Z.E Z.R Z.B Z.c s σ := by
    refine ⟨hnodeE, fun hw => ?_, fun hw => ?_, fun sc hsc x n hx b hb hw => ?_⟩
    · rcases hwrite _ hw with hw | ⟨t, ht, g1, g2⟩
      · exact hE.dom hw
      · rw [Sched.curDomA_val hc.node] at g1 g2; have := hks t ht; omega
    · rcases hwrite _ hw with hw | ⟨t, ht, g1, g2⟩
      · exact hE.dt hw
      · rw [Sched.dtA_val hc.node] at g1 g2; have := hks t ht; omega
    · rcases hwrite _ hw with hw | ⟨t, ht, g1, g2⟩
      · exact hE.sc sc hsc x n hx b hb hw
      · exact hfrO t ht b (by omega) g2
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, n, hx, hb⟩)))))))
  exact ⟨⟨⟨⟨hSch', hEp', hNt', hIrq, hIo, hKr, hAr⟩, hP'⟩, hV, hPt, hPI, hCO⟩,
    ⟨hPl, hCR, hFI, hD, hMO, hIA', hSA⟩, IpcRel.of hNt' hEp' (sched_sc hSch'), hE'⟩

end

end

end Fl4Proofs.P3

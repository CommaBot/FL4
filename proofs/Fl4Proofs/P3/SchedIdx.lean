/-
P3 (issue #16, g7a): **FL4's `schedule` keeps the `DOM_SCHED_IDX` word 0**
(the word DomDecode's `DomRel` now carries; INV-PLAN §1.U3L D1).

FL4 writes the kernel-global words below 256 in `schedule` only in
`next_domain`, which runs only when the `DOMAIN_TIME` word is 0. `IdxI kb m`:
the index word is 0, and either the domain time word is nonzero or the start
word, entry 1's duration and entry 0's domain are 0 (what `next_domain_eq`
asks; at a `JAtZ` state from `DomRel ∧ DomListOK`, `next_domain_words`).
`IdxI` is kept by every P1 `Foot` step (`KW` apart from the first 256 bytes,
`KWApart`) and by `next_domain` (`next_domain_eq`: the index back to 0, the
start, entry 1's duration and entry 0's domain untouched).

* `SFI kb s s'`: P1's `SFoot` with `IdxI` carried (from a state at base `kb`).
* `sched.schedule_choose_new_thread.sfi`, `cand_choose.sfi`,
  `sched.schedule.sfi`: QueueFootS's `.sfoot` lemmas with `SFI` (the same
  proofs, every `Foot` piece through `Foot.sfi`).
* **`sched.schedule.idx`**: from `IdxI` at the entry and the timers' `FootD`
  keeping the words below 256 (`hfd`), the index word is 0 after `schedule`.
-/
import Fl4Proofs.P1.QueueFootS
import Fl4Proofs.P1.FastFin
import Fl4Proofs.P3.ScNextDom
import Fl4Proofs.P3.ScNextDomB
import Fl4Proofs.P3.IrqDom
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64}

/-- **The index invariant** (module docstring). -/
def IdxI (kb : U64) (m : U64 → U64) : Prop :=
  m (ksW kb 24#u64) = 0#u64 ∧ (m (ksW kb 16#u64) ≠ 0#u64 ∨
    (m (ksW kb 32#u64) = 0#u64 ∧ m (ksW kb (durOff 1#u64)) = 0#u64 ∧ m (ksW kb (entOff 0#u64)) = 0#u64))

theorem IdxI.keep {kb : U64} {m m' : U64 → U64} (h : IdxI kb m)
    (hm : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → m' (ksW kb o) = m (ksW kb o)) : IdxI kb m' := by
  have e1 : durOff 1#u64 = 216#u64 := rfl
  have e0 : entOff 0#u64 = 192#u64 := rfl
  unfold IdxI at h ⊢
  rw [e1, e0] at h ⊢
  rw [hm 24#u64 (by decide) (by decide), hm 16#u64 (by decide) (by decide), hm 32#u64 (by decide) (by decide),
    hm 216#u64 (by decide) (by decide), hm 192#u64 (by decide) (by decide)]
  exact h

/-- `SFoot` with `IdxI` carried from a state at base `kb`. -/
abbrev SFI (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : Heap) (kb : U64) (s s' : S) : Prop :=
  SFoot st T Cs Sg Scs Z H s s' ∧ (L.ksb s = kb → IdxI kb (L.mem s) → IdxI kb (L.mem s'))

theorem SFI.refl (kb : U64) (s : S) : SFI (st := st) T Cs Sg Scs Z H kb s s := ⟨SFoot.refl _, fun _ h => h⟩

theorem SFI.trans {kb : U64} {s1 s2 s3 : S} (h1 : SFI (st := st) T Cs Sg Scs Z H kb s1 s2)
    (h2 : SFI (st := st) T Cs Sg Scs Z H kb s2 s3) : SFI (st := st) T Cs Sg Scs Z H kb s1 s3 :=
  ⟨h1.1.trans h2.1, fun hk hi => h2.2 (h1.1.1.trans hk) (h1.2 hk hi)⟩

/-- **A `Foot` step keeps `IdxI`** (`KW` apart from the first 256 bytes). -/
theorem Foot.sfi {s0 s1 s2 : S} (h : Foot st T Cs Sg Scs Z (EH H) s1 s2)
    (hf : (L.ksb s0).val + 13568 ≤ 2 ^ 64) (ha : (L.ksb s0).val % 8 = 0)
    (hK : KWApart (L := L) T Cs Sg Scs Z (EH H) s0) : SFI (st := st) T Cs Sg Scs Z H (L.ksb s0) s1 s2 := by
  refine ⟨h.sfoot, fun hk hi => hi.keep fun o ho h8 => ?_⟩
  have hal : Aligned (ksW (L.ksb s0) o) := ksW_al hf ha ho h8
  refine h.mem_eq hal fun hb => ?_
  have hv := ksW_val (kb := L.ksb s0) (o := o) (by omega)
  rcases hK _ hal (KW.ksb hk hb) with e | e <;> rw [hv] at e <;> omega

/-- FL4's state after `next_domain` (`ndS`): the words below 256 but the
index, `WORK_UNITS`, `CUR_DOMAIN` and `DOMAIN_TIME` kept, the index 0. -/
theorem ndS_ks {T : Set U64} (s : S) (hN : NodePlaced st T s (L.cpu s)) (t : U64) {k : U64} (hk : k.val < 256)
    (hk8 : k.val % 8 = 0) :
    L.mem (ndS (L := L) s t) (ksW (L.ksb s) k) =
      if k.val = 16 then t else if k.val = 8 ∨ k.val = 40 ∨ k.val = 24 then 0#u64 else L.mem s (ksW (L.ksb s) k) := by
  have hf : (L.ksb s).val + 13568 + (L.cpu s).val * 4288 + 4288 ≤ 2 ^ 64 := hN.fits
  have hal : ((L.ksb s).val + 13568 + (L.cpu s).val * 4288) % 8 = 0 := hN.align
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by omega
  have hka : (L.ksb s).val % 8 = 0 := by omega
  have hR : (L.nodeAt (L.wr s (ksW (L.ksb s) 24#u64) 0#u64) (L.cpu s) layout.node.REPROGRAM) =
      L.nodeAt s (L.cpu s) layout.node.REPROGRAM := Sched.nodeAt_ksb (L.ksb_wr _ _ _) _ _
  have hN1 : NodePlaced st T (L.wr s (ksW (L.ksb s) 24#u64) 0#u64)
      (L.cpu (L.wr s (ksW (L.ksb s) 24#u64) 0#u64)) := by rw [L.cpu_wr]; exact hN.wr
  have hnode := mem_node_ks (L.wr s (ksW (L.ksb s) 24#u64) 0#u64) hN1 (o := layout.node.REPROGRAM)
    (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]) 1#u64 hk hk8
  simp only [L.ksb_wr, L.cpu_wr, hR] at hnode
  unfold ndS
  by_cases e16 : k.val = 16
  · rw [if_pos e16, show k = 16#u64 from UScalar.eq_of_val_eq (by rw [e16]; rfl), mem_ks_same _ _ hkf hka (by decide) (by decide)]
  rw [if_neg e16, mem_ks_ne _ _ hkf hka (by decide) (by decide) hk hk8 (by simpa using Ne.symm e16)]
  by_cases e8 : k.val = 8
  · rw [if_pos (Or.inl e8), show k = 8#u64 from UScalar.eq_of_val_eq (by rw [e8]; rfl), mem_ks_same _ _ hkf hka (by decide) (by decide)]
  rw [mem_ks_ne _ _ hkf hka (by decide) (by decide) hk hk8 (by simpa using Ne.symm e8)]
  by_cases e40 : k.val = 40
  · rw [if_pos (Or.inr (Or.inl e40)), show k = 40#u64 from UScalar.eq_of_val_eq (by rw [e40]; rfl), mem_ks_same _ _ hkf hka (by decide) (by decide)]
  rw [mem_ks_ne _ _ hkf hka (by decide) (by decide) hk hk8 (by simpa using Ne.symm e40), hnode]
  by_cases e24 : k.val = 24
  · rw [if_pos (Or.inr (Or.inr e24)), show k = 24#u64 from UScalar.eq_of_val_eq (by rw [e24]; rfl), mem_ks_same _ _ hkf hka (by decide) (by decide)]
  rw [if_neg (by omega), mem_ks_ne _ _ hkf hka (by decide) (by decide) hk hk8 (by simpa using Ne.symm e24)]

/-- `IdxI` after `next_domain` (`next_domain_eq`). -/
theorem idxI_ndS (s : S) (hN : NodePlaced st T s (L.cpu s)) (t : U64)
    (h32 : L.mem s (ksW (L.ksb s) 32#u64) = 0#u64) (hd1 : L.mem s (ksW (L.ksb s) (durOff 1#u64)) = 0#u64)
    (he0 : L.mem s (ksW (L.ksb s) (entOff 0#u64)) = 0#u64) : IdxI (L.ksb s) (L.mem (ndS (L := L) s t)) := by
  have e1 : durOff 1#u64 = 216#u64 := rfl
  have e0 : entOff 0#u64 = 192#u64 := rfl
  unfold IdxI
  simp only [e1, e0] at hd1 he0 ⊢
  rw [ndS_ks s hN t (k := 24#u64) (by decide) (by decide), ndS_ks s hN t (k := 32#u64) (by decide) (by decide),
    ndS_ks s hN t (k := 216#u64) (by decide) (by decide), ndS_ks s hN t (k := 192#u64) (by decide) (by decide)]
  simp only [show (24#u64 : U64).val = 24 from rfl, show (32#u64 : U64).val = 32 from rfl,
    show (216#u64 : U64).val = 216 from rfl, show (192#u64 : U64).val = 192 from rfl]
  simp [h32, hd1, he0]

theorem sched.schedule_choose_new_thread.sfi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) {s0 : S}
    (hf : (L.ksb s0).val + 13568 ≤ 2 ^ 64) (ha : (L.ksb s0).val % 8 = 0)
    (hK : KWApart (L := L) T Cs Sg Scs Z (EH H) s0) :
    sched.schedule_choose_new_thread st ar s a ⦃ s' _ => SFI (st := st) T Cs Sg Scs Z H (L.ksb s0) s s' ⦄ := by
  unfold sched.schedule_choose_new_thread
  rw [domain_time_eq, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q R, SchedQueuesInv st T Cs Ω H s1 Q R) ∧
      SFI (st := st) T Cs Sg Scs Z H (L.ksb s0) s s1) ?_ ?_
  · split
    · rename_i h0
      have hkD : layout.ks.DOMAIN_TIME = 16#u64 := by unfold layout.ks.DOMAIN_TIME; rfl
      rw [hkD] at h0
      by_cases hI : L.ksb s = L.ksb s0 ∧ IdxI (L.ksb s0) (L.mem s)
      · obtain ⟨hk, h24, h16 | ⟨h32, hd1, he0⟩⟩ := hI
        · exact absurd (show L.mem s (ksW (L.ksb s0) 16#u64) = 0#u64 by rw [← hk]; exact h0) h16
        · rw [← hk] at h24 h32 hd1 he0
          have hN := h.nodes _ h.cur
          have e := next_domain_eq (T := T) s hN h24 h32 hd1 he0
          have h1 := sched.next_domain.sch s Q R h hB hS
          have h2 := sched.next_domain.sfoot (Scs := Scs) (Z := Z) s Q R h hB hS
          rw [e, WP.spec_ok] at h1 h2 ⊢
          refine ⟨h1.1.inv, h2, fun _ _ => ?_⟩
          rw [← hk]; exact idxI_ndS s hN _ h32 hd1 he0
      · exact WP.spec_mono (WP.spec_and (sched.next_domain.sch s Q R h hB hS)
          (sched.next_domain.sfoot (Scs := Scs) (Z := Z) s Q R h hB hS)) fun s1 hh =>
            ⟨hh.1.1.inv, hh.2, fun hk hi => absurd ⟨hk, hi⟩ hI⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, SFI.refl _ _⟩
  rintro s1 ⟨⟨Q1, R1, h1⟩, f1⟩
  exact WP.spec_mono (sched.choose_thread.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s1 a h1)
    fun r hr => by
      obtain ⟨s', a'⟩ := r
      have hr' : Foot st T Cs Sg Scs Z (EH H) s1 s' := by simpa using hr
      exact f1.trans (hr'.sfi hf ha hK)

theorem cand_choose.sfi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (act : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hact : L.actionW s = act) (hT : act ∈ T) (app : Bool) {s0 : S}
    (hf : (L.ksb s0).val + 13568 ≤ 2 ^ 64) (ha : (L.ksb s0).val % 8 = 0)
    (hK : KWApart (L := L) T Cs Sg Scs Z (EH H) s0) :
    (do
      let s5 ← if app then sched.append st s act else sched.enqueue st s act
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ s' _ => SFI (st := st) T Cs Sg Scs Z H (L.ksb s0) s s' ⦄ := by
  have hok := h.actOK (hact ▸ hT)
  rw [hact] at hok
  have hr : (L.mem s (inqA act) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hc
    exact hok.2 _ (h.aff act hT) ((h.released act hT).1 hc)
  have hbd : L.mem s (scA act) ≠ 0#u64 := by have := hB.act (hact ▸ hT); rw [hact] at this; exact this
  refine WP.spec_bind (Pₘ := fun s5 => Post st T Cs Ω H Sg Ac s s5 ∧ Foot st T Cs Sg Scs Z (EH H) s s5) ?_ ?_
  · split
    · exact WP.spec_mono (WP.spec_and (sched.append.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1)
        (fun _ => hbd) (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this))
        (sched.append.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s act h hT)) fun s5 h5 => ⟨h5.1.1, h5.2⟩
    · exact WP.spec_mono (WP.spec_and (sched.enqueue.sch s act Q R h hB hS.sg hT (fun _ => hr) (fun _ => hok.1)
        (fun _ => hbd) (fun _ => by have := hB.actA (hact ▸ hT); rwa [hact] at this))
        (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s act h hT)) fun s5 h5 => ⟨h5.1.1, h5.2⟩
  rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, f5⟩, F5⟩
  rw [choose_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s5 1#u64 Q5 R5 h5 hB5 (hS.fr f5).sg (Or.inr (Or.inl rfl))
    (fun hT => absurd hT (one_notT h)) (fun hT => absurd hT (one_notT h)) (fun e => by simp at e)
    (fun hT => absurd hT (one_notT h)))
    (sched.set_action.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s5 1#u64 (h5.nodes _ h5.cur) h5.cur)) ?_
  rintro s6 ⟨⟨⟨⟨Q6, R6, h6⟩, hB6, f6⟩, -, -, -⟩, F6⟩
  exact WP.spec_mono (sched.schedule_choose_new_thread.sfi (Scs := Scs) (Z := Z) hA s6 a Q6 R6 h6 hB6
    ((hS.fr f5).fr f6).sg hf ha hK) fun r hr => by
      obtain ⟨s', a'⟩ := r; exact ((Foot.trans F5 F6).sfi hf ha hK).trans (by simpa using hr)

theorem sched.schedule.sfi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (ha : (L.ksb s).val % 8 = 0)
    (hK : KWApart (L := L) T Cs Sg Scs Z (EH H) s) :
    sched.schedule st ar s a ⦃ s' _ => ∃ rf : S × A, timer.fire st ar s a = ok rf ∧
      FootD st T Cs Sg Scs Z (EH H) s rf.1 ∧ SFI (st := st) T Cs Sg Scs Z H (L.ksb s) rf.1 s' ⦄ := by
  unfold sched.schedule sched.awaken
  -- `awaken`
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ ∃ rf : S × A,
      timer.fire st ar s a = ok rf ∧ FootD st T Cs Sg Scs Z (EH H) s rf.1 ∧ SFI (st := st) T Cs Sg Scs Z H (L.ksb s) rf.1 r.1) ?_ ?_
  · refine WP.spec_bind (spec_eq' (timer.fire.tinvF hA hNt s a h.tinv)) ?_
    rintro ⟨s1, a1⟩ ⟨hf1, ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩, F1⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (WP.spec_and (sched.awaken_loop.sch s1 _ Q1 R1 h1 hB1 hS1.sg)
      (sched.awaken_loop.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 _ Q1 R1 h1 hB1 hS1.sg)) ?_
    rintro s2 ⟨⟨P2, -⟩, F2⟩
    exact (WP.spec_ok _).2 ⟨P2.good hS1 hX1, (s1, a1), hf1, F1, F2.sfi hf ha hK⟩
  rintro ⟨s1, a1⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, rf, hrf, Fd, F1⟩
  -- `check_domain_time` does nothing with one domain
  unfold sched.check_domain_time sched.is_cur_domain_expired
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, bind_ok, Bool.false_eq_true]
  step with sched.action.spec as ⟨act, act_post⟩
  -- the action
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ L.mem r.1 (scA (L.curW r.1)) ≠ 0#u64 ∧
      L.mem r.1 (scA (L.curW r.1)) ∈ Ac ∧ SFI (st := st) T Cs Sg Scs Z H (L.ksb s) s1 r.1) ?_ ?_
  · split
    · rename_i hnr
      step with sched.cur_thread.spec as ⟨ct, ct_post⟩
      have hctT : ct ∈ T := by rw [ct_post]; exact h1.curT
      step with sched.is_schedulable.spec' as ⟨wr, wr_post⟩
      refine WP.spec_bind (Pₘ := fun s4 => Post st T Cs Ω H Sg Ac s1 s4 ∧ L.actionW s4 = L.actionW s1 ∧
          Foot st T Cs Sg Scs Z (EH H) s1 s4) ?_ ?_
      · split
        · exact WP.spec_mono (WP.spec_and (sched.enqueue.sch s1 ct Q1 R1 h1 hB1 hS1.sg hctT (fun _ => (wr_post ‹_›).2.2.1)
            (fun _ => (wr_post ‹_›).1) (fun _ => (wr_post ‹_›).2.1)
            (fun _ => (hS1.act _ (hX1.2.2.bound _ hctT (wr_post ‹_›).2.1).1).2 (wr_post ‹_›).2.2.2))
            (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 ct h1 hctT))
            fun s4 h4 => ⟨h4.1.1, h4.1.2.1, h4.2⟩
        · exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, Fr.refl _ _⟩, rfl, Foot.refl _⟩
      rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, f4⟩, ea4, F4⟩
      have hS4 := hS1.fr f4
      have hX4 := hX1.fr f4
      have hact4 : L.actionW s4 = act := ea4.trans act_post.symm
      split
      · exact WP.spec_mono (WP.spec_and (sched.schedule_choose_new_thread.sch hA s4 a1 Q4 R4 h4 hB4 hS4 hX4)
          (sched.schedule_choose_new_thread.sfi (Scs := Scs) (Z := Z) hA s4 a1 Q4 R4 h4 hB4 hS4.sg hf ha hK)) fun r hr => by
            obtain ⟨s', a'⟩ := r
            simp only [WP.uncurry'_pair] at hr ⊢
            exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, (F4.sfi hf ha hK).trans hr.2⟩
      rename_i hnc
      have hT : act ∈ T := by
        rcases h4.action with e | e | e
        · exfalso; rw [hact4] at e; rw [e, resume_val] at hnr; simp at hnr
        · exfalso; rw [hact4] at e; rw [e, choose_val] at hnc; simp at hnc
        · rw [hact4] at e; exact e
      have hbd : L.mem s4 (scA act) ≠ 0#u64 := by have := hB4.act (hact4 ▸ hT); rw [hact4] at this; exact this
      have L1 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT true)
        (cand_choose.sfi (Scs := Scs) (Z := Z) hA s4 a1 act Q4 R4 h4 hB4 hS4 hact4 hT true hf ha hK)
      have L3 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT false)
        (cand_choose.sfi (Scs := Scs) (Z := Z) hA s4 a1 act Q4 R4 h4 hB4 hS4 hact4 hT false hf ha hK)
      simp only [↓reduceIte, Bool.false_eq_true] at L1 L3
      replace L1 := WP.spec_mono L1 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFI (st := st) T Cs Sg Scs Z H (L.ksb s) s1 s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, (F4.sfi hf ha hK).trans hr.2⟩
      replace L3 := WP.spec_mono L3 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFI (st := st) T Cs Sg Scs Z H (L.ksb s) s1 s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, (F4.sfi hf ha hK).trans hr.2⟩
      have L2 : sched.switch_to_thread st ar s4 a1 act ⦃ s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFI (st := st) T Cs Sg Scs Z H (L.ksb s) s1 s' ⦄ :=
        WP.spec_mono (WP.spec_and (sched.switch_to_thread.sch hA s4 a1 act Q4 R4 h4 hB4 hS4.sg hT hbd
          (by have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this))
          (sched.switch_to_thread.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s4 a1 act h4 hT)) fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1.good hS4 hX4, by rw [hr.1.2.1, hr.1.1.fr.sc act hT]; exact hbd, by
            rw [hr.1.2.1, hr.1.1.fr.sc act hT]; have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this,
            (F4.trans hr.2).sfi hf ha hK⟩
      step with sched.cur_thread.spec as ⟨ct1, _⟩
      step with sched.idle_thread.spec' as ⟨t, _⟩
      step with tcb_eq.spec as ⟨b⟩
      refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun fastfail _ => ?_
      · split
        · simp
        · step with obj.Tcb.prio.spec as ⟨i, _⟩
          step with obj.Tcb.prio.spec as ⟨i1, _⟩
          split <;> simp
      split
      · step with sched.cur_domain.spec' as ⟨i⟩
        step with obj.Tcb.prio.spec as ⟨i1, _⟩
        step with sched.is_highest_prio.ok s4 Q4 R4 h4 as ⟨b1⟩
        split
        · split
          · step with obj.Tcb.prio.spec as ⟨i2, _⟩
            split
            · exact L1
            · exact L2
          · exact L2
        · exact L3
      · split
        · step with obj.Tcb.prio.spec as ⟨i, _⟩
          step with obj.Tcb.prio.spec as ⟨i1, _⟩
          split
          · exact L1
          · exact L2
        · exact L2
    · rename_i hr0
      have e0 : L.actionW s1 = 0#u64 := by
        rw [← act_post]; rw [resume_val] at hr0
        apply UScalar.eq_of_val_eq; simpa using hr0
      exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, hB1.resume e0, hB1.curA h1.curT e0, SFI.refl _ _⟩
  rintro ⟨s3, a2⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hS3, hX3⟩, hcb1, hcb2, F3⟩
  have hcb := And.intro hcb1 hcb2
  try simp only [WP.uncurry'_pair]
  -- resume, then switch the SC
  rw [resume_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s3 0#u64 Q3 R3 h3 hB3 hS3.sg (Or.inl rfl)
    (fun hT => absurd hT (notT_small h3.tcbs (by simp))) (fun hT => absurd hT (notT_small h3.tcbs (by simp)))
    (fun _ => hcb) (fun hT => absurd hT (notT_small h3.tcbs (by simp))))
    (sched.set_action.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 0#u64 (h3.nodes _ h3.cur) h3.cur)) ?_
  rintro s4 ⟨⟨P4, ea4, -, -⟩, F4⟩
  obtain ⟨⟨Q4, R4, h4⟩, hB4, hS4, hX4⟩ := P4.good hS3 hX3
  have hcT := h4.curT
  have hb4 : L.mem s4 (scA (L.curW s4)) ≠ 0#u64 := hB4.resume ea4
  have hO4 := hX4.1
  have hsub4 := hS4.sub
  have hts : L.mem s4 (scA (L.curW s4)) ∈ Scs := (hX4.2.2.bound _ hcT hb4).1
  have hcs : L.cscW s4 ∈ Scs := hX4.2.2.cur
  obtain ⟨hPc, hzc⟩ := hO4.sc _ hcs
  obtain ⟨h8c, h128c, -⟩ := sc_lo hPc hzc
  have hvc := sc_word_val hPc hzc (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hcq : SCq st s4 Ω (L.cscW s4) (Z (L.cscW s4)) := by
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO4 hcs
    exact ⟨(hS4.all _ hcs).1, fun b hb hi => hsub4 _ ((hS4.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hvc]; omega, by rw [hvc, hcv]; omega⟩, by unfold Aligned; rw [hvc, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
  have htin : SCin st s4 Ω (L.mem s4 (scA (L.curW s4))) (Z (L.mem s4 (scA (L.curW s4)))) :=
    (hS4.scin hts (hB4.curA hcT ea4)).mono hsub4
  have hN4 := h4.nodes _ h4.cur
  refine WP.spec_bind (WP.spec_and (sched.switch_sched_context.free hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
    (zc := Z (L.cscW s4)) h4.cur hN4 h4.omega hcq
    (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩))
    (sched.switch_sched_context.fp hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
      (zc := Z (L.cscW s4))
      (B := KW st T Cs Sg Scs Z (EH H) s4) h4.cur hN4 h4.omega
      hcq (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩)
      (kw_node h4.cur (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
      (kw_node h4.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
      (kw_node h4.cur (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      (fun _ b _ hr => kw_sc hts hr.inSC)
      (fun b _ hr => by
        rcases hr with hr | rfl
        · exact kw_sc hcs hr.inSC
        · exact kw_sc hcs (show InSC (L.cscW s4) (Z (L.cscW s4))
            (core.num.U64.wrapping_add (L.cscW s4) layout.sc.CONSUMED) from
            ⟨by rw [hvc]; omega, by rw [hvc, hcv]; omega⟩)))) ?_
  rintro ⟨s5, a3⟩ ⟨w5, w5', -, -, -⟩
  simp only [WP.uncurry'_pair] at w5 w5' ⊢
  have h5 := (free_step h4 hB4 w5).1
  step with LawfulStore.cur_cpu_spec as ⟨c, c_post⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r => SchedQueuesInv st T Cs Ω H r.1 Q4 R4 ∧ SFI (st := st) T Cs Sg Scs Z H (L.ksb s) s5 r.1) ?_ ?_
  · split
    · have hB5 := (free_step h4 hB4 w5).2
      refine WP.spec_bind (WP.spec_and (sched.set_next_interrupt.free (Ω := Ω) hA s5 a3 h5.cur (h5.nodes _ h5.cur))
        (sched.set_next_interrupt.fp hA s5 a3 (B := KW st T Cs Sg Scs Z (EH H) s5) (h5.nodes _ h5.cur)
          (kw_node h5.cur (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED])))) ?_
      rintro ⟨s7, a5⟩ ⟨w7, w7'⟩
      simp only [WP.uncurry'_pair] at w7 w7' ⊢
      have h7 := free_step h5 hB5 w7
      step with obj.node_set.spec as ⟨s8, s8_post⟩
      try simp only [WP.spec_ok]
      have w8 : WritesIn st s5 s8 (L.Free s5 Ω Cs) := by
        rw [s8_post, c_post]
        exact w7.free_trans (free_node_write w7.1 h5.cur (h5.nodes _ h5.cur)
          (by simp [layout.node.REPROGRAM, LowFree]))
      have hN7 : NodePlaced st T s7 (L.cpu s7) := by rw [w7.2.1]; exact (h5.nodes _ h5.cur).ksb w7.1
      have F8 : Foot st T Cs Sg Scs Z (EH H) s7 s8 := by
        rw [s8_post, c_post, ← w7.2.1]
        exact (foot_node (Es := EH H) hN7 (by rw [w7.2.1]; exact h5.cur) (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
      exact ⟨(free_step h5 hB5 w8).1, (Foot.trans w7' F8).sfi hf ha hK⟩
    · exact (WP.spec_ok _).2 ⟨h5, SFI.refl _ _⟩
  rintro ⟨s6, a4⟩ ⟨h6, F6⟩
  try simp only [WP.uncurry'_pair]
  exact WP.spec_mono (smp.send_pending.fp hA s6 a4 (B := KW st T Cs Sg Scs Z (EH H) s6) (h6.nodes _ h6.cur)
      (kw_node h6.cur (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]))) fun r w => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at w ⊢
    exact ⟨rf, hrf, Fd, F1.trans (F3.trans (((Foot.trans F4 w5').sfi hf ha hK).trans
      (F6.trans ((show Foot st T Cs Sg Scs Z (EH H) s6 s' from w).sfi hf ha hK))))⟩


/-- **FL4's `schedule` keeps the `DOM_SCHED_IDX` word 0** (module docstring). -/
theorem sched.schedule.idx {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (ha : (L.ksb s).val % 8 = 0)
    (hK : KWApart (L := L) T Cs Sg Scs Z (EH H) s)
    (hfd : ∀ s1, FootD st T Cs Sg Scs Z (EH H) s s1 → ∀ o : U64, o.val < 256 → o.val % 8 = 0 →
      L.mem s1 (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o))
    (hI : IdxI (L.ksb s) (L.mem s)) :
    sched.schedule st ar s a ⦃ s' _ => L.mem s' (ksW (L.ksb s) 24#u64) = 0#u64 ⦄ := by
  refine WP.spec_mono (sched.schedule.sfi hA hNt s a h hf ha hK) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  obtain ⟨rf, -, Fd, F⟩ := hr
  exact (F.2 Fd.1 (hI.keep (hfd _ Fd))).1

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **FL4's TCB timers keep the kernel-global words below 256** (XTopJointSchedRF2's
`JAtZ.ndOK_fire`, from the facts it reads off `JAtZ`: P1's `FootD` words are
`KW` words apart from the first 256 bytes, or TCB / node debug links). -/
theorem fire_ks_of {H : P1.Heap} {Cs : Set U64} {s s1 : S}
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hks : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → p.val + 2 ^ k.bits ≤ (L.ksb s).val ∨
      (L.ksb s).val + 13568 ≤ p.val)
    (hH : P1.HeapOK H)
    (hKW : KWApart (L := L) (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s)
    (hnpl : ∀ c ∈ Cs, P1.NodePlaced st (P1.Heap.tcbs H) s c)
    (hf : P1.FootD st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s1) :
    ∀ o : U64, o.val < 256 → o.val % 8 = 0 → L.mem s1 (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) := by
  intro o ho h8
  refine hf.mem_eq (ksW_al hkf hka ho h8) fun hb => ?_
  have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
  rcases hb with hb | hb
  · rcases hKW _ (ksW_al hkf hka ho h8) hb with e | e <;> rw [hv] at e <;> omega
  · rcases hb with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
    · have hy' : H y = some .tcb := hy
      have hfit := hH.fits y _ hy'
      simp only [P1.HKind.bits] at hfit
      have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
      rw [h12] at hfit
      have hdv : (P1.dnA y).val = y.val + 3576 := by
        unfold P1.dnA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have h3 := hks y .tcb hy' (fun z h => by cases h)
      simp only [P1.HKind.bits, h12] at h3
      have := congrArg UScalar.val e
      rw [hv, hdv] at this
      omega
    · have hy' : H y = some .tcb := hy
      have hfit := hH.fits y _ hy'
      simp only [P1.HKind.bits] at hfit
      have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
      rw [h12] at hfit
      have hdv : (P1.dpA y).val = y.val + 3584 := by
        unfold P1.dpA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      have h3 := hks y .tcb hy' (fun z h => by cases h)
      simp only [P1.HKind.bits, h12] at h3
      have := congrArg UScalar.val e
      rw [hv, hdv] at this
      omega
    · have hnv := P1.nodeAt_val (hnpl c hc) (off := layout.node.DEBUG_TCBS) (by simp)
      unfold P1.LawfulStore.nodeBase at hnv
      have := congrArg UScalar.val e
      rw [hv, hnv] at this
      simp [layout.node.DEBUG_TCBS] at this
      omega

/-- **`IdxI` at a state** from `DomRel` (the index word 0) and the entry's
`σ.domainTime ≠ 0 ∨ NdOK` (the domain-time word nonzero by `SchedRel`, or
`next_domain_words`). -/
theorem idxI_of {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hD : DomRel (L.mem s) (L.ksb s) σ) (hS : Sched.SchedRel st N T C c s σ)
    (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) : P1.IdxI (L.ksb s) (L.mem s) := by
  refine ⟨hD.2.2.2, ?_⟩
  rcases hd with hdt | ⟨hD', hV, hi⟩
  · left
    intro h0
    obtain ⟨Q, R0, hc, hs⟩ := hS.lists
    apply hdt
    rw [hs.domTime]
    show (L.mem s (ksW (L.ksb s) 16#u64)).bv = 0
    rw [h0]; rfl
  · right
    obtain ⟨-, h32, hd1, he0, -⟩ := next_domain_words hD' hV hi
    exact ⟨h32, hd1, he0⟩

end

end Fl4Proofs.P3

/-
P1: **the debug-list words a footprint keeps** (`*.dbgKeep`): a `KW`
footprint (`Foot`) avoids every debug-list word (`DbgW`: the TCBs'
`DEBUG_NEXT` / `DEBUG_PREV` words and the cores' `DEBUG_TCBS` heads), so an
operation with such a footprint keeps them (`Foot.dbgKeep`). The finalisers
with a `Foot`: `fin_endpoint.dbgKeep`, `fin_cap_ntfn.dbgKeep`.
-/
import Fl4Proofs.P1.QueueFinSc
import Fl4Proofs.P1.QueueReplyKw
import Fl4Proofs.P1.QueueCaiFr
import Fl4Proofs.P1.QueueFinCap
import Fl4Proofs.P1.QueueFootD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- The debug words of a state are kept to the next. -/
def DbgKeep (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (s s' : S) : Prop :=
  L.ksb s' = L.ksb s ∧ ∀ b, DbgW st T Cs s b → L.mem s' b = L.mem s b

theorem DbgKeep.refl (s : S) : DbgKeep st T Cs s s := ⟨rfl, fun _ _ => rfl⟩

theorem DbgKeep.trans {s₁ s₂ s₃ : S} (h₁ : DbgKeep st T Cs s₁ s₂) (h₂ : DbgKeep st T Cs s₂ s₃) :
    DbgKeep st T Cs s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, fun b hb => (h₂.2 b (DbgW.ksb h₁.1.symm hb)).trans (h₁.2 b hb)⟩

/-- The debug words are aligned. -/
theorem dbgW_aligned {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) {b : U64} (hb : DbgW st T Cs s b) :
    Aligned b := by
  obtain ⟨⟨Q, R, hq⟩, -⟩ := h
  have hT := hq.tcbs
  rcases hb with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
  · rw [e]; exact field_aligned (hT y hy) (by simp) (by simp)
  · rw [e]; exact field_aligned (hT y hy) (by simp) (by simp)
  · rw [e]; exact nodeAt_aligned (hq.nodes c hc) (by simp [debug_val]) (by simp [debug_val])

/-- **No `KW` word is a debug word** (as ScSchTailP1's `dbg0_not_schedW`,
every core and every TCB). -/
theorem dbgW_not_kw {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) {b : U64}
    (hk : KW st T Cs Sg Scs Z (EH H) s b) : ¬ DbgW st T Cs s b := by
  have hal0 := fun {b} (hb : DbgW st T Cs s b) => dbgW_aligned h hb
  obtain ⟨⟨Q, R, hq⟩, -, hX, hS, hSg⟩ := h
  have hT := hq.tcbs
  have hnb : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
  have hd : layout.node.DEBUG_TCBS.val = 88 := debug_val
  have e12 : (2 : Nat) ^ 12 = 4096 := rfl
  -- a word outside the objects is no debug word
  have outD : OutsideObjs st T Cs s b → ¬ DbgW st T Cs s b := by
    intro hb hD
    rcases hD with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
    · have := hb.2.1 y hy
      rw [e, show dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, field_val (hT y hy) (by simp), e12] at this
      simp at this
    · have := hb.2.1 y hy
      rw [e, show dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, field_val (hT y hy) (by simp), e12] at this
      simp at this
    · have hNc := hq.nodes c hc
      have := hb.2.2 c hc
      rw [e, nodeAt_val hNc (by simp [hd]), hd] at this; omega
  rcases hk with ⟨y, hy, K, hK1, hK2, hK3, hK4, e⟩ | ⟨c, hc, o, ho, ho88, e⟩ | hs | ⟨c, hc, hin⟩ | ⟨e, he, he'⟩
  · rintro (⟨y', hy', e' | e'⟩ | ⟨c, hc, e'⟩)
    · exact field_ne (hT y hy) (hT y' hy') hK2 (by simp) (fun _ => by simp; omega) (e.symm.trans e')
    · exact field_ne (hT y hy) (hT y' hy') hK2 (by simp) (fun _ => by simp; omega) (e.symm.trans e')
    · exact node_ne_field (hq.nodes c hc) (by simp [hd]) hy (hT y hy) hK2 (e'.symm.trans e)
  · rintro (⟨y', hy', e' | e'⟩ | ⟨c', hc', e'⟩)
    · exact node_ne_field (hq.nodes c hc) ho hy' (hT y' hy') (by simp) (e.symm.trans e')
    · exact node_ne_field (hq.nodes c hc) ho hy' (hT y' hy') (by simp) (e.symm.trans e')
    · have hNc := hq.nodes c hc
      have hNc' := hq.nodes c' hc'
      have ev := congrArg UScalar.val (e.symm.trans e')
      rw [nodeAt_val hNc ho, nodeAt_val hNc' (by simp [hd]), hd, hnb, hnb] at ev
      by_cases hcc : c.val = c'.val
      · rw [hcc] at ev; omega
      · rcases Nat.lt_or_gt_of_ne hcc with h' | h'
        · have : c.val * 4288 + 4288 ≤ c'.val * 4288 := by nlinarith
          omega
        · have : c'.val * 4288 + 4288 ≤ c.val * 4288 := by nlinarith
          omega
  · exact outD (hq.omega _ (hSg.sub _ hs))
  · intro hD
    exact outD (hq.omega _ (hSg.sub _ ((hS.all c hc).2.2 _ (hal0 hD) hin))) hD
  · obtain ⟨E, EQ, w1, -, -, -, -, ty⟩ := hq.eps
    have heE : e ∈ E := (ty.2.2.1 e).2 he
    obtain ⟨hE, hEN, -⟩ := w1 e heE
    obtain ⟨o1, o2⟩ := ep_out hE hEN
    rcases he' with e1 | e1
    · exact outD (by rw [e1]; exact o1)
    · exact outD (by rw [e1]; exact o2)

/-- **A `KW` footprint keeps the debug words.** -/
theorem Foot.dbgKeep {s s' : S} {Es : Set U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hEs : Es ⊆ EH H) (f : Foot st T Cs Sg Scs Z Es s s') : DbgKeep st T Cs s s' := by
  refine ⟨f.1, fun b hb => ?_⟩
  exact f.mem_eq (dbgW_aligned h hb) fun hk => dbgW_not_kw h (hk.mono hEs) hb

/-! ## The finalisers with a `KW` footprint -/

/-- **Endpoint**: `finalise_cap` keeps the debug words (`fin_endpoint.fr`). -/
theorem fin_endpoint.dbgKeep {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (ep b0 b1 b2 b3 b4 : _)
    (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hH : H ep = some .ep) :
    objects.finalise_cap st ar s a (.Endpoint ep b0 b1 b2 b3 b4) fin ex ⦃ r => DbgKeep st T Cs s r.2.1 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  have hm : ({ep} : Set U64) ⊆ EH H := fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact Or.inl hH
  exact WP.spec_mono (fin_endpoint.fr (ar := ar) s a ep b0 b1 b2 b3 b4 fin h hH) fun r ⟨_, _, _, f, _⟩ =>
    Foot.dbgKeep h hm f

/-- **Notification**: `finalise_cap` keeps the debug words (`fin_cap_ntfn.slots`). -/
theorem fin_cap_ntfn.dbgKeep {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (n : U64) (b0 b1 b2 : _)
    (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hH : H n = some .ntfn) :
    objects.finalise_cap st ar s a (.Notification n b0 b1 b2) fin ex ⦃ r => DbgKeep st T Cs s r.2.1 ⦄ :=
  WP.spec_mono (fin_cap_ntfn.slots (ar := ar) s a n b0 b1 b2 fin ex h hn hH) fun _ ⟨_, _, f, _⟩ =>
    Foot.dbgKeep h (fun _ h => h) f

/-- **Scheduling context**: `finalise_cap` keeps the debug words (`fin_sc.blk`). -/
theorem fin_sc.dbgKeep {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p x : U64)
    (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) :
    objects.finalise_cap st ar s a (.SchedContext p x) fin ex ⦃ r => DbgKeep st T Cs s r.2.1 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (fin_sc.blk hA s a p x fin h hp hp0 hna hidle) fun _ ⟨_, _, _, f⟩ =>
    Foot.dbgKeep h (Set.empty_subset _) f


/-- **Reply**: `finalise_cap` keeps the debug words, the replied thread on
its SC's core (`ipc.reply_remove.kwA`: the donation's `migrate_tcb` then
moves nothing). -/
theorem fin_reply.dbgKeep {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (x fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Rp)
    (hdc : ∀ t ∈ T, headBit (L.mem s (rNextA p)) = true →
      L.mem s (affA t) = L.mem s (scCoreA (L.mem s (rNextA p) &&& ~~~1#u64))) :
    objects.finalise_cap st ar s a (.Reply p x) fin ex ⦃ r => DbgKeep st T Cs s r.2.1 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 (DbgKeep.refl s)
  refine WP.spec_bind (obj.Reply.tcb.blk s p) fun i ei => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (DbgKeep.refl s)
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hX := h.2.2.1
  obtain ⟨-, hiT, -, -⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
  rw [← ei] at hiT
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · rename_i hv
    refine WP.spec_bind (ipc.reply_remove.kwA (Es := EH H) hA s a p i h hp hiT ei.symm (by rw [← ev, hv])
      (hdc i hiT)) ?_
    rintro ⟨s1, a1⟩ ⟨-, -, f1, -, -⟩
    exact (WP.spec_ok _).2 (Foot.dbgKeep h (fun _ h => h) f1)
  split
  · obtain ⟨⟨Q, R, h0⟩, hB, -, hS, hSg⟩ := h
    refine WP.spec_bind (ipc.cancel_ipc.kw s a i h0 hiT hX.1 hSg.sub (fun hs => by
        obtain ⟨h1, h2⟩ := hX.2.1.reply i hiT hs
        exact ⟨h1, h2, hX.2.1.next _ h1, hX.2.1.prev _ h1⟩) (fun hs h0' => (hX.2.1.recv i hiT hs h0').1)) ?_
    rintro ⟨s1, a1⟩ f1
    exact (WP.spec_ok _).2 (Foot.dbgKeep ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ (fun _ h => h) f1)
  · exact (WP.spec_ok _).2 (DbgKeep.refl s)

end

end Fl4Proofs.P1

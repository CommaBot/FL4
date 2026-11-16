/-
P1: the P1 side of P3's `SuspendP1Hyp` (TcbHypsX): after the caller's
restart (`set_thread_state ct Restart`), `BlkOK` holds over the same sets,
the suspended thread is a TCB of them, and `KW`'s aligned words lie apart
from the first 256 bytes of the kernel-global block (`KWLow`: P3's `KWDom`
at aligned words, given the SCs apart from those bytes).
-/
import Fl4Proofs.P1.QueueEntryGaps4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- `KW`'s aligned words apart from the domain schedule (the first 256 bytes
of the kernel-global block). -/
def KWLow (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s : S) : Prop :=
  ∀ b, Aligned b → KW st T Cs Sg Scs Z Es s b → b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ b.val

/-- **`KWLow` from `BlkOK`**, the SCs lying apart from the first 256 bytes. -/
theorem kwLow_of_blk {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSc : ∀ c ∈ Scs, c.val + 2 ^ Z c ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ c.val) :
    KWLow st T Cs Sg Scs Z (EH H) s := by
  obtain ⟨⟨Q, R, q⟩, -, -, -, hSg⟩ := h
  have hT := q.tcbs
  have hk8 : (L.ksb s).val % 8 = 0 := by
    have := (q.nodes _ q.cur).align; simp only [LawfulStore.nodeBase] at this; omega
  intro b hb hkw
  unfold Aligned at hb
  rcases hkw with ⟨y, hy, K, hK1, hK2, -, -, e⟩ | ⟨c, hc, o, ho, -, e⟩ | hs | ⟨c, hc, hin⟩ | ⟨e', he, e | e⟩
  · subst e
    rw [field_val (hT y hy) hK2] at hb ⊢
    rcases q.ksOut y hy with h' | h'
    · left; omega
    · right; omega
  · subst e
    rw [nodeAt_val (q.nodes c hc) ho] at hb ⊢
    simp only [LawfulStore.nodeBase]; right; omega
  · rcases hSg.ks b hs with h' | h'
    · left; exact h'
    · right; omega
  · obtain ⟨h1, h2⟩ := hin
    rcases hSc c hc with h' | h'
    · left; omega
    · right; omega
  all_goals
    obtain ⟨E, EQ, hEW⟩ := q.eps
    have heE : e' ∈ E := (hEW.2.2.2.2.2.2.2.1 e').2 he
    obtain ⟨hE, hEN, -⟩ := hEW.1 e' heE
    subst e
    first | rw [epHeadA_val] at hb ⊢ | rw [epTSA_val hE] at hb ⊢
    rcases hEN.2 with h' | h'
    · left; omega
    · right; omega

/-- **The P1 side of `SuspendP1Hyp`**: after the current thread's restart,
`BlkOK` over the same sets, `p ∈ T`, and `KWLow`. -/
theorem suspendP1 {s : S} {ct p : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hct : ct = L.curW s) (hnb : ¬ Blocked (L.mem s (stA ct))) (hnr : L.mem s (stA ct) ≠ sched.TS_BLOCKED_ON_REPLY)
    (hp : p ∈ T) (hSc : ∀ c ∈ Scs, c.val + 2 ^ Z c ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ c.val) :
    ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ p ∈ T ∧ KWLow st T Cs Sg Scs Z (EH H) s1 := by
  intro s1 hs1
  have hcT : ct ∈ T := hct ▸ h.1.choose_spec.choose_spec.curT
  have hsp := sched.set_thread_state.restart_blk (Es := ∅) s ct h hcT hnb hnr
  rw [hs1] at hsp
  obtain ⟨h1, f1, -, -⟩ := (WP.spec_ok _).1 hsp
  exact ⟨h1, hp, kwLow_of_blk h1 fun c hc => by rw [f1.1]; exact hSc c hc⟩

end

end Fl4Proofs.P1

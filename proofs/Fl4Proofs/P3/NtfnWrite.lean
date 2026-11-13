/-
P3 (DESIGN.md §9), notifications: what single word writes leave alone.

A write to a word of the notification `n` leaves the other notifications'
words and all TCB words alone; a write to a field of the TCB `t` leaves the
notifications' words, the other TCBs' words and `t`'s other fields alone
(`NPlaced`: notifications are 64-byte aligned, TCBs 4 KiB aligned, and
the two do not overlap).
-/
import Fl4Proofs.P3.NtfnSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Notif
open fl4_core Fl4Proofs.P1

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {N T : Set U64}

theorem rd_wr_ne {s : S} {a c v : U64} (ha : Aligned a) (hc : Aligned c) (h : a ≠ c) :
    L.mem (L.wr s a v) c = L.mem s c :=
  L.mem_wr_ne ha hc (fun e => h (UScalar.eq_of_val_eq e))

theorem rd_wr_eq {s : S} {a v : U64} (ha : Aligned a) : L.mem (L.wr s a v) a = v := L.mem_wr_same ha

/-! ## Agreement is transitive -/

theorem NWordsEq.trans {m₁ m₂ m₃ : U64 → U64} {n : U64} (h₁ : NWordsEq m₁ m₂ n) (h₂ : NWordsEq m₂ m₃ n) :
    NWordsEq m₁ m₃ n :=
  ⟨h₂.head.trans h₁.head, h₂.ts.trans h₁.ts, h₂.badge.trans h₁.badge, h₂.bound.trans h₁.bound, h₂.sc.trans h₁.sc⟩
theorem TFieldsEq.trans {m₁ m₂ m₃ : U64 → U64} {t : U64} (h₁ : TFieldsEq m₁ m₂ t) (h₂ : TFieldsEq m₂ m₃ t) :
    TFieldsEq m₁ m₃ t :=
  ⟨h₂.st.trans h₁.st, h₂.blk.trans h₁.blk, h₂.badge.trans h₁.badge, h₂.prio.trans h₁.prio⟩
theorem TLinksEq.trans {m₁ m₂ m₃ : U64 → U64} {t : U64} (h₁ : TLinksEq m₁ m₂ t) (h₂ : TLinksEq m₂ m₃ t) :
    TLinksEq m₁ m₃ t :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩
theorem NWordsEq.rfl' {m : U64 → U64} {n : U64} : NWordsEq m m n := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem TFieldsEq.rfl' {m : U64 → U64} {t : U64} : TFieldsEq m m t := ⟨rfl, rfl, rfl, rfl⟩
theorem TLinksEq.rfl' {m : U64 → U64} {t : U64} : TLinksEq m m t := ⟨rfl, rfl⟩

/-! ## Writes to notification words -/

/-- What a write to word `K` of the notification `n` leaves alone. -/
structure NWr (st : machine.Store S) [L : LawfulStore st] (N T : Set U64) (n : U64) (s s' : S) : Prop where
  ntfn : ∀ n' ∈ N, n' ≠ n → NWordsEq (L.mem s) (L.mem s') n'
  tcb : ∀ y ∈ T, TFieldsEq (L.mem s) (L.mem s') y ∧ TLinksEq (L.mem s) (L.mem s') y
  foot : WritesIn st s s' (NWrite N T)

theorem NWr.trans {n : U64} {s₁ s₂ s₃ : S} (h₁ : NWr st N T n s₁ s₂) (h₂ : NWr st N T n s₂ s₃) :
    NWr st N T n s₁ s₃ :=
  ⟨fun n' hn' e => (h₁.ntfn n' hn' e).trans (h₂.ntfn n' hn' e),
   fun y hy => ⟨(h₁.tcb y hy).1.trans (h₂.tcb y hy).1, (h₁.tcb y hy).2.trans (h₂.tcb y hy).2⟩,
   (h₁.foot.trans h₂.foot).mono (fun _ h => by rcases h with h | h <;> exact h)⟩

theorem nwr_wr (hP : NPlaced T N) {n K : U64} (hn : n ∈ N) (hK : K.val < 40) (hK8 : K.val % 8 = 0)
    (s : S) (v : U64) : NWr st N T n s (L.wr s (core.num.U64.wrapping_add n K) v) := by
  have hna := hP.ntfn n hn
  obtain ⟨ha, hf⟩ := nword hP hn hK hK8
  have hnn : ∀ n' ∈ N, n' ≠ n → ∀ K' : U64, K'.val < 40 → K'.val % 8 = 0 →
      L.mem (L.wr s (core.num.U64.wrapping_add n K) v) (core.num.U64.wrapping_add n' K') =
        L.mem s (core.num.U64.wrapping_add n' K') := by
    intro n' hn' e K' h1 h2
    refine rd_wr_ne ha (nword hP hn' h1 h2).1 ?_
    rw [Ne, nn_eq_iff hna (hP.ntfn n' hn') (by omega) (by omega)]
    exact fun h => e h.1.symm
  have htn : ∀ y ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 →
      L.mem (L.wr s (core.num.U64.wrapping_add n K) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') := by
    intro y hy K' h1 h2
    exact rd_wr_ne ha (tword hP hy h1 h2) (tn_ne (hP.tcb y hy) hna (hP.disj n hn y hy) h1 (by omega)).symm
  have hf' : NWrite N T (core.num.U64.wrapping_add n K) := by
    refine Or.inl ⟨n, hn, ?_⟩
    rw [nfield_val hna (by omega)]; omega
  refine ⟨fun n' hn' e => ?_, fun y hy => ?_, (writesIn_wr ha).mono fun b hb => hb ▸ hf'⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [epHeadA_eq]; exact hnn n' hn' e _ (by simp) (by simp)
    · rw [epTSA_eq]; exact hnn n' hn' e _ (by simp) (by simp)
    · rw [nBadgeA_eq]; exact hnn n' hn' e _ (by simp) (by simp)
    · rw [nBoundA_eq]; exact hnn n' hn' e _ (by simp) (by simp)
    · rw [nScA_eq]; exact hnn n' hn' e _ (by simp) (by simp)
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [tStA_eq]; exact htn y hy _ (by simp) (by simp)
    · rw [tBlockA_eq]; exact htn y hy _ (by simp) (by simp)
    · rw [badgeRegA_eq]; exact htn y hy _ (by simp) (by simp)
    · rw [prioA_eq']; exact htn y hy _ (by simp) (by simp)
    · rw [prevEp_eq]; exact htn y hy _ (by simp) (by simp)
    · rw [nextEp_eq]; exact htn y hy _ (by simp) (by simp)

/-- Words of one notification are distinct. -/
theorem nwords_ne {n K1 K2 : U64} (hn : NAddr n) (h1 : K1.val < 64) (h2 : K2.val < 64) (hne : K1 ≠ K2) :
    core.num.U64.wrapping_add n K1 ≠ core.num.U64.wrapping_add n K2 := by
  rw [Ne, nn_eq_iff hn hn h1 h2]; exact fun h => hne h.2

/-! ## Writes to TCB fields -/

/-- What a write to a field (not a link) of the TCB `t` leaves alone. -/
structure TWr (st : machine.Store S) [L : LawfulStore st] (N T : Set U64) (t : U64) (s s' : S) : Prop where
  ntfn : ∀ n ∈ N, NWordsEq (L.mem s) (L.mem s') n
  tcb : ∀ y ∈ T, y ≠ t → TFieldsEq (L.mem s) (L.mem s') y
  links : ∀ y ∈ T, TLinksEq (L.mem s) (L.mem s') y
  foot : WritesIn st s s' (NWrite N T)

theorem TWr.trans {t : U64} {s₁ s₂ s₃ : S} (h₁ : TWr st N T t s₁ s₂) (h₂ : TWr st N T t s₂ s₃) :
    TWr st N T t s₁ s₃ :=
  ⟨fun n hn => (h₁.ntfn n hn).trans (h₂.ntfn n hn),
   fun y hy e => (h₁.tcb y hy e).trans (h₂.tcb y hy e),
   fun y hy => (h₁.links y hy).trans (h₂.links y hy),
   (h₁.foot.trans h₂.foot).mono (fun _ h => by rcases h with h | h <;> exact h)⟩

/-- A write to field `K` of the TCB `t` (one of the state, block-object and
badge-register words). -/
theorem twr_wr (hP : NPlaced T N) {t K : U64} (ht : t ∈ T)
    (hK : K = 3328#u64 ∨ K = 3336#u64 ∨ K = 256#u64) (s : S) (v : U64) :
    TWr st N T t s (L.wr s (core.num.U64.wrapping_add t K) v) ∧
    ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K' ≠ K →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add t K') =
        L.mem s (core.num.U64.wrapping_add t K') := by
  have hta := hP.tcb t ht
  have hK1 : K.val < 4096 := by rcases hK with rfl | rfl | rfl <;> simp
  have hK8 : K.val % 8 = 0 := by rcases hK with rfl | rfl | rfl <;> simp
  have ha := tword hP ht hK1 hK8
  have hf : NWrite N T (core.num.U64.wrapping_add t K) := by
    refine Or.inr ⟨t, ht, ?_⟩
    rcases hK with rfl | rfl | rfl
    · exact Or.inl (tStA_eq t).symm
    · exact Or.inr (Or.inl (tBlockA_eq t).symm)
    · exact Or.inr (Or.inr (Or.inl (badgeRegA_eq t).symm))
  have htt : ∀ y ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (y = t → K' ≠ K) →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add y K') =
        L.mem s (core.num.U64.wrapping_add y K') := by
    intro y hy K' h1 h2 hne
    refine rd_wr_ne ha (tword hP hy h1 h2) ?_
    rw [Ne, tt_eq_iff hta (hP.tcb y hy) hK1 h1]
    rintro ⟨rfl, rfl⟩; exact hne rfl rfl
  have hnt : ∀ n ∈ N, ∀ K' : U64, K'.val < 40 → K'.val % 8 = 0 →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add n K') =
        L.mem s (core.num.U64.wrapping_add n K') := by
    intro n hn K' h1 h2
    exact rd_wr_ne ha (nword hP hn h1 h2).1 (tn_ne hta (hP.ntfn n hn) (hP.disj n hn t ht) hK1 (by omega))
  have hl : ∀ K' : U64, K' = 3496#u64 ∨ K' = 3504#u64 → K' ≠ K := by
    rintro K' (rfl | rfl) <;> rcases hK with rfl | rfl | rfl <;> simp
  refine ⟨⟨fun n hn => ?_, fun y hy e => ?_, fun y hy => ?_, (writesIn_wr ha).mono fun b hb => hb ▸ hf⟩,
    fun K' h1 h2 hne => htt t ht K' h1 h2 (fun _ => hne)⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [epHeadA_eq]; exact hnt n hn _ (by simp) (by simp)
    · rw [epTSA_eq]; exact hnt n hn _ (by simp) (by simp)
    · rw [nBadgeA_eq]; exact hnt n hn _ (by simp) (by simp)
    · rw [nBoundA_eq]; exact hnt n hn _ (by simp) (by simp)
    · rw [nScA_eq]; exact hnt n hn _ (by simp) (by simp)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [tStA_eq]; exact htt y hy _ (by simp) (by simp) (fun h => absurd h e)
    · rw [tBlockA_eq]; exact htt y hy _ (by simp) (by simp) (fun h => absurd h e)
    · rw [badgeRegA_eq]; exact htt y hy _ (by simp) (by simp) (fun h => absurd h e)
    · rw [prioA_eq']; exact htt y hy _ (by simp) (by simp) (fun h => absurd h e)
  · exact ⟨by rw [prevEp_eq]; exact htt y hy _ (by simp) (by simp) (fun _ => hl _ (Or.inr rfl)),
      by rw [nextEp_eq]; exact htt y hy _ (by simp) (by simp) (fun _ => hl _ (Or.inl rfl))⟩

end

end

end Fl4Proofs.P3.Notif

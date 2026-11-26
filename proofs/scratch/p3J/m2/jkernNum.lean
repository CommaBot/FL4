/-- **`JKern`'s kernel-state facts at the 2-core witness** (`Cs = {0, 1}`). -/
theorem w0_jkernNum :
    (wL.ksb w0).val + 13568 ≤ 2 ^ 64 ∧ (wL.ksb w0).val % 8 = 0 ∧
      (wL.ksb w0).val + 13568 + ((wL.cpu w0).val + 1) * 4288 ≤ 2 ^ 64 ∧ wL.cpu w0 ∈ ({0#u64, 1#u64} : Set U64) ∧
      (∀ c ∈ ({0#u64, 1#u64} : Set U64), c.val < 64) ∧ (0#u64 ∈ ({0#u64, 1#u64} : Set U64)) ∧
      ∃ n : Nat, ∀ c : U64, c ∈ ({0#u64, 1#u64} : Set U64) ↔ c.val < n := by
  refine ⟨fkb_lt, by rw [ksb_w0, fkb_val], by rw [ksb_w0, cpu_w0, fkb_val]; decide, Or.inl rfl, ?_, Or.inl rfl, 2, ?_⟩
  · rintro c (rfl | rfl) <;> decide
  · intro c
    constructor
    · rintro (rfl | rfl) <;> decide
    · intro h
      have h' : c.val = 0 ∨ c.val = 1 := by omega
      rcases h' with h0 | h1
      · exact Or.inl (UScalar.eq_of_val_eq (by rw [h0]; rfl))
      · exact Or.inr (UScalar.eq_of_val_eq (by rw [h1]; rfl))

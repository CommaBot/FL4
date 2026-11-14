/-
P3 (DESIGN.md §9), CSpace: chunked lists (l4v `mdb_chunked`, per chain).

For a relation `R` (here: "the cap at `a` has the cap at `w` in its region"),
`ChunkL R L` says that, for every `a` in `L`, the later elements `w` with
`R a w` form a prefix of what follows `a`. The lemmas say how this survives
inserting an element (`chunkL_ins`), erasing one (`chunkL_erase`) and
renaming (`chunkL_map`), and what it gives (`chunkL_use`).
-/
import Mathlib.Data.List.Basic

namespace Fl4Proofs.P3.Mdb

variable {α : Type}

/-- After `a`, once `R a ·` fails it fails for good. -/
def CA (R : α → α → Bool) (a : α) : List α → Prop
  | [] => True
  | v :: L => (R a v = false → ∀ w ∈ L, R a w = false) ∧ CA R a L

def ChunkL (R : α → α → Bool) : List α → Prop
  | [] => True
  | a :: L => CA R a L ∧ ChunkL R L

theorem ca_use {R : α → α → Bool} {a : α} {B C : List α} {w : α} (h : CA R a (B ++ w :: C))
    (hw : R a w = true) : ∀ v ∈ B, R a v = true := by
  induction B with
  | nil => simp
  | cons b B ih =>
    intro v hv
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hv with rfl | hv
    · by_contra hb
      have := h1 (by simpa using hb) w (by simp)
      rw [hw] at this; cases this
    · exact ih h2 v hv

theorem chunkL_append {R : α → α → Bool} {A L : List α} (h : ChunkL R (A ++ L)) : ChunkL R L := by
  induction A with
  | nil => exact h
  | cons a A ih => exact ih h.2

theorem chunkL_ca {R : α → α → Bool} {A L : List α} {a : α} (h : ChunkL R (A ++ a :: L)) : CA R a L :=
  (chunkL_append h).1

theorem ca_congr {R R' : α → α → Bool} {a a' : α} {L : List α} (h : CA R a L)
    (he : ∀ v ∈ L, R' a' v = R a v) : CA R' a' L := by
  induction L with
  | nil => trivial
  | cons v L ih =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hv w hw => ?_, ih h2 (fun u hu => he u (by simp [hu]))⟩
    rw [he v (by simp)] at hv
    rw [he w (by simp [hw])]; exact h1 hv w hw

theorem ca_ins {R R' : α → α → Bool} {a s d : α} {P B : List α} (h : CA R a (P ++ s :: B))
    (he : ∀ v ∈ P ++ s :: B, R' a v = R a v) (hd : R' a d = R a s) : CA R' a (P ++ s :: d :: B) := by
  induction P with
  | nil =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hs w hw => ?_, fun hdd w hw => ?_, ca_congr h2 (fun v hv => he v (by simp [hv]))⟩
    · rw [he s (by simp)] at hs
      rcases List.mem_cons.1 hw with rfl | hw
      · rw [hd]; exact hs
      · rw [he w (by simp [hw])]; exact h1 hs w hw
    · rw [hd] at hdd
      rw [he w (by simp [hw])]; exact h1 hdd w hw
  | cons p P ih =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hp w hw => ?_, ih h2 (fun v hv => he v (by simp at hv ⊢; tauto))⟩
    rw [he p (by simp)] at hp
    have hw' : w = d ∨ w ∈ P ++ s :: B := by simp at hw ⊢; tauto
    rcases hw' with rfl | hw'
    · rw [hd]; exact h1 hp s (by simp)
    · rw [he w (by simp [hw'])]; exact h1 hp w hw'

/-- Inserting `d` right after `s`, `d` behaving like `s` (and in its own
region). -/
theorem chunkL_ins {R R' : α → α → Bool} {s d : α} {A B : List α} (h : ChunkL R (A ++ s :: B))
    (he : ∀ u ∈ A ++ s :: B, ∀ v ∈ A ++ s :: B, R' u v = R u v)
    (hd1 : ∀ u ∈ A ++ s :: B, R' u d = R u s) (hd2 : ∀ v ∈ A ++ s :: B, R' d v = R s v)
    (hss : R' s d = true) : ChunkL R' (A ++ s :: d :: B) := by
  induction A with
  | nil =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨⟨fun h0 => (by rw [hss] at h0; cases h0), ca_congr h1 (fun v hv => he s (by simp) v (by simp [hv]))⟩,
      ca_congr h1 (fun v hv => hd2 v (by simp [hv])), ?_⟩
    have hB : ChunkL R B := h2
    clear h1 h2
    have he' : ∀ u ∈ B, ∀ v ∈ B, R' u v = R u v := fun u hu v hv => he u (by simp [hu]) v (by simp [hv])
    clear he hd1 hd2 hss
    induction B with
    | nil => trivial
    | cons b B ih =>
      exact ⟨ca_congr hB.1 (fun v hv => he' b (by simp) v (by simp [hv])),
        ih hB.2 (fun u hu v hv => he' u (by simp [hu]) v (by simp [hv]))⟩
  | cons a A ih =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨ca_ins h1 (fun v hv => he a (by simp) v (by simp at hv ⊢; tauto)) (hd1 a (by simp)), ?_⟩
    exact ih h2 (fun u hu v hv => he u (by simp at hu ⊢; tauto) v (by simp at hv ⊢; tauto))
      (fun u hu => hd1 u (by simp at hu ⊢; tauto)) (fun v hv => hd2 v (by simp at hv ⊢; tauto))

theorem ca_erase {R : α → α → Bool} {a x : α} {P B : List α} (h : CA R a (P ++ x :: B)) : CA R a (P ++ B) := by
  induction P with
  | nil => exact h.2
  | cons p P ih =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨fun hp w hw => h1 hp w (by simp at hw ⊢; tauto), ih h2⟩

theorem chunkL_erase {R : α → α → Bool} {x : α} {A B : List α} (h : ChunkL R (A ++ x :: B)) :
    ChunkL R (A ++ B) := by
  induction A with
  | nil => exact h.2
  | cons a A ih => exact ⟨ca_erase h.1, ih h.2⟩

theorem chunkL_map {R : α → α → Bool} {R' : α → α → Bool} (e : α → α) {L : List α} (h : ChunkL R L)
    (he : ∀ u ∈ L, ∀ v ∈ L, R' (e u) (e v) = R u v) : ChunkL R' (L.map e) := by
  induction L with
  | nil => trivial
  | cons a L ih =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ih h2 (fun u hu v hv => he u (by simp [hu]) v (by simp [hv]))⟩
    have he' : ∀ v ∈ L, R' (e a) (e v) = R a v := fun v hv => he a (by simp) v (by simp [hv])
    clear h2 ih he
    induction L with
    | nil => trivial
    | cons v L ih =>
      obtain ⟨h3, h4⟩ := h1
      refine ⟨fun hv w hw => ?_, ih h4 (fun u hu => he' u (by simp [hu]))⟩
      simp only [List.mem_map] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      rw [he' v (by simp)] at hv
      rw [he' w' (by simp [hw'])]; exact h3 hv w' hw'

theorem chunkL_congr {R R' : α → α → Bool} {L : List α} (h : ChunkL R L)
    (he : ∀ u ∈ L, ∀ v ∈ L, R' u v = R u v) : ChunkL R' L := by
  have := chunkL_map (R' := R') id h (by simpa using he)
  simpa using this

theorem ca_false {α : Type} {R : α → α → Bool} {a : α} {L : List α} (h : ∀ v ∈ L, R a v = false) : CA R a L := by
  induction L with
  | nil => trivial
  | cons v L ih =>
    exact ⟨fun _ w hw => h w (by simp [hw]), ih (fun w hw => h w (by simp [hw]))⟩

/-- Inserting `d` right after `s`, `d` seen from the slots before it as `s`
is, with its own run after it. -/
theorem chunkL_ins2 {α : Type} {R R' : α → α → Bool} {s d : α} {A B : List α} (h : ChunkL R (A ++ s :: B))
    (he : ∀ u ∈ A ++ s :: B, ∀ v ∈ A ++ s :: B, R' u v = R u v)
    (hd1 : ∀ u ∈ A ++ s :: B, R' u d = R u s) (hdB : CA R' d B)
    (hss : R' s d = true) : ChunkL R' (A ++ s :: d :: B) := by
  induction A with
  | nil =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨⟨fun h0 => (by rw [hss] at h0; cases h0), ca_congr h1 (fun v hv => he s (by simp) v (by simp [hv]))⟩,
      hdB, ?_⟩
    have hB : ChunkL R B := h2
    clear h1 h2
    have he' : ∀ u ∈ B, ∀ v ∈ B, R' u v = R u v := fun u hu v hv => he u (by simp [hu]) v (by simp [hv])
    clear he hd1 hdB hss
    induction B with
    | nil => trivial
    | cons b B ih =>
      exact ⟨ca_congr hB.1 (fun v hv => he' b (by simp) v (by simp [hv])),
        ih hB.2 (fun u hu v hv => he' u (by simp [hu]) v (by simp [hv]))⟩
  | cons a A ih =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨ca_ins h1 (fun v hv => he a (by simp) v (by simp at hv ⊢; tauto)) (hd1 a (by simp)), ?_⟩
    exact ih h2 (fun u hu v hv => he u (by simp at hu ⊢; tauto) v (by simp at hv ⊢; tauto))
      (fun u hu => hd1 u (by simp at hu ⊢; tauto))

end Fl4Proofs.P3.Mdb

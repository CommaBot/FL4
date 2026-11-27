/-
# P2: building `SProg` trees for extracted bodies (line hpz)

Tools to discharge `IsProg F p` (`P2/PathObl.lean`) by constructing `p` from the extracted code, and the
counter-schema for the joint premise `∃ p, IsProg F p ∧ NoZero p`.

* `SProg.sbind` / `Monad SProg`: trees form a monad (sequencing), so a body's tree is written in `do`
  notation with the state threading removed (`interp_sbind`: `interp` maps sequencing to `Result` bind).
* `SProg.liftR`: a pure `Result` step as a tree (`interp_liftR`: exact for every non-diverging `r`).
* `SProg.iter`: a loop with an iteration budget; `interp_iter` relates it to Aeneas' `loop` under a
  measure that the Aeneas body's `cont` step decreases on every store.
* `interp_ne_div`: a `NoZero` tree never diverges when the store's other operations and the Arch calls never
  do. `not_isProg_noZero`: hence `∃ p, IsProg F p ∧ NoZero p` is refuted by one store / Arch instance with
  non-diverging `read`/`read_pair`/`write`/`ks_base`/`cur_cpu`/`frame_masks` and Arch calls on which the body
  diverges, e.g. a store whose `zero` / `clear_free` diverge and a run that reaches one of them
  (`handoff/hpz.md`: the I/O port body is such a body).
-/
import Fl4Proofs.P2.PathObl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core

/-! ## Sequencing -/

/-- Sequencing of trees: run `p`, then `f` on its value. -/
def SProg.sbind {X Y : Type} : SProg X → (X → SProg Y) → SProg Y
  | .ret x, f => f x
  | .err e, _ => .err e
  | .rd a k, f => .rd a (fun v => (k v).sbind f)
  | .rdp a k, f => .rdp a (fun v => (k v).sbind f)
  | .wr a v k, f => .wr a v (k.sbind f)
  | .zero a n k, f => .zero a n (k.sbind f)
  | .clr a n k, f => .clr a n (k.sbind f)
  | .ksb k, f => .ksb (fun v => (k v).sbind f)
  | .cpu k, f => .cpu (fun v => (k v).sbind f)
  | .masks k, f => .masks (fun v => (k v).sbind f)
  | .arch op k, f => .arch op (fun v => (k v).sbind f)

instance : Monad SProg where
  pure := .ret
  bind := SProg.sbind

theorem SProg.bind_eq_sbind {X Y : Type} (p : SProg X) (f : X → SProg Y) : (p >>= f) = p.sbind f := rfl
theorem SProg.pure_eq_ret {X : Type} (x : X) : (pure x : SProg X) = .ret x := rfl

section
variable {S : Type} {A : Type} (st : machine.Store S) (ar : machine.Arch A)

@[simp] theorem interp_ret' {X : Type} (x : X) (s : S) (a : A) : interp st ar (.ret x) s a = ok (x, s, a) := by
  simp [interp]

@[simp] theorem interp_err' {X : Type} (e : Error) (s : S) (a : A) :
    interp st ar (SProg.err (X := X) e) s a = fail e := by
  simp [interp]

/-- `interp` maps sequencing to `Result` bind. -/
theorem interp_sbind {X Y : Type} (p : SProg X) (f : X → SProg Y) (s : S) (a : A) :
    interp st ar (p.sbind f) s a =
      Aeneas.Std.bind (interp st ar p s a) (fun r => interp st ar (f r.1) r.2.1 r.2.2) := by
  induction p generalizing s a with
  | ret x => simp only [SProg.sbind, interp, bind_ok]
  | err e => simp only [SProg.sbind, interp, bind_fail]
  | rd p k ih => simp only [SProg.sbind, interp, Std.bind_assoc, ih]
  | rdp p k ih => simp only [SProg.sbind, interp, Std.bind_assoc, ih]
  | wr p v k ih => simp only [SProg.sbind, interp, Std.bind_assoc, ih]
  | zero p n k ih => simp only [SProg.sbind, interp, Std.bind_assoc, ih]
  | clr p n k ih => simp only [SProg.sbind, interp, Std.bind_assoc, ih]
  | ksb k ih => simp only [SProg.sbind, interp, Std.bind_assoc, ih]
  | cpu k ih => simp only [SProg.sbind, interp, Std.bind_assoc, ih]
  | masks k ih => simp only [SProg.sbind, interp, Std.bind_assoc, ih]
  | arch op k ih =>
    simp only [SProg.sbind, interp, Std.bind_assoc]
    congr 1; funext r; rcases r with ⟨v, a'⟩; exact ih v s a'

/-- `interp_sbind` in `do` form. -/
theorem interp_bind' {X Y : Type} (p : SProg X) (f : X → SProg Y) (s : S) (a : A) :
    interp st ar (p >>= f) s a =
      (do let r ← interp st ar p s a; interp st ar (f r.1) r.2.1 r.2.2) := by
  show interp st ar (p.sbind f) s a = _
  exact interp_sbind st ar p f s a

end

/-- Sequencing keeps `NoZero`. -/
theorem NoZero.sbind {X Y : Type} {p : SProg X} {f : X → SProg Y} (hp : NoZero p) (hf : ∀ x, NoZero (f x)) :
    NoZero (p.sbind f) := by
  induction p with
  | ret x => exact hf x
  | err e => trivial
  | rd _ k ih => exact fun v => ih v (hp v)
  | rdp _ k ih => exact fun v => ih v (hp v)
  | wr _ _ k ih => exact ih hp
  | zero _ _ k _ => exact absurd hp id
  | clr _ _ k _ => exact absurd hp id
  | ksb k ih => exact fun v => ih v (hp v)
  | cpu k ih => exact fun v => ih v (hp v)
  | masks k ih => exact fun v => ih v (hp v)
  | arch _ k ih => exact fun v => ih v (hp v)

/-! ## Pure steps -/

/-- Every `Result` value is `ok`, `fail` or `div`. -/
theorem result_trichotomy {T : Type} (r : Result T) : (∃ v, r = ok v) ∨ (∃ e, r = fail e) ∨ r = div := by
  cases r with
  | ret v => exact .inl ⟨v, rfl⟩
  | vis i k =>
    cases i with
    | fail e =>
      refine .inr (.inl ⟨e, ?_⟩)
      rw [Result.fail_eq_vis]
      congr 1
      funext x
      exact x.elim
  | div => exact .inr (.inr rfl)

open Classical in
/-- A pure `Result` step as a tree (exact for every non-diverging `r`, `interp_liftR`). -/
noncomputable def SProg.liftR {T : Type} (r : Result T) : SProg T :=
  if h : ∃ v, r = ok v then .ret h.choose
  else if h : ∃ e, r = fail e then .err h.choose else .err .panic

@[simp] theorem SProg.liftR_ok {T : Type} (v : T) : SProg.liftR (ok v) = .ret v := by
  have h : ∃ w, (ok v : Result T) = ok w := ⟨v, rfl⟩
  rw [SProg.liftR, dif_pos h]
  congr 1
  exact (Result.ok_injective h.choose_spec).symm

@[simp] theorem SProg.liftR_fail {T : Type} (e : Error) : SProg.liftR (fail e : Result T) = .err e := by
  have h0 : ¬ ∃ w, (fail e : Result T) = ok w := fun ⟨w, hw⟩ => fail_not_ok hw
  have h : ∃ e', (fail e : Result T) = fail e' := ⟨e, rfl⟩
  rw [SProg.liftR, dif_neg h0, dif_pos h]
  congr 1
  exact (Result.fail_injective h.choose_spec).symm

theorem interp_liftR {S A T : Type} (st : machine.Store S) (ar : machine.Arch A) (r : Result T) (hr : r ≠ div)
    (s : S) (a : A) : interp st ar (SProg.liftR r) s a = (do let v ← r; ok (v, s, a)) := by
  rcases result_trichotomy r with ⟨v, rfl⟩ | ⟨e, rfl⟩ | rfl
  · simp
  · simp
  · exact absurd rfl hr

theorem NoZero.liftR {T : Type} (r : Result T) : NoZero (SProg.liftR r) := by
  unfold SProg.liftR; split
  · trivial
  · split <;> trivial

/-- Inversion of a successful bind. -/
theorem bind_eq_ok' {T U : Type} {m : Result T} {f : T → Result U} {y : U} (h : (m >>= f) = ok y) :
    ∃ x, m = ok x ∧ f x = ok y := by
  rcases result_trichotomy m with ⟨x, rfl⟩ | ⟨e, rfl⟩ | rfl
  · exact ⟨x, rfl, by rw [bind_tc_ok] at h; exact h⟩
  · rw [bind_tc_fail] at h; exact absurd h fail_not_ok
  · rw [bind_tc_div] at h; exact absurd h div_not_ok

/-! ## Store and Arch leaves -/

/-- The store and Arch leaves as trees. -/
def SProg.read (x : U64) : SProg U64 := .rd x .ret
def SProg.readPair (x : U64) : SProg (U64 × U64) := .rdp x .ret
def SProg.write (x v : U64) : SProg Unit := .wr x v (.ret ())
def SProg.ksBase : SProg U64 := .ksb .ret
def SProg.curCpu : SProg U64 := .cpu .ret
def SProg.frameMasks : SProg (U64 × U64) := .masks .ret
def SProg.call (op : ArchCall) : SProg AV := .arch op .ret

section
variable {S : Type} {A : Type} (st : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)

@[simp] theorem interp_read' (x : U64) :
    interp st ar (SProg.read x) s a = (do let v ← st.read s x; ok (v, s, a)) := by simp [SProg.read, interp]
@[simp] theorem interp_readPair' (x : U64) :
    interp st ar (SProg.readPair x) s a = (do let v ← st.read_pair s x; ok (v, s, a)) := by
  simp [SProg.readPair, interp]
@[simp] theorem interp_write' (x v : U64) :
    interp st ar (SProg.write x v) s a = (do let s' ← st.write s x v; ok ((), s', a)) := by
  simp [SProg.write, interp]
@[simp] theorem interp_ksBase' :
    interp st ar SProg.ksBase s a = (do let v ← st.ks_base s; ok (v, s, a)) := by simp [SProg.ksBase, interp]
@[simp] theorem interp_curCpu' :
    interp st ar SProg.curCpu s a = (do let v ← st.cur_cpu s; ok (v, s, a)) := by simp [SProg.curCpu, interp]
@[simp] theorem interp_frameMasks' :
    interp st ar SProg.frameMasks s a = (do let v ← st.frame_masks s; ok (v, s, a)) := by
  simp [SProg.frameMasks, interp]

end

theorem NoZero.read (x : U64) : NoZero (SProg.read x) := fun _ => trivial
theorem NoZero.readPair (x : U64) : NoZero (SProg.readPair x) := fun _ => trivial
theorem NoZero.write (x v : U64) : NoZero (SProg.write x v) := trivial
theorem NoZero.ksBase : NoZero SProg.ksBase := fun _ => trivial
theorem NoZero.curCpu : NoZero SProg.curCpu := fun _ => trivial
theorem NoZero.frameMasks : NoZero SProg.frameMasks := fun _ => trivial
theorem NoZero.call (op : ArchCall) : NoZero (SProg.call op) := fun _ => trivial

/-! ## Loops -/

/-- A loop with an iteration budget `n` (`err panic` once it is spent; `interp_iter` rules that out). -/
def SProg.iter {X Y : Type} (body : X → SProg (ControlFlow X Y)) : Nat → X → SProg Y
  | 0, _ => .err .panic
  | n + 1, x => (body x).sbind fun
    | .cont x' => SProg.iter body n x'
    | .done y => .ret y

theorem NoZero.iter {X Y : Type} {body : X → SProg (ControlFlow X Y)} (hb : ∀ x, NoZero (body x)) :
    ∀ n x, NoZero (SProg.iter body n x)
  | 0, _ => trivial
  | n + 1, x => NoZero.sbind (hb x) (fun c => by cases c <;> [exact NoZero.iter hb n _; trivial])

/-- A tree-loop step's outcome as an Aeneas loop-body result (`mk` / `fin` pack the store and Arch state). -/
def cfOut {S A X Y σ β : Type} (mk : X → S → A → σ) (fin : Y → S → A → β) (r : ControlFlow X Y × S × A) :
    Result (ControlFlow σ β) :=
  match r.1 with
  | .cont x' => ok (.cont (mk x' r.2.1 r.2.2))
  | .done y => ok (.done (fin y r.2.1 r.2.2))

/-- **Loops.** The Aeneas loop over `σ` (the loop variables, store and Arch state among them: `mk x s a`, its
result `fin y s a`) is the tree loop over `X` when the tree body is the Aeneas body (`hb`) and a measure `μ`
on `X` drops at every `cont` step of the tree body on every store (`hμ`), within the budget `n > μ x`. -/
theorem interp_iter {S A X Y σ β : Type} (st : machine.Store S) (ar : machine.Arch A)
    (body : σ → Result (ControlFlow σ β)) (bodyP : X → SProg (ControlFlow X Y))
    (mk : X → S → A → σ) (fin : Y → S → A → β) (μ : X → Nat)
    (hb : ∀ x s a, body (mk x s a) = interp st ar (bodyP x) s a >>= fun r => cfOut mk fin r)
    (hμ : ∀ x s a x' s' a', body (mk x s a) = ok (.cont (mk x' s' a')) → μ x' < μ x) :
    ∀ n x s a, μ x < n →
      loop body (mk x s a) = (do let r ← interp st ar (SProg.iter bodyP n x) s a; ok (fin r.1 r.2.1 r.2.2))
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, s, a, h => by
    rw [loop, hb, SProg.iter, interp_sbind]
    simp only [cfOut]
    rcases result_trichotomy (interp st ar (bodyP x) s a) with ⟨⟨c, s', a'⟩, e⟩ | ⟨er, e⟩ | e
    · rw [e]
      simp only [bind_tc_eq, bind_ok]
      cases c with
      | cont x' =>
        simp only [bind_ok]
        have hc : body (mk x s a) = ok (.cont (mk x' s' a')) := by
          rw [hb, e]; simp only [bind_tc_eq, bind_ok, cfOut]
        have := interp_iter st ar body bodyP mk fin μ hb hμ n x' s' a'
          (Nat.lt_of_lt_of_le (hμ x s a x' s' a' hc) (Nat.le_of_lt_succ h))
        simpa only [bind_tc_eq] using this
      | done y => simp only [bind_ok, interp, cfOut]
    · rw [e]; simp only [bind_tc_eq, bind_fail]
    · rw [e]; simp only [bind_tc_eq, bind_div]

/-! ## The counter-schema for `IsProg ∧ NoZero` -/

section
variable {S : Type} {A : Type} (st : machine.Store S) (ar : machine.Arch A)

/-- The store operations a `NoZero` tree uses, and the Arch calls, never diverge. -/
structure NoDivOps : Prop where
  read : ∀ s x, st.read s x ≠ div
  read_pair : ∀ s x, st.read_pair s x ≠ div
  write : ∀ s x v, st.write s x v ≠ div
  ks_base : ∀ s, st.ks_base s ≠ div
  cur_cpu : ∀ s, st.cur_cpu s ≠ div
  frame_masks : ∀ s, st.frame_masks s ≠ div
  arch : ∀ op a, callArch ar op a ≠ div

theorem bind_ne_div' {T U : Type} {r : Result T} {f : T → Result U} (hr : r ≠ div) (hf : ∀ v, f v ≠ div) :
    (r >>= f) ≠ div := by
  rcases result_trichotomy r with ⟨v, rfl⟩ | ⟨e, rfl⟩ | rfl
  · rw [bind_tc_ok]; exact hf v
  · rw [bind_tc_fail]; exact fail_not_div
  · exact absurd rfl hr

/-- A `NoZero` tree never diverges on a store and Arch instance with `NoDivOps`. -/
theorem interp_ne_div {X : Type} (hN : NoDivOps st ar) :
    ∀ (p : SProg X), NoZero p → ∀ s a, interp st ar p s a ≠ div
  | .ret x, _, s, a => by simp [interp]
  | .err e, _, s, a => by simp [interp]
  | .rd x k, hz, s, a => by
    simp only [interp]; exact bind_ne_div' (hN.read s x) fun v => interp_ne_div hN (k v) (hz v) s a
  | .rdp x k, hz, s, a => by
    simp only [interp]
    exact bind_ne_div' (hN.read_pair s x) fun v => interp_ne_div hN (k v) (hz v) s a
  | .wr x v k, hz, s, a => by
    simp only [interp]; exact bind_ne_div' (hN.write s x v) fun s' => interp_ne_div hN k hz s' a
  | .zero _ _ _, hz, _, _ => absurd hz id
  | .clr _ _ _, hz, _, _ => absurd hz id
  | .ksb k, hz, s, a => by
    simp only [interp]; exact bind_ne_div' (hN.ks_base s) fun v => interp_ne_div hN (k v) (hz v) s a
  | .cpu k, hz, s, a => by
    simp only [interp]; exact bind_ne_div' (hN.cur_cpu s) fun v => interp_ne_div hN (k v) (hz v) s a
  | .masks k, hz, s, a => by
    simp only [interp]
    exact bind_ne_div' (hN.frame_masks s) fun v => interp_ne_div hN (k v) (hz v) s a
  | .arch op k, hz, s, a => by
    simp only [interp]
    exact bind_ne_div' (hN.arch op a) fun r => interp_ne_div hN (k r.1) (hz r.1) s r.2

/-- **Counter-schema**: if the body diverges at some state on a store / Arch instance with `NoDivOps`, no tree
has both `IsProg` and `NoZero`. -/
theorem not_isProg_noZero {X : Type}
    (F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A))
    (hN : NoDivOps st ar) (s : S) (a : A) (hF : F ar st s a = div) :
    ¬ ∃ p : SProg X, IsProg F p ∧ NoZero p := by
  rintro ⟨p, hp, hz⟩
  have h := hp A ar st
  exact interp_ne_div st ar hN p hz s a (by rw [← h]; exact hF)

end

end Fl4Proofs.P2.PathObl

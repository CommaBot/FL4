/-
# P2 (line mmuAD, gen 2): **environment writes that only the reader's insensitivity makes harmless**

`SerialHw` adds a hardware write of a word whose lock no core holds (`HwWr`): to every in-progress local path it
is `Foreign`, so it commutes with them. The page walker's accessed / dirty writes (`MmuAD.MmuAD` [P]) also hit
words that local paths *may read*: the upper paging levels (gate-owned, read lock-free by the walks) and a leaf
whose lock a local Delete holds. Such a write is not `Foreign`. It still serializes, as its own entry at the moment
it happens, provided every reader is **insensitive** to it, and a word a local path has stored to is never written
by it. This module states and proves that, generically (any word set `G`, any equivalence `Q` of values, any
"not writable" value class `NP`):

* **`ADIns G Q NP p`**: at every read (`rd`, `rds`, `rdc`) of a word of `G`, the continuation is the same tree
  for `Q`-equivalent values (`k u = k w`); every store into a word of `G` stores an `NP` value. For FL4:
  `G` = the paging-structure entries, `Q` = `MmuAD.ADEq` (equal off bits 5, 6), `NP` = not present
  (`v &&& 1 = 0`): the walker never writes a non-present entry (SDM §4.8, `MmuAD.present`), so once a local
  Delete has stored `0` into a leaf no A/D write can hit it until the next present store (which no local path
  makes on this branch).
* **`ADWr G Q NP s x y`**: the environment's write `x := y`: `x ∈ G`, `s.mem x` is not `NP`, `y` is
  `Q`-equivalent to it, the write moves no owner and `x`'s class is untracked. No condition on `x`'s owner or
  lock: gate words, held leaves and free leaves are all covered.
* **`SimA`**: `LocInv.sim` strengthened to histories `Q`-perturbed on the path's readable `G` words; **`InvA`**:
  `InvH` + `SimA` of every in-progress path + every in-progress path is in its glue or `ADIns` + every `G` word a
  path has stored to holds an `NP` value. `InvA.step` (every core step, given that a body that starts is `ADIns`),
  `InvA.hw` (a `HwWr`), **`InvA.ad`** (an `ADWr`, the history taking the same write: `H' = H[x := y]`),
  `InvA.regate` (the word set may change while no local path runs, i.e. under a closed gate).
* **`safe_ad`** / **`sinv_ad`**: `SInv` is kept by an `ADWr`: to a path that may not read `x` it is `Foreign`
  (`Safe.foreign`); to one that may, the body is `ADIns`, so `Safe` transfers (`freach_ad`: the memories other
  cores reach after the write are those reached before, with the write on top).
* **`ARun`**: executions whose core steps are `SafeStep`s whose started bodies are `ADIns G`, with `HwWr` steps,
  `ADWr` steps, and changes of `G` under a closed gate. **`serializable_safeA`**: where an `ARun` reaches a state
  with no local path in progress, memory is the serial run of the completed entries, every environment write
  logged as its own entry at the moment it happened. `aRun_of_xsafeRun`: every `XSafeRun` is an `ARun` (for the
  empty `G`, where `ADIns` is vacuous: `adIns_bot`).

**How the two kinds of A/D write of the task map here.** (1) An A bit on an upper-level entry: `x` gate-owned,
in no path's write set, so it is logged at its time; a path that read the entry before the write and one that
reads it after see `Q`-equivalent values, and `ADIns` makes their continuations equal: the serial order with the
write before the path explains both. (2) A/D on a leaf whose lock a local Delete holds: before Delete's store the
same argument (only the holder may read it; it is logged before the holder's entry, which is logged at `leave`);
after Delete's store `0` the entry is not present, and `ADWr.np` excludes the write (it would need a present
entry) — the "log after the holder's release" case does not arise on this branch, as no local path stores a
present value into a paging word (`ADIns.wr`).

No premise: everything here is proved. The FL4 instantiation (that the started bodies are `ADIns` for the paging
words) is the per-path part, see the handoff. No existing statement or file changed.
-/
import Fl4Proofs.P2.SerialHw

namespace Fl4Proofs.P2.Serial

noncomputable section

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-! ## Insensitive programs -/

/-- **A program insensitive to `Q`-changes of the `G` words**, storing only `NP` values into them. -/
inductive ADIns (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) : Prog A V L → Prop
  | done : ADIns G Q NP .done
  | rd {a : A} {k : V → Prog A V L} : (G a → ∀ u w, Q u w → k u = k w) → (∀ v, ADIns G Q NP (k v)) →
      ADIns G Q NP (.rd a k)
  | rds {a : A} {k : V → Prog A V L} : (G a → ∀ u w, Q u w → k u = k w) → (∀ v, ADIns G Q NP (k v)) →
      ADIns G Q NP (.rds a k)
  | rdc {a : A} {K : V → V → Prop} {k : V → Prog A V L} : (G a → ∀ u w, Q u w → k u = k w) →
      (∀ v, ADIns G Q NP (k v)) → ADIns G Q NP (.rdc a K k)
  | wr {a : A} {v : V} {k : Prog A V L} : (G a → NP v) → ADIns G Q NP k → ADIns G Q NP (.wr a v k)
  | lock {l : L} {k : Bool → Prog A V L} : (∀ b, ADIns G Q NP (k b)) → ADIns G Q NP (.lock l k)
  | start {k : Prog A V L} : ADIns G Q NP k → ADIns G Q NP (.start k)

/-- With no `G` word every program is insensitive. -/
theorem adIns_bot (Q : V → V → Prop) (NP : V → Prop) (p : Prog A V L) : ADIns (fun _ => False) Q NP p := by
  induction p with
  | done => exact .done
  | rd a k ih => exact .rd (fun h => h.elim) ih
  | wr a v k ih => exact .wr (fun h => h.elim) ih
  | lock l k ih => exact .lock ih
  | rds a k ih => exact .rds (fun h => h.elim) ih
  | start k ih => exact .start ih
  | rdc a K k ih => exact .rdc (fun h => h.elim) ih

/-- **The environment's write `x := y`** (module docstring). -/
structure ADWr (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) (s : Cfg A V C L) (x : A) (y : V) : Prop where
  g : G x
  np : ¬ NP (s.mem x)
  q : Q (s.mem x) y
  keep : ∀ m, s.own (Function.update m x y) = s.own m
  ko : s.ko x = .free

/-! ## The strengthened simulation -/

/-- `LocInv.sim` for every history `Q`-perturbed on the `G` words the path may read. -/
def SimA (G : A → Prop) (Q : V → V → Prop) (s : Cfg A V C L) (H : A → V) (d : C) (p0 p : Prog A V L)
    (W : Set A) : Prop :=
  ∀ n n' : A → V, (∀ x, Perm s d x → G x → Q (n x) (H x)) → (∀ x, Perm s d x → ¬ G x → n x = H x) →
    (∀ x, (s.ko x = .gate ∨ s.ko x = .core d) → s.cls x (n x) = s.cls x (H x)) →
    Run p (mix W s.mem n) n' → Run p0 n n'

/-- **The invariant with environment writes.** -/
structure InvA (G : A → Prop) (Q : V → V → Prop) (NP : V → Prop) (m0 : A → V) (s : Cfg A V C L)
    (H : A → V) : Prop where
  inv : InvH m0 s H
  sim : ∀ d p0 p W, s.ph d = .loc p0 p W → SimA G Q s H d p0 p W
  ins : ∀ d p0 p W, s.ph d = .loc p0 p W → Glue s.cls s.ko d p ∨ ADIns G Q NP p
  np : ∀ d p0 p W, s.ph d = .loc p0 p W → ∀ x ∈ W, G x → NP (s.mem x)

section inv
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop}

theorem SimA.mono {s s' : Cfg A V C L} {H H' : A → V} {d : C} {p0 p : Prog A V L} {W : Set A}
    (I : SimA G Q s H d p0 p W)
    (hperm : ∀ x, Perm s d x → Perm s' d x)
    (hH : ∀ x, Perm s d x → H' x = H x)
    (hmem : ∀ x ∈ W, s'.mem x = s.mem x)
    (hko : s'.ko = s.ko) (hcl : s'.cls = s.cls)
    (hHc : ∀ x, (s.ko x = .gate ∨ s.ko x = .core d) → s.cls x (H' x) = s.cls x (H x)) :
    SimA G Q s' H' d p0 p W := by
  intro n n' hG hN hc hr
  have he : mix W s'.mem n = mix W s.mem n := by
    funext x
    by_cases hx : x ∈ W
    · rw [mix_mem hx, mix_mem hx, hmem x hx]
    · rw [mix_nmem hx, mix_nmem hx]
  refine I n n' (fun x hx hg => ?_) (fun x hx hg => ?_) (fun x hx => ?_) (by rw [← he]; exact hr)
  · rw [← hH x hx]; exact hG x (hperm x hx) hg
  · rw [← hH x hx]; exact hN x (hperm x hx) hg
  · have h1 := hc x (by rw [hko]; exact hx)
    rw [hcl] at h1
    exact h1.trans (hHc x hx)

/-- A step of core `c` inside its local path, the history unchanged. -/
theorem InvA.locstep {m0 : A → V} {s s' : Cfg A V C L} {H : A → V} {c : C} {p0 p p' : Prog A V L}
    {W W' : Set A} (I : InvA G Q NP m0 s H) (I' : InvH m0 s' H)
    (hc : s.ph c = .loc p0 p W) (hph : s'.ph = Function.update s.ph c (.loc p0 p' W'))
    (hperm : ∀ d, d ≠ c → ∀ x, Perm s d x → Perm s' d x)
    (hmemd : ∀ d, d ≠ c → ∀ q0 q U, s.ph d = .loc q0 q U → ∀ x ∈ U, s'.mem x = s.mem x)
    (hko : s'.ko = s.ko) (hcl : s'.cls = s.cls)
    (hsim : SimA G Q s' H c p0 p' W') (hins : Glue s.cls s.ko c p' ∨ ADIns G Q NP p')
    (hnp : ∀ x ∈ W', G x → NP (s'.mem x)) : InvA G Q NP m0 s' H where
  inv := I'
  sim d q0 q U hd := by
    rw [hph] at hd
    rcases upd_loc hd with ⟨rfl, he⟩ | ⟨hdc, hd⟩
    · cases he; exact hsim
    · exact (I.sim d q0 q U hd).mono (hperm d hdc) (fun _ _ => rfl) (hmemd d hdc q0 q U hd) hko hcl
        (fun _ _ => rfl)
  ins d q0 q U hd := by
    rw [hph] at hd
    rw [hcl, hko]
    rcases upd_loc hd with ⟨rfl, he⟩ | ⟨_, hd⟩
    · cases he; exact hins
    · exact I.ins d q0 q U hd
  np d q0 q U hd x hx hg := by
    rw [hph] at hd
    rcases upd_loc hd with ⟨rfl, he⟩ | ⟨hdc, hd⟩
    · cases he; exact hnp x hx hg
    · rw [hmemd d hdc q0 q U hd x hx]; exact I.np d q0 q U hd x hx hg

/-- Steps that change neither memory, locks, owners nor classes, and start no local path. -/
theorem InvA.frame {m0 : A → V} {s s' : Cfg A V C L} {H : A → V} (I : InvA G Q NP m0 s H)
    (I' : InvH m0 s' H) (hmem : s'.mem = s.mem) (hlk : s'.lk = s.lk) (hown : s'.own = s.own)
    (hko : s'.ko = s.ko) (hcl : s'.cls = s.cls)
    (hl : ∀ d q0 q U, s'.ph d = .loc q0 q U → s.ph d = .loc q0 q U) : InvA G Q NP m0 s' H where
  inv := I'
  sim d q0 q U hd := (I.sim d q0 q U (hl d q0 q U hd)).mono
    (fun x h => by unfold Perm; rw [hlk, hmem, hown]; exact h) (fun _ _ => rfl)
    (fun x _ => by rw [hmem]) hko hcl (fun _ _ => rfl)
  ins d q0 q U hd := by rw [hcl, hko]; exact I.ins d q0 q U (hl d q0 q U hd)
  np d q0 q U hd x hx hg := by rw [hmem]; exact I.np d q0 q U (hl d q0 q U hd) x hx hg

/-- With no local path in progress, any word set. -/
theorem InvA.of_noLoc {G' : A → Prop} {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H)
    (hq : NoLoc s) : InvA G' Q NP m0 s H where
  inv := I
  sim d _ _ _ hd := absurd (by rw [hd]; trivial) (hq d)
  ins d _ _ _ hd := absurd (by rw [hd]; trivial) (hq d)
  np d _ _ _ hd := absurd (by rw [hd]; trivial) (hq d)

/-- **The word set may change under a closed gate.** -/
theorem InvA.regate (G' : A → Prop) {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvA G Q NP m0 s H)
    (hg : s.gate = .closed) : InvA G' Q NP m0 s H :=
  InvA.of_noLoc I.inv (I.inv.clo hg)

/-- `H a = s.mem a` at a word core `c` may read (no other path has written it, `c` has not). -/
theorem InvH.hist_perm {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {c : C}
    {p0 p : Prog A V L} {W : Set A} (hc : s.ph c = .loc p0 p W) {a : A} (hp : Perm s c a)
    (haW : a ∉ W) : H a = s.mem a := by
  symm; apply I.agree
  intro d q0 q U hd haU
  by_cases hdc : d = c
  · subst hdc; rw [hc] at hd; cases hd; exact haW haU
  · exact held_disj hdc ((I.loc d q0 q U hd).held a haU) hp

/-- **Every core step keeps `InvA`**, given that a body that starts is `ADIns`. -/
theorem InvA.step {m0 : A → V} {s s' : Cfg A V C L} {H : A → V} {c : C} (I : InvA G Q NP m0 s H)
    (hA : ArmInv s) (hal : Allowed s c) (hst : Step s c s')
    (hB : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ADIns G Q NP k) :
    ∃ H', InvA G Q NP m0 s' H' := by
  cases hst with
  | arm p hc =>
    have hc' : ¬ (s.ph c).IsLoc := by rw [hc]; exact Phase.idle_not_loc
    exact ⟨H, I.frame (inv_phase I.inv (Phase.arm_not_loc p) hc') rfl rfl rfl rfl rfl
      (fun d q0 q U h => (upd_nonloc (Phase.arm_not_loc p) hc' d q0 q U).mp h)⟩
  | back hc _ =>
    have hc' : ¬ (s.ph c).IsLoc := by rw [hc]; exact Phase.arm_not_loc _
    exact ⟨H, I.frame (inv_phase I.inv Phase.idle_not_loc hc') rfl rfl rfl rfl rfl
      (fun d q0 q U h => (upd_nonloc Phase.idle_not_loc hc' d q0 q U).mp h)⟩
  | @enter p hc hg =>
    have hnc : ∀ d q0 q U, s.ph d = .loc q0 q U → d ≠ c := by
      rintro d q0 q U hd rfl; rw [hc] at hd; cases hd
    refine ⟨H, inv_enter I.inv hc hg, ?_, ?_, ?_⟩
    · intro d q0 q U hd
      rcases upd_loc hd with ⟨rfl, he⟩ | ⟨hdc, hd⟩
      · cases he
        intro n n' _ _ _ hr
        rw [mix_empty] at hr; exact hr
      · exact (I.sim d q0 q U hd).mono (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
          (fun _ _ => rfl)
    · intro d q0 q U hd
      rcases upd_loc hd with ⟨rfl, he⟩ | ⟨_, hd⟩
      · cases he; exact Or.inl ((hA _ p hc).glue s.cls s.ko _)
      · exact I.ins d q0 q U hd
    · intro d q0 q U hd x hx hg
      rcases upd_loc hd with ⟨rfl, he⟩ | ⟨_, hd⟩
      · cases he; exact absurd hx (Set.notMem_empty x)
      · exact I.np d q0 q U hd x hx hg
  | @rd p0 a k W hc =>
    simp only [Allowed, hc] at hal
    refine ⟨H, I.locstep (inv_rd I.inv hc hal) hc rfl (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ => rfl)
      rfl rfl ?_ ?_ (fun x hx hg => I.np c p0 _ W hc x hx hg)⟩
    · intro n n' hG hN hcn hr
      refine I.sim c p0 _ W hc n n' hG hN hcn (Run.rd ?_)
      have hval : k (mix W s.mem n a) = k (s.mem a) := by
        by_cases haW : a ∈ W
        · rw [mix_mem haW]
        · rw [mix_nmem haW]
          have hHa := I.inv.hist_perm hc hal haW
          by_cases hg : G a
          · have hq := hG a hal hg
            rw [hHa] at hq
            rcases I.ins c p0 _ W hc with hgl | hAD
            · cases hgl
            · cases hAD with
              | rd h1 _ => exact h1 hg _ _ hq
          · rw [hN a hal hg, hHa]
      rw [hval]; exact hr
    · rcases I.ins c p0 _ W hc with hgl | hAD
      · cases hgl
      · cases hAD with
        | rd _ h2 => exact Or.inr (h2 _)
  | @rds p0 a k W hc =>
    refine ⟨H, I.locstep (inv_rds I.inv hc) hc rfl (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ => rfl)
      rfl rfl (fun n n' hG hN hcn hr => I.sim c p0 _ W hc n n' hG hN hcn (Run.rds _ hr)) ?_
      (fun x hx hg => I.np c p0 _ W hc x hx hg)⟩
    rcases I.ins c p0 _ W hc with hgl | hAD
    · cases hgl with
      | rds h => exact Or.inl (h _)
    · cases hAD with
      | rds _ h2 => exact Or.inr (h2 _)
  | @rdc p0 a K k W hc =>
    simp only [Allowed, hc] at hal
    obtain ⟨hko, hK⟩ := hal
    have hcl : ∀ n : A → V, (∀ x, (s.ko x = .gate ∨ s.ko x = .core c) →
        s.cls x (n x) = s.cls x (H x)) → s.cls a (mix W s.mem n a) = s.cls a (s.mem a) := by
      intro n hn
      by_cases haW : a ∈ W
      · rw [mix_mem haW]
      · rw [mix_nmem haW, hn a hko]
        rcases I.inv.clsinv a with h | ⟨e, q0, q, U, he, hx, hk⟩
        · exact h.symm
        · exfalso
          rcases hko with hg | hco
          · rcases hk with h | h <;> rw [hg] at h <;> cases h
          · rcases hk with h | h
            · rw [hco] at h
              obtain rfl : c = e := ClsOwner.core.inj h
              rw [hc] at he; cases he; exact haW hx
            · rw [hco] at h; cases h
    refine ⟨H, I.locstep (inv_rdc I.inv hc hko hK) hc rfl (fun _ _ _ h => h)
      (fun _ _ _ _ _ _ _ _ => rfl) rfl rfl
      (fun n n' hG hN hcn hr => I.sim c p0 _ W hc n n' hG hN hcn (Run.rdc _ (hK _ _ (hcl n hcn)) hr)) ?_
      (fun x hx hg => I.np c p0 _ W hc x hx hg)⟩
    rcases I.ins c p0 _ W hc with hgl | hAD
    · cases hgl with
      | rdc _ _ h => exact Or.inl (h _)
    · cases hAD with
      | rdc _ h2 => exact Or.inr (h2 _)
  | @start p0 k W hc =>
    refine ⟨H, I.locstep (inv_start I.inv hc) hc rfl (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ => rfl)
      rfl rfl (fun n n' hG hN hcn hr => I.sim c p0 _ W hc n n' hG hN hcn (Run.start hr)) ?_
      (fun x hx hg => I.np c p0 _ W hc x hx hg)⟩
    rcases I.ins c p0 _ W hc with hgl | hAD
    · exact Or.inr (hB p0 k W hc)
    · cases hAD with
      | start h => exact Or.inr h
  | @lock p0 l k W b hc hb =>
    refine ⟨H, I.locstep (inv_lock I.inv hc b hb) hc rfl (fun _ _ _ h => Or.imp (held_lock hb) id h)
      (fun _ _ _ _ _ _ _ _ => rfl) rfl rfl
      (fun n n' hG hN hcn hr => I.sim c p0 _ W hc n n'
        (fun x hx hg => hG x (Or.imp (held_lock hb) id hx) hg)
        (fun x hx hg => hN x (Or.imp (held_lock hb) id hx) hg) hcn (Run.lock b hr)) ?_
      (fun x hx hg => I.np c p0 _ W hc x hx hg)⟩
    rcases I.ins c p0 _ W hc with hgl | hAD
    · cases hgl with
      | lock h => exact Or.inl (h b)
    · cases hAD with
      | lock h => exact Or.inr (h b)
  | @wr p0 a v k W hc =>
    simp only [Allowed, hc] at hal
    obtain ⟨ha, hmv, hcls⟩ := hal
    have hsame : ∀ d, d ≠ c → ∀ x, (Held s.lk d (s.own s.mem x) ∨ s.own s.mem x = .gate) →
        s.own (Function.update s.mem a v) x = s.own s.mem x := by
      intro d hdc x h
      by_contra hne
      exact held_disj (Ne.symm hdc) (hmv x hne).1 h
    have hAD : ADIns G Q NP (.wr a v k) := by
      rcases I.ins c p0 _ W hc with hgl | hAD
      · cases hgl
      · exact hAD
    obtain ⟨hnpv, hk⟩ : (G a → NP v) ∧ ADIns G Q NP k := by
      cases hAD with
      | wr h1 h2 => exact ⟨h1, h2⟩
    refine ⟨H, I.locstep (inv_wr I.inv hc ha hmv hcls) hc rfl ?_ ?_ rfl rfl ?_ (Or.inr hk) ?_⟩
    · intro d hdc x h
      show Held s.lk d (s.own (Function.update s.mem a v) x) ∨
        s.own (Function.update s.mem a v) x = .gate
      rw [hsame d hdc x h]; exact h
    · intro d hdc q0 q U hd x hx
      have hxa : x ≠ a := by
        rintro rfl
        exact held_disj (Ne.symm hdc) ha (Or.inl ((I.inv.loc d q0 q U hd).held x hx))
      exact Function.update_of_ne hxa _ _
    · intro n n' hG hN hcn hr
      have hp : ∀ x, Perm s c x →
          Held s.lk c (s.own (Function.update s.mem a v) x) ∨
            s.own (Function.update s.mem a v) x = .gate := by
        intro x hx
        by_cases he : s.own (Function.update s.mem a v) x = s.own s.mem x
        · rw [he]; exact hx
        · exact Or.inl (hmv x he).2
      exact I.sim c p0 _ W hc n n' (fun x hx hg => hG x (hp x hx) hg) (fun x hx hg => hN x (hp x hx) hg)
        hcn (Run.wr (by rw [mix_upd]; exact hr))
    · intro x hx hg
      show NP (Function.update s.mem a v x)
      by_cases hxa : x = a
      · subst hxa; rw [Function.update_self]; exact hnpv hg
      · rw [Function.update_of_ne hxa]
        exact I.np c p0 _ W hc x ((Set.mem_insert_iff.mp hx).resolve_left hxa) hg
  | @leave p0 W hc =>
    have Ic := I.inv.loc c p0 _ W hc
    refine ⟨_, inv_leave I.inv hc, ?_, ?_, ?_⟩
    · intro d q0 q U hd
      rcases upd_loc hd with ⟨_, he⟩ | ⟨hdc, hd⟩
      · cases he
      · refine (I.sim d q0 q U hd).mono (fun x h => Or.imp (held_release hdc) id h)
          (fun x hp => mix_nmem (fun hxW => held_disj (Ne.symm hdc) (Ic.held x hxW) hp))
          (fun _ _ => rfl) rfl rfl (fun x hx => ?_)
        by_cases hxW : x ∈ W
        · rw [mix_mem hxW]
          rcases I.inv.clsinv x with h | ⟨e, q0', q', U', he, hxU, hk⟩
          · exact h
          · exfalso
            have hec : e = c := by
              by_contra hne
              exact held_disj hne ((I.inv.loc e q0' q' U' he).held x hxU) (Or.inl (Ic.held x hxW))
            subst hec
            rcases hx with h1 | h1 <;> rcases hk with h2 | h2 <;> rw [h1] at h2 <;>
              first | exact hdc (ClsOwner.core.inj h2) | exact hdc (ClsOwner.core.inj h2).symm | cases h2
        · rw [mix_nmem hxW]
    · intro d q0 q U hd
      rcases upd_loc hd with ⟨_, he⟩ | ⟨_, hd⟩
      · cases he
      · exact I.ins d q0 q U hd
    · intro d q0 q U hd x hx hg
      rcases upd_loc hd with ⟨_, he⟩ | ⟨_, hd⟩
      · cases he
      · exact I.np d q0 q U hd x hx hg
  | take p hc _ =>
    have hX : ¬ (Phase.ser p : Phase A V L).IsLoc := Phase.ser_not_loc p
    have hc' : ¬ (s.ph c).IsLoc := by rw [hc]; exact Phase.idle_not_loc
    exact ⟨H, I.frame (inv_take I.inv p hc) rfl rfl rfl rfl rfl
      (fun d q0 q U h => (upd_nonloc hX hc' d q0 q U).mp h)⟩
  | scan d _ _ hd => exact ⟨H, I.frame (inv_scan I.inv d hd) rfl rfl rfl rfl rfl (fun _ _ _ _ h => h)⟩
  | drain _ hg hall =>
    exact ⟨H, I.frame (inv_drain I.inv hg hall) rfl rfl rfl rfl rfl (fun _ _ _ _ h => h)⟩
  | serial keep own' cls' ko' _ hg _ hr =>
    have nl := I.inv.clo hg
    exact ⟨_, InvA.of_noLoc (inv_serial I.inv keep own' cls' ko' hg hr)
      (fun d hd => nl d (upd_isLoc Phase.idle_not_loc hd).2)⟩

/-- **`InvA` is kept by a `HwWr`** (the history taking the same write). -/
theorem InvA.hw {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvA G Q NP m0 s H) {a : A} {x : V}
    {l : L} (h : HwWr s a x l) : InvA G Q NP m0 (hwCfg s a x) (Function.update H a x) where
  inv := inv_hw I.inv h
  sim d p0 p W hd := by
    have L0 := I.inv.loc d p0 p W hd
    refine (I.sim d p0 p W hd).mono (s' := hwCfg s a x) (fun y hy => ?_) (fun y hy => ?_)
      (fun y hy => ?_) rfl rfl (fun y hy => ?_)
    · show Held s.lk d (s.own (Function.update s.mem a x) y) ∨ s.own (Function.update s.mem a x) y = .gate
      rw [h.keep]; exact hy
    · exact Function.update_of_ne (h.ne_of_perm hy) _ _
    · exact Function.update_of_ne (h.ne_of_held (L0.held y hy)) _ _
    · have hya : y ≠ a := by
        rintro rfl; rw [h.ko] at hy; rcases hy with hy | hy <;> cases hy
      rw [Function.update_of_ne hya]
  ins d p0 p W hd := I.ins d p0 p W hd
  np d p0 p W hd y hy hg := by
    show NP (Function.update s.mem a x y)
    rw [Function.update_of_ne (h.ne_of_held ((I.inv.loc d p0 p W hd).held y hy))]
    exact I.np d p0 p W hd y hy hg

/-- A word an `ADWr` writes is in no in-progress path's write set. -/
theorem InvA.ad_nmem {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvA G Q NP m0 s H) {x : A} {y : V}
    (h : ADWr G Q NP s x y) {d : C} {p0 p : Prog A V L} {W : Set A} (hd : s.ph d = .loc p0 p W) : x ∉ W :=
  fun hx => h.np (I.np d p0 p W hd x hx h.g)

/-- **`InvA` is kept by an `ADWr`**, the history taking the same write (`Q` an equivalence). -/
theorem InvA.ad (hQ : Equivalence Q) {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvA G Q NP m0 s H)
    {x : A} {y : V} (h : ADWr G Q NP s x y) :
    InvA G Q NP m0 (hwCfg s x y) (Function.update H x y) := by
  have hHx : H x = s.mem x :=
    (I.inv.agree x (fun d q0 q U hd hx => I.ad_nmem h hd hx)).symm
  have hperm : ∀ d z, Perm (hwCfg s x y) d z ↔ Perm s d z := by
    intro d z
    show (Held s.lk d (s.own (Function.update s.mem x y) z) ∨ s.own (Function.update s.mem x y) z = .gate) ↔ _
    rw [h.keep]; rfl
  have hmix : ∀ (W : Set A) (n : A → V), x ∉ W → mix W (Function.update s.mem x y) n = mix W s.mem n := by
    intro W n hxW
    funext z
    by_cases hz : z ∈ W
    · rw [mix_mem hz, mix_mem hz, Function.update_of_ne (fun e => hxW (by rw [← e]; exact hz))]
    · rw [mix_nmem hz, mix_nmem hz]
  have hcx : ∀ d, ¬ (s.ko x = .gate ∨ s.ko x = .core d) := by
    intro d hx; rw [h.ko] at hx; rcases hx with hx | hx <;> cases hx
  -- the perturbed-history simulation, from `H` to `H[x := y]`
  have key : ∀ d p0 p W, s.ph d = .loc p0 p W → ∀ n n' : A → V,
      (∀ z, Perm s d z → G z → Q (n z) (Function.update H x y z)) →
      (∀ z, Perm s d z → ¬ G z → n z = Function.update H x y z) →
      (∀ z, (s.ko z = .gate ∨ s.ko z = .core d) → s.cls z (n z) = s.cls z (Function.update H x y z)) →
      Run p (mix W (Function.update s.mem x y) n) n' → Run p0 n n' := by
    intro d p0 p W hd n n' hG hN hcn hr
    refine I.sim d p0 p W hd n n' (fun z hz hg => ?_) (fun z hz hg => ?_) (fun z hz => ?_)
      (by rw [← hmix W n (I.ad_nmem h hd)]; exact hr)
    · have h1 := hG z hz hg
      by_cases hzx : z = x
      · subst hzx
        rw [Function.update_self] at h1
        rw [hHx]; exact hQ.trans h1 (hQ.symm h.q)
      · rw [Function.update_of_ne hzx] at h1; exact h1
    · have hzx : z ≠ x := fun e => hg (e ▸ h.g)
      rw [hN z hz hg, Function.update_of_ne hzx]
    · have hzx : z ≠ x := fun e => hcx d (e ▸ hz)
      rw [hcn z hz, Function.update_of_ne hzx]
  refine ⟨⟨RunAll.snoc I.inv.hist (.wr (.done _)), I.inv.clo, I.inv.drn, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro z hz
    show Function.update s.mem x y z = Function.update H x y z
    by_cases hzx : z = x
    · subst hzx; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hzx, Function.update_of_ne hzx]; exact I.inv.agree z hz
  · intro d p0 p W hd
    have L0 := I.inv.loc d p0 p W hd
    refine ⟨fun z hz => ?_, fun n n' hn hcn hr => ?_⟩
    · show Held s.lk d (s.own (Function.update s.mem x y) z); rw [h.keep]; exact L0.held z hz
    · exact key d p0 p W hd n n' (fun z hz _ => by rw [hn z ((hperm d z).mpr hz)]; exact hQ.refl _)
        (fun z hz _ => hn z ((hperm d z).mpr hz)) hcn hr
  · intro z
    show s.cls z (Function.update s.mem x y z) = s.cls z (Function.update H x y z) ∨
      ∃ e p0 p W, s.ph e = .loc p0 p W ∧ z ∈ W ∧ (s.ko z = .core e ∨ s.ko z = .free)
    by_cases hzx : z = x
    · subst hzx; left; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hzx, Function.update_of_ne hzx]; exact I.inv.clsinv z
  · intro d p0 p W hd n n' hG hN hcn hr
    exact key d p0 p W hd n n' (fun z hz hg => hG z ((hperm d z).mpr hz) hg)
      (fun z hz hg => hN z ((hperm d z).mpr hz) hg) hcn hr
  · intro d p0 p W hd; exact I.ins d p0 p W hd
  · intro d p0 p W hd z hz hg
    show NP (Function.update s.mem x y z)
    rw [Function.update_of_ne (fun e => I.ad_nmem h hd (by rw [← e]; exact hz))]
    exact I.np d p0 p W hd z hz hg

end inv

/-! ## `Safe` across an environment write the reader is insensitive to -/

section safe
variable {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop}
variable {own : (A → V) → A → Owner C L} {cls : A → V → V} {ko : A → ClsOwner C} {d : C} {hs : L → Prop}

/-- **The memories other cores reach after the write are those reached before, with the write on top**
(the written word is one the core may read, which a `Foreign` write neither writes nor re-owns). -/
theorem freach_ad {x : A} {y : V} (hkeep : ∀ m, own (Function.update m x y) = own m) {ν μ : A → V}
    (hR : FReach own cls ko d hs (Function.update ν x y) μ) (hpo : PO d hs (own ν x)) :
    ∃ ν', FReach own cls ko d hs ν ν' ∧ μ = Function.update ν' x y ∧ ν' x = ν x ∧ PO d hs (own ν' x) := by
  generalize hμ0 : Function.update ν x y = μ0 at hR
  induction hR generalizing ν with
  | refl _ => exact ⟨ν, .refl _, hμ0.symm, rfl, hpo⟩
  | @step μ1 μ2 b v hF _ ih =>
    subst hμ0
    have hbx : b ≠ x := by
      rintro rfl
      exact hF.1 (by rw [hkeep]; exact hpo)
    have hcomm : Function.update (Function.update ν x y) b v = Function.update (Function.update ν b v) x y :=
      Function.update_comm (Ne.symm hbx) y v ν
    have hF' : Foreign own cls ko d hs ν b v := by
      refine ⟨by have h1 := hF.1; rw [hkeep] at h1; exact h1, fun z hz => ?_, ?_⟩
      · have h2 := hF.2.1 z (by rw [hcomm, hkeep, hkeep]; exact hz)
        rw [hcomm, hkeep, hkeep] at h2; exact h2
      · have h3 := hF.2.2
        rw [Function.update_of_ne hbx] at h3; exact h3
    have hpo1 : PO d hs (own (Function.update ν b v) x) := by
      by_cases he : own (Function.update ν b v) x = own ν x
      · rw [he]; exact hpo
      · exact absurd hpo (hF'.2.1 x he).1
    obtain ⟨ν', hR', heq, hx, hpo'⟩ := ih hpo1 hcomm.symm
    refine ⟨ν', .step hF' hR', heq, ?_, hpo'⟩
    rw [hx, Function.update_of_ne (Ne.symm hbx)]

/-- **`Safe` transfers across the write** for an insensitive body that may read the word. -/
theorem safe_ad (hQs : ∀ u w, Q u w → Q w u) {x : A} {y : V} (hGx : G x)
    (hkeep : ∀ m, own (Function.update m x y) = own m) (hko : ko x = .free) {ν : A → V} {q : Prog A V L}
    (hS : Safe own cls ko d hs ν q) :
    ADIns G Q NP q → PO d hs (own ν x) → Q (ν x) y → Safe own cls ko d hs (Function.update ν x y) q := by
  induction hS with
  | done => intro _ _ _; exact .done
  | @rd μ a k h1 _ ih =>
    intro hA hpo hq
    cases hA with
    | rd hA1 hA2 =>
      refine .rd (fun μ'' hR => ?_) (fun μ'' hR => ?_)
      · obtain ⟨ν', hR', rfl, _, _⟩ := freach_ad hkeep hR hpo
        rw [hkeep]; exact h1 ν' hR'
      · obtain ⟨ν', hR', rfl, hx, hpo'⟩ := freach_ad hkeep hR hpo
        have e : k (Function.update ν' x y a) = k (ν' a) := by
          by_cases hax : a = x
          · subst hax; rw [Function.update_self]
            exact hA1 hGx _ _ (hQs _ _ (by rw [hx]; exact hq))
          · rw [Function.update_of_ne hax]
        rw [e]; exact ih ν' hR' (hA2 _) hpo' (by rw [hx]; exact hq)
  | @rds μ a k _ ih =>
    intro hA hpo hq
    cases hA with
    | rds hA1 hA2 =>
      refine .rds (fun μ'' hR => ?_)
      obtain ⟨ν', hR', rfl, hx, hpo'⟩ := freach_ad hkeep hR hpo
      have e : k (Function.update ν' x y a) = k (ν' a) := by
        by_cases hax : a = x
        · subst hax; rw [Function.update_self]
          exact hA1 hGx _ _ (hQs _ _ (by rw [hx]; exact hq))
        · rw [Function.update_of_ne hax]
      rw [e]; exact ih ν' hR' (hA2 _) hpo' (by rw [hx]; exact hq)
  | @rdc μ a K k hko' hK _ ih =>
    intro hA hpo hq
    cases hA with
    | rdc hA1 hA2 =>
      refine .rdc hko' hK (fun μ'' hR => ?_)
      obtain ⟨ν', hR', rfl, hx, hpo'⟩ := freach_ad hkeep hR hpo
      have e : k (Function.update ν' x y a) = k (ν' a) := by
        by_cases hax : a = x
        · subst hax; rw [Function.update_self]
          exact hA1 hGx _ _ (hQs _ _ (by rw [hx]; exact hq))
        · rw [Function.update_of_ne hax]
      rw [e]; exact ih ν' hR' (hA2 _) hpo' (by rw [hx]; exact hq)
  | @wr μ a v k h1 h2 h3 h4 ih =>
    intro hA hpo hq
    cases hA with
    | wr _ hAk =>
      have hown : ∀ ν' : A → V,
          own (Function.update (Function.update ν' x y) a v) = own (Function.update ν' a v) := by
        intro ν'
        by_cases hax : a = x
        · subst hax; rw [Function.update_idem]
        · rw [Function.update_comm (Ne.symm hax) y v ν', hkeep]
      refine .wr (fun μ'' hR => ?_) (fun μ'' hR => ?_) (fun μ'' hR => ?_) (fun μ'' hR => ?_)
      · obtain ⟨ν', hR', rfl, _, _⟩ := freach_ad hkeep hR hpo
        rw [hkeep]; exact h1 ν' hR'
      · obtain ⟨ν', hR', rfl, _, _⟩ := freach_ad hkeep hR hpo
        intro z hz
        rw [hown, hkeep] at hz ⊢
        exact h2 ν' hR' z hz
      · obtain ⟨ν', hR', rfl, _, _⟩ := freach_ad hkeep hR hpo
        by_cases hax : a = x
        · subst hax; exact Or.inr (Or.inr hko)
        · rw [Function.update_of_ne hax]; exact h3 ν' hR'
      · obtain ⟨ν', hR', rfl, hx, hpo'⟩ := freach_ad hkeep hR hpo
        by_cases hax : a = x
        · subst hax; rw [Function.update_idem]; exact h4 ν' hR'
        · rw [Function.update_comm (Ne.symm hax) y v ν']
          have hpo1 : PO d hs (own (Function.update ν' a v) x) := by
            by_cases he : own (Function.update ν' a v) x = own ν' x
            · rw [he]; exact hpo'
            · exact Or.inl (h2 ν' hR' x he).2
          refine ih ν' hR' hAk hpo1 ?_
          rw [Function.update_of_ne (Ne.symm hax), hx]; exact hq

end safe

/-- **`SInv` is kept by an `ADWr`** to whose readers it is insensitive. -/
theorem sinv_ad {G : A → Prop} {Q : V → V → Prop} {NP : V → Prop} (hQs : ∀ u w, Q u w → Q w u)
    {s : Cfg A V C L} (I : SInv s)
    (hins : ∀ d p0 p W, s.ph d = .loc p0 p W → Glue s.cls s.ko d p ∨ ADIns G Q NP p)
    {x : A} {y : V} (h : ADWr G Q NP s x y) : SInv (hwCfg s x y) := by
  intro d p0 q W hd
  rcases I d p0 q W hd with hg | hS
  · exact Or.inl hg
  · by_cases hpo : PO d (fun l => s.lk l = some d) (s.own s.mem x)
    · rcases hins d p0 q W hd with hg | hA
      · exact Or.inl hg
      · exact Or.inr (safe_ad hQs h.g h.keep h.ko hS hA hpo h.q)
    · right
      have hF : Foreign s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem x y := by
        refine ⟨hpo, fun z hz => absurd (by rw [h.keep]) hz, ?_⟩
        right; rw [h.ko]; exact ⟨(fun e => by cases e), (fun e => by cases e)⟩
      exact Safe.foreign hS hF

/-! ## Executions -/

/-- **Executions with environment writes the readers are insensitive to** (module docstring): the word set `G`
is an index that may change under a closed gate. -/
inductive ARun (Q : V → V → Prop) (NP : V → Prop) (s0 : Cfg A V C L) : Cfg A V C L → (A → Prop) → Prop
  | refl (G : A → Prop) : ARun Q NP s0 s0 G
  | step {s s' : Cfg A V C L} {c : C} {G : A → Prop} :
      ARun Q NP s0 s G → Step s c s' → SafeStep s c s' →
      (∀ p0 k W, s.ph c = .loc p0 (.start k) W → ADIns G Q NP k) → ARun Q NP s0 s' G
  | hw {s : Cfg A V C L} {a : A} {x : V} {l : L} {G : A → Prop} :
      ARun Q NP s0 s G → HwWr s a x l → ARun Q NP s0 (hwCfg s a x) G
  | ad {s : Cfg A V C L} {x : A} {y : V} {G : A → Prop} :
      ARun Q NP s0 s G → ADWr G Q NP s x y → ARun Q NP s0 (hwCfg s x y) G
  | regate {s : Cfg A V C L} {G : A → Prop} (G' : A → Prop) :
      ARun Q NP s0 s G → s.gate = .closed → ARun Q NP s0 s G'

theorem aRun_inv {Q : V → V → Prop} {NP : V → Prop} (hQ : Equivalence Q) {s0 s : Cfg A V C L}
    {G : A → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (h : ARun Q NP s0 s G) :
    (∃ H, InvA G Q NP s0.mem s H) ∧ SInv s ∧ ArmInv s := by
  induction h with
  | refl G => exact ⟨⟨_, InvA.of_noLoc (inv_init h0) h0.2⟩,
      fun d p0 q W hd => absurd (by rw [hd]; trivial) (h0.2 d), hA0⟩
  | @step s s' c G _ hst hok hB ih =>
    obtain ⟨⟨H, I⟩, hS, hA⟩ := ih
    have hal := allowed_of_sinv hS c
    exact ⟨I.step hA hal hst hB, sinv_stepX I.inv.clo hA hok.start hS hal hst, armInv_step hA hst hok⟩
  | hw _ hh ih =>
    obtain ⟨⟨H, I⟩, hS, hA⟩ := ih
    exact ⟨⟨_, I.hw hh⟩, sinv_hw hS hh, hA⟩
  | ad _ hh ih =>
    obtain ⟨⟨H, I⟩, hS, hA⟩ := ih
    exact ⟨⟨_, I.ad hQ hh⟩, sinv_ad (fun u w h => hQ.symm h) hS I.ins hh, hA⟩
  | regate G' _ hg ih =>
    obtain ⟨⟨H, I⟩, hS, hA⟩ := ih
    exact ⟨⟨H, I.regate G' hg⟩, hS, hA⟩

/-- **Every `ARun` is a serial one** (module docstring): where it reaches a state with no local path in
progress, memory is the serial run of the completed entries, the environment writes logged as entries. -/
theorem serializable_safeA {Q : V → V → Prop} {NP : V → Prop} (hQ : Equivalence Q) {s0 s : Cfg A V C L}
    {G : A → Prop} (h0 : Init s0) (hA0 : ArmInv s0) (h : ARun Q NP s0 s G) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨⟨H, I⟩, -, -⟩ := aRun_inv hQ h0 hA0 h
  have : s.mem = H := funext fun x =>
    I.inv.agree x (fun d q0 q U hd => absurd (by rw [hd]; trivial) (hq d))
  rw [this]; exact I.inv.hist

/-- **Every `XSafeRun` is an `ARun`** (no environment write of the new kind, the empty word set). -/
theorem aRun_of_xsafeRun {Q : V → V → Prop} {NP : V → Prop} {s0 s : Cfg A V C L} (h : XSafeRun s0 s) :
    ARun Q NP s0 s (fun _ => False) := by
  induction h with
  | refl => exact .refl _
  | step _ hst hok ih => exact .step ih hst hok (fun _ k _ _ => adIns_bot Q NP k)
  | hw _ hh ih => exact .hw ih hh

end

end Fl4Proofs.P2.Serial

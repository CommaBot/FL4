/-
P2: **end to end, from the per-path obligations to serializability**
(`SerialSafe`'s plan, done).

`Serial.serializable_safe` needs `BodyOK` [W]: a body is `Safe` when it starts.
Here a body is the translation `tr` of a local path's trait-call tree, and
`BodyOK` follows from the path's obligations (`LocalPath`), by way of
`SafeCert.safe_of_runs`.

## The translation `tr`

Arch calls are made on the actual instance, from the Arch state at entry (their
results do not depend on memory; the Arch state is per core). The store's
constants (`ks_base`, `cur_cpu`, `frame_masks`) are the entry state's. A read:
of a kernel word in the entry state's `ReadSet`, or that the body has written,
is `rd`; else of a kernel word whose class the gate or this core owns, `rdc`
(class read); else (user words included) `rds`, any value. A write of a user
word is not tracked (dropped); of a kernel word, `wr`. `zero` / `clear_free`
are not translated: `ReadOnce` excludes them along the path's runs (all the
runs an interleaving can follow).

## User memory

User threads change user memory at any time, on other cores as well: a read of
a user word is `rds`, any value in `Serial`'s sequential meaning, and nothing
is assumed about who owns user words. For a sequential run of the body to
explain an arbitrary value at each such read, a run must read each user word at
most once and never after writing it: part of `ReadOnce` [W], a property of
each path. The local paths have it: `handle_syscall_local`'s trap branch only
writes user words (the handler's buffer, each once), its ReplyRecv branch only
reads them (the replier's buffer, each once), and the others touch none. It is
stated along the path's runs, not on every branch of its tree: branches no run
takes may use an address read from memory that lies in user memory.

## Certificates

For every memory `ν` the racy reads may return (`SafeCert.Adm`), the words the
translated body reads on `ν` (`reads`, finitely many) are written into the entry
state, the user ones first (`PathSide.user_free` keeps `Pre` and the sets), then
the kernel ones (an `Alt` state). If the run after the user ones accepts, `acc`
and `move` there give the certificate, checked at the real memory; otherwise
`dec_alt` at the second state does, checked at that state's memory.

## Premises

Of `serializable_paths` (generic ownership map):
* `Init`, `ArmGlue` [W] as in `serializable_safe`;
* per path, inside `LocalPath`: `IsProg` [P], `PathObl` [W], `PathSide` [W],
  `ReadOnce` [W] (it subsumes `DecOnce` and `NoZero`), totality (`<fn>.p0`,
  from a total Arch instance), `MasksWr` [P];
* `StartAt` [P] for every started body (below);
* `Deciders`, `MoveLocal`, `OwnDep`: hypotheses on the ownership map,
  discharged for `OwnMap.own`.

Of `serializable_e2e`: the same with `own := OwnMap.own K`; `RegionOK` [J] and
`UserOK` [J] for the layouts `K` of the execution.
-/
import Fl4Proofs.P2.SafeCert
import Fl4Proofs.P2.PathBridge
import Fl4Proofs.P2.OwnMap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2E
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner ClsOwner Prog HeldV PO MoveV Safe Deciders MoveLocal AltRun Adm
  Diff RInv WrOK)

noncomputable section
open Classical

abbrev SP := Prog U64 U64 U64

/-! ## The translation -/

section tr
variable (R User : U64 → Prop) (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (c : U64)

/-- A read that other cores' writes may race with: not of a kernel word the
path may read (`R`) or has written (`Wd`). -/
def Racy (Wd : Set U64) (q : U64) : Prop := ¬ (¬ User q ∧ (R q ∨ q ∈ Wd))

/-- The translated read of `q`. -/
def rdN (Wd : Set U64) (q : U64) (k : U64 → SP) : SP :=
  if ¬ Racy R User Wd q then .rd q k
  else if ¬ User q ∧ (ko q = .gate ∨ ko q = .core c) then
    .rdc q (fun u w => cls q u = cls q w) k
  else .rds q k

variable (kb : U64) (mk : U64 × U64) {A X : Type} (ar : machine.Arch A)

/-- **The translation** of a trait-call tree (module docstring), `Wd` the kernel
words written so far, `a` the Arch state. -/
def tr : SProg X → Set U64 → A → SP
  | .ret _, _, _ => .done
  | .err _, _, _ => .done
  | .rd q k, Wd, a => rdN R User cls ko c Wd q fun v => tr (k v) Wd a
  | .rdp q k, Wd, a => rdN R User cls ko c Wd q fun v =>
      rdN R User cls ko c Wd (core.num.U64.wrapping_add q 8#u64) fun w => tr (k (v, w)) Wd a
  | .wr q v k, Wd, a =>
      if User q then tr k Wd a else .wr q v (tr k (insert q Wd) a)
  | .zero _ _ _, _, _ => .done
  | .clr _ _ _, _, _ => .done
  | .ksb k, Wd, a => tr (k kb) Wd a
  | .cpu k, Wd, a => tr (k c) Wd a
  | .masks k, Wd, a => tr (k mk) Wd a
  | .arch op k, Wd, a =>
      if h : ∃ r, callArch ar op a = ok r then tr (k h.choose.1) Wd h.choose.2 else .done

end tr

/-- The words the run of `q` on `ν` reads. -/
def reads : SP → (U64 → U64) → List U64
  | .done, _ => []
  | .rd q k, ν => q :: reads (k (ν q)) ν
  | .rds q k, ν => q :: reads (k (ν q)) ν
  | .rdc q _ k, ν => q :: reads (k (ν q)) ν
  | .wr q v k, ν => reads k (Function.update ν q v)
  | .lock _ _, _ => []
  | .start _, _ => []

theorem reads_rdN {R User : U64 → Prop} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
    {c : U64} {Wd : Set U64} {q : U64} {k : U64 → SP} {ν : U64 → U64} :
    reads (rdN R User cls ko c Wd q k) ν = q :: reads (k (ν q)) ν := by
  unfold rdN; split_ifs <;> rfl

/-! ## Read-once along a run -/

/-- `T` (words racily read, user words written) after a read of `q`. -/
def tch (R User : U64 → Prop) (Wd : Set U64) (q : U64) (T : Set U64) : Set U64 :=
  if Racy R User Wd q then insert q T else T

theorem tch_sub {R User : U64 → Prop} {Wd : Set U64} {q : U64} {T : Set U64} :
    T ⊆ tch R User Wd q T := by
  unfold tch; split_ifs
  · exact Set.subset_insert _ _
  · exact subset_rfl

section once
variable {S A X : Type}

/-- **Read once**: along the run of `p` on `st` from `(s, a)`, each racy read
(`Racy`) is of a word not in `T` (the words racily read and the user words
written before), and there is no `zero` / `clear_free`. -/
def Once (st : machine.Store S) (ar : machine.Arch A) (R User : U64 → Prop) :
    Set U64 → Set U64 → SProg X → S → A → Prop
  | _, _, .ret _, _, _ => True
  | _, _, .err _, _, _ => True
  | Wd, T, .rd q k, s, a => (Racy R User Wd q → q ∉ T) ∧
      ∀ v, st.read s q = ok v → Once st ar R User Wd (tch R User Wd q T) (k v) s a
  | Wd, T, .rdp q k, s, a => (Racy R User Wd q → q ∉ T) ∧
      (Racy R User Wd (core.num.U64.wrapping_add q 8#u64) →
        core.num.U64.wrapping_add q 8#u64 ∉ tch R User Wd q T) ∧
      ∀ v, st.read_pair s q = ok v → Once st ar R User Wd
        (tch R User Wd (core.num.U64.wrapping_add q 8#u64) (tch R User Wd q T)) (k v) s a
  | Wd, T, .wr q v k, s, a => ∀ s', st.write s q v = ok s' →
      Once st ar R User (if User q then Wd else insert q Wd) (if User q then insert q T else T) k s' a
  | _, _, .zero _ _ _, _, _ => False
  | _, _, .clr _ _ _, _, _ => False
  | Wd, T, .ksb k, s, a => ∀ v, st.ks_base s = ok v → Once st ar R User Wd T (k v) s a
  | Wd, T, .cpu k, s, a => ∀ v, st.cur_cpu s = ok v → Once st ar R User Wd T (k v) s a
  | Wd, T, .masks k, s, a => ∀ v, st.frame_masks s = ok v → Once st ar R User Wd T (k v) s a
  | Wd, T, .arch op k, s, a => ∀ v a', callArch ar op a = ok (v, a') →
      Once st ar R User Wd T (k v) s a'

/-- **`ReadOnce`** [W] (per path): from an entry state and every alternative,
the run reads each racy word (a kernel word outside `ReadSet` it has not
written, or a user word) at most once, no user word after writing it, and
clears no range. For declined runs this is what makes `dec_alt`'s per-state
alternatives cover `Serial`'s per-read ones; for user words, module docstring.
`NoZero` gives its last part. **About the actual tree**: a Store read returns
no state, so no store instance can count reads, and `IsProg` (an extensional
equality) does not distinguish a body that reads a word twice from one that
keeps the first value. `p` must be the body's own tree of trait calls, as
`IsProg` [P] intends: to be checked against the extracted text
(`P2/ReadGap.lean`: a body with both kinds of tree). -/
def ReadOnce (st : machine.Store S) [LawfulStore st] (ar : machine.Arch A) (p : SProg X)
    (cls : U64 → U64 → U64) (ko : U64 → ClsOwner U64) (User : U64 → Prop) (Pre : S → Prop)
    (RS : S → U64 → Prop) : Prop :=
  ∀ s s' a r, Pre s → Alt st (RS s) cls ko User s s' → interp st ar p s' a = ok r →
    Once st ar (RS s) User ∅ ∅ p s' a

end once

/-! ## Facts about `Within`, owners, writes -/

section facts
variable {S A X : Type} {st : machine.Store S} {ar : machine.Arch A}

theorem within_and {R W R' W' : U64 → Prop} (p : SProg X) :
    ∀ (s : S) (a : A), Within st ar R W p s a → Within st ar R' W' p s a →
      Within st ar (fun b => R b ∧ R' b) (fun b => W b ∧ W' b) p s a := by
  induction p with
  | ret x => intros; simp only [Within]
  | err e => intros; simp only [Within]
  | rd q k ih =>
    intro s a h h'; simp only [Within] at h h' ⊢
    exact ⟨⟨h.1, h'.1⟩, fun v hv => ih v s a (h.2 v hv) (h'.2 v hv)⟩
  | rdp q k ih =>
    intro s a h h'; simp only [Within] at h h' ⊢
    exact ⟨⟨h.1, h'.1⟩, ⟨h.2.1, h'.2.1⟩, fun v hv => ih v s a (h.2.2 v hv) (h'.2.2 v hv)⟩
  | wr q v k ih =>
    intro s a h h'; simp only [Within] at h h' ⊢
    exact ⟨⟨h.1, h'.1⟩, fun s' hs => ih s' a (h.2 s' hs) (h'.2 s' hs)⟩
  | zero q n k ih =>
    intro s a h h'; simp only [Within] at h h' ⊢
    exact ⟨fun b hb => ⟨h.1 b hb, h'.1 b hb⟩, fun s' hs => ih s' a (h.2 s' hs) (h'.2 s' hs)⟩
  | clr q n k ih =>
    intro s a h h'; simp only [Within] at h h' ⊢
    exact ⟨fun b hb => ⟨h.1 b hb, h'.1 b hb⟩, fun s' hs => ih s' a (h.2 s' hs) (h'.2 s' hs)⟩
  | ksb k ih =>
    intro s a h h'; simp only [Within] at h h' ⊢
    exact fun v hv => ih v s a (h v hv) (h' v hv)
  | cpu k ih =>
    intro s a h h'; simp only [Within] at h h' ⊢
    exact fun v hv => ih v s a (h v hv) (h' v hv)
  | masks k ih =>
    intro s a h h'; simp only [Within] at h h' ⊢
    exact fun v hv => ih v s a (h v hv) (h' v hv)
  | arch op k ih =>
    intro s a h h'; simp only [Within] at h h' ⊢
    exact fun v a' hv => ih v s a' (h v a' hv) (h' v a' hv)

end facts

theorem heldBy_iff {c : U64} {hs : U64 → Prop} {o : Owner U64 U64} :
    HeldBy c hs o ↔ HeldV c hs o := by cases o <;> exact Iff.rfl

/-- **`OwnDep`** (a hypothesis on the ownership map, discharged for `OwnMap.own`
from the layout: `ownDep`): owners depend on aligned kernel words only. -/
def OwnDep (own : (U64 → U64) → U64 → Owner U64 U64) (User : U64 → Prop) : Prop :=
  ∀ m m' : U64 → U64, (∀ x, Aligned x → ¬ User x → m x = m' x) → own m = own m'

/-- **`MasksWr`** [P]: a word write does not change the store's frame-address
masks. True of every store the kernel runs (the masks are boot-time constants,
not memory) and of `PlainStore` (where they are constant); `LawfulStore` does
not state it. -/
def MasksWr {S : Type} (st : machine.Store S) [L : LawfulStore st] : Prop :=
  ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s

theorem masks_ok {S : Type} (st : machine.Store S) [L : LawfulStore st] (s : S) :
    ∃ v, st.frame_masks s = ok v := by
  have h := L.frame_masks_total s
  revert h
  cases st.frame_masks s <;> simp [WP.spec_vis, WP.spec_div, WP.spec_ok]

/-- The entry state's masks. -/
def masksOf {S : Type} (st : machine.Store S) [LawfulStore st] (s : S) : U64 × U64 :=
  (masks_ok st s).choose

theorem masksOf_eq {S : Type} (st : machine.Store S) [LawfulStore st] (s : S) :
    st.frame_masks s = ok (masksOf st s) := (masks_ok st s).choose_spec

/-! ## The run on the store and the run on `ν` -/

section sim
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {c : U64} {hs : U64 → Prop} {R User Hp : U64 → Prop}

/-- Words the translated body reads with `rd`. -/
def RpOf (R User Hp : U64 → Prop) (x : U64) : Prop := (¬ User x ∧ R x) ∨ Hp x

theorem altRun_rdN {P : Set U64} {Wd T : Set U64} {q : U64} {k : U64 → SP} {ν κ : U64 → U64}
    (hWd : ∀ x ∈ Wd, Hp x) (hPT : P ⊆ T) (ho : Racy R User Wd q → q ∉ T)
    (hk : ∀ P', P' ⊆ tch R User Wd q T →
      AltRun own cls ko c hs (RpOf R User Hp) Hp P' (k (ν q)) ν κ) :
    AltRun own cls ko c hs (RpOf R User Hp) Hp P (rdN R User cls ko c Wd q k) ν κ := by
  by_cases hr : Racy R User Wd q
  · have hq : q ∉ P := fun h => ho hr (hPT h)
    have hsub : insert q P ⊆ tch R User Wd q T := by
      unfold tch; rw [if_pos hr]; exact Set.insert_subset_insert hPT
    unfold rdN
    rw [if_neg (not_not.mpr hr)]
    split_ifs with hko
    · simp only [AltRun]; exact ⟨hq, hko.2, fun u w h => h, hk _ hsub⟩
    · simp only [AltRun]; exact ⟨hq, hk _ hsub⟩
  · unfold rdN
    rw [if_pos hr]
    simp only [AltRun]
    refine ⟨?_, hk P (hPT.trans tch_sub)⟩
    obtain ⟨hu, h | h⟩ := not_not.mp hr
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr (hWd q h)

variable {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}

theorem wrOK_of_stepOK (hO : OwnDep own User) {s s' : S} {κ : U64 → U64} {q v : U64}
    (hq : Aligned q) (hu : ¬ User q) (hK : ∀ x, Aligned x → ¬ User x → κ x = L.mem s x)
    (hs' : s' = L.wr s q v)
    (h : StepOK own cls ko User c hs (L.mem s) (L.mem s')) :
    WrOK own cls ko c hs κ q v := by
  subst hs'
  have e1 : own κ = own (L.mem s) := hO _ _ hK
  have e2 : own (Function.update κ q v) = own (L.mem (L.wr s q v)) := by
    refine hO _ _ fun x hx hxu => ?_
    rw [L.mem_wr s q v x hq hx]
    by_cases hxq : q = x
    · subst hxq; rw [if_pos rfl, Function.update_self]
    · rw [if_neg hxq, Function.update_of_ne (Ne.symm hxq)]; exact hK x hx hxu
  have em : L.mem (L.wr s q v) q = v := by rw [L.mem_wr s q v q hq hq, if_pos rfl]
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [e1, e2] at hx ⊢
    have := h.1 x hx
    exact ⟨heldBy_iff.mp this.1, heldBy_iff.mp this.2⟩
  · by_cases hv : L.mem (L.wr s q v) q = L.mem s q
    · left; rw [hK q hq hu, ← hv, em]
    · have := h.2 q hv hu
      rw [em] at this; rw [hK q hq hu]; exact this

/-- **The run on the store follows the translated body's run on `ν`**, and
certifies it with check memory `κ`. -/
theorem sim (hO : OwnDep own User) (hmk : MasksWr st) {kb : U64} {mk : U64 × U64}
    {Rr Wr : U64 → Prop} (hWr : ∀ x, Wr x → Aligned x ∧ (¬ User x → Hp x)) (p : SProg X) :
    ∀ (s : S) (a : A) (Wd T P : Set U64) (ν κ : U64 → U64),
      Within st ar (fun b => Aligned b ∧ Rr b) Wr p s a →
      WithinM st ar (fun x y => StepOK own cls ko User c hs (L.mem x) (L.mem y)) p s a →
      Once st ar R User Wd T p s a →
      (∀ x ∈ Wd, Hp x) → P ⊆ T → st.frame_masks s = ok mk → L.ksb s = kb → L.cpu s = c →
      (∀ x, Aligned x → ¬ User x → κ x = L.mem s x) →
      (∀ x ∈ reads (tr R User cls ko c kb mk ar p Wd a) ν, Aligned x → Rr x →
        (¬ User x ∨ x ∉ T) → L.mem s x = ν x) →
      AltRun own cls ko c hs (RpOf R User Hp) Hp P (tr R User cls ko c kb mk ar p Wd a) ν κ := by
  induction p with
  | ret x => intros; simp only [tr, AltRun]
  | err e => intros; simp only [tr, AltRun]
  | zero q n k ih => intros; simp only [tr, AltRun]
  | clr q n k ih => intros; simp only [tr, AltRun]
  | rd q k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    rw [reads_rdN] at hν
    obtain ⟨⟨hal, hr⟩, hW⟩ := hW
    obtain ⟨ho, hN⟩ := hN
    have hu : ¬ User q ∨ q ∉ T := by
      by_cases hu : User q
      · exact Or.inr (ho fun h => h.1 hu)
      · exact Or.inl hu
    have e : L.mem s q = ν q := hν q (List.mem_cons_self ..) hal hr hu
    have hrd : st.read s q = ok (ν q) := by rw [← e]; exact L.read_eq s q
    refine altRun_rdN hWd hPT ho fun P' hP' => ?_
    refine ih (ν q) s a Wd _ P' ν κ (hW _ hrd) (hM _ hrd) (hN _ hrd) hWd hP' hm hk hc hK ?_
    intro x hx hxa hxr hxu
    exact hν x (List.mem_cons_of_mem _ hx) hxa hxr (hxu.imp_right fun h hT => h (tch_sub hT))
  | rdp q k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    rw [reads_rdN, reads_rdN] at hν
    have hrp := L.read_pair_eq s q
    generalize core.num.U64.wrapping_add q 8#u64 = q8 at *
    obtain ⟨⟨hal, hr⟩, ⟨hal8, hr8⟩, hW⟩ := hW
    obtain ⟨ho, ho8, hN⟩ := hN
    have hu : ¬ User q ∨ q ∉ T := by
      by_cases hu : User q
      · exact Or.inr (ho fun h => h.1 hu)
      · exact Or.inl hu
    have hu8 : ¬ User q8 ∨ q8 ∉ T := by
      by_cases hu : User q8
      · exact Or.inr fun h => ho8 (fun h => h.1 hu) (tch_sub h)
      · exact Or.inl hu
    have e : L.mem s q = ν q := hν q (List.mem_cons_self ..) hal hr hu
    have e8 : L.mem s q8 = ν q8 :=
      hν q8 (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hal8 hr8 hu8
    have hrd : st.read_pair s q = ok (ν q, ν q8) := by rw [hrp, e, e8]
    refine altRun_rdN hWd hPT ho fun P' hP' => ?_
    refine altRun_rdN hWd hP' ho8 fun P'' hP'' => ?_
    refine ih (ν q, ν q8) s a Wd _ P'' ν κ (hW _ hrd) (hM _ hrd) (hN _ hrd) hWd hP'' hm hk hc hK ?_
    intro x hx hxa hxr hxu
    exact hν x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) hxa hxr
      (hxu.imp_right fun h hT => h (tch_sub (tch_sub hT)))
  | wr q v k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have hw := L.write_eq s q v
    obtain ⟨hWq, hW⟩ := hW
    have hW := hW _ hw
    obtain ⟨hQ, hM⟩ := hM _ hw
    have hN := hN _ hw
    obtain ⟨hal, hHp⟩ := hWr q hWq
    have hm' : st.frame_masks (L.wr s q v) = ok mk := by rw [hmk]; exact hm
    have hk' : L.ksb (L.wr s q v) = kb := by rw [L.ksb_wr]; exact hk
    have hc' : L.cpu (L.wr s q v) = c := by rw [L.cpu_wr]; exact hc
    by_cases hu : User q
    · rw [if_pos hu] at hN hν ⊢
      rw [if_pos hu] at hN
      refine ih _ a Wd _ P ν κ hW hM hN hWd (hPT.trans (Set.subset_insert _ _)) hm' hk' hc' ?_ ?_
      · intro x hx hxu
        have hne : q ≠ x := by rintro rfl; exact hxu hu
        rw [L.mem_wr s q v x hal hx, if_neg hne]; exact hK x hx hxu
      · intro x hx hxa hxr hxu
        have hne : q ≠ x := by
          rintro rfl
          rcases hxu with h | h
          · exact h hu
          · exact h (Set.mem_insert _ _)
        rw [L.mem_wr s q v x hal hxa, if_neg hne]
        exact hν x hx hxa hxr (hxu.imp_right fun h hT => h (Set.mem_insert_of_mem _ hT))
    · rw [if_neg hu] at hN hν ⊢
      rw [if_neg hu] at hN
      simp only [reads] at hν
      simp only [AltRun]
      refine ⟨hHp hu, wrOK_of_stepOK hO hal hu hK rfl hQ, ?_⟩
      refine ih _ a _ T P _ _ hW hM hN ?_ hPT hm' hk' hc' ?_ ?_
      · intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · exact hHp hu
        · exact hWd x hx
      · intro x hx hxu
        rw [L.mem_wr s q v x hal hx]
        by_cases hne : q = x
        · subst hne; rw [if_pos rfl, Function.update_self]
        · rw [if_neg hne, Function.update_of_ne (Ne.symm hne)]; exact hK x hx hxu
      · intro x hx hxa hxr hxu
        rw [L.mem_wr s q v x hal hxa]
        by_cases hne : q = x
        · subst hne; rw [if_pos rfl, Function.update_self]
        · rw [if_neg hne, Function.update_of_ne (Ne.symm hne)]; exact hν x hx hxa hxr hxu
  | ksb k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have h : st.ks_base s = ok kb := by rw [← hk]; exact L.ks_base_eq s
    exact ih kb s a Wd T P ν κ (hW _ h) (hM _ h) (hN _ h) hWd hPT hm hk hc hK hν
  | cpu k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    have h : st.cur_cpu s = ok c := by rw [← hc]; exact L.cur_cpu_eq s
    exact ih c s a Wd T P ν κ (hW _ h) (hM _ h) (hN _ h) hWd hPT hm hk hc hK hν
  | masks k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    simp only [tr] at hν ⊢
    exact ih mk s a Wd T P ν κ (hW _ hm) (hM _ hm) (hN _ hm) hWd hPT hm hk hc hK hν
  | arch op k ih =>
    intro s a Wd T P ν κ hW hM hN hWd hPT hm hk hc hK hν
    simp only [Within] at hW
    simp only [WithinM] at hM
    simp only [Once] at hN
    by_cases hca : ∃ r, callArch ar op a = ok r
    · have e := hca.choose_spec
      simp only [tr, dif_pos hca] at hν ⊢
      exact ih _ s _ Wd T P ν κ (hW _ _ e) (hM _ _ e) (hN _ _ e) hWd hPT hm hk hc hK hν
    · simp only [tr, dif_neg hca, AltRun]

end sim

/-! ## Realizing the values read -/

section wrs
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- `s` with each word of `l` set to its value in `ν`. -/
def wrs (ν : U64 → U64) : List U64 → S → S
  | [], s => s
  | x :: l, s => wrs ν l (L.wr s x (ν x))

theorem wrs_mem {ν : U64 → U64} : ∀ (l : List U64) (s : S), (∀ x ∈ l, Aligned x) →
    ∀ b, Aligned b → L.mem (wrs st ν l s) b = if b ∈ l then ν b else L.mem s b := by
  intro l
  induction l with
  | nil => intro s _ b _; simp [wrs]
  | cons x l ih =>
    intro s hl b hb
    rw [wrs, ih _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) b hb,
      L.mem_wr s x _ b (hl x (List.mem_cons_self ..)) hb]
    by_cases h1 : b ∈ l
    · rw [if_pos h1, if_pos (List.mem_cons_of_mem _ h1)]
    · rw [if_neg h1]
      by_cases h2 : x = b
      · subst h2; rw [if_pos rfl, if_pos (List.mem_cons_self ..)]
      · rw [if_neg h2, if_neg]
        intro h
        rcases List.mem_cons.mp h with h | h
        · exact h2 h.symm
        · exact h1 h

theorem wrs_const {ν : U64 → U64} (hmk : MasksWr st) : ∀ (l : List U64) (s : S),
    L.cpu (wrs st ν l s) = L.cpu s ∧ L.ksb (wrs st ν l s) = L.ksb s ∧
      st.frame_masks (wrs st ν l s) = st.frame_masks s := by
  intro l
  induction l with
  | nil => intro s; exact ⟨rfl, rfl, rfl⟩
  | cons x l ih =>
    intro s
    obtain ⟨h1, h2, h3⟩ := ih (L.wr s x (ν x))
    exact ⟨h1.trans (L.cpu_wr ..), h2.trans (L.ksb_wr ..), h3.trans (hmk ..)⟩

theorem wrs_user {A X : Type} {f : machine.Store S → S → A → Result (X × S × A)}
    {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}
    {Locks : S → U64 → Prop} {Pre : S → Prop} {RS WS DS : S → U64 → Prop}
    (Sd : PathSide st f cls ko User Locks Pre RS WS DS) {ν : U64 → U64} :
    ∀ (l : List U64) (s : S), (∀ x ∈ l, User x ∧ Aligned x) → Pre s →
      Pre (wrs st ν l s) ∧ Locks (wrs st ν l s) = Locks s ∧ RS (wrs st ν l s) = RS s ∧
        WS (wrs st ν l s) = WS s ∧ DS (wrs st ν l s) = DS s := by
  intro l
  induction l with
  | nil => intro s _ h; exact ⟨h, rfl, rfl, rfl, rfl⟩
  | cons x l ih =>
    intro s hl hs
    obtain ⟨hu, ha⟩ := hl x (List.mem_cons_self ..)
    obtain ⟨g0, g1, g2, g3, g4⟩ := Sd.user_free s x (ν x) hs hu ha
    obtain ⟨h0, h1, h2, h3, h4⟩ := ih _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) g0
    exact ⟨h0, h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩

end wrs

/-! ## A started body is safe -/

section body
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}
  {S A X : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
  {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A)}
  {p : SProg X} {Acc : X → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop}
  {RS WS DS : S → U64 → Prop}

/-- **A body is `Safe` when it starts**, from its per-path obligations: the
real store's state `σ` satisfies `Pre` and agrees with the model's memory `μ`
on aligned kernel words. -/
theorem body_safe (hD : Deciders own) (hL : MoveLocal own) (hO : OwnDep own User)
    (hp : IsProg F p) (O : PathObl st (F ar) Acc own cls ko User Locks Pre RS WS DS)
    (Sd : PathSide st (F ar) cls ko User Locks Pre RS WS DS)
    (hN : ReadOnce st ar p cls ko User Pre RS) (hT : ∀ s a, ∃ r, F ar st s a = ok r)
    (hmk : MasksWr st) {σ : S} {a : A} (hpre : Pre σ) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → ¬ User x → L.mem σ x = μ x) :
    Safe own cls ko (L.cpu σ) (Locks σ) μ
      (tr (RS σ) User cls ko (L.cpu σ) (L.ksb σ) (masksOf st σ) ar p ∅ a) := by
  have eF : ∀ st', F ar st' = interp st' ar p := fun st' => hp A ar st'
  have e0 : own (L.mem σ) = own μ := hO _ _ hμ
  let Hp : U64 → Prop := fun x => ¬ User x ∧ (WS σ x ∨ DS σ x)
  have hRI : RInv own (L.cpu σ) (Locks σ) (RpOf (RS σ) User Hp) Hp μ := by
    have hH : ∀ x, Hp x → HeldV (L.cpu σ) (Locks σ) (own μ x) := by
      intro x hx
      rw [← e0]; exact heldBy_iff.mp (O.write_own σ x hpre hx.2 hx.1)
    refine ⟨hH, fun x hx => ?_⟩
    rcases hx with ⟨hu, hr⟩ | hx
    · rw [← e0]
      rcases O.read_own σ x hpre hr hu with h | h
      · exact Or.inl (heldBy_iff.mp h)
      · exact Or.inr h
    · exact Or.inl (hH x hx)
  refine Fl4Proofs.P2.Serial.safe_of_runs hD hL (Rp := RpOf (RS σ) User Hp) (Hp := Hp) _ ∅ μ
    (fun _ => none) ⟨fun ν hν => ?_, fun y u hu => (by cases hu), fun y u hu => (by cases hu),
      fun y u hu => (by cases hu), hRI⟩
  have hνR : ∀ x, ¬ User x → RS σ x → ν x = μ x := fun x hu hr => hν.1 x (hRI.2 x (Or.inl ⟨hu, hr⟩))
  generalize hq : tr (RS σ) User cls ko (L.cpu σ) (L.ksb σ) (masksOf st σ) ar p ∅ a = q
  let rl := (reads q ν).filter (fun x => decide (Aligned x))
  let ul := rl.filter (fun x => decide (User x))
  let kl := rl.filter (fun x => decide (¬ User x))
  have hul : ∀ x, x ∈ ul ↔ (x ∈ reads q ν ∧ Aligned x) ∧ User x := by
    intro x; simp only [ul, rl, List.mem_filter, decide_eq_true_eq]
  have hkl : ∀ x, x ∈ kl ↔ (x ∈ reads q ν ∧ Aligned x) ∧ ¬ User x := by
    intro x; simp only [kl, rl, List.mem_filter, decide_eq_true_eq]
  obtain ⟨σu, hσu⟩ : ∃ s, s = wrs st ν ul σ := ⟨_, rfl⟩
  obtain ⟨σν, hσν⟩ : ∃ s, s = wrs st ν kl σu := ⟨_, rfl⟩
  obtain ⟨uP, uL, uR, uW, uD⟩ := wrs_user st Sd (ν := ν) ul σ
    (fun x hx => ⟨((hul x).mp hx).2, ((hul x).mp hx).1.2⟩) hpre
  obtain ⟨uc, ub, um⟩ := wrs_const st (ν := ν) hmk ul σ
  have uM := wrs_mem st (ν := ν) ul σ (fun x hx => ((hul x).mp hx).1.2)
  rw [← hσu] at uP uL uR uW uD uc ub um uM
  obtain ⟨kc, kb, km⟩ := wrs_const st (ν := ν) hmk kl σu
  have kM := wrs_mem st (ν := ν) kl σu (fun x hx => ((hkl x).mp hx).1.2)
  rw [← hσν] at kc kb km kM
  have hmσ := masksOf_eq st σ
  have uMk : ∀ x, Aligned x → ¬ User x → L.mem σu x = μ x := by
    intro x hx hu
    rw [uM x hx, if_neg (fun h => hu ((hul x).mp h).2)]; exact hμ x hx hu
  obtain ⟨ru, hru⟩ := hT σu a
  by_cases hacc : Acc ru.1
  · -- accepted at `σu`
    refine ⟨μ, fun y hy => absurd rfl hy, ?_⟩
    have hW := O.acc σu a ru uP hru hacc
    rw [eF] at hW
    have hW := (interp_guard p σu a ru hW).2
    have hA := Sd.read_aligned σu σu a ru uP (Alt.refl σu) hru
    rw [eF] at hA
    have hA := (interp_guard p σu a ru hA).2
    have hM := O.move_steps hp uP hru
    have hO1 := hN σu σu a ru uP (Alt.refl σu) (by rw [← eF]; exact hru)
    rw [uR] at hW hO1; rw [uW] at hW; rw [uc, uL] at hM
    rw [← hq]
    refine sim (L := L) hO hmk (Rr := RS σ) (Wr := fun x => True ∧ WS σ x) ?_ p σu a ∅ ∅ ∅ ν μ
      (within_and p σu a hA hW) hM hO1 (fun x hx => absurd hx (Set.notMem_empty x)) subset_rfl
      (um.trans hmσ) ub uc (fun x hx hu => (uMk x hx hu).symm) ?_
    · intro x hx
      exact ⟨O.aligned σ x hpre (Or.inl hx.2), fun hu => ⟨hu, Or.inl hx.2⟩⟩
    · rw [hq]
      intro x hx hxa hxr _
      by_cases hu : User x
      · rw [uM x hxa, if_pos ((hul x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
      · rw [uMk x hxa hu, hνR x hu hxr]
  · -- declined at `σu`
    have hAlt : Alt st (RS σu) cls ko User σu σν := by
      refine ⟨kc, kb, km, fun x hx => ?_, fun x hx hu hko => ?_⟩
      · have hxa := Sd.rs_aligned σu x uP hx
        rw [uR] at hx
        rw [kM x hxa]
        split_ifs with h
        · have hu := ((hkl x).mp h).2
          rw [hνR x hu hx, uMk x hxa hu]
        · rfl
      · have hxa : Aligned x := Sd.ko_aligned x (by rcases hko with h | h <;> rw [h] <;> simp)
        rw [kM x hxa]
        split_ifs with h
        · rw [uc] at hko
          rw [hν.2.2 x hko, uMk x hxa hu]
        · rfl
    obtain ⟨rν, hrν⟩ := hT σν a
    obtain ⟨-, hW, hM⟩ := O.dec_alt σu a ru uP hru hacc σν rν hAlt hrν
    rw [eF] at hW hM
    have hW := (interp_guard p σν a rν hW).2
    have hM := (interp_mguard p σν a rν hM).2
    have hA := Sd.read_aligned σu σν a rν uP hAlt hrν
    rw [eF] at hA
    have hA := (interp_guard p σν a rν hA).2
    have hO1 := hN σu σν a rν uP hAlt (by rw [← eF]; exact hrν)
    rw [uR] at hO1; rw [uD] at hW; rw [uc, uL] at hM
    refine ⟨fun x => if Aligned x ∧ ¬ User x then L.mem σν x else μ x, fun y hy hpo => ?_, ?_⟩
    · apply hy
      beta_reduce
      split_ifs with h
      · rw [kM y h.1, uMk y h.1 h.2]
        split_ifs
        · exact hν.1 y hpo
        · rfl
      · rfl
    · rw [← hq]
      refine sim (L := L) hO hmk (Rr := fun _ => True) (Wr := fun x => True ∧ DS σ x) ?_ p σν a
        ∅ ∅ ∅ ν _ (within_and p σν a hA hW) hM hO1 (fun x hx => absurd hx (Set.notMem_empty x))
        subset_rfl (km.trans (um.trans hmσ)) (kb.trans ub) (kc.trans uc)
        (fun x hx hu => if_pos ⟨hx, hu⟩) ?_
      · intro x hx
        exact ⟨O.aligned σ x hpre (Or.inr hx.2), fun hu => ⟨hu, Or.inr hx.2⟩⟩
      · rw [hq]
        intro x hx hxa _ _
        rw [kM x hxa]
        by_cases hu : User x
        · rw [if_neg (fun h => ((hkl x).mp h).2 hu), uM x hxa,
            if_pos ((hul x).mpr ⟨⟨hx, hxa⟩, hu⟩)]
        · rw [if_pos ((hkl x).mpr ⟨⟨hx, hxa⟩, hu⟩)]

end body

/-! ## Local paths and the top theorems -/

/-- **A local path with its obligations** for an ownership map, value classes
and user memory: the extracted body `F` (its other arguments fixed), the Store
and Arch instances, and, all per path, `IsProg` [P], `PathObl` [W], `PathSide`
[W], `ReadOnce` [W], totality (`<fn>.p0`, from a total Arch instance), and
`MasksWr` [P] of the store. -/
structure LocalPath (own : (U64 → U64) → U64 → Owner U64 U64) (cls : U64 → U64 → U64)
    (ko : U64 → ClsOwner U64) (User : U64 → Prop) : Type 1 where
  S : Type
  A : Type
  X : Type
  st : machine.Store S
  L : LawfulStore st
  ar : machine.Arch A
  F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (X × S × A)
  p : SProg X
  Acc : X → Prop
  Locks : S → U64 → Prop
  Pre : S → Prop
  RS : S → U64 → Prop
  WS : S → U64 → Prop
  DS : S → U64 → Prop
  isProg : IsProg F p
  obl : PathObl st (F ar) Acc own cls ko User Locks Pre RS WS DS
  side : PathSide st (F ar) cls ko User Locks Pre RS WS DS
  once : ReadOnce st ar p cls ko User Pre RS
  total : ∀ s a, ∃ r, F ar st s a = ok r
  masks : MasksWr st

section top
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- The body `P` runs from the store state `σ` and the Arch state `a`. -/
def LocalPath.body (P : LocalPath own cls ko User) (σ : P.S) (a : P.A) : SP :=
  letI := P.L
  tr (P.RS σ) User cls ko (P.L.cpu σ) (P.L.ksb σ) (masksOf P.st σ) P.ar P.p ∅ a

/-- **`StartAt`** [P], the glue's `start` correspondence: core `c`, holding the
locks `hs`, starts the local path `P` as the program `q` in model memory `μ`:
there is a store state `σ` and the core's Arch state `a` such that `σ` satisfies
the path's `Pre`, is of core `c`, has exactly the locks `hs`, agrees with `μ` on
aligned kernel words, and `q` is the body's run from there. Justification:
fl4-sync's glue (`local_syscall`, `local_vm_fault`, `run_timer_irq`, trusted)
calls the body on the one physical memory with its own core's Arch state, after
taking `Locks` and checking what `Pre` states. User words are left out: `Serial`
does not model user threads' writes. The body's program depends on `σ` and `a`
only through which reads are `rd` / `rdc` / `rds` (ghost: all three step alike)
and the core's constants and Arch answers; `Serial` lets a core arm any program,
so an execution is modelled with the program annotated for the `σ` at which its
body starts (what its glue's other branches start does not matter). -/
def StartAt (P : LocalPath own cls ko User) (c : U64) (hs : U64 → Prop) (μ : U64 → U64)
    (q : SP) : Prop :=
  ∃ (σ : P.S) (a : P.A), P.Pre σ ∧ P.L.cpu σ = c ∧ P.Locks σ = hs ∧
    (∀ x, Aligned x → ¬ User x → P.L.mem σ x = μ x) ∧ q = P.body σ a

theorem LocalPath.safe (P : LocalPath own cls ko User) (hD : Deciders own) (hL : MoveLocal own)
    (hO : OwnDep own User) {c : U64} {hs : U64 → Prop} {μ : U64 → U64} {q : SP}
    (h : StartAt P c hs μ q) : Safe own cls ko c hs μ q := by
  obtain ⟨σ, a, hpre, rfl, rfl, hμ, rfl⟩ := h
  let _ := P.L
  exact body_safe hD hL hO P.isProg P.obl P.side P.once P.total P.masks hpre hμ

end top

open Fl4Proofs.P2.Serial in
/-- **Every execution is a serial one**, from the per-path obligations, for any
ownership map: where a body starts, the map satisfies `Deciders`, `MoveLocal`,
`OwnDep`, and the body is a `LocalPath` started by the glue (`StartAt` [P]);
`ArmGlue` [W]. As in `serializable_safe`, a speculative read may return any
value in the serial order. -/
theorem serializable_paths {s0 s : Cfg U64 U64 U64 U64} (h0 : Init s0) (hA : ArmGlue s0)
    (hS : ∀ s, GReach s0 s → ∀ c p0 k W, s.ph c = .loc p0 (.start k) W →
      ∃ User, Deciders s.own ∧ MoveLocal s.own ∧ OwnDep s.own User ∧
        ∃ P : LocalPath s.own s.cls s.ko User, StartAt P c (fun l => s.lk l = some c) s.mem k)
    (h : Reach s0 s) (hq : NoLoc s) : RunAll s.log s0.mem s.mem := by
  refine serializable_safe h0 hA (fun s hs c p0 k W hph => ?_) h hq
  obtain ⟨User, hD, hL, hO, P, hP⟩ := hS s hs c p0 k W hph
  exact P.safe hD hL hO hP

/-! ## `OwnMap` -/

open OwnMap in
/-- **User memory lies outside the kernel's objects** [J] (from P1's typed-heap
disjointness and alignment, `HeapOK`: frames overlap no kernel object, objects
and slots are aligned to their size): the words an owner depends on are aligned
and not user words. Used only for `OwnDep`; nothing is assumed about who owns
user words. -/
structure UserOK (K : KLayout) : Prop where
  tcb : ∀ t, K.heap t = some .tcb → ∀ off, off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨
    off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT →
    Aligned (fld t off) ∧ fld t off ∉ K.user
  slot : ∀ p ∈ K.slots, Aligned p ∧ p ∉ K.user
  ntfn : ∀ p, K.heap p = some .ntfn → Aligned (fld p 24#u64) ∧ fld p 24#u64 ∉ K.user
  sc : ∀ p b, region K b = .sc p → Aligned (fld p 16#u64) ∧ fld p 16#u64 ∉ K.user

open OwnMap in
theorem ownDep {K : KLayout} (hK : RegionOK K) (hU : UserOK K) :
    OwnDep (own K) (· ∈ K.user) := by
  intro m m' h
  have ht : ∀ t, K.heap t = some .tcb → ∀ o, tcbOwner m t o = tcbOwner m' t o := by
    intro t ht o
    have g : ∀ off, off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨
        off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT →
        m (fld t off) = m' (fld t off) :=
      fun off ho => h _ (hU.tcb t ht off ho).1 (hU.tcb t ht off ho).2
    unfold tcbOwner
    rw [g oAFFINITY (by simp), g oSTATE (by simp), g oBLOCK_OBJ (by simp),
      g oTIMER_DEADLINE (by simp), g oTIMER_HEIGHT (by simp)]
  funext b
  unfold own
  cases hr : region K b with
  | node c => rfl
  | slot p =>
    obtain ⟨h1, h2⟩ := hU.slot p (hK.slotOf p b hr)
    simp only [slotOwner, h p h1 h2]
  | tcb t => exact ht t (hK.tcbOf t b hr) _
  | ntfn p =>
    obtain ⟨h1, h2⟩ := hU.ntfn p (hK.ntfnOf p b hr)
    simp only [ntfnOwner, h _ h1 h2]
    split_ifs with h3 h4
    · rfl
    · have h5 := hU.tcb _ h4 oAFFINITY (Or.inl rfl)
      rw [h _ h5.1 h5.2]
    · rfl
  | obj p => rfl
  | sc p =>
    obtain ⟨h1, h2⟩ := hU.sc p b hr
    simp only [h _ h1 h2]
  | none => rfl

open Fl4Proofs.P2.Serial in
/-- **`GlueStart`** [P]: wherever a body starts, the ghost maps are `OwnMap`'s
for a layout `K` with `RegionOK` [J] and `UserOK` [J] (the maps change only under
the gate, with `K`; `ko`'s home cores are read in the current memory, where
they are gate-owned), and the body is one of the local paths `LP`, started by
the glue (`StartAt`). -/
def GlueStart {ι : Type}
    (LP : ι → ∀ (K : OwnMap.KLayout) (m : U64 → U64), OwnMap.RegionOK K → UserOK K →
      LocalPath (OwnMap.own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user))
    (s0 : Cfg U64 U64 U64 U64) : Prop :=
  ∀ s, GReach s0 s → ∀ c p0 k W, s.ph c = .loc p0 (.start k) W →
    ∃ (K : OwnMap.KLayout) (hK : OwnMap.RegionOK K) (hU : UserOK K) (i : ι),
      s.own = OwnMap.own K ∧ s.cls = OwnMap.cls K ∧ s.ko = OwnMap.ko K s.mem ∧
      StartAt (LP i K s.mem hK hU) c (fun l => s.lk l = some c) s.mem k

open Fl4Proofs.P2.Serial in
/-- **End to end**: with FL4's ownership map, local paths `LP` (each with its
`LocalPath` obligations, for every layout) run beside the serial gate exactly
as some serial order of the completed entries: in every reachable state with no
local path in progress, memory is what running them one after another, in
completion order, produces. In that order a speculative read (user words
included) may return any value: that the result is a real serial run of the
entry is the per-path refinement obligation. Premises: `Init`; `ArmGlue` [W];
`GlueStart` [P] (with `RegionOK`, `UserOK` [J]); per path, `LocalPath`'s
([P]/[W]). -/
theorem serializable_e2e {ι : Type}
    (LP : ι → ∀ (K : OwnMap.KLayout) (m : U64 → U64), OwnMap.RegionOK K → UserOK K →
      LocalPath (OwnMap.own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user))
    {s0 s : Cfg U64 U64 U64 U64} (h0 : Init s0) (hA : ArmGlue s0) (hS : GlueStart LP s0)
    (h : Reach s0 s) (hq : NoLoc s) : RunAll s.log s0.mem s.mem := by
  refine serializable_safe h0 hA (fun s hs c p0 k W hph => ?_) h hq
  obtain ⟨K, hK, hU, i, e1, e2, e3, hP⟩ := hS s hs c p0 k W hph
  rw [e1, e2, e3]
  exact (LP i K s.mem hK hU).safe (OwnMap.deciders hK) (OwnMap.moveLocal hK) (ownDep hK hU) hP

end
end Fl4Proofs.P2.E2E

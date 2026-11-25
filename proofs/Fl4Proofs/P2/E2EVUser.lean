/-
P2 (line vlift): **lifting the existing local paths to rule 7 by the layout, not by re-walking them**.

`E2EV.LocalPath.liftV` needs `NoVcpuRd` [W]: the path's `ReadSet` holds no non-binding VCPU word
(`E2EV.VData`). The existing paths use maximal read sets built from `RPerm (own K)`, which contain every
`VData` word (`E2EVTop.not_noVcpuRd`). Every existing path, though, is stated **for every layout `K`**
(`E2E.Paths`), and several of them (`IoRS`: the VM fault, the VM ReplyRecv and the I/O port paths) cut
their read set to non-user words (`x ∉ K.user`). So instead of re-proving a path on a cut set:

* `userV K`: the base layout of `K` with the `VData` words counted as user memory. `own`, `cls`, `ko` do not
  look at `user`, so they are `K`'s (`rfl`); `RegionOK` is `K`'s; `UserOK` holds by `RegionOKV`
  (`userOK_userV`).
* The existing path at `userV K` has a read set cut to `¬ VData` for free when its `ReadSet` excludes user
  words (`IoRS`). Its `User` is `userV K`'s; **`LocalPath.unUser`** turns it back into a path for the
  real user memory `K.user`: `Alt` and the per-write check only get stronger or stay (a `VData` word's
  `ko` is `.free`, `OwnMapV.ko_vcpu`), `ReadOnce` is monotone in `User` (`once_mono`), `user_free` is
  for fewer words; `read_own` / `write_own` need that the sets' `userV`-user words are real user words.
* **`NoVcpuRW`** [W] (per path, a property of its *sets*, not of its runs): `ReadSet` / `WriteSet` /
  `DecSet` words are not `VData` or are real user words. For `IoRS` / `IoWS` it is the definitions plus
  `own_vcpu`; for `IoDS` the decline's words' regions (`P2/E2EVUserIo.lean`).
* `PathsV.ofPathsU`, **`serializable_e2eV_liftU`**: the existing family, each path taken at `userV K` and
  un-usered, lifted by `liftV` (its `NoVcpuRd` follows from `NoVcpuRW`), beside the VM paths.

Not covered by this route: a path whose `ReadSet` contains user words (`SlRS`: `x ∈ K.user ∨ RPerm`) or
does not exclude them (`MaxR`: `RPerm ∧ Aligned`); at `userV K` such a set still contains the `VData`
words (now as user words), so `NoVcpuRW.rd` fails for it (syscall_local, SetTimer, timer IRQ; handoff
`vlift.md`).

Premises: none new beyond `serializable_e2eV`'s and `NoVcpuRW` [W] per lifted path. A path's own
premises are now asked at `userV K` (its `Pre`, e.g. `IoLay.user` needs no VCPU in the kernel-state
block: `P2/E2EVUserIo.lean`'s `VcpuKs` [J]).
-/
import Fl4Proofs.P2.E2EVTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## The layout with the VCPU data words as user memory -/

/-- `K`'s base layout with the non-binding VCPU words counted as user memory. -/
def userV (K : KLayoutV) : OwnMap.KLayout :=
  { K.toKLayout with user := {x | x ∈ K.user ∨ VData K x} }

section layout
variable {K : KLayoutV}

theorem own_userV : OwnMap.own (userV K) = OwnMap.own K.toKLayout := rfl
theorem cls_userV : OwnMap.cls (userV K) = OwnMap.cls K.toKLayout := rfl
theorem ko_userV (m : U64 → U64) : OwnMap.ko (userV K) m = OwnMap.ko K.toKLayout m := rfl
theorem region_userV (b : U64) : OwnMap.region (userV K) b = OwnMap.region K.toKLayout b := rfl

theorem mem_userV {x : U64} : x ∈ (userV K).user ↔ x ∈ K.user ∨ VData K x := Iff.rfl

theorem regionOK_userV (hK : RegionOKV K) : OwnMap.RegionOK (userV K) where
  tcb := hK.base.tcb
  slot := hK.base.slot
  ntfn := hK.base.ntfn
  scw := hK.base.scw
  tcbOf := hK.base.tcbOf
  slotOf := hK.base.slotOf
  ntfnOf := hK.base.ntfnOf

/-- A word in a region other than `.none` is no VCPU data word. -/
theorem notVData_of_region' (hK : RegionOKV K) {b : U64} (h : OwnMap.region K.toKLayout b ≠ .none) :
    ¬ VData K b :=
  fun ⟨v, hv, _⟩ => h (hK.none v b hv)

theorem userOK_userV (hK : RegionOKV K) (hU : UserOKV K) : UserOK (userV K) where
  tcb t ht off hoff := by
    refine ⟨(hU.base.tcb t ht off hoff).1, ?_⟩
    rintro (h | h)
    · exact (hU.base.tcb t ht off hoff).2 h
    · have hr := (hK.base.tcb t ht off (by rcases hoff with h | h | h | h | h <;> simp [h])).1
      exact notVData_of_region' hK (by rw [hr]; intro e; cases e) h
  slot p hp := by
    refine ⟨(hU.base.slot p hp).1, ?_⟩
    rintro (h | h)
    · exact (hU.base.slot p hp).2 h
    · exact notVData_of_region' hK (by rw [hK.base.slot p hp]; intro e; cases e) h
  ntfn p hp := by
    refine ⟨(hU.base.ntfn p hp).1, ?_⟩
    rintro (h | h)
    · exact (hU.base.ntfn p hp).2 h
    · exact notVData_of_region' hK (by rw [(hK.base.ntfn p hp).1]; intro e; cases e) h
  sc p b hb := by
    refine ⟨(hU.base.sc p b hb).1, ?_⟩
    rintro (h | h)
    · exact (hU.base.sc p b hb).2 h
    · exact notVData_of_region' hK (by rw [(hK.base.scw p b hb).1]; intro e; cases e) h

end layout

/-! ## `ReadOnce` is monotone in the user words -/

section once
variable {S A X : Type} {st : machine.Store S} {ar : machine.Arch A} {R U U' : U64 → Prop}

theorem racy_mono (hU : ∀ x, U x → U' x) {Wd Wd' : Set U64} (hW : Wd' ⊆ Wd) {q : U64}
    (h : Racy R U Wd q) : Racy R U' Wd' q := by
  intro ⟨hu, hr⟩
  exact h ⟨fun h' => hu (hU _ h'), hr.imp id (fun hw => hW hw)⟩

theorem tch_mono (hU : ∀ x, U x → U' x) {Wd Wd' T T' : Set U64} (hW : Wd' ⊆ Wd) (hT : T ⊆ T') (q : U64) :
    tch R U Wd q T ⊆ tch R U' Wd' q T' := by
  unfold tch
  by_cases h1 : Racy R U Wd q
  · rw [if_pos h1, if_pos (racy_mono hU hW h1)]; exact Set.insert_subset_insert hT
  · rw [if_neg h1]; split_ifs
    · exact hT.trans (Set.subset_insert _ _)
    · exact hT

/-- **`Once` is monotone in `User`**: a run that reads each racy word once when more words count as user
words does so for fewer. -/
theorem once_mono (hU : ∀ x, U x → U' x) (p : SProg X) :
    ∀ (Wd T Wd' T' : Set U64) (s : S) (a : A), Wd' ⊆ Wd → T ⊆ T' →
      Once st ar R U' Wd' T' p s a → Once st ar R U Wd T p s a := by
  induction p with
  | ret x => intros; simp only [Once]
  | err e => intros; simp only [Once]
  | rd q k ih =>
    intro Wd T Wd' T' s a hW hT h
    simp only [Once] at h ⊢
    exact ⟨fun hr hq => h.1 (racy_mono hU hW hr) (hT hq),
      fun v hv => ih v _ _ _ _ s a hW (tch_mono hU hW hT q) (h.2 v hv)⟩
  | rdp q k ih =>
    intro Wd T Wd' T' s a hW hT h
    simp only [Once] at h ⊢
    refine ⟨fun hr hq => h.1 (racy_mono hU hW hr) (hT hq),
      fun hr hq => h.2.1 (racy_mono hU hW hr) (tch_mono hU hW hT q hq),
      fun v hv => ih v _ _ _ _ s a hW (tch_mono hU hW (tch_mono hU hW hT q) _) (h.2.2 v hv)⟩
  | wr q v k ih =>
    intro Wd T Wd' T' s a hW hT h
    simp only [Once] at h ⊢
    intro s' hs
    refine ih _ _ _ _ s' a ?_ ?_ (h s' hs)
    · by_cases h1 : U' q
      · rw [if_pos h1]; split_ifs
        · exact hW
        · exact hW.trans (Set.subset_insert _ _)
      · rw [if_neg h1, if_neg (fun h => h1 (hU _ h))]; exact Set.insert_subset_insert hW
    · by_cases h1 : U q
      · rw [if_pos h1, if_pos (hU _ h1)]; exact Set.insert_subset_insert hT
      · rw [if_neg h1]; split_ifs
        · exact hT.trans (Set.subset_insert _ _)
        · exact hT
  | zero q n k ih => intros _ _ _ _ _ _ _ _ h; simp only [Once] at h
  | clr q n k ih => intros _ _ _ _ _ _ _ _ h; simp only [Once] at h
  | ksb k ih =>
    intro Wd T Wd' T' s a hW hT h
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ _ s a hW hT (h v hv)
  | cpu k ih =>
    intro Wd T Wd' T' s a hW hT h
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ _ s a hW hT (h v hv)
  | masks k ih =>
    intro Wd T Wd' T' s a hW hT h
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ _ s a hW hT (h v hv)
  | arch op k ih =>
    intro Wd T Wd' T' s a hW hT h
    simp only [Once] at h ⊢
    exact fun v a' hv => ih v _ _ _ _ s a' hW hT (h v a' hv)

end once

/-! ## Fewer user words -/

section unuser
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
  {U U' : U64 → Prop}

theorem stepOK_unUser (hko : ∀ x, U' x → ¬ U x → ko x = .free) {c : U64} {lk : U64 → Prop}
    {m m' : U64 → U64} (h : StepOK own cls ko U' c lk m m') : StepOK own cls ko U c lk m m' :=
  ⟨h.1, fun x hx hu => if hu' : U' x then Or.inr (Or.inr (hko x hu' hu)) else h.2 x hx hu'⟩

theorem alt_unUser {S : Type} {st : machine.Store S} [LawfulStore st] {R : U64 → Prop}
    (hUU : ∀ x, U x → U' x) {s s' : S} (h : Alt st R cls ko U s s') : Alt st R cls ko U' s s' :=
  ⟨h.cpu, h.ksb, h.masks, h.read, fun x hx hu hk => h.clsEq x hx (fun h' => hu (hUU x h')) hk⟩

/-- **A local path for more user words is one for fewer** (`U ⊆ U'`), given that the words only `U'`
counts are untracked (`ko` free) and that the path's sets name none of them as a kernel word it reads
or writes (`hRS`, `hWS`). -/
def LocalPath.unUser (P : LocalPath own cls ko U') (hUU : ∀ x, U x → U' x)
    (hko : ∀ x, U' x → ¬ U x → ko x = .free)
    (hRS : ∀ s x, P.Pre s → P.RS s x → U' x → U x)
    (hWS : ∀ s x, P.Pre s → (P.WS s x ∨ P.DS s x) → U' x → U x) : LocalPath own cls ko U where
  S := P.S
  A := P.A
  X := P.X
  st := P.st
  L := P.L
  ar := P.ar
  F := P.F
  p := P.p
  Acc := P.Acc
  Locks := P.Locks
  Pre := P.Pre
  RS := P.RS
  WS := P.WS
  DS := P.DS
  isProg := by
    letI := P.L
    exact fun st' N s ⟨s0, h0, hA⟩ a => P.isProg st' N s ⟨s0, h0, alt_unUser hUU hA⟩ a
  obl := by
    letI := P.L
    have mono : ∀ (cpu : U64) (lk : U64 → Prop) (s : P.S) (a : P.A) r,
        AltOf P.st P.Pre P.RS cls ko U' s →
        P.F P.ar (mguard P.st (fun x y => StepOK own cls ko U' cpu lk (P.L.mem x) (P.L.mem y))) s a = ok r →
        P.F P.ar (mguard P.st (fun x y => StepOK own cls ko U cpu lk (P.L.mem x) (P.L.mem y))) s a = ok r := by
      intro cpu lk s a r hG h
      have e1 := P.isProg _ (Narrow.mguard P.st (fun x y => StepOK own cls ko U' cpu lk
        (P.L.mem x) (P.L.mem y))) s hG a
      have e2 := P.isProg _ (Narrow.mguard P.st (fun x y => StepOK own cls ko U cpu lk
        (P.L.mem x) (P.L.mem y))) s hG a
      exact e2.trans (interp_mguard_mono (fun x y hq => stepOK_unUser hko hq) P.p s a r (e1.symm.trans h))
    exact {
      acc := P.obl.acc
      dec_alt := fun s a r hp h hd s' r' hA h' => by
        obtain ⟨h1, h2, h3⟩ := P.obl.dec_alt s a r hp h hd s' r' (alt_unUser hUU hA) h'
        exact ⟨h1, h2, mono _ _ _ _ _ ⟨s, hp, alt_unUser hUU hA⟩ h3⟩
      read_own := fun s x hp hr hu =>
        P.obl.read_own s x hp hr (fun hu' => hu (hRS s x hp hr hu'))
      write_own := fun s x hp hw hu =>
        P.obl.write_own s x hp hw (fun hu' => hu (hWS s x hp hw hu'))
      aligned := P.obl.aligned
      move := fun s a r hp h => mono _ _ _ _ _ (AltOf.pre hp) (P.obl.move s a r hp h) }
  side := by
    letI := P.L
    exact {
      read_aligned := fun s s' a r hp hA h => P.side.read_aligned s s' a r hp (alt_unUser hUU hA) h
      rs_aligned := P.side.rs_aligned
      ko_aligned := P.side.ko_aligned
      user_free := fun s b v hp hb ha => P.side.user_free s b v hp (hUU b hb) ha }
  once := by
    letI := P.L
    exact fun s s' a r hp hA h =>
      once_mono hUU P.p ∅ ∅ ∅ ∅ s' a subset_rfl subset_rfl (P.once s s' a r hp (alt_unUser hUU hA) h)
  total := P.total
  masks := P.masks

end unuser

/-! ## The existing paths at `userV K`, lifted -/

section lift
variable {K : KLayoutV} {m : U64 → U64}

/-- **`NoVcpuRW`** [W] (per path, about its sets): every word of the path's `ReadSet`, `WriteSet` or
`DecSet` at `userV K` is no VCPU data word or a real user word. Holds by definition for `IoRS` / `IoWS`
(non-user words; `own`'s write permission excludes the gate's VCPU words); fails for a `ReadSet` holding
user words (`SlRS`, `MaxR`). -/
structure NoVcpuRW (K : KLayoutV)
    (P : LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)) :
    Prop where
  rd : ∀ s x, P.Pre s → P.RS s x → ¬ VData K x ∨ x ∈ K.user
  wr : ∀ s x, P.Pre s → (P.WS s x ∨ P.DS s x) → ¬ VData K x ∨ x ∈ K.user

/-- The path at `userV K`, for the real user memory. -/
def LocalPath.atV (hK : RegionOKV K)
    (P : LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user))
    (hW : NoVcpuRW K P) :
    LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  LocalPath.unUser (U := (· ∈ K.user)) P (fun x h => Or.inl h)
    (fun x hu' hu => by
      rcases hu' with h | ⟨v, hv, _⟩
      · exact absurd h hu
      · exact ko_vcpu hK hv m)
    (fun s x hp hr hu' => by
      rcases hu' with h | h
      · exact h
      · exact (hW.rd s x hp hr).resolve_left (not_not.mpr h))
    (fun s x hp hw hu' => by
      rcases hu' with h | h
      · exact h
      · exact (hW.wr s x hp hw).resolve_left (not_not.mpr h))

theorem noVcpuRd_atV (hK : RegionOKV K)
    (P : LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user))
    (hW : NoVcpuRW K P) : NoVcpuRd K (LocalPath.atV hK P hW) :=
  fun s x hp hr hu => (hW.rd s x hp hr).resolve_right hu

end lift

/-- **The existing paths, lifted through `userV`**: each path of `LP` taken at `userV K`, given back the real
user memory (`LocalPath.atV`) and lifted to `ownV` (`liftV`), given `NoVcpuRW` [W] of each. -/
def PathsV.ofPathsU {ι : Type} (LP : Paths ι)
    (hW : ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K),
      NoVcpuRW K (LP i (userV K) m (regionOK_userV hK) (userOK_userV hK hU))) : PathsV ι :=
  fun i K m hK hU =>
    LocalPath.liftV hK (LocalPath.atV hK _ (hW i K m hK hU)) (noVcpuRd_atV hK _ (hW i K m hK hU))

/-- **End to end with the existing paths lifted through `userV` and the VM paths beside them**: as
`serializable_e2eV_lift`, with `NoVcpuRW` [W] (a property of each path's sets, true by definition for the
`IoRS` paths) in place of `NoVcpuRd` [W] (false for every existing path as built). -/
theorem serializable_e2eV_liftU {ι κ : Type} (LP : Paths ι)
    (hW : ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K),
      NoVcpuRW K (LP i (userV K) m (regionOK_userV hK) (userOK_userV hK hU)))
    (LQ : PathsV κ) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV} (h0 : Init s0) (hA0 : ArmInv s0)
    (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV (PathsV.sum (PathsV.ofPathsU LP hW) LQ) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_e2eV _ h0 hA0 hK0 hU0 hM0 h hq

end
end Fl4Proofs.P2.E2EV

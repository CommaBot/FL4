/-
# P2: `TCB_SetTimer` as an `E2E.LocalPath` for `OwnMap`

`set_timer_localPath`: for a layout `K` with `RegionOK` / `UserOK` (what `E2E.serializable_e2e` hands each path) and
the model memory `m` the body starts on, `localtimer.handle_set_timer_local` with the maps `OwnMap.own K`,
`OwnMap.cls K`, `OwnMap.ko K m` and user memory `K.user`. The entry facts `StEntK` are `StEnt` (P1's invariant,
`StLay`, `StPre`, the core-placement facts) and that the store agrees with `m` on aligned kernel words (what
`E2E.StartAt` gives). The class premises of `set_timer_pathObl` are discharged here: the target's `TIMER_DEADLINE`
has the class zero / nonzero (`OwnMap.cls`), owned by the target's home core (`OwnMap.ko`, read in `m`), and is no
user word (`UserOK`); the declined run's words (`StDec`) are untracked; tracked words are aligned.

Premises:
* `hp` [P] (`IsProg`), `hm` [P] (`MasksWr`), `hz` [W] (`NoZero` of the tree);
* `hmv` [W]: `move` of accepted runs (`P2/MoveTimer`; pending the re-extracted write order);
* `hro` [W]: `ReadOnce`;
* `hEU` [J]: `StEnt` survives a write of a user word; `hlk` [P]: so do the glue's locks;
* `hNU` [J]: the node's words are no user words.
-/
import Fl4Proofs.P2.FootTimerSetObl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner ClsOwner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- **The entry facts for a layout and a model memory**: `StEnt`, and the store agrees with `m` on aligned kernel
words. -/
structure StEntK (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (target : U64) (m : U64 → U64) (s : S) : Prop where
  ent : StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s
  mem : ∀ x, Aligned x → x ∉ K.user → L.mem s x = m x

variable {target : U64} {m : U64 → U64}

theorem u64_eq0 (x : U64) : x = 0#u64 ↔ x.val = 0 :=
  ⟨fun h => by subst h; rfl, fun h => UScalar.eq_of_val_eq (by simp [h])⟩

theorem StEnt.td_region {s : S} (hE : StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s) :
    region K (tdA target) = .tcb target ∧ (tdA target).val - target.val = 3528 := by
  have hT : TcbPlaced T := hE.inv.1.choose_spec.choose_spec.tcbs
  refine ⟨hE.lay.tcb target hE.tg 3528#u64 (by simp) (by simp), ?_⟩
  unfold tdA
  rw [field_val (hT target hE.tg) (by simp)]
  simp

theorem set_timer_cls {s : S} (hE : StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s) (v w : U64)
    (e : cls K (tdA target) v = cls K (tdA target) w) : (v = 0#u64 ↔ w = 0#u64) := by
  obtain ⟨hr, -⟩ := hE.td_region
  have e' : v = w := by simpa only [OwnMap.cls, hr] using e
  subst e'; exact Iff.rfl

theorem set_timer_ko (hK : RegionOK K) (hUO : E2E.UserOK K) {s : S}
    (hE : StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m s) (ha : L.mem s (affA target) = L.cpu s) :
    OwnMap.ko K m (tdA target) = .core (L.cpu s) := by
  obtain ⟨hr, ev⟩ := hE.ent.td_region
  have ht := hK.tcbOf target _ hr
  obtain ⟨h1, h2⟩ := hUO.tcb target ht oAFFINITY (Or.inl rfl)
  have e : m (fld target oAFFINITY) = L.mem s (affA target) := (hE.mem _ h1 h2).symm
  simp only [OwnMap.ko, hr]
  rw [if_pos (Or.inr ev), e, ha]

theorem set_timer_user (hK : RegionOK K) (hUO : E2E.UserOK K) {s : S}
    (hE : StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s) : tdA target ∉ K.user := by
  obtain ⟨hr, -⟩ := hE.td_region
  exact (hUO.tcb target (hK.tcbOf target _ hr) oTIMER_DEADLINE (by simp)).2

theorem set_timer_koF {s : S} (hE : StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s) {q : U64}
    (hq : StDec st s q) : OwnMap.ko K m q = .free := by
  obtain ⟨-, -, h3⟩ := hE.dec hq
  rcases h3 with ⟨c, hc⟩ | ⟨t, hc, hlt⟩
  · simp only [OwnMap.ko, hc]
  · simp only [OwnMap.ko, hc]
    rw [if_neg (by omega)]

theorem ko_aligned (hK : RegionOK K) (hUO : E2E.UserOK K) (x : U64) (hx : OwnMap.ko K m x ≠ .free) :
    Aligned x := by
  unfold OwnMap.ko at hx
  cases hr : region K x with
  | slot p =>
    simp only [hr] at hx
    split_ifs at hx with h
    · obtain ⟨rfl, -⟩ := h
      exact (hUO.slot x (hK.slotOf x x hr)).1
    · exact absurd rfl hx
  | tcb t =>
    simp only [hr] at hx
    have ht := hK.tcbOf t x hr
    split_ifs at hx with h
    · rcases h with h | h
      · obtain ⟨-, e2⟩ := hK.tcb t ht oSTATE (by simp)
        have hs : oSTATE.val = 3328 := by simp [oSTATE]
        have : x = fld t oSTATE := UScalar.eq_of_val_eq (by omega)
        rw [this]; exact (hUO.tcb t ht oSTATE (by simp)).1
      · obtain ⟨-, e2⟩ := hK.tcb t ht oTIMER_DEADLINE (by simp)
        have hs : oTIMER_DEADLINE.val = 3528 := by simp [oTIMER_DEADLINE]
        have : x = fld t oTIMER_DEADLINE := UScalar.eq_of_val_eq (by omega)
        rw [this]; exact (hUO.tcb t ht oTIMER_DEADLINE (by simp)).1
    · exact absurd rfl hx
  | node c => simp [hr] at hx
  | ntfn p => simp [hr] at hx
  | obj p => simp [hr] at hx
  | sc p => simp [hr] at hx
  | none => simp [hr] at hx

/-- A user write leaves the declined run's words (`StDec` reads only the node's `CUR_THREAD`), the node's words
being no user words. -/
theorem set_timer_dec_user {s : S} (hE : StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s)
    (hNU : ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ K.user) {b v : U64} (hb : b ∈ K.user)
    (hba : Aligned b) : StDec st (L.wr s b v) = StDec st s := by
  have h0 := hE.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  have ec : L.curW (L.wr s b v) = L.curW s := by
    unfold LawfulStore.curW
    rw [nodeAt_wr, LawfulStore.cpu_wr]
    exact mem_wr_ne' hba (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val]))
      (fun e => hNU _ (by rw [curth_val]; omega) (e ▸ hb))
  funext w
  simp only [StDec, ctA, cnA, ec, nodeAt_wr, LawfulStore.cpu_wr]

variable {A : Type} (ar : machine.Arch A) (n : I64) {lk : S → U64 → Prop} {p : SProg Bool}

/-- The body as `E2E.LocalPath.F`. -/
abbrev stBody (S : Type) (n : I64) (target : U64) : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A →
    Result (Bool × S × A) :=
  fun ar m s a => localtimer.handle_set_timer_local m ar s a n target

/-- **`TCB_SetTimer` is a local path** (module docstring). -/
noncomputable def set_timer_localPath (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (stBody S n target) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hmv : ∀ s a s1 a1, StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m s →
      localtimer.handle_set_timer_local st ar s a n target = ok (true, s1, a1) →
      localtimer.handle_set_timer_local (mguard st
        (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
          (L.mem y))) ar s a n target = ok (true, s1, a1))
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m) (MaxR K st lk))
    (hEU : ∀ s b v, StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s → b ∈ K.user → Aligned b →
      StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hNU : ∀ s, StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s → ∀ o : U64, o.val < 4288 →
      L.nodeAt s (L.cpu s) o ∉ K.user) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := stBody S n target
  p := p
  Acc := fun b => b = true
  Locks := lk
  Pre := StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m
  RS := MaxR K st lk
  WS := MaxW K st lk
  DS := StDec st
  isProg := hp
  obl := set_timer_pathObl ar n hA hK hUO (fun s h => h.ent) (fun mm => hp A ar mm) hz hm
    (fun s h => set_timer_cls h.ent) (fun s h => set_timer_ko hK hUO h)
    (fun s h => set_timer_user hK hUO h.ent) (fun s h q hq => set_timer_koF h.ent hq)
    (ko_aligned hK hUO) hmv
  side := set_timer_pathSide ar n hA (fun s h => h.ent) (fun mm => hp A ar mm) hz hm
    (fun s h => set_timer_cls h.ent) (fun s h => set_timer_ko hK hUO h)
    (fun s h => set_timer_user hK hUO h.ent) (ko_aligned hK hUO) (fun s b v h hb hba => by
      have keep : ∀ x, Aligned x → x ∉ K.user → L.mem (L.wr s b v) x = L.mem s x :=
        fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb))
      have eo : own K (L.mem (L.wr s b v)) = own K (L.mem s) :=
        E2E.ownDep hK hUO _ _ (fun x hx hxu => keep x hx hxu)
      refine ⟨⟨hEU s b v h.ent hb hba, fun x hx hxu => by rw [keep x hx hxu]; exact h.mem x hx hxu⟩,
        hlk s b v hb, ?_, ?_, ?_⟩
      · funext w; simp only [MaxR, RPerm, GateOnly, eo, hlk s b v hb, L.cpu_wr]
      · funext w; simp only [MaxW, WPerm, eo, hlk s b v hb, L.cpu_wr]
      · exact set_timer_dec_user h.ent (hNU s h.ent) hb hba)
  once := hro
  total := fun s a => by
    obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localtimer.handle_set_timer_local.p0 st ar s a n target LawfulStore.total hA)
    exact ⟨r, e⟩
  masks := hm

end

end Fl4Proofs.P2

/-
# P2: the timer interrupt local path: `PathObl`, `PathSide`, `E2E.LocalPath`

For the ownership map `OwnMap.own K`, `localtimer.handle_timer_irq_local` with the maximal sets `MaxR` / `MaxW` and
`DecSet = IrqDec` (`update_timestamp`'s node `CUR_TIME` / `CONSUMED`):

* `irq_alt`: every run at an alternative state (`PathObl.Alt` for `MaxR`) is the entry's: an accepted entry run is
  the same run on `guard st MaxR MaxW` (`irq_acc_own`), a declined one on `guard st MaxR IrqDec`
  (`irq_dec_guard`), so the alternative's run is that run (`interp_agree`), and declines too;
* `irq_pathObl` / `irq_pathSide`: as `set_timer_pathObl` / `set_timer_pathSide` (declined `move` is `dec_alt` at
  the entry, accepted `move` is `irq_move_acc`); the declined run's words are this core's node words, untracked;
* `irq_localPath`: `E2E.LocalPath` with `Pre = IrqEntM` (`IrqEnt` and the store agreeing with the model memory on
  aligned kernel words); `IrqDec` and the node do not move under user writes (no premise needed for them).

Premises: `hp` [P] (`IsProg`), `hz` [W] (`NoZero`), `hm` [P] (`MasksWr`), `hro` [W] (`ReadOnce`); in `IrqEnt`:
`StLay` [J], `IrqLay` [J], `AsidOff` [J], `aff` [J] (p2j `AffSc`); `hEU` [J] (`IrqEnt` survives a user write),
`hlk` [P] (so do the glue's locks); `hF` / `hFm` (the fire case, p2j's line: accepted `acc` / `move`). A declined
fire run needs no premise (`irq_dec_guard` / `fire_rd`); `IrqEnt.nth` is P1's `Nt` typed in its heap `H` (`fun _ h => h`
at the canonical instantiation `Nt = H.ntfns`).
-/
import Fl4Proofs.P2.FootTimerIrqDec
import Fl4Proofs.P2.FootTimerSetLP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner ClsOwner)
open Fl4Proofs.P2.OwnMap
open Classical
open Fl4Proofs.P2.PathObl (guard mguard RPerm WPerm HeldBy GateOnly SProg IsProg NoZero interp interp_agree interp_mono
  interp_guard interp_to_mguard StepOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- **The entry facts of the timer interrupt** (`PathObl`'s `Pre` up to the model memory): P1's invariant, the
layouts [J], P1's `AsidOff` [J] and p2j's `AffSc` [J]. -/
structure IrqEnt (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (irq : U64) (s : S) : Prop where
  inv : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s
  lay : StLay K st T Scs Z s
  ly : IrqLay K st Nt irq s
  asid : AsidOff (L := L) Ω Sg s
  aff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)
  /-- P1's notifications are its heap's (`fun _ h => h` for `Nt = H.ntfns`). -/
  nth : ∀ n ∈ Nt, H n = some .ntfn

/-- `IrqEnt` and the store agreeing with the model memory `m` on aligned kernel words. -/
structure IrqEntM (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (irq : U64) (m : U64 → U64) (s : S) : Prop where
  ent : IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s
  mem : ∀ x, Aligned x → x ∉ K.user → L.mem s x = m x

variable {irq : U64} {m : U64 → U64}

theorem IrqEntM.k {s : S} (h : IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s) :
    IrqEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac m s :=
  ⟨h.ent.inv, h.ent.lay, h.mem, h.ent.asid⟩

theorem IrqEnt.dec {s : S} (h : IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s) {q : U64} (hq : IrqDec st s q) :
    Aligned q ∧ own K (L.mem s) q = .core (L.cpu s) ∧ ∃ c, region K q = .node c := by
  have h0 := h.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  rcases hq with rfl | rfl
  · exact ⟨nodeAt_aligned hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]),
      h.lay.own_node _ (by simp [layout.node.CUR_TIME]), _, h.lay.nd _ (by simp [layout.node.CUR_TIME])⟩
  · exact ⟨nodeAt_aligned hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
      h.lay.own_node _ (by simp [layout.node.CONSUMED]), _, h.lay.nd _ (by simp [layout.node.CONSUMED])⟩

theorem irq_koF {s : S} (hE : IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s) {q : U64} (hq : IrqDec st s q) :
    OwnMap.ko K m q = .free := by
  obtain ⟨-, -, c, hc⟩ := hE.dec hq
  simp only [OwnMap.ko, hc]

theorem irq_dec_user (s : S) (b v : U64) : IrqDec st (L.wr s b v) = IrqDec st s := by
  funext w
  simp only [IrqDec, ctA, cnA, nodeAt_wr, LawfulStore.cpu_wr]

variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop} {p : SProg Bool}
variable {lk : S → U64 → Prop}

/-- **Every run at an alternative is the entry's** (module docstring), the fire case premise `hF`. -/
theorem irq_alt (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hp : ∀ mm : machine.Store S, irqBody S irq pl ar mm = interp mm ar p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {s s' : S} {a : A} {r' : Bool × S × A}
    (hE : IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s)
    (hF : ∀ s1 a1, IrqFire st ar s a → localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq pl = ok (true, s1, a1))
    (hAlt : PathObl.Alt st (MaxR K st lk s) cls ko User s s')
    (h' : localtimer.handle_timer_irq_local st ar s' a irq pl = ok r') :
    (∃ s1 a1, localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) ∧ r'.1 = true ∧
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s' a irq pl = ok r') ∨
    (∃ s1 a1, localtimer.handle_timer_irq_local st ar s a irq pl = ok (false, s1, a1) ∧ r'.1 = false ∧
      localtimer.handle_timer_irq_local (guard st Aligned (IrqDec st s)) ar s' a irq pl = ok r') := by
  have hR1 : ∀ w, MaxR K st lk s w → Aligned w := fun _ hw => hw.2
  have hW1 : ∀ w, MaxW K st lk s w → Aligned w := fun _ hw => hw.2
  have hW2 : ∀ w, IrqDec st s w → Aligned w := fun _ hw => (hE.dec hw).1
  have eP : ∀ (mm : machine.Store S) (x : S),
      localtimer.handle_timer_irq_local mm ar x a irq pl = interp mm ar p x a :=
    fun mm x => congrFun (congrFun (hp mm) x) a
  have tr : ∀ {W' : U64 → Prop} {x : Bool} {s1 : S} {a1 : A}, (∀ w, W' w → Aligned w) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) W') ar s a irq pl = ok (x, s1, a1) →
      r'.1 = x ∧ localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) W') ar s' a irq pl = ok r' := by
    intro W' x s1 a1 hWa hg
    rw [eP] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm hR1 hWa p hz s s' a x s1 a1 hAlt.ksb hAlt.cpu hAlt.masks hAlt.read hg
    have hst := (interp_guard p s' a _ hg').1
    rw [← eP, h'] at hst
    have e := Result.ok_injective hst
    subst e
    exact ⟨rfl, by rw [eP]; exact hg'⟩
  obtain ⟨r, hr⟩ : ∃ r, localtimer.handle_timer_irq_local st ar s a irq pl = ok r := by
    have := P0.localtimer.handle_timer_irq_local.p0 st ar s a irq pl LawfulStore.total hA
    obtain ⟨r, e, -⟩ := spec_ex_fd this
    exact ⟨r, e⟩
  obtain ⟨b, s1, a1⟩ := r
  cases b
  swap
  · left
    obtain ⟨h1, h2⟩ := tr hW1 (irq_acc_own ar hA hK ⟨hE.inv, hE.lay, fun _ _ _ => rfl, hE.asid⟩ hE.ly hE.aff
      (fun hf => hF s1 a1 hf hr) hr)
    exact ⟨s1, a1, hr, h1, h2⟩
  · right
    obtain ⟨h1, h2⟩ := tr hW2 (irq_dec_guard ar hA hK (lk := lk) hE.inv hE.lay hE.ly hE.aff
      hE.nth hr)
    refine ⟨s1, a1, hr, h1, ?_⟩
    rw [eP] at h2 ⊢
    exact interp_mono hR1 (fun _ h => h) p hz s' a r' h2

/-- **`PathObl` for the timer interrupt** (module docstring), the fire case premises. -/
theorem irq_pathObl (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    {P : S → Prop} (hPE : ∀ s, P s → IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s)
    (hp : ∀ mm : machine.Store S, irqBody S irq pl ar mm = interp mm ar p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hkoF : ∀ s, P s → ∀ q, IrqDec st s q → ko q = .free)
    (hkoA : ∀ x, ko x ≠ .free → Aligned x)
    (hF : ∀ s a s1 a1, P s → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq pl = ok (true, s1, a1))
    (hmv : ∀ s a s1 a1, P s →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (mguard st
        (fun x y => StepOK (own K) cls ko User (L.cpu s) (lk s) (L.mem x) (L.mem y))) ar s a irq pl =
          ok (true, s1, a1)) :
    PathObl.PathObl st (fun mm s a => localtimer.handle_timer_irq_local mm ar s a irq pl) (fun b => b = true)
      (own K) cls ko User lk P (MaxR K st lk) (MaxW K st lk) (IrqDec st) := by
  have eP : ∀ (mm : machine.Store S) (x : S) (a : A),
      localtimer.handle_timer_irq_local mm ar x a irq pl = interp mm ar p x a :=
    fun mm x a => congrFun (congrFun (hp mm) x) a
  have hQ : ∀ s, P s → ∀ (x : S) (q v : U64), IrqDec st s q →
      StepOK (own K) cls ko User (L.cpu s) (lk s) (L.mem x) (L.mem (L.wr x q v)) := by
    intro s hE x q v hq
    obtain ⟨a1, -, c, hc⟩ := (hPE s hE).dec hq
    refine ⟨fun w hw => absurd (own_keep hK hUO a1 (Or.inl ⟨c, hc⟩) x v w) hw, fun w hw _ => ?_⟩
    by_cases hwq : w = q
    · subst hwq; exact Or.inr (Or.inr (hkoF s hE w hq))
    · by_cases hf : ko w = .free
      · exact Or.inr (Or.inr hf)
      · exact absurd (mem_wr_ne' a1 (hkoA w hf) (fun e => hwq e.symm)) hw
  have dec : ∀ s a r, P s →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok r → r.1 ≠ true →
      ∀ s' r', PathObl.Alt st (MaxR K st lk s) cls ko User s s' →
      localtimer.handle_timer_irq_local st ar s' a irq pl = ok r' →
      r'.1 ≠ true ∧
      localtimer.handle_timer_irq_local (guard st (fun _ => True) (IrqDec st s)) ar s' a irq pl = ok r' ∧
      localtimer.handle_timer_irq_local (mguard st
        (fun x y => StepOK (own K) cls ko User (L.cpu s) (lk s) (L.mem x) (L.mem y))) ar s' a irq pl = ok r' := by
    intro s a r hE hr hn s' r' hAlt h'
    rcases irq_alt ar hA hK hp hz hm (hPE s hE) (fun s1 a1 => hF s a s1 a1 hE)
      hAlt h' with ⟨s1, a1, e, -, -⟩ | ⟨s1, a1, -, h1, h2⟩
    · rw [hr] at e
      exact absurd (by rw [Result.ok_injective e]) hn
    · rw [eP] at h2
      refine ⟨by rw [h1]; exact Bool.false_ne_true, ?_, ?_⟩
      · rw [eP]; exact interp_mono (fun _ _ => trivial) (fun _ h => h) p hz s' a r' h2
      · rw [eP]; exact interp_to_mguard (fun x q v hq => hQ s hE x q v hq) p hz s' a r' h2
  refine ⟨?_, dec, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    have hE' := hPE s hE
    exact irq_acc_own ar hA hK ⟨hE'.inv, hE'.lay, fun _ _ _ => rfl, hE'.asid⟩ hE'.ly hE'.aff
      (fun hf => hF s a s1 a1 hE hf h) h
  · intro s x _ hx _; exact hx.1
  · intro s x hE hx _
    rcases hx with hx | hx
    · exact hx.1
    · exact held_core ((hPE s hE).dec hx).2.1
  · intro s x hE hx
    rcases hx with hx | hx
    · exact hx.2
    · exact ((hPE s hE).dec hx).1
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (dec s a _ hE h Bool.false_ne_true s _ (PathObl.Alt.refl s) h).2.2
    · exact hmv s a s1 a1 hE h

/-- **`PathSide` for the timer interrupt** (module docstring). -/
theorem irq_pathSide (hA : P0.ArchTotal ar) (hK : RegionOK K)
    {P : S → Prop} (hPE : ∀ s, P s → IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s)
    (hp : ∀ mm : machine.Store S, irqBody S irq pl ar mm = interp mm ar p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s) (hkoA : ∀ x, ko x ≠ .free → Aligned x)
    (hF : ∀ s a s1 a1, P s → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq pl = ok (true, s1, a1))
    (huf : ∀ s b v, P s → User b → Aligned b →
      P (L.wr s b v) ∧ lk (L.wr s b v) = lk s ∧
        MaxR K st lk (L.wr s b v) = MaxR K st lk s ∧ MaxW K st lk (L.wr s b v) = MaxW K st lk s ∧
        IrqDec st (L.wr s b v) = IrqDec st s) :
    PathObl.PathSide st (fun mm s a => localtimer.handle_timer_irq_local mm ar s a irq pl) cls ko User lk
      P (MaxR K st lk) (MaxW K st lk) (IrqDec st) := by
  refine ⟨?_, fun s x _ hx => hx.2, hkoA, huf⟩
  intro s s' a r hE hAlt h
  have eP : ∀ (mm : machine.Store S) (x : S),
      localtimer.handle_timer_irq_local mm ar x a irq pl = interp mm ar p x a :=
    fun mm x => congrFun (congrFun (hp mm) x) a
  rcases irq_alt ar hA hK hp hz hm (hPE s hE) (fun s1 a1 => hF s a s1 a1 hE)
    hAlt h with ⟨_, _, -, -, h2⟩ | ⟨_, _, -, -, h2⟩
  · show localtimer.handle_timer_irq_local _ ar s' a irq pl = ok r
    rw [eP] at h2 ⊢
    exact interp_mono (fun _ hw => hw.2) (fun _ _ => trivial) p hz s' a r h2
  · show localtimer.handle_timer_irq_local _ ar s' a irq pl = ok r
    rw [eP] at h2 ⊢
    exact interp_mono (fun _ hw => hw) (fun _ _ => trivial) p hz s' a r h2

/-- **The timer interrupt is a local path** (module docstring); `move` of accepted quiet / round-robin runs is
`irq_move_acc`, the fire case premises `hF` / `hFm`. -/
noncomputable def irq_localPath (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR K st lk))
    (hEU : ∀ s b v, IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ K.user → Aligned b →
      IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hF : ∀ s a s1 a1, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq pl = ok (true, s1, a1))
    (hFm : ∀ s a s1 a1, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (mguard st
        (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
          (L.mem y))) ar s a irq pl = ok (true, s1, a1)) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := irqBody S irq pl
  p := p
  Acc := fun b => b = true
  Locks := lk
  Pre := IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m
  RS := MaxR K st lk
  WS := MaxW K st lk
  DS := IrqDec st
  isProg := PathObl.IsProg.on hp _ _ _
  obl := irq_pathObl ar hA hK hUO (fun s h => h.ent) (fun mm => hp A ar mm) hz hm
    (fun s h q hq => irq_koF h.ent hq) (ko_aligned hK hUO) hF
    (fun s a s1 a1 hE h => irq_move_acc ar hA hK hUO hp hE.k (hFm s a s1 a1 hE · h) h)
  side := irq_pathSide ar hA hK (fun s h => h.ent) (fun mm => hp A ar mm) hz hm (ko_aligned hK hUO) hF
    (fun s b v h hb hba => by
      have keep : ∀ x, Aligned x → x ∉ K.user → L.mem (L.wr s b v) x = L.mem s x :=
        fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb))
      have eo : own K (L.mem (L.wr s b v)) = own K (L.mem s) :=
        E2E.ownDep hK hUO _ _ (fun x hx hxu => keep x hx hxu)
      refine ⟨⟨hEU s b v h.ent hb hba, fun x hx hxu => by rw [keep x hx hxu]; exact h.mem x hx hxu⟩,
        hlk s b v hb, ?_, ?_, irq_dec_user s b v⟩
      · funext w; simp only [MaxR, RPerm, GateOnly, eo, hlk s b v hb, L.cpu_wr]
      · funext w; simp only [MaxW, WPerm, eo, hlk s b v hb, L.cpu_wr])
  once := hro
  total := fun s a => by
    obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar s a irq pl LawfulStore.total hA)
    exact ⟨r, e⟩
  masks := hm

end

end Fl4Proofs.P2

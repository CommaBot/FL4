/-
# P2: `ReadOnce` of the timer interrupt tree (line hpzg, gen 4)

`irq_localPathG` (`P2/ProgGenTmLP.lean`) and p2lt2's `irq_pathsJ3` at the generated tree (`irq_pathsJ3G`,
`P2/ProgGenWire.lean`) left `hro` [W]: `E2E.ReadOnce` of `R.localtimer.handle_timer_irq_local irq pl` with
`RS = MaxR`. Since vlift's gen 3, `MaxR` excludes the user words (`w ∉ K.user`, carried by `irq_dec_guard` /
`irq_acc_own` and the fire-case guards), so no walk is needed:

* every run at an alternative is the entry's on the guard of `MaxR` (`irq_alt`'s argument, keeping the read set
  `MaxR` in the declining case, where `irq_alt` itself weakens it to `Aligned`): accepted by `irq_acc_own` (the fire
  case from `hF`), declined by `irq_dec_guard`; carried to the alternative by `interp_agree`;
* a run guarded on a read set without user words is `Once` (`once_of_guardG`).

* `irq_once_alt`: an alternative's run is `Once`, from `IrqEnt` at the entry and the fire-case guard `hF`;
* `irq_hro`: **`hro` of `irq_localPathG` holds** (its own `hF`); `irq_localPathG2`: the timer interrupt local
  path with `IsProg`, `NoZero` and `ReadOnce` discharged (premises: `irq_localPathG`'s minus `hro`);
* `irq_hroJ3`: **`hro` of `irq_pathsJ3` holds at every layout with `RegionOK` / `UserOK`**, the fire case from
  `irq_pathObl_J3`'s `acc` (`irq_acc_fire_nw` / `irq_acc_fire_wk2`, all from `SlJAt`); no premise beyond
  `irq_pathsJ3`'s own (`hA`, `hm` [P], `hPL` [P]);
* `irq_pathsJ3G2` / `irq_pathsJ3G2_startAt` / `irq_pathsKG2_startAt`: p2lt2's `irq_pathsJ3` and int13's
  `irq_pathsK_startAt` at the generated tree with `hp` [P], `hz` [W] and `hro` [W] all discharged. Premises:
  `hA`, `hm` [P] (`MasksWr`), `hlk` [P] (guarded lock contract), `hPL` [P] (`PlanLk`); `Fl4Step.start` [P]
  stays the glue's (`SlJAt K σ` and the memory agreement at the start state).
-/
import Fl4Proofs.P2.ProgGenWire
import Fl4Proofs.P2.OnceGuard
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner ClsOwner)
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.E2E (Once ReadOnce)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
variable {lk : S → U64 → Prop}

/-- **An alternative's run of the timer interrupt tree is `Once`** (module docstring). -/
theorem irq_once_alt (hA : P0.ArchTotal ar) (hK : RegionOK K) (hm : E2E.MasksWr st)
    {s s' : S} {a : A} (hE : IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s)
    (hF : ∀ s1 a1, IrqFire st ar s a → localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq pl = ok (true, s1, a1))
    (hAlt : Alt st (MaxR K st lk s) cls ko (· ∈ K.user) s s') :
    Once st ar (MaxR K st lk s) (· ∈ K.user) ∅ ∅ (R.localtimer.handle_timer_irq_local irq pl) s' a := by
  have hz := irq_noZero irq pl
  have eP : ∀ (mm : machine.Store S) (x : S),
      localtimer.handle_timer_irq_local mm ar x a irq pl = interp mm ar (R.localtimer.handle_timer_irq_local irq pl) x a :=
    fun mm x => congrFun (congrFun (irq_isProg S irq pl A ar mm) x) a
  have hR1 : ∀ w, MaxR K st lk s w → Aligned w := fun _ hw => hw.2.1
  have tr : ∀ {W' : U64 → Prop} {x : Bool} {s1 : S} {a1 : A}, (∀ w, W' w → Aligned w) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) W') ar s a irq pl = ok (x, s1, a1) →
      Once st ar (MaxR K st lk s) (· ∈ K.user) ∅ ∅ (R.localtimer.handle_timer_irq_local irq pl) s' a := by
    intro W' x s1 a1 hWa hg
    rw [eP] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm hR1 hWa _ hz s s' a x s1 a1 hAlt.ksb hAlt.cpu hAlt.masks hAlt.read hg
    exact once_of_guardG (User := (· ∈ K.user)) (fun q hq => hq.2.2) _ hz ∅ ∅ s' a _ hg'
  obtain ⟨r, hr⟩ : ∃ r, localtimer.handle_timer_irq_local st ar s a irq pl = ok r := by
    obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar s a irq pl LawfulStore.total hA)
    exact ⟨r, e⟩
  obtain ⟨b, s1, a1⟩ := r
  cases b
  · exact tr (W' := IrqDec st s) (fun _ hw => (hE.dec hw).1)
      (irq_dec_guard ar hA hK (lk := lk) hE.inv hE.lay hE.ly hE.aff hE.nth hr)
  · exact tr (W' := MaxW K st lk s) (fun _ hw => hw.2)
      (irq_acc_own ar hA hK ⟨hE.inv, hE.lay, fun _ _ _ => rfl, hE.asid⟩ hE.ly hE.aff (fun hf => hF s1 a1 hf hr) hr)

/-- **`hro` of `irq_localPathG` holds** (module docstring), given its fire-case premise `hF`. -/
theorem irq_hro (hA : P0.ArchTotal ar) (hK : RegionOK K) (hm : E2E.MasksWr st)
    (hF : ∀ s a s1 a1, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq pl = ok (true, s1, a1)) :
    ReadOnce st ar (R.localtimer.handle_timer_irq_local irq pl) (OwnMap.cls K) (OwnMap.ko K m)
      (· ∈ K.user) (IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m) (MaxR K st lk) :=
  fun s _ a _ hE hAlt _ => irq_once_alt ar hA hK hm hE.ent (fun s1 a1 => hF s a s1 a1 hE) hAlt

/-- **The timer interrupt local path with `IsProg`, `NoZero` and `ReadOnce` discharged** (module docstring):
`irq_localPathG` with `hro := irq_hro`. Premises: `hA`, `hK`, `hUO`, `hm` [P], `hEU` [J], `hlk` [P], `hF` / `hFm`
(the fire case). -/
noncomputable def irq_localPathG2 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hm : E2E.MasksWr st)
    (hEU : ∀ s b v, IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s → b ∈ K.user → Aligned b →
      IrqEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac irq (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hF : ∀ s a s1 a1, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq pl = ok (true, s1, a1))
    (hFm : ∀ s a s1 a1, IrqEntM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (PathObl.mguard st
        (fun x y => PathObl.StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
          (L.mem y))) ar s a irq pl = ok (true, s1, a1)) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  irq_localPathG ar hA hK hUO hm (irq_hro ar hA hK hm hF) hEU hlk hF hFm

/-- **`hro` of `irq_pathsJ3` holds** at a layout with `RegionOK` / `UserOK` (module docstring). -/
theorem irq_hroJ3 (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hPL : PlanLk lk pl)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hUO : E2E.UserOK K) :
    ReadOnce st ar (R.localtimer.handle_timer_irq_local irq pl) (OwnMap.cls K) (OwnMap.ko K m)
      (· ∈ K.user) (IrqPreJ3 K st m) (MaxR K st lk) := by
  intro s s' a _ hP hAlt _
  obtain ⟨Ω, Ac, hE⟩ := hP.entM (irq := irq)
  have O := irq_pathObl_J3 ar hA hK hUO (irq_isProg S irq pl) (irq_noZero irq pl) hm hPL hP
  exact irq_once_alt ar hA hK hm hE.ent (fun s1 a1 _ h1 => O.acc s a (true, s1, a1) rfl h1 rfl) hAlt

end

/-! ## The timer interrupt path member, program premises all discharged -/

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (irq : U64) {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}
open Fl4Proofs.P2.PathObl (SlJAt IrqPreK irqPreK_of_chain)

/-- **p2lt2's `irq_pathsJ3` at the generated tree with `hp`, `hz` and `hro` discharged** (module docstring).
Premises: `hA`, `hm` [P], `hlk` [P], `hPL` [P]. -/
noncomputable def irq_pathsJ3G2 (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)
    (hlk : ∀ (K : KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) : E2E.Paths Unit :=
  fun _ K m hK hU =>
    irq_localPathJ3 (K := K) (m := m) ar hA hK hU (irq_isProg S irq pl) (irq_noZero irq pl) hm
      (irq_hroJ3 ar hA hm hPL K m hK hU) (hlk K) hPL

/-- **`StartAt` for `irq_pathsJ3G2`**: `SlJAt K σ` and the memory agreement at the start state. -/
theorem irq_pathsJ3G2_startAt (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)
    (hlk : ∀ (K : KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hM : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (irq_pathsJ3G2 ar irq hA hm hlk hPL () K m hK hU) c hs μ
      ((irq_pathsJ3G2 ar irq hA hm hlk hPL () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨hJ, hM⟩, hc, hl, hμ, rfl⟩

/-- **int13's `irq_pathsK_startAt` for `irq_pathsJ3G2`**: every state of a chain carrying `SlJAt K`
(`loc_chain_all`'s clause 7 as `h7`) agreeing with `m` off the user words is a start. -/
theorem irq_pathsKG2_startAt {A3 : Type} {Rc : S → A3 → Fl4Spec.State Unit → Prop}
    (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)
    (hlk : ∀ (K : KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), Rc σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : Rc σ a3 τ) (a : A)
    (hM : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (irq_pathsJ3G2 ar irq hA hm hlk hPL () K m hK hU) c hs μ
      ((irq_pathsJ3G2 ar irq hA hm hlk hPL () K m hK hU).body σ a) :=
  have h : IrqPreK K st m σ := irqPreK_of_chain h7 hR hM
  irq_pathsJ3G2_startAt ar irq hA hm hlk hPL K m hK hU a h.1 h.2 hc hl hμ

end paths

end Fl4Proofs.P2

/-! ## Frames -/

theorem gkb_of_fk {α : Type} {m : NonDet (State Unit) α} (h : FK vw m) : GKB m :=
  fun _ L σ hP x hx => L.view σ x.2 (h σ x hx) hP

theorem vw_of_msFT {σ σ' : State Unit} (h : msFT σ' = msFT σ) : vw σ' = vw σ := by
  unfold msFT msF at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨⟨h1, -, -, h4, h5⟩, h6⟩ := h
  unfold vw; rw [h1, h4, h5, h6]

theorem gkb_of_mtk {α : Type} {m : NonDet (State Unit) α} (h : MTK m) : GKB m :=
  gkb_of_fk fun σ x hx => vw_of_msFT (h σ x hx)

theorem gkbe_of_mtke {ε α : Type} {m : NonDetE (State Unit) ε α} (h : MTKE m) : GKBE m :=
  gkb_of_mtk h

/-! ## Combinators -/

section Comb

theorem gkb_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : GKB m)
    (hg : ∀ a, GKB (g a)) : GKB (m >>= g) := by
  intro P L σ h x ⟨y, hy, hx⟩
  exact hg y.1 P L y.2 (hm P L σ h y hy) x hx

theorem gkb_bind' {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : GKB m)
    (hg : ∀ a, GKB (g a)) : GKB (NonDet.bind m g) := gkb_bind hm hg

theorem gkb_pure {α : Type} (a : α) : GKB (pure a : NonDet (State Unit) α) := gkb_of_fk (dk_pure a)

theorem gkb_pure' {α : Type} (a : α) : GKB (NonDet.pure a : NonDet (State Unit) α) := gkb_of_fk (dk_pure a)

theorem gkb_gets {α : Type} (g : State Unit → α) : GKB (NonDet.gets g) := gkb_of_fk (dk_gets g)

theorem gkb_get : GKB (NonDet.get : NonDet (State Unit) (State Unit)) := gkb_of_fk dk_get

theorem gkb_assert (P : Prop) : GKB (NonDet.assert P : NonDet (State Unit) Unit) := gkb_of_fk (dk_assert P)

theorem gkb_fail {α : Type} : GKB (NonDet.fail : NonDet (State Unit) α) := gkb_of_fk dk_fail

theorem gkb_assertOpt {α : Type} (o : Option α) : GKB (NonDet.assertOpt o : NonDet (State Unit) α) :=
  gkb_of_fk (dk_assertOpt o)

theorem gkb_getsThe {α : Type} (g : State Unit → Option α) : GKB (NonDet.getsThe g) := gkb_of_fk (dk_getsThe g)

theorem gkb_selectF {α : Type} (S : Set α × Prop) : GKB (NonDet.selectF S : NonDet (State Unit) α) :=
  gkb_of_fk (dk_selectF S)

theorem gkb_select {α : Type} (S : Set α) : GKB (NonDet.select S : NonDet (State Unit) α) := gkb_of_fk (dk_select S)

theorem gkb_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α} (h1 : GKB m1)
    (h2 : GKB m2) : GKB (if Q then m1 else m2) := by
  split <;> assumption

theorem gkb_when (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : GKB m) : GKB (NonDet.when Q m) := by
  unfold NonDet.when; exact gkb_ite Q h (gkb_pure' _)

theorem gkb_unless (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : GKB m) :
    GKB (NonDet.unless Q m) := by
  unfold NonDet.unless; exact gkb_ite Q (gkb_pure' _) h

theorem gkb_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, GKB (g a)) (o : Option α) :
    GKB (NonDet.maybeM g o) := by
  cases o
  · exact gkb_pure' _
  · exact h _

theorem gkb_liftM {α γ : Type} (g : α → γ) {m : NonDet (State Unit) α} (h : GKB m) : GKB (NonDet.liftM g m) :=
  gkb_bind' h fun _ => gkb_pure' _

theorem gkb_modify {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) : GKB (NonDet.modify g) :=
  gkb_of_fk (dk_modify hg)

theorem gkb_get_put {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) :
    GKB (NonDet.get >>= fun s => NonDet.put (g s)) := gkb_of_fk (dk_get_put hg)

theorem gkb_get_put' {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) :
    GKB (do let s ← NonDet.get; NonDet.put (g s)) := gkb_get_put hg

theorem gkb_getObject (p : ObjRef) : GKB (getObject (Z := Unit) p) := gkb_getsThe _

theorem gkb_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, GKB (B r)) (r : α) : GKB (NonDet.whileLoop C B r) := by
  intro P L σ h x hx
  induction hx with
  | done _ => exact h
  | step _ hm _ ih => exact ih (hB _ P L _ h _ hm)

theorem gkb_mapMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GKB (g a)) (xs : List α) :
    GKB (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact gkb_pure' _
  | cons a xs' ih => exact gkb_bind' (h a) fun _ => ih

theorem gkb_forMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GKB (g a)) (xs : List α) :
    GKB (NonDet.forMx xs g) := gkb_mapMx h xs

theorem gkb_mapM {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GKB (g a)) (xs : List α) :
    GKB (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact gkb_pure' _
  | cons a xs' ih => exact gkb_bind' (h a) fun _ => gkb_bind' ih fun _ => gkb_pure' _

end Comb

section CombE
variable {ε : Type}

theorem gkbe_bind {α γ : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε γ} (hm : GKBE m)
    (hg : ∀ a, GKBE (g a)) : GKBE (m >>= g) := by
  unfold GKBE; rw [ExceptT.run_bind]
  refine gkb_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact gkb_pure _

theorem gkbe_pure {α : Type} (a : α) : GKBE (pure a : NonDetE (State Unit) ε α) := gkb_pure _

theorem gkbe_returnOk {α : Type} (a : α) : GKBE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := gkb_pure _

theorem gkbe_throw {α : Type} (e : ε) : GKBE (NonDetE.throwError e : NonDetE (State Unit) ε α) := gkb_pure _

theorem gkbe_throw' {α : Type} (e : ε) : GKBE (throw e : NonDetE (State Unit) ε α) := gkb_pure _

theorem gkbe_liftE {α : Type} {m : NonDet (State Unit) α} (h : GKB m) : GKBE (NonDetE.liftE (ε := ε) m) := by
  unfold GKBE NonDetE.liftE; rw [ExceptT.run_lift]
  exact gkb_bind h fun _ => gkb_pure _

theorem gkbe_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDetE (State Unit) ε α} (h1 : GKBE m1)
    (h2 : GKBE m2) : GKBE (if Q then m1 else m2) := by
  split <;> assumption

theorem gkbe_whenE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : GKBE m) :
    GKBE (NonDetE.whenE Q m) := by
  unfold NonDetE.whenE; exact gkbe_ite Q h (gkbe_pure _)

theorem gkbe_unlessE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : GKBE m) :
    GKBE (NonDetE.unlessE Q m) := by
  unfold NonDetE.unlessE; exact gkbe_ite Q (gkbe_pure _) h

theorem gkbe_throwOpt {α : Type} (e : ε) (o : Option α) : GKBE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact gkbe_throw' e
  · exact gkbe_pure _

theorem gkbe_assertE (Q : Prop) : GKBE (NonDetE.assertE Q : NonDetE (State Unit) ε Unit) :=
  gkbe_liftE (gkb_assert Q)

theorem gkb_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : GKBE m)
    (hh : ∀ e, GKB (h e)) : GKB (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine gkb_bind' hm fun r => ?_
  cases r with
  | ok a => exact gkb_pure' _
  | error e => exact hh e

theorem gkbe_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : GKBE m) (hh : ∀ e, GKBE (h e)) : GKBE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE GKBE
  rw [ExceptT.run_mk]
  refine gkb_bind' hm fun r => ?_
  cases r with
  | ok a => exact gkb_pure' _
  | error e => exact hh e

theorem gkbe_liftME {α γ : Type} (g : α → γ) {m : NonDetE (State Unit) ε α} (h : GKBE m) :
    GKBE (NonDetE.liftME g m) := by
  unfold NonDetE.liftME; exact gkbe_bind h fun _ => gkbe_pure _

theorem gkbe_mapMEx {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, GKBE (F a)) :
    ∀ xs : List α, GKBE (NonDetE.mapMEx F xs)
  | [] => by unfold NonDetE.mapMEx; exact gkbe_pure _
  | a :: xs => by unfold NonDetE.mapMEx; exact gkbe_bind (h a) fun _ => gkbe_mapMEx h xs

theorem gkbe_mapME {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, GKBE (F a)) :
    ∀ xs : List α, GKBE (NonDetE.mapME F xs)
  | [] => by unfold NonDetE.mapME; exact gkbe_pure _
  | a :: xs => by
    unfold NonDetE.mapME; exact gkbe_bind (h a) fun _ => gkbe_bind (gkbe_mapME h xs) fun _ => gkbe_pure _

theorem gkbe_withoutPreemption {α : Type} {m : SMonad Unit α} (h : GKB m) :
    GKBE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact gkbe_liftE h

theorem gkbe_capFaultOnFailure {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : GKBE m) :
    GKBE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact gkbe_handleE h fun _ => gkbe_throw _

theorem gkbe_lookupErrorOnFailure {α : Type} (b : Bool) {m : LFMonad Unit α} (h : GKBE m) :
    GKBE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact gkbe_handleE h fun _ => gkbe_throw _

theorem gkbe_unifyFailure {F α : Type} {m : NonDetE (State Unit) F α} (h : GKBE m) :
    GKBE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact gkbe_handleE h fun _ => gkbe_throw _

theorem gkb_emptyOnFailure {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : GKBE m) :
    GKB (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact gkb_catch h fun _ => gkb_pure' _

theorem gkb_constOnFailure {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : GKBE m) :
    GKB (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact gkb_catch h fun _ => gkb_pure' _

end CombE

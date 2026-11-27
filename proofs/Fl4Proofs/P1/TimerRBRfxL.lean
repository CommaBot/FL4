/-
P1 (jc6d, TIMER-RB-PLAN stage 7, the loop): one round of `remove_fixup` (`rf_body`, by the side of `x` and
the colours of the sibling and nephews, see `TimerRBRfx`), the loop (`timer.remove_fixup_loop.rb`, measure =
fuel, the `fuel = 0` exit refuted by the path-length bound) and **`timer.remove_fixup.rb`**.
-/
import Fl4Proofs.P1.TimerRBRfx
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- After the optional case 1, `x` on the left: cases 2, 3, 4. -/
theorem rf_tailL {s0 s1 : S} {c : U64} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {tx : TRB.RBT} {pk w1 f1 f : U64} {n : Nat} (htx : TRB.Bal tx n)
    (hC : RfC2L st T s0 c Ks tx pk n f1.val s1 w1) (hlt : f1.val < f.val) :
    (do
      let t2 ← timer.left st s1 w1
      let b5 ← timer.is_red st s1 t2
      if b5
      then
        let t3 ← timer.right st s1 w1
        let b6 ← timer.is_red st s1 t3
        let (s2, w2) ←
          if b6
          then ok (s1, w1)
          else
            do
            let s3 ← timer.set_red st s1 t2 false
            let s4 ← timer.set_red st s3 w1 true
            let s5 ← timer.rotate_right st s4 c w1
            let w3 ← timer.right st s5 pk
            ok (s5, w3)
        let pr ← timer.is_red st s2 pk
        let s3 ← timer.set_red st s2 w2 pr
        let s4 ← timer.set_red st s3 pk false
        let wr ← timer.right st s4 w2
        let s5 ← timer.set_red st s4 wr false
        let s6 ← timer.rotate_left st s5 c pk
        let x1 ← timer.root st s6 c
        ok (ControlFlow.cont (s6, x1, 0#u64, f1))
      else
        let t3 ← timer.right st s1 w1
        let b6 ← timer.is_red st s1 t3
        if b6
        then
          let b7 ← timer.is_red st s1 t3
          let (s2, w2) ←
            if b7
            then ok (s1, w1)
            else
              do
              let s3 ← timer.set_red st s1 t2 false
              let s4 ← timer.set_red st s3 w1 true
              let s5 ← timer.rotate_right st s4 c w1
              let w3 ← timer.right st s5 pk
              ok (s5, w3)
          let pr ← timer.is_red st s2 pk
          let s3 ← timer.set_red st s2 w2 pr
          let s4 ← timer.set_red st s3 pk false
          let wr ← timer.right st s4 w2
          let s5 ← timer.set_red st s4 wr false
          let s6 ← timer.rotate_left st s5 c pk
          let x1 ← timer.root st s6 c
          ok (ControlFlow.cont (s6, x1, 0#u64, f1))
        else
          let s2 ← timer.set_red st s1 w1 true
          let p1 ← timer.parent st s2 pk
          ok (ControlFlow.cont (s2, pk, p1, f1))) ⦃ r => RfPost st T s0 c Ks f r ⦄ := by
  obtain ⟨up, cp, wl, wr, h, hwl, hwr, hU, hf⟩ := hC
  have hp1 : TRB.Rep (lk st s1) up.par pk (.node cp tx pk (.node false wl w1 wr)) :=
    ((TRB.rep_plug up _).1 h.rep).2
  have pk0 : pk ≠ 0#u64 := TRB.Rep.keys_ne0 hp1 pk (by simp [TRB.RBT.keys])
  have hw : TRB.Rep (lk st s1) pk w1 (.node false wl w1 wr) := ((TRB.rep_plug (.rc cp tx pk up) _).1 h.rep).2
  have hwlr : TRB.Rep (lk st s1) w1 wl.rootKey wl :=
    ((TRB.rep_plug (.lc false w1 wr (.rc cp tx pk up)) wl).1 h.rep).2
  have hwrr : TRB.Rep (lk st s1) w1 wr.rootKey wr :=
    ((TRB.rep_plug (.rc false wl w1 (.rc cp tx pk up)) wr).1 h.rep).2
  step with timer.left.rep s1 hw as ⟨t2, et2⟩
  replace et2 : t2 = wl.rootKey := et2
  subst t2
  step with timer.is_red.rep s1 hwlr as ⟨b5, eb5⟩
  split
  · rename_i hb5
    step with timer.right.rep s1 hw as ⟨t3, et3⟩
    replace et3 : t3 = wr.rootKey := et3
    subst t3
    step with timer.is_red.rep s1 hwrr as ⟨b6, eb6⟩
    refine WP.spec_bind (Pₘ := fun x => RfC4L st T s0 c Ks tx pk n x.1 x.2) ?_ ?_
    · split
      · rename_i hb6
        cases wr with
        | leaf => exfalso; rw [eb6] at hb6; exact absurd hb6 (by simp [TRB.RBT.isRed])
        | node cw c1 k2 d1 =>
          have e : cw = true := by rw [eb6] at hb6; exact hb6
          subst e
          cases hwr with
          | red hc1 hd1 _ _ => exact (WP.spec_ok _).2 ⟨up, cp, wl, c1, k2, d1, h, hwl, hc1, hd1, hU⟩
      · rename_i hb6
        have hwrb : wr.isRed = false := by rw [eb6] at hb6; simpa using hb6
        cases wl with
        | leaf => exfalso; rw [eb5] at hb5; exact absurd hb5 (by simp [TRB.RBT.isRed])
        | node cl a1 k1 b1 =>
          have e : cl = true := by rw [eb5] at hb5; exact hb5
          subst e
          cases hwl with
          | red ha hb _ hbb => exact rf_c3L hT hd hk h ha hb hbb hwr hwrb hU
    · rintro ⟨s2, w2⟩ hC4
      exact rf_c4L hT hd hk htx hC4 hlt
  · rename_i hb5
    have hwlb : wl.isRed = false := by rw [eb5] at hb5; simpa using hb5
    step with timer.right.rep s1 hw as ⟨t3, et3⟩
    replace et3 : t3 = wr.rootKey := et3
    subst t3
    step with timer.is_red.rep s1 hwrr as ⟨b6, eb6⟩
    split
    · rename_i hb6
      step with timer.is_red.rep s1 hwrr as ⟨b7, eb7⟩
      refine WP.spec_bind (Pₘ := fun x => RfC4L st T s0 c Ks tx pk n x.1 x.2) ?_ ?_
      · rw [if_pos (by rw [eb7, ← eb6]; exact hb6)]
        cases wr with
        | leaf => exfalso; rw [eb6] at hb6; exact absurd hb6 (by simp [TRB.RBT.isRed])
        | node cw c1 k2 d1 =>
          have e : cw = true := by rw [eb6] at hb6; exact hb6
          subst e
          cases hwr with
          | red hc1 hd1 _ _ => exact (WP.spec_ok _).2 ⟨up, cp, wl, c1, k2, d1, h, hwl, hc1, hd1, hU⟩
      · rintro ⟨s2, w2⟩ hC4
        exact rf_c4L hT hd hk htx hC4 hlt
    · rename_i hb6
      have hwrb : wr.isRed = false := by rw [eb6] at hb6; simpa using hb6
      step with FB.set_red (.rc cp tx pk up) false wl w1 wr hT hd hk h true as ⟨s2, h2⟩
      have hp2 : TRB.Rep (lk st s2) up.par pk (.node cp tx pk (.node true wl w1 wr)) :=
        ((TRB.rep_plug up _).1 h2.rep).2
      step with timer.parent.rep s2 hp2 as ⟨p1, ep1⟩
      rw [if_neg pk0] at ep1
      subst p1
      try simp only [WP.spec_ok]
      exact ⟨⟨_, h2, Or.inl (TRB.rf_case2L htx hwl hwr hwlb hwrb hU hf)⟩, hlt⟩

/-- After the optional case 1, `x` on the right: cases 2, 3, 4. -/
theorem rf_tailR {s0 s1 : S} {c : U64} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {tx : TRB.RBT} {pk w1 f1 f : U64} {n : Nat} (htx : TRB.Bal tx n)
    (hC : RfC2R st T s0 c Ks tx pk n f1.val s1 w1) (hlt : f1.val < f.val) :
    (do
      let t2 ← timer.left st s1 w1
      let b5 ← timer.is_red st s1 t2
      if b5
      then
        let b6 ← timer.is_red st s1 t2
        let (s2, w2) ←
          if b6
          then ok (s1, w1)
          else
            do
            let wr ← timer.right st s1 w1
            let s3 ← timer.set_red st s1 wr false
            let s4 ← timer.set_red st s3 w1 true
            let s5 ← timer.rotate_left st s4 c w1
            let w3 ← timer.left st s5 pk
            ok (s5, w3)
        let pr ← timer.is_red st s2 pk
        let s3 ← timer.set_red st s2 w2 pr
        let s4 ← timer.set_red st s3 pk false
        let wl ← timer.left st s4 w2
        let s5 ← timer.set_red st s4 wl false
        let s6 ← timer.rotate_right st s5 c pk
        let x1 ← timer.root st s6 c
        ok (ControlFlow.cont (s6, x1, 0#u64, f1))
      else
        let t3 ← timer.right st s1 w1
        let b6 ← timer.is_red st s1 t3
        if b6
        then
          let b7 ← timer.is_red st s1 t2
          let (s2, w2) ←
            if b7
            then ok (s1, w1)
            else
              do
              let s3 ← timer.set_red st s1 t3 false
              let s4 ← timer.set_red st s3 w1 true
              let s5 ← timer.rotate_left st s4 c w1
              let w3 ← timer.left st s5 pk
              ok (s5, w3)
          let pr ← timer.is_red st s2 pk
          let s3 ← timer.set_red st s2 w2 pr
          let s4 ← timer.set_red st s3 pk false
          let wl ← timer.left st s4 w2
          let s5 ← timer.set_red st s4 wl false
          let s6 ← timer.rotate_right st s5 c pk
          let x1 ← timer.root st s6 c
          ok (ControlFlow.cont (s6, x1, 0#u64, f1))
        else
          let s2 ← timer.set_red st s1 w1 true
          let p1 ← timer.parent st s2 pk
          ok (ControlFlow.cont (s2, pk, p1, f1))) ⦃ r => RfPost st T s0 c Ks f r ⦄ := by
  obtain ⟨up, cp, wl, wr, h, hwl, hwr, hU, hf⟩ := hC
  have hp1 : TRB.Rep (lk st s1) up.par pk (.node cp (.node false wl w1 wr) pk tx) :=
    ((TRB.rep_plug up _).1 h.rep).2
  have pk0 : pk ≠ 0#u64 := TRB.Rep.keys_ne0 hp1 pk (by simp [TRB.RBT.keys])
  have hw : TRB.Rep (lk st s1) pk w1 (.node false wl w1 wr) := ((TRB.rep_plug (.lc cp pk tx up) _).1 h.rep).2
  have hwlr : TRB.Rep (lk st s1) w1 wl.rootKey wl :=
    ((TRB.rep_plug (.lc false w1 wr (.lc cp pk tx up)) wl).1 h.rep).2
  have hwrr : TRB.Rep (lk st s1) w1 wr.rootKey wr :=
    ((TRB.rep_plug (.rc false wl w1 (.lc cp pk tx up)) wr).1 h.rep).2
  step with timer.left.rep s1 hw as ⟨t2, et2⟩
  replace et2 : t2 = wl.rootKey := et2
  subst t2
  step with timer.is_red.rep s1 hwlr as ⟨b5, eb5⟩
  split
  · rename_i hb5
    step with timer.is_red.rep s1 hwlr as ⟨b6, eb6⟩
    refine WP.spec_bind (Pₘ := fun x => RfC4R st T s0 c Ks tx pk n x.1 x.2) ?_ ?_
    · rw [if_pos (by rw [eb6, ← eb5]; exact hb5)]
      cases wl with
      | leaf => exfalso; rw [eb5] at hb5; exact absurd hb5 (by simp [TRB.RBT.isRed])
      | node cw c1 k2 d1 =>
        have e : cw = true := by rw [eb5] at hb5; exact hb5
        subst e
        cases hwl with
        | red hc1 hd1 _ _ => exact (WP.spec_ok _).2 ⟨up, cp, wr, c1, k2, d1, h, hwr, hc1, hd1, hU⟩
    · rintro ⟨s2, w2⟩ hC4
      exact rf_c4R hT hd hk htx hC4 hlt
  · rename_i hb5
    have hwlb : wl.isRed = false := by rw [eb5] at hb5; simpa using hb5
    step with timer.right.rep s1 hw as ⟨t3, et3⟩
    replace et3 : t3 = wr.rootKey := et3
    subst t3
    step with timer.is_red.rep s1 hwrr as ⟨b6, eb6⟩
    split
    · rename_i hb6
      step with timer.is_red.rep s1 hwlr as ⟨b7, eb7⟩
      refine WP.spec_bind (Pₘ := fun x => RfC4R st T s0 c Ks tx pk n x.1 x.2) ?_ ?_
      · rw [if_neg (by rw [eb7, hwlb]; simp)]
        cases wr with
        | leaf => exfalso; rw [eb6] at hb6; exact absurd hb6 (by simp [TRB.RBT.isRed])
        | node cw a1 k1 b1 =>
          have e : cw = true := by rw [eb6] at hb6; exact hb6
          subst e
          cases hwr with
          | red ha hb hab _ => exact rf_c3R hT hd hk h ha hab hb hwl hwlb hU
      · rintro ⟨s2, w2⟩ hC4
        exact rf_c4R hT hd hk htx hC4 hlt
    · rename_i hb6
      have hwrb : wr.isRed = false := by rw [eb6] at hb6; simpa using hb6
      step with FB.set_red (.lc cp pk tx up) false wl w1 wr hT hd hk h true as ⟨s2, h2⟩
      have hp2 : TRB.Rep (lk st s2) up.par pk (.node cp (.node true wl w1 wr) pk tx) :=
        ((TRB.rep_plug up _).1 h2.rep).2
      step with timer.parent.rep s2 hp2 as ⟨p1, ep1⟩
      rw [if_neg pk0] at ep1
      subst p1
      try simp only [WP.spec_ok]
      exact ⟨⟨_, h2, Or.inl (TRB.rf_case2R htx hwl hwr hwlb hwrb hU hf)⟩, hlt⟩

/-- A round with a black `x` that is a left child. -/
theorem rf_body_L (s : S) (c f : U64) {s0 : S} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {up : TRB.Ctx} {cp : Bool} {S0 tx : TRB.RBT} {pk : U64} {n : Nat}
    (h : FB st T s0 c Ks s (up.plug (.node cp tx pk S0))) (htx : TRB.Bal tx n) (htb : tx.isRed = false)
    (hS : TRB.Bal S0 (n + 1)) (hSb : cp = true → S0.isRed = false) (hU : TRB.UpOK up cp n)
    (hf : up.depth + 1 ≤ f.val) :
    timer.remove_fixup_loop.body st c s tx.rootKey pk f ⦃ r => RfPost st T s0 c Ks f r ⦄ := by
  have hW := h.nd hd
  have hxr : TRB.Rep (lk st s) pk tx.rootKey tx := ((TRB.rep_plug (.lc cp pk S0 up) tx).1 h.rep).2
  have hpr : TRB.Rep (lk st s) up.par pk (.node cp tx pk S0) := ((TRB.rep_plug up _).1 h.rep).2
  have hSr : TRB.Rep (lk st s) pk S0.rootKey S0 := ((TRB.rep_plug (.rc cp tx pk up) S0).1 h.rep).2
  have pk0 : pk ≠ 0#u64 := TRB.Rep.keys_ne0 hpr pk (by simp [TRB.RBT.keys])
  have hxR := TRB.x_ne_root (ctx := .lc cp pk S0 up) h.rep hW (by intro e; cases e)
  have hf0 : 0 < f.val := by omega
  unfold timer.remove_fixup_loop.body
  step with timer.root.val (st := st) s c as ⟨t, et⟩
  subst t
  step with tcb_ne.blk as ⟨b, hb⟩
  rw [if_pos (hb.2 hxR)]
  step with timer.is_red.rep s hxr as ⟨b1, hb1⟩
  rw [if_neg (by rw [hb1, htb]; simp)]
  step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
  rw [if_neg (by rw [ebn]; simpa using pk0)]
  split
  swap
  · rename_i hf0'; exfalso; have : f.val = 0 := by scalar_tac
    omega
  step as ⟨f1, hf1⟩
  have hf1' : f1.val = f.val - 1 := by clear * - hf1 hf0; scalar_tac
  have hlt : f1.val < f.val := by omega
  step with timer.left.rep s hpr as ⟨t1, et1⟩
  replace et1 : t1 = tx.rootKey := et1
  subst t1
  step with tcb_eq.iff as ⟨b3, hb3⟩
  rw [if_pos (hb3.2 trivial)]
  step with timer.right.rep s hpr as ⟨w, ew⟩
  replace ew : w = S0.rootKey := ew
  subst w
  step with timer.is_red.rep s hSr as ⟨b4, eb4⟩
  cases S0 with
  | leaf => cases hS
  | node cw wl w wr =>
  refine WP.spec_bind (Pₘ := fun x => RfC2L st T s0 c Ks tx pk n f1.val x.1 x.2) ?_ ?_
  · cases cw with
    | true =>
      rw [if_pos (by rw [eb4]; rfl)]
      cases cp with
      | true => exact absurd (hSb rfl) (by simp [TRB.RBT.isRed])
      | false =>
      cases hS with
      | red hwl hwr bl _ =>
      simp only [TRB.RBT.rootKey]
      step with FB.set_red (.rc false tx pk up) true wl w wr hT hd hk h false as ⟨s2, h2⟩
      step with FB.set_red up false tx pk (.node false wl w wr) hT hd hk h2 true as ⟨s3, h3⟩
      step with FB.rotL up true tx pk false wl w wr hT hd hk h3 as ⟨s4, h4⟩
      have hp4 : TRB.Rep (lk st s4) w pk (.node true tx pk wl) :=
        ((TRB.rep_plug (.lc false w wr up) (.node true tx pk wl)).1 h4.rep).2
      step with timer.right.rep s4 hp4 as ⟨w2, ew2⟩
      replace ew2 : w2 = wl.rootKey := ew2
      subst w2
      cases wl with
      | leaf => cases hwl
      | node cl wl1 wk wl2 =>
      cases cl with
      | true => simp [TRB.RBT.isRed] at bl
      | false =>
      cases hwl with
      | black h1 h2' =>
      try simp only [WP.spec_ok]
      exact ⟨.lc false w wr up, true, wl1, wl2, h4, h1, h2', TRB.UpOK.pushL hU hwr, Or.inl rfl⟩
    | false =>
      rw [if_neg (by rw [eb4]; simp [TRB.RBT.isRed])]
      cases hS with
      | black hwl hwr =>
      exact (WP.spec_ok _).2 ⟨up, cp, wl, wr, h, hwl, hwr, hU, Or.inr (by omega)⟩
  · rintro ⟨s1, w1⟩ hC
    exact rf_tailL hT hd hk htx hC hlt

/-- A round with a black `x` that is a right child (`x` may be null: the sibling is not). -/
theorem rf_body_R (s : S) (c f : U64) {s0 : S} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) {up : TRB.Ctx} {cp : Bool} {S0 tx : TRB.RBT} {pk : U64} {n : Nat}
    (h : FB st T s0 c Ks s (up.plug (.node cp S0 pk tx))) (htx : TRB.Bal tx n) (htb : tx.isRed = false)
    (hS : TRB.Bal S0 (n + 1)) (hSb : cp = true → S0.isRed = false) (hU : TRB.UpOK up cp n)
    (hf : up.depth + 1 ≤ f.val) :
    timer.remove_fixup_loop.body st c s tx.rootKey pk f ⦃ r => RfPost st T s0 c Ks f r ⦄ := by
  have hW := h.nd hd
  have hxr : TRB.Rep (lk st s) pk tx.rootKey tx := ((TRB.rep_plug (.rc cp S0 pk up) tx).1 h.rep).2
  have hpr : TRB.Rep (lk st s) up.par pk (.node cp S0 pk tx) := ((TRB.rep_plug up _).1 h.rep).2
  have hSr : TRB.Rep (lk st s) pk S0.rootKey S0 := ((TRB.rep_plug (.lc cp pk tx up) S0).1 h.rep).2
  have pk0 : pk ≠ 0#u64 := TRB.Rep.keys_ne0 hpr pk (by simp [TRB.RBT.keys])
  have hxR := TRB.x_ne_root (ctx := .rc cp S0 pk up) h.rep hW (by intro e; cases e)
  have hf0 : 0 < f.val := by omega
  cases S0 with
  | leaf => cases hS
  | node cw wl w wr =>
  have w0 : w ≠ 0#u64 := TRB.Rep.keys_ne0 hSr w (by simp [TRB.RBT.keys])
  have hSr' : TRB.Rep (lk st s) pk w (.node cw wl w wr) := hSr
  have hxw : tx.rootKey ≠ w := by
    by_cases x0 : tx.rootKey = 0#u64
    · rw [x0]; exact fun e => w0 e.symm
    · exact TRB.ne_rootL (ctx := up) (c := cp) (a := .node cw wl w wr) (b := tx) (k := pk) hW
        (Or.inl ((tx.rootKey_mem).resolve_left x0)) x0
  unfold timer.remove_fixup_loop.body
  step with timer.root.val (st := st) s c as ⟨t, et⟩
  subst t
  step with tcb_ne.blk as ⟨b, hb⟩
  rw [if_pos (hb.2 hxR)]
  step with timer.is_red.rep s hxr as ⟨b1, hb1⟩
  rw [if_neg (by rw [hb1, htb]; simp)]
  step with obj.Tcb.is_null.spec as ⟨bn, ebn⟩
  rw [if_neg (by rw [ebn]; simpa using pk0)]
  split
  swap
  · rename_i hf0'; exfalso; have : f.val = 0 := by scalar_tac
    omega
  step as ⟨f1, hf1⟩
  have hf1' : f1.val = f.val - 1 := by clear * - hf1 hf0; scalar_tac
  have hlt : f1.val < f.val := by omega
  step with timer.left.rep s hpr as ⟨t1, et1⟩
  replace et1 : t1 = w := et1
  subst t1
  step with tcb_eq.iff as ⟨b3, hb3⟩
  rw [if_neg (fun e => hxw (hb3.1 e))]
  step with timer.is_red.rep s hSr' as ⟨b4, eb4⟩
  refine WP.spec_bind (Pₘ := fun x => RfC2R st T s0 c Ks tx pk n f1.val x.1 x.2) ?_ ?_
  · cases cw with
    | true =>
      rw [if_pos (by rw [eb4]; rfl)]
      cases cp with
      | true => exact absurd (hSb rfl) (by simp [TRB.RBT.isRed])
      | false =>
      cases hS with
      | red hwl hwr _ br =>
      step with FB.set_red (.lc false pk tx up) true wl w wr hT hd hk h false as ⟨s2, h2⟩
      step with FB.set_red up false (.node false wl w wr) pk tx hT hd hk h2 true as ⟨s3, h3⟩
      step with FB.rotR up true false wl w wr pk tx hT hd hk h3 as ⟨s4, h4⟩
      have hp4 : TRB.Rep (lk st s4) w pk (.node true wr pk tx) :=
        ((TRB.rep_plug (.rc false wl w up) (.node true wr pk tx)).1 h4.rep).2
      step with timer.left.rep s4 hp4 as ⟨w2, ew2⟩
      replace ew2 : w2 = wr.rootKey := ew2
      subst w2
      cases wr with
      | leaf => cases hwr
      | node cl wr1 wk wr2 =>
      cases cl with
      | true => simp [TRB.RBT.isRed] at br
      | false =>
      cases hwr with
      | black h1 h2' =>
      try simp only [WP.spec_ok]
      exact ⟨.rc false wl w up, true, wr1, wr2, h4, h1, h2', TRB.UpOK.pushR hU hwl, Or.inl rfl⟩
    | false =>
      rw [if_neg (by rw [eb4]; simp [TRB.RBT.isRed])]
      cases hS with
      | black hwl hwr =>
      exact (WP.spec_ok _).2 ⟨up, cp, wl, wr, h, hwl, hwr, hU, Or.inr (by omega)⟩
  · rintro ⟨s1, w1⟩ hC
    exact rf_tailR hT hd hk htx hC hlt

/-- Exit: `x` is the root (mode A at the top). -/
theorem rf_body_top (s : S) (c x p f : U64) {s0 : S} {Ks : List U64} {tx : TRB.RBT} {n : Nat}
    (h : FB st T s0 c Ks s tx) (hx : x = tx.rootKey) (hdb : TRB.DB tx n) :
    timer.remove_fixup_loop.body st c s x p f ⦃ r => RfPost st T s0 c Ks f r ⦄ := by
  have ex : x = L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) := hx.trans h.rep.root.symm
  unfold timer.remove_fixup_loop.body
  step with timer.root.val (st := st) s c as ⟨t, et⟩
  subst t
  step with tcb_ne.blk as ⟨b, hb⟩
  rw [if_neg (fun e => (hb.1 e) ex)]
  try simp only [WP.spec_ok]
  exact ⟨tx, h, TRB.rfA_top hdb hx⟩

/-- Exit: mode B (`x` is the root). -/
theorem rf_body_B (s : S) (c x p f : U64) {s0 : S} {Ks : List U64} {W : TRB.RBT}
    (h : FB st T s0 c Ks s W) (hB : TRB.RfB W x) :
    timer.remove_fixup_loop.body st c s x p f ⦃ r => RfPost st T s0 c Ks f r ⦄ := by
  have ex : x = L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) := hB.1.trans h.rep.root.symm
  unfold timer.remove_fixup_loop.body
  step with timer.root.val (st := st) s c as ⟨t, et⟩
  subst t
  step with tcb_ne.blk as ⟨b, hb⟩
  rw [if_neg (fun e => (hb.1 e) ex)]
  try simp only [WP.spec_ok]
  exact ⟨W, h, Or.inl hB⟩

/-- Exit: `x` red (below the root). -/
theorem rf_body_red (s : S) (c p f : U64) {s0 : S} {Ks : List U64} (hd : Ks.Nodup) {ctx : TRB.Ctx}
    {l r : TRB.RBT} {k : U64} {n : Nat} (h : FB st T s0 c Ks s (ctx.plug (.node true l k r)))
    (hc0 : ctx ≠ .top) (hl : TRB.Bal l n) (hr : TRB.Bal r n) (hc : TRB.CtxOK ctx (n + 1)) (hR : TRB.RootB ctx) :
    timer.remove_fixup_loop.body st c s k p f ⦃ r => RfPost st T s0 c Ks f r ⦄ := by
  have hxR := TRB.x_ne_root h.rep (h.nd hd) hc0
  have hxr : TRB.Rep (lk st s) ctx.par k (.node true l k r) := ((TRB.rep_plug ctx _).1 h.rep).2
  unfold timer.remove_fixup_loop.body
  step with timer.root.val (st := st) s c as ⟨t, et⟩
  subst t
  step with tcb_ne.blk as ⟨b, hb⟩
  rw [if_pos (hb.2 hxR)]
  step with timer.is_red.rep s hxr as ⟨b1, hb1⟩
  rw [if_pos (by rw [hb1]; rfl)]
  try simp only [WP.spec_ok]
  exact ⟨_, h, Or.inr ⟨ctx, l, r, n, rfl, hl, hr, hc, hR⟩⟩

/-- **One round of `remove_fixup`'s loop keeps the invariant** (or exits). -/
theorem rf_body (s : S) (c x p f : U64) {s0 : S} {Ks : List U64} (hT : TcbPlaced T) (hd : Ks.Nodup)
    (hk : ∀ y ∈ Ks, y ∈ T) (hx : RfInv st T s0 c Ks (s, x, p, f)) :
    timer.remove_fixup_loop.body st c s x p f ⦃ r => RfPost st T s0 c Ks f r ⦄ := by
  obtain ⟨W, h, hm⟩ := hx
  rcases hm with ⟨ctx, tx, n, rfl, rfl, rfl, hc, hdb, hR, hf⟩ | hB
  · by_cases h0 : ctx = .top
    · subst h0; exact rf_body_top s c _ _ f h rfl hdb
    · rcases hdb with ⟨htb, htx⟩ | ⟨l, k, r, rfl, hl, hr⟩
      · have hf' : ctx.depth ≤ f.val := hf.resolve_left (by rw [htb]; simp)
        cases ctx with
        | top => exact absurd rfl h0
        | lc cp pk S0 up =>
          obtain ⟨hU, hS, hSb⟩ := TRB.UpOK.of_lc hc hR
          exact rf_body_L s c f hT hd hk h htx htb hS hSb hU hf'
        | rc cp S0 pk up =>
          obtain ⟨hU, hS, hSb⟩ := TRB.UpOK.of_rc hc hR
          exact rf_body_R s c f hT hd hk h htx htb hS hSb hU hf'
      · exact rf_body_red s c _ f hd h h0 hl hr hc hR
  · exact rf_body_B s c x p f h hB

/-- **`remove_fixup`'s loop**: from the invariant, it ends with `RfOut` (the fuel never runs out). -/
theorem timer.remove_fixup_loop.rb (s : S) (c x p f : U64) {s0 : S} {Ks : List U64} (hT : TcbPlaced T)
    (hd : Ks.Nodup) (hk : ∀ y ∈ Ks, y ∈ T) (h : RfInv st T s0 c Ks (s, x, p, f)) :
    timer.remove_fixup_loop st s c x p f ⦃ y => RfOut st T s0 c Ks y ⦄ := by
  unfold timer.remove_fixup_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.2.val) (inv := RfInv st T s0 c Ks)
  · rintro ⟨s1, x1, p1, f1⟩ hx
    refine WP.spec_mono (rf_body s1 c x1 p1 f1 hT hd hk hx) fun r hr => ?_
    cases r with
    | done y => exact hr
    | cont x' => exact hr
  · exact h

/-- **`timer::remove_fixup`** (stage 7): from `x` doubly black at the hole `ctx` of the tree `ctx.plug tx`
(`CtxOK ctx (n + 1)`, `DB tx n`, root black unless the hole is the root, path length ≤ 256), the result is a
red-black tree with black root over the same keys, with writes only to links and height words of those keys
and the root word, core bits kept (`FB`). -/
theorem timer.remove_fixup.rb (s : S) (c : U64) {ctx : TRB.Ctx} {tx : TRB.RBT} {n : Nat} (hT : TcbPlaced T)
    (hN : NodePlaced st T s c)
    (hrep : TRB.Rep (lk st s) 0#u64 (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT)) (ctx.plug tx))
    (hd : (ctx.plug tx).keys.Nodup) (hk : ∀ y ∈ (ctx.plug tx).keys, y ∈ T)
    (hc : TRB.CtxOK ctx (n + 1)) (hdb : TRB.DB tx n) (hR : TRB.RootB ctx) (hdep : ctx.depth ≤ 256) :
    timer.remove_fixup st s c tx.rootKey ctx.par ⦃ s' => ∃ W m, FB st T s c (ctx.plug tx).keys s' W ∧
      TRB.Bal W m ∧ W.isRed = false ⦄ := by
  have h0 := FB.init (T := T) hN hrep
  have e256 : (256#u64 : U64).val = 256 := by simp
  unfold timer.remove_fixup
  refine WP.spec_bind (timer.remove_fixup_loop.rb s c tx.rootKey ctx.par 256#u64 hT hd hk
    ⟨_, h0, Or.inl ⟨ctx, tx, n, rfl, rfl, rfl, hc, hdb, hR, Or.inr (by rw [e256]; exact hdep)⟩⟩) ?_
  rintro ⟨s1, x⟩ ⟨W, h1, hw⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb
    have x0 : x = 0#u64 := by rw [eb] at hb; exact of_decide_eq_true hb
    rcases hw with ⟨-, m, hb', hbl⟩ | ⟨ctx', l, r, n', rfl, -, -, -, -⟩
    · try simp only [WP.spec_ok]
      exact ⟨W, m, h1, hb', hbl⟩
    · exfalso
      have hr2 : TRB.Rep (lk st s1) ctx'.par x (.node true l x r) := ((TRB.rep_plug ctx' _).1 h1.rep).2
      exact TRB.Rep.keys_ne0 hr2 x (by simp [TRB.RBT.keys]) x0
  · rename_i hb
    have x0 : x ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    rcases hw with ⟨ex, m, hb', hbl⟩ | ⟨ctx', l, r, n', rfl, hl, hr, hc', hR'⟩
    · cases W with
      | leaf => exact absurd ex x0
      | node cw lw kw rw =>
        have e1 : cw = false := hbl
        subst e1
        have e2 : x = kw := ex
        subst x
        exact WP.spec_mono (FB.set_red .top false lw kw rw hT hd hk h1 false) fun s' h' => ⟨_, m, h', hb', rfl⟩
    · refine WP.spec_mono (FB.set_red ctx' true l x r hT hd hk h1 false) fun s' h' => ?_
      obtain ⟨hb2, hbl2⟩ := TRB.rfR_fin (x := x) hl hr hc' hR'
      exact ⟨_, _, h', hb2, hbl2⟩

end

end Fl4Proofs.P1

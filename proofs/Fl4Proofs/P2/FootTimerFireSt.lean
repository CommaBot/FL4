/-
# P2 (p2lf): `fire`'s second iteration stops (`FireStop`) on the real run

`fire_next`: at a state `s1` where the due thread `p.tm` is the leftmost key of a represented timer tree
`ctx.plug (node c a p.tm b)`, an accepted `fire_ok` says the in-order successor of `p.tm` (the first key of
`TRB.delKeys ctx a b`: the leftmost key of `b` through `fire_ok_loop = remove_loop0`, or `p.tm`'s parent) is null
or not due.

`fire_stop`: at a state `X` with P1's `TimerRB` whose `TIMER_MIN` is the plan's due thread `p.tm`,
`fire_ok` accepted at a state `s1` agreeing with `X` on the timer fields of `T`, `timer::remove` of `p.tm`, then
any step keeping the timer words (`TAgree`, the key-space base and the core: `send_signal` of the bound
notification, or nothing), then the `REPROGRAM` write: the new `TIMER_MIN` is null or a key of `X`'s tree other
than `p.tm`, which comes after the successor in the sorted key list (`CoreTree.sorted`), so it is not due; it is
read through the `TIMER_MIN` node word and an armed key's deadline (`FootLtArmed`), the reads `FireStop` needs.

`fire_stop_sig`: `fire_stop` for the real `fire` iteration, the step between being the bound notification's
`send_signal` (P1 `send_signal.tagree` / `tinvF`, with the IPC-buffer placement `BufAt` at `X` carried across
`remove` by `timer.remove.ibFr`) or nothing.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireT
import Fl4Proofs.P2.FootTimerFireNx
import Fl4Proofs.P1.TimerRBSig
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`fire_ok`'s successor** (module docstring). -/
theorem fire_next {s1 : S} {cpu now : U64} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    {ctx : TRB.Ctx} {c0 : Bool} {a b : TRB.RBT} {R0 : U64}
    (hrep : TRB.Rep (lk st s1) 0#u64 R0 (ctx.plug (.node c0 a p.tm b)))
    (hd : (ctx.plug (.node c0 a p.tm b)).keys.Nodup)
    (hh : (ctx.plug (.node c0 a p.tm b)).height ≤ 128)
    (hmt : (ctx.plug (.node c0 a p.tm b)).minKey = p.tm)
    (hfo : localtimer.fire_ok st s1 cpu ct p now = ok true) :
    (TRB.delKeys ctx a b).headD 0#u64 = 0#u64 ∨
      ¬ L.mem s1 (tdA ((TRB.delKeys ctx a b).headD 0#u64)) ≤ now := by
  obtain ⟨-, m0, -, -, -, -, ht'⟩ := TRB.mid_facts hrep hd
  have ht' : TRB.Rep (lk st s1) ctx.par p.tm (.node c0 a p.tm b) := ht'
  have ht0 : p.tm ≠ 0#u64 := m0 p.tm (by simp [TRB.RBT.keys])
  obtain ⟨hpt, -, -, hrb⟩ := TRB.Rep.node_inv ht'
  have er : L.mem s1 (trA p.tm) = b.rootKey := by
    have := ht'.right_root
    rw [if_neg ht0] at this
    exact this
  have ep : L.mem s1 (tpA p.tm) = ctx.par := hpt
  have hrb2 : TRB.Rep (lk st s1) p.tm b.rootKey b := by
    have e : (lk st s1).r p.tm = b.rootKey := er
    rw [← e]; exact hrb
  rw [fire_ok_eq, if_neg ht0] at hfo
  obtain ⟨i, ei, hfo⟩ := bind_eq_ok hfo
  rw [eq_of_spec_fd (obj.Tcb.timer_right.val (L := L) s1 _), er] at ei
  obtain rfl := ok_inj_ff ei
  obtain ⟨i1, ei1, hfo⟩ := bind_eq_ok hfo
  rw [eq_of_spec_fd (obj.Tcb.timer_parent.val (L := L) s1 _), ep] at ei1
  obtain rfl := ok_inj_ff ei1
  obtain ⟨bn, ebn, hfo⟩ := bind_eq_ok hfo
  rw [is_null_ok] at ebn
  obtain rfl := ok_inj_ff ebn
  by_cases hb0 : b.rootKey = 0#u64
  · have eb : b = .leaf := hrb2.zero hb0
    rw [if_pos (decide_eq_true hb0)] at hfo
    rw [TRB.min_new_par hd hmt eb]
    obtain ⟨b1, eb1, hfo⟩ := bind_eq_ok hfo
    rw [is_null_ok] at eb1
    obtain rfl := ok_inj_ff eb1
    by_cases hp0 : ctx.par = 0#u64
    · exact Or.inl hp0
    rw [if_neg (by simpa using hp0)] at hfo
    obtain ⟨d, ed, hfo⟩ := bind_eq_ok hfo
    rw [td_ok] at ed
    obtain rfl := ok_inj_ff ed
    refine Or.inr fun hle => ?_
    rw [if_pos hle] at hfo
    exact absurd (ok_inj_ff hfo) (by simp)
  · rw [if_neg (by simpa using hb0)] at hfo
    obtain ⟨y, ey, hfo⟩ := bind_eq_ok hfo
    rw [fire_ok_loop_eq _ _ _ _ hb0] at ey
    have hbh : b.height ≤ layout.TREE_FUEL.val + 1 := by
      have h1 := TRB.Ctx.height_le ctx (.node c0 a p.tm b)
      have h2 : b.height + 1 ≤ (TRB.RBT.node c0 a p.tm b).height := Nat.succ_le_succ (le_max_right _ _)
      rw [layout.TREE_FUEL.val_eq]; omega
    have hl := timer.remove_loop0.lm s1 layout.TREE_FUEL hrb2 hb0 hbh
    rw [ey, WP.spec_ok] at hl
    obtain ⟨ctx2, cy, g, hL, eb⟩ := hl
    have hy0 : y ≠ 0#u64 := by
      refine m0 y ?_
      simp only [TRB.RBT.keys, List.mem_append, List.mem_cons]
      right; right
      rw [eb]
      exact TRB.Ctx.keys_sub ctx2 _ y (by simp [TRB.RBT.keys])
    have hd' := hd
    have hmt' := hmt
    rw [eb] at hd' hmt'
    rw [eb, TRB.min_new_r hd' hmt' hL]
    obtain ⟨b1, eb1, hfo⟩ := bind_eq_ok hfo
    rw [is_null_ok] at eb1
    obtain rfl := ok_inj_ff eb1
    rw [if_neg (by simpa using hy0)] at hfo
    obtain ⟨d, ed, hfo⟩ := bind_eq_ok hfo
    rw [td_ok] at ed
    obtain rfl := ok_inj_ff ed
    refine Or.inr fun hle => ?_
    rw [if_pos hle] at hfo
    exact absurd (ok_inj_ff hfo) (by simp)

set_option maxHeartbeats 8000000 in
/-- **`fire`'s second iteration stops on the real run** (module docstring). -/
theorem fire_stop {R : U64 → Prop} {X s1 X1 X2 : S} {cpu now : U64} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    (hT : TcbPlaced T) (hR : TimerRB st T Cs X) (hN : ∀ c ∈ Cs, NodePlaced st T X c) (hcC : L.cpu X ∈ Cs)
    (htm : L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) = p.tm) (h0 : p.tm ≠ 0#u64)
    (hag : ∀ y ∈ T, ∀ K : U64, 3528 ≤ K.val → K.val < 3576 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem X (core.num.U64.wrapping_add y K))
    (hfo : localtimer.fire_ok st s1 cpu ct p now = ok true)
    (hrm : timer.remove st X p.tm = ok X1)
    (hsg : TAgree st T Cs X1 X2 ∧ L.ksb X2 = L.ksb X1 ∧ L.cpu X2 = L.cpu X1)
    (rM : R (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))
    (rD : ∀ y ∈ T, FootLtArmed st X (L.cpu X) y → R (tdA y)) :
    FireStop st R (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) now := by
  unfold FireStop
  have hNX := hN _ hcC
  obtain ⟨W, ctW⟩ := hR.tree _ hcC
  have hmt : W.minKey = p.tm := ctW.min.symm.trans htm
  have htW : p.tm ∈ W.keys := by
    rcases W.minKey_mem with e | e
    · exact absurd (hmt.symm.trans e) h0
    · rw [hmt] at e; exact e
  have htT : p.tm ∈ T := ctW.inT _ htW
  -- the remove
  have hrb := timer.remove.rb X p.tm hT htT hR hN
  rw [hrm, WP.spec_ok] at hrb
  obtain ⟨hR1, htd1, -, -⟩ := hrb
  have htl := timer.remove.tlx X p.tm hT htT hR hN
  rw [hrm, WP.spec_ok] at htl
  obtain ⟨wX1, kX1⟩ : WritesIn st X X1 (fun _ => True) ∧ TKeepO st T X X1 p.tm := by
    rcases htl with ⟨e, -⟩ | ⟨c, -, W', -, -, w, k⟩
    · exact absurd e (ctW.armed _ htW)
    · exact ⟨w.mono fun _ _ => trivial, k⟩
  have k1 : L.ksb X1 = L.ksb X := wX1.1
  have c1 : L.cpu X1 = L.cpu X := wX1.2.1
  -- the final state
  have k2 : L.ksb X2 = L.ksb X := hsg.2.1.trans k1
  have c2 : L.cpu X2 = L.cpu X := hsg.2.2.trans c1
  have eN : ∀ o, L.nodeAt X2 (L.cpu X2) o = L.nodeAt X (L.cpu X) o := fun o => by rw [c2, nodeAt_of_ksb k2]
  have eY : ∀ o, L.nodeAt (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64)
      (L.cpu (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64)) o = L.nodeAt X (L.cpu X) o :=
    fun o => by rw [L.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _), eN]
  have aRp : Aligned (L.nodeAt X (L.cpu X) layout.node.REPROGRAM) :=
    nodeAt_aligned hNX (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
  have aTm : Aligned (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) :=
    nodeAt_aligned hNX (by rw [timer_min_val]; simp) (by rw [timer_min_val])
  -- the new `TIMER_MIN`
  obtain ⟨W1, ct1⟩ := hR1.tree _ hcC
  have eM : L.mem (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64)
      (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) = W1.minKey := by
    rw [eN, mem_wr_ne' aRp aTm (nodeAt_ne hNX (by simp [layout.node.REPROGRAM]) (by rw [timer_min_val]; simp)
      (by rw [timer_min_val]; simp [layout.node.REPROGRAM]))]
    have e2 := hsg.1.min _ hcC
    rw [nodeAt_of_ksb k2, nodeAt_of_ksb k1] at e2
    rw [e2]
    have e1 := ct1.min
    rw [nodeAt_of_ksb k1] at e1
    exact e1
  refine ⟨by rw [eY]; exact rM, fun hne => ?_⟩
  rw [eY, eM] at hne ⊢
  -- the new minimum is a key of `X`'s tree other than `p.tm`
  have hM1 : W1.minKey ∈ W1.keys := W1.minKey_mem.resolve_left hne
  have hMT : W1.minKey ∈ T := ct1.inT _ hM1
  have hMt : W1.minKey ≠ p.tm := fun e => ct1.armed _ hM1 (by rw [e]; exact htd1)
  obtain ⟨kd, kh⟩ := kX1 _ hMT hMt
  have arm : FootLtArmed st X (L.cpu X) W1.minKey :=
    ⟨by rw [← kd]; exact ct1.armed _ hM1, by rw [← kh]; exact ct1.core _ hM1⟩
  have hMW : W1.minKey ∈ W.keys := by
    obtain ⟨c', hc', W'', ct'', hk''⟩ := hR.armed _ hMT arm.1
    have ec : c' = L.cpu X := UScalar.eq_of_val_eq ((ct''.core _ hk'').symm.trans arm.2)
    subst ec
    rw [ct''.uniq ctW] at hk''
    exact hk''
  -- deadlines along the run
  have hY : L.mem (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) (tdA W1.minKey) =
      L.mem X (tdA W1.minKey) := by
    have aM : Aligned (tdA W1.minKey) := tz_aligned hT (Tz.of_mem hMT) (K := 3528#u64) (by simp) (by simp)
    rw [eN, mem_wr_ne' aRp aM (fun e => node_ne_tz hT hNX (by simp [layout.node.REPROGRAM]) (Tz.of_mem hMT)
      (K := 3528#u64) (by simp) (congrArg UScalar.val e)), hsg.1.td _ hMT, kd]
  refine ⟨rD _ hMT arm, ?_⟩
  rw [hY]
  -- the successor `fire_ok` checked
  obtain ⟨ctx, c0, a, b, eW⟩ := TRB.RBT.mem_split W p.tm htW
  subst eW
  have hrep1 : TRB.Rep (lk st s1) 0#u64 (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_ROOT))
      (ctx.plug (.node c0 a p.tm b)) := by
    refine ctW.rep.congr fun y hy => ?_
    have f := fun (K : U64) (h1 : 3528 ≤ K.val) (h2 : K.val < 3576) (h3 : K.val % 8 = 0) =>
      hag y (ctW.inT y hy) K h1 h2 h3
    refine ⟨f 3544#u64 (by simp) (by simp) (by simp), f 3552#u64 (by simp) (by simp) (by simp),
      f 3560#u64 (by simp) (by simp) (by simp), ?_⟩
    show ((L.mem s1 (thA y) &&& 1#u64) != 0#u64) = ((L.mem X (thA y) &&& 1#u64) != 0#u64)
    rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl, f 3568#u64 (by simp) (by simp) (by simp)]
  have hnx := fire_next (p := p) (ct := ct) (cpu := cpu) (now := now) hrep1 ctW.nodup ctW.height_le hmt hfo
  obtain ⟨e1, -, -⟩ := TRB.min_is_t ctW.nodup hmt
  have ek : (ctx.plug (.node c0 a p.tm b)).keys = p.tm :: TRB.delKeys ctx a b := by
    obtain ⟨-, ea, -⟩ := TRB.min_is_t ctW.nodup hmt
    subst ea
    rw [TRB.plug_t_keys, TRB.delKeys_eq, e1]
    simp [TRB.RBT.keys]
  have hMr : W1.minKey ∈ TRB.delKeys ctx a b := by
    rw [ek] at hMW
    rcases List.mem_cons.1 hMW with e | e
    · exact absurd e hMt
    · exact e
  have hsorted := ctW.sorted
  rw [ek] at hsorted
  have hs2 := (List.pairwise_cons.1 hsorted).2
  generalize hrest : TRB.delKeys ctx a b = rest at hMr hs2 hnx
  cases rest with
  | nil => simp at hMr
  | cons N rest =>
    simp only [List.headD_cons] at hnx
    have hNk : N ∈ (ctx.plug (.node c0 a p.tm b)).keys := by rw [ek, hrest]; simp
    have hNT : N ∈ T := ctW.inT _ hNk
    have hN0 : N ≠ 0#u64 := ctW.rep.keys_ne0 _ hNk
    have hdN : now.val < (L.mem X (tdA N)).val := by
      rcases hnx with e | e
      · exact absurd e hN0
      · have e' : L.mem s1 (tdA N) = L.mem X (tdA N) := hag N hNT 3528#u64 (by simp) (by simp) (by simp)
        rw [e', UScalar.le_equiv] at e
        omega
    have hle : (L.mem X (tdA N)).val ≤ (L.mem X (tdA W1.minKey)).val := by
      rcases List.mem_cons.1 hMr with e | e
      · exact le_of_eq (by rw [e])
      · exact (List.pairwise_cons.1 hs2).1 _ e
    show now < L.mem X (tdA W1.minKey)
    rw [UScalar.lt_equiv]
    omega

set_option maxHeartbeats 8000000 in
/-- **`fire_stop` for the real iteration** (module docstring). -/
theorem fire_stop_sig {R : U64 → Prop} {Ω Sg Rp Scs Nt Ac U : Set U64} {H : Heap} {Z : U64 → Nat}
    {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {X s1 X1 X2 : S} {a a2 : A} {cpu now badge : U64} {ct : obj.Tcb} {p : localtimer.TimerIrqPlan}
    (hTI : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hBA : BufAt st T Cs H Sg Scs Z U X)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (htm : L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) = p.tm) (h0 : p.tm ≠ 0#u64)
    (hag : ∀ y ∈ T, ∀ K : U64, 3528 ≤ K.val → K.val < 3576 → K.val % 8 = 0 →
      L.mem s1 (core.num.U64.wrapping_add y K) = L.mem X (core.num.U64.wrapping_add y K))
    (hfo : localtimer.fire_ok st s1 cpu ct p now = ok true)
    (hrm : timer.remove st X p.tm = ok X1)
    (hbn : L.mem X1 (boundA p.tm) ≠ 0#u64 → L.mem X1 (boundA p.tm) ∈ Nt)
    (hsg : (if L.mem X1 (boundA p.tm) != 0#u64 then
        notification.send_signal st ar X1 a (L.mem X1 (boundA p.tm)) badge else ok (X1, a)) = ok (X2, a2))
    (rM : R (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))
    (rD : ∀ y ∈ T, FootLtArmed st X (L.cpu X) y → R (tdA y)) :
    FireStop st R (L.wr X2 (L.nodeAt X2 (L.cpu X2) layout.node.REPROGRAM) 1#u64) now := by
  have hR : TimerRB st T Cs X := TInv.rb hTI
  have h0' := hTI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0'.tcbs
  have hcC : L.cpu X ∈ Cs := h0'.cur
  have hN : ∀ c ∈ Cs, NodePlaced st T X c := h0'.nodes
  refine fire_stop hT hR hN hcC htm h0 hag hfo hrm ?_ rM rD
  by_cases hn : L.mem X1 (boundA p.tm) = 0#u64
  · rw [if_neg (by simp [hn])] at hsg
    have e := ok_inj_ff hsg
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, -⟩ := e
    exact ⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩, rfl, rfl⟩
  rw [if_pos (bne_iff_ne.mpr hn)] at hsg
  have htW : p.tm ∈ T := by
    obtain ⟨W, ctW⟩ := hR.tree _ hcC
    have hmt : W.minKey = p.tm := ctW.min.symm.trans htm
    rcases W.minKey_mem with e | e
    · exact absurd (hmt.symm.trans e) h0
    · rw [hmt] at e; exact ctW.inT _ e
  have TI1 := timer.remove.tinv X p.tm hTI htW
  rw [hrm, WP.spec_ok] at TI1
  have F1 := timer.remove.ibFr X p.tm hTI htW
  rw [hrm, WP.spec_ok] at F1
  have BA1 : BufAt st T Cs H Sg Scs Z U X1 := hBA.of_fr F1
  have hnN := hbn hn
  have tg := notification.send_signal.tagree hA X1 a _ badge TI1 hnN (hNt _ hnN) BA1.1 BA1.2
  rw [hsg, WP.spec_ok] at tg
  try simp only [WP.uncurry'_pair] at tg
  have tf := notification.send_signal.tinvF hA X1 a _ badge TI1 hnN (hNt _ hnN) BA1.1 BA1.2
  rw [hsg, WP.spec_ok] at tf
  try simp only [WP.uncurry'_pair] at tf
  exact ⟨tg.2.1, tg.2.2, tf.2.1.2.1⟩

end

end Fl4Proofs.P2

/-
P2 (line pte, gen 5): **`TCB_SetTimer` reads no PTE word** (the `stm` field of `P3AvP3`, discharged) and
**`serializable_fl4_localP3P4`** (3 [W] left: vmF, vmR, io).

* **`set_timer_farR`**: `FootTimerSetFar.set_timer_far` (a target of this core armed in another core's tree: the run
  declines) for **any read set `R`**: its two read-membership steps are the hypotheses `hnR` (this core's node words)
  and `hfR` (words of a TCB of `T`); `set_timer_far` is `R := Aligned`. The original is unchanged.
* **`region_tcb_ne_none`**: a word of a heap TCB lies in a region other than `.none`.
* **`stm_avoidP_path`** / **`stm_avoidP`**: the accepted run by `set_timer_acc_own` at the layout `userP K`
  (`MaxR (userP K) ⊆ MaxR (userV K) ∖ ptes`, as for irq); the declines from every alternative as
  `FootTimerSetObl.set_timer_alt`'s decline half, re-run: the "target far" case by `set_timer_dec_guard` at `userP K`
  carried to the alternative by `interp_agree`; the "armed in another core's tree" case by the copied `CoreTree`
  argument and `set_timer_farR` at `R := Aligned ∖ ptes` (`hnR`: node words, region `.node`; `hfR`: TCB words,
  `region_tcb_ne_none`; both off the PTEs by `RegionOKP.none`). PTE facts: `PteSl` [J] (domain words). **No new
  premise.**
* `P3AvP4` (= `P3AvP3` − `irq` − `stm`; the irq field by `E2EPIrq.irq_avoidP`), `P3AvP4.toP3`,
  **`serializable_fl4_localP3P4`**.

Remaining [W] (`P3AvP4` fields): vmF, vmR, io (held for the iolay line: `IoLay.ks` is being narrowed).
-/
import Fl4Proofs.P2.E2EPIrq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (guard RPerm WPerm HeldBy GateOnly ScAcc rhA tmA RdHead tr_bind tr_bind_same tr_ite)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A)

/-- **A target of this core armed elsewhere: the run declines**, writing nothing (module docstring). -/
theorem set_timer_farR {R : U64 → Prop} {s : S} {a : A} {n : I64} {target : U64} {r : Bool × S × A} {W0 : TRB.RBT}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T) (htg : target ∈ T)
    (ct : CoreTree st T s (L.cpu s) W0) (hk : target ∉ W0.keys) (hd : L.mem s (tdA target) ≠ 0#u64)
    (hnR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o))
    (hfR : ∀ {x k : U64}, x ∈ T → k.val < 4096 → k.val % 8 = 0 → R (core.num.U64.wrapping_add x k))
    (h : localtimer.handle_set_timer_local st ar s a n target = ok r) :
    r.1 = false ∧ localtimer.handle_set_timer_local (guard st R (fun _ => False)) ar s a n target = ok r := by
  have key : localtimer.set_timer_target_ok st s (L.cpu s) target ≠ ok true := by
    intro e
    unfold localtimer.set_timer_target_ok at e
    obtain ⟨i, -, e⟩ := bind_eq_ok e
    split at e
    · simp at e
    obtain ⟨d, ed, e⟩ := bind_eq_ok e
    rw [td_ok] at ed
    have hdv := ok_inj_ff ed
    split at e
    · rename_i h0; exact hd (hdv.trans h0)
    obtain ⟨b, eb, e⟩ := bind_eq_ok e
    cases b
    · simp at e
    · exact hk (in_core_found ct eb)
  have ht' := hT _ hcT
  have nA : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := hnR
  have fA : ∀ {x k : U64}, x ∈ T → k.val < 4096 → k.val % 8 = 0 → R (core.num.U64.wrapping_add x k) := hfR
  have gtgt : ∀ b, localtimer.set_timer_target_ok st s (L.cpu s) target = ok b →
      localtimer.set_timer_target_ok (guard st R (fun _ => False)) s (L.cpu s) target = ok b := fun b eb =>
    set_timer_target_ok.guard ct (fun w hw => by
      rcases hw with rfl | rfl | ⟨y, hy, rfl | rfl | rfl⟩
      · exact nA _ (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])
      · exact nA _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      · exact fA (ct.inT y hy) (by simp) (by simp)
      · exact fA (ct.inT y hy) (by simp) (by simp)
      · exact fA (ct.inT y hy) (by simp) (by simp)) (fA htg (by simp) (by simp)) (fA htg (by simp) (by simp))
      (fA htg (by simp) (by simp)) eb
  obtain ⟨b0, s0, a0⟩ := r
  have hb : b0 = false := by
    cases b0
    · rfl
    exfalso
    unfold localtimer.handle_set_timer_local at h
    try simp only [lift, bind_ok] at h
    obtain ⟨t, -, h⟩ := bind_eq_ok h
    obtain ⟨cpu, ecpu, h⟩ := bind_eq_ok h
    rw [L.cur_cpu_eq] at ecpu
    have hcpu : cpu = L.cpu s := (ok_inj_ff ecpu).symm
    subst hcpu
    obtain ⟨info, -, h⟩ := bind_eq_ok h
    rw [num_domains_ne_one_false] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    by_cases g1 : (n != fl4_abi.syscall.SysCall) = true
    · rw [if_pos g1] at h; simp at h
    rw [if_neg g1] at h
    obtain ⟨i, -, h⟩ := bind_eq_ok h
    by_cases g2 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
    · rw [if_pos g2] at h; simp at h
    rw [if_neg g2] at h
    by_cases g3 : (info.label != fl4_abi.label.TCBSetTimer) = true
    · rw [if_pos g3] at h; simp at h
    rw [if_neg g3] at h
    by_cases g4 : (info.extra_caps != 0#u64) = true
    · rw [if_pos g4] at h; simp at h
    rw [if_neg g4] at h
    by_cases g5 : info.length < 2#u64
    · rw [if_pos g5] at h; simp at h
    rw [if_neg g5] at h
    obtain ⟨csc, -, h⟩ := bind_eq_ok h
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    cases b
    · rw [if_neg Bool.false_ne_true] at h; simp at h
    · exact key eb
  subst hb
  refine ⟨rfl, ?_⟩
  revert h
  unfold localtimer.handle_set_timer_local
  rw [PathObl.sched.cur_thread.guard (gS := guard st R (fun _ => False)) s (nA _ (by rw [curth_val]; omega) (by rw [curth_val])), cur_thread_ok,
    PathObl.guard_cur_cpu, L.cur_cpu_eq]
  simp only [bind_ok, lift]
  rw [PathObl.msg.msg_info.guard (gS := guard st R (fun _ => False)) s _ (by
    obtain ⟨k, hk', e⟩ := regA_eq ht' (r := layout.reg.MSG_INFO) (by simp [layout.reg.MSG_INFO])
    have : layout.reg.MSG_INFO.val < 384 := by simp [layout.reg.MSG_INFO]
    rw [e]; exact fA hcT (by omega) (by omega))]
  refine tr_bind_same (fun info _ => ?_)
  rw [num_domains_ne_one_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.obj.Tcb.flags.guard (gS := guard st R (fun _ => False)) _ s (fA hcT (by simp) (by simp))]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.sched.cur_sc.guard (gS := guard st R (fun _ => False)) s (nA _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
  refine tr_bind_same (fun csc _ => ?_)
  refine tr_bind (fun b eb _ => gtgt b eb) (fun b eb => ?_)
  cases b
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]; exact fun h => h
  · exact absurd eb key

end

/-- **A word of a heap TCB lies in a region other than `.none`.** -/
theorem region_tcb_ne_none {K : KLayout} {x k : U64} (ht : K.heap x = some .tcb)
    (hv : (core.num.U64.wrapping_add x k).val = x.val + k.val) (hk : k.val < 4096) :
    region K (core.num.U64.wrapping_add x k) ≠ .none := by
  have hex : ∃ t, K.heap t = some .tcb ∧ InW t (2 ^ 12) (core.num.U64.wrapping_add x k) :=
    ⟨x, ht, by unfold InW; omega⟩
  intro e
  unfold region at e
  by_cases h1 : ∃ c, InNode K c (core.num.U64.wrapping_add x k)
  · rw [dif_pos h1] at e; cases e
  rw [dif_neg h1] at e
  by_cases h2 : ∃ p ∈ K.slots, InW p 32 (core.num.U64.wrapping_add x k)
  · rw [dif_pos h2] at e; cases e
  rw [dif_neg h2, dif_pos hex] at e
  cases e

end Fl4Proofs.P2

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll)
open Fl4Proofs.P2.OwnMap (KLayout region fld oTIMER_DEADLINE GateField TimerField tcbOwner tOwner)
open Fl4Proofs.P2.PathObl

noncomputable section
open Classical

section stm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **`TCB_SetTimer`'s route-U path reads no PTE word**, from `PteSl` [J] (module docstring). -/
theorem stm_avoidP_path (i : StArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hPS : PteSl st K) (h : (stSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) ((stSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h) := by
  have vf : VFacts L K.toKLayoutV := VFacts.ofEmpty h.1 h.2.bun.choose_spec
  have hKu := regionOK_userV hK.base
  have hUOu := userOK_userV hK.base hU.base
  have hp := st_isProg S i.n i.target
  have hz := st_noZero i.n i.target
  have ent : ∀ s, SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s →
      StEntK (userV K.toKLayoutV) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac i.target m s :=
    fun s hs => stEntK_userV hK.base (vf.v hs.1).1 (vf.v hs.1).2.1 (slJAt_ksb hs.1) (h.2.pe s hs.1 hs.2)
  have entP : ∀ s, SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s →
      StEnt (userP K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac i.target s :=
    fun s hs => ⟨(ent s hs).ent.inv, stLay_userP hK (ent s hs).ent.lay
      (pteKs_at hPS hs.1 (by simp [layout.ks.CUR_DOMAIN])) (pteKs_at hPS hs.1 (by simp [layout.ks.DOMAIN_TIME])),
      (ent s hs).ent.pre, (ent s hs).ent.aff, (ent s hs).ent.tg⟩
  have hex : ∃ p : SProg Bool, IsProg (stBody S i.n i.target) p ∧ NoZero p ∧
      E2E.ReadOnce st ar p (OwnMap.cls (userV K.toKLayoutV)) (OwnMap.ko (userV K.toKLayoutV) m)
        (· ∈ (userV K.toKLayoutV).user) (StEntV K.toKLayoutV st i.Cs i.Ω i.Sg i.Ac i.target m)
        (MaxR (userV K.toKLayoutV) st i.lk) :=
    ⟨_, hp, hz, st_hro ar i.n hA hKu hUOu hm⟩
  refine ⟨?_, ?_, IsProg.on (Classical.choose_spec hex).1 _ _ _⟩
  · intro s a r hs hr hb
    have hs' : SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s := hs
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localtimer.handle_set_timer_local st ar s a i.n i.target = ok (true, s1, a1) := hr
    have eP : ∀ (mm : machine.Store S) (x : S), localtimer.handle_set_timer_local mm ar x a i.n i.target =
        interp mm ar (R.localtimer.handle_set_timer_local i.n i.target) x a :=
      fun mm x => congrFun (congrFun (hp A ar mm) x) a
    have hE := (ent s hs').ent
    have hEP := entP s hs'
    have g1 := set_timer_acc_own ar hA (lk := i.lk) hE.inv hE.tg hE.lay hE.aff hr'
    have g2 := set_timer_acc_own ar hA (lk := i.lk) hEP.inv hEP.tg hEP.lay hEP.aff hr'
    replace g1 := (eP _ s).symm.trans g1
    replace g2 := (eP _ s).symm.trans g2
    have w1 := (interp_guard _ s a _ g1).2
    have w2 := (interp_guard _ s a _ g2).2
    show localtimer.handle_set_timer_local
      (guard st (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st i.lk) s) (MaxW (userV K.toKLayoutV) st i.lk s))
      ar s a i.n i.target = ok (true, s1, a1)
    refine (eP _ s).trans ?_
    exact guard_of_within (st := st) (L := L) (ar := ar) _ s a _ ((eP st s).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.2 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2))
  · intro s a r hs hr hn s' r' hA' h'
    have hs' : SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s := hs
    have hAl : PathObl.Alt st (MaxR (userV K.toKLayoutV) st i.lk s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have h'' : localtimer.handle_set_timer_local st ar s' a i.n i.target = ok r' := h'
    have eP : ∀ (mm : machine.Store S) (x : S), localtimer.handle_set_timer_local mm ar x a i.n i.target =
        interp mm ar (R.localtimer.handle_set_timer_local i.n i.target) x a :=
      fun mm x => congrFun (congrFun (hp A ar mm) x) a
    have hEK := ent s hs'
    have hE := hEK.ent
    have hEP := entP s hs'
    have hko : L.mem s (affA i.target) = L.cpu s →
        OwnMap.ko (userV K.toKLayoutV) m (tdA i.target) = .core (L.cpu s) := set_timer_ko hKu hUOu hEK
    have hcls := set_timer_cls hE
    have hU := set_timer_user hKu hUOu hE
    show localtimer.handle_set_timer_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a i.n i.target
      = ok r'
    obtain ⟨b, s1, a1⟩ := r
    cases b
    swap
    · exact absurd rfl hn
    have hr' : localtimer.handle_set_timer_local st ar s a i.n i.target = ok (false, s1, a1) := hr
    by_cases hfar : L.mem s (affA i.target) ≠ L.cpu s ∨ L.mem s (tdA i.target) = 0#u64 ∨
        (L.mem s (thA i.target)).val >>> 8 = (L.cpu s).val
    · have g := set_timer_dec_guard ar hA (lk := i.lk) hEP.inv hEP.tg hEP.lay hEP.pre hEP.aff hfar hr'
      replace g := (eP _ s).symm.trans g
      obtain ⟨s1', g'⟩ := interp_agree hm (fun w hw => hw.2.1) (fun w hw => (hE.dec hw).1) _ hz s s' a false s1 a1
        hAl.ksb hAl.cpu hAl.masks (fun w hw => hAl.read w ⟨hw.1, hw.2.1, fun hu => hw.2.2 (Or.inl hu)⟩) g
      obtain ⟨hst, w⟩ := interp_guard _ s' a _ g'
      have e : r' = (false, s1', a1) := Result.ok_injective (((eP st s').symm.trans h'').symm.trans hst)
      subst e
      refine (eP _ s').trans ?_
      exact guard_of_within (st := st) (L := L) (ar := ar) _ s' a _ hst (Within.mono (fun b hb hq => hb.2.2 (Or.inr hq)) (fun _ _ => trivial) _ s' a w)
    · rw [not_or, not_or, not_not] at hfar
      obtain ⟨hat, hd, hh⟩ := hfar
      have h0 := hE.inv.1.choose_spec.choose_spec
      have hT : TcbPlaced (Heap.tcbs K.heap) := h0.tcbs
      have hN : NodePlaced st (Heap.tcbs K.heap) s (L.cpu s) := h0.nodes _ h0.cur
      obtain ⟨W0, ct⟩ := (TInv.rb (BXI.blk hE.inv)).tree _ h0.cur
      have eN : ∀ o, L.nodeAt s' (L.cpu s) o = L.nodeAt s (L.cpu s) o := fun o => nodeAt_of_ksb hAl.ksb _ o
      have keyR : ∀ y ∈ W0.keys, ∀ k : U64, 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
          L.mem s' (core.num.U64.wrapping_add y k) = L.mem s (core.num.U64.wrapping_add y k) := by
        intro y hy k h1 h2 h3
        refine hAl.read _ ⟨Or.inl (held_core ?_), field_aligned (hT y (ct.inT y hy)) (by omega) h3,
          hE.lay.nu_tcb (ct.inT y hy) (by omega) (by omega)⟩
        have e := hE.lay.own_tcb hT (L.mem s) (ct.inT y hy) (k := k) (by omega) (by omega)
        unfold fld at e
        rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
          if_pos (show TimerField k.val by unfold TimerField; omega), tOwner,
          if_pos (show (L.mem s (fld y oTIMER_DEADLINE)).val ≠ 0 from
            fun h => ct.armed y hy (UScalar.eq_of_val_eq h))]
        have e2 := ct.core y hy
        rw [Nat.shiftRight_eq_div_pow] at e2
        exact congrArg Owner.core (MoveTimer.treeCore_of (c := L.cpu s) e2)
      have ct' : CoreTree st (Heap.tcbs K.heap) s' (L.cpu s) W0 := CoreTree.agree ct eN
        (hAl.read _ (nodeR hE (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])))
        (hAl.read _ (nodeR hE (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])))
        (fun y hy => ⟨keyR y hy _ (by simp) (by simp) (by simp), keyR y hy _ (by simp) (by simp) (by simp),
          keyR y hy _ (by simp) (by simp) (by simp), keyR y hy _ (by simp) (by simp) (by simp),
          keyR y hy _ (by simp) (by simp) (by simp)⟩)
      have hd' : L.mem s' (tdA i.target) ≠ 0#u64 := by
        by_cases hin : MaxR (userV K.toKLayoutV) st i.lk s (tdA i.target)
        · rw [hAl.read _ hin]; exact hd
        · have e := hAl.clsEq _ hin hU (Or.inr (hko hat))
          exact fun h => hd ((hcls _ _ e).1 h)
      have hcur : L.curW s' = L.curW s := by
        unfold LawfulStore.curW
        rw [hAl.cpu, eN]
        exact hAl.read _ (nodeR hE (by rw [curth_val]; omega) (by rw [curth_val]))
      have hk : i.target ∉ W0.keys := fun h => hh (ct.core i.target h)
      rw [← hAl.cpu] at ct'

      have hN' : NodePlaced st (Heap.tcbs K.heap) s' (L.cpu s') := by rw [hAl.cpu]; exact hN.ksb hAl.ksb
      have hnR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
          Aligned (L.nodeAt s' (L.cpu s') o) ∧ L.nodeAt s' (L.cpu s') o ∉ K.ptes := by
        intro o h1 h2
        refine ⟨nodeAt_aligned hN' h1 h2, ?_⟩
        have e : L.nodeAt s' (L.cpu s') o = L.nodeAt s (L.cpu s) o := by rw [hAl.cpu]; exact eN o
        rw [e]
        intro hq
        have h3 : region K.toKLayout (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) := hE.lay.nd o h1
        rw [hK.none _ hq] at h3
        cases h3
      have hfR : ∀ {x k : U64}, x ∈ Heap.tcbs K.heap → k.val < 4096 → k.val % 8 = 0 →
          Aligned (core.num.U64.wrapping_add x k) ∧ core.num.U64.wrapping_add x k ∉ K.ptes :=
        fun {x k} hx h1 h2 => ⟨field_aligned (hT _ hx) h1 h2,
          fun hq => region_tcb_ne_none (K := K.toKLayout) hx (tcb_wadd_val (hT _ hx) h1) h1 (hK.none _ hq)⟩
      obtain ⟨-, h2⟩ := set_timer_farR (R := fun w => Aligned w ∧ w ∉ K.ptes) ar hT hN'
        (by rw [hcur]; exact h0.curT) hE.tg ct' hk hd' hnR hfR h''
      replace h2 := (eP _ s').symm.trans h2
      refine (eP _ s').trans ?_
      exact interp_mono (fun _ hq => hq.2) (fun _ hq => hq.elim) _ hz s' a r' h2

/-- **`TCB_SetTimer` reads no PTE word** (the `stm` field of `P3AvP`), from `PteSl` [J]. -/
theorem stm_avoidP (i : StArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hPS : PteSl st K) (h : (stSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K ((stSlotP3W st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (stSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)) := by
    rintro P W rfl
    exact avoidE_liftAtV hK.base _ W (stm_avoidP_path st ar hA hm i K m hK hU hPS h)
  exact key _ _ (SlotU.fam_pos _ _ h)

/-- **`P3AvP3` with `irq` and `stm` discharged** (both by `PteSl` [J], already a field). -/
structure P3AvP4 : Prop where
  pteSl : ∀ K : KLayoutP, RegionOKP K → K.ptes ≠ ∅ → PteSl st K
  vtP : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (vtSlotP3 st ar hA hm).Prem i K.toKLayoutV m → ∀ s, VtPre st i K.toKLayoutV s → VtmP K st i.irq s
  vxP : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m → ∀ s, VxPre st i K.toKLayoutV m s → VxP (L := L) K s
  /-- [W] -/
  vmF : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).vmF.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).vmF.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  /-- [W] -/
  vmR : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).vmR.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).vmR.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  /-- [W] -/
  io : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).io.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).io.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)

theorem P3AvP4.toP3 (h : P3AvP4 st ar hA hSt hm a0) : P3AvP3 st ar hA hSt hm a0 where
  pteSl := h.pteSl
  vtP := h.vtP
  vxP := h.vxP
  vmF := h.vmF
  vmR := h.vmR
  io := h.io
  stm i K m hK hU he hp := stm_avoidP st ar hA hm i K m hK hU (h.pteSl K hK he) hp
  irq i K m hK hU he hp := irq_avoidP st ar hA hm i K m hK hU (h.pteSl K hK he) hp

/-- **FL4 end to end with rules 7 and 8, `K.ptes` arbitrary, five of the eight slots' PTE premises discharged**
(`serializable_fl4_localP3P3` with `P3AvP4`: `irq` / `stm` [W] gone; 3 [W] left: vmF, vmR, io). -/
theorem serializable_fl4_localP3P4 (hAv : P3AvP4 st ar hA hSt hm a0) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP (fl4LocP3P st ar hA hSt hm a0 (P3AvP2.toP3 st ar hA hSt hm a0 (P3AvP3.toP2 st ar hA hSt hm a0
      (P3AvP4.toP3 st ar hA hSt hm a0 hAv)))) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localP3P3 st ar hA hSt hm a0 (P3AvP4.toP3 st ar hA hSt hm a0 hAv) h0 hA0 hK0 hU0 hM0 h hq

end stm

end
end Fl4Proofs.P2.E2EP

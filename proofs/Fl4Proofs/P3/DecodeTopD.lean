/-
P3 (DESIGN.md §9): **the domain schedule through the top level**.

`DomRel` (DomDecode.lean) depends on five FL4 words (the `DOM_SCHED_START`
word and the two entries' domain and duration words) and on the spec's
`domain_list` and `domain_start_index`. `DomRel.frame`: a step of FL4 that
keeps those words, against a spec step that keeps those fields, keeps
`DomRel`; `DomSame.wr`: a write to any other aligned word keeps them.

`TopPostD` is `TopPost` with `DomRel` after the invocation, `DecOKD` the
statement for one cap, and `decode_invocation_refinesD` the dispatch. The
domain cap's statement is `decode_invocation_domainD`; for the other caps,
`DecOK.withDom` adds `DomRel` to `DecOK` from `DomFrame`: FL4's branch keeps
the five words and the kernel-global base, and the spec's invocation keeps
`domain_list` and `domain_start_index`.
-/
import Fl4Proofs.P3.DomDecode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The five words of the domain schedule (their offsets). -/
def domOffs : List U64 := [32#u64, 192#u64, 200#u64, 208#u64, 216#u64]

theorem domSame_iff {m m' : U64 → U64} {kb : U64} :
    (∀ o ∈ domOffs, m' (ksW kb o) = m (ksW kb o)) → DomSame m m' kb := by
  intro h
  refine ⟨h _ (by simp [domOffs]), fun i hi => ?_⟩
  rcases (show i.val = 0 ∨ i.val = 1 by omega) with h0 | h1
  · have : i = 0#u64 := UScalar.eq_of_val_eq (by rw [h0]; rfl)
    subst this
    exact ⟨by rw [show entOff 0#u64 = 192#u64 from rfl]; exact h _ (by simp [domOffs]),
      by rw [show durOff 0#u64 = 200#u64 from rfl]; exact h _ (by simp [domOffs])⟩
  · have : i = 1#u64 := UScalar.eq_of_val_eq (by rw [h1]; rfl)
    subst this
    exact ⟨by rw [show entOff 1#u64 = 208#u64 from rfl]; exact h _ (by simp [domOffs]),
      by rw [show durOff 1#u64 = 216#u64 from rfl]; exact h _ (by simp [domOffs])⟩

/-- **A write to an aligned word other than the five keeps them.** -/
theorem DomSame.wr (s : S) {kb a : U64} (v : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0)
    (ha : P1.Aligned a) (hne : ∀ o ∈ domOffs, (ksW kb o).val ≠ a.val) :
    DomSame (L.mem s) (L.mem (L.wr s a v)) kb := by
  apply domSame_iff
  intro o ho
  have h8 : o.val < 256 ∧ o.val % 8 = 0 := by
    simp only [domOffs, List.mem_cons, List.mem_nil_iff, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide
  exact L.mem_wr_ne ha (ksW_al hkf hka h8.1 h8.2) (Ne.symm (hne o ho))

/-- **The frame lemma**: FL4 keeping the five words (and the kernel-global
base), the spec keeping `domain_list` and `domain_start_index`. -/
theorem DomRel.frame {m m' : U64 → U64} {kb : U64} {σ σ' : Fl4Spec.State Unit} (h : DomRel m kb σ)
    (hw : ∀ o ∈ domOffs, m' (ksW kb o) = m (ksW kb o)) (hl : σ'.domainList = σ.domainList)
    (hst : σ'.domainStartIndex = σ.domainStartIndex) : DomRel m' kb σ' :=
  h.of_same (domSame_iff hw) hl hst

/-- The spec's `set_thread_state` keeps the domain schedule. -/
theorem setThreadState_dom {σ σ1 : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {tcb : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb tcb)) {ts : Fl4Spec.ThreadState}
    (h : Fl4Spec.setThreadState (Z := Unit) t ts σ = ({((), σ1)}, False)) :
    σ1.domainList = σ.domainList ∧ σ1.domainStartIndex = σ.domainStartIndex := by
  have e := Notif.setThreadState_eq (Z := Unit) ts hk
  rw [h] at e
  have e' : σ1 = Notif.stsAct (Notif.updK σ t (.tcb { tcb with tcbState := ts })) t := by
    have := congrArg (fun x => x.1) e; simpa using this
  subst e'
  unfold Notif.stsAct; split <;> exact ⟨rfl, rfl⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`TopPost` with the domain schedule**: `DomRel` holds after the
invocation (after an error, the state is unchanged). -/
def TopPostD (σ : Fl4Spec.State Unit) (blk call don : Bool) (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation)
    (s : S) (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
  (∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, ∃ th' G',
      ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
      DomRel (L.mem res.2.1) (L.ksb res.2.1) y.2)

theorem TopPostD.top {σ : Fl4Spec.State Unit} {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation}
    {s : S} {res : core.result.Result Unit error.Exc × S × A} (h : TopPostD (L := L) σ blk call don m s res) :
    TopPost (L := L) σ blk call don m s res := by
  rcases h with h | ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6⟩

/-- The statement for one cap, with the domain schedule. -/
abbrev DecOKD (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (c : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    TopPostD (L := L) σ blk call don (specDec fp slbl args ci sl c excaps buffer) s res ⦄

/-- **The domain-schedule frame of one cap's branch**: FL4's
`decode_invocation` keeps the kernel-global base and the five words, and
every outcome of the spec's invocation (after the decode and the restart)
keeps `domain_list` and `domain_start_index`. -/
def DomFrame (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (c : capability.Cap)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (slbl : Fl4Spec.Data)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) : Prop :=
  (syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    L.ksb res.2.1 = L.ksb s ∧ ∀ o ∈ domOffs, L.mem res.2.1 (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) ⦄) ∧
  ∀ inv σ1, DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv →
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    ∀ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1,
      y.2.domainList = σ.domainList ∧ y.2.domainStartIndex = σ.domainStartIndex

/-- **`DecOK` with the domain schedule**, from the cap's `DomFrame`. -/
theorem DecOK.withDom {s : S} {ar : A} {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap}
    {blk call don fp : Bool} {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data}
    {args : List Fl4Spec.Data} {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr}
    {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {buffer : Option Fl4Spec.ObjRef}
    (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (h : DecOK (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer)
    (hF : DomFrame (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOKD (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer := by
  refine WP.spec_mono (WP.spec_and h hF.1) ?_
  rintro res ⟨hq, hkb, hw⟩
  rcases hq with hq | ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6⟩
  · exact Or.inl hq
  · obtain ⟨hl, hst⟩ := hF.2 inv σ1 h1 h2 y hy
    refine Or.inr ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, ?_⟩
    rw [hkb]; exact hDR.frame hw hl hst

/-- **The domain cap**, with the domain schedule. -/
theorem decode_invocation_domainD (hcfg : DomConfig) (th : TypedHeap) (hP : Placed th) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 excs)
    (hSet : DomSetHyp (L := L) th s σ ct) (hRes : DomResHyp (L := L) th s σ ct)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKD (L := L) arI s ar σ lbl length slot .Domain blk call don fp buf extra slbl (args.map UScalar.bv) ci sl
      excs buffer := by
  unfold DecOKD syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (domain_decode_refines hcfg th hP s σ G hCR hFI hDR ct hct hcur htcb hact hkf hka hksO hactK
      lbl slbl hlbl length buf args hlen hargs extra x0 hx0 excs hex hSet hRes) ?_
    rintro ⟨r0, s'⟩ hq
    simp only [uncurry_apply_pair]
    rw [WP.spec_ok]
    rcases hq with ⟨e, he, hs', e', h1, h2⟩ | ⟨he, inv, hrun, σ1, hst, y, hy, -, hCR', hFI', -, hDR'⟩
    · exact Or.inl ⟨e, he, hs', e', run_liftME_err h1, Or.inl h2⟩
    · have hm : ((.ok [], y.2) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
          ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeDomain inv)).run σ1).1 := by
        show _ ∈ ((Fl4Spec.NonDetE.liftE (do Fl4Spec.invokeDomain (Z := Unit) inv; return ([] : List Fl4Spec.Data))).run
          σ1).1
        exact mem_liftE (x := ([], y.2)) (mem_bind_nd hy rfl)
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], y.2), hm, th, G, Or.inl ⟨he, [], rfl⟩, hP, hCR', hFI',
        hDR'⟩
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩

/-- **The dispatch of `decode_invocation`, with the domain schedule**: as
`decode_invocation_refines`, from one `DecOKD` per cap type (the null and
zombie caps aside). -/
theorem decode_invocation_refinesD (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (cap : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef)
    (hK : ∀ c, cap = c → (∀ p zt n, c ≠ .Zombie p zt n) → c ≠ .Null →
      DecOKD (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOKD (L := L) arI s ar σ lbl length slot cap blk call don fp buf extra slbl args ci sl excaps buffer := by
  by_cases hn : cap = .Null
  · subst hn
    unfold DecOKD syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩
  by_cases hz : ∃ p zt n, cap = .Zombie p zt n
  · obtain ⟨p, zt, n, rfl⟩ := hz
    unfold DecOKD syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩
  exact hK cap rfl (fun p zt n e => hz ⟨p, zt, n, e⟩) hn

end

end

end Fl4Proofs.P3

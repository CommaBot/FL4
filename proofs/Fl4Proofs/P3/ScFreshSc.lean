/-
P3, scheduling contexts: **fresh SCs** (UtXHyp's new-object part, the SC
family; with ScFresh's TCB, notification, endpoint and reply families).

* `ScRelW.fresh`: an SC block whose header words (offsets below 96) are 0,
  placed, and not the idle SC, is related (weakly: it is not configured, its
  `REFILL_MAX` is 0) to the spec's `default_sched_context`.
* `SchedRel.add_scs`: fresh SCs `Wc` (of size `n`) join `C`, on core 0 (a new
  SC's `CORE` word is 0, as a new TCB's affinity), placed apart from the
  TCBs, the node, the kernel-global block, the notifications, the old SCs
  and each other; the spec's new objects are `.schedContext
  default_sched_context n`.
* `SchedRel.frame_new`: for a core `c ≠ 0` the relation is unaffected by the
  new objects (new TCBs and SCs belong to core 0's sets): FL4's memory agrees
  on what it reads (`SAgree`, the SC words), the spec only gains objects.
* `Inv.add`, `BlockedScActive.add`: the Sc proofs' spec invariants across
  fresh objects that are default TCBs and SCs (inactive, unbound) or other
  kinds.
-/
import Fl4Proofs.P3.ScFresh
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **A fresh SC's relation**: header words 0, placed, not the idle SC. -/
theorem ScRelW.fresh {s : S} {sc : U64} {n : Nat} (hpl : Fl4Proofs.P1.Placed sc (n + Fl4Spec.minSchedContextBits))
    (hm : ∀ K : U64, K.val < 96 → K.val % 8 = 0 → L.mem s (scW sc K) = 0#u64)
    (hid : sc.bv ≠ isc) : ScRelW st isc s sc Fl4Spec.defaultSchedContext n := by
  have hmax : L.rmax s sc = 0#u64 := by simp only [LawfulStore.rmax, maxA_eq]; exact hm _ (by simp) (by simp)
  have hper : L.rperiod s sc = 0#u64 := by simp only [LawfulStore.rperiod, periodA_eq]; exact hm _ (by simp) (by simp)
  refine ⟨hpl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => ?_, fun h => absurd h hid, ?_, fun h => ?_⟩
  · rw [hper]; rfl
  · rw [hm 8#u64 (by simp) (by simp)]; rfl
  · rw [hm 24#u64 (by simp) (by simp), optRef_zero]; rfl
  · rw [hm 40#u64 (by simp) (by simp), optRef_zero]; rfl
  · rw [hm 48#u64 (by simp) (by simp)]; rfl
  · rw [hm 56#u64 (by simp) (by simp), optRef_zero]; rfl
  · rw [hm 64#u64 (by simp) (by simp)]; rfl
  · exact absurd (hm 64#u64 (by simp) (by simp)) h
  · rw [hmax]; rfl
  · exact absurd (by rw [hmax]; rfl) h

/-- The fresh SCs' spec objects. -/
def SWc (Wc : Set U64) (p : Fl4Spec.ObjRef) : Prop := ∃ sc ∈ Wc, sc.bv = p

set_option maxHeartbeats 1000000 in
/-- **The scheduler relation over fresh SCs** (module docstring). -/
theorem SchedRel.add_scs {N T C Wc : Set U64} {c : U64} {s : S} {σ σ' : Fl4Spec.State Unit} {n : Nat}
    (hS : SchedRel st N T C c s σ) (hc0 : c = 0#u64)
    (hpl : ∀ sc ∈ Wc, Fl4Proofs.P1.Placed sc (n + Fl4Spec.minSchedContextBits))
    (hm : ∀ sc ∈ Wc, ∀ K : U64, K.val < 96 → K.val % 8 = 0 → L.mem s (scW sc K) = 0#u64)
    (hid : ∀ sc ∈ Wc, sc.bv ≠ σ.idleSc)
    (hout : ∀ sc ∈ Wc, ∀ a : U64, ScObj sc n a → ¬ NWrite N T a ∧
      (a.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ a.val) ∧ (∀ t ∈ T, a.val < t.val ∨ t.val + 4096 ≤ a.val) ∧
      (a.val < (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ a.val))
    (hdo : ∀ sc ∈ Wc, ∀ sc' ∈ C, ∀ x' n', σ.kheap sc'.bv = some (.schedContext x' n') → ∀ a : U64,
      ScObj sc n a → ¬ ScObj sc' n' a)
    (hdn : ∀ sc ∈ Wc, ∀ sc' ∈ Wc, sc ≠ sc' → ∀ a : U64, ScObj sc n a → ¬ ScObj sc' n a)
    (hσ : SpecAdd σ σ' (SWc Wc) (fun _ => .schedContext Fl4Spec.defaultSchedContext n)) :
    SchedRel st N T (C ∪ Wc) c s σ' := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := hσ.f
  have hnew : ∀ sc ∈ Wc, σ'.kheap sc.bv = some (.schedContext Fl4Spec.defaultSchedContext n) :=
    fun sc h => (hσ.new _ ⟨sc, h, rfl⟩).2
  -- an SC object of `σ'` at an address of `C ∪ Wc`
  have back : ∀ sc ∈ C ∪ Wc, ∀ x m, σ'.kheap sc.bv = some (.schedContext x m) →
      (sc ∈ C ∧ σ.kheap sc.bv = some (.schedContext x m)) ∨ (sc ∈ Wc ∧ x = Fl4Spec.defaultSchedContext ∧ m = n) := by
    intro sc hsc x m hk
    rcases hσ.kback hk with h | ⟨⟨sc', hsc', e⟩, h⟩
    · rcases hsc with hsc | hsc
      · exact Or.inl ⟨hsc, h⟩
      · rw [(hσ.new _ ⟨sc, hsc, rfl⟩).1] at h; cases h
    · have : sc' = sc := eq_of_bv e
      subst this
      cases h; exact Or.inr ⟨hsc', rfl, rfl⟩
  refine ⟨hS.placed, hS.nodeNW, hS.domNW, hS.dtNW, fun sc hsc x m hx a hao => ?_, ?_, hS.actW,
    by rw [e4]; exact hS.act, by rw [e8]; exact hS.repr, fun sc hsc => ?_, Q, R, hc, ?_⟩
  · rcases back sc hsc x m hx with ⟨h1, h2⟩ | ⟨h1, -, rfl⟩
    · exact hS.scOut sc h1 x m h2 a hao
    · exact hout sc h1 a hao
  · intro sc hsc sc' hsc' hne x m x' m' hx hx' a ha
    rcases back sc hsc x m hx with ⟨h1, h2⟩ | ⟨h1, -, rfl⟩ <;>
      rcases back sc' hsc' x' m' hx' with ⟨g1, g2⟩ | ⟨g1, -, rfl⟩
    · exact hS.scDisj sc h1 sc' g1 hne x m x' m' h2 g2 a ha
    · exact fun hb => hdo sc' g1 sc h1 x m h2 a hb ha
    · exact hdo sc h1 sc' g1 x' m' g2 a ha
    · exact hdn sc h1 sc' g1 hne a ha
  · rcases hsc with hsc | hsc
    · exact hS.core sc hsc
    · rw [hm sc hsc 16#u64 (by simp) (by simp), hc0]
  · refine ⟨fun p hp => by rw [e1]; exact hs.rq p hp, fun d p hd => by rw [e1]; exact hs.rqDom d p hd,
      by rw [e2]; exact hs.rel, by rw [e3]; exact hs.curThread, by rw [e5]; exact hs.curSc,
      by rw [e6]; exact hs.curTime, by rw [e7]; exact hs.consumed, by rw [e9]; exact hs.curDom,
      fun t ht => ?_, fun t ht h0 => Or.inl (hs.scMem t ht h0), fun sc hsc => ?_, by rw [e12]; exact hs.idleSc,
      by rw [e10]; exact hs.domTime, by rw [e11]; exact hs.idleTh⟩
    · obtain ⟨x, hk, h1, h2, h3, h4⟩ := hs.tcb t ht
      exact ⟨x, hσ.kold hk, h1, h2, h3, h4⟩
    · rcases hsc with hsc | hsc
      · obtain ⟨x, m, hk, e⟩ := hs.scs sc hsc
        exact ⟨x, m, hσ.kold hk, by rw [e12]; exact e⟩
      · exact ⟨_, n, hnew sc hsc, ScRelW.fresh (hpl sc hsc) (hm sc hsc) (by rw [e12]; exact hid sc hsc)⟩

set_option maxHeartbeats 1000000 in
/-- **The scheduler relation of a core whose sets gain nothing** (for `c ≠ 0`
across a retype: the new TCBs and SCs belong to core 0's sets): FL4's memory
agrees on what the relation reads, the action and reprogram words are kept,
and the spec only gains objects (at addresses that held none). -/
theorem SchedRel.frame_new {N T C : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    {W : Fl4Spec.ObjRef → Prop} {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject}
    (hS : SchedRel st N T C c s σ) (ha : SAgree st T C c s s')
    (hact : nodeW st s' c layout.node.SCHED_ACTION = nodeW st s c layout.node.SCHED_ACTION)
    (hrp : nodeW st s' c layout.node.REPROGRAM = nodeW st s c layout.node.REPROGRAM)
    (hσ : SpecAdd σ σ' W o) :
    SchedRel st N T C c s' σ' := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := hσ.f
  have hk := ha.ksb
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
  -- the SCs of `C` are old ones
  have hscC : ∀ sc ∈ C, ∀ x m, σ'.kheap sc.bv = some (.schedContext x m) → σ.kheap sc.bv = some (.schedContext x m) := by
    intro sc hsc x m hx
    rcases hσ.kback hx with h | ⟨hw, -⟩
    · exact h
    · obtain ⟨x0, m0, hk0, -⟩ := hs.scs sc hsc
      rw [(hσ.new _ hw).1] at hk0; cases hk0
  have hs' := hs.agree ha
  refine ⟨hS.placed, fun o' ho hn => ?_, fun hn => ?_, fun hn => ?_, fun sc hsc x m hx a hao => ?_,
    fun sc hsc sc' hsc' hne x m x' m' hx hx' a h => hS.scDisj sc hsc sc' hsc' hne x m x' m' (hscC sc hsc x m hx)
      (hscC sc' hsc' x' m' hx') a h,
    by rw [hact]; exact hS.actW, by rw [hact, e4]; exact hS.act, by rw [hrp, e8]; exact hS.repr,
    hs.core_eq ha.sc hS.core, Q, R, hc.agree ha.toC, ?_⟩
  · rw [nodeAt_ksb hk] at hn; exact hS.nodeNW o' ho hn
  · rw [curDomA_ksb hk] at hn; exact hS.domNW hn
  · rw [dtA_ksb hk] at hn; exact hS.dtNW hn
  · obtain ⟨o1, o2, o3, o4⟩ := hS.scOut sc hsc x m (hscC sc hsc x m hx) a hao
    exact ⟨o1, by rw [hnb]; exact o2, o3, by rw [hk]; exact o4⟩
  · refine ⟨fun p hp => by rw [e1]; exact hs'.rq p hp, fun d p hd => by rw [e1]; exact hs'.rqDom d p hd,
      by rw [e2]; exact hs'.rel, by rw [e3]; exact hs'.curThread, by rw [e5]; exact hs'.curSc,
      by rw [e6]; exact hs'.curTime, by rw [e7]; exact hs'.consumed, by rw [e9]; exact hs'.curDom,
      fun t ht => ?_, hs'.scMem, fun sc hsc => ?_, by rw [e12]; exact hs'.idleSc, by rw [e10]; exact hs'.domTime,
      by rw [e11]; exact hs'.idleTh⟩
    · obtain ⟨x, hk', h1, h2, h3, h4⟩ := hs'.tcb t ht
      exact ⟨x, hσ.kold hk', h1, h2, h3, h4⟩
    · obtain ⟨x, m, hk', e⟩ := hs'.scs sc hsc
      exact ⟨x, m, hσ.kold hk', by rw [e12]; exact e⟩

section Spec
open Fl4Spec

/-- The fresh objects the Sc invariants allow: default TCBs and SCs (no SC,
inactive; unconfigured, unbound), the default notification, or an object of
another kind. -/
def FreshOK (k : KernelObject) : Prop :=
  (∃ d, k = .tcb (defaultTcb d)) ∨ (∃ n, k = .schedContext defaultSchedContext n) ∨
    k = .notification defaultNotification ∨
    ((∀ x, k ≠ .tcb x) ∧ (∀ y n, k ≠ .schedContext y n) ∧ (∀ x, k ≠ .notification x))

theorem FreshOK.tcb {k : KernelObject} (h : FreshOK k) {x : Tcb} (hk : k = .tcb x) :
    x.tcbSchedContext = none ∧ x.tcbState = .inactive := by
  rcases h with ⟨d, rfl⟩ | ⟨n, rfl⟩ | rfl | ⟨h1, -, -⟩
  · cases hk; exact ⟨rfl, rfl⟩
  · cases hk
  · cases hk
  · exact absurd hk (h1 x)

theorem FreshOK.sc {k : KernelObject} (h : FreshOK k) {y : SchedContext} {n : Nat} (hk : k = .schedContext y n) :
    y = defaultSchedContext := by
  rcases h with ⟨d, rfl⟩ | ⟨m, rfl⟩ | rfl | ⟨-, h2, -⟩
  · cases hk
  · cases hk; rfl
  · cases hk
  · exact absurd hk (h2 y n)

theorem FreshOK.ntfn {k : KernelObject} (h : FreshOK k) {x : Notification} (hk : k = .notification x) :
    x.ntfnSc = none := by
  rcases h with ⟨d, rfl⟩ | ⟨m, rfl⟩ | rfl | ⟨-, -, h3⟩
  · cases hk
  · cases hk
  · cases hk; rfl
  · exact absurd hk (h3 x)

theorem default_not_active : scActive defaultSchedContext = false := rfl

/-- **`Inv` across fresh objects** (`FreshOK`). -/
theorem Inv.add {σ σ' : State Unit} {W : ObjRef → Prop} {o : ObjRef → KernelObject} (h : Inv σ)
    (hσ : SpecAdd σ σ' W o) (ho : ∀ p, W p → FreshOK (o p)) : Inv σ' := by
  obtain ⟨e1, e2, -, -, -, e6, -⟩ := hσ.f
  have kb : ∀ {p k}, σ'.kheap p = some k → σ.kheap p = some k ∨ FreshOK k := fun {p k} hk => by
    rcases hσ.kback hk with h | ⟨hw, rfl⟩
    · exact Or.inl h
    · exact Or.inr (ho p hw)
  have rtq : ∀ u ∈ σ.releaseQueue, specRt σ' u = specRt σ u := by
    intro u hu
    obtain ⟨x, scp, y, m, h1, h2, -, h4, h5⟩ := h.rel u hu
    rw [specRt_eq (hσ.kold h1) h2 (hσ.kold h4) (h.ne _ _ _ h4 h5), specRt_eq h1 h2 h4 (h.ne _ _ _ h4 h5)]
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun q y m hy ha => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q y m hy ha => ?_, fun q y m hy ha hp0 => ?_⟩
  · rw [e1] at hu
    obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rq d q u hu
    exact ⟨x, scp, y, m, hσ.kold h1, h2, h3, hσ.kold h4, h5⟩
  · rw [e2] at hu
    obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rel u hu
    exact ⟨x, scp, y, m, hσ.kold h1, h2, h3, hσ.kold h4, h5⟩
  · rw [e2]
    exact List.Pairwise.imp_of_mem (fun {a b} ha hb hab => by rw [rtq a ha, rtq b hb]; exact hab) h.sorted
  · rcases kb hx with hx0 | hf
    · intro x' scp y m h1 h2 h3 h4 h5
      rw [hx] at h1; cases h1
      rcases kb h3 with h3' | hf3
      · have := h.rd u x hx0 hc x scp y m hx0 h2 h3' h4 (by rw [e2] at h5; exact h5)
        unfold released at this ⊢; rw [e6]; exact this
      · rw [hf3.sc rfl] at h4; cases h4
    · obtain ⟨-, hst⟩ := hf.tcb rfl
      rw [hst] at hc
      rcases hc.cls with h | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h
  · rcases kb hy with hy0 | hf
    · exact h.refills q y m hy0 ha
    · rw [hf.sc rfl] at ha; cases ha
  · rcases kb hx with hx0 | hf
    · obtain ⟨y, m, h1, h2⟩ := h.back u x q hx0 hq
      exact ⟨y, m, hσ.kold h1, h2⟩
    · rw [(hf.tcb rfl).1] at hq; cases hq
  · rcases kb hx with hx0 | hf
    · obtain ⟨y, m, h1⟩ := h.ntfnSc q x q' hx0 hq
      exact ⟨y, m, hσ.kold h1⟩
    · rw [hf.ntfn rfl] at hq; cases hq
  · rcases kb hy with hy0 | hf
    · exact h.ne q y m hy0 ha
    · rw [hf.sc rfl] at ha; cases ha
  · rcases kb hy with hy0 | hf
    · exact h.rr q y m hy0 ha hp0
    · rw [hf.sc rfl] at ha; cases ha

/-- **[J] across fresh objects** (`FreshOK`). -/
theorem BlockedScActive.add {σ σ' : State Unit} {W : ObjRef → Prop} {o : ObjRef → KernelObject}
    (h : BlockedScActive σ) (hσ : SpecAdd σ σ' W o) (ho : ∀ p, W p → FreshOK (o p)) : BlockedScActive σ' := by
  have kb : ∀ {p k}, σ'.kheap p = some k → σ.kheap p = some k ∨ FreshOK k := fun {p k} hk => by
    rcases hσ.kback hk with h | ⟨hw, rfl⟩
    · exact Or.inl h
    · exact Or.inr (ho p hw)
  refine ⟨fun p y n t x hp hyt hx hq => ?_, fun p y n hp hr => ?_⟩
  · rcases kb hp with hp0 | hf
    · rcases kb hx with hx0 | hfx
      · exact h.tcb p y n t x hp0 hyt hx0 hq
      · rw [(hfx.tcb rfl).2] at hq; cases hq
    · rw [hf.sc rfl] at hyt; cases hyt
  · rcases kb hp with hp0 | hf
    · exact h.replies p y n hp0 hr
    · rw [hf.sc rfl] at hr; exact absurd rfl hr

end Spec

end

end

end Fl4Proofs.P3.Sched

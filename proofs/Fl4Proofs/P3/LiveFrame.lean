/-
P3 (DESIGN.md §9), KENTRY-PLAN g2i: **the `LiveDN` frame lemmas upstream of
the step closure** (moved unchanged from XTopJointDbgKeep, XTopJointLiveStep
and XTopJointLiveIns so that XTopJointStep's `stepClosed_jat` can build the
`JAtZ.live` field): the debug-word exclusions (`dbgKeep_of_writes`,
`JAtZ.notDbg'`, `JAtZ.notDbg`, `JAtZ.slot_node`, `JAtZ.inSlot_notDbg`,
`JAtZ.ksW_notDbg`, `JAtZ.schW_notDbg`), `shape`'s facts, `ZNoBlk`,
`refsObj_objRefs`, and `LiveDN.wstepX` (XTopJointLiveStep's `LiveDN.wstep`
with the `XTopAt` after and the dead TCB zombies after in place of a `JAtZ`
after).
-/
import Fl4Proofs.P3.XTopJoint
import Fl4Proofs.P3.ScJointFrame
import Fl4Proofs.P3.IpcSlotsSameZ
import Fl4Proofs.P1.QueueIpc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

theorem refs_shape (q : U64) (c : capability.Cap) : RefsObj q (shape c) ↔ RefsObj q c := by
  cases c <;> exact Iff.rfl

theorem shape_refs {c' c : capability.Cap} (h : shape c' = shape c) (q : U64) : RefsObj q c' ↔ RefsObj q c := by
  rw [← refs_shape q c', h, refs_shape]

theorem shape_thread (c : capability.Cap) (w : U64) : shape c = .Thread w ↔ c = .Thread w := by
  cases c <;> simp [shape]

theorem shape_zombie (c : capability.Cap) (p zt n : U64) : shape c = .Zombie p zt n ↔ c = .Zombie p zt n := by
  cases c <;> simp [shape]

/-- **No zombie names an object inside the kernel-state block** [J]
(module docstring). -/
def ZNoBlk (th : TypedHeap) (m : U64 → U64) (kb : U64) : Prop :=
  ∀ y, IsSlot th y → ∀ p zt n, capV m y = .Zombie p zt n → ∀ k, th p = some k →
    ¬ (kb.val ≤ p.val ∧ p.val + objSize k ≤ kb.val + 13568)

theorem ZNoBlk.of_same {th : TypedHeap} {m m' : U64 → U64} {kb kb' : U64} (h : ZNoBlk th m kb)
    (hS : SlotsSame th m m') (hk : kb' = kb) : ZNoBlk th m' kb' := by
  subst hk
  intro y hy p zt n hz
  exact h y hy p zt n (by rw [← hS.capV hy]; exact hz)

/-- **A cap naming a container names it as an object.** -/
theorem refsObj_objRefs {q : U64} {c : capability.Cap} (h : RefsObj q c) : q.bv ∈ Fl4Spec.objRefs (absCap c) := by
  cases c <;> simp only [RefsObj] at h <;> subst h <;> simp [absCap, Fl4Spec.objRefs]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

/-- The spec's idle thread kept by every outcome of a deletion step (the
`GK` family) or a `CnK` step. -/
theorem _root_.Fl4Proofs.P3.Ipc.CnK.idle {σ σ' : Fl4Spec.State Unit} (h : Ipc.CnK σ σ') :
    σ'.idleThread = σ.idleThread :=
  by have e := congrArg Fl4Spec.AbstractState.idleThread h.1; exact e

/-- **The idle word kept**, from the spec's idle thread kept (`XTopAt.idleThread_bv`). -/
theorem XTopAt.idleW_eqS {Z Z' : XSets} {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hX' : XTopAt (L := L) AR Z' s' a' σ')
    (h : σ'.idleThread = σ.idleThread) : L.idleW s' = L.idleW s :=
  P1.eq_of_bv (by rw [← XTopAt.idleThread_bv hX', ← XTopAt.idleThread_bv hX]; exact h)

/-- **`DbgWFL` across a step keeping the debug words** (the affinities by the
`XTopAt`s' lists; as `liveDN_frame`). -/
theorem dbgWFL_step {Z Z' : XSets} {H : P1.Heap} {Cs : Set U64} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX0 : XTopAt (L := L) AR Z s a σ) (hX : XTopAt (L := L) AR Z' s' a' σ')
    (hT : Z'.T = Z.T) (hc : Z'.c = Z.c) (hTe : Z.T = P1.Heap.tcbs H) {lst : U64 → List U64}
    (hW : DbgWFL (P1.Heap.tcbs H) Cs (L.mem s) (dbgHd (L := L) s) lst)
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') :
    DbgWFL (P1.Heap.tcbs H) Cs (L.mem s') (dbgHd (L := L) s') lst := by
  obtain ⟨Q0, R0, hc0, -⟩ := hX0.fin.1.1.1.lists
  obtain ⟨Q1, R1, hc1, -⟩ := hX.fin.1.1.1.lists
  refine hW.of_keep hK fun y hy => ?_
  rw [hc1.aff y (by rw [hT, hTe]; exact hy), hc0.aff y (by rw [hTe]; exact hy), hc]

/-- **The TCB zombies after were TCB zombies before** when every zombie after
was one before. -/
theorem ZTcb.of_zombies {th : TypedHeap} {s s' : S}
    (hZ : ∀ y, IsSlot th y → ∀ p zt n, capV (L.mem s') y = .Zombie p zt n →
      ∃ y0, IsSlot th y0 ∧ capV (L.mem s) y0 = .Zombie p zt n)
    {p : U64} (hp : p ∈ ZTcb (L := L) th s') : p ∈ ZTcb (L := L) th s := by
  obtain ⟨y, hy, zt, n, hz, h65⟩ := hp
  obtain ⟨y0, hy0, hz0⟩ := hZ y hy p zt n hz
  exact ⟨y0, hy0, zt, n, hz0, h65⟩

/-- **`DbgKeep` from a middle state** (both from `s`). -/
theorem dbgKeep_cancel {T Cs : Set U64} {s s2 s6 : S} (h1 : P1.DbgKeep st T Cs s s2) (h2 : P1.DbgKeep st T Cs s s6) :
    P1.DbgKeep st T Cs s2 s6 :=
  ⟨h2.1.trans h1.1.symm, fun b hb => by
    have hb' := P1.DbgW.ksb h1.1 hb
    rw [h2.2 b hb', h1.2 b hb']⟩

/-- **Writes avoiding the debug words keep them.** -/
theorem dbgKeep_of_writes {T Cs Ω : Set U64} {H : P1.Heap} {Sg Rp Scs Nt : Set U64} {Zb : U64 → Nat}
    {Ac : Set U64} {s s' : S} (h : P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Zb Ac s) {B : U64 → Prop}
    (hw : P1.WritesIn st s s' B) (hB : ∀ b, B b → ¬ P1.DbgW st T Cs s b) : P1.DbgKeep st T Cs s s' :=
  ⟨hw.1, fun b hb => hw.mem_eq (P1.dbgW_aligned h hb) fun h' => hB b h' hb⟩

/-- **A word outside the TCBs and off the nodes' head words is no debug word.** -/
theorem JAtZ.notDbg' {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hobj : ∀ p, H p = some .tcb → b.val < p.val ∨ p.val + 2 ^ P1.HKind.bits .tcb ≤ b.val)
    (hnode : ∀ c ∈ Cs, b.val ≠ L.nodeBase s c + 88) :
    ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hT := hq.tcbs
  have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
  rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
  · have h1 := hobj y hy
    rw [e, show P1.dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, P1.field_val (hT y hy) (by simp), e12]
      at h1
    have : (3576#u64 : U64).val = 3576 := by simp
    omega
  · have h1 := hobj y hy
    rw [e, show P1.dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, P1.field_val (hT y hy) (by simp), e12]
      at h1
    have : (3584#u64 : U64).val = 3584 := by simp
    omega
  · have h1 := hnode c hc
    rw [e, P1.nodeAt_val (hq.nodes c hc) (by simp [P1.debug_val]), P1.debug_val] at h1
    exact h1 rfl

/-- **A word outside the TCBs and the nodes is no debug word.** -/
theorem JAtZ.notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hobj : ∀ p, H p = some .tcb → b.val < p.val ∨ p.val + 2 ^ P1.HKind.bits .tcb ≤ b.val)
    (hnode : ∀ c ∈ Cs, b.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ b.val) :
    ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b :=
  J.notDbg' hobj fun c hc => by rcases hnode c hc with h | h <;> omega

/-- A slot lies apart from every core's node (its object, an object of `H`,
does: `JKern.hnd`). -/
theorem JAtZ.slot_node {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {x : U64} (hx : IsSlot Z.th x) {c : U64} (hc : c ∈ Cs) :
    x.val + 32 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ x.val := by
  obtain ⟨p, i, hpi, rfl⟩ := hx
  have hv := hpi.val J.xtop.rel.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  rcases hpi with ⟨r, hp, hi⟩ | ⟨hp, hi⟩
  · have h1 := J.kern.hnd p _ (hJ.cnode p r hp) c hc
    simp only [P1.HKind.bits] at h1
    rw [pow_add] at h1
    rw [hv]
    generalize 2 ^ r = M at h1 hi
    omega
  · have h1 := J.kern.hnd p _ ((hJ.tcb p).1 hp) c hc
    simp only [P1.HKind.bits, tcbSlots] at h1 hi
    rw [hv]
    omega

/-- **A slot word is no debug word** (the TCBs' slots below their offset
256, `SlotsApart`; the slots apart from the nodes, `JAtZ.slot_node`). -/
theorem JAtZ.inSlot_notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : InSlot Z.th b) : ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  obtain ⟨x, hx, h1, h2⟩ := hb
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hT := hq.tcbs
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
  · have h3 := (J.apart x hx).1 y (hTe ▸ hy)
    rw [e, show P1.dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, P1.field_val (hT y hy) (by simp)]
      at h1 h2
    have : (3576#u64 : U64).val = 3576 := by simp
    omega
  · have h3 := (J.apart x hx).1 y (hTe ▸ hy)
    rw [e, show P1.dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, P1.field_val (hT y hy) (by simp)]
      at h1 h2
    have : (3584#u64 : U64).val = 3584 := by simp
    omega
  · have h3 := J.slot_node hx hc
    rw [e, P1.nodeAt_val (hq.nodes c hc) (by simp [P1.debug_val]), P1.debug_val] at h1 h2
    omega

/-- **A word apart from the TCBs' debug links and the nodes' debug heads is no
debug word** (the links at TCB offsets 3576 and 3584). -/
theorem JAtZ.notDbg_tw {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (htcb : ∀ y ∈ Z.T, ∀ (w : U64) (K : Nat), w.val = y.val + K → 3576 ≤ K → K < 4096 → b ≠ w)
    (hnode : ∀ c ∈ Cs, b ≠ L.nodeAt s c layout.node.DEBUG_TCBS) :
    ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hT := hq.tcbs
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
  · have h3 : (3576#u64 : U64).val = 3576 := by simp
    exact htcb y (by rw [hTe]; exact hy) _ 3576
      (by rw [show P1.dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, P1.field_val (hT y hy) (by simp), h3])
      le_rfl (by norm_num) e
  · have h3 : (3584#u64 : U64).val = 3584 := by simp
    exact htcb y (by rw [hTe]; exact hy) _ 3584
      (by rw [show P1.dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, P1.field_val (hT y hy) (by simp), h3])
      (by norm_num) (by norm_num) e
  · exact hnode c hc e

/-- Two TCB words at different offsets differ (the TCBs 4096-aligned). -/
theorem tcbOff_ne {T : Set U64} (hT : P1.TcbPlaced T) {t u b w : U64} (ht : t ∈ T) (hu : u ∈ T) {K K' : Nat}
    (hb : b.val = t.val + K) (hw : w.val = u.val + K') (hK : K < 4096) (hK' : K' < 4096) (hne : K ≠ K') :
    b ≠ w := by
  intro e
  rw [e] at hb
  have a1 := (hT t ht).align; have a2 := (hT u hu).align
  by_cases eu : u = t
  · subst eu; omega
  · have : u.val ≠ t.val := fun h => eu (UScalar.eq_of_val_eq h)
    omega

/-- **A notification step's word (`NWrite`) is no debug word.** -/
theorem JAtZ.nwrite_notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : Notif.NWrite Z.N Z.T b) :
    ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  have hT : P1.TcbPlaced Z.T := J.ip.e.tcb
  have hH := J.kern.heap
  rcases hb with ⟨n, hn, g1, g2⟩ | ⟨t, ht, h⟩
  · have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
    refine J.notDbg (fun p hp => ?_) (fun c hc => ?_)
    · have hpn : p ≠ n := fun e => by rw [e, hHn] at hp; cases hp
      have e := hH.disj p _ n _ hp hHn hpn
      simp only [P1.HKind.bits] at e ⊢
      omega
    · have := J.kern.hnd n _ hHn c hc
      simp only [P1.HKind.bits] at this
      omega
  · have hv := nfootT_val (hT t ht) (b := b) (by
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    refine J.notDbg_tw (fun y hy w K hwv h1 h2 => ?_) (fun c hc => ?_)
    · rcases hv with e | e | e | e | e | e <;> exact tcbOff_ne hT ht hy e hwv (by omega) (by omega) (by omega)
    · intro e
      have hN : P1.NodePlaced st Z.T s c := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk c hc
      have hnv := P1.nodeAt_val hN (off := layout.node.DEBUG_TCBS) (by simp)
      have := J.kern.hnd t _ (J.zH.1 t ht) c hc
      simp only [P1.HKind.bits] at this
      rw [← e] at hnv
      have hd88 : layout.node.DEBUG_TCBS.val = 88 := P1.debug_val
      rcases hv with e' | e' | e' | e' | e' | e' <;> omega

/-- A kernel-state word (`KsW`) is no debug word: below the nodes, outside
the TCBs (`ksOut`). -/
theorem JAtZ.ksW_notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : KsW (L.ksb s) b) : ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  obtain ⟨K, h1, h2, -, e, -⟩ := hb
  refine J.notDbg' (fun p hp => ?_) (fun c _ => ?_)
  · obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
    have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
    rw [e12]
    rcases hq.ksOut p hp with h | h <;> omega
  · have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
    rw [hnb]; omega

/-- **A scheduler step's word is no debug word** (`SchW`: the TCBs' queue
words, the current node but its debug head, the domain words). -/
theorem JAtZ.schW_notDbg {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : SchW (L := L) Z.T Z.c s b) : ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  have hS := J.xtop.fin.1.1.1
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hnb : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
  rcases hb with ⟨y, hy, e | e | e⟩ | hn | hd
  · subst e; exact P1.notDbgW_field hq.tcbs hq.nodes (hTe ▸ hy) (by simp) (by simp)
  · subst e; exact P1.notDbgW_field hq.tcbs hq.nodes (hTe ▸ hy) (by simp) (by simp)
  · subst e; exact P1.notDbgW_field hq.tcbs hq.nodes (hTe ▸ hy) (by simp) (by simp)
  · have hk : Sched.KFoot st Z.T Z.N Z.C Z.c s σ b := Sched.KFoot.of_sfoot (Or.inr ⟨hn.1, hn.2.1⟩)
    rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
    · exact Sched.KFoot.ne_tcbw hS hk (by rw [hTe]; exact hy) (K := 3576#u64) (by simp)
        (by unfold Sched.SOff Sched.SOffL; decide) e
    · exact Sched.KFoot.ne_tcbw hS hk (by rw [hTe]; exact hy) (K := 3584#u64) (by simp)
        (by unfold Sched.SOff Sched.SOffL; decide) e
    · obtain ⟨h1, h2, h3⟩ := hn
      have h4 := congrArg UScalar.val e
      rw [P1.nodeAt_val (hq.nodes c hc) (by simp [P1.debug_val]), P1.debug_val] at h4
      rw [hnb] at h1 h2 h3 h4
      omega
  · have hv := domKW_val hd
    refine J.notDbg' (fun p hp => ?_) (fun c _ => ?_)
    · have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
      rw [e12]; rcases hq.ksOut p hp with h | h <;> omega
    · rw [hnb]; omega

set_option maxHeartbeats 4000000 in
/-- **A step writing slot words at the slots `W` keeps `LiveDN` and
`ZNoBlk`** (XTopJointLiveStep's `LiveDN.wstep`, with the `XTopAt` after
and the TCB zombies' TCBs dead after). -/
theorem LiveDN.wstepX {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hZB : ZNoBlk Z.th (L.mem s) (L.ksb s))
    {G' : MdbGhost} {V' : XVs} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a' σ')
    (hdead : ∀ p ∈ ZTcb (L := L) Z.th s, Sched.DeadP (L := L) H s' p)
    (hid : σ'.idleThread = σ.idleThread) (hw : P1.WritesIn st s s' (InSlot Z.th))
    (W : List Fl4Spec.CslotPtr)
    (hW : ∀ sl ∈ W, ∃ p r, sl.1 = p.bv ∧ Z.th p = some (.cnode r) ∧ sl.2.length = r ∧
      DestLive Z.th (L.mem s) (L.ksb s) p)
    (hcW : ∀ y, IsSlot Z.th y → (∀ sl ∈ W, y ≠ cslotAddr sl) → capV (L.mem s') y = capV (L.mem s) y)
    (hoW : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ sl ∈ W)
    (hNO : ∀ sl ∈ W, capV (L.mem s') (cslotAddr sl) = .Null → σ'.isOriginalCap sl = false)
    (hZ : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s') y = .Zombie p zt n →
      ∃ y0, IsSlot Z.th y0 ∧ capV (L.mem s) y0 = .Zombie p zt n)
    (hK2 : ∀ y0, IsSlot Z.th y0 → capV (L.mem s) y0 ≠ .Null →
      ∃ y, IsSlot Z.th y ∧ capV (L.mem s') y ≠ .Null ∧ shape (capV (L.mem s') y) = shape (capV (L.mem s) y0)) :
    LiveDN (L := L) Z.th H Cs G' s' σ' ∧ ZNoBlk Z.th (L.mem s') (L.ksb s') := by
  obtain ⟨hL, ⟨lst, hDW⟩, hN⟩ := hLv
  have hP : Placed Z.th := J.xtop.rel.1
  have hM := J.xtop.rel.2.1.2.2.1
  have hM' := hX'.rel.2.1.2.2.1
  have hFI := J.xtop.rel.2.2.1
  have hks : L.ksb s' = L.ksb s := hw.1
  have hmemS : ∀ y ∈ Z.G.chains.flatten, IsSlot Z.th y := fun y hy => ((hM.members y).1 hy).1
  have hmemN : ∀ y ∈ Z.G.chains.flatten, capV (L.mem s) y ≠ .Null := fun y hy => by
    obtain ⟨-, c0, h0, hn0⟩ := (hM.members y).1 hy
    rw [capV_of_capAt h0]; exact hn0
  have hinG' : ∀ y, IsSlot Z.th y → capV (L.mem s') y ≠ .Null → y ∈ G'.chains.flatten := fun y hy hn =>
    (hM'.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩
  -- the written slots
  have hWat : ∀ sl ∈ W, ∃ p r i, Z.th p = some (.cnode r) ∧ IsSlotAt Z.th p i ∧ cslotAddr sl = slotOf p i ∧
      AbsSlot Z.th sl ∧ DestLive Z.th (L.mem s) (L.ksb s) p := fun sl hsl => by
    obtain ⟨p, r, h1, hp, hl, hDL⟩ := hW sl hsl
    have hA : AbsSlot Z.th sl := ⟨p, h1, Or.inl (by rw [hl]; exact hp)⟩
    obtain ⟨p', i, hpi, h1', hxe⟩ := hA.at
    have e : p' = p := P1.eq_of_bv (h1'.symm.trans h1)
    subst e
    exact ⟨p', r, i, hp, hpi, hxe, hA, hDL⟩
  -- a live container stays covered
  have hcov : ∀ p r i, Z.th p = some (.cnode r) → IsSlotAt Z.th p i → DestLive Z.th (L.mem s) (L.ksb s) p →
      (∃ y ∈ G'.chains.flatten, RefsObj p (capV (L.mem s') y)) ∨ KsSlot (L.ksb s') (slotOf p i) := by
    intro p r i hp hpi hDL
    rcases hDL with ⟨y, r', gs, g, hy, hc⟩ | hb
    · obtain ⟨y', hy', hn', hsh⟩ := hK2 y hy (by rw [hc]; exact fun h => by cases h)
      exact Or.inl ⟨y', hinG' y' hy' hn', (shape_refs hsh p).2 (by rw [hc]; rfl)⟩
    · right
      obtain ⟨hb1, hb2⟩ := hb _ hp
      have hi : i < 2 ^ r := by
        rcases hpi with ⟨r'', hp', hi⟩ | ⟨hp', -⟩
        · rw [hp] at hp'; cases hp'; exact hi
        · rw [hp] at hp'; cases hp'
      have hfit := hP.fits p _ hp
      simp only [objSize] at hb2 hfit
      have hsv : (slotOf p i).val = p.val + 32 * i := slotOf_val (by omega)
      show (L.ksb s').val ≤ (slotOf p i).val ∧ (slotOf p i).val < (L.ksb s').val + 13568
      rw [hks, hsv]
      omega
  -- no zombie names a live container
  have hnz : ∀ p r, Z.th p = some (.cnode r) → DestLive Z.th (L.mem s) (L.ksb s) p →
      ∀ y, IsSlot Z.th y → ∀ zt n, capV (L.mem s) y ≠ .Zombie p zt n := by
    intro p r hp hDL y hy zt n hz
    rcases hDL with ⟨y1, r', gs, g, hy1, hc⟩ | hb
    · have hne : y1 ≠ y := fun e => by rw [e, hz] at hc; cases hc
      exact FinInv.zombie_alone hFI hM hy hz y1 hy1 hne (refsObj_objRefs (by rw [hc]; rfl))
    · exact hZB y hy p zt n hz _ hp (hb _ hp)
  -- a slot off `W` in use after was in use before
  have hU : ∀ y, IsSlot Z.th y → (∀ sl ∈ W, y ≠ cslotAddr sl) → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := by
    intro y hy hyW hu
    rcases hu with hu | ⟨x, hx, ho⟩
    · exact Or.inl (by rw [← hcW y hy hyW]; exact hu)
    · rcases hoW x ho with ho' | hxW
      · exact Or.inr ⟨x, hx, ho'⟩
      · exact (hyW x hxW hx.symm).elim
  -- the debug words
  have hdk : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' := dbgKeep_of_writes J.blk hw fun _ hb => J.inSlot_notDbg hb
  have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s := ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
  have hc0 : 0#u64 ∈ Cs := J.kern.cs0
  have hhd : dbgHead (L := L) s' = dbgHead (L := L) s := by
    unfold dbgHead
    rw [nodeAt_of_ksb hdk.1]
    exact hdk.2 _ (Or.inr ⟨0#u64, hc0, rfl⟩)
  have hNt : ∀ k, dbgNth (L.mem s') k (dbgHead (L := L) s') = dbgNth (L.mem s) k (dbgHead (L := L) s) :=
    fun k => by
      rw [hhd]
      exact dbgNth_keep (fun y hy => hdk.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (fun y hy => hTz.dn y hy) k _
        (hTz.dh _ hc0)
  have hL' : LiveJ (L := L) Z.th H G' s' σ' := by
    refine ⟨fun q i hqi hu => ?_, fun k hk hki => ?_, fun y hy p zt n hz i hpi hni hu => ?_,
      fun y hy p zt n hz hzt => ?_⟩
    · by_cases hyW : ∀ sl ∈ W, slotOf q i ≠ cslotAddr sl
      · rcases hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hyW hu) with ⟨y, hy, hr⟩ | hb
        · obtain ⟨y', hy', hn', hsh⟩ := hK2 y (hmemS y hy) (hmemN y hy)
          exact Or.inl ⟨y', hinG' y' hy' hn', (shape_refs hsh q).2 hr⟩
        · exact Or.inr (by rw [hks]; exact hb)
      · push_neg at hyW
        obtain ⟨sl, hsl, e⟩ := hyW
        obtain ⟨p, r, i', hp, hpi, hxe, -, hDL⟩ := hWat sl hsl
        obtain ⟨e1, e2⟩ := slotOf_inj hP hqi hpi (e.trans hxe)
        subst e1; subst e2
        exact hcov q r i hp hqi hDL
    · rw [hNt] at hk hki ⊢
      obtain ⟨y, hy, hr⟩ := hL.dbg k hk (by rw [← hid]; exact hki)
      obtain ⟨y', hy', hn', hsh⟩ := hK2 y (hmemS y hy) (hmemN y hy)
      rw [hr] at hsh
      have hsh' : shape (capV (L.mem s') y') = .Thread (dbgNth (L.mem s) k (dbgHead (L := L) s)) := hsh
      exact ⟨y', hinG' y' hy' hn', (shape_thread _ _).1 hsh'⟩
    · obtain ⟨y0, hy0, hz0⟩ := hZ y hy p zt n hz
      by_cases hyW : ∀ sl ∈ W, slotOf p i ≠ cslotAddr sl
      · exact hL.zslots y0 hy0 p zt n hz0 i hpi hni (hU _ ⟨p, i, hpi, rfl⟩ hyW hu)
      · push_neg at hyW
        obtain ⟨sl, hsl, e⟩ := hyW
        obtain ⟨p', r, i', hp, hpi', hxe, -, hDL⟩ := hWat sl hsl
        obtain ⟨e1, -⟩ := slotOf_inj hP hpi hpi' (e.trans hxe)
        subst e1
        exact hnz p r hp hDL y0 hy0 zt n hz0
    · obtain ⟨y0, hy0, hz0⟩ := hZ y hy p zt n hz
      exact hdead p ⟨y0, hy0, zt, n, hz0, hzt⟩
  refine ⟨⟨hL', ⟨lst, hDW.of_keep hdk fun y hy => by
      obtain ⟨Q0, R0, hc0, -⟩ := J.xtop.fin.1.1.1.lists
      obtain ⟨Q1, R1, hc1, -⟩ := hX'.fin.1.1.1.lists
      rw [hc1.aff y (by rw [← J.tcbs_eq.1] at hy; exact hy), hc0.aff y (by rw [← J.tcbs_eq.1] at hy; exact hy)]; try rfl⟩, fun sl hA h => ?_⟩, fun y hy p zt n hz => ?_⟩
  · by_cases hsW : sl ∈ W
    · exact hNO sl hsW h
    · have hne : ∀ sl' ∈ W, cslotAddr sl ≠ cslotAddr sl' := fun sl' hsl' e => by
        obtain ⟨-, -, -, -, -, -, hA', -⟩ := hWat sl' hsl'
        exact hsW (by rw [cslotAddr_inj hP hA hA' e]; exact hsl')
      have h0 : capV (L.mem s) (cslotAddr sl) = .Null := by rw [← hcW _ hA.isSlot hne]; exact h
      cases ho : σ'.isOriginalCap sl
      · rfl
      · rcases hoW sl ho with ho' | hm
        · rw [hN sl hA h0] at ho'; cases ho'
        · exact absurd hm hsW
  · obtain ⟨y0, hy0, hz0⟩ := hZ y hy p zt n hz
    rw [hks]; exact hZB y0 hy0 p zt n hz0

end

end

end Fl4Proofs.P3

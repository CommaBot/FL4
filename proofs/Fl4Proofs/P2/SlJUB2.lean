/-
# P2 (line slhuf, gen 4): `SlPreB` across a user-word write

With P2/SlJUB.lean's machinery (`NU`, the commuting lemma `SlJAt.lp_wr`, `flt_chk_back`),
every field of `SlPreB` but the three ReplyRecv-check-guarded ones (`hPl`, `hy0r`, `hSu`) is
carried from `s` to `L.wr s b v` (`b` a user word) at a bundle state:

* static or entry-state fields (`hT`, `hN`, `hcT`, `aff`, `hSt`, `hlk`): the words are TCB or
  node words (`wr_nu`, `safe0_wr`);
* `hI` (P1's `BXI` at the prefix state): `bxi_user`, P1's `xfer_all` with the user words as
  transfer words, given P1's `UserOK` for the layout's user words (`hUO` [J] below);
* `hAs` (`AsidOff`): the ASID table words are `Ω` words, hence no user words (`UserOK`);
* `hF` (`FaultEntAt`): `AsidOff` as above, and m61's `FaultEnt` moved by `faultEnt_ag` (queue
  links, endpoint, node, buffer-slot words: all `NU`), the checks moved back by `flt_chk_back`;
* `hTm` (`TimerOK`): `timerOK_ag` (TCB timer words; the timer-tree words of the nodes of `Cs`,
  `NU` by `UserOK`);
* `hrecv`, `hy0f`, `hSd`: the checks moved back, the receiver's words are TCB words;
* `hrz`: the reply's link words (`fl4-sync`'s reply is a heap reply, `SlSyncC`).

Premises of `SlJAt.preB_wr`: `hUO` [J] P1's `UserOK st T Cs Ω H K.user` at the entry (the
user words lie outside the TCBs, the nodes of `Cs`, `Ω` and the endpoints / notifications:
P1's `UserOK` for P1's own sets, as `EntryInv` carries it), `SlSyncC` (part of `SlQ`), the
locks (`hlk` [P]) and `SlPreRR` at the written state (the three ReplyRecv-guarded fields).
-/
import Fl4Proofs.P2.SlJUB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem Ag.writesIn {K : KLayout} {X X' : S} (G : Ag st (NU K) X X') : WritesIn st X X' (· ∈ K.user) :=
  ⟨G.k, G.c, fun b hb hn => G.m b ⟨hb, hn⟩⟩

/-- A user-word write keeps every `NU` word. -/
theorem wr_nu {K : KLayout} {s : S} {b x : U64} (hba : Aligned b) (hb : b ∈ K.user) (v : U64)
    (h : NU K x) : L.mem (L.wr s b v) x = L.mem s x :=
  mem_wr_ne' hba h.1 (fun e => h.2 (e ▸ hb))

/-- A reply object's words are `NU`. -/
theorem nu_rp {K : KLayout} (hX : RegionOKX K) {p : U64} (hp : K.heap p = some .reply) {o : U64}
    (h1 : o.val < 32) (h2 : o.val % 8 = 0) : NU K (core.num.U64.wrapping_add p o) := by
  obtain ⟨r, a⟩ := hX.rpW p hp o h1 h2
  exact nu_of_region hX a (by rw [r]; intro h; cases h)

/-- A node word of a core of `Cs` is `NU`, given P1's `UserOK` for the layout's user words. -/
theorem nu_nodeCs {K : KLayout} {T Cs Ω : Set U64} {H : Heap} {s X : S}
    (hUO : UserOK st T Cs Ω H K.user s) (hk : L.ksb X = L.ksb s) {c : U64} (hc : c ∈ Cs)
    (hN : NodePlaced st T X c) {o : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    NU K (L.nodeAt X c o) := by
  refine ⟨nodeAt_aligned hN ho h8, fun hu => ?_⟩
  have h := ((hUO _ hu).1).2.2 c hc
  have v := nodeAt_val hN ho
  have e : L.nodeBase X c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
  rw [v, e] at h
  omega

/-- `Safe0` of a heap TCB is kept by a user-word write. -/
theorem safe0_wr {K : KLayout} {s : S} (hX : RegionOKX K) {b : U64} (hb : b ∈ K.user) (hba : Aligned b)
    (v : U64) {d : U64} (hd : K.heap d = some .tcb) {c : U64} {lk : U64 → Prop}
    (h : Safe0 c lk (L.mem s) d) : Safe0 c lk (L.mem (L.wr s b v)) d := by
  unfold Safe0 at h ⊢
  rw [wr_nu (x := fld d oAFFINITY) hba hb v
      (nu_tcb hX hd (by rw [oAFF_val]; omega) (by rw [oAFF_val]; omega) (by rw [oAFF_val])),
    wr_nu (x := fld d oSTATE) hba hb v
      (nu_tcb hX hd (by rw [oSTATE_val]; omega) (by rw [oSTATE_val]; omega) (by rw [oSTATE_val])),
    wr_nu (x := fld d oBLOCK_OBJ) hba hb v
      (nu_tcb hX hd (by rw [oBOBJ_val]; omega) (by rw [oBOBJ_val]; omega) (by rw [oBOBJ_val]))]
  exact h

/-! ## P1's facts at agreeing states -/

variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **`BXI` across a write of user words** (P1's `xfer_all`, the user words as transfer words). -/
theorem bxi_user {K : KLayout} {X X' : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X)
    (hU : UserOK st T Cs Ω H K.user X) (W : WritesIn st X X' (· ∈ K.user)) :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X' := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -⟩ := xfer_all h0 hB hX hS hSg hU (W.mono fun b hb => Or.inr hb)
  exact ⟨⟨Q, R, h1⟩, hB1, hX1, hSg1, hS1⟩

/-- **`AsidOff` at an agreeing state**: the ASID table words are `Ω` words, no user words. -/
theorem asidOff_ag {K : KLayout} {X X' : S} (hΩ : ∀ b ∈ K.user, b ∉ Ω)
    (hal : ∀ hi : U64, hi.val < 2048 → Aligned (atAF (L.ksb X) hi)) (G : Ag st (NU K) X X')
    (h : AsidOff (L := L) Ω Sg X) : AsidOff (L := L) Ω Sg X' := by
  intro hi hhi
  rw [G.k]
  have e : L.mem X' (atAF (L.ksb X) hi) = L.mem X (atAF (L.ksb X) hi) :=
    G.m _ ⟨hal hi hhi, fun hu => hΩ _ hu (h hi hhi).1⟩
  rw [e]
  exact h hi hhi

/-- **`TimerOK` at an agreeing state** (TCB timer words, the nodes' timer-tree words). -/
theorem timerOK_ag {K : KLayout} {s X X' : S} (hUO : UserOK st T Cs Ω H K.user s)
    (hk : L.ksb X = L.ksb s) (hX : RegionOKX K) (hTH : ∀ y ∈ T, K.heap y = some .tcb)
    (G : Ag st (NU K) X X') (h : TimerOK st T Cs X) : TimerOK st T Cs X' := by
  have e : ∀ y ∈ T, ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      L.mem X' (core.num.U64.wrapping_add y o) = L.mem X (core.num.U64.wrapping_add y o) :=
    fun y hy o h1 h2 h3 => G.m _ (nu_tcb hX (hTH y hy) h1 h2 h3)
  have en : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem X' (L.nodeAt X' c o) = L.mem X (L.nodeAt X c o) := fun c hc o ho h8 => by
    rw [nodeAt_of_ksb G.k]; exact G.m _ (nu_nodeCs hUO hk hc (h.npl c hc) ho h8)
  refine ⟨fun c hc => NodePlaced.of_ksb G.k (h.npl c hc), fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun c hc => ?_, fun c hc => ?_, fun y hy h0 c hc' => ?_, fun y hy => ?_, fun y hy => ?_, fun c hc => ?_⟩
  · unfold tlA; rw [e y hy 3544#u64 (by simp) (by simp) (by simp)]; exact h.lt y hy
  · unfold trA; rw [e y hy 3552#u64 (by simp) (by simp) (by simp)]; exact h.rt y hy
  · unfold tpA; rw [e y hy 3560#u64 (by simp) (by simp) (by simp)]; exact h.pt y hy
  · rw [en c hc _ (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])]; exact h.root c hc
  · rw [en c hc _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])]; exact h.min c hc
  · unfold tdA at h0; unfold thA at hc'
    rw [e y hy 3528#u64 (by simp) (by simp) (by simp)] at h0
    rw [e y hy 3568#u64 (by simp) (by simp) (by simp)] at hc'
    exact h.core y hy h0 c hc'
  · unfold dnA; rw [e y hy 3576#u64 (by simp) (by simp) (by simp)]; exact h.dn y hy
  · unfold dpA; rw [e y hy 3584#u64 (by simp) (by simp) (by simp)]; exact h.dp y hy
  · rw [en c hc _ (by simp [layout.node.DEBUG_TCBS]) (by simp [layout.node.DEBUG_TCBS])]; exact h.dh c hc

/-- **m61's `FaultEnt` at an agreeing state** (the endpoint, its queue's links, the node, the
receiver's words and buffer slot: all `NU`). -/
theorem faultEnt_ag {K : KLayout} {U : Set U64} {X X' : S} {t ptr dest r : U64} {rest : List U64}
    (hK : RegionOK K) (hX : RegionOKX K) (hTH : ∀ y ∈ T, K.heap y = some .tcb)
    (hpH : K.heap ptr = some .ep) (hdH : K.heap dest = some .tcb)
    (hnd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → NU K (L.nodeAt X (L.cpu X) o))
    (G : Ag st (NU K) X X') (F : FaultEnt (L := L) T Cs Ω U X t ptr dest r rest) :
    FaultEnt (L := L) T Cs Ω U X' t ptr dest r rest := by
  have eh : L.mem X' (epHeadA ptr) = L.mem X (epHeadA ptr) :=
    G.m _ (nu_ep hX hpH (o := layout.ep.HEAD) (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD]))
  have ets : L.mem X' (epTSA ptr) = L.mem X (epTSA ptr) :=
    G.m _ (nu_ep hX hpH (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE]))
  have eQ : L.epQ X' ptr = L.epQ X ptr := by unfold LawfulStore.epQ; rw [eh, ets]
  have enb : ∀ c, L.nodeBase X' c = L.nodeBase X c := fun c => by simp [LawfulStore.nodeBase, G.k]
  have q := F.hq
  have hsl := nu_tslot hK hX hdH (i := layout.tcb.SLOT_BUFFER) (by simp [layout.tcb.SLOT_BUFFER])
  exact
  { F with
    hEN := ⟨fun c hc => by rw [enb]; exact F.hEN.1 c hc, by rw [G.k]; exact F.hEN.2⟩
    hq := by
      rw [eQ]
      exact ⟨q.nodup, q.mem, q.head, q.last, Seg.congr (fun x hx =>
        ⟨G.m _ (nu_tcb hX (hTH x (q.mem x hx)) (o := 3504#u64) (by simp) (by simp) (by simp)),
          G.m _ (nu_tcb hX (hTH x (q.mem x hx)) (o := 3496#u64) (by simp) (by simp) (by simp))⟩) q.seg⟩
    hst := by unfold LawfulStore.epState; rw [ets]; exact F.hst
    hcC := by rw [G.c]; exact F.hcC
    hN := by rw [G.c]; exact NodePlaced.of_ksb G.k F.hN
    hU := fun b hb => ⟨(F.hU b hb).1.ksb G.k, (F.hU b hb).2⟩
    hΩ := fun a ha => (F.hΩ a ha).ksb G.k
    hcur := by
      show L.mem X' (L.nodeAt X' (L.cpu X') _) = t
      rw [G.node, G.m _ (hnd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]))]
      exact F.hcur
    hact := by
      unfold LawfulStore.actionW
      rw [G.node, G.m _ (hnd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
      exact F.hact
    hbuf := by
      rw [lib_congr G (tcb_slot_val _ _) (nu_tcb hX hdH (o := 3512#u64) (by simp) (by simp) (by simp))
        hsl.1 hsl.2]
      exact F.hbuf
    hrep := by
      rw [G.m (replyA dest) (nu_tcb hX hdH (o := 3360#u64) (by simp) (by simp) (by simp))]; exact F.hrep
    hsc := by
      rw [G.m (scA dest) (nu_tcb hX hdH (o := 3464#u64) (by simp) (by simp) (by simp))]; exact F.hsc }

end

/-! ## `SlPreB` across a user-word write -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {Cs Ω Sg Ac : Set U64}

/-- **The fault handler's endpoint at a prefix state is a heap endpoint** (its cap slot is a TCB
slot, unchanged by the prefix, and typed at the entry). -/
theorem flt_ptr_ep (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (C : FaultChecks st X (L.curW s) ptr badge dest r) : K.heap ptr = some .ep := by
  have hX := B.regionOKX
  have hK := B.regionOK
  obtain ⟨hk, hcp⟩ := B.kc
  have hcH := E.hSt.1
  obtain ⟨hs, -, r8, -, a0, a8⟩ := hX.tslot _ hcH layout.tcb.SLOT_FAULT_HANDLER
    (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  have nd0 : ¬ SlDS (L := L) s (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) :=
    not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp (by rw [hK.slot _ hs]; intro c h; cases h)
      (by rw [hK.slot _ hs]; intro h; cases h)
  have nd8 : ¬ SlDS (L := L) s (core.num.U64.wrapping_add (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) 8#u64) :=
    not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp (by rw [r8]; intro c h; cases h) (by rw [r8]; intro h; cases h)
  obtain ⟨-, ⟨sl, x, y, g, gr, hS, hcap, -⟩, -⟩ := C
  have esl : sl = fhA (L := L) s := by rw [tcb_slot_val] at hS; exact (ok_inj_ff hS).symm
  subst esl
  have ecap : obj.Slot.cap st (fhA (L := L) s) X = obj.Slot.cap st (fhA (L := L) s) s :=
    cap_congr (lp_mem ar hA E.hT E.hN E.hcT LP a0 nd0) (lp_mem ar hA E.hT E.hN E.hcT LP a8 nd8)
  have hcap' : obj.Slot.cap st (fhA (L := L) s) s = ok (capability.Cap.Endpoint ptr badge x y g gr) := by
    rw [← ecap]; exact hcap
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B'⟩ := B
  have h := B'.hep ⟨ptr, badge, x, y, g, gr, hcap'⟩
  rwa [resPtr_ok hcap'] at h

/-- **The ReplyRecv-guarded fields of `SlPreB`** (`hPl`, `hy0r`, `hSu`, as there). -/
structure SlPreRR (K : KLayout) (Locks : S → U64 → Prop) (found : U64 × U64)
    (T Cs Ω Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s : S) : Prop where
  hPl : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
    RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X (L.curW s) found.1 found.2 u usc
  hy0r : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc → L.mem X (yieldA u) = 0#u64
  hSu : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
    RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc →
      K.heap u = some .tcb ∧ Safe0 (L.cpu s) (Locks s) (L.mem s) u ∧
        SlWS (st := st) K Locks s (stA (L.curW s)) ∧ SlWS (st := st) K Locks s (blockA (L.curW s)) ∧
        SlWS (st := st) K Locks s (stA u)

/-- **`SlPreB` across a user-word write** at a bundle state (module docstring), given P1's
`UserOK` for the layout's user words (`hUO` [J]), fl4-sync's contract `SlSyncC`, the locks
(`hl`, [P]) and the ReplyRecv-guarded fields at the written state (`R`). -/
theorem SlJAt.preB_wr (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hUO : UserOK st K.heap.tcbs Cs Ω K.heap K.user s) (hC : SlSyncC st n found s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s)
    (R : SlPreRR (st := st) ar K Locks found K.heap.tcbs Cs Ω Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits (L.wr s b v)) :
    SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v) := by
  have hX := B.regionOKX
  have hK := B.regionOK
  obtain ⟨hk, hcp⟩ := B.kc
  have ecur := B.curW_wr hb hba v
  have etr := B.trap_wr hb hba v
  have rws := B.slRWS_wr hb hba v Locks hl
  have hΩ : ∀ x ∈ K.user, x ∉ Ω := fun x hx => (hUO x hx).2.1
  have back : ∀ a X' a1, LocalPre (st := st) ar (L.wr s b v) a (X', a1) →
      ∃ X, LocalPre (st := st) ar s a (X, a1) ∧ Ag st (NU K) X X' ∧ L.ksb X = L.ksb s :=
    fun a X' a1 LP' => by
      obtain ⟨X, LP, G⟩ := B.lp_wr ar hA E.hT E.hN E.hcT E.hSt.1 hb hba v LP'
      obtain ⟨kX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
      exact ⟨X, LP, G, kX⟩
  have hal : ∀ X : S, L.ksb X = L.ksb s → ∀ hi : U64, hi.val < 2048 → Aligned (atAF (L.ksb X) hi) :=
    fun X kX hi hhi => by rw [kX, hk]; exact (hX.asidT hi hhi).2
  refine
  { hT := E.hT
    hN := by rw [L.cpu_wr]; exact NodePlaced.of_ksb (L.ksb_wr _ _ _) E.hN
    hcT := by rw [ecur]; exact E.hcT
    hI := fun a X' a1 LP' => by
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      exact bxi_user (E.hI a X a1 LP) (hUO.ksb kX) G.writesIn
    hAs := fun a X' a1 LP' => by
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      exact asidOff_ag hΩ (hal X kX) G (E.hAs a X a1 LP)
    aff := fun d hd => by
      rw [E.aff d hd]
      exact (wr_nu (x := fld d oAFFINITY) hba hb v
        (nu_tcb hX hd (by rw [oAFF_val]; omega) (by rw [oAFF_val]; omega) (by rw [oAFF_val]))).symm
    hSt := by
      rw [ecur, L.cpu_wr, hl]
      exact ⟨E.hSt.1, safe0_wr hX hb hba v E.hSt.1 E.hSt.2⟩
    hrecv := fun hS' a X' a1 LP' ptr badge dest r C => by
      have hS := etr.1 hS'
      rw [ecur] at C
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have C0 := flt_chk_back (fltDec_nu ar hA B E LP) G C
      have hd := (E.hSd hS a X a1 LP C0).1
      rw [G.m (stA dest) (nu_tcb hX hd (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega)
        (by rw [st_val]))]
      exact E.hrecv hS a X a1 LP C0
    hF := fun hS' a X' a1 LP' => by
      have hS := etr.1 hS'
      rw [ecur]
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      refine ⟨asidOff_ag hΩ (hal X kX) G (E.hF hS a X a1 LP).1, fun ptr badge dest r C => ?_⟩
      have C0 := flt_chk_back (fltDec_nu ar hA B E LP) G C
      obtain ⟨hr, rest, F⟩ := (E.hF hS a X a1 LP).2 ptr badge dest r C0
      exact ⟨hr, rest, faultEnt_ag hK hX (fun y hy => hy) (flt_ptr_ep ar hA B E LP C0)
        (E.hSd hS a X a1 LP C0).1 (slCom_nu ar hA B E LP).nd G F⟩
    hy0f := fun hS' a X' a1 LP' ptr badge dest r C => by
      have hS := etr.1 hS'
      rw [ecur] at C
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have C0 := flt_chk_back (fltDec_nu ar hA B E LP) G C
      have hd := (E.hSd hS a X a1 LP C0).1
      rw [G.m (yieldA dest) (nu_tcb hX hd (o := 3472#u64) (by simp) (by simp) (by simp))]
      exact E.hy0f hS a X a1 LP C0
    hTm := fun hS' a X' a1 LP' => by
      have hS := etr.1 hS'
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      exact timerOK_ag hUO kX hX (fun y hy => hy) G (E.hTm hS a X a1 LP)
    hSd := fun hS' a X' a1 LP' ptr badge dest r C => by
      have hS := etr.1 hS'
      rw [ecur] at C ⊢
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have C0 := flt_chk_back (fltDec_nu ar hA B E LP) G C
      obtain ⟨h1, h2, h3, h4⟩ := E.hSd hS a X a1 LP C0
      rw [L.cpu_wr, hl, rws.2]
      exact ⟨h1, safe0_wr hX hb hba v h1 h2, h3, h4⟩
    hPl := R.hPl
    hrz := fun hS' a X' a1 LP' => by
      have hS : ¬ SlTrap st s := fun h => hS' (etr.2 h)
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have hrp : K.heap found.1 = some .reply := (B.rrG hC.fd hS (hC.arm hS)).1
      rw [G.m (rNextA found.1) (nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT])
          (by simp [layout.reply.NEXT])),
        G.m (rPrevA found.1) (nu_rp hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV])
          (by simp [layout.reply.PREV]))]
      exact E.hrz hS a X a1 LP
    hy0r := R.hy0r
    hSu := R.hSu
    hlk := fun hS' => by rw [hl]; exact E.hlk (fun h => hS' (etr.2 h)) }

end

end Fl4Proofs.P2.PathObl

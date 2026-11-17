/-
P3 (DESIGN.md §9), IPC: **P1's transfer placement (`XferKG`) at P3's
relations**, and DomFoot's IPC footprints discharged from it.

* `get_receive_slot_slot`: on a CSpace related to some spec state, the
  receive slot is none or an empty CNode slot of the typed heap;
  `lookup_extra_cslot`: the extra-cap lookups return CNode slots (or none).
* `RSW`: the words P1's non-insert steps write around a transfer (`KW`'s,
  the receivers' registers, the user words); `RSP`: the CSpace relation, the
  base placed, P1's TCBs in the typed heap, `RSW`'s words outside the slots;
  `RSP.of_writes`: kept by writes in `RSW`.
* `insert_rsp`: the transfer's insert of a derived cap keeps `RSP` and writes
  only slot words, which are `KG` (`kg_of_slotWd`).
* `RSI` / `RDI`: P1's `RS` and `RD` (`RSP` at the start and now; the receive
  slot an empty CNode slot); `xferKG_rsi`: P1's `XferKG` at them; `rsi_kw`,
  `rsi_refl`: the reply path's `hRSK`, `hRS0`.
* `sendIpcFootP1_rsp`, `replyFootP1_rsp`: DomFoot's `SendIpcFootP1` and
  `ReplyFootP1` at `RS := RSP`, from P1's `send_ipc.footB` and
  `do_reply_transfer.foot` (the latter with their timeout-handler and
  user-word premises); `decWritesHyp_endpoint_rsp`, `decWritesHyp_reply_rsp`:
  DomFoot's endpoint and reply write footprints with them.
-/
import Fl4Proofs.P3.IpcGrant
import Fl4Proofs.P3.UtDom
import Fl4Proofs.P1.QueueIpcFoot
import Fl4Proofs.P3.DomFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- A CNode slot of the typed heap. -/
def CSlot (th : TypedHeap) (x : U64) : Prop :=
  ∃ ps rs idxs, th ps = some (.cnode rs) ∧ idxs.length = rs ∧ x = cslotAddr (ps.bv, idxs)

theorem CSlot.isSlot {th : TypedHeap} {x : U64} (h : CSlot th x) : IsSlot th x := by
  obtain ⟨ps, rs, idxs, hps, hls, rfl⟩ := h
  exact AbsSlot.isSlot (th := th) (sl := (ps.bv, idxs)) ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩

/-- **The receive slot is a slot of the typed heap** (or none): FL4's
`get_receive_slot` on a CSpace related to some spec state. -/
theorem get_receive_slot_slot {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} (hR : StateRel th (L.mem s) σ)
    (hV : SlotsValid th (L.mem s)) {t : U64} (ht : th t = some .tcb) (rbw : U64) :
    ipc.get_receive_slot st s t rbw ⦃ d => d = 0#u64 ∨ (CSlot th d ∧ capAt (L.mem s) d = ok .Null) ⦄ := by
  unfold ipc.get_receive_slot
  by_cases hr0 : rbw = 0#u64
  · simp only [hr0, ↓reduceIte]; exact (WP.spec_ok _).2 (Or.inl rfl)
  simp only [hr0, ↓reduceIte]
  rw [buf_recv_eq.1, buf_recv_eq.2.1, buf_recv_eq.2.2]
  simp only [bind_ok]
  refine WP.spec_bind (msg.buf_get.spec s rbw _) fun root _ => ?_
  refine WP.spec_bind (msg.buf_get.spec s rbw _) fun index _ => ?_
  refine WP.spec_bind (msg.buf_get.spec s rbw _) fun depth _ => ?_
  refine WP.spec_bind (lookup_cap_valid th s σ hR hV t ht root) ?_
  rintro r ⟨⟨e, -, hrel⟩, hval⟩
  cases r with
  | Err lf => exact (WP.spec_ok _).2 (Or.inl rfl)
  | Ok c0 =>
    cases e with
    | error _ => simp [CapResRel] at hrel
    | ok a =>
      simp only []
      unfold cspace.lookup_target_slot
      refine WP.spec_bind (lookup_slot_for_cnode_op_refines th s σ hR hV false c0 a hrel (hval c0 rfl) index depth) ?_
      rintro r1 ⟨e1, -, hrel1⟩
      cases r1 with
      | Err _ => exact (WP.spec_ok _).2 (Or.inl rfl)
      | Ok slot =>
        cases e1 with
        | error _ => exact hrel1.elim
        | ok sl =>
          obtain ⟨hsl, p, hp1, hp⟩ := hrel1
          have hCS : CSlot th slot := by
            obtain ⟨o, idx⟩ := sl
            simp only at hp1 hp
            subst hp1
            exact ⟨p, idx.length, idx, hp, rfl, hsl⟩
          simp only []
          rw [slot_cap_eq]
          obtain ⟨c1, hc1⟩ := capAt_total (L.mem s) slot
          rw [hc1]
          simp only [bind_ok]
          by_cases hn : c1 = .Null
          · subst hn
            rw [cap_is_null_null]
            simp only [bind_ok, ↓reduceIte, WP.spec_ok]
            exact Or.inr ⟨hCS, hc1⟩
          · rw [cap_is_null_ne hn]
            simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
            exact (WP.spec_ok _).2 (Or.inl rfl)

/-- **The words P1's steps other than inserts write** around a transfer:
`KW`'s (TCB words from offset 192, node, `Sg`, SC and endpoint words), the
receivers' registers and the user words `U`. -/
def RSW (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : P1.Heap) (U : Set U64) (s : S) (b : U64) : Prop :=
  (∃ y ∈ T, ∃ K : U64, 192 ≤ K.val ∧ K.val < 4096 ∧ b = core.num.U64.wrapping_add y K) ∨
  (∃ c ∈ Cs, ∃ o : U64, o.val < 4288 ∧ b = L.nodeAt s c o) ∨ b ∈ Sg ∨ (∃ c ∈ Scs, InSC c (Z c) b) ∨
  (∃ e ∈ EH H, b = epHeadA e ∨ b = epTSA e) ∨ b ∈ U

/-- **P3's side of P1's `RS`** (the transfer's slot facts): the CSpace
relation to some spec state, the kernel-global base placed, P1's TCBs TCBs of
the typed heap, `RSW`'s words outside the slots, the extra-cap slots CNode
slots. -/
structure RSP (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : P1.Heap) (U : Set U64) (th : TypedHeap) (σ : Fl4Spec.State Unit) (G : MdbGhost) (s : S) :
    Prop where
  pl : Placed th
  cr : CRel th (L.mem s) σ G
  ks : KsbOK (L := L) th s
  tcb : ∀ y ∈ T, th y = some .tcb
  apart : ∀ b, RSW (L := L) T Cs Sg Scs Z H U s b → ∀ x, IsSlot th x → ¬ (x.val ≤ b.val ∧ b.val < x.val + 32)

variable {T Cs Sg Scs : Set U64} {Z : U64 → Nat} {H : P1.Heap} {U : Set U64}

/-- Writes in `RSW` keep every slot. -/
theorem RSP.slotsSame {th : TypedHeap} {σ : Fl4Spec.State Unit} {G : MdbGhost} {s s' : S} {W : U64 → Prop}
    (h : RSP (L := L) T Cs Sg Scs Z H U th σ G s) (hW : WritesIn st s s' W)
    (hWR : ∀ b, W b → RSW (L := L) T Cs Sg Scs Z H U s b) : SlotsSame th (L.mem s) (L.mem s') := by
  intro a ha
  have hal := ha.align h.pl
  have hfit := ha.fit h.pl
  have one : ∀ k : U64, k.val < 32 → k.val % 8 = 0 →
      L.mem s' (wordOf a k) = L.mem s (wordOf a k) := by
    intro k hk hk8
    have hv : (wordOf a k).val = a.val + k.val := wordOf_val (by omega)
    refine hW.2.2 _ (by unfold P1.Aligned; rw [hv]; omega) fun hw => ?_
    exact h.apart _ (hWR _ hw) a ha ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  have h0 : wordOf a 0#u64 = a := by
    apply UScalar.eq_of_val_eq; rw [wordOf_val (by simp; omega)]; simp
  refine ⟨?_, one 8#u64 (by decide) (by decide), one 16#u64 (by decide) (by decide),
    one 24#u64 (by decide) (by decide)⟩
  have := one 0#u64 (by decide) (by decide)
  rwa [h0] at this

theorem RSW.ksb {s s' : S} (hk : L.ksb s' = L.ksb s) {b : U64} (h : RSW (L := L) T Cs Sg Scs Z H U s' b) :
    RSW (L := L) T Cs Sg Scs Z H U s b := by
  rcases h with h | ⟨c, hc, o, ho, e⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨c, hc, o, ho, e.trans (P1.nodeAt_of_ksb hk c o)⟩)
  · exact Or.inr (Or.inr h)

/-- **`RSP` across writes in `RSW`.** -/
theorem RSP.of_writes {th : TypedHeap} {σ : Fl4Spec.State Unit} {G : MdbGhost} {s s' : S} {W : U64 → Prop}
    (h : RSP (L := L) T Cs Sg Scs Z H U th σ G s) (hW : WritesIn st s s' W)
    (hWR : ∀ b, W b → RSW (L := L) T Cs Sg Scs Z H U s b) : RSP (L := L) T Cs Sg Scs Z H U th σ G s' := by
  have hS := h.slotsSame hW hWR
  have hcap : ∀ x, IsSlot th x → capAt (L.mem s') x = capAt (L.mem s) x := fun x hx => hS.capAt hx
  obtain ⟨hR, hV, hM, hC, hI⟩ := h.cr
  exact ⟨h.pl, ⟨hR.of_caps hcap, hV.of_caps hcap, hM.of_same hS, hC.of_same hS rfl rfl, hI.of_same hM hS⟩,
    h.ks.same hW.1, h.tcb, fun b hb => h.apart b (RSW.ksb hW.1 hb)⟩

/-- **The extra-cap lookups return CNode slots of the typed heap** (or
none). -/
theorem lookup_extra_cslot {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} (hR : StateRel th (L.mem s) σ)
    (hV : SlotsValid th (L.mem s)) {t : U64} (ht : th t = some .tcb) (sbw : U64) (info : msginfo.MessageInfo) :
    ipc.lookup_extra_caps st s t sbw info ⦃ r => ∀ ex, r = .Ok ex → ∀ x ∈ ex.val, x = 0#u64 ∨ CSlot th x ⦄ := by
  have fin : ∀ ex : Aeneas.Std.Array obj.Slot 3#usize, (∀ j, j < 3 → exAt ex j = 0#u64 ∨ CSlot th (exAt ex j)) →
      ∀ x ∈ ex.val, x = 0#u64 ∨ CSlot th x := by
    intro ex hj x hx
    obtain ⟨j, hj3, rfl⟩ := List.getElem_of_mem hx
    have hl : ex.val.length = 3 := by simp
    have := hj j (by omega)
    unfold exAt at this
    rwa [List.getD_eq_getElem _ _ hj3] at this
  unfold ipc.lookup_extra_caps
  by_cases h0 : sbw = 0#u64
  · simp only [h0, ↓reduceIte]
    refine (WP.spec_ok _).2 fun ex hex => ?_
    cases hex
    exact fin _ fun j hj => Or.inl (exAt_none j hj)
  simp only [h0, ↓reduceIte]
  unfold ipc.lookup_extra_caps_loop
  refine WP.spec_mono (loop.spec_decr_nat (fun x => 3 - x.2.val)
    (fun x => ∀ j, j < 3 → exAt x.1 j = 0#u64 ∨ CSlot th (exAt x.1 j))
    (fun r => ∀ ex, r = .Ok ex → ∀ j, j < 3 → exAt ex j = 0#u64 ∨ CSlot th (exAt ex j)) _ _ (fun x hx => ?_)
    (fun j hj => Or.inl (exAt_none j hj))) fun r hr ex hex => fin ex (hr ex hex)
  obtain ⟨arr, i⟩ := x
  dsimp only at hx ⊢
  unfold ipc.lookup_extra_caps_loop.body
  by_cases hin : i < info.extra_caps
  · by_cases hi3 : i < 3#u64
    · have hi3' : i.val < 3 := by scalar_tac
      simp only [hin, hi3, ↓reduceIte, buf_caps_eq, lift, bind_ok]
      refine WP.spec_bind (msg.buf_get.spec s sbw _) ?_
      rintro w -
      refine WP.spec_bind (lookup_slot_refines th s σ hR hV t ht _) ?_
      rintro r ⟨e, -, hrel, hsok⟩
      cases r with
      | Ok r1 =>
        cases e with
        | error _ => exact hrel.elim
        | ok v =>
          obtain ⟨sl, rest⟩ := v
          obtain ⟨hsl, -⟩ := hrel
          obtain ⟨p, hp1, hp⟩ := hsok
          simp only []
          obtain ⟨a', ha', ha'v⟩ := spec_exists (Aeneas.Std.Array.update_spec arr (UScalar.cast .Usize i) r1.slot
            (by have hl : arr.val.length = 3 := by simp
                rw [cast_us_val i hi3']; simp [Aeneas.Std.Array.length, hl]; omega))
          rw [ha']
          simp only [bind_ok]
          obtain ⟨i4, h4e, h4v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
          rw [h4e, bind_ok, WP.spec_ok]
          have hi4 : i4.val = i.val + 1 := by simpa using h4v
          subst ha'v
          refine ⟨fun j hj => ?_, by rw [hi4]; omega⟩
          rw [exAt_set, cast_us_val i hi3']
          split
          · right
            obtain ⟨o, idx⟩ := sl
            simp only at hp1 hp
            subst hp1
            exact ⟨p, idx.length, idx, hp, rfl, hsl⟩
          · exact hx j hj
      | Err lf =>
        simp only [WP.spec_ok]
        intro ex hex; cases hex
    · simp only [hin, hi3, ↓reduceIte, WP.spec_ok]
      intro ex hex; cases hex; exact hx
  · simp only [hin, ↓reduceIte, WP.spec_ok]
    intro ex hex; cases hex; exact hx

/-- `KG` of a slot of the typed heap, from the base's placement. -/
theorem kg_of_slot {th : TypedHeap} {s : S} (hP : Placed th) (hK : KsbOK (L := L) th s) {x : U64}
    (hx : IsSlot th x) : KG (L.ksb s) x := by
  obtain ⟨q, k, hq, h1, h2⟩ := IsSlot.obj hP hx
  unfold KG
  rcases hK.apart q k hq with h | h <;> omega

/-- `KG` of a slot word of the typed heap. -/
theorem kg_of_slotWd {th : TypedHeap} {s : S} (hP : Placed th) (hK : KsbOK (L := L) th s) {b : U64}
    (hal : P1.Aligned b) (hb : Sched.SlotWd th b) : KG (L.ksb s) b := by
  obtain ⟨y, hy, h1, h2⟩ := slotWd_range hP hb
  obtain ⟨q, k, hq, h3, h4⟩ := IsSlot.obj hP hy
  have := hK.align
  unfold P1.Aligned at hal
  unfold KG
  rcases hK.apart q k hq with h | h <;> omega

/-- **The transfer's insert keeps `RSP`** and writes only slot words (`KG`):
a cap derived from a CNode slot's into an empty CNode slot (`insert_full`). -/
theorem insert_rsp {th : TypedHeap} {σ : Fl4Spec.State Unit} {G : MdbGhost} {s : S}
    (h : RSP (L := L) T Cs Sg Scs Z H U th σ G s) {src dest : U64} (hs : CSlot th src) (hd : CSlot th dest)
    (hdN : capAt (L.mem s) dest = ok .Null) {cap c : capability.Cap} (hcap : obj.Slot.cap st src s = ok cap)
    (hder : objects.derive_cap st s src cap = ok (.Ok c)) (hn : c ≠ .Null) :
    cdt.insert st s c src dest ⦃ s' => WritesIn st s s' (KG (L.ksb s)) ∧
      ∃ σ' G', RSP (L := L) T Cs Sg Scs Z H U th σ' G' s' ⦄ := by
  obtain ⟨ps, rs, idxs, hps, hls, rfl⟩ := hs
  obtain ⟨pd, rd, idxd, hpd, hld, rfl⟩ := hd
  obtain ⟨hR, hV, hM, hC, hI⟩ := h.cr
  have hPl := h.pl
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  rw [slot_cap_eq] at hcap
  obtain ⟨c0, a0, hc0, hca0, -⟩ := hR.slot_cap (Z := Unit) (sl := (ps.bv, idxs)) rfl (by simpa [hls] using hps)
  rw [hcap] at hc0
  obtain rfl : cap = c0 := by simpa using hc0
  have he0 : EncWf cap := by have := hcap; rw [capAt_words] at this; exact decode_encWf this
  have hcvv : CapValid th cap := hV.abs hAs hcap
  have hcvn : cap ≠ .Null := by
    rintro rfl; unfold objects.derive_cap at hder; simp at hder; exact hn hder.symm
  have hncs : NoChildrenRel (st := st) s σ (cslotAddr (ps.bv, idxs)) (ps.bv, idxs) :=
    noChildren_of_adj th hPl s σ G hM hC (hI.parentAdj (th := th)) _ hAs
      ((hM.members _).2 ⟨hAs.isSlot, cap, hcap, hcvn⟩)
  obtain ⟨r, hr, r', -, hdr⟩ := derive_rel (Z := Unit) s σ (cslotAddr (ps.bv, idxs)) (ps.bv, idxs) cap hca0.1 he0
    (fun _ => hncs)
  rw [hder] at hr
  obtain rfl : r = .Ok c := (ok_inj hr).symm
  cases r' with
  | error _ => exact hdr.elim
  | ok a' =>
    obtain ⟨hw', ha', he', hv', -⟩ := hdr
    obtain ⟨hsh, hbd, hzb, hnu⟩ := derive_shape hder hn hncs
    have hut : isUt cap = true → ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs)) := by
      intro hu0 y hy
      obtain ⟨z, hz⟩ := desc_tail_child hy
      exact hnu hu0 ((hC.has_child_iff hPl hAs).2 ⟨z, hz⟩)
    have hnx : nextOf (L.mem s) (cslotAddr (ps.bv, idxs)) = 0#u64 ∨
        IsSlot th (nextOf (L.mem s) (cslotAddr (ps.bv, idxs))) := by
      have hm := (hM.members _).2 ⟨hAs.isSlot, cap, hcap, hcvn⟩
      rcases hM.next_mem hm with h' | ⟨h', -⟩
      · exact Or.inl h'
      · exact Or.inr ((hM.members _).1 h').1
    refine WP.spec_mono (WP.spec_and (insert_full th s σ G hR hV hPl hM hC hI hps hpd hls hld hcap hcvn hdN c a'
      ⟨hw', ha'⟩ (hv' th hcvv) he' hn hsh (Or.inl hbd) hut hzb)
      (Sched.insert_ws hPl s c _ _ hAs.isSlot hAd.isSlot cap hcap hnx)) ?_
    rintro s' ⟨⟨σ', G', -, hR', hV', hM', hC', hI'⟩, hw⟩
    refine ⟨⟨hw.1, hw.2.1, fun b hal hnk => hw.2.2 b hal fun hb => hnk (kg_of_slotWd hPl h.ks hal hb)⟩, σ', G', hPl, ⟨hR', hV', hM', hC', hI'⟩,
      h.ks.same hw.1, h.tcb, fun b hb => h.apart b (RSW.ksb hw.1 hb)⟩

/-- **P3's `RS`**: `RSP` at the transfer's start and now, for one typed heap. -/
def RSI (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : P1.Heap) (U : Set U64) (th : TypedHeap) (s0 s : S) : Prop :=
  ∃ σ0 G0 σ G, RSP (L := L) T Cs Sg Scs Z H U th σ0 G0 s0 ∧ RSP (L := L) T Cs Sg Scs Z H U th σ G s

/-- **P3's `RD`**: the receive slot an empty CNode slot of the typed heap. -/
def RDI (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : P1.Heap) (U : Set U64) (th : TypedHeap) (s : S) (d : U64) :
    Prop :=
  (∃ σ G, RSP (L := L) T Cs Sg Scs Z H U th σ G s) ∧ CSlot th d ∧ capAt (L.mem s) d = ok .Null

theorem rsw_of_reg {s : S} {b : U64} (h : XferRegW T U b ∨ ∃ c ∈ Scs, InSC c (Z c) b) :
    RSW (L := L) T Cs Sg Scs Z H U s b := by
  rcases h with (⟨y, hy, K, h1, h2, -, e⟩ | h) | h
  · exact Or.inl ⟨y, hy, K, by omega, by omega, e⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem rsw_of_kw {s : S} {b : U64} (h : KW st T Cs Sg Scs Z (EH H) s b) : RSW (L := L) T Cs Sg Scs Z H U s b := by
  rcases h with ⟨y, hy, K, h1, h2, -, -, e⟩ | ⟨c, hc, o, ho, -, e⟩ | h | h | h
  · exact Or.inl ⟨y, hy, K, h1, h2, e⟩
  · exact Or.inr (Or.inl ⟨c, hc, o, ho, e⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem rsw_of_dbg {s : S} {b : U64} (h : DbgW st T Cs s b) : RSW (L := L) T Cs Sg Scs Z H U s b := by
  rcases h with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
  · exact Or.inl ⟨y, hy, 3576#u64, by simp, by simp, e⟩
  · exact Or.inl ⟨y, hy, 3584#u64, by simp, by simp, e⟩
  · exact Or.inr (Or.inl ⟨c, hc, layout.node.DEBUG_TCBS, by simp [layout.node.DEBUG_TCBS], e⟩)

/-- **P1's `XferKG` at P3's `RS` and `RD`.** -/
theorem xferKG_rsi {Ω Rp Nt : Set U64} (th : TypedHeap) :
    XferKG st T Cs Ω H Sg Rp Scs Nt Z U (RSI (L := L) T Cs Sg Scs Z H U th) (RDI (L := L) T Cs Sg Scs Z H U th) := by
  refine ⟨fun Ac X Q R s0 s y b _ hrs hy => ?_, fun Ac X Q R s0 s src dest cap c _ hrs hrd hef hcap hder hn _ _ _ => ?_,
    fun s0 s s' hrs hw => ?_, fun s s' d hrd hw => ?_⟩
  · obtain ⟨σ0, G0, σ, G, -, h⟩ := hrs
    exact WP.spec_mono (get_receive_slot_slot h.cr.1 h.cr.2.1 (h.tcb y hy) b) fun d hd =>
      hd.imp id fun ⟨hc, hnl⟩ => ⟨kg_of_slot h.pl h.ks hc.isSlot, ⟨σ, G, h⟩, hc, hnl⟩
  · obtain ⟨σ0, G0, σ, G, h0, h⟩ := hrs
    obtain ⟨-, hdC, hdN⟩ := hrd
    obtain ⟨y, hy, b, tag, ex, hlk, hmem, hne⟩ := hef
    have hl := lookup_extra_cslot h0.cr.1 h0.cr.2.1 (h0.tcb y hy) b tag
    rw [hlk, WP.spec_ok] at hl
    rcases hl ex rfl src hmem with h0' | hsC
    · exact absurd h0' hne
    exact WP.spec_mono (insert_rsp h hsC hdC hdN hcap hder hn) fun s' ⟨hw, σ', G', h'⟩ =>
      ⟨hw, σ0, G0, σ', G', h0, h'⟩
  · obtain ⟨σ0, G0, σ, G, h0, h⟩ := hrs
    exact ⟨σ0, G0, σ, G, h0, h.of_writes hw fun b hb => rsw_of_reg hb⟩
  · obtain ⟨⟨σ, G, h⟩, hdC, hdN⟩ := hrd
    have hS := h.slotsSame hw fun b hb => rsw_of_reg hb
    exact ⟨⟨σ, G, h.of_writes hw fun b hb => rsw_of_reg hb⟩, hdC, by rw [hS.capAt hdC.isSlot]; exact hdN⟩

/-- `RSI` across `KW` writes (`hRSK`). -/
theorem rsi_kw (th : TypedHeap) :
    ∀ s0 s1 s2 : S, RSI (L := L) T Cs Sg Scs Z H U th s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) →
      RSI (L := L) T Cs Sg Scs Z H U th s2 s2 := by
  rintro s0 s1 s2 ⟨-, -, σ, G, -, h⟩ hw
  have h' := h.of_writes hw fun b hb => rsw_of_kw hb
  exact ⟨σ, G, σ, G, h', h'⟩

/-- `RSI` across `KW` and debug-list writes (`hRSK` of the reply path). -/
theorem rsi_kwd (th : TypedHeap) :
    ∀ s0 s1 s2 : S, RSI (L := L) T Cs Sg Scs Z H U th s0 s1 →
      WritesIn st s1 s2 (fun b => KW st T Cs Sg Scs Z (EH H) s1 b ∨ DbgW st T Cs s1 b) →
      RSI (L := L) T Cs Sg Scs Z H U th s2 s2 := by
  rintro s0 s1 s2 ⟨-, -, σ, G, -, h⟩ hw
  have h' := h.of_writes hw fun b hb => hb.elim rsw_of_kw rsw_of_dbg
  exact ⟨σ, G, σ, G, h', h'⟩

theorem rsi_refl {th : TypedHeap} {σ : Fl4Spec.State Unit} {G : MdbGhost} {s : S}
    (h : RSP (L := L) T Cs Sg Scs Z H U th σ G s) : RSI (L := L) T Cs Sg Scs Z H U th s s :=
  ⟨σ, G, σ, G, h, h⟩

end

/-! ## DomFoot's IPC footprints, discharged -/

section
variable {S A : Type} {st : machine.Store S} [L : LawfulStore st] (arI : machine.Arch A)
variable {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {H : P1.Heap} {Ac U : Set U64}

/-- **`SendIpcFootP1` at `RSP`**, from P1's `send_ipc.footB` with the
transfer's footprint discharged (`xferFootOK_of`, `xferKG_rsi`). -/
theorem sendIpcFootP1_rsp {P3Ok : S → Prop} (hA : P0.ArchTotal arI) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (th : TypedHeap) (ct p : U64) (blk call : Bool) (b : U64) (g gr don : Bool) :
    SendIpcFootP1 (L := L) arI T Cs Ω H Sg Rp Scs Nt Z Ac U P3Ok
      (fun s => ∃ σ G, RSP (L := L) T Cs Sg Scs Z H U th σ G s) ct p blk call b g gr don := by
  intro hxf hH s1 a hB hcb hdon hU ⟨σ, G, hr⟩ hG
  exact endpoint.send_ipc.footB hA hxf (xferFootOK_of hA E (xferKG_rsi (Ω := Ω) (Rp := Rp) (Nt := Nt) th)) s1 a
    blk call b g gr don ct p hB hU hcb hdon hH (rsi_kw th) (rsi_refl hr) hG

/-- **`ReplyFootP1` at `RSP`**, from P1's `do_reply_transfer.foot`, given
its timeout-handler and user-word premises. -/
theorem replyFootP1_rsp {P3Ok : S → Prop} (hA : P0.ArchTotal arI) (th : TypedHeap)
    (tmoAny : ∀ (Ac : Set U64) (s : S) (t : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
      obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (userOK : ∀ (Ac : Set U64) (s : S), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → UserOK st T Cs Ω H U s)
    (ct r : U64) (g : Bool) :
    ReplyFootP1 (L := L) arI T Cs Ω H Sg Rp Scs Nt Z Ac U P3Ok
      (fun s => ∃ σ G, RSP (L := L) T Cs Sg Scs Z H U th σ G s) ct r g := by
  intro E hr hct s1 a hB _ ⟨σ, G, hrs⟩ hG
  exact ipc.do_reply_transfer.foot hA E (xferFootOK_of hA E (xferKG_rsi (Ω := Ω) (Rp := Rp) (Nt := Nt) th)) tmoAny
    userOK s1 a ct r g hB hr hct (rsi_kwd th) (rsi_refl hrs) hG

/-- **The endpoint cap's write footprint at `RSP`** (`decWritesHyp_endpoint`
with `SendIpcFootP1` discharged): no IPC hypothesis left but P1's
`XferHyps`. -/
theorem decWritesHyp_endpoint_rsp {P3Ok : S → Prop} (hA : P0.ArchTotal arI)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {th : TypedHeap} {σ : Fl4Spec.State Unit} {G : MdbGhost} (s : S) (hR : RSP (L := L) T Cs Sg Scs Z H U th σ G s)
    (ar : A) (lbl length slot : U64) (p b : U64) (sd rv g gr : Bool)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hB : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcb : CanBlock st T Ac s ct) (hdon : don = true → L.mem s (scA ct) ≠ 0#u64)
    (hUO : UserOK st T Cs Ω H U s) (hH : H p = some .ep) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hD : KWDom (L := L) T Cs Sg Scs Z (EH H) s)
    (hTk : ∀ y ∈ T, y.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ y.val)
    (hka : (L.ksb s).val % 8 = 0) (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64)
    (hcbs : ∀ s1, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 → Foot st T Cs Sg Scs Z (EH H) s s1 →
      L.mem s1 (P1.stA ct) = sched.TS_RESTART → CanBlock st T Ac s1 ct ∧
        (don = true → L.mem s1 (scA ct) ≠ 0#u64)) :
    DecWritesHyp (L := L) arI s ar lbl length slot (.Endpoint p b sd rv g gr) blk call don fp buf extra :=
  decWritesHyp_endpoint arI s ar lbl length slot p b sd rv g gr blk call don fp buf extra hB ct hct hcb hdon hUO
    (xferOK_of hA E) hH (fun s1 f => ⟨σ, G, hR.of_writes f fun _ hb => rsw_of_kw hb⟩) (fun _ f => hG.foot f)
    (sendIpcFootP1_rsp arI hA E th ct p blk call b g gr don) hD hTk hka hkf hcbs

/-- **The reply cap's write footprint at `RSP`** (`decWritesHyp_reply` with
`ReplyFootP1` discharged), given `do_reply_transfer.foot`'s timeout-handler
and user-word premises. -/
theorem decWritesHyp_reply_rsp {P3Ok : S → Prop} (hA : P0.ArchTotal arI) {th : TypedHeap} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (tmoAny : ∀ (Ac : Set U64) (s : S) (t : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
      obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl => obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (userOK : ∀ (Ac : Set U64) (s : S), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → UserOK st T Cs Ω H U s)
    (s : S) (hR : RSP (L := L) T Cs Sg Scs Z H U th σ G s) (ar : A) (lbl length slot : U64) (r : U64) (g : Bool)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hB : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hctT : ct ∈ T) (hnb : ¬ Blocked (L.mem s (P1.stA ct)))
    (hnr : L.mem s (P1.stA ct) ≠ sched.TS_BLOCKED_ON_REPLY)
    (hUO : UserOK st T Cs Ω H U s) (hE : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hr : r ∈ Rp)
    (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (hD : KWDom (L := L) T Cs Sg Scs Z (EH H) s)
    (hTk : ∀ y ∈ T, y.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ y.val)
    (hka : (L.ksb s).val % 8 = 0) (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) :
    DecWritesHyp (L := L) arI s ar lbl length slot (.Reply r g) blk call don fp buf extra :=
  decWritesHyp_reply arI s ar lbl length slot r g blk call don fp buf extra hB ct hct hctT hnb hnr hUO hE hr
    (fun s1 f => ⟨σ, G, hR.of_writes f fun _ hb => rsw_of_kw hb⟩) (fun _ f => hG.foot f)
    (replyFootP1_rsp arI hA th tmoAny userOK ct r g) hD hTk hka hkf

end

end

end Fl4Proofs.P3.Ipc

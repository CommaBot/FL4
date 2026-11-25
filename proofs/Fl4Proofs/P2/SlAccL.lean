/-
# P2 (line p2sl): the accepted arms' read / write facts from the ownership map

`fltAcc_of` / `rrAcc_of`: `SlPreB`'s `hRWfG` / `hRWrG` (`FltAcc` / `RrAcc` for the sets `SlRS s` /
`SlWS s` at the prefix state), word by word through `OwnMap.own`, like `slDecIn_of`
(P2/SlDecL.lean):

* node words of this core (`rs_node`), the kernel globals and `KERNEL_ROOT` (`rs_ks`), the ASID
  table (`RegionOKX.asidT`) and the pools it names (`SlAccIn.pool`): gate-owned;
* the TCB words of the current thread, the receiver / replied thread: gate fields (`rs_tcb_gate`),
  or, the thread fit for its `STATE` writes (`Safe0`: homed here, queued only on a held lock;
  `SlPreB.hSt` / `hSd` / `hSu`), its home core's or, for the queue links, its queue lock's
  (`rw_tcb_safe`); their slots (`rs_tslot`); registers (`regs_safe`);
* the next queued thread's `EP_PREV` (trap arm, `SlAccIn.nq`): the handler endpoint's lock
  (`rw_tcb_q`);
* endpoint / reply object words: their lock (`slRW_of_lock`, fl4-sync's locks);
* SC words of SCs homed here (`scAcc_here`; `SlHere.cs` / `usc` / `rh`, `SlAccIn.dsc`);
* IPC buffer words: user words (`SlAccIn.fbuf` / `rbuf`; `SlWS` admits aligned user words).

Each fact is proved once with writes in `SlWN` (`SlWS` and not an owner-dependency word, `NonDec`:
`nonDec_tcb`, `nonDec_sc`, `nonDec_user`, `nonDec_of_region` by `decW_region`), giving both
`SlPre`'s pair for the read / write sets (`fltAcc_of`, `rrAcc_of`) and its `NonDec` pair for `move`
(`fltAcc_nd`, `rrAcc_nd`, `preNd_of`). `slPre_of` assembles `SlPre`; `sl_pathObl_lay` /
`sl_pathSide_lay` restate the entry's obligations with every `SlPre` field from the layout.

Premises: `SlAccIn` [J]/[P] (each field tagged there), `RegionOKX` (with `asidT`, `kern` [J]),
`SlEnt`, `SlHere`, `SlPreB` (its fields: P1 facts at the prefix state [J], fl4-sync's lock `hlk` [P]).
-/
import Fl4Proofs.P2.SlDecL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}

/-! ## Owners to the read / write sets -/

/-- A word of a locked object is in the read and write sets. -/
theorem slRW_of_lock {s : S} {x p : U64} (ha : Aligned x) (h : region K x = .obj p) (hl : Locks s p) :
    SlRS (st := st) K Locks s x ∧ SlWS (st := st) K Locks s x := by
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) x := by
    show HeldBy (L.cpu s) (Locks s) (own K (L.mem s) x)
    simp only [own, h]
    exact hl
  exact ⟨⟨ha, Or.inr (Or.inl hw)⟩, ⟨ha, Or.inr hw⟩⟩

/-- An aligned user word is in the read and write sets. -/
theorem slRW_of_user {s : S} {x : U64} (h : Aligned x ∧ x ∈ K.user) :
    SlRS (st := st) K Locks s x ∧ SlWS (st := st) K Locks s x :=
  ⟨⟨h.1, Or.inl h.2⟩, ⟨h.1, Or.inl h.2⟩⟩

/-- A non-gate, non-timer word of a thread fit for its `STATE` writes (`Safe0`: homed here,
queued only on a held lock) is in the read and write sets. -/
theorem rw_tcb_safe (hX : RegionOKX K) {t o : U64} (ht : K.heap t = some .tcb) (h1 : 192 ≤ o.val)
    (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hg : ¬ GateField o.val) (hT : ¬ TimerField o.val) {s : S}
    (hs : Safe0 (L.cpu s) (Locks s) (L.mem s) t) :
    SlRS (st := st) K Locks s (core.num.U64.wrapping_add t o) ∧
      SlWS (st := st) K Locks s (core.num.U64.wrapping_add t o) := by
  by_cases hG : GField o.val
  · have ha := (hX.tcbW t ht o h1 h2 h3).2.2
    have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) (core.num.U64.wrapping_add t o) := by
      show HeldBy (L.cpu s) (Locks s) (own K (L.mem s) (core.num.U64.wrapping_add t o))
      rw [own_tcbW hX ht h1 h2 h3]
      simp only [tcbOwner, if_neg hg, if_neg hT, if_pos hG, gOwner]
      by_cases hq : QueuedState (L.mem s (fld t oSTATE))
      · rw [if_pos hq]; exact hs.2 hq
      · rw [if_neg hq]; exact hs.1
    exact ⟨⟨ha, Or.inr (Or.inl hw)⟩, ⟨ha, Or.inr hw⟩⟩
  · exact rs_tcb_home hX ht h1 h2 h3 hg hT hG (by rw [affA_fld]; exact hs.1)

/-- A queue link of a thread queued on a held lock is in the read and write sets. -/
theorem rw_tcb_q (hX : RegionOKX K) {t o : U64} (ht : K.heap t = some .tcb) (h1 : 192 ≤ o.val)
    (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hG : GField o.val) {s : S}
    (hq : QueuedState (L.mem s (stA t))) (hl : Locks s (L.mem s (blockA t))) :
    SlRS (st := st) K Locks s (core.num.U64.wrapping_add t o) ∧
      SlWS (st := st) K Locks s (core.num.U64.wrapping_add t o) := by
  have hg : ¬ GateField o.val := by unfold GField at hG; unfold GateField; omega
  have hT : ¬ TimerField o.val := by unfold GField at hG; unfold TimerField; omega
  have ha := (hX.tcbW t ht o h1 h2 h3).2.2
  rw [stA_fld] at hq
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) (core.num.U64.wrapping_add t o) := by
    show HeldBy (L.cpu s) (Locks s) (own K (L.mem s) (core.num.U64.wrapping_add t o))
    rw [own_tcbW hX ht h1 h2 h3]
    simp only [tcbOwner, if_neg hg, if_neg hT, if_pos hG, gOwner, if_pos hq]
    exact hl
  exact ⟨⟨ha, Or.inr (Or.inl hw)⟩, ⟨ha, Or.inr hw⟩⟩

/-- A register address as an offset into the TCB (no placement needed). -/
theorem regA_eq' {t r : U64} (hr : r.val < 384) :
    ∃ o : U64, o.val = 256 + 8 * r.val ∧ regA t r = core.num.U64.wrapping_add t o := by
  have hv : (⟨BitVec.ofNat 64 (256 + 8 * r.val)⟩ : U64).val = 256 + 8 * r.val := by
    show (BitVec.ofNat 64 (256 + 8 * r.val)).toNat = _
    simp; omega
  refine ⟨⟨BitVec.ofNat 64 (256 + 8 * r.val)⟩, hv, ?_⟩
  apply UScalar.eq_of_val_eq
  unfold regA
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, hv]
  omega

/-- The registers of a thread fit for its `STATE` writes. -/
theorem regs_safe (hX : RegionOKX K) {t : U64} (ht : K.heap t = some .tcb) {s : S}
    (hs : Safe0 (L.cpu s) (Locks s) (L.mem s) t) {r : U64} (hr : r.val < 384) :
    SlRS (st := st) K Locks s (regA t r) ∧ SlWS (st := st) K Locks s (regA t r) := by
  obtain ⟨o, ho, e⟩ := regA_eq' (t := t) hr
  rw [e]
  exact rw_tcb_safe hX ht (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
    (by simp only [TimerField]; omega) hs

/-- A TCB slot's two words are in the read set. -/
theorem rs_tslot (hK : RegionOK K) (hX : RegionOKX K) {t i : U64} (ht : K.heap t = some .tcb)
    (hi : i.val < 6) {s : S} :
    SlRS (st := st) K Locks s (slotIdx t i) ∧
      SlRS (st := st) K Locks s (core.num.U64.wrapping_add (slotIdx t i) 8#u64) := by
  obtain ⟨-, -, -, -, a0, a8⟩ := hX.tslot t ht i hi
  obtain ⟨g0, g8⟩ := own_tslot hK hX ht hi (L.mem s)
  exact ⟨slRS_of_gate a0 g0, slRS_of_gate a8 g8⟩

theorem vtA_slot (t : U64) : vtA t = slotIdx t layout.tcb.SLOT_VTABLE := by
  unfold vtA slotIdx layout.cte.SIZE
  rfl

/-! ## Words that are not owner-dependency words (`NonDec`) -/

/-- Where an owner-dependency word (`DecW`) lies. -/
theorem decW_region (hK : RegionOK K) {d : U64} (h : DecW K d) :
    (∃ t off, region K d = .tcb t ∧ DecOff off ∧ d.val - t.val = off.val) ∨ (∃ p, region K d = .slot p ∧ d = p) ∨
      (∃ p, region K d = .ntfn p ∧ d.val - p.val = 24) ∨ (∃ p, region K d = .sc p ∧ d.val = p.val + 16) := by
  rcases h with ⟨t, off, ht, ho, rfl⟩ | hs | ⟨p, hp, rfl⟩ | ⟨p, b, hb, rfl⟩
  · exact Or.inl ⟨t, off, (hK.tcb t ht off ho.reg).1, ho, (hK.tcb t ht off ho.reg).2⟩
  · exact Or.inr (Or.inl ⟨d, hK.slot d hs, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, (hK.ntfn p hp).1, (hK.ntfn p hp).2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p, (hK.scw p b hb).1, (hK.scw p b hb).2⟩))

theorem nonDec_reg (hK : RegionOK K) {x : U64} (ha : Aligned x)
    (h1 : ∀ t, region K x ≠ .tcb t) (h2 : ∀ p, region K x ≠ .slot p) (h3 : ∀ p, region K x ≠ .ntfn p)
    (h4 : ∀ p, region K x = .sc p → x.val ≠ p.val + 16) : NonDec K x := by
  refine ⟨ha, fun hd => ?_⟩
  rcases decW_region hK hd with ⟨t, -, hr, -, -⟩ | ⟨p, hr, -⟩ | ⟨p, hr, -⟩ | ⟨p, hr, hv⟩
  · exact h1 t hr
  · exact h2 p hr
  · exact h3 p hr
  · exact h4 p hr hv

/-- A word in a node, an endpoint / reply object, or no typed object is not an owner-dependency
word. -/
theorem nonDec_of_region (hK : RegionOK K) {x : U64} (ha : Aligned x)
    (hr : (∃ c, region K x = .node c) ∨ (∃ p, region K x = .obj p) ∨ region K x = .none) : NonDec K x := by
  rcases hr with ⟨c, hr⟩ | ⟨p, hr⟩ | hr <;>
    exact nonDec_reg hK ha (fun t h => by rw [hr] at h; cases h) (fun q h => by rw [hr] at h; cases h)
      (fun q h => by rw [hr] at h; cases h) (fun q h => by rw [hr] at h; cases h)

/-- An aligned user word is not an owner-dependency word (kernel objects are not user memory). -/
theorem nonDec_user (hK : RegionOK K) (hX : RegionOKX K) {x : U64} (h : Aligned x ∧ x ∈ K.user) :
    NonDec K x := by
  have hr : region K x = .none := by
    by_contra hne
    exact hX.kern x hne h.2
  exact nonDec_of_region hK h.1 (Or.inr (Or.inr hr))

/-- A TCB word at an offset other than `AFFINITY`, `STATE`, `BLOCK_OBJ`, `TIMER_DEADLINE`,
`TIMER_HEIGHT` is not an owner-dependency word. -/
theorem nonDec_tcb (hK : RegionOK K) (hX : RegionOKX K) {t o : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0)
    (hd : o.val ≠ 3520 ∧ o.val ≠ 3328 ∧ o.val ≠ 3336 ∧ o.val ≠ 3528 ∧ o.val ≠ 3568) :
    NonDec K (core.num.U64.wrapping_add t o) := by
  obtain ⟨r, d, a⟩ := hX.tcbW t ht o h1 h2 h3
  refine ⟨a, fun hw => ?_⟩
  rcases decW_region hK hw with ⟨t', off, hr, ho, hv⟩ | ⟨p, hr, -⟩ | ⟨p, hr, -⟩ | ⟨p, hr, -⟩ <;> rw [r] at hr
  · cases hr
    rcases ho with e | e | e | e | e <;> rw [e] at hv <;>
      simp only [oAFF_val, oSTATE_val, oBOBJ_val, oDL_val, oHT_val] at hv <;> omega
  all_goals cases hr

/-- An SC word other than `CORE` is not an owner-dependency word. -/
theorem nonDec_sc (hK : RegionOK K) {x p : U64} (ha : Aligned x) (hr : region K x = .sc p)
    (hv : x.val ≠ p.val + 16) : NonDec K x :=
  nonDec_reg hK ha (fun t h => by rw [hr] at h; cases h) (fun q h => by rw [hr] at h; cases h)
    (fun q h => by rw [hr] at h; cases h) (fun q h => by rw [hr] at h; cases h; exact hv)

/-- What an accepted run writes, for `SlPre`'s two pairs of sets at once: writable (`SlWS`) and not
an owner-dependency word (`NonDec`). -/
def SlWN (K : KLayout) (Locks : S → U64 → Prop) (s : S) (b : U64) : Prop :=
  SlWS (st := st) K Locks s b ∧ NonDec K b

theorem rwn_tcb (hK : RegionOK K) (hX : RegionOKX K) {t o : U64} (ht : K.heap t = some .tcb) (h1 : 192 ≤ o.val)
    (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hg : ¬ GateField o.val) (hT : ¬ TimerField o.val) {s : S}
    (hs : Safe0 (L.cpu s) (Locks s) (L.mem s) t)
    (hd : o.val ≠ 3520 ∧ o.val ≠ 3328 ∧ o.val ≠ 3336 ∧ o.val ≠ 3528 ∧ o.val ≠ 3568) :
    SlRS (st := st) K Locks s (core.num.U64.wrapping_add t o) ∧
      SlWN (st := st) K Locks s (core.num.U64.wrapping_add t o) :=
  ⟨(rw_tcb_safe hX ht h1 h2 h3 hg hT hs).1, (rw_tcb_safe hX ht h1 h2 h3 hg hT hs).2,
    nonDec_tcb hK hX ht h1 h2 h3 hd⟩

theorem regs_wn (hK : RegionOK K) (hX : RegionOKX K) {t : U64} (ht : K.heap t = some .tcb) {s : S}
    (hs : Safe0 (L.cpu s) (Locks s) (L.mem s) t) {r : U64} (hr : r.val < 384) :
    SlRS (st := st) K Locks s (regA t r) ∧ SlWN (st := st) K Locks s (regA t r) := by
  obtain ⟨o, ho, e⟩ := regA_eq' (t := t) hr
  rw [e]
  exact rwn_tcb hK hX ht (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
    (by simp only [TimerField]; omega) hs (by omega)

theorem slRWN_of_lock (hK : RegionOK K) {s : S} {x p : U64} (ha : Aligned x) (h : region K x = .obj p)
    (hl : Locks s p) : SlRS (st := st) K Locks s x ∧ SlWN (st := st) K Locks s x :=
  ⟨(slRW_of_lock ha h hl).1, (slRW_of_lock ha h hl).2, nonDec_of_region hK ha (Or.inr (Or.inl ⟨p, h⟩))⟩

/-- A node word of this core is not an owner-dependency word. -/
theorem nonDec_node (hK : RegionOK K) (hX : RegionOKX K) {T : Set U64} {s : S}
    (hN : NodePlaced st T s (L.cpu s)) (hk : L.ksb s = K.ksb) (hc : (L.cpu s).val < K.ncores) {o : U64}
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) : NonDec K (L.nodeAt s (L.cpu s) o) := by
  have v := nodeAt_val hN ho
  have hr : region K (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) :=
    hX.node _ _ ⟨hc, by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega,
      by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega⟩
  exact nonDec_of_region hK (nodeAt_aligned hN ho h8) (Or.inl ⟨_, hr⟩)

/-- An SC homed here, with its ring and `CONSUMED` in `SlWN`. -/
theorem scAcc_wn (hK : RegionOK K) (hX : RegionOKX K) {s : S} {sc : U64} {z : Nat}
    (hz : K.heap sc = some (.sc z)) (hc : L.mem s (fld sc 16#u64) = L.cpu s) :
    ScAcc (SlRS (st := st) K Locks s) (SlWN (st := st) K Locks s) sc z := by
  have H := scAcc_here (st := st) (Locks := Locks) hX hz hc
  obtain ⟨a8, h128, hfit⟩ := hX.scP sc z hz
  refine ⟨H.rd, fun b ha hb => ⟨H.wr b ha hb, nonDec_sc hK ha (hX.scW sc z hz b hb.inSC) (by
    have := hb.1; omega)⟩, ⟨H.cons, ?_⟩⟩
  have e : (core.num.U64.wrapping_add sc layout.sc.CONSUMED).val = sc.val + 8 := by
    simp [layout.sc.CONSUMED, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  exact nonDec_sc hK (by unfold Aligned; rw [e]; omega)
    (hX.scW sc z hz _ ⟨by rw [e]; omega, by rw [e]; omega⟩) (by rw [e]; omega)

/-! ## Monotone in the read set -/

theorem ScAcc.rmono {R R' W : U64 → Prop} (hR : ∀ b, R b → R' b) {sc : U64} {sb : Nat}
    (K : ScAcc R W sc sb) : ScAcc R' W sc sb :=
  ⟨fun b ha hb => hR _ (K.rd b ha hb), K.wr, K.cons⟩

theorem FltAcc.rmono {Z : U64 → Nat} {R R' W : U64 → Prop} (hR : ∀ b, R b → R' b) {s : S}
    {t ptr dest r : U64} (K : FltAcc (L := L) Z R W s t ptr dest r) :
    FltAcc (L := L) Z R' W s t ptr dest r where
  nd o h1 h2 := ⟨hR _ (K.nd o h1 h2).1, (K.nd o h1 h2).2⟩
  dt := hR _ K.dt
  cd := hR _ K.cd
  kr := hR _ K.kr
  tab hi hhi := ⟨hR _ (K.tab hi hhi).1, fun lo hlo hne => hR _ ((K.tab hi hhi).2 lo hlo hne)⟩
  fh sl h := ⟨hR _ (K.fh sl h).1, hR _ (K.fh sl h).2⟩
  eph := ⟨hR _ K.eph.1, K.eph.2⟩
  ept := ⟨hR _ K.ept.1, K.ept.2⟩
  tf k hk := ⟨hR _ (K.tf k hk).1, (K.tf k hk).2⟩
  treg r hr := hR _ (K.treg r hr)
  trp := K.trp
  drp := hR _ K.drp
  daf := hR _ K.daf
  ddo := hR _ K.ddo
  dsc0 := hR _ K.dsc0
  diq := hR _ K.diq
  dpr := hR _ K.dpr
  dyt := hR _ K.dyt
  dst := hR _ K.dst
  dfi := hR _ K.dfi
  den := hR _ K.den
  dib := hR _ K.dib
  dvt := ⟨hR _ K.dvt.1, hR _ K.dvt.2⟩
  dbs sl h := ⟨hR _ (K.dbs sl h).1, hR _ (K.dbs sl h).2⟩
  dw := K.dw
  dreg := K.dreg
  nxt := K.nxt
  buf := K.buf
  rt := K.rt
  spo := hR _ K.spo
  dsc := K.dsc.rmono hR
  csc := K.csc.rmono hR
  tm h := hR _ (K.tm h)
  rh h := ⟨hR _ (K.rh h).1, fun b ha hb => hR _ ((K.rh h).2.1 b ha hb), RdHead.mono hR (K.rh h).2.2⟩

theorem RrAcc.rmono {Z : U64 → Nat} {R R' W : U64 → Prop} (hR : ∀ b, R b → R' b) {s : S}
    {t rptr ep u usc : U64} (K : RrAcc (L := L) Z R W s t rptr ep u usc) :
    RrAcc (L := L) Z R' W s t rptr ep u usc where
  nd o h1 h2 := ⟨hR _ (K.nd o h1 h2).1, (K.nd o h1 h2).2⟩
  dt := hR _ K.dt
  cd := hR _ K.cd
  kr := hR _ K.kr
  tab hi hhi := ⟨hR _ (K.tab hi hhi).1, fun lo hlo hne => hR _ ((K.tab hi hhi).2 lo hlo hne)⟩
  tSt := hR _ K.tSt
  tSc := hR _ K.tSc
  tMx := hR _ K.tMx
  tIq := hR _ K.tIq
  tMi := hR _ K.tMi
  tBn := hR _ K.tBn
  tPr := hR _ K.tPr
  tReg r hr := hR _ (K.tReg r hr)
  tBuf := by
    obtain ⟨sl, h1, h2, h3, h4⟩ := K.tBuf
    exact ⟨sl, h1, hR _ h2, hR _ h3, hR _ h4⟩
  tBw buf h hne i hi := hR _ (K.tBw buf h hne i hi)
  ntf n h1 h2 := ⟨hR _ (K.ntf n h1 h2).1, hR _ (K.ntf n h1 h2).2⟩
  wRp := K.wRp
  wEn := K.wEn
  wEp := K.wEp
  rRt := hR _ K.rRt
  rNx := hR _ K.rNx
  rPv := hR _ K.rPv
  wNx := K.wNx
  wPv := K.wPv
  wRt := K.wRt
  uSt := hR _ K.uSt
  uFt := ⟨hR _ K.uFt.1, K.uFt.2⟩
  uSc := hR _ K.uSc
  uPr := hR _ K.uPr
  uAf := hR _ K.uAf
  uDo := hR _ K.uDo
  uIq := hR _ K.uIq
  uMx := hR _ K.uMx
  uReg := K.uReg
  uYt := hR _ K.uYt
  uFi := hR _ K.uFi
  uVt := ⟨hR _ K.uVt.1, hR _ K.uVt.2⟩
  eTS := hR _ K.eTS
  wEh := K.wEh
  wEt := K.wEt
  spo := hR _ K.spo
  cor := hR _ K.cor
  ccs := hR _ K.ccs
  uHd := RdHead.mono hR K.uHd
  uscA := K.uscA.rmono hR
  csc := K.csc.rmono hR
  tm h := hR _ (K.tm h)
  rh h := ⟨hR _ (K.rh h).1, fun b ha hb => hR _ ((K.rh h).2.1 b ha hb), RdHead.mono hR (K.rh h).2.2⟩

/-! ## The new entry facts -/

variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **The entry facts the accepted arms need beyond `SlEnt` / `SlHere`**, at the entry state `s`
(prefix state `X`, under the arm's checks). -/
structure SlAccIn (K : KLayout) (Locks : S → U64 → Prop) (Z : U64 → Nat) (Scs : Set U64)
    (found : U64 × U64) (s : S) : Prop where
  /-- [J] the ASID pools the table names are untyped kernel words: in no typed object of the
  layout (region `.none`, so gate-owned) and aligned (P1 `AsidOff` puts them among the kernel
  words `Ω`; the p2e VM line's `hTab` [J], P2/AccessVmTail.lean: the pools as their own region
  kind of the ownership map, discharged by P3's layout). -/
  pool : ∀ hi : U64, hi.val < 2048 → L.mem s (atAF K.ksb hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
    Aligned (peAF (L.mem s (atAF K.ksb hi)) lo) ∧ region K (peAF (L.mem s (atAF K.ksb hi)) lo) = .none
  /-- [J]/[P] trap arm: the receiver's reply object is a heap reply (P1 reply invariant: a thread
  blocked on receive with a nonzero `REPLY_OBJ` names a reply) and fl4-sync holds its lock
  (`lock_object(m, r, ..)`, crates/fl4-sync/src/lib.rs l.695). -/
  frp : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → K.heap r = some .reply ∧ Locks s r
  /-- [J] trap arm: the receiver's SC (nonzero: `schedulable_here`) is homed here (P1: a thread's
  bound SC is on the thread's core). -/
  dsc : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → ScHere (st := st) K Z Scs s (L.mem s (scA dest))
  /-- [J] trap arm: when the receiver is not the queue's tail, the next queued thread is a heap TCB
  blocked on receive on the handler endpoint (P1's endpoint queue invariant: `QueueRel` of the
  endpoint's queue, its members' `STATE` / `BLOCK_OBJ`). -/
  nq : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → (L.epQ X ptr).end ≠ dest →
    K.heap (L.mem X (nextA .Ep dest)) = some .tcb ∧ QueuedState (L.mem X (stA (L.mem X (nextA .Ep dest)))) ∧
      L.mem X (blockA (L.mem X (nextA .Ep dest))) = ptr
  /-- [J] trap arm: the receiver's IPC buffer words are aligned user words (P1 `BufW` / P3: a
  thread's IPC buffer lies in a frame, `K.user`). -/
  fbuf : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → ∀ rb, msg.lookup_ipc_buffer st X true dest = ok rb →
    BufW (fun b => Aligned b ∧ b ∈ K.user) rb
  /-- [J] ReplyRecv arm: the current thread's IPC buffer words are aligned user words. -/
  rbuf : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ buf,
    msg.lookup_ipc_buffer st X false (L.curW s) = ok buf → BufW (fun b => Aligned b ∧ b ∈ K.user) buf

/-! ## Common words at the prefix state -/

/-- The node, kernel globals, ASID words, timer and release-head words at the prefix state. -/
structure SlAccC (Z : U64 → Nat) (R W : U64 → Prop) (X : S) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o) ∧ W (L.nodeAt X (L.cpu X) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)
  kr : R (krA (L := L) X)
  tab : RdTab (L := L) R X
  tm : L.mem X (tmA (L := L) X) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64)
  rh : L.mem X (rhA (L := L) X) ≠ 0#u64 → R (scA (L.mem X (rhA (L := L) X))) ∧
    (∀ b, Aligned b → InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) (Z (L.mem X (scA (L.mem X (rhA (L := L) X))))) b →
      R b) ∧
    RdHead (L := L) R X (L.mem X (scA (L.mem X (rhA (L := L) X))))

theorem slAccC_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K Z Scs found s) (Ai : SlAccIn (st := st) ar K Locks Z Scs found s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    SlAccC (L := L) Z (SlRS (st := st) K Locks s) (SlWN (st := st) K Locks s) X := by
  have C := slCom_of ar hA hK hX E Hh LP
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])) (not_slDS_node E.hN E.hT E.hcT (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  refine ⟨fun o h1 h2 => by
      rw [nX]
      exact ⟨(rs_node hX E.hN Hh.ksb Hh.cpu h1 h2).1, (rs_node hX E.hN Hh.ksb Hh.cpu h1 h2).2,
        nonDec_node hK hX E.hN Hh.ksb Hh.cpu h1 h2⟩, C.dt, C.cd, ?_, ?_, C.tm, ?_⟩
  · show SlRS (st := st) K Locks s (core.num.U64.wrapping_add (L.ksb X) layout.ks.KERNEL_ROOT)
    rw [kX]
    exact rs_ks hX E.hN Hh.ksb (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
  · intro hi hhi
    rw [kX, Hh.ksb]
    obtain ⟨r0, a0⟩ := hX.asidT hi hhi
    have e0 : L.mem X (atAF K.ksb hi) = L.mem s (atAF K.ksb hi) :=
      lp_mem ar hA E.hT E.hN E.hcT LP a0 (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
        (by rw [r0]; intro c h; cases h) (by rw [r0]; intro h; cases h))
    refine ⟨slRS_of_gate a0 (by simp only [own, r0]), fun lo hlo hne => ?_⟩
    rw [e0] at hne ⊢
    obtain ⟨a1', r1⟩ := Ai.pool hi hhi hne lo hlo
    exact slRS_of_gate a1' (by simp only [own, r1])
  · intro h
    obtain ⟨h1, h3⟩ := C.rh h
    refine ⟨h1, ?_, h3⟩
    rw [eRh] at h ⊢
    obtain ⟨ht, hs⟩ := Hh.rh h
    have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu ht (by simp) (by simp) (by simp) (by simp))
    rw [eS]
    obtain ⟨hz, -, -, hco⟩ := hs
    exact (scAcc_here hX hz hco).rd

/-! ## The trap arm -/

/-- The checks' endpoint is the heap endpoint named by the fault-handler cap at the entry, whose
lock fl4-sync holds. -/
theorem trap_ep (hA : P0.ArchTotal ar) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (I : SlThrIn (st := st) K Locks found.1 s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) : K.heap ptr = some .ep ∧ Locks s ptr := by
  obtain ⟨sl, x, y, g, gr, hsl, hcap, -⟩ := hc.cap
  rw [tcb_slot_val] at hsl
  obtain rfl := ok_inj_ff hsl
  obtain ⟨f1, f2, f3, f4⟩ := I.fh hS
  rw [cap_congr (lp_mem ar hA E.hT E.hN E.hcT LP f1.1 f3) (lp_mem ar hA E.hT E.hN E.hcT LP f2.1 f4)] at hcap
  have hp : resPtr (obj.Slot.cap st (fhA (L := L) s) s) = ptr := resPtr_ok hcap
  have hE : IsEp (obj.Slot.cap st (fhA (L := L) s) s) := ⟨_, _, _, _, _, _, hcap⟩
  have he := N.hep hS hE
  have hl := N.lep hS hE
  rw [hp] at he hl
  exact ⟨he, hl⟩

set_option maxHeartbeats 4000000 in
/-- **The trap arm's access facts from the ownership map**, writes in `SlWN`. -/
theorem fltAcc_wn (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hh : SlHere (st := st) K Z Scs found s)
    (Ai : SlAccIn (st := st) ar K Locks Z Scs found s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) :
    FltAcc (L := L) Z (SlRS (st := st) K Locks s) (SlWN (st := st) K Locks s) X (L.curW s) ptr dest r := by
  have I : SlThrIn (st := st) K Locks found.1 s := slThrIn_of hK hX (preAcc_of ar hX E Hh) E.hSt.1 N
  have C := slAccC_of ar hA hK hX E Hh Ai LP
  obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  have hs0 := E.hSt.2
  obtain ⟨hep, hlk⟩ := trap_ep ar hA E N I hS LP hc
  obtain ⟨hdt, hds, -, -⟩ := E.hSd hS a X a1 LP hc
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  obtain ⟨hz, -, -, hco⟩ := Ai.dsc hS a X a1 LP hc
  have eSc : L.mem X (scA dest) = L.mem s (scA dest) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hdt 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT hdt (by simp) (by simp) (by simp) (by simp))
  obtain ⟨r1, a1h⟩ := hX.epW _ hep layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
  obtain ⟨r2, a2h⟩ := hX.epW _ hep layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE])
    (by simp [layout.ep.TAIL_STATE])
  obtain ⟨hrp, hlr⟩ := Ai.frp hS a X a1 LP hc
  obtain ⟨r3, a3h⟩ := hX.rpW _ hrp layout.reply.TCB (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
  exact
  { nd := C.nd
    dt := C.dt
    cd := C.cd
    kr := C.kr
    tab := C.tab
    fh := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact ⟨(I.fh hS).1, (I.fh hS).2.1⟩
    eph := slRWN_of_lock hK a1h r1 hlk
    ept := slRWN_of_lock hK a2h r2 hlk
    tf := fun o ho => rwn_tcb hK hX hc0 (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
      (by simp only [TimerField]; omega) hs0 (by omega)
    treg := fun _ hr => (regs_safe hX hc0 hs0 hr).1
    trp := (rwn_tcb hK hX hc0 (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    drp := (rw_tcb_safe hX hdt (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds).1
    daf := rs_tcb_gate hX hdt (o := 3520#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    ddo := rs_tcb_gate hX hdt (o := 3432#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dsc0 := rs_tcb_gate hX hdt (o := 3464#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    diq := (rw_tcb_safe hX hdt (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds).1
    dpr := rs_tcb_gate hX hdt (o := 3448#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dyt := (rw_tcb_safe hX hdt (o := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds).1
    dst := by
      rw [stA_eq]
      exact (rw_tcb_safe hX hdt (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds).1
    dfi := (regs_safe hX hdt hds (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])).1
    den := (rw_tcb_safe hX hdt (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds).1
    dib := rs_tcb_gate hX hdt (o := 3512#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dvt := by
      rw [vtA_slot]
      exact rs_tslot hK hX hdt (by simp [layout.tcb.SLOT_VTABLE])
    dbs := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact rs_tslot hK hX hdt (by simp [layout.tcb.SLOT_BUFFER])
    dw := ⟨(rwn_tcb hK hX hdt (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2,
      (rwn_tcb hK hX hdt (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2,
      (rwn_tcb hK hX hdt (o := 3480#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2,
      (rwn_tcb hK hX hdt (o := 3488#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2⟩
    dreg := fun _ hr => (regs_wn hK hX hdt hds hr).2
    nxt := fun hne => by
      obtain ⟨hnt, hq, hb⟩ := Ai.nq hS a X a1 LP hc hne
      have eSt : L.mem X (stA (L.mem X (nextA .Ep dest))) = L.mem s (stA (L.mem X (nextA .Ep dest))) := by
        rw [stA_eq]
        exact lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hnt 3328#u64 (by simp) (by simp) (by simp)).2.2
          (nT hnt (by simp) (by simp) (by simp) (by simp))
      have eBl : L.mem X (blockA (L.mem X (nextA .Ep dest))) = L.mem s (blockA (L.mem X (nextA .Ep dest))) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hnt 3336#u64 (by simp) (by simp) (by simp)).2.2
          (nT hnt (by simp) (by simp) (by simp) (by simp))
      rw [eSt] at hq
      rw [eBl] at hb
      exact ⟨(rw_tcb_q hX hnt (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GField]) hq
        (by rw [hb]; exact hlk)).2, nonDec_tcb hK hX hnt (o := 3504#u64) (by simp) (by simp) (by simp) (by simp)⟩
    buf := fun rb hrb hne i hi => ⟨(slRW_of_user (Ai.fbuf hS a X a1 LP hc rb hrb hne i hi)).2,
      nonDec_user hK hX (Ai.fbuf hS a X a1 LP hc rb hrb hne i hi)⟩
    rt := (slRWN_of_lock hK a3h r3 hlr).2
    spo := by
      rw [eSc]
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact (scAcc_here hX hz hco).rd _ am hin
    dsc := by
      rw [eSc]
      exact scAcc_wn hK hX hz hco
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, hco'⟩ := Hh.cs
      exact scAcc_wn hK hX hz' hco'
    tm := C.tm
    rh := C.rh }

/-! ## The ReplyRecv arm -/

set_option maxHeartbeats 4000000 in
/-- **The ReplyRecv arm's access facts from the ownership map**, writes in `SlWN`. -/
theorem rrAcc_wn (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hh : SlHere (st := st) K Z Scs found s)
    (Ai : SlAccIn (st := st) ar K Locks Z Scs found s) (hS : ¬ SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {u usc : U64}
    (hc : RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc) :
    RrAcc (L := L) Z (SlRS (st := st) K Locks s) (SlWN (st := st) K Locks s) X (L.curW s) found.1 found.2 u usc := by
  have I : SlThrIn (st := st) K Locks found.1 s := slThrIn_of hK hX (preAcc_of ar hX E Hh) E.hSt.1 N
  have C := slAccC_of ar hA hK hX E Hh Ai LP
  have D := (slDecIn_of ar hA hK hX E N Hh).rT hS a X a1 LP
  obtain ⟨-, cX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  have hs0 := E.hSt.2
  obtain ⟨hut, hus, -, -, -⟩ := E.hSu hS a X a1 LP u usc hc
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  -- the replied thread is the decided thread; its SC is homed here
  have eu : u = slThr st found.1 s := by
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hc.tcb, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    exact h1
  have lv : SlLive st found.1 s := slLive_rr (st := st) hS (by rw [← eu]; exact u_ne0 hc.u0)
  have haf : L.mem s (affA (slThr st found.1 s)) = L.cpu s := by rw [← eu, affA_fld]; exact hus.1
  have eusc : usc = L.mem s (scA u) := by
    have h1 := hc.sc
    rw [tcb_sc_ok] at h1
    rw [← ok_inj_ff h1]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hut 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT hut (by simp) (by simp) (by simp) (by simp))
  have husc0 : usc ≠ 0#u64 := by
    obtain ⟨b, hb, hn⟩ := hc.sc0
    rw [eq_of_spec_fd (obj.Sc.is_null.spec usc)] at hb
    rw [← ok_inj_ff hb] at hn
    simpa using hn
  have Hs := Hh.usc hS lv haf (by rw [← eu, ← eusc]; exact husc0)
  rw [← eu, ← eusc] at Hs
  obtain ⟨hz, hin0, hmx0, hco⟩ := Hs
  have hrp := N.hrp hS
  have hlr := N.lrp hS
  obtain ⟨rt1, rta⟩ := hX.rpW _ hrp layout.reply.TCB (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
  obtain ⟨rn1, rna⟩ := hX.rpW _ hrp layout.reply.NEXT (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])
  obtain ⟨rp1, rpa⟩ := hX.rpW _ hrp layout.reply.PREV (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])
  obtain ⟨eh1, eha⟩ := hX.epW _ (Hh.ep hS) layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
  obtain ⟨et1, eta⟩ := hX.epW _ (Hh.ep hS) layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE])
    (by simp [layout.ep.TAIL_STATE])
  obtain ⟨-, aC, hinC, rC⟩ := sc_off hX hz (o := layout.sc.CORE) (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
  have eC : L.mem X (core.num.U64.wrapping_add usc layout.sc.CORE) = L.cpu X := by
    rw [lp_mem ar hA E.hT E.hN E.hcT LP aC (not_slDS_reg hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu
      (by rw [rC]; intro c h; cases h) (by rw [rC]; intro h; cases h)), cX]
    have e : core.num.U64.wrapping_add usc layout.sc.CORE = fld usc 16#u64 := by simp [fld, layout.sc.CORE]
    rw [e]
    exact hco
  exact
  { nd := C.nd
    dt := C.dt
    cd := C.cd
    kr := C.kr
    tab := C.tab
    tSt := D.tSt
    tSc := D.tSc
    tMx := D.tMx
    tIq := D.tIq
    tMi := D.tMi
    tBn := D.tBn
    tPr := D.tPr
    tReg := fun _ hr => (regs_safe hX hc0 hs0 hr).1
    tBuf := ⟨_, tcb_slot_val _ _, rs_tcb_gate hX hc0 (o := 3512#u64) (by simp) (by simp) (by simp)
      (by simp [GateField]), (rs_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).1,
      (rs_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).2⟩
    tBw := fun buf hb hne i hi => (slRW_of_user (Ai.rbuf hS a X a1 LP buf hb hne i hi)).1
    ntf := D.ntf
    wRp := (rwn_tcb hK hX hc0 (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    wEn := (rwn_tcb hK hX hc0 (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    wEp := (rwn_tcb hK hX hc0 (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    rRt := D.rRt
    rNx := D.rNx
    rPv := (slRW_of_lock rpa rp1 hlr).1
    wNx := (slRWN_of_lock hK rna rn1 hlr).2
    wPv := (slRWN_of_lock hK rpa rp1 hlr).2
    wRt := (slRWN_of_lock hK rta rt1 hlr).2
    uSt := by
      rw [stA_eq]
      exact (rw_tcb_safe hX hut (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hus).1
    uFt := rwn_tcb hK hX hut (o := 3376#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus (by simp)
    uSc := rs_tcb_gate hX hut (o := 3464#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uPr := rs_tcb_gate hX hut (o := 3448#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uAf := rs_tcb_gate hX hut (o := 3520#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uDo := rs_tcb_gate hX hut (o := 3432#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uIq := (rw_tcb_safe hX hut (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus).1
    uMx := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact (scAcc_here hX hz hco).rd _ am hin
    uReg := fun _ hr => (regs_wn hK hX hut hus hr).2
    uYt := (rw_tcb_safe hX hut (o := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus).1
    uFi := (regs_safe hX hut hus (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])).1
    uVt := by
      rw [vtA_slot]
      exact rs_tslot hK hX hut (by simp [layout.tcb.SLOT_VTABLE])
    eTS := D.eTS
    wEh := (slRWN_of_lock hK eha eh1 (E.hlk hS)).2
    wEt := (slRWN_of_lock hK eta et1 (E.hlk hS)).2
    spo := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact (scAcc_here hX hz hco).rd _ am hin
    cor := (scAcc_here hX hz hco).rd _ aC hinC
    ccs := by
      rw [eC]
      exact (C.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
    uHd := rdHead_here ar hA hX E Hh LP ⟨hz, hin0, hmx0, hco⟩
    uscA := scAcc_wn hK hX hz hco
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, hco'⟩ := Hh.cs
      exact scAcc_wn hK hX hz' hco'
    tm := C.tm
    rh := C.rh }

/-! ## `SlPre`'s access fields -/

/-- **`SlPre.hRWfG` from the ownership map.** -/
theorem fltAcc_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hh : SlHere (st := st) K Z Scs found s)
    (Ai : SlAccIn (st := st) ar K Locks Z Scs found s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) :
    FltAcc (L := L) Z (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) X (L.curW s) ptr dest r :=
  (fltAcc_wn ar hA hK hX E N Hh Ai hS LP hc).wmono (fun _ h => h.1)

/-- **`SlPre.hRWf` from the ownership map.** -/
theorem fltAcc_nd (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hh : SlHere (st := st) K Z Scs found s)
    (Ai : SlAccIn (st := st) ar K Locks Z Scs found s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) :
    FltAcc (L := L) Z (fun _ => True) (NonDec K) X (L.curW s) ptr dest r :=
  FltAcc.rmono (fun _ _ => trivial) ((fltAcc_wn ar hA hK hX E N Hh Ai hS LP hc).wmono (fun _ h => h.2))

/-- **`SlPre.hRWrG` from the ownership map.** -/
theorem rrAcc_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hh : SlHere (st := st) K Z Scs found s)
    (Ai : SlAccIn (st := st) ar K Locks Z Scs found s) (hS : ¬ SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {u usc : U64}
    (hc : RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc) :
    RrAcc (L := L) Z (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) X (L.curW s) found.1 found.2 u usc :=
  (rrAcc_wn ar hA hK hX E N Hh Ai hS LP hc).wmono (fun _ h => h.1)

/-- **`SlPre.hRWr` from the ownership map.** -/
theorem rrAcc_nd (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hh : SlHere (st := st) K Z Scs found s)
    (Ai : SlAccIn (st := st) ar K Locks Z Scs found s) (hS : ¬ SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {u usc : U64}
    (hc : RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc) :
    RrAcc (L := L) Z (fun _ => True) (NonDec K) X (L.curW s) found.1 found.2 u usc :=
  RrAcc.rmono (fun _ _ => trivial) ((rrAcc_wn ar hA hK hX E N Hh Ai hS LP hc).wmono (fun _ h => h.2))

/-- **`SlPre.pre` from the layout**: the prefix writes this core's node and the current thread's
`FAULT_IP`, neither an owner-dependency word. -/
theorem preNd_of (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K Z Scs found s) : PreAcc (L := L) (fun _ => True) (NonDec K) s := by
  obtain ⟨KF, hKF, eKF⟩ := fip_eq E.hT E.hcT
  refine ⟨fun o h1 h2 => ⟨trivial, nonDec_node hK hX E.hN Hh.ksb Hh.cpu h1 h2⟩, trivial, trivial, ?_⟩
  rw [eKF]
  exact nonDec_tcb hK hX E.hSt.1 (by omega) (by omega) (by omega) (by omega)

/-- **`SlPre` from `SlPreB`, the layout, `SlEnt`, `SlHere` and `SlAccIn`** (`preG` by `preAcc_of`,
`hhd` by `hhd_of`, `pre` by `preNd_of`, `hRWf(G)` / `hRWr(G)` by `fltAcc_nd` / `fltAcc_of`,
`rrAcc_nd` / `rrAcc_of`). -/
theorem slPre_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hh : SlHere (st := st) K Z Scs found s)
    (Ai : SlAccIn (st := st) ar K Locks Z Scs found s) :
    SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s :=
  { toSlPreB := E, preG := preAcc_of ar hX E Hh, hhd := fun _ _ _ _ LP hcs => hhd_of ar hA hX E Hh LP hcs,
    pre := preNd_of ar hK hX E Hh
    hRWf := fun hS _ _ _ LP {_p _b _d _r} hc => fltAcc_nd ar hA hK hX E N Hh Ai hS LP hc
    hRWfG := fun hS _ _ _ LP {_p _b _d _r} hc => fltAcc_of ar hA hK hX E N Hh Ai hS LP hc
    hRWr := fun hS _ _ _ LP _ _ hc => rrAcc_nd ar hA hK hX E N Hh Ai hS LP hc
    hRWrG := fun hS _ _ _ LP _ _ hc => rrAcc_of ar hA hK hX E N Hh Ai hS LP hc }

variable {p : SProg Bool}

/-- **`PathObl` of the syscall entry from the ownership map**: `sl_pathObl_ent` with `SlDecIn`
from `slDecIn_of` and `SlPre` from `slPre_of` (`SlHere`, `SlAccIn` [J]). -/
theorem sl_pathObl_lay (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K)
    (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {P : S → Prop} (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hE : ∀ s, P s → SlEnt (st := st) K Locks found s)
    (hH : ∀ s, P s → SlHere (st := st) K Z Scs found s)
    (hAi : ∀ s, P s → SlAccIn (st := st) ar K Locks Z Scs found s) :
    PathObl st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathObl_ent ar hA hK hX hU hFp hz hm (fun s hP => slPre_of ar hA hK hX (hPE s hP) (hE s hP) (hH s hP) (hAi s hP)) hE
    (fun s hP => slDecIn_of ar hA hK hX (hPE s hP) (hE s hP) (hH s hP))

/-- **`PathSide` of the syscall entry from the ownership map** (`sl_pathSide_ent`, `slDecIn_of`,
`slPre_of`). -/
theorem sl_pathSide_lay (hS : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hX : RegionOKX K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {P : S → Prop} (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hE : ∀ s, P s → SlEnt (st := st) K Locks found s)
    (hH : ∀ s, P s → SlHere (st := st) K Z Scs found s)
    (hAi : ∀ s, P s → SlAccIn (st := st) ar K Locks Z Scs found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s) :
    PathSide st (fun m s a => syscall.handle_syscall_local m ar s a n found)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathSide_ent ar hS hA hK hX hU hFp hz hm (fun s hP => slPre_of ar hA hK hX (hPE s hP) (hE s hP) (hH s hP) (hAi s hP)) hE
    (fun s hP => slDecIn_of ar hA hK hX (hPE s hP) (hE s hP) (hH s hP)) huf

end

end Fl4Proofs.P2.PathObl

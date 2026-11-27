/-
# P2 (line slj): the syscall entry's [J] premises from P3's joint invariant

`sl_localPath` (P2/SlLP.lean) is generic in its sets and layout and carries many [J] premises
about the entry state. Here one bundled entry premise, `SlJAt K s` (P3's joint invariant `JAtZ`
at the entry with `K` its layout `OwnMap.layoutJ Zx H (L.ksb s) n` and the cores `Cs` the
layout's), together with the P1 sets convention of `JAtZ.blk` (`T = H.tcbs`, `Rp = H.replies`,
`Scs = H.scs`, `Nt = H.ntfns`, `Z = H.scBits`, P1's user words `U = K.user`), replaces:

* `SlSets` — by the convention (`slSets_conv`);
* `hK` (`RegionOK`), `hU` (`UserOK`) — `OwnMap.ok_of_JAtZ` at an anchor state (`hKJ`: the
  layout is read off a joint-invariant state, P2/SerExit.lean);
* `hX` (`RegionOKX`) — `regionOKX_of` from `LayP` (`layP_of_JAtZ`), the TCB slots of `Z.th`
  (`JPlaced.tcb`), the IPC-buffer words off endpoints / replies (`EPlaced.be` / `br`, `JAtZ.hset`)
  and off the nodes (`JAtZ.nodeB`, `JKern.csLt`), and the residual `SlKsJ` (below);
* `hUu` — by the convention `U = K.user`;
* `SlHereJ.ksb`, `SlHereJ.cpu` (`JKern.cpuCs` with `SlJAt.cs`), `SlAccK.jz` (the bundle itself).

Remaining premises (tagged): `SlJAt` [J] (the bundle: what P3 gives at a kernel entry of the
U29 chain, see its docstring for the one part P3 does not state), `SlKsJ` [J] (two
kernel-state-block facts P3 states only as premises elsewhere), `SlHereJ.cs`, `csc`, `ep`,
`SlAccK.pool`, `frl`, `SlEntJ.dsR`, `hep`, `hrp`, `lep`, `lrp`, `huf`, `hSt`, `hm`, `hpz`, `hPE`
as in `sl_localPath`.
-/
import Fl4Proofs.P2.SlLP
import Fl4Proofs.P2.OwnJAtZ
import Fl4Proofs.P3.XTopJointEntryInv29
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

/-! ## `RegionOKX` from the placement -/

section
variable {K : KLayout}

theorem slj_slotIdx_val {t i : U64} (h : t.val + 32 * i.val + 32 ≤ 2 ^ 64) :
    (slotIdx t i).val = t.val + 32 * i.val := by
  unfold slotIdx
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem slj_add8_val {p : U64} (h : p.val + 8 < 2 ^ 64) :
    (core.num.U64.wrapping_add p 8#u64).val = p.val + 8 := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- Two slots holding one word are one (slots are 32-aligned). -/
theorem _root_.Fl4Proofs.P2.OwnMap.LayP.slj_slot_uniq (h : LayP K) {p q b : U64} (hp : p ∈ K.slots) (hq : q ∈ K.slots)
    (hb : InW p 32 b) (hb' : InW q 32 b) : p = q := by
  have e1 := (h.slot p hp).1
  have e2 := (h.slot q hq).1
  obtain ⟨b1, b2⟩ := hb
  obtain ⟨b3, b4⟩ := hb'
  exact UScalar.eq_of_val_eq (by omega)

/-- The region of a word of a slot is that slot. -/
theorem _root_.Fl4Proofs.P2.OwnMap.LayP.slj_region_slot (h : LayP K) {p b : U64} (hp : p ∈ K.slots) (hb : InW p 32 b) :
    region K b = .slot p := by
  have hex : ∃ q ∈ K.slots, InW q 32 b := ⟨p, hp, hb⟩
  obtain ⟨q, k, hq, hqb, -, -⟩ := h.slot_obj hp hb
  unfold region
  rw [dif_neg (h.no_node hq hqb), dif_pos hex]
  have hc := Classical.choose_spec hex
  rw [h.slj_slot_uniq hc.1 hp hc.2 hb]

/-- The region of a word of an endpoint or reply object. -/
theorem _root_.Fl4Proofs.P2.OwnMap.LayP.slj_region_obj (h : LayP K) {p b : U64} {k : HKind} (hp : K.heap p = some k)
    (hk : k = .ep ∨ k = .reply) (hb : InW p (2 ^ k.bits) b) : region K b = .obj p := by
  have hk1 : ∀ z, k ≠ .other z := by intro z e; rcases hk with rfl | rfl <;> cases e
  have hk2 : k ≠ .tcb := by intro e; rcases hk with rfl | rfl <;> cases e
  have hex : ∃ p, (K.heap p = some .ep ∧ InW p (2 ^ 4) b) ∨ (K.heap p = some .reply ∧ InW p (2 ^ 5) b) := by
    rcases hk with rfl | rfl
    · exact ⟨p, Or.inl ⟨hp, hb⟩⟩
    · exact ⟨p, Or.inr ⟨hp, hb⟩⟩
  unfold region
  rw [dif_neg (h.no_node hp hb), dif_neg (h.no_slot hp hb hk1 (fun e => absurd e hk2)), dif_neg, dif_neg,
    dif_pos hex]
  · have hc := Classical.choose_spec hex
    rcases hc with ⟨hq, hqb⟩ | ⟨hq, hqb⟩
    · exact congrArg Region.obj (h.uniq hq hp hqb hb).1
    · exact congrArg Region.obj (h.uniq hq hp hqb hb).1
  · rintro ⟨q, hq, hqb⟩
    have := (h.uniq hq hp hqb hb).2
    subst this; rcases hk with e | e <;> cases e
  · rintro ⟨t, ht, htb⟩
    have := (h.uniq ht hp htb hb).2
    subst this; rcases hk with e | e <;> cases e

/-- The region of a node word. -/
theorem slj_region_node {c b : U64} (hb : InNode K c b) : region K b = .node c := by
  have hex : ∃ c, InNode K c b := ⟨c, hb⟩
  unfold region
  rw [dif_pos hex]
  have hc := Classical.choose_spec hex
  obtain ⟨-, h1, h2⟩ := hc
  obtain ⟨-, h3, h4⟩ := hb
  congr 1
  apply UScalar.eq_of_val_eq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · have : (Classical.choose hex).val * 4288 + 4288 ≤ c.val * 4288 := by
      have := Nat.mul_le_mul_right 4288 (Nat.succ_le_of_lt hl); simpa [Nat.succ_mul] using this
    omega
  · have : c.val * 4288 + 4288 ≤ (Classical.choose hex).val * 4288 := by
      have := Nat.mul_le_mul_right 4288 (Nat.succ_le_of_lt hl); simpa [Nat.succ_mul] using this
    omega

/-- **`RegionOKX` from the placement** `LayP` and four layout facts: the TCBs' six slots are
slots of the layout; user words lie in no endpoint, reply or node; and the residual kernel-state
facts (`ks`, `asidT`, as in `RegionOKX`). -/
theorem regionOKX_of (h : LayP K)
    (hts : ∀ t, K.heap t = some .tcb → ∀ i : U64, i.val < 6 → slotIdx t i ∈ K.slots)
    (huE : ∀ x ∈ K.user, ∀ p k, K.heap p = some k → (k = .ep ∨ k = .reply) → ¬ InW p (2 ^ k.bits) x)
    (huN : ∀ x ∈ K.user, ∀ c, ¬ InNode K c x)
    (hks : ∀ b, Aligned b → K.ksb.val ≤ b.val → b.val < K.ksb.val + 256 → region K b = .none)
    (hasid : ∀ hi : U64, hi.val < 2048 → region K (atAF K.ksb hi) = .none ∧ Aligned (atAF K.ksb hi)) :
    RegionOKX K where
  tslot t ht i hi := by
    have hf := h.heap.fits t _ ht
    have ha := h.heap.align t _ ht
    simp only [HKind.bits] at hf ha
    have hs := hts t ht i hi
    have hv : (slotIdx t i).val = t.val + 32 * i.val := slj_slotIdx_val (by omega)
    have h8 : (core.num.U64.wrapping_add (slotIdx t i) 8#u64).val = t.val + 32 * i.val + 8 := by
      rw [slj_add8_val (by omega), hv]
    refine ⟨hs, ⟨t, ht, by rw [hv]; omega, by rw [hv]; omega⟩, h.slj_region_slot hs ⟨by omega, by omega⟩,
      by omega, ?_, ?_⟩
    · have := (h.slot _ hs).1; unfold Aligned; omega
    · have := (h.slot _ hs).1; unfold Aligned; omega
  tcbW t ht o h1 h2 h3 := by
    have hv := h.tcb_fld ht h2
    have ha := h.heap.align t _ ht
    simp only [HKind.bits] at ha
    exact ⟨h.region_tcb ht ⟨by unfold fld at hv; omega, by unfold fld at hv; omega⟩
      (by unfold fld at hv; omega), by unfold fld at hv; omega, by unfold fld at hv; unfold Aligned; omega⟩
  epW p hp o h1 h2 := by
    have hf := h.heap.fits p _ hp
    have ha := h.heap.align p _ hp
    simp only [HKind.bits] at hf ha
    have hv : (core.num.U64.wrapping_add p o).val = p.val + o.val := fld_val (by omega)
    exact ⟨h.slj_region_obj hp (Or.inl rfl) ⟨by omega, by simp only [HKind.bits]; omega⟩,
      by unfold Aligned; omega⟩
  rpW p hp o h1 h2 := by
    have hf := h.heap.fits p _ hp
    have ha := h.heap.align p _ hp
    simp only [HKind.bits] at hf ha
    have hv : (core.num.U64.wrapping_add p o).val = p.val + o.val := fld_val (by omega)
    exact ⟨h.slj_region_obj hp (Or.inr rfl) ⟨by omega, by simp only [HKind.bits]; omega⟩,
      by unfold Aligned; omega⟩
  scW p z hp b hb := h.region_sc hp hb
  scP p z hp := by
    have hf := h.heap.fits p _ hp
    have ha := h.heap.align p _ hp
    have hz := h.heap.scmin p z hp
    simp only [HKind.bits] at hf ha
    have h7 : (2 : Nat) ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by omega) hz
    exact ⟨align8 ha (by omega), by simpa using h7, hf⟩
  ntW p hp o h1 h2 := by
    have hf := h.heap.fits p _ hp
    have ha := h.heap.align p _ hp
    simp only [HKind.bits] at hf ha
    have hv : (core.num.U64.wrapping_add p o).val = p.val + o.val := fld_val (by omega)
    exact ⟨h.region_ntfn hp ⟨by omega, by omega⟩, by omega, by unfold Aligned; omega⟩
  node c b hb := slj_region_node hb
  ks := hks
  kern b hne hu := by
    apply hne
    unfold region
    rw [dif_neg (fun ⟨c, hc⟩ => huN b hu c hc), dif_neg (fun ⟨p, hp, hpb⟩ => h.userSlot b hu p hp hpb),
      dif_neg (fun ⟨t, ht, htb⟩ => h.user b hu t _ ht (Or.inl rfl) htb),
      dif_neg (fun ⟨p, hp, hpb⟩ => h.user b hu p _ hp (Or.inr (Or.inl rfl)) hpb), dif_neg, dif_neg]
    · rintro ⟨p, z, hp, hpb⟩
      exact h.user b hu p _ hp (Or.inr (Or.inr ⟨z, rfl⟩)) hpb
    · rintro ⟨p, ⟨hp, hpb⟩ | ⟨hp, hpb⟩⟩
      · exact huE b hu p _ hp (Or.inl rfl) hpb
      · exact huE b hu p _ hp (Or.inr rfl) hpb
  asidT := hasid

end

/-! ## The bundled entry premise -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The syscall entry as a state of P3's joint invariant, at given ghosts** (fields below;
`SlJAt` quantifies the ghosts). -/
structure SlJAtZ {A' : Type} (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Cx Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (K : KLayout) (s : S) (a' : A')
    (σ : Fl4Spec.State Unit) : Prop where
  /-- The joint invariant at the entry, with `K`'s heap as its typed heap `H`. -/
  j : Fl4Proofs.P3.JAtZ (L := L) arI AR Zx K.heap Cx Ax Lst D s a' σ
  /-- `K` is the layout read off that state (`layoutJ`, P2/SerExit.lean). -/
  lay : layoutJ Zx K.heap (L.ksb s) K.ncores = K
  /-- The layout's cores are `JAtZ`'s `Cs` (P3: `JKern.csN`, the cores numbered from 0; line slj2). -/
  cs : ∀ c : U64, c ∈ Cx ↔ c.val < K.ncores
  /-- The scheduler action is resume (an entry state: `SInvX`'s `cr`, P3). Gives P1's
  `EntryInv` at the entry (`JAtZ.entryInv`, P3/XTopJointEntryInv29.lean). -/
  res : σ.schedulerAction = .resumeCurThread

/-- **The bundled entry premise** [J]: what P3 gives at a kernel entry of the U29 chain
(`JAt`: `JAtZ` at some ghosts), with `K` that state's layout and the three [J] fields of
`SlJAtZ`. -/
def SlJAt (K : KLayout) (s : S) : Prop :=
  ∃ (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Cx Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ

variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

theorem SlJAtZ.ksb (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) : L.ksb s = K.ksb := by
  rw [← B.lay]; rfl

theorem SlJAtZ.user (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    K.user = {b | ∃ wp ∈ Zx.B, wp.1 = b} := by
  rw [← B.lay]; rfl

theorem SlJAtZ.slots (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    K.slots = {a | Fl4Proofs.P3.IsSlot Zx.th a} := by
  rw [← B.lay]; rfl

theorem SlJAtZ.cpu (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) : (L.cpu s).val < K.ncores :=
  (B.cs _).1 B.j.kern.cpuCs

theorem SlJAtZ.layP (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) : LayP K := by
  have h := layP_of_JAtZ B.j (n := K.ncores) fun c hc => (B.cs c).2 hc
  rwa [B.lay] at h

theorem SlJAtZ.okRU (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    RegionOK K ∧ Fl4Proofs.P2.E2E.UserOK K := by
  have h := ok_of_JAtZ B.j (n := K.ncores) fun c hc => (B.cs c).2 hc
  rwa [B.lay] at h

/-- The TCBs' six slots are slots of `Zx.th`. -/
theorem SlJAtZ.tslots (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ∀ t, K.heap t = some .tcb → ∀ i : U64, i.val < 6 → slotIdx t i ∈ K.slots := by
  intro t ht i hi
  obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
  have hth : Zx.th t = some .tcb := (hJ.tcb t).2 ht
  have hf := hJ.heap.fits t _ ht
  simp only [HKind.bits] at hf
  rw [B.slots]
  have hsa : Fl4Proofs.P3.IsSlotAt Zx.th t i.val := Or.inr ⟨hth, by unfold Fl4Proofs.P3.tcbSlots; omega⟩
  refine ⟨t, i.val, hsa, ?_⟩
  apply UScalar.eq_of_val_eq
  rw [hsa.val hJ.pl, slj_slotIdx_val (by omega)]

/-- User words lie in no endpoint or reply. -/
theorem SlJAtZ.userEp (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ∀ x ∈ K.user, ∀ p k, K.heap p = some k → (k = .ep ∨ k = .reply) → ¬ InW p (2 ^ k.bits) x := by
  intro x hx p k hp hk hin
  rw [B.user] at hx
  obtain ⟨wp, hw, rfl⟩ := hx
  obtain ⟨h1, h2⟩ := hin
  rcases hk with rfl | rfl
  · have := B.j.ip.e.be wp hw p (B.j.hset.1 p hp)
    simp only [HKind.bits] at h2; omega
  · have := B.j.ip.e.br wp hw p (B.j.hset.2.2 p hp)
    simp only [HKind.bits] at h2; omega

/-- User words lie in no node. -/
theorem SlJAtZ.userNode (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ∀ x ∈ K.user, ∀ c, ¬ InNode K c x := by
  intro x hx c ⟨hc, h1, h2⟩
  rw [B.user] at hx
  obtain ⟨wp, hw, rfl⟩ := hx
  have h64 := B.j.kern.csLt c ((B.cs c).2 hc)
  have := B.j.nodeB wp hw c h64
  have hk := B.ksb
  simp only [LawfulStore.nodeBase, hk] at this
  omega

/-- **`SlSets` by the P1 sets convention** (`JAtZ.blk`'s sets). -/
theorem slSets_conv (K : KLayout) :
    SlSets K K.heap.tcbs K.heap.replies K.heap.scs K.heap.ntfns K.heap K.heap.scBits :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The kernel globals of the first 256 bytes of the block lie in no object of `Zx.th`**
(formerly the bundle's [J] field `ksO`; P3's `hksO`): `JAtZ.th_dom` (P3/JEntryKs.lean). -/
theorem SlJAtZ.ksO (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ∀ b : U64, Aligned b → (L.ksb s).val ≤ b.val → b.val < (L.ksb s).val + 256 →
      Fl4Proofs.P3.OutsideObjects Zx.th b := by
  intro b ha h1 h2
  refine ⟨ha, fun p k hp hin => ?_⟩
  have h := B.j.th_dom hp
  omega

/-- **A word of the ASID table or of a ghost ASID pool (`Vs.VsWrite`) is in no region of the
layout but a node, and aligned**: P3's VSpace placement (`TopPlaced.vo`: outside the objects of
`Zx.th`, so off every slot and TCB; `TopPlaced.disj`: off the endpoints, replies, notifications
and SCs of the relation's sets, which hold `H`'s by `JAtZ.hset` / `hscC`). -/
theorem SlJAtZ.vsNone (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {b : U64}
    (hb : Fl4Proofs.P3.Vs.VsWrite Zx.P (L.ksb s) b) (hn : ∀ c, ¬ InNode K c b) :
    region K b = .none ∧ Aligned b := by
  have hTP := B.j.xtop.fin.1.2
  have hO := hTP.vo b hb
  have hV := Fl4Proofs.P3.Vs.vsWrite_vobj (th := Zx.th) (L4 := Zx.L4) (L3 := Zx.L3) (L2 := Zx.L2) (L1 := Zx.L1)
    hTP.vs hb
  obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
  have hnd : ¬ ∃ c, InNode K c b := fun ⟨c, hc⟩ => hn c hc
  have hslot : ¬ ∃ p ∈ K.slots, InW p 32 b := by
    rintro ⟨p, hp, g1, g2⟩
    rw [B.slots] at hp
    obtain ⟨q, i, hqi, rfl⟩ := hp
    obtain ⟨k, hk', hsz⟩ := hqi.size
    have hv := hqi.val hJ.pl
    exact hO.2 q k hk' ⟨by omega, by omega⟩
  have htcb : ¬ ∃ t, K.heap t = some .tcb ∧ InW t (2 ^ 12) b := by
    rintro ⟨t, ht, g1, g2⟩
    exact hO.2 t .tcb ((hJ.tcb t).2 ht) ⟨g1, by simp only [Fl4Proofs.P3.objSize]; omega⟩
  have hnt : ¬ ∃ p, K.heap p = some .ntfn ∧ InW p (2 ^ 6) b := by
    rintro ⟨p, hp, g1, g2⟩
    exact hTP.disj b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, B.j.hset.2.1 p hp, g1, by omega⟩)))))) hV
  have hob : ¬ ∃ p, (K.heap p = some .ep ∧ InW p (2 ^ 4) b) ∨ (K.heap p = some .reply ∧ InW p (2 ^ 5) b) := by
    rintro ⟨p, ⟨hp, g1, g2⟩ | ⟨hp, g1, g2⟩⟩
    · exact hTP.disj b (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, B.j.hset.1 p hp, g1, by omega⟩)))) hV
    · exact hTP.disj b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, B.j.hset.2.2 p hp, g1, by omega⟩))))) hV
  have hsc : ¬ ∃ p z, K.heap p = some (.sc z) ∧ InW p (2 ^ z) b := by
    rintro ⟨p, z, hp, g1, g2⟩
    have hpC := B.j.hscC p z hp
    obtain ⟨Q, R0, hc, hs⟩ := B.j.xtop.fin.1.1.1.lists
    obtain ⟨x, n, hk, -⟩ := hs.scs p hpC
    have e := (hJ.sc p x n (B.j.c0 p hpC) hk).2
    rw [hp] at e
    have ez : z = n + Fl4Spec.minSchedContextBits := by
      injection e with e; injection e
    exact hTP.disj b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, hpC, x, n, hk, g1, by rw [← ez]; exact g2⟩))))))) hV
  refine ⟨?_, hO.1⟩
  unfold region
  rw [dif_neg hnd, dif_neg hslot, dif_neg htcb, dif_neg hnt, dif_neg hob, dif_neg hsc]

/-- **The ASID table is in no region and aligned** (`RegionOKX.asidT`; formerly the bundle's
[J] field `asid`): `vsNone`, the table at `[ksb+288000, ksb+304384)` past every node
(`VsPlaced.ksb_fit`, `JKern.csLt`). -/
theorem SlJAtZ.asid (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ∀ hi : U64, hi.val < 2048 → region K (atAF K.ksb hi) = .none ∧ Aligned (atAF K.ksb hi) := by
  intro hi hhi
  have hk := B.ksb
  have hvs := B.j.xtop.fin.1.2.vs
  have e : atAF K.ksb hi = Fl4Proofs.P3.Vs.atA (L.ksb s) hi := by rw [← hk]; rfl
  have hv : (Fl4Proofs.P3.Vs.atA (L.ksb s) hi).val = (L.ksb s).val + 288000 + 8 * hi.val :=
    Fl4Proofs.P3.Vs.atA_val hvs.ksb_fit hhi
  rw [e]
  refine B.vsNone (Or.inl ⟨hi, hhi, rfl⟩) fun c ⟨hc, h1, h2⟩ => ?_
  have h64 := B.j.kern.csLt c ((B.cs c).2 hc)
  rw [hv, ← hk] at h2
  omega

/-- **The ASID pools the table names are in no region and aligned** (`SlAccIn.pool`; formerly
the premise `SlAccK.pool` / `SlAccR.pool` [J]): a nonzero table entry is a ghost pool
(`VsRel.tmem`), whose words are `VsWrite` words (`vsNone`); the pool is a spec ASID pool
(`VsRel.pool`), so an `other` object of `H` of at least a page (`SpecCover.arch`), off every
node (`JKern.hnd`). -/
theorem SlJAtZ.pool (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ∀ hi : U64, hi.val < 2048 → L.mem s (atAF K.ksb hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
      Aligned (peAF (L.mem s (atAF K.ksb hi)) lo) ∧ region K (peAF (L.mem s (atAF K.ksb hi)) lo) = .none := by
  intro hi hhi h0 lo hlo
  have hk := B.ksb
  have hTP := B.j.xtop.fin.1.2
  have e : atAF K.ksb hi = Fl4Proofs.P3.Vs.atA (L.ksb s) hi := by rw [← hk]; rfl
  rw [e] at h0 ⊢
  have hP := B.j.xtop.fin.2.1.tmem hi hhi h0
  generalize L.mem s (Fl4Proofs.P3.Vs.atA (L.ksb s) hi) = p at hP h0 ⊢
  obtain ⟨f, hf, -⟩ := B.j.xtop.fin.2.1.pool p hP
  obtain ⟨n, hn12, hH⟩ := B.j.cover.arch _ _ hf
  have hH' : K.heap p = some (.other n) := hH
  have hpal := hTP.vs.pal p hP
  have hv : (peAF p lo).val = p.val + 8 * lo.val := Fl4Proofs.P3.Vs.peA_val hpal.2 hlo
  have h4 : (4096 : Nat) ≤ 2 ^ n :=
    calc (4096 : Nat) = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn12
  have hR := B.vsNone (b := peAF p lo) (Or.inr ⟨p, hP, lo, hlo, rfl⟩) fun c ⟨hc, h1, h2⟩ => by
    have hnd := B.j.kern.hnd _ _ hH' c ((B.cs c).2 hc)
    simp only [HKind.bits, LawfulStore.nodeBase] at hnd
    rw [hv, ← hk] at h1 h2
    omega
  exact ⟨hR.2, hR.1⟩

/-- **The current SC is active and homed here, and it is the current thread's SC**
(formerly the premises `SlHereJ.cs` / `csc` [J]): P1's `EntryInv` at the entry (`JAtZ.entryInv`
with `res`: `CUR_SC` an active SC, `SCsOK.act`), P3's `CurInv` (the current thread's SC word is
`CUR_SC`, nonzero), P3's scheduler relation (every thread of `Zx.T` has this core as its
`AFFINITY`, `SchedCore.aff`) and P1's `ScAff` (`XInv.core_eq`: the SC's `CORE` word is its
thread's `AFFINITY`). -/
theorem SlJAtZ.cscFacts (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ScHere (st := st) K K.heap.scBits K.heap.scs s (L.cscW s) ∧ L.mem s (scA (L.curW s)) = L.cscW s := by
  have EI := B.j.entryInv B.res
  have hcS : L.cscW s ∈ K.heap.scs := EI.cscS
  have hcA := EI.csc
  have hC : Fl4Proofs.P3.Sched.CurInv σ := B.j.curInv (by rw [B.res]; intro e; cases e)
  have hS := B.j.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨-, hsc0, -, hts, -⟩ := Fl4Proofs.P3.Sched.CurInv.facts hS B.j.inv hC
  have ecur : L.curW s = Fl4Proofs.P3.Sched.nodeW st s Zx.c layout.node.CUR_THREAD := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have ecsc : L.cscW s = Fl4Proofs.P3.Sched.nodeW st s Zx.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have hts' : L.mem s (scA (L.curW s)) = L.cscW s := by rw [ecur, ecsc]; exact hts
  have hcT : L.curW s ∈ Zx.T := by rw [B.j.tcbs_eq.1]; exact B.j.kern.curH
  have haf : L.mem s (affA (L.curW s)) = L.cpu s := (hc.aff _ hcT).trans hc.cur.symm
  have h0 : L.mem s (scA (L.curW s)) ≠ 0#u64 := by rw [hts', ecsc]; exact hsc0
  have hce := Fl4Proofs.P1.XInv.core_eq EI.2.2.1 (t := L.curW s) B.j.kern.curH h0
  refine ⟨⟨(slSets_conv K).sc hcS, hcS, (EI.2.2.2.1.act _ hcS).1 hcA, ?_⟩, hts'⟩
  have e16 : fld (L.cscW s) 16#u64 = scCoreA (L.cscW s) := by
    unfold fld scCoreA
    congr 1
    simp [layout.sc.CORE]
  rw [e16, ← hts', ← hce, haf]

/-- The kernel globals of the first 256 bytes of the block are in no region. -/
theorem SlJAtZ.ksNone (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ∀ b, Aligned b → K.ksb.val ≤ b.val → b.val < K.ksb.val + 256 → region K b = .none := by
  intro b ha h1 h2
  have hk := B.ksb
  rw [← hk] at h1 h2
  have hO := B.ksO b ha h1 h2
  obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
  have hobj : ∀ p k, K.heap p = some k → (∀ z, k ≠ .other z) → ¬ InW p (2 ^ k.bits) b := by
    intro p k hp hk' ⟨g1, g2⟩
    rcases hJ.ks p k hp hk' with e | e <;> omega
  unfold region
  rw [dif_neg, dif_neg, dif_neg (fun ⟨t, ht, htb⟩ => hobj t _ ht (by intro z e; cases e) htb),
    dif_neg (fun ⟨p, hp, hpb⟩ => hobj p _ hp (by intro z e; cases e) hpb), dif_neg, dif_neg]
  · rintro ⟨p, z, hp, hpb⟩
    exact hobj p _ hp (by intro z' e; cases e) hpb
  · rintro ⟨p, ⟨hp, hpb⟩ | ⟨hp, hpb⟩⟩
    · exact hobj p _ hp (by intro z e; cases e) hpb
    · exact hobj p _ hp (by intro z e; cases e) hpb
  · rintro ⟨p, hp, g1, g2⟩
    rw [B.slots] at hp
    obtain ⟨q, i, hqi, rfl⟩ := hp
    obtain ⟨k, hk', hsz⟩ := hqi.size
    have hv := hqi.val hJ.pl
    exact hO.2 q k hk' ⟨by omega, by omega⟩
  · rintro ⟨c, -, g1, -⟩
    rw [← hk] at g1
    omega

/-- **`RegionOKX` from the bundle.** -/
theorem SlJAtZ.regionOKX (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) : RegionOKX K :=
  regionOKX_of B.layP B.tslots B.userEp B.userNode B.ksNone B.asid

theorem SlJAt.regionOK {s : S} (B : SlJAt (L := L) K s) : RegionOK K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B; exact B.okRU.1

theorem SlJAt.userOK {s : S} (B : SlJAt (L := L) K s) : Fl4Proofs.P2.E2E.UserOK K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B; exact B.okRU.2

theorem SlJAt.regionOKX {s : S} (B : SlJAt (L := L) K s) : RegionOKX K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B; exact B.regionOKX

/-- The current thread's `FAULT_IP` register word. -/
theorem slj_faultIp_val {t : U64} (h : t.val + 4096 ≤ 2 ^ 64) :
    (regA t layout.reg.FAULT_IP).val = t.val + 392 := by
  unfold regA
  simp [layout.tcb.REGS, layout.reg.FAULT_IP, core.num.U64.wrapping_add_val_eq,
    core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  omega

/-- **`SlEntJ.dsR` from the bundle**: the prefix words are this core's node words (`CUR_TIME`,
`CONSUMED`) or the current thread's `FAULT_IP` (a TCB word at offset 392). -/
theorem SlJAtZ.dsR (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {T : Set U64}
    (hN : NodePlaced st T s (L.cpu s)) :
    ∀ x, SlDS (L := L) s x → (∃ c, region K x = .node c) ∨ region K x = .tcb (L.curW s) := by
  have hk := B.ksb
  have hc := B.cpu
  have hnode : ∀ o : U64, o.val < 4288 → region K (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) := by
    intro o ho
    have v := nodeAt_val hN ho
    exact slj_region_node ⟨hc, by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega,
      by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega⟩
  intro x hx
  rcases hx with rfl | rfl | rfl
  · right
    have ht : K.heap (L.curW s) = some .tcb := B.j.kern.curH
    have hf := B.layP.heap.fits _ _ ht
    simp only [HKind.bits] at hf
    have hv := slj_faultIp_val (t := L.curW s) (by omega)
    exact B.layP.region_tcb ht ⟨by omega, by omega⟩ (by omega)
  · exact Or.inl ⟨_, hnode _ (by simp [layout.node.CUR_TIME])⟩
  · exact Or.inl ⟨_, hnode _ (by simp [layout.node.CONSUMED])⟩

/-- **`SlEntJ.hep` from the bundle**: the current thread's fault-handler slot is a TCB slot of
`Zx.th`, whose cap is typed (`JPlaced.typed`): an endpoint cap names a heap endpoint. -/
theorem SlJAtZ.hep (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    (hE : IsEp (obj.Slot.cap st (fhA (L := L) s) s)) :
    K.heap (resPtr (obj.Slot.cap st (fhA (L := L) s) s)) = some .ep := by
  obtain ⟨ptr, b, x, y, g, gr, e⟩ := hE
  rw [resPtr_ok e]
  obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
  have hsl : fhA (L := L) s ∈ K.slots :=
    B.tslots _ B.j.kern.curH layout.tcb.SLOT_FAULT_HANDLER (by unfold layout.tcb.SLOT_FAULT_HANDLER; simp)
  rw [B.slots] at hsl
  have hc : obj.Slot.cap st (fhA (L := L) s) s = ok (Fl4Proofs.P3.capV (L.mem s) (fhA (L := L) s)) := by
    rw [Fl4Proofs.P3.slot_cap_eq]; exact Fl4Proofs.P3.capAt_capV _ _
  have e2 : Fl4Proofs.P3.capV (L.mem s) (fhA (L := L) s) = .Endpoint ptr b x y g gr :=
    ok_inj_ff (hc.symm.trans e)
  exact (hJ.typed _ hsl).1 ptr b x y g gr e2

/-- **What stays of `SlEntJ`** once `dsR` and `hep` come from the bundle. -/
structure SlEntR (K : KLayout) (Locks : S → U64 → Prop) (found : U64 × U64) (s : S) : Prop where
  /-- [J] as `SlEnt.hrp` (fl4-sync's reply object is a heap reply). -/
  hrp : ¬ SlTrap st s → K.heap found.1 = some .reply
  /-- [P] as `SlEnt.lep`. -/
  lep : SlTrap st s → IsEp (obj.Slot.cap st (fhA (L := L) s) s) →
    Locks s (resPtr (obj.Slot.cap st (fhA (L := L) s) s))
  /-- [P] as `SlEnt.lrp`. -/
  lrp : ¬ SlTrap st s → Locks s found.1

theorem SlJAt.entJ {Locks : S → U64 → Prop} {found : U64 × U64} {T : Set U64} (B : SlJAt (L := L) K s)
    (hN : NodePlaced st T s (L.cpu s)) (R : SlEntR (st := st) K Locks found s) :
    SlEntJ (st := st) K Locks found s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B
  exact ⟨B.dsR hN, fun _ hE => B.hep hE, R.hrp, R.lep, R.lrp⟩

/-- **What stays of `SlHereJ`** once `ksb`, `cpu` (the bundle) and `cs`, `csc`
(`SlJAtZ.cscFacts`, line slj2) are derived. -/
structure SlHereR (K : KLayout) (found : U64 × U64) (s : S) : Prop where
  /-- [J] as `SlHereJ.ep`. -/
  ep : ¬ SlTrap st s → K.heap found.2 = some .ep

theorem SlJAt.hereJ {found : U64 × U64} (B : SlJAt (L := L) K s)
    (R : SlHereR (st := st) K found s) : SlHereJ (st := st) K K.heap.scBits K.heap.scs found s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B
  exact ⟨B.ksb, B.cpu, B.cscFacts.1, fun _ => by rw [B.cscFacts.2]; exact B.cscFacts.1, R.ep⟩

/-- **What stays of `SlAccK`** once `jz` (the bundle) and `pool` (`SlJAtZ.pool`, line slj2)
are derived. -/
structure SlAccR {A : Type} (ar : machine.Arch A) (K : KLayout) (Locks : S → U64 → Prop) (found : U64 × U64)
    (s : S) : Prop where
  /-- [P] as `SlAccK.frl`. -/
  frl : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → Locks s r

theorem SlJAt.accK {A : Type} {ar : machine.Arch A} {Locks : S → U64 → Prop} {found : U64 × U64}
    (B : SlJAt (L := L) K s) (R : SlAccR (st := st) ar K Locks found s) :
    SlAccK (st := st) ar K Locks found s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := B
  exact ⟨B.pool, R.frl, ⟨A', arI, AR, Zx, K.heap, Cx, Ax, Lst, D, a', σ, B.j, B.user⟩⟩

/-- **The bundle at a joint-invariant entry state** (line slj2): `JAtZ` with the action resume
and its cores numbered `0 .. n-1` give `SlJAt` for the layout read off that state,
`layoutJ Zx H (L.ksb s) n`. P3 gives all three at every `JReachU17` state
(P2/SlJReach.lean: `kernel_entry_reachU17V`, `SInvX.cr`, `JKern.csN`). -/
theorem SlJAt.of_JAtZ {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : Fl4Proofs.P3.XSets} {H : Heap} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
    {σ : Fl4Spec.State Unit} (J : Fl4Proofs.P3.JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a' σ)
    (hres : σ.schedulerAction = .resumeCurThread) {n : Nat} (hn : ∀ c : U64, c ∈ Cx ↔ c.val < n) :
    SlJAt (L := L) (layoutJ Zx H (L.ksb s) n) s :=
  ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, ⟨J, rfl, hn, hres⟩⟩

end

/-! ## The local path -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}
variable {A : Type}
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **The syscall entry beside the gate as a local path, from P3's joint invariant**
(module docstring): `sl_localPath` with the sets by the P1 convention (`T = H.tcbs`, …, `U =
K.user`, `H = K.heap`), `SlSets`, `hK`, `hU`, `hX`, `hUu`, `SlHereJ.ksb` / `cpu` and `SlAccK.jz`
derived from the bundle `SlJAt` [J] at every entry state (`hJ`) and at an anchor state (`hKJ`: the
state the layout is read off, the last serial exit, P2/SerExit.lean; any entry state serves).
`SlEntJ.dsR` / `hep` likewise (`SlJAtZ.dsR`, `SlJAtZ.hep`).
Remaining: `hpz` [P]/[W], `hSt` [P], `hA`, `a0`, `hm` [P], `hPE` (`SlPreB`), `hEr` (`SlEntR`:
`hrp` [J], `lep`, `lrp` [P]), `hHr` (`SlHereR`: `ep` [J]), `hAr` (`SlAccR`: `frl` [P]), `huf` [J].
Line slj2 derived `SlHereJ.cs` / `csc` (`SlJAtZ.cscFacts`), `SlAccK.pool` (`SlJAtZ.pool`) and the
former bundle fields `ksO` (`SlJAtZ.ksO`), `asid` (`SlJAtZ.asid`). -/
noncomputable def sl_localPathJ (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (hKJ : ∃ s0, SlJAt (L := L) K s0)
    {P : S → Prop}
    (hJ : ∀ s, P s → SlJAt (L := L) K s)
    (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEr : ∀ s, P s → SlEntR (st := st) K Locks found s)
    (hHr : ∀ s, P s → SlHereR (st := st) K found s)
    (hAr : ∀ s, P s → SlAccR (st := st) ar K Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) P
        (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  sl_localPath ar hSt hA (hKJ.choose_spec.regionOK) (hKJ.choose_spec.regionOKX) (hKJ.choose_spec.userOK) hm
    (slSets_conv K) (fun _ h => h) a0 hPE (fun s hP => (hJ s hP).entJ (hPE s hP).hN (hEr s hP)) (fun s hP => (hJ s hP).hereJ (hHr s hP))
    (fun s hP => (hJ s hP).accK (hAr s hP)) huf hpz

end

end Fl4Proofs.P2.PathObl

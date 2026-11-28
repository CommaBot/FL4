/-
P1 (aarch64, gen 60): **`UtZeroA` along the cap steps, and `ValidUntypedA ∧ UtZeroA` through the CNode decode
tops**; with MdbCovC's `CoverA` tops, the whole carried bundle `StA` (`MdbST ∧ UtRev ∧ ValidUntypedA ∧ UtZeroA ∧
CoverA`) through CNode Copy / Mint / Move / Mutate / Rotate.

* **Cap steps** (`swap`, `cap_swap_for_delete`, `move_cap`, `insert_with_cap`): MdbVU's `ubF` forms (every `OS` slot
  after holds a cap `UB` an `OS` slot's cap before, `UBm`, and the step writes only cap-slot words: MdbStepF's
  `swap.lrWF`, MdbMove's `move_cap.lrF`, `insert_with_cap.lrF`), then `UtZeroA.capw` (MdbUZ): **`cdt.swap.uz`**,
  **`cdt.cap_swap_for_delete.uz`**, **`cdt.move_cap.uz`**, **`cdt.insert_with_cap.uz`**.
* **`UE d c`** (`d` untyped ⇒ `d = c`; `UE.ub`: then `UB d c`): `mask_cap_rights`, `update_cap_data`,
  `derive_cap` return an `Untyped` argument unchanged and never make one (`.ue`, from the `.ua` forms for the other
  kinds); **`cnode.copied_cap.ue`** / **`ueM`** — MdbTreeD's `copied_cap.uaG` / MdbTreeC's `copied_cap.uaMG` (gen 60's
  relation-generic forms of `copied_cap.ua` / `uaM`) at `UE`. This is the `UB` form of `copied_cap.ua` gen 58 owed.
* **`set_thread_state`** (the decode's restart): `UtZeroA.stt` — its two words are the current TCB's `STATE` word
  (inside a heap TCB, off every RAM free part by `ValidUntypedA`) and the core's `SCHED_ACTION` node word (case
  hypothesis **`hnS`**, `NodeOffA`: off every RAM untyped's free part — the node statics lie outside RAM untypeds,
  P3 `RegionOffNodes`; the same kind of fact as gen 59's `hnF`).
* Decode steps `cnode.decode_copy.mvVZ` / `insVZ`, `cnode.decode_rotate.swVZ` / `mvVZ` (`CpMv` / `CpIns` / `RtSw` /
  `RtMv` for `ValidUntypedA H ∧ UtZeroA`), top **`cnode.decode.cnode_vz`**, and the
  bundle tops **`cnode.decode.cnode_stA`** / **`syscall.decode_invocation.cnode_stA`** (`StA H` before ⇒
  after; the decode does not change the heap).
* (gen 62) **One traversal for any invariant**: `MvStep` / `InsStep` / `SwStep` / `RsStep` (a cap step from any
  `MdbS` state, the restart), the generic decode steps `cnode.decode_copy.mvQ` / `insQ`,
  `cnode.decode_rotate.swQ` / `mvQ` and the top **`cnode.decode.cnodeQ`**; gen 60's `mvVZ` / `insVZ` / `swVZ` /
  `mvVZ` and `cnode_vz` are instances (proofs in place; `vzW`, `vzR`, `*.vzS`).

No named premise. New case hypothesis `hnS` (node word, above); the others are MdbCovC's and gen 52's.
-/
import Fl4ProofsA64.P1.MdbCovC
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {Sg : Set U64}
variable {H : Heap} {Cs Rp Nt : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

/-! ## The cap steps -/

/-- **`swap`** keeps `UtZeroA` (caps `UB` the replaced ones). -/
theorem cdt.swap.uz (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S} (h : UtZeroA st OS s)
    (hV : ValidUntypedA st H OS s) (hS : MdbS st OS s) {x1 x2 : U64} {c1 c2 : capability.Cap} (hx1 : x1 ∈ OS)
    (hx2 : x2 ∈ OS) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2)
    (hw1 : CapRt.EncWf c1) (hw2 : CapRt.EncWf c2) (hb1 : UB c1 (capA st s x1)) (hb2 : UB c2 (capA st s x2)) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => UtZeroA st OS s' ⦄ :=
  WP.spec_mono (cdt.swap.ubF hO hS hx1 hx2 hne hs1 hs2 hw1 hw2 hb1 hb2) fun _ h' => h.capw hH hV h'.1 h'.2

/-- **`cap_swap_for_delete`** of two canonical `OS` slots keeps `UtZeroA`. -/
theorem cdt.cap_swap_for_delete.uz (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S}
    (h : UtZeroA st OS s) (hV : ValidUntypedA st H OS s) (hS : MdbS st OS s) {x1 x2 : U64} (hx1 : x1 ∈ OS)
    (hx2 : x2 ∈ OS) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2) :
    cdt.cap_swap_for_delete st s x1 x2 ⦃ s' => UtZeroA st OS s' ⦄ := by
  unfold cdt.cap_swap_for_delete
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  · rename_i hne'
    have hne : x1 ≠ x2 := by simpa using hne'
    rw [capA_eq, bind_ok, capA_eq, bind_ok]
    exact cdt.swap.uz hH hO h hV hS hx1 hx2 hne hs1 hs2 (CapRt.decodeF_encWf _ _) (CapRt.decodeF_encWf _ _)
      (UB.refl _) (UB.refl _)

/-- **`move_cap`** keeps `UtZeroA` (the moved cap `UB` the source's). -/
theorem cdt.move_cap.uz (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S} (h : UtZeroA st OS s)
    (hV : ValidUntypedA st H OS s) (hS : MdbS st OS s) {src dest : U64} {nc : capability.Cap} (hsrc : src ∈ OS)
    (hd : dest ∈ OS) (hsd : src ≠ dest) (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc)
    (hb : UB nc (capA st s src)) :
    cdt.move_cap st s nc src dest ⦃ s' => UtZeroA st OS s' ⦄ :=
  WP.spec_mono (cdt.move_cap.ubF hO hS hsrc hd hsd hdc hw hb) fun _ h' => h.capw hH hV h'.1 h'.2

/-- **`insert_with_cap`** keeps `UtZeroA` (the new cap `UB` the source's, the source made full at most). -/
theorem cdt.insert_with_cap.uz (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S} (h : UtZeroA st OS s)
    (hV : ValidUntypedA st H OS s) (hS : MdbS st OS s) {src dest : U64} {nc sc : capability.Cap}
    (hsrc : src ∈ OS) (hd : dest ∈ OS) (hsd : src ≠ dest) (hdc : obj.sext48 dest = ok dest)
    (hsc : capA st s src = sc) (hsc0 : sc ≠ .Null) (hw : CapRt.EncWf nc) (hb : UB nc sc)
    (hfib : ∀ p b i e, sc = .Untyped p b i e → i.val ≤ 2 ^ b.val) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => UtZeroA st OS s' ⦄ :=
  WP.spec_mono (cdt.insert_with_cap.ubF hO hS hsrc hd hsd hdc hsc hsc0 hw hb hfib) fun _ h' =>
    h.capw hH hV h'.1 h'.2

/-! ## Untyped caps pass the decode's cap functions unchanged -/

/-- **`d`, if untyped, is `c`** (module docstring). -/
def UE (d c : capability.Cap) : Prop := isUtA d = true → d = c

theorem UE.refl (c : capability.Cap) : UE c c := fun _ => rfl

theorem UE.trans {a b c : capability.Cap} (h1 : UE a b) (h2 : UE b c) : UE a c := fun h => by
  have e := h1 h
  exact e.trans (h2 (e ▸ h))

theorem UE.ub {d c : capability.Cap} (h : UE d c) : UB d c := fun p b i e =>
  ⟨i, (h (by simp [e, isUtA])).symm.trans e, le_refl _⟩

theorem ut_cases {c : capability.Cap} (hc : isUtA c = true) : ∃ p b i d, c = .Untyped p b i d := by
  cases c <;> first | exact ⟨_, _, _, _, rfl⟩ | simp [isUtA] at hc

theorem UN.ue {m c : capability.Cap} (h : UN m c) (hc : isUtA c ≠ true) : UE m c := fun hm => by
  rcases h with rfl | ⟨hua, -⟩
  · simp [isUtA] at hm
  · exact absurd (hua.isut ▸ hm) hc

theorem capability.mask_cap_rights.ue (r : capability.Rights) (c : capability.Cap) :
    capability.mask_cap_rights r c ⦃ m => UE m c ⦄ := by
  by_cases hc : isUtA c = true
  · obtain ⟨p, b, i, d, rfl⟩ := ut_cases hc
    simp only [capability.mask_cap_rights]
    exact (WP.spec_ok _).2 (UE.refl _)
  · exact WP.spec_mono (capability.mask_cap_rights.ua r c) fun m hm => hm.ue hc

theorem objects.update_cap_data.ue (pr : Bool) (data : U64) (c : capability.Cap) :
    objects.update_cap_data pr data c ⦃ m => UE m c ⦄ := by
  by_cases hc : isUtA c = true
  · obtain ⟨p, b, i, d, rfl⟩ := ut_cases hc
    simp only [objects.update_cap_data]
    exact (WP.spec_ok _).2 (UE.refl _)
  · exact WP.spec_mono (objects.update_cap_data.ua pr data c) fun m hm => hm.ue hc

set_option maxHeartbeats 1000000 in
theorem objects.derive_cap.ue (s : S) (slot : U64) (c : capability.Cap) :
    objects.derive_cap st s slot c ⦃ r => ∀ nc, r = .Ok nc → UE nc c ⦄ := by
  have hS : P0.StoreTotal st := L.total
  by_cases hc : isUtA c = true
  · obtain ⟨p, b, i, d, rfl⟩ := ut_cases hc
    simp only [objects.derive_cap]
    refine WP.spec_bind (P0.cdt.ensure_no_children.p0 st s slot hS) fun r _ => ?_
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine (WP.spec_ok _).2 fun nc h => ?_
      cases h
      exact UE.refl _
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      first
      | exact (WP.spec_ok _).2 fun nc h => (by cases h)
      | (simp only [WP.spec_ok]; intro nc h; cases h)
  · exact WP.spec_mono (objects.derive_cap.ua s slot c) fun r hr nc e => (hr nc e).ue hc

set_option maxHeartbeats 1000000 in
/-- **CNode Copy / Mint return an untyped source unchanged** (`copied_cap.uaG` at `UE`). -/
theorem cnode.copied_cap.ue (s : S) (lbl length buf src : U64) (src_cap : capability.Cap) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc, r = .Ok (nc, false) → UE nc src_cap ⦄ :=
  cnode.copied_cap.uaG (R := UE) (fun h1 h2 => UE.trans h1 h2) (fun r c => capability.mask_cap_rights.ue r c)
    (fun pr d c => objects.update_cap_data.ue pr d c) (fun s sl c => objects.derive_cap.ue s sl c) s lbl length buf src
    src_cap

set_option maxHeartbeats 1000000 in
/-- **CNode Move / Mutate return an untyped source unchanged** (`copied_cap.uaMG` at `UE`). -/
theorem cnode.copied_cap.ueM (s : S) (lbl length buf src : U64) (src_cap : capability.Cap)
    (hl : lbl = fl4_abi.label.CNodeMove ∨ lbl = fl4_abi.label.CNodeMutate) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc b, r = .Ok (nc, b) → UE nc src_cap ⦄ :=
  cnode.copied_cap.uaMG (R := UE) UE.refl (fun pr d c => objects.update_cap_data.ue pr d c) s lbl length buf src
    src_cap hl

/-! ## The decode's restart -/

/-- **A word off every RAM untyped's free part** (the `SCHED_ACTION` node word: module docstring). -/
def NodeOffA (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) (w : U64) : Prop :=
  ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false → w.val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ w.val

/-- **`set_thread_state`'s two words keep `UtZeroA`** (module docstring). -/
theorem UtZeroA.stt (hH : HeapOK H) {s s2 : S} (hV : ValidUntypedA st H OS s) (h : UtZeroA st OS s) {t : U64}
    (ht : t ∈ H.tcbs) (hnS : NodeOffA st OS s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (k : OSKeep st OS s s2)
    (w : WritesIn st s s2 (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) :
    UtZeroA st OS s2 := by
  refine h.writes w (fun y0 hy0 p b i hcy x hx => ?_) fun y hy => ⟨y, hy, by rw [k.capA hy]; exact UB.refl _⟩
  rcases hx with rfl | rfl
  · have ht' : H t = some .tcb := ht
    have hf := hH.fits t _ ht'
    have g := hV y0 hy0 p b i hcy t .tcb ht'
    simp only [HKind.bits] at hf g
    rw [stA_eq, wa_val]
    have e : (3328#u64 : U64).val = 3328 := by simp
    rw [e]
    rcases g with g | g
    · left; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · right; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · exact hnS y0 hy0 p b i hcy

/-! ## The `ValidUntypedA ∧ UtZeroA` steps of the decode traversals -/

/-- The free index bound of an `MdbST` state's untyped slots (`UtInvA.fib`). -/
theorem MdbST.fib {s : S} (hm : MdbST st OS s) {x : U64} (hx : x ∈ OS) :
    ∀ p b i e, capA st s x = .Untyped p b i e → i.val ≤ 2 ^ b.val := fun p b i e hc =>
  hm.tu.elim fun _ h => h.elim fun _ hT => hT.ut.fib x hx p b i e hc

/-! ## The decode traversals' steps for any invariant (gen 62) -/

/-- (gen 62) **A `move_cap` step for an invariant `P`**: from any state with `MdbS` and `P`, moving a cap `UB` and
`AlikeA` the source's into another canonical slot keeps `P`. -/
def MvStep (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (P : S → Prop) : Prop :=
  ∀ (a : S) (nc : capability.Cap) (x y : U64), MdbS st OS a → P a → x ∈ OS → y ∈ OS → x ≠ y →
    obj.sext48 y = ok y → CapRt.EncWf nc → UB nc (capA st a x) → AlikeA nc (capA st a x) →
    cdt.move_cap st a nc x y ⦃ s' => P s' ⦄

/-- (gen 62) **An `insert_with_cap` step for an invariant `P`** (the new cap also no `Zombie`, `NZA`). -/
def InsStep (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (P : S → Prop) : Prop :=
  ∀ (a : S) (nc sc : capability.Cap) (x y : U64), MdbS st OS a → P a → x ∈ OS → y ∈ OS → x ≠ y →
    obj.sext48 y = ok y → capA st a x = sc → sc ≠ .Null → CapRt.EncWf nc → UB nc sc → AlikeA nc sc → NZA nc →
    (∀ p b i e, sc = .Untyped p b i e → i.val ≤ 2 ^ b.val) →
    cdt.insert_with_cap st a nc sc x y ⦃ s' => P s' ⦄

/-- (gen 62) **A `swap` step for an invariant `P`.** -/
def SwStep (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (P : S → Prop) : Prop :=
  ∀ (a : S) (c1 c2 : capability.Cap) (x1 x2 : U64), MdbS st OS a → P a → x1 ∈ OS → x2 ∈ OS → x1 ≠ x2 →
    obj.sext48 x1 = ok x1 → obj.sext48 x2 = ok x2 → CapRt.EncWf c1 → CapRt.EncWf c2 →
    UB c1 (capA st a x1) → UB c2 (capA st a x2) → AlikeA c1 (capA st a x1) → AlikeA c2 (capA st a x2) →
    cdt.swap st a c1 x1 c2 x2 ⦃ s' => P s' ⦄

/-- (gen 62) **The decode's restart for an invariant `P`**: `P` after `set_thread_state` (`OSKeep`, its two words). -/
def RsStep (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) (P : S → Prop) : Prop :=
  ∀ s2 : S, OSKeep st OS s s2 →
    WritesIn st s s2 (fun b => b = stA (L.curW s) ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) → P s2

/-- (gen 62) **CNode Move / Mutate's `move_cap` step for any `P`** (gen 60's `mvVZ`, the invariant abstracted). -/
theorem cnode.decode_copy.mvQ {s : S} (hm : MdbST st OS s) {P : S → Prop} (h2 : RsStep st OS s P)
    (hmv : MvStep st OS P) {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest) :
    CpMv st OS s lbl len buf dest P := by
  intro s2 v nc k2 w2 hv hs0 hd0 he hn0
  have hwf : CapRt.EncWf (capA st s v) := CapRt.decodeF_encWf _ _
  have hlm := cnode.copied_cap.lblT hl4 hwf he
  have h2' := cnode.copied_cap.mv (st := st) s lbl len buf v (capA st s v) hlm hwf
  have hu2 := cnode.copied_cap.ueM (st := st) s lbl len buf v (capA st s v) hlm
  rw [he, WP.spec_ok] at h2' hu2
  have hsd : v ≠ dest := fun e => hs0 (by rw [e]; exact hd0)
  exact hmv s2 nc v dest (hm.mdbS.keep k2) (h2 s2 k2 w2) hv hd hsd hdc (h2' nc true rfl).2.2
    (by rw [k2.capA hv]; exact (hu2 nc true rfl).ub) (by rw [k2.capA hv]; exact (h2' nc true rfl).2.1.ne hn0)

/-- (gen 62) **CNode Copy / Mint's `insert_with_cap` step for any `P`** (gen 60's `insVZ` abstracted). -/
theorem cnode.decode_copy.insQ {s : S} (hm : MdbST st OS s) {P : S → Prop} (h2 : RsStep st OS s P)
    (hins : InsStep st OS P) {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest) :
    CpIns st OS s lbl len buf dest P := by
  intro s2 v nc k2 w2 hv hs0 hd0 he hn0
  have hwf : CapRt.EncWf (capA st s v) := CapRt.decodeF_encWf _ _
  have hw2 := cnode.copied_cap.wf (st := st) s lbl len buf v (capA st s v)
    (cnode.copied_cap.lblF hl4 hwf he) hwf
  have hu2 := cnode.copied_cap.ue (st := st) s lbl len buf v (capA st s v)
  have ha2 := cnode.copied_cap.al (st := st) s lbl len buf v (capA st s v)
  have hz2 := cnode.copied_cap.nz (st := st) s lbl len buf v (capA st s v)
  rw [he, WP.spec_ok] at hw2 hu2 ha2 hz2
  have hsd : v ≠ dest := fun e => hs0 (by rw [e]; exact hd0)
  exact hins s2 nc (capA st s v) v dest (hm.mdbS.keep k2) (h2 s2 k2 w2) hv hd hsd hdc (k2.capA hv) hs0
    (hw2 nc false rfl).2 (hu2 nc rfl).ub ((ha2 nc rfl).ne hn0) (hz2 nc rfl) (hm.fib hv)

/-- (gen 62) **CNode Rotate's `swap` step for any `P`** (gen 60's `swVZ` abstracted). -/
theorem cnode.decode_rotate.swQ (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega) {s : S}
    (hm : MdbST st OS s) {P : S → Prop} (h3 : RsStep st OS s P) (hsw : SwStep st OS P) {dest : U64} :
    RtSw st OS s dest P := by
  intro s3 src pv sd pd ns np k3 w3 hsrc hpv hps hpd hs0 hp0 hsd e1 e2 hns hnp
  have hus := objects.update_cap_data.ue true sd (capA st s src)
  have hwns := objects.update_cap_data.wf true sd (capA st s src) (CapRt.decodeF_encWf _ _)
  have has := objects.update_cap_data.al true sd (capA st s src)
  have hup := objects.update_cap_data.ue true pd (capA st s pv)
  have hwnp := objects.update_cap_data.wf true pd (capA st s pv) (CapRt.decodeF_encWf _ _)
  have hap := objects.update_cap_data.al true pd (capA st s pv)
  rw [e1, WP.spec_ok] at hus hwns has
  rw [e2, WP.spec_ok] at hup hwnp hap
  exact hsw s3 ns np src pv (hm.mdbS.keep k3) (h3 s3 k3 w3) hsrc hpv (Ne.symm hps) (hO.canon hW hsrc)
    (hO.canon hW hpv) hwns hwnp (by rw [k3.capA hsrc]; exact hus.ub) (by rw [k3.capA hpv]; exact hup.ub)
    (by rw [k3.capA hsrc]; exact has.ne hns) (by rw [k3.capA hpv]; exact hap.ne hnp)

/-- (gen 62) **CNode Rotate's two `move_cap` steps for any `P`** (gen 60's `mvVZ` abstracted; the first move's
`MdbS` from `cdt.move_cap.mdbS`, the source's cap from `cdt.move_cap.lr`). -/
theorem cnode.decode_rotate.mvQ (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega) {s : S}
    (hm : MdbST st OS s) {P : S → Prop} (h3 : RsStep st OS s P) (hmv : MvStep st OS P) {dest : U64}
    (hd : dest ∈ OS) :
    RtMv st OS s dest P := by
  intro s3 src pv sd pd ns np k3 w3 hsrc hpv hps hpd hs0 hp0 hsd hd0 e1 e2 hns hnp
  have hc3 : ∀ y ∈ OS, capA st s3 y = capA st s y := fun y hy => k3.capA hy
  have hus := objects.update_cap_data.ue true sd (capA st s src)
  have hwns := objects.update_cap_data.wf true sd (capA st s src) (CapRt.decodeF_encWf _ _)
  have has := objects.update_cap_data.al true sd (capA st s src)
  have hapl := objects.update_cap_data.al true pd (capA st s pv)
  have hup := objects.update_cap_data.ue true pd (capA st s pv)
  have hwnp := objects.update_cap_data.wf true pd (capA st s pv) (CapRt.decodeF_encWf _ _)
  rw [e1, WP.spec_ok] at hus hwns has
  rw [e2, WP.spec_ok] at hapl hup hwnp
  have m3 := hm.mdbS.keep k3
  obtain ⟨G, hM, -, -, -, -⟩ := id m3
  have F := hM.lkF hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have gp : pv ∈ G.flatten := (hM.members pv).2 ⟨hpv, by rw [hc3 pv hpv]; exact hp0⟩
  refine WP.spec_mono (WP.spec_and (WP.spec_and
    (cdt.move_cap.mdbS hO m3 hpv (by rw [hc3 pv hpv]; exact hp0) hd (by rw [hc3 dest hd]; exact hd0)
      (hO.canon hW hd) hwnp hnp (by rw [hc3 pv hpv]; exact hapl.ne hnp))
    (hmv s3 np pv dest m3 (h3 s3 k3 w3) hpv hd hpd (hO.canon hW hd) hwnp (by rw [hc3 pv hpv]; exact hup.ub)
      (by rw [hc3 pv hpv]; exact hapl.ne hnp)))
    (cdt.move_cap.lr hO (LR.self s3) hpv hd hpd (hO.canon hW hd) hwnp
      (fun h => inOS _ (F.pvm _ gp h)) (fun h => inOS _ (F.nxm _ gp h)))) fun s4 h4 => ?_
  obtain ⟨⟨m4, p4⟩, -, -, -, e4k⟩ := h4
  have c4s : capA st s4 src = capA st s src := by rw [e4k src hsrc hps.symm hsd, hc3 src hsrc]
  exact hmv s4 ns src pv m4 p4 hsrc hpv (Ne.symm hps) (hO.canon hW hpv) hwns (by rw [c4s]; exact hus.ub)
    (by rw [c4s]; exact has.ne hns)

set_option maxHeartbeats 1000000 in
/-- (gen 62) **`cnode.decode` at CNode Copy / Mint / Move / Mutate / Rotate keeps any invariant `P` with the four
steps** (the one `cnodeG` instance of the CNode decode tops: gen 60's `cnode_vz` and gen 62's `cnode_ubm` /
`cnode_zf` are instances). -/
theorem cnode.decode.cnodeQ {A : Type _} {ar : machine.Arch A}
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s)
    (hm : MdbST st OS s) {P : S → Prop} (h0 : P s) (h2 : RsStep st OS s P) (hmv : MvStep st OS P)
    (hins : InsStep st OS P) (hsw : SwStep st OS P)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => P s' ⦄ :=
  cnode.decode.cnodeG (P := P) h0 a hl c (lookup_tgt_in hT c hc)
    (fun hl4 _ hd => cnode.decode_copy.gen hO q (P := P) h0
      (fun sl hsl hs0 i d => lookup_src_in hT _ (RootOK.of_slot hT (hx sl hsl hs0) (capA_eq s sl)) i d)
      (cnode.decode_copy.mvQ hm h2 hmv hl4 hd (hO.canon hW hd))
      (cnode.decode_copy.insQ hm h2 hins hl4 hd (hO.canon hW hd)))
    fun _ hd => cnode.decode_rotate.gen hO q hT (P := P) h0 hx (cnode.decode_rotate.swQ hO hW hm h2 hsw)
      (cnode.decode_rotate.mvQ hO hW hm h2 hmv hd)

/-- (gen 62) **`ValidUntypedA H ∧ UtZeroA` across a cap-slot write with a `UBm` cap map.** -/
theorem vzW (hH : HeapOK H) {s s' : S} (h : ValidUntypedA st H OS s ∧ UtZeroA st OS s)
    (hw : WritesIn st s s' (W7.CapW H.tcbs H.omega Sg)) (hu : UBm st OS s s') :
    ValidUntypedA st H OS s' ∧ UtZeroA st OS s' :=
  ⟨h.1.of_ub (fun _ _ e => e) hu, h.2.capw hH h.1 hw hu⟩

theorem cdt.move_cap.vzS (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) :
    MvStep st OS fun x => ValidUntypedA st H OS x ∧ UtZeroA st OS x :=
  fun _ _ _ _ hma hq hx hy hxy hyc hw hb _ =>
    WP.spec_mono (cdt.move_cap.ubF hO hma hx hy hxy hyc hw hb) fun _ h' => vzW hH hq h'.1 h'.2

theorem cdt.insert_with_cap.vzS (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) :
    InsStep st OS fun x => ValidUntypedA st H OS x ∧ UtZeroA st OS x :=
  fun _ _ _ _ _ hma hq hx hy hxy hyc hsc hsc0 hw hb _ _ hfib =>
    WP.spec_mono (cdt.insert_with_cap.ubF hO hma hx hy hxy hyc hsc hsc0 hw hb hfib) fun _ h' => vzW hH hq h'.1 h'.2

theorem cdt.swap.vzS (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) :
    SwStep st OS fun x => ValidUntypedA st H OS x ∧ UtZeroA st OS x :=
  fun _ _ _ _ _ hma hq hx1 hx2 hne hs1 hs2 hw1 hw2 hb1 hb2 _ _ =>
    WP.spec_mono (cdt.swap.ubF hO hma hx1 hx2 hne hs1 hs2 hw1 hw2 hb1 hb2) fun _ h' => vzW hH hq h'.1 h'.2

theorem vzR (hH : HeapOK H) {s : S} (hV : ValidUntypedA st H OS s) (hZ : UtZeroA st OS s)
    (hcur : L.curW s ∈ H.tcbs) (hnS : NodeOffA st OS s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) :
    RsStep st OS s fun x => ValidUntypedA st H OS x ∧ UtZeroA st OS x :=
  fun _ k w => ⟨hV.keepO k, UtZeroA.stt hH hV hZ hcur hnS k w⟩

/-- **`ValidUntypedA ∧ UtZeroA`'s `move_cap` step** of CNode Move / Mutate. -/
theorem cnode.decode_copy.mvVZ (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S} (hm : MdbST st OS s)
    (hV : ValidUntypedA st H OS s) (hZ : UtZeroA st OS s) (hcur : L.curW s ∈ H.tcbs)
    (hnS : NodeOffA st OS s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest) :
    CpMv st OS s lbl len buf dest fun x => ValidUntypedA st H OS x ∧ UtZeroA st OS x :=
  cnode.decode_copy.mvQ hm (vzR hH hV hZ hcur hnS) (cdt.move_cap.vzS hH hO) hl4 hd hdc

/-- **`ValidUntypedA ∧ UtZeroA`'s `insert_with_cap` step** of CNode Copy / Mint. -/
theorem cnode.decode_copy.insVZ (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {s : S} (hm : MdbST st OS s)
    (hV : ValidUntypedA st H OS s) (hZ : UtZeroA st OS s) (hcur : L.curW s ∈ H.tcbs)
    (hnS : NodeOffA st OS s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest) :
    CpIns st OS s lbl len buf dest fun x => ValidUntypedA st H OS x ∧ UtZeroA st OS x :=
  cnode.decode_copy.insQ hm (vzR hH hV hZ hcur hnS) (cdt.insert_with_cap.vzS hH hO) hl4 hd hdc

/-- **`ValidUntypedA ∧ UtZeroA`'s `swap` step** of CNode Rotate. -/
theorem cnode.decode_rotate.swVZ (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {s : S} (hm : MdbST st OS s) (hV : ValidUntypedA st H OS s) (hZ : UtZeroA st OS s) (hcur : L.curW s ∈ H.tcbs)
    (hnS : NodeOffA st OS s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) {dest : U64} :
    RtSw st OS s dest fun x => ValidUntypedA st H OS x ∧ UtZeroA st OS x :=
  cnode.decode_rotate.swQ hO hW hm (vzR hH hV hZ hcur hnS) (cdt.swap.vzS hH hO)

/-- **`ValidUntypedA ∧ UtZeroA`'s two `move_cap` steps** of CNode Rotate (the first one's `MdbS` and caps from
`cdt.move_cap.mdbS` / `cdt.move_cap.lr`). -/
theorem cnode.decode_rotate.mvVZ (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {s : S} (hm : MdbST st OS s) (hV : ValidUntypedA st H OS s) (hZ : UtZeroA st OS s) (hcur : L.curW s ∈ H.tcbs)
    (hnS : NodeOffA st OS s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) {dest : U64} (hd : dest ∈ OS) :
    RtMv st OS s dest fun x => ValidUntypedA st H OS x ∧ UtZeroA st OS x :=
  cnode.decode_rotate.mvQ hO hW hm (vzR hH hV hZ hcur hnS) (cdt.move_cap.vzS hH hO) hd

/-! ## The decode tops -/

set_option maxHeartbeats 1000000 in
/-- **`cnode.decode` at CNode Copy / Mint / Move / Mutate / Rotate keeps `ValidUntypedA H ∧ UtZeroA`** (module
docstring). -/
theorem cnode.decode.cnode_vz {A : Type _} {ar : machine.Arch A} (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s)
    (hm : MdbST st OS s) (hV : ValidUntypedA st H OS s) (hZ : UtZeroA st OS s)
    (hnS : NodeOffA st OS s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => ValidUntypedA st H OS s' ∧ UtZeroA st OS s' ⦄ :=
  cnode.decode.cnodeQ hO hW q hT hm ⟨hV, hZ⟩ (vzR hH hV hZ q.curT hnS) (cdt.move_cap.vzS hH hO)
    (cdt.insert_with_cap.vzS hH hO) (cdt.swap.vzS hH hO) a hl c hc hx

/-- **`cnode.decode` at CNode Copy / Mint / Move / Mutate / Rotate keeps the carried bundle `StA H`** (MdbCovC's
`cnode_mdbSTRC` and `cnode_vz`). -/
theorem cnode.decode.cnode_stA {A : Type _} {ar : machine.Arch A} (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s)
    (hSt : StA st H OS s) (hnS : NodeOffA st OS s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hh : Held st OS s c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => StA st H OS s' ⦄ := by
  obtain ⟨hS, hR, hV, hZ, hC⟩ := hSt
  exact WP.spec_mono (WP.spec_and (cnode.decode.cnode_mdbSTRC hO hW q hT ⟨hS, hR, hC⟩ a hl c hc hh hx)
    (cnode.decode.cnode_vz hH hO hW q hT hS hV hZ hnS a hl c hc hx))
    fun ⟨_, _, _⟩ ⟨⟨h1, h2, h3⟩, h4, h5⟩ => ⟨h1, h2, h4, h5, h3⟩

/-- **CNode Copy / Mint / Move / Mutate / Rotate at `decode_invocation`** of a CNode cap read from an `OS` slot keep
`StA H`. -/
theorem syscall.decode_invocation.cnode_stA {A : Type _} {ar : machine.Arch A} (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s)
    (hSt : StA st H OS s) (hnS : NodeOffA st OS s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (a : A) {lbl : U64} (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ => StA st H OS s' ⦄ :=
  syscall.decode_invocation.cnodeG (P := StA st H OS) hSt a len slot cap blk call don fp buf extra hf
    (cnode.decode.cnode_stA hH hO hW q hT hSt hnS a hl cap (RootOK.of_slot hT hslot hcap)
      ⟨slot, hslot, okinj ((capA_eq s slot).symm.trans hcap)⟩ hx)

end ST
end R
end W7

end

end Fl4ProofsA64.P1

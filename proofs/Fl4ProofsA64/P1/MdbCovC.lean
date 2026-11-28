/-
P1 (aarch64, gen 60): **`CoverA` through the CNode decode tops** — CNode Copy / Mint / Move / Mutate / Rotate at
`cnode.decode` / `decode_invocation` keep `MdbS ∧ CoverA`, and with gen 57's `cnode_mdbSTR` the bundle
`MdbST ∧ UtRev ∧ CoverA` (l4v `cap_insert` / `cap_move` / `cap_swap` keep `if_unsafe_then_cap`).

All five go through the one decode traversal of each shape (MdbCopyD's `cnode.decode_copy.gen`, MdbRot's
`cnode.decode_rotate.gen`, the dispatch `cnode.decode.cnodeG` / `syscall.decode_invocation.cnodeG`); here only the
`CoverA` steps are new:

* **`CovBy.ua`**: a cap `UA` another covers what it covers (same physical / untyped bits, base, top).
* **`cnode.decode_copy.mvC`** / **`insC`** (`CpMv` / `CpIns` for `CoverA`): MdbCov's `cdt.move_cap.covG` /
  `cdt.insert_with_cap.cov`, the new cap `UN` the source's (`cnode.copied_cap.uaM` / `.ua`), the destination covered
  at the start (`hcd`).
* **`cnode.decode_rotate.swC`** (`RtSw`): `cdt.swap.covG`, both slots non-null, so covered by `CoverA` itself;
  **`mvC`** (`RtMv` for `MdbS ∧ CoverA`): the pivot into `dest` (`dest` covered at the start), then the source into
  the emptied pivot slot — covered after the first move by the cap that covered it before, which is either unchanged
  or (if the pivot covered itself) now in `dest` (`update_cap_data.ua`).
* Tops **`cnode.decode.cnode_cov`** / **`syscall.decode_invocation.cnode_cov`** (`MdbS ∧ CoverA`; the destination's
  cover from MdbCovL's `lookup_tgt_cov` and `SlotCov.cov`, the root `Held`: at `decode_invocation` the invoked cap is
  read from an `OS` slot) and **`cnode.decode.cnode_mdbSTRC`** / **`syscall.decode_invocation.cnode_mdbSTRC`**
  (`MdbST ∧ UtRev ∧ CoverA` before ⇒ after).

No named premise. Case hypotheses: gen 52's (`SlotTy`, `WinOK`, extra slots `0` or in `OS`), `Held` of the root at
the `cnode.decode` level.
-/
import Fl4ProofsA64.P1.MdbCovL
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}
variable {H : Heap} {Cs Rp Nt : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

theorem CovBy.ua {d c : capability.Cap} (h : UA d c) {y : U64} (hc : CovBy c y) : CovBy d y := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  exact ⟨by rw [h.phys]; exact h1, by rw [h.isut]; exact h2, by rw [h.base]; exact h3, by rw [h.top]; exact h4⟩

/-! ## The `CoverA` steps of the decode traversals -/

/-- **`CoverA`'s `move_cap` step** of CNode Move / Mutate (module docstring). -/
theorem cnode.decode_copy.mvC (hO : OSOK T Ω Sg OS) {s : S} (hm : MdbS st OS s) (hC : CoverA st OS s)
    {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest) (hcd : ∃ z ∈ OS, CovBy (capA st s z) dest) :
    CpMv st OS s lbl len buf dest (CoverA st OS) := by
  intro s2 v nc k2 _ hv hs0 hd0 he hn0
  have hc2 : ∀ y ∈ OS, capA st s2 y = capA st s y := fun y hy => by
    unfold capA; rw [(k2 y hy).1, (k2 y hy).2.1]
  have hwf : CapRt.EncWf (capA st s v) := CapRt.decodeF_encWf _ _
  have hmv := cnode.copied_cap.lblT hl4 hwf he
  have h2 := cnode.copied_cap.mv (st := st) s lbl len buf v (capA st s v) hmv hwf
  have hu2 := cnode.copied_cap.uaM (st := st) s lbl len buf v (capA st s v) hmv
  rw [he, WP.spec_ok] at h2 hu2
  have hwn := (h2 nc true rfl).2.2
  have hua := (hu2 nc true rfl).ne hn0
  have hsd : v ≠ dest := fun e => hs0 (by rw [e]; exact hd0)
  obtain ⟨z, hz, hcz⟩ := hcd
  exact cdt.move_cap.covG hO (hC.keepO k2) (hm.keep k2) hv hd hsd hdc (by rw [hc2 dest hd]; exact hd0) hwn
    (fun y hy => CovBy.ua hua (by rw [hc2 v hv] at hy; exact hy))
    (fun _ => ⟨z, hz, by rw [hc2 z hz]; exact hcz⟩)

/-- **`CoverA`'s `insert_with_cap` step** of CNode Copy / Mint (module docstring). -/
theorem cnode.decode_copy.insC (hO : OSOK T Ω Sg OS) {s : S} (hm : MdbS st OS s) (hC : CoverA st OS s)
    {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest) (hcd : ∃ z ∈ OS, CovBy (capA st s z) dest) :
    CpIns st OS s lbl len buf dest (CoverA st OS) := by
  intro s2 v nc k2 _ hv hs0 hd0 he hn0
  have hc2 : ∀ y ∈ OS, capA st s2 y = capA st s y := fun y hy => by
    unfold capA; rw [(k2 y hy).1, (k2 y hy).2.1]
  have hwf : CapRt.EncWf (capA st s v) := CapRt.decodeF_encWf _ _
  have hw2 := cnode.copied_cap.wf (st := st) s lbl len buf v (capA st s v)
    (cnode.copied_cap.lblF hl4 hwf he) hwf
  rw [he, WP.spec_ok] at hw2
  have hwn := (hw2 nc false rfl).2
  have hsd : v ≠ dest := fun e => hs0 (by rw [e]; exact hd0)
  obtain ⟨z, hz, hcz⟩ := hcd
  exact cdt.insert_with_cap.cov hO (hC.keepO k2) (hm.keep k2) hv hd hsd hdc (hc2 v hv) hs0 hwn
    (by rw [hc2 dest hd]; exact hd0) (fun _ => ⟨z, hz, by rw [hc2 z hz]; exact hcz⟩)

/-- **`CoverA`'s `swap` step** of CNode Rotate (module docstring). -/
theorem cnode.decode_rotate.swC (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω) {s : S} (hm : MdbS st OS s)
    (hC : CoverA st OS s) {dest : U64} : RtSw st OS s dest (CoverA st OS) := by
  intro s3 src pv sd pd ns np k3 _ hsrc hpv hps hpd hs0 hp0 hsd e1 e2 hns hnp
  have hc3 : ∀ y ∈ OS, capA st s3 y = capA st s y := fun y hy => by
    unfold capA; rw [(k3 y hy).1, (k3 y hy).2.1]
  have has := objects.update_cap_data.ua true sd (capA st s src)
  have hwns := objects.update_cap_data.wf true sd (capA st s src) (CapRt.decodeF_encWf _ _)
  have hap := objects.update_cap_data.ua true pd (capA st s pv)
  have hwnp := objects.update_cap_data.wf true pd (capA st s pv) (CapRt.decodeF_encWf _ _)
  rw [e1, WP.spec_ok] at has hwns
  rw [e2, WP.spec_ok] at hap hwnp
  have C3 := hC.keepO k3
  exact cdt.swap.covG hO C3 (hm.keep k3) hsrc hpv (Ne.symm hps) (hO.canon hW hsrc) (hO.canon hW hpv) hwns hwnp
    (fun y hy => CovBy.ua (has.ne hns) (by rw [hc3 src hsrc] at hy; exact hy))
    (fun y hy => CovBy.ua (hap.ne hnp) (by rw [hc3 pv hpv] at hy; exact hy))
    (fun _ => C3.cov hsrc (by rw [hc3 src hsrc]; exact hs0)) (fun _ => C3.cov hpv (by rw [hc3 pv hpv]; exact hp0))

/-- **`MdbS ∧ CoverA`'s two `move_cap` steps** of CNode Rotate (module docstring). -/
theorem cnode.decode_rotate.mvC (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω) {s : S} (hm : MdbS st OS s)
    (hC : CoverA st OS s) {dest : U64} (hd : dest ∈ OS) (hcd : ∃ z ∈ OS, CovBy (capA st s z) dest) :
    RtMv st OS s dest fun x => MdbS st OS x ∧ CoverA st OS x := by
  intro s3 src pv sd pd ns np k3 _ hsrc hpv hps hpd hs0 hp0 hsd hd0 e1 e2 hns hnp
  have hc3 : ∀ y ∈ OS, capA st s3 y = capA st s y := fun y hy => by
    unfold capA; rw [(k3 y hy).1, (k3 y hy).2.1]
  have hal := objects.update_cap_data.al true sd (capA st s src)
  have has := objects.update_cap_data.ua true sd (capA st s src)
  have hwns := objects.update_cap_data.wf true sd (capA st s src) (CapRt.decodeF_encWf _ _)
  have hapl := objects.update_cap_data.al true pd (capA st s pv)
  have hap := objects.update_cap_data.ua true pd (capA st s pv)
  have hwnp := objects.update_cap_data.wf true pd (capA st s pv) (CapRt.decodeF_encWf _ _)
  rw [e1, WP.spec_ok] at hal has hwns
  rw [e2, WP.spec_ok] at hapl hap hwnp
  have m3 := hm.keep k3
  have C3 := hC.keepO k3
  obtain ⟨G, hM, -, -, -, -⟩ := id m3
  have F := hM.lkF hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have gp : pv ∈ G.flatten := (hM.members pv).2 ⟨hpv, by rw [hc3 pv hpv]; exact hp0⟩
  obtain ⟨z, hz, hcz⟩ := hcd
  refine WP.spec_mono (WP.spec_and (WP.spec_and
    (cdt.move_cap.mdbS hO m3 hpv (by rw [hc3 pv hpv]; exact hp0) hd (by rw [hc3 dest hd]; exact hd0)
      (hO.canon hW hd) hwnp hnp (by rw [hc3 pv hpv]; exact hapl.ne hnp))
    (cdt.move_cap.covG hO C3 m3 hpv hd hpd (hO.canon hW hd) (by rw [hc3 dest hd]; exact hd0) hwnp
      (fun y hy => CovBy.ua (hap.ne hnp) (by rw [hc3 pv hpv] at hy; exact hy))
      (fun _ => ⟨z, hz, by rw [hc3 z hz]; exact hcz⟩)))
    (cdt.move_cap.lr hO (LR.self s3) hpv hd hpd (hO.canon hW hd) hwnp
      (fun h => inOS _ (F.pvm _ gp h)) (fun h => inOS _ (F.nxm _ gp h)))) fun s4 h4 => ?_
  obtain ⟨⟨m4, C4⟩, -, e4d, e4p, e4k⟩ := h4
  have c4s : capA st s4 src = capA st s src := by rw [e4k src hsrc hps.symm hsd, hc3 src hsrc]
  -- the emptied pivot slot is covered at `s4`
  have hcp : ∃ z ∈ OS, CovBy (capA st s4 z) pv := by
    obtain ⟨w, hw, hcw⟩ := C3.cov hpv (by rw [hc3 pv hpv]; exact hp0)
    by_cases a1 : w = pv
    · refine ⟨dest, hd, ?_⟩
      rw [e4d]
      rw [a1, hc3 pv hpv] at hcw
      exact CovBy.ua (hap.ne hnp) hcw
    · by_cases a2 : w = dest
      · rw [a2, hc3 dest hd, hd0] at hcw
        exact absurd hcw.1 (by rw [physA_null]; decide)
      · exact ⟨w, hw, by rw [e4k w hw a1 a2]; exact hcw⟩
  exact WP.spec_and
    (cdt.move_cap.mdbS hO m4 hsrc (by rw [c4s]; exact hs0) hpv e4p (hO.canon hW hpv) hwns hns
      (by rw [c4s]; exact hal.ne hns))
    (cdt.move_cap.covG hO C4 m4 hsrc hpv (Ne.symm hps) (hO.canon hW hpv) e4p hwns
      (fun y hy => CovBy.ua (has.ne hns) (by rw [c4s] at hy; exact hy)) fun _ => hcp)

/-! ## The decode tops -/

/-- The `UtInvA.reg` of an `MdbST` state. -/
theorem MdbST.reg {s : S} (hm : MdbST st OS s) :
    ∀ x ∈ OS, physA (capA st s x) = true → baseA (capA st s x) ≤ topA (capA st s x) := fun x hx hp =>
  hm.tu.elim fun _ h => h.elim fun _ hT => hT.ut.reg x hx hp

set_option maxHeartbeats 1000000 in
/-- **`cnode.decode` at CNode Copy / Mint / Move / Mutate / Rotate keeps `MdbS ∧ CoverA`** (module docstring). -/
theorem cnode.decode.cnode_cov {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : MdbST st OS s)
    (hC : CoverA st OS s) {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hh : Held st OS s c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => MdbS st OS s' ∧ CoverA st OS s' ⦄ := by
  have hS := hm.mdbS
  have hcov : ∀ y, y ∈ OS ∧ SlotCov st OS s y → ∃ z ∈ OS, CovBy (capA st s z) y := fun y hy =>
    SlotCov.cov hO hm.reg (fun x hx p r g b h => (RootOK.of_slot hT hx (capA_eq s x)).2 p r g b h) hy.1 hy.2
  exact cnode.decode.cnodeG (P := fun x => MdbS st OS x ∧ CoverA st OS x) ⟨hS, hC⟩ a hl c (lookup_tgt_cov hT c hc hh)
    (fun hl4 dest hy => cnode.decode_copy.gen hO q (P := fun x => MdbS st OS x ∧ CoverA st OS x) ⟨hS, hC⟩
      (fun sl hsl hs0 i d => lookup_src_in hT _ (RootOK.of_slot hT (hx sl hsl hs0) (capA_eq s sl)) i d)
      ((cnode.decode_copy.mvS hO hS hl4 hy.1 (hO.canon hW hy.1)).and
        (cnode.decode_copy.mvC hO hS hC hl4 hy.1 (hO.canon hW hy.1) (hcov dest hy)))
      ((cnode.decode_copy.insS hO hS hl4 hy.1 (hO.canon hW hy.1)).and
        (cnode.decode_copy.insC hO hS hC hl4 hy.1 (hO.canon hW hy.1) (hcov dest hy))))
    fun dest hy => cnode.decode_rotate.gen hO q hT (P := fun x => MdbS st OS x ∧ CoverA st OS x)
      ⟨hS, hC⟩ hx
      ((cnode.decode_rotate.swS hO hW hS).and (cnode.decode_rotate.swC hO hW hS hC))
      (cnode.decode_rotate.mvC hO hW hS hC hy.1 (hcov dest hy))

/-- **CNode Copy / Mint / Move / Mutate / Rotate at `decode_invocation`** of a CNode cap read from an `OS` slot
keep `MdbS ∧ CoverA`. -/
theorem syscall.decode_invocation.cnode_cov {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    (hW : WinOK T Ω) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : MdbST st OS s)
    (hC : CoverA st OS s)
    (a : A) {lbl : U64} (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ =>
      MdbS st OS s' ∧ CoverA st OS s' ⦄ :=
  syscall.decode_invocation.cnodeG (P := fun x => MdbS st OS x ∧ CoverA st OS x) ⟨hm.mdbS, hC⟩ a len slot cap
    blk call don fp buf extra hf
    (cnode.decode.cnode_cov hO hW q hT hm hC a hl cap (RootOK.of_slot hT hslot hcap)
      ⟨slot, hslot, okinj ((capA_eq s slot).symm.trans hcap)⟩ hx)

/-- **`cnode.decode` at CNode Copy / Mint / Move / Mutate / Rotate keeps `MdbST ∧ UtRev ∧ CoverA`.** -/
theorem cnode.decode.cnode_mdbSTRC {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hm : MdbST st OS s ∧ UtRev st OS s ∧ CoverA st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hh : Held st OS s c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ =>
      MdbST st OS s' ∧ UtRev st OS s' ∧ CoverA st OS s' ⦄ :=
  WP.spec_mono (WP.spec_and (cnode.decode.cnode_mdbSTR hO hW q hT ⟨hm.1, hm.2.1⟩ a hl c hc hx)
    (cnode.decode.cnode_cov hO hW q hT hm.1 hm.2.2 a hl c hc hh hx))
    fun ⟨_, _, _⟩ ⟨h1, h2⟩ => ⟨h1.1, h1.2, h2.2⟩

/-- **CNode Copy / Mint / Move / Mutate / Rotate at `decode_invocation` keep `MdbST ∧ UtRev ∧ CoverA`.** -/
theorem syscall.decode_invocation.cnode_mdbSTRC {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    (hW : WinOK T Ω) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hm : MdbST st OS s ∧ UtRev st OS s ∧ CoverA st OS s)
    (a : A) {lbl : U64} (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ =>
      MdbST st OS s' ∧ UtRev st OS s' ∧ CoverA st OS s' ⦄ :=
  WP.spec_mono (WP.spec_and
    (syscall.decode_invocation.cnode_mdbSTR hO hW q hT ⟨hm.1, hm.2.1⟩ a len slot cap blk call don fp buf extra hl hf
      hslot hcap hx)
    (syscall.decode_invocation.cnode_cov hO hW q hT hm.1 hm.2.2 a len slot cap blk call don fp buf extra hl hf
      hslot hcap hx))
    fun ⟨_, _, _⟩ ⟨h1, h2⟩ => ⟨h1.1, h1.2, h2.2⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1

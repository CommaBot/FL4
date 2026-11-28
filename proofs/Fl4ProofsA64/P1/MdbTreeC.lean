/-
P1 (aarch64, gen 57): **the tree and `UtRev` through the CNode decode tops** — CNode Copy / Mint / Move / Mutate /
Rotate at `cnode.decode_copy` / `cnode.decode_rotate` / `cnode.decode` / `decode_invocation` keep
`TR := MdbTU ∧ UtRev` (the tree on some ghost and the revocable bit of untyped slots), and, with gen 51/52's `MdbS`
tops (MdbLook, MdbRot; statements untouched), **`MdbST ∧ UtRev`** (`MdbST.of` aligns the two ghosts).

* **`TreeA.keepO`** / **`TR.keep`**: an `OSKeep` step (`set_thread_state`, `stt_osk`) keeps them.
* **`cnode.copied_cap.noDesc`**: Copy / Mint of an `Untyped` source returning `Ok` ⇒ the source has no descendants
  (`mask_cap_rights` / `update_cap_data false` return an `Untyped` unchanged, objects.rs; then
  `objects.derive_cap.noDescU`, `UtRev` giving the source's `revocable = true`): the `hut` of
  `cdt.insert_with_cap.tree`. **`cnode.copied_cap.uaM`**: Move / Mutate's cap is `UN` the source's (MdbTreeD's
  `copied_cap.ua` covers Copy / Mint).
* Step lemmas: **`cdt.insert_with_cap.tr`** (`insert_with_cap.tree` + `.utRev`), **`cdt.move_cap.tr`**
  (`move_cap.tree` + `.utRev`, `UA.isut` for the moved cap), **`cdt.swap.tr`** (`swap.tree` + `.utRev`).
* Decode traversals (gen 51/52's proofs, same case split, the `MdbS` steps replaced by the `TR` ones, `UA` / `UN`
  for `AlikeA` / `AlN`): **`cnode.decode_copy.trX`**, **`cnode.decode_rotate.tr`**, **`cnode.decode.copy_tr`**,
  **`cnode.decode.rot_tr`**, **`cnode.decode.cnode_tr`**, **`syscall.decode_invocation.cnode_tr`**.
* Tops with the whole bundle: **`cnode.decode.cnode_mdbSTR`**, **`syscall.decode_invocation.cnode_mdbSTR`**
  (`MdbST ∧ UtRev` before ⇒ after; hypotheses of gen 52's `cnode_mdbS` tops).

* (gen 60) The traversals are instances of the one traversal of each shape (MdbCopyD's `cnode.decode_copy.gen`,
  MdbRot's `cnode.decode_rotate.gen`, `cnode.decode.copyG` / `rotG` / `cnodeG`, `syscall.decode_invocation.cnodeG`)
  with `TR`'s steps `cnode.decode_copy.mvT` / `insT`, `cnode.decode_rotate.swT` / `mvT`.

No named premise; case hypotheses as gen 51/52's tops.
-/
import Fl4ProofsA64.P1.MdbTreeN
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **The tree (on some ghost) and `UtRev`** (module docstring). -/
def TR (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) : Prop :=
  MdbTU st OS s ∧ UtRev st OS s

variable {OS : Set U64}

theorem TreeA.keepO {G : List (List U64)} {par : U64 → Option U64} {s s' : S} (h : TreeA st OS G par s)
    (k : OSKeep st OS s s') : TreeA st OS G par s' :=
  ⟨h.lk.keep (fun x hx => ⟨(k x hx).2.2.1, (k x hx).2.2.2⟩) (fun x hx => by rw [k.capA hx]), h.tree,
    h.ut.recap h.parIn fun y hy => by rw [k.capA hy]; exact UA.refl _⟩

theorem TR.keep {s s' : S} (h : TR st OS s) (k : OSKeep st OS s s') : TR st OS s' := by
  obtain ⟨⟨G, par, hT⟩, hR⟩ := h
  exact ⟨⟨G, par, hT.keepO k⟩, hR.keep k⟩

/-! ## The new caps -/

theorem un_refl (c : capability.Cap) : UN c c := by
  by_cases h : c = .Null
  · exact Or.inl h
  · exact Or.inr ⟨UA.refl c, h⟩

set_option maxHeartbeats 1000000 in
/-- (gen 60) **CNode Move / Mutate's new cap is related to the source cap by any reflexive relation `R` that
`update_cap_data` respects** (`copied_cap.uaM`'s proof, the relation abstracted). -/
theorem cnode.copied_cap.uaMG {R : capability.Cap → capability.Cap → Prop} (hrf : ∀ c, R c c)
    (hup : ∀ (pr : Bool) (data : U64) (c : capability.Cap), objects.update_cap_data pr data c ⦃ m => R m c ⦄)
    (s : S) (lbl length buf src : U64) (src_cap : capability.Cap)
    (hl : lbl = fl4_abi.label.CNodeMove ∨ lbl = fl4_abi.label.CNodeMutate) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc b, r = .Ok (nc, b) → R nc src_cap ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h1 : ¬ lbl = fl4_abi.label.CNodeCopy := by
    rcases hl with rfl | rfl <;> (first | decide | (simp only [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeMint, fl4_abi.label.CNodeMove, fl4_abi.label.CNodeMutate]; decide) | simp [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeMint, fl4_abi.label.CNodeMove, fl4_abi.label.CNodeMutate])
  have h2 : ¬ lbl = fl4_abi.label.CNodeMint := by
    rcases hl with rfl | rfl <;> (first | decide | (simp only [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeMint, fl4_abi.label.CNodeMove, fl4_abi.label.CNodeMutate]; decide) | simp [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeMint, fl4_abi.label.CNodeMove, fl4_abi.label.CNodeMutate])
  unfold cnode.copied_cap
  refine WP.spec_bind (P0.sched.cur_thread.p0 st s hS) fun ct _ => ?_
  rw [if_neg h1, if_neg h2]
  split
  · rw [WP.spec_ok]; intro nc b h; cases h; exact hrf _
  · split
    · simp only [error.truncated, WP.spec_ok]; intro nc b h; cases h
    · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
      refine WP.spec_bind (hup true data src_cap) fun c hc => ?_
      rw [WP.spec_ok]; intro nc b h; cases h; exact hc

set_option maxHeartbeats 1000000 in
/-- **CNode Move / Mutate's new cap is `UN` the source cap.** -/
theorem cnode.copied_cap.uaM (s : S) (lbl length buf src : U64) (src_cap : capability.Cap)
    (hl : lbl = fl4_abi.label.CNodeMove ∨ lbl = fl4_abi.label.CNodeMutate) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc b, r = .Ok (nc, b) → UN nc src_cap ⦄ :=
  cnode.copied_cap.uaMG (R := UN) un_refl (fun pr d c => objects.update_cap_data.ua pr d c) s lbl length buf src
    src_cap hl

section nd
variable {G : List (List U64)} {par : U64 → Option U64}

set_option maxHeartbeats 1000000 in
/-- **Copy / Mint of an `Untyped` source returning `Ok`: the source has no descendants** (module docstring). -/
theorem cnode.copied_cap.noDesc (hO : OSOK T Ω Sg OS) {s : S} (h : TreeA st OS G par s) (hR : UtRev st OS s)
    {x : U64} (hx : x ∈ OS) (lbl length buf : U64) :
    cnode.copied_cap st s lbl length buf x (capA st s x) ⦃ r => ∀ nc, r = .Ok (nc, false) →
      isUtA (capA st s x) = true → ∀ y, ¬ Mdb.Desc par y x ⦄ := by
  have hS : P0.StoreTotal st := L.total
  by_cases hu : isUtA (capA st s x) = true
  swap
  · exact WP.spec_mono (P0.cnode.copied_cap.p0 st s lbl length buf x _ hS) fun _ _ _ _ h => absurd h hu
  obtain ⟨p, b, i, d, hc⟩ : ∃ p b i d, capA st s x = .Untyped p b i d := by
    revert hu; cases capA st s x <;> intro hu <;> simp [isUtA] at hu ⊢
  have D := objects.derive_cap.noDescU hO h hR hx hc
  rw [hc]
  have fin : ∀ x' : core.result.Result capability.Cap error.Exc,
      (∀ nc, x' = .Ok nc → ∀ y, ¬ Mdb.Desc par y x) →
      (do
        let cf ← core.result.Result.Insts.CoreOpsTry.branch x'
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val => ok (core.result.Result.Ok (val, false))
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (capability.Cap × Bool) (core.convert.FromSame error.Exc) residual :
        Result (core.result.Result (capability.Cap × Bool) error.Exc)) ⦃ r =>
        ∀ nc, r = .Ok (nc, false) → isUtA (.Untyped p b i d) = true → ∀ y, ¬ Mdb.Desc par y x ⦄ := by
    intro x' hx'
    rcases x' with v | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
      intro nc _ _; exact hx' v rfl
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      first
      | exact (WP.spec_ok _).2 fun nc h => (by cases h)
      | (simp only [WP.spec_ok]; intro nc h; cases h)
  unfold cnode.copied_cap
  refine WP.spec_bind (P0.sched.cur_thread.p0 st s hS) fun ct _ => ?_
  split
  · split
    · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
    · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun i' _ => ?_
      refine WP.spec_bind (P0.capability.Rights.from_word.p0 i') fun rr _ => ?_
      simp only [capability.mask_cap_rights, bind_ok]
      exact WP.spec_bind D fun r1 h1 => fin r1 h1
  · split
    · split
      · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
      · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun i' _ => ?_
        refine WP.spec_bind (P0.capability.Rights.from_word.p0 i') fun rr _ => ?_
        refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
        simp only [capability.mask_cap_rights, objects.update_cap_data, bind_ok]
        exact WP.spec_bind D fun r1 h1 => fin r1 h1
    · split
      · exact (WP.spec_ok _).2 fun nc h => by cases h
      · split
        · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
        · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
          exact WP.spec_bind (P0.objects.update_cap_data.p0 true data _) fun _ _ =>
            (WP.spec_ok _).2 fun nc h => by cases h

end nd

/-! ## Step lemmas -/

/-- **`insert_with_cap` keeps `TR`** (`cdt.insert_with_cap.tree` + `cdt.insert_with_cap.utRev`). -/
theorem cdt.insert_with_cap.tr (hO : OSOK T Ω Sg OS) {G : List (List U64)} {par : U64 → Option U64} {s : S}
    (hT : TreeA st OS G par s) (hR : UtRev st OS s) {src dest : U64} {nc sc : capability.Cap}
    (hsrc : src ∈ OS) (hs0 : capA st s src ≠ .Null) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null)
    (hdc : obj.sext48 dest = ok dest) (hsc : capA st s src = sc) (hw : CapRt.EncWf nc) (hnc : nc ≠ .Null)
    (hA : UA nc sc) (hut : isUtA sc = true → ∀ y, ¬ Mdb.Desc par y src) :
    cdt.insert_with_cap st s nc sc src dest ⦃ s' => TR st OS s' ⦄ := by
  have hsG : src ∈ G.flatten := (hT.lk.members src).2 ⟨hsrc, hs0⟩
  have F := hT.lk.lkF hO.nz
  have hsd : src ≠ dest := fun e => hs0 (by rw [e]; exact hd0)
  exact WP.spec_mono (WP.spec_and (cdt.insert_with_cap.tree hO hT hsG hd hd0 hdc hsc hw hnc hA hut)
    (cdt.insert_with_cap.utRev hO hR hsrc hd hsd hdc hsc (by rw [← hsc]; exact hs0) hw
      (fun h => ((hT.lk.members _).1 (F.nxm _ hsG h)).1))) fun _ ⟨h1, h2⟩ => ⟨⟨_, _, h1⟩, h2⟩

/-- **`move_cap` keeps `TR`** (`cdt.move_cap.tree` + `cdt.move_cap.utRev`). -/
theorem cdt.move_cap.tr (hO : OSOK T Ω Sg OS) {s : S} (hm : TR st OS s) {src dest : U64} {nc : capability.Cap}
    (hsrc : src ∈ OS) (hs0 : capA st s src ≠ .Null) (hd : dest ∈ OS) (hd0 : capA st s dest = .Null)
    (hdc : obj.sext48 dest = ok dest) (hw : CapRt.EncWf nc) (hn : nc ≠ .Null) (hal : UA nc (capA st s src)) :
    cdt.move_cap st s nc src dest ⦃ s' => TR st OS s' ⦄ := by
  obtain ⟨⟨G, par, hT⟩, hR⟩ := hm
  have hsG : src ∈ G.flatten := (hT.lk.members src).2 ⟨hsrc, hs0⟩
  have F := hT.lk.lkF hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hT.lk.members y).1 hy).1
  have hsd : src ≠ dest := fun e => hs0 (by rw [e]; exact hd0)
  exact WP.spec_mono (WP.spec_and (cdt.move_cap.tree hO hT hsG hd hd0 hdc hw hn hal)
    (cdt.move_cap.utRev hO hR hsrc hd hsd hdc hw (fun h => inOS _ (F.pvm _ hsG h))
      (fun h => inOS _ (F.nxm _ hsG h)) (fun h => by rw [← hal.isut]; exact h)))
    fun _ ⟨h1, h2⟩ => ⟨⟨_, _, h1⟩, h2⟩

/-- **`swap` keeps `TR`** (`cdt.swap.tree` + `cdt.swap.utRev`). -/
theorem cdt.swap.tr (hO : OSOK T Ω Sg OS) {s : S} (hm : TR st OS s) {x1 x2 : U64} {c1 c2 : capability.Cap}
    (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2)
    (h10 : capA st s x1 ≠ .Null) (h20 : capA st s x2 ≠ .Null) (hw1 : CapRt.EncWf c1) (hw2 : CapRt.EncWf c2)
    (hn1 : c1 ≠ .Null) (hn2 : c2 ≠ .Null) (ha1 : UA c1 (capA st s x1)) (ha2 : UA c2 (capA st s x2)) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => TR st OS s' ⦄ := by
  obtain ⟨⟨G, par, hT⟩, hR⟩ := hm
  have F := hT.lk.lkF hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hT.lk.members y).1 hy).1
  have g1 : x1 ∈ G.flatten := (hT.lk.members x1).2 ⟨hx1, h10⟩
  have g2 : x2 ∈ G.flatten := (hT.lk.members x2).2 ⟨hx2, h20⟩
  exact WP.spec_mono (WP.spec_and (cdt.swap.tree hO hT g1 g2 hne hs1 hs2 hw1 hw2 hn1 hn2 ha1 ha2)
    (cdt.swap.utRev hO hR hx1 hx2 hne hs1 hs2 hw1 hw2 (fun h => inOS _ (F.pvm _ g1 h))
      (fun h => inOS _ (F.nxm _ g1 h)) (fun h => inOS _ (F.pvm _ g2 h)) (fun h => inOS _ (F.nxm _ g2 h))
      (fun h => by rw [← ha1.isut]; exact h) (fun h => by rw [← ha2.isut]; exact h)))
    fun _ ⟨h1, h2⟩ => ⟨⟨_, _, h1⟩, h2⟩

/-! ## The decode traversals -/

/-- (gen 60) **`TR`'s `move_cap` step** of the CNode Move / Mutate decode (gen 57's `trX` move branch). -/
theorem cnode.decode_copy.mvT (hO : OSOK T Ω Sg OS) {s : S} (hm : TR st OS s) {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest) : CpMv st OS s lbl len buf dest (TR st OS) := by
  intro s2 v nc k2 _ hv hs0 hd0 he hn0
  have hc2 : ∀ y ∈ OS, capA st s2 y = capA st s y := fun y hy => by
    unfold capA; rw [(k2 y hy).1, (k2 y hy).2.1]
  have hwf : CapRt.EncWf (capA st s v) := CapRt.decodeF_encWf _ _
  have hmv := cnode.copied_cap.lblT hl4 hwf he
  have h2 := cnode.copied_cap.mv (st := st) s lbl len buf v (capA st s v) hmv hwf
  have hu2 := cnode.copied_cap.uaM (st := st) s lbl len buf v (capA st s v) hmv
  rw [he, WP.spec_ok] at h2 hu2
  have hwn := (h2 nc true rfl).2.2
  have hua := hu2 nc true rfl
  exact cdt.move_cap.tr hO (hm.keep k2) hv (by rw [hc2 v hv]; exact hs0) hd
    (by rw [hc2 dest hd]; exact hd0) hdc hwn hn0 (by rw [hc2 v hv]; exact hua.ne hn0)

/-- (gen 60) **`TR`'s `insert_with_cap` step** of the CNode Copy / Mint decode (gen 57's `trX` copy branch). -/
theorem cnode.decode_copy.insT (hO : OSOK T Ω Sg OS) {s : S} (hm : TR st OS s) {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest) : CpIns st OS s lbl len buf dest (TR st OS) := by
  intro s2 v nc k2 _ hv hs0 hd0 he hn0
  have hc2 : ∀ y ∈ OS, capA st s2 y = capA st s y := fun y hy => by
    unfold capA; rw [(k2 y hy).1, (k2 y hy).2.1]
  have hwf : CapRt.EncWf (capA st s v) := CapRt.decodeF_encWf _ _
  obtain ⟨⟨G, par, hTr⟩, hR⟩ := id hm
  have ha2 := cnode.copied_cap.ua (st := st) s lbl len buf v (capA st s v)
  have hw2 := cnode.copied_cap.wf (st := st) s lbl len buf v (capA st s v)
    (cnode.copied_cap.lblF hl4 hwf he) hwf
  have hnd2 := cnode.copied_cap.noDesc hO hTr hR hv lbl len buf
  rw [he, WP.spec_ok] at ha2 hw2 hnd2
  have hwn := (hw2 nc false rfl).2
  have hua := ha2 nc rfl
  have hut := hnd2 nc rfl
  exact cdt.insert_with_cap.tr hO (hTr.keepO k2) (hR.keep k2) hv (by rw [hc2 v hv]; exact hs0) hd
    (by rw [hc2 dest hd]; exact hd0) hdc (hc2 v hv) hwn hn0 (hua.ne hn0) hut

/-- (gen 60) **`TR`'s `swap` step** of CNode Rotate (gen 57's `decode_rotate.tr` swap branch). -/
theorem cnode.decode_rotate.swT (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω) {s : S} (hm : TR st OS s) {dest : U64} :
    RtSw st OS s dest (TR st OS) := by
  intro s3 src pv sd pd ns np k3 _ hsrc hpv hps hpd hs0 hp0 hsd e1 e2 hns hnp
  have hc3 : ∀ y ∈ OS, capA st s3 y = capA st s y := fun y hy => by
    unfold capA; rw [(k3 y hy).1, (k3 y hy).2.1]
  have has := objects.update_cap_data.ua true sd (capA st s src)
  have hwns := objects.update_cap_data.wf true sd (capA st s src) (CapRt.decodeF_encWf _ _)
  have hap := objects.update_cap_data.ua true pd (capA st s pv)
  have hwnp := objects.update_cap_data.wf true pd (capA st s pv) (CapRt.decodeF_encWf _ _)
  rw [e1, WP.spec_ok] at has hwns
  rw [e2, WP.spec_ok] at hap hwnp
  exact cdt.swap.tr hO (hm.keep k3) hsrc hpv (Ne.symm hps) (hO.canon hW hsrc) (hO.canon hW hpv)
    (by rw [hc3 src hsrc]; exact hs0) (by rw [hc3 pv hpv]; exact hp0) hwns hwnp hns hnp
    (by rw [hc3 src hsrc]; exact has.ne hns) (by rw [hc3 pv hpv]; exact hap.ne hnp)

/-- (gen 60) **`TR`'s two `move_cap` steps** of CNode Rotate (gen 57's `decode_rotate.tr` move branch). -/
theorem cnode.decode_rotate.mvT (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω) {s : S} (hm : TR st OS s) {dest : U64}
    (hd : dest ∈ OS) : RtMv st OS s dest (TR st OS) := by
  intro s3 src pv sd pd ns np k3 _ hsrc hpv hps hpd hs0 hp0 hsd hd0 e1 e2 hns hnp
  have hc3 : ∀ y ∈ OS, capA st s3 y = capA st s y := fun y hy => by
    unfold capA; rw [(k3 y hy).1, (k3 y hy).2.1]
  have has := objects.update_cap_data.ua true sd (capA st s src)
  have hwns := objects.update_cap_data.wf true sd (capA st s src) (CapRt.decodeF_encWf _ _)
  have hap := objects.update_cap_data.ua true pd (capA st s pv)
  have hwnp := objects.update_cap_data.wf true pd (capA st s pv) (CapRt.decodeF_encWf _ _)
  rw [e1, WP.spec_ok] at has hwns
  rw [e2, WP.spec_ok] at hap hwnp
  have m3 := hm.keep k3
  obtain ⟨⟨G, par, hT3⟩, -⟩ := id m3
  have hM := hT3.lk
  have F := hM.lkF hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have gp : pv ∈ G.flatten := (hM.members pv).2 ⟨hpv, by rw [hc3 pv hpv]; exact hp0⟩
  refine WP.spec_mono (WP.spec_and
    (cdt.move_cap.tr hO m3 hpv (by rw [hc3 pv hpv]; exact hp0) hd (by rw [hc3 dest hd]; exact hd0)
      (hO.canon hW hd) hwnp hnp (by rw [hc3 pv hpv]; exact hap.ne hnp))
    (cdt.move_cap.lr hO (LR.self s3) hpv hd hpd (hO.canon hW hd) hwnp
      (fun h => inOS _ (F.pvm _ gp h)) (fun h => inOS _ (F.nxm _ gp h)))) fun s4 h4 => ?_
  obtain ⟨m4, -, -, e4p, e4k⟩ := h4
  have c4s : capA st s4 src = capA st s src := by rw [e4k src hsrc hps.symm hsd, hc3 src hsrc]
  exact cdt.move_cap.tr hO m4 hsrc (by rw [c4s]; exact hs0) hpv e4p (hO.canon hW hpv) hwns hns
    (by rw [c4s]; exact has.ne hns)

/-- **CNode Copy / Mint / Move / Mutate at decode level keep `TR`** (`cnode.decode_copy.mdbSX`'s traversal). -/
theorem cnode.decode_copy.trX (hO : OSOK T Ω Sg OS) {X : Set U64} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} {s : S} (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hm : TR st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest)
    (hsrc : ∀ sl ∈ extra.val, sl ≠ 0#u64 → ∀ (i d : U64),
      cspace.lookup_source_slot st s (capA st s sl) i d ⦃ r => ∀ x, r = .Ok x → x ∈ OS ⦄) :
    cnode.decode_copy st s lbl len buf extra dest ⦃ r => TR st OS r.2 ⦄ :=
  cnode.decode_copy.gen hO q hm hsrc (cnode.decode_copy.mvT hO hm hl4 hd hdc)
    (cnode.decode_copy.insT hO hm hl4 hd hdc)

/-- **CNode Rotate at decode level keeps `TR`** (`cnode.decode_rotate.mdbS`'s traversal). -/
theorem cnode.decode_rotate.tr (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω) {X : Set U64}
    {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S} (q : SchedQueuesInvX st T Cs Ω H X s Q Rq)
    (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : TR st OS s) {extra : Aeneas.Std.Array obj.Slot 3#usize}
    {len buf dest : U64} (hd : dest ∈ OS) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode_rotate st s len buf extra dest ⦃ r => TR st OS r.2 ⦄ :=
  cnode.decode_rotate.gen hO q hT hm hx (cnode.decode_rotate.swT hO hW hm) (cnode.decode_rotate.mvT hO hW hm hd)

/-- **`cnode.decode` at CNode Copy / Mint / Move / Mutate keeps `TR`** (`cnode.decode.copy_mdbS`'s traversal). -/
theorem cnode.decode.copy_tr {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : TR st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => TR st OS s' ⦄ :=
  cnode.decode.copyG hm a hl c (lookup_tgt_in hT c hc) fun _ hv =>
    cnode.decode_copy.trX hO q hm hl hv (hO.canon hW hv) fun sl hsl hs0 i d =>
      lookup_src_in hT _ (RootOK.of_slot hT (hx sl hsl hs0) (capA_eq s sl)) i d

/-- **`cnode.decode` at CNode Rotate keeps `TR`** (`cnode.decode.rot_mdbS`'s traversal). -/
theorem cnode.decode.rot_tr {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : TR st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {len buf : U64}
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a fl4_abi.label.CNodeRotate len c buf extra ⦃ r s' _ => TR st OS s' ⦄ :=
  cnode.decode.rotG hm a c (lookup_tgt_in hT c hc) fun _ hv => cnode.decode_rotate.tr hO hW q hT hm hv hx

/-- **`cnode.decode` at CNode Copy / Mint / Move / Mutate / Rotate keeps `TR`.** -/
theorem cnode.decode.cnode_tr {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : TR st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => TR st OS s' ⦄ :=
  cnode.decode.cnodeG hm a hl c (lookup_tgt_in hT c hc)
    (fun hl4 _ hv => cnode.decode_copy.trX hO q hm hl4 hv (hO.canon hW hv) fun sl hsl hs0 i d =>
      lookup_src_in hT _ (RootOK.of_slot hT (hx sl hsl hs0) (capA_eq s sl)) i d)
    fun _ hv => cnode.decode_rotate.tr hO hW q hT hm hv hx

/-- **CNode Copy / Mint / Move / Mutate / Rotate at `decode_invocation`** of a CNode cap read from an `OS` slot
keep `TR`. -/
theorem syscall.decode_invocation.cnode_tr {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    (hW : WinOK T Ω) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : TR st OS s)
    (a : A) {lbl : U64} (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ => TR st OS s' ⦄ :=
  syscall.decode_invocation.cnodeG hm a len slot cap blk call don fp buf extra hf
    (cnode.decode.cnode_tr hO hW q hT hm a hl cap (RootOK.of_slot hT hslot hcap) hx)

/-! ## The whole bundle -/

/-- **`cnode.decode` at CNode Copy / Mint / Move / Mutate / Rotate keeps `MdbST ∧ UtRev`** (`cnode_mdbS` and
`cnode_tr`, the ghosts aligned by `MdbST.of`). -/
theorem cnode.decode.cnode_mdbSTR {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hm : MdbST st OS s ∧ UtRev st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => MdbST st OS s' ∧ UtRev st OS s' ⦄ :=
  WP.spec_mono (WP.spec_and (cnode.decode.cnode_mdbS hO hW q hT hm.1.mdbS a hl c hc hx)
    (cnode.decode.cnode_tr hO hW q hT ⟨hm.1.tu, hm.2⟩ a hl c hc hx))
    fun ⟨_, _, _⟩ ⟨h1, h2⟩ => ⟨MdbST.of hO.nz h1 h2.1, h2.2⟩

/-- **CNode Copy / Mint / Move / Mutate / Rotate at `decode_invocation` keep `MdbST ∧ UtRev`.** -/
theorem syscall.decode_invocation.cnode_mdbSTR {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    (hW : WinOK T Ω) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hm : MdbST st OS s ∧ UtRev st OS s)
    (a : A) {lbl : U64} (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ =>
      MdbST st OS s' ∧ UtRev st OS s' ⦄ :=
  WP.spec_mono (WP.spec_and
    (syscall.decode_invocation.cnode_mdbS hO hW q hT hm.1.mdbS a len slot cap blk call don fp buf extra hl hf hslot
      hcap hx)
    (syscall.decode_invocation.cnode_tr hO hW q hT ⟨hm.1.tu, hm.2⟩ a len slot cap blk call don fp buf extra hl hf
      hslot hcap hx))
    fun ⟨_, _, _⟩ ⟨h1, h2⟩ => ⟨MdbST.of hO.nz h1 h2.1, h2.2⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1

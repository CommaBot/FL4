/-
P1 (aarch64, gen 44): **`UnmZ` / `UnmU` along the Stage-2 leaf map** (`ept::map_frame` / `install_s2_leaf`, both the
first map and the remap path) and **the frame decode into a Stage-2 VSpace at decode level** (`vspace.decode_frame`
at `ARMPageMap` → `decode_page_map` → `ept::map_frame`) — toward discharging gen 41's [J] `SlotTyEntE` (QueueS2Inv)
step by step, on gen 42's `UnmZ` (QueueS2Map) and gen 43's `UnmU` (QueueS2Unm).

* **Frame caps** (pure / store): `CapRt.dec_frame_any` (an encoded `Frame` cap decodes to a `Frame` cap: tag 13,
  whatever its fields), `set_cap_frame` (`set_cap` of a `Frame` cap into an `OS` slot: every `VsR` word and every
  other `OS` cap kept, the slot holds a `Frame` cap), `frm_nvs` (a slot holding a `Frame` cap holds no `UnmC` /
  `NmC` / `VsC` cap).
* **`ept.install_s2_leaf.inv`** (ept.rs:290–316): any state predicate closed under writes of `0` or the leaf to the
  found slot holds after `install_s2_leaf` (break-before-make writes only `lu.slot`; the TLB invalidation is an
  `Arch` call).
* **`ept.map_frame.unmz`** (ept.rs:236–287, the whole function, fresh map and remap): the state unchanged, or `UnmZ`
  (same `Te`) and `UnmU` after — the frame cap's slot becomes a `Frame` cap (no `PageTable` / `Ept` cap appears),
  the leaf goes to a word of a `Te` table (no unmapped object's word, by `UnmZ`), via gen 43's `UnmZ.step`.
* **`vspace.decode_frame.map_s2`** (vspace.rs:687–729 and 731–788: `decode_frame` at `ARMPageMap` with a `Frame` cap
  and an `Ept` cap in the extra slot): unchanged, or `ks`, `VsTy`, `S2Ty` (same ghost sets), `UnmZ`, `UnmU`
  (`ept.root.ty`, gen 42's `ept.map_frame.ty`, `ept.map_frame.unmz`).

**Which part of [J] `SlotTyEntE` the covered steps preserve**: `ept::map_frame` / `install_s2_leaf` and the
decode-level ARMPageMap into a Stage-2 VSpace: `VsTy`, `S2Ty` (same `Te`, `Re`), `ks` (gen 42) and now the case
facts `UnmZ` and `UnmU`. `Gran`, `S2OK`, `S2Pl`, `HrOK` are state-free case hypotheses over the same sets.

No named premise is new: [P] `ArchPlat.s2_ipa_bits_const` (QueueS2Ty) is consumed via `hPl` (the walk);
`UnmZ`, `UnmU` are case facts (definitions).
-/
import Fl4ProofsA64.P1.QueueS2Unm
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1.CapRt
open fl4_core_a64

set_option maxHeartbeats 1000000 in
/-- An encoded `Frame` cap decodes to a `Frame` cap (tag 13; the fields need not fit). -/
theorem dec_frame_any (p : U64) (sz : capability.FrameSize) (r : U64) (dev m e : Bool) (asid va : U64) :
    ∃ p' sz' r' dev' m' e' a' v', decodeF (encodeF (.Frame p sz r dev m e asid va)).1
      (encodeF (.Frame p sz r dev m e asid va)).2 = .Frame p' sz' r' dev' m' e' a' v' := by
  have h4 := codeF_hb sz
  have htag := tag_gen (w := (encodeF (.Frame p sz r dev m e asid va)).1) (k := 13) (by bvext) (by decide)
  simp only [decodeF, htag]
  split
  · exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  · exact ⟨_, _, _, _, _, _, _, _, rfl⟩

end Fl4ProofsA64.P1.CapRt

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

section frm
variable {OS Vc Ub : Set U64} {kb : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **`set_cap` of a `Frame` cap** into a slot of `OS`: `VsR` words and the other `OS` caps kept, the slot holds a
`Frame` cap. -/
theorem set_cap_frame (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hO : OSOK T Ω Sg OS) {x : U64} (hx : x ∈ OS)
    (s : S) (p : U64) (sz : capability.FrameSize) (r : U64) (dev m e : Bool) (asid va : U64) :
    obj.Slot.set_cap st x s (.Frame p sz r dev m e asid va) ⦃ s' => VsKeep st kb Pt s s' ∧
      (∀ y ∈ OS, y ≠ x → obj.Slot.cap st y s' = obj.Slot.cap st y s) ∧
      ∃ p' sz' r' dev' m' e' a' v', obj.Slot.cap st x s' = ok (.Frame p' sz' r' dev' m' e' a' v') ⦄ := by
  rw [set_cap_eq (CapRt.encode_eq _), WP.spec_ok]
  obtain ⟨k, c2o, c2x⟩ := wr2_cap (st := st) (s := s) hR hO hx
    (w0 := ⟨(CapRt.encodeF (.Frame p sz r dev m e asid va)).1⟩)
    (w1 := ⟨(CapRt.encodeF (.Frame p sz r dev m e asid va)).2⟩)
  obtain ⟨p', sz', r', d', m', e', a', v', h⟩ := CapRt.dec_frame_any p sz r dev m e asid va
  refine ⟨k, c2o, p', sz', r', d', m', e', a', v', ?_⟩
  rw [c2x, CapRt.decode_eq]
  exact congrArg ok h

/-- A slot holding a `Frame` cap holds no `UnmC` / `NmC` / `VsC` cap. -/
theorem frm_nvs {x : U64} {s : S}
    (h : ∃ p' sz' r' d' m' e' a' v', obj.Slot.cap st x s = ok (.Frame p' sz' r' d' m' e' a' v')) :
    (∀ p n, ¬ UnmC st x p n s) ∧ (∀ p, ¬ NmC st x p s) ∧ (∀ p n, ¬ VsC st x p n s) := by
  obtain ⟨p', sz', r', d', m', e', a', v', hc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rintro p n (⟨-, a1, v1, hh⟩ | ⟨-, a1, v1, hh⟩) <;> rw [hc] at hh <;> cases okinj hh
  · rintro p (⟨m, a1, v1, hh⟩ | ⟨l, m, a1, v1, hh⟩) <;> rw [hc] at hh <;> cases okinj hh
  · rintro p n (⟨-, m, a1, v1, hh⟩ | ⟨-, m, a1, v1, hh⟩) <;> rw [hc] at hh <;> cases okinj hh

set_option maxHeartbeats 2000000 in
/-- **`ept::install_s2_leaf`** (ept.rs:290–316) keeps any state predicate closed under writes of `0` or the leaf to
the found slot. -/
theorem ept.install_s2_leaf.inv (hA : P0.ArchTotal ar) {P : S → Prop} {s : S} (h0 : P s) (a : A)
    (lu : ept.S2Slot) (e : U64) (hw : ∀ s1 : S, ∀ v : U64, (v = 0#u64 ∨ v = e) → P s1 → P (L.wr s1 lu.slot v))
    (root asid ipa ptr : U64) (dev : Bool) (attr : U64) :
    ept.install_s2_leaf st ar s a lu e root asid ipa ptr dev attr ⦃ r => P r.1 ⦄ := by
  have wr : ∀ s1 : S, P s1 → ∀ v : U64, (v = 0#u64 ∨ v = e) → st.write s1 lu.slot v ⦃ s' => P s' ⦄ :=
    fun s1 h1 v hv => WP.spec_mono (LawfulStore.write_spec s1 lu.slot v) fun s' e' => by
      subst e'; exact hw s1 v hv h1
  have cop : ∀ m : Result A, m ⦃ _ => True ⦄ → ∀ s1 : S, P s1 →
      (do
        let a2 ← m
        let s2 ← st.write s1 lu.slot e
        ok (s2, a2)) ⦃ r => P r.1 ⦄ :=
    fun m hm s1 h1 => WP.spec_bind hm fun a2 _ => WP.spec_bind (wr s1 h1 e (Or.inr rfl)) fun s2 h2 =>
      (WP.spec_ok _).2 h2
  unfold ept.install_s2_leaf
  refine WP.spec_bind (LawfulStore.read_spec s lu.slot) fun old _ => ?_
  refine WP.spec_bind (P0.ept.is_leaf.p0 old lu.shift) fun b _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  · refine spec_ite (fun _ => ?_) (fun _ => ?_)
    · refine WP.spec_bind P0.ept.S2_BBM_MASK.p0 fun mk _ => ?_
      refine spec_ite (fun _ => ?_) (fun _ => ?_)
      · refine WP.spec_bind (wr s h0 e (Or.inr rfl)) fun s1 h1 => ?_
        refine WP.spec_bind (hA.invalidate_stage2_page a asid ipa) fun a1 _ => ?_
        exact (WP.spec_ok _).2 h1
      · refine WP.spec_bind (wr s h0 0#u64 (Or.inl rfl)) fun s1 h1 => ?_
        refine WP.spec_bind (hA.invalidate_stage2_page a asid ipa) fun a1 _ => ?_
        exact cop _ (by copT) s1 h1
    · refine WP.spec_bind (wr s h0 0#u64 (Or.inl rfl)) fun s1 h1 => ?_
      refine WP.spec_bind (hA.invalidate_stage2_page a asid ipa) fun a1 _ => ?_
      exact cop _ (by copT) s1 h1
  · exact cop _ (by copT) s h0

set_option maxHeartbeats 4000000 in
/-- **`ept::map_frame` keeps `UnmZ` and `UnmU`** (ept.rs:236–287, the whole function: the fresh map and the remap
path; module docstring). -/
theorem ept.map_frame.unmz (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hO : OSOK T Ω Sg OS) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hTe : Gran Te bits ⊆ Pt) (hS : S2OK Te bits Hr)
    (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    {root : U64} (hr : root ∈ Te) (hre : Re root + 1 = s2lv hPl.ipa) (hrb : s2rb hPl.ipa ≤ bits root)
    (hU : UnmZ st OS Pt Te bits s) (hV : UnmU st OS Pp s)
    (a : A) (asid ipa vm attr ptr : U64) (size : capability.FrameSize) (rights : U64) (dev : Bool)
    (masid mvaddr : U64) {slot : U64} (hsl0 : slot ∈ OS) :
    ept.map_frame st ar s a root asid ipa vm attr ptr size rights dev masid mvaddr slot ⦃ r => r.2.1 = s ∨
      (UnmZ st OS Pt Te bits r.2.1 ∧ UnmU st OS Pp r.2.1) ⦄ := by
  unfold ept.map_frame
  refine WP.spec_bind (P0.capability.FrameSize.bits.p0 size) fun shift _ => ?_
  rw [hPl.ipa_eq a, bind_ok]
  try simp only [lift, bind_ok]
  refine WP.spec_bind (shl_and63u _) fun _ _ => ?_
  try simp only [lift, bind_ok]
  refine spec_ite (fun _ => by asErr) (fun _ => ?_)
  refine spec_ite (fun _ => ?_) (fun _ => ?_)
  all_goals
    repeat' (first
      | (refine spec_ite (fun _ => by asErr) (fun _ => ?_))
      | (refine WP.spec_bind (shl_and63u _) fun _ _ => ?_)
      | (refine WP.spec_bind (P0.ept.ipa_limit.p0 _) fun _ _ => ?_)
      | (simp only [lift, bind_ok]))
    refine WP.spec_bind (ept.lookup_slot.tyD h2 hS hr hre hrb ipa) fun lu ⟨p, hp, o, ho, h8, hsl, _⟩ => ?_
    refine spec_ite (fun _ => by asErr) (fun _ => ?_)
    have hw : PtWb Te bits (wa p o) := ⟨p, hp, o, ho, h8, rfl⟩
    have hv0 : VsR kb Pt (wa p o) := Or.inl (ptw_mono hTe (ptwb_gran hS.sz hw))
    refine WP.spec_bind (P0.vspace.rights_readable.p0 _) fun cr _ => ?_
    refine WP.spec_bind (P0.layout.paddr.p0 ptr) fun pa _ => ?_
    refine WP.spec_bind (ept.make_s2_leaf.b1 pa vm cr attr shift) fun e _ => ?_
    refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
    have hct : ct ∈ T := by rw [ect]; exact q.curT
    refine WP.spec_bind (stt_vk hR q hct) fun s1 ⟨w1, k1⟩ => ?_
    have c1 := stt_capk hO q hct w1
    repeat' (refine spec_ite (fun _ => ?_) (fun _ => ?_))
    all_goals
      refine WP.spec_bind (set_cap_frame hR hO hsl0 s1 _ _ _ _ _ _ _ _) fun s2 ⟨k2, c2o, c2x⟩ => ?_
      refine WP.spec_bind (ept.install_s2_leaf.inv hA (P := fun s3 =>
          (∀ x ∈ OS, obj.Slot.cap st x s3 = obj.Slot.cap st x s2) ∧
            ∀ b, VsR kb Pt b → b ≠ wa p o → L.mem s3 b = L.mem s2 b)
          ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩ a lu e (fun s3 v _ ⟨hc3, hm3⟩ => by
            beta_reduce
            rw [hsl]
            refine ⟨fun x hx => by rw [wrv_cap hR hO hv0 x hx, hc3 x hx], fun b hb hne => ?_⟩
            rw [L.mem_wr_ne (hR.al _ hv0) (hR.al b hb) (fun h => hne (UScalar.eq_of_val_eq h).symm),
              hm3 b hb hne]) root asid ipa ptr dev attr) ?_
      rintro ⟨s3, a1⟩ ⟨hc3, hm3⟩
      have hf3 : ∃ p' sz' r' d' m' e' a' v', obj.Slot.cap st slot s3 = ok (.Frame p' sz' r' d' m' e' a' v') := by
        rw [hc3 slot hsl0]; exact c2x
      obtain ⟨n0, n1, n2⟩ := frm_nvs hf3
      refine (WP.spec_ok _).2 (Or.inr (UnmZ.step (kb := kb) (W := fun b => b = wa p o) hsl0 hU hV
        (fun x hx hne => by rw [hc3 x hx, c2o x hx hne, c1 x hx]) n0 (fun p' h => absurd h (n1 p'))
        (fun p' n h => absurd h (n2 p' n)) (fun b hb hn => by rw [hm3 b hb hn, k2 b hb, k1 b hb])
        (fun x hx p' n hu o' ho' h8' he => (UnmZ.words (kb := kb) hU hx hu ho' h8').2.1 (by rw [he]; exact hw))
        (fun b hb => Or.inl hb)))

set_option maxHeartbeats 4000000 in
/-- **ARMPageMap into a Stage-2 VSpace at decode level** (vspace.rs:687–729, 731–788: `decode_frame` at
`ARMPageMap` with a `Frame` cap and an `Ept` cap in the extra slot): the state unchanged, or `ks`, `VsTy`, `S2Ty`
(same ghost sets), `UnmZ`, `UnmU` (`ept.root.ty`, then `ept.map_frame.ty` and `ept.map_frame.unmz`). -/
theorem vspace.decode_frame.map_s2 (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (hO : OSOK T Ω Sg OS) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hk : L.ksb s = kb) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    (hTe : Gran Te bits ⊆ Pt) (hH : HrOK kb Pp Tb Lv Hr) (hS : S2OK Te bits Hr) (hD : S2Pl kb Pp Tb Te bits)
    (hU : UnmZ st OS Pt Te bits s) (hV : UnmU st OS Pp s) (hY : VsTy st kb Pp Tb Lv s)
    (h2 : S2Ty st hPl.ipa Pp Hr Te Re bits s)
    (a : A) (len slot : U64) (call : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hsl : slot ∈ OS) (fp : U64) (fsz : capability.FrameSize) (fr : U64) (fd fm fe : Bool) (fa fv : U64)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → ∃ p l m asid v, obj.Slot.cap st x s = ok (.Ept p l m asid v)) :
    vspace.decode_frame st ar s a fl4_abi.label.ARMPageMap len slot (.Frame fp fsz fr fd fm fe fa fv) call buf extra
      ⦃ r => r.2.1 = s ∨ (L.ksb r.2.1 = kb ∧ VsTy st kb Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
        UnmZ st OS Pt Te bits r.2.1 ∧ UnmU st OS Pp r.2.1) ⦄ := by
  have hS' : P0.StoreTotal st := L.total
  have mf : ∀ (root asid ipa vm attr ptr : U64) (size : capability.FrameSize) (rights : U64) (dev : Bool)
      (masid mvaddr : U64), root ∈ Te → Re root + 1 = s2lv hPl.ipa → s2rb hPl.ipa ≤ bits root →
      ept.map_frame st ar s a root asid ipa vm attr ptr size rights dev masid mvaddr slot ⦃ r => r.2.1 = s ∨
        (L.ksb r.2.1 = kb ∧ VsTy st kb Pp Tb Lv r.2.1 ∧ S2Ty st hPl.ipa Pp Hr Te Re bits r.2.1 ∧
          UnmZ st OS Pt Te bits r.2.1 ∧ UnmU st OS Pp r.2.1) ⦄ :=
    fun root asid ipa vm attr ptr size rights dev masid mvaddr hrT hre hrb =>
      WP.spec_mono (WP.spec_and
        (ept.map_frame.ty hA hPl hR hO q hk hPp hTb hTe hH hS hD hY h2 hrT hre hrb a asid ipa vm attr ptr size
          rights dev masid mvaddr hsl)
        (ept.map_frame.unmz hA hPl hR hO q hTe hS h2 hrT hre hrb hU hV a asid ipa vm attr ptr size rights dev
          masid mvaddr hsl)) fun r ⟨h1, h3⟩ => by
        rcases h1 with e | ⟨hk', hY', h2'⟩
        · exact Or.inl e
        rcases h3 with e | ⟨hU', hV'⟩
        · exact Or.inl e
        exact Or.inr ⟨hk', hY', h2', hU', hV'⟩
  unfold vspace.decode_frame
  simp only [vspace.as_frame, bind_ok]
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct _ => ?_
  refine spec_ite (fun _ => ?_) (fun h => (h (by first | trivial | rfl)).elim)
  unfold vspace.decode_page_map
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct' _ => ?_
  refine WP.spec_bind (vspace.extra.memA extra 0#usize) fun o ho => ?_
  rcases o with _ | x
  · asErr
  obtain ⟨hxm, hx0⟩ := ho x rfl
  obtain ⟨p0, l0, m0, as0, va0, hxc⟩ := hx x hxm hx0
  try dsimp only
  refine spec_ite (fun _ => ?_) (fun _ => by asErr)
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS') fun vaddr _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS') fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS') fun attr _ => ?_
  refine WP.spec_bind (P0.capability.Rights.from_word.p0 _) fun _ _ => ?_
  refine WP.spec_bind (P0.capability.mask_vm_rights.p0 _ _) fun vm _ => ?_
  refine WP.spec_bind (show obj.Slot.cap st x s ⦃ c => c = .Ept p0 l0 m0 as0 va0 ⦄ by
    rw [hxc]; exact (WP.spec_ok _).2 rfl) fun vcap hv => ?_
  subst hv
  refine WP.spec_bind (Pₘ := fun b => b = true) ((WP.spec_ok _).2 rfl) fun b hb => ?_
  refine spec_ite (fun _ => ?_) (fun h => absurd hb h)
  refine WP.spec_bind (ept.root.ty hY h2 hk _ 1#u64) fun r hr => ?_
  rcases r with ⟨root, asid1⟩ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Or.inl rfl)
  obtain ⟨hrT, hre, hrb⟩ := hr _ rfl
  simp only [irq_branch_ok, bind_ok]
  refine spec_ite (fun _ => ?_) (fun _ => mf _ _ _ _ _ _ _ _ _ _ _ hrT hre hrb)
  refine spec_ite (fun _ => mf _ _ _ _ _ _ _ _ _ _ _ hrT hre hrb) (fun _ => by asErr)

end frm

end ST
end R
end W7

end

end Fl4ProofsA64.P1

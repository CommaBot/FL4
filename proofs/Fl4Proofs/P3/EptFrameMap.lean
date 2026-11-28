/-
P3 (line mmuAD, gen 42b12): **the EPT frame map's perform half at `EptCore`** — after P3/EptFrameMapDec's decode,
FL4's `ept::map_frame` (crates/fl4-core/src/ept.rs l. 173-187: the caller's restart, `ex`-slot `set_cap` of the frame
cap `Frame { mapped, is_ept: mapped, asid, vaddr }`, then `s.write(e, val)` of the frame entry) against the extended
spec's `performEptInvocation (.frameMap newCap slot tbl i entry)` (Fl4Spec/Ext/VirtEptInv l. 224-226: `setCap`, then
`storeGuestEntry`), in the style of P3/EptTableMap.

* Spec: **`performFrameMap_eq`** (the perform's single outcome: the CNode slot, then the guest-table object `t` with
  the entry written), `EptFrameMapSpec` (restart, then perform).
* A frame entry is no walk step: **`frame_nw`** (`¬ GWalkE` of the written entry: a 4 KiB frame is written into a
  level-21 table, whose entries are leaves, `eptChild 21 = none`; a 2 MiB frame carries bit 7, `GuestPte.encode`'s
  `ps`, `bit7_or`; the kernel-only entry is 0). So the tables reachable after the write are those before:
  **`GPath.storeNW`** (paths after the write are paths before), and P3/EptLookup's `EptWalk.store` with its new-entry
  obligation vacuous.
* **`EptCore.frameSlot`**: `EptCore` across the frame cap's rewrite in one slot (FL4 `set_cap`, spec `setCap`, a `CnK`
  step): no `Ept` cap changes, the new frame cap's `JExtEpt` obligation (`mapped ∧ is_ept → X ≠ ∅`) holds since the
  written table is in `X`, `dest` held a frame cap so it is no TCB's `SLOT_EPT`.
* **`EptCore.frameEntry`**: `EptCore` across the entry write on both sides (P3/EptStep3's `EptCore.entry`): the
  written table `t` is reached along `GPath` at a nonzero level, so it is not the table of an unmapped `Ept` cap
  (`EptNamed.unmUnreach`), `UnmappedEmpty` kept; `EptWalk` / `EptNamed` kept since the entry is no walk step.

Gen 42b15 (the Architect's `EptVTop` extension to EPT-mapped frame caps, P3/VmState): `EptCore.frameSlot` gains
`hv1 : m1 = true → e1 = true → v1 < 2^47` for the new frame cap (statement changed in place, this line's own).

No named premise; the spec is not touched. New file; root import after `P3.EptFrameMapDec`.
-/
import Fl4Proofs.P3.EptFrameMapDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Spec side -/

section Spec
open Fl4Spec Fl4Proofs.P3.Notif

/-- **The frame map's perform has a single outcome**: the CNode slot rewritten, then entry `i` of `t` written. -/
theorem performFrameMap_eq {σ : State Unit} {pc : ObjRef} {r : Nat} {cs : CnodeContents} {idx : List Bool}
    (hk : σ.kheap pc = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r)
    {t : ObjRef} {l : Nat} {es : BitVec 9 → Word} (ht : σ.kheap t = some (.archObj (.ept l es)))
    (nc : ArchCap) (i : BitVec 9) (e : Word) :
    performEptInvocation (Z := Unit) (.frameMap nc (pc, idx) t i e) σ =
      ({((), updK (setCnodeSlot σ pc r cs idx (.archObjectCap nc)) t (.archObj (.ept l (Function.update es i e))))},
        False) := by
  have htc : t ≠ pc := Endp.kheap_ne ht hk (fun _ h1 h2 => by subst h1; cases h2)
  have ht2 : (setCnodeSlot σ pc r cs idx (.archObjectCap nc)).kheap t = some (.archObj (.ept l es)) := by
    simp [setCnodeSlot, htc, ht]
  have hs : storeGuestEntry (Z := Unit) t i e (setCnodeSlot σ pc r cs idx (.archObjectCap nc)) =
      ({((), updK (setCnodeSlot σ pc r cs idx (.archObjectCap nc)) t
        (.archObj (.ept l (Function.update es i e))))}, False) := by
    unfold storeGuestEntry
    rw [Notif.nd_bind_one (getEpt_eq ht2)]
    exact setObject_eq ht2 rfl
  unfold performEptInvocation
  dsimp only
  rw [Notif.nd_bind_one (setCap_cnode _ hk hwf hidx)]
  exact hs

/-- The spec after the frame map's decode: `set_thread_state cur Restart`, then the perform, with the single outcome
`σ'`. -/
def EptFrameMapSpec (σ : State Unit) (nc : ArchCap) (sl : CslotPtr) (t : ObjRef) (i : BitVec 9) (e : Word)
    (σ' : State Unit) : Prop :=
  (setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
    performEptInvocation (.frameMap nc sl t i e)) σ = ({((), σ')}, False)

end Spec

/-! ## A frame entry is no walk step -/

/-- An entry with bit 7 set is not a walk step. -/
theorem bit7_or (x y : Fl4Spec.Word) : ((x ||| 128) ||| y) &&& 128 ≠ 0 := by
  intro h
  have h7 : (128 : Fl4Spec.Word).getLsbD 7 = true := by decide
  have e : (((x ||| 128) ||| y) &&& 128).getLsbD 7 = true := by
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, h7, Bool.or_true, Bool.true_or, Bool.and_self]
  rw [h] at e
  simp at e

/-- A large frame's entry has bit 7 (`GuestPte.encode`'s `ps`). -/
theorem encode_large_bit7 (k : Fl4Spec.VirtKind) (p : Fl4Spec.Paddr) (w : Bool) (mt : Fl4Spec.Word) :
    Fl4Spec.GuestPte.encode k (.frame p true w mt) &&& 128 ≠ 0 := by
  unfold Fl4Spec.GuestPte.encode
  simp only [↓reduceIte]
  by_cases hk : k = .svm
  · rw [if_pos hk]; exact bit7_or _ _
  · rw [if_neg hk]; exact bit7_or _ _

/-- **The frame map's entry is no walk step** (module docstring): at the table level the decode found
(`lkLvl (fbits size)`, not for `Huge`). -/
theorem frame_nw {size : capability.FrameSize} (hH : size ≠ .Huge) (R : Fl4Spec.VMRights) (p : Fl4Spec.ObjRef)
    (attr : Fl4Spec.Word) (es0 : BitVec 9 → Fl4Spec.Word) (i : BitVec 9) :
    ¬ GWalkE (lkLvl (fbits size).val)
      (Function.update es0 i (specFrameEntry R p (frameSizeOf size = .x64LargePage) attr)) i := by
  rintro ⟨h1, -, h3, h4⟩
  rw [Function.update_self] at h3 h4
  cases size with
  | Small => exact absurd h1 (by decide)
  | Huge => exact hH rfl
  | Large =>
    have hd : decide (frameSizeOf capability.FrameSize.Large = Fl4Spec.VMPageSize.x64LargePage) = true := by decide
    rw [hd] at h3 h4
    unfold specFrameEntry at h3 h4
    by_cases hk : R = Fl4Spec.vmKernelOnly
    · rw [if_pos hk] at h3; exact h3 (by decide)
    · rw [if_neg hk] at h4; exact encode_large_bit7 _ _ _ _ h4

/-- **Paths after writing an entry that is no walk step are paths before** (the other objects and the ASID table
kept). -/
theorem GPath.storeNW {σ σ' : Fl4Spec.State Unit} {tb : Fl4Spec.ObjRef} {l0 : Nat} {es0 : BitVec 9 → Fl4Spec.Word}
    (hk : σ.kheap tb = some (.archObj (.ept l0 es0))) {i : BitVec 9} {e : Fl4Spec.Word}
    (hk' : σ'.kheap tb = some (.archObj (.ept l0 (Function.update es0 i e))))
    (hoth : ∀ r, r ≠ tb → σ'.kheap r = σ.kheap r)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hnw : ¬ GWalkE l0 (Function.update es0 i e) i)
    {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex} {gpa : Fl4Spec.Word} {l : Nat}
    {u : Fl4Spec.ObjRef} (h : GPath σ' hi lo gpa l u) : GPath σ hi lo gpa l u := by
  induction h with
  | root hp h1 =>
    obtain ⟨p, f, g1, g2, g3⟩ := hp
    have hpt : p ≠ tb := fun e' => by subst e'; rw [hk'] at g2; cases g2
    exact .root ⟨p, f, by rw [← hat]; exact g1, by rw [← hoth p hpt]; exact g2, g3⟩ h1
  | @step l c t es _ hkt hc hw ih =>
    by_cases htb : t = tb
    · subst htb
      rw [hk'] at hkt
      injection hkt with hkt; injection hkt with hkt; injection hkt with hl hes; subst hl; subst hes
      by_cases hji : Fl4Spec.guestIndex gpa c = i
      · rw [hji] at hw; exact absurd hw hnw
      · have hw0 : GWalkE l0 es0 (Fl4Spec.guestIndex gpa c) := by
          obtain ⟨a1, a2, a3, a4⟩ := hw
          rw [Function.update_of_ne hji] at a3 a4
          exact ⟨a1, a2, a3, a4⟩
        rw [Function.update_of_ne hji]
        exact .step ih hk hc hw0
    · rw [hoth t htb] at hkt
      exact .step ih hkt hc hw

/-! ## `EptCore` across the frame map -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

/-- **`EptCore` across the frame cap's rewrite in one slot** (module docstring): FL4's writes miss the tables of `X`,
`dest` holds a frame cap before and after, every other slot kept; the spec's step is a `CnK` step. -/
theorem EptCore.frameSlot (C : EptCore (L := L) X XL th s σ) {s' : S} {σ' : Fl4Spec.State Unit} {t : U64}
    (ht : t ∈ X) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val)
    {dest : U64} {p0 a0 v0 r0 : U64} {sz0 : capability.FrameSize} {d0 m0 e0 : Bool}
    (hdc : capV (L.mem s) dest = .Frame p0 sz0 r0 d0 m0 e0 a0 v0)
    {p1 a1 v1 r1 : U64} {sz1 : capability.FrameSize} {d1 m1 e1 : Bool}
    (hcap' : capV (L.mem s') dest = .Frame p1 sz1 r1 d1 m1 e1 a1 v1)
    (hv1 : m1 = true → e1 = true → v1.val < 2 ^ 47)
    (hcp : ∀ y, IsSlot th y → y ≠ dest → capV (L.mem s') y = capV (L.mem s) y)
    (hcn : Ipc.CnK σ σ') : EptCore (L := L) X XL th s' σ' := by
  have hcpE : ∀ y, IsSlot th y → ∀ p l a v (mm : Bool), capV (L.mem s') y = .Ept p l mm a v →
      IsSlot th y ∧ capV (L.mem s) y = .Ept p l mm a v := by
    intro y hy p l a v mm hc
    by_cases e : y = dest
    · rw [e, hcap'] at hc; cases hc
    · exact ⟨hy, by rw [← hcp y hy e]; exact hc⟩
  refine C.frame hw hW hcpE ⟨fun y hy => ?_, ⟨fun y hy p l a v hc => C.exte.vtop.1 y hy p l a v (hcpE y hy p l a v true hc).2,
    fun y hy p sz r d a v hc => ?_⟩, fun y hy p l a v hc => C.exte.anz y hy p l a v (hcpE y hy p l a v true hc).2⟩
    (fun u hu => ?_) (fun r l es hk => ⟨l, es, (cnK_arch hcn).1 hk⟩)
    (cnK_entry hcn) (cnK_size hcn) (fun t' ht' => ?_) ?_
  · by_cases e : y = dest
    · rw [e, hcap']; exact fun _ => ⟨t, ht⟩
    · rw [hcp y hy e]; exact C.exte.cap y hy
  · by_cases e : y = dest
    · rw [e, hcap'] at hc
      obtain ⟨-, -, -, -, rfl, rfl, -, rfl⟩ := capability.Cap.Frame.inj hc
      exact hv1 rfl rfl
    · rw [hcp y hy e] at hc; exact C.exte.vtop.2 y hy p sz r d a v hc
  · obtain ⟨es, hk, -⟩ := C.rel.obj u hu
    rw [hk]; exact (cnK_arch hcn).2 hk
  · by_cases e : cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 5) = dest
    · exfalso
      rcases C.eslot t' ht' with h | ⟨p, a, v, h⟩ <;> rw [e, hdc] at h <;> cases h
    · exact Or.inr (Or.inr ⟨ht', hcp _ (isSlot_eptSlot ht') e⟩)
  · refine (C.named.cnK hcn).frameA rfl (fun _ _ _ h _ => h) (fun _ _ _ h => h)
      (fun y p lv a v hy hc _ => ?_) (fun y p lv mm a v hy hc => ⟨y, (hcpE y hy p lv a v mm hc).1,
        (hcpE y hy p lv a v mm hc).2⟩)
    have hyd : y ≠ dest := fun e => by rw [e, hdc] at hc; cases hc
    exact ⟨y, hy, by rw [hcp y hy hyd]; exact hc⟩

set_option maxHeartbeats 4000000 in
/-- **`EptCore` across a non-walk entry write on both sides, at any level** (gen 42b14: `frameEntry` generalised in
place, its `hXt0 : XL t ≠ 0` dropped — the table unmap writes 0 into the root at level 39; a root `t` is no unmapped
cap's table by `UnmappedEmpty`'s pool clause): the table `t ∈ X` reached along `(hi, lo, g)`, an entry that is no
walk step, FL4's write the entry word only, every slot kept, the spec's step `storeGuestEntry` (other objects and the
ASID table kept). -/
theorem EptCore.frameEntryG (C : EptCore (L := L) X XL th s σ) {s' : S} {σ' : Fl4Spec.State Unit} {t : U64}
    (ht : t ∈ X) {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex} {g : Fl4Spec.Word}
    (hg : g.toNat < 2 ^ 47) (hp : GPath σ hi lo g (XL t) t.bv)
    {es0 : BitVec 9 → Fl4Spec.Word} (hk0 : σ.kheap t.bv = some (.archObj (.ept (XL t) es0)))
    {i : BitVec 9} {e : Fl4Spec.Word} (hnw : ¬ GWalkE (XL t) (Function.update es0 i e) i)
    (hw : P1.WritesIn st s s' (· = eptA t i)) (hwd : EptWord Fl4Spec.virtKind (L.mem s' (eptA t i)).bv e)
    (hk1 : σ'.kheap t.bv = some (.archObj (.ept (XL t) (Function.update es0 i e))))
    (hoth : ∀ r, r ≠ t.bv → σ'.kheap r = σ.kheap r)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hSS : SlotsSame th (L.mem s) (L.mem s')) : EptCore (L := L) X XL th s' σ' := by
  have hge1 : ∀ x, GuestEntry σ' x → GuestEntry σ x := by
    rintro x ⟨hi', q, f, lo', h1, h2, h3⟩
    have hq : q ≠ t.bv := fun e' => by subst e'; rw [hk1] at h2; cases h2
    exact ⟨hi', q, f, lo', by rw [← hat]; exact h1, by rw [← hoth q hq]; exact h2, h3⟩
  have hpt : ∀ y p l a v, IsSlot th y → capV (L.mem s) y = .Ept p l false a v → p ≠ t := by
    intro y p l a v hy hc e'
    by_cases h0 : XL t = 0
    · rw [h0] at hp
      obtain ⟨e0, he0, h1, hr⟩ := hp.zero
      exact (C.ue y hy p l a v hc).2.2.2 e0 he0.guest h1 (by rw [e', hr])
    · exact C.named.unmUnreach hy hc hi lo g (XL t) hg h0 (by rw [e']; exact hp)
  have hxk : ∀ u ∈ X, u ≠ t → σ'.kheap u.bv = σ.kheap u.bv :=
    fun u _ hne => hoth _ (fun h => hne (P1.eq_of_bv h))
  refine C.entry ht hk0 hw (fun b hb => Or.inl hb) hwd hk1 hxk
    (fun y hy p l a v mm hc => ⟨y, a, v, mm, hy, by rw [← hSS.capV hy]; exact hc⟩)
    (C.exte.of_eq fun y hy => hSS.capV hy) (fun r l es hk => ?_) hge1 (fun o ko' ho => ?_) ?_
    (EptSlotStep.ofSS hSS) (EptWalk.store C.walk hk0 hk1 hoth hge1 (fun h => absurd h hnw)) ?_
  · by_cases hr : r = t.bv
    · subst hr; exact ⟨_, _, hk0⟩
    · rw [hoth r hr] at hk; exact ⟨l, es, hk⟩
  · by_cases hr : o = t.bv
    · subst hr
      rw [hk1] at ho; cases ho
      exact ⟨_, hk0, by rw [ept_bits, ept_bits]⟩
    · exact ⟨ko', by rw [← hoth o hr]; exact ho, rfl⟩
  · -- `UnmappedEmpty` after: the written table is no unmapped cap's table
    intro y hy p l a v hc
    rw [hSS.capV hy] at hc
    have hpX : p ∈ X := by have h := C.exte.cap y hy; rw [hc] at h; exact h
    obtain ⟨h1, h2, h3, h4⟩ := C.ue y hy p l a v hc
    have hpt' : p ≠ t := hpt y p l a v hy hc
    refine ⟨fun j => ?_, by rw [hxk p hpX hpt']; exact h2, fun y' hy' hne l' mm a' v' hc' =>
      h3 y' hy' hne l' mm a' v' (by rw [← hSS.capV hy']; exact hc'), fun e he h1' => h4 e (hge1 e he) h1'⟩
    have hpl := C.rel.place p hpX
    have e1 := eptA_val hpl.2 j
    have hi9 := j.isLt
    rw [hw.mem_eq (b := eptA p j) (by unfold P1.Aligned; rw [e1]; omega)
      (fun hb => hpt' (C.eptA_inj hpX ht (congrArg UScalar.val hb)).1)]
    exact h1 j
  · -- `EptNamed` after: paths after are paths before, every slot kept
    refine C.named.keep (fun hi' lo' gpa l u hp' _ => GPath.storeNW hk0 hk1 hoth hat hnw hp')
      (C.named.inj.mono hat fun hi' lo' e0 ⟨q, f, g1, g2, g3⟩ _ => ?_)
      (fun y p lv a v hy hc _ => ⟨y, hy, by rw [hSS.capV hy]; exact hc⟩)
      (fun y p lv mm a v hy hc => Or.inl ⟨y, hy, by rw [← hSS.capV hy]; exact hc⟩)
    have hq : q ≠ t.bv := fun e' => by subst e'; rw [hk1] at g2; cases g2
    exact ⟨q, f, by rw [← hat]; exact g1, by rw [← hoth q hq]; exact g2, g3⟩

/-- **`EptCore` across the frame entry's write on both sides** (module docstring): the table `t ∈ X` reached along
`(hi, lo, g)` at its nonzero level, an entry that is no walk step, FL4's write the entry word only, every slot kept,
the spec's step `storeGuestEntry` (other objects and the ASID table kept). Gen 42b14: the corollary of
`EptCore.frameEntryG`. -/
theorem EptCore.frameEntry (C : EptCore (L := L) X XL th s σ) {s' : S} {σ' : Fl4Spec.State Unit} {t : U64}
    (ht : t ∈ X) (hXt0 : XL t ≠ 0) {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex} {g : Fl4Spec.Word}
    (hg : g.toNat < 2 ^ 47) (hp : GPath σ hi lo g (XL t) t.bv)
    {es0 : BitVec 9 → Fl4Spec.Word} (hk0 : σ.kheap t.bv = some (.archObj (.ept (XL t) es0)))
    {i : BitVec 9} {e : Fl4Spec.Word} (hnw : ¬ GWalkE (XL t) (Function.update es0 i e) i)
    (hw : P1.WritesIn st s s' (· = eptA t i)) (hwd : EptWord Fl4Spec.virtKind (L.mem s' (eptA t i)).bv e)
    (hk1 : σ'.kheap t.bv = some (.archObj (.ept (XL t) (Function.update es0 i e))))
    (hoth : ∀ r, r ≠ t.bv → σ'.kheap r = σ.kheap r)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hSS : SlotsSame th (L.mem s) (L.mem s')) : EptCore (L := L) X XL th s' σ' :=
  C.frameEntryG ht hg hp hk0 hnw hw hwd hk1 hoth hat hSS

end

end

end Fl4Proofs.P3

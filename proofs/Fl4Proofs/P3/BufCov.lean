/-
P3 (DESIGN.md §9), IPC: **the user-memory cover of `B` and the zero free
ranges** (handoff/glob.md decisions 3/4): the two invariants to be carried
with `JAtZ` (after the VSpace line's `vsc` field), stated and with their
per-step lemmas, before any `JAtZ` edit.

* `FrameCover B σ`: every 8-aligned word of every non-device user-data
  object of the spec is a pair `(a, a)` of `B` (l4v: user memory is the
  shared `machine_state`; here the FL4/spec user-memory relation lives at
  `B`, `IpcRel.buf`).
* `bufCover_of_frameCover`: `BufCover` from `IpcBufCapOK` (the buffer's words
  in user frames, `inUserFrame`) and `FrameCover`: JEntryGlob's `bufCover`
  becomes a consequence.
* `FrameCover.step` (the data pages after are the ones before or new ones
  whose words are in the new `B`), `FrameCover.keep` (no new page, `B`
  growing), `FrameCover.sdrop` (the detype: `KeepB KB B` with the kept
  pages' words satisfying `KB`; `KBOf` for the drop).
* `UtZero mem G σ` (l4v `untyped_ranges_zero`): the spec's memory is zero in
  the free part `[p + fi, p + 2^sb)` of every RAM untyped cap of the MDB
  slots.
* `UtZero.step`: across a step whose untyped caps after are caps before with
  the free index not lower (retype), or whose free part is zero after
  (reset), and whose memory changes only outside the free parts or to zero.
* `UtZero.store`: a spec word store (`storeMem`) at a word outside every free
  part; `freeOut_of_obj`: a word inside a spec object is outside every free
  part (`SpecFree`): the user-memory writes of the IPC code (buffer words of
  live frames).
* The detype (decision 4): `Endp.IpcBufCapOK.sdrop` (the region's data
  pages inside it, no kept TCB's buffer word in it); `FrameOffJ` (no slot's
  frame cap meets the region: `RegionUnrefJ`'s new clause, l4v
  `untyped_mdb` / `descendants_range`), `JAtZ.bufOffJ` (a TCB's buffer words
  miss such a region, as `JAtZ.bufWord`), `JAtZ.ipcBufDrop`.
* `UtZero.zero_at`, `loadWordAt_zero`: the retype's new frame words read 0 in
  the spec (FL4 zeroes them, `UtCapP3.zero`), so `IpcRel.buf` holds at the
  words `B` gains.
-/
import Fl4Proofs.P3.BufInv
import Fl4Proofs.P3.XTopJointData
import Fl4Proofs.P3.UtDropSets
import Fl4Proofs.P3.UtDropSpec
import Fl4Proofs.P3.UtDropX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-! ## `FrameCover` -/

section Cover
open Fl4Spec

/-- **`B` covers the user frames** (module docstring). -/
def FrameCover (B : Set (U64 × Word)) (σ : State Unit) : Prop :=
  ∀ q vms, σ.kheap q = some (.archObj (.dataPage false vms)) → ∀ a : U64, q.toNat ≤ a.val →
    a.val < q.toNat + 2 ^ pageBitsForSize vms → a.val % 8 = 0 → (a, a.bv) ∈ B

/-- The words of an aligned buffer in an aligned page are 8-aligned. -/
theorem bufAddr_al8 (vms : VMPageSize) (pb tb : BitVec 64) (k : Nat) (hk : k < 128)
    (hpb : pb.toNat % 2 ^ pageBitsForSize vms = 0) (htb : tb.toNat % 1024 = 0) :
    (Endp.bufAddr (pb + (tb &&& mask (pageBitsForSize vms))) k).toNat % 8 = 0 := by
  have hm := Endp.pageBits_mem vms
  set b := pageBitsForSize vms with hbdef
  have hb : 12 ≤ b ∧ b ≤ 30 := by simp at hm; omega
  have h2b : 1024 ∣ 2 ^ b := by
    have : 2 ^ 10 ∣ 2 ^ b := Nat.pow_dvd_pow 2 (by omega)
    simpa using this
  have h8 : 8 ∣ 2 ^ b := by
    have : 2 ^ 3 ∣ 2 ^ b := Nat.pow_dvd_pow 2 (by omega)
    simpa using this
  have hpos : 0 < 2 ^ b := by positivity
  have hpbL := pb.isLt
  have htbL := tb.isLt
  have hoff := Endp.mask_toNat' b hm tb
  have hoff1 : tb.toNat % 2 ^ b % 1024 = 0 := by
    rw [Nat.mod_mod_of_dvd _ h2b]; exact htb
  have hpb8 : pb.toNat % 8 = 0 := by rw [← Nat.mod_mod_of_dvd _ h8, hpb]
  unfold Endp.bufAddr
  rw [BitVec.toNat_add, BitVec.toNat_add, hoff, BitVec.toNat_ofNat]
  have hk8 : k * wordSize % 2 ^ 64 = k * 8 := by
    simp only [wordSize]; omega
  rw [hk8]
  have hoff2 : tb.toNat % 2 ^ b < 2 ^ 64 := by omega
  omega

/-- **`BufCover` from `IpcBufCapOK` and `FrameCover`.** -/
theorem bufCover_of_frameCover {T : Set U64} {B : Set (U64 × Word)} {σ : State Unit}
    (hO : Endp.IpcBufCapOK σ) (hF : FrameCover B σ) : Endp.BufCover T B σ := by
  intro t _ x b q hk hq w hw i hi
  unfold Endp.ipcBufOf at hq
  split at hq
  · rename_i dev pb R mt vms md he
    split_ifs at hq with hc
    cases hq
    have hro : vmReadOnly ⊆ R := by
      rcases hc with h | ⟨h, -⟩
      · exact fun z hz => h (by unfold vmReadOnly vmReadWrite at *; simp at hz ⊢; simp [hz])
      · exact h
    obtain ⟨-, -, hd, ha, hpa⟩ := hO t.bv x hk dev pb R mt vms md he hro
    have hbv : (Endp.fl4BufA w i).bv = Endp.bufAddr (pb + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) i.val := by
      rw [fl4BufA_bv, hw]
    have hval : (Endp.fl4BufA w i).val =
        (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) i.val).toNat := by
      rw [← hbv]; rfl
    obtain ⟨sz, hsz⟩ := hd i.val hi
    have hn := Endp.and_not_mask_toNat (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) i.val) _
      (Endp.pageBits_mem sz)
    have hpos : 0 < 2 ^ pageBitsForSize sz := by positivity
    have hlo := Nat.div_mul_le_self (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) i.val).toNat
      (2 ^ pageBitsForSize sz)
    have hhi := Nat.lt_div_mul_add
      (a := (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) i.val).toNat) hpos
    have h8 := bufAddr_al8 vms pb x.tcbIpcBuffer i.val hi hpa ha
    have hm := hF _ sz hsz (Endp.fl4BufA w i) (by rw [hn, hval]; exact hlo) (by rw [hn, hval]; exact hhi)
      (by rw [hval]; exact h8)
    rw [hbv] at hm; exact hm
  · cases hq

variable {B B' : Set (U64 × Word)} {σ σ' : State Unit}

/-- **`FrameCover` across a step** (module docstring). -/
theorem FrameCover.step (h : FrameCover B σ) (hB : B ⊆ B')
    (hnew : ∀ q vms, σ'.kheap q = some (.archObj (.dataPage false vms)) →
      σ.kheap q = some (.archObj (.dataPage false vms)) ∨
      ∀ a : U64, q.toNat ≤ a.val → a.val < q.toNat + 2 ^ pageBitsForSize vms → a.val % 8 = 0 → (a, a.bv) ∈ B') :
    FrameCover B' σ' := by
  intro q vms hq a h1 h2 h3
  rcases hnew q vms hq with e | e
  · exact hB (h q vms e a h1 h2 h3)
  · exact e a h1 h2 h3

/-- `FrameCover` across a step adding no data page. -/
theorem FrameCover.keep (h : FrameCover B σ) (hB : B ⊆ B')
    (hpg : ∀ q vms, σ'.kheap q = some (.archObj (.dataPage false vms)) →
      σ.kheap q = some (.archObj (.dataPage false vms))) : FrameCover B' σ' :=
  h.step hB fun q vms hq => Or.inl (hpg q vms hq)

/-- `FrameCover` at the same objects. -/
theorem FrameCover.of_kheap (h : FrameCover B σ) (hk : σ'.kheap = σ.kheap) : FrameCover B σ' :=
  h.keep (fun _ h => h) fun q vms hq => by rw [← hk]; exact hq

/-- **`FrameCover` across the detype** (`SDrop`): the kept words `KeepB KB B`,
the pages outside the region with their words satisfying `KB`. -/
theorem FrameCover.sdrop {Rg : ObjRef → Prop} {KB : U64 × Word → Prop} (h : FrameCover B σ) (hD : SDrop Rg σ σ')
    (hkb : ∀ q vms, σ.kheap q = some (.archObj (.dataPage false vms)) → ¬ Rg q → ∀ a : U64, q.toNat ≤ a.val →
      a.val < q.toNat + 2 ^ pageBitsForSize vms → a.val % 8 = 0 → KB (a, a.bv)) :
    FrameCover (KeepB KB B) σ' := by
  intro q vms hq a h1 h2 h3
  by_cases hr : Rg q
  · rw [hD.kin q hr] at hq; cases hq
  · rw [hD.kout q hr] at hq
    exact ⟨h q vms hq a h1 h2 h3, hkb q vms hq hr a h1 h2 h3⟩

end Cover

/-! ## `UtZero` (l4v `untyped_ranges_zero`) -/

section Zero
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
open Fl4Spec

/-- **The free parts of the RAM untyped caps are zero in the spec's memory**
(module docstring). -/
def UtZero (mem : U64 → U64) (G : MdbGhost) (σ : State Unit) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV mem x = .Untyped p sb fi false →
    ∀ a : Word, p.val + fi.val ≤ a.toNat → a.toNat < p.val + 2 ^ sb.val → σ.machineState.underlyingMemory a = 0

variable {mem mem' : U64 → U64} {G G' : MdbGhost} {σ σ' : State Unit}

/-- **`UtZero` across a step** (module docstring): each RAM untyped cap after
is one before with a free index at most its own (the memory changing in its
free part only to zero), or its free part is zero after. -/
theorem UtZero.step (h : UtZero mem G σ)
    (hc : ∀ x ∈ G'.chains.flatten, ∀ p sb fi, capV mem' x = .Untyped p sb fi false →
      (∃ y ∈ G.chains.flatten, ∃ fi0 : U64, capV mem y = .Untyped p sb fi0 false ∧ fi0.val ≤ fi.val ∧
        ∀ a : Word, p.val + fi.val ≤ a.toNat → a.toNat < p.val + 2 ^ sb.val →
          σ'.machineState.underlyingMemory a = σ.machineState.underlyingMemory a ∨
          σ'.machineState.underlyingMemory a = 0) ∨
      ∀ a : Word, p.val + fi.val ≤ a.toNat → a.toNat < p.val + 2 ^ sb.val → σ'.machineState.underlyingMemory a = 0) :
    UtZero mem' G' σ' := by
  intro x hx p sb fi hcx a h1 h2
  rcases hc x hx p sb fi hcx with ⟨y, hy, fi0, hcy, hle, hum⟩ | hz
  · rcases hum a h1 h2 with e | e
    · rw [e]; exact h y hy p sb fi0 hcy a (by omega) h2
    · exact e
  · exact hz a h1 h2

/-- `UtZero` at the same caps and memory. -/
theorem UtZero.same (h : UtZero mem G σ) (hG : ∀ x ∈ G'.chains.flatten, x ∈ G.chains.flatten)
    (hcap : ∀ x ∈ G'.chains.flatten, capV mem' x = capV mem x)
    (hum : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory) : UtZero mem' G' σ' :=
  h.step fun x hx p sb fi hcx => Or.inl ⟨x, hG x hx, fi, by rw [← hcap x hx]; exact hcx, le_rfl,
    fun a _ _ => Or.inl (by rw [hum])⟩

/-- **A word store outside every free part keeps `UtZero`.** -/
theorem UtZero.store (h : UtZero mem G σ) {w : Word} (v : Word) (hw : w.toNat + 8 ≤ 2 ^ 64)
    (hout : ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV mem x = .Untyped p sb fi false →
      w.toNat + 8 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ w.toNat) :
    UtZero mem G (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory w v)) := by
  intro x hx p sb fi hcx a h1 h2
  show Endp.storeMem σ.machineState.underlyingMemory w v a = 0
  rw [Endp.storeMem_other]
  · exact h x hx p sb fi hcx a h1 h2
  · intro y hy e
    have hv : a.toNat = w.toNat + y.toNat := by
      rw [e, BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    rcases hout x hx p sb fi hcx with g | g <;> omega

/-- **A word inside a spec object is outside every free part** (`SpecFree`). -/
theorem freeOut_of_obj (hF : Sched.SpecFree mem G σ) {w : Word} {o : ObjRef} {ko : KernelObject}
    (hk : σ.kheap o = some ko) (h1 : o.toNat ≤ w.toNat) (h2 : w.toNat + 8 ≤ o.toNat + 2 ^ objBits ko) :
    ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV mem x = .Untyped p sb fi false →
      w.toNat + 8 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ w.toNat := by
  intro x hx p sb fi hcx
  rcases hF x hx p sb fi hcx o ko hk with (g | g) | ⟨g1, g2⟩ <;> omega

/-- **The free part reads zero** (the retype's new objects). -/
theorem UtZero.zero_at (h : UtZero mem G σ) {x : U64} (hx : x ∈ G.chains.flatten) {p sb fi : U64}
    (hcx : capV mem x = .Untyped p sb fi false) {a : Word} (h1 : p.val + fi.val ≤ a.toNat)
    (h2 : a.toNat < p.val + 2 ^ sb.val) : σ.machineState.underlyingMemory a = 0 :=
  h x hx p sb fi hcx a h1 h2

end Zero

/-! ## The detype: no IPC buffer in the dropped region -/

section Drop
open Fl4Spec

theorem andNot_bounds (a : Word) (sz : VMPageSize) :
    (a &&& ~~~(mask (pageBitsForSize sz) : BitVec 64)).toNat ≤ a.toNat ∧
      a.toNat < (a &&& ~~~(mask (pageBitsForSize sz) : BitVec 64)).toNat + 2 ^ pageBitsForSize sz := by
  have hn := Endp.and_not_mask_toNat a _ (Endp.pageBits_mem sz)
  have hpos : 0 < 2 ^ pageBitsForSize sz := by positivity
  rw [hn]
  exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add hpos⟩

/-- **`IpcBufCapOK` across the detype** (`SDrop`): the region's data pages lie
in the region (`hpg`, no straddle), and no kept TCB's IPC buffer word lies in
the region (`hoff`, from `FrameOffJ` by `JAtZ.bufOffJ`). -/
theorem _root_.Fl4Proofs.P3.Endp.IpcBufCapOK.sdrop {Rg : ObjRef → Prop} {σ σ' : State Unit}
    (h : Endp.IpcBufCapOK σ) (hD : SDrop Rg σ σ')
    (hpg : ∀ q vms, σ.kheap q = some (.archObj (.dataPage false vms)) → Rg q → ∀ a : Word, q.toNat ≤ a.toNat →
      a.toNat < q.toNat + 2 ^ pageBitsForSize vms → Rg a)
    (hoff : ∀ t x, σ.kheap t = some (.tcb x) → ¬ Rg t → ∀ dev p R mt vms md,
      x.tcbIpcframe = .archObjectCap (.pageCap dev p R mt vms md) → vmReadOnly ⊆ R → ∀ k, k < 128 →
        ¬ Rg (Endp.bufAddr (p + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) k)) :
    Endp.IpcBufCapOK σ' := by
  intro t x hx dev p R mt vms md hf hR
  by_cases hr : Rg t
  · rw [hD.kin t hr] at hx; cases hx
  rw [hD.kout t hr] at hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := h t x hx dev p R mt vms md hf hR
  refine ⟨h1, h2, fun k hk => ?_, h4, h5⟩
  obtain ⟨sz, hsz⟩ := h3 k hk
  obtain ⟨g1, g2⟩ := andNot_bounds (Endp.bufAddr (p + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) k) sz
  by_cases hb : Rg (Endp.bufAddr (p + (x.tcbIpcBuffer &&& mask (pageBitsForSize vms))) k &&&
      ~~~(mask (pageBitsForSize sz) : BitVec 64))
  · exact absurd (hpg _ sz hsz hb _ g1 g2) (hoff t x hx hr dev p R mt vms md hf hR k hk)
  · exact ⟨sz, by rw [hD.kout _ hb]; exact hsz⟩

end Drop

section DropJ
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **No frame cap of the typed heap's slots meets `[lo, hi)`** (decision 4:
`RegionUnrefJ`'s new clause at the drop's state; l4v `untyped_mdb` /
`descendants_range`: a childless untyped cap's region is named by no cap). -/
def FrameOffJ (th : TypedHeap) (mem : U64 → U64) (lo hi : Nat) : Prop :=
  ∀ x, IsSlot th x → ∀ q sz r d m ep asid va, capV mem x = .Frame q sz r d m ep asid va →
    topF (.Frame q sz r d m ep asid va) < lo ∨ hi ≤ baseF (.Frame q sz r d m ep asid va)

set_option maxHeartbeats 8000000 in
/-- **A TCB's IPC-buffer words miss `[lo, hi)`** under `FrameOffJ` (the
frame cap in its buffer slot, `StateRel.bufCap`, as `JAtZ.bufWord`). -/
theorem JAtZ.bufOffJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {lo hi : Nat}
    (hFO : FrameOffJ Z.th (L.mem s) lo hi) {t : U64} (ht : Z.th t = some .tcb) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) {dev pb R mt vms md}
    (he : x.tcbIpcframe = .archObjectCap (.pageCap dev pb R mt vms md))
    (hpa : pb.toNat % 2 ^ Fl4Spec.pageBitsForSize vms = 0) (ha : x.tcbIpcBuffer.toNat % 1024 = 0)
    {k : Nat} (hk128 : k < 128) :
    (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k).toNat + 8 ≤ lo ∨
      hi ≤ (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k).toNat := by
  obtain ⟨r1, r2, r3⟩ := buf_frame_rng vms pb x.tcbIpcBuffer k hk128 hpa ha
  obtain ⟨x', c, hkx, hcap, hcr⟩ := J.xtop.rel.2.1.1.bufCap ht
  rw [hk] at hkx; cases hkx
  rw [he] at hcr
  obtain ⟨-, h2⟩ := hcr
  cases c <;> try (simp [absCap] at h2; done)
  case Frame p0 sz r0 d0 m0 ep0 as0 va0 =>
    simp only [absCap] at h2
    injection h2 with h2
    injection h2 with _ hp0 _ _ hsz _
    have hsl : IsSlot Z.th (slotOf t 2) := ⟨t, 2, Or.inr ⟨ht, by simp [tcbSlots]⟩, rfl⟩
    have hcv : capV (L.mem s) (slotOf t 2) = .Frame p0 sz r0 d0 m0 ep0 as0 va0 := capV_of_capAt hcap
    obtain ⟨bs, ts⟩ := frame_range p0 sz r0 d0 m0 as0 va0 ep0
    have hm := Endp.pageBits_mem vms
    have hbits : (fbitsF sz).val = Fl4Spec.pageBitsForSize vms := by rw [fbitsF_val, hsz]
    have hmk : (maskF (fbitsF sz)).val = 2 ^ Fl4Spec.pageBitsForSize vms - 1 := by
      rw [maskF_val (by rw [hbits]; simp at hm; omega), hbits]
    have hpv : p0.val = pb.toNat := by rw [← hp0]; rfl
    have hpos : 0 < 2 ^ Fl4Spec.pageBitsForSize vms := by positivity
    have htop : topF (.Frame p0 sz r0 d0 m0 ep0 as0 va0) = p0.val + 2 ^ Fl4Spec.pageBitsForSize vms - 1 := by
      rw [ts]
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hmk]
      omega
    rcases hFO _ hsl _ _ _ _ _ _ _ _ hcv with e | e
    · rw [htop] at e; left; omega
    · rw [bs] at e; right; omega

/-- **`IpcBufCapOK` after the drop of an untyped region at `J`**: `FrameOffJ`
at the region (decision 4's clause) and the region's data pages inside it
(`hpg`). -/
theorem JAtZ.ipcBufDrop (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hOK : Endp.IpcBufCapOK σ)
    {p sb : U64} (hsb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (hFO : FrameOffJ Z.th (L.mem s) p.val (p.val + 2 ^ sb.val)) {σ' : Fl4Spec.State Unit}
    (hD : SDrop (RgOf p sb) σ σ')
    (hpg : ∀ q vms, σ.kheap q = some (.archObj (.dataPage false vms)) → RgOf p sb q → ∀ a : Fl4Spec.Word,
      q.toNat ≤ a.toNat → a.toNat < q.toNat + 2 ^ Fl4Spec.pageBitsForSize vms → RgOf p sb a) :
    Endp.IpcBufCapOK σ' := by
  refine hOK.sdrop hD hpg fun t x hk _ dev pb R mt vms md he hR k hk128 hin => ?_
  obtain ⟨t', ht', rfl⟩ := J.obj.tcb t x hk
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hth : Z.th t' = some .tcb := (hJ.tcb t').2 (J.zH.1 t' ht')
  obtain ⟨-, -, -, ha, hpa⟩ := hOK t'.bv x hk dev pb R mt vms md he hR
  have e := J.bufOffJ hFO hth hk he hpa ha hk128
  have hr := (rgOf_iff hsb hfit ⟨Endp.bufAddr (pb + (x.tcbIpcBuffer &&& Fl4Spec.mask
    (Fl4Spec.pageBitsForSize vms))) k⟩).1 hin
  have hv : (⟨Endp.bufAddr (pb + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k⟩ : U64).val =
      (Endp.bufAddr (pb + (x.tcbIpcBuffer &&& Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k).toNat := rfl
  rw [hv] at hr
  omega

end DropJ

/-- **A word of zero bytes reads 0.** -/
theorem loadWordAt_zero {um : Fl4Spec.Word → Fl4Spec.Word8} {p : Fl4Spec.Word}
    (h : ∀ i ∈ Fl4Spec.intUpto 0 7, um (p + (7 - BitVec.ofInt 64 i)) = 0) : Endp.loadWordAt um p = 0 := by
  unfold Endp.loadWordAt
  rw [List.map_congr_left h, Endp.intUpto_07]
  decide

end

end Fl4Proofs.P3

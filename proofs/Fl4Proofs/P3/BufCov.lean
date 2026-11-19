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
* `UtZero.zero_at`, `loadWordAt_zero`: the retype's new frame words read 0 in
  the spec (FL4 zeroes them, `UtCapP3.zero`), so `IpcRel.buf` holds at the
  words `B` gains.
-/
import Fl4Proofs.P3.BufInv
import Fl4Proofs.P3.XTopJointData
import Fl4Proofs.P3.UtDropSets
import Fl4Proofs.P3.UtDropSpec
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

/-- **A word of zero bytes reads 0.** -/
theorem loadWordAt_zero {um : Fl4Spec.Word → Fl4Spec.Word8} {p : Fl4Spec.Word}
    (h : ∀ i ∈ Fl4Spec.intUpto 0 7, um (p + (7 - BitVec.ofInt 64 i)) = 0) : Endp.loadWordAt um p = 0 := by
  unfold Endp.loadWordAt
  rw [List.map_congr_left h, Endp.intUpto_07]
  decide

end

end Fl4Proofs.P3

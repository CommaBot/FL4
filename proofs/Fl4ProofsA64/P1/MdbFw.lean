/-
P1 (aarch64, gen 62): **gen 61's `hFw` (the VZ deletion tops' frame hypothesis) split into its parts** at the heap's
own sets (`PSets.ofHeap`: `T = H.tcbs`, `Ω = H.omega`, `Sg = H.frame`, `Scs = H.scs`, `Z = H.scBits`).

* **`Cur0W.off`**: every `Cur0W s0` word that is not a `UserW` word is `NodeOffA` (off every RAM untyped's free
  part) at a later state `s` with the same state block — from `ValidUntypedA H` (TCB words below 4096, `Ω` /
  frame / SC words, endpoint / notification head and tail words: words of heap objects, `heapw_off`) and `KsOffA`
  with the nodes' placement (node words, the debug-list node word: `KsOffA.node`). So of `hFw` only its `UserW` part
  is left: **`hFw_of_user`**.
* **The `UserW` part is not satisfiable as stated** (**`UserW.free`**): every aligned word of a RAM untyped's free
  part `[p + i, p + 2^b)` is a `UserW` word (outside the heap's TCBs, `Ω`, endpoints and notifications by
  `ValidUntypedA`, outside the nodes by `KsOffA`) and is not `NodeOffA`. So `hFw` holds only in states whose RAM
  untypeds have no aligned free word: the VZ deletion tops are vacuous elsewhere. The hypothesis has to be narrowed to
  the user words the deletion actually writes — on AArch64 only `vcpu::cancel_run`'s `RUN_CALLER` word of the run
  VCPU (crates/fl4-core/src/arch/aarch64/vcpu.rs:146–152, `v = RUN_VCPU(t)`, `RUN_CALLER(v) := 0`; the [P]
  `W7.DelPlaceAt.rcw` field places it as a `UserW` word) — which needs the deletion's frame (`JV`'s cumulative
  `Cur0W` frame) refined; see the gen-62 handoff for the proposed fact.

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbZK
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {H : Heap} {Cs : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

/-- **A word of a heap object is off every RAM free part.** -/
theorem heapw_off {s : S} (hV : ValidUntypedA st H OS s) {q : U64} {k : HKind} (hq : H q = some k) {w : U64}
    (h1 : q.val ≤ w.val) (h2 : w.val < q.val + 2 ^ k.bits) : NodeOffA st OS s w :=
  fun u hu p b i hc => (hV u hu p b i hc q k hq).elim (fun _ => Or.inl (by omega)) fun _ => Or.inr (by omega)

/-- **A TCB word below offset 4096.** -/
theorem tcbw_off (hH : HeapOK H) {s : S} (hV : ValidUntypedA st H OS s) {y K : U64} (hy : y ∈ H.tcbs)
    (hK : K.val < 4096) : NodeOffA st OS s (wa y K) := by
  have hy' : H y = some .tcb := hy
  have hf := hH.fits y _ hy'
  simp only [HKind.bits] at hf
  have e : (wa y K).val = y.val + K.val := by rw [wa_val, Nat.mod_eq_of_lt (by omega)]
  exact heapw_off hV hy' (by rw [e]; omega) (by rw [e]; simp only [HKind.bits]; omega)

/-- **An `Ω` word.** -/
theorem omegaw_off {s : S} (hV : ValidUntypedA st H OS s) {w : U64} (hw : w ∈ H.omega) : NodeOffA st OS s w := by
  obtain ⟨-, q, k, hq, -, h1, h2⟩ := hw
  exact heapw_off hV hq h1 h2

/-- **An endpoint / notification's head and tail words.** -/
theorem epw_off (hH : HeapOK H) {s : S} (hV : ValidUntypedA st H OS s) {e : U64} {k : HKind} (h : H e = some k)
    (hk : 4 ≤ k.bits) : NodeOffA st OS s (epHeadA e) ∧ NodeOffA st OS s (epTSA e) := by
  have hf := hH.fits e k h
  have h16 : 16 ≤ 2 ^ k.bits := (Nat.pow_le_pow_right (by decide) hk : 2 ^ 4 ≤ 2 ^ k.bits)
  exact ⟨heapw_off hV h (le_of_eq epHeadA_val.symm) (by rw [epHeadA_val]; omega),
    heapw_off hV h (by rw [epTSA_val' (by omega)]; omega) (by rw [epTSA_val' (by omega)]; omega)⟩

/-- **`hFw`'s heap and node parts** (module docstring). -/
theorem Cur0W.off (hH : HeapOK H) {s0 s : S} (hV : ValidUntypedA st H OS s) (hK : KsOffA st Cs OS s)
    (hN : ∀ c ∈ Cs, NodePlaced st H.tcbs s c) (hk : L.ksb s = L.ksb s0) {w : U64}
    (hw : Cur0W st H.tcbs Cs H.omega H H.frame H.scs H.scBits s0 w)
    (hu : ¬ UserW st H.tcbs Cs H.omega H s0 w) : NodeOffA st OS s w := by
  have nd : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → NodeOffA st OS s (L.nodeAt s0 c o) := fun c hc o ho => by
    rw [← nodeAt_of_ksb hk]; exact KsOffA.node hK hc (hN c hc) ho
  rcases hw with ((⟨y, hy, K, -, hK2, -, -, rfl⟩ | ⟨c, hc, o, ho, -, rfl⟩ | hS | ⟨c, hc, h1, h2⟩ | ⟨e, he, he'⟩)) |
      (⟨y, hy, e⟩ | ⟨c, hc, e⟩) | (⟨t, ht, K, hK, rfl⟩ | ⟨hΩ, -⟩) | hU
  · exact tcbw_off hH hV hy hK2
  · exact nd c hc o ho
  · exact omegaw_off hV (Heap.frame_omega hS)
  · obtain ⟨z, hz⟩ := hc
    have e : H.scBits c = z := by simp [Heap.scBits, hz]
    rw [e] at h2
    exact heapw_off hV hz h1 (by simpa [HKind.bits] using h2)
  · have hk4 : ∀ k : HKind, (k = .ep ∨ k = .ntfn) → 4 ≤ k.bits := fun k hk => by
      rcases hk with rfl | rfl <;> simp [HKind.bits]
    rcases he with h | h <;> rcases he' with rfl | rfl
    · exact (epw_off hH hV h (hk4 _ (Or.inl rfl))).1
    · exact (epw_off hH hV h (hk4 _ (Or.inl rfl))).2
    · exact (epw_off hH hV h (hk4 _ (Or.inr rfl))).1
    · exact (epw_off hH hV h (hk4 _ (Or.inr rfl))).2
  · rcases e with rfl | rfl
    · exact tcbw_off hH hV hy (by simp)
    · exact tcbw_off hH hV hy (by simp)
  · rw [e]; exact nd c hc _ (by rw [debug_val]; omega)
  · exact tcbw_off hH hV ht (by omega)
  · exact omegaw_off hV hΩ
  · exact absurd hU hu

/-- **`hFw` from its `UserW` part** (module docstring). -/
theorem hFw_of_user (hH : HeapOK H) {s0 s : S} (hV : ValidUntypedA st H OS s) (hK : KsOffA st Cs OS s)
    (hN : ∀ c ∈ Cs, NodePlaced st H.tcbs s c) (hk : L.ksb s = L.ksb s0)
    (hUw : ∀ w, UserW st H.tcbs Cs H.omega H s0 w → NodeOffA st OS s w) :
    ∀ w, Cur0W st H.tcbs Cs H.omega H H.frame H.scs H.scBits s0 w → NodeOffA st OS s w := fun w hw =>
  Classical.byCases (fun hu : UserW st H.tcbs Cs H.omega H s0 w => hUw w hu)
    fun hu => Cur0W.off hH hV hK hN hk hw hu

/-- **An aligned free word of a RAM untyped is a `UserW` word and not `NodeOffA`** (module docstring: `hFw`'s
`UserW` part fails whenever a RAM untyped has an aligned free word). -/
theorem UserW.free {s0 s : S} (hV : ValidUntypedA st H OS s) (hK : KsOffA st Cs OS s) (hk : L.ksb s = L.ksb s0)
    {u p b i : U64} (hu : u ∈ OS) (hc : capA st s u = .Untyped p b i false) {w : U64} (ha : Aligned w)
    (h1 : p.val + i.val ≤ w.val) (h2 : w.val + 8 ≤ p.val + 2 ^ b.val) :
    UserW st H.tcbs Cs H.omega H s0 w ∧ ¬ NodeOffA st OS s w := by
  have hR := hK u hu p b i hc
  unfold RegionOffNodes LawfulStore.nodeBase at hR
  rw [hk] at hR
  refine ⟨⟨⟨ha, fun t ht => ?_, fun c hc' => ?_⟩, fun hΩ => ?_, fun e he => ?_⟩, fun h => ?_⟩
  · have g := hV u hu p b i hc t .tcb ht
    simp only [HKind.bits] at g
    rcases g with g | g
    · right; omega
    · left; omega
  · have g := hR.1 c hc'
    unfold LawfulStore.nodeBase
    rcases g with g | g
    · right; omega
    · left; omega
  · obtain ⟨-, q, k, hq, -, q1, q2⟩ := hΩ
    rcases hV u hu p b i hc q k hq with g | g <;> omega
  · rcases he with h | h
    · rcases hV u hu p b i hc e _ h with g | g <;> (try simp only [HKind.bits, Nat.reducePow] at g)
      · right; omega
      · left; omega
    · rcases hV u hu p b i hc e _ h with g | g <;> (try simp only [HKind.bits, Nat.reducePow] at g)
      · right; omega
      · left; omega
  · rcases h u hu p b i hc with g | g <;> omega

end ST
end R
end W7

end

end Fl4ProofsA64.P1

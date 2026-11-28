/-
P1 (aarch64, gen 37): **ASID-pool caps as top-level deletion targets over `JV`**.

Source (objects.rs `finalise_cap_object`, `AsidPool` arm: final → `vspace::delete_asid_pool`; vspace.rs:551–568):
`delete_asid_pool(base, pool)` returns unless the ASID-table entry of `base >> 9` is `pool`, reads the pool's 512
entries only to invalidate (`Arch` state), then `set_asid_table(base >> 9, 0)` — one ASID-table word (`AsW`),
written `0`.

* **`JV.vsr`**: writes of `VsR` words (QueueVsTy: `PtW Pt` and ASID-table words), under QueueVsWs's `VrOK`, keep
  `JV`, every `OS` word, the idle word and every thread's `SC` field (QueueVsPt's `JV.ptw` text over `VrOK`).
* `vspace.set_asid_table.vs`, `fin_pool.vs`, **`finJV_poolP`**, **`cdt.delete.poolP`** (any finality).

The pool's deletion inside a covered slot of the Zombie loop is not covered: `ZP`'s `VsCap` (QueueZombieP) has no
`AsidPool` arm, and `VsTy`'s `tbl` clause then loses the pool (the entry becomes `0`, which `VsTy` accepts). No named
premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueVsWs
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

/-- **`set_asid_table`** writes one ASID-table word. -/
theorem vspace.set_asid_table.as (s : S) (hi v : U64) :
    vspace.set_asid_table st s hi v ⦃ s1 => ∃ o : U64, 772352 ≤ o.val ∧ o.val < 773376 ∧ o.val % 8 = 0 ∧
      s1 = L.wr s (wa (L.ksb s) o) v ⦄ := by
  unfold vspace.set_asid_table
  rw [eq_of_spec_fd P0.Consts.vspace.N_ASID_POOLS.spec, eq_of_spec_fd P0.Consts.layout.ks.ASID_TABLE.spec]
  step as ⟨i1, hi1⟩
  try (have e1 : i1 = 127#u64 := UScalar.eq_of_val_eq (by scalar_tac)
       subst e1)
  simp only [lift, bind_ok]
  refine WP.spec_mono (obj.ks_set.spec s _ v) fun s1 e => ⟨_, ?_, ?_, ?_, e⟩
  · have : (hi.val &&& 127) ≤ 127 := Nat.and_le_right
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits] <;> omega
  · have : (hi.val &&& 127) ≤ 127 := Nat.and_le_right
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits] <;> omega
  · have : (hi.val &&& 127) ≤ 127 := Nat.and_le_right
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits] <;> omega

namespace W7
namespace R
namespace ST

section pool
variable {OS Vc Ub : Set U64} {kb : U64} {Pt : Set U64}

set_option maxHeartbeats 4000000 in
/-- **Writes of `VsR` words keep `JV`**, every `OS` word, the idle word and every thread's `SC` field. -/
theorem JV.vsr (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    {s0 s s' : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hw : WritesIn st s s' (VsR kb Pt)) :
    JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s' ∧ OSKeep st OS s s' ∧ L.idleW s' = L.idleW s ∧
      ScK st T s s' := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hT := q.tcbs
  have hN := q.nodes _ q.cur
  have kf : ∀ z ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → L.mem s' (wa z K) = L.mem s (wa z K) :=
    fun z hz K hK h8 => hw.mem_eq (field_aligned (hT z hz) hK h8) fun hp =>
      (out_ne_field (q.omega _ (hR.om _ hp)) hz (hT z hz) hK) rfl
  have c0 := h.1.1.1.capw hw fun b hb' => Or.inr ⟨hR.om b hb', hR.sg b hb'⟩
  have kst : StK st T s s' := fun z hz => by rw [stA_eq]; exact kf z hz _ (by simp) (by simp)
  have rv := h.1.1.2.keep kst (fun z hz => kf z hz 3672#u64 (by simp) (by simp))
  have k : OSKeep st OS s s' := fun y hy => by
    obtain ⟨v8, v16, v24⟩ := vals hO hy
    have m := fun (b : U64) (hal : Aligned b) (h1 : y.val ≤ b.val) (h2 : b.val < y.val + 32) =>
      hw.mem_eq hal fun hp => hR.os _ hp ⟨y, hy, h1, h2⟩
    exact ⟨m _ (hO.al0 hy) le_rfl (by omega), m _ (hO.al hy (k := 8#u64) (by simp) (by simp)) (by omega) (by omega),
      m _ (hO.al hy (k := 16#u64) (by simp) (by simp)) (by omega) (by omega),
      m _ (hO.al hy (k := 24#u64) (by simp) (by simp)) (by omega) (by omega)⟩
  have vk : VKeep st T Vc s s' :=
    ⟨hw.1, fun b hb' => hw.mem_eq (h.2.w hb').1 (fun hp => hR.vc _ hp hb'),
      fun t ht => kf t ht 3664#u64 (by simp) (by simp), fun t ht => kf t ht 3672#u64 (by simp) (by simp),
      fun t ht => Or.inl (k.cap (hV.bcov t ht))⟩
  refine ⟨⟨⟨⟨c0, rv⟩, h.1.2.keep k⟩, h.2.keep vk⟩, k, ?_, fun z hz => by rw [scA_eq]; exact kf z hz _ (by simp) (by simp)⟩
  unfold LawfulStore.idleW
  rw [hw.2.1, nodeAt_of_ksb hw.1]
  exact hw.mem_eq (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8])) fun hp =>
    out_ne_node (q.omega _ (hR.om _ hp)) q.cur hN (by rw [idle8]; omega) rfl

/-- **An ASID-pool cap's finalisation** (any finality) writes only ASID-table words (at a state whose `ks` base is
`kb`). -/
theorem fin_pool.vs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt)
    (s : S) (a : A) (ptr base : U64) (fin : Bool) (hk : L.ksb s = kb) :
    objects.finalise_cap_object st ar s a (.AsidPool ptr base) fin ⦃ r =>
      r.1 = (.Null, .Null) ∧ WritesIn st s r.2.1 (VsR kb Pt) ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  have hset : ∀ hi, vspace.set_asid_table st s hi 0#u64 ⦃ s1 => WritesIn st s s1 (VsR kb Pt) ⦄ := fun hi =>
    WP.spec_mono (vspace.set_asid_table.as s hi 0#u64) fun s1 ⟨o, h1, h2, h8, e⟩ => by
      have hb : VsR kb Pt (wa (L.ksb s) o) := Or.inr ⟨o, h1, h2, h8, by rw [hk]⟩
      rw [e]; exact (writesIn_wr (hR.al _ hb)).mono fun b eb => by rw [eb]; exact hb
  split
  · refine WP.spec_bind (vspace.delete_asid_pool.vs (V := VsR kb Pt) hA s a base ptr hset) ?_
    rintro ⟨s1, a1⟩ w1
    exact (WP.spec_ok _).2 ⟨rfl, w1⟩
  · exact (WP.spec_ok _).2 ⟨rfl, WritesIn.refl _ _⟩

/-- **An ASID-pool cap's finalisation over `JV`** (any finality). -/
theorem finJV_poolP (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {A : Type _} {ar : machine.Arch A}
    (hP : P0.ArchTotal ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hk : L.ksb s = kb) {x ptr base : U64}
    (hc : obj.Slot.cap st x s = ok (.AsidPool ptr base)) :
    FinJV st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x := by
  intro a c fin hc'
  rw [hc] at hc'
  obtain rfl := okinj hc'
  rw [fin_cap_eq_obj (by simp)]
  exact WP.spec_mono (fin_pool.vs hP hR s a ptr base fin hk) fun r hr =>
    ⟨hr.1, (JV.vsr hO hV hR h hr.2).1⟩

/-- **The exposed `cdt.delete` of an ASID-pool slot of `OS` keeps `JV`** (the ASID-table words placed by
`VrOK` at the start state's `ks` base). -/
theorem cdt.delete.poolP {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x ptr base : U64} (hx : x ∈ OS)
    (hc : obj.Slot.cap st x s = ok (.AsidPool ptr base)) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ⦄ :=
  cdt.delete.finJV hO hV h hx (finJV_poolP hO hV hP hR h h.ksb hc)

end pool

end ST
end R
end W7

end

end Fl4ProofsA64.P1

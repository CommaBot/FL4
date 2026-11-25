/-
# P2 (line lvm, gen 5): **the declining holder of `lock v` reads no hardware-written word**

`E2EV.HwStepV` keeps `s.lk v = none` [P] (lead decision 2, option (a)). The case it leaves out: another core `d`
holds `lock v` (fl4-sync `vcpu_locks` for a VCPU-cap invocation by a thread on `d`) while `v`'s bound thread
runs its guest elsewhere; `handle_vcpu_invocation_local` then declines at its binding check `v.TCB ≠ ct`. This
module proves the body-level fact a weaker premise would rest on:

* **`vinvHead.guard_decl`**: when `v.TCB ≠ ct`, the invocation's checks, on any store answering six words as
  `st` (this core's `CUR_THREAD`, `ct`'s `MSG_INFO` register and flags word, the slot's two cap words, `v.TCB`),
  decline as the real ones whatever the work (`T1`, `T2`): those six words are everything the declining run
  reads;
* **`vinv_decl_noVData`**: none of them is a non-binding VCPU word (`E2EV.VData`, what the hardware writes):
  the first five lie in a node / slot / TCB region (`region_ne_none`, so outside every VCPU by
  `RegionOKV.none`), and `v.TCB` is a binding word (`notVData_vtcb`).

What is not done (handoff §14): wiring the weaker premise ("every core holding `lock v` runs such a decline")
into `SerialHw` needs `InvH.loc`'s held-word agreement and the holder's `Safe` body to tolerate a write to a
word it holds but never reads; neither follows from `Safe.foreign`. No named premises here.
-/
import Fl4Proofs.P2.AccessLvm
import Fl4Proofs.P2.E2EV
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **The declining invocation reads six words** (module docstring). -/
theorem vinvHead.guard_decl {A : Type} (ar : machine.Arch A) (s : S) (a : A) (number : I64) (slot : obj.Slot)
    (v : U64) (info : msginfo.MessageInfo) (hinfo : msg.msg_info st s (L.curW s) = ok info)
    (hcur : R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hmi : R (regA (L.curW s) layout.reg.MSG_INFO)) (hf : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hsl : R slot) (hsl8 : R (core.num.U64.wrapping_add slot 8#u64))
    (hvt : R (core.num.U64.wrapping_add v vcpu.TCB))
    (hne : L.mem s (core.num.U64.wrapping_add v vcpu.TCB) ≠ L.curW s)
    (T1 T2 : U64 → U64 → U64 → msginfo.MessageInfo → Result (Bool × S × A)) :
    vinvHead gS ar s a number slot v T1 = vinvHead st ar s a number slot v T2 := by
  have e : vcpu.get st s v vcpu.TCB = ok (L.mem s (core.num.U64.wrapping_add v vcpu.TCB)) := by
    unfold vcpu.get; simp only [lift, bind_ok]; exact L.read_eq _ _
  have hb : (L.mem s (core.num.U64.wrapping_add v vcpu.TCB) != L.curW s) = true := bne_iff_ne.mpr hne
  unfold vinvHead
  rw [PathObl.sched.cur_thread.guard s hcur, cur_thread_ok, PathObl.gst_cur_cpu, L.cur_cpu_eq]
  simp only [bind_ok]
  rw [PathObl.msg.msg_info.guard s _ hmi, hinfo]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.flags.guard _ s hf, PathObl.obj.Slot.cap.guard slot s hsl hsl8, vcpu.get.guard s v _ hvt, e]
  simp only [bind_ok, hb, ↓reduceIte]

end

section
open OwnMap OwnMapV E2EV

/-- A word in a node, a slot or a TCB lies in no `.none` region. -/
theorem region_ne_none {K : KLayout} {b : U64}
    (h : (∃ c, InNode K c b) ∨ (∃ p ∈ K.slots, InW p 32 b) ∨ (∃ t, K.heap t = some .tcb ∧ InW t (2 ^ 12) b)) :
    region K b ≠ .none := by
  unfold region
  split_ifs with h1 h2 h3 h4 h5 h6
  all_goals first
    | (exfalso; rcases h with h | h | h <;> contradiction)
    | (intro e; cases e)

variable {K : KLayoutV}

theorem notVData_of_region (hK : RegionOKV K) {b : U64} (h : region K.toKLayout b ≠ .none) : ¬ VData K b :=
  fun ⟨v, hv, _⟩ => h (hK.none v b hv)

/-- A VCPU's binding word is not a non-binding word of any VCPU. -/
theorem notVData_vtcb (hK : RegionOKV K) {v : U64} (hv : v ∈ K.vcpus) : ¬ VData K (fld v oVTCB) := by
  rintro ⟨w, hw, hg⟩
  have e := hK.disj _ _ _ hw (vtcb_in hK hv)
  rw [e] at hg
  apply hg
  have := hK.tcbw v hv
  unfold VcpuGate; left; omega

/-- The words `vinvHead.guard_decl` lists. -/
def VinvDeclRd (cur ct slot v w : U64) : Prop :=
  w = cur ∨ w = regA ct layout.reg.MSG_INFO ∨ w = core.num.U64.wrapping_add ct 3456#u64 ∨ w = slot ∨
    w = core.num.U64.wrapping_add slot 8#u64 ∨ w = fld v oVTCB

/-- **The declining invocation reads no word the hardware writes** (module docstring): given where the five
non-VCPU words lie (this core's node word in its node; `ct`'s two words in its TCB; the slot's words in the
slot), none of the six is a non-binding VCPU word. -/
theorem vinv_decl_noVData (hK : RegionOKV K) {cur ct slot v : U64} (hv : v ∈ K.vcpus)
    (hcur : ∃ c, InNode K.toKLayout c cur)
    (hct : K.heap ct = some .tcb) (hmi : InW ct (2 ^ 12) (regA ct layout.reg.MSG_INFO))
    (hfl : InW ct (2 ^ 12) (core.num.U64.wrapping_add ct 3456#u64))
    (hsl : slot ∈ K.slots) (hs0 : InW slot 32 slot) (hs8 : InW slot 32 (core.num.U64.wrapping_add slot 8#u64))
    {w : U64} (hw : VinvDeclRd cur ct slot v w) : ¬ VData K w := by
  rcases hw with e | e | e | e | e | e <;> rw [e]
  · exact notVData_of_region hK (region_ne_none (Or.inl hcur))
  · exact notVData_of_region hK (region_ne_none (Or.inr (Or.inr ⟨ct, hct, hmi⟩)))
  · exact notVData_of_region hK (region_ne_none (Or.inr (Or.inr ⟨ct, hct, hfl⟩)))
  · exact notVData_of_region hK (region_ne_none (Or.inr (Or.inl ⟨slot, hsl, hs0⟩)))
  · exact notVData_of_region hK (region_ne_none (Or.inr (Or.inl ⟨slot, hsl, hs8⟩)))
  · exact notVData_vtcb hK hv

/-- `vcpu.TCB` is rule 7's binding offset. -/
theorem vcpu_TCB_eq : vcpu.TCB = oVTCB := by
  unfold vcpu.TCB oVTCB; rfl

end

end Fl4Proofs.P2

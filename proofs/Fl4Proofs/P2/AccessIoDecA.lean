/-
# P2: `PathObl.dec_alt` of the I/O port path (line p2io)

* `IoDS.safe`: the declined run's writes (`FAULT_IP`, `CUR_TIME`, `CONSUMED`) are
  aligned words no owner depends on (`SafeW`);
* `io_dec_alt`: **`PathObl.dec_alt`** for `syscall.handle_ioport_local`: a run that
  declines at `s` declines at every alternative `s'` (`io_alt_not_acc`), the same way
  on the store guarded to writes of `IoDS s` and on `mguard` (`handle_dec_m`).

Premises: those of `IoPre`; `RegionOK`, `IoLayA` [J].
-/
import Fl4Proofs.P2.AccessIoDecl
import Fl4Proofs.P2.AccessIoDec2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s' : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}

/-- The declined run's writes are aligned safe words. -/
theorem IoDS.safe (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {b : U64} (hb : IoDS (st := st) s b) :
    Aligned b ∧ SafeW K b := by
  rcases hb with rfl | rfl | rfl
  · obtain ⟨k, hk, e⟩ := regA_eq P.tA (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    have hk' : k.val = 392 := by rw [hk]; simp [layout.reg.FAULT_IP]
    have ht := P.hT _ P.cT
    rw [e]
    refine ⟨field_aligned P.tA (by omega) (by omega), Or.inr (Or.inl ⟨_, k.val, ht,
      P.lay.tcbw _ ht k (by omega) (by omega), by omega, tcb_wadd_val P.tA (by omega),
      by omega, by omega, by omega, by omega, by omega, by omega⟩)⟩
  · exact ⟨nodeAt_aligned P.np (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]),
      Or.inl ⟨_, P.lay.node _ _ (P.inNode _ (by simp [layout.node.CUR_TIME]))⟩⟩
  · exact ⟨nodeAt_aligned P.np (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
      Or.inl ⟨_, P.lay.node _ _ (P.inNode _ (by simp [layout.node.CONSUMED]))⟩⟩

/-- **`PathObl.dec_alt`** for the I/O port path. -/
theorem io_dec_alt {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K)
    {number : I64} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {a : A} {r r' : Bool × S × A}
    (h : syscall.handle_ioport_local st ar s a number = ok r) (hr : r.1 ≠ true)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    (h' : syscall.handle_ioport_local st ar s' a number = ok r') :
    r'.1 ≠ true ∧
      syscall.handle_ioport_local (guard st (fun _ => True) (IoDS (st := st) s)) ar s' a number = ok r' ∧
      syscall.handle_ioport_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s' a number = ok r' := by
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hpre : ∀ b, (b = regA (L.curW s') layout.reg.FAULT_IP ∨
      b = L.nodeAt s' (L.cpu s') layout.node.CUR_TIME ∨ b = L.nodeAt s' (L.cpu s') layout.node.CONSUMED) →
      IoDS (st := st) s b := by
    intro b hb
    rw [hcur, G.node, G.node] at hb
    exact hb
  have hn : r'.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r'
    intro hb
    change b = true at hb
    subst hb
    exact io_alt_not_acc hA P Al h hr h'
  refine ⟨hn, ?_, ?_⟩
  · refine handle_dec_m ⟨fun _ _ => guard_read trivial, fun _ _ => guard_read_pair trivial trivial,
      fun _ => rfl, fun _ => rfl⟩ (fun y b v hb _ _ => guard_write (hpre b hb)) h' hn
  · have hR : RdEq st (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) :=
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
    have hW : PreOK st (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) s' (L.curW s') := by
      intro y b v hb _ _
      obtain ⟨ha, hs⟩ := IoDS.safe P (hpre b hb)
      rw [L.write_eq]
      exact mguard_write (L.write_eq y b v) (stepOK_safe (m0 := m0) hK hLA ha hs)
    exact handle_dec_m hR hW h' hn

end

end Fl4Proofs.P2.PathObl

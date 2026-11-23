/-
# A declined local entry: two timestamp updates are one (FL4 #71, pf1 step 2, decline route (b))

A local entry (`handle_vm_fault_local`, `handle_reply_recv_vm_local`, …) that
returns `false` has already run `update_timestamp` (`vm_local_decline`); fl4-sync
then runs the general entry, whose own `update_timestamp` follows. With one
domain `update_timestamp` writes only the core's `CUR_TIME` (the reading `n`)
and `CONSUMED` (`+ (n - CUR_TIME)`, wrapping), so two updates with readings
`n1`, `n2` leave what one update with `n2` alone leaves (`utW_twice`:
`c + (n1 - p) + (n2 - n1) = c + (n2 - p)` mod `2 ^ 64`).

`update_timestamp_twice`: the second update from the first's result is the
update from the entry state with an Arch value `a'` that reads the later
clock value (`ar.now a' = ar.now a1`). That such an `a'` exists, related to
the spec as the entry's `a` is, is the platform clock law the decline top
takes as a named premise (KENTRY-PLAN pf1: `ClockLater` [P]).
-/
import Fl4Proofs.P1.FastVmInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- The core's `CUR_TIME` word. -/
abbrev ctA (s : S) : U64 := L.nodeAt s (L.cpu s) layout.node.CUR_TIME
/-- The core's `CONSUMED` word. -/
abbrev cnA (s : S) : U64 := L.nodeAt s (L.cpu s) layout.node.CONSUMED

/-- `update_timestamp`'s two writes for the clock reading `n` (one domain). -/
def utW (s : S) (n : U64) : S :=
  L.wr (L.wr s (ctA (L := L) s) n) (cnA (L := L) s)
    (core.num.U64.wrapping_add (L.mem s (cnA (L := L) s)) (core.num.U64.wrapping_sub n (L.mem s (ctA (L := L) s))))

theorem ctA_wr (s : S) (b v : U64) : ctA (L := L) (L.wr s b v) = ctA (L := L) s := by
  unfold ctA; rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
theorem cnA_wr (s : S) (b v : U64) : cnA (L := L) (L.wr s b v) = cnA (L := L) s := by
  unfold cnA; rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]

/-- The two words are aligned and distinct on a placed node. -/
theorem ct_cn {T : Set U64} {s : S} (hN : NodePlaced st T s (L.cpu s)) :
    Aligned (ctA (L := L) s) ∧ Aligned (cnA (L := L) s) ∧ ctA (L := L) s ≠ cnA (L := L) s := by
  refine ⟨nodeAt_aligned hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]),
    nodeAt_aligned hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]), fun e => ?_⟩
  have h := congrArg UScalar.val e
  unfold ctA cnA at h
  rw [nodeAt_val hN (by simp [layout.node.CUR_TIME]), nodeAt_val hN (by simp [layout.node.CONSUMED])] at h
  simp [layout.node.CUR_TIME, layout.node.CONSUMED] at h

/-- **`update_timestamp` in closed form** (one domain). -/
theorem update_timestamp_ok {T : Set U64} {s : S} {a a1 : A} {n : U64} (hN : NodePlaced st T s (L.cpu s))
    (hn : ar.now a = ok (n, a1)) : sched.update_timestamp st ar s a = ok (utW (L := L) s n, a1) := by
  obtain ⟨hct, hcn, hne⟩ := ct_cn hN
  unfold sched.update_timestamp
  rw [cur_time_ok]; simp only [bind_ok]
  rw [hn]; simp only [bind_ok, uncurry_apply_pair]
  rw [L.cur_cpu_eq]; simp only [bind_ok]
  rw [eq_of_spec_fd (obj.node_set.spec (L := L) s _ _ _)]; simp only [bind_ok, lift]
  unfold sched.consumed
  rw [L.cur_cpu_eq]; simp only [bind_ok]
  rw [node_get_ok]; simp only [bind_ok, lift]
  rw [eq_of_spec_fd (sched.set_consumed.spec (L := L) _ _)]; simp only [bind_ok]
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have e1 : L.nodeA (L.wr s (ctA (L := L) s) n) layout.node.CONSUMED = cnA (L := L) s := by
    unfold LawfulStore.nodeA; rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
  have e2 : L.nodeAt (L.wr s (ctA (L := L) s) n) (L.cpu (L.wr s (ctA (L := L) s) n)) layout.node.CONSUMED =
      cnA (L := L) s := by
    rw [LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
  have e3 : L.mem (L.wr s (ctA (L := L) s) n) (cnA (L := L) s) = L.mem s (cnA (L := L) s) :=
    mem_wr_ne' hct hcn hne
  simp only [e1, e2, e3]
  first
    | rfl
    | (unfold utW; simp)

/-- The wrapping sums: `c + (n1 - p) + (n2 - n1) = c + (n2 - p)`. -/
theorem wrap_twice (c p n1 n2 : U64) :
    core.num.U64.wrapping_add (core.num.U64.wrapping_add c (core.num.U64.wrapping_sub n1 p))
      (core.num.U64.wrapping_sub n2 n1) =
    core.num.U64.wrapping_add c (core.num.U64.wrapping_sub n2 p) := by
  apply UScalar.eq_of_val_eq
  have hc := c.hBounds; have hp := p.hBounds; have h1 := n1.hBounds; have h2 := n2.hBounds
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits] at hc hp h1 h2 ⊢
  omega

/-- **Two timestamp updates are the later one** (as states, under
`StoreExt`). -/
theorem utW_twice (hX : StoreExt st) {T : Set U64} {s : S} (hN : NodePlaced st T s (L.cpu s)) (n1 n2 : U64) :
    utW (L := L) (utW (L := L) s n1) n2 = utW (L := L) s n2 := by
  obtain ⟨hct, hcn, hne⟩ := ct_cn hN
  have k1 : ctA (L := L) (utW (L := L) s n1) = ctA (L := L) s := by unfold utW; rw [ctA_wr, ctA_wr]
  have k2 : cnA (L := L) (utW (L := L) s n1) = cnA (L := L) s := by unfold utW; rw [cnA_wr, cnA_wr]
  have m1 : L.mem (utW (L := L) s n1) (ctA (L := L) s) = n1 := by
    unfold utW; rw [mem_wr_ne' hcn hct (Ne.symm hne), LawfulStore.mem_wr_same hct]
  have m2 : L.mem (utW (L := L) s n1) (cnA (L := L) s) =
      core.num.U64.wrapping_add (L.mem s (cnA (L := L) s)) (core.num.U64.wrapping_sub n1 (L.mem s (ctA (L := L) s))) := by
    unfold utW; rw [LawfulStore.mem_wr_same hcn]
  generalize hU : utW (L := L) s n1 = U at k1 k2 m1 m2 ⊢
  unfold utW
  rw [k1, k2, m1, m2, wrap_twice, ← hU]
  unfold utW
  -- the first update's two writes are overwritten
  rw [wr_comm hX _ _ _ hcn hct (Ne.symm hne), wr_wr hX _ _ _ hct, wr_wr hX _ _ _ hcn]

/-- **A second `update_timestamp` from the first's result is one update from
the entry state with an Arch value reading the later clock value.** -/
theorem update_timestamp_twice (hX : StoreExt st) (hA : P0.ArchTotal ar) {T : Set U64} {s s1 s2 : S}
    {a a1 a2 a' : A} (hN : NodePlaced st T s (L.cpu s))
    (h1 : sched.update_timestamp st ar s a = ok (s1, a1)) (h2 : sched.update_timestamp st ar s1 a1 = ok (s2, a2))
    (h' : ar.now a' = ar.now a1) : sched.update_timestamp st ar s a' = ok (s2, a2) := by
  obtain ⟨⟨n1, b1⟩, hn1, -⟩ := spec_ex_fd (hA.now a)
  obtain ⟨⟨n2, b2⟩, hn2, -⟩ := spec_ex_fd (hA.now a1)
  rw [update_timestamp_ok ar hN hn1] at h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff h1)
  have hN1 : NodePlaced st T (utW (L := L) s n1) (L.cpu (utW (L := L) s n1)) := by
    have e : L.cpu (utW (L := L) s n1) = L.cpu s := by unfold utW; simp [LawfulStore.cpu_wr]
    rw [e]; unfold utW; exact hN.wr.wr
  rw [update_timestamp_ok ar hN1 hn2] at h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff h2)
  rw [update_timestamp_ok ar hN (h'.trans hn2), utW_twice hX hN]

end

end Fl4Proofs.P1

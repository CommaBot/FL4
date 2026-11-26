/-
P3 (p3P, FINDING): **`JEntryAtR7.stall` (= `JEntryAt.stall`, [P] "one core") is false at states
whose memory holds a two-word pattern that no invariant constrains.**

`stall : ∀ q, smp.remote_tcb_stall st arI s ar q = ok (s, ar)` asks the no-op for *every* word `q`,
not only for TCBs. FL4's `remote_tcb_stall` reads `cpu := mem (q + 3520)` (the affinity word) and,
when `cpu ≠ cur_cpu`, `mem (nodeAt cpu CUR_THREAD)`; if that is `q` it stalls `cpu` and
`remote_reschedule` sets bit `cpu &&& 63` of the current node's `IPI_PENDING` word.

`remote_tcb_stall_moves`: if `mem (q + 3520) ≠ cpu s`, `mem (nodeAt (mem (q + 3520)) CUR_THREAD) = q`
and the current node's `IPI_PENDING` word is 0, the stall changes the store, so `stall` fails at `q`
(`stall_false`). `node_base cpu = ksb + NODES + cpu * 4288` (wrapping, `4288 = 64 · 67`, `67` odd),
so every address `≡ ksb + NODES (mod 64)` is some `cpu`'s node base: a user thread's own 4 KiB frame
`F` holds such an address `X`; writing `q := F` at `X` and `cpu := (X - ksb - NODES) / 64 · 67⁻¹`
(mod 2^64, ≠ 0) at `F + 3520` gives the pattern. Nothing in `JAtZ` / `JReachU17` constrains user
frame contents, and on one core `IPI_PENDING` is 0, so at such states `KDispHypsKVU29.inv` / `mid`
are unsatisfiable and the syscall clause of `kernel_entry_reachU29` (and `U30`) is vacuous for the
invocation syscalls. Not a kernel bug: the consumers only use `stall` at the Thread decode's TCB
target (`remote_tcb_stall_id`: on one core every TCB of `T` has the current core's affinity), so
the premise should be narrowed to `∀ q ∈ Z.T` (then provable from `SchedRel`). No premise added.
-/
import Fl4Proofs.P3.XTopJointKEntryU29
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Fl4Proofs.P1

section
variable {S A : Type} {st : machine.Store S} [L : LawfulStore st] {arI : machine.Arch A}

/-- **The stall of a non-TCB word `q` can change the store** (module docstring). -/
theorem remote_tcb_stall_moves (hA : P0.ArchTotal arI) (s : S) (a : A) (q : U64)
    (hcpu : L.mem s (affA q) ≠ L.cpu s)
    (hcur : L.mem s (L.nodeAt s (L.mem s (affA q)) layout.node.CUR_THREAD) = q)
    (hal : Aligned (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING))
    (hz : L.mem s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) = 0#u64) :
    smp.remote_tcb_stall st arI s a q ⦃ r => r.1 ≠ s ⦄ := by
  unfold smp.remote_tcb_stall smp.remote_reschedule
  step with obj.Tcb.affinity.spec as ⟨cpu, hc⟩
  step with LawfulStore.cur_cpu_spec as ⟨i, hi⟩
  subst hc hi
  have hb : (L.mem s (affA q) != L.cpu s) = true := by simpa using hcpu
  simp only [hb, ↓reduceIte]
  step with obj.node_get.spec as ⟨t1, ht1⟩
  rw [hcur] at ht1
  subst ht1
  simp only [↓reduceIte]
  refine WP.spec_bind (hA.remote_stall a _) (fun a1 _ => ?_)
  step with LawfulStore.cur_cpu_spec as ⟨i, hi⟩
  subst hi
  simp only [hb, ↓reduceIte]
  step with obj.node_get.spec as ⟨i1, hi1⟩
  step as ⟨i2, hi2, hi2'⟩
  step as ⟨i3, hi3, hi3', hi3p⟩
  step as ⟨m, hm, hm'⟩
  step with obj.node_set.spec as ⟨s1, hs1⟩
  try simp only [WP.spec_ok]
  intro e
  have hw := LawfulStore.mem_wr_same (L := L) (s := s) (v := m) hal
  rw [hs1] at e
  rw [e, hz] at hw
  have hi10 : i1 = 0#u64 := by rw [hi1, hz]
  subst hw hi10
  have h3 : i3.bv = 0#64 := by simpa using hm'.symm
  have h4 : i3.val = 0 := by show i3.bv.toNat = 0; rw [h3]; rfl
  omega

/-- **`JEntryAtR7.stall` fails at such a `q`** (module docstring): the stall of `q` is not the no-op. -/
theorem stall_false (hA : P0.ArchTotal arI) (s : S) (a : A) (q : U64)
    (hcpu : L.mem s (affA q) ≠ L.cpu s)
    (hcur : L.mem s (L.nodeAt s (L.mem s (affA q)) layout.node.CUR_THREAD) = q)
    (hal : Aligned (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING))
    (hz : L.mem s (L.nodeAt s (L.cpu s) layout.node.IPI_PENDING) = 0#u64) :
    smp.remote_tcb_stall st arI s a q ≠ ok (s, a) := by
  intro h
  have hm := remote_tcb_stall_moves hA s a q hcpu hcur hal hz
  rw [h, WP.spec_ok] at hm
  exact hm rfl

end

end Fl4Proofs.P3

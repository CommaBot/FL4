/-
P3x for virtualization (line virt, gen 24, item 3b): **the `mdb_chunked` fact for VCPU caps** (gen 23's side finding:
keeping `JExtV.cap` across a final `Vcpu` delete needs caps to the same VCPU to be MDB-adjacent).

FL4 decides finality locally: `cdt::is_final_capability_with_cap` (cdt.rs l. 163-175) compares the cap with its MDB
`prev` and `next` only (`same_object_as`). seL4 / l4v justify this with `mdb_chunked` (`valid_mdb`: caps to the same
region form a contiguous run of the derivation list). For `Vcpu` caps (`same_object_as (Vcpu v) b ↔ b = Vcpu v`,
VirtVCappedDel's `soB_vcpu_left/right`) the fact is:

* **`VcpuChunked G mem`**: for every VCPU `v`, (a) inside one ghost chain the positions holding `Vcpu v` form an
  interval, and (b) all `Vcpu v` caps lie in one chain.
* `chain_adj`: adjacent elements of an `IsChain` list are related (the MDB links `nextOf` / `prevOf`).
* **`vcpu_alone`**: under `MdbLinks` + `VcpuChunked`, a slot holding `Vcpu v` whose MDB neighbours are null or hold
  no `Vcpu v` is the only slot holding `Vcpu v` — what a final delete of `Vcpu v` needs for `JExtV.shrink` (no
  other cap names `v` once `v` leaves `V`).

## Checked against FL4 source: which steps keep `VcpuChunked`

* `cdt::insert` / `insert_with_cap` (cdt.rs l. 28-46; Copy, Mint, the IRQ / IO-port issue paths): the new cap goes
  right after the source in the source's chain. A new `Vcpu v` cap comes only from a `Vcpu v` source
  (`derive_cap` / `update_cap_data` keep `Vcpu`, objects.rs l. 180), so it joins the source's run; a cap of any other
  object inserted after a non-`Vcpu v` source never lands inside a run (a run's interior holds `Vcpu v` caps only).
* `cdt::insert_new_cap` (cdt.rs l. 187; retype): new caps after the untyped parent, to fresh objects in the free
  region (no older cap names them: `UtInv`), each a run of one.
* `cdt::move_cap` (l. 49-65; Move, Mutate, Rotate): the destination takes the source's chain position.
* `cdt::swap` (l. 67-; Swap, Rotate, `cap_swap_for_delete`): seL4 `cteSwap`, the caps exchange slots with their MDB
  nodes, so the chain order of caps is unchanged (P3's ghost: `renG G (Equiv.swap s1 s2)`).
* `cdt::delete` / `empty_slot`: one element leaves its chain; a sub-list of an interval-closed list stays
  interval-closed, and no chain is split.
* In-place cap rewrites (the `set_cap` sites listed in gen 23's handoff) never write or overwrite a `Vcpu` cap; at
  boot no VCPU exists.

So `VcpuChunked` holds on every reachable state, but proving its preservation means a per-step argument over each
MDB operation's ghost (`insG`, `renG`, `remG`, the retype's insertion) that no P3 bundle carries yet. It is the
natural **[J] carried field** of the VM-epoch bundle (`JAtZV3`, mmuAD's), with these per-step lemmas as its
obligations — not provable now without that bundle. Here only its use (`vcpu_alone`) is proved.

Named premises: none (`VcpuChunked` is a hypothesis of `vcpu_alone`, a state fact, to become a [J] bundle field).
New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtVCappedDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVChunk
open fl4_core Fl4Proofs.P3 Classical

noncomputable section

/-- **Caps to one VCPU are MDB-contiguous** (module docstring; l4v `mdb_chunked` for `Vcpu` caps). -/
def VcpuChunked (G : MdbGhost) (mem : U64 → U64) : Prop :=
  (∀ v, ∀ ch ∈ G.chains, ∀ (i j k : Nat) (a c : U64), i ≤ j → j ≤ k → ch[i]? = some a → ch[k]? = some c →
      capV mem a = .Vcpu v → capV mem c = .Vcpu v → ∃ b, ch[j]? = some b ∧ capV mem b = .Vcpu v) ∧
  (∀ v, ∀ ch ∈ G.chains, ∀ ch' ∈ G.chains, ∀ y ∈ ch, ∀ y' ∈ ch',
      capV mem y = .Vcpu v → capV mem y' = .Vcpu v → ch = ch')

theorem chain_adj {α : Type} {R : α → α → Prop} :
    ∀ (l : List α), l.IsChain R → ∀ (i : Nat) (a b : α), l[i]? = some a → l[i + 1]? = some b → R a b
  | [], _, i, a, b, ha, _ => by simp at ha
  | [x], _, i, a, b, _, hb => by simp at hb
  | x :: y :: t, h, 0, a, b, ha, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at ha hb
    subst ha; subst hb
    exact (List.isChain_cons_cons.1 h).1
  | x :: y :: t, h, i + 1, a, b, ha, hb =>
    chain_adj (y :: t) (List.isChain_cons_cons.1 h).2 i a b (by simpa using ha) (by simpa using hb)

variable {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost}

/-- **A `Vcpu v` cap without a `Vcpu v` neighbour is the only one** (module docstring). -/
theorem vcpu_alone (hP : Placed th) (hM : MdbLinks th mem G) (hK : VcpuChunked G mem) {y v : U64}
    (hy : y ∈ G.chains.flatten) (hc : capV mem y = .Vcpu v)
    (hp : prevOf mem y = 0#u64 ∨ capV mem (prevOf mem y) ≠ .Vcpu v)
    (hn : nextOf mem y = 0#u64 ∨ capV mem (nextOf mem y) ≠ .Vcpu v) :
    ∀ y', y' ∈ G.chains.flatten → capV mem y' = .Vcpu v → y' = y := by
  intro y' hy' hc'
  by_contra hne
  obtain ⟨ch, hch, hyc⟩ := List.mem_flatten.1 hy
  obtain ⟨ch', hch', hyc'⟩ := List.mem_flatten.1 hy'
  have e := hK.2 v ch hch ch' hch' y hyc y' hyc' hc hc'
  subst e
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hyc
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hyc'
  have hik : i ≠ k := by
    rintro rfl; rw [hi] at hk; exact hne (Option.some.inj hk).symm
  have hmem : ∀ (j : Nat) (b : U64), ch[j]? = some b → b ≠ 0#u64 := fun j b hb =>
    (((hM.members b).1 (List.mem_flatten.2 ⟨ch, hch, List.mem_of_getElem? hb⟩)).1).ne_zero hP
  rcases Nat.lt_or_gt_of_ne hik with h | h
  · obtain ⟨b, hb, hbc⟩ := hK.1 v ch hch i (i + 1) k y y' (by omega) (by omega) hi hk hc hc'
    have hR := chain_adj ch (hM.chain ch hch) i y b hi hb
    rcases hn with h0 | h0
    · rw [hR.1] at h0; exact hmem _ _ hb h0
    · rw [hR.1] at h0; exact h0 hbc
  · obtain ⟨b, hb, hbc⟩ := hK.1 v ch hch k (i - 1) i y' y (by omega) (by omega) hk hi hc' hc
    have hR := chain_adj ch (hM.chain ch hch) (i - 1) b y hb (by rw [show i - 1 + 1 = i by omega]; exact hi)
    rcases hp with h0 | h0
    · rw [hR.2] at h0; exact hmem _ _ hb h0
    · rw [hR.2] at h0; exact h0 hbc

end
end Fl4Proofs.P3.VirtVChunk

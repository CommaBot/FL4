/-
P3 (DESIGN.md §9): **keeping `JCov`: monotone ghost heaps and a dead set**
(ScPlaceUt's design note, option 2).

* `DeadP H s q`: the object at `q` is read by nothing P1 tracks: a TCB
  inactive (so in no queue and named by no reply, through `runQ`/`runR`
  and `back`), with no SC or bound notification, neither the scheduler
  action nor idle; an endpoint idle; a notification not
  waiting, with no bound TCB and no SC; a reply with no TCB; an SC with no
  TCB, reply or notification.  (The current thread and the current SC may
  still name a dead object: finalising the current thread's TCB or SC
  leaves `CUR_THREAD` / `CUR_SC` until the next `schedule`, as in seL4; a
  notification keeps an `Active` state and its badge.)
* `JCovD th H G D Cs s`: every object of `th` and `H` is covered by a cap
  or in the dead set `D`, `D`'s objects are `DeadP`, and the untyped caps
  miss the kernel area (`JCov` with "covered" weakened to "covered or
  dead", the idle objects exempt; `JCov.toD` with `D = ∅`).
* `JCovD.step`: across any step, with `D' = D ∪` the objects no longer
  covered, given that an object losing its cover is then dead, and the dead
  stay dead (`JCovD.same`: the frame for steps keeping the MDB's caps;
  `JCovD.delete`: a slot's cap removed, the objects of its range dead).
* `dead_childless`: an object meeting a childless untyped region is dead,
  so retype removes only dead objects.
* `FinDeadHyp`: P1's finalisation of a final cap leaves its object dead;
  proved per kind from P1's `fin_cap_*.dead` (QueueDead): `finDead_ep`,
  `finDead_ntfn`, `finDead_reply`, `finDead_sc`, `finDead_thread`.
-/
import Fl4Proofs.P3.ScPlaceUt
import Fl4Proofs.P1.QueueDead
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **A dead object** (module docstring). -/
def DeadP (H : Heap) (s : S) (q : U64) : Prop :=
  (H q = some .tcb → L.mem s (P1.stA q) = sched.TS_INACTIVE ∧
    L.mem s (scA q) = 0#u64 ∧ L.mem s (boundA q) = 0#u64 ∧
    q ≠ L.actionW s ∧ q ≠ L.idleW s) ∧
  (H q = some .ep → L.epState s q = 0#u64) ∧
  (H q = some .ntfn → L.epState s q ≠ 1#u64 ∧ L.mem s (ntfnBtA q) = 0#u64 ∧ L.mem s (ntfnScA q) = 0#u64) ∧
  (H q = some .reply → L.mem s (rTcbA q) = 0#u64) ∧
  (∀ z, H q = some (.sc z) → L.mem s (scTcbA q) = 0#u64 ∧ L.mem s (scReplyA q) = 0#u64 ∧
    L.mem s (scNtfnA q) = 0#u64)

/-- **`JCov` with a dead set** (module docstring): every object of `th`
and `H` covered, dead, or exempt (`ExAt`): an idle object (`IdleAt`,
outside the untyped regions: `idleOut`) or one inside the kernel-state block
(`KsObj`: the IRQ node's CNodes and `H`'s other block objects; not dead,
`D` holding only reclaimable objects). -/
structure JCovD (thp : TypedHeap) (H : Heap) (G : MdbGhost) (D : Set U64) (Cs : Set U64) (s : S) : Prop where
  th : ∀ q k, thp q = some k → Covered (L.mem s) G q.val (q.val + max (objSize k) 1) ∨ q ∈ D ∨ ExAt (L := L) thp H s q
  h : ∀ q k, H q = some k → Covered (L.mem s) G q.val (q.val + 2 ^ k.bits) ∨ q ∈ D ∨ ExAt (L := L) thp H s q
  dead : ∀ q ∈ D, DeadP (L := L) H s q
  ks : UtKsApart (L := L) G Cs s
  idleOut : IdleOut (L := L) thp H G s

variable {th : TypedHeap} {H : Heap} {G : MdbGhost} {D Cs : Set U64} {s : S}

theorem JCov.toD (h : JCov (L := L) th H G Cs s) : JCovD (L := L) th H G ∅ Cs s :=
  ⟨fun q k hq => (h.th q k hq).imp_right Or.inr, fun q k hq => (h.h q k hq).imp_right Or.inr, fun _ h => h.elim,
    h.ks, h.idleOut⟩

/-- The objects of a typed heap that lose their cover, except those `I`
exempts (the idle objects after). -/
def Uncov (th : TypedHeap) (H : Heap) (mem : U64 → U64) (G : MdbGhost) (I : U64 → Prop) : Set U64 :=
  {q | ¬ I q ∧ ((∃ k, th q = some k ∧ ¬ Covered mem G q.val (q.val + max (objSize k) 1)) ∨
    (∃ k, H q = some k ∧ ¬ Covered mem G q.val (q.val + 2 ^ k.bits)))}

/-- **`JCovD` across a step**: the dead set grows by the objects no longer
covered (and not idle), which must then be dead, and the dead stay dead;
the RAM untyped caps after miss the kernel area and the idle objects. -/
theorem JCovD.step (h : JCovD (L := L) th H G D Cs s) {s' : S} {G' : MdbGhost}
    (hunc : ∀ q, q ∈ Uncov th H (L.mem s') G' (ExAt (L := L) th H s') → DeadP (L := L) H s' q)
    (hdead : ∀ q ∈ D, DeadP (L := L) H s q → DeadP (L := L) H s' q)
    (hks : UtKsApart (L := L) G' Cs s')
    (hio : IdleOut (L := L) th H G' s') :
    JCovD (L := L) th H G' (D ∪ Uncov th H (L.mem s') G' (ExAt (L := L) th H s')) Cs s' := by
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, fun q hq => ?_, hks, hio⟩
  · by_cases hc : Covered (L.mem s') G' q.val (q.val + max (objSize k) 1)
    · exact Or.inl hc
    · by_cases hi : ExAt (L := L) th H s' q
      · exact Or.inr (Or.inr hi)
      · exact Or.inr (Or.inl (Or.inr ⟨hi, Or.inl ⟨k, hq, hc⟩⟩))
  · by_cases hc : Covered (L.mem s') G' q.val (q.val + 2 ^ k.bits)
    · exact Or.inl hc
    · by_cases hi : ExAt (L := L) th H s' q
      · exact Or.inr (Or.inr hi)
      · exact Or.inr (Or.inl (Or.inr ⟨hi, Or.inr ⟨k, hq, hc⟩⟩))
  · rcases hq with hq | hq
    · exact hdead q hq (h.dead q hq)
    · exact hunc q hq

/-- **A cover kept**: a cap of the MDB kept by the step (in the MDB after,
the same cap) covers the same range. -/
theorem covered_keep {m m' : U64 → U64} {G' : MdbGhost} {lo hi : Nat} (hc : Covered m G lo hi)
    (hk : ∀ y ∈ G.chains.flatten, physF (capV m y) = true → isUt (capV m y) = false →
      y ∈ G'.chains.flatten ∧ capV m' y = capV m y) : Covered m' G' lo hi := by
  obtain ⟨y, hy, hp, hu, hb, ht⟩ := hc
  obtain ⟨hy', e⟩ := hk y hy hp hu
  exact ⟨y, hy', by rw [e]; exact hp, by rw [e]; exact hu, by rw [e]; exact hb, by rw [e]; exact ht⟩

/-- **`JCovD` across a step keeping the MDB's covering caps** (creating and
destroying no object): nothing loses its cover, the idle word is kept, and
the dead stay dead. -/
theorem JCovD.same (h : JCovD (L := L) th H G D Cs s) {s' : S} {G' : MdbGhost}
    (hk : ∀ y ∈ G.chains.flatten, physF (capV (L.mem s) y) = true → isUt (capV (L.mem s) y) = false →
      y ∈ G'.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y)
    (hdead : ∀ q ∈ D, DeadP (L := L) H s q → DeadP (L := L) H s' q)
    (hks : UtKsApart (L := L) G' Cs s')
    (hidl : IdleKeep (L := L) s s') (hkb : L.ksb s' = L.ksb s) (hio : IdleOut (L := L) th H G' s') :
    JCovD (L := L) th H G' D Cs s' := by
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, fun q hq => hdead q hq (h.dead q hq), hks, hio⟩
  · rcases h.th q k hq with hc | hd | hi
    · exact Or.inl (covered_keep hc hk)
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr ((exAt_of hidl hkb).2 hi))
  · rcases h.h q k hq with hc | hd | hi
    · exact Or.inl (covered_keep hc hk)
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr ((exAt_of hidl hkb).2 hi))

/-- **`JCovD` across the removal of one slot's cap** (`delete`'s
`empty_slot`, after the finalisation): every other cap of the MDB is kept;
an object covered by the removed cap `c` is then dead (P1's `FinDeadHyp`
for a final cap; for a non-final one another cap covers it, `hother`). -/
theorem JCovD.delete (h : JCovD (L := L) th H G D Cs s) {s' : S} {G' : MdbGhost} {x : U64}
    (hk : ∀ y ∈ G.chains.flatten, y ≠ x → physF (capV (L.mem s) y) = true → isUt (capV (L.mem s) y) = false →
      y ∈ G'.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y)
    (hx : ∀ lo hi, lo < hi → baseF (capV (L.mem s) x) ≤ lo → hi ≤ topF (capV (L.mem s) x) + 1 →
      Covered (L.mem s') G' lo hi ∨ (∀ q, q.val = lo → DeadP (L := L) H s' q))
    (hdead : ∀ q ∈ D, DeadP (L := L) H s q → DeadP (L := L) H s' q)
    (hks : UtKsApart (L := L) G' Cs s')
    (hidl : IdleKeep (L := L) s s') (hkb : L.ksb s' = L.ksb s) (hio : IdleOut (L := L) th H G' s') :
    JCovD (L := L) th H G' (D ∪ Uncov th H (L.mem s') G' (ExAt (L := L) th H s')) Cs s' := by
  have cov : ∀ {lo hi : Nat}, lo < hi → Covered (L.mem s) G lo hi →
      Covered (L.mem s') G' lo hi ∨ (∀ q, q.val = lo → DeadP (L := L) H s' q) := by
    intro lo hi hlh hc
    obtain ⟨y, hy, hp, hu, hb, ht⟩ := hc
    by_cases hyx : y = x
    · subst hyx; exact hx lo hi hlh hb ht
    · obtain ⟨hy', e⟩ := hk y hy hyx hp hu
      exact Or.inl ⟨y, hy', by rw [e]; exact hp, by rw [e]; exact hu, by rw [e]; exact hb, by rw [e]; exact ht⟩
  refine h.step (fun q hq => ?_) hdead hks hio
  obtain ⟨hni, hq⟩ := hq
  rcases hq with ⟨k, hq, hnc⟩ | ⟨k, hq, hnc⟩
  · rcases h.th q k hq with hc | hd | hi
    · rcases cov (by omega) hc with hc' | hd'
      · exact absurd hc' hnc
      · exact hd' q rfl
    · exact hdead q hd (h.dead q hd)
    · exact absurd ((exAt_of hidl hkb).2 hi) hni
  · rcases h.h q k hq with hc | hd | hi
    · rcases cov (by have := Nat.one_le_two_pow (n := k.bits); omega) hc with hc' | hd'
      · exact absurd hc' hnc
      · exact hd' q rfl
    · exact hdead q hd (h.dead q hd)
    · exact absurd ((exAt_of hidl hkb).2 hi) hni

/-- **An object meeting a childless RAM untyped region is dead** (`ut_free`:
a covered object misses the region; `idleOut`: so does an idle one), so a
retype over the region removes only dead objects. -/
theorem dead_childless (h : JCovD (L := L) th H G D Cs s) (hU : UtInv (L.mem s) G) (hI : MdbInv (L.mem s) G)
    {x : U64} (hx : x ∈ G.chains.flatten) {p sb fi : U64}
    (hcx : capV (L.mem s) x = .Untyped p sb fi false) (hnd : ∀ y, ¬ Mdb.Desc G.par y x) :
    (∀ q k, th q = some k → ¬ (q.val + max (objSize k) 1 ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val) →
      q ∈ D ∧ DeadP (L := L) H s q) ∧
    (∀ q k, H q = some k → ¬ (q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val) →
      q ∈ D ∧ DeadP (L := L) H s q) := by
  refine ⟨fun q k hq hm => ?_, fun q k hq hm => ?_⟩
  · rcases h.th q k hq with hc | hd | hi
    · exact absurd (ut_free hU hI hx hcx hnd (by omega) hc) hm
    · exact ⟨hd, h.dead q hd⟩
    · rcases hi with hi | hi
      · exact absurd ((h.idleOut x hx p sb fi hcx q hi).2.1 k hq) hm
      · obtain ⟨k1, k2⟩ := hi.1 k hq
        have := (h.ks x hx p sb fi hcx).1
        omega
  · rcases h.h q k hq with hc | hd | hi
    · exact absurd (ut_free hU hI hx hcx hnd (by have := Nat.one_le_two_pow (n := k.bits); omega) hc) hm
    · exact ⟨hd, h.dead q hd⟩
    · rcases hi with hi | hi
      · exact absurd ((h.idleOut x hx p sb fi hcx q hi).2.2 k hq) hm
      · obtain ⟨k1, k2⟩ := hi.2 k hq
        have := (h.ks x hx p sb fi hcx).1
        omega

end

/-- The object a cap of a finalisable kind names. -/
def finObj : capability.Cap → U64
  | .Endpoint p _ _ _ _ _ => p
  | .Notification p _ _ _ => p
  | .Reply p _ => p
  | .SchedContext p _ => p
  | .Thread p => p
  | _ => 0#u64

/-- **P1's finalisation of a final cap leaves its object dead**: for the caps
`K s c` (a kind, its object's heap kind and P1 set, and the state conditions
P1's lemma takes), the object `obj c` is `DeadP` afterwards. -/
def FinDeadHyp {S A : Type} (st : machine.Store S) [L : P1.LawfulStore st] (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64)
    (K : S → capability.Cap → Prop) (obj : capability.Cap → U64) : Prop :=
  ∀ (s : S) (a : A) (c : capability.Cap) (ex : Bool), K s c → BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    objects.finalise_cap st ar s a c true ex ⦃ r => DeadP (L := L) H r.2.1 (obj c) ⦄

section fin
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {ar : machine.Arch A}
variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **Endpoint**: `cancel_all_ipc` leaves it idle. -/
theorem finDead_ep : FinDeadHyp st ar T Cs Ω H Sg Rp Scs Nt Z Ac
    (fun _ c => ∃ ep b0 b1 b2 b3 b4, c = .Endpoint ep b0 b1 b2 b3 b4 ∧ H ep = some .ep) finObj := by
  rintro s a c ex ⟨ep, b0, b1, b2, b3, b4, rfl, hH⟩ h
  exact WP.spec_mono (fin_cap_ep.dead (ar := ar) s a ep b0 b1 b2 b3 b4 ex h hH) fun r e =>
    ⟨fun h' => by simp [finObj, hH] at h', fun _ => e, fun h' => by simp [finObj, hH] at h', fun h' => by simp [finObj, hH] at h',
      fun z h' => by simp [finObj, hH] at h'⟩

/-- **Notification**: unbound from its SC and TCB, and not waiting. -/
theorem finDead_ntfn : FinDeadHyp st ar T Cs Ω H Sg Rp Scs Nt Z Ac
    (fun _ c => ∃ n b0 b1 b2, c = .Notification n b0 b1 b2 ∧ n ∈ Nt ∧ H n = some .ntfn) finObj := by
  rintro s a c ex ⟨n, b0, b1, b2, rfl, hn, hH⟩ h
  exact WP.spec_mono (fin_cap_ntfn.dead (ar := ar) s a n b0 b1 b2 ex h hn hH) fun r e =>
    ⟨fun h' => by simp [finObj, hH] at h', fun h' => by simp [finObj, hH] at h', fun _ => e, fun h' => by simp [finObj, hH] at h',
      fun z h' => by simp [finObj, hH] at h'⟩

/-- **Reply**: its `TCB` word cleared. -/
theorem finDead_reply (hA : P0.ArchTotal ar) : FinDeadHyp st ar T Cs Ω H Sg Rp Scs Nt Z Ac
    (fun _ c => ∃ p x, c = .Reply p x ∧ p ∈ Rp ∧ H p = some .reply) finObj := by
  rintro s a c ex ⟨p, x, rfl, hp, hH⟩ h
  exact WP.spec_mono (fin_cap_reply.dead hA s a p x ex h hp) fun r e =>
    ⟨fun h' => by simp [finObj, hH] at h', fun h' => by simp [finObj, hH] at h', fun h' => by simp [finObj, hH] at h', fun _ => e,
      fun z h' => by simp [finObj, hH] at h'⟩

/-- **Scheduling context**: its `TCB`, `REPLY` and `NTFN` words cleared;
P1's conditions: the SC's thread is neither the scheduler action nor idle. -/
theorem finDead_sc (hA : P0.ArchTotal ar) : FinDeadHyp st ar T Cs Ω H Sg Rp Scs Nt Z Ac
    (fun s c => ∃ p x z, c = .SchedContext p x ∧ p ∈ Scs ∧ p ≠ 0#u64 ∧ H p = some (.sc z) ∧
      (L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p)) ∧
      (L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p))) finObj := by
  rintro s a c ex ⟨p, x, z, rfl, hp, hp0, hH, hna, hidle⟩ h
  exact WP.spec_mono (fin_cap_sc.dead hA s a p x ex h hp hp0 hna hidle) fun r e =>
    ⟨fun h' => by simp [finObj, hH] at h', fun h' => by simp [finObj, hH] at h', fun h' => by simp [finObj, hH] at h',
      fun h' => by simp [finObj, hH] at h', fun _ _ => e⟩

/-- **Thread**: inactive, with no SC and no bound notification, neither the
scheduler action nor idle; P1's conditions: the thread is neither the
scheduler action nor idle, and has no VCPU. -/
theorem finDead_thread (hA : P0.ArchTotal ar) : FinDeadHyp st ar T Cs Ω H Sg Rp Scs Nt Z Ac
    (fun s c => ∃ p, c = .Thread p ∧ p ∈ T ∧ H p = some .tcb ∧ L.actionW s ≠ p ∧ L.idleW s ≠ p ∧
      L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) finObj := by
  rintro s a c ex ⟨p, rfl, hp, hH, hna, hidle, hv0⟩ h
  exact WP.spec_mono (fin_cap_thread.dead hA s a p ex h hp hna hidle hv0) fun r ⟨e1, e2, e3, e4, e5⟩ =>
    ⟨fun _ => ⟨e1, e2, e3, Ne.symm e4, Ne.symm e5⟩, fun h' => by simp [finObj, hH] at h',
      fun h' => by simp [finObj, hH] at h', fun h' => by simp [finObj, hH] at h', fun z h' => by simp [finObj, hH] at h'⟩

end fin

end

end Fl4Proofs.P3.Sched

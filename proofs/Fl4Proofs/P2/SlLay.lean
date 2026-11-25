/-
# P2 (line p2sl): the decided thread's input words from the ownership map

`slThrIn_of`: `SlThrIn` (P2/SlThr.lean) from the layout and the entry's glue facts, with the read
set `SlRS` as defined (aligned words this path may read by `OwnMap.own`):

* the current thread's fault-handler slot is one of its TCB slots, gate-owned (`own_tslot`);
* the handler endpoint's head / tail-state words and the reply object's thread word are
  lock-owned (`.obj` region), read under fl4-sync's locks (`slRS_of_lock`);
* the live decided thread's `AFFINITY` is gate-owned (`af_of_tcb`);
* a word in an object or slot region is not a prefix word (`SlEnt.dsR`: prefix words lie in
  node regions or the current TCB).

Premises:
* `RegionOKX K` [J]: companion of `OwnMap.RegionOK` (p2c's shared file, not edited here): where
  TCB slots, TCB words from offset 192, endpoint / reply / SC / notification words, node words and
  the kernel globals lie, and their alignment. To be folded into `RegionOK` later; P3's layout lemmas
  (placed objects, `HeapOK` disjointness) are the intended discharge.
* `SlEnt` at the entry state: [J] `dsR` (prefix words: node words and the current thread's
  `FAULT_IP`), `hep` (the handler cap names a heap endpoint), `hrp` (fl4-sync's reply object is a
  heap reply), `hthr` (the live decided thread is a heap TCB: an endpoint in `RECV` queues TCBs, a
  reply names its caller); [P] `lep`, `lrp` (fl4-sync's locks, `crates/fl4-sync/src/lib.rs`).
-/
import Fl4Proofs.P2.SlHome
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

/-- **The layout's regions** [J] (companion of `RegionOK`, module docstring; fold into it later,
discharge by P3's layout lemmas). -/
structure RegionOKX (K : KLayout) : Prop where
  /-- A TCB's six capability slots (below offset 192): slots of `K.slots`, TCB slots, both words
  in the slot's region, aligned. -/
  tslot : ∀ t, K.heap t = some .tcb → ∀ i : U64, i.val < 6 →
    slotIdx t i ∈ K.slots ∧ TcbSlot K (slotIdx t i) ∧
    region K (core.num.U64.wrapping_add (slotIdx t i) 8#u64) = .slot (slotIdx t i) ∧
    (core.num.U64.wrapping_add (slotIdx t i) 8#u64).val - (slotIdx t i).val = 8 ∧
    Aligned (slotIdx t i) ∧ Aligned (core.num.U64.wrapping_add (slotIdx t i) 8#u64)
  /-- A TCB's aligned words from offset 192 lie in the TCB's region. -/
  tcbW : ∀ t, K.heap t = some .tcb → ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
    region K (core.num.U64.wrapping_add t o) = .tcb t ∧
    (core.num.U64.wrapping_add t o).val - t.val = o.val ∧ Aligned (core.num.U64.wrapping_add t o)
  /-- An endpoint's two words. -/
  epW : ∀ p, K.heap p = some .ep → ∀ o : U64, o.val < 16 → o.val % 8 = 0 →
    region K (core.num.U64.wrapping_add p o) = .obj p ∧ Aligned (core.num.U64.wrapping_add p o)
  /-- A reply object's four words. -/
  rpW : ∀ p, K.heap p = some .reply → ∀ o : U64, o.val < 32 → o.val % 8 = 0 →
    region K (core.num.U64.wrapping_add p o) = .obj p ∧ Aligned (core.num.U64.wrapping_add p o)
  /-- A scheduling context's words (`[p, p + 2 ^ z)`). -/
  scW : ∀ p z, K.heap p = some (.sc z) → ∀ b, InSC p z b → region K b = .sc p
  /-- A scheduling context is aligned, at least 128 bytes (seL4's minimum SC size is 2 ^ 8),
  and does not wrap. -/
  scP : ∀ p z, K.heap p = some (.sc z) → p.val % 8 = 0 ∧ 128 ≤ 2 ^ z ∧ p.val + 2 ^ z ≤ 2 ^ 64
  /-- A notification's eight words. -/
  ntW : ∀ p, K.heap p = some .ntfn → ∀ o : U64, o.val < 64 → o.val % 8 = 0 →
    region K (core.num.U64.wrapping_add p o) = .ntfn p ∧
    (core.num.U64.wrapping_add p o).val - p.val = o.val ∧ Aligned (core.num.U64.wrapping_add p o)
  /-- Node words. -/
  node : ∀ c b, InNode K c b → region K b = .node c
  /-- The kernel globals below the nodes. -/
  ks : ∀ b, K.ksb.val ≤ b.val → b.val < K.ksb.val + 13568 → region K b = .none

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}

/-- A TCB slot's two words are gate-owned. -/
theorem own_tslot (hK : RegionOK K) (hX : RegionOKX K) {t i : U64} (ht : K.heap t = some .tcb)
    (hi : i.val < 6) (m : U64 → U64) :
    own K m (slotIdx t i) = .gate ∧ own K m (core.num.U64.wrapping_add (slotIdx t i) 8#u64) = .gate := by
  obtain ⟨hs, hts, h8, hd, -, -⟩ := hX.tslot t ht i hi
  constructor
  · simp [own, hK.slot _ hs, slotOwner, hts]
  · simp only [own, h8]
    rw [hd]
    simp [slotOwner, hts]

/-- A word of a locked object is in the read set. -/
theorem slRS_of_lock {s : S} {x p : U64} (ha : Aligned x) (h : region K x = .obj p) (hl : Locks s p) :
    SlRS (st := st) K Locks s x := by
  refine ⟨ha, Or.inr (Or.inl ?_)⟩
  show HeldBy (L.cpu s) (Locks s) (own K (L.mem s) x)
  simp only [own, h]
  exact hl

/-- **The entry's layout and glue facts for the decided thread** (module docstring). -/
structure SlEnt (K : KLayout) (Locks : S → U64 → Prop) (found : U64 × U64) (s : S) : Prop where
  /-- [J] the prefix words are node words or the current thread's (`FAULT_IP`). -/
  dsR : ∀ x, SlDS (L := L) s x → (∃ c, region K x = .node c) ∨ region K x = .tcb (L.curW s)
  /-- [J] the fault-handler cap names a heap endpoint (P1 cap validity). -/
  hep : SlTrap st s → IsEp (obj.Slot.cap st (fhA (L := L) s) s) →
    K.heap (resPtr (obj.Slot.cap st (fhA (L := L) s) s)) = some .ep
  /-- [J] fl4-sync's reply object is a heap reply (`fastpath::reply_caps`). -/
  hrp : ¬ SlTrap st s → K.heap found.1 = some .reply
  /-- [J] the live decided thread is a heap TCB (an endpoint in `RECV` queues TCBs, P1's queue
  invariant; a reply object's nonzero `tcb` is its caller, P1's reply invariant). -/
  hthr : SlLive st found.1 s → K.heap (slThr st found.1 s) = some .tcb
  /-- [P] fl4-sync holds the handler endpoint's lock (`lock_object(m, ptr, ..)`,
  crates/fl4-sync/src/lib.rs l.691, before `handle_syscall_local`). -/
  lep : SlTrap st s → IsEp (obj.Slot.cap st (fhA (L := L) s) s) →
    Locks s (resPtr (obj.Slot.cap st (fhA (L := L) s) s))
  /-- [P] fl4-sync holds the reply object's lock (`lock_object(m, r, ..)`, l.703). -/
  lrp : ¬ SlTrap st s → Locks s found.1

/-- A word in an object region is not a prefix word. -/
theorem not_slDS_of_obj {found : U64 × U64} {s : S} (N : SlEnt (st := st) K Locks found s) {x p : U64}
    (h : region K x = .obj p) : ¬ SlDS (L := L) s x := fun hx => by
  rcases N.dsR x hx with ⟨c, e⟩ | e <;> rw [h] at e <;> cases e

/-- **`SlThrIn` from the layout and the entry's glue facts.** -/
theorem slThrIn_of (hK : RegionOK K) (hX : RegionOKX K) {found : U64 × U64} {s : S}
    (hp : PreAcc (L := L) (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) s)
    (hc : K.heap (L.curW s) = some .tcb) (N : SlEnt (st := st) K Locks found s) :
    SlThrIn (st := st) K Locks found.1 s := by
  have hi : (layout.tcb.SLOT_FAULT_HANDLER).val < 6 := by simp [layout.tcb.SLOT_FAULT_HANDLER]
  obtain ⟨-, -, -, -, a0, a8⟩ := hX.tslot _ hc _ hi
  obtain ⟨g0, g8⟩ := own_tslot hK hX hc hi (L.mem s)
  refine ⟨fun _ => ⟨slRS_of_gate a0 g0, slRS_of_gate a8 g8, not_slDS_of_gate hp g0, not_slDS_of_gate hp g8⟩,
    fun hS hE => ?_, fun hS => ?_, fun lv => ?_⟩
  · have he := N.hep hS hE
    have hl := N.lep hS hE
    obtain ⟨r1, a1⟩ := hX.epW _ he layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
    obtain ⟨r2, a2⟩ := hX.epW _ he layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE])
    exact ⟨slRS_of_lock a1 r1 hl, not_slDS_of_obj N r1, slRS_of_lock a2 r2 hl, not_slDS_of_obj N r2⟩
  · obtain ⟨r1, a1⟩ := hX.rpW _ (N.hrp hS) layout.reply.TCB (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
    exact ⟨slRS_of_lock a1 r1 (N.lrp hS), not_slDS_of_obj N r1⟩
  · have ht := N.hthr lv
    exact af_of_tcb hK hp ht (hX.tcbW _ ht 3520#u64 (by simp) (by simp) (by simp)).2.2


variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {p : SProg Bool}

/-- **`PathObl` of the syscall entry from the layout**: `sl_pathObl_sl` with `SlThrIn` given by
`slThrIn_of` (`RegionOKX` [J], `SlEnt` [J]/[P]). -/
theorem sl_pathObl_ent (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K)
    (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {P : S → Prop} (hPE : ∀ s, P s → SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hE : ∀ s, P s → SlEnt (st := st) K Locks found s)
    (hD : ∀ s, P s → SlDecIn (st := st) ar K Locks found s) :
    PathObl st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathObl_sl ar hA hK hU hFp hz hm hPE
    (fun s hP => slThrIn_of hK hX (hPE s hP).preG (hPE s hP).hSt.1 (hE s hP)) hD

/-- **`PathSide` of the syscall entry from the layout**: `sl_pathSide_sl` with `SlThrIn` given by
`slThrIn_of`. -/
theorem sl_pathSide_ent (hS : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hX : RegionOKX K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {P : S → Prop} (hPE : ∀ s, P s → SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hE : ∀ s, P s → SlEnt (st := st) K Locks found s)
    (hD : ∀ s, P s → SlDecIn (st := st) ar K Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s) :
    PathSide st (fun m s a => syscall.handle_syscall_local m ar s a n found)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathSide_sl ar hS hA hK hU hFp hz hm hPE
    (fun s hP => slThrIn_of hK hX (hPE s hP).preG (hPE s hP).hSt.1 (hE s hP)) hD huf

end

end Fl4Proofs.P2.PathObl

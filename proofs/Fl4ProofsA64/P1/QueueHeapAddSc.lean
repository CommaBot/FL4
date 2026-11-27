-- AArch64 port of Fl4Proofs.P1.QueueHeapAddSc (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: **adding zeroed scheduling contexts keeps the invariants**
(`BlkOK.addSc`).  Their words join `Ω` and the frame words `Sg`; they are
inactive (`REFILL_MAX` is zero), so they leave the active set (`Ac` minus the
new SCs); their links are null, and their `CORE` word names core `0`.
-/
import Fl4ProofsA64.P1.QueueHeapAdd
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {N : U64 → Prop} {Cs : Set U64} {s : S} {z : Nat}

/-- A new SC's word. -/
def NewScW (N : U64 → Prop) (z : Nat) (b : U64) : Prop :=
  Aligned b ∧ ∃ c, N c ∧ c.val ≤ b.val ∧ b.val < c.val + 2 ^ z

theorem AddOK.newSc_frame (A : AddOK st H N (.sc z) Cs s) {b : U64} (h : NewScW N z b) :
    b ∈ (H.add N (.sc z)).frame := by
  obtain ⟨ha, c, hc, h1, h2⟩ := h
  exact ⟨ha, c, .sc z, Heap.add_of_mem hc, Or.inr (Or.inl ⟨z, rfl⟩), ⟨h1, h2⟩⟩

theorem AddOK.omega_sc (A : AddOK st H N (.sc z) Cs s) {b : U64} (h : b ∈ (H.add N (.sc z)).omega) :
    b ∈ H.omega ∨ NewScW N z b := by
  obtain ⟨ha, p, k, hp, hk, hin⟩ := h
  rcases Heap.add_eq_some.1 hp with ⟨hn, rfl⟩ | ⟨hn, hp'⟩
  · exact Or.inr ⟨ha, p, hn, hin.1, hin.2⟩
  · exact Or.inl ⟨ha, p, k, hp', hk, hin⟩

theorem AddOK.frame_sc (A : AddOK st H N (.sc z) Cs s) {b : U64} (h : b ∈ (H.add N (.sc z)).frame) :
    b ∈ H.frame ∨ NewScW N z b := by
  obtain ⟨ha, p, k, hp, hk, hin⟩ := h
  rcases Heap.add_eq_some.1 hp with ⟨hn, rfl⟩ | ⟨hn, hp'⟩
  · exact Or.inr ⟨ha, p, hn, hin.1, hin.2⟩
  · exact Or.inl ⟨ha, p, k, hp', hk, hin⟩

theorem AddOK.scs_sc (A : AddOK st H N (.sc z) Cs s) {c : U64} :
    c ∈ (H.add N (.sc z)).scs ↔ c ∈ H.scs ∨ N c := by
  simp only [Heap.scs, Set.mem_setOf_eq, Heap.add_eq_some]
  constructor
  · rintro ⟨z', ⟨hn, -⟩ | ⟨-, h⟩⟩
    · exact Or.inr hn
    · exact Or.inl ⟨z', h⟩
  · rintro (⟨z', h⟩ | hn)
    · exact ⟨z', Or.inr ⟨fun hn => (by rw [A.fresh c hn] at h; cases h), h⟩⟩
    · exact ⟨z, Or.inl ⟨hn, rfl⟩⟩

theorem AddOK.notN (A : AddOK st H N (.sc z) Cs s) {c : U64} (hc : c ∈ H.scs) : ¬ N c := fun hn => by
  obtain ⟨z', h⟩ := hc; rw [A.fresh c hn] at h; cases h

theorem AddOK.scBits_old (A : AddOK st H N (.sc z) Cs s) {c : U64} (hc : c ∈ H.scs) :
    (H.add N (.sc z)).scBits c = H.scBits c := by
  unfold Heap.scBits; rw [Heap.add_of_not (A.notN hc)]

theorem AddOK.scBits_new (A : AddOK st H N (.sc z) Cs s) {c : U64} (hc : N c) :
    (H.add N (.sc z)).scBits c = z := by
  unfold Heap.scBits; rw [Heap.add_of_mem hc]

set_option maxHeartbeats 8000000 in
/-- **`BlkOK` with zeroed SCs added** (of at least the minimum size, with core
`0` a core); the new SCs are not active. -/
theorem BlkOK.addSc (A : AddOK st H N (.sc z) Cs s) (hH : HeapOK H) (hz : 7 ≤ z) (h0Cs : 0#u64 ∈ Cs)
    {Ac : Set U64} (h : BlkOK st H.tcbs Cs H.omega H H.frame H.replies H.scs H.ntfns H.scBits Ac s) :
    BlkOK st (H.add N (.sc z)).tcbs Cs (H.add N (.sc z)).omega (H.add N (.sc z)) (H.add N (.sc z)).frame
      (H.add N (.sc z)).replies (H.add N (.sc z)).scs (H.add N (.sc z)).ntfns (H.add N (.sc z)).scBits
      {c | c ∈ Ac ∧ ¬ N c} s := by
  rw [A.tcbs_eq (by simp), A.replies_eq (by simp), A.ntfns_eq (by simp)]
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hE := hX.2.2
  have SS : ∀ c, c ∈ (H.add N (.sc z)).scs ↔ c ∈ H.scs ∨ N c := fun c => A.scs_sc
  have SSi : ∀ c, c ∈ H.scs → c ∈ (H.add N (.sc z)).scs := fun c hc => (SS c).2 (Or.inl hc)
  have oS := A.omega_sub
  have fS := A.frame_sub
  have h128 : 128 ≤ 2 ^ z := le_trans (by decide) (Nat.pow_le_pow_right (by decide) hz)
  have cP : ∀ c, N c → c.val % 8 = 0 ∧ c.val + 2 ^ z ≤ 2 ^ 64 ∧ c.val % 2 ^ z = 0 := fun c hc => by
    have hd : 8 ∣ 2 ^ z := Nat.pow_dvd_pow 2 (by omega : 3 ≤ z)
    have ha := A.align c hc
    rw [show (HKind.sc z).bits = z from rfl] at ha
    refine ⟨?_, A.fits c hc, ha⟩
    rw [← Nat.mod_mod_of_dvd c.val hd, ha]
  have wv : ∀ c, N c → ∀ o : U64, o.val < 128 → o.val % 8 = 0 →
      Aligned (core.num.U64.wrapping_add c o) ∧ c.val ≤ (core.num.U64.wrapping_add c o).val ∧
        (core.num.U64.wrapping_add c o).val < c.val + 2 ^ z := fun c hc o ho h8 => by
    obtain ⟨p8, pf, -⟩ := cP c hc
    have hv : (core.num.U64.wrapping_add c o).val = c.val + o.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    unfold Aligned; rw [hv]; omega
  have nw : ∀ c, N c → ∀ o : U64, o.val < 128 → o.val % 8 = 0 →
      core.num.U64.wrapping_add c o ∈ (H.add N (.sc z)).frame := fun c hc o ho h8 => by
    obtain ⟨a1, a2, a3⟩ := wv c hc o ho h8; exact A.newSc_frame ⟨a1, c, hc, a2, a3⟩
  have zw : ∀ c, N c → ∀ o : U64, o.val < 128 → o.val % 8 = 0 →
      L.mem s (core.num.U64.wrapping_add c o) = 0#u64 := fun c hc o ho h8 => by
    obtain ⟨a1, a2, a3⟩ := wv c hc o ho h8; exact A.zero c hc _ a1 a2 a3
  have zT : ∀ c, N c → L.mem s (scTcbA c) = 0#u64 := fun c hc =>
    zw c hc layout.sc.TCB (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB])
  have zC : ∀ c, N c → L.mem s (scCoreA c) = 0#u64 := fun c hc =>
    zw c hc layout.sc.CORE (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
  have zR : ∀ c, N c → L.mem s (scReplyA c) = 0#u64 := fun c hc =>
    zw c hc layout.sc.REPLY (by simp [layout.sc.REPLY]) (by simp [layout.sc.REPLY])
  have zN : ∀ c, N c → L.mem s (scNtfnA c) = 0#u64 := fun c hc =>
    zw c hc layout.sc.NTFN (by simp [layout.sc.NTFN]) (by simp [layout.sc.NTFN])
  have zY : ∀ c, N c → L.mem s (scYieldFromA c) = 0#u64 := fun c hc =>
    zw c hc layout.sc.YIELD_FROM (by simp [layout.sc.YIELD_FROM]) (by simp [layout.sc.YIELD_FROM])
  have zM : ∀ c, N c → L.mem s (maxA c) = 0#u64 := fun c hc =>
    zw c hc layout.sc.REFILL_MAX (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])
  have zS : ∀ c, N c → L.mem s (sporA c) = 0#u64 := fun c hc =>
    zw c hc layout.sc.SPORADIC (by simp [layout.sc.SPORADIC]) (by simp [layout.sc.SPORADIC])
  have fT : ∀ c, N c → scTcbA c ∈ (H.add N (.sc z)).frame := fun c hc =>
    nw c hc layout.sc.TCB (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB])
  have fC : ∀ c, N c → scCoreA c ∈ (H.add N (.sc z)).frame := fun c hc =>
    nw c hc layout.sc.CORE (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
  have fR : ∀ c, N c → scReplyA c ∈ (H.add N (.sc z)).frame := fun c hc =>
    nw c hc layout.sc.REPLY (by simp [layout.sc.REPLY]) (by simp [layout.sc.REPLY])
  have fN : ∀ c, N c → scNtfnA c ∈ (H.add N (.sc z)).frame := fun c hc =>
    nw c hc layout.sc.NTFN (by simp [layout.sc.NTFN]) (by simp [layout.sc.NTFN])
  have fY : ∀ c, N c → scYieldFromA c ∈ (H.add N (.sc z)).frame := fun c hc =>
    nw c hc layout.sc.YIELD_FROM (by simp [layout.sc.YIELD_FROM]) (by simp [layout.sc.YIELD_FROM])
  have fM : ∀ c, N c → maxA c ∈ (H.add N (.sc z)).frame := fun c hc =>
    nw c hc layout.sc.REFILL_MAX (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])
  have fS' : ∀ c, N c → sporA c ∈ (H.add N (.sc z)).frame := fun c hc =>
    nw c hc layout.sc.SPORADIC (by simp [layout.sc.SPORADIC]) (by simp [layout.sc.SPORADIC])
  have q : SchedQueuesInv st H.tcbs Cs (H.add N (.sc z)).omega (H.add N (.sc z)) s Q R :=
    { h0 with
      eps := h0.eps.addOther (by simp) A.toAddOKP hH fun a ha => (A.omega_sc ha).imp id fun ⟨hal, c, hc, h1, h2⟩ =>
        ⟨c, hc, hal, h1, h2⟩
      omega := fun a ha => by
        rcases A.omega_sc ha with ha | ⟨hal, c, hc, h1, h2⟩
        · exact h0.omega a ha
        · refine ⟨hal, fun t ht => ?_, fun c' hc' => ?_⟩
          · have := A.disjH c hc t .tcb ht
            rw [show (HKind.tcb).bits = 12 from rfl, show (HKind.sc z).bits = z from rfl] at this; omega
          · have := A.nodes c hc c' hc'; rw [show (HKind.sc z).bits = z from rfl] at this; omega }
  have obj : ObjsOK st (H.add N (.sc z)).omega (H.add N (.sc z)).frame H.replies (H.add N (.sc z)).scs H.ntfns
      (H.add N (.sc z)).scBits s := by
    refine ⟨hO.rp, fun c hc => ?_, fun r hr b ha h1 h2 => fS (hO.rpW r hr b ha h1 h2), fun c hc b ha hin => ?_,
      fun c hc => ?_, fun c hc c' hc' hne => ?_, fun r hr c hc => ?_, fun c hc => ?_, fun n hn => fS (hO.ntW n hn),
      hO.ntRp, fun n hn c hc => ?_, hO.ntAl, hO.ntP, fun n hn => ⟨fS (hO.ntB n hn).1, fS (hO.ntB n hn).2⟩,
      hO.ntORp, fun n hn c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, hO.nt0, hO.rp0, fun c hc => ?_⟩
    · rcases (SS c).1 hc with hc | hc
      · rw [A.scBits_old hc]; exact hO.sc c hc
      · rw [A.scBits_new hc]
        obtain ⟨-, pf, pa⟩ := cP c hc
        have hne := A.nz c hc
        have hc0 : 0 < c.val := by
          rcases Nat.eq_zero_or_pos c.val with h | h
          · exact absurd (UScalar.eq_of_val_eq (by simpa using h)) hne
          · exact h
        refine ⟨⟨?_, pa, pf⟩, hz⟩
        by_contra hl
        have : 2 ^ 64 ≤ 2 ^ z := Nat.pow_le_pow_right (by decide) (by omega)
        omega
    · rcases (SS c).1 hc with hc | hc
      · rw [A.scBits_old hc] at hin; exact oS (hO.scW c hc b ha hin)
      · rw [A.scBits_new hc] at hin; exact Heap.frame_omega (A.newSc_frame ⟨ha, c, hc, hin⟩)
    · rcases (SS c).1 hc with hc | hc
      · exact ⟨fS (hO.fixW c hc).1, fS (hO.fixW c hc).2⟩
      · exact ⟨fT c hc, fC c hc⟩
    · rcases (SS c).1 hc with hc | hc <;> rcases (SS c').1 hc' with hc' | hc'
      · rw [A.scBits_old hc, A.scBits_old hc']; exact hO.scDisj c hc c' hc' hne
      · obtain ⟨z0, h0'⟩ := hc
        have := A.disjH c' hc' c (.sc z0) h0'
        rw [A.scBits_old ⟨z0, h0'⟩, A.scBits_new hc', Heap.scBits_eq h0']
        rw [show (HKind.sc z).bits = z from rfl, show (HKind.sc z0).bits = z0 from rfl] at this; omega
      · obtain ⟨z0, h0'⟩ := hc'
        have := A.disjH c hc c' (.sc z0) h0'
        rw [A.scBits_old ⟨z0, h0'⟩, A.scBits_new hc, Heap.scBits_eq h0']
        rw [show (HKind.sc z).bits = z from rfl, show (HKind.sc z0).bits = z0 from rfl] at this; omega
      · rw [A.scBits_new hc, A.scBits_new hc']
        have := A.disjN c c' hc hc' hne; rw [show (HKind.sc z).bits = z from rfl] at this; exact this
    · rcases (SS c).1 hc with hc | hc
      · rw [A.scBits_old hc]; exact hO.rpSc r hr c hc
      · rw [A.scBits_new hc]
        have := A.disjH c hc r .reply hr
        rw [show (HKind.reply).bits = 5 from rfl, show (HKind.sc z).bits = z from rfl] at this; omega
    · rcases (SS c).1 hc with hc | hc
      · exact fS (hO.repW c hc)
      · exact fR c hc
    · rcases (SS c).1 hc with hc | hc
      · rw [A.scBits_old hc]; exact hO.ntSc n hn c hc
      · rw [A.scBits_new hc]
        have := A.disjH c hc n .ntfn hn; rw [ntfnScA_val (hO.ntP n hn)]
        rw [show (HKind.ntfn).bits = 6 from rfl, show (HKind.sc z).bits = z from rfl] at this; omega
    · rcases (SS c).1 hc with hc | hc
      · rw [A.scBits_old hc]; exact hO.ntOSc n hn c hc
      · rw [A.scBits_new hc]
        have := A.disjH c hc n .ntfn hn
        rw [show (HKind.ntfn).bits = 6 from rfl, show (HKind.sc z).bits = z from rfl] at this; omega
    · rcases (SS c).1 hc with hc | hc
      · exact fS (hO.snW c hc)
      · exact fN c hc
    · rcases (SS c).1 hc with hc | hc
      · exact fS (hO.syW c hc)
      · exact fY c hc
    · rcases (SS c).1 hc with hc | hc
      · exact fS (hO.mxW c hc)
      · exact fM c hc
    · rcases (SS c).1 hc with hc | hc
      · exact hO.sc0 c hc
      · exact A.nz c hc
  have rinv : ReplyInv st H.tcbs H.replies (H.add N (.sc z)).scs s := by
    obtain ⟨⟨r1, r2, r3, r4, r5, r6, r7⟩, r8⟩ := hX.2.1
    refine ⟨⟨r1, r2, fun r hr h0' => ?_, r4, r5, fun c hc h0' => ?_, fun c hc e => ?_⟩, r8⟩
    · obtain ⟨a1, a2⟩ := r3 r hr h0'; exact ⟨fun hb => SSi _ (a1 hb), a2⟩
    · rcases (SS c).1 hc with hc | hc
      · exact r6 c hc h0'
      · exact absurd (zR c hc) h0'
    · rcases (SS c).1 hc with hc | hc
      · exact r7 c hc e
      · exact zR c hc
  have ext : ScExtra st H.tcbs Cs (H.add N (.sc z)).scs H.ntfns s := by
    refine { hE with
      bound := fun t ht h0' => by
        obtain ⟨a1, a2, a3⟩ := hE.bound t ht h0'; exact ⟨SSi _ a1, a2, a3⟩
      cur := SSi _ hE.cur
      core := fun c hc => by
        rcases (SS c).1 hc with hc | hc
        · exact hE.core c hc
        · rw [zC c hc]; exact h0Cs
      nsc := fun n hn h0' => by
        obtain ⟨a1, a2⟩ := hE.nsc n hn h0'; exact ⟨SSi _ a1, a2⟩
      scn := fun c hc h0' => by
        rcases (SS c).1 hc with hc | hc
        · exact hE.scn c hc h0'
        · exact absurd (zN c hc) h0'
      yt := ⟨fun c hc h0' => by
          rcases (SS c).1 hc with hc | hc
          · exact hE.yt.1 c hc h0'
          · exact absurd (zT c hc) h0',
        fun t ht h0' => SSi _ (hE.yt.2.1 t ht h0'),
        fun c hc h0' => by
          rcases (SS c).1 hc with hc | hc
          · exact hE.yt.2.2 c hc h0'
          · exact absurd (zY c hc) h0'⟩
      tsc := fun c hc hc0 h0' => by
        rcases (SS c).1 hc with hc | hc
        · exact hE.tsc c hc hc0 h0'
        · exact absurd (zT c hc) h0'
      bs := ⟨hE.bs.tb, hE.bs.nt, fun c hc hc0 h0' => by
        rcases (SS c).1 hc with hc | hc
        · exact hE.bs.sn c hc hc0 h0'
        · exact absurd (zN c hc) h0'⟩ }
  have sub : ∀ b ∈ (H.add N (.sc z)).frame, b ∈ (H.add N (.sc z)).omega := fun b hb => Heap.frame_omega hb
  have ks : ∀ b ∈ (H.add N (.sc z)).frame, b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 223488 ≤ b.val := by  -- a64: 13568->223488
    intro b hb
    rcases A.frame_sc hb with hb | ⟨hal, c, hc, h1, h2⟩
    · exact hSg.ks b hb
    · have := A.ks c hc; rw [show (HKind.sc z).bits = z from rfl] at this
      obtain ⟨p8, -, pa⟩ := cP c hc
      have hd : 8 ∣ 2 ^ z := Nat.pow_dvd_pow 2 (by omega : 3 ≤ z)
      obtain ⟨m, hm⟩ := hd
      unfold Aligned at hal; omega
  have kO : ∀ o : U64, o.val < 223488 → o.val % 8 = 0 →  -- a64: 13568->223488
      core.num.U64.wrapping_add (L.ksb s) o ∈ (H.add N (.sc z)).omega := fun o h1 h2 => oS (hSg.ksΩ o h1 h2)
  have x : XInv st H.tcbs Cs (H.add N (.sc z)).omega (H.add N (.sc z)).frame H.replies (H.add N (.sc z)).scs H.ntfns
      (H.add N (.sc z)).scBits s := ⟨obj, rinv, ext⟩
  have sc : SCsOK st H.tcbs (H.add N (.sc z)).omega (H.add N (.sc z)).frame (H.add N (.sc z)).scs
      (H.add N (.sc z)).scBits {c | c ∈ Ac ∧ ¬ N c} s := by
    refine ⟨sub, ks, kO, fun t ht h1 h2 b hb => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc h0' => ?_,
      fun c hc => ?_, fun c hc h0' => ?_, fun c hc => ?_, fun c hc => ?_⟩
    · have e1 := A.scBits_old (hE.bound t ht h1).1
      have e2 := A.scBits_old hE.cur
      rw [e1] at hb; rw [e2]; exact hS.disj t ht h1 h2 b hb
    · rcases (SS c).1 hc with hc | hc
      · rw [A.scBits_old hc]
        exact ⟨(hS.all c hc).1, fS (hS.all c hc).2.1, fun b ha hin => fS ((hS.all c hc).2.2 b ha hin)⟩
      · rw [A.scBits_new hc]
        exact ⟨fun h => absurd (zM c hc) h, fM c hc, fun b ha hin => A.newSc_frame ⟨ha, c, hc, hin⟩⟩
    · rcases (SS c).1 hc with hc | hc
      · exact ⟨fun h => (hS.act c hc).1 h.1, fun h => ⟨(hS.act c hc).2 h, A.notN hc⟩⟩
      · exact ⟨fun h => absurd hc h.2, fun h => absurd (zM c hc) h⟩
    · rcases (SS c).1 hc with hc | hc
      · exact ⟨hS.spor c hc h0', A.notN hc⟩
      · exact absurd (zS c hc) h0'
    · rcases (SS c).1 hc with hc | hc
      · exact fS (hS.spSg c hc)
      · exact fS' c hc
    · rcases (SS c).1 hc with hc | hc
      · exact ⟨hS.rep c hc h0', A.notN hc⟩
      · exact absurd (zR c hc) h0'
    · rcases (SS c).1 hc with hc | hc
      · exact fS (hS.repSg c hc)
      · exact fR c hc
    · rcases (SS c).1 hc with hc | hc
      · rw [A.scBits_old hc]; exact hS.scKs c hc
      · rw [A.scBits_new hc]
        have := A.ks c hc; rw [show (HKind.sc z).bits = z from rfl] at this; exact this
  have bnd : BoundInv st H.tcbs {c | c ∈ Ac ∧ ¬ N c} s :=
    { hB with sact := fun t ht hs h0' => ⟨hB.sact t ht hs h0', A.notN (hE.bound t ht h0').1⟩ }
  exact ⟨⟨Q, R, q⟩, bnd, x, sc, ⟨sub, ks, kO⟩⟩

end

end Fl4ProofsA64.P1

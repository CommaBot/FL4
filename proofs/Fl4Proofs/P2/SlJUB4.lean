/-
# P2 (line slhuf, gen 5): `SlPreB` across a user-word write without `UserOK`

Gen 4 (P2/SlJUB3.lean, `sl_pathsKC3`) carried `SlPreB` across a write of a user word from
`hUO` [J]: P1's `UserOK st K.heap.tcbs Cs Ω K.heap K.user` at every bundle state, for the
fixed sets `Cs`, `Ω` of the canonical `Q` (`SlQ`).

## `hUO` is unsatisfiable at P3's sets
At P3's joint relation (`JAtZ.entryInv`) `Ω = Heap.omega H`, which holds every aligned word
of every `other` object of `H`. Every word of `Z.B` (`K.user`, `layoutJ`) lies in a non-device
data page (`JCarry.bufPg`), and every spec arch object is an `other` object of `H` of at least
a page (`SpecCover.arch`). So the user words in the first 4 KiB of their page are `Ω` words:
`SlJAt.user_other` below. P1's `UserOK` asks `b ∉ Ω` of every user word, so it is false at
P3's `Ω` whenever such a word exists (P3's own fast fault path uses the set
`OmegaU = (Heap.omega H \ BufU) ∪ VsU` for the same reason, XTopJointKEntryFF; `OmegaU` still
holds the user-frame words outside IPC buffers, so `UserOK K.user` fails there as well).

## What the transports actually read
`bxi_user` (P1's `xfer_all`) needs only that the written words are off what `BXI`'s invariants
read; `UserOK`'s `b ∉ Ω` is stronger than that. Every invariant of `BXI` reads `Ω` and `Sg`
only through mem-free placement facts ("an `Ω` word is outside the TCBs / nodes / endpoints",
"these words are `Ω` / `Sg` words"), so:
* `BXI.shrinkU`: `BXI` at `Ω`, `Sg` gives `BXI` at `Ω \ U`, `Sg \ U`, given that the words
  `BXI` names as `Ω` / `Sg` words (the replies', SCs', notifications' words, the kernel-state
  block) are no `U` words;
* `BXI.growU`: `BXI` at `Ω`, `Sg` comes back at any state with the same kernel base where `BXI`
  holds at smaller sets (the placement facts are taken from the first state);
* `bxi_userJ`: **`BXI` across a write of user words at a bundle state** for ANY `Ω`, `Sg`: at
  `Ω \ U`, `Sg \ U` (`U` the aligned user words) P1's `UserOK` holds (user words are outside
  the TCBs, endpoints and notifications, `SlJAt.userObj`; outside every node of a core below 64,
  P3's `JAtZ.nodeB`), so `xfer_all` applies; then `growU`.
* `asidOff_agN`: the ASID-table words are no user words (`SlJAt.userAsid`: P3's
  `TopPlaced.disj`, a `Z.B` word is no VSpace word, `vsWrite_vobj`).
* `timerOK_agN`: the timer-tree / node words of `Cs`'s cores are no user words
  (`SlJAt.nuNode64`, P3's `JAtZ.nodeB`), for `Cs` below 64 cores.

The only fact about the parameters left is `hCs`: `∀ c ∈ Cs, c.val < 64` (a fact about the set
`Cs` alone, no state; P3's sets satisfy it: `JKern.csLt`; FL4's `MAX_CORES` is 64). It is
needed: `TimerOK` reads every node of `Cs`, and nothing places the node of a core ≥ 64 away
from user memory.

## Results
* **`SlJAt.preB_wrG`**: `SlPreB` across a user-word write from `hCs`, `SlSyncC` and the locks
  (`hl` [P]).
* `slQ_wrG`, **`sl_pathsKC4`**, `sl_pathsKC4_startAt`: `sl_pathsKC3` with `hUO` [J] replaced by
  `hCs` (static, [P]). Remaining premises: `hCs`, `hlk` [P], `hpz`, and `hSt`, `hA`, `hm`, `a0`.
-/
import Fl4Proofs.P2.SlJUB3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

/-! ## `BXI` over smaller word sets and back -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **`BXI` at `Ω \ U`, `Sg \ U`** (module docstring): the words `BXI` names as `Ω` / `Sg`
words are no `U` words. -/
theorem BXI.shrinkU {U : Set U64} {s : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hrp : ∀ r ∈ Rp, ∀ b : U64, r.val ≤ b.val → b.val < r.val + 32 → b ∉ U)
    (hsc : ∀ c ∈ Scs, ∀ b, InSC c (Z c) b → b ∉ U)
    (hsch : ∀ c ∈ Scs, ∀ o : U64, o.val < 128 → o.val % 8 = 0 → core.num.U64.wrapping_add c o ∉ U)
    (hnt : ∀ n ∈ Nt, ∀ o : U64, o.val < 64 → o.val % 8 = 0 → core.num.U64.wrapping_add n o ∉ U)
    (hks : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 → core.num.U64.wrapping_add (L.ksb s) o ∉ U) :
    BXI st T Cs {a | a ∈ Ω ∧ a ∉ U} H {a | a ∈ Sg ∧ a ∉ U} Rp Scs Nt Z Ac s := by
  obtain ⟨⟨Q, R, hSQ⟩, hB, ⟨hO, hR, hX⟩, hSgK, hS⟩ := h
  obtain ⟨E, EQ, w1, w2, w3, w4, w5, w6⟩ := hSQ.eps
  have hSgU : ∀ b ∈ Sg, b ∉ U → b ∈ ({a | a ∈ Sg ∧ a ∉ U} : Set U64) := fun b hb hu => ⟨hb, hu⟩
  have w3' : ∀ e ∈ E, ∀ a ∈ ({a | a ∈ Ω ∧ a ∉ U} : Set U64), a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val :=
    fun e he a ha => w3 e he a ha.1
  have hom : ∀ a ∈ ({a | a ∈ Ω ∧ a ∉ U} : Set U64), OutsideObjs st T Cs s a := fun a ha => hSQ.omega a ha.1
  refine ⟨⟨Q, R, { hSQ with eps := ⟨E, EQ, w1, w2, w3', w4, w5, w6⟩, omega := hom }⟩, hB,
    ⟨{ hO with
      rpW := fun r hr b ha h1 h2 => hSgU _ (hO.rpW r hr b ha h1 h2) (hrp r hr b h1 h2)
      scW := fun c hc b ha hin => ⟨hO.scW c hc b ha hin, hsc c hc b hin⟩
      fixW := fun c hc => ⟨hSgU _ (hO.fixW c hc).1 (hsch c hc _ (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB])),
        hSgU _ (hO.fixW c hc).2 (hsch c hc _ (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE]))⟩
      repW := fun c hc => hSgU _ (hO.repW c hc) (hsch c hc _ (by simp [layout.sc.REPLY]) (by simp [layout.sc.REPLY]))
      ntW := fun n hn => hSgU _ (hO.ntW n hn) (hnt n hn _ (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC]))
      ntB := fun n hn => ⟨hSgU _ (hO.ntB n hn).1 (hnt n hn _ (by simp [layout.ntfn.BADGE]) (by simp [layout.ntfn.BADGE])),
        hSgU _ (hO.ntB n hn).2 (hnt n hn _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]))⟩
      snW := fun c hc => hSgU _ (hO.snW c hc) (hsch c hc _ (by simp [layout.sc.NTFN]) (by simp [layout.sc.NTFN]))
      syW := fun c hc => hSgU _ (hO.syW c hc)
        (hsch c hc _ (by simp [layout.sc.YIELD_FROM]) (by simp [layout.sc.YIELD_FROM]))
      mxW := fun c hc => hSgU _ (hO.mxW c hc)
        (hsch c hc _ (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])) }, hR, hX⟩,
    ⟨fun b hb => ⟨hSgK.sub b hb.1, hb.2⟩, fun b hb => hSgK.ks b hb.1,
      fun o h1 h2 => ⟨hSgK.ksΩ o h1 h2, hks o h1 h2⟩⟩,
    { hS with
      sub := fun b hb => ⟨hS.sub b hb.1, hb.2⟩
      ks := fun b hb => hS.ks b hb.1
      ksΩ := fun o h1 h2 => ⟨hS.ksΩ o h1 h2, hks o h1 h2⟩
      all := fun c hc => ⟨(hS.all c hc).1,
        hSgU _ (hS.all c hc).2.1 (hsch c hc _ (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])),
        fun b ha hin => hSgU _ ((hS.all c hc).2.2 b ha hin) (hsc c hc b hin)⟩
      spSg := fun c hc => hSgU _ (hS.spSg c hc)
        (hsch c hc _ (by simp [layout.sc.SPORADIC]) (by simp [layout.sc.SPORADIC]))
      repSg := fun c hc => hSgU _ (hS.repSg c hc)
        (hsch c hc _ (by simp [layout.sc.REPLY]) (by simp [layout.sc.REPLY])) }⟩

/-- **`BXI` back at `Ω`, `Sg`** (module docstring): its placement facts from `BXI` at a state
with the same kernel base, everything else from `BXI` at any other sets. -/
theorem BXI.growU {Ω' Sg' : Set U64} {s s' : S} (h0 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hk : L.ksb s' = L.ksb s) (h : BXI st T Cs Ω' H Sg' Rp Scs Nt Z Ac s') :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨⟨Q0, R0, hSQ0⟩, -, ⟨hO0, -, -⟩, hSg0, hS0⟩ := h0
  obtain ⟨E0, EQ0, -, -, v3, -, -, v6⟩ := hSQ0.eps
  obtain ⟨⟨Q, R, hSQ⟩, hB, ⟨-, hR, hX⟩, -, hS⟩ := h
  obtain ⟨E, EQ, w1, w2, -, w4, w5, w6⟩ := hSQ.eps
  have w3' : ∀ e ∈ E, ∀ a ∈ Ω, a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val :=
    fun e he a ha => v3 e ((v6.2.2.1 e).2 ((w6.2.2.1 e).1 he)) a ha
  have hom : ∀ a ∈ Ω, OutsideObjs st T Cs s' a := fun a ha => (hSQ0.omega a ha).ksb hk
  refine ⟨⟨Q, R, { hSQ with eps := ⟨E, EQ, w1, w2, w3', w4, w5, w6⟩, omega := hom }⟩, hB,
    ⟨{ hO0 with }, hR, hX⟩,
    ⟨hSg0.sub, by rw [hk]; exact hSg0.ks, by rw [hk]; exact hSg0.ksΩ⟩,
    { hS with
      sub := hS0.sub
      ks := by rw [hk]; exact hS0.ks
      ksΩ := by rw [hk]; exact hS0.ksΩ
      all := fun c hc => ⟨(hS.all c hc).1, (hS0.all c hc).2⟩
      spSg := hS0.spSg
      repSg := hS0.repSg }⟩

end

/-! ## User words at a bundle state -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem SlJAt.layP {K : KLayout} {s : S} (B : SlJAt (L := L) K s) : LayP K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B; exact B.layP

/-- **User words lie in no TCB, endpoint, notification, reply or SC.** -/
theorem SlJAt.userObj {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {x : U64} (hx : x ∈ K.user)
    {p : U64} {k : HKind} (hp : K.heap p = some k) (hk : ∀ z, k ≠ .other z) : ¬ InW p (2 ^ k.bits) x := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B
  cases k with
  | tcb => exact B.layP.user x hx p _ hp (Or.inl rfl)
  | ntfn => exact B.layP.user x hx p _ hp (Or.inr (Or.inl rfl))
  | sc z => exact B.layP.user x hx p _ hp (Or.inr (Or.inr ⟨z, rfl⟩))
  | ep => exact B.userEp x hx p _ hp (Or.inl rfl)
  | reply => exact B.userEp x hx p _ hp (Or.inr rfl)
  | other z => exact absurd rfl (hk z)

/-- **User words miss the node of every core below 64** (P3's `JAtZ.nodeB`). -/
theorem SlJAt.userNode64 {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {x : U64} (hx : x ∈ K.user)
    {c : U64} (hc : c.val < 64) : x.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ x.val := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B
  rw [B.user] at hx
  obtain ⟨wp, hw, rfl⟩ := hx
  exact B.j.nodeB wp hw c hc

/-- **User words are no ASID-table words** (P3's `TopPlaced.disj`: a `Z.B` word is no VSpace
word, `vsWrite_vobj`). -/
theorem SlJAt.userAsid {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {x : U64} (hx : x ∈ K.user)
    {hi : U64} (hhi : hi.val < 2048) : x ≠ atAF (L.ksb s) hi := by
  obtain ⟨_, _, _, Zx, _, _, _, _, _, σ, B⟩ := B
  rw [B.user] at hx
  obtain ⟨wp, hw, rfl⟩ := hx
  intro e
  have hv : Fl4Proofs.P3.Vs.VsWrite Zx.P (L.ksb s) wp.1 := Or.inl ⟨hi, hhi, e⟩
  have hO : Fl4Proofs.P3.Vs.OObj st Zx.N Zx.T Zx.C Zx.E Zx.R Zx.B Zx.c s σ wp.1 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩))))))
  exact B.j.xtop.fin.1.2.disj wp.1 hO (Fl4Proofs.P3.Vs.vsWrite_vobj B.j.xtop.fin.1.2.vs hv)

/-- **User words are in `other` objects of `H`** (module docstring: why P1's `UserOK` fails at
P3's `Ω = Heap.omega H`): every user word lies in a non-device data page (`JCarry.bufPg`), which
is an `other` object of `H` of at least a page (`SpecCover.arch`); the aligned ones in its first
4 KiB are `Heap.omega H` words. -/
theorem SlJAt.user_other {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {x : U64} (hx : x ∈ K.user) :
    ∃ q n, K.heap q = some (.other n) ∧ 12 ≤ n ∧ q.val ≤ x.val ∧
      (Aligned x → x.val < q.val + 4096 → x ∈ Heap.omega K.heap) := by
  obtain ⟨_, _, _, Zx, _, _, _, _, _, σ, B⟩ := B
  rw [B.user] at hx
  obtain ⟨wp, hw, rfl⟩ := hx
  obtain ⟨q, vms, hq, h1, -⟩ := B.j.carry.bufPg wp hw
  obtain ⟨n, hn, hH⟩ := B.j.cover.arch q _ hq
  have hv : (⟨q⟩ : U64).val = q.toNat := rfl
  have hp : (4096 : Nat) ≤ 2 ^ n := by
    calc (4096 : Nat) = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨q⟩, n, hH, hn, by rw [hv]; exact h1, fun ha hlt =>
    ⟨ha, ⟨q⟩, .other n, hH, Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)), by rw [hv]; exact h1, ?_⟩⟩
  show wp.1.val < (⟨q⟩ : U64).val + 2 ^ n
  omega

/-- **P1's `UserOK` fails at P3's `Ω`** as soon as one aligned user word lies in the first 4 KiB
of the `other` object holding it (e.g. any word of a 4 KiB frame). -/
theorem SlJAt.not_userOK_omega {K : KLayout} {s : S} {T Cs : Set U64} (B : SlJAt (L := L) K s) {x : U64}
    (hx : x ∈ K.user) (ha : Aligned x)
    (h4 : ∀ q n, K.heap q = some (.other n) → q.val ≤ x.val → x.val < q.val + 4096) :
    ¬ UserOK st T Cs (Heap.omega K.heap) K.heap K.user s := fun h => by
  obtain ⟨q, n, hH, -, hq, hO⟩ := B.user_other hx
  exact (h x hx).2.1 (hO ha (h4 q n hH hq))

/-- A node word of a core below 64 is `NU` (at any state with the bundle's kernel base). -/
theorem SlJAt.nuNode64 {K : KLayout} {s X : S} (B : SlJAt (L := L) K s) (hk : L.ksb X = L.ksb s)
    {T : Set U64} {c : U64} (hc : c.val < 64) (hN : NodePlaced st T X c) {o : U64} (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) : NU K (L.nodeAt X c o) := by
  refine ⟨nodeAt_aligned hN ho h8, fun hu => ?_⟩
  have h := B.userNode64 hu hc
  have v := nodeAt_val hN ho
  have e : L.nodeBase X c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
  rw [v, e] at h
  omega

/-- An ASID-table word is `NU` (at any state with the bundle's kernel base). -/
theorem SlJAt.nuAsid {K : KLayout} {s X : S} (B : SlJAt (L := L) K s) (hk : L.ksb X = L.ksb s)
    {hi : U64} (hhi : hi.val < 2048) : NU K (atAF (L.ksb X) hi) := by
  refine ⟨?_, fun hu => B.userAsid hu hhi (by rw [hk])⟩
  rw [hk, B.kc.1]; exact (B.regionOKX.asidT hi hhi).2

/-! ## `BXI`, `AsidOff`, `TimerOK` across a write of user words, for any sets -/

variable {T Cs Ω Sg Ac : Set U64}

/-- **`BXI` across a write of user words at a bundle state, for any `Ω`, `Sg`** (module
docstring; `Cs` below 64 cores). -/
theorem bxi_userJ {K : KLayout} {s X X' : S} (B : SlJAt (L := L) K s) (hk : L.ksb X = L.ksb s)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (h : BXI st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac X)
    (G : Ag st (NU K) X X') :
    BXI st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac X' := by
  have hX := B.regionOKX
  have hkK : L.ksb X = K.ksb := by rw [hk]; exact B.kc.1
  have h1 := BXI.shrinkU (U := {b | b ∈ K.user ∧ Aligned b}) h
    (fun r hr b h1 h2 hu => B.userObj hu.1 (k := .reply) hr (fun z e => by cases e) ⟨h1, by
      show b.val < r.val + 2 ^ 5; omega⟩)
    (fun c hc b hin hu => B.userObj hu.1 (scs_heap hc) (fun z e => by cases e) hin)
    (fun c hc o h1 h2 hu => (nu_scw hX (scs_heap hc) h1 h2).2 hu.1)
    (fun n hn o h1 h2 hu => (nu_of_region hX (hX.ntW n hn o h1 h2).2.2
      (by rw [(hX.ntW n hn o h1 h2).1]; intro h; cases h)).2 hu.1)
    (fun o h1 h2 hu => B.userKs hu.1 (o := o) h1 (by rw [← hkK]))
  have hUO : UserOK st K.heap.tcbs Cs {a | a ∈ Ω ∧ a ∉ {b | b ∈ K.user ∧ Aligned b}} K.heap
      {b | b ∈ K.user ∧ Aligned b} X := by
    intro b hb
    obtain ⟨hu, ha⟩ := hb
    refine ⟨⟨ha, fun t ht => ?_, fun c hc => ?_⟩, fun h => h.2 ⟨hu, ha⟩, fun e he => ?_⟩
    · have := B.userObj hu (k := .tcb) ht (fun z e => by cases e)
      simp only [InW, HKind.bits] at this
      omega
    · have h := B.userNode64 hu (hCs c hc)
      have e : L.nodeBase X c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
      rw [e]; omega
    · have hH := B.layP.heap
      rcases he with he | he
      · have := B.userObj hu he (fun z e => by cases e)
        have hal : e.val % 16 = 0 := by simpa [HKind.bits] using hH.align e _ he
        simp only [InW, HKind.bits] at this
        unfold Aligned at ha
        omega
      · have := B.userObj hu he (fun z e => by cases e)
        have hal : e.val % 64 = 0 := by simpa [HKind.bits] using hH.align e _ he
        simp only [InW, HKind.bits] at this
        unfold Aligned at ha
        omega
  obtain ⟨⟨Q, R, h0⟩, hB, hXi, hSg, hS⟩ := h1
  obtain ⟨h1', hB1, hX1, hS1, hSg1, -⟩ := xfer_all h0 hB hXi hS hSg hUO
    (G.writesIn.mono' fun b hb hu => Or.inr ⟨hu, hb⟩)
  exact BXI.growU h G.k ⟨⟨Q, R, h1'⟩, hB1, hX1, hSg1, hS1⟩

/-- **`AsidOff` at an agreeing state** (the ASID-table words are `NU`). -/
theorem asidOff_agN {K : KLayout} {X X' : S} (hna : ∀ hi : U64, hi.val < 2048 → NU K (atAF (L.ksb X) hi))
    (G : Ag st (NU K) X X') (h : AsidOff (L := L) Ω Sg X) : AsidOff (L := L) Ω Sg X' := by
  intro hi hhi
  rw [G.k]
  have e : L.mem X' (atAF (L.ksb X) hi) = L.mem X (atAF (L.ksb X) hi) := G.m _ (hna hi hhi)
  rw [e]
  exact h hi hhi

/-- **`TimerOK` at an agreeing state**, the node words of `Cs` `NU` (as `timerOK_ag`). -/
theorem timerOK_agN {K : KLayout} {X X' : S} (hX : RegionOKX K) (hTH : ∀ y ∈ T, K.heap y = some .tcb)
    (hnd : ∀ c ∈ Cs, NodePlaced st T X c → ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → NU K (L.nodeAt X c o))
    (G : Ag st (NU K) X X') (h : TimerOK st T Cs X) : TimerOK st T Cs X' := by
  have e : ∀ y ∈ T, ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      L.mem X' (core.num.U64.wrapping_add y o) = L.mem X (core.num.U64.wrapping_add y o) :=
    fun y hy o h1 h2 h3 => G.m _ (nu_tcb hX (hTH y hy) h1 h2 h3)
  have en : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem X' (L.nodeAt X' c o) = L.mem X (L.nodeAt X c o) := fun c hc o ho h8 => by
    rw [nodeAt_of_ksb G.k]; exact G.m _ (hnd c hc (h.npl c hc) o ho h8)
  refine ⟨fun c hc => NodePlaced.of_ksb G.k (h.npl c hc), fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun c hc => ?_, fun c hc => ?_, fun y hy h0 c hc' => ?_, fun y hy => ?_, fun y hy => ?_, fun c hc => ?_⟩
  · unfold tlA; rw [e y hy 3544#u64 (by simp) (by simp) (by simp)]; exact h.lt y hy
  · unfold trA; rw [e y hy 3552#u64 (by simp) (by simp) (by simp)]; exact h.rt y hy
  · unfold tpA; rw [e y hy 3560#u64 (by simp) (by simp) (by simp)]; exact h.pt y hy
  · rw [en c hc _ (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])]; exact h.root c hc
  · rw [en c hc _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])]; exact h.min c hc
  · unfold tdA at h0; unfold thA at hc'
    rw [e y hy 3528#u64 (by simp) (by simp) (by simp)] at h0
    rw [e y hy 3568#u64 (by simp) (by simp) (by simp)] at hc'
    exact h.core y hy h0 c hc'
  · unfold dnA; rw [e y hy 3576#u64 (by simp) (by simp) (by simp)]; exact h.dn y hy
  · unfold dpA; rw [e y hy 3584#u64 (by simp) (by simp) (by simp)]; exact h.dp y hy
  · rw [en c hc _ (by simp [layout.node.DEBUG_TCBS]) (by simp [layout.node.DEBUG_TCBS])]; exact h.dh c hc

end

/-! ## `SlPreB` across a user-word write, no `UserOK` -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {Cs Ω Sg Ac : Set U64}

/-- **`SlPreB` across a user-word write** at a bundle state, for any `Ω`, `Sg` and `Cs` below
64 cores (`hCs`), from fl4-sync's contract `SlSyncC` and the locks (`hl`, [P]) and the
ReplyRecv-guarded fields at the written state (`R`); `SlJAt.preB_wr` without `UserOK`. -/
theorem SlJAt.preB_wrN (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hCs : ∀ c ∈ Cs, c.val < 64) (hC : SlSyncC st n found s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s)
    (R : SlPreRR (st := st) ar K Locks found K.heap.tcbs Cs Ω Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits (L.wr s b v)) :
    SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v) := by
  have hX := B.regionOKX
  have hK := B.regionOK
  have ecur := B.curW_wr hb hba v
  have etr := B.trap_wr hb hba v
  have rws := B.slRWS_wr hb hba v Locks hl
  have back : ∀ a X' a1, LocalPre (st := st) ar (L.wr s b v) a (X', a1) →
      ∃ X, LocalPre (st := st) ar s a (X, a1) ∧ Ag st (NU K) X X' ∧ L.ksb X = L.ksb s :=
    fun a X' a1 LP' => by
      obtain ⟨X, LP, G⟩ := B.lp_wr ar hA E.hT E.hN E.hcT E.hSt.1 hb hba v LP'
      obtain ⟨kX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
      exact ⟨X, LP, G, kX⟩
  refine
  { hT := E.hT
    hN := by rw [L.cpu_wr]; exact NodePlaced.of_ksb (L.ksb_wr _ _ _) E.hN
    hcT := by rw [ecur]; exact E.hcT
    hI := fun a X' a1 LP' => by
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      exact bxi_userJ B kX hCs (E.hI a X a1 LP) G
    hAs := fun a X' a1 LP' => by
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      exact asidOff_agN (fun hi hhi => B.nuAsid kX hhi) G (E.hAs a X a1 LP)
    aff := fun d hd => by
      rw [E.aff d hd]
      exact (wr_nu (x := fld d oAFFINITY) hba hb v
        (nu_tcb hX hd (by rw [oAFF_val]; omega) (by rw [oAFF_val]; omega) (by rw [oAFF_val]))).symm
    hSt := by
      rw [ecur, L.cpu_wr, hl]
      exact ⟨E.hSt.1, safe0_wr hX hb hba v E.hSt.1 E.hSt.2⟩
    hrecv := fun hS' a X' a1 LP' ptr badge dest r C => by
      have hS := etr.1 hS'
      rw [ecur] at C
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have C0 := flt_chk_back (fltDec_nu ar hA B E LP) G C
      have hd := (E.hSd hS a X a1 LP C0).1
      rw [G.m (stA dest) (nu_tcb hX hd (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega)
        (by rw [st_val]))]
      exact E.hrecv hS a X a1 LP C0
    hF := fun hS' a X' a1 LP' => by
      have hS := etr.1 hS'
      rw [ecur]
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      refine ⟨asidOff_agN (fun hi hhi => B.nuAsid kX hhi) G (E.hF hS a X a1 LP).1,
        fun ptr badge dest r C => ?_⟩
      have C0 := flt_chk_back (fltDec_nu ar hA B E LP) G C
      obtain ⟨hr, rest, F⟩ := (E.hF hS a X a1 LP).2 ptr badge dest r C0
      exact ⟨hr, rest, faultEnt_ag hK hX (fun y hy => hy) (flt_ptr_ep ar hA B E LP C0)
        (E.hSd hS a X a1 LP C0).1 (slCom_nu ar hA B E LP).nd G F⟩
    hy0f := fun hS' a X' a1 LP' ptr badge dest r C => by
      have hS := etr.1 hS'
      rw [ecur] at C
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have C0 := flt_chk_back (fltDec_nu ar hA B E LP) G C
      have hd := (E.hSd hS a X a1 LP C0).1
      rw [G.m (yieldA dest) (nu_tcb hX hd (o := 3472#u64) (by simp) (by simp) (by simp))]
      exact E.hy0f hS a X a1 LP C0
    hTm := fun hS' a X' a1 LP' => by
      have hS := etr.1 hS'
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      exact timerOK_agN hX (fun y hy => hy) (fun c hc hN o ho h8 => B.nuNode64 kX (hCs c hc) hN ho h8) G
        (E.hTm hS a X a1 LP)
    hSd := fun hS' a X' a1 LP' ptr badge dest r C => by
      have hS := etr.1 hS'
      rw [ecur] at C ⊢
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have C0 := flt_chk_back (fltDec_nu ar hA B E LP) G C
      obtain ⟨h1, h2, h3, h4⟩ := E.hSd hS a X a1 LP C0
      rw [L.cpu_wr, hl, rws.2]
      exact ⟨h1, safe0_wr hX hb hba v h1 h2, h3, h4⟩
    hPl := R.hPl
    hrz := fun hS' a X' a1 LP' => by
      have hS : ¬ SlTrap st s := fun h => hS' (etr.2 h)
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have hrp : K.heap found.1 = some .reply := (B.rrG hC.fd hS (hC.arm hS)).1
      rw [G.m (rNextA found.1) (nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT])
          (by simp [layout.reply.NEXT])),
        G.m (rPrevA found.1) (nu_rp hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV])
          (by simp [layout.reply.PREV]))]
      exact E.hrz hS a X a1 LP
    hy0r := R.hy0r
    hSu := R.hSu
    hlk := fun hS' => by rw [hl]; exact E.hlk (fun h => hS' (etr.2 h)) }

/-- **`SlPreB` across a user-word write, no `UserOK`** (`Cs` below 64 cores, `SlSyncC`, `hl` [P]). -/
theorem SlJAt.preB_wrG (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hCs : ∀ c ∈ Cs, c.val < 64) (hC : SlSyncC st n found s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s) :
    SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v) :=
  B.preB_wrN ar hA E hCs hC hb hba v hl (B.preRR_wr ar hA E hC hb hba v hl)

end

/-! ## The syscall local path with no `UserOK` premise -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Locks : S → U64 → Prop}
variable {A : Type}
variable {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **`hQ` for `SlQ`** from `Cs` below 64 cores (`hCs`) and the locks (`hlk` [P]). -/
theorem slQ_wrG (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ K m s b v, SlJAt (L := L) K s → SlQ st ar Locks n found Cs Ω Sg Ac K m s → b ∈ K.user →
      Aligned b → SlQ st ar Locks n found Cs Ω Sg Ac K m (L.wr s b v) :=
  fun K m s b v hJ q hb hba =>
    have hl := hlk K s b v hJ hb hba
    ⟨hJ.preB_wrG ar hA q.1 hCs q.2.2.1 hb hba v hl, hJ.entL_wr hb hba v hl q.2.1,
      hJ.syncC_wr hb hba v q.2.2.1, hJ.accR_wr ar hA q.1 hb hba v hl q.2.2.2⟩

/-- **The syscall local path with the canonical `Q`, no `UserOK` premise** (`sl_pathsKC3` with
`hUO` [J] replaced by `hCs`: the fixed core set `Cs` of `SlQ` lies below 64 cores, a fact about
the set alone, [P], true of P3's sets by `JKern.csLt`). Premises: `hCs` [P], `hlk` [P], `hpz`,
and `hSt`, `hA`, `hm`, `a0`. -/
noncomputable def sl_pathsKC4 (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
        (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  sl_pathsKF (Locks := Locks) ar hSt hA hm a0 (SlQ st ar Locks n found Cs Ω Sg Ac)
    (fun _ _ _ _ q => q.1) (fun _ _ _ _ q => q.2.1) (fun _ _ _ _ q => q.2.2.1) (fun _ _ _ _ q => q.2.2.2)
    (slQ_wrG ar hA hCs hlk) hlk hpz

/-- **`StartAt` for `sl_pathsKC4`**. -/
theorem sl_pathsKC4_startAt (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
        (SlRS (st := st) K Locks))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : SlQ st ar Locks n found Cs Ω Sg Ac K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsKC4 (Locks := Locks) ar hSt hA hm a0 hCs hlk hpz () K m hK hU) c hs μ
      ((sl_pathsKC4 (Locks := Locks) ar hSt hA hm a0 hCs hlk hpz () K m hK hU).body σ a) :=
  sl_pathsKF_startAt ar hSt hA hm a0 _ _ _ _ _ (slQ_wrG ar hA hCs hlk) hlk hpz K m hK hU a hJ hq hc hl hμ

end

end Fl4Proofs.P2.PathObl

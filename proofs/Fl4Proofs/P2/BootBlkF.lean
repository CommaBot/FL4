/-
# P2 (line p3mc, gen 35): P1's `BlkOK` (`JAtZ.blk`) at the boot

At `sB` with gen 34's heap `HB` (P1's sets `HB.tcbs = {tiB}`, `HB.scs = {sciB}` of size `2^7`, no reply or
notification; `Ω = HB.omega` = the idle SC, the three paging structures and the kernel-state block; `Sg =
HB.frame` = the idle SC's words), core set `CsB = {0}` and active SCs **`AcB = {sciB}`**:

* `sqi_B` (`SchedQueuesInv`: empty ready / release queues, no endpoint queue, the idle thread current and idle,
  action resume; `Ω` outside the idle TCB and core 0's node);
* `boundInv_B` (`BoundInv`: the idle thread bound to the idle SC, which is active);
* `xInv_B` (`XInv`: `ObjsOK` for the one SC, `ReplyInv` vacuous, `ScExtra`: the idle SC / TCB links, empty
  timer trees `coreTree_B`, no notification);
* `scsOK_B` (`SCsOK`: the idle SC's refills well formed, `refillsWF_B`; the block in `Ω`, P3's `ksH_omega`),
  `sgOK_B`;
* **`blk_B`**: `BlkOK bst HB.tcbs CsB HB.omega HB HB.frame HB.replies HB.scs HB.ntfns HB.scBits AcB sB`.

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootFinF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

/-- The active SCs at the boot: the idle SC. -/
def AcB : Set U64 := {sciB}

/-! ## P1's sets of `HB` -/

theorem tcbs_HB {t : U64} (h : t ∈ HB.tcbs) : t = tiB := by
  rcases HB_cases h with ⟨e, -⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩
  · exact eq_of_val' (by rw [e, tiB_val])
  all_goals cases k

theorem ti_HB : tiB ∈ HB.tcbs := HB_ti

theorem scs_HB {c : U64} (h : c ∈ HB.scs) : c = sciB := by
  obtain ⟨z, hz⟩ := h
  rcases HB_cases hz with ⟨-, k⟩ | ⟨e, -⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩
  · cases k
  · exact eq_of_val' (by rw [e, sciB_val])
  all_goals cases k

theorem sci_HB : sciB ∈ HB.scs := ⟨7, HB_sci⟩

theorem replies_HB {r : U64} (h : r ∈ HB.replies) : False := by
  rcases HB_cases h with ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> cases k

theorem ntfns_HB {n : U64} (h : n ∈ HB.ntfns) : False := by
  rcases HB_cases h with ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> cases k

theorem scBits_HB : HB.scBits sciB = 7 := by unfold Heap.scBits; rw [HB_sci]

/-- The frame words: the idle SC's. -/
theorem frame_HB {b : U64} (h : b ∈ HB.frame) :
    18446744071562096640 ≤ b.val ∧ b.val < 18446744071562096640 + 128 ∧ b.val % 8 = 0 := by
  obtain ⟨ha, p, k, hp, hk, h1, h2⟩ := h
  rcases HB_cases hp with ⟨-, rfl⟩ | ⟨e, rfl⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rcases hk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
  · simp only [HKind.bits, Nat.reducePow] at h2
    exact ⟨by omega, by omega, ha⟩
  all_goals (rcases hk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h)

theorem in_frame {b : U64} (h1 : 18446744071562096640 ≤ b.val) (h2 : b.val < 18446744071562096640 + 128)
    (h8 : b.val % 8 = 0) : b ∈ HB.frame :=
  ⟨h8, sciB, .sc 7, HB_sci, Or.inr (Or.inl ⟨7, rfl⟩), by rw [sciB_val]; exact h1,
    by rw [sciB_val]; simp only [HKind.bits, Nat.reducePow]; omega⟩

/-- An SC word (offset `k < 128`, aligned) is a frame word. -/
theorem scw_frame {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 128) (h8 : k % 8 = 0) :
    core.num.U64.wrapping_add sciB K ∈ HB.frame := by
  have hv := sciB_off hK (by omega)
  exact in_frame (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)

/-- The words of `Ω`: the idle SC, the three paging structures, the kernel-state block. -/
theorem omega_HB {b : U64} (h : b ∈ HB.omega) : b.val % 8 = 0 ∧
    ((18446744071562096640 ≤ b.val ∧ b.val < 18446744071562096640 + 128) ∨
     (18446744071562084352 ≤ b.val ∧ b.val < 18446744071562092544 + 4096) ∨
     (18446744071562100736 ≤ b.val ∧ b.val < 18446744071562100736 + 13568)) := by
  obtain ⟨ha, p, k, hp, hk, h1, h2⟩ := h
  refine ⟨ha, ?_⟩
  rcases HB_cases hp with ⟨-, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ | ⟨rfl, g1, g2, g3, -⟩
  · rcases hk with h | ⟨z, h⟩ | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
  · simp only [HKind.bits, Nat.reducePow] at h2; left; omega
  · simp only [HKind.bits, Nat.reducePow] at h2; right; left; omega
  · simp only [HKind.bits, Nat.reducePow] at h2; right; right; omega
  · simp only [HKind.bits, Nat.reducePow] at h2; right; right; omega

theorem ksOmega_B : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 →
    core.num.U64.wrapping_add (bsL.ksb sB) o ∈ HB.omega := by
  intro o ho h8
  rw [sB_ksb]
  obtain ⟨ha, p, k, hp, hk, hin⟩ := ksH_omega kbB_fit' kbB_al o ho h8
  have hr := ksH_some hp
  rw [kbB_val] at hr
  refine ⟨ha, p, k, ?_, hk, hin⟩
  unfold HB
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact hp

/-! ## `SchedQueuesInv` -/

theorem nodePlaced_B : NodePlaced bst HB.tcbs sB 0#u64 :=
  ⟨by rw [sB_nodeBase _ rfl], by rw [sB_nodeBase _ rfl]; norm_num, fun t ht => by
    rw [tcbs_HB ht, sB_nodeBase _ rfl, tiB_val]; omega⟩

theorem mem_CsB {c : U64} (h : c ∈ CsB) : c = 0#u64 := h

theorem inq0 : bsL.mem sB (inqA tiB) = 0#u64 := tw0 (k := 3592) (by decide) (by omega) (by omega) (by omega) (by omega)
theorem aff0 : bsL.mem sB (affA tiB) = 0#u64 := tw0 (k := 3520) (by decide) (by omega) (by omega) (by omega) (by omega)
theorem prio0 : bsL.mem sB (prioA tiB) = 0#u64 := tw0 (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega)

theorem actionW_B : bsL.actionW sB = 0#u64 := by
  unfold LawfulStore.actionW; rw [sB_cpu]
  exact nw0 act_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem stA_B : bsL.mem sB (P1.stA tiB) = 7#u64 := by
  have : P1.stA tiB = Notif.tStA tiB := rfl
  rw [this]; exact stw

theorem not_blocked7 : ¬ Blocked (7#u64) := by
  simp [Blocked, sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_NTFN]

theorem not_blockedR7 : ¬ BlockedR (7#u64) := by
  simp [BlockedR, Blocked, sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_NTFN,
    sched.TS_BLOCKED_ON_REPLY]

theorem sqi_B : SchedQueuesInv bst HB.tcbs CsB HB.omega HB sB (fun _ _ => []) (fun _ => []) where
  tcbs := fun t ht => by rw [tcbs_HB ht]; exact tiB_addr
  nodes c hc := by rw [mem_CsB hc]; exact nodePlaced_B
  cur := by rw [sB_cpu]; rfl
  aff t ht := by rw [tcbs_HB ht, aff0]; rfl
  prio t ht := by rw [tcbs_HB ht, prio0]; decide
  ready c hc := by
    rw [mem_CsB hc]
    obtain ⟨⟨hrel, hdisj⟩, hbm⟩ := schedCore_B.ready
    exact ⟨⟨fun p hp => ⟨(hrel p hp).nodup, fun _ h => (List.not_mem_nil h).elim, (hrel p hp).head,
      (hrel p hp).last, (hrel p hp).seg⟩, hdisj⟩, hbm⟩
  release c hc := by
    rw [mem_CsB hc]
    have h := schedCore_B.release
    exact ⟨h.nodup, fun _ h => (List.not_mem_nil h).elim, h.head, h.last, h.seg⟩
  inQ _ _ _ _ _ h := (List.not_mem_nil h).elim
  inR _ _ _ h := (List.not_mem_nil h).elim
  queued t ht := by rw [tcbs_HB ht, inq0]; simp
  released t ht := by rw [tcbs_HB ht, inq0]; simp
  excl _ _ h := (List.not_mem_nil h).elim
  action := Or.inl actionW_B
  runQ _ _ _ _ _ h := (List.not_mem_nil h).elim
  runR _ _ _ h := (List.not_mem_nil h).elim
  actOK h := by rw [actionW_B] at h; exact absurd (tcbs_HB h).symm tiB_ne0'
  eps := by
    refine ⟨∅, fun _ => [], fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
      fun t ht _ hb => ?_, ?_⟩
    · rw [tcbs_HB ht, stA_B] at hb; exact absurd hb not_blocked7
    · refine ⟨fun t ht _ hs => ?_, fun t ht _ hs => ?_, fun e => ?_, fun _ h => h.elim, fun _ h => h.elim,
        fun _ h => h.elim⟩
      · rw [tcbs_HB ht, stA_B] at hs
        rcases hs with h | h <;> exact absurd h (by simp [sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_RECV])
      · rw [tcbs_HB ht, stA_B] at hs; exact absurd hs (by simp [sched.TS_BLOCKED_ON_NTFN])
      · constructor
        · intro h; exact h.elim
        · rintro (h | h) <;> rcases HB_cases h with ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> cases k
  curT := by
    rw [sB_cpu]
    have : bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.CUR_THREAD) = tiB := by
      rw [nw curth0 (by omega) (by omega)]; simp [wordB]
    rw [this]; exact ti_HB
  idleT := by
    rw [sB_cpu]
    have : bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.IDLE_THREAD) = tiB := by
      rw [nw (k := 8) (by simp [layout.node.IDLE_THREAD]) (by omega) (by omega)]; simp [wordB]
    rw [this]; exact ti_HB
  ksOut t ht := by rw [tcbs_HB ht, sB_ksb, kbB_val, tiB_val]; omega
  omega a ha := by
    obtain ⟨h8, hr⟩ := omega_HB ha
    refine ⟨h8, fun t ht => ?_, fun c hc => ?_⟩
    · rw [tcbs_HB ht, tiB_val]; omega
    · rw [mem_CsB hc, sB_nodeBase _ rfl]; omega

/-! ## `BoundInv` -/

theorem idleW_B : bsL.idleW sB = tiB := sB_idleW
theorem curW_B : bsL.curW sB = tiB := sB_curW

theorem boundInv_B : BoundInv bst HB.tcbs AcB sB where
  q t ht h := by rw [tcbs_HB ht, inq0] at h; simp at h
  r t ht h := by rw [tcbs_HB ht, inq0] at h; simp at h
  act h := by rw [actionW_B] at h; exact absurd (tcbs_HB h).symm tiB_ne0'
  idle := by rw [idleW_B, scw]; exact sciB_ne0
  resume _ := by rw [curW_B, scw]; exact sciB_ne0
  idleNB := by rw [idleW_B, stA_B]; exact not_blockedR7
  sact t ht _ _ := by rw [tcbs_HB ht, scw]; rfl

/-! ## `XInv` -/

theorem sc0w {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 128) (h8 : k % 8 = 0) (h1 : k ≠ 24) (h2 : k ≠ 72)
    (h3 : k ≠ 88) (h4 : k ≠ 104) (h5 : k ≠ 112) : bsL.mem sB (core.num.U64.wrapping_add sciB K) = 0#u64 :=
  sw0 hK hk h8 h1 h2 h3 h4 h5

theorem scTcbB : bsL.mem sB (scTcbA sciB) = tiB := by
  unfold scTcbA
  rw [memB_at (sciB_off (n := 24) (by simp [layout.sc.TCB]) (by omega)) (by omega)]; simp [wordB]

theorem scCoreB : bsL.mem sB (scCoreA sciB) = 0#u64 := by
  unfold scCoreA
  exact sw0 (k := 16) (by simp [layout.sc.CORE]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

theorem scReplyB : bsL.mem sB (scReplyA sciB) = 0#u64 := by
  unfold scReplyA
  exact sw0 (k := 32) (by simp [layout.sc.REPLY]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

theorem scNtfnB : bsL.mem sB (scNtfnA sciB) = 0#u64 := by
  unfold scNtfnA
  exact sw0 (k := 40) (by simp [layout.sc.NTFN]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

theorem scYfB : bsL.mem sB (scYieldFromA sciB) = 0#u64 := by
  unfold scYieldFromA
  exact sw0 (k := 56) (by simp [layout.sc.YIELD_FROM]) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem sporB : bsL.mem sB (sporA sciB) = 0#u64 := by
  unfold sporA
  exact sw0 (k := 64) (by simp [layout.sc.SPORADIC]) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem objsOK_B : ObjsOK bst HB.omega HB.frame HB.replies HB.scs HB.ntfns HB.scBits sB where
  rp _ h := (replies_HB h).elim
  sc c hc := by rw [scs_HB hc, scBits_HB]; exact ⟨refillsWF_B.placed, le_refl _⟩
  rpW _ h := (replies_HB h).elim
  scW c hc b hb hin := by
    rw [scs_HB hc, scBits_HB] at hin
    obtain ⟨h1, h2⟩ := hin
    rw [sciB_val] at h1 h2
    exact Heap.frame_omega (in_frame h1 (by simp only [Nat.reducePow] at h2; omega) hb)
  fixW c hc := by
    rw [scs_HB hc]
    exact ⟨scw_frame (k := 24) (by simp [layout.sc.TCB]) (by omega) (by omega),
      scw_frame (k := 16) (by simp [layout.sc.CORE]) (by omega) (by omega)⟩
  scDisj c hc c' hc' hne := absurd ((scs_HB hc).trans (scs_HB hc').symm) hne
  rpSc _ h := (replies_HB h).elim
  repW c hc := by rw [scs_HB hc]; exact scw_frame (k := 32) (by simp [layout.sc.REPLY]) (by omega) (by omega)
  ntW _ h := (ntfns_HB h).elim
  ntRp _ h := (ntfns_HB h).elim
  ntSc _ h := (ntfns_HB h).elim
  ntAl _ h := (ntfns_HB h).elim
  ntP _ h := (ntfns_HB h).elim
  ntB _ h := (ntfns_HB h).elim
  ntORp _ h := (ntfns_HB h).elim
  ntOSc _ h := (ntfns_HB h).elim
  snW c hc := by rw [scs_HB hc]; exact scw_frame (k := 40) (by simp [layout.sc.NTFN]) (by omega) (by omega)
  syW c hc := by rw [scs_HB hc]; exact scw_frame (k := 56) (by simp [layout.sc.YIELD_FROM]) (by omega) (by omega)
  mxW c hc := by rw [scs_HB hc]; exact scw_frame (k := 72) (by simp [layout.sc.REFILL_MAX]) (by omega) (by omega)
  nt0 _ h := (ntfns_HB h).elim
  rp0 _ h := (replies_HB h).elim
  sc0 c hc := by rw [scs_HB hc]; exact sciB_ne0

theorem replyInv_B : ReplyInv bst HB.tcbs HB.replies HB.scs sB where
  reply t ht h := by rw [tcbs_HB ht, stA_B] at h; exact absurd h (by simp [sched.TS_BLOCKED_ON_REPLY])
  recv t ht h := by rw [tcbs_HB ht, stA_B] at h; exact absurd h (by simp [sched.TS_BLOCKED_ON_RECV])
  next _ h := (replies_HB h).elim
  prev _ h := (replies_HB h).elim
  back _ h := (replies_HB h).elim
  screp c hc h := by rw [scs_HB hc, scReplyB] at h; exact absurd rfl h
  idle c hc _ := by rw [scs_HB hc]; exact scReplyB
  head _ h := (replies_HB h).elim

theorem coreTree_B : CoreTree bst HB.tcbs sB 0#u64 .leaf where
  rep := TRB.Rep.leaf _ _ (nw0 timer_root_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  nodup := List.nodup_nil
  inT _ h := (List.not_mem_nil h).elim
  armed _ h := (List.not_mem_nil h).elim
  core _ h := (List.not_mem_nil h).elim
  sorted := List.Pairwise.nil
  bal := ⟨0, TRB.Bal.leaf⟩
  black := rfl
  min := nw0 timer_min_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem tz0 {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 4096) (h8 : k % 8 = 0) (h1 : k ≠ 3328) (h2 : k ≠ 3464) :
    Tz HB.tcbs (bsL.mem sB (core.num.U64.wrapping_add tiB K)) := by
  rw [tw0 hK hk h8 h1 h2]; exact Tz.zero

theorem scExtra_B : ScExtra bst HB.tcbs CsB HB.scs HB.ntfns sB where
  bound t ht _ := by
    rw [tcbs_HB ht, scw, scTcbB, scCoreB]
    exact ⟨sci_HB, rfl, rfl⟩
  cur := by rw [sB_cscW]; exact sci_HB
  core c hc := by rw [scs_HB hc, scCoreB]; rfl
  bnd t ht h := by
    rw [tcbs_HB ht, show bsL.mem sB (boundA tiB) = 0#u64 from
      tw0 (k := 3368) (by decide) (by omega) (by omega) (by omega) (by omega)] at h
    exact absurd rfl h
  nsc _ h := (ntfns_HB h).elim
  tm := {
    npl := fun c hc => by rw [mem_CsB hc]; exact nodePlaced_B
    lt := fun y hy => by rw [tcbs_HB hy]; exact tz0 (k := 3544) (by decide) (by omega) (by omega) (by omega) (by omega)
    rt := fun y hy => by rw [tcbs_HB hy]; exact tz0 (k := 3552) (by decide) (by omega) (by omega) (by omega) (by omega)
    pt := fun y hy => by rw [tcbs_HB hy]; exact tz0 (k := 3560) (by decide) (by omega) (by omega) (by omega) (by omega)
    root := fun c hc => by
      rw [mem_CsB hc, nw0 timer_root_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact Tz.zero
    min := fun c hc => by
      rw [mem_CsB hc, nw0 timer_min_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact Tz.zero
    core := fun y hy h => by
      rw [tcbs_HB hy, show bsL.mem sB (tdA tiB) = 0#u64 from
        tw0 (k := 3528) (by decide) (by omega) (by omega) (by omega) (by omega)] at h
      exact absurd rfl h
    dn := fun y hy => by rw [tcbs_HB hy]; exact tz0 (k := 3576) (by decide) (by omega) (by omega) (by omega) (by omega)
    dp := fun y hy => by rw [tcbs_HB hy]; exact tz0 (k := 3584) (by decide) (by omega) (by omega) (by omega) (by omega)
    dh := fun c hc => by
      rw [mem_CsB hc, nw0 debug_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact Tz.zero }
  ntb _ h := (ntfns_HB h).elim
  rb := {
    tree := fun c hc => by rw [mem_CsB hc]; exact ⟨_, coreTree_B⟩
    armed := fun y hy h => by
      rw [tcbs_HB hy, show bsL.mem sB (tdA tiB) = 0#u64 from
        tw0 (k := 3528) (by decide) (by omega) (by omega) (by omega) (by omega)] at h
      exact absurd rfl h
    idle := fun y hy _ => by
      rw [tcbs_HB hy]
      exact ⟨tw0 (k := 3544) (by decide) (by omega) (by omega) (by omega) (by omega),
        tw0 (k := 3552) (by decide) (by omega) (by omega) (by omega) (by omega),
        tw0 (k := 3560) (by decide) (by omega) (by omega) (by omega) (by omega)⟩ }
  scn c hc h := by rw [scs_HB hc, scNtfnB] at h; exact absurd rfl h
  yt := ⟨fun c hc _ => by rw [scs_HB hc, scTcbB]; exact ti_HB,
    fun t ht h => by rw [tcbs_HB ht, yieldB0] at h; exact absurd rfl h,
    fun c hc h => by rw [scs_HB hc, scYfB] at h; exact absurd rfl h⟩
  bs := ⟨fun t ht h => by
      rw [tcbs_HB ht, show bsL.mem sB (boundA tiB) = 0#u64 from
        tw0 (k := 3368) (by decide) (by omega) (by omega) (by omega) (by omega)] at h
      exact absurd rfl h,
    fun _ h => (ntfns_HB h).elim,
    fun c hc _ h => by rw [scs_HB hc, scNtfnB] at h; exact absurd rfl h⟩
  tsc c hc _ _ := by rw [scs_HB hc, scTcbB, scw]
  aff t ht _ := by rw [tcbs_HB ht, scw, scCoreB, aff0]

theorem xInv_B : XInv bst HB.tcbs CsB HB.omega HB.frame HB.replies HB.scs HB.ntfns HB.scBits sB :=
  ⟨objsOK_B, replyInv_B, scExtra_B⟩

/-! ## `SCsOK`, `SgOK` -/

theorem scsOK_B : SCsOK bst HB.tcbs HB.omega HB.frame HB.scs HB.scBits AcB sB where
  sub _ h := Heap.frame_omega h
  ks b h := by
    have := frame_HB h
    rw [sB_ksb, kbB_val]; omega
  ksΩ := ksOmega_B
  disj t ht _ hne := by rw [tcbs_HB ht, scw, sB_cscW] at hne; exact absurd rfl hne
  all c hc := by
    rw [scs_HB hc, scBits_HB]
    refine ⟨fun _ => refillsWF_B, scw_frame (k := 72) (by simp [layout.sc.REFILL_MAX]) (by omega) (by omega),
      fun b hb hin => ?_⟩
    obtain ⟨h1, h2⟩ := hin
    rw [sciB_val] at h1 h2
    exact in_frame h1 (by simp only [Nat.reducePow] at h2; omega) hb
  act c hc := by
    rw [scs_HB hc, rmaxB]
    exact ⟨fun _ => by decide, fun _ => rfl⟩
  spor c hc h := by rw [scs_HB hc, sporB] at h; exact absurd rfl h
  spSg c hc := by rw [scs_HB hc]; exact scw_frame (k := 64) (by simp [layout.sc.SPORADIC]) (by omega) (by omega)
  rep c hc h := by rw [scs_HB hc, scReplyB] at h; exact absurd rfl h
  repSg c hc := by rw [scs_HB hc]; exact scw_frame (k := 32) (by simp [layout.sc.REPLY]) (by omega) (by omega)
  scKs c hc := by rw [scs_HB hc, scBits_HB, sB_ksb, kbB_val, sciB_val]; left; norm_num

theorem sgOK_B : SgOK bst HB.omega HB.frame sB := scsOK_B.sg

/-- **P1's `BlkOK` at the boot** (`JAtZ.blk`). -/
theorem blk_B : BlkOK bst (Heap.tcbs HB) CsB (Heap.omega HB) HB (Heap.frame HB) (Heap.replies HB) (Heap.scs HB)
    (Heap.ntfns HB) (Heap.scBits HB) AcB sB :=
  ⟨⟨_, _, sqi_B⟩, boundInv_B, xInv_B, scsOK_B, sgOK_B⟩

end

end Fl4Proofs.P2.BootSt

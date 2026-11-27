/-
P2 (actv): **the post-`schedule` tail of an entry keeps `AllCores`**.

Every local entry that calls `schedule` (`handle_timer_irq_local`,
`handle_set_timer_local`) ends with `syscall::finish`'s tail:
`activate_thread`, then `vcpu::check` of the (new) current thread. P2's
wrappers (`P2/EntryIrq.lean`, `P2/EntryTmr.lean`) stop at `schedule`'s end;
this module carries `AllCores` over the tail.

* `TW y s0`: the tail's words, for the executing core's current thread `y`:
  words outside the TCBs and nodes that are no SC `REPLY`/`TCB` header
  (`OutsideObjs ∧ NoHdr`: an SC's `CONSUMED`/`YIELD_FROM`, a notification's
  `TAIL_STATE`, a user word, the VCPU's `PENDING` word), `y`'s register words
  (`256 ≤ K < 3328`), `y`'s `YIELD_TO` and `STATE`, and the executing core's
  `SCHED_ACTION`. `TWr`/`TWc` are its first two / three kinds.
  `TW.frames`: such a write keeps the core, the current/idle thread, the
  current SC, every node word but `SCHED_ACTION`, and every TCB field but `y`'s
  registers, `YIELD_TO` and `STATE`. `TW.notLoc`: no `TW` word is a `LocW2`
  word (`y` is no other core's thread).
* **`AllCores.twStep`**: a `TW` step from an `AllCores` state to an `EntryInv`
  state that keeps the action or makes it `CHOOSE_NEW`, and keeps `y`'s state
  or makes a runnable `y` running, ends in `AllCores` (`AllCores.step2`).
* `sched.activate_thread.tw`: `activate_thread` is such a step
  (`complete_yield_to.tw`: the SC's `CONSUMED`/`YIELD_FROM`, `y`'s registers and
  `YIELD_TO`; the restart: `NEXT_IP` and `STATE`); P1's
  `sched.activate_thread.entry` gives `EntryInv`.
* **`vcpu.check.tw`**: `vcpu::check` of the current thread keeps `EntryInv`, as
  a `TW` step: P1's `vcpu.check.vck` (P1/VcpuCheckInv; line vmchk moved the
  proof and `Fl4Proofs.P1.vcpu.check.entry` there), whose words `VckW` are `TW`
  words (`VckW.tw`).
* **`AllCores.tail`**: from `AllCores`, `EntryInv` and `BufAt` at `schedule`'s
  end, the tail ends in `AllCores`.

Named premise of `vcpu.check.tw` / `AllCores.tail`:
`hpw` / `hVW` **[P]** (`VcpuUsr`): a TCB's bound VCPU's `PENDING` word is a
user-class word (`UsrW`: outside the TCBs and nodes, apart from the endpoints
and notifications, off `Sg`, the kernel-global area and the SC objects). A
VCPU is a heap object of its own (`.other 15`, P1 `QueueVcpu`, P3's
`VcpuPl.bound`/`listed`), so this is a placement fact like `VcpuPl`'s.
-/
import Fl4Proofs.P2.EntryEnd
import Fl4Proofs.P1.FastFault
import Fl4Proofs.P1.FastFin
import Fl4Proofs.P1.VcpuCheckInv
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-! ## The tail's words -/

/-- Words outside the TCBs and nodes that are no SC header, and `y`'s register words. -/
def TWr (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (y : U64) (s0 : S) (b : U64) : Prop :=
  (OutsideObjs st T Cs s0 b ∧ NoHdr True Scs b) ∨
  (∃ K : U64, 256 ≤ K.val ∧ K.val < 3328 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add y K)

/-- `TWr` and `y`'s `YIELD_TO` word. -/
def TWc (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (y : U64) (s0 : S) (b : U64) : Prop :=
  TWr st T Cs Scs y s0 b ∨ b = yieldA y

/-- **The tail's words** (module docstring). -/
def TW (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (y : U64) (s0 : S) (b : U64) : Prop :=
  TWc st T Cs Scs y s0 b ∨ b = stA y ∨ b = L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION

theorem TWr.ksb {y : U64} {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0)
    (h : TWr st T Cs Scs y s1 b) : TWr st T Cs Scs y s0 b := by
  rcases h with ⟨ho, hh⟩ | h
  · exact Or.inl ⟨ho.ksb hk.symm, hh⟩
  · exact Or.inr h

theorem TWc.ksb {y : U64} {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0)
    (h : TWc st T Cs Scs y s1 b) : TWc st T Cs Scs y s0 b :=
  h.elim (fun h => Or.inl (TWr.ksb hk h)) Or.inr

theorem TW.ksb {y : U64} {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : TW st T Cs Scs y s1 b) : TW st T Cs Scs y s0 b := by
  rcases h with h | h | h
  · exact Or.inl (TWc.ksb hk h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by rw [h, hc, nodeAt_of_ksb hk]))

theorem TWr.trans {y : U64} {s0 s1 s2 : S} (h1 : WritesIn st s0 s1 (TWr st T Cs Scs y s0))
    (h2 : WritesIn st s1 s2 (TWr st T Cs Scs y s1)) : WritesIn st s0 s2 (TWr st T Cs Scs y s0) :=
  (h1.trans h2).mono fun _ hb => hb.elim id (TWr.ksb h1.1)

theorem TWc.trans {y : U64} {s0 s1 s2 : S} (h1 : WritesIn st s0 s1 (TWc st T Cs Scs y s0))
    (h2 : WritesIn st s1 s2 (TWc st T Cs Scs y s1)) : WritesIn st s0 s2 (TWc st T Cs Scs y s0) :=
  (h1.trans h2).mono fun _ hb => hb.elim id (TWc.ksb h1.1)

theorem TW.trans {y : U64} {s0 s1 s2 : S} (h1 : WritesIn st s0 s1 (TW st T Cs Scs y s0))
    (h2 : WritesIn st s1 s2 (TW st T Cs Scs y s1)) : WritesIn st s0 s2 (TW st T Cs Scs y s0) :=
  (h1.trans h2).mono fun _ hb => hb.elim id (TW.ksb h1.1 h1.2.1)

theorem TWr.tw {y : U64} {s0 s1 : S} (h : WritesIn st s0 s1 (TWr st T Cs Scs y s0)) :
    WritesIn st s0 s1 (TW st T Cs Scs y s0) := h.mono fun _ hb => Or.inl (Or.inl hb)

theorem TWc.tw {y : U64} {s0 s1 : S} (h : WritesIn st s0 s1 (TWc st T Cs Scs y s0)) :
    WritesIn st s0 s1 (TW st T Cs Scs y s0) := h.mono fun _ hb => Or.inl hb

/-! ## What a `TW` write misses -/

theorem TWr.not_fld {y z K : U64} {s0 : S} (hT : TcbPlaced T) (hy : y ∈ T) (hz : z ∈ T) (hK : K.val < 4096)
    (hne : z = y → K.val < 256 ∨ 3328 ≤ K.val) : ¬ TWr st T Cs Scs y s0 (core.num.U64.wrapping_add z K) := by
  rintro (⟨hout, -⟩ | ⟨K', h1, h2, -, e⟩)
  · exact out_ne_field hout hz (hT z hz) hK rfl
  · exact field_ne (hT z hz) (hT y hy) hK (by omega) (fun h => by have := hne h; omega) e

theorem TWc.not_fld {y z K : U64} {s0 : S} (hT : TcbPlaced T) (hy : y ∈ T) (hz : z ∈ T) (hK : K.val < 4096)
    (hne : z = y → K.val < 256 ∨ (3328 ≤ K.val ∧ K.val ≠ 3472)) :
    ¬ TWc st T Cs Scs y s0 (core.num.U64.wrapping_add z K) := by
  rintro (h | e)
  · exact TWr.not_fld hT hy hz hK (fun h => by have := hne h; omega) h
  · have h3 : (3472#u64 : U64).val = 3472 := by simp
    exact field_ne (K2 := 3472#u64) (hT z hz) (hT y hy) hK (by omega) (fun h => by have := hne h; omega) e

theorem TW.not_fld {y z K : U64} {s0 : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s0 c)
    (hcpu : L.cpu s0 ∈ Cs) (hy : y ∈ T) (hz : z ∈ T) (hK : K.val < 4096)
    (hne : z = y → K.val < 256 ∨ (3328 < K.val ∧ K.val ≠ 3472)) :
    ¬ TW st T Cs Scs y s0 (core.num.U64.wrapping_add z K) := by
  rintro (h | e | e)
  · exact TWc.not_fld hT hy hz hK (fun h => by have := hne h; omega) h
  · rw [stA_eq] at e
    have h3 : (3328#u64 : U64).val = 3328 := by simp
    exact field_ne (hT z hz) (hT y hy) hK (by omega) (fun h => by have := hne h; omega) e
  · exact node_ne_field (NP _ hcpu) (by rw [act_val]; omega) hz (hT z hz) hK e.symm

theorem TWc.not_node {y c o : U64} {s0 : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s0 c)
    (hy : y ∈ T) (hc : c ∈ Cs) (ho : o.val < 4288) : ¬ TWc st T Cs Scs y s0 (L.nodeAt s0 c o) := by
  rintro ((⟨hout, -⟩ | ⟨K, -, hK, -, e⟩) | e)
  · exact out_ne_node hout hc (NP c hc) ho rfl
  · exact node_ne_field (NP c hc) ho hy (hT y hy) (by omega) e
  · exact node_ne_field (K := 3472#u64) (NP c hc) ho hy (hT y hy) (by simp) e

theorem TW.not_node {y c o : U64} {s0 : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s0 c)
    (hcpu : L.cpu s0 ∈ Cs) (hy : y ∈ T) (hc : c ∈ Cs) (ho : o.val < 4288)
    (h16 : c = L.cpu s0 → o.val ≠ 16) : ¬ TW st T Cs Scs y s0 (L.nodeAt s0 c o) := by
  rintro (h | e | e)
  · exact TWc.not_node hT NP hy hc ho h
  · rw [stA_eq] at e; exact node_ne_field (NP c hc) ho hy (hT y hy) (by simp) e
  · by_cases hcc : c = L.cpu s0
    · subst hcc
      exact nodeAt_ne (NP _ hcpu) ho (by rw [act_val]; omega) (by rw [act_val]; exact h16 rfl) e
    · exact nodeAt_ne_cpu (NP c hc) (NP _ hcpu) ho (by rw [act_val]; omega) hcc e

theorem TWc.not_st {y : U64} {s0 : S} (hT : TcbPlaced T) (hy : y ∈ T) :
    ¬ TWc st T Cs Scs y s0 (stA y) := by
  rw [stA_eq]; exact TWc.not_fld hT hy hy (by simp) (fun _ => Or.inr ⟨by simp, by simp⟩)

/-- **The frame of a `TW` write.** -/
theorem TW.frames {y : U64} {s s' : S} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hy : y ∈ T) (w : WritesIn st s s' (TW st T Cs Scs y s)) :
    L.cpu s' = L.cpu s ∧ L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ L.idleW s' = L.idleW s ∧
      (∀ z ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        (z = y → K.val < 256 ∨ (3328 < K.val ∧ K.val ≠ 3472)) →
        L.mem s' (core.num.U64.wrapping_add z K) = L.mem s (core.num.U64.wrapping_add z K)) ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (c = L.cpu s → o.val ≠ 16) →
        L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) := by
  have hT := hq.tcbs
  have NP := hq.nodes
  have hc := hq.cur
  have nd : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → (c = L.cpu s → o.val ≠ 16) →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := fun c hc' o ho h8 h16 =>
    w.mem_eq (nodeAt_aligned (NP c hc') ho h8) (TW.not_node hT NP hc hy hc' ho h16)
  refine ⟨w.2.1, ?_, ?_, ?_, fun z hz K hK hK8 hne =>
    w.mem_eq (field_aligned (hT z hz) hK hK8) (TW.not_fld hT NP hc hy hz hK hne), nd⟩
  · unfold LawfulStore.curW
    rw [w.2.1, nodeAt_of_ksb w.1]
    exact nd _ hc _ (by rw [curth0]; omega) (by rw [curth0]) (fun _ => by rw [curth0]; omega)
  · unfold LawfulStore.cscW LawfulStore.nodeA
    rw [w.2.1, nodeAt_of_ksb w.1]
    exact nd _ hc _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (fun _ => by simp [layout.node.CUR_SC])
  · unfold LawfulStore.idleW
    rw [w.2.1, nodeAt_of_ksb w.1]
    exact nd _ hc _ (by rw [idle8]; omega) (by rw [idle8]) (fun _ => by rw [idle8]; omega)

/-- No `TW` word is a protected word of `IdW Kp True` when `y ∉ Kp`. -/
theorem TW.notIdW {y b : U64} {s0 : S} {Kp : Set U64} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s0 c)
    (hcpu : L.cpu s0 ∈ Cs) (hy : y ∈ T) (hyK : y ∉ Kp) (h : TW st T Cs Scs y s0 b) :
    ¬ IdW st Kp True T Cs Scs s0 b := by
  rcases h with ((⟨hout, hh⟩ | ⟨K, h1, h2, -, rfl⟩) | rfl) | rfl | rfl
  · exact notIdW_out NP hout hh
  · exact notIdW_field hT NP hy (by omega) (PrF.of_ne (by omega) (by omega) (by omega) (by omega))
  · exact notIdW_field (K := 3472#u64) hT NP hy (by simp) (PrF.of_ne (by simp) (by simp) (by simp) (by simp))
  · rw [stA_eq]; exact notIdW_field hT NP hy (by simp) (PrF.of_nk hyK (by simp) (by simp))
  · exact notIdW_node NP hcpu (by rw [act_val]; omega)
      (idOff_cur (by rw [act_val]; omega) (by rw [act_val]; omega) (fun _ => by rw [act_val]; omega))

/-- **No `TW` word is a `LocW2` word** (`y` no other core's thread). -/
theorem TW.notLoc {y b : U64} {s0 : S} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s0)
    (hKT : ∀ y ∈ OtherK st T Cs (L.cpu s0) s0, y ∈ T) (hiT : ∀ c ∈ Cs, idleAt st c s0 ∈ T)
    (hiS : ∀ c ∈ Cs, L.mem s0 (scA (idleAt st c s0)) ∈ Scs) (hy : y ∈ T)
    (hyK : y ∉ OtherK st T Cs (L.cpu s0) s0) (h : TW st T Cs Scs y s0 b) : ¬ LocW2 st T Cs (L.cpu s0) s0 b :=
  fun hl => TW.notIdW hq.tcbs hq.nodes hq.cur hy hyK h (locW2_idW hq hO hKT hiT hiS hl)

/-! ## `AllCores` across a `TW` step -/

/-- **A `TW` step keeps `AllCores`** (module docstring). -/
theorem AllCores.twStep {s s' : S} (h : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcpu : L.cpu s ∈ Cs)
    (hS0 : (0#u64) ∉ Scs) (hI : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (w : WritesIn st s s' (TW st T Cs Scs (L.curW s) s)) (he : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s')
    (hst : L.mem s' (stA (L.curW s)) = L.mem s (stA (L.curW s)) ∨
      (Runnable (L.mem s (stA (L.curW s))) ∧ L.mem s' (stA (L.curW s)) = sched.TS_RUNNING))
    (hact : L.actionW s' = L.actionW s ∨ L.actionW s' = sched.ACTION_CHOOSE_NEW) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -, -, -, -⟩ := hI
  have hT := hq.tcbs
  have hy : L.curW s ∈ T := hq.curT
  have hyK : L.curW s ∉ OtherK st T Cs (L.cpu s) s := h.notK (h.curAff _ hcpu)
  have hiT : ∀ c ∈ Cs, idleAt st c s ∈ T := fun c hc => (h.core hc).per.idleT
  have hiS : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ∈ Scs := fun c hc =>
    (hX.2.2.bound _ (hiT c hc) (h.core hc).per.idle).1
  have k : OKeep2 st T Cs (L.cpu s) s s' :=
    OKeep2.ofW hq hX.1 h.KT hiT hiS w fun b hb => TW.notLoc hq hX.1 h.KT hiT hiS hy hyK hb
  obtain ⟨hc', ec, -, ei, fld, -⟩ := TW.frames hq hy w
  have ecA : curAt st (L.cpu s) s' = L.curW s' := by rw [← hc']; rfl
  have eaA : actAt st (L.cpu s) s' = L.actionW s' := by rw [← hc']; rfl
  have eiA : idleAt st (L.cpu s) s' = L.idleW s' := by rw [← hc']; rfl
  have hid : L.mem s (stA (L.idleW s)) = sched.TS_IDLE := h.idleSt _ hcpu
  have hacNT : L.actionW s' ∉ T := by
    rcases hact with e1 | e1
    · rw [e1]; exact h.actNT _ hcpu
    · rw [e1, choose_val]; exact notT_small hT (by simp)
  refine AllCores.step2 h hcpu k hS0 he hc' ?_ ?_ ?_ ?_ ?_ ?_
  · rw [ecA, ec, affA_eq, fld _ hy _ (by simp) (by simp) (fun _ => Or.inr ⟨by simp, by simp⟩), ← affA_eq]
    exact h.curAff _ hcpu
  · intro hTa; rw [eaA] at hTa; exact absurd hTa hacNT
  · rw [ecA, ec]
    rcases hst with e1 | ⟨-, e1⟩
    · rw [e1]; exact h.curNB _ hcpu
    · rw [e1]; exact not_blocked_running
  · intro hn
    rw [ecA, eiA, ec, ei] at hn
    rw [ecA, ec, inqA_eq, fld _ hy _ (by simp) (by simp) (fun _ => Or.inr ⟨by simp, by simp⟩), ← inqA_eq]
    exact h.nq _ hcpu hn
  · rw [eaA]; exact hacNT
  · rw [eiA, ei]
    by_cases hyi : L.curW s = L.idleW s
    · rw [← hyi]
      rcases hst with e1 | ⟨hr, -⟩
      · rw [e1, hyi]; exact hid
      · rw [hyi, hid] at hr; exact absurd hr tsIdle_nr
    · have hiT' : L.idleW s ∈ T := hiT _ hcpu
      rw [stA_eq, fld _ hiT' _ (by simp) (by simp) (fun e => absurd e.symm hyi), ← stA_eq]
      exact hid

/-! ## `activate_thread` -/

/-- `ObjsOK` does not depend on the state (as P1 `FastTailNvm`'s `ObjsOK.any`). -/
theorem ObjsOK.anyT {s s' : S} (h : ObjsOK st Ω Sg Rp Scs Nt Z s) : ObjsOK st Ω Sg Rp Scs Nt Z s' :=
  ⟨h.rp, h.sc, h.rpW, h.scW, h.fixW, h.scDisj, h.rpSc, h.repW, h.ntW, h.ntRp, h.ntSc, h.ntAl, h.ntP, h.ntB,
    h.ntORp, h.ntOSc, h.snW, h.syW, h.mxW, h.nt0, h.rp0, h.sc0⟩

theorem tw_sc {s : S} {i o : U64} (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hi : i ∈ Scs) (ho : o.val < 128) (h8 : o.val % 8 = 0) (h24 : o.val ≠ 24) (h32 : o.val ≠ 32) :
    Aligned (core.num.U64.wrapping_add i o) ∧ ∀ y, TWr st T Cs Scs y s (core.num.U64.wrapping_add i o) := by
  obtain ⟨hP, hz⟩ := hO.sc i hi
  obtain ⟨c8, c128, cfit⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz ho
  have ha : Aligned (core.num.U64.wrapping_add i o) := by unfold Aligned; rw [hv]; omega
  have hin : InSC i (Z i) (core.num.U64.wrapping_add i o) := ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  exact ⟨ha, fun y => Or.inl ⟨hΩ _ (hO.scW i hi _ ha hin),
    noHdr_sc hO hi hin (by rw [hv]; omega) (by rw [hv]; omega)⟩⟩

theorem tw_reg {s : S} {y r v : U64} (hy : TcbAddr y) (hr : r.val < 384) :
    obj.Tcb.set_reg st y s r v ⦃ s' => WritesIn st s s' (TWr st T Cs Scs y s) ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.wrK s y r v hy hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    exact (writesIn_wr (field_aligned hy (by omega) (by omega))).mono fun b e =>
      Or.inr ⟨K, by omega, by omega, by omega, e⟩

theorem schedcontext.update_consumed.tw (hA : P0.ArchTotal ar) {s : S} {a : A} {c y : U64}
    (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hc : c ∈ Scs) :
    schedcontext.update_consumed st ar s a c ⦃ r => WritesIn st s r.2 (TWr st T Cs Scs y s) ⦄ := by
  obtain ⟨ha, hw⟩ := tw_sc (o := layout.sc.CONSUMED) hΩ hO hc (by simp [layout.sc.CONSUMED])
    (by simp [layout.sc.CONSUMED]) (by simp [layout.sc.CONSUMED]) (by simp [layout.sc.CONSUMED])
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec as ⟨x, _hx⟩
  split
  · step as ⟨z, _hz⟩
    refine WP.spec_bind (obj.Sc.set_consumed.spec' s c z) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact hw y)
  · refine WP.spec_bind (obj.Sc.set_consumed.spec' s c 0#u64) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ =>
      (WP.spec_ok _).2 ((writesIn_wr ha).mono fun b e => by rw [e]; exact hw y)

theorem schedcontext.set_consumed.tw (hA : P0.ArchTotal ar) (s : S) (a : A) (c y : U64) (wm : Bool)
    (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hya : TcbAddr y)
    (hc : c ∈ Scs) :
    schedcontext.set_consumed st ar s a c y wm ⦃ s' => WritesIn st s s' (TWr st T Cs Scs y s) ⦄ := by
  unfold schedcontext.set_consumed
  refine WP.spec_bind (schedcontext.update_consumed.tw (y := y) hA hΩ hO hc) ?_
  rintro ⟨x, s1⟩ w1
  simp only at w1
  try simp only [WP.uncurry'_pair]
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s1 true y L.total) fun buf _ => ?_
    refine WP.spec_bind (tw_reg (T := T) (Cs := Cs) (Scs := Scs) (s := s1) (r := layout.reg.BADGE) (v := 0#u64) hya
      (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s2 w2 => ?_
    unfold msg.set_mr
    simp only [show (0#u64 < msg.N_MSG_REGISTERS) = True from by simp [msg.N_MSG_REGISTERS], if_true]
    simp only [msg.msg_register, if_true, Aeneas.Std.bind_ok]
    refine WP.spec_bind (Pₘ := fun r : U64 × S => WritesIn st s2 r.2 (TWr st T Cs Scs y s2)) ?_ ?_
    · refine WP.spec_bind (tw_reg (T := T) (Cs := Cs) (Scs := Scs) (s := s2) (r := layout.reg.R10) hya
        (by simp [layout.reg.R10])) fun s3 hh => ?_
      simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok]; exact hh
    rintro ⟨len, s3⟩ w3
    simp only at w3
    try simp only [WP.uncurry'_pair]
    unfold msginfo.MessageInfo.new msg.set_msg_info
    simp only [Aeneas.Std.bind_ok]
    refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun wd _ => ?_
    exact WP.spec_mono (tw_reg (T := T) (Cs := Cs) (Scs := Scs) (s := s3) (r := layout.reg.MSG_INFO) hya
      (by simp [layout.reg.MSG_INFO, layout.reg.RSI]))
      fun s4 w4 => TWr.trans w1 (TWr.trans w2 (TWr.trans w3 w4))
  · exact (WP.spec_ok _).2 w1

theorem schedcontext.cancel_yield_to.tw (s : S) (y : U64) (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hya : TcbAddr y)
    (hyt : L.mem s (yieldA y) ≠ 0#u64 → L.mem s (yieldA y) ∈ Scs) :
    schedcontext.cancel_yield_to st s y ⦃ s' => WritesIn st s s' (TWc st T Cs Scs y s) ⦄ := by
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, _⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact hyt (by rw [← ei]; simpa using hi)
    obtain ⟨ha1, hw1⟩ := tw_sc (o := layout.sc.YIELD_FROM) hΩ hO hiS (by simp [layout.sc.YIELD_FROM])
      (by simp [layout.sc.YIELD_FROM]) (by simp [layout.sc.YIELD_FROM]) (by simp [layout.sc.YIELD_FROM])
    step with obj.Sc.set_yield_from.spec as ⟨s1, e1⟩
    subst e1
    step with obj.Tcb.set_yield_to.spec as ⟨s2, e2⟩
    subst e2
    have w1 : WritesIn st s (L.wr s (scYieldFromA i) 0#u64) (TWc st T Cs Scs y s) :=
      (writesIn_wr ha1).mono fun b e => Or.inl (by rw [e]; exact hw1 y)
    have w2 : WritesIn st (L.wr s (scYieldFromA i) 0#u64)
        (L.wr (L.wr s (scYieldFromA i) 0#u64) (yieldA y) 0#u64) (TWc st T Cs Scs y s) :=
      (writesIn_wr (field_aligned (K := 3472#u64) hya (by simp) (by simp))).mono fun b e => Or.inr e
    exact (w1.trans w2).mono fun _ hb => hb.elim id id
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

theorem schedcontext.complete_yield_to.tw (hA : P0.ArchTotal ar) (s : S) (a : A) (y : U64)
    (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs s a) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hy : y ∈ T) (hT : TcbPlaced T)
    (hyt : L.mem s (yieldA y) ≠ 0#u64 → L.mem s (yieldA y) ∈ Scs) :
    schedcontext.complete_yield_to st ar s a y ⦃ r => WritesIn st s r.1 (TWc st T Cs Scs y s) ⦄ := by
  have hya := hT y hy
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact hyt (by rw [← ei]; simpa using hi)
    refine WP.spec_bind (schedcontext.set_consumed.tw hA s a i y true hΩ hO hya hiS) fun s1 w1 => ?_
    have ya : Aligned (yieldA y) := field_aligned (K := 3472#u64) hya (by simp) (by simp)
    have ey : L.mem s1 (yieldA y) = L.mem s (yieldA y) :=
      w1.mem_eq ya (TWr.not_fld (K := 3472#u64) hT hy hy (by simp) (fun _ => Or.inr (by simp)))
    have hΩ1 : ∀ a ∈ Ω, OutsideObjs st T Cs s1 a := fun a ha => (hΩ a ha).ksb w1.1
    refine WP.spec_bind (schedcontext.cancel_yield_to.tw s1 y hΩ1 (ObjsOK.anyT hO) hya (by rw [ey]; exact hyt))
      fun s2 w2 => ?_
    exact (WP.spec_ok _).2 (TWc.trans (w1.mono fun _ hb => Or.inl hb) w2)
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- **`activate_thread` is a `TW` step** of the current thread. -/
theorem sched.activate_thread.tw (hA : P0.ArchTotal ar) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.activate_thread st ar s a ⦃ r => WritesIn st s r.1 (TW st T Cs Scs (L.curW s) s) ∧
      (L.actionW r.1 = L.actionW s ∨ L.actionW r.1 = sched.ACTION_CHOOSE_NEW) ∧
      (L.mem r.1 (stA (L.curW s)) = L.mem s (stA (L.curW s)) ∨
        (Runnable (L.mem s (stA (L.curW s))) ∧ L.mem r.1 (stA (L.curW s)) = sched.TS_RUNNING)) ⦄ := by
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -⟩ := h
  have hT := hq.tcbs
  have hcT : L.curW s ∈ T := hq.curT
  have hN := hq.nodes _ hq.cur
  unfold sched.activate_thread
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have ect' : ct = L.curW s := ect
  subst ect'
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => WritesIn st s r.1 (TWc st T Cs Scs (L.curW s) s)) ?_ ?_
  · split
    · exact schedcontext.complete_yield_to.tw hA s a _ hq.omega hX.1 hcT hT (hX.2.2.yt.2.1 _ hcT)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rintro ⟨s1, a1⟩ w1
  try simp only [WP.uncurry'_pair]
  have st1 : L.mem s1 (stA (L.curW s)) = L.mem s (stA (L.curW s)) :=
    w1.mem_eq (by rw [stA_eq]; exact field_aligned (hT _ hcT) (by simp) (by simp)) (TWc.not_st hT hcT)
  have ea1 : L.actionW s1 = L.actionW s := actionW_of w1 hN (TWc.not_node hT hq.nodes hcT hq.cur (by rw [act_val]; omega))
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · rename_i hv
    step with obj.Tcb.reg.spec as ⟨pc⟩
    refine WP.spec_bind (tw_reg (T := T) (Cs := Cs) (Scs := Scs) (s := s1) (r := layout.reg.NEXT_IP) (v := pc)
      (hT _ hcT) (by simp [layout.reg.NEXT_IP])) fun s2 w2 => ?_
    have w12 : WritesIn st s s2 (TWc st T Cs Scs (L.curW s) s) := TWc.trans w1 (w2.mono fun _ hb => Or.inl hb)
    have ea2 : L.actionW s2 = L.actionW s :=
      actionW_of w12 hN (TWc.not_node hT hq.nodes hcT hq.cur (by rw [act_val]; omega))
    have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [w12.2.1]; exact hN.ksb w12.1
    refine WP.spec_bind (sched.set_thread_state.w2 s2 (L.curW s) sched.TS_RUNNING hT hN2 hcT)
      fun s3 ⟨w3, ea3, st3⟩ => ?_
    have w3' : WritesIn st s2 s3 (TW st T Cs Scs (L.curW s) s2) :=
      w3.mono fun b hb => hb.elim (fun e => Or.inr (Or.inl e)) (fun e => Or.inr (Or.inr e))
    refine (WP.spec_ok _).2 ⟨TW.trans (TWc.tw w12) w3', ?_, Or.inr ⟨?_, st3⟩⟩
    · rcases ea3 with e3 | e3
      · exact Or.inl (e3.trans ea2)
      · exact Or.inr e3
    · rw [← st1, ← ev, hv]; exact Or.inr (Or.inl rfl)
  · exact (WP.spec_ok _).2 ⟨TWc.tw w1, Or.inl ea1, Or.inl st1⟩

/-! ## `vcpu::check` (P1 `VcpuCheckInv`) -/

/-- The words of P1's `vcpu.check.vck` are `TW` words. -/
theorem VckW.tw {y b : U64} {s0 : S} (h : VckW st T Cs Scs y s0 b) : TW st T Cs Scs y s0 b := by
  rcases h with (⟨ho, hh⟩ | hr) | e | e
  · exact Or.inl (Or.inl (Or.inl ⟨ho, fun _ => hh⟩))
  · exact Or.inl (Or.inl (Or.inr hr))
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)

/-- The post of `vcpu.check` (and its report) as a `TW` step. -/
abbrev CkPost (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (y : U64) (s s' : S) : Prop :=
  EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ WritesIn st s s' (TW st T Cs Scs y s) ∧
    (L.actionW s' = L.actionW s ∨ L.actionW s' = sched.ACTION_CHOOSE_NEW) ∧
    (L.mem s' (stA y) = L.mem s (stA y) ∨ (Runnable (L.mem s (stA y)) ∧ L.mem s' (stA y) = sched.TS_RUNNING))

theorem CkPost.trans {y : U64} {s s1 s2 : S} (h1 : CkPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s s1)
    (h2 : CkPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s1 s2) : CkPost st T Cs Ω H Sg Rp Scs Nt Z Ac y s s2 := by
  obtain ⟨-, w1, a1, t1⟩ := h1
  obtain ⟨E2, w2, a2, t2⟩ := h2
  refine ⟨E2, TW.trans w1 w2, ?_, ?_⟩
  · rcases a2 with e2 | e2
    · rw [e2]; exact a1
    · exact Or.inr e2
  · rcases t2 with e2 | ⟨r2, e2⟩
    · rw [e2]; exact t1
    · rcases t1 with e1 | ⟨r1, -⟩
      · rw [e1] at r2; exact Or.inr ⟨r2, e2⟩
      · exact Or.inr ⟨r1, e2⟩

/-- A `TW` write keeps the buffer-lookup words of every TCB. -/
theorem TW.ibFr {y : U64} {s s' : S} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hy : y ∈ T) (w : WritesIn st s s' (TW st T Cs Scs y s)) :
    IbFr (L := L) T s s' := by
  obtain ⟨-, -, -, -, fld, -⟩ := TW.frames hq hy w
  refine ⟨w.1, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · show L.mem s' (core.num.U64.wrapping_add t 3512#u64) = L.mem s (core.num.U64.wrapping_add t 3512#u64)
    exact fld t ht _ (by simp) (by simp) (fun _ => Or.inr ⟨by simp, by simp⟩)
  · rw [sbWordA_eq]; exact fld t ht _ (by simp) (by simp) (fun _ => Or.inl (by simp))
  · rw [sbWordA8_eq]; exact fld t ht _ (by simp) (by simp) (fun _ => Or.inl (by simp))

/-- **`vcpu::check` of the current thread keeps `EntryInv`, as a `TW` step**
(P1's `vcpu.check.vck`, moved there by line vmchk). Named premises `hbuf` [P]
(the thread's IPC buffer in `U`) and `hpw` [P]: the bound VCPU's `PENDING` word
is a user word of `U`. -/
theorem vcpu.check.tw (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK U b ⦄)
    (hpw : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING ∈ U) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => CkPost st T Cs Ω H Sg Rp Scs Nt Z Ac (L.curW s) s s' ⦄ := by
  refine WP.spec_mono (vcpu.check.vck hA hNt s a h hU hbuf hpw) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨E, w, ea, est⟩ := hh
  exact ⟨E, w.mono fun _ hb => VckW.tw hb, ea, est⟩

/-! ## The tail -/

/-- **[P] The VCPU placement the tail needs**: every TCB's bound VCPU's
`PENDING` word is a user-class word (`UsrW`). -/
def VcpuUsr (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (s : S) : Prop :=
  ∀ t ∈ T, L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
    UsrW st T Cs H Sg Scs Z s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING)

/-- **The post-`schedule` tail (`activate_thread`, `vcpu::check`) keeps
`AllCores`.** Named premise `hVW` [P] (`VcpuUsr` at the tail's `AllCores`
states); `hS0` [W] (as `AllCores.step2`). -/
theorem AllCores.tail (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {s4 s' : S} {a4 a' : A}
    (h4 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4) (hS0 : (0#u64) ∉ Scs)
    (hI4 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s4) (hBA4 : BufAt st T Cs H Sg Scs Z U s4)
    (hVW : ∀ s : S, AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s → VcpuUsr st T Cs H Sg Scs Z s)
    (e : (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨⟨s5, a5⟩, e5, e'⟩ := bind_eq_ok e
  try simp only [uncurry_apply_pair] at e'
  obtain ⟨t, et, e'⟩ := bind_eq_ok e'
  rw [cur_thread_ok] at et
  have ht : L.curW s5 = t := ok_inj_ff et
  subst ht
  obtain ⟨Q4, R4, hq4⟩ := hI4.1
  have hcpu : L.cpu s4 ∈ Cs := hq4.cur
  have A1 := WP.spec_and (sched.activate_thread.entry hA s4 a4 hI4) (sched.activate_thread.tw hA s4 a4 hI4.blkOK)
  rw [e5, WP.spec_ok] at A1
  try simp only [WP.uncurry'_pair] at A1
  obtain ⟨hI5, w5, ea5, st5⟩ := A1
  have h5 := AllCores.twStep h4 hcpu hS0 hI4 w5 hI5 st5 ea5
  have hcpu5 : L.cpu s5 ∈ Cs := by rw [w5.2.1]; exact hcpu
  have hBA5 : BufAt st T Cs H Sg Scs Z U s5 := BufAt.of_fr hBA4 (TW.ibFr hq4 hq4.curT w5)
  obtain ⟨Q5, R5, hq5⟩ := hI5.1
  have hc5 : L.curW s5 ∈ T := hq5.curT
  have C := vcpu.check.tw (U := {b | UsrW st T Cs H Sg Scs Z s5 b}) hA hNt s5 a5 hI5 (fun b hb => hb)
    (WP.spec_mono (hBA5.2 _ hc5) fun b hb h0 i hi => hBA5.1 _ (hb h0 i hi)) (fun hv => hVW s5 h5 _ hc5 hv)
  rw [e', WP.spec_ok] at C
  try simp only [WP.uncurry'_pair] at C
  obtain ⟨hI', w', ea', st'⟩ := C
  exact AllCores.twStep h5 hcpu5 hS0 hI5 w' hI' st' ea'

end

end Fl4Proofs.P2.Stall

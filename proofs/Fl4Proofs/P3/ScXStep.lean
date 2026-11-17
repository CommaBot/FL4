/-
P3, scheduling contexts: **the SC caps' steps at `XTop`** (TopXAll): an
SC-cap step (FL4 writing only `TFoot` words, the spec changing only
scheduling fields, `ScTKw`) keeps the composite relation, given the
scheduler and notification relations after.

* `EpStateRel.scStep`: the endpoint relation across such a step. Its
  words are not written but for TCB state words (`TFoot` meets `EFoot`
  only there, `tfoot_efoot`), and those agree with the states after (the
  notification relation after); a TCB that changes state blocks on nothing
  before or after (`IpcFree`).
-/
import Fl4Proofs.P3.ScTK
import Fl4Proofs.P3.TopXAll
import Fl4Proofs.P3.IpcSchedLift
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

variable {P : ObjRef → Prop} {σ σ' : State Unit}

theorem ScTKw.ep (h : ScTKw P σ σ') {p : ObjRef} {x : Endpoint} (hk : σ.kheap p = some (.endpoint x)) :
    σ'.kheap p = some (.endpoint x) := by
  have := h.kh p
  rw [hk] at this
  cases e : σ'.kheap p with
  | none => rw [e] at this; exact this.elim
  | some o =>
    rw [e] at this
    rcases this with rfl | ⟨_, _, h1, -⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, h1, -⟩ | ⟨_, _, h1, -⟩ <;> first | rfl | cases h1

/-- A reply keeps its TCB (it may change its SC). -/
theorem ScTKw.reply (h : ScTKw P σ σ') {p : ObjRef} {x : Reply} (hk : σ.kheap p = some (.reply x)) :
    ∃ y, σ'.kheap p = some (.reply y) ∧ y.replyTcb = x.replyTcb := by
  have := h.kh p
  rw [hk] at this
  cases e : σ'.kheap p with
  | none => rw [e] at this; exact this.elim
  | some o =>
    rw [e] at this
    rcases this with rfl | ⟨_, _, h1, -⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, h1, -⟩ | ⟨_, y, h1, rfl, ey⟩
    · exact ⟨x, rfl, rfl⟩
    · cases h1
    · cases h1
    · cases h1
    · cases h1; exact ⟨y, rfl, by rw [ey]⟩

theorem ScTKw.tcb (h : ScTKw P σ σ') {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ TcbSchedOnly x y ∧
      (y.tcbState = x.tcbState ∨ (P p ∧ IpcFree x.tcbState ∧ IpcFree y.tcbState)) := by
  have := h.kh p
  rw [hk] at this
  cases e : σ'.kheap p with
  | none => rw [e] at this; exact this.elim
  | some o =>
    rw [e] at this
    rcases this with rfl | ⟨x1, y1, h1, rfl, h3, h4⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, h1, -⟩ | ⟨_, _, h1, -⟩
    · exact ⟨x, rfl, TcbSchedOnly.refl x, Or.inl rfl⟩
    · cases h1; exact ⟨y1, rfl, h3, h4⟩
    · cases h1
    · cases h1
    · cases h1


theorem ScTKw.keep_other (h : ScTKw P σ σ') {p : ObjRef} {o : KernelObject} (hk : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ y n, o ≠ .schedContext y n) (h3 : ∀ x, o ≠ .notification x)
    (h4 : ∀ x, o ≠ .reply x) :
    σ'.kheap p = some o := by
  have := h.kh p
  rw [hk] at this
  cases e : σ'.kheap p with
  | none => rw [e] at this; exact this.elim
  | some o' =>
    rw [e] at this
    rcases this with rfl | ⟨x, _, e1, -⟩ | ⟨y, _, n, e1, -⟩ | ⟨x, _, e1, -⟩ | ⟨x, _, e1, -⟩
    · rfl
    · exact absurd e1 (h1 x)
    · exact absurd e1 (h2 y n)
    · exact absurd e1 (h3 x)
    · exact absurd e1 (h4 x)

theorem ScTKw.none (h : ScTKw P σ σ') {p : ObjRef} (hk : σ.kheap p = none) : σ'.kheap p = none := by
  have := h.kh p
  rw [hk] at this
  cases e : σ'.kheap p with
  | none => rfl
  | some o => rw [e] at this; exact this.elim

/-- The object before, for an object after of the same kind. -/
theorem ScTKw.back (h : ScTKw P σ σ') {p : ObjRef} {o' : KernelObject} (hk : σ'.kheap p = some o') :
    ∃ o, σ.kheap p = some o ∧ TKObj (P p) o o' := by
  have := h.kh p
  rw [hk] at this
  cases e : σ.kheap p with
  | none => rw [e] at this; exact this.elim
  | some o => rw [e] at this; exact ⟨o, rfl, this⟩

theorem ScTKw.szKeep (h : ScTKw P σ σ') : SzKeep σ σ' := by
  intro p y n hk
  obtain ⟨o, ho, ht⟩ := h.back hk
  rcases ht with rfl | ⟨_, _, -, e, -⟩ | ⟨x, y', m, rfl, e⟩ | ⟨_, _, -, e, -⟩ | ⟨_, _, -, e, -⟩
  · exact ⟨y, ho⟩
  · cases e
  · cases e; exact ⟨x, ho⟩
  · cases e
  · cases e

theorem ScTKw.ckeep (h : ScTKw P σ σ') : Fl4Proofs.P3.CKeep σ σ' := by
  refine ⟨fun o => ⟨fun r cs hc hw => ?_, fun t ht => ?_, fun hn => h.none hn⟩, fun o r cs hc _ => ?_,
    fun o t ht => ?_, h.cdt, h.orig⟩
  · obtain ⟨o0, ho0, htk⟩ := h.back hc
    rcases htk with rfl | ⟨_, _, -, e, -⟩ | ⟨_, _, _, -, e⟩ | ⟨_, _, -, e, -⟩ | ⟨_, _, -, e, -⟩
    · exact ⟨cs, ho0, hw⟩
    all_goals cases e
  · obtain ⟨o0, ho0, htk⟩ := h.back ht
    rcases htk with rfl | ⟨x, _, rfl, -, -⟩ | ⟨_, _, _, -, e⟩ | ⟨_, _, -, e, -⟩ | ⟨_, _, -, e, -⟩
    · exact ⟨t, ho0⟩
    · exact ⟨x, ho0⟩
    all_goals cases e
  · exact h.keep_other hc (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e)
  · obtain ⟨y, hy, hso, -⟩ := h.tcb ht
    refine ⟨y, hy, ?_⟩
    unfold TcbSchedOnly at hso
    rw [hso]; rfl

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

theorem tStA_val' {t : U64} (ht : TcbAddr t) : (tStA t).val = t.val + 3328 := by
  rw [tStA_eq, tw_val ht (by simp)]; rfl

/-- A TCB field or link word other than the state word is no TCB's state word. -/
theorem ne_st_of_tf (hP : EPlaced T E R B) {y a : U64} (hy : y ∈ T) (ha : TF y a ∨ TL y a)
    (hne : a.val ≠ y.val + 3328) : ∀ t ∈ T, a ≠ tStA t := by
  intro t ht e
  have hv := tStA_val' (hP.tcb t ht)
  rw [← e] at hv
  have hr : y.val ≤ a.val ∧ a.val < y.val + 4096 := by
    rcases ha with ⟨h1, h2⟩ | h
    · unfold TOffN at h2; omega
    · unfold TL at h; omega
  by_cases eyt : t = y
  · subst eyt; exact hne hv
  · have := tcb_disj hP hy ht eyt; omega

/-- A word apart from every TCB is no TCB's state word. -/
theorem ne_st_of_apart (hP : EPlaced T E R B) {a : U64} (h : ∀ t ∈ T, a.val < t.val ∨ t.val + 4096 ≤ a.val) :
    ∀ t ∈ T, a ≠ tStA t := by
  intro t ht e
  have hv := tStA_val' (hP.tcb t ht)
  rw [← e] at hv
  have := h t ht; omega

/-- **The endpoint relation across an SC step** (module docstring). -/
theorem EpStateRel.scStep {m m' : U64 → U64} {P : Fl4Spec.ObjRef → Prop} {σ σ' : Fl4Spec.State Unit}
    (hR : EpStateRel T E R B m σ) (hP : EPlaced T E R B)
    (hm : ∀ a, Aligned a → EFoot T E R B a → (∀ t ∈ T, a ≠ tStA t) → m' a = m a)
    (hst : ∀ t ∈ T, ∀ x', σ'.kheap t.bv = some (.tcb x') → (m' (tStA t)).val = tsCode x'.tcbState)
    (hK : ScTKw P σ σ') : EpStateRel T E R B m' σ' := by
  -- a TCB's state word is kept unless its state changes
  have hstK : ∀ t ∈ T, ∀ x, σ.kheap t.bv = some (.tcb x) → ¬ IpcFree x.tcbState → m' (tStA t) = m (tStA t) := by
    intro t ht x hk hnf
    obtain ⟨y, hky, -, hs⟩ := hK.tcb hk
    have hs' : y.tcbState = x.tcbState := hs.resolve_right fun ⟨_, h1, _⟩ => hnf h1
    obtain ⟨x0, hk0, hx0⟩ := hR.tcb t ht
    rw [hk] at hk0; cases hk0
    apply UScalar.eq_of_val_eq
    rw [hst t ht y hky, hs', hx0.st]
  refine ⟨fun e he => ?_, fun r hr => ?_, fun t ht => ?_, fun wp hw => ?_⟩
  · obtain ⟨x, hkx, hx⟩ := hR.ep e he
    have hea : ∀ t ∈ T, (epHeadA e).val < t.val ∨ t.val + 4096 ≤ (epHeadA e).val := fun t ht => by
      have := hP.et e he t ht; rw [val_head e]; omega
    have hta' : ∀ t ∈ T, (epTSA e).val < t.val ∨ t.val + 4096 ≤ (epTSA e).val := fun t ht => by
      have := hP.et e he t ht; rw [val_ts hP he]; omega
    refine ⟨x, hK.ep hkx, hx.frame (hm _ (a_head hP he).1 (a_head hP he).2 (ne_st_of_apart hP hea))
      (hm _ (a_ts hP he).1 (a_ts hP he).2 (ne_st_of_apart hP hta')) fun y hy hq => ?_⟩
    have hya := hP.tcb y hy
    -- a queued thread blocks on the endpoint
    obtain ⟨xy, hky, hxy⟩ := hR.tcb y hy
    have hnf : ¬ IpcFree xy.tcbState := by
      obtain ⟨xs, hxs, hq0, -⟩ := hx.queue
      have hst0 : ∀ z ∈ xs, (m (tStA z)).val = 3 ∨ (m (tStA z)).val = 4 := by
        intro z hz
        cases x with
        | idleEP =>
          simp only [Fl4Spec.Endpoint.epQueue] at hq0
          rw [eq_comm, List.map_eq_nil_iff] at hq0; subst hq0; cases hz
        | sendEP q =>
          obtain ⟨-, ys, -, rfl, hys, hqo⟩ := hx
          have := hxs.unique hP.tcb hys; subst this
          exact Or.inr (hqo z hz).1
        | recvEP q =>
          obtain ⟨-, ys, -, rfl, hys, hqo⟩ := hx
          have := hxs.unique hP.tcb hys; subst this
          exact Or.inl (hqo z hz).1
      rw [hq0] at hq
      obtain ⟨z, hz, hzy⟩ := List.mem_map.1 hq
      have : z = y := eq_of_bv hzy
      subst this
      have := hst0 z hz
      rw [hxy.st] at this
      rintro ⟨h1, -, -⟩
      cases hs : xy.tcbState <;> rw [hs] at this h1 <;> simp [tsCode, Fl4Spec.epBlocked] at this h1
    refine ⟨hstK y hy xy hky hnf, hm _ (a_blk hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_blk hya).2⟩)))
        (ne_st_of_tf hP hy (Or.inl (a_blk hya).2) (by rw [tBlockA_eq, tw_val hya (by simp)]; simp)),
      hm _ (a_prev hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr (a_prev hya).2⟩)))
        (ne_st_of_tf hP hy (Or.inr (a_prev hya).2) (by rw [prevEp_eq, tw_val hya (by simp)]; simp)),
      hm _ (a_next hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr (a_next hya).2⟩)))
        (ne_st_of_tf hP hy (Or.inr (a_next hya).2) (by rw [nextEp_eq, tw_val hya (by simp)]; simp))⟩
  · obtain ⟨x, hkx, hx⟩ := hR.reply r hr
    have hra : ∀ t ∈ T, (Endp.rTcbA r).val < t.val ∨ t.val + 4096 ≤ (Endp.rTcbA r).val := fun t ht => by
      have := hP.rt r hr t ht; rw [Endp.rTcbA_val]; omega
    obtain ⟨y, hky, ey⟩ := hK.reply hkx
    exact ⟨y, hky, by rw [ey, hx, hm _ (a_rtcb hP hr).1 (a_rtcb hP hr).2 (ne_st_of_apart hP hra)]⟩
  · obtain ⟨x, hkx, hx⟩ := hR.tcb t ht
    obtain ⟨y, hky, hso, hs⟩ := hK.tcb hkx
    have hta := hP.tcb t ht
    have hf : ∀ a, Aligned a → TF t a → a.val ≠ t.val + 3328 → m' a = m a := fun a ha hf hne =>
      hm a ha (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl hf⟩))) (ne_st_of_tf hP ht (Or.inl hf) hne)
    have hne : ∀ K : U64, K.val < 4096 → K ≠ 3328#u64 →
        (core.num.U64.wrapping_add t K).val ≠ t.val + 3328 := fun K hK hK' => by
      rw [tw_val hta hK]; intro e
      exact hK' (UScalar.eq_of_val_eq (by show K.val = (3328#u64 : U64).val; simp; omega))
    have e_blk := hf _ (a_blk hta).1 (a_blk hta).2 (by rw [tBlockA_eq]; exact hne _ (by simp) (by decide))
    have e_badge := hf _ (a_badge hta).1 (a_badge hta).2 (hne _ (by simp) (by decide))
    have e_flags := hf _ (a_flags hta).1 (a_flags hta).2 (hne _ (by simp) (by decide))
    have e_reply := hf _ (a_reply hta).1 (a_reply hta).2 (hne _ (by simp) (by decide))
    have e_bound := hf _ (a_bound hta).1 (a_bound hta).2 (hne _ (by simp) (by decide))
    have e_fault := hf _ (a_fault hta).1 (a_fault hta).2 (hne _ (by simp) (by decide))
    have e_prio := hf _ (a_prio hta).1 (a_prio hta).2 (by rw [prioA_eq']; exact hne _ (by simp) (by decide))
    have e_fw0 := hf _ (a_fw0 hta).1 (a_fw0 hta).2 (hne _ (by simp) (by decide))
    have e_fw1 := hf _ (a_fw1 hta).1 (a_fw1 hta).2 (hne _ (by simp) (by decide))
    have e_fw2 := hf _ (a_fw2 hta).1 (a_fw2 hta).2 (hne _ (by simp) (by decide))
    have e_lf := hf _ (a_lf hta).1 (a_lf hta).2 (hne _ (by simp) (by decide))
    have e_lf0 := hf _ (a_lf0 hta).1 (a_lf0 hta).2 (hne _ (by simp) (by decide))
    have e_lf1 := hf _ (a_lf1 hta).1 (a_lf1 hta).2 (hne _ (by simp) (by decide))
    have e_reg : ∀ r, m' (regA t (regIdx r)) = m (regA t (regIdx r)) := fun r => by
      refine hf _ (a_reg hta r).1 (a_reg hta r).2 ?_
      rw [regA_val hta (regIdx_lt r)]; have := regIdx_lt r; omega
    have hyx := hso
    unfold TcbSchedOnly at hyx
    -- the fields other than the state are kept
    have hregs : y.tcbArch.tcbContext.userRegs = x.tcbArch.tcbContext.userRegs := by rw [hyx]
    have hprio : y.tcbPriority = x.tcbPriority := by rw [hyx]
    have hfault : y.tcbFault = x.tcbFault := by rw [hyx]
    have hbound : y.tcbBoundNotification = x.tcbBoundNotification := by rw [hyx]
    -- the state-dependent clauses
    have hcl : ∀ (Q : Fl4Spec.ThreadState → Prop), (∀ ts, Q ts → ¬ IpcFree ts) → Q y.tcbState →
        y.tcbState = x.tcbState := fun Q hQ hq => by
      rcases hs with hs | ⟨-, -, h2⟩
      · exact hs
      · exact absurd h2 (hQ _ hq)
    refine ⟨y, hky, ⟨hst t ht y hky, fun e hb => ?_, fun e d hsd => ?_, fun e r d hsr => ?_, fun r hsr => ?_,
      fun r => by rw [e_reg, hregs]; exact hx.regs r, by rw [e_prio, hprio]; exact hx.prio,
      by rw [e_fault, hfault]; exact hx.fault0, by rw [e_fault, hfault]; exact hx.faultT,
      by rw [e_bound, hbound]; exact hx.bound,
      by rw [hfault]; exact hx.faultR.congr e_fault e_fw0 e_fw1 e_lf e_lf0 e_lf1 e_fw2⟩⟩
    · have := hcl (fun ts => Fl4Spec.epBlocked ts = some e) (fun ts h hf => by obtain ⟨h1, -⟩ := hf; rw [h1] at h; cases h) hb
      rw [e_blk]; exact hx.blk e (this ▸ hb)
    · have := hcl (fun ts => ts = .blockedOnSend e d) (fun ts h hf => by obtain ⟨h1, -⟩ := hf; subst h; simp [Fl4Spec.epBlocked] at h1) hsd
      rw [e_badge, e_flags]; exact hx.send e d (this ▸ hsd)
    · have := hcl (fun ts => ts = .blockedOnReceive e r d) (fun ts h hf => by obtain ⟨h1, -⟩ := hf; subst h; simp [Fl4Spec.epBlocked] at h1) hsr
      rw [e_reply]; exact hx.recv e r d (this ▸ hsr)
    · have := hcl (fun ts => ts = .blockedOnReply r) (fun ts h hf => hf.2.2 r h) hsr
      rw [e_reply]; exact hx.reply r (this ▸ hsr)
  · have hal : Aligned wp.1 := (hP.balign wp hw).1
    have hba : ∀ t ∈ T, wp.1.val < t.val ∨ t.val + 4096 ≤ wp.1.val := fun t ht => hP.bt wp hw t ht
    rw [hm _ hal (Or.inr (Or.inr (Or.inr ⟨wp, hw, rfl⟩))) (ne_st_of_apart hP hba), hR.buf wp hw, hK.um]


/-! ## The SC words and the endpoint relation's -/

section Foot
variable {N C : Set U64} {c : U64}

/-- The TCB offset of an SC-cap step's word (`SOffL` or `YIELD_TO`), as a
number. -/
theorem soff_val {K : U64} (h : SOffL K) :
    K.val = 3328 ∨ K.val = 3464 ∨ K.val = 3480 ∨ K.val = 3488 ∨ K.val = 3520 ∨ K.val = 3592 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- A TCB word at one of the SC code's offsets other than the state's is no
endpoint-relation word. -/
theorem tword_not_efoot (hP : EPlaced T E R B) {y : U64} (hy : y ∈ T) {b : U64} {K : Nat}
    (hb : b.val = y.val + K) (hK : K = 3464 ∨ K = 3480 ∨ K = 3488 ∨ K = 3520 ∨ K = 3592 ∨ K = 3472)
    (h2 : EFoot T E R B b) : False := by
  rcases h2 with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hw, h⟩
  · have := hP.et e he y hy; omega
  · have := hP.rt r hr y hy; omega
  · by_cases e : t = y
    · subst e; obtain ⟨-, h2⟩ := h; unfold TOffN at h2; omega
    · have := tcb_disj hP ht hy (Ne.symm e); have := h.range; omega
  · by_cases e : t = y
    · subst e; unfold TL at h; omega
    · have := tcb_disj hP ht hy (Ne.symm e); unfold TL at h; omega
  · have := hP.bt wp hw y hy; rw [← h] at this; omega

/-- **An SC-cap step's word read by the endpoint relation is a TCB state
word.** -/
theorem tfoot_efoot (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hA : EpSchedApart st T C E R B c s σ) {b : U64}
    (h1 : TFoot st T N C c s σ b) (h2 : EFoot T E R B b) : ∃ t ∈ T, b = tStA t := by
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hP := hP0.e
  rcases h1 with ((⟨y, hy, K, ⟨-, hK4, -, -, -, hL⟩, rfl⟩ | ⟨g1, g2⟩) | ⟨n, hn, n1, n2⟩ | ⟨sc, hsc, x, n, hk, hobj, -⟩) |
      ⟨y, hy, rfl⟩
  · have hya := hP.tcb y hy
    have hv := tw_val hya hK4
    rcases soff_val hL with h | h | h | h | h | h
    · exact ⟨y, hy, by rw [tStA_eq]; congr 1; exact UScalar.eq_of_val_eq (by simp [h])⟩
    all_goals exact (tword_not_efoot hP hy hv (by omega) h2).elim
  · exact (hA.node _ g1 g2 h2).elim
  · exfalso
    rcases h2 with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hw, h⟩
    · have := hP0.ne n hn e he; omega
    · have := hP0.nr n hn r hr; omega
    · have := hP0.n.disj n hn t ht; have := h.range; omega
    · have := hP0.n.disj n hn t ht; unfold TL at h; omega
    · have := hP0.nb n hn wp hw; rw [← h] at this; omega
  · exfalso
    have hE := hA.sc sc hsc x n hk b hobj
    have hT := (hS.scOut sc hsc x n hk b hobj).2.2.1
    rcases h2 with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hw, h⟩
    · exact hE (Or.inl ⟨e, he, h⟩)
    · exact hE (Or.inr (Or.inl ⟨r, hr, h⟩))
    · have := hT t ht; have := h.range; omega
    · have := hT t ht; unfold TL at h; omega
    · exact hE (Or.inr (Or.inr (Or.inr ⟨wp, hw, h⟩)))
  · exact (tword_not_efoot hP hy (yieldA_val hP.tcb hy) (by omega) h2).elim

/-- The TCB word of an SC-cap step: in the TCB, past offset 256. -/
theorem tfoot_tcb {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {b : U64}
    (h : TFoot st T N C c s σ b) :
    (∃ y ∈ T, y.val + 256 ≤ b.val ∧ b.val < y.val + 4096) ∨
    (L.nodeBase s c ≤ b.val ∧ b.val < L.nodeBase s c + 4288) ∨
    (∃ n ∈ N, n.val ≤ b.val ∧ b.val < n.val + 40) ∨ ScObjW C σ b := by
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  rcases h with ((⟨y, hy, K, ⟨k1, k2, -, -, -⟩, rfl⟩ | ⟨g1, g2⟩) | ⟨n, hn, n1, n2⟩ | ⟨sc, hsc, x, n, hk, hobj, -⟩) |
      ⟨y, hy, rfl⟩
  · have hv := tw_val (hc.tcbs y hy) k2
    exact Or.inl ⟨y, hy, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨g1, g2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn, n1, n2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨sc, hsc, x, n, hk, hobj⟩))
  · have hv := yieldA_val hc.tcbs hy
    exact Or.inl ⟨y, hy, by omega, by omega⟩

/-- **An SC-cap step's words are IPC, node or SC words** (`RelTopB.frameS`). -/
theorem tfoot_iw {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {b : U64}
    (h : TFoot st T N C c s σ b) : IWords N T E R B b ∨ NodeW (L.ksb s) c b ∨ ScObjW C σ b := by
  rcases tfoot_tcb hS h with ⟨y, hy, h1, h2⟩ | ⟨g1, g2⟩ | ⟨n, hn, n1, n2⟩ | h
  · exact Or.inl (Or.inl ⟨y, hy, h1, h2⟩)
  · simp only [LawfulStore.nodeBase] at g1 g2; exact Or.inr (Or.inl ⟨g1, g2⟩)
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, n1, n2⟩))))
  · exact Or.inr (Or.inr h)

/-- **An SC-cap step's words are words of the other objects** (`OObj`). -/
theorem tfoot_oobj {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) {b : U64}
    (h : TFoot st T N C c s σ b) : Vs.OObj st N T C E R B c s σ b := by
  rcases tfoot_tcb hS h with ⟨y, hy, h1, h2⟩ | ⟨g1, g2⟩ | ⟨n, hn, n1, n2⟩ | ⟨sc, hsc, x, n, hk, hobj⟩
  · exact Or.inr (Or.inr (Or.inl ⟨y, hy, h1, h2⟩))
  · exact Or.inl ⟨g1, g2⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, n1, by omega⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, n, hk, hobj⟩))))))

/-- **An SC-cap step writes nothing of the kernel-global block.** -/
theorem tfoot_ksb {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val) {b : U64}
    (h : TFoot st T N C c s σ b) : b.val < (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ b.val := by
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  rcases tfoot_tcb hS h with ⟨y, hy, h1, h2⟩ | ⟨g1, g2⟩ | ⟨n, hn, n1, n2⟩ | ⟨sc, hsc, x, n, hk, hobj⟩
  · have := hc.ksOut y hy; have h12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
    rw [h12] at this; omega
  · simp only [LawfulStore.nodeBase] at g1; omega
  · have := hNk n hn; omega
  · have := (hS.scOut sc hsc x n hk b hobj).2.2.2; omega

end Foot

end

/-! ## The step at `XTop` -/

section Step
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- Writes of IPC, node and SC words keep the slots (`RelTopB.frameS`'s). -/
theorem slotsSame_of_iw {th : TypedHeap} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c kb : U64}
    {σ : Fl4Spec.State Unit} (hPl : Placed th) (hA : IpcApart th N T E R B kb c) (hSA : ScApart th C σ)
    {s s' : S} {W : U64 → Prop} (hW : WritesIn st s s' W)
    (hWI : ∀ a, W a → IWords N T E R B a ∨ NodeW kb c a ∨ ScObjW C σ a) :
    SlotsSame th (L.mem s) (L.mem s') := by
  intro a ha
  have hf := ha.fit hPl
  have hal := ha.align hPl
  have w : ∀ k : U64, k.val < 32 → k.val % 8 = 0 → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := by
    intro k hk hk8
    have hv := wordOf_val (a := a) (k := k) (by omega)
    refine hW.2.2 _ (by unfold P1.Aligned; rw [hv]; omega) fun hw => ?_
    rcases hWI _ hw with hi | ⟨h1, h2⟩ | ⟨sc, hsc, x, n, hk', hobj⟩
    · exact hA.slot _ hi a ha (by rw [hv]; omega)
    · exact hA.node _ h1 h2 a ha (by rw [hv]; omega)
    · exact hSA sc hsc x n hk' _ hobj a ha ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  refine ⟨?_, w 8#u64 (by decide) (by decide), w 16#u64 (by decide) (by decide), w 24#u64 (by decide) (by decide)⟩
  have := w 0#u64 (by decide) (by decide)
  rwa [wordOf_zero] at this

/-- The other objects after an SC step were the other objects before (the
SC sizes kept). -/
theorem OObj.of_szKeep {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s s' : S}
    {σ σ' : Fl4Spec.State Unit} (hksb : L.ksb s' = L.ksb s) (hz : SzKeep σ σ') {a : U64}
    (h : Vs.OObj st N T C E R B c s' σ' a) : Vs.OObj st N T C E R B c s σ a := by
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hksb]
  unfold Vs.OObj at h ⊢
  rw [hnb, hksb] at h
  rcases h with h | h | h | h | h | h | ⟨sc, hsc, x, n, hk, ho⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · obtain ⟨x0, hk0⟩ := hz _ _ _ hk
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x0, n, hk0, ho⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- An arch object stays across an SC step. -/
theorem ScTKw.arch_obj {P : Fl4Spec.ObjRef → Prop} {σ σ' : Fl4Spec.State Unit} (h : ScTKw P σ σ') {p : Fl4Spec.ObjRef}
    {ao : Fl4Spec.ArchKernelObj} (hk : σ.kheap p = some (.archObj ao)) : σ'.kheap p = σ.kheap p := by
  rw [h.keep_other hk (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e), hk]

set_option maxHeartbeats 2000000 in
/-- **An SC-cap step keeps `XTop`, with extra writes `W`** apart from the
kernel-global block, the endpoint relation's words, the VSpace objects and the
slots (`xtop_sc_step` for `W` empty; `xtop_sc_stepCW` for the call-stack
words). FL4 writing only `TFoot` words, the spec changing only scheduling fields
(`ScTKw`, the current thread's state among non-blocking states), the
scheduler and notification relations after; with the IPC placement and the
notifications apart from the kernel-global block. -/
theorem xtop_sc_stepW {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} {ct : Fl4Spec.ObjRef}
    (hX : XTopAt (L := L) AR Z s a σ) (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B)
    (hNk : ∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    {W : U64 → Prop}
    (hW : WritesIn st s s' (fun b => TFoot st Z.T Z.N Z.C Z.c s σ b ∨ W b))
    (hWk : ∀ b, W b → b.val < (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ b.val)
    (hWo : ∀ b, W b → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b)
    (hWe : ∀ b, W b → ¬ EFoot Z.T Z.E Z.R Z.B b)
    (hWi : ∀ b, W b → IWords Z.N Z.T Z.E Z.R Z.B b ∨ NodeW (L.ksb s) Z.c b ∨ ScObjW Z.C σ b)
    (hK : ScTKw (fun p => p = ct) σ σ')
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ') (hN' : NtfnStateRel Z.N Z.T (L.mem s') σ')
    (hAR : AR a σ.archState.x64CurrentCr3 → AR a' σ.archState.x64CurrentCr3) :
    XTopAt (L := L) AR Z s' a' σ' := by
  obtain ⟨hF, hB, -, hA⟩ := hX
  obtain ⟨⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hTP⟩, hVs, hPt, hPI, hCur⟩ := hF
  have hks : L.ksb s' = L.ksb s := hW.1
  have hmem : ∀ b, Aligned b → ¬ (TFoot st Z.T Z.N Z.C Z.c s σ b ∨ W b) → L.mem s' b = L.mem s b := hW.2.2
  have hiw : ∀ b, (TFoot st Z.T Z.N Z.C Z.c s σ b ∨ W b) →
      IWords Z.N Z.T Z.E Z.R Z.B b ∨ NodeW (L.ksb s) Z.c b ∨ ScObjW Z.C σ b :=
    fun b hb => hb.elim (tfoot_iw hSch) (hWi b)
  have hoo : ∀ b, (TFoot st Z.T Z.N Z.C Z.c s σ b ∨ W b) → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b :=
    fun b hb => hb.elim (tfoot_oobj hSch) (hWo b)
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hTP.vs.ksb_fit; omega
  have hka := hTP.vs.ksb_al
  -- words of the kernel-global block
  have hkw : ∀ b, Aligned b → (L.ksb s).val ≤ b.val → b.val < (L.ksb s).val + 13568 → L.mem s' b = L.mem s b :=
    fun b hb h1 h2 => hmem b hb fun ht => by
      rcases ht with ht | ht
      · rcases tfoot_ksb hSch hNk ht with e | e <;> omega
      · rcases hWk b ht with e | e <;> omega
  -- words of the VSpace objects
  have hvw : ∀ b, Aligned b → Vs.VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b → L.mem s' b = L.mem s b :=
    fun b hb hv => hmem b hb fun ht => hTP.disj b (hoo b ht) hv
  -- the endpoint relation
  have hE' : EpStateRel Z.T Z.E Z.R Z.B (L.mem s') σ' := EpStateRel.scStep hEp hTP.ep
    (fun x hx hf hns => hmem x hx fun ht => by
      rcases ht with ht | ht
      · obtain ⟨t, htT, rfl⟩ := tfoot_efoot hP0 hSch hA ht hf; exact hns t htT rfl
      · exact hWe x ht hf)
    (fun t ht x' hk => by
      obtain ⟨y, hky, hy⟩ := hN'.tcb t ht; rw [hk] at hky; cases hky; exact hy.st) hK
  -- the IRQ, IO-port and kernel-root relations
  have hIrq' : IrqRel (L.mem s') (L.ksb s') σ' := by
    rw [hks]
    refine ⟨fun i hi => ?_, fun i hi => by rw [hK.inode]; exact hIrq.node i hi⟩
    have hv := irqStA_val hkf hi
    rw [hK.ist, hkw _ (by unfold Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)]
    exact hIrq.st i hi
  have hIo' : IoRel (L.mem s') (L.ksb s') σ' := by
    rw [hks]
    intro p hp
    have hw : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have hv := ioA_val hkf hw
    unfold bitOf
    rw [hkw _ (by unfold Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega), hK.arch]
    exact hIo p hp
  have hKr' : Vs.KRootRel (L.mem s') (L.ksb s') σ' := by
    unfold Vs.KRootRel Vs.globCr3 at hKr ⊢
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [hks, hkw _ (by unfold Aligned; rw [hkv]; omega) (by rw [hkv]; omega) (by rw [hkv]; omega), hK.arch]
    exact hKr
  -- the placement
  have hz := hK.szKeep
  have hTP' : Vs.TopPlaced st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' := by
    have hnb : L.nodeBase s' Z.c = L.nodeBase s Z.c := by simp [LawfulStore.nodeBase, hks]
    exact ⟨hTP.ep, by rw [hks]; exact hTP.vs, hTP.pt, hTP.pl,
      fun x hx => by rw [hks]; exact hTP.disj x (OObj.of_szKeep hks hz hx),
      fun x h1 h2 => by rw [hnb] at h1 h2; exact hTP.nodeE x h1 h2, hTP.po, hTP.ps,
      by rw [hks]; exact hTP.pv, by rw [hks]; exact hTP.vo, by rw [hks]; exact hTP.sd, by rw [hks]; exact hTP.tko⟩
  -- the VSpace relations
  have hVs' : Vs.VsRel Z.P (L.mem s') (L.ksb s') σ' := by
    rw [hks]
    refine Vs.VsRel.frame hVs (fun b hb => hvw b (hb.aligned hTP.vs) (Vs.vsWrite_vobj hTP.vs hb))
      (by rw [hK.arch]) fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hVs.pool p hp
    exact hK.arch_obj hf
  have hPt' : Vs.PtRel Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s') σ' := by
    refine Vs.PtRel.frame hPt (fun b ⟨q, hq, i, hi, e⟩ => ?_) fun q hq => ?_
    · subst e
      have hq4 := hTP.pt q hq
      refine hvw _ (by show _ % 8 = 0; rw [Vs.peA_val (Vs.tbl_fit hq4) hi]; omega)
        (Vs.table_vobj hTP.pt hq hi _)
    · rcases hq with hq | hq | hq | hq
      · obtain ⟨f, hf, -⟩ := hPt.l4 q hq; exact hK.arch_obj hf
      · obtain ⟨f, hf, -⟩ := hPt.l3 q hq; exact hK.arch_obj hf
      · obtain ⟨f, hf, -⟩ := hPt.l2 q hq; exact hK.arch_obj hf
      · obtain ⟨f, hf, -⟩ := hPt.l1 q hq; exact hK.arch_obj hf
  have hPI' : Vs.PoolsIn Z.P Z.L4 (L.mem s') :=
    Vs.PoolsIn.of_writes hPI hW hTP.vs fun b hb hv => hTP.disj b (hoo b hb) (Vs.vsWrite_vobj hTP.vs hv)
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    slotsSame_of_iw hB.1 hB.2.2.2.2.2.1 hB.2.2.2.2.2.2 hW hiw
  have hCur' := Vs.CurOK.of_same hCur hSS hK.ct
  -- the CSpace relation, the merged IPC relation and the apartness
  have hB' := RelTopB.frameS hB hW hiw
    (fun x ⟨sc, hsc, y, n, hk, hobj⟩ => (hSch.scOut sc hsc y n hk x hobj).2.2.2) hK.ckeep hK.dl hK.dsi hz
  refine ⟨⟨⟨⟨hS', hE', hN', hIrq', hIo', hKr', ?_⟩, hTP'⟩, hVs', hPt', hPI', hCur'⟩, hB',
    IpcRel.of hN' hE' (sched_sc hS'), hA.mono hks hz⟩
  rw [hK.arch]; exact hAR hAr


set_option maxHeartbeats 2000000 in
/-- **An SC-cap step keeps `XTop`** at the same sets (module docstring): FL4
writing only `TFoot` words, the spec changing only scheduling fields
(`ScTKw`, the current thread's state among non-blocking states), the
scheduler and notification relations after; with the IPC placement and the
notifications apart from the kernel-global block. -/
theorem xtop_sc_step {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} {ct : Fl4Spec.ObjRef}
    (hX : XTopAt (L := L) AR Z s a σ) (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B)
    (hNk : ∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hW : WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ))
    (hK : ScTKw (fun p => p = ct) σ σ')
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ') (hN' : NtfnStateRel Z.N Z.T (L.mem s') σ')
    (hAR : AR a σ.archState.x64CurrentCr3 → AR a' σ.archState.x64CurrentCr3) :
    XTopAt (L := L) AR Z s' a' σ' :=
  xtop_sc_stepW (W := fun _ => False) hX hP0 hNk (hW.mono fun _ h => Or.inl h) (fun _ h => h.elim)
    (fun _ h => h.elim) (fun _ h => h.elim) (fun _ h => h.elim) hK hS' hN' hAR

/-- **The call-stack words at `XTop`**: a reply's `NEXT`/`PREV` word or an
SC's `REPLY` word is outside the kernel-global block (the replies apart from
it, `hRk`), a word of the other objects, no endpoint-relation word (replies
are related by their `TCB` word only), and an IPC or SC word. -/
theorem callW'_xtop {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B)
    (hRk : ∀ r ∈ Z.R, r.val + 32 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ r.val) {b : U64}
    (h : CallW' Z.R Z.C b) :
    (b.val < (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ b.val) ∧ Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧
      ¬ EFoot Z.T Z.E Z.R Z.B b ∧ (IWords Z.N Z.T Z.E Z.R Z.B b ∨ NodeW (L.ksb s) Z.c b ∨ ScObjW Z.C σ b) := by
  have hSch := hX.fin.1.1.1
  have hA := hX.esa
  have hP := hP0.e
  rcases h with ⟨r, hr, e⟩ | ⟨q, hq, rfl⟩
  · have hrA := hP.rep r hr
    have hA' : r.val % 32 = 0 ∧ r ≠ 0#u64 ∧ r.val + 32 ≤ 2 ^ 64 :=
      ⟨hrA.1, fun e => hrA.2.1 (by rw [e]; rfl), hrA.2.2⟩
    have hv : b.val = r.val + 16 ∨ b.val = r.val + 8 := by
      rcases e with rfl | rfl
      · exact Or.inl (rNextA_val hA')
      · exact Or.inr (rPrevA_val hA')
    refine ⟨by have := hRk r hr; omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, by omega, by omega⟩)))),
      fun hf => ?_, Or.inl (Or.inr (Or.inr (Or.inl ⟨r, hr, by omega, by omega⟩)))⟩
    rcases hf with ⟨e', he, h'⟩ | ⟨r', hr', h'⟩ | ⟨t, ht, h' | h'⟩ | ⟨wp, hw, h'⟩
    · have := hP.er e' he r hr; omega
    · have := (hP.rep r' hr').1; omega
    · have := hP.rt r hr t ht; have := h'.range; omega
    · have := hP.rt r hr t ht; unfold TL at h'; omega
    · have := hP.br wp hw r hr; rw [← h'] at this; omega
  · obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
    obtain ⟨-, hvq, hsz⟩ := sc_reply_word hSch hq
    obtain ⟨x, n, hk, -⟩ := hs.scs q hq
    have hobj : ScObj q n (scReplyA q) := by have := hsz x n hk; unfold ScObj; rw [hvq]; omega
    have hO := hSch.scOut q hq x n hk _ hobj
    refine ⟨by have := hO.2.2.2; omega,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq, x, n, hk, hobj⟩)))))), fun hf => ?_,
      Or.inr (Or.inr ⟨q, hq, x, n, hk, hobj⟩)⟩
    have hE := hA.sc q hq x n hk _ hobj
    have hT := hO.2.2.1
    rcases hf with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hw, h⟩
    · exact hE (Or.inl ⟨e, he, h⟩)
    · exact hE (Or.inr (Or.inl ⟨r, hr, h⟩))
    · have := hT t ht; have := h.range; omega
    · have := hT t ht; unfold TL at h; omega
    · exact hE (Or.inr (Or.inr (Or.inr ⟨wp, hw, h⟩)))

set_option maxHeartbeats 1000000 in
/-- **An SC-cap step with call-stack writes keeps `XTop`**: `xtop_sc_step`
with FL4 also writing replies' `NEXT`/`PREV` words and SCs' `REPLY` words
(`CallW'`), the replies apart from the kernel-global block. -/
theorem xtop_sc_stepCW {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} {ct : Fl4Spec.ObjRef}
    (hX : XTopAt (L := L) AR Z s a σ) (hP0 : IPlaced Z.N Z.T Z.E Z.R Z.B)
    (hNk : ∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hRk : ∀ r ∈ Z.R, r.val + 32 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ r.val)
    (hW : WritesIn st s s' (fun b => TFoot st Z.T Z.N Z.C Z.c s σ b ∨ CallW' Z.R Z.C b))
    (hK : ScTKw (fun p => p = ct) σ σ')
    (hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ') (hN' : NtfnStateRel Z.N Z.T (L.mem s') σ')
    (hAR : AR a σ.archState.x64CurrentCr3 → AR a' σ.archState.x64CurrentCr3) :
    XTopAt (L := L) AR Z s' a' σ' :=
  xtop_sc_stepW hX hP0 hNk hW (fun _ h => (callW'_xtop hX hP0 hRk h).1) (fun _ h => (callW'_xtop hX hP0 hRk h).2.1)
    (fun _ h => (callW'_xtop hX hP0 hRk h).2.2.1) (fun _ h => (callW'_xtop hX hP0 hRk h).2.2.2) hK hS' hN' hAR

end Step

end

end Fl4Proofs.P3.Sched

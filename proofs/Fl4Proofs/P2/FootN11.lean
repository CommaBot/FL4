/-
P2 (hr): **the `res` part of `SchPre` at the end of `awaken`** (premise `hR`
of `AllCores.schedE` / `schedB`), from FL4's one domain (P1 `DomInv`).

`RC s`: with action `RESUME`, the current thread is `SchCur`. Each piece of
`awaken` keeps `DomInv` and `RC`:

* a step that leaves the action `RESUME` (it never writes `RESUME`: every
  `SCHED_ACTION` write is `CHOOSE_NEW` or a thread) and misses the current
  thread's `STATE`/`IN_QUEUES`/`AFFINITY` words and the executing core's
  `CUR_THREAD`/`IDLE_THREAD` words keeps `SchCur` (`SchCur.keep`,
  `SchCur.wi` with `CurFree`, `SchCur.fn` for a `FootN` protecting the
  current thread);
* the threads the pieces write (woken, donated to, dequeued) are blocked, so
  not the current thread while the action is `RESUME` (`SchCur.nb`), except
  the `RunningVM` completion (`vcpu.report`, which sets `RUNNING`) and the
  release loop's head (whose `Q_RELEASE` bit only is cleared);
* **`possible_switch_to t`** under `DomInv`: the domain-mismatch branch
  (sched.rs:369) is dead (`DomInv.cur`); a thread of another core is queued,
  and it is not the current thread (`SchCur.aff`); otherwise the action
  becomes `t` (or `CHOOSE_NEW`), not `RESUME`.

`DomInv` is kept by every write (`DomFree`): the TCB fields written are not
`DOMAIN` (3432), and the node, frame (`Sg`), endpoint and user words lie
outside the TCBs and the kernel-global area (`CUR_DOMAIN`). The one
footprint given only as `KW` (`cancel_ipc`) is instantiated with no SC
objects (`ObjsOK.noScs`), so its words are TCB fields, node words, frame
words and endpoint words (`kw0_ne_cdom`).

**`sched.awaken.rc`**: `DomInv` and `RC` at the start of `awaken` give `RC`
at its end, i.e. `hR`. **`AllCores.schedH`** / **`AllCores.schedBH`**:
`AllCores.schedE` / `schedB` with `hR` discharged; entry end facts (as
`hsa`): `hD` (`DomInv` at the body's end: P1/DomInv, P3's
`kernel_entry_domInvU29`) and `hrs` (`RC` at the body's end). Named premise
left: `hS0` [W] (`0 ∉ Scs`).
-/
import Fl4Proofs.P2.EntryEnd
import Fl4Proofs.P1.DomInvQ
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64}
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-- With action `RESUME`, the current thread is `SchCur`. -/
def RC (st : machine.Store S) [L : LawfulStore st] (s : S) : Prop := L.actionW s = 0#u64 → SchCur st s

theorem RC.nz {s : S} (h : L.actionW s ≠ 0#u64) : RC st s := fun e => absurd e h

theorem zero_notT (hT : TcbPlaced T) : (0#u64) ∉ T := notT_small hT (by simp)

theorem u1_ne0 : (1#u64 : U64) ≠ 0#u64 := by decide

theorem one_ne_zero' : (sched.ACTION_CHOOSE_NEW : U64) ≠ 0#u64 := by rw [choose_val]; exact u1_ne0

/-! ## `SchCur` frames -/

theorem SchCur.keep {s s' : S} (hk : L.ksb s' = L.ksb s) (hc : L.cpu s' = L.cpu s)
    (e0 : L.mem s' (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = L.curW s)
    (e8 : L.mem s' (L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD) = L.idleW s)
    (ea : L.mem s' (affA (L.curW s)) = L.mem s (affA (L.curW s)))
    (es : ¬ Blocked (L.mem s (stA (L.curW s))) → ¬ Blocked (L.mem s' (stA (L.curW s))))
    (eq : (L.mem s (inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64 →
      (L.mem s' (inqA (L.curW s)) &&& sched.Q_QUEUED) = 0#u64)
    (h : SchCur st s) : SchCur st s' := by
  have ecur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [nodeAt_of_ksb hk, hc]; exact e0
  have eidle : L.idleW s' = L.idleW s := by
    unfold LawfulStore.idleW; rw [nodeAt_of_ksb hk, hc]; exact e8
  refine ⟨?_, ?_, fun hne => ?_⟩
  · rw [ecur, ea, hc]; exact h.aff
  · rw [ecur]; exact es h.nb
  · rw [ecur] at hne ⊢; rw [eidle] at hne; exact eq (h.nq hne)

/-- A word that is none of the words `SchCur` reads. -/
def CurFree (st : machine.Store S) [L : LawfulStore st] (s : S) (b : U64) : Prop :=
  b ≠ L.nodeAt s (L.cpu s) layout.node.CUR_THREAD ∧ b ≠ L.nodeAt s (L.cpu s) layout.node.IDLE_THREAD ∧
    b ≠ affA (L.curW s) ∧ b ≠ stA (L.curW s) ∧ b ≠ inqA (L.curW s)

/-- A step writing only `CurFree` words keeps `SchCur`. -/
theorem SchCur.wi {s s' : S} {B : U64 → Prop} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (w : WritesIn st s s' B) (hB : ∀ b, Aligned b → B b → CurFree st s b) (h : SchCur st s) : SchCur st s' := by
  have hN := hq.nodes _ hq.cur
  have hcT : L.curW s ∈ T := hq.curT
  have hca := hq.tcbs _ hcT
  have a0 := nodeAt_aligned (off := layout.node.CUR_THREAD) hN (by rw [curth0]; omega) (by rw [curth0])
  have a8 := nodeAt_aligned (off := layout.node.IDLE_THREAD) hN (by rw [idle8]; omega) (by rw [idle8])
  have aa : Aligned (affA (L.curW s)) := by rw [affA_eq]; exact field_aligned hca (by simp) (by simp)
  have ast : Aligned (stA (L.curW s)) := by rw [stA_eq]; exact field_aligned hca (by simp) (by simp)
  have ai := inqA_aligned hca
  refine SchCur.keep w.1 w.2.1 ?_ ?_ ?_ ?_ ?_ h
  · exact w.mem_eq a0 fun hb => (hB _ a0 hb).1 rfl
  · exact w.mem_eq a8 fun hb => (hB _ a8 hb).2.1 rfl
  · exact w.mem_eq aa fun hb => (hB _ aa hb).2.2.1 rfl
  · rw [w.mem_eq ast fun hb => (hB _ ast hb).2.2.2.1 rfl]; exact id
  · rw [w.mem_eq ai fun hb => (hB _ ai hb).2.2.2.2 rfl]; exact id

theorem CurFree.out {s : S} {a : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (ha : OutsideObjs st T Cs s a) : CurFree st s a := by
  have hN := hq.nodes _ hq.cur
  have hcT : L.curW s ∈ T := hq.curT
  have hca := hq.tcbs _ hcT
  refine ⟨fun e => out_ne_node ha hq.cur hN (by rw [curth0]; omega) (by rw [e]),
    fun e => out_ne_node ha hq.cur hN (by rw [idle8]; omega) (by rw [e]),
    fun e => out_ne_field (K := 3520#u64) ha hcT hca (by simp) (by rw [e]; rfl),
    fun e => out_ne_field (K := 3328#u64) ha hcT hca (by simp) (by rw [e, stA_eq]),
    fun e => out_ne_field (K := 3592#u64) ha hcT hca (by simp) (by rw [e]; rfl)⟩

theorem CurFree.field {s : S} {y K : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hy : y ∈ T)
    (hK : K.val < 4096) (hne : y = L.curW s → K.val ≠ 3520 ∧ K.val ≠ 3328 ∧ K.val ≠ 3592) :
    CurFree st s (core.num.U64.wrapping_add y K) := by
  have hN := hq.nodes _ hq.cur
  have hcT : L.curW s ∈ T := hq.curT
  have hca := hq.tcbs _ hcT
  have hya := hq.tcbs _ hy
  refine ⟨fun e => node_ne_field hN (by rw [curth0]; omega) hy hya hK e.symm,
    fun e => node_ne_field hN (by rw [idle8]; omega) hy hya hK e.symm,
    fun e => field_ne (K2 := 3520#u64) hya hca hK (by simp) (fun h => by simpa using (hne h).1) (by rw [e]; rfl),
    fun e => field_ne (K2 := 3328#u64) hya hca hK (by simp) (fun h => by simpa using (hne h).2.1) (by rw [e, stA_eq]),
    fun e => field_ne (K2 := 3592#u64) hya hca hK (by simp) (fun h => by simpa using (hne h).2.2) (by rw [e]; rfl)⟩

theorem CurFree.node {s : S} {c o : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hc : c ∈ Cs)
    (ho : o.val < 4288) (hne : c = L.cpu s → o.val ≠ 0 ∧ o.val ≠ 8) : CurFree st s (L.nodeAt s c o) := by
  have hN := hq.nodes _ hq.cur
  have hN' := hq.nodes _ hc
  have hcT : L.curW s ∈ T := hq.curT
  have hca := hq.tcbs _ hcT
  refine ⟨fun e => node_ne_node hN' hN ho (by rw [curth0]; omega) (fun h => by rw [curth0]; exact (hne h).1)
      (by rw [e]),
    fun e => node_ne_node hN' hN ho (by rw [idle8]; omega) (fun h => by rw [idle8]; exact (hne h).2) (by rw [e]),
    fun e => node_ne_field hN' ho hcT hca (K := 3520#u64) (by simp) (by rw [e]; rfl),
    fun e => node_ne_field hN' ho hcT hca (K := 3328#u64) (by simp) (by rw [e, stA_eq]),
    fun e => node_ne_field hN' ho hcT hca (K := 3592#u64) (by simp) (by rw [e]; rfl)⟩

/-- A `FootN` protecting the current thread (`STATE`, `IN_QUEUES`), in
no-donation mode (every `AFFINITY`, the executing core's `CUR_THREAD`),
keeps `SchCur`. -/
theorem SchCur.fn {Kp : Set U64} {s s' : S} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (f : FootN st Kp True T Cs Sg Scs Z Es s s') (hK : L.curW s ∈ Kp) (h : SchCur st s) : SchCur st s' := by
  have hcT : L.curW s ∈ T := hq.curT
  have hca := hq.tcbs _ hcT
  refine SchCur.wi hq f.w (fun b _ hb => ⟨?_, ?_, ?_, ?_, ?_⟩) h <;> intro e <;> subst e <;> apply hb.2
  · exact Or.inl ⟨_, hq.cur, _, Or.inr (Or.inr (Or.inr ⟨trivial, rfl, by rw [curth0]⟩)), rfl⟩
  · exact Or.inl ⟨_, hq.cur, _, Or.inl idle8, rfl⟩
  · exact Or.inr (Or.inr ⟨trivial, Or.inl ⟨_, hcT, hca, Or.inr rfl⟩⟩)
  · exact Or.inr (Or.inl ⟨_, hcT, hca, hK, Or.inl rfl⟩)
  · exact Or.inr (Or.inl ⟨_, hcT, hca, hK, Or.inr rfl⟩)

/-- `RC` through a `FootN` protecting every thread, with the action kept. -/
theorem RC.fnT {s s' : S} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (f : FootN st T True T Cs Sg Scs Z Es s s') (ea : L.actionW s' = L.actionW s) (hr : RC st s) : RC st s' :=
  fun e => SchCur.fn hq f hq.curT (hr (ea ▸ e))

/-- `RC` through a step writing `CurFree` words, with the action kept. -/
theorem RC.wi {s s' : S} {B : U64 → Prop} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (w : WritesIn st s s' B) (hB : L.actionW s = 0#u64 → ∀ b, Aligned b → B b → CurFree st s b)
    (ea : L.actionW s' = L.actionW s) (hr : RC st s) : RC st s' := fun e => by
  have e' : L.actionW s = 0#u64 := ea ▸ e
  exact SchCur.wi hq w (hB e') (hr e')

/-! ## `DomFree` words -/

theorem domFree_out {s : S} {a : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (ha : OutsideObjs st T Cs s a) (hk : a.val ≠ (L.ksb s).val + 8) : DomFree st T s a :=
  ⟨fun e => hk (by rw [e, cdomA_valN hN]),
    fun y hy e => out_ne_field (K := 3432#u64) ha hy (hT y hy) (by simp) (by rw [e]; rfl)⟩

theorem domFree_sg {s : S} {b : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hSg : SgOK st Ω Sg s)
    (hb : b ∈ Sg) : DomFree st T s b :=
  domFree_out hq.tcbs (hq.nodes _ hq.cur) (hq.omega _ (hSg.sub b hb)) (by have := hSg.ks b hb; omega)

theorem domFree_ep {s : S} {e : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hE : EpPlaced T e)
    (hEN : EpOutNodes st Cs s e) : DomFree st T s (epHeadA e) ∧ DomFree st T s (epTSA e) := by
  obtain ⟨o1, o2⟩ := ep_out hE hEN
  have := hEN.2
  exact ⟨domFree_out hq.tcbs (hq.nodes _ hq.cur) o1 (by rw [epHeadA_val]; omega),
    domFree_out hq.tcbs (hq.nodes _ hq.cur) o2 (by rw [epTSA_val hE]; omega)⟩

theorem domFree_dbg {s : S} {b : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hb : DbgW st T Cs s b) :
    DomFree st T s b := by
  have hN := hq.nodes _ hq.cur
  rcases hb with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩ <;> subst e
  · exact field_domFree hq.tcbs hN hy (hq.ksOut y hy) (by simp) (by simp)
  · exact field_domFree hq.tcbs hN hy (hq.ksOut y hy) (by simp) (by simp)
  · exact node_domFree hq.tcbs (hq.nodes c hc) (by rw [debug_val]; omega)

theorem curFree_dbg {s : S} {b : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hb : DbgW st T Cs s b) :
    CurFree st s b := by
  rcases hb with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩ <;> subst e
  · exact CurFree.field hq hy (by simp) (fun _ => by simp)
  · exact CurFree.field hq hy (by simp) (fun _ => by simp)
  · exact CurFree.node hq hc (by rw [debug_val]; omega) (fun _ => by rw [debug_val]; omega)

/-- `ObjsOK` with no SC objects. -/
theorem ObjsOK.noScs {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) : ObjsOK st Ω Sg Rp (∅ : Set U64) Nt Z s :=
  { hO with
    sc := fun c hc => absurd hc (Set.notMem_empty c)
    scW := fun c hc => absurd hc (Set.notMem_empty c)
    fixW := fun c hc => absurd hc (Set.notMem_empty c)
    scDisj := fun c hc => absurd hc (Set.notMem_empty c)
    rpSc := fun _ _ c hc => absurd hc (Set.notMem_empty c)
    repW := fun c hc => absurd hc (Set.notMem_empty c)
    ntSc := fun _ _ c hc => absurd hc (Set.notMem_empty c)
    ntOSc := fun _ _ c hc => absurd hc (Set.notMem_empty c)
    snW := fun c hc => absurd hc (Set.notMem_empty c)
    syW := fun c hc => absurd hc (Set.notMem_empty c)
    mxW := fun c hc => absurd hc (Set.notMem_empty c) }

/-- A `KW` word with no SC objects is not the `CUR_DOMAIN` word. -/
theorem kw0_ne_cdom {s : S} {b : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hSg : SgOK st Ω Sg s)
    (hb : KW st T Cs Sg (∅ : Set U64) Z (EH H) s b) : b ≠ cdomA st s := by
  have hN := hq.nodes _ hq.cur
  rcases hb with ⟨y, hy, K, -, hK, -, -, rfl⟩ | ⟨c, hc, o, ho, -, rfl⟩ | hb | ⟨c, hc, -⟩ | ⟨e, he, rfl | rfl⟩
  · intro e
    have hv := congrArg UScalar.val e
    rw [field_val (hq.tcbs y hy) hK, cdomA_valN hN] at hv
    have := hq.ksOut y hy; omega
  · exact (node_domFree hq.tcbs (hq.nodes c hc) ho).1
  · exact (domFree_sg hq hSg hb).1
  · exact absurd hc (Set.notMem_empty c)
  · obtain ⟨E, EQ, hEW⟩ := hq.eps
    have he' : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 he
    obtain ⟨hE, hEN, -⟩ := hEW.1 e he'
    exact (domFree_ep hq hE hEN).1.1
  · obtain ⟨E, EQ, hEW⟩ := hq.eps
    have he' : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 he
    obtain ⟨hE, hEN, -⟩ := hEW.1 e he'
    exact (domFree_ep hq hE hEN).2.1

theorem cdomA_ks {s : S} : cdomA st s = core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN := rfl

/-- The `Q_QUEUED` bit survives a mask. -/
theorem qq_mask {x m : U64} (h : (x &&& sched.Q_QUEUED) = 0#u64) : ((x &&& m) &&& sched.Q_QUEUED) = 0#u64 := by
  apply eq_of_bv
  have hb := congrArg UScalar.bv h
  simp only [UScalar.bv_and] at hb ⊢
  rw [BitVec.and_assoc, BitVec.and_comm m.bv, ← BitVec.and_assoc, hb]
  simp


/-! ## `DomInv` and `RC` through single writes and frames -/

theorem DomFree.ksb {s s' : S} {b : U64} (hk : L.ksb s' = L.ksb s) (h : DomFree st T s b) : DomFree st T s' b :=
  ⟨by unfold cdomA; rw [hk]; exact h.1, h.2⟩

theorem DomInv.freeA {s s' : S} {A : U64 → Prop} (h : DomInv st T s) (w : WritesIn st s s' A) (hT : TcbPlaced T)
    (hka : Aligned (cdomA st s)) (hA : ∀ b, Aligned b → A b → DomFree st T s b) : DomInv st T s' :=
  h.writesIn w hT hka (fun hc => (hA _ hka hc).1 rfl) (fun y hy hd => (hA _ (domA_aligned (hT y hy)) hd).2 y hy rfl)

theorem DomInv.wr' {s : S} {a v : U64} (hD : DomInv st T s) (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (ha : Aligned a) (hf : DomFree st T s a) : DomInv st T (L.wr s a v) :=
  DomInv.freeA hD (writesIn_wr ha) hT (cdomA_alignedN hN) fun b _ hb => by subst hb; exact hf

/-- `DomInv` through a `KeepT0` frame whose `KW` footprint has no SC words. -/
theorem DomInv.keepT {t : U64} {s s' : S} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hSg : SgOK st Ω Sg s)
    (k : KeepT0 st T Cs Rp Scs Nt t s s') (f : Foot st T Cs Sg (∅ : Set U64) Z (EH H) s s') (hD : DomInv st T s) :
    DomInv st T s' :=
  hD.keep k.ksb (f.mem_eq (cdomA_alignedN (hq.nodes _ hq.cur)) fun hb => kw0_ne_cdom hq hSg hb rfl)
    fun y hy => k.fld y hy 3432#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)

/-- `RC` through a `KeepT0` frame of a thread that is not the current one
while the action is `RESUME`. -/
theorem RC.keepT {t : U64} {s s' : S} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (k : KeepT0 st T Cs Rp Scs Nt t s s') (htc : L.actionW s = 0#u64 → t ≠ L.curW s) (hr : RC st s) :
    RC st s' := fun e => by
  rcases k.act with ea | ea
  · have e' : L.actionW s = 0#u64 := ea ▸ e
    have hcT : L.curW s ∈ T := hq.curT
    have hnt : L.curW s ≠ t := fun h' => htc e' h'.symm
    have fk : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s' (core.num.U64.wrapping_add (L.curW s) K) = L.mem s (core.num.U64.wrapping_add (L.curW s) K) :=
      fun K h1 h2 h3 h4 => k.fld _ hcT K h1 h2 h3 h4 (fun h' => absurd h' hnt)
    have nd : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 24) →
        L.mem s' (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho => by
      have := k.nd o ho; rwa [nodeAt_of_ksb k.ksb, k.cpu] at this
    refine SchCur.keep k.ksb k.cpu (nd _ (Or.inl curth0)) (nd _ (Or.inr (Or.inl idle8)))
      (by rw [affA_eq]; exact fk _ (by simp) (by simp) (by simp) (by simp)) ?_ ?_ (hr e')
    · rw [stA_eq, fk _ (by simp) (by simp) (by simp) (by simp)]; exact id
    · rw [inqA_eq, fk _ (by simp) (by simp) (by simp) (by simp)]; exact id
  · rw [ea] at e; exact absurd e u1_ne0

/-- `set_thread_state`'s writes (`set_thread_state.w2`) keep `DomInv`. -/
theorem DomInv.sts {t : U64} {s s' : S} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (w : WritesIn st s s' (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hD : DomInv st T s) : DomInv st T s' := by
  have hN := hq.nodes _ hq.cur
  refine DomInv.freeA hD w hq.tcbs (cdomA_alignedN hN) fun b _ hb => ?_
  rcases hb with rfl | rfl
  · rw [stA_eq]; exact field_domFree hq.tcbs hN ht (hq.ksOut t ht) (by simp) (by simp)
  · exact node_domFree hq.tcbs hN (by rw [act_val]; omega)

/-- The timer words (`TW`) keep `DomInv` and the action. -/
theorem TW.dom {s s' : S} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (w : WritesIn st s s' (TW st T Cs s))
    (hD : DomInv st T s) : DomInv st T s' :=
  DomInv.freeA hD w hq.tcbs (cdomA_alignedN (hq.nodes _ hq.cur)) fun b _ hb => by
    rcases hb with ⟨y, hy, K, h1, h2, rfl⟩ | ⟨c, hc, o, ho, rfl⟩
    · exact field_domFree hq.tcbs (hq.nodes _ hq.cur) hy (hq.ksOut y hy) (by omega) (by omega)
    · exact node_domFree hq.tcbs (hq.nodes c hc) (by rcases ho with h | h <;> omega)

theorem TW.act {s s' : S} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (w : WritesIn st s s' (TW st T Cs s)) :
    L.actionW s' = L.actionW s := by
  have hN := hq.nodes _ hq.cur
  refine actionW_of w hN ?_
  rintro (⟨y, hy, K, h1, h2, e⟩ | ⟨c, hc, o, ho, e⟩)
  · exact node_ne_field hN (by rw [act_val]; omega) hy (hq.tcbs y hy) (by omega) e
  · exact notAct_node hN (hq.nodes c hc) (by rcases ho with h | h <;> omega) (by rcases ho with h | h <;> omega) e

/-- An SC's ring words and the current node's `REPROGRAM` word
(`unblock_check`) keep the action, `DomInv` and `RC`. -/
theorem ring_facts {s s' : S} {i : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hi : i ∈ Scs)
    (w : WritesIn st s s' (fun b => InRing i (Z i) b ∨ b = L.nodeA s layout.node.REPROGRAM)) :
    L.actionW s' = L.actionW s ∧ (DomInv st T s → DomInv st T s') ∧ (RC st s → RC st s') := by
  have hN := hq.nodes _ hq.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have hact : L.actionW s' = L.actionW s := by
    refine actionW_of w hN ?_
    rintro (hr | e)
    · exact notAct_omega hq (hX.1.scW i hi _ (act_aligned hN) hr.inSC)
    · exact notAct_node hN hN (by rw [rp]; omega) (by rw [rp]; omega) e
  refine ⟨hact, fun hD => DomInv.freeA hD w hq.tcbs (cdomA_alignedN hN) fun b hb hh => ?_,
    RC.wi hq w (fun _ b hb hh => ?_) hact⟩
  · rcases hh with hr | rfl
    · exact domFree_sg hq hS.sg ((hS.all i hi).2.2 b hb hr.inSC)
    · exact node_domFree hq.tcbs hN (by rw [rp]; omega)
  · rcases hh with hr | rfl
    · exact CurFree.out hq (hq.omega _ (hX.1.scW i hi b hb hr.inSC))
    · exact CurFree.node hq hq.cur (by rw [rp]; omega) (fun _ => by rw [rp]; omega)

/-- The current node's `REPROGRAM` write keeps the action, `DomInv` and `RC`. -/
theorem reprogram_facts {s : S} {v : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) :
    L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v) = L.actionW s ∧
      (DomInv st T s → DomInv st T (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v)) ∧
      (RC st s → RC st (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v)) := by
  have hN := hq.nodes _ hq.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have al := nodeAt_aligned (off := layout.node.REPROGRAM) hN (by rw [rp]; omega) (by rw [rp])
  have hact : L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v) = L.actionW s :=
    actionW_of (writesIn_wr al) hN fun e => notAct_node hN hN (by rw [rp]; omega) (by rw [rp]; omega) e
  refine ⟨hact, fun hD => DomInv.wr' hD hq.tcbs hN al (node_domFree hq.tcbs hN (by rw [rp]; omega)),
    RC.wi hq (writesIn_wr al) (fun _ b _ hb => ?_) hact⟩
  subst hb
  exact CurFree.node hq hq.cur (by rw [rp]; omega) (fun _ => by rw [rp]; omega)

/-! ## The queue operations -/

theorem sched.enqueue.rc (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hne : L.actionW s = 0#u64 → t ≠ L.curW s) (hr : RC st s) :
    sched.enqueue st s t ⦃ s' => RC st s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  have hW : ∀ w ∈ t :: Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact (hR1.1.rel _ hp).mem w hw
  refine WP.spec_mono (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => ?_
  have ea := LawfulStore.QFoot.act h.tcbs h.nodes hW hc h.cur ht (fun o ho => by omega) hh.1
  have f : FootN st {y | y ≠ t} True T Cs (∅ : Set U64) (∅ : Set U64) (fun _ => 0) (∅ : Set U64) s s' :=
    WritesIn.a (hh.1.mono fun b hb => LawfulStore.QFoot.kwN h.tcbs h.nodes hW hc h.cur ht (fun o ho => by omega)
      (fun o ho => idOff_ge (by omega)) (fun e => e rfl) hb) (AcK.of_eq ea)
  intro e
  have e' : L.actionW s = 0#u64 := ea ▸ e
  exact SchCur.fn h f (show L.curW s ≠ t from fun h' => hne e' h'.symm) (hr e')

/-- `reschedule_required` ends with action `CHOOSE_NEW`. -/
theorem sched.reschedule_required.ch (s : S) (h : SchedQueuesInvX st T Cs Ω H X s Q R) :
    sched.reschedule_required st s ⦃ s' => L.actionW s' = sched.ACTION_CHOOSE_NEW ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  have hpart : (if (act != sched.ACTION_RESUME_CURRENT) = true then
      if (act != sched.ACTION_CHOOSE_NEW) = true then do
        let b ← sched.is_schedulable st s act
        if b = true then sched.enqueue st s act else ok s
      else ok s
    else ok s) ⦃ s1 => FootN st (∅ : Set U64) True T Cs (∅ : Set U64) (∅ : Set U64) (fun _ => 0) (∅ : Set U64) s s1 ⦄ := by
    split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · exact sched.enqueue.kwN s act h hT (Set.notMem_empty _)
        · exact (WP.spec_ok _).2 (FootN.refl _)
      · exact (WP.spec_ok _).2 (FootN.refl _)
    · exact (WP.spec_ok _).2 (FootN.refl _)
  refine WP.spec_bind hpart fun s1 f1 => ?_
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [f1.2.1]; exact (h.nodes _ h.cur).ksb f1.1
  refine WP.spec_mono (sched.set_action.spec s1 _) fun s2 e2 => ?_
  subst e2
  exact actionW_set hN1

/-- **`possible_switch_to` keeps `DomInv` and `RC`** (module docstring). -/
theorem sched.possible_switch_to.rd (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hD : DomInv st T s) (hr : RC st s) :
    sched.possible_switch_to st s t ⦃ s' => DomInv st T s' ∧ RC st s' ⦄ := by
  refine WP.spec_and (sched.possible_switch_to.domInv s t h ht hD) ?_
  unfold sched.possible_switch_to
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  split
  · exact (WP.spec_ok _).2 hr
  step with sched.in_release_queue.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 hr
  unfold sched.cur_domain
  step with obj.ks_get.spec as ⟨i1, e1⟩
  step with obj.Tcb.domain.spec as ⟨i2, e2⟩
  split
  · rename_i hne
    exfalso
    have hii : i2 = i1 := by rw [e1, e2]; exact (hD.2 t ht).trans hD.1.symm
    rw [hii] at hne; simp at hne
  step with obj.Tcb.affinity.spec as ⟨i3, i3_post⟩
  step with LawfulStore.cur_cpu_spec as ⟨i4, i4_post⟩
  split
  · rename_i haff
    refine sched.enqueue.rc s t h ht (fun e0 et => ?_) hr
    have hii : i3 = i4 := by rw [i3_post, i4_post, et]; exact (hr e0).aff
    rw [hii] at haff; simp at haff
  step with sched.action.spec as ⟨i5, _⟩
  split
  · refine WP.spec_bind (WP.spec_and (sched.reschedule_required.inv s Q R h) (sched.reschedule_required.ch s h)) ?_
    rintro s1 ⟨⟨⟨Q1, h1⟩, -, -⟩, a1⟩
    exact sched.enqueue.rc s1 t h1 ht (fun e0 => absurd (a1.symm.trans e0) one_ne_zero')
      (RC.nz (by rw [a1]; exact one_ne_zero'))
  · refine WP.spec_mono (sched.set_action.spec s _) fun s' e => ?_
    subst e
    exact RC.nz (by rw [actionW_set (h.nodes _ h.cur)]; exact fun e => zero_notT h.tcbs (e ▸ ht))


/-! ## Writes outside the objects, `set_thread_state` -/

theorem curW_wi {s s' : S} {B : U64 → Prop} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (w : WritesIn st s s' B) (hB : ∀ b, Aligned b → B b → CurFree st s b) : L.curW s' = L.curW s := by
  have hN := hq.nodes _ hq.cur
  have a0 := nodeAt_aligned (off := layout.node.CUR_THREAD) hN (by rw [curth0]; omega) (by rw [curth0])
  unfold LawfulStore.curW; rw [nodeAt_of_ksb w.1, w.2.1]; exact w.mem_eq a0 fun hb => (hB _ a0 hb).1 rfl

/-- Two writes of words outside the objects and the kernel-global `CUR_DOMAIN`
word keep the action, `DomInv` and `RC`. -/
theorem out2_facts {s : S} {a1 a2 v1 v2 : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (o1 : OutsideObjs st T Cs s a1) (o2 : OutsideObjs st T Cs s a2) (k1 : a1.val ≠ (L.ksb s).val + 8)
    (k2 : a2.val ≠ (L.ksb s).val + 8) (hD : DomInv st T s) (hr : RC st s) :
    L.actionW (L.wr (L.wr s a1 v1) a2 v2) = L.actionW s ∧ DomInv st T (L.wr (L.wr s a1 v1) a2 v2) ∧
      RC st (L.wr (L.wr s a1 v1) a2 v2) := by
  have hN := hq.nodes _ hq.cur
  have w : WritesIn st s (L.wr (L.wr s a1 v1) a2 v2) (fun b => b = a1 ∨ b = a2) :=
    (writesIn_wr o1.1).trans (writesIn_wr o2.1)
  have ea : L.actionW (L.wr (L.wr s a1 v1) a2 v2) = L.actionW s := actionW_of w hN (by
    rintro (e | e)
    · exact out_ne_node o1 hq.cur hN (by rw [act_val]; omega) (by rw [e])
    · exact out_ne_node o2 hq.cur hN (by rw [act_val]; omega) (by rw [e]))
  refine ⟨ea, DomInv.freeA hD w hq.tcbs (cdomA_alignedN hN) fun b _ hb => ?_, RC.wi hq w (fun _ b _ hb => ?_) ea hr⟩
  · rcases hb with rfl | rfl
    · exact domFree_out hq.tcbs hN o1 k1
    · exact domFree_out hq.tcbs hN o2 k2
  · rcases hb with rfl | rfl
    · exact CurFree.out hq o1
    · exact CurFree.out hq o2

theorem out1_facts {s : S} {a v : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (o : OutsideObjs st T Cs s a) (k : a.val ≠ (L.ksb s).val + 8) (hD : DomInv st T s) (hr : RC st s) :
    DomInv st T (L.wr s a v) ∧ RC st (L.wr s a v) := by
  have hN := hq.nodes _ hq.cur
  have ea : L.actionW (L.wr s a v) = L.actionW s := actionW_out hq.nodes hq.cur o
  refine ⟨DomInv.wr' hD hq.tcbs hN o.1 (domFree_out hq.tcbs hN o k), RC.wi hq (writesIn_wr o.1) (fun _ b _ hb => ?_) ea hr⟩
  subst hb; exact CurFree.out hq o

/-- `RC` through `set_thread_state`'s writes: the thread's `STATE` (not
blocked if it is the current thread) and possibly `CHOOSE_NEW`. -/
theorem RC.sts {t v : U64} {s s' : S} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (w : WritesIn st s s' (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (ea : L.actionW s' = L.actionW s ∨ L.actionW s' = sched.ACTION_CHOOSE_NEW) (hst : L.mem s' (stA t) = v)
    (hv : t = L.curW s → ¬ Blocked v) (hr : RC st s) : RC st s' := by
  rcases ea with ea | ea
  swap
  · exact RC.nz (by rw [ea]; exact one_ne_zero')
  intro e
  have e' : L.actionW s = 0#u64 := ea ▸ e
  have hN := hq.nodes _ hq.cur
  have hcT : L.curW s ∈ T := hq.curT
  have hca := hq.tcbs _ hcT
  have hta := hq.tcbs _ ht
  have cfA := CurFree.node hq hq.cur (o := layout.node.SCHED_ACTION) (by rw [act_val]; omega)
    (fun _ => by rw [act_val]; omega)
  have a0 := nodeAt_aligned (off := layout.node.CUR_THREAD) hN (by rw [curth0]; omega) (by rw [curth0])
  have a8 := nodeAt_aligned (off := layout.node.IDLE_THREAD) hN (by rw [idle8]; omega) (by rw [idle8])
  have aa : Aligned (affA (L.curW s)) := by rw [affA_eq]; exact field_aligned hca (by simp) (by simp)
  have ast : Aligned (stA (L.curW s)) := by rw [stA_eq]; exact field_aligned hca (by simp) (by simp)
  have ai := inqA_aligned hca
  refine SchCur.keep w.1 w.2.1 ?_ ?_ ?_ ?_ ?_ (hr e')
  · refine w.mem_eq a0 ?_
    rintro (e | e)
    · rw [stA_eq] at e; exact node_ne_field hN (by rw [curth0]; omega) ht hta (by simp) e
    · exact cfA.1 e.symm
  · refine w.mem_eq a8 ?_
    rintro (e | e)
    · rw [stA_eq] at e; exact node_ne_field hN (by rw [idle8]; omega) ht hta (by simp) e
    · exact cfA.2.1 e.symm
  · refine w.mem_eq aa ?_
    rintro (e | e)
    · rw [stA_eq, affA_eq] at e
      exact field_ne (K1 := 3520#u64) (K2 := 3328#u64) hca hta (by simp) (by simp) (fun _ => by simp) e
    · exact cfA.2.2.1 e.symm
  · by_cases htc : t = L.curW s
    · rw [← htc, hst]; exact fun _ => hv htc
    · rw [w.mem_eq ast ?_]
      · exact id
      rintro (e | e)
      · rw [stA_eq, stA_eq] at e
        exact field_ne (K1 := 3328#u64) (K2 := 3328#u64) hca hta (by simp) (by simp) (fun h => absurd h.symm htc) e
      · exact cfA.2.2.2.1 e.symm
  · rw [w.mem_eq ai ?_]
    · exact id
    rintro (e | e)
    · rw [stA_eq, inqA_eq] at e
      exact field_ne (K1 := 3592#u64) (K2 := 3328#u64) hca hta (by simp) (by simp) (fun _ => by simp) e
    · exact cfA.2.2.2.2 e.symm

/-! ## Donation, `resume`, `postpone` -/

/-- `donate` of an SC whose `TCB` word is null, as one `WritesIn`. -/
theorem schedcontext.donate.w {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (D : DbgTz st T Cs s)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hsc : sc ∈ Scs) (hdst : dst ∈ T)
    (hcore : L.mem s (scCoreA sc) ∈ Cs) (htc0 : L.mem s (scTcbA sc) = 0#u64) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ =>
      WritesIn st s s' (fun b => b = scTcbA sc ∨ b = scA dst ∨ b = affA dst ∨ DbgW st T Cs s b) ⦄ := by
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => r.1 = s) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 rfl
    · rename_i hb
      exact absurd (by rw [eb, ei, htc0]; rfl) hb
  rintro ⟨s1, a1⟩ e1
  simp only at e1
  subst e1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (donate_tail.frame hA _ a1 sc dst h D hO hsub hsc hdst hcore) ?_
  rintro ⟨s', a'⟩ ⟨w, -⟩
  try simp only [WP.uncurry'_pair] at w ⊢
  exact w

theorem donW_dom {s : S} {sc dst b : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s) (hsc : sc ∈ Scs) (hdst : dst ∈ T)
    (hb : b = scTcbA sc ∨ b = scA dst ∨ b = affA dst ∨ DbgW st T Cs s b) : DomFree st T s b := by
  have hN := hq.nodes _ hq.cur
  rcases hb with rfl | rfl | rfl | hb
  · exact domFree_sg hq hSg (hO.fixW sc hsc).1
  · rw [scA_eq]; exact field_domFree hq.tcbs hN hdst (hq.ksOut dst hdst) (by simp) (by simp)
  · rw [affA_eq]; exact field_domFree hq.tcbs hN hdst (hq.ksOut dst hdst) (by simp) (by simp)
  · exact domFree_dbg hq hb

theorem donW_cur {s : S} {sc dst b : U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s) (hsc : sc ∈ Scs) (hdst : dst ∈ T)
    (hne : dst ≠ L.curW s) (hb : b = scTcbA sc ∨ b = scA dst ∨ b = affA dst ∨ DbgW st T Cs s b) :
    CurFree st s b := by
  rcases hb with rfl | rfl | rfl | hb
  · exact CurFree.out hq (hq.omega _ (hSg.sub _ (hO.fixW sc hsc).1))
  · rw [scA_eq]; exact CurFree.field hq hdst (by simp) (fun _ => ⟨by simp, by simp, by simp⟩)
  · rw [affA_eq]; exact CurFree.field hq hdst (by simp) (fun e => absurd e hne)
  · exact curFree_dbg hq hb

/-- `postpone` keeps `DomInv`: a `dequeue`, a `release_enqueue` (queue
footprints) and a node's `REPROGRAM` word. -/
theorem sched.postpone.dom (s : S) (sc : obj.Sc) (h : SchedQueuesInv st T Cs Ω H s Q R)
    (ht : L.mem s (scTcbA sc) ∈ T) (hr0 : (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_RELEASE) = 0#u64)
    (hcore : OutsideObjs st T Cs s (scCoreA sc)) (hcs : L.mem s (scCoreA sc) ∈ Cs) (hD : DomInv st T s) :
    sched.postpone st s sc ⦃ s' => DomInv st T s' ⦄ := by
  unfold sched.postpone
  step with obj.Sc.tcb.spec as ⟨t, t_post⟩
  subst t_post
  set t := L.mem s (scTcbA sc) with ht_def
  have hT := h.tcbs
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hN := h.nodes _ hc
  have hN' := h.nodes _ h.cur
  have hR1 := h.ready _ hc
  have hmemq := (h.queued t ht).1
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.dequeue.inv s t Q R h ht)
    (sched.dequeue.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) hmemq)) (sched.dequeue.domInv s t h ht hD)) ?_
  rintro s1 ⟨⟨h1, hw1, -⟩, D1⟩
  have hW1 : ∀ w ∈ Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := fun w hw => h.memT hc hp hw
  have core1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) :=
    hw1.mem_eq hcore.1 (qfoot_out hT hW1 hN hN' ht hc h.cur hcore)
  have hr1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hcn
    exact h.notR ht hr0 (h1.aff t ht) ((h1.released t ht).1 hcn)
  have hT1 := h1.tcbs
  have hc1 := h1.aff t ht
  have hN1 := h1.nodes _ hc1
  have hN1' := h1.nodes _ h1.cur
  refine WP.spec_bind (sched.release_enqueue.foot s1 t _ hT1 ht (h1.notR ht hr1 hc1) hN1 hN1'
    (h1.release _ hc1)) ?_
  rintro s2 ⟨hw2, -⟩
  have hW2 : ∀ w ∈ t :: R (L.mem s1 (affA t)), w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact h1.memTR hc1 hw
  have D2 : DomInv st T s2 := DomInv.free D1 hw2 hT1 (cdomA_alignedN hN1') fun b hb =>
    QFoot.domFree hT1 hN1 hN1' hW2 ht h1.ksOut hb
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hw2.mem_eq hcore.1 (qfoot_out hT1 hW2 hN1 hN1' ht hc1 h1.cur (hcore.ksb hw1.1))).trans core1
  step with obj.Sc.cpu.spec as ⟨cpu, cpu_post⟩
  rw [core2] at cpu_post
  subst cpu_post
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have NP2 : NodePlaced st T s2 (L.mem s (scCoreA sc)) := (h.nodes _ hcs).ksb (hw2.1.trans hw1.1)
  have NP2' : NodePlaced st T s2 (L.cpu s2) := by
    rw [hw2.2.1, hw1.2.1]; exact hN'.ksb (hw2.1.trans hw1.1)
  refine WP.spec_mono (sched.set_reprogram_on.spec s2 _) fun s3 e3 => ?_
  subst e3
  exact DomInv.wr' D2 hT1 NP2' (nodeAt_aligned NP2 (by rw [rp]; omega) (by rw [rp]))
    (node_domFree hT1 NP2 (by rw [rp]; omega))

theorem schedcontext.resume.dom {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc : obj.Sc) (h : SchedQueuesInv st T Cs Ω H s Q R)
    (hsc : sc ≠ 0#u64 → L.mem s (scTcbA sc) ≠ 0#u64 →
      L.mem s (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s (scCoreA sc) ∧ L.mem s (scCoreA sc) ∈ Cs)
    (hD : DomInv st T s) :
    schedcontext.resume st ar s a sc ⦃ s' _ => DomInv st T s' ⦄ := by
  unfold schedcontext.resume
  step with obj.Sc.is_null.spec as ⟨b, b_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact hD
  rename_i hb
  have hsc0 : sc ≠ 0#u64 := by simpa [b_post] using hb
  step with obj.Sc.tcb.spec as ⟨i, i_post⟩
  step with obj.Tcb.is_null.spec as ⟨b1, b1_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact hD
  rename_i hb1
  have hi0 : L.mem s (scTcbA sc) ≠ 0#u64 := by rw [← i_post]; simpa [b1_post] using hb1
  obtain ⟨hiT, hcore, hcs⟩ := hsc hsc0 hi0
  step with sched.is_schedulable.spec' as ⟨b2, b2_post⟩
  split
  · rename_i hb2
    obtain ⟨-, -, hr0, -⟩ := b2_post hb2
    rw [i_post] at hr0
    have post := sched.postpone.dom s sc h hiT hr0 hcore hcs hD
    step with sporadic.ready.spec as ⟨b3⟩
    split
    · step with sporadic.sufficient.ok (st := st) hA as ⟨b4⟩
      split
      · simp only [WP.spec_ok, WP.uncurry'_pair]; exact hD
      · exact WP.spec_bind post fun s1 h1 => by simpa using h1
    · exact WP.spec_bind post fun s1 h1 => by simpa using h1
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact hD


/-- **`maybe_donate_sched_context` keeps `DomInv` and `RC`**: it donates only
to a thread without an SC, which is not the current thread while the action
is `RESUME` (`BoundInv.resume`). -/
theorem notification.maybe_donate_sched_context.rd {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hti : L.idleW s ≠ t)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac))
    (hD : DomInv st T s) (hr : RC st s) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => DomInv st T s' ∧ RC st s' ⦄ := by
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => DomInv st T s' ∧ RC st s' ⦄ := (WP.spec_ok _).2 ⟨hD, hr⟩
  unfold notification.maybe_donate_sched_context
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have htc : L.actionW s = 0#u64 → t ≠ L.curW s := fun e0 et =>
      hB.resume e0 (by rw [← et, ← ei, hi])
    step with obj.Ntfn.sc.val as ⟨i1, ei1⟩
    step with obj.Sc.is_null.spec as ⟨b, eb⟩
    split
    · exact ok0
    rename_i hb
    have hi10 : i1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with obj.Sc.tcb.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      have htc0 : L.mem s (scTcbA i1) = 0#u64 := by rw [← ei2, hi2]
      obtain ⟨hS1, hcore1, hin1⟩ := hns (by rw [← ei1]; exact hi10) (by rw [← ei1]; exact htc0) (by rw [← ei, hi])
      rw [← ei1] at hS1 hin1 hcore1
      refine WP.spec_bind (WP.spec_and (schedcontext.donate.unbound hA s a i1 t Q R h hB hX hS hSg ht htq htr hS1
        hi10 htc0 hcore1 hin1 (by rw [← ei, hi]) hti)
        (schedcontext.donate.w hA s a i1 t h hX.dbg hX.1 hSg.sub hS1 ht hcore1 htc0)) ?_
      rintro ⟨s4, a4⟩ ⟨⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, -, -, -, sc4, tc4, ea4⟩, w4⟩
      try simp only [WP.uncurry'_pair]
      have D4 : DomInv st T s4 := DomInv.freeA hD w4 h.tcbs (cdomA_alignedN (h.nodes _ h.cur))
        fun b _ hb => donW_dom h hX.1 hSg hS1 ht hb
      have r4 : RC st s4 := RC.wi h w4 (fun e0 b _ hb => donW_cur h hX.1 hSg hS1 ht (htc e0) hb) ea4 hr
      have htc4 : L.actionW s4 = 0#u64 → t ≠ L.curW s4 := fun e0 => by
        have e0' : L.actionW s = 0#u64 := ea4 ▸ e0
        rw [curW_wi h w4 fun b _ hb => donW_cur h hX.1 hSg hS1 ht (htc e0') hb]
        exact htc e0'
      have hsc : i1 ≠ 0#u64 → L.mem s4 (scTcbA i1) ≠ 0#u64 →
          L.mem s4 (scTcbA i1) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA i1) ∧ L.mem s4 (scCoreA i1) ∈ Cs ∧
            L.mem s4 (scTcbA i1) ∉ {y | y ≠ t} := fun _ _ => by
        obtain ⟨-, -, hc4⟩ := hX4.2.2.bound t ht (by rw [sc4]; exact hi10)
        rw [sc4] at hc4
        rw [tc4]
        exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 i1 hS1).2.1, hc4, fun e => e rfl⟩
      have hsc' : i1 ≠ 0#u64 → L.mem s4 (scTcbA i1) ≠ 0#u64 →
          L.mem s4 (scTcbA i1) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA i1) ∧ L.mem s4 (scCoreA i1) ∈ Cs ∧
            L.actionW s4 ≠ L.mem s4 (scTcbA i1) := fun a b => by
        obtain ⟨x1, x2, x3, -⟩ := hsc a b
        exact ⟨x1, x2, x3, by rw [ea4, tc4]; exact hta'⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_mono (WP.spec_and (WP.spec_and (schedcontext.resume.allF hA s4 a4 i1 Q4 R4 h4 hB4 hX4 hSg4 hS4 hsc')
        (schedcontext.resume.kwN (Sg := Sg) (Kp := {y | y ≠ t}) (Nd := True) (Scs := Scs) (Z := Z)
          (Es := (∅ : Set U64)) hA s4 a4 i1 Q4 R4 h4 hsc))
        (schedcontext.resume.dom hA s4 a4 i1 h4 (fun a b => by
          obtain ⟨x1, x2, x3, -⟩ := hsc a b; exact ⟨x1, x2, x3⟩) D4)) ?_
      rintro ⟨s5, a5⟩ ⟨⟨⟨Q5, R5, h5, hB5, hX5, hSg5, f5, ea5, -, -⟩, k5⟩, D5⟩
      refine ⟨D5, fun e => ?_⟩
      have e' : L.actionW s4 = 0#u64 := ea5 ▸ e
      exact SchCur.fn h4 k5 (show L.curW s4 ≠ t from fun h' => htc4 e' h'.symm) (r4 e')
    · exact ok0
  · exact ok0

theorem notification.maybe_donate_sched_context.rdB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac))
    (hD : DomInv st T s) (hr : RC st s) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => DomInv st T s' ∧ RC st s' ⦄ := by
  by_cases h0 : L.mem s (scA t) = 0#u64
  · refine notification.maybe_donate_sched_context.rd hA s a t n Q R h hB hX hS hSg ht ?_ ?_ ?_ ?_ hns hD hr
    · by_contra hq; exact hB.q t ht hq h0
    · by_contra hq; exact hB.r t ht hq h0
    · intro e; exact hB.act (by rw [e]; exact ht) (by rw [e]; exact h0)
    · intro e; exact hB.idle (by rw [e]; exact h0)
  · unfold notification.maybe_donate_sched_context
    step with obj.Tcb.sc.spec as ⟨i, ei⟩
    rw [if_neg (by rw [ei]; exact h0)]
    exact (WP.spec_ok _).2 ⟨hD, hr⟩

theorem endpoint.unblock_sporadic.rd (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T)
    (hD : DomInv st T s) (hr : RC st s) :
    endpoint.unblock_sporadic st s t ⦃ s' => DomInv st T s' ∧ RC st s' ⦄ := by
  unfold endpoint.unblock_sporadic
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hi0, hsp⟩ := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := hS.wf hiS (hS.spor i hiS hsp)
    have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
    step with sched.cur_sc.spec as ⟨c4, _⟩
    step with sc_ne.spec as ⟨b2⟩
    split
    · have hN' := h.nodes _ h.cur
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
      have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
        hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => ?_
      obtain ⟨-, d, r⟩ := ring_facts h hX hS hiS w3
      exact ⟨d hD, r hr⟩
    · exact (WP.spec_ok _).2 ⟨hD, hr⟩
  · exact (WP.spec_ok _).2 ⟨hD, hr⟩

/-- `signal_tail` keeps `DomInv` and `RC`. -/
theorem signal_tail.rd {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s2 : S) (a1 : A)
    (dst n badge : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h2 : SchedQueuesInv st T Cs Ω H s2 Q R) (hB2 : BoundInv st T Ac s2) (hX2 : XInv st T Cs Ω Sg Rp Scs Nt Z s2)
    (hS2 : SCsOK st T Ω Sg Scs Z Ac s2) (hSg2 : SgOK st Ω Sg s2) (hd : dst ∈ T) (hn : n ∈ Nt)
    (dq : (L.mem s2 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (dr : (L.mem s2 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (da : L.actionW s2 ≠ dst) (di : L.idleW s2 ≠ dst) (dR : ¬ BlockedR (L.mem s2 (stA dst)))
    (hD : DomInv st T s2) (hr : RC st s2) :
    (do
      let s3 ← obj.Tcb.set_reg st dst s2 layout.reg.BADGE badge
      let (s4, a2) ← notification.maybe_donate_sched_context st ar s3 a1 dst n
      let b1 ← sched.is_schedulable st s4 dst
      let s5 ← if b1 then sched.possible_switch_to st s4 dst else ok s4
      let s6 ← notification.unblock_sporadic st s5 dst
      ok (s6, a2)) ⦃ s' _ => DomInv st T s' ∧ RC st s' ⦄ := by
  have hT := h2.tcbs
  have hta := hT dst hd
  refine WP.spec_bind (obj.Tcb.set_reg.badge s2 dst badge hta) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, hB3, hX3, hS3, hSg3⟩ := badge_all (v := badge) h2 hB2 hX2 hS2 hSg2 hd
  have F3 : FootN st T True T Cs Sg Scs Z (∅ : Set U64) s2 (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) :=
    footN_field hT h2.nodes h2.cur hd (by simp) (by simp) (by simp) (by simp)
  have iq3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (inqA dst) = L.mem s2 (inqA dst) := by
    rw [inqA_eq]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp)) (field_aligned hta (by simp) (by simp))
      (fun e => field_ne (K1 := 256#u64) (K2 := 3592#u64) hta hta (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e))
  have ea3 : L.actionW (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) = L.actionW s2 :=
    act_wr_field (h2.nodes _ h2.cur) hd hta rfl (by simp) (by simp)
  have D3 : DomInv st T (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) :=
    DomInv.wr' hD hT (h2.nodes _ h2.cur) (field_aligned hta (by simp) (by simp))
      (field_domFree hT (h2.nodes _ h2.cur) hd (h2.ksOut dst hd) (by simp) (by simp))
  have r3 := RC.fnT h2 F3 ea3 hr
  have ei3 : L.idleW (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) = L.idleW s2 := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp))
      (nodeAt_aligned (h2.nodes _ h2.cur) (by rw [idle8]; omega) (by rw [idle8]))
      (fun e => node_ne_field (K := 256#u64) (h2.nodes _ h2.cur) (by rw [idle8]; omega) hd hta (by simp)
        (UScalar.eq_of_val_eq e).symm)
  have sc3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (scA dst) = L.mem s2 (scA dst) := by
    rw [scA_eq]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp)) (field_aligned hta (by simp) (by simp))
      (fun e => field_ne (K1 := 256#u64) (K2 := 3464#u64) hta hta (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e))
  have hsA3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (scA dst) = 0#u64 →
      ¬ Sch st (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) dst := fun h0 hS => by
    rw [sc3] at h0
    rcases Sch.wr_field h2 hd (by simp) (by simp) (by simp) hd hS with e | e | e | e | ⟨e1, e2⟩ | e
    · exact e dq
    · exact e dr
    · exact da e
    · exact di e
    · exact hB2.resume e1 (by rw [e2]; exact h0)
    · exact dR e
  refine WP.spec_bind (WP.spec_and (notification.maybe_donate_sched_context.ff (Kp := (∅ : Set U64))
    (Il := (∅ : Set U64)) (Ks := (∅ : Set U64)) (Es := (∅ : Set U64)) (U := (∅ : Set U64)) hA _ a1 dst n Q R
    h3 hB3 hX3 hS3 hSg3 hd (by rw [iq3]; exact dq) (by rw [iq3]; exact dr) (by rw [ea3]; exact da)
    (by rw [ei3]; exact di) (ntfn_sc_ok hX3 hn hsA3) (Set.notMem_empty _) (Set.notMem_empty _)
    (fun k hk => absurd hk (Set.notMem_empty _)))
    (notification.maybe_donate_sched_context.rd hA _ a1 dst n Q R h3 hB3 hX3 hS3 hSg3 hd
      (by rw [iq3]; exact dq) (by rw [iq3]; exact dr) (by rw [ea3]; exact da)
      (by rw [ei3]; exact di) (ntfn_sc_ok hX3 hn hsA3) D3 r3)) ?_
  rintro ⟨s4, a2⟩ ⟨⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, -⟩, D4, r4⟩
  try simp only [WP.uncurry'_pair]
  step with sched.is_schedulable.spec' as ⟨b1, hb1⟩
  refine WP.spec_bind (Pₘ := fun s5 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s5 ∧ DomInv st T s5 ∧ RC st s5) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch s4 dst Q4 R4 h4 hB4 hSg4 hd (hb1 hb).1
        (fun _ => (hS4.act _ (hX4.2.2.bound dst hd (hb1 hb).2.1).1).2 (hb1 hb).2.2.2))
        (sched.possible_switch_to.rd s4 dst h4 hd D4 r4)) fun s5 hh => ?_
      obtain ⟨⟨p5, -, -⟩, k5⟩ := hh
      exact ⟨⟨p5.inv, p5.bnd, hX4.fr p5.fr, hS4.fr p5.fr, hSg4.fr p5.fr⟩, k5⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, D4, r4⟩
  rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, D5, r5⟩
  refine WP.spec_bind (endpoint.unblock_sporadic.rd s5 dst h5 hX5 hS5 hd D5 r5) ?_
  intro s6 F6
  exact (WP.spec_ok _).2 F6

/-- `vcpu.report` keeps `DomInv` and `RC`: its writes are the thread's
registers and the user words, then the thread's `STATE` (`RUNNING`). -/
theorem vcpu.report.rd {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t badge : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hvm : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (hc : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) = 0#u64)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true t ⦃ b => BufOK U b ⦄)
    (hD : DomInv st T s) (hr : RC st s) :
    vcpu.report st ar s a t badge ⦃ s' => DomInv st T s' ∧ RC st s' ⦄ := by
  have h0 := h
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -⟩ := h0
  refine WP.spec_mono (vcpu.report.xf hA s a t badge h ht hvm hc hU hbuf) ?_
  rintro s' ⟨s1, h1, -, w1, e⟩
  have hN := hq.nodes _ hq.cur
  have hta := hq.tcbs t ht
  have fr : ∀ b, RepW t U b → DomFree st T s b ∧ CurFree st s b := by
    intro b hb
    rcases hb with ⟨K, k1, k2, -, rfl⟩ | hb
    · exact ⟨field_domFree hq.tcbs hN ht (hq.ksOut t ht) (by omega) (by omega),
        CurFree.field hq ht (by omega) (fun _ => ⟨by omega, by omega, by omega⟩)⟩
    · have hu := hU b hb
      exact ⟨⟨fun e => hu.ks layout.ks.CUR_DOMAIN (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
          e.symm, fun y hy e => out_ne_field (K := 3432#u64) hu.out hy (hq.tcbs y hy) (by simp) (by rw [e]; rfl)⟩,
        CurFree.out hq hu.out⟩
  have D1 : DomInv st T s1 := DomInv.freeA hD w1 hq.tcbs (cdomA_alignedN hN) fun b _ hh => (fr b hh).1
  have ea1 : L.actionW s1 = L.actionW s := actionW_of w1 hN (by
    rintro (⟨K, k1, k2, -, e⟩ | hb)
    · exact node_ne_field hN (by rw [act_val]; omega) ht hta (by omega) e
    · exact out_ne_node (hU _ hb).out hq.cur hN (by rw [act_val]; omega) rfl)
  have r1 : RC st s1 := RC.wi hq w1 (fun _ b _ hh => (fr b hh).2) ea1 hr
  obtain ⟨⟨Q1, R1, hq1⟩, -, -, -, -⟩ := h1
  have K2 := sched.set_thread_state.w2 s1 t sched.TS_RUNNING hq1.tcbs (hq1.nodes _ hq1.cur) ht
  rw [e, WP.spec_ok] at K2
  obtain ⟨w2, ea2, st2⟩ := K2
  exact ⟨DomInv.sts hq1 ht w2 D1, RC.sts hq1 ht w2 ea2 st2 (fun _ => not_blocked_running) r1⟩

/-- `signal_vm` keeps `DomInv` and `RC`. -/
theorem signal_vm.rd {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a : A) (i n : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hiT : i ∈ T) (hn : n ∈ Nt)
    (st1 : L.mem s1 (stA i) = sched.TS_RUNNING) (hD : DomInv st T s1) (hr : RC st s1) :
    (do
      let (s2, a1) ← notification.maybe_donate_sched_context st ar s1 a i n
      let b2 ← sched.is_schedulable st s2 i
      let s3 ← if b2 = true then sched.possible_switch_to st s2 i else ok s2
      let i4 ← obj.Tcb.sc st i s3
      let b3 ← obj.Sc.is_null i4
      if b3 = true then ok (s3, a1)
      else do
        let b4 ← sporadic.sc_active st s3 i4
        if b4 = true then do
          let i5 ← obj.Ntfn.sc st n s3
          if i4 = i5 then do
            let b5 ← sporadic.sc_sporadic st s3 i4
            if b5 = true then do
              let s4 ← sched.cur_sc st s3
              let b6 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i4 s4
              if b6 = true then do
                let s5 ← sporadic.unblock_check st s3 i4
                ok (s5, a1)
              else ok (s3, a1)
            else ok (s3, a1)
          else ok (s3, a1)
        else ok (s3, a1)) ⦃ s' _ => DomInv st T s' ∧ RC st s' ⦄ := by
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  have hsA1 : L.mem s1 (scA i) = 0#u64 → ¬ Sch st s1 i := fun h0 hS => by
    rcases hS with e | e | e | e | ⟨e1, e2⟩ | e
    · exact hB1.q i hiT e h0
    · exact hB1.r i hiT e h0
    · exact hB1.act (by rw [e]; exact hiT) (by rw [e]; exact h0)
    · exact hB1.idle (by rw [e]; exact h0)
    · exact hB1.resume e1 (by rw [e2]; exact h0)
    · rw [st1] at e
      rcases e with e | e
      · exact not_blocked_running e
      · exact running_ne.1 e
  refine WP.spec_bind (WP.spec_and (notification.maybe_donate_sched_context.ffB (Kp := (∅ : Set U64))
    (Il := (∅ : Set U64)) (Ks := (∅ : Set U64)) (Es := (∅ : Set U64)) (U := (∅ : Set U64)) hA s1 a i n Q1 R1 q1
    hB1 hX1 hS1 hSg1 hiT (ntfn_sc_ok hX1 hn hsA1) (Set.notMem_empty _) (Set.notMem_empty _)
    (fun k hk => absurd hk (Set.notMem_empty _)))
    (notification.maybe_donate_sched_context.rdB hA s1 a i n Q1 R1 q1 hB1 hX1 hS1 hSg1 hiT
      (ntfn_sc_ok hX1 hn hsA1) hD hr)) ?_
  rintro ⟨s2, a1⟩ ⟨⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩, -⟩, D2, r2⟩
  try simp only [WP.uncurry'_pair]
  step with sched.is_schedulable.spec' as ⟨b2, hb2⟩
  refine WP.spec_bind (Pₘ := fun s3 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ DomInv st T s3 ∧ RC st s3) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch s2 i Q2 R2 q2 hB2 hSg2 hiT (hb2 hb).1
        (fun _ => (hS2.act _ (hX2.2.2.bound i hiT (hb2 hb).2.1).1).2 (hb2 hb).2.2.2))
        (sched.possible_switch_to.rd s2 i q2 hiT D2 r2)) fun s3 hh => ?_
      obtain ⟨⟨p3, -, -⟩, k3⟩ := hh
      exact ⟨⟨p3.inv, p3.bnd, hX2.fr p3.fr, hS2.fr p3.fr, hSg2.fr p3.fr⟩, k3⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩, D2, r2⟩
  rintro s3 ⟨⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩, D3, r3⟩
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => DomInv st T s' ∧ RC st s' ⦄ := (WP.spec_ok _).2 ⟨D3, r3⟩
  step with obj.Tcb.sc.spec as ⟨i4, ei4⟩
  step with obj.Sc.is_null.spec as ⟨b3, _hb3⟩
  refine sig_if _ _ _ _ (fun _ => ok3) (fun _ => ?_)
  refine WP.spec_bind (sporadic.sc_active.spec s3 i4) fun b4 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  refine WP.spec_bind (obj.Ntfn.sc.any s3 n) fun i5 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  step with sporadic.sc_sporadic.spec as ⟨b5, eb5⟩
  refine sig_if _ _ _ _ (fun hb5 => ?_) (fun _ => ok3)
  step with sched.cur_sc.spec as ⟨c4, _⟩
  step with sc_ne.spec as ⟨b6⟩
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  have hi4S : i4 ∈ Scs := (hX3.2.2.bound i hiT (by rw [← ei4]; exact (eb5 hb5).1)).1 |> fun h => by
    rw [← ei4] at h; exact h
  have hiA : i4 ∈ Ac := hS3.spor i4 hi4S (eb5 hb5).2
  have hW : RefillsWF st s3 i4 (Z i4) := hS3.wf hi4S hiA
  have hSCin : SCin st s3 Ω i4 (Z i4) := ⟨hW, hX3.1.scW i4 hi4S⟩
  have hN' := q3.nodes _ q3.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aR : Aligned (L.nodeA s3 layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
  have oR : Outside (L.nodeA s3 layout.node.REPROGRAM) i4 (Z i4) :=
    hSCin.node_out q3.omega q3.cur hN' (by rw [rp]; omega) (by rw [rp])
  refine WP.spec_bind (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s5 w5 => ?_
  obtain ⟨-, d, r⟩ := ring_facts q3 hX3 hS3 hi4S w5
  exact (WP.spec_ok _).2 ⟨d D3, r r3⟩


theorem SchCur.keep' {s s' : S} (hc : L.cpu s' = L.cpu s) (ecur : L.curW s' = L.curW s)
    (eidle : L.idleW s' = L.idleW s)
    (ea : L.mem s' (affA (L.curW s)) = L.mem s (affA (L.curW s)))
    (es : L.mem s' (stA (L.curW s)) = L.mem s (stA (L.curW s)))
    (eq : L.mem s' (inqA (L.curW s)) = L.mem s (inqA (L.curW s))) (h : SchCur st s) : SchCur st s' := by
  refine ⟨?_, ?_, fun hne => ?_⟩
  · rw [ecur, ea, hc]; exact h.aff
  · rw [ecur, es]; exact h.nb
  · rw [ecur] at hne ⊢; rw [eidle] at hne; rw [eq]; exact h.nq hne

/-- **`send_signal` keeps `DomInv` and `RC`.** -/
theorem notification.send_signal.rd {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (n badge : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt)
    (hH : H n = some .ntfn) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄) (hD : DomInv st T s) (hr : RC st s) :
    notification.send_signal st ar s a n badge ⦃ s' _ => DomInv st T s' ∧ RC st s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hNb := hX.2.2.ntb
  have hT := h0.tcbs
  have hN := h0.nodes _ h0.cur
  have hb0 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩
  have saK : notification.set_active st s n badge ⦃ s' => DomInv st T s' ∧ RC st s' ⦄ := by
    unfold notification.set_active
    refine WP.spec_bind (obj.Ntfn.set_state.val s n _) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (obj.Ntfn.set_badge.wr _ n badge) fun s2 e2 => ?_
    subst e2
    obtain ⟨E, EQ, hEW⟩ := h0.eps
    have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hH)
    obtain ⟨hE, hEN, -⟩ := hEW.1 n he
    have hbS : ntfnBdA n ∈ Sg := (hX.1.ntB n hn).1
    have k1 : (epTSA n).val ≠ (L.ksb s).val + 8 := by have := hEN.2; rw [epTSA_val hE]; omega
    have k2 : (ntfnBdA n).val ≠ (L.ksb s).val + 8 := by have := hSg.ks _ hbS; omega
    exact (out2_facts h0 (ep_out hE hEN).2 (h0.omega _ (hSg.sub _ hbS)) k1 k2 hD hr).2
  unfold notification.send_signal
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  refine sig_if _ _ _ _ (fun hidl => ?_) (fun hnidl => ?_)
  · -- an idle notification
    step with obj.Ntfn.bound_tcb.val as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    have OLD : (do
        let s1 ← notification.set_active st s n badge
        if b = true then ok (s1, a)
        else do
          let i2 ← obj.Tcb.state st i s1
          if i2 = sched.TS_RUNNING_VM then notification.kick_guest st ar s1 a i else ok (s1, a))
        ⦃ s' _ => DomInv st T s' ∧ RC st s' ⦄ := by
      refine WP.spec_bind saK fun s1 k1 => ?_
      refine sig_if _ _ _ _ (fun _ => (WP.spec_ok _).2 k1) (fun _ => ?_)
      step with obj.Tcb.state.spec
      refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => (WP.spec_ok _).2 k1)
      refine WP.spec_mono (notification.kick_guest.same hA s1 a i) fun r hr => ?_
      obtain ⟨s', a'⟩ := r
      simp only at hr
      subst hr
      exact k1
    by_cases hb : b = true
    · rw [if_pos hb, if_pos hb]
      refine WP.spec_bind saK fun s1 k1 => ?_
      rw [if_pos hb]
      exact (WP.spec_ok _).2 k1
    rw [if_neg hb]
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    have hiT : i ∈ T := by
      rcases hNb n hn with e | e
      · rw [← ei] at e; exact absurd e hi0
      · rw [← ei] at e; exact e
    have hta := hT i hiT
    step with obj.Tcb.state.spec as ⟨i1, ei1⟩
    refine sig_if _ _ _ _ (fun hrecv => ?_) (fun hnrecv => ?_)
    · have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_RECV := by rw [← ei1, hrecv]
      have hbl : Blocked (L.mem s (stA i)) := by rw [hst]; exact Or.inr (Or.inl rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hiT (not_runnable_of_blocked hbl)
      have htc : L.actionW s = 0#u64 → i ≠ L.curW s := fun e0 et => (hr e0).nb (by rw [← et]; exact hbl)
      refine WP.spec_bind (WP.spec_and (ipc.cancel_ipc.all s a i Q R h0 hiT hB hX hSg.sub)
        (ipc.cancel_ipc.kw (Scs := (∅ : Set U64)) s a i h0 hiT (ObjsOK.noScs hX.1) hSg.sub
          (fun e => absurd e (by rw [hst]; exact blocked_ne_reply (Or.inr (Or.inl rfl))))
          (fun _ h0' => (hX.2.1.recv i hiT hst h0').1))) ?_
      rintro ⟨s1, a1⟩ ⟨⟨h1, hB1, hX1, nb1, nr1, -, k1, -⟩, F1⟩
      try simp only [WP.uncurry'_pair]
      have D1 : DomInv st T s1 := DomInv.keepT h0 hSg k1.toKeepT0 F1 hD
      have r1 : RC st s1 := RC.keepT h0 k1.toKeepT0 htc hr
      have hS1 := hS.keepT hX k1
      have hSg1 : SgOK st Ω Sg s1 := ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb,
        fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩
      have dq1 : (L.mem s1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k1.inqf hiT]; exact dq
      have dr1 : (L.mem s1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k1.inqf hiT]; exact dr
      have da1 : L.actionW s1 ≠ i := by
        rcases k1.act with e | e
        · rw [e]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      refine WP.spec_bind (WP.spec_and (sts_all s1 i _ Q R h1 hB1 hX1 hS1 hSg1 hiT not_blocked_running running_ne
        (Or.inr nb1) (hX1.noref hta nr1 (fun e => nb1 (by rw [e]; exact Or.inr (Or.inl rfl))))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
        (sched.set_thread_state.w2 s1 i sched.TS_RUNNING h1.tcbs (h1.nodes _ h1.cur) hiT)) ?_
      rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩, w2, ea2, -⟩
      have D2 : DomInv st T s2 := DomInv.sts h1 hiT w2 D1
      have r2 : RC st s2 := RC.sts h1 hiT w2 ea2 st2 (fun _ => not_blocked_running) r1
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr
      have dq2 : (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hiT]; exact dq1
      have dr2 : (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hiT]; exact dr1
      have da2 : L.actionW s2 ≠ i := by
        rcases k2.act with e | e
        · rw [e]; exact da1
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hiT)
      exact signal_tail.rd hA s2 a1 i n badge Q R h2' hB2 hX2 hS2 hSg2 hiT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← k1.idleW, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb) D2 r2
    · -- not receiving: the `RunningVM` completion, else active (and kicked)
      rw [if_neg hb]
      refine sig_if _ _ _ _ (fun hvm => ?_) (fun _ => OLD)
      refine WP.spec_bind (vcpu.signal_completes.blk s i) ?_
      rintro b1 hb1
      refine sig_if _ _ _ _ (fun hb1t => ?_) (fun _ => OLD)
      have hvmS : L.mem s (stA i) = sched.TS_RUNNING_VM := by rw [← ei1]; exact hvm
      refine WP.spec_bind (WP.spec_and (vcpu.report.blk hA s a i badge hb0 hiT hvmS (hb1 hb1t) hU (hbuf i hiT))
        (vcpu.report.rd hA s a i badge hb0 hiT hvmS (hb1 hb1t) hU (hbuf i hiT) hD hr)) ?_
      rintro s1 ⟨⟨h1, st1⟩, D1, r1⟩
      exact signal_vm.rd hA s1 a i n h1 hiT hn st1 D1 r1
  · split
    · -- a waiting notification
      rename_i hwait
      have hst1 : L.epState s n = 1#u64 := by rw [← hv, hwait]; unfold obj.NTFN_WAITING; rfl
      obtain ⟨hdT, hbe, hds⟩ := ntfn_head h0 hH hst1
      step with notification.get_queue.spec as ⟨q, eq⟩
      subst eq
      set hd := (L.epQ s n).head with hhd
      have hta := hT hd hdT
      have hbl : Blocked (L.mem s (stA hd)) := by rw [hds]; exact Or.inr (Or.inr rfl)
      obtain ⟨dq, dr, da⟩ := blocked_out h0 hdT (not_runnable_of_blocked hbl)
      have hinv := notification.ntfn_dequeue.inv s hd Q R h0 hdT (by simp) hbl
      rw [hbe] at hinv
      refine WP.spec_bind hinv ?_
      rintro s1 ⟨h1, f1, o1, n1, k1, hcp1, nc1⟩
      have tm1 : TmFr st T Cs Nt s s1 := TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
        fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩
      obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h0 hB hX hS hSg f1 o1 n1 k1 tm1
      have D1 : DomInv st T s1 := DomInv.keep hD k1
        (o1 _ (hSg.ksΩ layout.ks.CUR_DOMAIN (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])))
        fun y hy => f1 y hy 3432#u64 (by simp) (by simp) (by simp) (by simp)
      have r1 : RC st s1 := fun e => by
        have e' : L.actionW s = 0#u64 := ea1 ▸ e
        have hcT : L.curW s ∈ T := h0.curT
        exact SchCur.keep' hcp1 ec1 ei1
          (by rw [affA_eq]; exact f1 _ hcT _ (by simp) (by simp) (by simp) (by simp))
          (by rw [stA_eq]; exact f1 _ hcT _ (by simp) (by simp) (by simp) (by simp))
          (by rw [inqA_eq]; exact f1 _ hcT _ (by simp) (by simp) (by simp) (by simp)) (hr e')
      have st1 : L.mem s1 (stA hd) = sched.TS_BLOCKED_ON_NTFN := by
        rw [stA_eq, f1 hd hdT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hds
      have iq1 : L.mem s1 (inqA hd) = L.mem s (inqA hd) := by
        rw [inqA_eq]; exact f1 hd hdT _ (by simp) (by simp) (by simp) (by simp)
      obtain ⟨-, -, r3, -, r6⟩ := ts_vals
      refine WP.spec_bind (WP.spec_and (sts_all s1 hd _ Q R h1 hB1 hX1 hS1 hSg1 hdT not_blocked_running running_ne
        (Or.inl (Or.inr rfl)) (hX1.noref hta (by rw [st1]; exact blocked_ne_reply (Or.inr (Or.inr rfl)))
          (by rw [st1, r3, r6]; decide))
        ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
        (sched.set_thread_state.w2 s1 hd sched.TS_RUNNING h1.tcbs (h1.nodes _ h1.cur) hdT)) ?_
      rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, st2, k2⟩, w2, ea2, -⟩
      have D2 : DomInv st T s2 := DomInv.sts h1 hdT w2 D1
      have r2 : RC st s2 := RC.sts h1 hdT w2 ea2 st2 (fun _ => not_blocked_running) r1
      have h2' : SchedQueuesInv st T Cs Ω H s2 Q R := h2.congrX empty_congr'
      have dq2 : (L.mem s2 (inqA hd) &&& sched.Q_QUEUED) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dq
      have dr2 : (L.mem s2 (inqA hd) &&& sched.Q_RELEASE) = 0#u64 := by rw [k2.inqf hdT, iq1]; exact dr
      have da2 : L.actionW s2 ≠ hd := by
        rcases k2.act with e | e
        · rw [e, ea1]; exact da
        · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hdT)
      exact signal_tail.rd hA s2 a hd n badge Q R h2' hB2 hX2 hS2 hSg2 hdT hn dq2 dr2 da2
        (fun e => hB.idleNB (by rw [← ei1, ← k2.idleW, e]; exact Or.inl hbl))
        (by rw [st2]; rintro (hb | hb); exact not_blocked_running hb; exact running_ne.1 hb) D2 r2
    · -- an active notification
      step with obj.Ntfn.badge.val as ⟨i, ei⟩
      simp only [lift, Aeneas.Std.bind_ok]
      refine WP.spec_bind (obj.Ntfn.set_badge.wr s n _) fun s1 e1 => ?_
      subst e1
      have hbS : ntfnBdA n ∈ Sg := (hX.1.ntB n hn).1
      exact (WP.spec_ok _).2 (out1_facts h0 (h0.omega _ (hSg.sub _ hbS)) (by have := hSg.ks _ hbS; omega) hD hr)

/-! ## `timer::fire`, the release loop, `awaken` -/

theorem timer.fire_loop.rd {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (hD : DomInv st T s)
    (hr : RC st s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => DomInv st T s' ∧ RC st s' ⦄ := by
  obtain ⟨IKr, IKs, IKp⟩ := IK T Cs Ω H Sg Rp Scs Nt Z Ac U
  unfold timer.fire_loop
  refine WP.spec_mono (P₀ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
    FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ DomInv st T r.1 ∧ RC st r.1) ?_
      fun r hr => by obtain ⟨s', a'⟩ := r; exact hr.2.2.2
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ FootDU st T Cs Sg Scs Z (EH H) U s x.1 ∧
      IbFr (L := L) T s x.1 ∧ DomInv st T x.1 ∧ RC st x.1)
  · rintro ⟨s1, a1, i1⟩ ⟨h1, F1, f1, K1⟩
    simp only at h1 F1 f1 K1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_get.spec as ⟨t, et⟩
      step with obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 ⟨h1, F1, f1, K1⟩
      rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      have hI1 := h1
      obtain ⟨⟨Q1, R1, h1q⟩, -, hX1, -, -⟩ := h1
      have hTm1 := hX1.2.2.tm
      have htT : t ∈ T := by
        have := hTm1.min _ h1q.cur
        rw [← ec] at this; rw [← et] at this
        rcases this with e | e
        · exact absurd e ht0
        · exact e
      step with obj.Tcb.timer_deadline.val as ⟨d, ed⟩
      split
      · exact (WP.spec_ok _).2 ⟨hI1, F1, f1, K1⟩
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (WP.spec_and (timer.remove.tf (s0 := s1) s1 t (TF.start hI1) htT) (IKr s1 t hI1 htT)) ?_
      rintro s2 ⟨⟨h2, f2, -, -, w2⟩, g2⟩
      have F2 : FootDU st T Cs Sg Scs Z (EH H) U s s2 := F1.trans (FootD.u (Foot.d (f2.mono (Set.empty_subset _))))
      have f12 := f1.trans g2
      have N2 : FootN st T True T Cs Sg Scs Z ∅ s1 s2 := TW.fn h1q.tcbs h1q.nodes h1q.cur w2
      have K2 : DomInv st T s2 ∧ RC st s2 := ⟨TW.dom h1q w2 K1.1, RC.fnT h1q N2 (TW.act h1q w2) K1.2⟩
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
          FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ DomInv st T r.1 ∧ RC st r.1) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hb2 := hBA.of_fr f12
          exact WP.spec_mono (WP.spec_and (WP.spec_and
            (notification.send_signal.tinvF hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2)
            (IKs s2 a1 n bd h2 hn (hNt n hn) hb2))
            (notification.send_signal.rd hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2 K2.1 K2.2)) fun r hr => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr
            exact ⟨hr.1.1.1, F2.trans hr.1.1.2.1, f12.trans hr.1.2, hr.2⟩
        · exact (WP.spec_ok _).2 ⟨h2, F2, f12, K2⟩
      rintro ⟨s3, a3⟩ ⟨h3, F3, f3, K3⟩
      simp only at h3 F3 f3 K3
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3', ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have hc3 := h3.1.choose_spec.choose_spec.cur
      have h3' := h3
      obtain ⟨⟨Q3, R3, q3⟩, -, hX3, -, -⟩ := h3'
      obtain ⟨-, d4, r4⟩ := reprogram_facts (v := 1#u64) q3
      exact ⟨reprogram.tinv h3, F3.trans (FootD.u (Foot.d (foot_node (h3.1.choose_spec.choose_spec.nodes _ hc3) hc3
        (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)))), f3.trans (IKp s3 1#u64 h3),
        d4 K3.1, r4 K3.2, by omega⟩
    · exact (WP.spec_ok _).2 ⟨h1, F1, f1, K1⟩
  · exact ⟨h, FootD.u (Foot.d (Foot.refl _)), IbFr.refl s, hD, hr⟩

theorem timer.fire.rd {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (hD : DomInv st T s)
    (hr : RC st s) :
    timer.fire st ar s a ⦃ s' _ => DomInv st T s' ∧ RC st s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.rd hA IK hNt s a now 0#u64 h hBA hD hr

/-- The release loop keeps `DomInv` and `RC`: `release_remove` clears only
the head's `Q_RELEASE` bit (`qq_mask`), then `possible_switch_to`. -/
theorem sched.awaken_loop.rd (s : S) (fuel : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) (hD : DomInv st T s)
    (hr : RC st s) :
    sched.awaken_loop st s fuel ⦃ s' => DomInv st T s' ∧ RC st s' ⦄ := by
  unfold sched.awaken_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val)
    (inv := fun x => Post st T Cs Ω H Sg Ac s x.1 ∧ DomInv st T x.1 ∧ RC st x.1)
  · rintro ⟨s1, fu⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, f1⟩, D1, K1⟩
    have hS1 := hS.fr f1
    unfold sched.awaken_loop.body
    dsimp only
    split
    swap
    · simp only [WP.spec_ok]; exact ⟨D1, K1⟩
    step as ⟨fuel1, efuel⟩
    step with LawfulStore.cur_cpu_spec as ⟨i, ei⟩
    step with obj.node_get.spec as ⟨i1, ei1⟩
    step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
    split
    · simp only [WP.spec_ok]; exact ⟨D1, K1⟩
    step with obj.Tcb.sc.spec as ⟨i2, _⟩
    step with sporadic.ready.spec as ⟨b1⟩
    split
    swap
    · simp only [WP.spec_ok]; exact ⟨D1, K1⟩
    have hR := h1.release _ h1.cur
    have hhead : i1 = (L.relQ s1 (L.cpu s1)).head := by subst_vars; rfl
    have hne : i1 ≠ 0#u64 := by simpa [b_post] using ‹¬b = true›
    have hmem : i1 ∈ R1 (L.cpu s1) := by
      rw [hhead, hR.head] at hne ⊢
      cases hR' : R1 (L.cpu s1) with
      | nil => rw [hR'] at hne; exact absurd rfl hne
      | cons x xs => simp
    have hT1 : i1 ∈ T := h1.memTR h1.cur hmem
    have hc := h1.aff i1 hT1
    refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and (sched.release_remove.sch s1 i1 Q1 R1 h1 hB1 hS1 hT1)
      (sched.release_remove.kwN (Sg := Sg) (Kp := {y | y ≠ i1}) (Nd := True) (Scs := (∅ : Set U64))
        (Z := fun _ => 0) (Es := (∅ : Set U64)) s1 i1 h1 hT1 (fun e => e rfl)))
      (sched.release_remove.foot s1 i1 _ h1.tcbs hT1 (h1.nodes _ hc) (h1.nodes _ h1.cur) (h1.release _ hc)
        (h1.released i1 hT1).1))
      (sched.release_remove.domInv s1 i1 h1 hT1 D1)) ?_
    rintro s2 ⟨⟨⟨⟨⟨⟨Q2, R2, h2⟩, hB2, f2⟩, ea2, -, hst2⟩, F2⟩, -, hinq⟩, D2⟩
    have hcT : L.curW s1 ∈ T := h1.curT
    have hca := h1.tcbs _ hcT
    have hN := h1.nodes _ h1.cur
    have K2 : RC st s2 := fun e => by
      have e' : L.actionW s1 = 0#u64 := ea2 ▸ e
      refine SchCur.keep F2.1 F2.2.1 ?_ ?_ (fnAff h1.tcbs trivial F2 hcT) ?_ ?_ (K1 e')
      · exact F2.idKeep (nodeAt_aligned hN (by rw [curth0]; omega) (by rw [curth0]))
          (Or.inl ⟨_, h1.cur, _, Or.inr (Or.inr (Or.inr ⟨trivial, rfl, by rw [curth0]⟩)), rfl⟩)
      · exact F2.idKeep (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8])) (Or.inl ⟨_, h1.cur, _, Or.inl idle8, rfl⟩)
      · rw [hst2 _ hcT]; exact id
      · intro hq0
        by_cases hic : i1 = L.curW s1
        · rw [← hic, hinq]
          rw [← hic] at hq0
          split
          · exact qq_mask hq0
          · exact hq0
        · rw [F2.idKeep (inqA_aligned hca) (Or.inr (Or.inl ⟨_, hcT, hca, fun e => hic e.symm, Or.inr rfl⟩))]
          exact hq0
    have hrun : Runnable (L.mem s2 (stA i1)) := by
      rw [hst2 i1 hT1]; exact h1.runR _ h1.cur i1 hmem
    have hrel : (L.mem s1 (inqA i1) &&& sched.Q_RELEASE) ≠ 0#u64 :=
      (h1.released i1 hT1).2 (by rw [h1.inR _ h1.cur i1 hmem]; exact hmem)
    refine WP.spec_bind (WP.spec_and (sched.possible_switch_to.sch s2 i1 Q2 R2 h2 hB2 (hS1.fr f2) hT1 hrun (fun h0 => by
      rw [f2.sc i1 hT1] at h0 ⊢; exact hB1.sact i1 hT1 (Or.inr (Or.inl hrel)) h0))
      (sched.possible_switch_to.rd s2 i1 h2 hT1 D2 K2)) ?_
    rintro s3 ⟨⟨⟨hi3, hB3, f3⟩, -, -⟩, D3, K3⟩
    simp only [WP.spec_ok]
    exact ⟨⟨hi3, hB3, f1.trans (f2.trans f3)⟩, D3, K3, by omega⟩
  · exact ⟨⟨⟨Q, R, h⟩, hB, Fr.refl _ _⟩, hD, hr⟩

/-- **`RC` at the end of `awaken`** (the `res` part of `SchPre`), from
`DomInv` and `RC` at its start. -/
theorem sched.awaken.rc {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (hD : DomInv st T s)
    (hr : RC st s) :
    sched.awaken st ar s a ⦃ r => RC st r.1 ⦄ := by
  unfold sched.awaken
  refine WP.spec_bind (WP.spec_and (timer.fire.tinvF hA IK hNt s a h hBA) (timer.fire.rd hA IK hNt s a h hBA hD hr)) ?_
  rintro ⟨s1, a1⟩ hh
  simp only [WP.uncurry'_pair] at hh
  obtain ⟨⟨⟨⟨Q1, R1, h1⟩, hB1, -, hS1, -⟩, -⟩, D1, r1⟩ := hh
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (sched.awaken_loop.rd s1 _ Q1 R1 h1 hB1 hS1.sg D1 r1) ?_
  rintro s2 ⟨-, r2⟩
  exact (WP.spec_ok _).2 r2

/-- **`schedule` closes an entry, `hR` discharged** (`AllCores.schedE` with
the `res` part of `SchPre` from `sched.awaken.rc`). Entry end facts: as
`schedE` (`kb`, `hao`, `hcK`, `hsa`, `hidl`), and `hD` (`DomInv` at the
body's end, FL4's one domain: P1/DomInv, P3 `kernel_entry_domInvU29`) and
`hrs` (`RC` at the body's end). Named premise: `hS0` [W]. -/
theorem AllCores.schedH {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {s0 s : S} (a : A)
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (kb : OKeep2 st T Cs (L.cpu s0) s0 s) (hc : L.cpu s = L.cpu s0)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hao : ActOut st T (OtherK st T Cs (L.cpu s0) s0) s) (hcK : L.curW s ∉ OtherK st T Cs (L.cpu s0) s0)
    (hsa : ActAff st T s) (hD : DomInv st T s) (hrs : RC st s)
    (hidl : L.mem s (stA (L.idleW s)) = sched.TS_IDLE) :
    sched.schedule st ar s a ⦃ s' _ => AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  refine AllCores.schedE hA IK hNt a h0 hcpu hS0 kb hc h hBA hao hcK hsa (fun r hr => ?_) hidl
  have w := sched.awaken.rc hA IK hNt s a h hBA hD hrs
  rw [hr] at w
  exact (WP.spec_ok r).1 w


/-- **`schedule` closes an entry from the body's footprint, `hR` discharged**
(`AllCores.schedB` with `AllCores.schedH`). Entry end facts: `hsa`, `hD`,
`hrs` (as `schedH`). Named premise: `hS0` [W]. -/
theorem AllCores.schedBH {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {s0 s : S} (a : A)
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hB0 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s0)
    (f : FootN st (KI st T Cs (L.cpu s0) s0) True T Cs Sg Scs Z (EH H) s0 s)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (hsa : ActAff st T s)
    (hD : DomInv st T s) (hrs : RC st s) :
    sched.schedule st ar s a ⦃ s' _ => AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨kb, hc, hao, hcK, hidl, -⟩ := AllCores.bodyEnd h0 hcpu hB0 f
  exact AllCores.schedH hA IK hNt a h0 hcpu hS0 kb hc h hBA hao hcK hsa hD hrs hidl

end

end Fl4Proofs.P2.Stall

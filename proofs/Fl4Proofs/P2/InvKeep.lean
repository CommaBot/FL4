/-
P2 (local-path ownership): **keeping the core-placement premises `OwnJ`**
(`P2/InvAff.lean`: (2) `AffSc`, (1) `CurAff`, `CurScOf`, `curT`) across
writes, without new premises.

* `OwnW … E s`: the words `OwnJ` reads — every TCB's `AFFINITY` and `SC`,
  every SC's `CORE`, and every core's `CUR_THREAD`/`CUR_SC` except the cores
  `E`. `OwnJ.frame`: a step whose writes miss `OwnW … E` keeps `OwnJ`, given
  the end state's facts at the cores `E` (a core whose current thread it
  switches). In the ownership map (`P2/OwnMap.lean`) `AFFINITY`, `SC` and
  `CORE` are gate-owned and another core's node words are that core's, so a
  local path's footprint obligation (it writes only words it owns) is the
  `hF` premise of `OwnJ.frame` with `E` = its own core: **an accepted local
  path keeps `OwnJ`** once its footprint obligation is proved and its end
  state satisfies P1's `EntryInv` with the new current thread on this core
  (`OwnJ.accept`, from `EntryInv` via `OwnJ.here_of_entry`; every fast path
  switches only to a thread with `affinity == cur_cpu`,
  `fastpath::schedulable_here`).
* `notOwnW_field` / `notOwnW_node`: TCB fields other than `SC` (3464) and
  `AFFINITY` (3520), and node words other than `CUR_THREAD` (0) and `CUR_SC`
  (24), are no `OwnW` words.
* **Declined local entries keep `OwnJ`**: `OwnJ.ut` (one `update_timestamp`,
  the node's `CUR_TIME`/`CONSUMED`), `OwnJ.localPre` (the `FAULT_IP` write and
  `update_timestamp`), and the decline lemmas of P1 (`syscall_local_decline`,
  `rr_vm_local_decline`, `ioport_local_decline`, `invocation_local_decline`,
  `set_timer_local_decline`, `irq_local_decline`, `vm_local_decline`):
  `OwnJ.decline_syscall`, `…_rr_vm`, `…_ioport`, `…_invocation`,
  `…_set_timer`, `…_irq`, `…_vm`.
* `OwnPl.of_entry`: the placement facts `OwnJ.frame` needs, from `EntryInv`.

What remains for `OwnJ` (still [J] in `InvAff`): every **serial** entry
(`kernel_entry.entry`'s `handle_syscall_old` / `handle_interrupt_entry` and
the VM entries) and the accepted local paths' footprint obligations (P2's own
per-path frame lemmas). P1's footprints (`Foot`/`KW`, QueueFoot*) cover every
TCB word past the cap slots and every SC word, `AFFINITY` and `CORE` included,
so they cannot be reused: the serial case needs a `KW` without `AFFINITY`/
`CORE`/other cores' node words through every operation but `migrate_tcb`,
`configure_flags` and the stall (as `KWB` did for `IPC_BUFFER`), or `AffSc`
threaded through P1's entry invariant.
-/
import Fl4Proofs.P2.InvAff
import Fl4Proofs.P1.LocalTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Cs Scs : Set U64}

theorem own_csc24 : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]

/-- The words `OwnJ` reads, but the node words of the cores `E`. -/
def OwnW (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (E : U64 → Prop) (s : S) (b : U64) :
    Prop :=
  (∃ y ∈ T, b = affA y ∨ b = scA y) ∨ (∃ c ∈ Scs, b = scCoreA c) ∨
    (∃ c ∈ Cs, ¬ E c ∧ (b = L.nodeAt s c layout.node.CUR_THREAD ∨ b = L.nodeAt s c layout.node.CUR_SC))

/-- The placement facts `OwnJ.frame` reads. -/
structure OwnPl (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (s : S) : Prop where
  tcbs : TcbPlaced T
  nodes : ∀ c ∈ Cs, NodePlaced st T s c
  core : ∀ c ∈ Scs, OutsideObjs st T Cs s (scCoreA c)
  scs : ∀ y ∈ T, L.mem s (scA y) ≠ 0#u64 → L.mem s (scA y) ∈ Scs

/-- `OwnPl` from P1's `EntryInv`. -/
theorem OwnPl.of_entry {Ω : Set U64} {H : Heap} {Sg Rp Nt Ac : Set U64} {Z : U64 → Nat} {s : S}
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) : OwnPl st T Cs Scs s := by
  obtain ⟨⟨Q, R, hq⟩, -, hX, hS, -⟩ := h
  exact ⟨hq.tcbs, hq.nodes, fun c hc => hq.omega _ ((objs_omega hX.1 hS.sub).2 c hc).2.1,
    fun y hy h0 => (hX.2.2.bound y hy h0).1⟩

theorem OwnW.aligned {E : U64 → Prop} {s : S} (P : OwnPl st T Cs Scs s) {b : U64}
    (hb : OwnW st T Cs Scs E s b) : Aligned b := by
  rcases hb with ⟨y, hy, rfl | rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, -, rfl | rfl⟩
  · exact field_aligned (K := 3520#u64) (P.tcbs y hy) (by simp) (by simp)
  · exact scA_aligned (P.tcbs y hy)
  · exact (P.core c hc).1
  · exact nodeAt_aligned (P.nodes c hc) (by simp [curth0]) (by simp [curth0])
  · exact nodeAt_aligned (P.nodes c hc) (by simp [own_csc24]) (by simp [own_csc24])

/-- A TCB field other than `SC` and `AFFINITY` is no `OwnW` word. -/
theorem notOwnW_field {E : U64 → Prop} {s : S} (P : OwnPl st T Cs Scs s) {y K : U64} (hy : y ∈ T)
    (hK : K.val < 4096) (h1 : K.val ≠ 3464) (h2 : K.val ≠ 3520) :
    ¬ OwnW st T Cs Scs E s (core.num.U64.wrapping_add y K) := by
  have hya := P.tcbs y hy
  rintro (⟨y', hy', e | e⟩ | ⟨c, hc, e⟩ | ⟨c, hc, -, e | e⟩)
  · exact field_ne (K2 := 3520#u64) hya (P.tcbs y' hy') hK (by simp) (fun _ h => h2 (by simpa using h)) e
  · exact field_ne (K2 := 3464#u64) hya (P.tcbs y' hy') hK (by simp) (fun _ h => h1 (by simpa using h)) e
  · exact out_ne_field (P.core c hc) hy hya hK (congrArg UScalar.val e)
  · exact node_ne_field (P.nodes c hc) (by simp [curth0]) hy hya hK e.symm
  · exact node_ne_field (P.nodes c hc) (by simp [own_csc24]) hy hya hK e.symm

/-- A node word other than `CUR_THREAD` and `CUR_SC` is no `OwnW` word. -/
theorem notOwnW_node {E : U64 → Prop} {s : S} (P : OwnPl st T Cs Scs s) {c o : U64} (hc : c ∈ Cs)
    (ho : o.val < 4288) (h0 : o.val ≠ 0) (h24 : o.val ≠ 24) :
    ¬ OwnW st T Cs Scs E s (L.nodeAt s c o) := by
  rintro (⟨y, hy, e | e⟩ | ⟨c', hc', e⟩ | ⟨c', hc', -, e | e⟩)
  · exact node_ne_field (K := 3520#u64) (P.nodes c hc) ho hy (P.tcbs y hy) (by simp) e
  · exact node_ne_field (K := 3464#u64) (P.nodes c hc) ho hy (P.tcbs y hy) (by simp) e
  · exact out_ne_node (P.core c' hc') hc (P.nodes c hc) ho (congrArg UScalar.val e)
  · exact node_ne_node (P.nodes c hc) (P.nodes c' hc') ho (by simp [curth0])
      (fun _ => by rw [curth0]; exact h0) (congrArg UScalar.val e)
  · exact node_ne_node (P.nodes c hc) (P.nodes c' hc') ho (by simp [own_csc24])
      (fun _ => by rw [own_csc24]; exact h24) (congrArg UScalar.val e)

/-- **`OwnJ` across writes that miss `OwnW … E`**, given the end state's facts
at the cores `E`. -/
theorem OwnJ.frame {E : U64 → Prop} {s s' : S} {F : U64 → Prop} (h : OwnJ st T Cs s)
    (P : OwnPl st T Cs Scs s) (w : WritesIn st s s' F)
    (hF : ∀ b, Aligned b → F b → ¬ OwnW st T Cs Scs E s b)
    (hE : ∀ c ∈ Cs, E c → curTh st s' c ∈ T ∧ L.mem s' (affA (curTh st s' c)) = c ∧
      (L.mem s' (scA (curTh st s' c)) ≠ 0#u64 ∧ curSc st s' c = L.mem s' (scA (curTh st s' c)))) :
    OwnJ st T Cs s' := by
  have k : ∀ b, OwnW st T Cs Scs E s b → L.mem s' b = L.mem s b := fun b hb =>
    w.mem_eq (hb.aligned P) (fun hf => hF b (hb.aligned P) hf hb)
  have hn : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := nodeAt_of_ksb w.1
  have sc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => k _ (Or.inl ⟨y, hy, Or.inr rfl⟩)
  have af : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y) := fun y hy => k _ (Or.inl ⟨y, hy, Or.inl rfl⟩)
  have co : ∀ c ∈ Scs, L.mem s' (scCoreA c) = L.mem s (scCoreA c) := fun c hc =>
    k _ (Or.inr (Or.inl ⟨c, hc, rfl⟩))
  have ct : ∀ c ∈ Cs, ¬ E c → curTh st s' c = curTh st s c := fun c hc he => by
    unfold curTh; rw [hn]; exact k _ (Or.inr (Or.inr ⟨c, hc, he, Or.inl rfl⟩))
  have cs : ∀ c ∈ Cs, ¬ E c → curSc st s' c = curSc st s c := fun c hc he => by
    unfold curSc; rw [hn]; exact k _ (Or.inr (Or.inr ⟨c, hc, he, Or.inr rfl⟩))
  have aff' : AffSc st T s' := fun y hy h0 => by
    rw [sc y hy] at h0 ⊢; rw [co _ (P.scs y hy h0), af y hy]; exact h.affSc y hy h0
  refine ⟨aff', fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · by_cases he : E c
    · exact (hE c hc he).2.1
    · rw [ct c hc he, af _ (h.curT c hc)]; exact h.curAff c hc
  · by_cases he : E c
    · exact (hE c hc he).2.2
    · rw [ct c hc he, sc _ (h.curT c hc), cs c hc he]; exact h.curScOf c hc
  · by_cases he : E c
    · exact (hE c hc he).1
    · rw [ct c hc he]; exact h.curT c hc

/-- The end-state facts at the executing core from P1's `EntryInv`, given the
new current thread on this core with an SC (`BoundInv.resume` when the action
is resume, `EntryInv.cur_sc_ne0`). -/
theorem OwnJ.here_of_entry {Ω : Set U64} {H : Heap} {Sg Rp Nt Ac : Set U64} {Z : U64 → Nat} {s' : S}
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s') (ha : L.mem s' (affA (L.curW s')) = L.cpu s')
    (h0 : L.mem s' (scA (L.curW s')) ≠ 0#u64) :
    curTh st s' (L.cpu s') ∈ T ∧ L.mem s' (affA (curTh st s' (L.cpu s'))) = L.cpu s' ∧
      (L.mem s' (scA (curTh st s' (L.cpu s'))) ≠ 0#u64 ∧
        curSc st s' (L.cpu s') = L.mem s' (scA (curTh st s' (L.cpu s')))) := by
  obtain ⟨⟨Q, R, hq⟩, -, -, -, -, -, -, hc⟩ := h
  exact ⟨hq.curT, ha, h0, hc h0⟩

/-- **An accepted local path keeps `OwnJ`**, from its footprint obligation
(`hF`: it writes no `AFFINITY`, `SC` or `CORE` word, and no other core's
`CUR_THREAD`/`CUR_SC`) and its end state: P1's `EntryInv` with the current
thread on this core and holding an SC. -/
theorem OwnJ.accept {Ω : Set U64} {H : Heap} {Sg Rp Nt Ac : Set U64} {Z : U64 → Nat} {s s' : S}
    {F : U64 → Prop} (h : OwnJ st T Cs s) (P : OwnPl st T Cs Scs s) (w : WritesIn st s s' F)
    (hF : ∀ b, Aligned b → F b → ¬ OwnW st T Cs Scs (· = L.cpu s) s b)
    (he : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s') (ha : L.mem s' (affA (L.curW s')) = L.cpu s')
    (h0 : L.mem s' (scA (L.curW s')) ≠ 0#u64) : OwnJ st T Cs s' := by
  refine h.frame P w hF fun c _ hc => ?_
  have e : c = L.cpu s' := by rw [hc, w.2.1]
  subst e
  exact OwnJ.here_of_entry he ha h0

/-! ## Declined local entries -/

/-- `update_timestamp`'s two writes. -/
theorem utW_writes {s : S} (hN : NodePlaced st T s (L.cpu s)) (n : U64) :
    WritesIn st s (utW (L := L) s n) (fun b => b = ctA (L := L) s ∨ b = cnA (L := L) s) := by
  obtain ⟨hct, hcn, -⟩ := ct_cn hN
  unfold utW
  exact WritesIn.mono (WritesIn.trans (writesIn_wr hct) (writesIn_wr hcn)) fun b hb => hb

theorem notOwnW_ct {E : U64 → Prop} {s : S} (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs) :
    ¬ OwnW st T Cs Scs E s (ctA (L := L) s) :=
  notOwnW_node P hcpu (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
    (by simp [layout.node.CUR_TIME])

theorem notOwnW_cn {E : U64 → Prop} {s : S} (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs) :
    ¬ OwnW st T Cs Scs E s (cnA (L := L) s) :=
  notOwnW_node P hcpu (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
    (by simp [layout.node.CONSUMED])

/-- `OwnJ` after `update_timestamp`'s writes. -/
theorem OwnJ.utW {s : S} (h : OwnJ st T Cs s) (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs) (n : U64) :
    OwnJ st T Cs (utW (L := L) s n) :=
  h.frame (E := fun _ => False) P (utW_writes (P.nodes _ hcpu) n)
    (fun b _ hb => by
      rcases hb with rfl | rfl
      · exact notOwnW_ct P hcpu
      · exact notOwnW_cn P hcpu)
    (fun _ _ he => he.elim)

section
variable {A : Type _} {ar : machine.Arch A}

/-- `OwnJ` after one `update_timestamp`. -/
theorem OwnJ.ut (hA : P0.ArchTotal ar) {s : S} {a : A} {r : S × A} (h : OwnJ st T Cs s)
    (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs) (hu : sched.update_timestamp st ar s a = ok r) :
    OwnJ st T Cs r.1 := by
  obtain ⟨n1, -, er⟩ := ut_now ar hA (P.nodes _ hcpu) hu
  rw [er]; exact h.utW P hcpu n1

/-- `OwnJ` after a local entry's prefix (`FAULT_IP` write, `update_timestamp`). -/
theorem OwnJ.localPre (hA : P0.ArchTotal ar) {s : S} {a : A} {r : S × A} (h : OwnJ st T Cs s)
    (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs) (hcur : L.curW s ∈ T)
    (hp : LocalPre (st := st) ar s a r) : OwnJ st T Cs r.1 := by
  obtain ⟨t, nx, s1, et, -, es1, eu⟩ := hp
  rw [cur_thread_ok] at et
  have ht : t = L.curW s := (ok_inj_ff et).symm
  subst ht
  have hta := P.tcbs _ hcur
  have e1 := obj.Tcb.set_reg.fault_ip (L := L) s (L.curW s) (core.num.U64.wrapping_sub nx 2#u64) hta
  rw [es1, WP.spec_ok] at e1
  subst e1
  have ha : Aligned (core.num.U64.wrapping_add (L.curW s) 392#u64) := field_aligned hta (by simp) (by simp)
  have hN := P.nodes _ hcpu
  have hN1 : NodePlaced st T (L.wr s (core.num.U64.wrapping_add (L.curW s) 392#u64)
      (core.num.U64.wrapping_sub nx 2#u64))
      (L.cpu (L.wr s (core.num.U64.wrapping_add (L.curW s) 392#u64) (core.num.U64.wrapping_sub nx 2#u64))) := by
    rw [LawfulStore.cpu_wr]; exact hN.wr
  obtain ⟨n1, -, er⟩ := ut_now ar hA hN1 eu
  rw [er]
  refine h.frame (E := fun _ => False) P (WritesIn.trans (writesIn_wr ha) (utW_writes hN1 n1))
    (fun b _ hb => ?_) (fun _ _ he => he.elim)
  rcases hb with hb | hb | hb
  · change b = _ at hb; subst hb; exact notOwnW_field P hcur (by simp) (by simp) (by simp)
  · rw [ctA_wr] at hb; subst hb; exact notOwnW_ct P hcpu
  · rw [cnA_wr] at hb; subst hb; exact notOwnW_cn P hcpu

/-- The entry state, or the prefix. -/
theorem OwnJ.pre_or (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {X : Prop} (h : OwnJ st T Cs s)
    (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs) (hcur : L.curW s ∈ T)
    (hd : (s' = s ∧ a' = a) ∨ (LocalPre (st := st) ar s a (s', a') ∧ X)) : OwnJ st T Cs s' := by
  rcases hd with ⟨e, -⟩ | ⟨p, -⟩
  · rw [e]; exact h
  · exact h.localPre hA P hcpu hcur p

/-- **A declined `handle_syscall_local` keeps `OwnJ`.** -/
theorem OwnJ.decline_syscall (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64} {found : U64 × U64}
    (h : OwnJ st T Cs s) (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs) (hcur : L.curW s ∈ T)
    (hd : syscall.handle_syscall_local st ar s a n found = ok (false, s', a')) : OwnJ st T Cs s' :=
  h.pre_or hA P hcpu hcur (syscall_local_decline ar hd)

/-- **A declined `handle_reply_recv_vm_local` keeps `OwnJ`.** -/
theorem OwnJ.decline_rr_vm (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {found : U64 × U64}
    (h : OwnJ st T Cs s) (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs) (hcur : L.curW s ∈ T)
    (hd : syscall.handle_reply_recv_vm_local st ar s a found = ok (false, s', a')) : OwnJ st T Cs s' :=
  h.pre_or hA P hcpu hcur (rr_vm_local_decline ar hd)

/-- **A declined `handle_ioport_local` keeps `OwnJ`.** -/
theorem OwnJ.decline_ioport (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64}
    (h : OwnJ st T Cs s) (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs) (hcur : L.curW s ∈ T)
    (hd : syscall.handle_ioport_local st ar s a n = ok (false, s', a')) : OwnJ st T Cs s' :=
  h.pre_or hA P hcpu hcur (ioport_local_decline ar hd)

/-- **A declined `handle_invocation_local` keeps `OwnJ`.** -/
theorem OwnJ.decline_invocation (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64} {p : localinv.Plan}
    (h : OwnJ st T Cs s) (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs) (hcur : L.curW s ∈ T)
    (hd : syscall.handle_invocation_local st ar s a n p = ok (false, s', a')) : OwnJ st T Cs s' :=
  h.pre_or hA P hcpu hcur (invocation_local_decline ar hd)

/-- **A declined `handle_set_timer_local` keeps `OwnJ`.** -/
theorem OwnJ.decline_set_timer (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64} {target : U64}
    (h : OwnJ st T Cs s) (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs) (hcur : L.curW s ∈ T)
    (hd : localtimer.handle_set_timer_local st ar s a n target = ok (false, s', a')) : OwnJ st T Cs s' :=
  h.pre_or hA P hcpu hcur (set_timer_local_decline ar hd)

/-- **A declined `handle_timer_irq_local` keeps `OwnJ`.** -/
theorem OwnJ.decline_irq (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64}
    {p : localtimer.TimerIrqPlan} (h : OwnJ st T Cs s) (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs)
    (hd : localtimer.handle_timer_irq_local st ar s a irq p = ok (false, s', a')) : OwnJ st T Cs s' := by
  rcases irq_local_decline ar hd with ⟨e, -⟩ | hu
  · rw [e]; exact h
  · exact h.ut hA P hcpu hu

/-- **A declined `handle_vm_fault_local` keeps `OwnJ`.** -/
theorem OwnJ.decline_vm (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {addr code : U64}
    (h : OwnJ st T Cs s) (P : OwnPl st T Cs Scs s) (hcpu : L.cpu s ∈ Cs)
    (hd : syscall.handle_vm_fault_local st ar s a addr code = ok (false, s', a')) : OwnJ st T Cs s' :=
  h.ut hA P hcpu (vm_local_decline ar hd)

end

end

end Fl4Proofs.P1

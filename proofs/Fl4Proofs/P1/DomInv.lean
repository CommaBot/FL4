/-
P1 (p1dom): **FL4's one domain** (`DomInv`): the `CUR_DOMAIN` word is 0 and
every TCB's `DOMAIN` word is 0, so every TCB's `DOMAIN` word equals
`CUR_DOMAIN` (`DomInv.cur`; seL4's `ct_in_cur_domain` / `valid_queues` domain
facts, uniform under `numDomains = 1`).

FL4 is built with `NUM_DOMAINS = 1` (`fl4_abi::config::NUM_DOMAINS`,
Fl4Core/Funs.lean `fl4_abi.config.NUM_DOMAINS := 1#u64`). The writers in
fl4-core:

* `DOMAIN` words: `sched::set_domain` (crates/fl4-core/src/sched.rs:701-703),
  called only from the domain cap's `DomainSetSet` (domain.rs:22-38), which
  rejects `dom >= NUM_DOMAINS` (domain.rs:23), so it writes 0;
  `objects::create_object` (objects.rs:453-454) copies `CUR_DOMAIN` into a new
  TCB; boot (boot.rs:723) sets the root thread's to 0 (idle threads and every
  other TCB word start zeroed).
* `CUR_DOMAIN`: boot (boot.rs:744) sets 0; `next_domain` (sched.rs:566-577,
  from `schedule_choose_new_thread` when the domain time is 0, sched.rs:620-624)
  sets it to the domain of the domain-schedule entry it switches to; those
  entries are written only by boot (boot.rs:746, domain 0) and
  `DomainScheduleConfigure` (domain.rs:44-63), which rejects `dom >= NUM_DOMAINS`
  (domain.rs:50). So `CUR_DOMAIN` can change, but only to 0: the invariant is
  stated with the absolute value 0 (the relative form alone is not inductive:
  `set_domain` writes 0 whatever `CUR_DOMAIN` is). P3/XTopJointDomInv29 has
  `next_domain` (`sched.next_domain.domInv`, from the schedule entries' domain
  words, `NdDomOK`).

Here: `DomInv`, its frames (`keep`, `mono`, `writesIn`, `wr`), and the
`DOMAIN` writers (`obj.Tcb.set_domain.domInv`: a TCB's `DOMAIN` set to 0;
`create_tcb_domain.domInv`: `create_object`'s `set_domain (cur_domain)`).

The existing P1 footprints (`KW`/`Foot`, `Cur0W`, `SchedW`) include the
`DOMAIN` words and the kernel-global area, so they do not frame `DomInv` by
themselves; P3's relation carries it (`SchedSpec.curDom` / `.tcb`), and
P3/XTopJointDomInv29 proves `DomInv` at every joint state and at the exit of
every kernel entry `kernel_entry_reachU29` reaches. No premise.
-/
import Fl4Proofs.P1.QueueFire
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Cs Ω : Set U64} {H : Heap}

/-- The `CUR_DOMAIN` word (layout.rs `ks::CUR_DOMAIN`). -/
def cdomA (st : machine.Store S) [L : LawfulStore st] (s : S) : U64 :=
  core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN

/-- **FL4's one domain**: `CUR_DOMAIN` is 0 and so is every TCB's `DOMAIN`
word (module docstring). -/
def DomInv (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) : Prop :=
  L.mem s (cdomA st s) = 0#u64 ∧ ∀ t ∈ T, L.mem s (domA t) = 0#u64

/-- Every TCB's `DOMAIN` word is the `CUR_DOMAIN` word. -/
theorem DomInv.cur {s : S} (h : DomInv st T s) : ∀ t ∈ T, L.mem s (domA t) = L.mem s (cdomA st s) :=
  fun t ht => (h.2 t ht).trans h.1.symm

theorem DomInv.mono {T' : Set U64} {s : S} (h : DomInv st T s) (hT : T' ⊆ T) : DomInv st T' s :=
  ⟨h.1, fun t ht => h.2 t (hT ht)⟩

/-- `DomInv` reads the `CUR_DOMAIN` word and the TCBs' `DOMAIN` words only. -/
theorem DomInv.keep {s s' : S} (h : DomInv st T s) (hk : L.ksb s' = L.ksb s)
    (hc : L.mem s' (cdomA st s) = L.mem s (cdomA st s))
    (hd : ∀ t ∈ T, L.mem s' (domA t) = L.mem s (domA t)) : DomInv st T s' := by
  refine ⟨?_, fun t ht => (hd t ht).trans (h.2 t ht)⟩
  show L.mem s' (core.num.U64.wrapping_add (L.ksb s') layout.ks.CUR_DOMAIN) = 0#u64
  rw [hk]; exact hc.trans h.1

theorem domA_aligned {t : U64} (ht : TcbAddr t) : Aligned (domA t) :=
  field_aligned (K := 3432#u64) ht (by simp) (by simp)

theorem domA_val {t : U64} (ht : TcbAddr t) : (domA t).val = t.val + 3432 := by
  unfold domA; rw [field_val ht (by simp)]; simp

theorem cdomA_val {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) : (cdomA st s).val = (L.ksb s).val + 8 := by
  unfold cdomA; rw [ks_val h (by simp [layout.ks.CUR_DOMAIN])]; simp [layout.ks.CUR_DOMAIN]

theorem cdomA_aligned {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) : Aligned (cdomA st s) :=
  ks_aligned h (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])

/-- A step writing outside the `CUR_DOMAIN` word and the `DOMAIN` words keeps
`DomInv`. -/
theorem DomInv.writesIn {s s' : S} {A : U64 → Prop} (h : DomInv st T s) (w : WritesIn st s s' A)
    (hT : TcbPlaced T) (hka : Aligned (cdomA st s)) (hc : ¬ A (cdomA st s)) (hd : ∀ t ∈ T, ¬ A (domA t)) :
    DomInv st T s' :=
  h.keep w.1 (w.2.2 _ hka hc) fun t ht => w.2.2 _ (domA_aligned (hT t ht)) (hd t ht)

/-- One aligned write of another word keeps `DomInv`. -/
theorem DomInv.wr {s : S} {a v : U64} (h : DomInv st T s) (hT : TcbPlaced T) (ha : Aligned a)
    (hka : Aligned (cdomA st s)) (hc : a.val ≠ (cdomA st s).val) (hd : ∀ t ∈ T, a.val ≠ (domA t).val) :
    DomInv st T (L.wr s a v) :=
  h.writesIn (writesIn_wr ha) hT hka (fun e => hc (by rw [e])) fun t ht e => hd t ht (by rw [e])

/-! ## The `DOMAIN` writers -/

theorem obj.Tcb.set_domain.wr_eq (s : S) (t v : U64) :
    obj.Tcb.set_domain st t s v = ok (L.wr s (domA t) v) := by
  unfold obj.Tcb.set_domain domA
  rw [show layout.tcb.DOMAIN = ok 3432#u64 by unfold layout.tcb.DOMAIN layout.tcb.F; rfl]
  simp only [lift, bind_ok, L.write_eq]

/-- **`set_domain`'s write of a 0 domain** (the only value `DomainSetSet`
passes, domain.rs:23, and `create_object`'s copy of a 0 `CUR_DOMAIN`) keeps
`DomInv`, with the written TCB added; `t`'s object lies outside the
kernel-global area (`SchedQueuesInvX.ksOut`'s form). -/
theorem obj.Tcb.set_domain.domInv (s : S) (t v : U64) (h : DomInv st T s) (hT : TcbPlaced T)
    (ht : TcbAddr t) (hka : Aligned (cdomA st s)) (hkv : (cdomA st s).val = (L.ksb s).val + 8)
    (hko : t.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val) (hv : v = 0#u64) :
    obj.Tcb.set_domain st t s v ⦃ s' => DomInv st (insert t T) s' ⦄ := by
  rw [obj.Tcb.set_domain.wr_eq, WP.spec_ok]
  have hal := domA_aligned ht
  have hne : (domA t).val ≠ (cdomA st s).val := by rw [domA_val ht, hkv]; omega
  refine ⟨?_, fun y hy => ?_⟩
  · show L.mem _ (core.num.U64.wrapping_add (L.ksb (L.wr s (domA t) v)) layout.ks.CUR_DOMAIN) = 0#u64
    rw [L.ksb_wr]
    exact (L.mem_wr_ne hal hka hne).trans h.1
  · rcases Set.mem_insert_iff.1 hy with rfl | hy
    · rw [L.mem_wr_same hal, hv]
    · by_cases e : y = t
      · subst e; rw [L.mem_wr_same hal, hv]
      · have hy' := hT y hy
        rw [L.mem_wr_ne hal (domA_aligned hy') ?_]
        · exact h.2 y hy
        · rw [domA_val ht, domA_val hy']
          intro e'
          exact e (UScalar.eq_of_val_eq (by omega))

/-- **`create_object`'s domain** (objects.rs:453-454): `cur_domain`, then
`set_domain` of the new TCB with it, keeps `DomInv` with the new TCB added. -/
theorem create_tcb_domain.domInv (s : S) (t : U64) (h : DomInv st T s) (hT : TcbPlaced T)
    (ht : TcbAddr t) (hka : Aligned (cdomA st s)) (hkv : (cdomA st s).val = (L.ksb s).val + 8)
    (hko : t.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val) :
    (do
      let d ← sched.cur_domain st s
      obj.Tcb.set_domain st t s d) ⦃ s' => DomInv st (insert t T) s' ⦄ := by
  have e : sched.cur_domain st s = ok (L.mem s (cdomA st s)) := by
    unfold sched.cur_domain obj.ks_get cdomA; simp [L.ks_base_eq, L.read_eq, lift]
  rw [e, bind_ok]
  exact obj.Tcb.set_domain.domInv s t _ h hT ht hka hkv hko h.1

/-- `DomainSetSet`'s check (domain.rs:23): a domain below `NUM_DOMAINS` is 0. -/
theorem dom_lt_num {d : U64} (h : ¬ (d ≥ layout.NUM_DOMAINS)) : d = 0#u64 := by
  rw [show layout.NUM_DOMAINS = 1#u64 by unfold layout.NUM_DOMAINS fl4_abi.config.NUM_DOMAINS; rfl] at h
  apply UScalar.eq_of_val_eq
  have : d.val < 1 := by scalar_tac
  rw [show (0#u64 : U64).val = 0 by simp]; omega

end

end Fl4Proofs.P1

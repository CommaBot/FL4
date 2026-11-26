/-
P3 (line mmuAD, gen 34): **overwriting a written message word, buffer case** (spec side), toward `ReportJ3`
(gen 33's P3/JAtZV3MrSet has the register case).

FL4's `vcpu::report` overwrites buffer MRs it wrote before (the GPRs MR10..24 and MR7/8/9/29 over the exit record
when `VALID = 0`, `finish_notification`'s MR4/5/6/25/26); the spec writes the final list once (`setMrs`). Here:

* `v3_storeMem_apply`: X64 `storeWord`'s byte memory, pointwise (`(a - p).toNat < 8`: byte `7 - (a - p)` of the
  word, else the old byte); hence **`v3_storeMem_same`** (a store over a store at the same address) and
  **`v3_storeMem_comm`** (stores to disjoint 8-byte ranges commute; `v3_buf_disj`: buffer words `x ≠ y < 128`).
* `v3_mrMem_store`, **`v3_mrMem_set`** (storing word `j` of a written zip list = the list with `j` replaced),
  `v3_mrPairs_set_mem`, **`v3_mrState_set_ge`** / **`v3_mrStateN_set_ge`** (`4 ≤ k < |ms| ≤ 120`), and the
  `jMrSt` forms **`v3_jMrSt_set_lt`** (register, both buffer cases) / **`v3_jMrSt_setN_ge`** (no buffer).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3MrSet
import Fl4Proofs.P3.XTopJointFault
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open Fl4Spec

noncomputable section

/-- **`storeWord`'s byte memory, pointwise.** -/
theorem v3_storeMem_apply (um : Word → Word8) (p w a : Word) :
    storeMem um p w a =
      if (a - p).toNat < 8 then (wordRsplit w : List Word8).getD (7 - (a - p).toNat) 0 else um a := by
  unfold storeMem
  rw [intUpto_07]
  simp only [List.foldl_cons, List.foldl_nil, Function.update_apply]
  simp only [← sub_eq_iff_eq_add']
  generalize a - p = d
  by_cases hn : d.toNat < 8
  · obtain ⟨n, hn8, rfl⟩ : ∃ n, n < 8 ∧ d = BitVec.ofNat 64 n :=
      ⟨d.toNat, hn, BitVec.eq_of_toNat_eq (by simp <;> omega)⟩
    interval_cases n <;> simp (config := { decide := true })
  · have hne : ∀ c : Word, c.toNat < 8 → (d = c) = False := fun c hc => eq_false fun e => hn (e ▸ hc)
    rw [if_neg hn]
    simp only [hne _ (by decide : (BitVec.ofInt 64 0).toNat < 8), hne _ (by decide : (BitVec.ofInt 64 1).toNat < 8),
      hne _ (by decide : (BitVec.ofInt 64 2).toNat < 8), hne _ (by decide : (BitVec.ofInt 64 3).toNat < 8),
      hne _ (by decide : (BitVec.ofInt 64 4).toNat < 8), hne _ (by decide : (BitVec.ofInt 64 5).toNat < 8),
      hne _ (by decide : (BitVec.ofInt 64 6).toNat < 8), hne _ (by decide : (BitVec.ofInt 64 7).toNat < 8),
      ↓reduceIte]

/-- **A store over a store at the same address.** -/
theorem v3_storeMem_same (um : Word → Word8) (p w w' : Word) :
    storeMem (storeMem um p w) p w' = storeMem um p w' := by
  funext a
  simp only [v3_storeMem_apply]
  split_ifs <;> rfl

/-- **Stores to disjoint 8-byte ranges commute.** -/
theorem v3_storeMem_comm (um : Word → Word8) (p q w w' : Word)
    (h : ∀ a : Word, (a - p).toNat < 8 → (a - q).toNat < 8 → False) :
    storeMem (storeMem um p w) q w' = storeMem (storeMem um q w') p w := by
  funext a
  simp only [v3_storeMem_apply]
  by_cases h1 : (a - p).toNat < 8
  · by_cases h2 : (a - q).toNat < 8
    · exact (h a h1 h2).elim
    · simp only [h1, h2, ↓reduceIte]
  · simp only [h1, ↓reduceIte]

/-- Two buffer words `x ≠ y` (both `< 128`) have disjoint byte ranges. -/
theorem v3_buf_disj (p : Word) {x y : Nat} (hxy : x ≠ y) (hx : x < 128) (hy : y < 128) (a : Word) :
    (a - bufAddr p x).toNat < 8 → (a - bufAddr p y).toNat < 8 → False := by
  intro h1 h2
  unfold bufAddr wordSize at h1 h2
  rw [sub_add_eq_sub_sub, BitVec.toNat_sub, BitVec.toNat_ofNat] at h1 h2
  have hd := (a - p).isLt
  have e : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  rw [e] at h1 h2 hd
  omega

theorem v3_mrMem_store (p : Word) {x : Nat} (hx : x < 128) : ∀ (xs : List Nat) (ys : List Word)
    (um : Word → Word8) (v : Word), (∀ y ∈ xs, y ≠ x ∧ y < 128) →
    mrMem (storeMem um (bufAddr p x) v) p (xs.zip ys) = storeMem (mrMem um p (xs.zip ys)) (bufAddr p x) v
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | y :: xs, w :: ys, um, v, h => by
    obtain ⟨hyx, hy⟩ := h y (by simp)
    show mrMem (storeMem (storeMem um (bufAddr p x) v) (bufAddr p y) w) p (xs.zip ys) =
      storeMem (mrMem (storeMem um (bufAddr p y) w) p (xs.zip ys)) (bufAddr p x) v
    rw [v3_storeMem_comm _ _ _ _ _ (v3_buf_disj p (Ne.symm hyx) hx hy),
      v3_mrMem_store p hx xs ys _ v (fun z hz => h z (by simp [hz]))]

/-- **Storing word `j` of a written zip list** = writing the list with word `j` replaced. -/
theorem v3_mrMem_set (p : Word) : ∀ (xs : List Nat) (ys : List Word) (um : Word → Word8) (j : Nat) (v : Word),
    xs.Nodup → (∀ y ∈ xs, y < 128) → j < xs.length → j < ys.length →
    storeMem (mrMem um p (xs.zip ys)) (bufAddr p (xs.getD j 0)) v = mrMem um p (xs.zip (ys.set j v))
  | [], _, _, _, _, _, _, hj, _ => absurd hj (by simp)
  | _ :: _, [], _, _, _, _, _, _, hj => absurd hj (by simp)
  | x :: xs, w :: ys, um, 0, v, hnd, hlt, _, _ => by
    obtain ⟨hxn, -⟩ := List.nodup_cons.1 hnd
    have hA : ∀ y ∈ xs, y ≠ x ∧ y < 128 := fun y hy =>
      ⟨fun e => hxn (e ▸ hy), hlt y (List.mem_cons_of_mem _ hy)⟩
    have hx := hlt x (by simp)
    show storeMem (mrMem (storeMem um (bufAddr p x) w) p (xs.zip ys)) (bufAddr p x) v =
      mrMem (storeMem um (bufAddr p x) v) p (xs.zip ys)
    rw [v3_mrMem_store p hx xs ys um w hA, v3_storeMem_same, v3_mrMem_store p hx xs ys um v hA]
  | x :: xs, w :: ys, um, j + 1, v, hnd, hlt, hj, hj' => by
    show storeMem (mrMem (storeMem um (bufAddr p x) w) p (xs.zip ys)) (bufAddr p (xs.getD j 0)) v =
      mrMem (storeMem um (bufAddr p x) w) p (xs.zip (ys.set j v))
    exact v3_mrMem_set p xs ys _ j v (List.nodup_cons.1 hnd).2 (fun y hy => hlt y (List.mem_cons_of_mem _ hy))
      (by simp at hj; omega) (by simp at hj'; omega)

theorem v3_drop_set_ge (ms : List Word) (v : Word) {k : Nat} (h4 : 4 ≤ k) :
    (ms.set k v).drop 4 = (ms.drop 4).set (k - 4) v := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop]
  by_cases e : i = k - 4
  · subst e
    rw [show 4 + (k - 4) = k by omega, List.getElem?_set_self', List.getElem?_set_self', List.getElem?_drop,
      show 4 + (k - 4) = k by omega]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_drop]

theorem v3_range_getD {k : Nat} (h4 : 4 ≤ k) (hk : k < 120) : (List.range' 5 116).getD (k - 4) 0 = k + 1 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_range' (by omega)]
  simp
  omega

/-- **The buffer words after overwriting word `k`** (`4 ≤ k < |ms| ≤ 120`). -/
theorem v3_mrPairs_set_mem (um : Word → Word8) (p : Word) (ms : List Word) (v : Word) {k : Nat} (h4 : 4 ≤ k)
    (hk : k < ms.length) (h120 : ms.length ≤ 120) :
    mrMem um p (mrPairs (ms.set k v)) = storeMem (mrMem um p (mrPairs ms)) (bufAddr p (k + 1)) v := by
  unfold mrPairs
  rw [v3_drop_set_ge _ _ h4, ← v3_range_getD h4 (by omega)]
  have hnd : (List.range' 5 116).Nodup := by
    first | exact List.nodup_range' | exact List.nodup_range' 5 116 | exact List.nodup_range' (s := 5) (n := 116)
  refine (v3_mrMem_set p (List.range' 5 116) (ms.drop 4) um (k - 4) v hnd
    (fun y hy => by rw [List.mem_range'_1] at hy; omega) (by simp <;> omega) (by simp <;> omega)).symm

theorem v3_mrRegs_set_ge (ctx : Register → Word) (ms : List Word) (v : Word) {k : Nat} (h4 : 4 ≤ k) :
    mrRegs ctx (ms.set k v) = mrRegs ctx ms := by
  funext reg
  rcases mr_cases reg with ⟨j, hj, rfl⟩ | hr
  · rw [mrRegs_mr _ _ hj, mrRegs_mr _ _ hj, List.length_set]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (show k ≠ j by omega)]
  · rw [mrRegs_other _ _ hr, mrRegs_other _ _ hr]

/-- **Overwriting buffer word `k` of a written message** (spec side). -/
theorem v3_mrState_set_ge (σ : State Unit) (rcv : ObjRef) (x : Tcb) (p : ObjRef) (ms : List Word) (v : Word)
    {k : Nat} (h4 : 4 ≤ k) (hk : k < ms.length) (h120 : ms.length ≤ 120) :
    setUm (mrState σ rcv x p ms) (storeMem (mrState σ rcv x p ms).machineState.underlyingMemory
      (bufAddr p (k + 1)) v) = mrState σ rcv x p (ms.set k v) := by
  unfold mrState
  rw [setUm_um, setUm_setUm, v3_mrRegs_set_ge _ _ _ h4, v3_mrPairs_set_mem _ _ _ _ h4 hk h120]

theorem v3_mrStateN_set_ge (σ : State Unit) (rcv : ObjRef) (x : Tcb) (ms : List Word) (v : Word)
    {k : Nat} (h4 : 4 ≤ k) : mrStateN σ rcv x (ms.set k v) = mrStateN σ rcv x ms := by
  unfold mrStateN
  rw [v3_mrRegs_set_ge _ _ _ h4]

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3
open Fl4Spec

noncomputable section

/-- Overwriting a message register (`k < 4`), either buffer case. -/
theorem v3_jMrSt_set_lt (σ0 : State Unit) (rcv : ObjRef) (x0 : Tcb) (pb : Option ObjRef) (ms : List Word)
    (v : Word) {k : Nat} (hk : k < ms.length) (h4 : k < 4) :
    Notif.updK (jMrSt σ0 rcv x0 pb ms) rcv
      (.tcb (Notif.setReg (Endp.withRegs x0 (Endp.mrRegs x0.tcbArch.tcbContext.userRegs ms)) (Endp.mrIdx k) v)) =
    jMrSt σ0 rcv x0 pb (ms.set k v) := by
  cases pb with
  | none => exact Endp.v3_mrStateN_set_lt σ0 rcv x0 ms v hk h4
  | some p => exact Endp.v3_mrState_set_lt σ0 rcv x0 p ms v hk h4

/-- Overwriting a buffer word without a buffer: nothing changes. -/
theorem v3_jMrSt_setN_ge (σ0 : State Unit) (rcv : ObjRef) (x0 : Tcb) (ms : List Word) (v : Word) {k : Nat}
    (h4 : 4 ≤ k) : jMrSt σ0 rcv x0 none (ms.set k v) = jMrSt σ0 rcv x0 none ms :=
  Endp.v3_mrStateN_set_ge σ0 rcv x0 ms v h4

end

end Fl4Proofs.P3

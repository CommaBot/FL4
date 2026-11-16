/-
P3 (DESIGN.md §9), endpoints: **the IPC-buffer part of the message
transfer**.

* `upd_buf`: FL4's write of a mapped buffer word and the spec's store of the
  same user word keep the relation (`EpStateRel.buf`, via
  `load_store_same` / `load_store_other`).
* `copy_mrs_loop1_rel`: FL4's second `copy_mrs` loop (buffer words
  `5 .. n`) refines the spec's buffer copy (`copyBufMem`), when both buffers
  are mapped (`BufMap`).
-/
import Fl4Proofs.P3.EpBufSpec
import Fl4Proofs.P3.EpPush
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-- Word `i` of FL4's IPC buffer at `w` (msg.rs `buf_get` / `buf_set`). -/
def fl4BufA (w i : U64) : U64 := core.num.U64.wrapping_add w (core.num.U64.wrapping_mul i 8#u64)

/-- The IPC buffer at FL4 address `w` and spec address `p` is mapped: its
first 128 words are pairs of `B`. -/
def BufMap (B : Set (U64 × Fl4Spec.Word)) (w : U64) (p : Fl4Spec.Word) : Prop :=
  ∀ i : U64, i.val < 128 → (fl4BufA w i, bufAddr p i.val) ∈ B

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

@[step] theorem msg.buf_get.spec (s : S) (w i : U64) : msg.buf_get st s w i ⦃ v => v = L.mem s (fl4BufA w i) ⦄ := by
  unfold msg.buf_get; step*; simp_all [fl4BufA]
@[step] theorem msg.buf_set.spec (s : S) (w i v : U64) : msg.buf_set st s w i v ⦃ s' => s' = L.wr s (fl4BufA w i) v ⦄ := by
  unfold msg.buf_set; step*; simp_all [fl4BufA]

end

theorem copyBufMem_snoc (um : Fl4Spec.Word → Fl4Spec.Word8) (sb rb : Fl4Spec.Word) :
    ∀ (xs : List Nat) (x : Nat), copyBufMem um sb rb (xs ++ [x]) =
      storeMem (copyBufMem um sb rb xs) (bufAddr rb x) (loadWordAt (copyBufMem um sb rb xs) (bufAddr sb x))
  | [], x => rfl
  | y :: xs, x => copyBufMem_snoc _ sb rb xs x

section
open Fl4Spec
variable {Z : Type}

theorem EpStep.setUm' (σ : State Z) (um : Word → Word8) : EpStep σ (setUm σ um) := ⟨rfl, rfl, fun _ => Or.inl rfl⟩

end

section
variable {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

/-- **Writing a mapped buffer word** on both sides. -/
theorem EpStateRel.upd_buf {Z : Type} {m m' : U64 → U64} {σ : Fl4Spec.State Z} (hR : EpStateRel T E R B m σ)
    (hP : EPlaced T E R B) {wp : U64 × Fl4Spec.Word} (hw : wp ∈ B) (v : U64)
    (hA : Agree m m' (fun b => b.val ≠ wp.1.val)) (hv : m' wp.1 = v) :
    EpStateRel T E R B m' (setUm σ (storeMem σ.machineState.underlyingMemory wp.2 v.bv)) := by
  have g : ∀ a, Aligned a → a.val ≠ wp.1.val → m' a = m a := fun a ha h => hA a ha h
  have hb := hP.bt wp hw; have he := hP.be wp hw; have hr := hP.br wp hw
  refine ⟨fun e he' => ?_, fun r hr' => ?_, fun t ht => ?_, fun wq hq => ?_⟩
  · obtain ⟨x, hk, hx⟩ := hR.ep e he'
    have := he e he'
    refine ⟨x, hk, hx.frame (g _ (a_head hP he').1 (by rw [val_head]; omega))
      (g _ (a_ts hP he').1 (by rw [val_ts hP he']; omega)) fun y hy _ => ?_⟩
    have hya := hP.tcb y hy
    have := hb y hy
    exact ⟨g _ (a_st hya).1 (by rw [val_st hya]; omega), g _ (a_blk hya).1 (by rw [val_blk hya]; omega),
      g _ (a_prev hya).1 (by rw [val_prev hya]; omega), g _ (a_next hya).1 (by rw [val_next hya]; omega)⟩
  · obtain ⟨x, hk, hx⟩ := hR.reply r hr'
    have := hr r hr'
    exact ⟨x, hk, by rw [hx, g _ (a_rtcb hP hr').1 (by rw [rTcbA_val]; omega)]⟩
  · obtain ⟨x, hk, hx⟩ := hR.tcb t ht
    have hta := hP.tcb t ht
    have := hb t ht
    exact ⟨x, hk, hx.frame hta fun a ha hf => hA a ha (by have := hf.range; omega)⟩
  · show (m' wq.1).bv = loadWordAt (storeMem σ.machineState.underlyingMemory wp.2 v.bv) wq.2
    by_cases e : wq.1 = wp.1
    · have e2 : wq.2 = wp.2 := ((hP.binj wq hq wp hw).1 e)
      rw [e, e2, hv, load_store_same]
    · have e2 : wq.2 ≠ wp.2 := fun h => e ((hP.binj wq hq wp hw).2 h)
      rw [hA _ (hP.balign wq hq).1 (val_ne_of_ne e), load_store_other _ _ (hP.balign wp hw).2 (hP.balign wq hq).2 e2]
      exact hR.buf wq hq

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
  {SR : S → Fl4Spec.State Unit → Prop}

/-- The FL4 words of mapped buffers. -/
def BufW (B : Set (U64 × Fl4Spec.Word)) (b : U64) : Prop := ∃ wp ∈ B, b = wp.1

theorem range'_snoc5 (k : Nat) : List.range' 5 (k + 1) = List.range' 5 k ++ [5 + k] := by
  rw [List.range'_concat]; simp

/-- **The second loop of `copy_mrs`**: the buffer words `5 .. n`. -/
theorem copy_mrs_loop1_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {sw rw : U64} {sp rp : Fl4Spec.Word}
    (hms : BufMap B sw sp) (hmr : BufMap B rw rp) (n i0 : U64) (hn : n.val ≤ 120) (hi0 : i0.val = min n.val 4) :
    msg.copy_mrs_loop1 st s sw rw n i0 ⦃ r => r.1.val = n.val ∧
      EpStateRel T E R B (L.mem r.2)
        (setUm σ (copyBufMem σ.machineState.underlyingMemory sp rp (List.range' 5 (n.val - 4)))) ∧
      SR r.2 (setUm σ (copyBufMem σ.machineState.underlyingMemory sp rp (List.range' 5 (n.val - 4)))) ∧
      Agree (L.mem s) (L.mem r.2) (fun b => ¬ BufW B b) ∧ WritesIn st s r.2 (EWrite T E R B) ⦄ := by
  unfold msg.copy_mrs_loop1
  apply loop.spec_decr_nat (measure := fun x => n.val - x.2.val)
    (inv := fun x => i0.val ≤ x.2.val ∧ x.2.val ≤ n.val ∧
      EpStateRel T E R B (L.mem x.1)
        (setUm σ (copyBufMem σ.machineState.underlyingMemory sp rp (List.range' 5 (x.2.val - 4)))) ∧
      SR x.1 (setUm σ (copyBufMem σ.machineState.underlyingMemory sp rp (List.range' 5 (x.2.val - 4)))) ∧
      Agree (L.mem s) (L.mem x.1) (fun b => ¬ BufW B b) ∧ WritesIn st s x.1 (EWrite T E R B))
  · rintro ⟨s', i⟩ ⟨h1, h2, hR', hS', hA', hW'⟩
    unfold msg.copy_mrs_loop1.body
    simp only at h1 h2 hR' hS' hA' hW' ⊢
    by_cases hc1 : i < n
    · have hlt : i.val < n.val := (gt_iff_val).1 hc1
      have h4 : 4 ≤ i.val := by omega
      have hmax : msg.MSG_MAX_LENGTH.val = 120 := by unfold msg.MSG_MAX_LENGTH; rfl
      have hc2 : i < msg.MSG_MAX_LENGTH := (gt_iff_val).2 (by rw [hmax]; omega)
      simp only [hc1, hc2, ↓reduceIte]
      step as ⟨i1, hi1⟩
      step as ⟨v, hv⟩
      step as ⟨s1, hs1⟩
      subst hv hs1
      have hi1v : i1.val = i.val + 1 := by simpa using hi1
      set um' := copyBufMem σ.machineState.underlyingMemory sp rp (List.range' 5 (i.val - 4))
      have hwr := hmr i1 (by omega)
      have hws := hms i1 (by omega)
      have hal := (hP.balign _ hwr).1
      have hag := agree_wr (L := L) (s := s') (v := L.mem s' (fl4BufA sw i1)) hal
      have hR1 := hR'.upd_buf hP hwr (L.mem s' (fl4BufA sw i1)) hag (rd_wr_eq hal)
      have hvb : (L.mem s' (fl4BufA sw i1)).bv = loadWordAt um' (bufAddr sp i1.val) := hR'.buf _ hws
      have hlist : List.range' 5 (i1.val - 4) = List.range' 5 (i.val - 4) ++ [i1.val] := by
        rw [show i1.val - 4 = (i.val - 4) + 1 by omega, range'_snoc5]; congr 2; omega
      have hmem : copyBufMem σ.machineState.underlyingMemory sp rp (List.range' 5 (i1.val - 4)) =
          storeMem um' (bufAddr rp i1.val) (L.mem s' (fl4BufA sw i1)).bv := by
        rw [hlist, copyBufMem_snoc, hvb]
      have hW : WritesIn st s' (L.wr s' (fl4BufA rw i1) (L.mem s' (fl4BufA sw i1))) (EWrite T E R B) :=
        (writesIn_wr hal).mono fun b hb => Or.inr (Or.inr (Or.inr ⟨_, hwr, hb⟩))
      refine ⟨by omega, by omega, ?_, ?_, ?_, (hW'.trans hW).mono fun b h => h.elim id id, by omega⟩
      · rw [hmem]; exact hR1
      · rw [hmem]; exact hH.stable _ _ _ _ hS' hW (EpStep.setUm' _ _)
      · exact fun b hb hn => (hag b hb fun h => hn ⟨_, hwr, UScalar.eq_of_val_eq h⟩).trans (hA' b hb hn)
    · simp only [hc1, ↓reduceIte, WP.spec_ok]
      have : i.val = n.val := by have : ¬ i.val < n.val := fun h => hc1 ((gt_iff_val).2 h); omega
      refine ⟨this, ?_, ?_, hA', hW'⟩ <;> rw [← this] <;> assumption
  · dsimp only
    refine ⟨le_refl _, by omega, ?_, ?_, Agree.rfl', WritesIn.refl s _⟩
    · rw [show i0.val - 4 = 0 by omega]; exact hR
    · rw [show i0.val - 4 = 0 by omega]; exact hSR

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
  {SR : S → Fl4Spec.State Unit → Prop}

/-- The relation after the first `copy_mrs` loop. -/
theorem loop0_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s s1 : S} {σ : Fl4Spec.State Unit}
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T)
    {xs xr : Fl4Spec.Tcb} (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    (k : Nat)
    (hregs : ∀ reg, L.mem s1 (regA rcv (regIdx reg)) =
        if reg ∈ Fl4Spec.msgRegisters.take k then L.mem s (regA snd (regIdx reg))
        else L.mem s (regA rcv (regIdx reg)))
    (hag : Agree (L.mem s) (L.mem s1) (fun b => ¬ RcvMR rcv b)) (hw : WritesIn st s s1 (EWrite T E R B)) :
    EpStateRel T E R B (L.mem s1)
      (updK σ rcv.bv (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take k)))) ∧
    SR s1 (updK σ rcv.bv (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take k)))) := by
  have hra := hP.tcb rcv hr
  have hxs := hR.at_tcb hs hks
  have hxr := hR.at_tcb hr hkr
  set x1 := copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take k) with hx1
  have hnotreg : ∀ b, TF rcv b → (b.val < rcv.val + 256 ∨ rcv.val + 448 ≤ b.val) → ¬ RcvMR rcv b := by
    rintro b - hv' ⟨r, -, hb⟩
    rw [regA_val hra (regIdx_lt r)] at hb; have := regIdx_lt r; omega
  have hR1 : EpStateRel T E R B (L.mem s1) (updK σ rcv.bv (.tcb x1)) := by
    refine hR.upd_tcb hP hr x1 (hag.mono fun b hb h' => hb.2 ?_) (Or.inr ⟨hag _ (a_st hra).1 ?_, hag _ (a_blk hra).1 ?_⟩)
      (hxr.with_regs hra (hag.mono fun b hb => hnotreg b hb.1 hb.2) (copyRegsTcb_other _ _ _) fun r => ?_)
    · obtain ⟨r', -, hb'⟩ := h'
      exact TF.of_val (a_reg hra r').2 hb'
    · exact hnotreg _ (a_st hra).2 (by rw [val_st hra]; omega)
    · exact hnotreg _ (a_blk hra).2 (by rw [val_blk hra]; omega)
    · rw [hregs r, hx1, copyRegsTcb_regs]
      show _ = if r ∈ Fl4Spec.msgRegisters.take k then _ else _
      split
      · exact hxs.regs r
      · exact hxr.regs r
  have hS1 : EpStep σ (updK σ rcv.bv (.tcb x1)) := by
    have h := EpStep.tcb hkr xr.tcbState x1.tcbArch
    rwa [← copyRegsTcb_other] at h
  exact ⟨hR1, hH.stable _ _ _ _ hSR hw hS1⟩

theorem xfer_len_buf {n : U64} (hn : n.val ≤ 120) :
    n.bv = min n.bv (Fl4Spec.natToLen ((Fl4Spec.msg_registers.take (Fl4Spec.unat n.bv)).length +
      ((bufIdx n.bv).map fun _ => ()).length)) := by
  have hl : (Fl4Spec.msg_registers.take (Fl4Spec.unat n.bv)).length + ((bufIdx n.bv).map fun _ => ()).length =
      n.bv.toNat := by
    simp [Fl4Spec.msg_registers, Fl4Spec.msgRegisters, Fl4Spec.unat, bufIdx]
    have : n.bv.toNat = n.val := rfl
    omega
  rw [hl, BitVec.min_def]
  have : Fl4Spec.natToLen n.bv.toNat = n.bv := by unfold Fl4Spec.natToLen; simp
  rw [this, if_pos (BitVec.le_refl _)]

theorem bufIdx_eq (n : U64) : bufIdx n.bv = List.range' 5 (n.val - 4) := by
  unfold bufIdx
  simp only [Fl4Spec.msg_registers, Fl4Spec.msgRegisters, List.length_cons, List.length_nil, Fl4Spec.unat]
  congr 1

/-- **`copy_mrs` with a receive buffer.** -/
theorem copy_mrs_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T)
    (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb} (hks : σ.kheap snd.bv = some (.tcb xs))
    (hkr : σ.kheap rcv.bv = some (.tcb xr)) {rw : U64} {rp : Fl4Spec.Word} (hmr : BufMap B rw rp)
    (hrw0 : rw ≠ 0#u64) (hu : ∀ k, k < 128 → Fl4Spec.inUserFrame (bufAddr rp k) σ) {sw : U64}
    {sb : Option Fl4Spec.ObjRef}
    (hsw : (sb = none ∧ sw = 0#u64) ∨ (∃ sp, sb = some sp ∧ sw ≠ 0#u64 ∧ BufMap B sw sp))
    (n : U64) (hn : n.val ≤ 120) :
    msg.copy_mrs st s snd sw rcv rw n ⦃ r => ∃ σc, Fl4Spec.copyMrs (Z := Unit) snd.bv sb rcv.bv (some rp) n.bv σ =
        ({(r.1.bv, σc)}, False) ∧
      σc.kheap = Function.update σ.kheap rcv.bv (some (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
        (Fl4Spec.msg_registers.take n.val)))) ∧
      EpStateRel T E R B (L.mem r.2) σc ∧ SR r.2 σc ∧
      Agree (L.mem s) (L.mem r.2) (fun b => ¬ RcvMR rcv b ∧ ¬ BufW B b) ∧ r.1.val ≤ 120 ∧
      WritesIn st s r.2 (EWrite T E R B) ∧ EpStep σ σc ⦄ := by
  unfold msg.copy_mrs
  refine WP.spec_bind (copy_mrs_loop0_spec (L := L) hP s hs hr hne n) ?_
  rintro ⟨s1, i⟩ ⟨hi, hregs, hag, hw⟩
  obtain ⟨hR1, hS1⟩ := loop0_rel hH hP hR hSR hs hr hks hkr n.val hregs hag hw
  have hun : Fl4Spec.unat n.bv = n.val := rfl
  set σ1 := updK σ rcv.bv (.tcb (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs (Fl4Spec.msg_registers.take n.val)))
  have hE1 : EpStep σ σ1 := by
    have h := EpStep.tcb hkr xr.tcbState (copyRegsTcb xr xs.tcbArch.tcbContext.userRegs
      (Fl4Spec.msg_registers.take n.val)).tcbArch
    rwa [← copyRegsTcb_other] at h
  simp only [hrw0, ↓reduceIte]
  rcases hsw with ⟨rfl, rfl⟩ | ⟨sp, rfl, hsw0, hms⟩
  · simp only [↓reduceIte]
    show (ok (i, s1)) ⦃ _ ⦄
    simp only [WP.spec_ok]
    refine ⟨σ1, ?_, rfl, hR1, hS1, hag.mono fun b hb => hb.1, by rw [hi]; omega, hw, hE1⟩
    rw [copyMrs_noSendBuf (bv_inj hne) hks hkr _ _, hun]
    congr
    exact (xfer_len (by rw [hi]; rfl)).symm
  · simp only [hsw0, ↓reduceIte]
    refine WP.spec_mono (copy_mrs_loop1_rel hH hP s1 σ1 hR1 hS1 hms hmr n i hn hi) ?_
    rintro ⟨n2, s2⟩ ⟨hn2, hR2, hS2, hA2, hW2⟩
    refine ⟨_, ?_, rfl, hR2, hS2, fun b hb hn' => (hA2 b hb hn'.2).trans (hag b hb hn'.1),
      by rw [hn2]; exact hn, (hw.trans hW2).mono fun b h => h.elim id id, hE1.trans (EpStep.setUm' _ _)⟩
    rw [copyMrs_bufs (bv_inj hne) hks hkr sp rp n.bv ?_]
    · have e : n2 = n := UScalar.eq_of_val_eq hn2
      subst e
      rw [← xfer_len_buf hn, bufIdx_eq, hun]
      rfl
    · intro x hx
      rw [bufIdx_eq] at hx
      have hx' : x < 128 := by simp at hx; omega
      have hp0 := (hP.balign _ (hms 0#u64 (by decide))).2
      have hr0 := (hP.balign _ (hmr 0#u64 (by decide))).2
      simp only [bufAddr, show (0#u64 : U64).val = 0 from rfl, Nat.zero_mul, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero] at hp0 hr0
      refine ⟨?_, ?_, hu x hx'⟩ <;> unfold bufAddr <;> rw [BitVec.toNat_add, BitVec.toNat_ofNat] <;>
        simp only [Fl4Spec.wordSize] <;> omega

theorem lookup_extra_caps_none (s : S) (t buf : U64) (info : msginfo.MessageInfo)
    (h : buf = 0#u64 ∨ info.extra_caps = 0#u64) :
    ipc.lookup_extra_caps st s t buf info ⦃ r => r = .Ok ipc.NO_EXTRA_CAPS ⦄ := by
  unfold ipc.lookup_extra_caps
  by_cases hb : buf = 0#u64
  · simp [hb]
  · simp only [hb, ↓reduceIte]
    have he : info.extra_caps = 0#u64 := h.resolve_left hb
    unfold ipc.lookup_extra_caps_loop
    apply loop.spec_decr_nat (measure := fun _ => 0) (inv := fun x => x.1 = ipc.NO_EXTRA_CAPS)
    · rintro ⟨caps, i⟩ hc
      simp only at hc
      subst hc
      unfold ipc.lookup_extra_caps_loop.body
      have : ¬ i < info.extra_caps := by rw [he]; intro h'; have := (gt_iff_val).1 h'; simp at this
      simp [this]
    · rfl

theorem transfer_caps_noextra (s : S) (info : msginfo.MessageInfo) (ep : U64) (receiver : obj.Tcb) (rb : U64) :
    ipc.transfer_caps st s info ipc.NO_EXTRA_CAPS ep receiver rb ⦃ r =>
      r = ({ label := info.label, caps_unwrapped := 0#u64, extra_caps := 0#u64, length := info.length }, s) ⦄ := by
  unfold ipc.transfer_caps msginfo.MessageInfo.new
  step*
  all_goals simp_all [obj.Slot.is_null, ipc.NO_EXTRA_CAPS]

end

end

end Fl4Proofs.P3.Endp

/-
# P2 (line slhuf, gen 12): `InvCMDecOnceW` — `Once` of the Copy / Mint decode onward

`InvCMDecOnceW` [W] (P2/InvCMOnce.lean): `Once` of `invCMRest` (`decCNG` → `cnode.decode` → `decode_copy` →
`copied_cap`, then `invPostG`, `after_invocation`, `finish`) at the post-check state, from the empty touched set.

* walk lemmas: `hd_step` / `hd_liftR` (a second, decode-only run carried along the walk, so that a leaf knows the
  decode's outcome), `once_bufget` / `once_sargB` (a read of a buffer word not touched before), `once_postErr`
  (an error reply whose error writes no message register: the buffer lookup and `BADGE` on the guard, the buffer
  word `DEBUG_MESSAGE_START + 1` read once from the empty touched set, then writes only), `once_copied`
  (`copied_cap`'s Copy / Mint arm on a non-EPT frame cap: the buffer words of message words 4 and, for Mint, 5,
  each once; `derive_cap` of a frame cap reads nothing), `once_K2` / `once_leafOk` / `once_leafErr` (the reply and
  `finish` after the decode);
* **`invCMRest_once`**: the walk at the post-check state from explicit facts there (no premise);
* **`invCMDecOnceW_of`**: `InvCMDecOnceW` at any `P` with `IoPre`, `InvCMArm`, `CMEnt` (P2/InvCMEnt.lean) and
  `p.slot ∈ K.slots`, from the one remaining premise **`InvCMTailW` [W]**: after the decode, an `Ok` reply
  (`invPostG`) and `finish` after any reply run alike on `guard st (IoRS s) ⊤` (kernel words only; the acc / fin
  lines' generic-store `invRep` and `FinOK` + `syscall.finish.guard_resume` give it).

Error paths reached under `CMEnt`: `TruncatedMessage` (length < 2 / 4 / 5 / 6) and `DeleteFirst`; both write no
message register, so the reply's buffer word is read from the empty touched set (the user reads of message
words 4 / 5 happen only on the success path, after which no user word is read).
-/
import Fl4Proofs.P2.InvCMEnt
import Fl4Proofs.P2.InvCMOnce
import Fl4Proofs.P2.SlOnceL
import Fl4Proofs.P2.InvTrunc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-! ## Walk lemmas -/

section walkL
open Classical
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {Rd User : U64 → Prop}

/-- A second run along a walk: after a step `p`, the continuation's run. -/
theorem hd_step {X Y : Type} {p : SProg X} {f : X → SProg Y} {s : S} {a : A} {r : X × S × A}
    {r0 : Y × S × A} (hd : interp st ar (p.sbind f) s a = ok r0) (h1 : interp st ar p s a = ok r) :
    interp st ar (f r.1) r.2.1 r.2.2 = ok r0 := by
  rw [interp_sbind, h1, bind_ok] at hd
  exact hd

/-- A pure step of the second run. -/
theorem hd_liftR {X Y : Type} {e : Result X} {k : X → SProg Y} {s : S} {a : A} {r : Y × S × A} {v : X}
    (h : interp st ar ((SProg.liftR e).sbind k) s a = ok r) (he : e = ok v) : interp st ar (k v) s a = ok r := by
  subst he
  rw [SProg.liftR_ok] at h
  exact h

theorem tch_sub_insert {Wd T : Set U64} {q : U64} : E2E.tch Rd User Wd q T ⊆ insert q T := by
  unfold E2E.tch
  split_ifs
  · exact subset_rfl
  · exact Set.subset_insert _ _

/-- **A read of a buffer word** (`msg.buf_get`'s tree) not touched before. -/
theorem once_bufget {Y : Type} {b i : U64} {k : U64 → SProg Y} {Wd T : Set U64} {x : S} {a : A}
    {r' : Y × S × A} (h : interp st ar ((R.msg.buf_get b i).sbind k) x a = ok r')
    (hT : core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64) ∉ T)
    (hk : ∀ v, st.read x (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) = ok v →
      interp st ar (k v) x a = ok r' →
      Once st ar Rd User Wd (insert (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) T) (k v) x a) :
    Once st ar Rd User Wd T ((R.msg.buf_get b i).sbind k) x a := by
  unfold R.msg.buf_get at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.read, SProg.sbind] at h ⊢
  simp only [Once]
  refine ⟨fun _ => hT, fun v hv => ?_⟩
  simp only [interp] at h
  obtain ⟨v', hv', h⟩ := bok.mp h
  rw [hv] at hv'
  cases ok_inj_ff hv'
  exact once_mono _ _ _ _ _ x a (hk v hv h) subset_rfl tch_sub_insert

/-- The run after a buffer-word read. -/
theorem interp_bufget {Y : Type} {b i : U64} {k : U64 → SProg Y} {x : S} {a : A} {r' : Y × S × A} {v : U64}
    (h : interp st ar ((R.msg.buf_get b i).sbind k) x a = ok r')
    (hv : st.read x (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) = ok v) :
    interp st ar (k v) x a = ok r' := by
  unfold R.msg.buf_get at h
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.read, SProg.sbind] at h
  simp only [interp] at h
  obtain ⟨v', hv', h⟩ := bok.mp h
  rw [hv] at hv'
  cases ok_inj_ff hv'
  exact h

/-- **A message word past the registers** (`syscall_arg`'s tree, `i ≥ 4`): a read of the buffer word `i + 1`
(none for a null buffer), with a second run `hd` along. -/
theorem once_sargB {Y Z : Type} {t b i : U64} (hi : ¬ i < msg.N_MSG_REGISTERS) {k : U64 → SProg Y}
    {f : U64 → SProg Z} {Wd T : Set U64} {x : S} {a : A} {r' : Y × S × A} {r0 : Z × S × A}
    (h : interp st ar ((R.msg.syscall_arg t b i).sbind k) x a = ok r')
    (hd : interp st ar ((R.msg.syscall_arg t b i).sbind f) x a = ok r0)
    (hT : core.num.U64.wrapping_add b (core.num.U64.wrapping_mul (core.num.U64.wrapping_add i 1#u64) 8#u64) ∉ T)
    (hk : ∀ v, interp st ar (k v) x a = ok r' → interp st ar (f v) x a = ok r0 →
      Once st ar Rd User Wd (insert (core.num.U64.wrapping_add b
        (core.num.U64.wrapping_mul (core.num.U64.wrapping_add i 1#u64) 8#u64)) T) (k v) x a) :
    Once st ar Rd User Wd T ((R.msg.syscall_arg t b i).sbind k) x a := by
  unfold R.msg.syscall_arg at h hd ⊢
  rw [if_neg hi] at h hd ⊢
  by_cases hb : (b != 0#u64) = true
  · rw [if_pos hb] at h hd ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h hd ⊢
    exact once_bufget h hT (fun v hv h' => hk v h' (interp_bufget hd hv))
  · rw [if_neg hb] at h hd ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind] at h hd ⊢
    exact once_mono _ _ _ _ _ x a (hk _ h hd) subset_rfl (Set.subset_insert _ _)

end walkL

/-! ## The error reply -/

section post
variable {S A : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A} {Rd User : U64 → Prop}

theorem error_mrs_df (m : machine.Store S) (x : S) (t buf : U64) :
    syscall.error_mrs m x t buf .DeleteFirst = ok (0#u64, x) := by
  unfold syscall.error_mrs; rfl

theorem error_mrs_il (m : machine.Store S) (x : S) (t buf : U64) :
    syscall.error_mrs m x t buf .IllegalOperation = ok (0#u64, x) := by
  unfold syscall.error_mrs; rfl

set_option maxHeartbeats 4000000 in
/-- **`Once` through an error reply** whose error writes no message register (`he`): the receiver's buffer lookup
and `BADGE` on `guard st R0 W0`, then, with the buffer set, one read of the buffer word `DEBUG_MESSAGE_START + 1`
from the empty touched set, then writes only (on `guard st R0 ⊤`); the continuation holds for every touched set. -/
theorem once_postErr {Y : Type} {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → Rd q ∧ ¬ User q)
    (hW0 : ∀ q, W0 q → ¬ User q) {t sl : U64} {e : error.SysError}
    (he : ∀ (m : machine.Store S) x b, syscall.error_mrs m x t b e = ok (0#u64, x))
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok sl)
    (hI : R0 (core.num.U64.wrapping_add t 3512#u64)) (h0 : R0 sl) (h8 : R0 (core.num.U64.wrapping_add sl 8#u64))
    (hB : W0 (regA t layout.reg.BADGE))
    {K : core.result.Result Unit error.Exc → SProg Y} {x : S} {a : A} {Wd : Set U64} {r' : Y × S × A}
    {w : core.result.Result Unit error.Exc × S × A}
    (h : interp st ar ((R.invPostG t (.Err (.Sys e))).sbind K) x a = ok r')
    (hd : interp st ar (R.invPostG t (.Err (.Sys e))) x a = ok w)
    (hK : interp st ar (K w.1) w.2.1 w.2.2 = ok r' → ∀ Wd' T', Once st ar Rd User Wd' T' (K w.1) w.2.1 w.2.2) :
    Once st ar Rd User Wd ∅ ((R.invPostG t (.Err (.Sys e))).sbind K) x a := by
  have hd' : interp st ar ((R.invPostG t (.Err (.Sys e))).sbind SProg.ret) x a = ok w := by
    rw [SProg.sbind_ret]; exact hd
  clear hd
  unfold R.invPostG at h hd' ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.blk, SProg.sbind_assoc, SProg.sbind] at h hd' ⊢
  unfold R.syscall.reply_error at h hd' ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.blk, SProg.sbind_assoc, SProg.sbind] at h hd' ⊢
  -- the buffer lookup
  refine once_gstep hR0 hW0 (R.msg.lookup_ipc_buffer_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.msg.lookup_ipc_buffer_eq] at h1 ⊢
    rw [msg.lookup_ipc_buffer.guard (gS := PathObl.guard st R0 W0) x true t hsl hI h0 h8]
    exact h1
  have hd1 := hd_step hd' h1
  replace h := hk
  rw [R.msg.lookup_ipc_buffer_eq] at h1
  obtain ⟨b, eb, rfl⟩ := bind_shape h1
  dsimp only at h hd1 ⊢
  -- `BADGE`
  refine once_gstep hR0 hW0 (R.obj.Tcb.set_reg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd2 _ => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st R0 W0) t x _ _ hB]
    exact h1
  have hd2 := hd_step hd1 h1
  replace h := hk
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x1, -, rfl⟩ := bind_shape h1
  dsimp only at h hd2 ⊢
  -- the error words: none
  refine once_gstep hR0 hW0 (R.syscall.error_mrs_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd3 _ => ?_)
  · rw [R.syscall.error_mrs_eq] at h1 ⊢
    rw [he] at h1 ⊢
    exact h1
  have hd3 := hd_step hd2 h1
  replace h := hk
  rw [R.syscall.error_mrs_eq, he] at h1
  obtain ⟨v, ev, rfl⟩ := bind_shape h1
  cases ok_inj_ff ev
  dsimp only at h hd3 ⊢
  simp only [fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte] at h hd3 ⊢
  -- after the buffer word: writes only, for every touched set
  have tail : ∀ (x4 : S) (a : A) (len1 : U64) Wd4 T4,
      interp st ar (((SProg.liftR (error.SysError.code e)).sbind fun i =>
        (SProg.liftR (msginfo.MessageInfo.new i 0#u64 0#u64 len1)).sbind fun mi =>
          (R.msg.set_msg_info t mi).sbind fun _ => K (core.result.Result.Ok ()))) x4 a = ok r' →
      interp st ar (((SProg.liftR (error.SysError.code e)).sbind fun i =>
        (SProg.liftR (msginfo.MessageInfo.new i 0#u64 0#u64 len1)).sbind fun mi =>
          (R.msg.set_msg_info t mi).sbind fun _ => SProg.ret (core.result.Result.Ok ()))) x4 a = ok w →
      Once st ar Rd User Wd4 T4 ((SProg.liftR (error.SysError.code e)).sbind fun i =>
        (SProg.liftR (msginfo.MessageInfo.new i 0#u64 0#u64 len1)).sbind fun mi =>
          (R.msg.set_msg_info t mi).sbind fun _ => K (core.result.Result.Ok ())) x4 a := by
    intro x4 a len1 Wd4 T4 h hd
    refine once_liftR h (fun i ei h => ?_)
    replace hd := hd_liftR hd ei
    refine once_liftR h (fun mi emi h => ?_)
    replace hd := hd_liftR hd emi
    refine once_gstepW (W0 := fun _ => True) hR0 (R.msg.set_msg_info_nz _ _) h (fun r h1 => ?_)
      (fun r h1 hk Wd5 T5 => ?_)
    · rw [R.msg.set_msg_info_eq] at h1 ⊢
      rw [msg.set_msg_info.guard (gS := PathObl.guard st R0 (fun _ => True)) x4 t mi trivial]
      exact h1
    have hd5 := hd_step hd h1
    rw [interp_ret'] at hd5
    have ew := ok_inj_ff hd5
    subst ew
    exact hK hk Wd5 T5
  by_cases hb0 : (b != 0#u64) = true
  · rw [if_pos hb0] at h hd3 ⊢
    try simp only [SProg.sbind_assoc, SProg.sbind] at h hd3 ⊢
    refine once_liftR h (fun i ei h => ?_)
    have hd3' := hd_liftR hd3 ei
    clear hd3
    refine once_bufget h (fun hq => by simp at hq) (fun v hrv h => ?_)
    have hd4 := interp_bufget hd3' hrv
    try simp only [SProg.sbind] at h hd4 ⊢
    refine once_gstepW (W0 := fun _ => True) hR0 (R.msg.buf_set_nz _ _ _) h (fun r h1 => ?_)
      (fun r h1 hk Wd5 T5 => ?_)
    · rw [R.msg.buf_set_eq] at h1 ⊢
      rw [msg.buf_set.guard (gS := PathObl.guard st R0 (fun _ => True)) _ b i _ trivial]
      exact h1
    have hd5 := hd_step hd4 h1
    exact tail _ _ _ _ _ hk hd5
  · rw [if_neg hb0] at h hd3 ⊢
    try simp only [SProg.sbind_assoc, SProg.sbind] at h hd3 ⊢
    exact tail _ _ _ _ _ h hd3

end post

/-! ## `copied_cap` on a frame cap -/

section copied
variable {S A : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A} {Rd User : U64 → Prop}

/-- The buffer word message word `j` (`j ≥ 4`) is read from. -/
def cmW (buf j : U64) : U64 :=
  core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul (core.num.U64.wrapping_add j 1#u64) 8#u64)

theorem cmW_ne (buf : U64) : cmW buf 5#u64 ≠ cmW buf 4#u64 := by
  intro h
  have := congrArg UScalar.val h
  simp [cmW, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def,
    U64.numBits] at this
  omega

theorem cmo_n4 : ¬ (4#u64 : U64) < msg.N_MSG_REGISTERS := by rw [n_msg_regs]; decide
theorem cmo_n5 : ¬ (5#u64 : U64) < msg.N_MSG_REGISTERS := by rw [n_msg_regs]; decide
theorem cmo_mc : fl4_abi.label.CNodeMint ≠ fl4_abi.label.CNodeCopy := by
  unfold fl4_abi.label.CNodeMint fl4_abi.label.CNodeCopy; decide

theorem mask_frame {r : capability.Rights} {fp rt asid va : U64} {sz : capability.FrameSize} {d mp ep : Bool}
    {c : capability.Cap} (h : capability.mask_cap_rights r (.Frame fp sz rt d mp ep asid va) = ok c) :
    ∃ i, c = .Frame fp sz i d mp ep asid va := by
  unfold capability.mask_cap_rights at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  exact ⟨i, (ok_inj_ff h).symm⟩

set_option maxHeartbeats 4000000 in
/-- **`Once` through `copied_cap`'s Copy / Mint arm on a non-EPT frame cap**: the current thread on
`guard st R0 W0`, then the buffer word of message word 4 (and, for Mint, 5), each from a touched set without it;
`derive_cap` of a frame cap reads nothing. Results: `TruncatedMessage` (touched set unchanged) or the derived frame
cap (`insert`ed buffer words). A second run `hd` is carried along. -/
theorem once_copied {Y Z : Type} {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → Rd q ∧ ¬ User q)
    (hW0 : ∀ q, W0 q → ¬ User q) {lbl length buf src fp rt asid va : U64} {sz : capability.FrameSize}
    {d mp : Bool} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    {k : core.result.Result (capability.Cap × Bool) error.Exc → SProg Y}
    {f : core.result.Result (capability.Cap × Bool) error.Exc → SProg Z}
    {x : S} {a : A} {Wd T : Set U64} {r' : Y × S × A} {r0 : Z × S × A}
    (hct : R0 (L.nodeAt x (L.cpu x) layout.node.CUR_THREAD))
    (h : interp st ar ((R.cnode.copied_cap lbl length buf src (.Frame fp sz rt d mp false asid va)).sbind k) x a =
      ok r')
    (hd : interp st ar ((R.cnode.copied_cap lbl length buf src (.Frame fp sz rt d mp false asid va)).sbind f) x a =
      ok r0)
    (h4 : cmW buf 4#u64 ∉ T) (h5 : cmW buf 5#u64 ∉ T)
    (hkE : interp st ar (k (.Err (.Sys .TruncatedMessage))) x a = ok r' →
      interp st ar (f (.Err (.Sys .TruncatedMessage))) x a = ok r0 →
      ∀ Wd', Wd ⊆ Wd' → Once st ar Rd User Wd' T (k (.Err (.Sys .TruncatedMessage))) x a)
    (hkO : ∀ i, interp st ar (k (.Ok (.Frame fp sz i d false false 0#u64 0#u64, false))) x a = ok r' →
      interp st ar (f (.Ok (.Frame fp sz i d false false 0#u64 0#u64, false))) x a = ok r0 →
      ∀ Wd', Wd ⊆ Wd' → Once st ar Rd User Wd' (insert (cmW buf 5#u64) (insert (cmW buf 4#u64) T))
        (k (.Ok (.Frame fp sz i d false false 0#u64 0#u64, false))) x a) :
    Once st ar Rd User Wd T
      ((R.cnode.copied_cap lbl length buf src (.Frame fp sz rt d mp false asid va)).sbind k) x a := by
  unfold R.cnode.copied_cap at h hd ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h hd ⊢
  refine once_gstep hR0 hW0 (R.sched.cur_thread_nz) h (fun r h1 => ?_) (fun r h1 hk Wd1 hW1 => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st R0 W0) x hct]
    exact h1
  have hd1 := hd_step hd h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, -, rfl⟩ := bind_shape h1
  dsimp only at h hd1 ⊢
  -- the common tail: mask, (update), derive, branch
  have hder : ∀ (c : capability.Cap) T1, (∃ i, c = .Frame fp sz i d mp false asid va) → T1 ⊆
      insert (cmW buf 5#u64) (insert (cmW buf 4#u64) T) →
      interp st ar ((R.objects.derive_cap src c).sbind fun r1 =>
        (SProg.liftR (core.result.Result.Insts.CoreOpsTry.branch r1)).sbind fun cf =>
          (match cf with
          | core.ops.control_flow.ControlFlow.Continue val => SProg.ret (core.result.Result.Ok (val, false))
          | core.ops.control_flow.ControlFlow.Break residual =>
            SProg.liftR (core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (capability.Cap × Bool) (core.convert.FromSame error.Exc) residual)).sbind k) x a = ok r' →
      interp st ar ((R.objects.derive_cap src c).sbind fun r1 =>
        (SProg.liftR (core.result.Result.Insts.CoreOpsTry.branch r1)).sbind fun cf =>
          (match cf with
          | core.ops.control_flow.ControlFlow.Continue val => SProg.ret (core.result.Result.Ok (val, false))
          | core.ops.control_flow.ControlFlow.Break residual =>
            SProg.liftR (core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (capability.Cap × Bool) (core.convert.FromSame error.Exc) residual)).sbind f) x a = ok r0 →
      Once st ar Rd User Wd1 T1 ((R.objects.derive_cap src c).sbind fun r1 =>
        (SProg.liftR (core.result.Result.Insts.CoreOpsTry.branch r1)).sbind fun cf =>
          (match cf with
          | core.ops.control_flow.ControlFlow.Continue val => SProg.ret (core.result.Result.Ok (val, false))
          | core.ops.control_flow.ControlFlow.Break residual =>
            SProg.liftR (core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (capability.Cap × Bool) (core.convert.FromSame error.Exc) residual)).sbind k) x a := by
    rintro c T1 ⟨i, rfl⟩ hT1 h hd
    unfold R.objects.derive_cap at h hd ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind, core.result.Result.Insts.CoreOpsTry.branch,
      SProg.liftR_ok] at h hd ⊢
    exact once_mono _ _ _ _ _ x a (hkO i h hd Wd1 hW1) subset_rfl hT1
  rcases hl with rfl | rfl
  · rw [if_pos rfl] at h hd1 ⊢
    by_cases hlen : length < 5#u64
    · rw [if_pos hlen] at h hd1 ⊢
      simp only [error.truncated, SProg.liftR_ok, SProg.sbind] at h hd1 ⊢
      exact hkE h hd1 Wd1 hW1
    rw [if_neg hlen] at h hd1 ⊢
    try simp only [SProg.sbind_assoc] at h hd1 ⊢
    refine once_sargB cmo_n4 h hd1 h4 (fun v h hd => ?_)
    refine once_liftR h (fun rr err h => ?_)
    replace hd := hd_liftR hd err
    refine once_liftR h (fun c ec h => ?_)
    replace hd := hd_liftR hd ec
    exact hder c _ (mask_frame ec) (Set.subset_insert _ _) h hd
  · rw [if_neg cmo_mc, if_pos rfl] at h hd1 ⊢
    by_cases hlen : length < 6#u64
    · rw [if_pos hlen] at h hd1 ⊢
      simp only [error.truncated, SProg.liftR_ok, SProg.sbind] at h hd1 ⊢
      exact hkE h hd1 Wd1 hW1
    rw [if_neg hlen] at h hd1 ⊢
    try simp only [SProg.sbind_assoc] at h hd1 ⊢
    refine once_sargB cmo_n4 h hd1 h4 (fun v h hd => ?_)
    refine once_liftR h (fun rr err h => ?_)
    replace hd := hd_liftR hd err
    refine once_sargB cmo_n5 h hd (fun hm => (Set.mem_insert_iff.mp hm).elim (cmW_ne buf) h5)
      (fun v5 h hd => ?_)
    refine once_liftR h (fun c ec h => ?_)
    replace hd := hd_liftR hd ec
    obtain ⟨i, rfl⟩ := mask_frame ec
    refine once_liftR h (fun c1 ec1 h => ?_)
    replace hd := hd_liftR hd ec1
    have e1 : c1 = .Frame fp sz i d mp false asid va := by
      unfold objects.update_cap_data at ec1; exact (ok_inj_ff ec1).symm
    exact hder c1 _ ⟨i, e1⟩ subset_rfl h hd

end copied

/-! ## The leaves: the reply and `finish` -/

section leaf
variable {S A : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A} {Rd User : U64 → Prop}

/-- After the reply: `after_invocation`, `finish`, `true`. -/
noncomputable def cmK2 : core.result.Result Unit error.Exc → SProg Bool := fun r1 =>
  (R.syscall.after_invocation r1).sbind fun _ => R.syscall.finish.sbind fun _ => SProg.ret true

/-- After the decode: the reply, then `cmK2`. -/
noncomputable def cmK1 (t : U64) : core.result.Result Unit error.Exc → SProg Bool := fun r =>
  (R.invPostG t r).sbind cmK2

theorem invCMRest_eq (t : U64) (info : msginfo.MessageInfo) (p : localinv.Plan) (buf length : U64)
    (cap : capability.Cap) :
    invCMRest t info p buf length cap =
      (R.decCNG info.label length p.slot cap true true true false buf p.extra).sbind (cmK1 t) := rfl

theorem invPostG_okR {m : machine.Store S} {x : S} {a : A} {t : U64} {z : S × A × core.result.Result Unit error.Exc}
    (h : invPostG m x a t (.Ok ()) = ok z) : z.2.2 = .Ok () := by
  unfold invPostG at h
  obtain ⟨i6, -, h⟩ := bind_eq_ok h
  obtain ⟨t1, -, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  subst e
  rfl

theorem invPostG_errR {m : machine.Store S} {x : S} {a : A} {t : U64} {e : error.SysError}
    {z : S × A × core.result.Result Unit error.Exc} (h : invPostG m x a t (.Err (.Sys e)) = ok z) :
    z.2.2 = .Ok () := by
  unfold invPostG at h
  obtain ⟨q, eq, h⟩ := bind_eq_ok h
  obtain ⟨s5, -, eq⟩ := bind_eq_ok eq
  have e1 := ok_inj_ff eq
  subst e1
  have e2 := ok_inj_ff h
  subst e2
  rfl

/-- **`cmK2` is `Once` for every touched set** when `finish` runs alike on `guard st R0 ⊤`. -/
theorem once_K2 {R0 : U64 → Prop} (hR0 : ∀ q, R0 q → Rd q ∧ ¬ User q) {x : S} {a : A} {r' : Bool × S × A}
    (h : interp st ar (cmK2 (.Ok ())) x a = ok r')
    (hf : ∀ y, syscall.finish st ar x a = ok y → syscall.finish (PathObl.guard st R0 (fun _ => True)) ar x a = ok y)
    (Wd T : Set U64) : Once st ar Rd User Wd T (cmK2 (.Ok ())) x a := by
  unfold cmK2 at h ⊢
  refine once_gstepW (W0 := fun _ => True) hR0 (R.syscall.after_invocation_nz _) h (fun r h1 => ?_)
    (fun r h1 hk Wd1 T1 => ?_)
  · rw [R.syscall.after_invocation_eq] at h1 ⊢
    rw [syscall.after_invocation.ok_eq] at h1 ⊢
    exact h1
  rw [R.syscall.after_invocation_eq, syscall.after_invocation.ok_eq] at h1
  obtain ⟨y, ey, rfl⟩ := bind_shape h1
  cases ok_inj_ff ey
  dsimp only at hk ⊢
  refine once_gstepW (W0 := fun _ => True) hR0 (R.syscall.finish_nz) hk (fun r h1 => ?_)
    (fun r h1 hk Wd2 T2 => ?_)
  · rw [R.syscall.finish_eq] at h1 ⊢
    obtain ⟨y, ey, rfl⟩ := bind_shape h1
    rw [hf y ey]
    exact bok.mpr ⟨_, rfl, rfl⟩
  simp only [Once]

/-- **The `Ok` leaf**: the reply and `finish` run alike on `guard st R0 ⊤` (`hI`): `Once` for every touched set. -/
theorem once_leafOk {R0 : U64 → Prop} (hR0 : ∀ q, R0 q → Rd q ∧ ¬ User q) {t : U64} {x : S} {a : A}
    {r' : Bool × S × A} (h : interp st ar (cmK1 t (.Ok ())) x a = ok r')
    (hI : ∀ z, invPostG st x a t (.Ok ()) = ok z →
      invPostG (PathObl.guard st R0 (fun _ => True)) x a t (.Ok ()) = ok z ∧
      ∀ y, syscall.finish st ar z.1 z.2.1 = ok y →
        syscall.finish (PathObl.guard st R0 (fun _ => True)) ar z.1 z.2.1 = ok y)
    (Wd T : Set U64) : Once st ar Rd User Wd T (cmK1 t (.Ok ())) x a := by
  unfold cmK1 at h ⊢
  refine once_gstepW (W0 := fun _ => True) hR0 (R.invPostG_nz _ _) h (fun r h1 => ?_)
    (fun r h1 hk Wd1 T1 => ?_)
  · rw [R.invPostG_eq] at h1 ⊢
    obtain ⟨z, ez, rfl⟩ := bind_shape h1
    rw [(hI z ez).1]
    exact bok.mpr ⟨_, rfl, rfl⟩
  rw [R.invPostG_eq] at h1
  obtain ⟨z, ez, rfl⟩ := bind_shape h1
  dsimp only at hk ⊢
  rw [invPostG_okR ez] at hk ⊢
  exact once_K2 hR0 hk (hI z ez).2 Wd1 T1

/-- **An error leaf** (an error writing no message register): `once_postErr`, then `once_K2`. -/
theorem once_leafErr {R0 : U64 → Prop} (hR0 : ∀ q, R0 q → Rd q ∧ ¬ User q) {t sl : U64} {e : error.SysError}
    (he : ∀ (m : machine.Store S) x b, syscall.error_mrs m x t b e = ok (0#u64, x))
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok sl)
    (hI : R0 (core.num.U64.wrapping_add t 3512#u64)) (h0 : R0 sl) (h8 : R0 (core.num.U64.wrapping_add sl 8#u64))
    (hB : ¬ User (regA t layout.reg.BADGE)) {x : S} {a : A} {r' : Bool × S × A}
    (h : interp st ar (cmK1 t (.Err (.Sys e))) x a = ok r')
    (hfin : ∀ z, invPostG st x a t (.Err (.Sys e)) = ok z → ∀ y, syscall.finish st ar z.1 z.2.1 = ok y →
      syscall.finish (PathObl.guard st R0 (fun _ => True)) ar z.1 z.2.1 = ok y)
    (Wd : Set U64) : Once st ar Rd User Wd ∅ (cmK1 t (.Err (.Sys e))) x a := by
  unfold cmK1 at h ⊢
  have h' := h
  rw [interp_sbind] at h'
  obtain ⟨w, hw, -⟩ := bind_eq_ok' h'
  have hw' := hw
  rw [R.invPostG_eq] at hw'
  obtain ⟨z, ez, hzw⟩ := bind_shape hw'
  refine once_postErr (W0 := fun q => ¬ User q) hR0 (fun _ h => h) he hsl hI h0 h8 hB h hw (fun hk Wd' T' => ?_)
  subst hzw
  dsimp only at hk ⊢
  rw [invPostG_errR ez] at hk ⊢
  exact once_K2 hR0 hk (hfin z ez) Wd' T'

end leaf

/-! ## The decode walk -/

section dec
variable {S A : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A} {Rd User : U64 → Prop}

theorem cm_l1 {lbl : U64} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint) :
    ¬ lbl < fl4_abi.label.CNodeRevoke := by
  have h1 : fl4_abi.label.CNodeRevoke.val = 25 := by simp [fl4_abi.label.CNodeRevoke]
  rcases hl with rfl | rfl
  · have h2 : fl4_abi.label.CNodeCopy.val = 28 := by simp [fl4_abi.label.CNodeCopy]
    scalar_tac
  · have h2 : fl4_abi.label.CNodeMint.val = 29 := by simp [fl4_abi.label.CNodeMint]
    scalar_tac

theorem cm_l2 {lbl : U64} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint) :
    ¬ lbl > fl4_abi.label.CNodeRotate := by
  have h1 : fl4_abi.label.CNodeRotate.val = 32 := by simp [fl4_abi.label.CNodeRotate]
  rcases hl with rfl | rfl
  · have h2 : fl4_abi.label.CNodeCopy.val = 28 := by simp [fl4_abi.label.CNodeCopy]
    scalar_tac
  · have h2 : fl4_abi.label.CNodeMint.val = 29 := by simp [fl4_abi.label.CNodeMint]
    scalar_tac

theorem cm_l3 {lbl : U64} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint) :
    lbl ≥ fl4_abi.label.CNodeCopy := by
  have h1 : fl4_abi.label.CNodeCopy.val = 28 := by simp [fl4_abi.label.CNodeCopy]
  rcases hl with rfl | rfl
  · scalar_tac
  · have h2 : fl4_abi.label.CNodeMint.val = 29 := by simp [fl4_abi.label.CNodeMint]
    scalar_tac

theorem cm_l4 {lbl : U64} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint) :
    lbl ≤ fl4_abi.label.CNodeMutate := by
  have h1 : fl4_abi.label.CNodeMutate.val = 31 := by simp [fl4_abi.label.CNodeMutate]
  rcases hl with rfl | rfl
  · have h2 : fl4_abi.label.CNodeCopy.val = 28 := by simp [fl4_abi.label.CNodeCopy]
    scalar_tac
  · have h2 : fl4_abi.label.CNodeMint.val = 29 := by simp [fl4_abi.label.CNodeMint]
    scalar_tac

theorem fromSame_eq (x : error.Exc) : core.convert.FromSame.from x = x := rfl

theorem prod3_eq {X Y Z : Type} {p q : X × Y × Z} (h : (p.1, p.2.1, p.2.2) = q) : p = q := by
  obtain ⟨_, _, _⟩ := p; exact h

theorem msgreg_R {R0 : U64 → Prop} {t : U64} (h10 : R0 (regA t layout.reg.R10)) (h8 : R0 (regA t layout.reg.R8))
    (h9 : R0 (regA t layout.reg.R9)) (h15 : R0 (regA t layout.reg.R15)) :
    ∀ i r, msg.msg_register i = ok r → R0 (regA t r) := by
  intro i r hr
  unfold msg.msg_register at hr
  by_cases e0 : i = 0#u64
  · rw [if_pos e0] at hr; cases ok_inj_ff hr; exact h10
  rw [if_neg e0] at hr
  by_cases e1 : i = 1#u64
  · rw [if_pos e1] at hr; cases ok_inj_ff hr; exact h8
  rw [if_neg e1] at hr
  by_cases e2 : i = 2#u64
  · rw [if_pos e2] at hr; cases ok_inj_ff hr; exact h9
  rw [if_neg e2] at hr; cases ok_inj_ff hr; exact h15

set_option maxHeartbeats 16000000 in
/-- (slhuf gen 12) **`Once` of the Copy / Mint decode onward** (`invCMRest`) at the post-check state `x`, from the
empty touched set: every kernel read on `guard st R0 _` (`R0` inside `Rd`, no user word), the buffer words of
message words 4 / 5 read once (`once_copied`), an error reply's buffer word read once (`once_leafErr`); the
reply and `finish` after the decode by `htail` (they run alike on `guard st R0 ⊤`). Inputs: the arm's facts at `x`
(the target and source lookups on `st` and on the guard, the first extra cap, the source's frame cap), the reads
`R0` of the current thread, its argument registers, the IPC-buffer cap, the slots; `set_thread_state RESTART` /
`insert_with_cap` on `guard st R0 ⊤`. -/
theorem invCMRest_once {R0 : U64 → Prop} (hR0 : ∀ q, R0 q → Rd q ∧ ¬ User q)
    {t : U64} {info : msginfo.MessageInfo} {p : localinv.Plan} {buf length : U64}
    {cp cr cg cgb dest s1 rp rr rg rgb src fp rt asid va sl : U64} {sz : capability.FrameSize} {d mp : Bool}
    (hl : info.label = fl4_abi.label.CNodeCopy ∨ info.label = fl4_abi.label.CNodeMint)
    {x : S} {a : A}
    (hct : R0 (L.nodeAt x (L.cpu x) layout.node.CUR_THREAD)) (hcur : L.curW x = t)
    (h10 : R0 (regA t layout.reg.R10)) (h8 : R0 (regA t layout.reg.R8))
    (h9 : R0 (regA t layout.reg.R9)) (h15 : R0 (regA t layout.reg.R15))
    (hlk : cspace.lookup_target_slot st x (.CNode cp cr cg cgb) (L.mem x (regA t layout.reg.R10))
      (L.mem x (regA t layout.reg.R8)) = ok (.Ok dest))
    (hlkG : cspace.lookup_target_slot (PathObl.guard st R0 (fun _ => False)) x (.CNode cp cr cg cgb)
      (L.mem x (regA t layout.reg.R10)) (L.mem x (regA t layout.reg.R8)) = ok (.Ok dest))
    (hs1 : Aeneas.Std.Array.index_usize p.extra 0#usize = ok s1) (hs10 : s1 ≠ 0#u64)
    (hrc : obj.Slot.cap st s1 x = ok (.CNode rp rr rg rgb)) (hrc0 : R0 s1)
    (hrc8 : R0 (core.num.U64.wrapping_add s1 8#u64))
    (hd0 : R0 dest) (hd8 : R0 (core.num.U64.wrapping_add dest 8#u64))
    (hls : cspace.lookup_source_slot st x (.CNode rp rr rg rgb) (L.mem x (regA t layout.reg.R9))
      (L.mem x (regA t layout.reg.R15)) = ok (.Ok src))
    (hlsG : cspace.lookup_source_slot (PathObl.guard st R0 (fun _ => False)) x (.CNode rp rr rg rgb)
      (L.mem x (regA t layout.reg.R9)) (L.mem x (regA t layout.reg.R15)) = ok (.Ok src))
    (hsc : obj.Slot.cap st src x = ok (.Frame fp sz rt d mp false asid va)) (hsc0 : R0 src)
    (hsc8 : R0 (core.num.U64.wrapping_add src 8#u64))
    (hsts : ∀ x3, sched.set_thread_state st x t sched.TS_RESTART = ok x3 →
      sched.set_thread_state (PathObl.guard st R0 (fun _ => True)) x t sched.TS_RESTART = ok x3)
    (hins : ∀ x3 nc x4, sched.set_thread_state st x t sched.TS_RESTART = ok x3 →
      cdt.insert_with_cap st x3 nc (.Frame fp sz rt d mp false asid va) src dest = ok x4 →
      cdt.insert_with_cap (PathObl.guard st R0 (fun _ => True)) x3 nc (.Frame fp sz rt d mp false asid va) src
        dest = ok x4)
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok sl) (hI : R0 (core.num.U64.wrapping_add t 3512#u64))
    (hb0 : R0 sl) (hb8 : R0 (core.num.U64.wrapping_add sl 8#u64)) (hB : ¬ User (regA t layout.reg.BADGE))
    (htail : ∀ r x' a2 z, decCNG st ar x a info.label length p.slot (.CNode cp cr cg cgb) true true true false buf
        p.extra = ok (r, x', a2) → invPostG st x' a2 t r = ok z →
      (r = .Ok () → invPostG (PathObl.guard st R0 (fun _ => True)) x' a2 t r = ok z) ∧
      ∀ y, syscall.finish st ar z.1 z.2.1 = ok y →
        syscall.finish (PathObl.guard st R0 (fun _ => True)) ar z.1 z.2.1 = ok y)
    {r' : Bool × S × A} (h : interp st ar (invCMRest t info p buf length (.CNode cp cr cg cgb)) x a = ok r')
    (Wd : Set U64) :
    Once st ar Rd User Wd ∅ (invCMRest t info p buf length (.CNode cp cr cg cgb)) x a := by
  have hreg := msgreg_R h10 h8 h9 h15
  have hW0 : ∀ q, (fun _ => False) q → ¬ User q := fun _ h => h.elim
  rw [invCMRest_eq] at h ⊢
  have h' := h
  rw [interp_sbind] at h'
  obtain ⟨r0, hD, -⟩ := bind_eq_ok' h'
  have hD' := hD
  rw [R.decCNG_eq] at hD'
  obtain ⟨r0', eD, hr0⟩ := bind_shape hD'
  have eD0 : decCNG st ar x a info.label length p.slot (.CNode cp cr cg cgb) true true true false buf p.extra =
      ok r0 := by rw [← prod3_eq hr0]; exact eD
  have hd : interp st ar ((R.decCNG info.label length p.slot (.CNode cp cr cg cgb) true true true false buf
      p.extra).sbind SProg.ret) x a = ok r0 := by rw [SProg.sbind_ret]; exact hD
  clear hD hD' h' eD hr0
  -- the leaves
  have leafE : ∀ e, (∀ (m : machine.Store S) y b, syscall.error_mrs m y t b e = ok (0#u64, y)) →
      interp st ar (cmK1 t (.Err (.Sys e))) x a = ok r' → r0 = (.Err (.Sys e), x, a) →
      ∀ Wd', Once st ar Rd User Wd' ∅ (cmK1 t (.Err (.Sys e))) x a := by
    intro e he hk e0 Wd'
    rw [e0] at eD0
    exact once_leafErr hR0 he hsl hI hb0 hb8 hB hk (fun z ez y ey => (htail _ _ _ _ eD0 ez).2 y ey) Wd'
  have leafO : ∀ x4, interp st ar (cmK1 t (.Ok ())) x4 a = ok r' → r0 = (.Ok (), x4, a) →
      ∀ Wd' T', Once st ar Rd User Wd' T' (cmK1 t (.Ok ())) x4 a := by
    intro x4 hk e0 Wd' T'
    rw [e0] at eD0
    exact once_leafOk hR0 hk (fun z ez => ⟨(htail _ _ _ _ eD0 ez).1 rfl, (htail _ _ _ _ eD0 ez).2⟩) Wd' T'
  unfold R.decCNG at h hd ⊢
  try simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h hd ⊢
  -- the current thread (decCNG)
  refine once_gstep hR0 hW0 (R.sched.cur_thread_nz) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st R0 (fun _ => False)) x hct]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t0, -, rfl⟩ := bind_shape h1
  dsimp only at h hd ⊢
  try simp only [Bool.false_eq_true, ↓reduceIte, SProg.sbind_assoc, SProg.sbind] at h hd ⊢
  -- `cnode.decode`
  unfold R.cnode.decode at h hd ⊢
  rw [if_neg (cm_l1 hl), if_neg (cm_l2 hl)] at h hd ⊢
  by_cases hl2 : length < 2#u64
  · rw [if_pos hl2] at h hd ⊢
    simp only [error.truncated, SProg.liftR_ok, SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind] at h hd ⊢
    rw [interp_ret'] at hd
    exact leafE _ (fun m y b => error_mrs_trunc m y t b) h (ok_inj_ff hd).symm Wd1
  rw [if_neg hl2] at h hd ⊢
  try simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h hd ⊢
  refine once_gstep hR0 hW0 (R.sched.cur_thread_nz) h (fun r h1 => ?_) (fun r h1 hk Wd2 hW2 => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st R0 (fun _ => False)) x hct]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.sched.cur_thread_eq, cur_thread_ok, hcur] at h1
  obtain ⟨t1, et1, rfl⟩ := bind_shape h1
  cases ok_inj_ff et1
  dsimp only at h hd ⊢
  -- the target's index and depth (registers)
  refine once_gstep hR0 hW0 (R.msg.syscall_arg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd3 hW3 => ?_)
  · rw [R.msg.syscall_arg_eq] at h1 ⊢
    rw [msg.syscall_arg.guard_lt (gS := PathObl.guard st R0 (fun _ => False)) x _ buf 0#u64
      (by rw [n_msg_regs]; decide) (hreg 0#u64)]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.msg.syscall_arg_eq, sarg0_reg, reg_ok] at h1
  obtain ⟨i0, ei0, rfl⟩ := bind_shape h1
  cases ok_inj_ff ei0
  dsimp only at h hd ⊢
  refine once_gstep hR0 hW0 (R.msg.syscall_arg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd4 hW4 => ?_)
  · rw [R.msg.syscall_arg_eq] at h1 ⊢
    rw [msg.syscall_arg.guard_lt (gS := PathObl.guard st R0 (fun _ => False)) x _ buf 1#u64
      (by rw [n_msg_regs]; decide) (hreg 1#u64)]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.msg.syscall_arg_eq, sarg1_reg, reg_ok] at h1
  obtain ⟨i1, ei1, rfl⟩ := bind_shape h1
  cases ok_inj_ff ei1
  dsimp only at h hd ⊢
  -- the target lookup
  refine once_gstep hR0 hW0 (R.cspace.lookup_target_slot_nz _ _ _) h (fun r h1 => ?_)
    (fun r h1 hk Wd5 hW5 => ?_)
  · rw [R.cspace.lookup_target_slot_eq] at h1 ⊢
    rw [hlk] at h1
    rw [hlkG]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.cspace.lookup_target_slot_eq, hlk] at h1
  obtain ⟨rl, erl, rfl⟩ := bind_shape h1
  cases ok_inj_ff erl
  dsimp only at h hd ⊢
  simp only [core.result.Result.Insts.CoreOpsTry.branch, SProg.liftR_ok, SProg.sbind, SProg.sbind_assoc] at h hd ⊢
  rw [if_pos (cm_l3 hl), if_pos (cm_l4 hl)] at h hd ⊢
  try simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h hd ⊢
  -- `decode_copy`
  unfold R.cnode.decode_copy at h hd ⊢
  by_cases hl4 : length < 4#u64
  · rw [if_pos hl4] at h hd ⊢
    simp only [error.truncated, SProg.liftR_ok, SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind] at h hd ⊢
    rw [interp_ret'] at hd
    exact leafE _ (fun m y b => error_mrs_trunc m y t b) h (ok_inj_ff hd).symm Wd5
  rw [if_neg hl4] at h hd ⊢
  try simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h hd ⊢
  have hn1 : obj.Slot.is_null s1 = ok false := by
    unfold obj.Slot.is_null; simp [hs10]
  rw [hs1] at h hd ⊢
  simp only [SProg.liftR_ok, SProg.sbind] at h hd ⊢
  rw [hn1] at h hd ⊢
  simp only [SProg.liftR_ok, SProg.sbind, Bool.false_eq_true, ↓reduceIte, SProg.sbind_assoc] at h hd ⊢
  refine once_gstep hR0 hW0 (R.sched.cur_thread_nz) h (fun r h1 => ?_) (fun r h1 hk Wd6 hW6 => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st R0 (fun _ => False)) x hct]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.sched.cur_thread_eq, cur_thread_ok, hcur] at h1
  obtain ⟨t2, et2, rfl⟩ := bind_shape h1
  cases ok_inj_ff et2
  dsimp only at h hd ⊢
  -- the source's index and depth (registers)
  refine once_gstep hR0 hW0 (R.msg.syscall_arg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd7 hW7 => ?_)
  · rw [R.msg.syscall_arg_eq] at h1 ⊢
    rw [msg.syscall_arg.guard_lt (gS := PathObl.guard st R0 (fun _ => False)) x _ buf 2#u64
      (by rw [n_msg_regs]; decide) (hreg 2#u64)]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.msg.syscall_arg_eq, sarg2_reg, reg_ok] at h1
  obtain ⟨i2, ei2, rfl⟩ := bind_shape h1
  cases ok_inj_ff ei2
  dsimp only at h hd ⊢
  refine once_gstep hR0 hW0 (R.msg.syscall_arg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd8 hW8 => ?_)
  · rw [R.msg.syscall_arg_eq] at h1 ⊢
    rw [msg.syscall_arg.guard_lt (gS := PathObl.guard st R0 (fun _ => False)) x _ buf 3#u64
      (by rw [n_msg_regs]; decide) (hreg 3#u64)]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.msg.syscall_arg_eq, sarg3_reg, reg_ok] at h1
  obtain ⟨i3, ei3, rfl⟩ := bind_shape h1
  cases ok_inj_ff ei3
  dsimp only at h hd ⊢
  -- the first extra cap's cap (the source root)
  refine once_gstep hR0 hW0 (R.obj.Slot.cap_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd9 hW9 => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := PathObl.guard st R0 (fun _ => False)) s1 x hrc0 hrc8]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.obj.Slot.cap_eq, hrc] at h1
  obtain ⟨c0, ec0, rfl⟩ := bind_shape h1
  cases ok_inj_ff ec0
  dsimp only at h hd ⊢
  -- `ensure_empty_slot`
  refine once_gstep hR0 hW0 (R.cdt.ensure_empty_slot_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd10 hW10 => ?_)
  · rw [R.cdt.ensure_empty_slot_eq] at h1 ⊢
    rw [cdt.ensure_empty_slot.guard (gS := PathObl.guard st R0 (fun _ => False)) x dest hd0 hd8]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.cdt.ensure_empty_slot_eq] at h1
  obtain ⟨re, ere, rfl⟩ := bind_shape h1
  dsimp only at h hd ⊢
  have hre : re = .Ok () ∨ re = .Err (.Sys .DeleteFirst) := by
    unfold cdt.ensure_empty_slot at ere
    obtain ⟨c, -, ere⟩ := bind_eq_ok ere
    obtain ⟨b, -, ere⟩ := bind_eq_ok ere
    cases b
    · exact Or.inr (ok_inj_ff ere).symm
    · exact Or.inl (ok_inj_ff ere).symm
  rcases hre with rfl | rfl
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, SProg.liftR_ok, SProg.sbind,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, fromSame_eq,
      SProg.sbind_assoc] at h hd ⊢
    rw [interp_ret'] at hd
    exact leafE _ (fun m y b => error_mrs_df m y t b) h (ok_inj_ff hd).symm Wd10
  simp only [core.result.Result.Insts.CoreOpsTry.branch, SProg.liftR_ok, SProg.sbind, SProg.sbind_assoc] at h hd ⊢
  -- the source lookup
  refine once_gstep hR0 hW0 (R.cspace.lookup_source_slot_nz _ _ _) h (fun r h1 => ?_)
    (fun r h1 hk Wd11 hW11 => ?_)
  · rw [R.cspace.lookup_source_slot_eq] at h1 ⊢
    rw [hls] at h1
    rw [hlsG]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.cspace.lookup_source_slot_eq, hls] at h1
  obtain ⟨rs, ers, rfl⟩ := bind_shape h1
  cases ok_inj_ff ers
  dsimp only at h hd ⊢
  simp only [core.result.Result.Insts.CoreOpsTry.branch, SProg.liftR_ok, SProg.sbind, SProg.sbind_assoc] at h hd ⊢
  -- the source cap
  refine once_gstep hR0 hW0 (R.obj.Slot.cap_nz _) h (fun r h1 => ?_) (fun r h1 hk Wd12 hW12 => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := PathObl.guard st R0 (fun _ => False)) src x hsc0 hsc8]
    exact h1
  replace hd := hd_step hd h1
  replace h := hk
  rw [R.obj.Slot.cap_eq, hsc] at h1
  obtain ⟨c1, ec1, rfl⟩ := bind_shape h1
  cases ok_inj_ff ec1
  dsimp only at h hd ⊢
  have hfn : capability.Cap.is_null (.Frame fp sz rt d mp false asid va) = ok false := rfl
  rw [hfn] at h hd ⊢
  simp only [SProg.liftR_ok, SProg.sbind, Bool.false_eq_true, ↓reduceIte, SProg.sbind_assoc] at h hd ⊢
  -- `copied_cap`
  refine once_copied hR0 hW0 hl hct h hd (fun hq => by simp at hq) (fun hq => by simp at hq)
    (fun hk hd' Wd' _ => ?_) (fun i hk hd' Wd' _ => ?_)
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, SProg.liftR_ok, SProg.sbind,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, bind_tc_ok, fromSame_eq,
      SProg.sbind_assoc] at hk hd' ⊢
    rw [interp_ret'] at hd'
    exact leafE _ (fun m y b => error_mrs_trunc m y t b) hk (ok_inj_ff hd').symm Wd'
  simp only [core.result.Result.Insts.CoreOpsTry.branch, SProg.liftR_ok, SProg.sbind, SProg.sbind_assoc] at hk hd' ⊢
  have hfn2 : capability.Cap.is_null (.Frame fp sz i d false false 0#u64 0#u64) = ok false := rfl
  rw [hfn2] at hk hd' ⊢
  simp only [SProg.liftR_ok, SProg.sbind, Bool.false_eq_true, ↓reduceIte, SProg.sbind_assoc] at hk hd' ⊢
  -- `set_thread_state RESTART`, `insert_with_cap`: on `guard st R0 ⊤`
  refine once_gstepW (W0 := fun _ => True) hR0 (R.sched.set_thread_state_nz _ _) hk (fun r h1 => ?_)
    (fun r h1 hk2 Wd13 T13 => ?_)
  · rw [R.sched.set_thread_state_eq] at h1 ⊢
    obtain ⟨x3, ex3, rfl⟩ := bind_shape h1
    rw [hsts x3 ex3]
    exact bok.mpr ⟨_, rfl, rfl⟩
  replace hd' := hd_step hd' h1
  rw [R.sched.set_thread_state_eq] at h1
  obtain ⟨x3, ex3, rfl⟩ := bind_shape h1
  dsimp only at hk2 hd' ⊢
  try simp only [Bool.false_eq_true, ↓reduceIte, SProg.sbind_assoc, SProg.sbind] at hk2 hd' ⊢
  refine once_gstepW (W0 := fun _ => True) hR0 (R.cdt.insert_with_cap_nz _ _ _ _) hk2 (fun r h1 => ?_)
    (fun r h1 hk3 Wd14 T14 => ?_)
  · rw [R.cdt.insert_with_cap_eq] at h1 ⊢
    obtain ⟨x4, ex4, rfl⟩ := bind_shape h1
    rw [hins x3 _ x4 ex3 ex4]
    exact bok.mpr ⟨_, rfl, rfl⟩
  replace hd' := hd_step hd' h1
  rw [R.cdt.insert_with_cap_eq] at h1
  obtain ⟨x4, ex4, rfl⟩ := bind_shape h1
  dsimp only at hk3 hd' ⊢
  try simp only [SProg.sbind] at hk3 hd' ⊢
  rw [interp_ret'] at hd'
  exact leafO x4 hk3 (ok_inj_ff hd').symm Wd14 T14

end dec

/-! ## `InvCMDecOnceW` from the arm's entry facts -/

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- [W] (slhuf gen 12) **The kernel tail after the Copy / Mint decode on the read guard**: at an accepted entry
`s`, after the prefix, the checks, the IPC buffer lookup and the invoked slot's cap read, for the decode's result
`(r, x, a2)` and the reply's `z` (`invPostG`): an `Ok` reply, and `finish` after any reply, run alike on
`guard st (IoRS s) ⊤` (they read only `IoRS s` words). Dischargeable from the acc / fin lines' generic-store
results (`invRep` on any store reading `IoRS s`; `FinOK` at that store with `syscall.finish.guard_resume`). -/
def InvCMTailW {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : OwnMap.KLayout)
    (Locks : S → U64 → Prop) (P : S → Prop) : Prop :=
  ∀ s (a : A) info nx s1 s2 a1 buf length cap r x a2 z, P s →
    (∃ s' a', syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) →
    msg.msg_info st s (L.curW s) = ok info → InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
    msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf → obj.Slot.cap st p.slot s2 = ok cap →
    decCNG st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok (r, x, a2) →
    invPostG st x a2 (L.curW s) r = ok z →
    (r = .Ok () → invPostG (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x a2 (L.curW s) r = ok z) ∧
    ∀ y, syscall.finish st ar z.1 z.2.1 = ok y →
      syscall.finish (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) ar z.1 z.2.1 = ok y

set_option maxHeartbeats 8000000 in
/-- (slhuf gen 12) **`InvCMDecOnceW` discharged** up to the kernel tail `InvCMTailW` [W]: at a `P` entry with
`IoPre`, the Copy / Mint label (`InvCMArm`), the arm's entry facts (`CMEnt`) and the plan's slot a capability slot,
the walk `invCMRest_once` at the post-check state (the prefix keeps the slot words and argument registers, so
the entry's lookups and caps hold there). -/
theorem invCMDecOnceW_of {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64}
    {p : localinv.Plan} {K : OwnMap.KLayout} {Locks : S → U64 → Prop} {Cs Ω Sg Ac : Set U64} {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits Ac s)
    (harm : ∀ s, P s → InvCMArm st s) (hE : ∀ s, P s → CMEnt st K Cs Locks p s)
    (hsl : ∀ s, P s → p.slot ∈ K.slots) (htl : InvCMTailW st ar number p K Locks P) :
    InvCMDecOnceW st ar number p K Locks P := by
  intro s a info nx s1 s2 a1 buf length cap r' hP hacc emi C ebuf hcap hR Wd
  have PE := hPE s hP
  obtain ⟨sA, aA, h0⟩ := hacc
  have hl := harm s hP (L.curW s) info (cur_thread_ok s) emi
  obtain ⟨cp, cr, cg, cgb, dest, s1', rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, Cw, hcs, hs1, hs10,
    hlk, hrc, hls, hsc, -, -, hC, hCr, hcl, hWk, hs1K, -, hd, hdO, hLd, hsK, hsO, hLs, hnx⟩ := hE s hP
  have C' := C
  obtain ⟨enx, es1, eu, eac, ey, ehere, -⟩ := C'
  have Ent := PE.ent (Locks := Locks) (PE.ioWr (Locks := Locks))
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL : Slot8 K := fun q hq => PE.lay.slot8 q hq
  have w0 := prefix_writes ar hA PE.tp PE.np PE.cT es1 eu
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact PE.slot_keep w0 hq hbq hb
  have hcap' : cap = .CNode cp cr cg cgb := by
    rw [cap_agree hL (hsl s hP) ag, hcs] at hcap; exact (ok_inj_ff hcap).symm
  subst hcap'
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned PE.tA h1 h2) (preW_tcb PE.tA PE.np PE.cT h1 h3)
  have r10 : L.mem s2 (regA (L.curW s) layout.reg.R10) = L.mem s (regA (L.curW s) layout.reg.R10) := by
    have e := reg_keepK (st := st) PE.tA (r := layout.reg.R10) (by simp [layout.reg.R10])
      (by simp [layout.reg.R10]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r8 : L.mem s2 (regA (L.curW s) layout.reg.R8) = L.mem s (regA (L.curW s) layout.reg.R8) := by
    have e := reg_keepK (st := st) PE.tA (r := layout.reg.R8) (by simp [layout.reg.R8])
      (by simp [layout.reg.R8]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r9 : L.mem s2 (regA (L.curW s) layout.reg.R9) = L.mem s (regA (L.curW s) layout.reg.R9) := by
    have e := reg_keepK (st := st) PE.tA (r := layout.reg.R9) (by simp [layout.reg.R9])
      (by simp [layout.reg.R9]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r15 : L.mem s2 (regA (L.curW s) layout.reg.R15) = L.mem s (regA (L.curW s) layout.reg.R15) := by
    have e := reg_keepK (st := st) PE.tA (r := layout.reg.R15) (by simp [layout.reg.R15])
      (by simp [layout.reg.R15]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have slotK : ∀ p r, Cw p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s2 = obj.Slot.cap st (cnSlot p (x &&& m)) s :=
    fun p r hp m hm x => cap_agree hL (hWk p r m x hp hm).1 ag
  have hRc2 : WalkRc (st := st) (IoRS (st := st) K Locks s) s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    exact PE.slot (hWk p r m y hp hm).1 (Or.inr (cap_not_nof hc (Or.inl ⟨_, _, _, _, rfl⟩)))
  have hcl2 : WalkCl (st := st) s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    exact hcl p r m y p' r' gs' g' hp hm hc
  -- the two lookups at `s2`
  have hlk2 : cspace.lookup_target_slot st s2 (.CNode cp cr cg cgb) (L.mem s2 (regA (L.curW s) layout.reg.R10))
      (L.mem s2 (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) := by
    rw [r10, r8]
    unfold cspace.lookup_target_slot cspace.lookup_slot_for_cnode_op at hlk ⊢
    simp only [bind_ok, ↓reduceIte] at hlk ⊢
    by_cases d1 : L.mem s (regA (L.curW s) layout.reg.R8) < 1#u64
    · rw [if_pos d1] at hlk; simp at hlk
    rw [if_neg d1] at hlk ⊢
    by_cases d2 : L.mem s (regA (L.curW s) layout.reg.R8) > cspace.WORD_BITS
    · rw [if_pos d2] at hlk; simp at hlk
    rw [if_neg d2] at hlk ⊢
    unfold cspace.resolve_address_bits at hlk ⊢
    obtain ⟨res, eres, hl⟩ := bind_eq_ok hlk
    have eres' := rab_loop_congr2 st Cw slotK hcl 66 _ _ 65#u64 res (by simp)
      (fun p1 r1 gs1 g1 e => by cases e; exact hC) eres
    rw [eres']; simp only [bind_ok]; exact hl
  have hls2 : cspace.lookup_source_slot st s2 (.CNode rp rr rg rgb) (L.mem s2 (regA (L.curW s) layout.reg.R9))
      (L.mem s2 (regA (L.curW s) layout.reg.R15)) = ok (.Ok src) := by
    rw [r9, r15]
    unfold cspace.lookup_source_slot cspace.lookup_slot_for_cnode_op at hls ⊢
    simp only [bind_ok, ↓reduceIte] at hls ⊢
    by_cases d1 : L.mem s (regA (L.curW s) layout.reg.R15) < 1#u64
    · rw [if_pos d1] at hls; simp at hls
    rw [if_neg d1] at hls ⊢
    by_cases d2 : L.mem s (regA (L.curW s) layout.reg.R15) > cspace.WORD_BITS
    · rw [if_pos d2] at hls; simp at hls
    rw [if_neg d2] at hls ⊢
    unfold cspace.resolve_address_bits at hls ⊢
    obtain ⟨res, eres, hl⟩ := bind_eq_ok hls
    have eres' := rab_loop_congr2 st Cw slotK hcl 66 _ _ 65#u64 res (by simp)
      (fun p1 r1 gs1 g1 e => by cases e; exact hCr) eres
    rw [eres']; simp only [bind_ok]; exact hl
  -- the words
  have dR : ∀ o : U64, o.val < 32 → o.val % 8 = 0 → IoRS (st := st) K Locks s (core.num.U64.wrapping_add dest o) :=
    fun o ho h8 => (PE.lockSlot hd hLd ho h8).1
  have sR : ∀ o : U64, o.val < 32 → o.val % 8 = 0 → IoRS (st := st) K Locks s (core.num.U64.wrapping_add src o) :=
    fun o ho h8 => (PE.lockSlot hsK hLs ho h8).1
  have e0d : core.num.U64.wrapping_add dest 0#u64 = dest := wadd_zero (hL dest hd).2
  have e0s : core.num.U64.wrapping_add src 0#u64 = src := wadd_zero (hL src hsK).2
  have rd0 : IoRS (st := st) K Locks s dest := by have := dR 0#u64 (by simp) (by simp); rwa [e0d] at this
  have rs0 : IoRS (st := st) K Locks s src := by have := sR 0#u64 (by simp) (by simp); rwa [e0s] at this
  have hs1R := PE.slot (Locks := Locks) hs1K (Or.inr (cap_not_nof hrc (Or.inl ⟨_, _, _, _, rfl⟩)))
  have hlkG := cspace.lookup_target_slot.guardM
    (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => False)) Cw hRc2 hcl2 hC
    ⟨rd0, dR 8#u64 (by simp) (by simp)⟩ hlk2
  have hlsG := cspace.lookup_source_slot.guardM
    (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => False)) Cw hRc2 hcl2 hCr
    ⟨rs0, sR 8#u64 (by simp) (by simp)⟩ hls2
  have hrc2 : obj.Slot.cap st s1' s2 = ok (.CNode rp rr rg rgb) := by rw [cap_agree hL hs1K ag]; exact hrc
  have hsc2 : obj.Slot.cap st src s2 = ok (.Frame fp sz rt d mp false asid va) := by
    rw [cap_agree hL hsK ag]; exact hsc
  -- the node and the caller's words, `set_thread_state RESTART`
  have hctR : IoRS (st := st) K Locks s (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact (PE.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  have hsaR : IoRS (st := st) K Locks s (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact (PE.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])).1
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact Ent.run
  have hK0 := SchedOK.of_sw I.F (by rw [hct]; exact Hf.sc) (by rw [hct]; exact Hf.nr)
  rw [hct] at hK0
  have hK : SchedOK (L := L) s2 (L.curW s) := hK0
  have rst := PE.stw (Locks := Locks)
  have rsc : IoRS (st := st) K Locks s (scA (L.curW s)) :=
    PE.gate (off := 3464#u64) PE.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have riq : IoRS (st := st) K Locks s (inqA (L.curW s)) :=
    (PE.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  have hmxR : IoRS (st := st) K Locks s (maxA (L.cscW s)) := by
    have hmx := maxA_facts PE.bxi.2.2.1.1 PE.cscS
    exact PE.cscacc.rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩
  have hsc2' : L.mem s2 (scA (L.curW s)) = L.cscW s := by rw [← hct]; exact I.F.i
  have hmx2 : IoRS (st := st) K Locks s
      (maxA (L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)))) := by
    have kw := (KeepA.refl ha2 hrun).wr hK (b := stA (L.curW s)) (v := sched.TS_RESTART) (Or.inr rfl)
      (fun _ => Or.inl rfl)
    have e : L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      kw.mem (field_aligned PE.tA (by simp) (by simp)) (iotw_field PE.tA (by simp) (by simp))
    rw [e, hsc2']
    exact hmxR
  have hsts : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 →
      sched.set_thread_state (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) s2 (L.curW s)
        sched.TS_RESTART = ok x3 := fun x3 e => by
    rw [sched.set_thread_state.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) s2
      (L.curW s) _ ⟨hctR, hsaR, trivial⟩ trivial rst.1 rsc hmx2 riq]
    exact e
  have hins : ∀ x3 nc x4, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 →
      cdt.insert_with_cap st x3 nc (.Frame fp sz rt d mp false asid va) src dest = ok x4 →
      cdt.insert_with_cap (PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x3 nc
        (.Frame fp sz rt d mp false asid va) src dest = ok x4 := fun x3 nc x4 _ e => by
    rw [cdt.insert_with_cap.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) x3 nc _ src
      dest (sR layout.cte.NEXT (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])) trivial trivial trivial
      trivial trivial trivial (dR layout.cte.NEXT (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])) trivial
      (fun _ _ _ => trivial)]
    exact e
  -- the IPC buffer cap
  have M := invCM_hmid (Locks := Locks) hA PE h0 info nx s1 s2 a1 emi enx es1 eu
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
  have hR0 : ∀ q, IoRS (st := st) K Locks s q → InvCMRS (st := st) K Locks s q ∧ ¬ (q ∈ K.user) :=
    fun q hq => ⟨ioRS_cm hq, hq.2.1⟩
  exact invCMRest_once (Rd := InvCMRS (st := st) K Locks s) (User := (· ∈ K.user)) hR0 hl hctR hct
    (PE.reg (Locks := Locks) (by simp [layout.reg.R10])).1 (PE.reg (Locks := Locks) (by simp [layout.reg.R8])).1
    (PE.reg (Locks := Locks) (by simp [layout.reg.R9])).1 (PE.reg (Locks := Locks) (by simp [layout.reg.R15])).1
    hlk2 hlkG hs1 hs10 hrc2 hs1R.1 hs1R.2 rd0
    (dR 8#u64 (by simp) (by simp)) hls2 hlsG hsc2 rs0
    (sR 8#u64 (by simp) (by simp)) hsts hins hbsl M.ib (M.bs _ hbsl).1 (M.bs _ hbsl).2
    (PE.reg (Locks := Locks) (by simp [layout.reg.BADGE])).1.2.1
    (fun r x' a2 z eD ez => htl s a info nx s1 s2 a1 buf length _ r x' a2 z hP ⟨sA, aA, h0⟩ emi C ebuf hcap eD ez)
    hR Wd

end ent

end Fl4Proofs.P2.PathObl

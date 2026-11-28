/-
P3 (DESIGN.md §9): **FL4's half of `DomFrame` for the IRQ and IO-port caps**
(`DecDomHyp`, AllDom).

* `ioport_wfr`: `ioport::decode` writes only the caller's state, registers and
  IPC buffer (`WFr`, TcbReplyX: the restart, the reply of a port read).
* `decDomHyp_irqHandler`, `decDomHyp_irqControl`, `decDomHyp_ioportControl`,
  `decDomHyp_ioport`: the caps' `DecDomHyp`, from `irq_handler_dk4` (IrqDom),
  the refinements' posts (`CPost`, `IoCPost`: their `DK4` conjunct) and
  `ioport_wfr`.
-/
import Fl4Proofs.P3.AllDom
import Fl4Proofs.P3.IrqDom
import Fl4Proofs.P3.TcbDataX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- `DecDomHyp` is a `DK4` post. -/
theorem decDomHyp_of_dk4 {s : S} {ar : A} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool}
    {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (h : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
      DK4 (L := L) s res.2.1 ⦄) :
    DecDomHyp (L := L) arI s ar lbl length slot c blk call don fp buf extra := h

/-- A `WFr` step is a `DK4` step. -/
theorem DK4.of_wfr {th : TypedHeap} {s s' : S} (h : WFr (L := L) th s s') : DK4 (L := L) s s' := by
  refine ⟨h.2.1, fun o ho => ?_⟩
  obtain ⟨h32, hi, h24⟩ := h.2.2.2
  simp only [domOffs0, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h24
  · exact h32
  · exact (hi 0#u64 (by decide)).1
  · exact (hi 0#u64 (by decide)).2
  · exact (hi 1#u64 (by decide)).1
  · exact (hi 1#u64 (by decide)).2

/-- **`ioport::decode` writes only the caller's words** (`WFr`). -/
theorem ioport_wfr (th : TypedHeap) (hP : Placed th) (hA : P0.ArchTotal arI) (s : S) (ar : A) (lbl length : U64)
    (first last x : U64) (call : Bool) (buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hC : TCtx (L := L) th s ct) (hB : CallerBufHyp (L := L) th s ct) :
    ioport.decode st arI s ar lbl length (.IoPort first last x) call buf ⦃ res => WFr (L := L) th s res.2.1 ⦄ := by
  unfold ioport.decode
  simp only [hct, bind_ok]
  obtain ⟨size, hsz, -⟩ := spec_exists (P0.ioport.port_size.p0 lbl)
  rw [hsz]; simp only [bind_ok]
  split
  · simp only [error.illegal, bind_ok, WP.spec_ok]; exact WFr.refl _ _
  obtain ⟨isin, hin, -⟩ := spec_exists (P0.ioport.is_port_in.p0 lbl)
  rw [hin]; simp only [bind_ok]
  split
  · split
    · simp only [error.truncated, bind_ok, WP.spec_ok]; exact WFr.refl _ _
    obtain ⟨i0, hi0, -⟩ := spec_exists (P0.msg.syscall_arg.p0 st s ct buf 0#u64 L.total)
    rw [hi0]; simp only [bind_ok, lift]
    obtain ⟨r, hr, -⟩ := spec_exists (P0.ioport.allowed.p0 first last (i0 &&& 65535#u64) size)
    rw [hr]; simp only [bind_ok]
    cases r with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      exact WFr.refl _ _
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_bind (sts_t hP hC _) ?_
      rintro s1 ⟨hW1, -⟩
      obtain ⟨⟨v, a1⟩, hpi, -⟩ := spec_exists (hA.port_in ar (i0 &&& 65535#u64) size)
      rw [hpi]; simp only [bind_ok]
      have hC1 := hC.wfr hW1
      refine WP.spec_bind (?_ : (if call = true then _ else ok s1) ⦃ s2 => WFr (L := L) th s s2 ⦄) ?_
      · split
        · obtain ⟨bf, hl, -⟩ := spec_exists (P0.msg.lookup_ipc_buffer.p0 st s1 true ct L.total)
          rw [hl]; simp only [bind_ok]
          refine WP.spec_bind (set_reg_wfr hP hC1.ksb hC.tcb (i := layout.reg.BADGE)
            (by unfold layout.reg.BADGE layout.reg.RDI; decide) 0#u64) ?_
          intro s3 hW3
          have hC3 := hC1.wfr hW3
          refine WP.spec_bind (set_mr_t hP hC3 (buf := bf) (i := 0#u64) (fun h => absurd h (by decide))
            (by decide) v) ?_
          rintro ⟨n, s4⟩ ⟨hn, hW4⟩
          simp only [uncurry_apply_pair]
          unfold msginfo.MessageInfo.new
          simp only [bind_ok]
          have hC4 := hC3.wfr hW4
          exact WP.spec_mono (set_msg_info_wfr hP hC4.ksb hC.tcb 0#u64 n hn) fun s5 hW5 =>
            hW1.trans (hW3.trans (hW4.trans hW5))
        · exact (WP.spec_ok _).2 hW1
      intro s2 hW2
      refine WP.spec_bind (sts_t hP (hC.wfr hW2) _) ?_
      rintro s3 ⟨hW3, -⟩
      exact (WP.spec_ok _).2 (hW2.trans hW3)
  · split
    · simp only [error.truncated, bind_ok, WP.spec_ok]; exact WFr.refl _ _
    obtain ⟨i0, hi0, -⟩ := spec_exists (P0.msg.syscall_arg.p0 st s ct buf 0#u64 L.total)
    rw [hi0]; simp only [bind_ok, lift]
    obtain ⟨raw, hraw, -⟩ := spec_exists (P0.msg.syscall_arg.p0 st s ct buf 1#u64 L.total)
    rw [hraw]; simp only [bind_ok]
    obtain ⟨r, hr, -⟩ := spec_exists (P0.ioport.allowed.p0 first last (i0 &&& 65535#u64) size)
    rw [hr]; simp only [bind_ok]
    cases r with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      exact WFr.refl _ _
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_bind (?_ : (if size = 1#u64 then ok (raw &&& 255#u64) else if size = 2#u64 then
          ok (raw &&& 65535#u64) else ok (raw &&& 4294967295#u64)) ⦃ _ => True ⦄) ?_
      · split
        · exact (WP.spec_ok _).2 trivial
        · split <;> exact (WP.spec_ok _).2 trivial
      intro d _
      refine WP.spec_bind (sts_t hP hC _) ?_
      rintro s1 ⟨hW1, -⟩
      obtain ⟨a1, hpo, -⟩ := spec_exists (hA.port_out ar (i0 &&& 65535#u64) size d)
      rw [hpo]; simp only [bind_ok, WP.spec_ok]
      exact hW1


/-- **The IRQ handler cap's `DecDomHyp`** (`irq_handler_dk4`). -/
theorem decDomHyp_irqHandler (th : TypedHeap) (hP : Placed th)
    (hO : FinObjHyp (L := L) arI th) (hPD : PostDelHyp (L := L) arI th) (hK : NtfnKeepHyp (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hL : IntLayout th (L.ksb s)) (lbl : U64)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (irq : U64) (hirq : irq.val < 128) (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : lbl.val = 35 → ExtraSRel th (L.mem s) x0 cps) (hxn : lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq)
    (hD : DomPlaced (L := L) th s) (hP1 : IrqDelP1 (L := L) s ct irq)
    (length slot buf : U64) (blk call don fp : Bool) :
    DecDomHyp (L := L) arI s ar lbl length slot (.IrqHandler irq) blk call don fp buf extra := by
  unfold DecDomHyp syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  exact irq_handler_dk4 arI th hP hO hPD hK s ar σ G hDS hL lbl ct hct hcur htcb hact hmask irq hirq hok extra x0 hx0
    cps hex hxn hD hP1

/-- **The IO port control cap's `DecDomHyp`** (`IoCPost`'s `DK4` conjunct). -/
theorem decDomHyp_ioportControl (th : TypedHeap) (hP : Placed th) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hL : IoLayout th (L.ksb s))
    (hIo : IoRel (L.mem s) (L.ksb s) σ) (hPA : IoPortsAlloc (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : lbl.val = 63 ↔ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IOPortControlIssue)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact3 : ∀ w : U64, w.val < 1024 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ ioA (L.ksb s) w)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IoPortControl)
    (hD : DomPlaced (L := L) th s) (blk call don fp : Bool) :
    DecDomHyp (L := L) arI s ar lbl length (cslotAddr (ps.bv, idxs)) .IoPortControl blk call don fp buf extra := by
  unfold DecDomHyp syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (ioport_control_decode_refines arI th hP s ar σ G hCR hL hIo hPA hFI hFR lbl slbl hlbl length buf
    ct hct args hlen hargs hcur htcb hact hact3 extra x0 hx0 _ hex hps hls hsrcC .ioPortControlCap) ?_
  rintro ⟨r0, s', a'⟩ hq
  cases r0 with
  | Err e => obtain ⟨rfl, -⟩ := hq; exact DK4.refl _
  | Ok u =>
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hdk, -⟩ := hq
    exact hdk hD

/-- **The IO port cap's `DecDomHyp`** (`ioport_wfr`). -/
theorem decDomHyp_ioport (th : TypedHeap) (hP : Placed th) (hA : P0.ArchTotal arI) (s : S) (ar : A)
    (lbl length slot : U64) (first last x : U64) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hC : TCtx (L := L) th s ct) (hB : CallerBufHyp (L := L) th s ct) :
    DecDomHyp (L := L) arI s ar lbl length slot (.IoPort first last x) blk call don fp buf extra := by
  unfold DecDomHyp syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  exact WP.spec_mono (ioport_wfr arI th hP hA s ar lbl length first last x call buf ct hct hC hB)
    fun _ h => DK4.of_wfr h

end

end

end Fl4Proofs.P3

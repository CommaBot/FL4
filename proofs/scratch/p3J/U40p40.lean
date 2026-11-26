  obtain ⟨⟨hJ17, hB⟩, hR0⟩ := hJ
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    Fl4ProofsJ.P3.SInvR.G5.kernel_entry_reachU33 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu
      hRef hPI hSX hDR hJ17
  obtain ⟨x, hk, -⟩ := hX.sb.1.2
  have hh := hX.sb.1.1.vih
  have hm := hX.sb.1.1.vim
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, SInvIB.IrqCarry.capBound hh hB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl
      (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
        (((hK σb hb V' Ac' Lst' D' s' a' hF J').toU38 hMap).toU36 (BudgetAt.ioaRel hR0 hb)).toJ.toU32 hA)
      (fun σb hb V' Ac' Lst' D' s' a' hF J' ct' hct' =>
        ⟨hDL σb hb V' Ac' Lst' D' s' a' hF J' ct' hct',
          irqAckU_of_capBound hM J' (SInvIB.IrqCarry.capBound (vih_disp hnd hk hb hh) (BudgetAt.irqCarry hm hB hb))⟩)
      hFin) ?_
    rintro r ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ'⟩
    exact ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', ⟨hJ', SInvIB.kentry_irqCarry true c hm hB _ hσ'⟩,
      hR0.frame (SInvIox.kentry_ioxV true c σ _ hσ')⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqCarry hm hB hO⟩, EvOut.ioaRel hR0 hO⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqCarry hm hB hO⟩, EvOut.ioaRel hR0 hO⟩
  · intro ad c ft hct hVm' hE
    refine WP.spec_mono (hVm ad c ft hct hVm' hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqCarry hm hB hO⟩, EvOut.ioaRel hR0 hO⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqCarry hm hB hO⟩, EvOut.ioaRel hR0 hO⟩
  · intro n hct hU hD hE
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqCarry hm hB hO⟩, EvOut.ioaRel hR0 hO⟩

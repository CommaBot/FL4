  have hB := hJ.1.2
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU40 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hMap
      (JReachU40.of_U38 hJ)
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl hK hDL hFin) ?_
    rintro r ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', ⟨hJ', -⟩, hIR'⟩
    exact ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', ⟨hJ', SInvIB.kentry_irqStB true c hB _ hσ'⟩, hIR'⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', -⟩, hIR'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqStB hB hO⟩, hIR'⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', -⟩, hIR'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqStB hB hO⟩, hIR'⟩
  · intro ad c ft hct hVm' hE
    refine WP.spec_mono (hVm ad c ft hct hVm' hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', -⟩, hIR'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqStB hB hO⟩, hIR'⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', -⟩, hIR'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqStB hB hO⟩, hIR'⟩
  · intro n hct hU hD hE
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', -⟩, hIR'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqStB hB hO⟩, hIR'⟩

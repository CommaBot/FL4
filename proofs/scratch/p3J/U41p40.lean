  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU41 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hMap hFpu hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    exact hSys n c hct hn hfl hK hDL
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' => (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').to41)
  · intro w a1 hIh hE; exact hIrq w a1 hIh hE.to41
  · intro n c hct hU hE; exact hUs n c hct hU hE.to41
  · intro ad c ft hct hVm' hE; exact hVm ad c ft hct hVm' hE.to41
  · intro v hct hv hE; exact hTr v hct hv (fun ev hev w hw => (hE ev hev w hw).to41)
  · intro n hct hU hD hE; exact hSU n hct hU hD (fun ev hev w hw => (hE ev hev w hw).to41)

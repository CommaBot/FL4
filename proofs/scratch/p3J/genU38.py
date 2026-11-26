# p3J gen 4: generate P3/XTopJointKEntryU38.lean from U36's statement.
import sys
root = sys.argv[1]
src = open(root + '/Fl4Proofs/P3/XTopJointKEntryU36.lean').read().split('\n')
i = next(k for k, l in enumerate(src) if l.startswith('theorem kernel_entry_reachU36 '))
j = next(k for k in range(i, len(src)) if src[k].rstrip().endswith(':= by'))
stmt = '\n'.join(src[i:j + 1])
hj = '(hJ : JReachU34 (L := L) arI AR MR s a σ)'
ex = 'JReachU34 (L := L) arI AR MR r.1 r.2 σ\''
assert stmt.count(hj) == 1 and stmt.count(ex) == 6 and stmt.count('KDispHypsKVU36') == 1
s38 = (stmt.replace('theorem kernel_entry_reachU36 ', 'theorem kernel_entry_reachU38 ', 1)
       .replace(hj, '(hJ : JReachU38 (L := L) arI AR MR s a σ)').replace(ex, 'JReachU38 (L := L) arI AR MR r.1 r.2 σ\'')
       .replace('KDispHypsKVU36', 'KDispHypsKVU38'))
s36 = (stmt.replace('theorem kernel_entry_reachU36 ', 'theorem kernel_entry_reachU36_of38 ', 1)
       .replace(hj, hj + '\n    (hIR : IoaRel arI σ)'))
head = open(root + '/scratch/p3J/U38head.lean').read()
args = 'arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR'
body38 = '''
  obtain ⟨hJ34, hR0⟩ := hJ
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU36 %s hJ34
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
      (hK σb hb V' Ac' Lst' D' s' a' hF J').toU36 (BudgetAt.ioaRel hR0 hb)) hDL hFin) ?_
    rintro r ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ'⟩
    exact ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ', hR0.frame (SInvIox.kentry_ioxV true c σ _ hσ')⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.ioaRel hR0 hO⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.ioaRel hR0 hO⟩
  · intro ad c ft hct hVm' hE
    refine WP.spec_mono (hVm ad c ft hct hVm' hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.ioaRel hR0 hO⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.ioaRel hR0 hO⟩
  · intro n hct hU hD hE
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.ioaRel hR0 hO⟩
''' % args
body36 = '''
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU38 %s ⟨hJ, hIR⟩
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
      (hK σb hb V' Ac' Lst' D' s' a' hF J').toU38) hDL hFin) ?_
    rintro r ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ'⟩
    exact ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ'.1⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'.1⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'.1⟩
  · intro ad c ft hct hVm' hE
    refine WP.spec_mono (hVm ad c ft hct hVm' hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'.1⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'.1⟩
  · intro n hct hU hD hE
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'.1⟩
''' % args
out = head + '''
set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU38`** (module docstring): U36 without the per-entry `ioapics` / `pins`, from the
carried `IoaRel`. -/
''' + s38 + body38 + '''
set_option maxHeartbeats 8000000 in
/-- **U38 gives U36 at the states whose backend IOAPIC counts are the spec's** (module docstring):
U36's statement, with the hypothesis `hIR : IoaRel arI σ`. -/
''' + s36 + body36 + '''
end

end

end Fl4Proofs.P3.SInvR.G5
'''
open(root + '/Fl4Proofs/P3/XTopJointKEntryU38.lean', 'w').write(out)
print('ok')

# p3J: generate P3/XTopJointKEntryU35.lean from U34's statement (verbatim copy, one name changed).
import sys, re
root = sys.argv[1]
src = open(root + '/Fl4Proofs/P3/XTopJointKEntryU34.lean').read().split('\n')
i = next(k for k, l in enumerate(src) if l.startswith('theorem kernel_entry_reachU34 '))
j = next(k for k in range(i, len(src)) if src[k].rstrip().endswith(':= by'))
stmt = '\n'.join(src[i:j + 1])
assert stmt.count('KDispHypsKVU32') == 1
s35 = stmt.replace('theorem kernel_entry_reachU34 ', 'theorem kernel_entry_reachU35 ', 1).replace('KDispHypsKVU32', 'KDispHypsKVU35')
s34 = stmt.replace('theorem kernel_entry_reachU34 ', 'theorem kernel_entry_reachU34_of35 ', 1)
head = open(root + '/scratch/p3J/U35head.lean').read()
body35 = '''
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hRest⟩ :=
    kernel_entry_reachU34 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, hRest⟩
  intro n c hct hn hfl hK hDL hFin
  exact hSys n c hct hn hfl
    (fun σb hb V' Ac' Lst' D' s' a' hF J' => (hK σb hb V' Ac' Lst' D' s' a' hF J').toU32 hA) hDL hFin
'''
body34 = '''
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hRest⟩ :=
    kernel_entry_reachU35 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, hRest⟩
  intro n c hct hn hfl hK hDL hFin
  exact hSys n c hct hn hfl
    (fun σb hb V' Ac' Lst' D' s' a' hF J' => (hK σb hb V' Ac' Lst' D' s' a' hF J').toU35) hDL hFin
'''
out = head + '''
set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU35`** (module docstring): U34 with the syscall clause's per-entry
`KDispHypsKVU32` narrowed to `KDispHypsKVU35` (no `ArchIrqRelN.num`, no `ArchIrqRelN.mask`). -/
''' + s35 + body35 + '''
set_option maxHeartbeats 8000000 in
/-- **U35 gives U34**: `kernel_entry_reachU34`'s statement, verbatim, from `kernel_entry_reachU35`
(`KDispHypsKVU32.toU35`). -/
''' + s34 + body34 + '''
end

end

end Fl4Proofs.P3.SInvR.G5
'''
open(root + '/Fl4Proofs/P3/XTopJointKEntryU35.lean', 'w').write(out)
print('ok')

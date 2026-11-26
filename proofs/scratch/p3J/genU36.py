# p3J gen 2: generate P3/XTopJointKEntryU36.lean from U35's statement (verbatim copy, one name changed).
import sys
root = sys.argv[1]
src = open(root + '/Fl4Proofs/P3/XTopJointKEntryU35.lean').read().split('\n')
i = next(k for k, l in enumerate(src) if l.startswith('theorem kernel_entry_reachU35 '))
j = next(k for k in range(i, len(src)) if src[k].rstrip().endswith(':= by'))
stmt = '\n'.join(src[i:j + 1])
assert stmt.count('KDispHypsKVU35') == 1
s36 = stmt.replace('theorem kernel_entry_reachU35 ', 'theorem kernel_entry_reachU36 ', 1).replace('KDispHypsKVU35', 'KDispHypsKVU36')
s35 = stmt.replace('theorem kernel_entry_reachU35 ', 'theorem kernel_entry_reachU35_of36 ', 1)
head = open(root + '/scratch/p3J/U36head.lean').read()
args = 'arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ'
body36 = '''
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hRest⟩ :=
    Fl4ProofsJ.P3.SInvR.G5.kernel_entry_reachU35 %s
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, hRest⟩
  intro n c hct hn hfl hK hDL hFin
  exact hSys n c hct hn hfl
    (fun σb hb V' Ac' Lst' D' s' a' hF J' => (hK σb hb V' Ac' Lst' D' s' a' hF J').toJ) hDL hFin
''' % args
body35 = '''
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hRest⟩ :=
    kernel_entry_reachU36 %s
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, hRest⟩
  intro n c hct hn hfl hK hDL hFin
  exact hSys n c hct hn hfl
    (fun σb hb V' Ac' Lst' D' s' a' hF J' => (hK σb hb V' Ac' Lst' D' s' a' hF J').toU36) hDL hFin
''' % args
out = head + '''
set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU36`** (module docstring): U35 with the path premise at the invoked slot only. -/
''' + s36 + body36 + '''
set_option maxHeartbeats 8000000 in
/-- **U36 gives U35**: `kernel_entry_reachU35`'s statement, verbatim, from `kernel_entry_reachU36`
(`KDispHypsKVU35.toU36`). -/
''' + s35 + body35 + '''
end

end

end Fl4Proofs.P3.SInvR.G5
'''
open(root + '/Fl4Proofs/P3/XTopJointKEntryU36.lean', 'w').write(out)
print('ok')

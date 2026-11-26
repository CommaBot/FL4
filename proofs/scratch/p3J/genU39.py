# gen 5: XTopJointKEntryU39 = U38 with the per-entry map/mapr replaced by a global IoaMap premise.
import re, pathlib
src = pathlib.Path('Fl4Proofs/P3/XTopJointKEntryU38.lean').read_text().splitlines()
st = next(i for i,l in enumerate(src) if l.startswith('theorem kernel_entry_reachU38 '))
en = next(i for i in range(st, len(src)) if src[i].rstrip().endswith(':= by'))
stmt = src[st:en+1]
stmt[0] = stmt[0].replace('kernel_entry_reachU38', 'kernel_entry_reachU39')
body = '\n'.join(stmt)
assert body.count('KDispHypsKVU38') == 1
body = body.replace('KDispHypsKVU38', 'KDispHypsKVU39')
old = '(hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)'
assert body.count(old) == 1
body = body.replace(old, old + '\n    (hMap : IoaMap arI)')
head = pathlib.Path('scratch/p3J/U39head.lean').read_text()
tail = '''
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hRest⟩ :=
    kernel_entry_reachU38 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, hRest⟩
  intro n c hct hn hfl hK hDL hFin
  exact hSys n c hct hn hfl (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
    (hK σb hb V' Ac' Lst' D' s' a' hF J').toU38 hMap) hDL hFin

end

end

end Fl4Proofs.P3.SInvR.G5
'''
pathlib.Path('Fl4Proofs/P3/XTopJointKEntryU39.lean').write_text(head + body + tail)

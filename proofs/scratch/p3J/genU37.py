# p3J gen 3: generate P3/XTopJointKEntryU37.lean from U36's statement (+ the KNoVtx antecedent).
import sys
root = sys.argv[1]
src = open(root + '/Fl4Proofs/P3/XTopJointKEntryU36.lean').read().split('\n')
i = next(k for k, l in enumerate(src) if l.startswith('theorem kernel_entry_reachU36 '))
j = next(k for k in range(i, len(src)) if src[k].rstrip().endswith(':= by'))
stmt = '\n'.join(src[i:j + 1])
blk = '''        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU36 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
'''
assert stmt.count(blk) == 1
nov = blk.replace("KDispHypsKVU36 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c", "KNoVtx (L := L) s' σb n c")
new = nov + blk.replace('KDispHypsKVU36', 'KDispHypsKVU37')
s37 = stmt.replace(blk, new).replace('theorem kernel_entry_reachU36 ', 'theorem kernel_entry_reachU37 ', 1)
head = open(root + '/scratch/p3J/U37head.lean').read()
args = 'arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ'
body = '''
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hRest⟩ :=
    kernel_entry_reachU36 %s
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, hRest⟩
  intro n c hct hn hfl hNV hK hDL hFin
  exact hSys n c hct hn hfl
    (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
      (hK σb hb V' Ac' Lst' D' s' a' hF J').toU36 (hNV σb hb V' Ac' Lst' D' s' a' hF J')) hDL hFin
''' % args
out = head + '''
set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU37`** (module docstring): U36 for non-VT-x invocations (`KNoVtx` [S]), without
the VT-x leaves. -/
''' + s37 + body + '''
end

end

end Fl4Proofs.P3.SInvR.G5
'''
open(root + '/Fl4Proofs/P3/XTopJointKEntryU37.lean', 'w').write(out)
print('ok')

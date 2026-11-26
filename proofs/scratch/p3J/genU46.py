# gen 14: XTopJointKEntryU46 from U45's statement text (run from proofs/)
u=open('Fl4Proofs/P3/XTopJointKEntryU45.lean').read()
i=u.index('set_option maxHeartbeats 8000000 in\n/-- **`kernel_entry_reachU45`**')
j=u.index('set_option maxHeartbeats 8000000 in\n/-- **U45 gives U44**')
thm=u[i:j]
stmt45=thm[:thm.index(':= by')]
assert stmt45.count('JDecMRLK (L := L) arI VtxU')==1
d45='''/-- **`kernel_entry_reachU45`** (module docstring): U44 with the per-entry `JDecMRLK VtxK` [J] narrowed to
`JDecMRLK VtxU` [J] (D1 discharged by `jDecMRLK_ofVtxU`). -/'''
assert stmt45.count(d45)==1
s46=stmt45.replace(d45,'''/-- **`kernel_entry_reachU46`** (module docstring): U45 with the per-entry `JDecMRLK VtxU` [J] narrowed to
`JDecMRLK VtxR` [J] (the VT-x-type untyped decodes off the VT-x retype discharged by `jDecMRLK_ofVtxR`). -/''')
s46=s46.replace('kernel_entry_reachU45','kernel_entry_reachU46').replace('JDecMRLK (L := L) arI VtxU','JDecMRLK (L := L) arI VtxR')
s45o=stmt45.replace(d45,'/-- **U46 gives U45** (module docstring): U45\'s statement verbatim. -/').replace('kernel_entry_reachU45','kernel_entry_reachU45_of46')
# nv: drop the JDecMRLK antecedent, add hNV
blk='''        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxU AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
'''
assert stmt45.count(blk)==1
snv=stmt45.replace(d45,'''/-- **`kernel_entry_reachU45nv`** (module docstring): U45 on a platform reporting no virtualization
(`NoVirt` [P]), with no `JDecMRLK` premise at all (`jDecMRLK_vtxU_nv`). -/''').replace(blk,'').replace('kernel_entry_reachU45','kernel_entry_reachU45nv').replace('U45nvnv','U45nv')
assert snv.count('(hCfg : KCfgFL4)')==1
snv=snv.replace('(hCfg : KCfgFL4)','(hCfg : KCfgFL4) (hNV : NoVirt arI)')
args='arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hMap hFpu hFW hCfg hJ'
def proof(src,conv):
  return f''':= by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    {src} {args}
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, hIrq, hUs, hVm, hTr, hSU⟩
  intro n c hct hn hfl hK hDL
  exact hSys n c hct hn hfl hK (fun σb hB V' Ac' Lst' D' s' a' hF hJ' ct' hct' =>
    {conv} (hDL σb hB V' Ac' Lst' D' s' a' hF hJ' ct' hct'))

'''
pnv=f''':= by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU45 {args}
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, hIrq, hUs, hVm, hTr, hSU⟩
  intro n c hct hn hfl hK
  exact hSys n c hct hn hfl hK (fun σb hB V' Ac' Lst' D' s' a' hF hJ' ct' hct' =>
    jDecMRLK_vtxU_nv arI hA hNV hct')

'''
doc=open('scratch/p3J/U46head.lean').read()
out=(doc+s46+proof('kernel_entry_reachU45','jDecMRLK_ofVtxR arI hA hct\'')+s45o+proof('kernel_entry_reachU46','JDecMRLK.mono arI vtxR_vtxU')
     +snv+pnv+'end\n\nend\n\nend Fl4Proofs.P3.SInvR.G5\n')
open('Fl4Proofs/P3/XTopJointKEntryU46.lean','w').write(out)
open('scratch/p3J/U46stmt.txt','w').write(s46)
open('scratch/p3J/U45nvstmt.txt','w').write(snv)

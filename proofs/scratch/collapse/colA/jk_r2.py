"""Rule 2 for collapse A, J + K: jk_r2.py BRANCH OWNLIST -> lines of the branch's own files naming a deleted (DEL) or
re-stated (RST) constant / module."""
import subprocess,re,sys
DEL='''P3JLook P3JGen P3JXport P3KXport P3KGen1 P3KGen P3KFin P3JStIrqK P3JStEvK P3JStTrapK P3JSysStK P3JStIrqKFin ScNextDomCF
kernel_entry_reachU34 kernel_entry_reachU35 kernel_entry_reachU36 kernel_entry_reachU38 KDispHypsKVU32.toU35 KDispHypsKVU35.toU36
KDispHypsKVU36.toU38 KDispHypsKVU38.toU39 KDispHypsKVU39.toU44 JPathAtMU30.toU35 JPathAtMU35.toU44 JPathMEU30.toU44 JEntryAtR7T.toV
JEntryAtR7V.toW BudgetAt.irqStB EvOut.irqStB vtxR_vtxU vtxU_vtxK KDispHypsKVU36.toJ JPathAtMU35 JPathAtMU35.of_invoked
JPathAtML JPathAtM35L JPathAtM35EL JPathAtM36EL JPathAtMU4L JPathAtMU7L JPathAtMU12L JPathAtMU17L JPathAtMU18L JPathAtMU19L JPathAtMU21L
JPathAtMU25L JPathAtMU26L JPathAtMU27L JPathAtMU28L JPathAtMU29L handle_invocation_entryJMUL handle_invocation_entryJMUML
scnt_refines0F cn_refines0F cn_enq0F cn_app0F switch_branch_refines0F schedule_refinesWP0FR sw_refinesF schedule_choose_new_thread_refinesF
scnt_refines0FI sw_refinesFI ArchSwF' ArchSwF.toN scnt_refines0FAI sw_refinesFAI msF_mrT KFinAtRI KFinAtR27I KFinAtR31I KFinAtR5I
to5I to31I to27I toRI jat_scheduleWP0FZRI jat_scheduleFR2ZRI jat_scheduleSR2ZRPI jat_finishJRPI jat_finishJRNI jat_finishJRNMQI
jat_finishJRNMStQI specL specK specK1 specKSt'''.split()
RST='''JPathAtM JPathAtM35 JPathAtM35E JPathAtM36E JPathAtMU4 JPathAtMU7 JPathAtMU12 JPathAtMU17 JPathAtMU18 JPathAtMU19 JPathAtMU21
JPathAtMU25 JPathAtMU26 JPathAtMU27 JPathAtMU28 JPathAtMU29 JPathAtMU30 LookAt handle_invocation_refinesMXPL handle_invocation_entryJMU
handle_invocation_entryJMUM decPt_joint offRoute6_of_path KDispHypsKVU36.toU35 JPathAtMU30.of_invoked ArchSwF ArchSwFT ArchSwFI IdleVt
KFinAtR KFinAtR27 KFinAtR31 KFinAtR5 FinRootR FinRootI jat_finishJRP jat_finishJRN jat_finishJRNM jat_finishJRNMSt jat_scheduleWP0FZR
jat_scheduleFR2ZR jat_scheduleSR2ZRP KFinAtR8.to5 KFinAtR5.to31 KFinAtR31.to27 KFinAtR27.toR scnt_refines0FA sw_refinesFA'''.split()
NS=re.compile(r'Fl4Proofs(J|K|KJ)\.')
TOK=re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
b,lst=sys.argv[1],sys.argv[2]
for f in open(lst).read().split():
    try: t=subprocess.check_output(['git','show',f'{b}:{f}'],text=True,stderr=subprocess.DEVNULL)
    except Exception: continue
    for i,l in enumerate(t.split('\n'),1):
        toks=set(TOK.findall(l)); last={x.split('.')[-1] for x in toks}|toks|{'.'.join(x.split('.')[-2:]) for x in toks}
        d=sorted(x for x in DEL if x in last); r=sorted(x for x in RST if x in last)
        if NS.search(l): d.append('Fl4Proofs{J,K,KJ}')
        if d or r: print(f'{"DEL" if d else "RST"} {f}:{i}: {d or r} | {l.strip()[:150]}')

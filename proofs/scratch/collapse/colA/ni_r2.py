import subprocess,re,sys
DEL='decode_invocation_threadJ_stepM decode_invocation_threadJ_stepMM tcb_copy_regsJ JEntryAtN JEntryAtRN JEntryAtR2N JEntryAtR3N JEntryAtR5N JEntryAtR6N JEntryAtR7N decode_invocation_threadJ_stepMMN decode_invocation_threadJ_stepMN ArchIrqRelN irq_ioapic_refinesN irq_remap_refinesN irq_ioapic_refinesMN irq_remap_refinesMN irq_ioapic_refinesMQ0 irq_remap_refinesMQ0 ctlQ0 stallRecs stallConsts StallNarrowGen StallNarrowRec StallNarrowTcb ArchIrqNarrow ArchIrqNarrowGen JBoot5CtlQ'.split()
RST='JEntryAt JEntryAtR JEntryAtR2 JEntryAtR3 JEntryAtR5 JEntryAtR6 JEntryAtR7 ArchIrqRel JEntryAtR7T toN toI irq_ioapic_refinesMNQ irq_remap_refinesMNQ jDecMRL_ofQ jDecMRL2_ofTQ jDecMRLK_ofUQ handle_invocation_entryJMUL handle_invocation_entryJMUML specB specD specBW specM JAtZ.stallT tcb_copy_regsJT decode_invocation_threadJ_stepMT decode_invocation_threadJ_stepMMT irq_ioapic_refines irq_remap_refines irq_ioapic_refinesM irq_remap_refinesM'.split()
NS=re.compile(r'Fl4Proofs(?:K?J?Q?)(?:N|I)\.')
TOK=re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
b,lst=sys.argv[1],sys.argv[2]
for f in open(lst).read().split():
    try: t=subprocess.check_output(['git','show',f'{b}:{f}'],text=True,stderr=subprocess.DEVNULL)
    except Exception: continue
    for i,l in enumerate(t.split('\n'),1):
        toks=set(TOK.findall(l)); last={x.split('.')[-1] for x in toks}|toks
        d=sorted(x for x in DEL if x in last); r=sorted(x for x in RST if x in last)
        if NS.search(l): d.append('Fl4Proofs[N|I]-copy')
        if d or r: print(f'{"DEL" if d else "RST"} {f}:{i}: {d or r} | {l.strip()[:140]}')

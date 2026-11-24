# fb3: scratch-only stubs at the six FrameBatch sites (NOT for commit). apply / revert
import sys
mode=sys.argv[1]
P='proofs/Fl4Proofs/'
E=[]
# fb3j: VsTopX / VsThX (capX, domFrame_pml4, thX) restricted to non-batch labels; the batch is
# XTopJointVsFb.decode_invocation_pml4_fbJV; fb3k: decode + fb_loopJ proved, the one P3 chain stub is
# XTopJointVsFb.fb_loopI (the loop entry by entry; same `fail` line)
# fb3l: fb_entryJ split by op; the stubs are the three per-op lemmas
E.append((P+'P3/XTopJointFbDelDefer.lean','  fail "FB3 OPEN: the deferred unmap at J (KENTRY-PLAN fb3l)"\n','  sorry -- FB3SCRATCH\n'))
# fb3g: P1 QueueDecVs batch arm proved (vspace.decode_frame_batch.dec)
# fb3e: UtP1 batch arm proved (SpecFbP3)
# fb3e: SgD / SiD batch arms proved (SpecFbP3.fbq_run)
for p,a,b in E:
    if mode=="saferevert":
        t=open(p).read()
        if b in t: open(p,"w").write(t.replace(b,a)); print("reverted",p)
        continue
    t=open(p).read()
    if mode=='apply':
        assert t.count(a)==1,(p,'apply'); t=t.replace(a,b)
    else:
        assert t.count(b)==1,(p,'revert'); t=t.replace(b,a)
    open(p,'w').write(t)
print(mode,'ok')

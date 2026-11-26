import re,sys
P2=sys.argv[1]
blk=open(P2+'/InvBlk.lean').read().split('\n')
accx=open(P2+'/InvDelPteAccX.lean').read().split('\n')
fin=open(P2+'/InvBlkFin.lean').read().split('\n')
vs=open(P2+'/InvVs.lean').read().split('\n')
def rng(L,a,b): return L[a-1:b]
def find(L,pat,start=0):
    for i in range(start,len(L)):
        if pat in L[i]: return i
    raise Exception(pat)
# --- delAcc (InvBlk) lines
i0=find(blk,'theorem delAcc {A'); i1=find(blk,'end acc',i0)
da=blk[i0:i1]
# --- delAccX lines
j0=find(accx,'theorem delAccX'); 
xw0=find(accx,'  -- the words',j0); xw1=find(accx,'  -- the frame finalisation',xw0)
words=accx[xw0:xw1]
xn0=find(accx,'  have nXs',j0); xn1=find(accx,'  have w0 :=',xn0)
nx=accx[xn0:xn1]
s='\n'.join(da)
s=s.replace('theorem delAcc {A','theorem delAccN {A',1)
s=s.replace('{W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]',
            '{R W X : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]',1)
s=s.replace('''        VsRd st K s asid va)
''','''        VsRdG st (fun b => VsW K b ∧ ¬ X b) s asid va)
    (hXv : ∀ b, X b → VsW K b) (hR : ∀ b, IoRS (st := st) K Locks s b → ¬ X b → R b)
''',1)
L=s.split('\n')
k=[i for i,l in enumerate(L) if l.startswith('  have hL : Slot8 K')][0]
L=L[:k+1]+nx+L[k+1:]
s='\n'.join(L)
# replace words block
a=s.index('  -- the words'); b=s.index('  -- the frame finalisation')
s=s[:a]+'\n'.join(words)+'\n'+s[b:]
# frame part
s=s.replace('va ≤ fl4_abi.consts.USER_TOP ∧ VsRd st K s asid va := fun hmp hA => by','va ≤ fl4_abi.consts.USER_TOP ∧\n      VsRdG st (fun b => VsW K b ∧ ¬ X b) s asid va := fun hmp hA => by')
s=s.replace('''      ∀ b, VsW K b → st.read x3 b = st.read s b := fun x3 hs3 b hb => by
''','''      ∀ b, (fun b => VsW K b ∧ ¬ X b) b → st.read x3 b = st.read s b := fun x3 hs3 b hb0 => by
    have hb := hb0.1
''')
s=s.replace('FrNo st ar x3 mp asid va fp := fun x3 hs3 => frNo_of ar hm hvs1','FrNo st ar x3 mp asid va fp := fun x3 hs3 => frNo_ofG ar hm hvs1')
s=s.replace('FrNo gS ar x3 mp asid va fp := fun x3 hs3 => frNo_of ar hm hvs1','FrNo gS ar x3 mp asid va fp := fun x3 hs3 => frNo_ofG ar hm hvs1')
s=s.replace('(fun b hb => (gst_read (VsW.ioRS (Locks := Locks) (s := s) hb)).trans (hr3 x3 hs3 b hb))',
            '(fun b hb => (gst_read (hR _ (VsW.ioRS (Locks := Locks) (s := s) hb.1) hb.2)).trans (hr3 x3 hs3 b hb))')
s=s.replace('''  have hmx2 : IoRS (st := st) K Locks s
''','''  have hmx2 : R
''')
s=s.replace('(hN s2 hnd2) (hWs _ rst.2) rst.1 rsc hmx2 riq]','(hN s2 hnd2) (hWs _ rst.2) rstR rsc hmx2 riq]')
s=s.replace('refine invRep.guard_ok (gS := gS) rst.1 (hWs _ rst.2)','refine invRep.guard_ok (gS := gS) rstR (hWs _ rst.2)')
assert 'IoRS (st := st) K Locks s (' not in s.split('theorem delAccN')[1].split(':= by')[1], 'left IoRS'
delaccN=s
# --- delFin
f0=find(fin,'theorem delFin {A'); f1=find(fin,'end fin',f0)
t='\n'.join(fin[f0:f1]).rstrip()
t=t.replace('theorem delFin {A','theorem delFinN {A',1)
t=t.replace('IoRS (st := st) K Locks s','IoRSR st K Locks s')
t=t.replace('P.ent (Locks := Locks)','P.entR (Locks := Locks)')
# --- unmap_nop / frNo_of
u0=find(vs,'theorem unmap_nop'); u1=find(vs,'end nop',u0)
u='\n'.join(vs[u0:u1]).rstrip()
u=u.replace('theorem unmap_nop','theorem unmap_nopG').replace('theorem frNo_of','theorem frNo_ofG')
u=u.replace('{K : KLayout}','{V : U64 → Prop}').replace('VsW K a','V a').replace('VsW K b','V b')
u=u.replace('VsRd st K s asid va','VsRdG st V s asid va').replace('unmap_nop ar hr','unmap_nopG ar hr')
out=open(sys.argv[2],'w')
out.write(open(sys.argv[3]).read())
out.write('''
section nopG
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (unify gen 2) **`unmap_nop` for any walk read set `V`** (InvVs's `unmap_nop`, `VsW K` → `V`). -/
'''+u+'''

end nopG

section accN
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayout}

set_option maxHeartbeats 2000000 in
/-- (unify gen 2) **The no-PTE Delete decode block on a read set without the leaf entries**: stpost's `delAcc`
(scripted copy) for any read set `R` containing the `IoRS` words off a set `X` of `VsW` words (`hR`), the walk
reading only `VsW` words off `X` (`hvs` with `VsRdG`; `SlJAtZ.vsRdX`). The read conversions are delAccX's. -/
'''+delaccN.rstrip()+'''

end accN

section finN
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

set_option maxHeartbeats 4000000 in
/-- (unify gen 2) **`FinOK` over `IoRSR` after the no-PTE Delete decode block** (stpost's `delFin`, scripted:
`IoRS` → `IoRSR`, `IoPre.ent` → `IoPre.entR`). -/
'''+t+'''

end finN

end Fl4Proofs.P2.PathObl
''')

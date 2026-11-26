import sys
P2=sys.argv[1]
def grab(fn,start,endpat='end '):
    L=open(P2+'/'+fn).read().split('\n')
    i=[k for k,l in enumerate(L) if l.startswith(start)][0]
    j=i+1
    while not L[j].startswith(endpat): j+=1
    # stop at next top-level docstring/set_option/theorem after this theorem
    out=[L[i]]
    for l in L[i+1:j]:
        if l.startswith('/--') or l.startswith('set_option') or l.startswith('theorem') or l.startswith('def '): break
        out.append(l)
    return '\n'.join(out).rstrip()
def R(t):
    for a,b in [('IoRS (st := st) K Locks s','IoRSR st K Locks s'),('P.ent (Locks','P.entR (Locks'),
                ('P.slot (Locks','P.slotR (Locks'),('P.lockSlot ','P.lockSlotR '),('P.nd ','P.ndR '),
                ('(P.nd layout','(P.ndR layout'),('P.reg ','P.regR '),('P.reg (','P.regR ('),('P.stw (','P.stwR ('),
                ('P.gate (','P.gateR ('),('P.home (','P.homeR ('),('P.cscacc.','P.cscaccR.'),('P.mid (','P.midR (')]:
        t=t.replace(a,b)
    return t
a=R(grab('InvCMAccZ.lean','theorem cmAccZ {')).replace('theorem cmAccZ {','theorem cmAccZR {',1)
f=R(grab('InvCMFin8.lean','theorem cmFin8 {')).replace('theorem cmFin8 {','theorem cmFin8R {',1)
a=a.replace('hR _ (P.lockSlotR hq hl ho h8).1','hR _ (P.lockSlotR hq hl ho h8)')
g=R(grab('InvCMBlk.lean','theorem inv_acc_gen3 {')).replace('theorem inv_acc_gen3 {','theorem inv_acc_gen3R {',1)
g=g.replace('guard_acc3 (gS := gS) ar (P.entR','guard_acc3 (gS := gS) ar (P.entR')
out=open(sys.argv[2],'w')
out.write(open(sys.argv[3]).read())
out.write('''
section accZR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayout}

set_option maxHeartbeats 4000000 in
/-- (unify gen 2) **slhuf's `cmAccZ` on a store reading `IoRSR s`** (and the aligned user words): scripted copy,
`IoRS` → `IoRSR`, the `IoPre` lemmas → their `…R` versions. -/
'''+a+'''

end accZR

section finR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

set_option maxHeartbeats 4000000 in
/-- (unify gen 2) **slhuf's `cmFin8` with `FinOK` over `IoRSR`** (scripted copy, `IoRS` → `IoRSR`,
`IoPre.ent` → `IoPre.entR`). -/
'''+f+'''

end finR

section accR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- (unify gen 2) **slhuf's `inv_acc_gen3` on a store reading `IoRSR s`** (scripted copy, as invj's
`inv_acc_genR` of `inv_acc_gen2`). -/
'''+g+'''

end accR

end Fl4Proofs.P2.PathObl
''')

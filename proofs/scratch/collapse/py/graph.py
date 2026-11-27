#!/usr/bin/env python3
"""Import graph over a tree (working dir or git rev). usage: graph.py [rev]"""
import os, re, subprocess, sys, json
ROOT='/Users/stillfail/.stillfail/sessions/claude-ember@d70ccd1321eaa3aa3390df77fb901ff2774a7cc3da926c3cf25ca287a3ba5f22/C0AQ0C0KVMH-1794890878-390829/workspace/FL4-collapse'
IMP=re.compile(r'^\s*import\s+(.+)$')
def parse_imports(txt):
    txt=strip_comments(txt)
    out=[]
    for line in txt.splitlines():
        t=line.strip()
        if not t: continue
        if t.startswith('import ') or t.startswith('public import '):
            out+=t.split('import',1)[1].split()
        elif t in ('prelude','module'): continue
        else: break
    return out
def strip_comments(txt):
    o=[];i=0;d=0;n=len(txt)
    while i<n:
        if txt.startswith('/-',i): d+=1;i+=2;continue
        if d and txt.startswith('-/',i): d-=1;i+=2;continue
        if d: 
            if txt[i]=='\n': o.append('\n')
            i+=1;continue
        if txt.startswith('--',i):
            j=txt.find('\n',i); i=n if j<0 else j; continue
        o.append(txt[i]);i+=1
    return ''.join(o)
def _old(txt):
    out=[]
    for line in txt.splitlines():
        s=line.strip()
        if s.startswith('import '):
            out+= [x for x in s[7:].split() if not x.startswith('--')]
        elif s and not s.startswith('--') and not s.startswith('/-') and not s.startswith('prelude') and not s.startswith('module'):
            # imports must come first; stop at first other non-comment line
            if not s.startswith('import'): 
                if s.startswith('public import') : continue
                break
    return out
def mod_of(path):
    return path[len('proofs/'):-5].replace('/','.')
def load_worktree():
    g={}
    for d,_,fs in os.walk(ROOT+'/proofs'):
        if '/.lake' in d or '/scratch' in d or '/.deps' in d: continue
        for f in fs:
            if f.endswith('.lean'):
                p=os.path.join(d,f)[len(ROOT)+1:]
                g[mod_of(p)]=parse_imports(open(ROOT+'/'+p,errors='replace').read())
    return g
def load_rev(rev):
    fs=subprocess.run(['git','-C',ROOT,'ls-tree','-r','--name-only',rev,'proofs'],capture_output=True,text=True).stdout.split()
    fs=[f for f in fs if f.endswith('.lean') and '/scratch/' not in f and '/.lake' not in f]
    # batch cat
    inp='\n'.join(f'{rev}:{f}' for f in fs)+'\n'
    out=subprocess.run(['git','-C',ROOT,'cat-file','--batch'],input=inp.encode(),capture_output=True).stdout
    g={};i=0
    for f in fs:
        nl=out.index(b'\n',i); hdr=out[i:nl].split(); n=int(hdr[2]); body=out[nl+1:nl+1+n]; i=nl+1+n+1
        g[mod_of(f)]=parse_imports(body.decode(errors='replace'))
    return g
if __name__=='__main__':
    g=load_rev(sys.argv[1]) if len(sys.argv)>1 else load_worktree()
    json.dump(g,sys.stdout)

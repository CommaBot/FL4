"""Parse Lean source into top-level declaration blocks with fully qualified names."""
import re
DECL=re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)\s+([^\s:({\[]+)")
PREFIX=re.compile(r"^(/--|@\[|set_option .* in\s*$)")
def blocks(text):
    lines=text.split('\n')
    ns=[]  # stack of (kind,name)
    out=[]
    i=0;n=len(lines)
    # first pass: find decl header lines and namespace context
    hdrs=[]
    depth=0  # block comment depth for skipping module docstring etc
    for idx,l in enumerate(lines):
        if depth==0 and re.match(r'^/-(?!-)',l) and '-/' not in l[2:]:
            depth=1; continue
        if depth:
            if '-/' in l: depth=0
            continue
        m=re.match(r'^namespace\s+(\S+)',l)
        if m: ns.append(('ns',m.group(1))); continue
        m=re.match(r'^(noncomputable\s+)?section(\s+(\S+))?\s*$',l)
        if m: ns.append(('sec',m.group(3) or '')); continue
        m=re.match(r'^end(\s+(\S+))?\s*$',l)
        if m:
            if ns: ns.pop()
            continue
        m=DECL.match(l)
        if m:
            priv = bool(m.group(1)) and 'private' in (m.group(0))
            nm=m.group(3)
            full = nm[7:] if nm.startswith('_root_.') else '.'.join([x for k,x in ns if k=='ns']+[nm])
            hdrs.append((idx,full,m.group(2),'private' in m.group(0)))
    for j,(idx,full,kind,priv) in enumerate(hdrs):
        # start: walk back over docstring / attributes / set_option-in lines
        s=idx
        k=idx-1
        while k>=0:
            l=lines[k]
            if PREFIX.match(l): s=k; k-=1; continue
            # inside a docstring that started above
            if l.rstrip().endswith('-/') and not l.startswith('/-'):
                # find its start
                kk=k
                while kk>=0 and not lines[kk].startswith('/--'): kk-=1
                if kk>=0: s=kk; k=kk-1; continue
                break
            if l.startswith('/--') : s=k; k-=1; continue
            break
        # end: next column-0 nonblank line that is not part of this decl
        e=idx+1
        while e<n:
            l=lines[e]
            if l and not l[0].isspace() and not l.startswith('--') :
                break
            if l.startswith('--'):
                # col-0 line comment: part of block only if next nonblank line is indented
                f=e+1
                while f<n and not lines[f].strip(): f+=1
                if f<n and lines[f][:1].isspace(): e+=1; continue
                break
            e+=1
        # trim trailing blank lines
        while e>idx+1 and not lines[e-1].strip(): e-=1
        out.append(dict(name=full,kind=kind,priv=priv,start=s,hdr=idx,end=e))
    return lines,out

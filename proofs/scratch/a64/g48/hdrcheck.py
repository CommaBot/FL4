# usage: hdrcheck.py OLD NEW : every declaration of OLD has a byte-identical statement (text up to `:=`/`where`) in NEW
import re,sys
def hdrs(t):
    out={}
    for m in re.finditer(r'^(?:private )?(theorem|def|abbrev|structure|noncomputable def|lemma|instance) (\S+)',t,re.M):
        i=m.start(); n=m.group(2)
        j1=t.find(':=',i); j2=t.find(' where',i)
        j=min(x for x in (j1,j2) if x>=0)
        out.setdefault(n,[]).append(t[i:j])
    return out
a=hdrs(open(sys.argv[1]).read()); b=hdrs(open(sys.argv[2]).read())
bad=[n for n in a if a[n]!=b.get(n)]
print('old decls',len(a),'new decls',len(b),'changed/missing',bad,'added',[n for n in b if n not in a])

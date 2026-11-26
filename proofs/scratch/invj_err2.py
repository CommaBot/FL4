import sys,re
lines=open(sys.argv[1],errors='replace').read().split('\n')
seen=set(); out=[]; i=0
while i<len(lines):
    l=lines[i]
    if re.match(r'^error: .*\.lean:\d+:\d+:',l) and l not in seen:
        seen.add(l); out.append('=== '+l[:400])
        j=i+1; ing=False
        while j<len(lines) and not re.match(r'^(error|warning):',lines[j]):
            t=lines[j]
            if t.startswith('⊢'): ing=True
            elif t and not t.startswith(' ') and ing: ing=False
            if ing: out.append(t[:300])
            elif not ing and not re.match(r'^\S.* :',t) and not t.startswith(' ') and t.strip() and not t.startswith('case'): out.append(t[:300])
            j+=1
        i=j
    else: i+=1
print('\n'.join(out)[:int(sys.argv[2])])

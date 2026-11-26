import sys,re
# print each error message: header line, then lines starting with ⊢ (goal) and their continuation, skipping hypotheses
lines=open(sys.argv[1],errors='replace').read().split('\n')
seen=set(); out=[]
i=0
while i<len(lines):
    l=lines[i]
    m=re.match(r'^(error: .*?\.lean:\d+:\d+:.*)$',l)
    if m and m.group(1) not in seen:
        seen.add(m.group(1)); out.append('=== '+l)
        j=i+1
        while j<len(lines) and not lines[j].startswith('error:') and not lines[j].startswith('warning:') and not lines[j].startswith('✖') and not lines[j].startswith('⚠'):
            t=lines[j]
            if t.startswith('⊢') or t.startswith('  ') and out and out[-1].startswith(('⊢','  ')) and not re.match(r'^\S+ : ',t):
                out.append(t)
            elif not re.match(r'^[^ ⊢].* : ',t) and not t.startswith('case ') and t.strip():
                out.append(t)
            j+=1
        i=j
    else:
        i+=1
print('\n'.join(out)[:int(sys.argv[2]) if len(sys.argv)>2 else 20000])

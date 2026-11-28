import sys,re,os
def imps(m):
    p=m.replace('.','/')+'.lean'
    if not os.path.exists(p): return []
    return re.findall(r'^import\s+(\S+)', open(p).read(), re.M)
root=sys.argv[1]; seen=set(); st=[root]
while st:
    m=st.pop()
    if m in seen: continue
    seen.add(m); st+=imps(m)
for q in sys.argv[2:]: print(q, q in seen)

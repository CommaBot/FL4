import sys
L=open(sys.argv[1]).read().split('\n')
hdr=[(i,l) for i,l in enumerate(L) if ': error' in l or l.startswith('error:')]
for i,l in hdr[:60]: print(l[:200])
print('====')
for i,l in hdr[:int(sys.argv[2]) if len(sys.argv)>2 else 6]:
  print(l[:200])
  for m in range(i+1,min(i+80,len(L))):
    if ': error' in L[m] or ': warning' in L[m] or L[m].startswith('error:') or L[m].startswith('warning:'): break
    if m-i<6 or L[m].startswith('⊢'): print('   '+L[m][:300])
print(L[-2:])

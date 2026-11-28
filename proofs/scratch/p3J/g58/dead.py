import pickle,re,sys
D,M,K=pickle.load(open('dd.pkl','rb'))
def parent(n):
    # owner source decl for generated constants
    return n
U={}
for n,ds in D.items():
    for d in ds:
        if d!=n and not n.startswith(d+'.'): U.setdefault(d,set()).add(n)
P='Fl4Proofs.P3.Mc.'
dead_tops=[P+'kernel_entry_runMcWKR_sys'+x for x in 'Lo Lq Ls Lt Lu Ly Lz Lza Lzb Lzc Lzd Lze Lzf Lzg Lzh Lzi Lzj Lzk Lzl Lzm Lzn Lzo Lzp Lzq Lzr Lzs Lzt Lzu Lzv Lzw Lzx Li Lj Lr Lzx_of_Lzy Lzy_of_Lzz Lzz_of_Lzy'.split()]
EPT=[n for n in D if M[n]=='Fl4Proofs.P3.P3JEptScope']
protect={'Fl4Proofs.P3.thHard20_ept','Fl4Proofs.P3.midDecStWL29'}
st=list(protect)
while st:
    x=st.pop()
    for d in D[x]:
        if d in EPT and d not in protect: protect.add(d); st.append(d)
for x in list(protect): protect|={n for n in EPT if n.startswith(x+'.')}
pool=set(dead_tops)|{P+'KNo88',P+'KNo88L'}|(set(EPT)-protect)
pool|={n for n in D if re.match(r'Fl4Proofs\.P3\.Mc\.(DispStabFoot\w+|dispStabFoot\w+_of_\w+)$',n)}
def aux(n,dead):
    p=n
    while '.' in p:
        p=p.rsplit('.',1)[0]
        if p in dead: return True
    return False
dead=set(dead_tops)|{P+'KNo88',P+'KNo88L'}|(set(EPT)-protect)
forced=set()
ch=True
while ch:
    ch=False
    for n in D:
        if n in dead: continue
        us=U.get(n,set())
        why=None
        if aux(n,dead): why='aux'
        elif any(d in dead for d in D[n]): why='uses'
        elif us and us<=dead: why='users'
        elif n in pool and K[n]=='ind' and all(u in dead or (u in pool and K[u]=='thm' and not U.get(u)) for u in us): why='poolrec'
        if why:
            dead.add(n); ch=True
            if why=='uses' and n not in pool: forced.add(n)
keep=['sysLzz','sysLzy','sysU','sysUWC','sysLn','runMcWKR_sys','sysLzz_globals_sat','sysLzz_w2','opaqueSysLzz_model','fInitASt_ct_idle','sysLzz_w1_yield','dispStabFootLzx_disch']
print('BAD',[n for n in dead if any(n.endswith('.'+k) for k in keep) or n in protect])
print('FORCED',sorted(forced))
pickle.dump(dead,open('dead.pkl','wb'))
src=[n for n in dead if K[n] in('thm','def','ind','opq') and not re.search(r'\._|\.(rec|recOn|casesOn|mk|noConfusion|noConfusionType|ctorIdx|eq_\d+|eq_def|injEq|inj|sizeOf_spec|_flat_ctor)$|match_|_proof|proof_',n)]
print(len(dead),len(src))
open('dead_src.txt','w').write('\n'.join(sorted(M[n]+'\t'+n+'\t'+K[n] for n in src))+'\n')
# pool survivors
print('POOL LIVE', sorted(n.replace(P,'') for n in pool if n not in dead and K[n] in ('thm','ind') and not re.search(r'\.(rec|mk)$',n)))

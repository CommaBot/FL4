#!/usr/bin/env python3
"""p3J gen 47: generalise XTopJointMRTcbM's `ssp_tailJMM` / `tcb_set_sched_paramsJMM` in place.

The existing proofs move to `ssp_tailJMG` / `tcb_set_sched_paramsJMG` (preempted invariant `Wp`, exits `Xo` / `Xp`,
the post-install steps' relation `Rf` with its step hypotheses, the `MR` frame `hmf` for `MachPlat`); the old
names keep their exact statements (header text byte-identical up to `:=`) and are proved by the new ones.
Run once from proofs/: python3 scratch/p3J/g47/gen.py
"""
import sys
sys.path.insert(0, 'scratch/p3J/g46')
from gen import find_theorem, header_split

F = 'Fl4Proofs/P3/XTopJointMRTcbM.lean'
text = open(F).read()


def rep(s, old, new, n=1):
    c = s.count(old)
    assert c == n, (c, n, old[:120])
    return s.replace(old, new)


JM = '(JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR)'

# the shared new hypotheses (after `hTA`)
NEWH = '''
    (hwp : ∀ kb s a σ G, Wp kb s a σ G → WJP (L := L) arI AR Z H Cs kb s a σ G ∧ Xp s a σ)
    (hRt : ∀ s1 s2 s3 : S, Rf s1 s2 → Rf s2 s3 → Rf s1 s3)
    (hRm : ∀ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A)
      (σ' : Fl4Spec.State Unit), JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' s' a' σ' → ∀ t ∈ Z'.T, ∀ v : U64,
        Rf s' (L.wr s' (mcpA t) v))
    (hRp : ∀ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A)
      (σ' : Fl4Spec.State Unit), JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' s' a' σ' →
        (∀ u, σ'.schedulerAction ≠ .switchThread u) → ∀ t ∈ Z'.T, ∀ v : U64, v.val < 256 →
        (σ'.curThread = t.bv → t.bv ∉ σ'.releaseQueue ∧ ∃ x scp y n, σ'.kheap t.bv = some (.tcb x) ∧
          x.tcbSchedContext = some scp ∧ σ'.kheap scp = some (.schedContext y n) ∧ Fl4Spec.scActive y = true) →
        (t = L.mem s' (L.nodeAt s' (L.cpu s') layout.node.CUR_THREAD) →
          (L.mem s' (P1.inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s' (P1.scA t) ≠ 0#u64 ∧
            L.mem s' (P1.scA t) ∈ Ac') →
        sched.set_priority st s' t v ⦃ s'' => Rf s' s'' ⦄)
    (hRu : ∀ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A)
      (σ' : Fl4Spec.State Unit), JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' s' a' σ' →
        ∀ (t i : U64) (x : Fl4Spec.Tcb), t ∈ Z'.T → i ∈ Z'.C → σ'.kheap t.bv = some (.tcb x) →
        x.tcbSchedContext = some i.bv → (∀ u, σ'.schedulerAction = .switchThread u → u ≠ t.bv) →
        t.bv ≠ σ'.idleThread → schedcontext.unbind_tcb st s' i ⦃ s'' => Rf s' s'' ⦄)
    (hRb : ∀ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A)
      (σ' : Fl4Spec.State Unit), JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' s' a' σ' →
        ∀ (sc t : U64), sc ∈ Z'.C → t ∈ Z'.T → ∀ (y : Fl4Spec.SchedContext) (n : Nat),
        σ'.kheap sc.bv = some (.schedContext y n) → y.scTcb = none → ∀ (xt : Fl4Spec.Tcb),
        σ'.kheap t.bv = some (.tcb xt) → xt.tcbSchedContext = none →
        (Fl4Spec.ipcQueuedThreadState xt.tcbState = true → Fl4Spec.scReleased σ'.curTime y = true) →
        (∀ u, σ'.schedulerAction ≠ .switchThread u) → CurInv σ' → t.bv ≠ σ'.idleThread →
        ∀ (xs ys sb : U64), IsSlot Z'.th xs → capAt (L.mem s') xs = ok (.Thread t) → IsSlot Z'.th ys →
        capAt (L.mem s') ys = ok (.SchedContext sc sb) → sb.val < 64 → n + Fl4Spec.minSchedContextBits = sb.val →
        schedcontext.bind_tcb st arI s' a' sc t ⦃ r => Rf s' r.1 ⦄)
    (hfx : ∀ kb s2 a2 σ2 G2, W kb s2 a2 σ2 G2 → ∀ (G : MdbGhost) (V : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64) (s5 : S) (a5 : A) (σ5 : Fl4Spec.State Unit),
        JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac' Lst' D' s5 a5 σ5 → MR a5 σ5.machineState → Rf s2 s5 →
        Xo s5 a5 σ5)'''

GPARAMS = '''
    {Wp : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}
    {Xo Xp : S → A → Fl4Spec.State Unit → Prop} {Rf : S → S → Prop}'''

HMF = ('(hmf : ∀ (a : A) (σ σ\' : Fl4Spec.State Unit), MR a σ.machineState → MachF.msF σ\' = MachF.msF σ →\n'
       '      MR a σ\'.machineState)')

# ---------------------------------------------------------------- ssp_tail
pre, th, end = find_theorem(text, 'ssp_tailJMM')
old_decl = text[th:end]
hdr, body = header_split(old_decl)
g = hdr
g = rep(g, 'theorem ssp_tailJMM ', 'theorem ssp_tailJMG ')
g = rep(g, '(hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)\n    (hHp : TcbInsWM (L := L) arI AR MR Z H Cs W Rd Rz)\n'
           '    (hmR : MR ar σ.machineState) (hWM : ∀ kb s a σ G, W kb s a σ G → MR a σ.machineState)\n'
           '    (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)',
        '(hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)' + GPARAMS +
        '\n    (hHp : TcbInsWG (L := L) arI AR Z H Cs W Wp Rd Rz)\n'
        '    (hWM : ∀ kb s a σ G, W kb s a σ G → MR a σ.machineState)\n    ' + HMF + ' (hKD : MRKeepD arI MR)')
g = rep(g, '(hAT : P0.ArchTotal arI) (hAK : ARKeep arI AR) (hTA : TimeAgree arI)\n',
        '(hAT : P0.ArchTotal arI) (hAK : ARKeep arI AR) (hTA : TimeAgree arI)' + NEWH + '\n')
g = rep(g, 'TopPostDMXP (L := L) ' + JM + ' σ blk call don m s res', 'TopPostDMXP (L := L) Xo Xp σ blk call don m s res')
b = body
b = rep(b, 'J.restartWM arI hni hsg hP0 hct hHp (hR ct hct)', 'J.restartWG arI hni hsg hP0 hct hHp (hR ct hct)')
b = rep(b, 'install_fhOkJM arI', 'install_fhOkJMp arI')
b = rep(b, 'hPre⟩ := hWp\n', 'hPre⟩ := hwp _ _ _ _ _ hWp\n')
b = rep(b, 'msF_mr hMP', 'hmf _ _ _', 3)
# set_mcp's relation
b = rep(b, '''  obtain ⟨V3, J3⟩ := J2.mcpWrJ hpT hk2 y0 (Fl4Spec.ucast 8 y0.bv)
    (by rw [Ipc.ucast8_specPrio, Sched.specPrio_toNat hy0])
''', '''  obtain ⟨V3, J3⟩ := J2.mcpWrJ hpT hk2 y0 (Fl4Spec.ucast 8 y0.bv)
    (by rw [Ipc.ucast8_specPrio, Sched.specPrio_toNat hy0])
  have hRf3 : Rf s2 (L.wr s2 (mcpA p) y0) := hRm _ _ _ _ _ _ _ J2 p hpT y0
''')
# set_priority's relation
b = rep(b, '''  refine WP.spec_bind (J3.setPrioJS (fun u => hns2 u) hpT y1 hy1 hc3 hp3) ?_
  rintro s4 ⟨σb, hmb, hPF, hSS4, V4, J4⟩
''', '''  refine WP.spec_bind (WP.spec_and (J3.setPrioJS (fun u => hns2 u) hpT y1 hy1 hc3 hp3)
    (hRp _ _ _ _ _ _ _ J3 (fun u => hns2 u) p hpT y1 hy1 hc3 hp3)) ?_
  rintro s4 ⟨⟨σb, hmb, hPF, hSS4, V4, J4⟩, hRf4⟩
''')
# the outcome
b = rep(b, '''      (∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' s5 a5 σc ∧ VxE Z') →
      MR a5 σc.machineState →
      (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a5) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res =>
        TopPostDMXP (L := L) ''' + JM + ''' σ blk call don m s res ⦄ := by
    rintro s5 a5 σc hcc ⟨Z', Ac', Lst', D', J', _⟩ hmr5
    rw [WP.spec_ok]
    refine TopPostDMX.toPne (Or.inr ⟨_, hdec, σ1', hst1, (.ok [], σc), ?_, ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩,
      J'.xtop.rel.1, J'.xtop.rel.2.1, J'.xtop.rel.2.2.1, J'.xtop.rel.2.2.2.1, J'.xtop.rel.2.2.2.2.1⟩,
      ⟨⟨Z', H, Cs, Ac', Lst', D', J', inferInstance⟩, hmr5⟩⟩) (by simp)
''', '''      (∃ (G' : MdbGhost) (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s5 a5 σc) →
      MR a5 σc.machineState → Rf s2 s5 →
      (ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a5) :
        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res =>
        TopPostDMXP (L := L) Xo Xp σ blk call don m s res ⦄ := by
    rintro s5 a5 σc hcc ⟨G', V', Ac', Lst', D', J'⟩ hmr5 hrf5
    rw [WP.spec_ok]
    refine TopPostDMX.toPne (Or.inr ⟨_, hdec, σ1', hst1, (.ok [], σc), ?_, ⟨Z.th, G', Or.inl ⟨rfl, rfl⟩,
      J'.xtop.rel.1, J'.xtop.rel.2.1, J'.xtop.rel.2.2.1, J'.xtop.rel.2.2.2.1, J'.xtop.rel.2.2.2.2.1⟩,
      hfx _ _ _ _ _ hW2 G' V' Ac' Lst' D' s5 a5 σc J' hmr5 hrf5⟩) (by simp)
''')
b = rep(b, 'exact fin s4 a1 σb (Set.mem_singleton _) ⟨_, _, _, _, J4, inferInstance⟩ hMb',
        'exact fin s4 a1 σb (Set.mem_singleton _) ⟨G2, V4, _, _, _, J4⟩ hMb (hRt _ _ _ hRf3 hRf4)')
# unbind
b = rep(b, '''    refine WP.spec_bind (J4.unbindTcbJ hpT hi4C hkb (by rw [hxbsc, hi4c]) (fun u e => absurd e (hnsb u)) hidb) ?_
    rintro s5 ⟨σc, hsc, Ac5, Lst5, D5, J5⟩
    refine fin s5 a1 σc ?_ ⟨_, Ac5, Lst5, D5, J5, inferInstance⟩
''', '''    refine WP.spec_bind (WP.spec_and
      (J4.unbindTcbJ hpT hi4C hkb (by rw [hxbsc, hi4c]) (fun u e => absurd e (hnsb u)) hidb)
      (hRu _ _ _ _ _ _ _ J4 p i4 xb hpT hi4C hkb (by rw [hxbsc, hi4c]) (fun u e => absurd e (hnsb u)) hidb)) ?_
    rintro s5 ⟨⟨σc, hsc, Ac5, Lst5, D5, J5⟩, hRf5⟩
    refine fin s5 a1 σc ?_ ⟨G2, V4, Ac5, Lst5, D5, J5⟩
''')
b = rep(b, '''      (hmf _ _ _ hMb (congrArg Prod.fst (MachT.mtk_schedContextUnbindTcb' _ σb ((), σc) (mem_of_single hsc))))
''', '''      (hmf _ _ _ hMb (congrArg Prod.fst (MachT.mtk_schedContextUnbindTcb' _ σb ((), σc) (mem_of_single hsc))))
      (hRt _ _ _ (hRt _ _ _ hRf3 hRf4) hRf5)
''')
# bind
b = rep(b, '''      hAs.isSlot hT4 hxsS hS4 hsb (hssz yd nd hkbd)) (MKD.schedcontext_bind_tcb L.total hAT hKD hMb)) ?_
    rintro ⟨s5, a5⟩ ⟨⟨σc, hsc, Ac5, Lst5, D5, J5⟩, hm5⟩
''', '''      hAs.isSlot hT4 hxsS hS4 hsb (hssz yd nd hkbd)) (WP.spec_and (MKD.schedcontext_bind_tcb L.total hAT hKD hMb)
      (hRb _ _ _ _ _ _ _ J4 scv p hscvC hpT yd nd hkbd hyd0 xb hkb hxb0 hrelb hnsb hCb hidb _ _ sb
        hAs.isSlot hT4 hxsS hS4 hsb (hssz yd nd hkbd)))) ?_
    rintro ⟨s5, a5⟩ ⟨⟨σc, hsc, Ac5, Lst5, D5, J5⟩, hm5, hRf5⟩
''')
b = rep(b, '''    refine fin s5 a5 σc ?_ ⟨_, Ac5, Lst5, D5, J5, inferInstance⟩
      (hmf _ _ _ hm5 (congrArg Prod.fst (MachT.mtk_schedContextBindTcbG _ _ σb ((), σc) (mem_of_single hsc))))
''', '''    refine fin s5 a5 σc ?_ ⟨G2, V4, Ac5, Lst5, D5, J5⟩
      (hmf _ _ _ hm5 (congrArg Prod.fst (MachT.mtk_schedContextBindTcbG _ _ σb ((), σc) (mem_of_single hsc))))
      (hRt _ _ _ (hRt _ _ _ hRf3 hRf4) hRf5)
''')
ssp_doc = ('/-- (p3J gen 47) **`ssp_tailJMM` with the preempted invariant `Wp`, the exits `Xo` / `Xp` and the '
           'post-install\nsteps\' relation `Rf` as parameters** (`hRm` / `hRp` / `hRu` / `hRb`: `set_mcp`, '
           '`set_priority`, `unbind_tcb`,\n`bind_tcb` relate their states by `Rf`; `hfx`: the final state\'s '
           '`Xo` from the install\'s `W`, the final `JAtZ`,\n`MR` and `Rf`; `hmf`: `MachPlat`\'s `MR` frame). '
           '`ssp_tailJMM` is the `WJPM` / `JAtM` / `JAtPreMV` / `True`\ninstance. -/\n')
ssp_new = 'set_option maxHeartbeats 32000000 in\n' + ssp_doc + g + b
ssp_corr = (hdr + '\n  ssp_tailJMG arI s ar σ J hni hsg hP0 (Rf := fun _ _ => True) (hHp.toG arI) hWM\n'
            '    (fun _ _ _ h e => msF_mr hMP h e) hKD hR hAT hAK hTA (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ => trivial)\n'
            '    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)\n'
            '    (fun _ _ _ _ _ _ _ J hna _ ht v hv hc hp => WP.spec_mono (J.setPrioJS hna ht v hv hc hp) fun _ _ => trivial)\n'
            '    (fun _ _ _ _ _ _ _ J _ _ _ ht hi hk hsp hsa hid =>\n'
            '      WP.spec_mono (J.unbindTcbJ ht hi hk hsp hsa hid) fun _ _ => trivial)\n'
            '    (fun _ _ _ _ _ _ _ J _ _ hsC ht _ _ hk hy0 _ hkt hxt0 hrel hnsw hC htid _ _ _ hxS hxc hyS hyc hsb hssz =>\n'
            '      WP.spec_mono (J.bindTcbJ hAT hAK hTA hsC ht hk hy0 hkt hxt0 hrel hnsw hC htid hxS hxc hyS hyc hsb hssz)\n'
            '        fun _ _ => trivial)\n'
            '    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ J\' hmr _ => ⟨⟨_, H, Cs, _, _, _, J\', inferInstance⟩, hmr⟩)\n'
            '    p hp ct hct ssl hAs hpsl x2 e2 hxe2 he21 ps hps hps1 hv y0 y1 scv hy0 hy1 scf q sco h1 h2 h3 hD hpI hscs m hdec\n'
            '    blk call don\n')
# keep the old prefix (set_option + docstring) for the corollary but drop its heartbeat line
old_pre = text[pre:th]
old_pre_c = old_pre.replace('set_option maxHeartbeats 32000000 in\n', '')
text = text[:pre] + ssp_new + '\n' + old_pre_c + ssp_corr + '\n' + text[end:]

# ---------------------------------------------------------------- tcb_set_sched_params
pre, th, end = find_theorem(text, 'tcb_set_sched_paramsJMM')
old_decl = text[th:end]
hdr, body = header_split(old_decl)
g = hdr
g = rep(g, 'theorem tcb_set_sched_paramsJMM ', 'theorem tcb_set_sched_paramsJMG ')
g = rep(g, '(hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)\n    (hHp : TcbInsWM (L := L) arI AR MR Z H Cs W Rd Rz)\n'
           '    (hmR : MR ar σ.machineState) (hWM : ∀ kb s a σ G, W kb s a σ G → MR a σ.machineState)\n'
           '    (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR)',
        '(hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)' + GPARAMS +
        '\n    (hHp : TcbInsWG (L := L) arI AR Z H Cs W Wp Rd Rz) (hX0 : Xo s ar σ)\n'
        '    (hWM : ∀ kb s a σ G, W kb s a σ G → MR a σ.machineState)\n    ' + HMF + ' (hKD : MRKeepD arI MR)')
g = rep(g, '(hAT : P0.ArchTotal arI) (hAK : ARKeep arI AR) (hTA : TimeAgree arI)\n',
        '(hAT : P0.ArchTotal arI) (hAK : ARKeep arI AR) (hTA : TimeAgree arI)' + NEWH + '\n')
g = rep(g, 'TcbOKXP (L := L) arI ' + JM + ' s ar σ', 'TcbOKXP (L := L) arI Xo Xp s ar σ')
b = body
b = rep(b, '  have hJ0 : JAtM (L := L) arI AR MR s ar σ := ⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hmR⟩\n',
        '  have hJ0 : Xo s ar σ := hX0\n')
b = rep(b, 'TopPostDMXP (L := L) ' + JM + ' σ', 'TopPostDMXP (L := L) Xo Xp σ', 4)
b = rep(b, 'ssp_tailJMM arI s ar σ J hni hsg hP0 hHp hmR hWM hMP hKD hRs hAT hAK hTA p',
        'ssp_tailJMG arI s ar σ J hni hsg hP0 hHp hWM hmf hKD hRs hAT hAK hTA hwp hRt hRm hRp hRu hRb hfx p', 2)
tsp_doc = ('/-- (p3J gen 47) **`tcb_set_sched_paramsJMM` with the preempted invariant `Wp`, the exits `Xo` (start, '
           'Ok) / `Xp`\n(preempted) and the post-install steps\' relation `Rf` as parameters** (as `ssp_tailJMG`; '
           '`tcb_set_sched_paramsJMM` is\nthe `WJPM` / `JAtM` / `JAtPreMV` / `True` instance). -/\n')
tsp_new = 'set_option maxHeartbeats 8000000 in\n' + tsp_doc + g + b
tsp_corr = (hdr + '\n  tcb_set_sched_paramsJMG arI s ar σ J hni hsg hP0 (Rf := fun _ _ => True) (hHp.toG arI)\n'
            '    ⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hmR⟩ hWM\n'
            '    (fun _ _ _ h e => msF_mr hMP h e) hKD hRs hAT hAK hTA (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ => trivial)\n'
            '    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)\n'
            '    (fun _ _ _ _ _ _ _ J hna _ ht v hv hc hp => WP.spec_mono (J.setPrioJS hna ht v hv hc hp) fun _ _ => trivial)\n'
            '    (fun _ _ _ _ _ _ _ J _ _ _ ht hi hk hsp hsa hid =>\n'
            '      WP.spec_mono (J.unbindTcbJ ht hi hk hsp hsa hid) fun _ _ => trivial)\n'
            '    (fun _ _ _ _ _ _ _ J _ _ hsC ht _ _ hk hy0 _ hkt hxt0 hrel hnsw hC htid _ _ _ hxS hxc hyS hyc hsb hssz =>\n'
            '      WP.spec_mono (J.bindTcbJ hAT hAK hTA hsC ht hk hy0 hkt hxt0 hrel hnsw hC htid hxS hxc hyS hyc hsb hssz)\n'
            '        fun _ _ => trivial)\n'
            '    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ J\' hmr _ => ⟨⟨_, H, Cs, _, _, _, J\', inferInstance⟩, hmr⟩)\n'
            '    p hp slbl hlbl length buf ct hct args hlen hargs hpI hstall call ssl hAs hpsl extra x0 x1 x2 hx0 hx1 hx2\n'
            '    excaps hXc hcapT hcapC blk don ci buffer\n')
old_pre = text[pre:th]
old_pre_c = old_pre.replace('set_option maxHeartbeats 8000000 in\n', '')
text = text[:pre] + tsp_new + '\n' + old_pre_c + tsp_corr + '\n' + text[end:]

# the module docstring
text = rep(text, '''`ssp_tailJMM` / `tcb_set_sched_paramsJMM` are unchanged (their post-install steps build `JAtM` directly).
-/''', '''`ssp_tailJMM` / `tcb_set_sched_paramsJMM` are unchanged (their post-install steps build `JAtM` directly).
(p3J gen 47) `ssp_tailJMG` / `tcb_set_sched_paramsJMG`: the same with `Wp`, `Xo` / `Xp`, `MachPlat`'s `MR` frame as a
parameter `hmf`, and a relation `Rf` between the fault handler's install state and the final state, with its step
hypotheses for `set_mcp` / `set_priority` / `unbind_tcb` / `bind_tcb` (`hRm` / `hRp` / `hRu` / `hRb`, transitivity
`hRt`) and the Ok exit `hfx`; `ssp_tailJMM` / `tcb_set_sched_paramsJMM` keep their statements as the `WJPM` /
`JAtM` / `JAtPreMV` / `Rf := True` instances.
-/''')
open(F, 'w').write(text)
print('ok')

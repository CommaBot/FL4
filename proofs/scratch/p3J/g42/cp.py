src=open('Fl4Proofs/P3/XTopJointCopyRegs.lean').read()
def cut(s,a,b):
    i=s.index(a); j=s.index(b,i); return s[i:j]
def rep(s,R):
    for a,b in R:
        assert s.count(a)==1,(a[:80],s.count(a))
        s=s.replace(a,b)
    return s
loop=cut(src,'theorem crJ_loop {a : A}','set_option maxHeartbeats 8000000 in\n/-- **The tail of `copy_registers` at `J`**')
tail=cut(src,'theorem JAtZ.crTailJ {a : A}','\nend\n\nsection')
cr=cut(src,'theorem JAtZ.copyRegsJ (hAT','\nend\n\nend\n\nend Fl4Proofs.P3')
loop=rep(loop,[
('theorem crJ_loop {a : A}','theorem crJ_loopW {a : A}'),
("""    loop (fun (x : S × U64) => body x.1 x.2) (s0, 0#u64) ⦃ s' => ∃ σ',""","""    loop (fun (x : S × U64) => body x.1 x.2) (s0, 0#u64) ⦃ s' => P1.WritesIn st s0 s' (RcvReg dest) ∧ ∃ σ',"""),
("""    (inv := fun x => x.2.val ≤ Lr.length ∧ ∃ σ',""","""    (inv := fun x => x.2.val ≤ Lr.length ∧ P1.WritesIn st s0 x.1 (RcvReg dest) ∧ ∃ σ',"""),
("""  · rintro ⟨s', i⟩ ⟨hi, σ', hm, V', J'⟩
    simp only at hi hm J' ⊢""","""  · rintro ⟨s', i⟩ ⟨hi, hw', σ', hm, V', J'⟩
    simp only at hi hw' hm J' ⊢"""),
("""      exact ⟨σ', hm, V', J'⟩""","""      exact ⟨hw', σ', hm, V', J'⟩"""),
("""    refine ⟨⟨by show i3.val ≤ Lr.length; omega, _, ?_, V2, J2⟩,""","""    refine ⟨⟨by show i3.val ≤ Lr.length; omega, wr_regW (J'.ip.e.tcb dest hd) Lr[i.val] w hw', _, ?_, V2, J2⟩,"""),
("""  · exact ⟨by simp, σ0, by simp; rfl, Z.vs, by simpa using J⟩""","""  · exact ⟨by simp, P1.WritesIn.refl _ _, σ0, by simp; rfl, Z.vs, by simpa using J⟩"""),
])
tail=rep(tail,[
('theorem JAtZ.crTailJ {a : A}','theorem JAtZ.crTailJW {a : A}'),
("""      r.1 = .Ok () ∧ r.2.2 = a ∧ ∃ σ', (do""","""      r.1 = .Ok () ∧ r.2.2 = a ∧ P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ∧ ∃ σ', (do"""),
("""  have hpm : tcb.post_modify_registers st s dest ⦃ s4 => ∃ ct : U64,""","""  have hpm : tcb.post_modify_registers st s dest ⦃ s4 => P1.WritesIn st s s4 (Mc.ProjW (L := L) H Cs s) ∧ ∃ ct : U64,"""),
("""      refine ⟨dest, hct.symm, σ, ?_, hct.symm, Z.vs, by simpa using J⟩""","""      refine ⟨P1.WritesIn.refl _ _, dest, hct.symm, σ, ?_, hct.symm, Z.vs, by simpa using J⟩"""),
("""      refine ⟨ct, hct.symm, _, ?_, by simp [Notif.updK, hct],""","""      refine ⟨J.regProjW hd .errorRegister s 0#u64, ct, hct.symm, _, ?_, by simp [Notif.updK, hct],"""),
("""  rintro s4 ⟨ct, hct, σ4, hpm4, hct4, V4, J4⟩""","""  rintro s4 ⟨hW4, ct, hct, σ4, hpm4, hct4, V4, J4⟩"""),
("""    rw [hrun, bind_ok, WP.spec_ok]
    exact ⟨rfl, rfl, σ6,""","""    have hW6 := J4.reschedProjW
    rw [hrun, WP.spec_ok] at hW6
    rw [hrun, bind_ok, WP.spec_ok]
    exact ⟨rfl, rfl, hW4.projW_trans hW6, σ6,"""),
("""    exact ⟨trivial, trivial, σ4, hfin σ4 (by""","""    exact ⟨trivial, trivial, hW4, σ4, hfin σ4 (by"""),
])
cr=rep(cr,[
('theorem JAtZ.copyRegsJ (hAT','theorem JAtZ.copyRegsJW (hAT'),
("""    tcb.copy_registers st arI s a dest src flags ⦃ r => r.1 = .Ok () ∧ r.2.2 = a ∧ ∃ σ',""",
 """    tcb.copy_registers st arI s a dest src flags ⦃ r => r.1 = .Ok () ∧ r.2.2 = a ∧
      P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ∧ ∃ σ',"""),
("""  have h1 : (if b0 = true then sched.suspend st arI s a src else ok (s, a)) ⦃ r => r.2 = a ∧ ∃ σ1,""",
 """  have h1 : (if b0 = true then sched.suspend st arI s a src else ok (s, a)) ⦃ r => r.2 = a ∧
      P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ∧ ∃ σ1,"""),
("""      exact ⟨trivial, σ, rfl, hns, Z.vs, Ac, Lst, by simpa using J⟩""","""      exact ⟨trivial, P1.WritesIn.refl _ _, σ, rfl, hns, Z.vs, Ac, Lst, by simpa using J⟩"""),
("""      refine WP.spec_mono (J.suspendJD hSd hNt hRv hRp hsT (fun u e => (hns u e).elim) hsI) ?_
      rintro r ⟨h1, σ1, h2, V, Ac', Lst', J'⟩
      exact ⟨h1, σ1,""","""      refine WP.spec_mono (WP.spec_and (J.suspendJD hSd hNt hRv hRp hsT (fun u e => (hns u e).elim) hsI)
        (J.suspendProjW hsT)) ?_
      rintro r ⟨⟨h1, σ1, h2, V, Ac', Lst', J'⟩, hW⟩
      exact ⟨h1, hW, σ1,"""),
("""  rintro ⟨s1, a1⟩ ⟨ha1, σ1, hm1, hns1, V1, Ac1, Lst1, J1⟩""","""  rintro ⟨s1, a1⟩ ⟨ha1, Wa, σ1, hm1, hns1, V1, Ac1, Lst1, J1⟩"""),
("""  have h2 : (if b1 = true then sched.restart st arI s1 a dest else ok (s1, a)) ⦃ r => r.2 = a ∧ ∃ σ2,""",
 """  have h2 : (if b1 = true then sched.restart st arI s1 a dest else ok (s1, a)) ⦃ r => r.2 = a ∧
      P1.WritesIn st s1 r.1 (Mc.ProjW (L := L) H Cs s1) ∧ ∃ σ2,"""),
("""      exact ⟨trivial, σ1, rfl, V1, Ac1, Lst1, D, J1⟩""","""      exact ⟨trivial, P1.WritesIn.refl _ _, σ1, rfl, V1, Ac1, Lst1, D, J1⟩"""),
("""      refine WP.spec_mono hrs ?_
      rintro r ⟨h1, σ2, h2, hJ⟩
      exact ⟨h1, σ2,""","""      refine WP.spec_mono (WP.spec_and hrs (J1.restartProjW hAT hdT)) ?_
      rintro r ⟨⟨h1, σ2, h2, hJ⟩, hW⟩
      exact ⟨h1, hW, σ2,"""),
("""  rintro ⟨s2, a2⟩ ⟨ha2, σ2, hm2, V2, Ac2, Lst2, D2, J2⟩""","""  rintro ⟨s2, a2⟩ ⟨ha2, Wb, σ2, hm2, V2, Ac2, Lst2, D2, J2⟩"""),
("""      (∀ s' σ', JAtV (L := L) arI AR Z H Cs s' a σ' → lp s' ⦃ s'' => ∃ σ'',""",
 """      (∀ s' σ', JAtV (L := L) arI AR Z H Cs s' a σ' → lp s' ⦃ s'' => P1.WritesIn st s' s'' (Mc.ProjW (L := L) H Cs s') ∧
        ∃ σ'',"""),
("""      r.1 = .Ok () ∧ r.2.2 = a ∧ ∃ σ', (do
        Fl4Spec.NonDet.when (b3 = true)""","""      r.1 = .Ok () ∧ r.2.2 = a ∧ P1.WritesIn st s3 r.2.1 (Mc.ProjW (L := L) H Cs s3) ∧ ∃ σ', (do
        Fl4Spec.NonDet.when (b3 = true)"""),
("""      refine WP.spec_mono (J3.crTailJ hdT) ?_
      rintro r ⟨h1, h2, σ', h3, h4⟩
      refine ⟨h1, h2, σ', ?_, by rw [h2]; exact h4⟩
      rw [nd_bind_one (show Fl4Spec.NonDet.when (false = true)""","""      refine WP.spec_mono (J3.crTailJW hdT) ?_
      rintro r ⟨h1, h2, hW, σ', h3, h4⟩
      refine ⟨h1, h2, hW, σ', ?_, by rw [h2]; exact h4⟩
      rw [nd_bind_one (show Fl4Spec.NonDet.when (false = true)"""),
("""      rintro s5 ⟨σ5, hm5, V5, Ac5, Lst5, D5, J5⟩
      refine WP.spec_mono (J5.crTailJ hdT) ?_
      rintro r ⟨h1, h2, σ', h3, h4⟩
      refine ⟨h1, h2, σ', ?_, by rw [h2]; exact h4⟩""","""      rintro s5 ⟨hW5, σ5, hm5, V5, Ac5, Lst5, D5, J5⟩
      refine WP.spec_mono (J5.crTailJW hdT) ?_
      rintro r ⟨h1, h2, hW, σ', h3, h4⟩
      refine ⟨h1, h2, hW5.projW_trans hW, σ', ?_, by rw [h2]; exact h4⟩"""),
("""      ∀ s' σ', JAtV (L := L) arI AR Z H Cs s' a σ' → loop (fun (x : S × U64) => body x.1 x.2) (s', 0#u64) ⦃ s'' =>
        ∃ σ'',""","""      ∀ s' σ', JAtV (L := L) arI AR Z H Cs s' a σ' → loop (fun (x : S × U64) => body x.1 x.2) (s', 0#u64) ⦃ s'' =>
        P1.WritesIn st s' s'' (Mc.ProjW (L := L) H Cs s') ∧ ∃ σ'',"""),
("""    fun body hbody s' σ' ⟨V', Ac', Lst', D', J'⟩ => WP.spec_mono (crJ_loop (Z := Z.mv Z.G V') regs.GP_REGISTERS
      tcb.N_GP Fl4Spec.gpRegisters hgr (by unfold tcb.N_GP; rfl) (by decide) hsT hdT body hbody J')
      fun _ ⟨σ'', hm, V'', J''⟩ => ⟨σ'', hm, V'', Ac', Lst', D', J''⟩""",
 """    fun body hbody s' σ' ⟨V', Ac', Lst', D', J'⟩ => WP.spec_mono (crJ_loopW (Z := Z.mv Z.G V') regs.GP_REGISTERS
      tcb.N_GP Fl4Spec.gpRegisters hgr (by unfold tcb.N_GP; rfl) (by decide) hsT hdT body hbody J')
      fun _ ⟨hW, σ'', hm, V'', J''⟩ => ⟨hW.mono fun _ hb => J'.rcvRegProjW hdT hb, σ'', hm, V'', Ac', Lst', D', J''⟩"""),
("""    rintro r ⟨h1, h2, σ', h3, h4⟩
    exact ⟨h1, h2, σ', hspec σ2 σ' rfl h3, h4⟩""","""    rintro r ⟨h1, h2, hW, σ', h3, h4⟩
    exact ⟨h1, h2, Wa.projW_trans (Wb.projW_trans hW), σ', hspec σ2 σ' rfl h3, h4⟩"""),
("""    have hl0 := crJ_loop (Z := Z.mv Z.G V2)""","""    have hl0 := crJ_loopW (Z := Z.mv Z.G V2)"""),
("""    rintro s3 ⟨σ3, hm3, V3, J3⟩""","""    rintro s3 ⟨hw3, σ3, hm3, V3, J3⟩
    have Wc : P1.WritesIn st s2 s3 (Mc.ProjW (L := L) H Cs s2) := hw3.mono fun _ hb => J2.rcvRegProjW hdT hb"""),
("""    rw [hNx]
    obtain ⟨V4, J4⟩""","""    rw [hNx]
    have Wd := J3.regProjW hdT .nextIP s3 pc
    obtain ⟨V4, J4⟩"""),
("""    rintro r ⟨h1, h2, σ', h3, h4⟩
    refine ⟨h1, h2, σ', hspec _ σ' ?_ h3, h4⟩""","""    rintro r ⟨h1, h2, hW, σ', h3, h4⟩
    refine ⟨h1, h2, Wa.projW_trans (Wb.projW_trans (Wc.projW_trans (Wd.projW_trans hW))), σ', hspec _ σ' ?_ h3, h4⟩"""),
])
t=open('Fl4Proofs/P3/StallNarrowTcb.lean').read()
leaf=cut(t,'theorem tcb_copy_regsJT (hAT','\n\n\nset_option')
leaf=rep(leaf,[
('theorem tcb_copy_regsJT (hAT','theorem tcb_copy_regsJTSt (hAT'),
("""    TcbOKX (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.TCBCopyRegisters p
      ⟨length, buf, call, cslotAddr ssl, extra⟩""","""    TcbOKX (L := L) arI (fun s1 a1 σ1 => JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧
        P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) s ar σ fl4_abi.label.TCBCopyRegisters p
      ⟨length, buf, call, cslotAddr ssl, extra⟩"""),
("""  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩""",
 """  have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ ∧ P1.WritesIn st s s (Mc.ProjW (L := L) H Cs s) :=
    ⟨J.stab, P1.WritesIn.refl _ _⟩
  have hctT : ct ∈ Z.T := J.thT ct (J.xtop.curTcb hcur).1"""),
("""        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMX (L := L) (JAt (L := L) arI AR) σ blk""",
 """        Result (core.result.Result Unit error.Exc × S × A)) ⦃ res => TopPostDMX (L := L) (fun s1 a1 σ1 =>
          JStab (L := L) arI AR Z H Cs s1 a1 σ1 ∧ P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s)) σ blk"""),
("""    obtain ⟨s1, σ1, x, hrc1, hst, hk, -, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
""","""    obtain ⟨s1, σ1, x, hrc1, hst, hk, -, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    have W1 : P1.WritesIn st s s1 (Mc.ProjW (L := L) H Cs s) := by
      have h := stsProjW J hctT sched.TS_RESTART
      rw [hs1, WP.spec_ok] at h; exact h
"""),
("""    refine WP.spec_mono ((J1.undead hAs.isSlot hcap1 hpT).copyRegsJ hAT""","""    refine WP.spec_mono ((J1.undead hAs.isSlot hcap1 hpT).copyRegsJW hAT"""),
("""    rintro ⟨r2, s2, a2⟩ ⟨hr2, -, σ', hsp, V', Ac', Lst', D', J2⟩""","""    rintro ⟨r2, s2, a2⟩ ⟨hr2, -, W2, σ', hsp, V', Ac', Lst', D', J2⟩"""),
("""      J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac', Lst', D', J2, inferInstance⟩⟩""",
 """      J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.rel.2.2.2.2.1⟩, ⟨⟨_, _, Ac', Lst', D', J2⟩, W1.projW_trans W2⟩⟩"""),
])
open('scratch/p3J/g41/cp_parts.txt','w').write('\n=====\n'.join([loop,tail,cr,leaf]))
print('ok')

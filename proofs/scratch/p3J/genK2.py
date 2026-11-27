# gen 10: writes Fl4Proofs/P3/P3KGen1.lean (stage-1 transport), P3KFin.lean (hand), P3KGen.lean (stage 2)
import re
P='Fl4Proofs/P3/'
STOP=re.compile(r'^(/--|set_option|theorem |def |structure |end\b|variable|section|-- =====|@\[)')
def block(f, thm):
    L=open(P+f).read().split('\n')
    i=[k for k,l in enumerate(L) if l.startswith('theorem '+thm+' ')]
    assert len(i)==1,(f,thm,i); i=i[0]
    s=i
    while s>0 and not L[s-1].strip()=='' : s-=1      # include doc/set_option above
    e=i+1
    while e<len(L) and not STOP.match(L[e]): e+=1
    while L[e-1].strip()=='': e-=1
    return '\n'.join(L[s:e])
def subs(b,pairs,count1=True):
    for x,y,n in pairs:
        c=b.count(x); assert c==n,(x,c,n); b=b.replace(x,y)
    return b
AS=('(hA : ArchSwF st arI Z.N Z.T Z.C Z.c)',"(hA : ArchSwF' st arI Z.N Z.T Z.C Z.c)",1)
FO=('(hFO : FpuOwnOK σ)','(hFO : FinRootI arI AR σ)',1)
# --- WP0FZR: statement copied, new proof on the g7e chain
w=block('XTopJointJAtZRB.lean','jat_scheduleWP0FZR')
st,_=w.split(':= by\n',1)
st=subs(st,[('theorem jat_scheduleWP0FZR ','theorem jat_scheduleWP0FZRI ',1),AS,FO])
st=st.replace('set_option maxHeartbeats 2000000 in','set_option maxHeartbeats 4000000 in',1)
wbody=''':= by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hB := J.blk
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hSt : P0.StoreTotal st := P1.LawfulStore.total
  obtain ⟨⟨s1, a1⟩, hfr, ⟨σ1, V1, Ac1, Lst1, D1, h1, hd1, J1⟩, hk⟩ :=
    spec_exists (WP.spec_and (J.fireJ P hP hSig) (P1.timer.fire.kw hAT (P1.ibKeep_holds hAT) hNt s a hB J.bufAtJ))
  simp only [WP.uncurry'_pair] at hk
  have hfire : timer.fire st arI s a ⦃ r => ∃ σ1', Fires σ σ1' ∧ SchedRel st Z.N Z.T Z.C Z.c r.1 σ1' ∧
      NtfnStateRel Z.N Z.T (L.mem r.1) σ1' ∧ NSC Z.N Z.C σ1' ∧ SchedPreW0R Z.T Z.C σ1' ∧
      ((σ1'.domainTime ≠ 0 ∨ NdOK (L := L) r.1 σ1') ∧
        (∀ n ∈ Z.N, n.val + 40 ≤ (L.ksb r.1).val ∨ (L.ksb r.1).val + 13568 ≤ n.val) ∧
        ((((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
          JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 r.1 r.2 σ1') ∧
          timer.fire st arI s a = ok r ∧ L.ksb r.1 = L.ksb s ∧ FpuOwnOK σ1') ∧ VsRootOK Z.T σ1' ∧
          (RootFr (L := L) AR Z.T (Z.mv Z.G V1).P Z.c r.1 r.2 σ1' ∧ AR r.2 σ1'.archState.x64CurrentCr3)))) ⦄ := by
    rw [hfr, WP.spec_ok]
    exact ⟨σ1, h1, J1.xtop.fin.1.1.1, J1.xtop.fin.1.1.2.2.1, J1.nsc, ⟨J1.inv, J1.cur, J1.off, J1.act, J1.own⟩,
      hd.imp (fun h => by rw [hd1]; exact h) (fun h => J.ndOK_fire h hk (fun b hb o ho h8 => (J.bufAtJ.1 b hb).ks o ho h8) h1), J1.nk,
      ⟨⟨V1, Ac1, Lst1, D1, J1⟩, rfl, hk.1, fpuOwnOK_firesZR J h1 J1.xtop.fin.1.1.2.2.1 hFO.fo⟩, J1.vsRootOK,
      J1.rootFr (J.idleVt_fire hAT hFO.rr.idle hfr h1 J1), J1.xtop.fin.1.1.2.2.2.2.2.2⟩
  refine WP.spec_mono (Fl4ProofsK.P3.Sched.schedule_refinesWP0FRA hFO.rr.ref hSt hAT hFO.rr.keep s a σ hS hR J.nsc hnd
    hfire (fun _ _ h => h.1.2.2.2) (fun _ _ h => h.2.1) (fun _ _ h => h.2.2) hA hAN hsni hsend hT) ?_
  rintro r ⟨σ1', σ', hF', hsc, h2, h3, h4, h5, h6, h7, rf, hPf, hw, σ3, h8, h9, h10, -⟩
  exact ⟨σ1', σ', hF', hsc, h2, h3, h4, h5, h6, h7, rf, hPf.1, hw, σ3, h8, h9, h10⟩'''
wp=st+wbody
fr=subs(block('XTopJointJAtZRB.lean','jat_scheduleFR2ZR'),[('theorem jat_scheduleFR2ZR ','theorem jat_scheduleFR2ZRI ',1),AS,FO,
   ('(jat_scheduleWP0FZR s a σ','(jat_scheduleWP0FZRI s a σ',1)])
sr=subs(block('XTopJointJAtZRB.lean','jat_scheduleSR2ZRP'),[('theorem jat_scheduleSR2ZRP ','theorem jat_scheduleSR2ZRPI ',1),AS,FO,
   ('  jat_scheduleFR2ZR s a σ','  jat_scheduleFR2ZRI s a σ',1)])
jp=subs(block('XTopJointKEntry4.lean','jat_finishJRP'),[('theorem jat_finishJRP ','theorem jat_finishJRPI ',1),AS,FO,
   ('(jat_scheduleSR2ZRP s a σ','(jat_scheduleSR2ZRPI s a σ',1)])
jn=subs(block('XTopJointKEntry28.lean','jat_finishJRN'),[('theorem jat_finishJRN ','theorem jat_finishJRNI ',1),AS,FO,
   ('  jat_finishJRP s a σ','  jat_finishJRPI s a σ',1)])
jm=subs(block('XTopJointKEntry36.lean','jat_finishJRNM'),[('theorem jat_finishJRNM ','theorem jat_finishJRNMQI ',1),AS,FO,
   ('(jat_finishJRN s a σ','(jat_finishJRNI s a σ',1),('(hM : MachPlat arI MR)','(hM : MachPlatT arI MR)',1),('msF_mr hM','msF_mrT hM',1)])
open('scratch/p3J/_k2_blocks.lean','w').write('\n\n'.join([wp,fr,sr,jp,jn,jm]))

# ---------- records and conversions
def sblock(f,name):
    L=open(P+f).read().split('\n')
    i=[k for k,l in enumerate(L) if l.startswith('structure '+name+' ')]; assert len(i)==1; i=i[0]
    e=i+1
    while e<len(L) and L[e].strip()!='': e+=1
    return '\n'.join(L[i:e])
ARCH=('  arch : ArchSwF st arI Z.N Z.T Z.C Z.c',"  arch : ArchSwF' st arI Z.N Z.T Z.C Z.c",1)
RR='\n  /-- [J] the idle TCB\'s vtable (`IdleVt`, from `KFinAtR8.idle`) and the arch premises `ArchRefines` [P] /\n  `ARKeep` the g7e scheduler chain needs, carried to the old finish lemmas. -/\n  rr : FinRootR arI AR σ'
r5=subs(sblock('XTopJointKEntryU5.lean','KFinAtR5'),[('structure KFinAtR5 ','structure KFinAtR5I ',1),ARCH])+RR
r31=subs(sblock('XTopJointKEntry31.lean','KFinAtR31'),[('structure KFinAtR31 ','structure KFinAtR31I ',1),ARCH])+RR
r27=subs(sblock('XTopJointKEntry27.lean','KFinAtR27'),[('structure KFinAtR27 ','structure KFinAtR27I ',1),ARCH])+RR
rR=subs(sblock('XTopJointKEntry4.lean','KFinAtR'),[('structure KFinAtR ','structure KFinAtRI ',1),ARCH,('  fo : FpuOwnOK σ','  fo : FinRootI arI AR σ',1)])
c5=subs(block('G7eTail.lean','KFinAtR8.to5'),[('theorem KFinAtR8.to5 ','theorem KFinAtR8.to5I ',1),
  ('(F : KFinAtR8 (L := L)','(F : Fl4ProofsK.P3.SInvR.G5.KFinAtR8 (L := L)',1),('KFinAtR5 (L := L)','KFinAtR5I (L := L)',1),
  ('kfin_tail_of J','Fl4ProofsK.P3.SInvR.G5.kfin_tail_of J',1),('hT hFO F.idle⟩','hT hFO F.idle, ⟨F.idle, hRef, hK⟩⟩',1)])
c31=subs(block('XTopJointKEntryU5.lean','KFinAtR5.to31'),[('theorem KFinAtR5.to31 ','theorem KFinAtR5I.to31I ',1),
  ('(F : KFinAtR5 (L := L)','(F : KFinAtR5I (L := L)',1),('KFinAtR31 (L := L)','KFinAtR31I (L := L)',1),('F.tail⟩','F.tail, F.rr⟩',1)])
c27=subs(block('XTopJointKEntry31.lean','KFinAtR31.to27'),[('theorem KFinAtR31.to27 ','theorem KFinAtR31I.to27I ',1),
  ('(F : KFinAtR31 (L := L)','(F : KFinAtR31I (L := L)',1),('KFinAtR27 (L := L)','KFinAtR27I (L := L)',1),('F.tail⟩','F.tail, F.rr⟩',1)])
cR=subs(block('XTopJointKEntry27.lean','KFinAtR27.toR'),[('theorem KFinAtR27.toR ','theorem KFinAtR27I.toRI ',1),
  ('(F : KFinAtR27 (L := L)','(F : KFinAtR27I (L := L)',1),('KFinAtR (L := L)','KFinAtRI (L := L)',1),('F.archNd, fo,','F.archNd, ⟨fo, F.rr⟩,',1)])
OPEN='open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched'
VE='variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)'
VI='variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}'
head=open('scratch/p3J/P3KFin.head').read()
out=head+f'''
import Fl4Proofs.P3.P3KGen1
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
{OPEN}
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
{VE}

/-- **The root facts of a finish state** the g7e scheduler chain needs (module docstring). -/
structure FinRootR (AR : A → Fl4Spec.Cr3 → Prop) (σ : Fl4Spec.State Unit) : Prop where
  /-- [J] `IdleVt` (INV-PLAN §1.U3L D7). -/
  idle : IdleVt σ
  /-- [P] `ArchRefines` (A15). -/
  ref : ArchRefines arI AR
  /-- [P] `ARKeep`. -/
  keep : ARKeep arI AR

/-- **`FpuOwnOK σ` with the root facts**: the old finish record's `fo`. -/
structure FinRootI (AR : A → Fl4Spec.Cr3 → Prop) (σ : Fl4Spec.State Unit) : Prop where
  /-- [J] the FPU owner is a TCB. -/
  fo : FpuOwnOK σ
  rr : FinRootR arI AR σ

{r31}

{r27}

{rR}

end

theorem msF_mrT {{A : Type}} {{arI : machine.Arch A}} {{MR : A → Fl4Spec.MachineState → Prop}} (hM : MachPlatT arI MR)
    {{a : A}} {{σ σ' : Fl4Spec.State Unit}} (hR : MR a σ.machineState) (h : MachF.msF σ' = MachF.msF σ) :
    MR a σ'.machineState := by
  simp only [MachF.msF, Prod.mk.injEq] at h
  exact hM.frame a _ _ hR h.1 h.2.1 h.2.2.1 h.2.2.2.1

section
{VI}
variable {{AR : A → Fl4Spec.Cr3 → Prop}}

{wp}

{fr}

{sr}

{jp}

{jn}

end

section
{VI}
variable {{AR : A → Fl4Spec.Cr3 → Prop}} {{MR : A → Fl4Spec.MachineState → Prop}}

{jm}

end

section
{VI}

{c27}

{cR}

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
{OPEN}
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
{VE}

{r5}

end

section
{VI}

{c31}

end

section
{VI}
  {{AR : A → Fl4Spec.Cr3 → Prop}}

{c5}

end

end

end Fl4Proofs.P3.SInvR.G5
'''
out=out.replace('    spec_exists (WP.spec_and','    Fl4Proofs.P3.spec_exists (WP.spec_and')
open(P+'P3KFin.lean','w').write(out)

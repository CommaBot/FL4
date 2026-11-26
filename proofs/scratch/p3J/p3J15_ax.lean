import Fl4Proofs.P3.JBootQ1Disp
#print axioms Fl4Proofs.P3.JBootQ.w1_irqRel
#print axioms Fl4Proofs.P3.JBootQ.img1_zero
#print axioms Fl4Proofs.P3.JBootQ.jAtZ_w1I1
#print axioms Fl4Proofs.P3.JBootQ.σ1_irqCarry
#print axioms Fl4Proofs.P3.JBootQ.jReachU40_w1I1
#print axioms Fl4Proofs.P3.JBootQ.u40_w1I1
#print axioms Fl4Proofs.P3.JBootQ.σ1_nonIdle
#print axioms Fl4Proofs.P3.SInvR.G5.budgetAt_capOpt
#print axioms Fl4Proofs.P3.SInvR.G5.KDispHypsKVU44.of_w
#print axioms Fl4Proofs.P3.JBootQ.jPathAtMU44w_σ1
#print axioms Fl4Proofs.P3.JBootQ.kDispHypsKVU44w_σ1
#print axioms Fl4Proofs.P3.JBootQ.kDispHypsKVU44_σ1_of_k6
#print axioms Fl4Proofs.P3.JBootQ.kDispHypsKVU44_k6
#print axioms Fl4Proofs.P3.JBootQ.u45nv_w1I1
-- the start's spec state is the root-thread σ1 on the IRQ layout: interrupt states are JBootQ.fInitASt's
example : Fl4Proofs.P3.JBootQ.σ1.interruptStates = Fl4Proofs.P3.SInvIB.fInitIpiASt.interruptStates := rfl
example : Fl4Proofs.P3.JBootQ.σ1.curThread ≠ Fl4Proofs.P3.JBootQ.σ1.idleThread := Fl4Proofs.P3.JBootQ.σ1_nonIdle

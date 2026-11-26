set_option maxHeartbeats 4000000 in
/-- `jDecMRL2_ofT` (its transported copy) carrying `IrqAckU`. -/
theorem jDecMRL2_ofTQ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : Fl4ProofsI.P3.JEntryAtN (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlatT arI MR) (hKD : MRKeepD arI MR)
    (hR3 : JDecMRLKQ (L := L) arI LoudT AR MR Z H Cs D s ar σ ct) :
    JDecMRL2Q (L := L) arI AR MR Z H Cs D s ar σ ct :=
  ⟨Fl4ProofsQI.P3.jDecMRL2_ofT arI s ar σ J hG hE ct hct hM hKD hR3.1, hR3.2⟩

set_option maxHeartbeats 4000000 in
/-- `jDecMRLK_ofU` (its transported copy) carrying `IrqAckU`. -/
theorem jDecMRLK_ofUQ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : Fl4ProofsI.P3.JEntryAtN (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hM : MachPlatT arI MR) (hKD : MRKeepD arI MR)
    (hVx : JDecMRLKQ (L := L) arI VtxK AR MR Z H Cs D s ar σ ct)
    (hUR : JUtResetHyp (L := L) arI AR MR Z H Cs D s ar σ ct) :
    JDecMRLKQ (L := L) arI LoudT AR MR Z H Cs D s ar σ ct :=
  ⟨Fl4ProofsQI.P3.jDecMRLK_ofU arI s ar σ J hG hE ct hct hM hKD hVx.1 hUR, hVx.2⟩

end

/-- `jVtxHypMU_of` on `JDecMRLKQ`. -/
theorem jVtxHypMU_ofQ {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}
    {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}
    {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {ct : U64}
    (h : JDecMRLKQ (L := L) arI VtxK AR MR Z H Cs D s ar σ ct) :
    JVtxHypMU (L := L) arI AR MR Z H Cs D s ar σ ct :=
  jVtxHypMU_of h.1

end

end Fl4Proofs.P3

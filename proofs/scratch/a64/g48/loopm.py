# gen 48: move the four Zombie-loop proofs of QueueZombieQ into `…M` theorems carrying a loop-invariant field
# `M` (LoopM obligations); the old theorems become their `M := True` instances (statements unchanged).
import sys
p='Fl4ProofsA64/P1/QueueZombieQ.lean'
s=open(p).read()
def R(t,a,b,c=1):
    assert t.count(a)==c,(a[:90],t.count(a))
    return t.replace(a,b)
def decl(n):
    i=s.index('theorem '+n+' '); j=s.index(':= by\n',i); k=s.find('\n\n',j)
    # start of the decl block: preceding 'set_option' line
    b=s.rindex('set_option maxHeartbeats 4000000 in\n',0,i)
    return b,i,j,k
EXTRA='\n    {M : S → Prop} (hM : LoopM st ar OS D M) (hm : M s)'
def mk(n,newn,doc,postold,postnew,bodyf,inst):
    global s
    b,i,j,k=decl(n)
    pre=s[b:i]; hdr=s[i:j]; body=s[j:k]
    hdrM=R(hdr,'theorem '+n+' ','theorem '+newn+' ')
    hdrM=R(hdrM,'(hY : Ty s) :','(hY : Ty s)'+EXTRA+' :')
    hdrM=R(hdrM,postold,postnew)
    newdecl='set_option maxHeartbeats 4000000 in\n/-- '+doc+' -/\n'+hdrM+bodyf(body)
    olddecl=pre+hdr+':=\n'+inst
    s=s[:b]+newdecl+'\n\n'+olddecl+s[k:]
# ---- LoopM structure
s=R(s,'''theorem FinK.toT {kb : U64}''','''/-- **A loop-invariant field** (gen 48): a state predicate `M` kept by each step of the Zombie loops below — the
finalisation, the in-place `Zombie` cap write, `cap_swap_for_delete` of two slots of the domain, the preemption point
and `empty_slot` — stated as Hoare-triple obligations on the kernel functions. `M := True` (`LoopM.triv`) gives back
the loops' earlier statements; an `M` that needs context (e.g. `JV`) includes it. -/
structure LoopM (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (OS D : Set U64) (M : S → Prop) :
    Prop where
  fin : ∀ (s : S) (a : A) (x : U64) (c : capability.Cap) (f : Bool), M s → x ∈ OS → obj.Slot.cap st x s = ok c →
    objects.finalise_cap st ar s a c f false ⦃ r => M r.2.1 ⦄
  setz : ∀ (s : S) (x p t n : U64), M s → x ∈ OS → obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => M s' ⦄
  swap : ∀ (s : S) (p y : U64), M s → p ∈ D → y ∈ D → p ≠ y → cdt.cap_swap_for_delete st s p y ⦃ s' => M s' ⦄
  pre : ∀ (s : S) (a : A), M s → sched.preemption_point st ar s a ⦃ r => M r.2.1 ⦄
  emp : ∀ (s : S) (a : A) (x : U64) (cl : capability.Cap), M s → x ∈ OS → ClOK cl →
    cdt.empty_slot st ar s a x cl ⦃ r => M r.1 ⦄

/-- The trivial field. -/
theorem LoopM.triv (hP : P0.ArchTotal ar) : LoopM st ar OS D (fun _ => True) where
  fin s a _ c f _ _ _ := WP.spec_mono (P0.objects.finalise_cap.p0 st ar s a c f false L.total hP) fun _ _ => trivial
  setz s x _ _ _ _ _ := WP.spec_mono (P0.obj.Slot.set_cap.p0 st x s _ L.total) fun _ _ => trivial
  swap s p y _ _ _ _ := WP.spec_mono (P0.cdt.cap_swap_for_delete.p0 st s p y L.total) fun _ _ => trivial
  pre s a _ := WP.spec_mono (P0.sched.preemption_point.p0 st ar s a L.total hP) fun _ _ => trivial
  emp s a x cl _ _ _ := WP.spec_mono (P0.cdt.empty_slot.p0 st ar s a x cl L.total hP) fun _ _ => trivial

theorem FinK.toT {kb : U64}''')
# ---- deferred
def fdef(b):
    b=R(b,'L.idleW z.1 = I ∧ L.mem z.1 (scA I) = Is ∧ Ty z.1)','L.idleW z.1 = I ∧ L.mem z.1 (scA I) = Is ∧ Ty z.1 ∧ M z.1)')
    b=R(b,'⟨h1, d1, o1, i1, j1, y1, ','⟨h1, d1, o1, i1, j1, y1, m1, ',2)
    b=R(b,'''  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, o1, i1, j1, y1⟩
    simp only at h1 d1 o1 i1 j1 y1''','''  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, o1, i1, j1, y1, m1⟩
    simp only at h1 d1 o1 i1 j1 y1 m1''')
    b=R(b,'''    refine WP.spec_bind (finXQG hP hO hA hV hR hK hTy h1 hIO hN1 y1 h1.ksb (hDO hy) hc
      (by rw [i1, j1]; exact d1 y hy c hc) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨hcl, h2, k2, hrem, j2, sc2, v2⟩
    simp only at hcl hrem j2 sc2 v2''','''    refine WP.spec_bind (WP.spec_and (finXQG hP hO hA hV hR hK hTy h1 hIO hN1 y1 h1.ksb (hDO hy) hc
      (by rw [i1, j1]; exact d1 y hy c hc) a1 fin) (hM.fin s1 a1 y c fin m1 (hDO hy) hc)) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨hcl, h2, k2, hrem, j2, sc2, v2⟩, m2⟩
    simp only at hcl hrem j2 sc2 v2 m2''')
    b=R(b,'⟨h2, d2, o2, i2, js2, y2, ','⟨h2, d2, o2, i2, js2, y2, m2, ',4)
    b=R(b,'''    refine WP.spec_bind (WP.spec_and (WP.spec_and (JV.setz hO hV h2 (hDO hy) hcp ⟨hDO hp0, fun i hi => hDO (hcov i hi)⟩)
      (W7.obj.Slot.set_cap.capw (hO.slot _ (hDO hy)))) (W7.obj.Slot.set_cap.capw (osw hO (hDO hy)))) ?_
    rintro s3 ⟨⟨⟨h3, k3, c3⟩, w3⟩, ow3⟩''','''    refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and (JV.setz hO hV h2 (hDO hy) hcp ⟨hDO hp0, fun i hi =>
      hDO (hcov i hi)⟩) (W7.obj.Slot.set_cap.capw (hO.slot _ (hDO hy)))) (W7.obj.Slot.set_cap.capw (osw hO (hDO hy))))
      (hM.setz s2 y p t n m2 (hDO hy))) ?_
    rintro s3 ⟨⟨⟨⟨h3, k3, c3⟩, w3⟩, ow3⟩, m3⟩''')
    b=R(b,'⟨h3, d3, o3, i3, js3, y3, ','⟨h3, d3, o3, i3, js3, y3, m3, ')
    b=R(b,'''    refine WP.spec_bind (cdt.cap_swap_for_delete.zqG (kb' := L.ksb s0) hO hV hDO hDC hR h3 d3 hp0 hpF hy hyc hpy) ?_
    rintro s4 ⟨h4, d4, o4, j4, K4, v4⟩''','''    refine WP.spec_bind (WP.spec_and (cdt.cap_swap_for_delete.zqG (kb' := L.ksb s0) hO hV hDO hDC hR h3 d3 hp0 hpF hy
      hyc hpy) (hM.swap s3 p y m3 hp0 hy hpy)) ?_
    rintro s4 ⟨⟨h4, d4, o4, j4, K4, v4⟩, m4⟩''')
    b=R(b,'''    refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.preemption_point.jv hP hO hV h4 (by rw [h4.ksb]; exact hW))
      (sched.preemption_point.si hP h4)) (sched.preemption_point.vk hP hR h4 h4.ksb)) ?_
    rintro ⟨rr, s5, a5⟩ ⟨⟨⟨h5, k5, j5⟩, K5⟩, v5⟩
    try simp only [uncurry_apply_pair] at h5 k5 j5 K5 v5 ⊢''','''    refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and (sched.preemption_point.jv hP hO hV h4 (by
      rw [h4.ksb]; exact hW)) (sched.preemption_point.si hP h4)) (sched.preemption_point.vk hP hR h4 h4.ksb))
      (hM.pre s4 _ m4)) ?_
    rintro ⟨rr, s5, a5⟩ ⟨⟨⟨⟨h5, k5, j5⟩, K5⟩, v5⟩, m5⟩
    try simp only [uncurry_apply_pair] at h5 k5 j5 K5 v5 m5 ⊢''')
    b=R(b,'⟨h5, d5, o5, i5, js5, y5, ','⟨h5, d5, o5, i5, js5, y5, m5, ',2)
    b=R(b,'  · exact ⟨h, hD, OKD.refl s, hI, hIs, hY⟩','  · exact ⟨h, hD, OKD.refl s, hI, hIs, hY, hm⟩')
    return b
mk('cdt.finalise_slot_deferred.zqG','cdt.finalise_slot_deferred.zqGM',
   '**`finalise_slot_deferred.zqG` with a loop-invariant field `M`** (gen 48, `LoopM`).',
   'L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ ∀ v','L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ M r.2.1 ∧ ∀ v', fdef,
   '''  WP.spec_mono (cdt.finalise_slot_deferred.zqGM (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO h hy hD hI hIs hN hY
    (LoopM.triv hP) trivial) fun _ ⟨a1, a2, a3, a4, a5, a6, _, a7⟩ => ⟨a1, a2, a3, a4, a5, a6, a7⟩''')
# ---- delete_deferred
def fdd(b):
    b=R(b,'''  refine WP.spec_bind (cdt.finalise_slot_deferred.zqG (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO h hy hD hI hIs
    hN hY) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, d1, o1, i1, j1, y1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 d1 o1 i1 j1 y1 hv1 ⊢''','''  refine WP.spec_bind (cdt.finalise_slot_deferred.zqGM (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO h hy hD hI hIs
    hN hY hM hm) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, d1, o1, i1, j1, y1, m1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 d1 o1 i1 j1 y1 m1 hv1 ⊢''')
    b=R(b,'''    · refine WP.spec_bind (WP.spec_and (cdt.empty_slot.zs (a := a1) hP hO hV h1 (hDO hy) (hv1 v rfl) hap)
        (cdt.empty_slot.vk hP hO hR h1 (hDO hy) (hv1 v rfl) h1.ksb)) ?_
      rintro ⟨s2, a2⟩ ⟨⟨h2, k2, c2, w2, K2⟩, v2⟩
      try simp only [uncurry_apply_pair] at h2 k2 c2 w2 K2 v2 ⊢''','''    · refine WP.spec_bind (WP.spec_and (WP.spec_and (cdt.empty_slot.zs (a := a1) hP hO hV h1 (hDO hy) (hv1 v rfl) hap)
        (cdt.empty_slot.vk hP hO hR h1 (hDO hy) (hv1 v rfl) h1.ksb)) (hM.emp s1 a1 y _ m1 (hDO hy) (hv1 v rfl))) ?_
      rintro ⟨s2, a2⟩ ⟨⟨⟨h2, k2, c2, w2, K2⟩, v2⟩, m2⟩
      try simp only [uncurry_apply_pair] at h2 k2 c2 w2 K2 v2 m2 ⊢''')
    b=R(b,'''        (K2 I (i1 ▸ h1.idleT)).trans j1, hTy _ _ y1 v2⟩''','''        (K2 I (i1 ▸ h1.idleT)).trans j1, hTy _ _ y1 v2, m2⟩''')
    b=R(b,'(WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, y1⟩','(WP.spec_ok _).2 ⟨h1, d1, o1, i1, j1, y1, m1⟩',2)
    return b
mk('cdt.delete_deferred.zqG','cdt.delete_deferred.zqGM',
   '**`delete_deferred.zqG` with a loop-invariant field `M`** (gen 48, `LoopM`).',
   'L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ⦄','L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ M r.2.1 ⦄', fdd,
   '''  WP.spec_mono (cdt.delete_deferred.zqGM (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY
    (LoopM.triv hP) trivial) fun _ ⟨a1, a2, a3, a4, a5, a6, _⟩ => ⟨a1, a2, a3, a4, a5, a6⟩''')
# ---- macro
s=R(s,'''  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.preemption_point.jv hP hO hV h5 (by rw [h5.ksb]; exact hW))
    (sched.preemption_point.si hP h5)) (sched.preemption_point.vk hP hR h5 h5.ksb)) ?_
  rintro ⟨rr, s6, a6⟩ ⟨⟨⟨h6, k6, i6⟩, K6⟩, v6⟩
  try simp only [uncurry_apply_pair] at h6 k6 i6 K6 v6 ⊢''','''  refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and (sched.preemption_point.jv hP hO hV h5 (by
    rw [h5.ksb]; exact hW)) (sched.preemption_point.si hP h5)) (sched.preemption_point.vk hP hR h5 h5.ksb))
    (hM.pre s5 _ m5)) ?_
  rintro ⟨rr, s6, a6⟩ ⟨⟨⟨⟨h6, k6, i6⟩, K6⟩, v6⟩, m6⟩
  try simp only [uncurry_apply_pair] at h6 k6 i6 K6 v6 m6 ⊢''')
s=R(s,'''IrqN.oka hIO N5 (OKA.of_osk k6), hTy _ _ y5 v6, ?_⟩''','''IrqN.oka hIO N5 (OKA.of_osk k6), hTy _ _ y5 v6, m6, ?_⟩''')
s=R(s,'''    exact (WP.spec_ok _).2 ⟨h6, hTy _ _ y5 v6, fun v hv => by cases hv⟩))''','''    exact (WP.spec_ok _).2 ⟨h6, hTy _ _ y5 v6, m6, fun v hv => by cases hv⟩))''')
s=R(s,'/-- The preemption-point tail of an immediate round, `Ty` kept on the error exit (gen 41). -/','/-- The preemption-point tail of an immediate round, `Ty` kept on the error exit (gen 41), `M` kept (gen 48). -/')
# ---- immediate
def fim(b):
    b=R(b,'''IrqN st (L.ksb s0) y.1 ∧
      Ty y.1)''','''IrqN st (L.ksb s0) y.1 ∧
      Ty y.1 ∧ M y.1)''')
    b=R(b,'''  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, x1, j1, js1, N1, y1⟩
    simp only at h1 d1 x1 j1 js1 N1 y1''','''  · rintro ⟨s1, a1, fuel⟩ ⟨h1, d1, x1, j1, js1, N1, y1, m1⟩
    simp only at h1 d1 x1 j1 js1 N1 y1 m1''')
    b=R(b,'⟨h1, y1, ','⟨h1, y1, m1, ',2)
    b=R(b,'''    refine WP.spec_bind (finXQG hP hO hA hV hR hK hTy h1 hIO N1 y1 h1.ksb hx hc
      (by rw [j1, js1]; exact x1 c hc) a1 fin) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨hcl, h2, k2, hrem, j2', sc2, v2⟩
    simp only at hcl hrem j2' sc2 v2''','''    refine WP.spec_bind (WP.spec_and (finXQG hP hO hA hV hR hK hTy h1 hIO N1 y1 h1.ksb hx hc
      (by rw [j1, js1]; exact x1 c hc) a1 fin) (hM.fin s1 a1 x c fin m1 hx hc)) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨hcl, h2, k2, hrem, j2', sc2, v2⟩, m2⟩
    simp only at hcl hrem j2' sc2 v2 m2''')
    b=R(b,'⟨h2, y2, ','⟨h2, y2, m2, ',4)
    b=R(b,'''    refine WP.spec_bind (WP.spec_and (WP.spec_and (JV.setz hO hV h2 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i hi)⟩)
      (W7.obj.Slot.set_cap.capw (hO.slot _ hx))) (W7.obj.Slot.set_cap.capw (osw hO hx))) ?_
    rintro s3 ⟨⟨⟨h3, k3, c3⟩, w3⟩, ow3⟩''','''    refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and (JV.setz hO hV h2 hx hcp ⟨hDO hp0, fun i hi =>
      hDO (hcov i hi)⟩) (W7.obj.Slot.set_cap.capw (hO.slot _ hx))) (W7.obj.Slot.set_cap.capw (osw hO hx)))
      (hM.setz s2 x p t n m2 hx)) ?_
    rintro s3 ⟨⟨⟨⟨h3, k3, c3⟩, w3⟩, ow3⟩, m3⟩''')
    b=R(b,'''    refine WP.spec_bind (cdt.delete_deferred.zqG (a := a2) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h3 heD d3 j3 js3
      N3 y3) ?_
    rintro ⟨r4, s4, a4⟩ ⟨h4, d4, o4, j4, js4, y4⟩
    try simp only [uncurry_apply_pair] at h4 d4 o4 j4 js4 y4 ⊢''','''    refine WP.spec_bind (cdt.delete_deferred.zqGM (a := a2) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h3 heD d3 j3 js3
      N3 y3 hM m3) ?_
    rintro ⟨r4, s4, a4⟩ ⟨h4, d4, o4, j4, js4, y4, m4⟩
    try simp only [uncurry_apply_pair] at h4 d4 o4 j4 js4 y4 m4 ⊢''')
    b=R(b,'''        IrqN st (L.ksb s0) y.1 ∧ Ty y.1) ?_ ?_''','''        IrqN st (L.ksb s0) y.1 ∧ Ty y.1 ∧ M y.1) ?_ ?_''')
    b=R(b,'⟨h4, d4, xo4, j4, js4, N4, y4⟩','⟨h4, d4, xo4, j4, js4, N4, y4, m4⟩',4)
    b=R(b,'''              IrqN st (L.ksb s0) s5 ∧ Ty s5) ?_ fun s5 h5 => (WP.spec_ok _).2 h5''','''              IrqN st (L.ksb s0) s5 ∧ Ty s5 ∧ M s5) ?_ fun s5 h5 => (WP.spec_ok _).2 h5''')
    b=R(b,'''              refine WP.spec_mono (WP.spec_and (WP.spec_and (JV.setz hO hV h4 hx hcp ⟨hDO hp0, fun i hi => hDO (hcov i (by
                rw [wsub1 hn0] at hi; omega))⟩) (W7.obj.Slot.set_cap.capw (hO.slot _ hx)))
                (W7.obj.Slot.set_cap.capw (osw hO hx))) ?_
              rintro s5 ⟨⟨⟨h5, k5, c5⟩, w5⟩, ow5⟩''','''              refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (JV.setz hO hV h4 hx hcp ⟨hDO hp0,
                fun i hi => hDO (hcov i (by rw [wsub1 hn0] at hi; omega))⟩) (W7.obj.Slot.set_cap.capw (hO.slot _ hx)))
                (W7.obj.Slot.set_cap.capw (osw hO hx))) (hM.setz s4 x _ _ _ m4 hx)) ?_
              rintro s5 ⟨⟨⟨⟨h5, k5, c5⟩, w5⟩, ow5⟩, m5⟩''')
    b=R(b,'''                hTy _ _ y4 (vsk_cw q0 hR ow5)⟩''','''                hTy _ _ y4 (vsk_cw q0 hR ow5), m5⟩''')
    b=R(b,'''      rintro ⟨s5, a5⟩ ⟨h5, d5, x5, j5, js5, N5, y5⟩
      try simp only [uncurry_apply_pair] at h5 d5 x5 j5 js5 N5 y5 ⊢''','''      rintro ⟨s5, a5⟩ ⟨h5, d5, x5, j5, js5, N5, y5, m5⟩
      try simp only [uncurry_apply_pair] at h5 d5 x5 j5 js5 N5 y5 m5 ⊢''')
    b=R(b,'''      exact (WP.spec_ok _).2 ⟨h4, y4, fun v hv => by cases hv⟩''','''      exact (WP.spec_ok _).2 ⟨h4, y4, m4, fun v hv => by cases hv⟩''')
    b=R(b,'  · exact ⟨h, hD, hX, hI, hIs, hN, hY⟩','  · exact ⟨h, hD, hX, hI, hIs, hN, hY, hm⟩')
    return b
mk('cdt.finalise_slot_immediate.zqGT','cdt.finalise_slot_immediate.zqGTM',
   '**`finalise_slot_immediate.zqGT` with a loop-invariant field `M`** (gen 48, `LoopM`).',
   'JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧ ∀ v','JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧ M r.2.1 ∧ ∀ v', fim,
   '''  WP.spec_mono (cdt.finalise_slot_immediate.zqGTM (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI
    hIs hN hY (LoopM.triv hP) trivial) fun _ ⟨a1, a2, _, a3⟩ => ⟨a1, a2, a3⟩''')
# ---- delete
def fde(b):
    b=R(b,'''  refine WP.spec_bind (cdt.finalise_slot_immediate.zqGT (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI
    hD hX hI hIs hN hY) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, y1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 y1 hv1 ⊢''','''  refine WP.spec_bind (cdt.finalise_slot_immediate.zqGTM (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI
    hD hX hI hIs hN hY hM hm) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, y1, m1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 y1 m1 hv1 ⊢''')
    b=R(b,'''    refine WP.spec_bind (WP.spec_and (cdt.empty_slot.zs hP hO hV h1 hx (hv1 v rfl) hap)
      (cdt.empty_slot.vk hP hO hR h1 hx (hv1 v rfl) h1.ksb)) ?_
    rintro ⟨s2, a2⟩ ⟨h2, v2⟩
    try simp only [uncurry_apply_pair] at h2 v2 ⊢
    exact (WP.spec_ok _).2 ⟨h2.1, hTy _ _ y1 v2⟩''','''    refine WP.spec_bind (WP.spec_and (WP.spec_and (cdt.empty_slot.zs hP hO hV h1 hx (hv1 v rfl) hap)
      (cdt.empty_slot.vk hP hO hR h1 hx (hv1 v rfl) h1.ksb)) (hM.emp s1 a1 x _ m1 hx (hv1 v rfl))) ?_
    rintro ⟨s2, a2⟩ ⟨⟨h2, v2⟩, m2⟩
    try simp only [uncurry_apply_pair] at h2 v2 m2 ⊢
    exact (WP.spec_ok _).2 ⟨h2.1, hTy _ _ y1 v2, m2⟩''')
    b=R(b,'''    exact (WP.spec_ok _).2 ⟨h1, y1⟩''','''    exact (WP.spec_ok _).2 ⟨h1, y1, m1⟩''')
    return b
mk('cdt.delete.zqIGT','cdt.delete.zqIGTM',
   '**`cdt.delete.zqIGT` with a loop-invariant field `M`** (gen 48, `LoopM`).',
   'JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ⦄','JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧ M r.2.1 ⦄', fde,
   '''  WP.spec_mono (cdt.delete.zqIGTM hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY
    (LoopM.triv hP) trivial) fun _ ⟨a1, a2, _⟩ => ⟨a1, a2⟩''')
open(p,'w').write(s)
print('ok')

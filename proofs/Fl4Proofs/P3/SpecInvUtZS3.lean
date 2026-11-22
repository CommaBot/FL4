/- g5h: `ZR` across the invocation shell (KENTRY-PLAN g5h; see SpecInvUtZS2). -/
import Fl4Proofs.P3.SpecInvUtZS2
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef}

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `ZR`** (given `PerfGapZ`; ut7's `p3N_handleInvocationR` with `ZR`). -/
theorem zr_handleInvocationR (hG : PerfGapZ) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKZE (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_split) fun thread =>
    ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_split) fun info => ?_
  intro N σ hI hN hZ y hy
  have hF : ∀ v, UKE v (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := fun _ => by uk_auto
  have hFN : NKE N (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by nk_auto
  have hFZ := zr_hiFront thread cptr info
  have hOk : OkV (uV σ) (fun r : CslotPtr × Cap × List (Cap × CslotPtr) × Option ObjRef =>
      (uV σ).2.1 r.1 = some r.2.1 ∧ ∀ p ∈ r.2.2.1, (uV σ).2.1 p.2 = some p.1 ∧ DestRefV (uV σ) p.2) (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
    refine okv_bind (fun _ => uk_capFaultOnFailure _ _ _ (uk_lookupCapAndSlot _ _))
      (okv_capFaultOnFailure _ _ (okv_lookupCapAndSlot _ _)) fun x hx => ?_
    obtain ⟨cap, slot⟩ := x
    dsimp only
    refine okv_bind_uk (fun _ => ike_liftE (uk_lookupIpcBuffer _ _)) fun buf => ?_
    refine okv_bind (fun _ => uk_lookupExtraCaps _ _ _) (okv_lookupExtraCapsN _ _ _) fun ex hex => okv_returnOk ?_
    exact ⟨hx, hex⟩
  refine syscall_postU (I := fun s => ZR s ∧ P3 N s ∧ uV s = uV σ ∧ NodeIs N s) (Q := ZR)
    (fun w hw => ⟨hFZ σ hZ w hw, p3_of_view (hF _ σ rfl w hw) hI, hF _ σ rfl w hw, hFN σ hN w hw⟩) ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv
    exact (show IKH ZR (NonDet.when blocking (handleFault thread f)) by zr_split) s hs.1 v hv
  · intro a s has w hw
    have hs : ZR s ∧ P3 N s ∧ uV s = uV σ ∧ NodeIs N s :=
      ⟨hFZ σ hZ _ has, p3_of_view (hF _ σ rfl _ has) hI, hF _ σ rfl _ has, hFN σ hN _ has⟩
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hE : ∀ v, UKE v (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := fun _ => by uk_auto
    have hEN : NKE N (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := by nk_auto
    exact ⟨zr_hiDecode thread fp info cptr sl cap ex buf s hs.1 w hw, p3_of_view (hE _ s rfl w hw) hs.2.1,
      (hE _ s rfl w hw).trans hs.2.2.1, hEN s hs.2.2.2 w hw⟩
  · intro e s hs v hv
    exact (show IKH ZR _ by zr_split) s hs.1 v hv
  · intro a s b s' has hbs hI' y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hvs : uV s = uV σ := hF _ σ rfl _ has
    obtain ⟨hc, hex⟩ := hOk σ rfl _ s has
    obtain ⟨z0, hz0, ⟨args, ha0, hb0⟩ | ⟨e, -, he⟩⟩ := mem_bindE' hbs
    swap
    · simp at he
    obtain ⟨x0, hx0, e0⟩ := mem_liftE' hz0
    subst e0
    simp only [Except.ok.injEq] at ha0
    subst ha0
    have hvx : uV x0.2 = uV σ := (uk_getMrs (uvw := uV s) _ _ _ s rfl x0 hx0).trans hvs
    have hdec : InvZ (uV σ) b :=
      okv_fl4Decode_z fp info.miLabel x0.1 cptr sl cap ex buf (fun p hp => (hex p hp).1) x0.2 hvx b s' hb0
    have hdecN : InvOKN (uV σ) b :=
      okv_fl4DecodeN fp info.miLabel x0.1 cptr sl cap ex buf hc hex x0.2 hvx b s' hb0
    have hDF : DecodedFrom (uV σ) b := ⟨fp, info.miLabel, x0.1, cptr, sl, cap, ex, buf, x0.2, s', hvx, hc, hex, hb0⟩
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · have hz' : uV z.2 = uV s' := (show ∀ v, UKE v (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        from fun _ => by uk_auto) _ s' rfl z hz
      have hzN : NodeIs N z.2 := (show NKE N (withoutPreemption (Z := Unit) (setThreadState thread .restart))
        by nk_auto) s' hI'.2.2.2 z hz
      have hzZ : ZR z.2 := zr_restart thread s' hI'.1 z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hv1 : uV s1 = uV σ := hz'.trans hI'.2.2.1
      have hI1 : P3 N s1 := p3_of_view hz' hI'.2.1
      have hok1 : InvZ (uV s1) b := by rw [hv1]; exact hdec
      have hokN1 : InvOKN (uV s1) b := by rw [hv1]; exact hdecN
      have hDF1 : DecodedFrom (uV s1) b := by rw [hv1]; exact hDF
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := zr_fl4Perform hG blocking calling don b s1 hI1 hzN hzZ hok1 hokN1 hDF1 _ hz2
        exact (show IKHE ZR _ by zr_split) s2 hs2 y hy
      · exact zr_fl4Perform hG blocking calling don b s1 hI1 hzN hzZ hok1 hokN1 hDF1 _ hz2
    · exact zr_restart thread s' hI'.1 z hz


end

end Fl4Proofs.P3.SInvUZ

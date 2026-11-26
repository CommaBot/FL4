/-! ## The writer leaves -/

theorem gkb_doMachineOp {α : Type} {mop : NonDet MachineState α} (h : MaskT mop) :
    GKB (doMachineOp (Z := Unit) mop) := fun _ L => L.msk mop h

theorem gkb_updateTimeStamp : GKB (updateTimeStamp (Z := Unit)) := fun _ L => L.uts

theorem gkb_setIrqState (st : IrqState) (i : Irq) : GKB (setIrqState (Z := Unit) st i) := fun _ L => L.sis st i

theorem gkb_ack (i : Irq) : GKB (doMachineOp (Z := Unit) (maskInterrupt false i)) := fun _ L => L.ack i

/-- A `MaskT` goal by the machine leaves. -/
macro "mt_auto" : tactic => `(tactic| repeat' (first
  | with_reducible exact mt_maskInterrupt_true _ | with_reducible exact mt_getActiveIRQ _ | with_reducible exact mt_ackInterrupt _
  | with_reducible exact mt_machineOpLift _ | with_reducible exact mt_storeWord _ _ | with_reducible exact mt_clearMemory _ _ | with_reducible exact mt_freeMemory _ _
  | with_reducible exact mt_of_mkf (mkf_loadWord _) | with_reducible exact mt_of_mkf (mkf_invalidateASID _ _)
  | with_reducible exact mt_of_mkf (mkf_invalidateTranslationSingleASID _ _)
  | with_reducible exact mt_of_mkf (mkf_invalidateLocalPageStructureCacheASID _ _)
  | with_reducible exact mt_of_mkf mkf_readFpuState | with_reducible exact mt_of_mkf (mkf_writeFpuState _)
  | with_reducible exact mt_of_mkf mkf_enableFpu | with_reducible exact mt_of_mkf mkf_disableFpu | with_reducible exact mt_of_mkf mkf_isFpuEnable
  | with_reducible exact mt_of_mkf mkf_getFaultAddress | with_reducible exact mt_fl4FpuToFrame _
  | with_reducible exact mt_pure _ | with_reducible exact mt_pure' _ | with_reducible exact mt_gets _
  | with_reducible exact mt_setDeadline _ | with_reducible exact mt_ackDeadlineIRQ
  | with_reducible exact mt_in8 _ | with_reducible exact mt_in16 _ | with_reducible exact mt_in32 _
  | with_reducible exact mt_out8 _ _ | with_reducible exact mt_out16 _ _ | with_reducible exact mt_out32 _ _
  | with_reducible exact mt_ioapicMapPinToVector _ _ _ _ _
  | with_reducible exact mt_ioapicMapPinToVectorRemapped _ _ _ _ _ _
  | (with_reducible refine mt_bind ?_ (fun _ => ?_)) | (with_reducible refine mt_bind' ?_ (fun _ => ?_))
  | (with_reducible apply mt_ite)))

/-- One step of a `GKB` proof. -/
macro "gkb_step0" : tactic => `(tactic| first
  | with_reducible exact gkb_pure _ | with_reducible exact gkb_pure' _ | with_reducible exact gkb_fail
  | with_reducible exact gkb_gets _ | with_reducible exact gkb_get
  | with_reducible exact gkb_assert _ | with_reducible exact gkb_assertOpt _
  | with_reducible exact gkb_getsThe _
  | with_reducible exact gkb_selectF _ | with_reducible exact gkb_select _
  | ((with_reducible apply gkb_modify); intro _; exact rfl)
  | ((with_reducible apply gkb_get_put); intro _; exact rfl)
  | (exact gkb_get_put' (fun _ => rfl))
  | (exact gkb_get_put (fun _ => rfl))
  | with_reducible exact gkb_getObject _
  | with_reducible exact gkb_updateTimeStamp | with_reducible exact gkb_setIrqState _ _
  | with_reducible exact gkb_ack _
  | with_reducible exact gkb_of_mtk (mtk_performPml4Flush _)
  | ((with_reducible refine gkb_doMachineOp ?_); mt_auto; done)
  | (with_reducible refine gkb_bind ?_ (fun _ => ?_))
  | (with_reducible refine gkb_bind' ?_ (fun _ => ?_))
  | (with_reducible apply gkb_ite) | (with_reducible apply gkb_when) | (with_reducible apply gkb_unless)
  | (with_reducible refine gkb_maybeM (fun _ => ?_) _) | (with_reducible apply gkb_liftM)
  | (with_reducible refine gkb_whileLoop (fun _ => ?_) _)
  | (with_reducible refine gkb_mapMx (fun _ => ?_) _)
  | (with_reducible refine gkb_mapM (fun _ => ?_) _)
  | (with_reducible refine gkb_forMx (fun _ => ?_) _)
  | with_reducible exact gkbe_pure _ | with_reducible exact gkbe_returnOk _ | with_reducible exact gkbe_throw _
  | with_reducible exact gkbe_throw' _ | with_reducible exact gkbe_throwOpt _ _ | with_reducible exact gkbe_assertE _
  | (with_reducible refine gkbe_bind ?_ (fun _ => ?_))
  | (with_reducible apply gkbe_liftE) | (with_reducible apply gkbe_ite) | (with_reducible apply gkbe_whenE)
  | (with_reducible apply gkbe_unlessE) | (with_reducible refine gkb_catch ?_ (fun _ => ?_))
  | (with_reducible refine gkbe_handleE ?_ (fun _ => ?_)) | (with_reducible apply gkbe_liftME)
  | (with_reducible refine gkbe_mapMEx (fun _ => ?_) _) | (with_reducible refine gkbe_mapME (fun _ => ?_) _)
  | (with_reducible apply gkbe_withoutPreemption) | (with_reducible apply gkbe_capFaultOnFailure)
  | (with_reducible apply gkbe_lookupErrorOnFailure) | (with_reducible apply gkbe_unifyFailure)
  | (with_reducible apply gkb_emptyOnFailure) | (with_reducible apply gkb_constOnFailure)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact gkb_pure _)
  | (exact gkb_pure _))

/-- A `GKB` lemma of a spec function (extended by the generated family, one
rule per lemma). -/
syntax "gkb_leaf" : tactic
macro_rules | `(tactic| gkb_leaf) => `(tactic| fail "no gkb_leaf")

/-- `GKB` from MachFieldFamT's `MTK` family, else one step. -/
macro "gkb_auto" : tactic => `(tactic| repeat' (first
  | gkb_leaf
  | gkb_step0
  | ((with_reducible apply gkb_of_mtk); mtk_leaf; done)
  | ((with_reducible apply gkbe_of_mtke); mtk_leaf; done)))

end

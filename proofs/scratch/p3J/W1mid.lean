/-- `JKern` at `warI1`: `warI`'s, its TDX clause read through the unchanged `tdx_active` / `dma_ram`. -/
theorem w0_jkernI1 : JKern (L := wL) warI1 Hw Csw Dw thW w0 fInitASt :=
  { orig := w0_jkern.orig, cur := w0_jkern.cur, curT := w0_jkern.curT, act := w0_jkern.act,
    dwAl := w0_jkern.dwAl, dwObj := w0_jkern.dwObj, dwNe := w0_jkern.dwNe, head := w0_jkern.head,
    gpm := w0_jkern.gpm, ga := w0_jkern.ga, gf := w0_jkern.gf, heap := w0_jkern.heap, h0 := w0_jkern.h0,
    hks := w0_jkern.hks, hksIn := w0_jkern.hksIn, hnd := w0_jkern.hnd, ksbFit := w0_jkern.ksbFit,
    ksbAl := w0_jkern.ksbAl, nodeFit := w0_jkern.nodeFit, cpuCs := w0_jkern.cpuCs, curH := w0_jkern.curH,
    cscH := w0_jkern.cscH, csLt := w0_jkern.csLt, cs0 := w0_jkern.cs0, csN := w0_jkern.csN,
    tdx := w0_jkern.tdx }

/-- **`JAtZ.utc`** at `warI1` (vacuous: no slot holds an untyped cap). -/
theorem w0_utcI1 : ∀ sl p sb fi dev, AbsSlot thW sl →
    capAt (wL.mem w0) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
    Sched.UtCapP3 (L := wL) warI1 thW w0 fInitASt Gw sl p sb fi := by
  intro sl p sb fi dev hs h _
  rw [capAt_slot hs.isSlot] at h
  cases ok_inj h


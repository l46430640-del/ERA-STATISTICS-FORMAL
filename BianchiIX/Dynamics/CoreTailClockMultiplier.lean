import BianchiIX.Analysis.CoordinateFactorCancellation
import BianchiIX.Dynamics.CoreTailMultipliers
import BianchiIX.Dynamics.ExitClockWallFactor

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The canonical Einstein-flow multiplier equals the clock multiplier as a germ, also on a zero wall. -/
theorem coreTailMultiplier_eventuallyEq_exitClock {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {h T : ℝ}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) (ht : coreTailTime h Y ≤ T)
    (hs : -Real.log h ∈ Icc 0 (exitEntryClock (Y, T))) (i : Fin 2) :
    (fun Z => coreTailMultiplier h Z i) =ᶠ[𝓝 Y]
      (fun Z => Real.exp (exitClockLogMultiplier I i Z (-Real.log h))) := by
  have Hreg := coreTail_regular_of_valid hR HV
  have Hmult := (contDiffAt_coreTailMultiplier_two hR HV Hreg.1 i).1
  have Hnear := exitClockFlow_near_wall_equation hIo hI hUo hY H hT hcover hs i
  have Hlog := (exitClockLogMultiplier_regular hs.1 i (fun r hr => (Hnear.self_of_nhds r hr).1)).1
  apply coordinate_factor_eventuallyEq i.succ (Hmult.of_le (by norm_num)) Hlog.exp
  have Hend := coreTailState_eventuallyEq_exitClockFlow hIo hI hUo hY H HV
    (hcover ⟨HV.1.1.1.le, ht⟩)
  have Hwall := exitClockFlow_eventually_wall_factor hIo hI hUo hY H hT hcover hs i
  filter_upwards [Hreg.2.2, Hend, Hwall] with Z hZ hZe hZw
  rw [← coreTailMultiplier_formula hZ i, ← hZw, ← hZe]
  fin_cases i <;> rfl

end BianchiIX

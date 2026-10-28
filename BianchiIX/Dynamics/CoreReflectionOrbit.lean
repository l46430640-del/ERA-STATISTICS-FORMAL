import BianchiIX.Dynamics.CoreReturnExitChart
import BianchiIX.Dynamics.ReflectionReturnEstimates

noncomputable section

namespace BianchiIX

def coreReflectionTime (Y : CoreAngleState) : ℝ :=
  reflectionReturnTime (coreReturnState coreRadiusReturnTime Y) + coreRadiusReturnTime Y

/-- The two canonical passages, after the axis reflection, are a single exact Einstein flow segment. -/
theorem coreReflection_canonical_orbit {Y : CoreAngleState}
    (hcore : coreRadiusReturnValid Y)
    (hchart : coreTailEntry (coreReturnState coreRadiusReturnTime Y) =
      projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y))
    (ht : 0 < reflectionReturnTime (coreReturnState coreRadiusReturnTime Y))
    (hactual : coreRadiusEntry (reflectionReturnState (coreReturnState coreRadiusReturnTime Y)) =
      projectiveReflection (projectiveOriginalFlow (coreTailEntry (coreReturnState coreRadiusReturnTime Y)) 0
        (reflectionReturnTime (coreReturnState coreRadiusReturnTime Y)))) :
    0 < coreReflectionTime Y ∧
      coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) =
        projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y)) := by
  have hT := hcore.1.1.1
  have hA := (hcore.2.1 (coreRadiusReturnTime Y) ⟨hT.le, le_rfl⟩).2
  have HR := projectiveOriginalFlow_restart (coreRadiusReturnValid_denom_pos hcore) hT.le ht.le hA
  rw [← hchart] at HR
  exact ⟨add_pos ht hT, hactual.trans (congrArg projectiveReflection HR)⟩

end BianchiIX

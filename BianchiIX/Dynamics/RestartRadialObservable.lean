import BianchiIX.Dynamics.RestartRadialDriftBounds

noncomputable section

namespace BianchiIX

def restartSectionQuadratic (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  restartQuadratic (restartSectionStrongWall h t Z) (restartSectionCenterFlow h t Z 0)
    (restartSectionCenterFlow h t Z 1 - restartSectionCenterFlow h t Z 2)

def restartSectionQuadraticRate (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  restartRadialDrift (restartSectionStrongWall h t Z, restartSectionCenterFlow h t Z)

def restartSectionRadius (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  Real.sqrt (restartSectionQuadratic h t Z)

def restartRadialNorm (Z : RestartCenterState) : ℝ :=
  Real.sqrt (Z 0 ^ 2 + (Z 1 - Z 2) ^ 2)

theorem restartSectionQuadratic_nonneg (h t : ℝ) (Z : RestartCenterState) :
    0 ≤ restartSectionQuadratic h t Z := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem restartSectionQuadratic_initial (h : ℝ) (Z : RestartCenterState) :
    restartSectionQuadratic h 0 Z = restartQuadratic h (Z 0) (Z 1 - Z 2) := by
  simp only [restartSectionQuadratic, restartSectionStrongWall, restartSectionCenterFlow,
    normalizedMaxCurve_initial, restartCenterProjection_section]
  rfl

theorem hasDerivAt_restartSectionQuadratic {h t : ℝ} {Z : RestartCenterState}
    (hr : 0 ≤ restartSectionRadicand h Z) (ht : 0 ≤ t)
    (hp : normalizedMaxCurve (restartSectionChart h Z) 0 t 0 < 0)
    (hn : restartSectionStrongWall h t Z ^ 2 < 1) :
    HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t := by
  have H := normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hr) ht
  exact hasDerivAt_restartQuadratic_drift H.1 H.2.1 hp hn

theorem hasDerivAt_restartSectionRadius {h t : ℝ} {Z : RestartCenterState}
    (HD : HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t)
    (HJ : 0 < restartSectionQuadratic h t Z) :
    HasDerivAt (fun s => restartSectionRadius h s Z)
      (restartSectionQuadraticRate h t Z / (2 * restartSectionRadius h t Z)) t :=
  HD.sqrt HJ.ne'

end BianchiIX

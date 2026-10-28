import BianchiIX.Dynamics.RestartEquations

noncomputable section

namespace BianchiIX

/-- Transport first, then estimate the forcing; all reference linear terms cancel exactly. -/
theorem hasDerivAt_restart_transported_components
    {n s v : ℝ → ℝ} {t dF es ev : ℝ} (hn₀ : n t ^ 2 < 1)
    (hn : HasDerivAt n (n t * (restartReferenceStrongRate (n t) + dF)) t)
    (hs : HasDerivAt s (n t ^ 2 * s t + Real.sqrt 3 * n t * v t + es) t)
    (hv : HasDerivAt v (restartReferenceWallRate (n t) * v t + ev) t) :
    HasDerivAt (fun r => restartShearFactor (n r) * s r + restartShearCoupling (n r) * v r)
      (n t * dF * (deriv restartShearFactor (n t) * s t + deriv restartShearCoupling (n t) * v t) +
        restartShearFactor (n t) * es + restartShearCoupling (n t) * ev) t ∧
    HasDerivAt (fun r => restartWallFactor (n r) * v r)
      (n t * dF * deriv restartWallFactor (n t) * v t + restartWallFactor (n t) * ev) t := by
  have HA := (hasDerivAt_restartShearFactor hn₀).differentiableAt.hasDerivAt.comp t hn
  have HC := (hasDerivAt_restartWallFactor hn₀).differentiableAt.hasDerivAt.comp t hn
  have HK := (hasDerivAt_restartShearCoupling hn₀).differentiableAt.hasDerivAt.comp t hn
  obtain ⟨ha, hc, hk⟩ := restart_transport_cancellation hn₀
  constructor
  · convert! (HA.mul hs).add (HK.mul hv) using 1
    simp only [Function.comp_def]
    linear_combination -(s t) * ha - (v t) * hk
  · convert! HC.mul hv using 1
    simp only [Function.comp_def]
    linear_combination -(v t) * hc

theorem hasDerivAt_restartQuadratic_strong {n : ℝ} (hn : n ^ 2 < 1) (s v : ℝ) :
    HasDerivAt (fun m => restartQuadratic m s v) (restartQuadraticStrongDerivative n s v) n := by
  have HA := (hasDerivAt_restartShearFactor hn).differentiableAt.hasDerivAt
  have HC := (hasDerivAt_restartWallFactor hn).differentiableAt.hasDerivAt
  have HK := (hasDerivAt_restartShearCoupling hn).differentiableAt.hasDerivAt
  convert! (((HA.mul_const s).add (HK.mul_const v)).pow 2).add ((HC.mul_const v).pow 2) using 1
  simp only [Pi.add_apply]
  dsimp only [restartQuadraticStrongDerivative]
  ring

theorem hasDerivAt_restartQuadratic_perturbed
    {n s v : ℝ → ℝ} {t dF es ev : ℝ} (hn₀ : n t ^ 2 < 1)
    (hn : HasDerivAt n (n t * (restartReferenceStrongRate (n t) + dF)) t)
    (hs : HasDerivAt s (n t ^ 2 * s t + Real.sqrt 3 * n t * v t + es) t)
    (hv : HasDerivAt v (restartReferenceWallRate (n t) * v t + ev) t) :
    HasDerivAt (fun r => restartQuadratic (n r) (s r) (v r))
      (n t * dF * restartQuadraticStrongDerivative (n t) (s t) (v t) +
        2 * (restartShearFactor (n t) * s t + restartShearCoupling (n t) * v t) *
          (restartShearFactor (n t) * es + restartShearCoupling (n t) * ev) +
        2 * restartWallFactor (n t) ^ 2 * v t * ev) t := by
  obtain ⟨HS, HV⟩ := hasDerivAt_restart_transported_components hn₀ hn hs hv
  convert! (HS.pow 2).add (HV.pow 2) using 1
  dsimp only [restartQuadraticStrongDerivative]
  ring

/-- Equation (E.9) in scalar components, along an exact constrained Einstein solution. -/
theorem hasDerivAt_restartQuadratic_normalized {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1)
    (hn : x t 2 ^ 2 < 1) :
    HasDerivAt (fun r => restartQuadratic (x r 2) (x r 1) (x r 3 - x r 4))
      (x t 2 * restartStrongRateDifference (x t) *
          restartQuadraticStrongDerivative (x t 2) (x t 1) (x t 3 - x t 4) +
        2 * restartCurvatureDifference (x t) * restartQuadratic (x t 2) (x t 1) (x t 3 - x t 4) +
        2 * restartRootDifference (x t) * (x t 3 - x t 4) *
          (restartShearFactor (x t 2) * restartShearCoupling (x t 2) * x t 1 +
            (restartShearCoupling (x t 2) ^ 2 + restartWallFactor (x t 2) ^ 2) * (x t 3 - x t 4)) +
        2 * Real.sqrt 3 * (x t 3 + x t 4) * restartRotationDefect (x t 2) (x t 1) (x t 3 - x t 4)) t := by
  obtain ⟨HN, HS, HV⟩ := hasDerivAt_restart_components hx hc
  have HV' : HasDerivAt (fun r => x r 3 - x r 4)
      (restartReferenceWallRate (x t 2) * (x t 3 - x t 4) +
        ((restartCurvatureDifference (x t) + restartRootDifference (x t)) * (x t 3 - x t 4) +
          Real.sqrt 3 * (x t 3 + x t 4) * x t 1)) t := by
    convert! HV using 1
    ring
  convert! hasDerivAt_restartQuadratic_perturbed hn HN HS HV' using 1
  dsimp only [restartQuadratic, restartRotationDefect]
  ring

end BianchiIX

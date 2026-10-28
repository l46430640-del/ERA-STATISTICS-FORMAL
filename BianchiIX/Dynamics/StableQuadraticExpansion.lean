import BianchiIX.Algebra.StableWeakRemainderBounds
import BianchiIX.Dynamics.StableCorrectedRemainderDerivatives
import BianchiIX.Dynamics.StableCorrectedRemainder

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

local instance stableQuadraticExpansionOperatorGroup : NormedAddCommGroup (StableState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance stableQuadraticExpansionOperatorSpace : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance

def stableQuadraticPhase (m u w : ℝ) : ℝ :=
  m + stableCorrectionA m * u ^ 2 + stableCorrectionC m * u * w + w ^ 2 / (2 * (m + 1))

def stableQuadraticRemainder (y : StableState) : ℝ :=
  stableBoundaryProjection (y 0) (y 1) (y 2) - stableQuadraticPhase (y 0) (y 1) (y 2)

theorem stableQuadraticRemainder_decomposition :
    stableQuadraticRemainder = fun y => stableCorrectedRemainder y + stableWeakRemainder (y 0) (y 2) := by
  funext y
  unfold stableQuadraticRemainder stableQuadraticPhase stableCorrectedRemainder stableCorrectedPhase stableWeakRemainder
  ring

theorem stableBoundaryProjection_quadratic_expansion (m u w : ℝ) :
    stableBoundaryProjection m u w = m + m / (m ^ 2 - 1) * u ^ 2 - 2 / (m + 1) * u * w +
      w ^ 2 / (2 * (m + 1)) + stableQuadraticRemainder ![m, u, w] := by
  dsimp [stableQuadraticRemainder, stableQuadraticPhase, stableCorrectionA, stableCorrectionC]
  ring

theorem stableQuadraticRemainder_weak {m w : ℝ} (hm : 2 ≤ m) (hw : |w| ≤ 1 / 200) :
    stableQuadraticRemainder ![m, 0, w] =
      -w ^ 4 / (2 * (m + 1) * (stableWeakRadius m w + (m + 1)) ^ 2) := by
  rw [← stableWeakRemainder_factorization (by linarith : -1 < m)]
  dsimp [stableQuadraticRemainder]
  rw [stableBoundaryProjection_weak hm (by simp) hw]
  dsimp [stableQuadraticPhase, stableWeakRemainder]
  ring

theorem stableQuadraticRemainder_derivatives {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    let E := fun z : StableState => stableWeakRemainder (z 0) (z 2)
    ContDiffAt ℝ 2 stableQuadraticRemainder y ∧
      fderiv ℝ stableQuadraticRemainder y = fderiv ℝ stableCorrectedRemainder y + fderiv ℝ E y ∧
      fderiv ℝ (fderiv ℝ stableQuadraticRemainder) y =
        fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y + fderiv ℝ (fderiv ℝ E) y := by
  have hR : ContDiffAt ℝ 2 stableCorrectedRemainder y :=
    (contDiffAt_stableBoundaryProjection_two hm hu hw).sub (contDiffAt_stableCorrectedPhase 2 (by linarith))
  have hE := contDiffAt_stableWeakRemainder 2 (y := y) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [stableQuadraticRemainder_decomposition]
    exact hR.add hE
  · rw [stableQuadraticRemainder_decomposition]
    exact fderiv_fun_add (hR.differentiableAt (by norm_num)) (hE.differentiableAt (by norm_num))
  · have heq : fderiv ℝ stableQuadraticRemainder =ᶠ[𝓝 y] (fun z => fderiv ℝ stableCorrectedRemainder z +
        fderiv ℝ (fun a : StableState => stableWeakRemainder (a 0) (a 2)) z) := by
      filter_upwards [hR.eventually (by norm_num), hE.eventually (by norm_num)] with z hr he
      rw [stableQuadraticRemainder_decomposition]
      exact fderiv_fun_add (hr.differentiableAt (by norm_num)) (he.differentiableAt (by norm_num))
    rw [heq.fderiv_eq]
    exact fderiv_fun_add
      ((hR.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num))
      ((hE.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num))

end BianchiIX

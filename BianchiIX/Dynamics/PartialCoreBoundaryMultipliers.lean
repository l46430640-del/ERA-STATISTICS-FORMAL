import BianchiIX.Dynamics.ReferenceMovingEndpoint
import BianchiIX.Dynamics.PartialCoreMultiplierRegularity

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- At zero walls, ordinary transverse derivatives determine the positive return factors. -/
theorem partialCoreReturn_reference_multipliers {k : ℝ} (hk : 1 < k) (s : ℝ)
    {τ : ProjectiveState → ℝ} (hτ : DifferentiableAt ℝ τ (referencePulse k s))
    (htime : τ (referencePulse k s) = referenceShiftClock k s (referenceHalfTime k))
    (hMu : ∀ i : Fin 2, DifferentiableAt ℝ (fun x => partialCoreReturnMultiplier τ x i) (referencePulse k s))
    (hformula : ∀ᶠ x in 𝓝 (referencePulse k s),
      projectiveOriginalFlow x 0 (τ x) 1 = x 1 * partialCoreReturnMultiplier τ x 0 ∧
      projectiveOriginalFlow x 0 (τ x) 3 = (x 2 * x 3) * partialCoreReturnMultiplier τ x 1) :
    partialCoreReturnMultiplier τ (referencePulse k s) 0 =
        (k / Real.cosh (k * s)) * Real.exp (-(k ^ 2 / 2) * (referenceHalfTime k - s)) ∧
      partialCoreReturnMultiplier τ (referencePulse k s) 1 =
        Real.exp (-2 * (referenceHalfTime k - s)) := by
  let y := referencePulse k s
  have hu : y 1 = 0 := rfl
  have hw : y 3 = 0 := rfl
  have hprodU := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y).mul (hMu 0).hasFDerivAt
  have hprodW := ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y).mul
    (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y)).mul (hMu 1).hasFDerivAt
  have heqU : (fun x => projectiveOriginalFlow x 0 (τ x) 1) =ᶠ[𝓝 y]
      (fun x => x 1 * partialCoreReturnMultiplier τ x 0) := hformula.mono fun _ h => h.1
  have heqW : (fun x => projectiveOriginalFlow x 0 (τ x) 3) =ᶠ[𝓝 y]
      (fun x => (x 2 * x 3) * partialCoreReturnMultiplier τ x 1) := hformula.mono fun _ h => h.2
  have HU := congrArg (fun A : ProjectiveState →L[ℝ] ℝ => A (Pi.single 1 1))
    (heqU.fderiv_eq.trans hprodU.fderiv)
  have HW := congrArg (fun A : ProjectiveState →L[ℝ] ℝ => A (Pi.single 3 1))
    (heqW.fderiv_eq.trans hprodW.fderiv)
  rw [(referenceMovingEndpoint_wall_derivative k s (referenceHalfTime k) hτ htime (Pi.single 1 1)).1,
    Pi.single_eq_same, mul_one, referenceTransverseMode_interior_ratio hk] at HU
  rw [(referenceMovingEndpoint_wall_derivative k s (referenceHalfTime k) hτ htime (Pi.single 3 1)).2,
    Pi.single_eq_same, mul_one, referenceTransverseMode_interior_ratio hk] at HW
  constructor
  · simpa only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      hu, zero_smul, zero_apply, zero_add, Pi.single_eq_same, mul_one] using HU.symm
  · have HE : (k / Real.cosh (k * s)) * partialCoreReturnMultiplier τ y 1 =
        (k / Real.cosh (k * s)) * Real.exp (-2 * (referenceHalfTime k - s)) := by
      simpa [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
        hw, y, referencePulse, mul_comm] using HW.symm
    exact mul_left_cancel₀ (div_pos (zero_lt_one.trans hk) (Real.cosh_pos _)).ne' HE

end BianchiIX

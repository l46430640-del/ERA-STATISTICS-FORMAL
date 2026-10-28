import BianchiIX.Dynamics.EntranceRadialDriftBounds
import BianchiIX.Dynamics.EntranceStrongDerivativeBounds
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- The full differential of the radial drift in the actual radial chart. -/
theorem EntranceRadialInverseAt.drift_differential {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    let z := entranceRadialCoordinates y
    DifferentiableAt ℝ (fun z => entranceRadialDrift (Ψ z)) z ∧
      ∀ v : ProjectiveState,
        fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) z v =
          (v 1 * y 2 + y 1 * v 2) * entranceRadialStrongCoefficient y +
          y 1 * y 2 * fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z v +
          2 * y 2 * v 2 * entranceRadialWeakCoefficient y +
          y 2 ^ 2 * fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z v := by
  have heq : (fun z => entranceRadialDrift (Ψ z)) =ᶠ[𝓝 (entranceRadialCoordinates y)]
      (fun z => z 1 * z 2 * entranceRadialStrongCoefficient (Ψ z) + z 2 ^ 2 * entranceRadialWeakCoefficient (Ψ z)) := by
    filter_upwards [H.wall_coordinates] with z hz
    simp only [entranceRadialDrift, hz.1, hz.2.1]
  obtain ⟨hA, hB⟩ := H.coefficients_regular hk hy hv
  have hd (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i (entranceRadialCoordinates y)
  have hsum := (((hd 1).mul (hd 2)).mul (hA.differentiableAt (by norm_num)).hasFDerivAt).add
    (((hd 2).pow 2).mul (hB.differentiableAt (by norm_num)).hasFDerivAt)
  change HasFDerivAt (fun z => z 1 * z 2 * entranceRadialStrongCoefficient (Ψ z) + z 2 ^ 2 * entranceRadialWeakCoefficient (Ψ z)) _
    (entranceRadialCoordinates y) at hsum
  have hactual := hsum.congr_of_eventuallyEq heq
  refine ⟨hactual.differentiableAt, fun v => ?_⟩
  rw [hactual.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.mul_apply]
  rw [H.apply_base]
  simp only [entranceRadialCoordinates, Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem EntranceRadialInverseAt.drift_wall_partials {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    let z := entranceRadialCoordinates y
    let LA := fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z
    let LB := fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z
    let LG := fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) z
    LG (Pi.single 1 1) = y 2 * entranceRadialStrongCoefficient y + y 1 * y 2 * LA (Pi.single 1 1) +
        y 2 ^ 2 * LB (Pi.single 1 1) ∧
      LG (Pi.single 3 1) = y 1 * y 2 * LA (Pi.single 3 1) + y 2 ^ 2 * LB (Pi.single 3 1) := by
  constructor <;> simp [(H.drift_differential hk hy hv).2]

/-- Multiplicative wall displacement differentiates to the logarithmic coordinate column. -/
theorem hasDerivAt_projective_logCoordinate {f : ProjectiveState → ℝ} {z : ProjectiveState}
    (hf : DifferentiableAt ℝ f z) (i : Fin 4) :
    HasDerivAt (fun t => f (Function.update z i (z i * Real.exp t)))
      (z i * fderiv ℝ f z (Pi.single i 1)) 0 := by
  have hp := (hasDerivAt_update z i (z i * Real.exp 0)).scomp 0
    ((Real.hasDerivAt_exp 0).const_mul (z i))
  have hf' : HasFDerivAt f (fderiv ℝ f z) (Function.update z i (z i * Real.exp 0)) := by
    simpa using hf.hasFDerivAt
  have H := hf'.comp_hasDerivAt 0 hp
  simpa [Function.comp_def, map_smul, smul_eq_mul] using H

theorem EntranceRadialInverseAt.drift_log_derivative {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (i : Fin 4) :
    let z := entranceRadialCoordinates y
    HasDerivAt (fun t => entranceRadialDrift (Ψ (Function.update z i (z i * Real.exp t))))
      (z i * fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) z (Pi.single i 1)) 0 :=
  hasDerivAt_projective_logCoordinate (H.drift_differential hk hy hv).1 i

end BianchiIX

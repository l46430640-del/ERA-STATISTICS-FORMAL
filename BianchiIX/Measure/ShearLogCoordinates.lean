import BianchiIX.Measure.MainWallMeasure
import BianchiIX.Dynamics.ShearSectionFlux

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def scaledShearLogCoordinates (a : ℝ) (z : SectionCoordinates) : SectionCoordinates :=
  ![z 0, -Real.log (a * z 1), -Real.log (a * z 2)]

def scaledShearLogDifferential (z : SectionCoordinates) : SectionCoordinates →L[ℝ] SectionCoordinates :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    (-(z 1)⁻¹) • ContinuousLinearMap.proj 1, (-(z 2)⁻¹) • ContinuousLinearMap.proj 2]

theorem hasFDerivAt_scaledShearLogCoordinates {a : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (h₁ : 0 < z 1) (h₂ : 0 < z 2) :
    HasFDerivAt (scaledShearLogCoordinates a) (scaledShearLogDifferential z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z
  · have H := (((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) z).const_mul a).log
      (mul_pos ha h₁).ne').neg
    convert! H using 1
    ext v
    change -(z 1)⁻¹ * v 1 = -((a * z 1)⁻¹ * (a * v 1))
    field_simp
  · have H := (((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) z).const_mul a).log
      (mul_pos ha h₂).ne').neg
    convert! H using 1
    ext v
    change -(z 2)⁻¹ * v 2 = -((a * z 2)⁻¹ * (a * v 2))
    field_simp

theorem scaledShearLogDifferential_det (z : SectionCoordinates) :
    (scaledShearLogDifferential z).det = 1 / (z 1 * z 2) := by
  change (scaledShearLogDifferential z).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  have H : LinearMap.toMatrix' (scaledShearLogDifferential z).toLinearMap =
      !![1, 0, 0; 0, -(z 1)⁻¹, 0; 0, 0, -(z 2)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, scaledShearLogDifferential]
  rw [H, Matrix.det_fin_three]
  simp [mul_comm]

theorem scaledShearLogCoordinates_injOn {a : ℝ} (ha : 0 < a) :
    InjOn (scaledShearLogCoordinates a) {z : SectionCoordinates | 0 < z 1 ∧ 0 < z 2} := by
  intro z hz w hw heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  change -Real.log (a * z 1) = -Real.log (a * w 1) at h1
  change -Real.log (a * z 2) = -Real.log (a * w 2) at h2
  have H1 := Real.log_injOn_pos (mul_pos ha hz.1) (mul_pos ha hw.1) (neg_injective h1)
  have H2 := Real.log_injOn_pos (mul_pos ha hz.2) (mul_pos ha hw.2) (neg_injective h2)
  ext i
  fin_cases i
  · exact h0
  · exact mul_left_cancel₀ ha.ne' H1
  · exact mul_left_cancel₀ ha.ne' H2

theorem scaledShearLogCoordinates_radicand {a h : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (h₁ : 0 < z 1) (h₂ : 0 < z 2) :
    mainWallRadicand h (scaledShearLogCoordinates a z) =
      restartSectionRadicand h (restartShearCurve 1 (a * z 1) (a * z 2) (z 0)) := by
  simp [mainWallRadicand, scaledShearLogCoordinates, restartSectionRadicand,
    restartShearCurve, Real.exp_log (mul_pos ha h₁), Real.exp_log (mul_pos ha h₂)]

/-- The scale cancels in the exact change of coordinates: physical flux pulls back with density 1/(xy). -/
theorem mainWallMeasure_scaledShearLogCoordinates {a h : ℝ} {A : Set SectionCoordinates}
    (ha : 0 < a) (hA : MeasurableSet A)
    (hpos : ∀ z ∈ A, 0 < z 1 ∧ 0 < z 2)
    (hrad : ∀ z ∈ A, 0 < restartSectionRadicand h (restartShearCurve 1 (a * z 1) (a * z 2) (z 0))) :
    mainWallMeasure h (scaledShearLogCoordinates a '' A) =
      ∫⁻ z in A, ENNReal.ofReal (restartShearFluxDensity h (a * z 1) (a * z 2) (z 0) / (z 1 * z 2)) := by
  have hd (z : SectionCoordinates) (hz : z ∈ A) := hasFDerivAt_scaledShearLogCoordinates ha (hpos z hz).1 (hpos z hz).2
  have hi : InjOn (scaledShearLogCoordinates a) A := (scaledShearLogCoordinates_injOn ha).mono hpos
  have himage : MeasurableSet (scaledShearLogCoordinates a '' A) :=
    hA.image_of_continuousOn_injOn (fun z hz => (hd z hz).continuousAt.continuousWithinAt) hi
  have hdom : scaledShearLogCoordinates a '' A ⊆ mainWallChartDomain h := by
    rintro _ ⟨z, hz, rfl⟩
    change 0 < mainWallRadicand h (scaledShearLogCoordinates a z)
    rw [scaledShearLogCoordinates_radicand ha (hpos z hz).1 (hpos z hz).2]
    exact hrad z hz
  rw [mainWallMeasure_apply himage hdom,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA (fun z hz => (hd z hz).hasFDerivWithinAt) hi]
  apply setLIntegral_congr_fun hA
  intro z hz
  change ENNReal.ofReal |(scaledShearLogDifferential z).det| *
    ENNReal.ofReal (mainWallChartDensity h (scaledShearLogCoordinates a z)) = _
  have Hden : mainWallChartDensity h (scaledShearLogCoordinates a z) =
      restartShearFluxDensity h (a * z 1) (a * z 2) (z 0) :=
    (restartShearFluxDensity_eq_mainWall (mul_pos ha (hpos z hz).1) (mul_pos ha (hpos z hz).2)).symm
  rw [scaledShearLogDifferential_det,
    abs_of_pos (one_div_pos.mpr (mul_pos (hpos z hz).1 (hpos z hz).2)),
    Hden,
    ← ENNReal.ofReal_mul (one_div_nonneg.mpr (mul_nonneg (hpos z hz).1.le (hpos z hz).2.le))]
  congr 1
  ring

end BianchiIX

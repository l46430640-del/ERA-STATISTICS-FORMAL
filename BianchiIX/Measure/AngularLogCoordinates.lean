import BianchiIX.Measure.MainWallMeasure

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def scaledAngularLogCoordinates (a : ℝ) (z : SectionCoordinates) : SectionCoordinates :=
  ![z 1 * z 0, -Real.log (z 0), -Real.log (2 * a * z 2)]

def scaledAngularLogDifferential (z : SectionCoordinates) : SectionCoordinates →L[ℝ] SectionCoordinates :=
  ContinuousLinearMap.pi ![z 1 • ContinuousLinearMap.proj 0 + z 0 • ContinuousLinearMap.proj 1,
    (-(z 0)⁻¹) • ContinuousLinearMap.proj 0, (-(z 2)⁻¹) • ContinuousLinearMap.proj 2]

theorem hasFDerivAt_scaledAngularLogCoordinates {a : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (hρ : 0 < z 0) (ht : 0 < z 2) :
    HasFDerivAt (scaledAngularLogCoordinates a) (scaledAngularLogDifferential z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) z).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z) using 1
  · convert! ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z).log hρ.ne').neg using 1
    ext v
    change -(z 0)⁻¹ * v 0 = -((z 0)⁻¹ * v 0)
    ring
  · have H := (((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) z).const_mul (2 * a)).log
      (mul_pos (mul_pos (by norm_num) ha) ht).ne').neg
    convert! H using 1
    ext v
    change -(z 2)⁻¹ * v 2 = -((2 * a * z 2)⁻¹ * (2 * a * v 2))
    field_simp

theorem scaledAngularLogDifferential_det {z : SectionCoordinates} (hρ : z 0 ≠ 0) :
    (scaledAngularLogDifferential z).det = -(z 2)⁻¹ := by
  change (scaledAngularLogDifferential z).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  have H : LinearMap.toMatrix' (scaledAngularLogDifferential z).toLinearMap =
      !![z 1, z 0, 0; -(z 0)⁻¹, 0, 0; 0, 0, -(z 2)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, scaledAngularLogDifferential]
  rw [H]
  simp [Matrix.det_fin_three, mul_comm, hρ]

theorem scaledAngularLogCoordinates_injOn {a : ℝ} (ha : 0 < a) :
    InjOn (scaledAngularLogCoordinates a) {z : SectionCoordinates | 0 < z 0 ∧ 0 < z 2} := by
  intro z hz w hw heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  change -Real.log (z 0) = -Real.log (w 0) at h1
  change -Real.log (2 * a * z 2) = -Real.log (2 * a * w 2) at h2
  have hρ := Real.log_injOn_pos hz.1 hw.1 (neg_injective h1)
  have ht := Real.log_injOn_pos (mul_pos (mul_pos (by norm_num) ha) hz.2)
    (mul_pos (mul_pos (by norm_num) ha) hw.2) (neg_injective h2)
  have htw : z 2 = w 2 := mul_left_cancel₀ (by positivity : 2 * a ≠ 0) ht
  change z 1 * z 0 = w 1 * w 0 at h0
  rw [hρ] at h0
  have hθ := mul_right_cancel₀ hw.1.ne' h0
  ext i
  fin_cases i
  · exact hρ
  · exact hθ
  · exact htw

/-- The angular coordinate cancels the radial logarithmic wall factor exactly. -/
theorem volume_scaledAngularLogCoordinates {a : ℝ} {A : Set SectionCoordinates}
    (ha : 0 < a) (hA : MeasurableSet A) (hpos : ∀ z ∈ A, 0 < z 0 ∧ 0 < z 2) :
    volume (scaledAngularLogCoordinates a '' A) = ∫⁻ z in A, ENNReal.ofReal (1 / z 2) := by
  have hd (z : SectionCoordinates) (hz : z ∈ A) :=
    hasFDerivAt_scaledAngularLogCoordinates ha (hpos z hz).1 (hpos z hz).2
  have hi : InjOn (scaledAngularLogCoordinates a) A := (scaledAngularLogCoordinates_injOn ha).mono hpos
  have H := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA
    (fun z hz => (hd z hz).hasFDerivWithinAt) hi (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one] at H
  rw [H]
  apply setLIntegral_congr_fun hA
  intro z hz
  change ENNReal.ofReal |(scaledAngularLogDifferential z).det| = ENNReal.ofReal (1 / z 2)
  rw [scaledAngularLogDifferential_det (hpos z hz).1.ne', abs_neg,
    abs_of_pos (inv_pos.mpr (hpos z hz).2), one_div]

end BianchiIX

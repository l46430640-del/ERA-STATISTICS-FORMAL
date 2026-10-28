import BianchiIX.Measure.ShearFailureCoordinates
import BianchiIX.Measure.ThreeCoordinateTonelli

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal Classical

/-- The normalized-coordinate integral is exactly the iterated radial failure flux. -/
theorem restartShearFailureCoordinates_lintegral {h s a ε P η σ Bcap : ℝ} {J : ℕ}
    (hA : MeasurableSet (restartShearFailureCoordinates h s a ε P η J σ Bcap)) :
    (∫⁻ z in restartShearFailureCoordinates h s a ε P η J σ Bcap,
      ENNReal.ofReal (restartShearFluxDensity h (a * z 1) (a * z 2) (z 0) / (z 1 * z 2))) =
        restartShearFailureLayer h s a ε P η J σ Bcap := by
  let A := restartShearFailureCoordinates h s a ε P η J σ Bcap
  let f : SectionCoordinates → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (restartShearFluxDensity h (a * z 1) (a * z 2) (z 0) / (z 1 * z 2))
  have hf : Measurable f := by
    have hg : Measurable (fun z : SectionCoordinates => ((a * z 1, a * z 2), z 0)) := by fun_prop
    have hd : Measurable (fun z : SectionCoordinates =>
        restartShearFluxDensity h (a * z 1) (a * z 2) (z 0)) := by
      simpa only [Function.comp_def] using (measurable_restartShearFluxDensity h).comp hg
    exact (hd.div ((measurable_pi_apply 1).mul (measurable_pi_apply 2))).ennreal_ofReal
  change (∫⁻ z in A, f z) = _
  rw [← lintegral_indicator hA, lintegral_three_coordinates (hf.indicator hA)]
  unfold restartShearFailureLayer
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro x
  by_cases hx : 0 < x ∧ x < 1
  · rw [indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from hx), ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro y
    by_cases hy : 0 < y ∧ y < 1
    · rw [indicator_of_mem (show y ∈ Ioo (0 : ℝ) 1 from hy)]
      by_cases hl : (a * x, a * y) ∈ restartShearLabelSet ε a P
      · rw [if_pos hl]
        let F := eraRadialFailure η J σ (restartShearAmplitudeBudget a (a * x) (a * y)) Bcap a (2 * a)
          (restartShearReturnState h s (a * x) (a * y))
        have hF : MeasurableSet F := by
          have H := hA.preimage (show Measurable (fun r : ℝ => ![r, x, y]) by fun_prop)
          simpa [restartShearFailureCoordinates, hx, hy, hl, F] using H
        have heq : (fun r => A.indicator f ![r, x, y]) =
            F.indicator (fun r => ENNReal.ofReal (restartShearFluxDensity h (a * x) (a * y) r / (x * y))) := by
          funext r
          simp [indicator, A, restartShearFailureCoordinates, f, F, hx, hy, hl]
        rw [heq, lintegral_indicator hF]
        simp_rw [ENNReal.ofReal_div_of_pos (mul_pos hx.1 hy.1), div_eq_mul_inv]
        exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr
          (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hx.1 hy.1))))
      · simp [indicator, restartShearFailureCoordinates, hl]
    · simp [indicator, restartShearFailureCoordinates, hy]
  · simp [indicator, restartShearFailureCoordinates, hx]

/-- Corrected physical section measure equals the previously estimated logarithmic layer integral. -/
theorem mainWallMeasure_restartShearFailureSection {h s a ε P η σ Bcap : ℝ} {J : ℕ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64)
    (hA : MeasurableSet (restartShearFailureCoordinates h s a ε P η J σ Bcap)) :
    mainWallMeasure h (restartShearFailureSection h s a ε P η J σ Bcap) =
      restartShearFailureLayer h s a ε P η J σ Bcap := by
  rw [restartShearFailureSection, mainWallMeasure_scaledShearLogCoordinates ha hA
    (fun z hz => ⟨hz.1.1, hz.2.1.1⟩) (fun z hz => ?_)]
  · exact restartShearFailureCoordinates_lintegral hA
  · have hl := hz.2.2.1
    exact (restartShear_small_section hh hh1 ha hah hε
      ⟨hl.1.1.le, hl.1.2⟩ ⟨hl.2.1.1.le, hl.2.1.2⟩ hz.2.2.2.1).1

end BianchiIX

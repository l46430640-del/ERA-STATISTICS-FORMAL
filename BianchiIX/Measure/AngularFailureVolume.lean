import BianchiIX.Measure.AngularFailureCoordinates
import BianchiIX.Measure.AngularFailureBudget
import BianchiIX.Measure.ThreeCoordinateTonelli
import BianchiIX.Measure.SmallSectionVolume

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal Classical

theorem volume_restartAngularFailureSection_le {h s a L P η σ Bcap : ℝ} {J : ℕ}
    (ha : 0 < a) (hL : 0 ≤ L)
    (hA : MeasurableSet (restartAngularFailureCoordinates h s a L P η J σ Bcap))
    (Hslice : ∀ θ ζ : ℝ, (θ, ζ) ∈ restartLabelSet L a P →
      volume (eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a)
        (restartReturnState h s θ ζ)) ≤ ENNReal.ofReal (min a (640 * Real.sqrt 3 * (restartAmplitudeBudget L a ζ) ^ σ))) :
    volume (restartAngularFailureSection h s a L P η J σ Bcap) ≤
      ENNReal.ofReal (2 * L) * logarithmicLayerCostOne a (angularFailureFluxConstant L σ) σ := by
  let A := restartAngularFailureCoordinates h s a L P η J σ Bcap
  let f : SectionCoordinates → ℝ≥0∞ := fun z => ENNReal.ofReal (1 / z 2)
  have hf : Measurable f := (measurable_const.div (measurable_pi_apply 2)).ennreal_ofReal
  rw [restartAngularFailureSection, volume_scaledAngularLogCoordinates ha hA
    (fun z hz => ⟨ha.trans_le hz.2.2.2.1.1, hz.2.1.1⟩)]
  change (∫⁻ z in A, f z) ≤ _
  rw [← lintegral_indicator hA, lintegral_three_coordinates (hf.indicator hA)]
  calc
    _ ≤ ∫⁻ θ in Icc (-L) L, ∫⁻ t in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (min a ((angularFailureFluxConstant L σ * a ^ (-2 * σ)) * t ^ σ) / t) := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_mono
      intro θ
      by_cases hθ : -L ≤ θ ∧ θ ≤ L
      · rw [indicator_of_mem (show θ ∈ Icc (-L) L from hθ), ← lintegral_indicator measurableSet_Ioo]
        apply lintegral_mono
        intro t
        by_cases ht : 0 < t ∧ t < 1
        · rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ht)]
          by_cases hl : (θ, 2 * a * t) ∈ restartLabelSet L a P
          · let F := eraRadialFailure η J σ (restartAmplitudeBudget L a (2 * a * t)) Bcap a (2 * a)
              (restartReturnState h s θ (2 * a * t))
            have hF : MeasurableSet F := by
              have H := hA.preimage (show Measurable (fun r : ℝ => ![r, θ, t]) by fun_prop)
              simpa [restartAngularFailureCoordinates, hθ, ht, hl, F] using H
            have heq : (fun r => A.indicator f ![r, θ, t]) = F.indicator (fun _ => ENNReal.ofReal (1 / t)) := by
              funext r
              simp [indicator, A, restartAngularFailureCoordinates, f, F, hθ, ht, hl]
            change (∫⁻ r, A.indicator f ![r, θ, t]) ≤ _
            rw [heq, lintegral_indicator hF, lintegral_const, Measure.restrict_apply_univ]
            calc
              _ ≤ ENNReal.ofReal (1 / t) * ENNReal.ofReal (min a (640 * Real.sqrt 3 *
                  (restartAmplitudeBudget L a (2 * a * t)) ^ σ)) := mul_le_mul' le_rfl (Hslice θ (2 * a * t) hl)
              _ = _ := by
                rw [restartAmplitudeBudget_normalized hL ha ht.1.le,
                  ← ENNReal.ofReal_mul (one_div_nonneg.mpr ht.1.le)]
                congr 1
                ring
          · simp [indicator, restartAngularFailureCoordinates, hl]
        · simp [indicator, restartAngularFailureCoordinates, ht]
      · simp [indicator, restartAngularFailureCoordinates, hθ]
    _ = _ := by
      change (∫⁻ _ in Icc (-L) L, logarithmicLayerCostOne a (angularFailureFluxConstant L σ) σ) = _
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
        show L - -L = 2 * L by ring, mul_comm]

theorem mainWallMeasure_restartAngularFailureSection_le_volume {h s a L P η σ Bcap : ℝ} {J : ℕ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 16)
    (hL : 0 ≤ L) (hLa : 2 * L * a ≤ 1 / 8)
    (hA : MeasurableSet (restartAngularFailureCoordinates h s a L P η J σ Bcap)) :
    mainWallMeasure h (restartAngularFailureSection h s a L P η J σ Bcap) ≤
      ENNReal.ofReal (3 : ℝ) * volume (restartAngularFailureSection h s a L P η J σ Bcap) := by
  apply mainWallMeasure_le_three_volume hh hh1 (measurableSet_restartAngularFailureSection ha hA)
  rintro _ ⟨z, hz, rfl⟩
  have hρ : 0 < z 0 := ha.trans_le hz.2.2.2.1.1
  have ht : 0 < 2 * a * z 2 := mul_pos (by positivity) hz.2.1.1
  have hsmall : 2 * a ≤ h / 8 := by linarith only [hah]
  have hθ : |z 1| ≤ L := abs_le.mpr hz.1
  have hs : |z 1 * z 0| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_pos hρ]
    have H := mul_le_mul hθ hz.2.2.2.1.2 hρ.le hL
    nlinarith only [H, hLa]
  change |z 1 * z 0| ≤ 1 / 8 ∧ Real.exp (- -Real.log (z 0)) ≤ h / 8 ∧
    Real.exp (- -Real.log (2 * a * z 2)) ≤ h / 8
  rw [neg_neg, neg_neg, Real.exp_log hρ, Real.exp_log ht]
  exact ⟨hs, hz.2.2.2.1.2.trans hsmall,
    (mul_le_of_le_one_right (by positivity : 0 ≤ 2 * a) hz.2.1.2.le).trans hsmall⟩

end BianchiIX

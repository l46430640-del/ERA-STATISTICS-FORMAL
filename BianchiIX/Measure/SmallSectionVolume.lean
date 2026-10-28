import BianchiIX.Measure.MainWallMeasure
import BianchiIX.Algebra.SectionBounds

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- A bounded physical density controls any small Borel coordinate set, including its restriction to the constraint chart. -/
theorem mainWallMeasure_le_three_volume {h : ℝ} {A : Set SectionCoordinates}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hA : MeasurableSet A)
    (hsmall : ∀ z ∈ A, |z 0| ≤ 1 / 8 ∧ Real.exp (-z 1) ≤ h / 8 ∧ Real.exp (-z 2) ≤ h / 8) :
    mainWallMeasure h A ≤ ENNReal.ofReal (3 : ℝ) * volume A := by
  rw [mainWallMeasure, withDensity_apply _ hA, Measure.restrict_restrict hA]
  have hAD := hA.inter (isOpen_mainWallChartDomain h).measurableSet
  calc
    _ ≤ ∫⁻ _ in A ∩ mainWallChartDomain h, ENNReal.ofReal (3 : ℝ) := by
      apply setLIntegral_mono' hAD
      intro z hz
      obtain ⟨hs, h₂, h₃⟩ := hsmall z hz.1
      exact ENNReal.ofReal_le_ofReal (small_section_corrected_flux_bounds hh hh1
        (Real.exp_pos _).le (Real.exp_pos _).le h₂ h₃ hs
        (mainWallChart_negative hz.2) (mainWallChart_constraint hz.2)).2.2
    _ = ENNReal.ofReal (3 : ℝ) * volume (A ∩ mainWallChartDomain h) := by simp
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono inter_subset_left)

theorem volume_three_box {b c : Fin 3 → ℝ} (h : b ≤ c) :
    volume (Icc b c) = ENNReal.ofReal ((c 0 - b 0) * (c 1 - b 1) * (c 2 - b 2)) := by
  rw [Real.volume_Icc_pi]
  simp only [Fin.prod_univ_succ, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton]
  change ENNReal.ofReal (c 0 - b 0) *
    (ENNReal.ofReal (c 1 - b 1) * ENNReal.ofReal (c 2 - b 2)) = _
  rw [← ENNReal.ofReal_mul (sub_nonneg.mpr (h 1)), ← ENNReal.ofReal_mul (sub_nonneg.mpr (h 0))]
  congr 1
  ring

end BianchiIX

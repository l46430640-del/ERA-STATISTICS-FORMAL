import BianchiIX.Measure.MainWallMeasure
import BianchiIX.Algebra.SharpSectionBounds

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def mainWallOriginalDensity (h : ℝ) (z : SectionCoordinates) : ℝ :=
  sectionFluxDensity (mainWallChart h z 0) (z 0)

/-- The unmodified section flux in logarithmic wall coordinates. -/
def mainWallOriginalMeasure (h : ℝ) : Measure SectionCoordinates :=
  (volume.restrict (mainWallChartDomain h)).withDensity
    (fun z => ENNReal.ofReal (mainWallOriginalDensity h z))

theorem measurable_mainWallOriginalDensity (h : ℝ) : Measurable (mainWallOriginalDensity h) := by
  unfold mainWallOriginalDensity sectionFluxDensity shearSq mainWallChart mainWallRadicand curvature
  fun_prop

theorem mainWallOriginalDensity_eq {h : ℝ} (hh : 0 < h) (z : SectionCoordinates) :
    mainWallOriginalDensity h z =
      (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2))) * mainWallChartDensity h z := by
  have hH : 0 ≤ wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)) :=
    Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
  unfold mainWallOriginalDensity mainWallChartDensity correctedSectionFluxDensity
  exact (mul_div_cancel₀ _ (by positivity : 1 + 4 * wallAmplitude h (Real.exp (-z 1))
    (Real.exp (-z 2)) ≠ 0)).symm

/-- The change of flux is an exact density identity, with no finiteness assumption. -/
theorem mainWallOriginalMeasure_eq_withDensity {h : ℝ} (hh : 0 < h) :
    mainWallOriginalMeasure h = (mainWallMeasure h).withDensity
      (fun z => ENNReal.ofReal (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)))) := by
  have hw : Measurable (fun z : SectionCoordinates =>
      ENNReal.ofReal (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)))) := by
    unfold wallAmplitude
    fun_prop
  unfold mainWallOriginalMeasure mainWallMeasure
  rw [← withDensity_mul _ (measurable_mainWallChartDensity h).ennreal_ofReal hw]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have hH : 0 ≤ wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)) :=
    Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
  dsimp only [Pi.mul_apply]
  rw [mainWallOriginalDensity_eq hh, ENNReal.ofReal_mul (by positivity)]
  exact mul_comm _ _

theorem mainWallOriginalMeasure_apply {h : ℝ} (hh : 0 < h) {A : Set SectionCoordinates}
    (hA : MeasurableSet A) :
    mainWallOriginalMeasure h A = ∫⁻ z in A,
      ENNReal.ofReal (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2))) ∂mainWallMeasure h := by
  rw [mainWallOriginalMeasure_eq_withDensity hh, withDensity_apply _ hA]

theorem mainWallMeasure_le_original {h : ℝ} (hh : 0 < h) :
    mainWallMeasure h ≤ mainWallOriginalMeasure h := by
  rw [mainWallOriginalMeasure_eq_withDensity hh]
  have H : (fun _ : SectionCoordinates => (1 : ℝ≥0∞)) ≤ᵐ[mainWallMeasure h]
      (fun z => ENNReal.ofReal (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)))) := by
    apply Filter.Eventually.of_forall
    intro z
    have hH : 0 ≤ wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)) :=
      Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
    exact ENNReal.one_le_ofReal.mpr (by linarith)
  simpa using withDensity_mono H

theorem mainWallOriginalMeasure_null_iff {h : ℝ} (hh : 0 < h) (A : Set SectionCoordinates) :
    mainWallOriginalMeasure h A = 0 ↔ mainWallMeasure h A = 0 := by
  constructor
  · intro hA
    exact le_antisymm ((mainWallMeasure_le_original hh A).trans_eq hA) bot_le
  · intro hA
    rw [mainWallOriginalMeasure_eq_withDensity hh]
    exact withDensity_absolutelyContinuous _ _ hA

/-- A height-dependent comparison transfers the same failure set to the original flux. -/
theorem mainWallOriginalMeasure_le_of_small_walls {h : ℝ} (hh : 0 < h)
    {A : Set SectionCoordinates} (hA : MeasurableSet A)
    (hsmall : ∀ z ∈ A, Real.exp (-z 1) ≤ h ∧ Real.exp (-z 2) ≤ h) :
    mainWallOriginalMeasure h A ≤ ENNReal.ofReal (1 + 4 * h ^ 2) * mainWallMeasure h A := by
  rw [mainWallOriginalMeasure_apply hh hA]
  calc
    _ ≤ ∫⁻ _ in A, ENNReal.ofReal (1 + 4 * h ^ 2) ∂mainWallMeasure h := by
      apply setLIntegral_mono' hA
      intro z hz
      apply ENNReal.ofReal_le_ofReal
      have H := wallAmplitude_le_square hh.le (Real.exp_pos _).le (Real.exp_pos _).le
        (hsmall z hz).1 (hsmall z hz).2
      linarith
    _ = _ := by simp

theorem mainWallChartDomain_of_small {h d : ℝ} {z : SectionCoordinates}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hdh : d ≤ h / 8)
    (hs : |z 0| ≤ d) (hb : Real.exp (-z 1) ≤ d) (hc : Real.exp (-z 2) ≤ d) :
    z ∈ mainWallChartDomain h := by
  have hQ := (abs_le.mp (curvature_abs_le_sum_sq hh.le (Real.exp_pos (-z 1)).le
    (Real.exp_pos (-z 2)).le)).2
  have hsum : h + Real.exp (-z 1) + Real.exp (-z 2) ≤ 5 / 4 * h := by linarith
  have hsum2 := pow_le_pow_left₀ (by positivity : 0 ≤ h + Real.exp (-z 1) + Real.exp (-z 2)) hsum 2
  have hh2 := pow_le_pow_left₀ hh.le hh1 2
  have hs2 : (z 0) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := sq_le_sq.mpr (by simpa using hs.trans (by linarith : d ≤ 1 / 8))
  change 0 < 1 - (z 0) ^ 2 - curvature h (Real.exp (-z 1)) (Real.exp (-z 2))
  nlinarith only [hQ, hsum2, hh2, hs2]

theorem mainWallOriginalDensity_small_bounds {h d : ℝ} {z : SectionCoordinates}
    (hh : 0 < h) (hh1 : h ≤ 1 / 128) (hd : 0 < d) (hdh : d < h / 8)
    (hs : |z 0| ≤ d) (hb : Real.exp (-z 1) ≤ d) (hc : Real.exp (-z 2) ≤ d) :
    47 / 32 < mainWallOriginalDensity h z ∧ mainWallOriginalDensity h z < 2 := by
  have hz := mainWallChartDomain_of_small hh (by linarith) hdh.le hs hb hc
  exact (small_section_sharp_flux_bounds hh hh1 hd hdh (Real.exp_pos _).le (Real.exp_pos _).le
    hb hc hs (mainWallChart_negative hz) (mainWallChart_constraint hz)).2.2.2.2.2

end BianchiIX

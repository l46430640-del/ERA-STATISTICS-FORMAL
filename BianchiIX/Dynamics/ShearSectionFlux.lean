import BianchiIX.Dynamics.ShearRestartCurves
import BianchiIX.Dynamics.MainWallDensity

noncomputable section

namespace BianchiIX

open Set

def restartShearFluxDensity (h n₂ n₃ ρ : ℝ) : ℝ :=
  correctedSectionFluxDensity (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ) 0) ρ h n₂ n₃

/-- The radial weight is the corrected physical flux in the existing logarithmic wall chart. -/
theorem restartShearFluxDensity_eq_mainWall {h n₂ n₃ ρ : ℝ} (h₂ : 0 < n₂) (h₃ : 0 < n₃) :
    restartShearFluxDensity h n₂ n₃ ρ = mainWallChartDensity h ![ρ, -Real.log n₂, -Real.log n₃] := by
  simp [restartShearFluxDensity, mainWallChartDensity, mainWallChart, mainWallRadicand,
    restartSectionChart, restartSectionRadicand, restartShearCurve, Real.exp_log h₂, Real.exp_log h₃]

theorem measurable_restartShearFluxDensity (h : ℝ) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => restartShearFluxDensity h p.1.1 p.1.2 p.2) := by
  unfold restartShearFluxDensity correctedSectionFluxDensity sectionFluxDensity shearSq
    restartSectionChart restartSectionRadicand restartShearCurve curvature wallAmplitude
  fun_prop

/-- Small physical section coordinates lie on the negative constraint branch before any dynamical restart. -/
theorem restartShear_small_section {h a ε n₂ n₃ ρ : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a)
    (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) (hρ : ρ ∈ Icc a (2 * a)) :
    let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
    0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧ x 0 < 0 ∧
      constraint (x 0) ρ h n₂ n₃ = 1 ∧ n₂ ≤ h / 8 ∧ n₃ ≤ h / 8 ∧ |ρ| ≤ 1 / 8 := by
  intro x
  have hε2 : 2 * ε ≤ 1 := by linarith only [hε.2]
  have hn₂ : n₂ ≤ h / 8 := (h₂.2.trans (mul_le_of_le_one_left ha.le hε2)).trans hah
  have hn₃ : n₃ ≤ h / 8 := (h₃.2.trans (mul_le_of_le_one_left ha.le hε2)).trans hah
  have hρ0 : 0 ≤ ρ := ha.le.trans hρ.1
  have hρsmall : |ρ| ≤ 1 / 8 := by
    rw [abs_of_nonneg hρ0]
    linarith only [hρ.2, hah, hh1]
  have hsum : h + n₂ + n₃ ≤ 5 / 4 * h := by linarith only [hn₂, hn₃]
  have H := pow_le_pow_left₀ (add_nonneg (add_nonneg hh.le h₂.1) h₃.1) hsum 2
  have HQ := (abs_le.mp (curvature_abs_le_sum_sq hh.le h₂.1 h₃.1)).2
  have hh2 := pow_le_pow_left₀ hh.le hh1 2
  have hρ2 : ρ ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := sq_le_sq.mpr (by simpa using hρsmall)
  have hrad : 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) := by
    change 0 < 1 - (1 * ρ) ^ 2 - curvature h n₂ n₃
    simp only [one_mul]
    nlinarith only [H, HQ, hh2, hρ2]
  refine ⟨hrad, neg_neg_of_pos (Real.sqrt_pos.mpr hrad), ?_, hn₂, hn₃, hρsmall⟩
  have Hcon := restartSectionChart_constraint hrad.le
  change constraint (x 0) (1 * ρ) h n₂ n₃ = 1 at Hcon
  simpa only [one_mul] using Hcon

theorem restartShearFluxDensity_bounds {h a ε n₂ n₃ ρ : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a)
    (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) (hρ : ρ ∈ Icc a (2 * a)) :
    1 / 2 ≤ restartShearFluxDensity h n₂ n₃ ρ ∧ restartShearFluxDensity h n₂ n₃ ρ ≤ 3 := by
  obtain ⟨_, hp, hcon, hn₂, hn₃, hs⟩ := restartShear_small_section hh hh1 ha hah hε h₂ h₃ hρ
  have H := small_section_corrected_flux_bounds hh hh1 h₂.1 h₃.1 hn₂ hn₃ hs hp hcon
  exact ⟨H.1, H.2.2⟩

end BianchiIX

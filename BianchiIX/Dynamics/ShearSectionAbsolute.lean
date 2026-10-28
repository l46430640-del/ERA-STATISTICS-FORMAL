import BianchiIX.Dynamics.ShearSectionFlux

noncomputable section

namespace BianchiIX

open Set

theorem mainWallRadicand_eq_shear_abs (h : ℝ) (z : SectionCoordinates) :
    mainWallRadicand h z = restartSectionRadicand h
      (restartShearCurve 1 (Real.exp (-z 1)) (Real.exp (-z 2)) |z 0|) := by
  simp [mainWallRadicand, restartSectionRadicand, restartShearCurve, sq_abs]

theorem mainWallChartDensity_eq_shear_abs (h : ℝ) (z : SectionCoordinates) :
    mainWallChartDensity h z =
      restartShearFluxDensity h (Real.exp (-z 1)) (Real.exp (-z 2)) |z 0| := by
  simp [mainWallChartDensity, restartShearFluxDensity, mainWallChart, mainWallRadicand,
    restartSectionChart, restartSectionRadicand, restartShearCurve,
    correctedSectionFluxDensity, sectionFluxDensity, shearSq, sq_abs]

/-- The same physical section density bound holds for both signs of the shear. -/
theorem mainWall_small_shear_abs {h a ε : ℝ} {z : SectionCoordinates}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (hρ : |z 0| ∈ Icc a (2 * a))
    (h₂ : Real.exp (-z 1) ≤ 2 * ε * a) (h₃ : Real.exp (-z 2) ≤ 2 * ε * a) :
    z ∈ mainWallChartDomain h ∧ 1 / 2 ≤ mainWallChartDensity h z ∧ mainWallChartDensity h z ≤ 3 := by
  refine ⟨?_, ?_⟩
  · change 0 < mainWallRadicand h z
    rw [mainWallRadicand_eq_shear_abs]
    exact (restartShear_small_section hh hh1 ha hah hε
      ⟨(Real.exp_pos _).le, h₂⟩ ⟨(Real.exp_pos _).le, h₃⟩ hρ).1
  · rw [mainWallChartDensity_eq_shear_abs]
    exact restartShearFluxDensity_bounds hh hh1 ha hah hε
      ⟨(Real.exp_pos _).le, h₂⟩ ⟨(Real.exp_pos _).le, h₃⟩ hρ

end BianchiIX

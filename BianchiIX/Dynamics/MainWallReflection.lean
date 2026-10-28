import BianchiIX.Dynamics.AxisSymmetry
import BianchiIX.Dynamics.MainWallDensity

noncomputable section

namespace BianchiIX

open Set

/-- Exchange the weak walls in logarithmic section coordinates. -/
def mainWallReflection (y : SectionCoordinates) : SectionCoordinates := ![-y 0, y 2, y 1]

@[simp] theorem mainWallReflection_twice (y : SectionCoordinates) :
    mainWallReflection (mainWallReflection y) = y := by
  ext i
  fin_cases i <;> simp [mainWallReflection]

def mainWallReflectionLinear : SectionCoordinates →ₗ[ℝ] SectionCoordinates where
  toFun := mainWallReflection
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mainWallReflection]
    ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [mainWallReflection]

def mainWallReflectionEquiv : SectionCoordinates ≃L[ℝ] SectionCoordinates :=
  ({ mainWallReflectionLinear with
    invFun := mainWallReflection
    left_inv := mainWallReflection_twice
    right_inv := mainWallReflection_twice } : SectionCoordinates ≃ₗ[ℝ] SectionCoordinates).toContinuousLinearEquiv

@[simp] theorem mainWallReflectionEquiv_apply (y : SectionCoordinates) :
    mainWallReflectionEquiv y = mainWallReflection y := rfl

theorem mainWallReflection_det : mainWallReflectionEquiv.toLinearMap.det = 1 := by
  rw [← LinearMap.det_toMatrix']
  have H : LinearMap.toMatrix' mainWallReflectionEquiv.toLinearMap =
      !![-1, 0, 0; 0, 0, 1; 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, mainWallReflectionEquiv, mainWallReflectionLinear, mainWallReflection]
  rw [H]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

theorem mainWallRadicand_reflection (h : ℝ) (y : SectionCoordinates) :
    mainWallRadicand h (mainWallReflection y) = mainWallRadicand h y := by
  dsimp [mainWallRadicand, mainWallReflection, curvature]
  ring

theorem mainWallChart_reflection (h : ℝ) (y : SectionCoordinates) :
    mainWallChart h (mainWallReflection y) = axisSwap (mainWallChart h y) := by
  simp only [mainWallChart, mainWallRadicand_reflection]
  rfl

theorem mainWallChartDensity_reflection (h : ℝ) (y : SectionCoordinates) :
    mainWallChartDensity h (mainWallReflection y) = mainWallChartDensity h y := by
  unfold mainWallChartDensity
  rw [mainWallChart_reflection]
  dsimp [axisSwap, mainWallReflection, correctedSectionFluxDensity, sectionFluxDensity, shearSq, wallAmplitude]
  rw [neg_sq, show h * Real.exp (-y 2) * Real.exp (-y 1) = h * Real.exp (-y 1) * Real.exp (-y 2) by ring]

theorem normalizedMaxDomain_mainWallReflection (h t₀ : ℝ) (y : SectionCoordinates) :
    normalizedMaxDomain (mainWallChart h (mainWallReflection y)) t₀ =
      normalizedMaxDomain (mainWallChart h y) t₀ := by
  rw [mainWallChart_reflection]
  exact NormalizedSymmetry.swap.maxDomain _ _

theorem normalizedMaxCurve_mainWallReflection {h t₀ t : ℝ} {y : SectionCoordinates}
    (ht : t ∈ normalizedMaxDomain (mainWallChart h y) t₀) :
    normalizedMaxCurve (mainWallChart h (mainWallReflection y)) t₀ t =
      axisSwap (normalizedMaxCurve (mainWallChart h y) t₀ t) := by
  rw [mainWallChart_reflection]
  exact NormalizedSymmetry.swap.maxCurve ht

end BianchiIX

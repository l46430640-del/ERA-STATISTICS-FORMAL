import BianchiIX.Dynamics.MainWallChart
import BianchiIX.Dynamics.SectionFlux
import Mathlib.LinearAlgebra.Alternating.Curry

noncomputable section

namespace BianchiIX

theorem normalizedConstraintDifferential_first (x : NormalizedState) :
    normalizedConstraintDifferential x (Pi.single 0 1) = 2 * x 0 := by
  have H := (hasFDerivAt_stateConstraint (Function.update x 0 (x 0))).comp_hasDerivAt (x 0)
    (hasDerivAt_update x 0 (x 0))
  simp only [Function.update_eq_self] at H
  apply H.unique
  simpa [Function.comp_def, stateConstraint, constraint, shearSq] using
    (((hasDerivAt_id (x 0)).pow 2).add_const (x 1 ^ 2)).add_const (curvature (x 2) (x 3) (x 4))

private theorem mainWall_volume_determinant (a b c u v w : ℝ) (F : NormalizedState) :
    normalizedAmbientVolume ![![a, 0, 0, 0, 0], F, ![u, 1, 0, 0, 0],
      ![v, 0, 0, -b, 0], ![w, 0, 0, 0, -c]] = -a * F 2 * b * c := by
  rw [normalizedAmbientVolume, Pi.basisFun_det_apply]
  have hm : (Matrix.of ![![a, 0, 0, 0, 0], F, ![u, 1, 0, 0, 0],
      ![v, 0, 0, -b, 0], ![w, 0, 0, 0, -c]]).submatrix Fin.succ Fin.succ =
      !![F 1, F 2, F 3, F 4; 1, 0, 0, 0; 0, 0, -b, 0; 0, 0, 0, -c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ]
  rw [hm]
  have hn : (!![F 1, F 2, F 3, F 4; 1, 0, 0, 0; 0, 0, -b, 0; 0, 0, 0, -c]).submatrix
      (1 : Fin 4).succAbove Fin.succ = !![F 2, F 3, F 4; 0, -b, 0; 0, 0, -c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row _ 1]
  norm_num [Fin.sum_univ_succ]
  rw [hn]
  rw [Matrix.det_fin_three]
  simp
  ring

def mainWallChartFrame (h : ℝ) (y : SectionCoordinates) : Fin 3 → NormalizedState :=
  fun i => mainWallChartDifferential h y (Pi.single i 1)

def mainWallChartDensity (h : ℝ) (y : SectionCoordinates) : ℝ :=
  correctedSectionFluxDensity (mainWallChart h y 0) (y 0) h (Real.exp (-y 1)) (Real.exp (-y 2))

theorem mainWallChartFrame_tangent {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (i : Fin 3) :
    normalizedConstraintDifferential (mainWallChart h y) (mainWallChartFrame h y i) = 0 :=
  congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L (Pi.single i 1)) (mainWallChartDifferential_tangent hy)

theorem mainWallChartDensity_pos {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) : 0 < mainWallChartDensity h y := by
  have hp := mainWallChart_negative hy
  have hS : 0 ≤ shearSq (mainWallChart h y 0) (y 0) := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hH : 0 ≤ wallAmplitude h (Real.exp (-y 1)) (Real.exp (-y 2)) :=
    Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity
  exact div_pos (div_pos (by linarith) (mul_pos (by norm_num) (abs_pos.mpr (ne_of_lt hp))))
    (by linarith)

theorem mainWallChart_signed_flux {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) :
    normalizedSectionFlux (mainWallChart h y) (mainWallChartFrame h y) = -mainWallChartDensity h y := by
  let x := mainWallChart h y
  let V := mainWallChartFrame h y
  let X : NormalizedState := (2 * x 0)⁻¹ • Pi.single 0 1
  have hp : x 0 < 0 := mainWallChart_negative hy
  have hX : normalizedConstraintDifferential x X = 1 := by
    rw [map_smul, normalizedConstraintDifferential_first]
    exact inv_mul_cancel₀ (mul_ne_zero (by norm_num) (ne_of_lt hp))
  have htan : ∀ i : Fin 4, normalizedConstraintDifferential x ((Fin.cons (normalizedField x) V :
      Fin 4 → NormalizedState) i) = 0 := by
    intro i
    exact Fin.cases (normalizedConstraintDifferential_field x) (mainWallChartFrame_tangent hy) i
  change normalizedConstraintVolume x (Fin.cons (normalizedField x) V) = _
  rw [normalizedConstraintVolume_normal (mainWallChart_constraint hy) hX htan]
  have hcoords (i : Fin 3) := mainWallChartDifferential_components hy (Pi.single i 1)
  have hframe : Fin.cons X (Fin.cons (normalizedField x) V) =
      ![![(2 * x 0)⁻¹, 0, 0, 0, 0], normalizedField x, ![V 0 0, 1, 0, 0, 0],
        ![V 1 0, 0, 0, -Real.exp (-y 1), 0], ![V 2 0, 0, 0, 0, -Real.exp (-y 2)]] := by
    funext i
    fin_cases i
    · ext j
      fin_cases j <;> simp [X]
    · rfl
    · change V 0 = ![V 0 0, 1, 0, 0, 0]
      ext j
      fin_cases j
      · rfl
      · simpa [V, mainWallChartFrame] using (hcoords 0).1
      · exact (hcoords 0).2.1
      · simpa [V, mainWallChartFrame] using (hcoords 0).2.2.1
      · simpa [V, mainWallChartFrame] using (hcoords 0).2.2.2
    · change V 1 = ![V 1 0, 0, 0, -Real.exp (-y 1), 0]
      ext j
      fin_cases j
      · rfl
      · simpa [V, mainWallChartFrame] using (hcoords 1).1
      · exact (hcoords 1).2.1
      · simpa [V, mainWallChartFrame] using (hcoords 1).2.2.1
      · simpa [V, mainWallChartFrame] using (hcoords 1).2.2.2
    · change V 2 = ![V 2 0, 0, 0, 0, -Real.exp (-y 2)]
      ext j
      fin_cases j
      · rfl
      · simpa [V, mainWallChartFrame] using (hcoords 2).1
      · exact (hcoords 2).2.1
      · simpa [V, mainWallChartFrame] using (hcoords 2).2.2.1
      · simpa [V, mainWallChartFrame] using (hcoords 2).2.2.2
  rw [hframe, mainWall_volume_determinant]
  change -(2 * x 0)⁻¹ * (rateOne (x 0) (y 0) * h) * Real.exp (-y 1) * Real.exp (-y 2) /
    (h * Real.exp (-y 1) * Real.exp (-y 2) *
      (1 + 4 * wallAmplitude h (Real.exp (-y 1)) (Real.exp (-y 2)))) = _
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity
  rw [abs_of_neg hp]
  unfold rateOne
  field_simp [ne_of_lt hp, ne_of_gt hh, Real.exp_ne_zero]
  ring

theorem mainWallChart_flux {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) :
    |normalizedSectionFlux (mainWallChart h y) (mainWallChartFrame h y)| = mainWallChartDensity h y := by
  rw [mainWallChart_signed_flux hh hy, abs_neg, abs_of_pos (mainWallChartDensity_pos hh hy)]

theorem mainWallChart_flux_linear {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) (L : SectionCoordinates →L[ℝ] SectionCoordinates) :
    |normalizedSectionFlux (mainWallChart h y)
        (fun i => mainWallChartDifferential h y (L (Pi.single i 1)))| =
      mainWallChartDensity h y * |L.det| := by
  let x := mainWallChart h y
  let f : SectionCoordinates [⋀^Fin 3]→ₗ[ℝ] ℝ :=
    (normalizedVolumeWeight x)⁻¹ •
      ((normalizedAmbientVolume.curryLeft ((1 / 2 : ℝ) • x)).curryLeft (normalizedField x)).compLinearMap
        (mainWallChartDifferential h y).toLinearMap
  let b := Pi.basisFun ℝ (Fin 3)
  have hd : b.det (L ∘ b) = L.det := by
    convert! b.det_comp L.toLinearMap b using 1
    simp only [b.det_self, mul_one]
  have H : f (L ∘ b) = L.det * f b := by
    calc
      f (L ∘ b) = (f b • b.det) (L ∘ b) := congrArg (fun a => a (L ∘ b)) (f.eq_smul_basis_det b)
      _ = L.det * f b := by
        change f b * b.det (L ∘ b) = L.det * f b
        rw [hd, mul_comm]
  have hf (v : Fin 3 → SectionCoordinates) :
      f v = normalizedSectionFlux x (fun i => mainWallChartDifferential h y (v i)) := by
    simp only [f, AlternatingMap.smul_apply, AlternatingMap.compLinearMap_apply,
      AlternatingMap.curryLeft_apply_apply, smul_eq_mul,
      normalizedSectionFlux, normalizedConstraintVolume, div_eq_mul_inv]
    rw [mul_comm]
    congr 1
  rw [hf, hf] at H
  have heq : normalizedSectionFlux x (fun i => mainWallChartDifferential h y (L (Pi.single i 1))) =
      L.det * normalizedSectionFlux x (mainWallChartFrame h y) := by
    simp only [b, Pi.basisFun_apply, Function.comp_apply] at H
    convert! H using 1
  rw [heq, abs_mul, mainWallChart_flux hh hy, mul_comm]

end BianchiIX

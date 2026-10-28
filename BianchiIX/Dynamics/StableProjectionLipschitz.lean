import BianchiIX.Dynamics.StableProjectionDifferential

noncomputable section

namespace BianchiIX

open Set

theorem exists_stableBoundaryProjection_uniform_fderiv :
    ∃ C ≥ (1 : ℝ), ∀ y : StableState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 2| < 1 / 200 →
      ‖fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y‖ ≤ C := by
  let A : ℝ := 128 / 100 + 33000 * (1 / 100) ^ 2 * Real.exp (512 / 100)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨1 + 2 * A, by linarith only [hA], ?_⟩
  intro y hm hu hw
  have hb : |y 1| + |y 2| ≤ 1 / 100 := by linarith only [hu, hw]
  have HA : stableCenterTailCoefficient y ≤ A := by
    unfold stableCenterTailCoefficient A
    gcongr <;> linarith only [hb]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have HD := stableBoundaryProjection_fderiv_drift hm (by simp : |y 0 - y 0| < 1 / 40) hu hw v
  have HB := (stableVariationCenterBudget_le_norm y v).trans (mul_le_mul_of_nonneg_right HA (norm_nonneg v))
  have H0 : |v 0| ≤ ‖v‖ := norm_le_pi_norm v 0
  have Habs := abs_add_le (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y v - v 0) (v 0)
  rw [sub_add_cancel] at Habs
  change |fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y v| ≤ _
  nlinarith only [Habs, HD, HB, H0]

/-- The stable projection is uniformly Lipschitz on an unbounded center strip, including both zero-wall faces. -/
theorem exists_stableBoundaryProjection_lipschitz :
    ∃ C ≥ (1 : ℝ), ∀ x y : StableState,
      2 ≤ x 0 → |x 1| ≤ 1 / 400 → |x 2| ≤ 1 / 400 →
      2 ≤ y 0 → |y 1| ≤ 1 / 400 → |y 2| ≤ 1 / 400 →
      |stableBoundaryProjection (y 0) (y 1) (y 2) - stableBoundaryProjection (x 0) (x 1) (x 2)| ≤ C * ‖y - x‖ := by
  obtain ⟨C, hC, HC⟩ := exists_stableBoundaryProjection_uniform_fderiv
  refine ⟨C, hC, ?_⟩
  intro x y hxm hxu hxw hym hyu hyw
  let lo : StableState := ![2, -(1 / 400), -(1 / 400)]
  let hi : StableState := ![max (x 0) (y 0), 1 / 400, 1 / 400]
  let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  have hcoords {z : StableState} (hz : z ∈ Icc lo hi) : 2 ≤ z 0 ∧ |z 1| < 1 / 200 ∧ |z 2| < 1 / 200 := by
    refine ⟨hz.1 0, ?_, ?_⟩
    · have H : |z 1| ≤ 1 / 400 := abs_le.mpr ⟨hz.1 1, hz.2 1⟩
      linarith only [H]
    · have H : |z 2| ≤ 1 / 400 := abs_le.mpr ⟨hz.1 2, hz.2 2⟩
      linarith only [H]
  have hmem {z : StableState} (hm : 2 ≤ z 0) (hhi : z 0 ≤ max (x 0) (y 0))
      (hu : |z 1| ≤ 1 / 400) (hw : |z 2| ≤ 1 / 400) : z ∈ Icc lo hi := by
    constructor
    · intro i
      fin_cases i
      · exact hm
      · exact (abs_le.mp hu).1
      · exact (abs_le.mp hw).1
    · intro i
      fin_cases i
      · exact hhi
      · exact (abs_le.mp hu).2
      · exact (abs_le.mp hw).2
  have hdiff (z : StableState) (hz : z ∈ Icc lo hi) : DifferentiableAt ℝ P z :=
    (contDiffAt_stableBoundaryProjection_one (hcoords hz).1 (hcoords hz).2.1 (hcoords hz).2.2).differentiableAt (by norm_num)
  have hbound (z : StableState) (hz : z ∈ Icc lo hi) : ‖fderiv ℝ P z‖ ≤ C :=
    HC z (hcoords hz).1 (hcoords hz).2.1 (hcoords hz).2.2
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_Icc lo hi)
    (hmem hxm (le_max_left _ _) hxu hxw) (hmem hym (le_max_right _ _) hyu hyw)

end BianchiIX

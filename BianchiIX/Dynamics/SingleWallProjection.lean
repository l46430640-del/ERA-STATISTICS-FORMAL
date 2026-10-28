import BianchiIX.Algebra.SingleWallProjection
import BianchiIX.Dynamics.SingleWallExit
import BianchiIX.Dynamics.TaubDistance

noncomputable section

namespace BianchiIX

def singleWallProjection (x : NormalizedState) : NormalizedState :=
  ![singleWallProjectionScale (x 0) (x 1) (x 2) * x 0,
    singleWallProjectionScale (x 0) (x 1) (x 2) * x 1, x 2, 0, 0]

/-- Constraint-preserving projection with both the analytic and physical distance bounds. -/
theorem normalized_singleWall_projection {x : NormalizedState} {Δ : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hnmax : x 2 ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ x 2 / 8)
    (hprod : normalizedWallProductsBound Δ x) :
    stateConstraint (singleWallProjection x) = 1 ∧
      singleWallProjection x 2 = x 2 ∧ singleWallProjection x 3 = 0 ∧
      singleWallProjection x 4 = 0 ∧
      ‖singleWallProjection x - x‖ ≤ Δ ^ 2 / x 2 ∧
      normalizedEuclideanDistance (singleWallProjection x) x ≤ 2 * Δ ^ 2 / x 2 ∧
      |rateOne (singleWallProjection x 0) (singleWallProjection x 1) - rateOne (x 0) (x 1)| ≤
        9 * Δ ^ 2 := by
  have hscale := singleWall_projection_scale_bounds hc hp.1 hnmax hp.2.1.le hp.2.2.le hΔ hprod.1 hprod.2.2
  obtain ⟨hep, hes, her⟩ := singleWall_projection_errors hc hp.1 hnmax hp.2.1.le hp.2.2.le hΔ hprod.1 hprod.2.2
  have hweak := (weak_wall_sum_of_products hp.1 le_rfl hp.2.1.le hp.2.2.le hΔ hprod.1 hprod.2.2).1
  let E := Δ ^ 2 / x 2
  have hE : 0 ≤ E := div_nonneg (sq_nonneg Δ) hp.1.le
  have hshear : 4 * Δ ^ 2 ≤ E := by
    apply (le_div_iff₀ hp.1).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hnmax (sq_nonneg Δ)]
  have hweak' : x 3 + x 4 ≤ E / 2 := by
    convert hweak using 1
    dsimp [E]
    ring
  have hcoords (i : Fin 5) : |singleWallProjection x i - x i| ≤ E := by
    fin_cases i
    · exact hep.trans hshear
    · exact hes.trans hshear
    · simpa [singleWallProjection] using hE
    · simpa [singleWallProjection, abs_of_pos hp.2.1] using
        (show x 3 ≤ E by linarith only [hweak', hp.2.2, hE])
    · simpa [singleWallProjection, abs_of_pos hp.2.2] using
        (show x 4 ≤ E by linarith only [hweak', hp.2.1, hE])
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_, her⟩
  · change shearSq _ _ + curvature (x 2) 0 0 = 1
    dsimp [singleWallProjection]
    rw [hscale.2.2.1]
    dsimp [curvature]
    ring
  · exact (pi_norm_le_iff_of_nonneg hE).mpr (fun i => by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hcoords i)
  · have H (i : Fin 5) : (singleWallProjection x i - x i) ^ 2 ≤ E ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hE).mpr (hcoords i)
    have Hd := normalizedEuclideanDistance_sq (singleWallProjection x) x
    simp [Fin.sum_univ_succ, singleWallProjection] at Hd
    change normalizedEuclideanDistance (singleWallProjection x) x ^ 2 = _ at Hd
    have h0 := H 0
    have h1 := H 1
    have h3 := H 3
    have h4 := H 4
    dsimp [singleWallProjection] at h0 h1 h3 h4
    have Hsum : normalizedEuclideanDistance (singleWallProjection x) x ^ 2 ≤ 4 * E ^ 2 := by
      nlinarith only [Hd, h0, h1, h3, h4]
    have Hdist : normalizedEuclideanDistance (singleWallProjection x) x ≤ 2 * E := by
      nlinarith only [Hsum, hE, normalizedEuclideanDistance_nonneg (singleWallProjection x) x]
    convert Hdist using 1
    dsimp [E]
    ring

theorem singleWall_projection_growth {x : NormalizedState} {Δ c : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hnmax : x 2 ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ x 2 / 8)
    (hprod : normalizedWallProductsBound Δ x)
    (hgrowth : c ≤ rateOne (x 0) (x 1)) (hsmall : Δ ^ 2 ≤ c / 18) :
    c / 2 ≤ rateOne (singleWallProjection x 0) (singleWallProjection x 1) := by
  have H := (normalized_singleWall_projection hc hp hnmax hΔ hprod).2.2.2.2.2.2
  have Hlo := (abs_le.mp H).1
  linarith only [Hlo, hgrowth, hsmall]

end BianchiIX

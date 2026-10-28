import BianchiIX.Analysis.VanishingAxis

noncomputable section

namespace BianchiIX

open Set

/-- A stationary axis makes the full derivative proportional to the transverse distance. -/
theorem exists_fderiv_bound_of_stationary_axis
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℝ × E → V} {R : ℝ}
    (hreg : ∀ x : ℝ × E, ‖x‖ ≤ R → ContDiffAt ℝ 3 F x)
    (haxis : ∀ n : ℝ, |n| ≤ R → fderiv ℝ F (n, 0) = 0) :
    ∃ C ≥ (1 : ℝ), ∀ x : ℝ × E, ‖x‖ ≤ R → ‖fderiv ℝ F x‖ ≤ C * ‖x.2‖ := by
  let S := Metric.closedBall (0 : ℝ × E) R
  have hregS (x : ℝ × E) (hx : x ∈ S) := hreg x (by simpa [S] using hx)
  have hc : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ F) x‖) S := by
    intro x hx
    exact (((hregS x hx).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ × E) R).exists_bound_of_continuousOn hc
  let C := max B 1
  have hb (x : ℝ × E) (hx : x ∈ S) : ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ C :=
    (le_abs_self _).trans ((hB x hx).trans (le_max_left _ _))
  have hD (x : ℝ × E) (hx : x ∈ S) : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hregS x hx).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx
  have hn : |x.1| ≤ R := (norm_fst_le x).trans hx
  have hax : (x.1, (0 : E)) ∈ S := by
    simpa [S, Prod.norm_def] using hn
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hD hb
    (convex_closedBall (0 : ℝ × E) R) hax (by simpa [S] using hx)
  simpa [haxis x.1 hn, Prod.norm_def] using H

end BianchiIX

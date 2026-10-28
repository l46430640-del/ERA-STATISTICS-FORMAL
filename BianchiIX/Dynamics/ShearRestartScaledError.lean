import BianchiIX.Dynamics.RestartProjectionError

noncomputable section

namespace BianchiIX

open Set

theorem contDiffAt_restartProjectionScaledError_shear_axis {X : RestartProjectionCenter}
    (hs : X 0 ≠ 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartProjectionScaledError (0, X) := by
  apply contDiffAt_restartProjectionScaledError
  · simp
  · simp only [restartProjectionScaledDenom, Pi.zero_apply, zero_mul, sub_zero, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith only [sq_pos_of_ne_zero hs, sq_nonneg (X 1)]
  · simp only [Pi.zero_apply, sub_zero]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg _)

/-- A nonzero shear replaces the positive active-wall lower bound in the compact phase comparison. -/
theorem exists_shearRestartProjectionScaledError_bounds {c M : ℝ} (hc : 0 < c) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ),
      ∀ X : RestartProjectionCenter, c ≤ |X 0| → |X 0| ≤ M → |X 1| ≤ M →
        ∀ u : RestartProjectionNormal, ‖u‖ ≤ δ →
          ContDiffAt ℝ 2 restartProjectionScaledError (u, X) ∧
          |restartProjectionScaledError (u, X)| ≤ C * ‖u‖ ∧
          ‖fderiv ℝ restartProjectionScaledError (u, X)‖ ≤ C ∧
          ∀ w : RestartProjectionCenter,
            |fderiv ℝ restartProjectionScaledError (u, X) (0, w)| ≤ C * ‖u‖ * ‖w‖ := by
  let K : Set RestartProjectionCenter := Metric.closedBall 0 M ∩ {X | c ≤ |X 0|}
  have hK : IsCompact K := (isCompact_closedBall 0 M).inter_right
    (isClosed_le continuous_const ((continuous_apply 0).abs))
  have hreg (X : RestartProjectionCenter) (hX : X ∈ K) :
      ContDiffAt ℝ 2 restartProjectionScaledError (0, X) := by
    apply contDiffAt_restartProjectionScaledError_shear_axis
    have H : 0 < |X 0| := hc.trans_le hX.2
    exact abs_pos.mp H
  obtain ⟨δ, hδ, C, hC, H⟩ := exists_compact_vanishing_slice_bounds hK hreg restartProjectionScaledError_axis
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro X hXlo hX₀ hX₁ u hu
  have hX : X ∈ K := by
    refine ⟨?_, hXlo⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg ((abs_nonneg (X 0)).trans hX₀)).mpr
    intro i
    fin_cases i
    · exact hX₀
    · exact hX₁
  exact H X hX u hu

end BianchiIX

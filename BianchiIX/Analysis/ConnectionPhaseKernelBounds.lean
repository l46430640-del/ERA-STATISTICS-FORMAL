import BianchiIX.Analysis.ConnectionPhaseKernel
import BianchiIX.Analysis.ConnectionAmplitudeBounds

noncomputable section

namespace BianchiIX

theorem connectionPhaseB_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseB m u v w| ≤ 6 / μ ^ 3 ∧
    |connectionPhaseBPartials m u v w 0| ≤ 40 / μ ^ 4 ∧
    |connectionPhaseBPartials m u v w 1| ≤ 36 * u / μ ^ 4 ∧
    |connectionPhaseBPartials m u v w 2| ≤ 100 * v ^ 2 / μ ^ 5 + 12 * u * v / μ ^ 4 ∧
    |connectionPhaseBPartials m u v w 3| ≤ 100 * w ^ 2 / μ ^ 5 + 12 * u * w / μ ^ 4 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hu0 := hu.1
  have hK := matchingPhase_kernel_derivative_bounds hμ hm hv hw
  have hvar := matchingPhase_inverse_weighted_bounds hμ hm hv hw
  have hS := (connection_amplitude_base_bounds hμ hm hu hv hw).2.2.2
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have hD2 : μ ^ 2 / 4 ≤ connectionSpeed m u v w ^ 2 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ μ / 2) hD 2
    nlinarith only [H]
  have div_bound (x K : ℝ) (hx : |x| ≤ K) : |x / connectionSpeed m u v w| ≤ 2 * K / μ := by
    rw [abs_div, abs_of_pos hD0]
    exact (div_le_div₀ ((abs_nonneg x).trans hx) hx (by positivity) hD).trans_eq (by ring)
  have div_sq_bound (x K : ℝ) (hx : |x| ≤ K) : |x / connectionSpeed m u v w ^ 2| ≤ 4 * K / μ ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos hD0 2)]
    exact (div_le_div₀ ((abs_nonneg x).trans hx) hx (by positivity) hD2).trans_eq (by ring)
  have wall_bound (r e q : ℝ) (hr : 0 ≤ r) (he : |e| ≤ 3 * r ^ 2 / μ)
      (hq : |q| ≤ 32 * r ^ 2 / μ ^ 4) :
      |q / connectionSpeed m u v w - matchingPhaseKernel m v w * (e - u * r) / connectionSpeed m u v w ^ 2| ≤
        100 * r ^ 2 / μ ^ 5 + 12 * u * r / μ ^ 4 := by
    have hdiff : |e - u * r| ≤ 3 * r ^ 2 / μ + u * r := by
      simpa only [abs_of_nonneg (mul_nonneg hu0 hr)] using (abs_sub e (u * r)).trans (add_le_add he le_rfl)
    have hnum : |matchingPhaseKernel m v w * (e - u * r)| ≤
        (3 / μ ^ 2) * (3 * r ^ 2 / μ + u * r) := by
      rw [abs_mul]
      exact mul_le_mul hK.1 hdiff (abs_nonneg _) (by positivity)
    exact ((abs_sub _ _).trans (add_le_add (div_bound _ _ hq) (div_sq_bound _ _ hnum))).trans_eq (by ring)
  refine ⟨(div_bound _ _ hK.1).trans_eq (by ring), ?_, ?_,
    wall_bound v _ _ hv.1 hvar.2.1 hK.2.2.2.1, wall_bound w _ _ hw.1 hvar.2.2 hK.2.2.2.2⟩
  · have hnum : |matchingPhaseKernel m v w * (1 / matchingPhaseSlope m v w)| ≤ (3 / μ ^ 2) * (4 / 3) := by
      rw [abs_mul]
      exact mul_le_mul hK.1 hvar.1 (abs_nonneg _) (by positivity)
    exact ((abs_sub _ _).trans (add_le_add (div_bound _ _ hK.2.2.1) (div_sq_bound _ _ hnum))).trans_eq (by ring)
  · have hnum : |matchingPhaseKernel m v w * (-u * (v + w - 2 * u))| ≤ (3 / μ ^ 2) * (u * 3) := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hu0]
      exact mul_le_mul hK.1 (mul_le_mul_of_nonneg_left hS hu0) (by positivity) (by positivity)
    change |0 / connectionSpeed m u v w - matchingPhaseKernel m v w * (-u * (v + w - 2 * u)) /
      connectionSpeed m u v w ^ 2| ≤ _
    rw [zero_div, zero_sub, abs_neg]
    exact (div_sq_bound _ _ hnum).trans_eq (by ring)

end BianchiIX

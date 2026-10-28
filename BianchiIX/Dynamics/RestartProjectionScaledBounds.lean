import BianchiIX.Dynamics.RestartProjectionScaling
import BianchiIX.Analysis.CompactVanishingSlice

noncomputable section

namespace BianchiIX

open Set

theorem exists_restartProjectionScaledError_bounds {c M : ℝ} (hc : 0 < c) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ),
      ∀ X : RestartProjectionCenter, |X 0| ≤ M → X 1 ∈ Icc c M →
        ∀ u : RestartProjectionNormal, ‖u‖ ≤ δ →
          ContDiffAt ℝ 2 restartProjectionScaledError (u, X) ∧
          |restartProjectionScaledError (u, X)| ≤ C * ‖u‖ ∧
          ‖fderiv ℝ restartProjectionScaledError (u, X)‖ ≤ C ∧
          ∀ w : RestartProjectionCenter,
            |fderiv ℝ restartProjectionScaledError (u, X) (0, w)| ≤ C * ‖u‖ * ‖w‖ := by
  let K : Set RestartProjectionCenter := Icc ![-M, c] ![M, M]
  have hK : IsCompact K := isCompact_Icc
  have hreg (X : RestartProjectionCenter) (hX : X ∈ K) :
      ContDiffAt ℝ 2 restartProjectionScaledError (0, X) := by
    have H : c ≤ X 1 := hX.1 1
    exact contDiffAt_restartProjectionScaledError_axis (ne_of_gt (hc.trans_le H)) 2
  obtain ⟨δ, hδ, C, hC, H⟩ := exists_compact_vanishing_slice_bounds hK hreg restartProjectionScaledError_axis
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro X hX₀ hX₁ u hu
  have hX : X ∈ K := by
    constructor
    · intro i
      fin_cases i
      · exact (abs_le.mp hX₀).1
      · exact hX₁.1
    · intro i
      fin_cases i
      · exact (abs_le.mp hX₀).2
      · exact hX₁.2
  exact H X hX u hu

/-- Separate normal and tangential directions before estimating the full differential. -/
theorem restartProjectionScaledError_direction_bound {u du : RestartProjectionNormal}
    {X dX : RestartProjectionCenter} {C : ℝ}
    (HD : ‖fderiv ℝ restartProjectionScaledError (u, X)‖ ≤ C)
    (HT : ∀ w : RestartProjectionCenter,
      |fderiv ℝ restartProjectionScaledError (u, X) (0, w)| ≤ C * ‖u‖ * ‖w‖) :
    |fderiv ℝ restartProjectionScaledError (u, X) (du, dX)| ≤ C * ‖du‖ + C * ‖u‖ * ‖dX‖ := by
  have HN : |fderiv ℝ restartProjectionScaledError (u, X) (du, 0)| ≤ C * ‖du‖ := by
    have H := ((fderiv ℝ restartProjectionScaledError (u, X)).le_opNorm (du, 0)).trans
      (mul_le_mul_of_nonneg_right HD (norm_nonneg (du, (0 : RestartProjectionCenter))))
    simpa only [Real.norm_eq_abs, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg du)] using H
  have heq : (du, dX) = (du, (0 : RestartProjectionCenter)) + ((0 : RestartProjectionNormal), dX) := by simp
  rw [heq, map_add]
  exact (abs_add_le _ _).trans (add_le_add HN (HT dX))

end BianchiIX

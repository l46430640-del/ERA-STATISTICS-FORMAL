import BianchiIX.Algebra.MatchingPhase

noncomputable section

namespace BianchiIX

theorem phaseNorm_le_abs_add (a b : ℝ) : phaseNorm a b ≤ |a| + |b| := by
  have hr : 0 ≤ phaseNorm a b := Real.sqrt_nonneg _
  have hs := phaseNorm_sq a b
  nlinarith only [hr, hs, sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

/-- Comparison with a positive boundary radius does not require differentiating the norm at zero. -/
theorem phaseNorm_boundary_error {a b c : ℝ} (hc : 0 ≤ c) :
    |phaseNorm a b - c| ≤ |a - c| + |b| := by
  have hr : 0 ≤ phaseNorm a b := Real.sqrt_nonneg _
  have hrad : a ≤ phaseNorm a b := by nlinarith only [phaseNorm_sq a b, hr, sq_nonneg b]
  have ha : |a| ≤ |a - c| + c := by
    have H := abs_add_le (a - c) c
    simpa only [sub_add_cancel, abs_of_nonneg hc] using H
  apply abs_le.mpr
  constructor
  · linarith only [hrad, neg_abs_le (a - c), abs_nonneg b]
  · linarith only [phaseNorm_le_abs_add a b, ha]

end BianchiIX

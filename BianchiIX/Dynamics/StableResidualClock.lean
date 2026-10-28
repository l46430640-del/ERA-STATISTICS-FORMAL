import BianchiIX.Dynamics.StableHessianClockBounds

noncomputable section

namespace BianchiIX

def stableResidualClock (K : ℝ) (y : StableState) : ℝ := 6 * K / stableBoundaryDenom y

theorem contDiff_stableResidualClock (n : WithTop ℕ∞) (K : ℝ) :
    ContDiff ℝ n (stableResidualClock K) := by
  unfold stableResidualClock
  exact contDiff_const.div (contDiff_stableBoundaryDenom n) (fun y => (stableBoundaryDenom_pos y).ne')

theorem hasDerivAt_stableResidualClock {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (K : ℝ) :
    HasDerivAt (fun s => stableResidualClock K (gamma s))
      (-(6 * K / stableBoundaryDenom (gamma t) ^ 2) * dotProduct (stableDenomGradient (gamma t)) v) t := by
  have H := (hasDerivAt_const t (6 * K)).div (hasDerivAt_stableBoundaryDenom h)
    (stableBoundaryDenom_pos (gamma t)).ne'
  convert! H using 1
  simp
  ring

theorem stableResidualClock_fderiv (K : ℝ) (y v : StableState) :
    fderiv ℝ (stableResidualClock K) y v =
      -(6 * K / stableBoundaryDenom y ^ 2) * dotProduct (stableDenomGradient y) v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_stableResidualClock 1 K).differentiable (by norm_num) y).hasFDerivAt
  have H := (show HasFDerivAt (stableResidualClock K) (fderiv ℝ (stableResidualClock K) y)
      (y + (0 : ℝ) • v) by simpa using hd).comp_hasDerivAt 0 hl
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_stableResidualClock hl K)

theorem stableResidualClock_fderiv2 (K : ℝ) (y v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableResidualClock K)) y v w =
      stableResidualClock K y *
        (2 * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
          (dotProduct (stableDenomGradient y) w / stableBoundaryDenom y) -
          stableDenomHessian v w / stableBoundaryDenom y) := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_stableResidualClock 2 K).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have Hleft := hasDerivAt_fderiv_apply_const (hd (y + (0 : ℝ) • v)) hl w
  simp only [stableResidualClock_fderiv] at Hleft
  have hD := hasDerivAt_stableBoundaryDenom hl
  have hG := hasDerivAt_stableDenomGradient_dotProduct hl w
  have Hright := (((hasDerivAt_const (0 : ℝ) (6 * K)).div (hD.pow 2)
    (pow_ne_zero 2 (stableBoundaryDenom_pos _).ne')).neg).mul hG
  have H := Hleft.unique Hright
  simp only [Pi.pow_apply, Pi.div_apply, Pi.neg_apply, zero_smul, add_zero] at H
  rw [H]
  unfold stableResidualClock
  have hn := (stableBoundaryDenom_pos y).ne'
  field_simp
  ring

end BianchiIX

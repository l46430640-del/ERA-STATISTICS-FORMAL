import BianchiIX.Dynamics.StableSecondDifferential
import BianchiIX.Dynamics.StableOriginalHessian

noncomputable section

namespace BianchiIX

def stableRescaledVariationRate (K : ℝ) (w : StableState) (p : StableState × ℝ) : StableState :=
  K • fderiv ℝ stableOriginalField (stableRescaledFlow K p.1 p.2)
    (stableRescaledDifferential K p.1 p.2 w)

def stableRescaledSecondSource (K : ℝ) (v w : StableState) (p : StableState × ℝ) : StableState :=
  K • (stableOriginalHessian (stableRescaledFlow K p.1 p.2)
      (stableRescaledDifferential K p.1 p.2 v) (stableRescaledDifferential K p.1 p.2 w) +
    (stableOriginalJacobian (stableRescaledFlow K p.1 p.2)).mulVec
      (stableRescaledSecondDifferential K p.1 p.2 v w))

theorem contDiffAt_stableRescaledVariationRate_one {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (w : StableState) :
    ContDiffAt ℝ 1 (stableRescaledVariationRate K w) (y, s) := by
  have hF := (contDiffAt_stableRescaledFlow_two hK hc hm hu hw hs).of_le
    (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hD := ((contDiff_stableOriginalField 2).fderiv_right
    (m := 1) (by norm_num)).contDiffAt.comp (y, s) hF
  have hJ := (contDiffAt_stableRescaledDifferential_one hK hc hm hu hw hs).clm_apply
    (contDiffAt_const (c := w))
  exact (contDiffAt_const (c := K)).smul (hD.clm_apply hJ)

theorem stableRescaledVariationRate_fderiv_initial {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    fderiv ℝ (stableRescaledVariationRate K w) (y, s) (v, 0) =
      stableRescaledSecondSource K v w (y, s) := by
  have hF := hasFDerivAt_stableRescaledFlow hK hc hm hu hw hs
  have hJ := (hasFDerivAt_stableRescaledDifferential hK hc hm hu hw hs).clm_apply
    (hasFDerivAt_const w y)
  have hD := (((contDiff_stableOriginalField 2).fderiv_right
    (m := 1) (by norm_num)).differentiable (by norm_num)
      (stableRescaledFlow K y s)).hasFDerivAt.comp y hF
  have H := (hD.clm_apply hJ).const_smul K
  have hpartial := ((contDiffAt_stableRescaledVariationRate_one hK hc hm hu hw hs w).differentiableAt
    (by norm_num)).hasFDerivAt.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y s)
  have Heq := congrArg (fun L : StableState →L[ℝ] StableState => L v) (hpartial.unique H)
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    smul_apply, add_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add, stableOriginalField_fderiv2,
    stableOriginalField_fderiv, stableRescaledSecondSource, add_comm] using Heq

end BianchiIX

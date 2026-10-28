import BianchiIX.Dynamics.StableBoundaryHessian

noncomputable section

namespace BianchiIX

def stableOriginalHessian (y v w : StableState) : StableState :=
  (6 / stableBoundaryDenom y) • stableBoundaryHessian y v w -
    (6 / stableBoundaryDenom y ^ 2) •
      (dotProduct (stableDenomGradient y) v • (stableBoundaryJacobian y).mulVec w +
        dotProduct (stableDenomGradient y) w • (stableBoundaryJacobian y).mulVec v +
        stableDenomHessian v w • stableBoundaryField y) +
    (12 * dotProduct (stableDenomGradient y) v * dotProduct (stableDenomGradient y) w /
      stableBoundaryDenom y ^ 3) • stableBoundaryField y

theorem stableOriginalJacobian_mulVec (y v : StableState) :
    (stableOriginalJacobian y).mulVec v =
      (6 / stableBoundaryDenom y) • (stableBoundaryJacobian y).mulVec v -
        (6 * dotProduct (stableDenomGradient y) v / stableBoundaryDenom y ^ 2) •
          stableBoundaryField y := by
  ext i
  simp [stableOriginalJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem hasDerivAt_stableOriginalJacobian_mulVec
    {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (w : StableState) :
    HasDerivAt (fun s => (stableOriginalJacobian (gamma s)).mulVec w)
      (stableOriginalHessian (gamma t) v w) t := by
  simp only [stableOriginalJacobian_mulVec]
  have hD := hasDerivAt_stableBoundaryDenom h
  have hg := hasDerivAt_stableDenomGradient_dotProduct h w
  have hJ := hasDerivAt_stableBoundaryJacobian_mulVec h w
  have hf := hasDerivAt_stableBoundaryField h
  have hpos := stableBoundaryDenom_pos (gamma t)
  apply ((((hasDerivAt_const t (6 : ℝ)).div hD hpos.ne').smul hJ).sub
    (((hg.const_mul 6).div (hD.pow 2) (pow_ne_zero 2 hpos.ne')).smul hf)).congr_deriv
  ext i
  dsimp [stableOriginalHessian]
  field_simp
  ring

theorem stableOriginalField_fderiv2 (y v w : StableState) :
    fderiv ℝ (fderiv ℝ stableOriginalField) y v w = stableOriginalHessian y v w := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hD : Differentiable ℝ (fderiv ℝ stableOriginalField) :=
    ((contDiff_stableOriginalField 2).fderiv_right
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have H := hasDerivAt_fderiv_apply_const (hD (y + (0 : ℝ) • v)) hl w
  simp only [stableOriginalField_fderiv] at H
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_stableOriginalJacobian_mulVec hl w)

theorem stableOriginalHessian_symm (y v w : StableState) :
    stableOriginalHessian y v w = stableOriginalHessian y w v := by
  ext i
  simp only [stableOriginalHessian, stableBoundaryHessian_symm y v w, stableDenomHessian_symm v w,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem stableOriginalHessian_strong_zero {y v w : StableState}
    (hy : y 1 = 0) (hv : v 1 = 0) (hw : w 1 = 0) :
    stableOriginalHessian y v w 1 = 0 := by
  simp [stableOriginalHessian, stableBoundaryHessian, stableBoundaryJacobian_mulVec,
    stableBoundaryField, hy, hv, hw]

theorem stableOriginalHessian_zero_walls (m : ℝ) (v w : StableState) :
    stableOriginalHessian ![m, 0, 0] v w =
      ![(6 / (3 + m ^ 2)) * (2 * m * v 1 * w 1 -
          (m + 1) * (v 1 * w 2 + v 2 * w 1) + 2 * v 2 * w 2),
        (-24 * m / (3 + m ^ 2) ^ 2) * (v 0 * w 1 + v 1 * w 0),
        (6 * (m - 1) * (m + 3) / (3 + m ^ 2) ^ 2) * (v 0 * w 2 + v 2 * w 0)] := by
  have hD : (3 : ℝ) + m ^ 2 ≠ 0 := ne_of_gt (by positivity)
  ext i
  fin_cases i <;>
    simp [stableOriginalHessian, stableBoundaryHessian, stableDenomHessian,
      stableBoundaryJacobian_mulVec, stableDenomGradient_dotProduct, stableBoundaryDenom,
      stableBoundaryField, stableStrongRate, stableWeakRate] <;>
    field_simp <;> ring

end BianchiIX

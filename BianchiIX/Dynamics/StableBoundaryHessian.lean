import BianchiIX.Dynamics.StableBoundaryLinearization
import BianchiIX.Analysis.HessianEvaluation

noncomputable section

namespace BianchiIX

def stableBoundaryHessian (y v w : StableState) : StableState :=
  ![(2 * y 1 - y 2) * (v 0 * w 1 + v 1 * w 0) -
      y 1 * (v 0 * w 2 + v 2 * w 0) + 2 * y 0 * v 1 * w 1 -
      (y 0 + 1) * (v 1 * w 2 + v 2 * w 1) + 2 * v 2 * w 2,
    -y 1 * v 0 * w 0 - y 0 * (v 0 * w 1 + v 1 * w 0) +
      3 * y 1 * v 1 * w 1 - y 2 * (v 1 * w 2 + v 2 * w 1) -
      y 1 * v 2 * w 2,
    -(v 0 * w 2 + v 2 * w 0) + 2 * y 2 * v 1 * w 1 +
      2 * (y 1 - y 2) * (v 1 * w 2 + v 2 * w 1) - 2 * y 1 * v 2 * w 2]

def stableDenomHessian (v w : StableState) : ℝ :=
  2 * v 0 * w 0 + 2 * (v 1 - v 2) * (w 1 - w 2)

theorem stableBoundaryJacobian_mulVec (y v : StableState) :
    (stableBoundaryJacobian y).mulVec v =
      ![(y 1 ^ 2 - y 1 * y 2) * v 0 + (2 * y 0 * y 1 - (y 0 + 1) * y 2) * v 1 +
          (-(y 0 + 1) * y 1 + 2 * y 2) * v 2,
        (-y 0 * y 1) * v 0 + ((1 - y 0 ^ 2 - y 2 ^ 2 + 3 * y 1 ^ 2) / 2) * v 1 +
          (-y 1 * y 2) * v 2,
        -y 2 * v 0 + (2 * y 1 - y 2) * y 2 * v 1 -
          (y 0 + 1 + 2 * y 1 * y 2 - y 1 ^ 2) * v 2] := by
  ext i
  fin_cases i <;> simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem stableDenomGradient_dotProduct (y v : StableState) :
    dotProduct (stableDenomGradient y) v =
      2 * y 0 * v 0 + 2 * (y 1 - y 2) * (v 1 - v 2) := by
  simp [stableDenomGradient, dotProduct, Fin.sum_univ_succ]
  ring

theorem hasDerivAt_stableBoundaryJacobian_mulVec
    {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (w : StableState) :
    HasDerivAt (fun s => (stableBoundaryJacobian (gamma s)).mulVec w)
      (stableBoundaryHessian (gamma t) v w) t := by
  simp only [stableBoundaryJacobian_mulVec]
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply ((((hu.pow 2).sub (hu.mul hw)).mul_const (w 0)).add
      ((((hm.const_mul 2).mul hu).sub ((hm.add_const 1).mul hw)).mul_const (w 1)) |>.add
      ((((hm.add_const 1).neg.mul hu).add (hw.const_mul 2)).mul_const (w 2))).congr_deriv
    dsimp [stableBoundaryHessian]
    ring
  · apply (((hm.neg.mul hu).mul_const (w 0)).add
      ((((((hasDerivAt_const t (1 : ℝ)).sub (hm.pow 2)).sub (hw.pow 2)).add
        ((hu.pow 2).const_mul 3)).div_const 2).mul_const (w 1)) |>.add
      ((hu.neg.mul hw).mul_const (w 2))).congr_deriv
    dsimp [stableBoundaryHessian]
    ring
  · apply (((hw.neg.mul_const (w 0)).add
      ((((hu.const_mul 2).sub hw).mul hw).mul_const (w 1))).sub
      ((((hm.add_const 1).add (((hu.const_mul 2).mul hw))).sub (hu.pow 2)).mul_const (w 2))).congr_deriv
    dsimp [stableBoundaryHessian]
    ring

theorem hasDerivAt_stableDenomGradient_dotProduct
    {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (w : StableState) :
    HasDerivAt (fun s => dotProduct (stableDenomGradient (gamma s)) w)
      (stableDenomHessian v w) t := by
  simp only [stableDenomGradient_dotProduct]
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  exact ((hm.const_mul 2).mul_const (w 0)).add
    (((hu.sub hw).const_mul 2).mul_const (w 1 - w 2))

theorem stableBoundaryField_fderiv2 (y v w : StableState) :
    fderiv ℝ (fderiv ℝ stableBoundaryField) y v w = stableBoundaryHessian y v w := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hD : Differentiable ℝ (fderiv ℝ stableBoundaryField) :=
    ((contDiff_stableBoundaryField 2).fderiv_right
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have H := hasDerivAt_fderiv_apply_const (hD (y + (0 : ℝ) • v)) hl w
  simp only [stableBoundaryField_fderiv] at H
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_stableBoundaryJacobian_mulVec hl w)

theorem stableBoundaryDenom_fderiv2 (y v w : StableState) :
    fderiv ℝ (fderiv ℝ stableBoundaryDenom) y v w = stableDenomHessian v w := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hD : Differentiable ℝ (fderiv ℝ stableBoundaryDenom) :=
    ((contDiff_stableBoundaryDenom 2).fderiv_right
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have H := hasDerivAt_fderiv_apply_const (hD (y + (0 : ℝ) • v)) hl w
  simp only [stableBoundaryDenom_fderiv] at H
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_stableDenomGradient_dotProduct hl w)

theorem stableBoundaryHessian_symm (y v w : StableState) :
    stableBoundaryHessian y v w = stableBoundaryHessian y w v := by
  ext i
  fin_cases i <;> dsimp [stableBoundaryHessian] <;> ring

theorem stableDenomHessian_symm (v w : StableState) :
    stableDenomHessian v w = stableDenomHessian w v := by
  unfold stableDenomHessian
  ring

end BianchiIX

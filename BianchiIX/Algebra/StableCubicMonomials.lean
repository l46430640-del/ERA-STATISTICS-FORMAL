import BianchiIX.Dynamics.StableBoundaryHessian

noncomputable section

namespace BianchiIX

def stableCubicMonomial (i : Fin 4) (y : StableState) : ℝ :=
  ![y 1 ^ 3, y 1 ^ 2 * y 2, y 1 * y 2 ^ 2, y 2 ^ 3] i

def stableCubicDifferential (i : Fin 4) (y v : StableState) : ℝ :=
  ![3 * y 1 ^ 2 * v 1, 2 * y 1 * y 2 * v 1 + y 1 ^ 2 * v 2,
    y 2 ^ 2 * v 1 + 2 * y 1 * y 2 * v 2, 3 * y 2 ^ 2 * v 2] i

def stableCubicHessian (i : Fin 4) (y v w : StableState) : ℝ :=
  ![6 * y 1 * v 1 * w 1,
    2 * y 2 * v 1 * w 1 + 2 * y 1 * v 1 * w 2 + 2 * y 1 * v 2 * w 1,
    2 * y 2 * v 1 * w 2 + 2 * y 2 * v 2 * w 1 + 2 * y 1 * v 2 * w 2,
    6 * y 2 * v 2 * w 2] i

theorem contDiff_stableCubicMonomial (n : WithTop ℕ∞) (i : Fin 4) :
    ContDiff ℝ n (stableCubicMonomial i) := by
  fin_cases i <;> unfold stableCubicMonomial <;> dsimp <;> fun_prop

theorem hasDerivAt_stableCubicMonomial {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (i : Fin 4) :
    HasDerivAt (fun s => stableCubicMonomial i (gamma s)) (stableCubicDifferential i (gamma t) v) t := by
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  fin_cases i
  · exact hu.pow 3
  · convert! (hu.pow 2).mul hw using 1
    dsimp [stableCubicMonomial, stableCubicDifferential]
    ring
  · convert! hu.mul (hw.pow 2) using 1
    dsimp [stableCubicMonomial, stableCubicDifferential]
    ring
  · exact hw.pow 3

theorem stableCubicMonomial_fderiv (i : Fin 4) (y v : StableState) :
    fderiv ℝ (stableCubicMonomial i) y v = stableCubicDifferential i y v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_stableCubicMonomial 1 i).differentiable (by norm_num) y).hasFDerivAt
  have H := (show HasFDerivAt (stableCubicMonomial i) (fderiv ℝ (stableCubicMonomial i) y)
      (y + (0 : ℝ) • v) by simpa using hd).comp_hasDerivAt 0 hl
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_stableCubicMonomial hl i)

theorem hasDerivAt_stableCubicDifferential {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (i : Fin 4) (w : StableState) :
    HasDerivAt (fun s => stableCubicDifferential i (gamma s) w) (stableCubicHessian i (gamma t) v w) t := by
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  fin_cases i
  · convert! ((hu.pow 2).const_mul 3).mul_const (w 1) using 1
    dsimp [stableCubicDifferential, stableCubicHessian]
    ring
  · convert! (((hu.const_mul 2).mul hw).mul_const (w 1)).add ((hu.pow 2).mul_const (w 2)) using 1
    dsimp [stableCubicDifferential, stableCubicHessian]
    ring
  · convert! ((hw.pow 2).mul_const (w 1)).add (((hu.const_mul 2).mul hw).mul_const (w 2)) using 1
    dsimp [stableCubicDifferential, stableCubicHessian]
    ring
  · convert! ((hw.pow 2).const_mul 3).mul_const (w 2) using 1
    dsimp [stableCubicDifferential, stableCubicHessian]
    ring

theorem stableCubicMonomial_fderiv2 (i : Fin 4) (y v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableCubicMonomial i)) y v w = stableCubicHessian i y v w := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_stableCubicMonomial 2 i).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have H := hasDerivAt_fderiv_apply_const (hd (y + (0 : ℝ) • v)) hl w
  simp only [stableCubicMonomial_fderiv] at H
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_stableCubicDifferential hl i w)

end BianchiIX

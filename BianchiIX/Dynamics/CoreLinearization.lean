import BianchiIX.Dynamics.CoreAuxiliary

noncomputable section

namespace BianchiIX

/-- The exact state derivative of the angle-time vector field. -/
def coreAngleJacobian (z : ℝ) (y : CoreAngleState) : Matrix (Fin 3) (Fin 3) ℝ :=
  let r := y 0
  let u := y 1
  let p := y 2
  let q := coreAuxiliary z y
  let h := coreAuxiliaryJacobian z y
  let c := q 0
  let d := q 1
  let a := q 2
  let g := q 3
  ![![h 3 0 / d - g * h 1 0 / d ^ 2,
      h 3 1 / d - g * h 1 1 / d ^ 2,
      h 3 2 / d - g * h 1 2 / d ^ 2],
    ![u * h 2 0 / d - u * a * h 1 0 / d ^ 2,
      a / d + u * h 2 1 / d - u * a * h 1 1 / d ^ 2,
      u * h 2 2 / d - u * a * h 1 2 / d ^ 2],
    ![2 * p * (1 + c) / (r ^ 2 * d) - 2 * p * h 0 0 / (r * d) +
        2 * p * (1 + c) * h 1 0 / (r * d ^ 2),
      -2 * p * h 0 1 / (r * d) + 2 * p * (1 + c) * h 1 1 / (r * d ^ 2),
      -2 * (1 + c) / (r * d) - 2 * p * h 0 2 / (r * d) +
        2 * p * (1 + c) * h 1 2 / (r * d ^ 2)]]

theorem coreAngleField_auxiliary (z : ℝ) (y : CoreAngleState) :
    coreAngleField z y = ![(coreAuxiliary z y) 3 / (coreAuxiliary z y) 1,
      y 1 * (coreAuxiliary z y) 2 / (coreAuxiliary z y) 1,
      -2 * y 2 * (1 + (coreAuxiliary z y) 0) / (y 0 * (coreAuxiliary z y) 1)] := rfl

theorem contDiffAt_coreAngleField (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : (coreAuxiliary z y) 1 ≠ 0) :
    ContDiffAt ℝ n (coreAngleField z) y := by
  have hq := contDiffAt_pi.mp (contDiffAt_coreAuxiliary n z hr)
  have hrd : y 0 * (coreAuxiliary z y) 1 ≠ 0 := mul_ne_zero hr hd
  apply contDiffAt_pi.mpr
  intro i
  simp_rw [coreAngleField_auxiliary]
  fin_cases i <;> dsimp <;> fun_prop

theorem contDiffAt_coreAngleField_joint (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : (coreAuxiliary z y) 1 ≠ 0) :
    ContDiffAt ℝ n (fun p : ℝ × CoreAngleState => coreAngleField p.1 p.2) (z, y) := by
  have hq := contDiffAt_pi.mp (contDiffAt_coreAuxiliary_joint n z hr)
  have hrd : y 0 * (coreAuxiliary z y) 1 ≠ 0 := mul_ne_zero hr hd
  apply contDiffAt_pi.mpr
  intro i
  simp_rw [coreAngleField_auxiliary]
  fin_cases i <;> dsimp <;> fun_prop

theorem hasDerivAt_coreAngleField {γ : ℝ → CoreAngleState} {ξ : CoreAngleState} {z t : ℝ}
    (hγ : HasDerivAt γ ξ t) (hr : γ t 0 ≠ 0) (hd : (coreAuxiliary z (γ t)) 1 ≠ 0) :
    HasDerivAt (fun s => coreAngleField z (γ s)) ((coreAngleJacobian z (γ t)).mulVec ξ) t := by
  have hR := hasDerivAt_pi.mp hγ 0
  have hU := hasDerivAt_pi.mp hγ 1
  have hP := hasDerivAt_pi.mp hγ 2
  have hq := hasDerivAt_pi.mp (hasDerivAt_coreAuxiliary (z := z) hγ hr)
  have hrd : γ t 0 * (coreAuxiliary z (γ t)) 1 ≠ 0 := mul_ne_zero hr hd
  apply hasDerivAt_pi.mpr
  intro i
  simp_rw [coreAngleField_auxiliary]
  fin_cases i
  · apply ((hq 3).div (hq 1) hd).congr_deriv
    simp [coreAngleJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hd]
    ring
  · apply ((hU.mul (hq 2)).div (hq 1) hd).congr_deriv
    simp [coreAngleJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hd]
    ring
  · apply (((hP.const_mul (-2)).mul ((hq 0).const_add 1)).div (hR.mul (hq 1)) hrd).congr_deriv
    simp [coreAngleJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, hd]
    ring

theorem coreAngleField_fderiv (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : (coreAuxiliary z y) 1 ≠ 0) (ξ : CoreAngleState) :
    fderiv ℝ (coreAngleField z) y ξ = (coreAngleJacobian z y).mulVec ξ := by
  have hl : HasDerivAt (fun s : ℝ => y + s • ξ) ξ 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const ξ) using 1
    simp
  have hzero : y + (0 : ℝ) • ξ = y := by simp
  have hf := ((contDiffAt_coreAngleField 1 z hr hd).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hzero.symm ▸ hf).comp_hasDerivAt 0 hl
  simpa only [hzero] using H.unique (hasDerivAt_coreAngleField hl
    (by simpa only [hzero] using hr) (by simpa only [hzero] using hd))

end BianchiIX

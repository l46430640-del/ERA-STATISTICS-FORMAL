import BianchiIX.Dynamics.CoreAngle
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

namespace BianchiIX

/-- The four scalar quantities `(C, d, a, g)` in the core variational equations. -/
def coreAuxiliary (z : ℝ) (y : CoreAngleState) : Fin 4 → ℝ :=
  let r := y 0
  let u := y 1
  let v := r / Real.cosh z
  let w := y 2 / v
  ![coupling u v w,
    coreClockFactor r u w,
    -r / 2 + Real.tanh z + w / Real.cosh z + (u ^ 2 - w ^ 2) / (2 * r),
    -coupling u v w - Real.tanh z * (u - w) ^ 2 / r]

/-- Rows are `(C, d, a, g)` and columns are `(R, U, P)` at fixed angle. -/
def coreAuxiliaryJacobian (z : ℝ) (y : CoreAngleState) : Matrix (Fin 4) (Fin 3) ℝ :=
  let r := y 0
  let u := y 1
  let v := r / Real.cosh z
  let w := y 2 / v
  let s := 1 / Real.cosh z
  let c := -Real.tanh z
  let δ := u - w
  ![![u * (s - w / r), v - 2 * u + w, u / v],
    ![2 * δ * (u - 2 * w) / r ^ 3, -2 * δ / r ^ 2, 2 * δ / (v * r ^ 2)],
    ![-1 / 2 - s * w / r + (3 * w ^ 2 - u ^ 2) / (2 * r ^ 2), u / r, (1 - w / v) / r],
    ![-u * (s - w / r) + c * δ * (3 * w - u) / r ^ 2,
      -(v - 2 * u + w) + 2 * c * δ / r, -u / v - 2 * c * δ / (r * v)]]

theorem contDiffAt_coreAuxiliary (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) : ContDiffAt ℝ n (coreAuxiliary z) y := by
  have hv : y 0 / Real.cosh z ≠ 0 := div_ne_zero hr (ne_of_gt (Real.cosh_pos z))
  have hr2 : y 0 ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr' : 2 * y 0 ≠ 0 := mul_ne_zero (by norm_num) hr
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreAuxiliary, coupling, coreClockFactor] <;> fun_prop

theorem contDiffAt_coreAuxiliary_joint (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) :
    ContDiffAt ℝ n (fun p : ℝ × CoreAngleState => coreAuxiliary p.1 p.2) (z, y) := by
  have hz : Real.cosh z ≠ 0 := ne_of_gt (Real.cosh_pos z)
  have hv : y 0 / Real.cosh z ≠ 0 := div_ne_zero hr hz
  have hr2 : y 0 ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr' : 2 * y 0 ≠ 0 := mul_ne_zero (by norm_num) hr
  have ht : ContDiffAt ℝ n (fun p : ℝ × CoreAngleState => Real.tanh p.1) (z, y) := by
    simp_rw [Real.tanh_eq_sinh_div_cosh]
    fun_prop
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreAuxiliary, coupling, coreClockFactor] <;> fun_prop

theorem hasDerivAt_coreAuxiliary {γ : ℝ → CoreAngleState} {ξ : CoreAngleState} {z t : ℝ}
    (hγ : HasDerivAt γ ξ t) (hr : γ t 0 ≠ 0) :
    HasDerivAt (fun s => coreAuxiliary z (γ s)) ((coreAuxiliaryJacobian z (γ t)).mulVec ξ) t := by
  have hR := hasDerivAt_pi.mp hγ 0
  have hU := hasDerivAt_pi.mp hγ 1
  have hP := hasDerivAt_pi.mp hγ 2
  have hV := hR.div_const (Real.cosh z)
  have hv : γ t 0 / Real.cosh z ≠ 0 := div_ne_zero hr (ne_of_gt (Real.cosh_pos z))
  have hr2 : (γ t 0) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr' : 2 * γ t 0 ≠ 0 := mul_ne_zero (by norm_num) hr
  have hW : HasDerivAt (fun s => γ s 2 / (γ s 0 / Real.cosh z))
      (-(γ t 2 / (γ t 0 / Real.cosh z)) / γ t 0 * ξ 0 + ξ 2 / (γ t 0 / Real.cosh z)) t := by
    apply (hP.div hV hv).congr_deriv
    field_simp [hr, ne_of_gt (Real.cosh_pos z)]
    ring
  have hC := hU.mul ((hV.add hW).sub hU)
  have hD := (((hU.sub hW).pow 2).div (hR.pow 2) hr2).const_sub 1
  have hA := (((hR.neg.div_const 2).add_const (Real.tanh z)).add (hW.div_const (Real.cosh z))).add
    (((hU.pow 2).sub (hW.pow 2)).div (hR.const_mul 2) hr')
  have hG := hC.neg.sub ((((hU.sub hW).pow 2).const_mul (Real.tanh z)).div hR hr)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply hC.congr_deriv
    simp [coreAuxiliaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, ne_of_gt (Real.cosh_pos z)]
    ring
  · apply hD.congr_deriv
    simp [coreAuxiliaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, ne_of_gt (Real.cosh_pos z)]
    ring
  · apply hA.congr_deriv
    simp [coreAuxiliaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, ne_of_gt (Real.cosh_pos z)]
    ring
  · apply hG.congr_deriv
    simp [coreAuxiliaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, ne_of_gt (Real.cosh_pos z)]
    ring

theorem coreAuxiliary_fderiv (z : ℝ) {y : CoreAngleState} (hr : y 0 ≠ 0) (ξ : CoreAngleState) :
    fderiv ℝ (coreAuxiliary z) y ξ = (coreAuxiliaryJacobian z y).mulVec ξ := by
  have hl : HasDerivAt (fun s : ℝ => y + s • ξ) ξ 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const ξ) using 1
    simp
  have hzero : y + (0 : ℝ) • ξ = y := by simp
  have hf := ((contDiffAt_coreAuxiliary 1 z hr).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hzero.symm ▸ hf).comp_hasDerivAt 0 hl
  simpa only [hzero] using H.unique (hasDerivAt_coreAuxiliary hl (by simpa only [hzero] using hr))

end BianchiIX

import BianchiIX.Dynamics.CoreLinearization

noncomputable section

namespace BianchiIX

/-- The logarithmic rates of `U` and `P = V W`, defined also on the zero-wall boundary. -/
def coreLogRates (z : ℝ) (y : CoreAngleState) : Fin 2 → ℝ :=
  let q := coreAuxiliary z y
  ![q 2 / q 1, -2 * (1 + q 0) / (y 0 * q 1)]

def coreLogRateJacobian (z : ℝ) (y : CoreAngleState) : Matrix (Fin 2) (Fin 3) ℝ :=
  let r := y 0
  let q := coreAuxiliary z y
  let h := coreAuxiliaryJacobian z y
  ![![h 2 0 / q 1 - q 2 * h 1 0 / q 1 ^ 2,
      h 2 1 / q 1 - q 2 * h 1 1 / q 1 ^ 2,
      h 2 2 / q 1 - q 2 * h 1 2 / q 1 ^ 2],
    ![2 * (1 + q 0) / (r ^ 2 * q 1) - 2 * h 0 0 / (r * q 1) +
        2 * (1 + q 0) * h 1 0 / (r * q 1 ^ 2),
      -2 * h 0 1 / (r * q 1) + 2 * (1 + q 0) * h 1 1 / (r * q 1 ^ 2),
      -2 * h 0 2 / (r * q 1) + 2 * (1 + q 0) * h 1 2 / (r * q 1 ^ 2)]]

theorem coreAngleField_log_rates (z : ℝ) (y : CoreAngleState) :
    coreAngleField z y 1 = y 1 * coreLogRates z y 0 ∧
      coreAngleField z y 2 = y 2 * coreLogRates z y 1 := by
  rw [coreAngleField_auxiliary]
  constructor <;> dsimp [coreLogRates] <;> ring

theorem contDiffAt_coreLogRates (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : coreAuxiliary z y 1 ≠ 0) : ContDiffAt ℝ n (coreLogRates z) y := by
  have hq := contDiffAt_pi.mp (contDiffAt_coreAuxiliary n z hr)
  have hrd : y 0 * coreAuxiliary z y 1 ≠ 0 := mul_ne_zero hr hd
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreLogRates] <;> fun_prop

theorem contDiffAt_coreLogRates_joint (n : WithTop ℕ∞) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : coreAuxiliary z y 1 ≠ 0) :
    ContDiffAt ℝ n (fun p : ℝ × CoreAngleState => coreLogRates p.1 p.2) (z, y) := by
  have hq := contDiffAt_pi.mp (contDiffAt_coreAuxiliary_joint n z hr)
  have hrd : y 0 * coreAuxiliary z y 1 ≠ 0 := mul_ne_zero hr hd
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreLogRates] <;> fun_prop

theorem hasDerivAt_coreLogRates {γ : ℝ → CoreAngleState} {ξ : CoreAngleState} {z t : ℝ}
    (hγ : HasDerivAt γ ξ t) (hr : γ t 0 ≠ 0) (hd : coreAuxiliary z (γ t) 1 ≠ 0) :
    HasDerivAt (fun s => coreLogRates z (γ s)) ((coreLogRateJacobian z (γ t)).mulVec ξ) t := by
  have hR := hasDerivAt_pi.mp hγ 0
  have hq := hasDerivAt_pi.mp (hasDerivAt_coreAuxiliary (z := z) hγ hr)
  have hrd : γ t 0 * coreAuxiliary z (γ t) 1 ≠ 0 := mul_ne_zero hr hd
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply ((hq 2).div (hq 1) hd).congr_deriv
    simp [coreLogRateJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hd]
    ring
  · apply ((((hq 0).const_add 1).const_mul (-2)).div (hR.mul (hq 1)) hrd).congr_deriv
    simp [coreLogRateJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, hd]
    ring

theorem coreLogRates_fderiv (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : coreAuxiliary z y 1 ≠ 0) (ξ : CoreAngleState) :
    fderiv ℝ (coreLogRates z) y ξ = (coreLogRateJacobian z y).mulVec ξ := by
  have hl : HasDerivAt (fun s : ℝ => y + s • ξ) ξ 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const ξ) using 1
    simp
  have hzero : y + (0 : ℝ) • ξ = y := by simp
  have hf := ((contDiffAt_coreLogRates 1 z hr hd).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hzero.symm ▸ hf).comp_hasDerivAt 0 hl
  simpa only [hzero] using H.unique (hasDerivAt_coreLogRates hl
    (by simpa only [hzero] using hr) (by simpa only [hzero] using hd))

end BianchiIX

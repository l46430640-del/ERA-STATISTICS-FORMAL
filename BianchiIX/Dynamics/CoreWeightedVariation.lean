import BianchiIX.Dynamics.CoreLinearization

noncomputable section

namespace BianchiIX

def scaleCoreVariation (k : ℝ) (ξ : CoreAngleState) : CoreAngleState :=
  ![ξ 0, k * ξ 1, ξ 2]

/-- The fixed weight is applied to tangent vectors, not differentiated with the state. -/
def coreWeightedJacobian (k z : ℝ) (y : CoreAngleState) : Matrix (Fin 3) (Fin 3) ℝ :=
  let j := coreAngleJacobian z y
  ![![j 0 0, j 0 1 / k, j 0 2], ![k * j 1 0, j 1 1, k * j 1 2],
    ![j 2 0, j 2 1 / k, j 2 2]]

theorem coreWeightedJacobian_mulVec {k : ℝ} (hk : k ≠ 0) (z : ℝ)
    (y ξ : CoreAngleState) :
    (coreWeightedJacobian k z y).mulVec (scaleCoreVariation k ξ) =
      scaleCoreVariation k ((coreAngleJacobian z y).mulVec ξ) := by
  ext i
  fin_cases i <;>
    simp [coreWeightedJacobian, scaleCoreVariation, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> field_simp [hk]

theorem coreWeightedJacobian_fderiv {k : ℝ} (hk : k ≠ 0) (z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : (coreAuxiliary z y) 1 ≠ 0) (ξ : CoreAngleState) :
    (coreWeightedJacobian k z y).mulVec (scaleCoreVariation k ξ) =
      scaleCoreVariation k (fderiv ℝ (coreAngleField z) y ξ) := by
  rw [coreAngleField_fderiv z hr hd, coreWeightedJacobian_mulVec hk]

theorem hasDerivAt_scaleCoreVariation {k z : ℝ} (hk : k ≠ 0)
    {Y ξ : ℝ → CoreAngleState}
    (hξ : HasDerivAt ξ ((coreAngleJacobian z (Y z)).mulVec (ξ z)) z) :
    HasDerivAt (fun t => scaleCoreVariation k (ξ t))
      ((coreWeightedJacobian k z (Y z)).mulVec (scaleCoreVariation k (ξ z))) z := by
  rw [coreWeightedJacobian_mulVec hk]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp hξ 0
  · exact (hasDerivAt_pi.mp hξ 1).const_mul k
  · exact hasDerivAt_pi.mp hξ 2

/-- Cancellation of the leading coupling in the radius row. -/
theorem coreWeightedJacobian_radius_strong {k z : ℝ} (hk : k ≠ 0) {y : CoreAngleState}
    (hd : (coreAuxiliary z y) 1 ≠ 0) :
    let r := y 0
    let u := y 1
    let v := r / Real.cosh z
    let w := y 2 / v
    let d := (coreAuxiliary z y) 1
    let g := (coreAuxiliary z y) 3
    (coreWeightedJacobian k z y) 0 1 + v / k =
      (2 * u - w - 2 * Real.tanh z * (u - w) / r) / (k * d) -
        v * (1 - d) / (k * d) - g * (-2 * (u - w) / r ^ 2) / (k * d ^ 2) := by
  dsimp only
  change ((-(y 0 / Real.cosh z - 2 * y 1 + y 2 / (y 0 / Real.cosh z)) +
    2 * -Real.tanh z * (y 1 - y 2 / (y 0 / Real.cosh z)) / y 0) /
    (coreAuxiliary z y) 1 - (coreAuxiliary z y) 3 *
      (-2 * (y 1 - y 2 / (y 0 / Real.cosh z)) / y 0 ^ 2) / (coreAuxiliary z y) 1 ^ 2) / k +
        (y 0 / Real.cosh z) / k = _
  field_simp [hk, hd]
  ring

/-- Combining the clock derivative with the diagonal retains its negative sign. -/
theorem coreWeightedJacobian_strong_diagonal (k z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : (coreAuxiliary z y) 1 ≠ 0) :
    let r := y 0
    let u := y 1
    let w := y 2 / (r / Real.cosh z)
    let d := (coreAuxiliary z y) 1
    let a := (coreAuxiliary z y) 2
    (coreWeightedJacobian k z y) 1 1 =
      a * (r ^ 2 + u ^ 2 - w ^ 2) / (r ^ 2 * d ^ 2) + u ^ 2 / (r * d) := by
  dsimp only
  change (coreAuxiliary z y) 2 / (coreAuxiliary z y) 1 +
    y 1 * (y 1 / y 0) / (coreAuxiliary z y) 1 - y 1 * (coreAuxiliary z y) 2 *
      (-2 * (y 1 - y 2 / (y 0 / Real.cosh z)) / y 0 ^ 2) / (coreAuxiliary z y) 1 ^ 2 = _
  generalize ha : (coreAuxiliary z y) 2 = a
  field_simp [hr, hd]
  dsimp [coreAuxiliary, coreClockFactor]
  field_simp [hr]
  ring

theorem coreWeightedJacobian_weak_diagonal (k z : ℝ) {y : CoreAngleState}
    (hr : y 0 ≠ 0) (hd : (coreAuxiliary z y) 1 ≠ 0) :
    let r := y 0
    let u := y 1
    let v := r / Real.cosh z
    let w := y 2 / v
    let d := (coreAuxiliary z y) 1
    let c := (coreAuxiliary z y) 0
    (coreWeightedJacobian k z y) 2 2 =
      -2 * (1 + c) * (r ^ 2 - u ^ 2 + w ^ 2) / (r ^ 3 * d ^ 2) -
        2 * u * w / (r * d) := by
  dsimp only
  change -2 * (1 + (coreAuxiliary z y) 0) / (y 0 * (coreAuxiliary z y) 1) -
    2 * y 2 * (y 1 / (y 0 / Real.cosh z)) / (y 0 * (coreAuxiliary z y) 1) +
      2 * y 2 * (1 + (coreAuxiliary z y) 0) *
        (2 * (y 1 - y 2 / (y 0 / Real.cosh z)) / ((y 0 / Real.cosh z) * y 0 ^ 2)) /
        (y 0 * (coreAuxiliary z y) 1 ^ 2) = _
  generalize hc : (coreAuxiliary z y) 0 = c
  field_simp [hr, hd, ne_of_gt (Real.cosh_pos z)]
  dsimp [coreAuxiliary, coreClockFactor]
  field_simp [hr, ne_of_gt (Real.cosh_pos z)]
  ring

end BianchiIX

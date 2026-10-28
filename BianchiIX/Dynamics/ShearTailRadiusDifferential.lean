import BianchiIX.Dynamics.ShearTailRadius

noncomputable section

namespace BianchiIX

def shearTailRadiusNumerator (z : NormalizedState) : ℝ :=
  curvature (z 2) (z 3) (z 4) * (z 1 ^ 2 + (z 3 - z 4) ^ 2) -
    (1 + z 0) * (z 3 - z 4) ^ 2 + Real.sqrt 3 * z 2 * z 1 * (z 3 - z 4)

def shearTailRadiusNumeratorDifferential (z v : NormalizedState) : ℝ :=
  shearTailCurvatureDifferential z v * (z 1 ^ 2 + (z 3 - z 4) ^ 2) +
    2 * curvature (z 2) (z 3) (z 4) * (z 1 * v 1 + (z 3 - z 4) * (v 3 - v 4)) -
    v 0 * (z 3 - z 4) ^ 2 - 2 * (1 + z 0) * (z 3 - z 4) * (v 3 - v 4) +
    Real.sqrt 3 * (v 2 * z 1 * (z 3 - z 4) + z 2 * v 1 * (z 3 - z 4) +
      z 2 * z 1 * (v 3 - v 4))

def shearTailRadiusRateDifferential (z v : NormalizedState) : ℝ :=
  shearTailRadiusNumeratorDifferential z v / shearTailRadius z -
    shearTailRadiusNumerator z * shearTailRadiusDifferential z v / shearTailRadius z ^ 2

theorem shearTailRadiusRate_eq_quotient (z : NormalizedState) :
    shearTailRadiusRate z = shearTailRadiusNumerator z / shearTailRadius z := by
  by_cases hR : shearTailRadius z = 0
  · simp [shearTailRadiusRate, hR]
  · dsimp only [shearTailRadiusRate, shearTailRadiusNumerator]
    field_simp
    rw [shearTailRadius_sq]

theorem hasDerivAt_shearTailRadiusNumerator {α : ℝ → NormalizedState} {v : NormalizedState} {r : ℝ}
    (hα : HasDerivAt α v r) :
    HasDerivAt (fun u => shearTailRadiusNumerator (α u)) (shearTailRadiusNumeratorDifferential (α r) v) r := by
  have Hp := hasDerivAt_pi.mp hα 0
  have Hs := hasDerivAt_pi.mp hα 1
  have Hn := hasDerivAt_pi.mp hα 2
  have Hd := (hasDerivAt_pi.mp hα 3).sub (hasDerivAt_pi.mp hα 4)
  have HQ := (hasDerivAt_shearTail_polynomials hα).1
  convert! ((HQ.mul ((Hs.pow 2).add (Hd.pow 2))).sub ((Hp.const_add 1).mul (Hd.pow 2))).add
    (((Hn.mul Hs).mul Hd).const_mul (Real.sqrt 3)) using 1
  · ext u
    dsimp only [shearTailRadiusNumerator, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
    ring
  · dsimp only [shearTailRadiusNumeratorDifferential, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
    ring

/-- The radial rate has an ordinary directional derivative with no inverse weak-wall factors. -/
theorem hasDerivAt_shearTailRadiusRate {α : ℝ → NormalizedState} {v : NormalizedState} {r : ℝ}
    (hα : HasDerivAt α v r) (hs : α r 1 ≠ 0) :
    HasDerivAt (fun u => shearTailRadiusRate (α u)) (shearTailRadiusRateDifferential (α r) v) r := by
  simp_rw [shearTailRadiusRate_eq_quotient]
  convert! (hasDerivAt_shearTailRadiusNumerator hα).div (hasDerivAt_shearTailRadius hα hs)
    (shearTailRadius_pos hs).ne' using 1
  dsimp only [shearTailRadiusRateDifferential]
  field_simp [(shearTailRadius_pos hs).ne']

/-- Constraint tangents control the radius and the negative shear branch on the full closed wall region. -/
theorem shearTailRadius_differential_bounds {a L : ℝ} {z v : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hL : 0 ≤ L) (hr : shearTailRegion a z)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : normalizedConstraintDifferential z v = 0) (hs : |v 1| ≤ 5)
    (hw : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |shearTailRadiusDifferential z v| ≤ 40 * (1 + a * L) ∧
    |v 0| ≤ 40 * a * (1 + a * L) := by
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha1]
  have hx : z 3 ≤ a := hr.2.2.2.2.1.trans ha2
  have hy : z 4 ≤ a := by linarith only [hr.2.2.2.2.2, ha.1]
  have hs0 : 0 < z 1 := by linarith only [hr.2.1, ha.1]
  have hR := shearTailRadius_pos hs0.ne'
  have HR := shearTailRadius_region_bounds ⟨ha.1, ha1⟩ hr hn.2
  have HE := shearTailRadius_energy_bounds ⟨ha.1, ha1⟩ hr hn
  have HQ := (shearTail_polynomial_variation_bounds hL hn hw).2.1
  have HQ' : |shearTailCurvatureDifferential z v| ≤ 36 * a ^ 2 * L := by
    have Hb : shearTailEnergy z ≤ 9 * a ^ 2 := by linarith only [HE.2.1, HE.2.2]
    have H := mul_le_mul_of_nonneg_right Hb hL
    nlinarith only [HQ, H]
  have Hd : |z 3 - z 4| ≤ 2 * a := (abs_sub _ _).trans (by
    rw [abs_of_nonneg hn.2.1, abs_of_nonneg hn.2.2]
    linarith only [hx, hy])
  have Hdv : |v 3 - v 4| ≤ 2 * a * L := by
    have H := (abs_sub (v 3) (v 4)).trans (add_le_add hw.2.1 hw.2.2)
    have Hx := mul_le_mul_of_nonneg_right hx hL
    have Hy := mul_le_mul_of_nonneg_right hy hL
    linarith only [H, Hx, Hy]
  have HS := mul_le_mul hr.2.2.1 hs (abs_nonneg _) (by positivity [ha.1] : 0 ≤ 3 * a)
  have HD := mul_le_mul Hd Hdv (abs_nonneg _) (by positivity [ha.1] : 0 ≤ 2 * a)
  have Hnum : |z 1 * v 1 + (z 3 - z 4) * (v 3 - v 4)| ≤ 15 * a + 4 * a ^ 2 * L := by
    have H := abs_add_le (z 1 * v 1) ((z 3 - z 4) * (v 3 - v 4))
    rw [abs_mul, abs_mul, abs_of_pos hs0] at H
    nlinarith only [H, HS, HD]
  constructor
  · dsimp only [shearTailRadiusDifferential]
    rw [abs_div, abs_of_pos hR]
    calc
      _ ≤ (15 * a + 4 * a ^ 2 * L) / (a / 2) := div_le_div₀
        (by positivity [ha.1]) Hnum (by positivity [ha.1]) HR.1
      _ = 30 + 8 * a * L := by field_simp [ha.1.ne']; ring
      _ ≤ _ := by nlinarith only [mul_nonneg ha.1.le hL]
  · rw [normalizedConstraintDifferential_shearTail] at hv
    have hp : z 0 < 0 := by linarith only [hr.1]
    have he : (-z 0) * v 0 = z 1 * v 1 + shearTailCurvatureDifferential z v / 2 := by nlinarith only [hv]
    have HEq := congrArg abs he
    rw [abs_mul, abs_of_pos (neg_pos.mpr hp)] at HEq
    have H := abs_add_le (z 1 * v 1) (shearTailCurvatureDifferential z v / 2)
    rw [abs_mul, abs_of_pos hs0, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    have Hp := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ -z 0 by linarith only [hr.1]) (abs_nonneg (v 0))
    nlinarith only [HEq, H, Hp, HS, HQ', ha.1, mul_nonneg (sq_nonneg a) hL]

end BianchiIX

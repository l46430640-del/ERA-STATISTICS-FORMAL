import BianchiIX.Dynamics.ShearTailProjection
import BianchiIX.Algebra.PhaseBoundaryStability
import BianchiIX.Algebra.CoreAngle

noncomputable section

namespace BianchiIX

/-- The small-scale shear region supplies a large growing circle before the first upward hit. -/
theorem shearTail_core_radius_bounds {a : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hc : stateConstraint z = 1)
    (hr : shearTailRegion a z) (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : toProjectiveState z 2 < 1) :
    let y := toProjectiveState z
    let k := coreRadius (y 0) (y 2)
    1 < y 0 ∧ 8 ≤ k ∧ 1 / (24 * a) ≤ k ∧ k ≤ 64 / a := by
  intro y k
  obtain ⟨_, _, _, _, _, HAl, HAu⟩ := shearTail_constraint_bounds ha
    (by linarith only [hr.1]) ⟨hr.2.1, hr.2.2.1⟩ ⟨hn.1, hr.2.2.2.1⟩
    ⟨hn.2.1, hr.2.2.2.2.1⟩ ⟨hn.2.2, hr.2.2.2.2.2⟩ hc
  have hA : 0 < 1 + z 0 := (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le HAl
  have hs : 0 < z 1 := by linarith only [hr.2.1, ha.1]
  have hsqrt : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have HMlo : 1 / (12 * a) ≤ y 0 := by
    change 1 / (12 * a) ≤ Real.sqrt 3 * z 1 / (1 + z 0)
    calc
      _ = (a / 2) / (6 * a ^ 2) := by field_simp [ha.1.ne']; ring
      _ ≤ (Real.sqrt 3 * z 1) / (1 + z 0) := div_le_div₀ (by positivity [ha.1])
        (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt hs.le, hr.2.1]) hA HAu
  have HMhi : y 0 ≤ 60 / a := by
    have H := (shearTail_projectiveCoordinate_le ha.1 HAl ⟨hs.le, hr.2.2.1⟩).2
    convert! H using 1
    field_simp [ha.1.ne']
    ring
  have HM : 1 < y 0 := by
    have H : (2 : ℝ) < 1 / (12 * a) := (lt_div_iff₀ (by positivity [ha.1])).mpr
      (by linarith only [ha.2])
    linarith only [H, HMlo]
  have HKlo : y 0 - 1 ≤ k := phaseNorm_ge (by linarith only [HM])
  have Hscale : 1 / (24 * a) ≤ k := by
    have H : (1 : ℝ) ≤ 1 / (24 * a) := (le_div_iff₀ (by positivity [ha.1])).mpr
      (by linarith only [ha.2])
    have he : 1 / (12 * a) = 2 * (1 / (24 * a)) := by ring
    rw [he] at HMlo
    linarith only [HMlo, HKlo, H]
  have HK8 : 8 ≤ k := (show (8 : ℝ) ≤ 1 / (24 * a) from
    (le_div_iff₀ (by positivity [ha.1])).mpr (by linarith only [ha.2])).trans Hscale
  have HV0 : 0 ≤ y 2 := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hn.2.1) hA.le
  have HKhi : k ≤ y 0 := by
    have H := phaseNorm_le_abs_add (y 0 - 1) (y 2)
    rw [abs_of_pos (sub_pos.mpr HM), abs_of_nonneg HV0] at H
    change k ≤ _ at H
    linarith only [H, hv]
  exact ⟨HM, HK8, Hscale, HKhi.trans (HMhi.trans
    (div_le_div_of_nonneg_right (by norm_num) ha.1.le))⟩

end BianchiIX

import BianchiIX.Algebra.RestartTransport
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FinCases

noncomputable section

namespace BianchiIX

abbrev RestartCenterState := Fin 3 → ℝ

def restartCenterTransfer (n : ℝ) : RestartCenterState →L[ℝ] RestartCenterState :=
  let p : Fin 3 → (RestartCenterState →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
  ContinuousLinearMap.pi ![
    restartShearFactor n • p 0 + restartShearCoupling n • (p 1 - p 2),
    restartWallFactor n • p 1, restartWallFactor n • p 2]

theorem restartCenterTransfer_apply (n : ℝ) (v : RestartCenterState) :
    restartCenterTransfer n v = ![
      restartShearFactor n * v 0 + restartShearCoupling n * (v 1 - v 2),
      restartWallFactor n * v 1, restartWallFactor n * v 2] := by
  ext i
  fin_cases i <;> rfl

theorem restart_coefficients_small {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) :
    0 ≤ restartShearFactor n - 1 ∧ restartShearFactor n - 1 ≤ n ∧
      0 ≤ restartWallFactor n - 1 ∧ restartWallFactor n - 1 ≤ n ∧
      0 ≤ restartShearCoupling n ∧ restartShearCoupling n ≤ n := by
  let z := restartReferenceRoot n
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hz2 : z ^ 2 = 1 - n ^ 2 := restartReferenceRoot_sq (by nlinarith only [hn.1, hn.2])
  have hz1 : z ≤ 1 := by nlinarith only [hz0, hz2, sq_nonneg n]
  have hzhalf : 1 / 2 ≤ z := by nlinarith only [hz0, hz2, hn.1, hn.2]
  have hzsmall : 1 - z ≤ n := by
    nlinarith only [hz2, hn.1, hn.2, mul_nonneg hz0 (sub_nonneg.mpr hz1)]
  have hd : 0 < 2 + z := by positivity
  have hd2 : 0 < 2 * (2 + z) ^ 2 := by positivity
  have ha : restartShearFactor n - 1 = (1 - z) / (2 + z) := by
    dsimp only [restartShearFactor]
    change 3 / (2 + z) - 1 = _
    field_simp
    ring
  have hc : restartWallFactor n - 1 = (1 - z) * (2 * z + 1) / (2 * (2 + z) ^ 2) := by
    dsimp only [restartWallFactor]
    change 9 * (1 + z) / (2 * (2 + z) ^ 2) - 1 = _
    field_simp
    ring
  have ha0 : 0 ≤ restartShearFactor n - 1 := by rw [ha]; positivity
  have ha1 : restartShearFactor n - 1 ≤ n := by
    rw [ha]
    apply le_trans _ hzsmall
    apply (div_le_iff₀ hd).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hz1) (show 0 ≤ 1 + z by positivity)]
  have hc0 : 0 ≤ restartWallFactor n - 1 := by rw [hc]; positivity
  have hc1 : restartWallFactor n - 1 ≤ n := by
    rw [hc]
    apply le_trans _ hzsmall
    apply (div_le_iff₀ hd2).mpr
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hz0, sq_nonneg z]) (sub_nonneg.mpr hz1)
  have hk0 : 0 ≤ restartShearCoupling n := by
    dsimp only [restartShearCoupling]
    exact div_nonneg (mul_nonneg (by positivity) hn.1) (sq_nonneg _)
  have hk1 : restartShearCoupling n ≤ n := by
    dsimp only [restartShearCoupling]
    change 3 * Real.sqrt 3 * n / (2 + z) ^ 2 ≤ n
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    have H : 3 * Real.sqrt 3 ≤ (2 + z) ^ 2 := by
      nlinarith only [hsqrt, hzhalf, sq_nonneg (z - 1 / 2)]
    nlinarith only [mul_le_mul_of_nonneg_right H hn.1]
  exact ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩

/-- The transported coordinates differ from the identity by at most three times the strong wall. -/
theorem restartCenterTransfer_sub_id_bound {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) :
    ‖restartCenterTransfer n - ContinuousLinearMap.id ℝ RestartCenterState‖ ≤ 3 * n := by
  obtain ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩ := restart_coefficients_small hn
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [hn.1])
  intro v
  have hv (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hdiff : |v 1 - v 2| ≤ 2 * ‖v‖ := by
    have H := abs_sub_le (v 1) 0 (v 2)
    simp only [sub_zero, zero_sub, abs_neg] at H
    linarith only [H, hv 1, hv 2]
  have hw (i : Fin 3) : |(restartWallFactor n - 1) * v i| ≤ n * ‖v‖ := by
    rw [abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul hc1 (hv i) (abs_nonneg _) hn.1
  apply (pi_norm_le_iff_of_nonneg (by positivity [hn.1] : 0 ≤ 3 * n * ‖v‖)).mpr
  intro i
  rw [sub_apply, ContinuousLinearMap.id_apply, restartCenterTransfer_apply]
  fin_cases i
  · change |restartShearFactor n * v 0 + restartShearCoupling n * (v 1 - v 2) - v 0| ≤ _
    rw [show restartShearFactor n * v 0 + restartShearCoupling n * (v 1 - v 2) - v 0 =
      (restartShearFactor n - 1) * v 0 + restartShearCoupling n * (v 1 - v 2) by ring]
    calc
      _ ≤ |(restartShearFactor n - 1) * v 0| + |restartShearCoupling n * (v 1 - v 2)| := abs_add_le _ _
      _ ≤ n * ‖v‖ + n * (2 * ‖v‖) := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hk0]
        exact add_le_add (mul_le_mul ha1 (hv 0) (abs_nonneg _) hn.1)
          (mul_le_mul hk1 hdiff (abs_nonneg _) hn.1)
      _ = _ := by ring
  · change |restartWallFactor n * v 1 - v 1| ≤ _
    rw [← sub_one_mul]
    exact (hw 1).trans (by nlinarith only [mul_nonneg hn.1 (norm_nonneg v)])
  · change |restartWallFactor n * v 2 - v 2| ≤ _
    rw [← sub_one_mul]
    exact (hw 2).trans (by nlinarith only [mul_nonneg hn.1 (norm_nonneg v)])

theorem restartCenterTransfer_norm_bound {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) :
    ‖restartCenterTransfer n‖ ≤ 1 + 3 * n := by
  have H := norm_le_norm_sub_add (restartCenterTransfer n) (ContinuousLinearMap.id ℝ RestartCenterState)
  linarith only [H, restartCenterTransfer_sub_id_bound hn,
    ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := RestartCenterState)]

/-- Conservation turns a small coefficient defect into a uniform tail bound, without time integration. -/
theorem restartCenterTransfer_conserved_bounds {h n : ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (hn : 0 ≤ n ∧ n ≤ 1 / 16)
    (Y : RestartCenterState →L[ℝ] RestartCenterState)
    (hY : (restartCenterTransfer n).comp Y = restartCenterTransfer h) :
    ‖Y‖ ≤ 2 ∧ ‖Y - restartCenterTransfer h‖ ≤ 6 * n := by
  have hid : Y - restartCenterTransfer h =
      (ContinuousLinearMap.id ℝ RestartCenterState - restartCenterTransfer n).comp Y := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp, hY]
  have htail : ‖Y - restartCenterTransfer h‖ ≤ 3 * n * ‖Y‖ := by
    rw [hid]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_right (restartCenterTransfer_sub_id_bound hn) (norm_nonneg Y)
  have hnorm : ‖Y‖ ≤ 2 := by
    have H := norm_le_norm_sub_add Y (restartCenterTransfer h)
    have HB := restartCenterTransfer_norm_bound hh
    have Hn := mul_le_mul_of_nonneg_right hn.2 (norm_nonneg Y)
    nlinarith only [H, HB, htail, hh.2, Hn]
  exact ⟨hnorm, htail.trans (by nlinarith only [mul_le_mul_of_nonneg_left hnorm hn.1])⟩

end BianchiIX

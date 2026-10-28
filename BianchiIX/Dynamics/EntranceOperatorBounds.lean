import BianchiIX.Dynamics.EntranceProjectionEstimates
import BianchiIX.Dynamics.EntranceRadialPullback

noncomputable section

namespace BianchiIX

local instance entranceOperatorGroup : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance entranceOperatorSpace : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance

theorem norm_stableRestriction_apply_le (v : ProjectiveState) : ‖stableRestriction v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  fin_cases i <;> exact norm_le_pi_norm v _

/-- Coarse full operator bounds suffice for the ordinary coefficient derivatives. -/
theorem exists_entranceProjection_operator_bounds :
    ∃ C ≥ (1 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      ‖fderiv ℝ entranceStablePhase y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ entranceStablePhase) y‖ ≤ C := by
  obtain ⟨C, hC, HC⟩ := exists_entranceProjection_estimates
  refine ⟨320002 + 2 * C, by linarith, ?_⟩
  intro k y hk hy
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hU := hy.2.2.1.1
  have hW := hy.2.2.2.2.1
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hU]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hW]; linarith [hy.2.2.2.2.2]
  have hb : 0 ≤ y 1 + y 3 := add_nonneg hU hW
  have hb1 : y 1 + y 3 ≤ 1 / 5000 := by linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hk1 : 1 ≤ k := by linarith
  have hsmall : C * (y 1 + y 3) / k ≤ C :=
    (div_le_self (by positivity) hk1).trans (by nlinarith only [hC, hb1])
  have hPM := (entranceRegion_stable_radial_bounds hk hy).2.2
  have hPMabs : |entranceStablePartial y 0| ≤ 2 := (abs_le.mpr ⟨by linarith [hPM.1], by linarith [hPM.2]⟩)
  have hPU := (HC k y hk hy).2.2.1.trans hsmall
  have hPW := (HC k y hk hy).2.2.2.1.trans hsmall
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hv (i : Fin 4) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
    rw [Real.norm_eq_abs, entranceStablePhase_fderiv_coordinates hm hu hw]
    calc
      _ ≤ |entranceStablePartial y 0 * v 0| + |entranceStablePartial y 1 * v 1| + |entranceStablePartial y 3 * v 3| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 2 * ‖v‖ + C * ‖v‖ + C * ‖v‖ := by
        simp only [abs_mul]
        exact add_le_add (add_le_add (mul_le_mul hPMabs (hv 0) (abs_nonneg _) (by norm_num))
          (mul_le_mul hPU (hv 1) (abs_nonneg _) hC.le)) (mul_le_mul hPW (hv 3) (abs_nonneg _) hC.le)
      _ ≤ _ := by nlinarith only [norm_nonneg v]
  · have he : Real.exp (512 * (y 1 + y 3)) ≤ 2 :=
      (Real.exp_bound_div_one_sub_of_interval (by positivity) (by linarith)).trans
        ((div_le_iff₀ (by linarith : 0 < 1 - 512 * (y 1 + y 3))).mpr (by linarith))
    have hQ := stableBoundaryProjection_fderiv2_bound (y := stableRestriction y) hm (by simp [stableRestriction]) hu hw
    have hQ' : ‖fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))) (stableRestriction y)‖ ≤ 320000 := by
      have he3 := pow_le_pow_left₀ (Real.exp_pos _).le he 3
      simp only [stableRestriction_apply, Matrix.cons_val_one, Matrix.cons_val,
        abs_of_nonneg hU, abs_of_nonneg hW] at hQ
      rw [stableRestriction_apply]
      nlinarith only [hQ, he3]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    rw [Real.norm_eq_abs, entranceStablePhase_hessian hm hu hw]
    have H0 := (((fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)))
      (stableRestriction y)) (stableRestriction v)).le_opNorm (stableRestriction w)).trans
        (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)))
          (stableRestriction y)).le_opNorm (stableRestriction v)) (norm_nonneg _))
    have H1 := mul_le_mul (mul_le_mul (hQ'.trans (by linarith)) (norm_stableRestriction_apply_le v)
      (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 320002 + 2 * C)) (norm_stableRestriction_apply_le w)
        (norm_nonneg _) (by positivity : 0 ≤ (320002 + 2 * C) * ‖v‖)
    exact H0.trans H1

theorem entranceClockRate_fderiv_bound {y : ProjectiveState} {k : ℝ}
    (hy : entranceRegion k y) (v : ProjectiveState) :
    |fderiv ℝ entranceClockRate y v| ≤ 7 * ‖v‖ := by
  have hu0 := hy.2.2.1.1
  have hu1 : y 1 ≤ 1 := by linarith [hy.2.2.1.2]
  have hcoef : |y 2 + y 3 - 2 * y 1| ≤ 4 := abs_le.mpr ⟨by linarith [hy.2.2.2.1.1, hy.2.2.2.2.1],
    by linarith [hy.2.2.2.1.2, hy.2.2.2.2.2]⟩
  have hv (i : Fin 4) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  rw [entranceClockRate_fderiv]
  calc
    _ ≤ |v 0| + |(y 2 + y 3 - 2 * y 1) * v 1| + |y 1 * v 2| + |y 1 * v 3| :=
      (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ ‖v‖ + 4 * ‖v‖ + 1 * ‖v‖ + 1 * ‖v‖ := by
      simp only [abs_mul, abs_of_nonneg hu0]
      exact add_le_add (add_le_add (add_le_add (hv 0) (mul_le_mul hcoef (hv 1) (abs_nonneg _) (by norm_num)))
        (mul_le_mul hu1 (hv 2) (abs_nonneg _) (by norm_num))) (mul_le_mul hu1 (hv 3) (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem exists_entranceRadialInverse_operator_bound :
    ∃ C ≥ (1 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        ‖fderiv ℝ Ψ (entranceRadialCoordinates y)‖ ≤ C := by
  obtain ⟨C, hC, HC⟩ := exists_entranceRadialInverse_column_bounds
  refine ⟨13 + 2 * C, by linarith, ?_⟩
  intro k y hk hy hv Ψ H
  have hk1 : 1 ≤ k := by linarith
  have hb : 0 ≤ y 1 + y 3 := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hb1 : y 1 + y 3 ≤ 1 := by linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hsmall : C * (y 1 + y 3) / k ≤ C :=
    (div_le_self (by positivity) hk1).trans (by nlinarith only [hC, hb1])
  obtain ⟨h0, h1, h2, h3⟩ := HC k y hk hy hv Ψ H
  obtain ⟨d0, d1, d2, d3⟩ := H.phase_partials
  rw [d0] at h0
  rw [d1, abs_div, abs_neg, ← abs_div] at h1
  rw [d2, abs_div, abs_neg, ← abs_div] at h2
  rw [d3, abs_div, abs_neg, ← abs_div] at h3
  have h0' : |entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0)| ≤ 8 :=
    (abs_le.mpr ⟨by linarith only [h0.1], h0.2⟩)
  have h2' : |y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0)| ≤ 4 :=
    h2.trans ((div_le_self (by positivity) hk1).trans (by linarith [hy.2.2.2.1.2]))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv' (i : Fin 4) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  rw [H.differential_apply]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · simp only [Real.norm_eq_abs]
    calc
      _ ≤ |entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * v 0| +
          |entranceStablePartial y 1 / entranceStablePartial y 0 * v 1| +
          |y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * v 2| +
          |entranceStablePartial y 3 / entranceStablePartial y 0 * v 3| :=
        (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
      _ ≤ 8 * ‖v‖ + C * ‖v‖ + 4 * ‖v‖ + C * ‖v‖ := by
        simp only [abs_mul]
        exact add_le_add (add_le_add (add_le_add (mul_le_mul h0' (hv' 0) (abs_nonneg _) (by norm_num))
          (mul_le_mul (h1.trans hsmall) (hv' 1) (abs_nonneg _) hC.le))
          (mul_le_mul h2' (hv' 2) (abs_nonneg _) (by norm_num))) (mul_le_mul (h3.trans hsmall) (hv' 3) (abs_nonneg _) hC.le)
      _ ≤ _ := by nlinarith only [norm_nonneg v]
  all_goals
    simp only [Real.norm_eq_abs]
    exact (hv' _).trans (by nlinarith only [norm_nonneg v, mul_nonneg hC.le (norm_nonneg v)])

end BianchiIX

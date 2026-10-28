import BianchiIX.Dynamics.EntranceWallLogPullback

noncomputable section

namespace BianchiIX

theorem entranceWallLogRates_base_bounds {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    |1 + coupling (y 1) (y 2) (y 3)| ≤ 2 ∧
      |entranceStrongLogRate y| ≤ 12 * k ∧ |entranceWeakLogRate y| ≤ 9 := by
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 ≤ y 0 := by linarith [hy.1]
  have hm : y 0 ≤ 3 * k := by linarith [(entranceRegion_phase hk hy).2]
  have hu0 := hy.2.2.1.1
  have hu1 : y 1 ≤ 1 := by linarith [hy.2.2.1.2]
  have hw1 : y 3 ≤ 1 := by linarith [hy.2.2.2.2.2]
  have huv : |y 2 - y 3| ≤ 1 := abs_le.mpr ⟨by linarith [hy.2.2.2.1.1],
    by linarith [hy.2.2.2.1.2, hy.2.2.2.2.1]⟩
  have hu2 : y 1 ^ 2 ≤ 1 := by nlinarith [pow_le_pow_left₀ hu0 hu1 2]
  have hC := connection_coupling_bounds hu0 hy.2.2.2.1 ⟨hy.2.2.2.2.1, hw1⟩
  have hc : |1 + coupling (y 1) (y 2) (y 3)| ≤ 2 :=
    abs_le.mpr ⟨by linarith [hC.1], by linarith [hC.2, hy.2.2.1.2]⟩
  have hD := entranceRegion_clock_pos hk hy
  have hDlo : k / 2 ≤ entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]
  refine ⟨hc, ?_, ?_⟩
  · have hm2 : y 0 ^ 2 ≤ 9 * k ^ 2 := by nlinarith [pow_le_pow_left₀ hm0 hm 2]
    have hdiff2 : (y 2 - y 3) ^ 2 ≤ 1 := by nlinarith [sq_abs (y 2 - y 3), pow_le_pow_left₀ (abs_nonneg _) huv 2]
    have hr : |connectionStrongRate (y 0) (y 1) (y 2) (y 3)| ≤ 6 * k ^ 2 := by
      unfold connectionStrongRate
      apply abs_le.mpr
      constructor <;> nlinarith only [hm2, hdiff2, hu2, sq_nonneg (y 0), sq_nonneg (y 2 - y 3), sq_nonneg (y 1), hk1, hk0]
    change |connectionStrongRate (y 0) (y 1) (y 2) (y 3) / entranceClockRate y| ≤ _
    rw [abs_div, abs_of_pos hD]
    exact (div_le_iff₀ hD).mpr (hr.trans (by nlinarith only [hDlo, hk0]))
  · change |-1 - 2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y| ≤ _
    have hq : |2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y| ≤ 8 := by
      rw [abs_div, abs_mul, abs_of_pos hD, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply (div_le_iff₀ hD).mpr
      nlinarith only [hc, hDlo, hk1]
    exact (abs_sub _ _).trans (by norm_num only [abs_neg, abs_one]; linarith only [hq])

theorem entranceStrongLogRate_fderiv_bound {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (v : ProjectiveState) :
    |fderiv ℝ entranceStrongLogRate y v| ≤ 180 * ‖v‖ := by
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm : |y 0| ≤ 3 * k := by
    rw [abs_of_nonneg (by linarith [hy.1] : 0 ≤ y 0)]
    linarith [(entranceRegion_phase hk hy).2]
  have hu : |y 1| ≤ 1 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hdiff : |y 2 - y 3| ≤ 1 := abs_le.mpr ⟨by linarith [hy.2.2.2.1.1, hy.2.2.2.2.2],
    by linarith [hy.2.2.2.1.2, hy.2.2.2.2.1]⟩
  have hv (i : Fin 4) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hdv : |v 2 - v 3| ≤ 2 * ‖v‖ := (abs_sub _ _).trans (by linarith only [hv 2, hv 3])
  have hrate := (entranceWallLogRates_base_bounds hk hy).2.1
  have hclock := entranceClockRate_fderiv_bound hy v
  have hD := entranceRegion_clock_pos hk hy
  have hDlo : k / 2 ≤ entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]
  have he : v 0 - (v 1 * (y 2 + y 3 - 2 * y 1) + y 1 * (v 2 + v 3)) =
      fderiv ℝ entranceClockRate y v := by rw [entranceClockRate_fderiv]; ring
  rw [(entranceWallLogRates_fderiv hD.ne' v).1, he, abs_div, abs_of_pos hD]
  apply (div_le_iff₀ hD).mpr
  calc
    _ ≤ |-y 0 * v 0| + |(y 2 - y 3) * (v 2 - v 3)| + |y 1 * v 1| +
        |entranceStrongLogRate y * fderiv ℝ entranceClockRate y v| :=
      (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ 3 * k * ‖v‖ + 1 * (2 * ‖v‖) + 1 * ‖v‖ + (12 * k) * (7 * ‖v‖) := by
      simp only [abs_mul, abs_neg]
      exact add_le_add (add_le_add (add_le_add (mul_le_mul hm (hv 0) (abs_nonneg _) (by positivity))
        (mul_le_mul hdiff hdv (abs_nonneg _) (by norm_num)))
        (mul_le_mul hu (hv 1) (abs_nonneg _) (by norm_num)))
        (mul_le_mul hrate hclock (abs_nonneg _) (by positivity))
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hDlo (norm_nonneg v),
      mul_le_mul_of_nonneg_right hk1 (norm_nonneg v)]

theorem exists_entranceStrongLogRate_radial_bound :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        ∀ v : ProjectiveState,
          |fderiv ℝ (fun z => entranceStrongLogRate (Ψ z)) (entranceRadialCoordinates y) v| ≤ C * ‖v‖ := by
  obtain ⟨J, hJ, HJ⟩ := exists_entranceRadialInverse_operator_bound
  refine ⟨180 * J, by positivity, ?_⟩
  intro k y hk hy hv Ψ H v
  have hf := (contDiffAt_entranceWallLogRates 1 (entranceRegion_clock_pos hk hy).ne').1.differentiableAt (by norm_num)
  have hnorm := ((fderiv ℝ Ψ (entranceRadialCoordinates y)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (HJ k y hk hy hv Ψ H) (norm_nonneg v))
  rw [H.scalar_differential hf, ← H.hasFDerivAt.fderiv]
  exact (entranceStrongLogRate_fderiv_bound hk hy _).trans
    (by nlinarith only [hnorm])

end BianchiIX

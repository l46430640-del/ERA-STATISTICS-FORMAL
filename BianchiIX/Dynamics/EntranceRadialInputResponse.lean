import BianchiIX.Dynamics.EntranceRadiusCorrectionBounds
import BianchiIX.Dynamics.EntrancePhysicalDirections

noncomputable section

namespace BianchiIX

/-- The corrected radius and the physical radius have the same leading radial response. -/
theorem exists_entrance_radius_input_direction_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      let b := y 1 + y 3
      let R := fun p : ProjectiveState => coreRadius (p 0) (p 2)
      |entranceStableRadius y - R y| ≤ C * b ^ 2 / k ∧
      ∀ (D : ℝ) (d : ProjectiveState), 0 ≤ D → |d 0| ≤ D * k ^ 2 →
        (∀ i : Fin 4, i ≠ 0 → |d i| ≤ D * k * y i) →
        |fderiv ℝ entranceStableRadius y d - fderiv ℝ R y d| ≤ C * D * b ^ 2 ∧
        |fderiv ℝ entranceStableRadius y d| ≤ (C + 2) * D * k ^ 2 := by
  obtain ⟨A, hA, HA⟩ := exists_entranceProjection_estimates
  refine ⟨10 * A, by positivity, ?_⟩
  intro k y hk hy hv b R
  let r := entranceStableRadius y
  let χ := entranceStablePhase y - 1
  let q := y 0 - 1
  have hk0 : 0 < k := by linarith only [hk]
  have hk1 : 1 ≤ k := by linarith only [hk]
  have hb0 : 0 ≤ b := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hb1 : b ≤ 1 := by dsimp only [b]; linarith only [hy.2.2.1.2, hy.2.2.2.2.2]
  have hq0 : 0 < q := by dsimp only [q]; linarith only [(entranceRegion_phase hk hy).1, hk0]
  have hm : 2 ≤ y 0 := by linarith only [(entranceRegion_phase hk hy).1, hk]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith only [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith only [hy.2.2.2.2.2]
  obtain ⟨hχ, hr, _⟩ := entranceRegion_stable_radial_bounds hk hy
  have hχ0 : 0 < χ := by dsimp only [χ]; linarith only [hχ.1, hk]
  have hr0 : 0 < r := entranceStableRadius_pos hv
  have hR0 : 0 < R y := coreRadius_pos hv
  have hRlo : k / 2 ≤ R y := by
    have H := (abs_le.mp hy.2.1).1
    change -(k / 100) ≤ R y - k at H
    linarith only [H, hk]
  have hri : 1 / r ≤ 2 / k := by
    apply (div_le_div_iff₀ hr0 hk0).mpr
    linarith only [hr.1]
  have hRi : 1 / R y ≤ 2 / k := by
    apply (div_le_div_iff₀ hR0 hk0).mpr
    linarith only [hRlo]
  obtain ⟨Hval, Hm, Hu, Hw, _⟩ := HA k y hk hy
  have Hphase : |χ - q| ≤ A * b ^ 2 / k := by
    convert Hval using 1
    congr 1
    dsimp only [χ, q]
    ring
  have Hrad : |r - R y| ≤ A * b ^ 2 / k := (phaseNorm_sub_le hχ0 hq0).trans Hphase
  have hχr : |χ / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hχ0, abs_of_pos hr0]
    exact (div_le_one hr0).mpr (phaseNorm_ge hχ0.le)
  have hqR : |q / R y| ≤ 1 := by
    rw [abs_div, abs_of_pos hq0, abs_of_pos hR0]
    exact (div_le_one hR0).mpr (phaseNorm_ge hq0.le)
  have Hcoeff : |χ / r - q / R y| ≤ 4 * A * b ^ 2 / k ^ 2 := by
    have heq : χ / r - q / R y = (χ - q) / r - (q / R y) * ((r - R y) / r) := by
      field_simp [hr0.ne', hR0.ne']
      ring
    rw [heq]
    calc
      _ ≤ |(χ - q) / r| + |(q / R y) * ((r - R y) / r)| := abs_sub _ _
      _ = |χ - q| * (1 / r) + |q / R y| * (|r - R y| * (1 / r)) := by
        simp only [abs_mul, abs_div, abs_of_pos hr0]
        ring
      _ ≤ (A * b ^ 2 / k) * (2 / k) + 1 * ((A * b ^ 2 / k) * (2 / k)) := by gcongr
      _ = _ := by field_simp [hk0.ne']; ring
  have Hinv : |1 / r - 1 / R y| ≤ 4 * A * b ^ 2 / k ^ 3 := by
    have heq : 1 / r - 1 / R y = -(r - R y) * (1 / r) * (1 / R y) := by
      field_simp [hr0.ne', hR0.ne']
      ring
    rw [heq, abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / r),
      abs_of_pos (by positivity : 0 < 1 / R y)]
    calc
      _ ≤ (A * b ^ 2 / k) * (2 / k) * (2 / k) := by gcongr
      _ = _ := by field_simp [hk0.ne']; ring
  refine ⟨Hrad.trans ?_, ?_⟩
  · gcongr
    linarith only [hA]
  · intro D d hD hd0 hdwall
    have Hδ : |fderiv ℝ entranceStablePhase y d - d 0| ≤ 2 * A * D * b ^ 2 := by
      rw [entranceStablePhase_fderiv_coordinates hm hu hw]
      have heq : entranceStablePartial y 0 * d 0 + entranceStablePartial y 1 * d 1 +
          entranceStablePartial y 3 * d 3 - d 0 =
          (entranceStablePartial y 0 - 1) * d 0 + entranceStablePartial y 1 * d 1 +
            entranceStablePartial y 3 * d 3 := by ring
      rw [heq]
      calc
        _ ≤ |(entranceStablePartial y 0 - 1) * d 0| + |entranceStablePartial y 1 * d 1| +
            |entranceStablePartial y 3 * d 3| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ (A * b ^ 2 / k ^ 2) * (D * k ^ 2) +
            (A * b / k) * (D * k * y 1) + (A * b / k) * (D * k * y 3) := by
          simp only [abs_mul]
          exact add_le_add (add_le_add (mul_le_mul Hm hd0 (abs_nonneg _) (by positivity))
            (mul_le_mul Hu (hdwall 1 (by decide)) (abs_nonneg _) (by positivity)))
            (mul_le_mul Hw (hdwall 3 (by decide)) (abs_nonneg _) (by positivity))
        _ = _ := by
          dsimp only [b]
          field_simp [hk0.ne']
          ring
    have Hcore : fderiv ℝ R y d = (q * d 0 + y 2 * d 2) / R y := by
      rw [(hasFDerivAt_coreRadius_state hv).fderiv]
      simp only [smul_apply, add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
      ring
    have Hdiff : fderiv ℝ entranceStableRadius y d - fderiv ℝ R y d =
        (χ / r) * (fderiv ℝ entranceStablePhase y d - d 0) +
        (χ / r - q / R y) * d 0 + y 2 * (1 / r - 1 / R y) * d 2 := by
      rw [entranceStableRadius_fderiv hm hu hw hv, Hcore]
      dsimp only [χ, q, r]
      ring
    have hvk : (y 2) ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hv.le (hy.2.2.2.1.2.trans hk1) 2
    have hlast : 4 * A * D * b ^ 2 * (y 2) ^ 2 / k ^ 2 ≤ 4 * A * D * b ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hk0)).mpr
      exact mul_le_mul_of_nonneg_left hvk (by positivity)
    have Hdiffbound : |fderiv ℝ entranceStableRadius y d - fderiv ℝ R y d| ≤ 10 * A * D * b ^ 2 := by
      rw [Hdiff]
      calc
        _ ≤ |(χ / r) * (fderiv ℝ entranceStablePhase y d - d 0)| +
            |(χ / r - q / R y) * d 0| + |y 2 * (1 / r - 1 / R y) * d 2| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ 1 * (2 * A * D * b ^ 2) + (4 * A * b ^ 2 / k ^ 2) * (D * k ^ 2) +
            (y 2 * (4 * A * b ^ 2 / k ^ 3)) * (D * k * y 2) := by
          simp only [abs_mul, abs_of_pos hv]
          exact add_le_add (add_le_add (mul_le_mul hχr Hδ (abs_nonneg _) (by norm_num))
            (mul_le_mul Hcoeff hd0 (abs_nonneg _) (by positivity)))
            (mul_le_mul (mul_le_mul_of_nonneg_left Hinv hv.le) (hdwall 2 (by decide))
              (abs_nonneg _) (by positivity))
        _ = 6 * A * D * b ^ 2 + 4 * A * D * b ^ 2 * (y 2) ^ 2 / k ^ 2 := by
          field_simp [hk0.ne']
          ring
        _ ≤ _ := by linarith only [hlast]
    refine ⟨Hdiffbound, ?_⟩
    have Hcorebound : |fderiv ℝ R y d| ≤ 2 * D * k ^ 2 := by
      rw [Hcore]
      have heq : (q * d 0 + y 2 * d 2) / R y = (q / R y) * d 0 + (y 2 / R y) * d 2 := by ring
      have hvR : |y 2 / R y| ≤ 1 := by
        rw [abs_div, abs_of_pos hv, abs_of_pos hR0]
        exact (div_le_one hR0).mpr (by simpa only [abs_of_pos hv] using (coreRadius_component_bounds (y 0) (y 2)).2)
      rw [heq]
      calc
        _ ≤ |q / R y| * |d 0| + |y 2 / R y| * |d 2| := by
          simpa only [abs_mul] using abs_add_le ((q / R y) * d 0) ((y 2 / R y) * d 2)
        _ ≤ 1 * (D * k ^ 2) + 1 * (D * k * y 2) := by
          exact add_le_add (mul_le_mul hqR hd0 (abs_nonneg _) (by norm_num))
            (mul_le_mul hvR (hdwall 2 (by decide)) (abs_nonneg _) (by norm_num))
        _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left (hy.2.2.2.1.2.trans hk1) (by positivity : 0 ≤ D * k)]
    have hbksq : b ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hb0 (hb1.trans hk1) 2
    have Htriangle := abs_sub_le (fderiv ℝ entranceStableRadius y d) (fderiv ℝ R y d) 0
    simp only [sub_zero] at Htriangle
    nlinarith only [Htriangle, Hdiffbound, Hcorebound,
      mul_le_mul_of_nonneg_left hbksq (by positivity : 0 ≤ 10 * A * D)]

end BianchiIX

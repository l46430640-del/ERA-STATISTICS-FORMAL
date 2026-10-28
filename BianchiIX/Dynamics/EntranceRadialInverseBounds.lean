import BianchiIX.Dynamics.EntranceRadialInverse
import BianchiIX.Dynamics.StableProjectionRefinedDerivatives

noncomputable section

namespace BianchiIX

theorem exists_entranceStable_wall_partial_bounds :
    ∃ C > (0 : ℝ), ∀ y : ProjectiveState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 3| < 1 / 200 →
      |entranceStablePartial y 1| ≤ C / (y 0 + 1) * (|y 1| + |y 3|) ∧
        |entranceStablePartial y 3| ≤ C / (y 0 + 1) * (|y 1| + |y 3|) := by
  obtain ⟨C, hC, HC⟩ := exists_stableBoundaryProjection_refined_derivatives
  refine ⟨C, hC, ?_⟩
  intro y hm hu hw
  have H := (HC (stableRestriction y) hm hu hw).2.1
  have hU : stableRestriction (Pi.single (1 : Fin 4) (1 : ℝ)) = Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [stableRestriction]
  have hW : stableRestriction (Pi.single (3 : Fin 4) (1 : ℝ)) = Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp [stableRestriction]
  constructor
  · rw [entranceStablePartial, entranceStablePhase_fderiv hm hu hw, hU]
    simpa [stableRestriction_apply, Pi.norm_single] using H (Pi.single 1 1) (by simp)
  · rw [entranceStablePartial, entranceStablePhase_fderiv hm hu hw, hW]
    simpa [stableRestriction_apply, Pi.norm_single] using H (Pi.single 2 1) (by simp)

/-- The inverse columns have the uniform scales used before equation (C.20). -/
theorem exists_entranceRadialInverse_column_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let z := entranceRadialCoordinates y
        (2 / 3 ≤ fderiv ℝ Ψ z (Pi.single 0 1) 0 ∧ fderiv ℝ Ψ z (Pi.single 0 1) 0 ≤ 8) ∧
          |fderiv ℝ Ψ z (Pi.single 1 1) 0| ≤ C * (y 1 + y 3) / k ∧
          |fderiv ℝ Ψ z (Pi.single 2 1) 0| ≤ 4 * y 2 / k ∧
          |fderiv ℝ Ψ z (Pi.single 3 1) 0| ≤ C * (y 1 + y 3) / k := by
  obtain ⟨C, hC, HC⟩ := exists_entranceStable_wall_partial_bounds
  refine ⟨4 * C, by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, hR, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have hchi0 : 0 < entranceStablePhase y - 1 := by linarith [hchi.1]
  have hPM0 : 0 < entranceStablePartial y 0 := by linarith [hPM.1]
  have hden : 0 < (entranceStablePhase y - 1) * entranceStablePartial y 0 := mul_pos hchi0 hPM0
  have hdenlo : k / 4 ≤ (entranceStablePhase y - 1) * entranceStablePartial y 0 := by
    have hprod := mul_le_mul hchi.1 hPM.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) hchi0.le
    nlinarith only [hprod]
  have hk0 : 0 < k := by linarith
  have hLk : k / 2 ≤ y 0 + 1 := by linarith [(entranceRegion_phase hk hy).1]
  have hb : 0 ≤ y 1 + y 3 := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hwall (a : ℝ) (ha : |a| ≤ C / (y 0 + 1) * (y 1 + y 3)) :
      |(-a) / entranceStablePartial y 0| ≤ 4 * C * (y 1 + y 3) / k := by
    rw [abs_div, abs_neg, abs_of_pos hPM0]
    calc
      _ ≤ |a| / (1 / 2) := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hPM.1
      _ = 2 * |a| := by ring
      _ ≤ 2 * (C / (y 0 + 1) * (y 1 + y 3)) := mul_le_mul_of_nonneg_left ha (by norm_num)
      _ ≤ 2 * (C / (k / 2) * (y 1 + y 3)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hC.le (by positivity) hLk) hb) (by norm_num)
      _ = _ := by ring
  have hpartials := HC y hm hu hw
  rw [abs_of_nonneg hy.2.2.1.1, abs_of_nonneg hy.2.2.2.2.1] at hpartials
  obtain ⟨h0, h1, h2, h3⟩ := H.phase_partials
  dsimp only
  rw [h0, h1, h2, h3]
  refine ⟨⟨?_, ?_⟩, hwall _ hpartials.1, ?_, hwall _ hpartials.2⟩
  · apply (le_div_iff₀ hden).mpr
    have hRchi : entranceStablePhase y - 1 ≤ entranceStableRadius y := phaseNorm_ge hchi0.le
    have hprod := mul_le_mul_of_nonneg_left hPM.2 hchi0.le
    nlinarith only [hRchi, hprod]
  · apply (div_le_iff₀ hden).mpr
    linarith [hR.2]
  · rw [abs_div, abs_neg, abs_of_pos hv, abs_of_pos hden]
    calc
      _ ≤ y 2 / (k / 4) := div_le_div_of_nonneg_left hv.le (by positivity) hdenlo
      _ = _ := by ring

end BianchiIX

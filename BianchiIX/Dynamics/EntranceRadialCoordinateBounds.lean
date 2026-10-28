import BianchiIX.Dynamics.EntranceStablePhase
import BianchiIX.Dynamics.EntranceRegion
import BianchiIX.Algebra.MatchingPhase

noncomputable section

namespace BianchiIX

theorem entranceStablePhase_small_wall_bounds {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 10000) (hw : |y 3| ≤ 1 / 10000) :
    |entranceStablePhase y - y 0| ≤ 1 / 100 ∧
      |entranceStablePartial y 0 - 1| ≤ 1 / 2 := by
  have hu' : |y 1| < 1 / 200 := by linarith
  have hw' : |y 3| < 1 / 200 := by linarith
  let b := |y 1| + |y 3|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 / 5000 := by dsimp [b]; linarith
  have hb2 : b ^ 2 ≤ (1 / 5000 : ℝ) ^ 2 := pow_le_pow_left₀ hb hb1 2
  have hval : |entranceStablePhase y - y 0| ≤ 8 * b ^ 2 / (y 0 + 1) :=
    (stableBoundaryProjection_exists hm (by simp) hu'.le hw'.le).2.2.2.2
  have hvec : stableRestriction (Pi.single (0 : Fin 4) (1 : ℝ)) = Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [stableRestriction]
  have hd := stableBoundaryProjection_fderiv_drift (y := stableRestriction y) hm
    (by simp [stableRestriction]) hu' hw' (Pi.single 0 1)
  have hd' : |entranceStablePartial y 0 - 1| ≤ 66000 * b ^ 2 * Real.exp (512 * b) := by
    rw [entranceStablePartial, entranceStablePhase_fderiv hm hu' hw', hvec]
    have hz : (![0, 0] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> rfl
    simp [stableVariationCenterBudget, stableRestriction_apply, Pi.norm_single, hz] at hd
    rw [stableRestriction_apply]
    convert! hd using 1
    ring
  have he : Real.exp (512 * b) ≤ 2 :=
    (Real.exp_bound_div_one_sub_of_interval (by positivity) (by linarith)).trans
      ((div_le_iff₀ (by linarith : 0 < 1 - 512 * b)).mpr (by linarith))
  constructor
  · apply hval.trans
    apply (div_le_iff₀ (by linarith : 0 < y 0 + 1)).mpr
    nlinarith only [hb2, hm]
  · have H := mul_le_mul hb2 he (Real.exp_pos _).le (by positivity : (0 : ℝ) ≤ (1 / 5000) ^ 2)
    nlinarith only [hd', H]

theorem entranceRegion_stable_radial_bounds {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    (k / 2 ≤ entranceStablePhase y - 1 ∧ entranceStablePhase y - 1 ≤ 3 * k / 2) ∧
      (k / 2 ≤ entranceStableRadius y ∧ entranceStableRadius y ≤ 2 * k) ∧
      (1 / 2 ≤ entranceStablePartial y 0 ∧ entranceStablePartial y 0 ≤ 3 / 2) := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| ≤ 1 / 10000 := by rw [abs_of_nonneg hy.2.2.1.1]; exact hy.2.2.1.2
  have hw : |y 3| ≤ 1 / 10000 := by rw [abs_of_nonneg hy.2.2.2.2.1]; exact hy.2.2.2.2.2
  obtain ⟨hP, hdP⟩ := entranceStablePhase_small_wall_bounds hm hu hw
  obtain ⟨hPl, hPu⟩ := abs_le.mp hP
  obtain ⟨hdl, hdu⟩ := abs_le.mp hdP
  have hchi : k / 2 ≤ entranceStablePhase y - 1 ∧ entranceStablePhase y - 1 ≤ 3 * k / 2 := by
    obtain ⟨hl, hu⟩ := entranceRegion_phase hk hy
    constructor <;> linarith
  have hpos : 0 ≤ entranceStablePhase y - 1 := by linarith [hchi.1]
  have hRlo : k / 2 ≤ entranceStableRadius y := hchi.1.trans (phaseNorm_ge hpos)
  have hsq := pow_le_pow_left₀ hpos hchi.2 2
  have hv2 : y 2 ^ 2 ≤ 1 := by nlinarith [hy.2.2.2.1.1, hy.2.2.2.1.2]
  have hRhi : entranceStableRadius y ≤ 2 * k := by
    nlinarith only [entranceStableRadius_sq y, hsq, hv2, hRlo, hk, sq_nonneg (k - 1)]
  exact ⟨hchi, ⟨hRlo, hRhi⟩, ⟨by linarith, by linarith⟩⟩

/-- The stable radial coordinate has a uniformly nonzero ordinary M derivative. -/
theorem entranceRegion_stable_radial_derivative {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    1 / 8 ≤ fderiv ℝ entranceStableRadius y (Pi.single 0 1) ∧
      fderiv ℝ entranceStableRadius y (Pi.single 0 1) ≤ 3 / 2 := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, hR, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have hpos := entranceStableRadius_pos hv
  have heq : fderiv ℝ entranceStableRadius y (Pi.single 0 1) =
      (entranceStablePhase y - 1) * entranceStablePartial y 0 / entranceStableRadius y := by
    rw [entranceStableRadius_fderiv hm hu hw hv]
    simp [entranceStablePartial]
  rw [heq]
  have hchi0 : 0 ≤ entranceStablePhase y - 1 := by linarith [hchi.1]
  constructor
  · apply (le_div_iff₀ hpos).mpr
    have H := mul_le_mul hchi.1 hPM.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) hchi0
    nlinarith only [H, hR.2]
  · apply (div_le_iff₀ hpos).mpr
    have H := mul_le_mul_of_nonneg_left hPM.2 hchi0
    have H' : entranceStablePhase y - 1 ≤ entranceStableRadius y := phaseNorm_ge hchi0
    linarith

end BianchiIX

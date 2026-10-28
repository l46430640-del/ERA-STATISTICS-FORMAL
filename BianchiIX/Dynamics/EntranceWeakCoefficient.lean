import BianchiIX.Dynamics.EntranceRadialCoefficients
import BianchiIX.Dynamics.StableCorrectedRemainder

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem entranceStablePhase_weak {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : y 1 = 0) (hw : |y 3| ≤ 1 / 200) :
    entranceStablePhase y = stableWeakRadius (y 0) (y 3) - 1 := by
  unfold entranceStablePhase
  rw [hu]
  exact stableBoundaryProjection_weak hm (by simp) hw

theorem entranceStablePartial_weak_phase {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : y 1 = 0) (hw : |y 3| < 1 / 200) :
    entranceStablePartial y 0 = (y 0 + 1) / stableWeakRadius (y 0) (y 3) := by
  let c : ℝ → ProjectiveState := fun m => ![m, 0, y 2, y 3]
  have hc : c (y 0) = y := by ext i; fin_cases i <;> simp [c, hu]
  have hdc : HasDerivAt c (Pi.single 0 1) (y 0) := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! hasDerivAt_id (y 0) using 1
    · simpa [c] using hasDerivAt_const (y 0) (0 : ℝ)
    · simpa [c] using hasDerivAt_const (y 0) (y 2)
    · simpa [c] using hasDerivAt_const (y 0) (y 3)
  have hp : HasFDerivAt entranceStablePhase (fderiv ℝ entranceStablePhase y) (c (y 0)) := by
    rw [hc]
    exact ((contDiffAt_entranceStablePhase_two hm (by rw [hu]; norm_num) hw).differentiableAt (by norm_num)).hasFDerivAt
  have H := hp.comp_hasDerivAt (y 0) hdc
  have hsmall : ∀ᶠ m : ℝ in 𝓝 (y 0), |m - y 0| < 1 / 40 := by
    exact ((continuousAt_id.sub_const (y 0)).abs).eventually (gt_mem_nhds (by simp : |y 0 - y 0| < (1 : ℝ) / 40))
  have heq : (fun m => entranceStablePhase (c m)) =ᶠ[𝓝 (y 0)]
      (fun m => stableWeakRadius m (y 3) - 1) := by
    filter_upwards [hsmall] with m hm'
    exact stableBoundaryProjection_weak hm hm'.le hw.le
  have hS := (hasDerivAt_stableWeakRadius (hasDerivAt_id (y 0))
    (hasDerivAt_const (y 0) (y 3)) (by dsimp; linarith)).sub_const 1
  have he := (H.congr_of_eventuallyEq heq.symm).unique hS
  simpa only [entranceStablePartial, id_eq, mul_one, mul_zero, add_zero] using he

/-- The weak-wall numerator retains the two extra large-parameter powers. -/
theorem entranceWeakNumerator_weak {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : y 1 = 0) (hw : |y 3| < 1 / 200) :
    entranceWeakNumerator y = -2 * y 3 ^ 2 /
      (stableWeakRadius (y 0) (y 3) * (stableWeakRadius (y 0) (y 3) + (y 0 + 1))) := by
  rw [entranceWeakNumerator, entranceStablePhase_weak hm hu hw.le, entranceStablePartial_weak_phase hm hu hw, hu, zero_mul, sub_zero]
  have hL : 0 < y 0 + 1 := by linarith
  have H := phaseNorm_ratio_defect (b := y 3) hL
  change 1 - (y 0 + 1) / stableWeakRadius (y 0) (y 3) =
    y 3 ^ 2 * (1 / (stableWeakRadius (y 0) (y 3) * (stableWeakRadius (y 0) (y 3) + (y 0 + 1)))) at H
  have hS := (stableWeakRadius_pos (w := y 3) (by linarith : -1 < y 0)).ne'
  calc
    _ = -2 * (1 - (y 0 + 1) / stableWeakRadius (y 0) (y 3)) := by field_simp; ring
    _ = _ := by rw [H]; ring

theorem entranceWeakNumerator_weak_bound {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : y 1 = 0) (hw : |y 3| < 1 / 200) :
    |entranceWeakNumerator y| ≤ y 3 ^ 2 / (y 0 + 1) ^ 2 := by
  have hL : 0 < y 0 + 1 := by linarith
  have hS : 0 < stableWeakRadius (y 0) (y 3) := stableWeakRadius_pos (by linarith)
  have hLS : y 0 + 1 ≤ stableWeakRadius (y 0) (y 3) := phaseNorm_ge hL.le
  rw [entranceWeakNumerator_weak hm hu hw, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y 3)),
    abs_of_pos (mul_pos hS (add_pos hS hL))]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply (div_le_div_iff₀ (mul_pos hS (add_pos hS hL)) (sq_pos_of_pos hL)).mpr
  have H : 2 * (y 0 + 1) ^ 2 ≤ stableWeakRadius (y 0) (y 3) *
      (stableWeakRadius (y 0) (y 3) + (y 0 + 1)) := by nlinarith
  nlinarith only [mul_le_mul_of_nonneg_left H (sq_nonneg (y 3))]

theorem entranceRadialWeakCoefficient_zero_strong_bound {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hu : y 1 = 0) :
    |entranceRadialWeakCoefficient y| ≤ 16 * y 3 ^ 2 / k ^ 4 := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hk0 : 0 < k := by linarith
  have hL : 0 < y 0 + 1 := by linarith
  have hLk : k / 2 ≤ y 0 + 1 := by linarith [(entranceRegion_phase hk hy).1]
  have hSk : k / 2 ≤ entranceStablePhase y - 1 := by
    rw [entranceStablePhase_weak hm hu hw.le]
    have H : y 0 + 1 ≤ stableWeakRadius (y 0) (y 3) := phaseNorm_ge hL.le
    linarith [(entranceRegion_phase hk hy).1]
  have hRk : k / 2 ≤ entranceStableRadius y := hSk.trans
    (phaseNorm_ge (by linarith : 0 ≤ entranceStablePhase y - 1))
  have hDk : k / 2 ≤ entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]
  have hR : 0 < entranceStableRadius y := lt_of_lt_of_le (by positivity) hRk
  have hD := entranceRegion_clock_pos hk hy
  have hden : (k / 2) ^ 2 ≤ entranceStableRadius y * entranceClockRate y := by
    simpa only [pow_two] using mul_le_mul hRk hDk (by positivity : 0 ≤ k / 2) hR.le
  have hsq : (k / 2) ^ 2 ≤ (y 0 + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hLk 2
  have hN : |entranceWeakNumerator y| ≤ y 3 ^ 2 / (k / 2) ^ 2 :=
    (entranceWeakNumerator_weak_bound hm hu hw).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hsq)
  rw [entranceRadialWeakCoefficient, abs_div, abs_of_pos (mul_pos hR hD)]
  calc
    _ ≤ (y 3 ^ 2 / (k / 2) ^ 2) / (entranceStableRadius y * entranceClockRate y) :=
      div_le_div_of_nonneg_right hN (mul_pos hR hD).le
    _ ≤ (y 3 ^ 2 / (k / 2) ^ 2) / (k / 2) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by field_simp; ring

end BianchiIX

import BianchiIX.Dynamics.EntrancePhysicalBounds
import BianchiIX.Analysis.EntranceFixedProductEstimate

noncomputable section

namespace BianchiIX

theorem entranceWeakLogRate_defect_bound {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) : |entranceWeakLogRate y + 1| ≤ 8 / k := by
  have hk0 : 0 < k := by linarith
  have hD := entranceRegion_clock_pos hk hy
  have hDlo : k / 2 ≤ entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]
  have hc := (entranceWallLogRates_base_bounds hk hy).1
  change |-1 - 2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y + 1| ≤ _
  rw [show -1 - 2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y + 1 =
    -(2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y) by ring,
    abs_neg, abs_div, abs_mul, abs_of_pos hD, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 4 / entranceClockRate y := div_le_div_of_nonneg_right (by linarith only [hc]) hD.le
    _ ≤ 4 / (k / 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hDlo
    _ = _ := by ring

/-- Equation (C.41) already holds on the fixed amplitude entrance domain. -/
theorem exists_entrance_fixed_product_bound :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      ContDiffAt ℝ 2 F z ∧
      y 2 * fderiv ℝ F z (Pi.single 2 1) - y 3 * fderiv ℝ F z (Pi.single 3 1) =
        -entranceRadialDrift y * fderiv ℝ F z (Pi.single 0 1) -
          (y 1 * entranceStrongLogRate y) * fderiv ℝ F z (Pi.single 1 1) -
          y 3 * (entranceWeakLogRate y + 1) * fderiv ℝ F z (Pi.single 3 1) ∧
      |y 2 * fderiv ℝ F z (Pi.single 2 1) - y 3 * fderiv ℝ F z (Pi.single 3 1)| ≤
        C * (y 1 * y 2 + (y 2 * y 3) ^ 2 / k ^ 2) := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_physical_bounds
  obtain ⟨B, hB, HB⟩ := exists_entranceRadialDrift_weighted_bound
  refine ⟨B * (1 + 3 * A) + 28 * A, by positivity, ε, hε, hεsmall, ?_⟩
  intro y k hk hm hu hv hw
  obtain ⟨Ψ, HΨ, hF, _, Hr, Hu, _, Hw⟩ := HA y 1 hk hm hu hv hw (Or.inl rfl)
  refine ⟨Ψ, HΨ, ?_⟩
  intro z F
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
  have hu1 : y 1 ≤ 1 := by linarith [hu'.2]
  have hw1 : y 3 ≤ 1 := by linarith [hw'.2]
  have hy : entranceRegion k y := ⟨hm, by rw [sub_self, abs_zero]; positivity,
    hu', ⟨hv.1.le, hv.2.le⟩, hw'⟩
  let L := -Real.log (y 2)
  let ω := Real.exp (-2 * L / k)
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hwait := (entrance_terminal_clock_weights hk1 hL).2.2.2.2
  have hω : ω ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hL]) hk0.le)
  have hP : y 1 * y 2 ≤ 1 := mul_le_one₀ hu1 hv.1.le hv.2.le
  have hS : (y 2) ^ 2 * (y 3) ^ 2 ≤ 1 := by
    exact mul_le_one₀ (pow_le_one₀ hv.1.le hv.2.le) (sq_nonneg _) (pow_le_one₀ hw.1.le hw1)
  have hnum : y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (1 + (1 + L / k) * ω) ≤ 3 := by
    have H := mul_le_mul_of_nonneg_left hwait (show 0 ≤ (y 2) ^ 2 * (y 3) ^ 2 by positivity)
    nlinarith only [hP, hS, H]
  have hinc : |fderiv ℝ F z (Pi.single 0 1) - 1| ≤ 3 * A := by
    apply Hr.trans
    calc
      _ ≤ A * 3 / k ^ 2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hA.le) (sq_nonneg k)
      _ ≤ A * 3 := div_le_self (by positivity) (one_le_pow₀ hk1)
      _ = _ := by ring
  have hFr : |fderiv ℝ F z (Pi.single 0 1)| ≤ 1 + 3 * A := by
    have H := abs_add_le (fderiv ℝ F z (Pi.single 0 1) - 1) (1 : ℝ)
    simp only [sub_add_cancel, abs_one] at H
    linarith only [H, hinc]
  have hFw : |fderiv ℝ F z (Pi.single 3 1)| ≤ A * (y 1 * y 2 + 2 * (y 2) ^ 2 * y 3) / k := by
    apply Hw.trans
    apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA.le) hk0.le
    have H := mul_le_mul_of_nonneg_left hω (show 0 ≤ (y 2) ^ 2 * y 3 by positivity [hw.1])
    nlinarith only [H]
  have hpV : 0 < entranceReturnState y 2 := by
    rw [(entranceReturn_active_component hk hm hu' hv hw').1]
    norm_num
  have HT := HΨ.return_observable_transport hk hm hu' hv hw'
    (hasFDerivAt_coreRadius_state hpV).differentiableAt
  refine ⟨hF, ?_, ?_⟩
  · nlinarith only [HT]
  · exact entrance_fixed_product_estimate hA.le hB.le hk1 hu.1.le hv.1.le ⟨hw.1.le, hw1⟩
      (by simpa only [one_mul] using HB k 1 y hk hy hv.1 (Or.inl rfl))
      (entranceWallLogRates_base_bounds hk hy).2.1 (entranceWeakLogRate_defect_bound hk hy)
      hFr Hu hFw HT

end BianchiIX

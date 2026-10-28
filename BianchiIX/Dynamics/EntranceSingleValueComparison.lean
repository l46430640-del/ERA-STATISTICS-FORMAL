import BianchiIX.Dynamics.EntrancePhysicalValue
import BianchiIX.Dynamics.EntranceSingleReciprocalError

noncomputable section

namespace BianchiIX

/-- The actual arrival differs from the single-wall phase by wall products, not a linear stable-wall term. -/
theorem exists_entrance_single_value_comparison :
    ∃ C ≥ (1 : ℝ), ∀ y : ProjectiveState,
      7 / 4 ≤ coreRadius (y 0) (y 2) → 2 ≤ y 0 →
      (0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) → (0 < y 2 ∧ y 2 < 1) →
      (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) →
      |2 / coreRadius (entranceReturnState y 0) (entranceReturnState y 2) -
          singleStrongPhase (y 0) (y 1)| ≤ C * (y 1 * (y 2 + y 3) + (y 2 + y 3) ^ 2) := by
  obtain ⟨A, hA, HA⟩ := exists_entrance_physical_basic_value
  obtain ⟨B, hB, HB⟩ := exists_entranceSingleReciprocalError_direction_bounds
  refine ⟨32 * A + B + 1, by linarith only [hA, hB], ?_⟩
  intro y hk hm hu hv hw
  have hu0 := hu.1
  have hv0 := hv.1.le
  have hw0 := hw.1
  have hu' : |y 1| ≤ 1 / 10000 := by simpa only [abs_of_nonneg hu.1] using hu.2
  have hw' : |y 3| ≤ 1 / 10000 := by simpa only [abs_of_nonneg hw.1] using hw.2
  have hscale : 1 / (1 : ℝ) ≤ y 0 + 1 := by linarith only [hm]
  have Hr := (entranceSinglePhaseError_radius_lower (by norm_num : (0 : ℝ) < 1)
    hscale hm hu' hw').1
  have Hp : 1 ≤ coreRadius (entranceReturnState y 0) (entranceReturnState y 2) := calc
    1 = |entranceReturnState y 2| := by
      rw [(entranceReturn_active_component hk (by linarith only [hm]) hu hv hw).1, abs_one]
    _ ≤ _ := (coreRadius_component_bounds _ _).2
  have Hrec := reciprocal_difference_value_bound (by norm_num : (0 : ℝ) < 4)
    (show 1 / (4 : ℝ) ≤ coreRadius (entranceReturnState y 0) (entranceReturnState y 2) from by linarith only [Hp])
    (show 1 / (4 : ℝ) ≤ entranceStableRadius y from by simpa using Hr)
  let E := y 1 * (y 2 + y 3) + (y 2 + y 3) ^ 2
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hs : (y 1 + y 3) ^ 2 ≤ 1 := by
    nlinarith only [hu.1, hu.2, hw.1, hw.2]
  have Hnum : y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2 ≤ E := by
    have Hsq := mul_le_mul_of_nonneg_left hs (sq_nonneg (y 2))
    dsimp only [E]
    nlinarith only [Hsq, mul_nonneg hu.1 hw.1, mul_nonneg hv.1.le hw.1, sq_nonneg (y 3)]
  have Hphys : |coreRadius (entranceReturnState y 0) (entranceReturnState y 2) - entranceStableRadius y| ≤ A * E := by
    apply (HA y hk (by linarith only [hm]) hu hv hw).trans
    apply (div_le_self (by positivity) (by linarith only [hk] : 1 ≤ coreRadius (y 0) (y 2))).trans
    exact mul_le_mul_of_nonneg_left Hnum hA.le
  have Hsingle := (HB 1 0 y 0 (by norm_num) le_rfl hscale hm hu' hw'
    (by simp) (by intro i hi; simp)).2.1
  have HEq := (entranceSingleReciprocalError_eventuallyEq_single hm
    (by linarith only [hu'])).eq_of_nhds
  rw [HEq, abs_of_nonneg hu.1, abs_of_nonneg hw.1] at Hsingle
  have Hsingle' : |2 / entranceStableRadius y - singleStrongPhase (y 0) (y 1)| ≤ B * E := by
    apply Hsingle.trans
    simp only [one_pow, mul_one]
    apply mul_le_mul_of_nonneg_left _ hB.le
    dsimp only [E]
    nlinarith only [mul_nonneg hu.1 hv.1.le, mul_nonneg hv.1.le hw.1]
  have Htri := abs_sub_le (2 / coreRadius (entranceReturnState y 0) (entranceReturnState y 2))
    (2 / entranceStableRadius y) (singleStrongPhase (y 0) (y 1))
  have Hbound := Hrec.trans (mul_le_mul_of_nonneg_left Hphys (by norm_num : 0 ≤ 2 * (4 : ℝ) ^ 2))
  nlinarith only [Htri, Hbound, Hsingle', hE]

end BianchiIX

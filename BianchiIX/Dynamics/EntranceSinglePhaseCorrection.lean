import BianchiIX.Dynamics.StableStrongProjectionError
import BianchiIX.Dynamics.EntranceRadialCoordinateBounds

noncomputable section

namespace BianchiIX

def entranceSinglePhaseError (y : ProjectiveState) : ℝ :=
  entranceStableRadius y - (stableBoundaryProjection (y 0) (y 1) 0 - 1)

theorem entranceSinglePhaseError_eq {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 200) :
    entranceSinglePhaseError y = entranceStableRadius y -
      (singleStrongUpperRoot (singleStrongInvariant (y 0) (y 1)) - 1) := by
  rw [entranceSinglePhaseError, stableBoundaryProjection_strong hm (by simp) hu]

theorem entranceSinglePhaseError_decomposition {y : ProjectiveState}
    (hP : 1 < entranceStablePhase y) :
    entranceSinglePhaseError y = stableStrongProjectionError (stableRestriction y) +
      (y 2) ^ 2 / (entranceStableRadius y + entranceStablePhase y - 1) := by
  have HR : 0 ≤ entranceStableRadius y := Real.sqrt_nonneg _
  have HD : 0 < entranceStableRadius y + entranceStablePhase y - 1 := by linarith only [HR, hP]
  have HS := entranceStableRadius_sq y
  change entranceStableRadius y - (stableBoundaryProjection (y 0) (y 1) 0 - 1) =
    entranceStablePhase y - stableBoundaryProjection (y 0) (y 1) 0 + _
  have Hroot : entranceStableRadius y - (entranceStablePhase y - 1) =
      (y 2) ^ 2 / (entranceStableRadius y + entranceStablePhase y - 1) := by
    apply (eq_div_iff HD.ne').mpr
    nlinarith only [HS]
  linarith only [Hroot]

theorem entranceStablePhase_large_lower {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 10000) (hw : |y 3| ≤ 1 / 10000) :
    (y 0 + 1) / 4 ≤ entranceStablePhase y - 1 ∧ 1 < entranceStablePhase y := by
  have HP := (entranceStablePhase_small_wall_bounds hm hu hw).1
  have HM := (abs_le.mp HP).1
  constructor <;> linarith only [HM, hm]

/-- The radial correction contains either a weak stable wall or two active walls, with no pure strong-wall error. -/
theorem exists_entranceSinglePhaseError_bounds :
    ∃ C > (0 : ℝ), ∀ y : ProjectiveState,
      2 ≤ y 0 → |y 1| ≤ 1 / 10000 → |y 3| ≤ 1 / 10000 →
      let b := |y 1| + |y 3|
      |entranceSinglePhaseError y| ≤ C * (|y 3| * b + (y 2) ^ 2) / (y 0 + 1) := by
  obtain ⟨C, hC, HC⟩ := exists_stableStrongProjectionError_bounds
  refine ⟨C + 4, by positivity, ?_⟩
  intro y hm hu hw b
  have hu' : |y 1| < 1 / 200 := by linarith only [hu]
  have hw' : |y 3| < 1 / 200 := by linarith only [hw]
  have HP := entranceStablePhase_large_lower hm hu hw
  have hL : 0 < y 0 + 1 := by linarith only [hm]
  have HR : 0 ≤ entranceStableRadius y := Real.sqrt_nonneg _
  have HD : (y 0 + 1) / 4 ≤ entranceStableRadius y + entranceStablePhase y - 1 := by
    linarith only [HP.1, HR]
  have HDpos : 0 < entranceStableRadius y + entranceStablePhase y - 1 := lt_of_lt_of_le (by positivity) HD
  have HE := (HC (stableRestriction y) hm hu' hw').1
  change |stableStrongProjectionError (stableRestriction y)| ≤ C * |y 3| * b / (y 0 + 1) at HE
  rw [entranceSinglePhaseError_decomposition HP.2]
  calc
    _ ≤ |stableStrongProjectionError (stableRestriction y)| +
        |(y 2) ^ 2 / (entranceStableRadius y + entranceStablePhase y - 1)| := abs_add_le _ _
    _ = |stableStrongProjectionError (stableRestriction y)| +
        (y 2) ^ 2 / (entranceStableRadius y + entranceStablePhase y - 1) := by
      rw [abs_of_nonneg (div_nonneg (sq_nonneg _) HDpos.le)]
    _ ≤ C * |y 3| * b / (y 0 + 1) + (y 2) ^ 2 / ((y 0 + 1) / 4) :=
      add_le_add HE (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) HD)
    _ = (C * |y 3| * b + 4 * (y 2) ^ 2) / (y 0 + 1) := by field_simp
    _ ≤ (C + 4) * (|y 3| * b + (y 2) ^ 2) / (y 0 + 1) := by
      apply (div_le_div_iff_of_pos_right hL).mpr
      have hb : 0 ≤ b := by dsimp only [b]; positivity
      nlinarith only [mul_nonneg hC.le (sq_nonneg (y 2)), mul_nonneg (abs_nonneg (y 3)) hb]

theorem exists_entranceSinglePhaseError_scaled_bounds :
    ∃ C > (0 : ℝ), ∀ (α : ℝ) (y : ProjectiveState), 0 < α → 1 / α ≤ y 0 + 1 →
      2 ≤ y 0 → |y 1| ≤ 1 / 10000 → |y 3| ≤ 1 / 10000 →
      |entranceSinglePhaseError y| ≤ C * α * (|y 3| * (|y 1| + |y 3|) + (y 2) ^ 2) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceSinglePhaseError_bounds
  refine ⟨C, hC, ?_⟩
  intro α y hα hscale hm hu hw
  have HL : 0 < y 0 + 1 := by linarith only [hm]
  have Hinv : 1 / (y 0 + 1) ≤ α := (div_le_iff₀ HL).mpr
    (by have H := (div_le_iff₀ hα).mp hscale; nlinarith only [H])
  refine (HC y hm hu hw).trans ?_
  calc
    _ = (C * (|y 3| * (|y 1| + |y 3|) + (y 2) ^ 2)) * (1 / (y 0 + 1)) := by ring
    _ ≤ (C * (|y 3| * (|y 1| + |y 3|) + (y 2) ^ 2)) * α :=
      mul_le_mul_of_nonneg_left Hinv (by positivity)
    _ = _ := by ring

end BianchiIX

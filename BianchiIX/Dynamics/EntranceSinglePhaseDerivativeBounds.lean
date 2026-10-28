import BianchiIX.Dynamics.EntranceSinglePhaseDifferential
import BianchiIX.Dynamics.ExitActualDirections

noncomputable section

namespace BianchiIX

/-- A radial-size direction preserves the weak-wall and active-wall-square factors of the correction. -/
theorem exists_entranceSinglePhaseError_direction_bound :
    ∃ C > (0 : ℝ), ∀ (α D : ℝ) (y d : ProjectiveState), 0 < α → 0 ≤ D →
      1 / α ≤ y 0 + 1 → 2 ≤ y 0 → |y 1| ≤ 1 / 10000 → |y 3| ≤ 1 / 10000 →
      ‖d‖ ≤ D / α ^ 2 → (∀ i : Fin 4, i ≠ 0 → |d i| ≤ D * |y i| / α) →
      |fderiv ℝ entranceSinglePhaseError y d| ≤ C * D * (|y 3| * (|y 1| + |y 3|) + (y 2) ^ 2) := by
  obtain ⟨A, hA, HA⟩ := exists_stableStrongProjectionError_scaled_bounds
  obtain ⟨K, hK, HK⟩ := exists_stableBoundaryProjection_uniform_fderiv
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  refine ⟨3 * A + 4 + 16 * K, by positivity, ?_⟩
  intro α D y d hα hD hscale hm hu hw hd hwall
  have hu' : |y 1| < 1 / 200 := by linarith only [hu]
  have hw' : |y 3| < 1 / 200 := by linarith only [hw]
  let b := |y 1| + |y 3|
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have Hd0 : |d 0| ≤ D / α ^ 2 := (norm_le_pi_norm d 0).trans hd
  have HP : |fderiv ℝ entranceStablePhase y d| ≤ K * D / α ^ 2 := by
    rw [entranceStablePhase_fderiv hm hu' hw']
    have hn : ‖stableRestriction d‖ ≤ ‖d‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg d)).mpr
      intro i; fin_cases i <;> exact norm_le_pi_norm d _
    exact (((fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))
      (stableRestriction y)).le_opNorm (stableRestriction d)).trans
        (mul_le_mul (HK (stableRestriction y) hm hu' hw') (hn.trans hd) (norm_nonneg _) hK0)).trans_eq (by ring)
  obtain ⟨_, Hm, Hu, Hw⟩ := HA α (stableRestriction y) hα hscale hm hu' hw'
  have HE : |fderiv ℝ stableStrongProjectionError (stableRestriction y) (stableRestriction d)| ≤
      3 * A * D * |y 3| * b := by
    have H := clm_three_coordinate_bound (fderiv ℝ stableStrongProjectionError (stableRestriction y)) (stableRestriction d)
    change _ ≤ |d 0| * _ + |d 1| * _ + |d 3| * _ at H
    calc
      _ ≤ _ := H
      _ ≤ (D / α ^ 2) * (A * α ^ 2 * |y 3| * b) +
          (D * |y 1| / α) * (A * α * |y 3|) +
          (D * |y 3| / α) * (A * α * b) := by
        exact add_le_add (add_le_add (mul_le_mul Hd0 Hm (abs_nonneg _) (by positivity))
          (mul_le_mul (hwall 1 (by decide)) Hu (abs_nonneg _) (by positivity)))
          (mul_le_mul (hwall 3 (by decide)) Hw (abs_nonneg _) (by positivity))
      _ = A * D * |y 3| * (2 * b + |y 1|) := by field_simp; ring
      _ ≤ _ := by
        have hpart : |y 1| ≤ b := le_add_of_nonneg_right (abs_nonneg _)
        nlinarith only [mul_le_mul_of_nonneg_left hpart (by positivity : 0 ≤ A * D * |y 3|)]
  obtain ⟨HR, HS⟩ := entranceSinglePhaseError_radius_lower hα hscale hm hu hw
  have hr : 0 < entranceStableRadius y := (by positivity : 0 < 1 / (4 * α)).trans_le HR
  have hs : 0 < entranceStableRadius y + entranceStablePhase y - 1 :=
    (by positivity : 0 < 1 / (4 * α)).trans_le HS
  have Hri : 1 / entranceStableRadius y ≤ 4 * α := (div_le_iff₀ hr).mpr (by
    have H := (div_le_iff₀ (by positivity : 0 < 4 * α)).mp HR; nlinarith only [H])
  have Hsi : 1 / (entranceStableRadius y + entranceStablePhase y - 1) ≤ 4 * α :=
    (div_le_iff₀ hs).mpr (by
      have H := (div_le_iff₀ (by positivity : 0 < 4 * α)).mp HS; nlinarith only [H])
  have Hv : |y 2 * d 2 / entranceStableRadius y| ≤ 4 * D * (y 2) ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos hr]
    calc
      _ = |y 2| * |d 2| * (1 / entranceStableRadius y) := by ring
      _ ≤ |y 2| * (D * |y 2| / α) * (4 * α) := by gcongr; exact hwall 2 (by decide)
      _ = 4 * D * |y 2| ^ 2 := by field_simp
      _ = _ := by rw [sq_abs]
  have Hv2 : |(y 2) ^ 2 * fderiv ℝ entranceStablePhase y d /
      (entranceStableRadius y * (entranceStableRadius y + entranceStablePhase y - 1))| ≤
      16 * K * D * (y 2) ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (mul_pos hr hs)]
    calc
      _ = (y 2) ^ 2 * |fderiv ℝ entranceStablePhase y d| *
          (1 / entranceStableRadius y) * (1 / (entranceStableRadius y + entranceStablePhase y - 1)) := by
            field_simp [hr.ne', hs.ne']
      _ ≤ (y 2) ^ 2 * (K * D / α ^ 2) * (4 * α) * (4 * α) := by gcongr
      _ = _ := by field_simp; ring
  rw [(entranceSinglePhaseError_differential hm hu hw).2]
  have H := (abs_sub (fderiv ℝ stableStrongProjectionError (stableRestriction y) (stableRestriction d) +
    y 2 * d 2 / entranceStableRadius y) ((y 2) ^ 2 * fderiv ℝ entranceStablePhase y d /
      (entranceStableRadius y * (entranceStableRadius y + entranceStablePhase y - 1)))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  nlinarith only [H, HE, Hv, Hv2, mul_nonneg (by positivity : 0 ≤ 3 * A * D) (sq_nonneg (y 2)),
    mul_nonneg (by positivity : 0 ≤ (4 + 16 * K) * D) (mul_nonneg (abs_nonneg (y 3)) hb)]

end BianchiIX

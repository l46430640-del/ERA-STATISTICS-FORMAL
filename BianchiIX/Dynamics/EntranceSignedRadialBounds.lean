import BianchiIX.Dynamics.StableProjectionLipschitz
import BianchiIX.Dynamics.EntranceRadialCoordinates
import BianchiIX.Analysis.CoordinateDerivativeNorm

noncomputable section

namespace BianchiIX

theorem entranceStablePhase_signed_lower {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 400) (hw : |y 3| ≤ 1 / 400) :
    |entranceStablePhase y - y 0| ≤ 1 / 100 ∧ 1 < entranceStablePhase y := by
  have hu' : |y 1| ≤ 1 / 200 := by linarith only [hu]
  have hw' : |y 3| ≤ 1 / 200 := by linarith only [hw]
  have H := (stableBoundaryProjection_exists hm (by simp : |y 0 - y 0| ≤ (1 : ℝ) / 40) hu' hw').2.2.2.2
  change |entranceStablePhase y - y 0| ≤ _ at H
  have hb : |y 1| + |y 3| ≤ 1 / 200 := by linarith only [hu, hw]
  have hb2 := pow_le_pow_left₀ (add_nonneg (abs_nonneg (y 1)) (abs_nonneg (y 3))) hb 2
  have HD : |entranceStablePhase y - y 0| ≤ 1 / 100 := H.trans
    ((div_le_iff₀ (by linarith only [hm] : 0 < y 0 + 1)).mpr (by nlinarith only [hb2, hm]))
  exact ⟨HD, by linarith only [(abs_le.mp HD).1, hm]⟩

theorem entranceStableRadius_signed_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 400) (hw : |y 3| ≤ 1 / 400) :
    ContDiffAt ℝ 2 entranceStableRadius y ∧
      ∀ v : ProjectiveState, fderiv ℝ entranceStableRadius y v =
        ((entranceStablePhase y - 1) * fderiv ℝ entranceStablePhase y v + y 2 * v 2) /
          entranceStableRadius y := by
  have hχ : 0 < entranceStablePhase y - 1 := sub_pos.mpr (entranceStablePhase_signed_lower hm hu hw).2
  have hu' : |y 1| < 1 / 200 := by linarith only [hu]
  have hw' : |y 3| < 1 / 200 := by linarith only [hw]
  have hP := contDiffAt_entranceStablePhase_two hm hu' hw'
  have hV : ContDiffAt ℝ 2 (fun z : ProjectiveState => z 2) y := by fun_prop
  have hnonzero : (entranceStablePhase y - 1) ^ 2 + (y 2) ^ 2 ≠ 0 := by positivity
  refine ⟨(((hP.sub contDiffAt_const).pow 2).add (hV.pow 2)).sqrt hnonzero, ?_⟩
  intro v
  have H := ((((hP.differentiableAt (by norm_num)).hasFDerivAt.sub_const 1).pow 2).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y).pow 2)).sqrt hnonzero
  change HasFDerivAt entranceStableRadius _ y at H
  rw [H.fderiv]
  simp only [Pi.add_apply, smul_apply, add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  change _ = _ / Real.sqrt ((entranceStablePhase y - 1) ^ 2 + y 2 ^ 2)
  ring

/-- The corrected entrance coordinates have a bounded derivative even on both zero-wall faces. -/
theorem exists_entranceRadialCoordinates_signed_bound :
    ∃ K ≥ (1 : ℝ), ∀ y : ProjectiveState,
      2 ≤ y 0 → |y 1| ≤ 1 / 400 → |y 3| ≤ 1 / 400 →
      ContDiffAt ℝ 2 entranceRadialCoordinates y ∧ ‖fderiv ℝ entranceRadialCoordinates y‖ ≤ K := by
  obtain ⟨A, hA, HA⟩ := exists_stableBoundaryProjection_uniform_fderiv
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  refine ⟨A + 1, by linarith only [hA], ?_⟩
  intro y hm hu hw
  have hu' : |y 1| < 1 / 200 := by linarith only [hu]
  have hw' : |y 3| < 1 / 200 := by linarith only [hw]
  have HR := entranceStableRadius_signed_fderiv hm hu hw
  have Hreg : ContDiffAt ℝ 2 entranceRadialCoordinates y := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact HR.1
    all_goals dsimp [entranceRadialCoordinates]; fun_prop
  have hχ : 0 < entranceStablePhase y - 1 := sub_pos.mpr (entranceStablePhase_signed_lower hm hu hw).2
  have hr : 0 < entranceStableRadius y := by
    unfold entranceStableRadius coreRadius coreEnergy
    positivity
  have hχr : entranceStablePhase y - 1 ≤ entranceStableRadius y := by
    nlinarith only [entranceStableRadius_sq y, sq_nonneg (y 2), hr, hχ]
  have hvr : |y 2| ≤ entranceStableRadius y := by
    nlinarith only [entranceStableRadius_sq y, sq_nonneg (entranceStablePhase y - 1), hr,
      sq_abs (y 2), abs_nonneg (y 2)]
  have HP (v : ProjectiveState) : |fderiv ℝ entranceStablePhase y v| ≤ A * ‖v‖ := by
    rw [entranceStablePhase_fderiv hm hu' hw']
    have hv : ‖stableRestriction v‖ ≤ ‖v‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
      intro i
      fin_cases i <;> exact norm_le_pi_norm v _
    exact ((fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))
      (stableRestriction y)).le_opNorm (stableRestriction v)).trans
        (mul_le_mul (HA (stableRestriction y) hm hu' hw') hv (norm_nonneg _) hA0)
  have Hradius : ‖fderiv ℝ entranceStableRadius y‖ ≤ A + 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [Real.norm_eq_abs, HR.2 v, abs_div, abs_of_pos hr]
    apply (div_le_iff₀ hr).mpr
    have H0 := (abs_add_le ((entranceStablePhase y - 1) * fderiv ℝ entranceStablePhase y v)
      (y 2 * v 2))
    rw [abs_mul, abs_mul, abs_of_pos hχ] at H0
    have H1 := mul_le_mul hχr (HP v) (abs_nonneg _) hr.le
    have H2 := mul_le_mul hvr (show |v 2| ≤ ‖v‖ from norm_le_pi_norm v 2) (abs_nonneg _) hr.le
    nlinarith only [H0, H1, H2]
  refine ⟨Hreg, fderiv_norm_le_of_coordinate_bounds (by positivity)
    (Hreg.differentiableAt (by norm_num)) ?_⟩
  intro i
  fin_cases i
  · exact Hradius
  all_goals
    change ‖fderiv ℝ (fun z : ProjectiveState => z _) y‖ ≤ A + 1
    rw [(hasFDerivAt_apply (𝕜 := ℝ) _ y).fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    exact (norm_le_pi_norm v _).trans (by nlinarith only [hA, norm_nonneg v])

end BianchiIX

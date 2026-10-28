import BianchiIX.Dynamics.EntranceSinglePhaseDerivativeBounds
import BianchiIX.Analysis.ReciprocalDifference

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def entranceSingleRadius (y : ProjectiveState) : ℝ := stableBoundaryProjection (y 0) (y 1) 0 - 1

def entranceSingleReciprocalError (y : ProjectiveState) : ℝ :=
  2 / entranceStableRadius y - 2 / entranceSingleRadius y

theorem entranceSingleReciprocalError_eventuallyEq_single {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) :
    entranceSingleReciprocalError =ᶠ[𝓝 y] (fun z : ProjectiveState =>
      2 / entranceStableRadius z - singleStrongPhase (z 0) (z 1)) := by
  have HE := (stableStrongProjectionError_eventuallyEq_single (y := stableRestriction y) hm hu).comp_tendsto
    stableRestriction.continuous.continuousAt.tendsto
  filter_upwards [HE] with z hz
  have HQ : stableBoundaryProjection (z 0) (z 1) 0 = singleStrongUpperRoot (singleStrongInvariant (z 0) (z 1)) := by
    change stableBoundaryProjection (z 0) (z 1) (z 3) - stableBoundaryProjection (z 0) (z 1) 0 =
      stableBoundaryProjection (z 0) (z 1) (z 3) - singleStrongUpperRoot (singleStrongInvariant (z 0) (z 1)) at hz
    linarith only [hz]
  simp only [entranceSingleReciprocalError, entranceSingleRadius, singleStrongPhase, HQ]

theorem entranceSingleRadius_differential {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) :
    ContDiffAt ℝ 2 entranceSingleRadius y ∧ ∀ d : ProjectiveState,
      fderiv ℝ entranceSingleRadius y d =
        fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))
          (stableStrongBase (stableRestriction y)) (stableStrongBase (stableRestriction d)) := by
  have HP := contDiffAt_stableBoundaryProjection_two (y := stableStrongBase (stableRestriction y))
    hm hu (by change |(0 : ℝ)| < 1 / 200; norm_num)
  let Hmap := stableStrongBase.comp stableRestriction
  have HR := (HP.comp y Hmap.contDiff.contDiffAt).sub (contDiffAt_const (c := (1 : ℝ)))
  have HD := ((HP.differentiableAt (by norm_num)).hasFDerivAt.comp y Hmap.hasFDerivAt).sub_const 1
  change ContDiffAt ℝ 2 entranceSingleRadius y at HR
  change HasFDerivAt entranceSingleRadius _ y at HD
  refine ⟨HR, ?_⟩
  intro d
  rw [HD.fderiv]
  rfl

/-- The reciprocal of the single-wall correction gains two phase powers in the radial column. -/
theorem exists_entranceSingleReciprocalError_direction_bounds :
    ∃ C > (0 : ℝ), ∀ (α D : ℝ) (y d : ProjectiveState), 0 < α → 0 ≤ D →
      1 / α ≤ y 0 + 1 → 2 ≤ y 0 → |y 1| ≤ 1 / 10000 → |y 3| ≤ 1 / 10000 →
      ‖d‖ ≤ D / α ^ 2 → (∀ i : Fin 4, i ≠ 0 → |d i| ≤ D * |y i| / α) →
      ContDiffAt ℝ 2 entranceSingleReciprocalError y ∧
        |entranceSingleReciprocalError y| ≤ C * α ^ 3 * (|y 3| * (|y 1| + |y 3|) + (y 2) ^ 2) ∧
        |fderiv ℝ entranceSingleReciprocalError y d| ≤
          C * D * α ^ 2 * (|y 3| * (|y 1| + |y 3|) + (y 2) ^ 2) := by
  obtain ⟨A, hA, HA⟩ := exists_entranceSinglePhaseError_direction_bound
  obtain ⟨B, hB, HB⟩ := exists_entranceSinglePhaseError_scaled_bounds
  obtain ⟨K, hK, HK⟩ := exists_stableBoundaryProjection_uniform_fderiv
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  refine ⟨32 * A + 256 * K * B + 32 * B, by positivity, ?_⟩
  intro α D y d hα hD hscale hm hu hw hd hwall
  have hu' : |y 1| < 1 / 200 := by linarith only [hu]
  have HR := entranceStableRadius_signed_fderiv hm (by linarith only [hu]) (by linarith only [hw])
  have HQ := entranceSingleRadius_differential hm hu'
  have Hr := (entranceSinglePhaseError_radius_lower hα hscale hm hu hw).1
  have HP := (entranceStablePhase_large_lower (y := ![y 0, y 1, 0, 0]) hm hu
    (by change |(0 : ℝ)| ≤ 1 / 10000; norm_num)).1
  change (y 0 + 1) / 4 ≤ entranceSingleRadius y at HP
  have Hq : 1 / (4 * α) ≤ entranceSingleRadius y := by
    calc
      _ = (1 / α) / 4 := by ring
      _ ≤ (y 0 + 1) / 4 := div_le_div_of_nonneg_right hscale (by norm_num)
      _ ≤ _ := HP
  have hr : 0 < entranceStableRadius y := (by positivity : 0 < 1 / (4 * α)).trans_le Hr
  have hq : 0 < entranceSingleRadius y := (by positivity : 0 < 1 / (4 * α)).trans_le Hq
  have Hdiff := reciprocal_difference_differential HR.1 HQ.1 hr.ne' hq.ne'
  change ContDiffAt ℝ 2 entranceSingleReciprocalError y ∧ _ at Hdiff
  have HqD : |fderiv ℝ entranceSingleRadius y d| ≤ K * D / α ^ 2 := by
    rw [HQ.2]
    have hn : ‖stableStrongBase (stableRestriction d)‖ ≤ ‖d‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg d)).mpr
      intro i; fin_cases i
      · exact norm_le_pi_norm d 0
      · exact norm_le_pi_norm d 1
      · change ‖(0 : ℝ)‖ ≤ ‖d‖
        simpa only [norm_zero] using norm_nonneg d
    exact (((fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))
      (stableStrongBase (stableRestriction y))).le_opNorm (stableStrongBase (stableRestriction d))).trans
        (mul_le_mul (HK _ hm hu' (by change |(0 : ℝ)| < 1 / 200; norm_num))
          (hn.trans hd) (norm_nonneg _) hK0)).trans_eq (by ring)
  let E := |y 3| * (|y 1| + |y 3|) + (y 2) ^ 2
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have Hval : |entranceSinglePhaseError y| ≤ B * α * E := HB α y hα hscale hm hu hw
  have Hder : |fderiv ℝ entranceSinglePhaseError y d| ≤ A * D * E := HA α D y d hα hD hscale hm hu hw hd hwall
  have HV := reciprocal_difference_value_bound (by positivity : 0 < 4 * α) Hr Hq
  change |entranceSingleReciprocalError y| ≤ 2 * (4 * α) ^ 2 * |entranceSinglePhaseError y| at HV
  have HD := reciprocal_difference_derivative_bound (by positivity : 0 < 4 * α) Hr Hq
    (D := 16 * K * D) (p := fderiv ℝ entranceSinglePhaseError y d)
    (Θ := entranceSinglePhaseError y) (HqD.trans_eq (by field_simp; ring))
  have Heq := Hdiff.2.2 d
  change fderiv ℝ entranceSingleReciprocalError y d =
    -2 * fderiv ℝ entranceSinglePhaseError y d / (entranceStableRadius y) ^ 2 +
      2 * entranceSinglePhaseError y * (entranceStableRadius y + entranceSingleRadius y) *
        fderiv ℝ entranceSingleRadius y d / ((entranceSingleRadius y) ^ 2 * (entranceStableRadius y) ^ 2) at Heq
  rw [← Heq] at HD
  refine ⟨Hdiff.1, ?_, ?_⟩
  · have H := mul_le_mul_of_nonneg_left Hval (by positivity : 0 ≤ 2 * (4 * α) ^ 2)
    nlinarith only [HV, H, (by positivity : 0 ≤ (32 * A + 256 * K * B) * α ^ 3 * E)]
  · have H1 := mul_le_mul_of_nonneg_left Hder (by positivity : 0 ≤ 2 * (4 * α) ^ 2)
    have H2 := mul_le_mul_of_nonneg_left Hval (by positivity : 0 ≤ 4 * (16 * K * D) * (4 * α))
    nlinarith only [HD, H1, H2, (by positivity : 0 ≤ 32 * B * D * α ^ 2 * E)]

end BianchiIX

import BianchiIX.Algebra.CoreConeRefinement
import BianchiIX.Dynamics.CoreConeInvariance

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem coreReturnMultiplier_eventuallyEq_of_first {Y : CoreAngleState} {τ σ : CoreAngleState → ℝ}
    (hτ : ∀ᶠ Z in 𝓝 Y, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z))
    (hσ : ∀ᶠ Z in 𝓝 Y, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (σ Z))
    (i : Fin 2) : (fun Z => coreReturnMultiplier τ Z i) =ᶠ[𝓝 Y] (fun Z => coreReturnMultiplier σ Z i) := by
  filter_upwards [hτ, hσ] with Z hτZ hσZ
  unfold coreReturnMultiplier
  rw [hτZ.unique hσZ]

/-- The logarithmic estimates belong to every locally identified first-return branch. -/
theorem coreReturnMultiplier_log_bounds {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0)
    (hnear : ∀ᶠ Z in 𝓝 Y, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z)) :
    (∀ i : Fin 2, ContDiffAt ℝ 1 (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y) ∧
      ∀ v : CoreAngleState,
        let Q := |v 0| + Y 0 * |v 1| + |v 2|
        |fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z 0)) Y v| ≤
          (20 * coreVariationBound + 4) * Real.log (4 * Y 0) * Q ∧
        |fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z 1)) Y v| ≤
          (118 * coreVariationBound + 8) * Real.log (4 * Y 0) * Q / Y 0 ^ 2 := by
  obtain ⟨σ, _, _, hσ, hreg, hbound⟩ := exists_large_core_log_derivative_bounds hk hu hw
  have heq (i : Fin 2) : (fun Z => Real.log (coreReturnMultiplier τ Z i)) =ᶠ[𝓝 Y]
      (fun Z => Real.log (coreReturnMultiplier σ Z i)) :=
    (coreReturnMultiplier_eventuallyEq_of_first hnear (hσ.mono fun _ h => h.1) i).fun_comp Real.log
  refine ⟨fun i => (hreg i).2.1.congr_of_eventuallyEq (heq i), ?_⟩
  intro v Q
  rw [(heq 0).fderiv_eq, (heq 1).fderiv_eq]
  exact hbound v

/-- Formula (B.40) keeps the actual entrance wall sum. -/
theorem coreReturnState_radius_cone_bound {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0)
    (hnear : ∀ᶠ Z in 𝓝 Y, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z))
    (v : CoreAngleState) (hv0 : v 0 = 1) (hv1 : |v 1| ≤ Real.sqrt (Y 1)) (hv2 : |v 2| ≤ Real.sqrt (Y 2)) :
    |(fderiv ℝ (coreReturnState τ) Y v) 0 - 1| ≤
      (5 * (1040 + 512 * coreVariationBound)) * Real.sqrt (Y 1 + Y 2) / Y 0 := by
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hR : 0 ≤ 1040 + 512 * coreVariationBound := by
    have hK := (Real.exp_pos (2 * Real.pi + 48 / 10000)).le
    change 0 ≤ coreVariationBound at hK
    positivity
  have H := (coreReturnState_radius_bound hk hu hw hnear).2 v
  rw [hv0, abs_one] at H
  have hsize := core_cone_radius_size hk
    (by norm_num : (0 : ℝ) ≤ 1 / 10000 ∧ (1 : ℝ) / 10000 ≤ 1) hu hw hv1 hv2
  apply H.trans
  calc
    _ = (1040 + 512 * coreVariationBound) *
        (|v 1| + (Y 1 + Y 2) * (1 + Y 0 * |v 1| + |v 2|)) / Y 0 := by ring
    _ ≤ (1040 + 512 * coreVariationBound) * (5 * Real.sqrt (Y 1 + Y 2)) / Y 0 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [hv1, hsize]) hR) hk0.le
    _ = _ := by ring

end BianchiIX

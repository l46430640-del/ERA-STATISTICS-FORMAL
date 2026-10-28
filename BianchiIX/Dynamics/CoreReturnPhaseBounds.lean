import BianchiIX.Dynamics.CompactCorePhaseBounds
import BianchiIX.Dynamics.CoreReturnCanonical
import BianchiIX.Dynamics.CoreReturnRefinement

noncomputable section

namespace BianchiIX

open Set

/-- The phase drift of the canonical large-core return vanishes with its incoming walls. -/
theorem coreRadiusReturn_large_phase_value {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    |coreReturnState coreRadiusReturnTime Y 0 - Y 0| ≤ 16 * (Y 1 + Y 2) / Y 0 := by
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hfirst := (coreRadiusReturn_large_regular hk hu hw).2.2.2.self_of_nhds
  obtain ⟨T, _, hT, _, _, _, _, herr, _⟩ := exists_large_core_traversal hk hu hw
  have htime : T = coreRadiusReturnTime Y := hT.unique hfirst
  subst T
  change |coreReturnState coreRadiusReturnTime Y 0 - Y 0| ≤
    16 / Y 0 * (Y 1 + Y 2 ^ 2) at herr
  have hw1 : Y 2 ≤ 1 := hw.2.trans ((div_le_one hk0).mpr (by linarith only [hk]))
  have hsq : Y 2 ^ 2 ≤ Y 2 := by nlinarith only [hw.1, hw1]
  calc
    _ ≤ 16 / Y 0 * (Y 1 + Y 2 ^ 2) := herr
    _ ≤ 16 / Y 0 * (Y 1 + Y 2) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hsq) (by positivity)
    _ = _ := by ring

/-- A single first-return map has amplitude-dependent phase and ordinary derivative errors for all radii. -/
theorem exists_coreRadiusReturn_phase_bounds :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      2 ≤ Y 0 → (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
      let F := coreReturnState coreRadiusReturnTime
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 1 F Y ∧
        |F Y 0 - Y 0| ≤ C * (Y 1 + Y 2) / Y 0 ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
          |fderiv ℝ F Y v 0 - 1| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 := by
  obtain ⟨ε, hε, C, hC, H⟩ := exists_compact_core_phase_bounds
  let B := 5 * (1040 + 512 * coreVariationBound)
  let C' := max 16 (max C B)
  have hCC : C ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  have hBC : B ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
  have h16C : 16 ≤ C' := le_max_left _ _
  refine ⟨min ε (1 / 10000), lt_min hε (by norm_num), min_le_right _ _,
    C', lt_of_lt_of_le hC hCC, ?_⟩
  intro Y hk hu hw F
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1 hw.1
  have hη : min ε (1 / 10000) / Y 0 ≤ (1 / 10000) / Y 0 :=
    div_le_div_of_nonneg_right (min_le_right _ _) hk0.le
  by_cases hk6 : 6 ≤ Y 0
  · have hu' := And.intro hu.1 (hu.2.trans hη)
    have hw' := And.intro hw.1 (hw.2.trans hη)
    obtain ⟨hvalid, _, hF, hnear⟩ := coreRadiusReturn_large_regular hk6 hu' hw'
    refine ⟨hvalid, hF, (coreRadiusReturn_large_phase_value hk6 hu' hw').trans ?_, ?_⟩
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h16C hb) hk0.le
    · intro v hv0 hv1 hv2
      exact (coreReturnState_radius_cone_bound hk6 hu' hw' hnear v hv0 hv1 hv2).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBC (Real.sqrt_nonneg _)) hk0.le)
  · have hsmall : min ε (1 / 10000) / Y 0 ≤ ε :=
      (div_le_self (le_of_lt (lt_min hε (by norm_num))) (by linarith only [hk])).trans
        (min_le_left _ _)
    obtain ⟨hvalid, hF, hvalue, hderiv⟩ := H Y ⟨hk, le_of_not_ge hk6⟩
      ⟨hu.1, hu.2.trans hsmall⟩ ⟨hw.1, hw.2.trans hsmall⟩
    refine ⟨hvalid, hF.of_le (by norm_num), hvalue.trans ?_, ?_⟩
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hb) hk0.le
    · intro v hv0 hv1 hv2
      exact (hderiv v hv0 hv1 hv2).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (Real.sqrt_nonneg _)) hk0.le)

end BianchiIX

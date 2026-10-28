import BianchiIX.Dynamics.CoreReturnRefinement

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Formula (B.42), together with the amplitude-sensitive radial bound (B.40). -/
theorem exists_large_core_refined_cone :
    ∃ ε > 0, ∃ C > 0, ε ≤ 1 / 10000 ∧ ∀ Y : CoreAngleState, 6 ≤ Y 0 →
      (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
      ∃ τ : CoreAngleState → ℝ, 0 < τ Y ∧ ContDiffAt ℝ 1 τ Y ∧
        ContDiffAt ℝ 1 (coreReturnState τ) Y ∧
        (∀ᶠ Z in 𝓝 Y,
          IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
          projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
          projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1) ∧
        ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ v : CoreAngleState, v 0 = 1 →
          |v 1| ≤ θ * Real.sqrt (Y 1) → |v 2| ≤ θ * Real.sqrt (Y 2) →
          let d := fderiv ℝ (coreReturnState τ) Y v
          let S := Real.sqrt (Y 1 + Y 2) * Real.log (4 * Y 0) / Y 0 ^ 2
          3 / 4 ≤ d 0 ∧
            |d 0 - 1| ≤ (5 * (1040 + 512 * coreVariationBound)) * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
            |d 1| ≤ C * (θ + S) * Real.sqrt (coreReturnState τ Y 1) * d 0 ∧
            |d 2| ≤ C * (θ + S) * Real.sqrt (coreReturnState τ Y 2) * d 0 ∧
            (0 < Y 1 → 0 < Y 2 →
              max (|d 1| / (Real.sqrt (coreReturnState τ Y 1) * d 0))
                (|d 2| / (Real.sqrt (coreReturnState τ Y 2) * d 0)) ≤ C * (θ + S)) := by
  let A := 20 * coreVariationBound + 4
  let B := 118 * coreVariationBound + 8
  let C := 2 * (1 + 12800 * A + 2 * B)
  have hK : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨ε, hε, hεη, hcone⟩ := exists_large_core_invariant_cone
  refine ⟨ε, hε, C, hC, hεη, ?_⟩
  intro Y hk hu hw
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hu' : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right hεη hk0.le)⟩
  have hw' : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0 :=
    ⟨hw.1, hw.2.trans (div_le_div_of_nonneg_right hεη hk0.le)⟩
  obtain ⟨τ, hτ, hcτ, hcF, hnear, hinv⟩ := hcone Y hk hu hw
  have hfirst := hnear.mono fun _ h => h.1
  obtain ⟨hlogreg, hlogs⟩ := coreReturnMultiplier_log_bounds hk hu' hw' hfirst
  have hhit : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1 :=
    hnear.mono fun _ h => ⟨h.1.1.2, h.2⟩
  have hcon := coreReturnMultiplier_contraction hk hu' hw' hfirst.self_of_nhds
  have hvalueU : coreReturnState τ Y 1 = Y 1 * coreReturnMultiplier τ Y 0 :=
    (coreReturnState_multiplier_formula hhit 0).self_of_nhds
  have hvalueW : coreReturnState τ Y 2 = Y 2 * coreReturnMultiplier τ Y 1 :=
    (coreReturnState_multiplier_formula hhit 1).self_of_nhds
  refine ⟨τ, hτ, hcτ, hcF, hnear, ?_⟩
  intro θ hθ hθ1 v hv0 hv1 hv2 d S
  have hv1' : |v 1| ≤ Real.sqrt (Y 1) :=
    hv1.trans (mul_le_of_le_one_left (Real.sqrt_nonneg _) hθ1)
  have hv2' : |v 2| ≤ Real.sqrt (Y 2) :=
    hv2.trans (mul_le_of_le_one_left (Real.sqrt_nonneg _) hθ1)
  have hconeV := hinv v hv0 hv1' hv2'
  have he : 1 / (32 * Y 0) ≤ 1 / 192 :=
    (div_le_iff₀ (by positivity : 0 < 32 * Y 0)).mpr (by linarith only [hk])
  have hdK : 3 / 4 ≤ d 0 := by linarith only [(abs_le.mp hconeV.2.1).1, he]
  have hrad := coreReturnState_radius_cone_bound hk hu' hw' hfirst v hv0 hv1' hv2'
  have hd (i : Fin 2) := coreReturnState_transverse_differential
    (hcF.differentiableAt (by norm_num)) hhit i ((hlogreg i).differentiableAt (by norm_num)) v
  have hlogs' := hlogs v
  dsimp only at hlogs'
  rw [hv0, abs_one] at hlogs'
  have H := core_cone_slope_bound hk ⟨hε.le, by linarith only [hεη]⟩ hu hw hθ hv1 hv2 hA hB hdK
    ⟨coreFlowMultiplier_pos _ _ _ _ _, hcon.1⟩ ⟨coreFlowMultiplier_pos _ _ _ _ _, hcon.2⟩
    hlogs'.1 hlogs'.2 (hd 0) (hd 1)
  change |d 1| ≤ C * (θ + S) * Real.sqrt (Y 1 * coreReturnMultiplier τ Y 0) * d 0 ∧
    |d 2| ≤ C * (θ + S) * Real.sqrt (Y 2 * coreReturnMultiplier τ Y 1) * d 0 at H
  rw [← hvalueU, ← hvalueW] at H
  refine ⟨hdK, hrad, H.1, H.2, ?_⟩
  intro hU hW
  have houtU : 0 < coreReturnState τ Y 1 := by rw [hvalueU]; exact mul_pos hU (coreFlowMultiplier_pos _ _ _ _ _)
  have houtW : 0 < coreReturnState τ Y 2 := by rw [hvalueW]; exact mul_pos hW (coreFlowMultiplier_pos _ _ _ _ _)
  have hd0 : 0 < d 0 := by linarith only [hdK]
  apply max_le
  · apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr houtU) hd0)).mpr
    simpa only [mul_assoc] using H.1
  · apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr houtW) hd0)).mpr
    simpa only [mul_assoc] using H.2

end BianchiIX

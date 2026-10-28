import BianchiIX.Dynamics.ShearRestartPartialCoreRadialData
import BianchiIX.Dynamics.ShearRestartDownwardReturn
import BianchiIX.Dynamics.PartialCoreDownwardCone

noncomputable section

namespace BianchiIX

open Set

/-- The actual shear family has the square-root exit cone on a uniform scale, including V = 1. -/
theorem exists_restartShearPartialCore_downward_cone :
    ∃ hstar > (0 : ℝ), ∃ K ≥ (1 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let k := restartFastShearCoreRadius h s 1 n₂ n₃
            let U := fun r => Y r 1
            let p := fun r => Y r 2 * Y r 3
            let τ := partialCoreDownwardReturnTime
            let f := fun r => partialCoreDownwardReturnState (Y r) 0
            let fU := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r)) 1
            let fP := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r)) 3
            let A := (200 * coreVariationBound + 2) * K ^ 2
            let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
            1 ≤ Y ρ 2 →
            s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
            IsLeast {t | s < t ∧ toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 t) 2 = 1}
              (s + τ (Y ρ)) ∧
            partialCoreDownwardReturnState (Y ρ) = toCoreAngleState (toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 (s + τ (Y ρ)))) ∧
            DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ fU ρ ∧ DifferentiableAt ℝ fP ρ ∧
            1 / (8192 * a ^ 2) ≤ -deriv f ρ ∧ |deriv f ρ| ≤ (K + 1 / 8192) / a ^ 2 ∧
            0 ≤ fU ρ ∧ 0 ≤ fP ρ ∧ fU ρ ≤ U ρ * Real.exp (-k ρ / 12) ∧ fP ρ ≤ p ρ ∧
            |deriv fU ρ| ≤ (8192 * (K + 24 * A) * Real.sqrt (U ρ)) * Real.sqrt (fU ρ) * |deriv f ρ| ∧
            |deriv fP ρ| ≤ (8192 * K * (1 + B) * a * Real.sqrt (p ρ)) * Real.sqrt (fP ρ) * |deriv f ρ| ∧
            (U ρ = 0 → fU ρ = 0 ∧ deriv fU ρ = 0) ∧
            (p ρ = 0 → fP ρ = 0 ∧ deriv fP ρ = 0) := by
  obtain ⟨hstar, hhstar, K, hK, H⟩ := exists_restartShearPartialCore_radial_data
  have hK0 : 0 < K := by linarith only [hK]
  let C₀ := 4096 * coreVariationBound
  have hC₀ : 0 < C₀ := mul_pos (by norm_num) (Real.exp_pos _)
  refine ⟨hstar, hhstar, K, hK, ?_⟩
  intro h hh q P hq hP
  obtain ⟨a₀, ha₀, Ha⟩ := H h hh q P hq hP
  refine ⟨min a₀ (1 / (8 * C₀ * K ^ 3 * 4096)), lt_min ha₀ (by positivity), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y k U p τ f fU fP A B hv
  obtain ⟨ha1, hs, hrad, hdom, hA, hY, hk, hy, hvcase, hz, hsum, hklo, hkhi, hdk, hdklo, hdU, hdp, hdz⟩ :=
    Ha a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  have hk0 : 0 < k ρ := by linarith only [hk]
  have hki : 1 / k ρ ≤ K * a := by
    apply (div_le_iff₀ hk0).mpr
    have Hb := (div_le_iff₀ (mul_pos hK0 ha.1)).mp hklo
    nlinarith only [Hb]
  have hsum' : U ρ + a * p ρ ≤ K * a := by
    have Hp := mul_le_mul_of_nonneg_right ha1 hy.2.2.2.1
    have Hsum := hsum.trans hki
    change U ρ + p ρ ≤ K * a at Hsum
    nlinarith only [Hp, Hsum]
  have hsmall : 4 * C₀ * K ^ 2 * (U ρ + a * p ρ) ≤ 1 / (2 * 4096) := by
    apply le_trans (mul_le_mul_of_nonneg_left hsum' (by positivity))
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 * 4096)).mpr
    have Hb := (le_div_iff₀ (by positivity : 0 < 8 * C₀ * K ^ 3 * 4096)).mp
      (ha.2.trans (min_le_right _ _))
    nlinarith only [Hb]
  have hkZ : 2 * Real.cosh 0 ≤ k ρ := by rw [Real.cosh_zero]; linarith only [hk]
  have HC := partialCoreDownwardReturn_radial_cone ⟨ha.1, ha1⟩ hK (by norm_num : (0 : ℝ) < 4096)
    (le_refl (0 : ℝ)) hY hk hy hvcase hkZ hz hklo hkhi hdk hdklo hdU hdp hdz hsmall
  have hfirst := (partialCoreDownwardReturn_regular hk hy rfl hvcase).1
  have Hflow (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad.le hs hA ht
  refine ⟨hdom, ?_, ?_, ?_⟩
  · refine ⟨⟨by linarith only [hfirst.1.1], ?_⟩, ?_⟩
    · rw [← Hflow _ hfirst.1.1.le]
      exact hfirst.1.2
    · intro t ht
      have hsub : 0 < t - s := sub_pos.mpr ht.1
      have HF := Hflow (t - s) hsub.le
      rw [add_sub_cancel] at HF
      have Hleast := hfirst.2 ⟨hsub, by rw [HF]; exact ht.2⟩
      linarith only [Hleast]
  · change toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 (τ (Y ρ))) = _
    rw [Hflow _ hfirst.1.1.le]
  · simp only [show (2 : ℝ) * 4096 = 8192 by norm_num] at HC
    exact HC

end BianchiIX

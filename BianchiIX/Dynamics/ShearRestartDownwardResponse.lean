import BianchiIX.Dynamics.ShearRestartPartialCoreRadialData
import BianchiIX.Dynamics.ShearRestartDownwardReturn
import BianchiIX.Dynamics.PartialCoreDownwardRadialCurve
import BianchiIX.Dynamics.PartialCoreDownwardRadialMultipliers

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Radius, phase and wall responses are on one actual downward return for every shear entry with V at least one. -/
theorem exists_restartShearPartialCore_downward_response :
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
            let m := fun i r => partialCoreReturnMultiplier τ (Y r) i
            let fU := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r)) 1
            let fP := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r)) 3
            let C := 4096 * coreVariationBound
            let A := (200 * coreVariationBound + 2) * K ^ 2
            let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
            let L := Real.log (4 * k ρ)
            1 ≤ Y ρ 2 →
            s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
            IsLeast {t | s < t ∧ toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 t) 2 = 1}
              (s + τ (Y ρ)) ∧
            partialCoreDownwardReturnState (Y ρ) = toCoreAngleState (toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 (s + τ (Y ρ)))) ∧
            (DifferentiableAt ℝ f ρ ∧ k ρ / 2 ≤ f ρ ∧ f ρ ≤ 2 * k ρ ∧
              DifferentiableAt ℝ (fun r => f r - k r) ρ ∧
              |f ρ - k ρ| ≤ 16 * K * (U ρ + a * (p ρ) ^ 2) ∧
              |deriv (fun r => f r - k r) ρ| ≤ 4 * C * K ^ 2 * (U ρ + a * p ρ) / a ^ 2 ∧
              DifferentiableAt ℝ (fun r => 2 / f r - 2 / k r) ρ ∧
              |2 / f ρ - 2 / k ρ| ≤ 32 * K ^ 3 * a ^ 2 * (U ρ + a * (p ρ) ^ 2) ∧
              |deriv (fun r => 2 / f r - 2 / k r) ρ| ≤
                (8 * C * K ^ 4 + 64 * K ^ 5) * (U ρ + a * p ρ)) ∧
            (∀ i : Fin 2, 0 < m i ρ ∧ DifferentiableAt ℝ (m i) ρ ∧
              DifferentiableAt ℝ (fun r => Real.log (m i r)) ρ) ∧
            (fU =ᶠ[𝓝 ρ] fun r => U r * m 0 r) ∧ (fP =ᶠ[𝓝 ρ] fun r => p r * m 1 r) ∧
            |deriv (fun r => Real.log (m 0 r)) ρ| ≤ A * L / a ^ 2 ∧
            |deriv (fun r => Real.log (m 1 r)) ρ| ≤ B * L ∧
            DifferentiableAt ℝ fU ρ ∧ DifferentiableAt ℝ fP ρ ∧ 0 ≤ fU ρ ∧ 0 ≤ fP ρ ∧
            |deriv fU ρ| ≤ fU ρ * (K / a + A * L / a ^ 2) ∧
            |deriv fP ρ| ≤ fP ρ * (K / a + B * L) ∧
            (U ρ = 0 → fU ρ = 0 ∧ deriv fU ρ = 0) ∧
            (p ρ = 0 → fP ρ = 0 ∧ deriv fP ρ = 0) := by
  obtain ⟨hstar, hhstar, K, hK, H⟩ := exists_restartShearPartialCore_radial_data
  refine ⟨hstar, hhstar, K, hK, ?_⟩
  intro h hh q P hq hP
  obtain ⟨astar, hastar, Ha⟩ := H h hh q P hq hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y k U p τ f m fU fP C A B L hv
  obtain ⟨ha1, hs, hrad, hdom, hA, hY, hk, hy, hvcase, _, _, hklo, hkhi, hdk, _, hdU, hdp, hdz⟩ :=
    Ha a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  have hk0 : 0 < k ρ := by linarith only [hk]
  have hK0 : 0 < K := by linarith only [hK]
  have hki : 1 / k ρ ≤ K * a := by
    apply (div_le_iff₀ hk0).mpr
    have Hb := (div_le_iff₀ (mul_pos hK0 ha.1)).mp hklo
    nlinarith only [Hb]
  have HR := partialCoreDownwardReturn_radial_response ⟨ha.1, ha1⟩ hK hY
    hk hy hvcase hklo hkhi hdk hdU hdp hdz
  have HM := partialCoreDownwardReturn_radial_multipliers ⟨ha.1, ha1⟩ hK hY
    hk hy hvcase hki hkhi hdk hdU hdp hdz
  have hfirst := (partialCoreDownwardReturn_regular hk hy rfl hvcase).1
  have Hflow (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad.le hs hA ht
  refine ⟨hdom, ?_, ?_, HR, HM⟩
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

end BianchiIX

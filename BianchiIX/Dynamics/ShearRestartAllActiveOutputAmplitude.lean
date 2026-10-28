import BianchiIX.Dynamics.ShearRestartEntranceOutputAmplitude
import BianchiIX.Dynamics.ShearRestartOutputAmplitude

noncomputable section

namespace BianchiIX

open Set

/-- One fixed return reaches the reflected ascending section with a uniform product amplitude budget for every positive active wall. -/
theorem exists_restartShearReturn_all_active_output_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
            let p := restartShearReturnParameters h s n₂ n₃ ρ
            let G := restartShearReturnState h s n₂ n₃ ρ
            connectionReturnValid p ∧ s < restartShearReturnTime h s n₂ n₃ ρ ∧
              1 / (64 * a) ≤ G 0 ∧ G 0 ≤ 64 / a ∧
              0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * n₂ * n₃ / a ^ 4 ∧
              coreRadiusEntry G = projectiveReflection (toProjectiveState
                (normalizedMaxCurve x 0 (restartShearReturnTime h s n₂ n₃ ρ))) := by
  obtain ⟨hU, hhU, HU⟩ := exists_restartShearConnection_output_bounds
  obtain ⟨hL, hhL, HL⟩ := exists_restartShearEntrance_output_bounds
  refine ⟨min hU hL, lt_min hhU hhL, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aU, haU, HaU⟩ := HU h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aL, haL, HaL⟩ := HL h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aU aL, lt_min haU haL, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s x p G
  by_cases hv : 1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2
  · obtain ⟨hT, _, hvalid, hlo, hhi, hu, hw, hsum, hentry⟩ :=
      HaU a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ h₃P ρ hρ hv
    refine ⟨hvalid, ?_, hlo, hhi, hu, hw, hsum, hentry⟩
    have htc : 0 < connectionReturnTime p := hvalid.1.1.1
    change s < s + partialCoreDownwardReturnTime (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ) + connectionReturnTime p
    linarith only [hT, htc]
  · exact HaL a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ (lt_of_not_ge hv)

end BianchiIX

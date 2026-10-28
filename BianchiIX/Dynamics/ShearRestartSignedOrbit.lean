import BianchiIX.Dynamics.ShearRestartNegativeReturn
import BianchiIX.Dynamics.MainWallReflection

noncomputable section

namespace BianchiIX

open Set

theorem mainWallChart_restartShear {h τ n₂ n₃ ρ : ℝ} (h₂ : 0 < n₂) (h₃ : 0 < n₃) :
    mainWallChart h ![τ * ρ, -Real.log n₂, -Real.log n₃] =
      restartSectionChart h (restartShearCurve τ n₂ n₃ ρ) := by
  simp [mainWallChart, mainWallRadicand, restartSectionChart, restartSectionRadicand,
    restartShearCurve, Real.exp_log h₂, Real.exp_log h₃]

theorem mainWallRadicand_restartShear {h τ n₂ n₃ ρ : ℝ} (h₂ : 0 < n₂) (h₃ : 0 < n₃) :
    mainWallRadicand h ![τ * ρ, -Real.log n₂, -Real.log n₃] =
      restartSectionRadicand h (restartShearCurve τ n₂ n₃ ρ) := by
  simp [mainWallRadicand, restartSectionRadicand, restartShearCurve, Real.exp_log h₂, Real.exp_log h₃]

/-- Both shear signs have an actual positive-time return to the same statistical core chart, with its physical frame stated explicitly. -/
theorem exists_restartShear_signed_orbit :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε τ n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (τ = 1 ∨ τ = -1) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let z := if τ = 1 then (n₂, n₃) else (n₃, n₂)
          let y : SectionCoordinates := ![τ * ρ, -Real.log n₂, -Real.log n₃]
          let T := restartShearReturnTime h s z.1 z.2 ρ
          let G := restartShearReturnState h s z.1 z.2 ρ
          y ∈ mainWallChartDomain h ∧ 0 < T ∧ T ∈ normalizedMaxDomain (mainWallChart h y) 0 ∧
            (coreRadiusEntry G = toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T) ∨
              coreRadiusEntry G = projectiveReflection (toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T))) := by
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_common_bounds
  obtain ⟨hN, hhN, HN⟩ := exists_restartShear_negative_output_bounds
  refine ⟨min hA hN, lt_min hhA hhN, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aN, haN, HAN⟩ := HN h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aA aN, lt_min haA haN, ?_⟩
  intro a ha ε τ n₂ n₃ hε hτ h₂ h₃ hmin ρ hρ
  rcases hτ with rfl | rfl
  · simp only [ite_true]
    obtain ⟨hrad, hs, ht, hdom, _, _, _, _, _, _, ho⟩ :=
      HAA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin ρ hρ
    refine ⟨?_, hs.trans_lt ht, ?_, Or.inr ?_⟩
    · change 0 < mainWallRadicand h ![1 * ρ, -Real.log n₂, -Real.log n₃]
      rwa [mainWallRadicand_restartShear h₂.1 h₃.1]
    · rwa [mainWallChart_restartShear h₂.1 h₃.1]
    · rwa [mainWallChart_restartShear h₂.1 h₃.1]
  · simp only [if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    obtain ⟨hrad, hs, ht, hdom, _, _, _, _, _, _, ho⟩ :=
      HAN a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin ρ hρ
    refine ⟨?_, hs.trans_lt ht, ?_, Or.inl ?_⟩
    · change 0 < mainWallRadicand h ![(-1) * ρ, -Real.log n₂, -Real.log n₃]
      rwa [mainWallRadicand_restartShear h₂.1 h₃.1]
    · rwa [mainWallChart_restartShear h₂.1 h₃.1]
    · rwa [mainWallChart_restartShear h₂.1 h₃.1]

end BianchiIX

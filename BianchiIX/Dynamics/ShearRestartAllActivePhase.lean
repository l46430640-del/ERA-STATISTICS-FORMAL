import BianchiIX.Dynamics.ShearRestartEntrancePhase
import BianchiIX.Dynamics.ShearRestartReturnControl

noncomputable section

namespace BianchiIX

open Set

/-- The fixed positive-shear return has uniform reference-phase error and a nondegenerate
radial derivative throughout the positive-wall annulus. -/
theorem exists_restartShearReturn_all_active_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∃ C > (0 : ℝ), ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let X := restartShearReturnPhase h s n₂ n₃
              let F := fun r => restartReferenceRadialPhase h (restartShearCurve 1 n₂ n₃ r)
              DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ C * a ^ 2 ∧
                |deriv X ρ - deriv F ρ| ≤ C * a ∧
                1 / (8 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨hU, hhU, HU⟩ := exists_restartShearReturn_control
  obtain ⟨hL, hhL, HL⟩ := exists_restartShearEntrance_output_phase
  refine ⟨min hU hL, lt_min hhU hhL, ?_⟩
  intro h hh
  obtain ⟨CU, hCU, HCU⟩ := HU h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  obtain ⟨CL, hCL, HCL⟩ := HL h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
  refine ⟨CU + CL, add_pos hCU hCL, ?_⟩
  intro q P hq hP
  obtain ⟨aU, haU, HaU⟩ := HCU q P hq hP
  obtain ⟨aL, haL, HaL⟩ := HCL q P hq hP
  refine ⟨min aU aL, lt_min haU haL, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s X F
  have H : ∃ D ≤ CU + CL, DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ D * a ^ 2 ∧
      |deriv X ρ - deriv F ρ| ≤ D * a ∧
      1 / (8 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ D := by
    by_cases hv : 1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, Hrest⟩ :=
        HaU a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ h₃P ρ hρ hv
      exact ⟨CU, le_add_of_nonneg_right hCL.le, Hrest⟩
    · exact ⟨CL, le_add_of_nonneg_left hCU.le,
        HaL a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ (lt_of_not_ge hv)⟩
  obtain ⟨D, hD, hX, hval, hder, hlo, hhi⟩ := H
  exact ⟨hX, hval.trans (mul_le_mul_of_nonneg_right hD (sq_nonneg a)),
    hder.trans (mul_le_mul_of_nonneg_right hD ha.1.le), hlo, hhi.trans hD⟩

end BianchiIX

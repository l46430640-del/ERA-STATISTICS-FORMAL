import BianchiIX.Dynamics.ShearRestartAllActivePhase
import BianchiIX.Dynamics.ShearRestartTailFastReturn

noncomputable section

namespace BianchiIX

open Set

/-- Compare once with the reference slope, rather than spending a positive-slope margin at every stage. -/
theorem restartShearPhase_deriv_lower {h σ n₂ n₃ ρ a ε C : ℝ} {X : ℝ → ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (ha : 0 < a) (hρ : ρ ∈ Icc a (2 * a))
    (hσ : |σ| = 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 64)
    (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a)
    (herr : |deriv X ρ - deriv (fun r => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ r)) ρ| ≤ C * a)
    (hsmall : C * a ≤ 1 / (4 * Real.sqrt 3)) :
    1 / (4 * Real.sqrt 3) ≤ deriv X ρ := by
  have H := (restartReferenceRadialPhase_shear_derivative hh ha hρ hσ hε h₂ h₃).2.1
  have heq : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
  rw [heq] at H
  linarith only [H, (abs_le.mp herr).1, hsmall]

/-- The full small-decaying-wall shear family has a quarter-reference lower slope. -/
theorem exists_restartShearReturn_all_active_phase_quarter :
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
                1 / (4 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨h₀, hh₀, HH⟩ := exists_restartShearReturn_all_active_phase
  refine ⟨min h₀ (1 / 16), lt_min hh₀ (by norm_num), ?_⟩
  intro h hh
  obtain ⟨C, hC, HC⟩ := HH h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  obtain ⟨a₀, ha₀, HA⟩ := HC q P hq hP
  refine ⟨min a₀ (1 / (4 * Real.sqrt 3 * C)), lt_min ha₀ (by positivity), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s X F
  obtain ⟨hX, hv, hd, _, hu⟩ := HA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  refine ⟨hX, hv, hd, ?_, hu⟩
  apply restartShearPhase_deriv_lower ⟨hh.1.le, hh.2.trans (min_le_right _ _)⟩
    ha.1 hρ (by norm_num : |(1 : ℝ)| = 1) hε ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ hd
  have H := mul_le_mul_of_nonneg_left (ha.2.trans (min_le_right _ _)) hC.le
  exact H.trans_eq (by field_simp)

/-- The complete long-tail family has the same quarter-reference slope on the original fast-cutoff map. -/
theorem exists_restartShearTail_fast_output_phase_quarter :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 3 < q → 4 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let X := restartShearReturnPhase h s ζ ν
            let F := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ C * a ^ 2 ∧
            |deriv X ρ - deriv F ρ| ≤ C * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨h₀, hh₀, HH⟩ := exists_restartShearTail_fast_output_phase
  refine ⟨min h₀ (1 / 16), lt_min hh₀ (by norm_num), ?_⟩
  intro h hh q D hq hD
  obtain ⟨C, hC, HC⟩ := HH h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq hD
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨a₀, ha₀, HA⟩ := HC P hP
  refine ⟨min a₀ (1 / (4 * Real.sqrt 3 * C)), lt_min ha₀ (by positivity), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s X F
  obtain ⟨hX, hv, hd, _, hu⟩ := HA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  refine ⟨hX, hv, hd, ?_, hu⟩
  apply restartShearPhase_deriv_lower ⟨hh.1.le, hh.2.trans (min_le_right _ _)⟩
    ha.1 hρ (by norm_num : |(1 : ℝ)| = 1) ⟨hε.1, by linarith only [hε.2]⟩
    ⟨hζ.1.le, hζ.2.2⟩ ⟨hν.1.le, hν.2⟩ hd
  have H := mul_le_mul_of_nonneg_left (ha.2.trans (min_le_right _ _)) hC.le
  exact H.trans_eq (by field_simp)

end BianchiIX

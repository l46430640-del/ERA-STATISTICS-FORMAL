import BianchiIX.Dynamics.ShearRestartProjectiveEntry
import BianchiIX.Dynamics.ProjectiveReflection

noncomputable section

namespace BianchiIX

theorem restartSectionRadicand_shear_reflection (h σ n₂ n₃ ρ : ℝ) :
    restartSectionRadicand h (restartShearCurve (-σ) n₃ n₂ ρ) =
      restartSectionRadicand h (restartShearCurve σ n₂ n₃ ρ) := by
  dsimp [restartSectionRadicand, restartShearCurve, curvature]
  ring

/-- Reversing the shear and exchanging the weak walls is an exact physical axis swap. -/
theorem restartSectionChart_shear_reflection (h σ n₂ n₃ ρ : ℝ) :
    restartSectionChart h (restartShearCurve (-σ) n₃ n₂ ρ) =
      axisSwap (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) := by
  simp only [restartSectionChart, restartSectionRadicand_shear_reflection]
  ext i
  fin_cases i <;> dsimp [restartShearCurve, axisSwap]
  all_goals ring

theorem normalizedMaxDomain_shear_reflection (h σ n₂ n₃ ρ t₀ : ℝ) :
    normalizedMaxDomain (restartSectionChart h (restartShearCurve (-σ) n₃ n₂ ρ)) t₀ =
      normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) t₀ := by
  rw [restartSectionChart_shear_reflection]
  exact NormalizedSymmetry.swap.maxDomain _ _

theorem normalizedMaxCurve_shear_reflection {h σ n₂ n₃ ρ t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) t₀) :
    normalizedMaxCurve (restartSectionChart h (restartShearCurve (-σ) n₃ n₂ ρ)) t₀ t =
      axisSwap (normalizedMaxCurve (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) t₀ t) := by
  rw [restartSectionChart_shear_reflection]
  exact NormalizedSymmetry.swap.maxCurve ht

theorem restartFastShearProjectiveEntry_reflection {h s σ n₂ n₃ ρ : ℝ}
    (hs : s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0) :
    restartFastShearProjectiveEntry h s (-σ) n₃ n₂ ρ =
      projectiveReflection (restartFastShearProjectiveEntry h s σ n₂ n₃ ρ) := by
  unfold restartFastShearProjectiveEntry
  rw [normalizedMaxCurve_shear_reflection hs, toProjectiveState_axisSwap]

/-- The reference phase is invariant under the same physical axis swap, as a function of the full input. -/
theorem restartReferenceRadialPhase_shear_reflection (h σ n₂ n₃ ρ : ℝ) :
    restartReferenceRadialPhase h (restartShearCurve (-σ) n₃ n₂ ρ) =
      restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ ρ) := by
  unfold restartReferenceRadialPhase
  congr 2
  dsimp [restartQuadratic, restartShearCurve]
  ring

end BianchiIX

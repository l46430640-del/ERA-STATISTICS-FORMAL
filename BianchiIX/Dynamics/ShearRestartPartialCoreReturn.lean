import BianchiIX.Dynamics.ShearRestartPartialCoreEntry
import BianchiIX.Dynamics.PartialCoreEvents

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The shear-family fast layer reaches its first outgoing core event in original Einstein time, also from V = 1. -/
theorem exists_restartShearPartialCore_firstReturn :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 64) → (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
            let k := restartFastShearCoreRadius h T 1 n₂ n₃ ρ
            let β := fun u => toProjectiveState (normalizedMaxCurve x 0 u)
            1 ≤ β T 2 → ∃ t > T, IsLeast {u | T < u ∧ β u 2 = 1} t ∧
              β t 0 < 1 ∧ 0 < coreAngle (β t 0) (β t 2) ∧
              deriv (fun u => β u 2) t ≤ -(1 + normalizedMaxCurve x 0 t 0) * k / 2 ∧
              t - T ≤ 2 * k * Real.log (4 * k) ∧ ∀ u ∈ Icc T t,
                3 / (2 * k ^ 2) ≤ 1 + normalizedMaxCurve x 0 u 0 ∧ coreRegion k (β u) ∧
                |coreRadius (β u 0) (β u 2) - k| ≤ 16 * (β T 1 + (β T 2 * β T 3) ^ 2 / k) ∧
                |coreRadius (β u 0) (β u 2) ^ 2 - k ^ 2| < 1 / 16 := by
  obtain ⟨hstar, hhstar, H⟩ := exists_restartShearPartialCore_entry
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q P hq hP η hη
  obtain ⟨astar, hastar, Ha⟩ := H h hh q P hq hP η hη
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ T x k β hv
  obtain ⟨hT, hrad, _, hA, _, hk, _, _, hR, _, _, _, Hentry⟩ :=
    Ha a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  obtain ⟨_, _, hregion, hvcase⟩ := Hentry hv
  exact exists_normalized_partialCore_firstReturn (restartSectionChart_constraint hrad.le)
    hk hT hA hR hvcase hregion.2.2.1 hregion.2.2.2

/-- At an interior entry, the same first outgoing event has an ordinary ambient C2 time and endpoint. -/
theorem exists_restartShearPartialCore_firstReturn_two :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 64) → (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
            1 < restartFastShearProjectiveEntry h T 1 n₂ n₃ ρ 2 →
            ∃ t > T, ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 2 τ x ∧
              ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y))) x ∧
              HasFDerivAt τ (normalizedEventTimeDifferential projectiveActiveWall x 0 t) x ∧
              HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y)))
                ((fderiv ℝ toProjectiveState (normalizedMaxCurve x 0 t)).comp
                  (normalizedEventDifferential projectiveActiveWall x 0 t)) x ∧
              (∀ᶠ y in 𝓝 x,
                IsLeast {u | T < u ∧ u ∈ normalizedMaxDomain y 0 ∧
                  projectiveActiveWall (normalizedMaxCurve y 0 u) = 1} (τ y) ∧
                (∀ u ∈ Icc T (τ y), u ∈ normalizedMaxDomain y 0 ∧ 0 < 1 + normalizedMaxCurve y 0 u 0) ∧
                normalizedEventRate projectiveActiveWall y 0 (τ y) < 0) := by
  obtain ⟨hstar, hhstar, H⟩ := exists_restartShearPartialCore_entry
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q P hq hP η hη
  obtain ⟨astar, hastar, Ha⟩ := H h hh q P hq hP η hη
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ T x hv
  obtain ⟨hT, hrad, _, hA, _, hk, _, _, hR, _, _, _, Hentry⟩ :=
    Ha a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  obtain ⟨_, _, hregion, _⟩ := Hentry hv.le
  exact exists_normalized_partialCore_firstReturn_two (restartSectionChart_constraint hrad.le)
    hk hT hA hR hv hregion.2.2.1 hregion.2.2.2

end BianchiIX

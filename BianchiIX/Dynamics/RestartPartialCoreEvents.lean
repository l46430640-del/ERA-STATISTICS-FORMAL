import BianchiIX.Dynamics.RestartPartialCoreEntry
import BianchiIX.Dynamics.PartialCoreEvents

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The first partial-core exit of every actual fast-layer input has a C2 event time and endpoint. -/
theorem exists_restartPartialCore_firstReturn_two :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∀ ε ∈ Ioc (0 : ℝ) (1 / 10000), ∃ rstar : ℝ, 0 < rstar ∧
          ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) →
            ∀ ρ ∈ Icc r (2 * r),
              let T := q / 2 * Real.log (1 / r)
              let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
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
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartPartialCore_entry
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP ε hε
  obtain ⟨rstar, hrstar, HR⟩ := HH h hh L hL q P hq hP ε hε
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  obtain ⟨hT, hrad, _, hA, hk, _, hR, _, _, _, hv, _, hregion⟩ := HR r hr θ ζ hθ hζ ρ hρ
  have hc := restartSectionChart_constraint hrad.le
  have hk6 : 6 ≤ restartFastCoreRadius h (q / 2 * Real.log (1 / r)) θ ζ ρ := (le_max_left _ _).trans hk
  exact exists_normalized_partialCore_firstReturn_two hc hk6 hT hA hR
    (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hv) hregion.2.2.1 hregion.2.2.2

end BianchiIX

import BianchiIX.Dynamics.RestartPartialCoreEntry
import BianchiIX.Dynamics.PartialCoreFirstReturn

noncomputable section

namespace BianchiIX

open Set

/-- The exact fast-layer family completes its first outgoing core event on a common radius scale. -/
theorem exists_restartPartialCore_firstReturn :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∀ ε ∈ Ioc (0 : ℝ) (1 / 10000), ∃ rstar : ℝ, 0 < rstar ∧
          ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) →
            ∀ ρ ∈ Icc r (2 * r),
              let T := q / 2 * Real.log (1 / r)
              let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
              let k := restartFastCoreRadius h T θ ζ ρ
              let β := fun u => toProjectiveState (normalizedMaxCurve x 0 u)
              ∃ t > T, IsLeast {u | T < u ∧ β u 2 = 1} t ∧
                β t 0 < 1 ∧ 0 < coreAngle (β t 0) (β t 2) ∧
                deriv (fun u => β u 2) t ≤ -(1 + normalizedMaxCurve x 0 t 0) * k / 2 ∧
                t - T ≤ 2 * k * Real.log (4 * k) ∧ ∀ u ∈ Icc T t,
                  3 / (2 * k ^ 2) ≤ 1 + normalizedMaxCurve x 0 u 0 ∧ coreRegion k (β u) ∧
                  |coreRadius (β u 0) (β u 2) - k| ≤ 16 * (β T 1 + (β T 2 * β T 3) ^ 2 / k) ∧
                  |coreRadius (β u 0) (β u 2) ^ 2 - k ^ 2| < 1 / 16 := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartPartialCore_entry
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP ε hε
  obtain ⟨rstar, hrstar, HR⟩ := HH h hh L hL q P hq hP ε hε
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  obtain ⟨hT, hrad, _, hA, hk, _, hR, _, _, _, hv, _, hregion⟩ := HR r hr θ ζ hθ hζ ρ hρ
  have hc := restartSectionChart_constraint hrad.le
  have hk6 : 6 ≤ restartFastCoreRadius h (q / 2 * Real.log (1 / r)) θ ζ ρ :=
    (le_max_left _ _).trans hk
  exact exists_normalized_partialCore_firstReturn hc hk6 hT hA hR
    (Or.inl (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hv)) hregion.2.2.1 hregion.2.2.2

end BianchiIX

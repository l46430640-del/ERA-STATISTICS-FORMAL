import BianchiIX.Dynamics.RestartPartialCoreEntry
import BianchiIX.Dynamics.PartialCoreContraction

noncomputable section

namespace BianchiIX

open Set

/-- The actual fast-layer family has the uniform partial-core angle length and exit decay (E.18). -/
theorem exists_restartPartialCore_exit_bounds :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∀ ε ∈ Ioc (0 : ℝ) (1 / 10000), ∃ rstar : ℝ, 0 < rstar ∧
          ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) →
            ∀ ρ ∈ Icc r (2 * r),
              let T := q / 2 * Real.log (1 / r)
              let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
              let k := restartFastCoreRadius h T θ ζ ρ
              let β := fun u => toProjectiveState (normalizedMaxCurve x 0 u)
              let z := fun u => coreAngle (β u 0) (β u 2)
              ∃ t > T, IsLeast {u | T < u ∧ β u 2 = 1} t ∧
                Real.log (99 / 50 : ℝ) ≤ z t - z T ∧ 49 / 99 ≤ z t - z T ∧
                β t 1 ≤ β T 1 * Real.exp (-k / 12) ∧ β t 3 ≤ β T 2 * β T 3 ∧
                β t 0 < 1 ∧
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
  let T := q / 2 * Real.log (1 / r)
  let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
  let k := restartFastCoreRadius h T θ ζ ρ
  let β := fun u => toProjectiveState (normalizedMaxCurve x 0 u)
  let Z := Real.arsinh (4 * (8 * (L + 1)))
  obtain ⟨hT, hrad, _, hA, hk, hz, hR, _, _, _, hv, _, hregion⟩ := HR r hr θ ζ hθ hζ ρ hρ
  have hc : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have hk6 : 6 ≤ k := (le_max_left _ _).trans hk
  have hk0 : 0 < k := by linarith only [hk6]
  have hZ : 0 ≤ Z := Real.arsinh_nonneg_iff.mpr (by positivity)
  obtain ⟨t, ht, hleast, hm, _, hder, htime, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk6 hT hA hR
      (Or.inl (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hv)) hregion.2.2.1 hregion.2.2.2
  have hpos (u : ℝ) (hu : u ∈ Icc T t) : 0 < 1 + normalizedMaxCurve x 0 u 0 :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (H u hu).1
  obtain ⟨hgap, hgap', hU, hW⟩ := normalized_partialCore_exit_contraction hc hk6 hT ht hZ
    ((le_max_right _ _).trans hk) hpos (fun u hu => (H u hu).2.1) hz.2 hleast.1.2
  exact ⟨t, ht, hleast, hgap, hgap', hU, hW, hm, hder, htime, H⟩

end BianchiIX

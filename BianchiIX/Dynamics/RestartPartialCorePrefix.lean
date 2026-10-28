import BianchiIX.Dynamics.RestartPartialCoreEntry

noncomputable section

namespace BianchiIX

open Set

theorem normalized_coreRegion_angle_evolution {x : NormalizedState} {t₀ t k : ℝ}
    (hc : stateConstraint x = 1) (ht : t₀ ≤ t) (hk : 6 ≤ k)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (hy : coreRegion k (toProjectiveState (normalizedMaxCurve x t₀ t))) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    let z := fun u => coreAngle (β u 0) (β u 2)
    let S := fun u => toCoreAngleState (β u)
    let ω := (1 + normalizedMaxCurve x t₀ t 0) * coreRadius (β t 0) (β t 2) *
      coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3)
    1 / k ≤ ω ∧ HasDerivAt z ω t ∧ HasDerivAt S (ω • coreAngleField (z t) (S t)) t := by
  intro β z S ω
  have Hactual := normalizedMaxCurve_forward_of_constraint hc ht
  have Hβ := hasDerivAt_toProjectiveState_normalized Hactual.1 (ne_of_gt hA) Hactual.2.1
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hv : 0 < β t 2 := zero_lt_one.trans_le hy.2.1
  have hd := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
  have Hlower := coreBootstrap_original_clock_lower hk hr hv.le hu hw
  have Hscale : 6 / projectiveDenom (β t 0) (β t 1) (β t 2) (β t 3) =
      1 + normalizedMaxCurve x t₀ t 0 := projective_inverse_scale (ne_of_gt hA) Hactual.2.1
  rw [Hscale] at Hlower
  exact ⟨Hlower, hasDerivAt_coreAngle_scaled Hβ hv,
    hasDerivAt_toCoreAngleState_scaled Hβ hv (by linarith only [hd])⟩

/-- Actual partial-core entries extend for positive time, with the exact angular system and a nonvanishing clock. -/
theorem exists_restartPartialCore_prefix :
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
              let S := fun u => toCoreAngleState (β u)
              ∃ tend > T, ∀ t ∈ Icc T tend,
                let A := 1 + normalizedMaxCurve x 0 t 0
                let ω := A * coreRadius (β t 0) (β t 2) *
                  coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3)
                3 / (2 * k ^ 2) < A ∧ coreRegion k (β t) ∧ 1 / k ≤ ω ∧
                  HasDerivAt z ω t ∧ HasDerivAt S (ω • coreAngleField (z t) (S t)) t := by
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
  obtain ⟨hT, hrad, _, hA, hk, _, _, _, _, _, hv, _, hregion⟩ := HR r hr θ ζ hθ hζ ρ hρ
  have hc : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have hk6 : 6 ≤ k := (le_max_left _ _).trans hk
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk6
  have he : |coreEnergy (β T 0) (β T 2) - k ^ 2| < 1 / 8 := by
    change |coreEnergy (β T 0) (β T 2) - coreRadius (β T 0) (β T 2) ^ 2| < 1 / 8
    rw [coreRadius_sq, sub_self, abs_zero]
    norm_num
  obtain ⟨tend, htend, HT⟩ := normalized_core_local_prefix hc hk6 hT hA he
    (Or.inl (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hv)) hregion.2.2.1 hregion.2.2.2
  refine ⟨tend, htend, ?_⟩
  intro t ht
  obtain ⟨hAt, hyt⟩ := HT t ht
  have hApos : 0 < 1 + normalizedMaxCurve x 0 t 0 :=
    lt_trans (by positivity : 0 < 3 / (2 * k ^ 2)) hAt
  exact ⟨hAt, hyt, normalized_coreRegion_angle_evolution hc (hT.trans ht.1) hk6 hApos hyt⟩

end BianchiIX

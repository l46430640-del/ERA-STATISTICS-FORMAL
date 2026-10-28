import BianchiIX.Dynamics.PartialCoreRadialCone
import BianchiIX.Dynamics.RestartPartialCoreResponse

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The exact fast entrance produces the actual square-root exit cone on one uniform small scale. -/
theorem exists_restartPartialCore_radial_cone :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 1 ≤ K ∧ ∃ D : ℝ, 0 < D ∧
        ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let k := restartFastCoreRadius h s θ ζ
            let U := fun a => Y a 1
            let p := fun a => Y a 2 * Y a 3
            let A := (200 * coreVariationBound + 2) * K ^ 2
            let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
            s ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            (∀ t : ℝ, 0 ≤ t → projectiveOriginalFlow (Y ρ) 0 t = toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 (s + t))) ∧
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
              IsLeast {t | s < t ∧ toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 t) 2 = 1} (s + T) ∧
              ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                (∀ᶠ y in 𝓝 (Y ρ), IsLeast {t | 0 < t ∧
                  t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
                let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
                  (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
                let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
                let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
                DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ fU ρ ∧ DifferentiableAt ℝ fP ρ ∧
                1 / (2 * D * r ^ 2) ≤ -deriv f ρ ∧ |deriv f ρ| ≤ (K + 1 / (2 * D)) / r ^ 2 ∧
                0 ≤ fU ρ ∧ 0 ≤ fP ρ ∧ fU ρ ≤ U ρ * Real.exp (-k ρ / 12) ∧ fP ρ ≤ p ρ ∧
                |deriv fU ρ| ≤ (2 * D * (K + 24 * A) * Real.sqrt (U ρ)) * Real.sqrt (fU ρ) * |deriv f ρ| ∧
                |deriv fP ρ| ≤ (2 * D * K * (1 + B) * r * Real.sqrt (p ρ)) * Real.sqrt (fP ρ) * |deriv f ρ| ∧
                (U ρ = 0 → fU ρ = 0 ∧ deriv fU ρ = 0) ∧
                (p ρ = 0 → fP ρ = 0 ∧ deriv fP ρ = 0) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartPartialCore_radial_data
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL
  obtain ⟨K, hK, D, hD, HK⟩ := HH h hh L hL
  have hK0 : 0 < K := by linarith only [hK]
  let C₀ := 4096 * coreVariationBound
  have hC₀ : 0 < C₀ := mul_pos (by norm_num) (Real.exp_pos _)
  refine ⟨K, hK, D, hD, ?_⟩
  intro q P hq hP
  obtain ⟨r₀, hr₀, HR⟩ := HK q P hq hP
  refine ⟨min r₀ (1 / (8 * C₀ * K ^ 3 * D)), lt_min hr₀ (by positivity), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  obtain ⟨hr1, hs, hrad, hdom, hA, hY, hZ, hk6, hz, hy, hV, hsum, hklo, hkhi, hdk, hdklo, hdU, hdp, hdz⟩ :=
    HR r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let k := restartFastCoreRadius h s θ ζ
  have hk : 6 ≤ k ρ := (le_max_left _ _).trans hk6
  have hk0 : 0 < k ρ := by linarith only [hk]
  have hki : 1 / k ρ ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    nlinarith only [H]
  have hsum' : Y ρ 1 + r * (Y ρ 2 * Y ρ 3) ≤ K * r := by
    have H := mul_le_mul_of_nonneg_right hr1 hy.2.2.2.1
    have Hsum := hsum.trans hki
    change Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ K * r at Hsum
    nlinarith only [H, Hsum]
  have hsmall : 4 * C₀ * K ^ 2 * (Y ρ 1 + r * (Y ρ 2 * Y ρ 3)) ≤ 1 / (2 * D) := by
    apply le_trans (mul_le_mul_of_nonneg_left hsum' (by positivity))
    apply (le_div_iff₀ (by positivity : 0 < 2 * D)).mpr
    have H := (le_div_iff₀ (by positivity : 0 < 8 * C₀ * K ^ 3 * D)).mp
      (hr.2.trans (min_le_right _ _))
    nlinarith only [H]
  obtain ⟨T, hT, hfirst, Hτ⟩ := exists_partialCore_radial_cone ⟨hr.1, hr1⟩ hK hD hZ hY
    hk hy hV ((le_max_right _ _).trans hk6) hz hklo hkhi hdk hdklo hdU hdp hdz hsmall
  exact ⟨hdom, fun _ ht => restartFastProjectiveEntry_flow hrad.le hs hA ht,
    T, hT, hfirst, restartFastProjectiveEntry_firstReturn hrad.le hs hA hfirst, Hτ⟩

end BianchiIX

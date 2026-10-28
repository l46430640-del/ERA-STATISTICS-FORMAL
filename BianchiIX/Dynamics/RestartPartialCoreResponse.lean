import BianchiIX.Dynamics.PartialCoreRadialCurve
import BianchiIX.Dynamics.RestartPartialCoreRadialData

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem restartFastProjectiveEntry_flow {h s θ ζ ρ t : ℝ}
    (hrad : 0 ≤ restartSectionRadicand h (restartRadialCurve θ ζ ρ))
    (hs : 0 ≤ s) (hA : 0 < restartFastProjectionHeight h s θ ζ ρ) (ht : 0 ≤ t) :
    projectiveOriginalFlow (restartFastProjectiveEntry h s θ ζ ρ) 0 t =
      toProjectiveState (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 (s + t)) := by
  have hc := restartSectionChart_constraint hrad
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hbase := fromProjectiveState_toProjectiveState hA.ne'
    ((normalizedMaxCurve_constraint hdom).trans hc)
  have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hdom)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hs))
  simp only [zero_add] at H
  change toProjectiveState (normalizedMaxCurve
    (fromProjectiveState (toProjectiveState (normalizedMaxCurve _ 0 s))) 0 t) = _
  rw [hbase, H, add_comm t s]

theorem restartFastProjectiveEntry_firstReturn {h s θ ζ ρ T : ℝ}
    (hrad : 0 ≤ restartSectionRadicand h (restartRadialCurve θ ζ ρ))
    (hs : 0 ≤ s) (hA : 0 < restartFastProjectionHeight h s θ ζ ρ)
    (hfirst : IsLeast {t | 0 < t ∧
      projectiveOriginalFlow (restartFastProjectiveEntry h s θ ζ ρ) 0 t 2 = 1} T) :
    IsLeast {t | s < t ∧ toProjectiveState
      (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 t) 2 = 1} (s + T) := by
  have HF := restartFastProjectiveEntry_flow hrad hs hA hfirst.1.1.le
  refine ⟨⟨by linarith only [hfirst.1.1], ?_⟩, ?_⟩
  · rw [← HF]
    exact hfirst.1.2
  intro t ht
  have hsub : 0 < t - s := sub_pos.mpr ht.1
  have Hflow := restartFastProjectiveEntry_flow hrad hs hA hsub.le
  rw [add_sub_cancel] at Hflow
  have Hleast := hfirst.2 ⟨hsub, by rw [Hflow]; exact ht.2⟩
  linarith only [Hleast]

/-- All entrance hypotheses of the ordinary radial response follow from the exact fast flow. -/
theorem exists_restartPartialCore_radial_response :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 1 ≤ K ∧ ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let k := restartFastCoreRadius h s θ ζ
            let U := fun a => Y a 1
            let p := fun a => Y a 2 * Y a 3
            let C := 4096 * coreVariationBound
            s ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            (∀ t : ℝ, 0 ≤ t → projectiveOriginalFlow (Y ρ) 0 t = toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 (s + t))) ∧
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
              IsLeast {t | s < t ∧ toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 t) 2 = 1} (s + T) ∧
              ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                (∀ᶠ y in 𝓝 (Y ρ),
                  IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
                    projectiveOriginalFlow y 0 t 2 = 1} (τ y) ∧
                  ∀ t ∈ Icc 0 (τ y), t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
                    0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0) ∧
                let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
                  (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
                DifferentiableAt ℝ f ρ ∧ k ρ / 2 ≤ f ρ ∧ f ρ ≤ 2 * k ρ ∧
                DifferentiableAt ℝ (fun a => f a - k a) ρ ∧
                |f ρ - k ρ| ≤ 16 * K * (U ρ + r * (p ρ) ^ 2) ∧
                |deriv (fun a => f a - k a) ρ| ≤ 4 * C * K ^ 2 * (U ρ + r * p ρ) / r ^ 2 ∧
                DifferentiableAt ℝ (fun a => 2 / f a - 2 / k a) ρ ∧
                |2 / f ρ - 2 / k ρ| ≤ 32 * K ^ 3 * r ^ 2 * (U ρ + r * (p ρ) ^ 2) ∧
                |deriv (fun a => 2 / f a - 2 / k a) ρ| ≤
                  (8 * C * K ^ 4 + 64 * K ^ 5) * (U ρ + r * p ρ) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartPartialCore_radial_data
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL
  obtain ⟨K, hK, _, _, HK⟩ := HH h hh L hL
  refine ⟨K, hK, ?_⟩
  intro q P hq hP
  obtain ⟨rstar, hrstar, HR⟩ := HK q P hq hP
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  obtain ⟨hr1, hs, hrad, hdom, hA, hY, _, hk6, _, hregion, hV, _, hklo, hkhi, hdk, _, hdU, hdp, hdz⟩ :=
    HR r hr θ ζ hθ hζ ρ hρ
  obtain ⟨T, hT, hfirst, Hτ⟩ := exists_partialCore_radial_curve_response ⟨hr.1, hr1⟩ hK hY
    ((le_max_left _ _).trans hk6) hregion hV hklo hkhi hdk hdU hdp hdz
  exact ⟨hdom, fun _ ht => restartFastProjectiveEntry_flow hrad.le hs hA ht,
    T, hT, hfirst, restartFastProjectiveEntry_firstReturn hrad.le hs hA hfirst, Hτ⟩

end BianchiIX

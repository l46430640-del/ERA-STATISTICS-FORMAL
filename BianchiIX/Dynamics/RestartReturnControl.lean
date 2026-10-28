import BianchiIX.Dynamics.RestartReturnMap
import BianchiIX.Dynamics.RestartOutputAmplitude
import BianchiIX.Dynamics.RestartOutputPhase

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- One fixed actual return map satisfies E.13 and E.14 simultaneously on the whole annulus. -/
theorem exists_restartReturn_control :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let y := restartFastProjectiveEntry h s θ ζ ρ
            let p := restartReturnParameters h s θ ζ ρ
            let G := restartReturnState h s θ ζ ρ
            let f := restartReturnPhase h s θ ζ
            let F := fun a => restartReferenceRadialPhase h (restartRadialCurve θ ζ a)
            IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} (partialCoreReturnTime y) ∧
              ContDiffAt ℝ 2 partialCoreReturnTime y ∧ connectionReturnValid p ∧
              1 / (2 * (8 * (L + 1) + 1) * r) ≤ G 0 ∧ G 0 ≤ 64 / r ∧
              0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 4096 * (8 * (L + 1)) * ζ / r ^ 3 ∧
              coreRadiusEntry G = projectiveReflection (toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0
                  (restartReturnTime h s θ ζ ρ))) ∧
              DifferentiableAt ℝ f ρ ∧ |f ρ - F ρ| ≤ C * r ^ 2 ∧
              |deriv f ρ - deriv F ρ| ≤ C * r ∧
              1 / (8 * Real.sqrt 3) ≤ deriv f ρ ∧ deriv f ρ ≤ C := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartConnection_output_phase
  obtain ⟨hA, hhA, HA⟩ := exists_restartConnection_output_bounds
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  refine ⟨min hE (min hA hV), lt_min hhE (lt_min hhA hhV), ?_⟩
  intro h hh L hL
  obtain ⟨C, hC, HCE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rE, hrE, HRE⟩ := HCE q P hq hP
  obtain ⟨rA, hrA, HRA⟩ := HA h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨rV, hrV, HRV⟩ := HV h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩ L hL q hq2
  refine ⟨min rE (min rA (min rV 1)), lt_min hrE (lt_min hrA (lt_min hrV (by norm_num))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrA' := hr.2.trans (min_le_right _ _)
  have hrV' := hrA'.trans (min_le_right _ _)
  have hr1 := hrV'.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1.le, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1 (by linarith only [hP] : (2 : ℝ) ≤ P)
  obtain ⟨_, hY, _⟩ := HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨T, _, hfirst, τ, hτ, hcτ, hnear, _, _, hdf, hval, hder, hlo, hhi⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨S, _, hfirstS, hvalid, hradlo, hradhi, hu, hw, hsum, horbit⟩ :=
    HRA r ⟨hr.1, hrA'.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hvalid hradlo hradhi hu hw hsum horbit
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  have heqTime := partialCoreReturnTime_eventuallyEq hnear
  have ht : partialCoreReturnTime (Y ρ) = T := heqTime.self_of_nhds.trans hτ
  have hp : restartReturnParameters h s θ ζ ρ =
      coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 T)) := by
    change coreExitConnectionParameters (toCoreAngleState
      (projectiveOriginalFlow (Y ρ) 0 (partialCoreReturnTime (Y ρ)))) = _
    rw [ht]
  have hg : restartReturnState h s θ ζ ρ =
      connectionReturnPhysicalState (coreExitConnectionParameters
        (toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 T))) := congrArg connectionReturnPhysicalState hp
  have heq := restartReturnParameters_eventuallyEq hY.continuousAt hnear
  have heqPhase : restartReturnPhase h s θ ζ =ᶠ[𝓝 ρ] fun a =>
      let out := projectiveOriginalFlow (Y a) 0 (τ (Y a))
      2 / connectionReturnPhysicalState
        (coreExitConnectionParameters ![coreRadius (out 0) (out 2), out 1, out 3]) 0 :=
    heq.mono fun _ ha => congrArg (fun p => 2 / connectionReturnPhysicalState p 0) ha
  dsimp only [s, Y] at ht hp hg heqPhase
  refine ⟨?_, hcτ.congr_of_eventuallyEq heqTime, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hdf.congr_of_eventuallyEq heqPhase, ?_, ?_, ?_, ?_⟩
  · simpa only [ht] using hfirst
  · simpa only [hp] using hvalid
  · simpa only [hg] using hradlo
  · simpa only [hg] using hradhi
  · simpa only [hg] using hu
  · simpa only [hg] using hw
  · simpa only [hg] using hsum
  · simpa only [restartReturnTime, ht, hp, hg] using horbit
  · simpa only [heqPhase.self_of_nhds] using hval
  · simpa only [heqPhase.deriv_eq] using hder
  · simpa only [heqPhase.deriv_eq] using hlo
  · simpa only [heqPhase.deriv_eq] using hhi

end BianchiIX

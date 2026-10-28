import BianchiIX.Dynamics.ShearRestartReturnMap
import BianchiIX.Dynamics.ShearRestartOutputAmplitude
import BianchiIX.Dynamics.ShearRestartOutputPhase

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- One fixed positive-shear map satisfies all E.36 value and phase bounds wherever the fast entry has V ≥ 1. -/
theorem exists_restartShearReturn_control :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∃ C > (0 : ℝ), ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
              let p := restartShearReturnParameters h s n₂ n₃ ρ
              let G := restartShearReturnState h s n₂ n₃ ρ
              let f := restartShearReturnPhase h s n₂ n₃
              let F := fun b => restartReferenceRadialPhase h (restartShearCurve 1 n₂ n₃ b)
              1 ≤ y 2 →
              IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} (partialCoreDownwardReturnTime y) ∧
              ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ connectionReturnValid p ∧
              s < restartShearReturnTime h s n₂ n₃ ρ ∧
              1 / (64 * a) ≤ G 0 ∧ G 0 ≤ 64 / a ∧
              0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * n₂ * n₃ / a ^ 4 ∧
              coreRadiusEntry G = projectiveReflection (toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0
                  (restartShearReturnTime h s n₂ n₃ ρ))) ∧
              DifferentiableAt ℝ f ρ ∧ |f ρ - F ρ| ≤ C * a ^ 2 ∧
              |deriv f ρ - deriv F ρ| ≤ C * a ∧
              1 / (8 * Real.sqrt 3) ≤ deriv f ρ ∧ deriv f ρ ≤ C := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearConnection_output_phase
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearConnection_output_bounds
  obtain ⟨hD, hhD, K, _, HD⟩ := exists_restartShearPartialCore_radial_data
  refine ⟨min hE (min hA hD), lt_min hhE (lt_min hhA hhD), ?_⟩
  intro h hh
  obtain ⟨C, hC, HCE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  have hhAD := hh.2.trans (min_le_right _ _)
  obtain ⟨aE, haE, HaE⟩ := HCE q P hq hP
  obtain ⟨aA, haA, HaA⟩ := HA h ⟨hh.1, hhAD.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aD, haD, HaD⟩ := HD h ⟨hh.1, hhAD.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aE (min aA aD), lt_min haE (lt_min haA haD), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s y p G f F hv
  have haAD := ha.2.trans (min_le_right _ _)
  obtain ⟨_, _, _, _, _, hY, hk, hy, hvcase, _⟩ :=
    HaD a ⟨ha.1, haAD.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ hv
  obtain ⟨_, _, _, _, hdf, hval, hder, hlo, hhi⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, hvalid, hradlo, hradhi, hu, hw, hsum, horbit⟩ :=
    HaA a ⟨ha.1, haAD.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  have Hcore := partialCoreDownwardReturn_regular hk hy rfl hvcase
  have heq := restartShearReturnParameters_eventuallyEq hY.continuousAt hk hy rfl hvcase
  have heqPhase : f =ᶠ[𝓝 ρ] fun b =>
      let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃ b
      let out := projectiveOriginalFlow Y 0 (partialCoreDownwardReturnTime Y)
      2 / connectionReturnPhysicalState
        (coreExitConnectionParameters ![coreRadius (out 0) (out 2), out 1, out 3]) 0 :=
    heq.mono fun _ hb => congrArg (fun p => 2 / connectionReturnPhysicalState p 0) hb
  have hT : 0 < partialCoreDownwardReturnTime y := Hcore.1.1.1
  have htc : 0 < connectionReturnTime p := hvalid.1.1.1
  refine ⟨Hcore.1, Hcore.2.1, hvalid, ?_, hradlo, hradhi, hu, hw, hsum, horbit,
    hdf.congr_of_eventuallyEq heqPhase, ?_, ?_, ?_, ?_⟩
  · change s < s + partialCoreDownwardReturnTime y + connectionReturnTime p
    linarith only [hT, htc]
  · rw [heqPhase.self_of_nhds]
    exact hval
  · rw [heqPhase.deriv_eq]
    exact hder
  · rw [heqPhase.deriv_eq]
    exact hlo
  · rw [heqPhase.deriv_eq]
    exact hhi

end BianchiIX

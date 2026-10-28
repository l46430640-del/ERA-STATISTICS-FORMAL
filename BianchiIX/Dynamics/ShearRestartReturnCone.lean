import BianchiIX.Dynamics.ShearRestartReturnRegularity
import BianchiIX.Dynamics.ShearRestartConnectionCurve

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The same fixed shear restart preserves the square-root cone, with ordinary derivatives at V = 1. -/
theorem exists_restartShearReturn_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let G := restartShearReturnState h s n₂ n₃
            let k := fun b => G b 0
            1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 →
            ContDiffAt ℝ 2 G ρ ∧ deriv k ρ < 0 ∧
            |deriv (fun b => G b 1) ρ| ≤ Real.sqrt (G ρ 1) * |deriv k ρ| ∧
            |deriv (fun b => G b 2) ρ| ≤ Real.sqrt (G ρ 2) * |deriv k ρ| := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearReturn_regular
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearConnection_radial_curve
  obtain ⟨hD, hhD, K, _, HD⟩ := exists_restartShearPartialCore_radial_data
  refine ⟨min hR (min hC hD), lt_min hhR (lt_min hhC hhD), ?_⟩
  intro h hh q P hq hP
  have hhCD := hh.2.trans (min_le_right _ _)
  obtain ⟨aR, haR, HaR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hhCD.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aD, haD, HaD⟩ := HD h ⟨hh.1, hhCD.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aR (min aC aD), lt_min haR (lt_min haC haD), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s G k hv
  have haCD := ha.2.trans (min_le_right _ _)
  obtain ⟨_, _, hcG, _⟩ :=
    HaR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, _, _, _, hneg, _, _, hcone, _⟩ :=
    HaC a ⟨ha.1, haCD.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, _, _, hY, hk, hy, hvcase, _⟩ :=
    HaD a ⟨ha.1, haCD.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ hv
  let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
  let out := fun b => projectiveOriginalFlow (Y b) 0 (partialCoreDownwardReturnTime (Y b))
  let p := fun b => coreExitConnectionParameters ![coreRadius (out b 0) (out b 2), out b 1, out b 3]
  have heq := restartShearReturnParameters_eventuallyEq hY.continuousAt hk hy rfl hvcase
  have heqG : G =ᶠ[𝓝 ρ] fun b => connectionReturnPhysicalState (p b) :=
    heq.mono fun _ hb => congrArg connectionReturnPhysicalState hb
  have heqi (i : Fin 3) : (fun b => G b i) =ᶠ[𝓝 ρ] fun b => connectionReturnPhysicalState (p b) i :=
    heqG.mono fun _ hb => congrArg (fun z => z i) hb
  have hv1 : G ρ 1 = connectionReturnPhysicalState (p ρ) 1 := (heqi 1).self_of_nhds
  have hv2 : G ρ 2 = connectionReturnPhysicalState (p ρ) 2 := (heqi 2).self_of_nhds
  refine ⟨hcG, ?_, ?_, ?_⟩
  · change deriv (fun b => G b 0) ρ < 0
    rw [(heqi 0).deriv_eq]
    exact hneg.2
  · change |deriv (fun b => G b 1) ρ| ≤ Real.sqrt (G ρ 1) * |deriv (fun b => G b 0) ρ|
    rw [(heqi 1).deriv_eq, hv1, (heqi 0).deriv_eq]
    exact hcone.1
  · change |deriv (fun b => G b 2) ρ| ≤ Real.sqrt (G ρ 2) * |deriv (fun b => G b 0) ρ|
    rw [(heqi 2).deriv_eq, hv2, (heqi 0).deriv_eq]
    exact hcone.2

end BianchiIX

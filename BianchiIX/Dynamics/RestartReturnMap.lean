import BianchiIX.Dynamics.PartialCoreReturn
import BianchiIX.Dynamics.CoreConnectionChart
import BianchiIX.Dynamics.ConnectionPhysicalReturn
import BianchiIX.Dynamics.RestartFastProjectiveEntry

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartReturnParameters (h s θ ζ ρ : ℝ) : ConnectionParameters :=
  coreExitConnectionParameters (partialCoreReturnState (restartFastProjectiveEntry h s θ ζ ρ))

def restartReturnState (h s θ ζ ρ : ℝ) : CoreAngleState :=
  connectionReturnPhysicalState (restartReturnParameters h s θ ζ ρ)

def restartReturnPhase (h s θ ζ ρ : ℝ) : ℝ := 2 / restartReturnState h s θ ζ ρ 0

def restartReturnTime (h s θ ζ ρ : ℝ) : ℝ :=
  s + partialCoreReturnTime (restartFastProjectiveEntry h s θ ζ ρ) +
    connectionReturnTime (restartReturnParameters h s θ ζ ρ)

/-- Radial estimates for any ordinary event germ apply to the fixed restart map. -/
theorem restartReturnParameters_eventuallyEq {h s θ ζ ρ : ℝ} {τ : ProjectiveState → ℝ}
    (hY : ContinuousAt (restartFastProjectiveEntry h s θ ζ) ρ)
    (hτ : ∀ᶠ y in 𝓝 (restartFastProjectiveEntry h s θ ζ ρ), IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) :
    restartReturnParameters h s θ ζ =ᶠ[𝓝 ρ] fun a =>
      let out := projectiveOriginalFlow (restartFastProjectiveEntry h s θ ζ a) 0
        (τ (restartFastProjectiveEntry h s θ ζ a))
      coreExitConnectionParameters ![coreRadius (out 0) (out 2), out 1, out 3] := by
  filter_upwards [hY.tendsto.eventually (partialCoreReturnState_eventuallyEq hτ)] with a ha
  exact congrArg coreExitConnectionParameters ha

end BianchiIX

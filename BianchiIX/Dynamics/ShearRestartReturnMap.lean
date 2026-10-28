import BianchiIX.Dynamics.PartialCoreDownwardConnection
import BianchiIX.Dynamics.ConnectionPhysicalReturn
import BianchiIX.Dynamics.ShearRestartProjectiveEntry

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- The positive-shear restart uses one fixed downward event, also across the incoming boundary. -/
def restartShearReturnParameters (h s n₂ n₃ ρ : ℝ) : ConnectionParameters :=
  coreExitConnectionParameters (partialCoreDownwardReturnState (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ))

def restartShearReturnState (h s n₂ n₃ ρ : ℝ) : CoreAngleState :=
  connectionReturnPhysicalState (restartShearReturnParameters h s n₂ n₃ ρ)

def restartShearReturnPhase (h s n₂ n₃ ρ : ℝ) : ℝ := 2 / restartShearReturnState h s n₂ n₃ ρ 0

def restartShearReturnTime (h s n₂ n₃ ρ : ℝ) : ℝ :=
  s + partialCoreDownwardReturnTime (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ) +
    connectionReturnTime (restartShearReturnParameters h s n₂ n₃ ρ)

/-- Both physical descriptions of the exit define the same ordinary parameter germ. -/
theorem restartShearReturnParameters_eventuallyEq {h s n₂ n₃ ρ k : ℝ}
    (hY : ContinuousAt (restartFastShearProjectiveEntry h s 1 n₂ n₃) ρ)
    (hk : 6 ≤ k) (hy : coreRegion k (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ))
    (hR : coreRadius (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 0)
      (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2) = k)
    (hV : 1 < restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 ∨
      (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 = 1 ∧ 1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 0)) :
    restartShearReturnParameters h s n₂ n₃ =ᶠ[𝓝 ρ] fun a =>
      let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ a
      let out := projectiveOriginalFlow y 0 (partialCoreDownwardReturnTime y)
      coreExitConnectionParameters ![coreRadius (out 0) (out 2), out 1, out 3] := by
  filter_upwards [hY.tendsto.eventually
    (partialCoreDownwardReturn_connectionParameters_eventuallyEq hk hy hR hV)] with a ha
  exact ha.symm

end BianchiIX

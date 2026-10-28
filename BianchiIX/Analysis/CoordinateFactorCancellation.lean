import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- Differentiation recovers a smooth factor even where its coordinate multiplier vanishes. -/
theorem coordinate_factor_eq_of_eventuallyEq {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} (i : Fin n) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x)
    (H : (fun y => y i * f y) =ᶠ[𝓝 x] (fun y => y i * g y)) : f x = g x := by
  by_cases hx : x i = 0
  · have HF := (hasFDerivAt_apply (𝕜 := ℝ) i x).mul hf.hasFDerivAt
    have HG := (hasFDerivAt_apply (𝕜 := ℝ) i x).mul hg.hasFDerivAt
    have HE := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i 1))
      ((HF.congr_of_eventuallyEq H.symm).unique HG)
    simpa [hx] using HE
  · exact mul_left_cancel₀ hx H.self_of_nhds

theorem coordinate_factor_eventuallyEq {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} (i : Fin n) (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x)
    (H : (fun y => y i * f y) =ᶠ[𝓝 x] (fun y => y i * g y)) : f =ᶠ[𝓝 x] g := by
  filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num),
    eventually_eventually_nhds.mpr H] with y hyf hyg hy
  exact coordinate_factor_eq_of_eventuallyEq i (hyf.differentiableAt (by norm_num))
    (hyg.differentiableAt (by norm_num)) hy

end BianchiIX

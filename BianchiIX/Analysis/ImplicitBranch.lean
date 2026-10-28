import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- A continuous transverse branch inherits the regularity of its defining equation. -/
theorem contDiffAt_scalar_event_branch {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Q : E × ℝ → ℝ} {x : E} {t a : ℝ}
    {n : WithTop ℕ∞} (hn : n ≠ 0) (hQ : ContDiffAt ℝ n Q (x, t))
    (hd : HasDerivAt (fun u => Q (x, u)) a t) (ha : a ≠ 0)
    {τ : E → ℝ} (hτ : τ x = t) (hcτ : ContinuousAt τ x)
    (hhit : ∀ᶠ y in 𝓝 x, Q (y, τ y) = Q (x, t)) : ContDiffAt ℝ n τ x := by
  have htime : (fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ) =
      a • ContinuousLinearMap.id ℝ ℝ := by
    have H := ((hQ.differentiableAt hn).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_right x t)).unique hd.hasFDerivAt
    rw [H]
    ext
    simp [mul_comm]
  have hinv : ((fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    rw [htime]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := a⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [ha]
    · ext
      simp [ha]
  have hgraph : Tendsto (fun y => (y, τ y)) (𝓝 x) (𝓝 (x, t)) := by
    simpa only [hτ, id_eq] using (continuousAt_id.prodMk hcτ).tendsto
  have heq : τ =ᶠ[𝓝 x] hQ.implicitFunction hn hinv := by
    filter_upwards [hhit,
      hgraph.eventually (hQ.eventually_apply_eq_iff_implicitFunction hn hinv)] with y hy hiff
    exact (hiff.mp hy).symm
  exact (hQ.contDiffAt_implicitFunction hn hinv).congr_of_eventuallyEq heq

theorem contDiffAt_scalar_event_branch_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Q : E × ℝ → ℝ} {x : E} {t a : ℝ}
    (hQ : ContDiffAt ℝ 2 Q (x, t))
    (hd : HasDerivAt (fun u => Q (x, u)) a t) (ha : a ≠ 0)
    {τ : E → ℝ} (hτ : τ x = t) (hcτ : ContinuousAt τ x)
    (hhit : ∀ᶠ y in 𝓝 x, Q (y, τ y) = Q (x, t)) : ContDiffAt ℝ 2 τ x :=
  contDiffAt_scalar_event_branch (by norm_num) hQ hd ha hτ hcτ hhit

end BianchiIX

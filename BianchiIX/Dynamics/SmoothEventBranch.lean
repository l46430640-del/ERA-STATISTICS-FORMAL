import BianchiIX.Analysis.ImplicitBranch
import BianchiIX.Dynamics.Events
import BianchiIX.Dynamics.FlowSmoothRegularity

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology ContDiff

/-- A continuous transverse event along a smooth initial chart inherits the smooth exact flow. -/
theorem contDiffAt_normalized_event_branch {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {e : E → NormalizedState} {x : E}
    {τ : E → ℝ} {g : NormalizedState → ℝ} {t₀ : ℝ}
    (he : ContDiffAt ℝ ∞ e x) (ht : τ x ∈ normalizedMaxDomain (e x) t₀)
    (hg : ContDiffAt ℝ ∞ g (normalizedMaxCurve (e x) t₀ (τ x)))
    (htrans : normalizedEventRate g (e x) t₀ (τ x) ≠ 0) (hτ : ContinuousAt τ x)
    (hhit : ∀ᶠ y in 𝓝 x, g (normalizedMaxCurve (e y) t₀ (τ y)) =
      g (normalizedMaxCurve (e x) t₀ (τ x))) :
    ContDiffAt ℝ ∞ τ x ∧
      ContDiffAt ℝ ∞ (fun y => normalizedMaxCurve (e y) t₀ (τ y)) x := by
  let F : E × ℝ → NormalizedState := fun z => normalizedMaxCurve (e z.1) t₀ z.2
  let Q : E × ℝ → ℝ := fun z => g (F z)
  have hF : ContDiffAt ℝ ∞ F (x, τ x) :=
    (contDiffAt_normalizedMaxCurve_smooth ht).comp (x, τ x)
      ((he.comp (x, τ x) contDiffAt_fst).prodMk contDiffAt_snd)
  have hQ : ContDiffAt ℝ ∞ Q (x, τ x) := hg.comp (x, τ x) hF
  have hd : HasDerivAt (fun t => Q (x, t)) (normalizedEventRate g (e x) t₀ (τ x)) (τ x) :=
    (hg.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (τ x)
      (hasDerivAt_normalizedMaxCurve ht)
  have hτsmooth := contDiffAt_scalar_event_branch (by simp) hQ hd htrans rfl hτ hhit
  exact ⟨hτsmooth, hF.comp x (g := F) (f := fun y => (y, τ y))
    (contDiffAt_id.prodMk hτsmooth)⟩

end BianchiIX

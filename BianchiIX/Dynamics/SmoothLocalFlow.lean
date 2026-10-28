import BianchiIX.Dynamics.InitialDerivative
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

/-- Joint differentiability in initial state and time, on an actual local domain of the maximal flow. -/
theorem exists_normalizedMaxCurve_local_contDiff (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      (∀ x ∈ ball x₀ r, Ioo (t₀ - ε) (t₀ + ε) ⊆ normalizedMaxDomain x t₀) ∧
      ContDiffOn ℝ 1 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
        (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨r, hr, ε, hε, J, hc, hcJ, hJ⟩ := exists_normalizedMaxCurve_local_derivative x₀ t₀
  let U := ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)
  let V : NormalizedState × ℝ → ℝ →L[ℝ] NormalizedState := fun z =>
    (ContinuousLinearMap.id ℝ ℝ).smulRight (normalizedField (normalizedMaxCurve z.1 t₀ z.2))
  have ho : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hcV : ContinuousOn V U :=
    (ContinuousLinearMap.smulRightL ℝ ℝ NormalizedState (ContinuousLinearMap.id ℝ ℝ)).continuous.comp_continuousOn
      ((contDiff_normalizedField 1).continuous.comp_continuousOn hc)
  have hd (z : NormalizedState × ℝ) (hz : z ∈ U) :
      HasStrictFDerivAt (fun w : NormalizedState × ℝ => normalizedMaxCurve w.1 t₀ w.2)
        ((J z).coprod (V z)) z := by
    apply hasStrictFDerivAt_uncurry_coprod
      (f := fun x t => normalizedMaxCurve x t₀ t)
      (f₁ := fun x t => J (x, t)) (f₂ := fun x t => V (x, t))
    · filter_upwards [ho.mem_nhds hz] with w hw
      exact ((hJ w.1 hw.1).2.2 w.2 hw.2).1
    · filter_upwards [ho.mem_nhds hz] with w hw
      exact (hasDerivAt_normalizedMaxCurve ((hJ w.1 hw.1).1 hw.2)).hasFDerivAt
    · exact hcJ.continuousAt (ho.mem_nhds hz)
    · exact hcV.continuousAt (ho.mem_nhds hz)
  refine ⟨r, hr, ε, hε, fun x hx => (hJ x hx).1, ?_⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn ho.uniqueDiffOn]
  exact ⟨by simp, fun z => (J z).coprod (V z),
    contDiffOn_zero.mpr (hcJ.continuousLinearMapCoprod hcV),
    fun z hz => (hd z hz).hasFDerivAt.hasFDerivWithinAt⟩

end BianchiIX

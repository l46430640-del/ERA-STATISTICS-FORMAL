import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section

namespace BianchiIX

open Filter Set
open scoped Topology

/-- Boundary value asymptotics control interior secants without differentiating a remainder. -/
theorem tendsto_interior_secant_of_boundary_slope {f : ℝ → ℝ} {a c : ℝ}
    (hf : Tendsto (fun t => (f t - a) / t) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun t => (f (2 * t) - f t) / t) (𝓝[>] 0) (𝓝 c) := by
  have H0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have HT : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using H0.const_mul (2 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < 2 * t
      exact mul_pos (by norm_num) ht
  have H := ((hf.comp HT).const_mul 2).sub hf
  rw [show 2 * c - c = c by ring] at H
  apply H.congr'
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only [Function.comp_def]
    simp only [div_mul_eq_div_div]
    ring)

/-- A nonzero boundary slope forces large derivatives at strictly positive interior points. -/
theorem exists_derivative_gt_of_boundary_slope {f f' : ℝ → ℝ} {a c B r : ℝ}
    (hf : Tendsto (fun t => (f t - a) / t) (𝓝[>] 0) (𝓝 c))
    (hr : 0 < r) (hB : B < c)
    (hd : ∀ t ∈ Ioo 0 r, HasDerivAt f (f' t) t) :
    ∃ s ∈ Ioo 0 r, B < f' s := by
  have HS := (tendsto_interior_secant_of_boundary_slope hf).eventually (lt_mem_nhds hB)
  have Ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ t < r / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
        (gt_mem_nhds (by positivity : (0 : ℝ) < r / 2))] with t ht htr
    exact ⟨ht, htr⟩
  obtain ⟨t, ht, hs⟩ := (Ht.and HS).exists
  have hI : Icc t (2 * t) ⊆ Ioo 0 r := by
    intro x hx
    constructor <;> linarith only [ht.1, ht.2, hx.1, hx.2]
  have HC : ContinuousOn f (Icc t (2 * t)) :=
    fun x hx => (hd x (hI hx)).continuousAt.continuousWithinAt
  obtain ⟨s, hst, Heq⟩ := exists_hasDerivAt_eq_slope f f'
    (by linarith only [ht.1] : t < 2 * t) HC
    (fun x hx => hd x (hI ⟨hx.1.le, hx.2.le⟩))
  refine ⟨s, hI ⟨hst.1.le, hst.2.le⟩, ?_⟩
  rwa [Heq, show 2 * t - t = t by ring]

end BianchiIX

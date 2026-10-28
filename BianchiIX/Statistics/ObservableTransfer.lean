import BianchiIX.Statistics.TreeOrbits
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Continuous observables have the same time averages on asymptotic phase sequences. -/

open Set Filter
open scoped Topology

namespace BianchiIX

noncomputable def timeAverage (u : ℕ → ℝ) (n : ℕ) : ℝ := (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u j

theorem timeAverage_sub (u v : ℕ → ℝ) (n : ℕ) :
    timeAverage (fun j => u j - v j) n = timeAverage u n - timeAverage v n := by
  simp only [timeAverage, Finset.sum_sub_distrib, mul_sub]

theorem timeAverage_mono {u v : ℕ → ℝ} (h : ∀ j, u j ≤ v j) (n : ℕ) :
    timeAverage u n ≤ timeAverage v n :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => h j)) (by positivity)

theorem timeAverage_tendsto_atTop_of_truncations {u l : ℕ → ℝ}
    (htrunc : ∀ R : ℕ, Tendsto (timeAverage (fun j => min (u j) (R : ℝ))) atTop (𝓝 (l R)))
    (hl : Tendsto l atTop atTop) : Tendsto (timeAverage u) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨R, hR⟩ := ((tendsto_atTop.mp hl) (b + 1)).exists
  have hb : b < l R := by linarith
  filter_upwards [(tendsto_order.mp (htrunc R)).1 b hb] with n hn
  exact hn.le.trans (timeAverage_mono (fun j => min_le_left (u j) (R : ℝ)) n)

theorem continuous_observable_difference {x y : ℕ → ℝ} {f : ℝ → ℝ}
    {S : Set ℝ} (hS : IsCompact S) (hf : ContinuousOn f S)
    (hx : ∀ n, x n ∈ S) (hy : ∀ n, y n ∈ S)
    (hxy : Tendsto (fun n => x n - y n) atTop (𝓝 0)) :
    Tendsto (fun n => f (x n) - f (y n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hS.uniformContinuousOn_of_continuous hf) ε hε
  filter_upwards [Metric.tendsto_nhds.mp hxy δ hδ] with n hn
  have hdist : dist (x n) (y n) < δ := by simpa only [Real.dist_eq, sub_zero] using hn
  simpa only [Real.dist_eq, sub_zero] using hclose (x n) (hx n) (y n) (hy n) hdist

theorem timeAverage_difference_tendsto {u v : ℕ → ℝ}
    (h : Tendsto (fun n => u n - v n) atTop (𝓝 0)) :
    Tendsto (fun n => timeAverage u n - timeAverage v n) atTop (𝓝 0) := by
  simpa only [timeAverage, Finset.sum_sub_distrib, mul_sub] using h.cesaro

theorem continuous_timeAverage_transfer {x y : ℕ → ℝ} {f : ℝ → ℝ} {l : ℝ}
    {S : Set ℝ} (hS : IsCompact S) (hf : ContinuousOn f S)
    (hx : ∀ n, x n ∈ S) (hy : ∀ n, y n ∈ S)
    (hxy : Tendsto (fun n => x n - y n) atTop (𝓝 0))
    (hl : Tendsto (timeAverage (fun n => f (y n))) atTop (𝓝 l)) :
    Tendsto (timeAverage (fun n => f (x n))) atTop (𝓝 l) := by
  have hdiff := timeAverage_difference_tendsto (continuous_observable_difference hS hf hx hy hxy)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hl

namespace InverseBranchTree.BranchEstimates

variable {T : InverseBranchTree} {d e : ℕ → ℝ} (E : T.BranchEstimates d e)

include E

theorem continuous_timeAverage (hd : Tendsto d atTop (𝓝 0)) (x : T.survivors)
    {f : ℝ → ℝ} {l : ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hl : Tendsto (timeAverage (fun n => f (gaussMap^[n] (T.code x)))) atTop (𝓝 l)) :
    Tendsto (timeAverage (fun n => f (T.phase x n))) atTop (𝓝 l) := by
  apply continuous_timeAverage_transfer isCompact_Icc hf (E.phase_mem_unit x) _
    (E.phase_shadowing hd x) hl
  intro n
  simpa only [InverseBranchTree.code, gaussMap_iterate_code] using
    gaussCode_mem_unit (shiftDigits (T.digits x) n)

end InverseBranchTree.BranchEstimates
end BianchiIX

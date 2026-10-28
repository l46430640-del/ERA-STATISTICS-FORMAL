import BianchiIX.Statistics.GaussContinuous
import BianchiIX.Statistics.GaussDigitStatistics

/-! The complete statistical reduction for asymptotic Gauss recurrences. -/

open Set Filter MeasureTheory
open scoped Topology

namespace BianchiIX

/-- All phase and digit statistics asserted by the era-statistics reduction. -/
structure EraStatistics (a : ℕ → ℕ+) (y : ℕ → ℝ) : Prop where
  continuous_average : ∀ f : ℝ → ℝ, ContinuousOn f (Icc (0 : ℝ) 1) →
    Tendsto (timeAverage (fun j => f (y j))) atTop (𝓝 (∫ x, f x ∂gaussMeasure))
  block_frequency : ∀ w : List ℕ, (∀ k ∈ w, 1 ≤ k) →
    Tendsto (timeAverage (fun j => if digitPrefix (shiftDigits a j) w.length = w then 1 else 0))
      atTop (𝓝 (gaussMeasure (gaussCylinder w)).toReal)
  digit_frequency : ∀ k : ℕ+,
    Tendsto (timeAverage (fun j => if (a j : ℕ) = (k : ℕ) then 1 else 0)) atTop
      (𝓝 (Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2))
  tail_frequency : ∀ k : ℕ+,
    Tendsto (timeAverage (fun j => if (k : ℕ) ≤ (a j : ℕ) then 1 else 0)) atTop
      (𝓝 (Real.log (1 + 1 / (k : ℝ)) / Real.log 2))
  truncated_average : ∀ R : ℕ,
    Tendsto (timeAverage (fun j => min (a j : ℝ) (R : ℝ))) atTop
      (𝓝 (Real.log ((R : ℝ) + 1) / Real.log 2))
  divergent_average : Tendsto (timeAverage (fun j => (a j : ℝ))) atTop atTop

theorem eraStatistics_of_typical_code (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    {y : ℕ → ℝ} (hy : ∀ n, y n ∈ Icc (0 : ℝ) 1)
    (herror : Tendsto (inverseError (fun n => (a n : ℕ)) y) atTop (𝓝 0)) :
    EraStatistics a y := by
  refine ⟨?_, fun w hw => gauss_digit_block_frequency a ha w hw,
    gauss_digit_frequency a ha, gauss_digit_tail_frequency a ha,
    gauss_truncated_digit_average a ha, gauss_digit_average_tendsto_atTop a ha⟩
  intro f hf
  apply continuous_timeAverage_transfer isCompact_Icc hf hy _
    (gaussCode_shadowing a hy herror) (gauss_continuous_average a ha hf)
  intro n
  simpa only [gaussMap_iterate_code] using gaussCode_mem_unit (shiftDigits a n)

theorem ae_eraStatistics_of_code_absolutelyContinuous {X : Type*} [MeasurableSpace X]
    (hB : Literature.BirkhoffErgodicInput ℝ) (μ : Measure X) (a : X → ℕ → ℕ+)
    (ha : Measurable a) (y : X → ℕ → ℝ)
    (hunit : ∀ᵐ q ∂μ, ∀ n, y q n ∈ Icc (0 : ℝ) 1)
    (herror : ∀ᵐ q ∂μ, Tendsto (inverseError (fun n => (a q n : ℕ)) (y q)) atTop (𝓝 0))
    (hac : Measure.map (fun q => gaussCode (a q)) μ ≪ volume) :
    ∀ᵐ q ∂μ, EraStatistics (a q) (y q) := by
  have ht := (ae_restrict_iff' measurableSet_Ioo).mp (ae_volume_gaussCylinderTypicalSet hB)
  have hp := ae_of_ae_map (measurable_gaussCode.comp ha).aemeasurable (hac.ae_le ht)
  filter_upwards [hp, hunit, herror] with q hq hu he
  exact eraStatistics_of_typical_code (a q)
    (hq ⟨gaussCode_pos (a q), gaussCode_lt_one (a q)⟩) hu he

namespace InverseBranchTree.BranchEstimates

theorem ae_eraStatistics {T : InverseBranchTree} {d e : ℕ → ℝ}
    (E : T.BranchEstimates d e) (hB : Literature.BirkhoffErgodicInput ℝ) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (hd : Tendsto d atTop (𝓝 0)) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)), EraStatistics (T.digits x) (T.phase x) := by
  filter_upwards [E.ae_code_gaussCylinderTypical hB hbudget] with x hx
  apply eraStatistics_of_typical_code (T.digits x) hx (E.phase_mem_unit x)
  exact squeeze_zero (fun _ => abs_nonneg _) (E.phase_error_le x) hd

end InverseBranchTree.BranchEstimates
end BianchiIX

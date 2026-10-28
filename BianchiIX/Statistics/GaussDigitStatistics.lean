import BianchiIX.Statistics.GaussDigits
import BianchiIX.Statistics.ObservableTransfer

/-! Tail frequencies, truncated means, and divergence on the fixed cylinder-typical set. -/

open Set Filter MeasureTheory
open scoped Topology

namespace BianchiIX

noncomputable section

theorem timeAverage_finsetSum {ι : Type*} (s : Finset ι) (u : ι → ℕ → ℝ) (N : ℕ) :
    timeAverage (fun j => ∑ i ∈ s, u i j) N = ∑ i ∈ s, timeAverage (u i) N := by
  unfold timeAverage
  rw [Finset.sum_comm, Finset.mul_sum]

theorem gauss_digit_frequency (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet) (k : ℕ+) :
    Tendsto (timeAverage (fun j => if (a j : ℕ) = k then 1 else 0)) atTop
      (𝓝 (Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2)) := by
  have h := gauss_digit_block_frequency a ha [(k : ℕ)] (by simpa using Nat.succ_le_of_lt k.pos)
  rw [gaussMeasure_singleton_cylinder] at h
  unfold timeAverage
  simpa [digitPrefix, shiftDigits] using h

theorem gauss_tail_average_integral (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    (k : ℕ+) :
    Tendsto (timeAverage (fun j => gaussTailObservable k (gaussMap^[j] (gaussCode a)))) atTop
      (𝓝 (∫ x, gaussTailObservable k x ∂gaussMeasure)) := by
  induction k using PNat.recOn with
  | one =>
    have heq : (fun j => gaussTailObservable 1 (gaussMap^[j] (gaussCode a))) =
        (fun _ : ℕ => (1 : ℝ)) := by
      funext j
      rw [gaussMap_iterate_code, gaussTailObservable_one_code]
    rw [heq, integral_gaussTailObservable]
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    unfold timeAverage
    convert! hc.cesaro using 1
    norm_num [log_two_pos.ne']
  | succ k ih =>
    have heq : (fun j => gaussTailObservable (k + 1) (gaussMap^[j] (gaussCode a))) =
        (fun j => gaussTailObservable k (gaussMap^[j] (gaussCode a)) -
          gaussCylinderObservable [(k : ℕ)] (gaussMap^[j] (gaussCode a))) := by
      funext j
      simp only [gaussMap_iterate_code, gaussTailObservable_succ_code]
    rw [heq, integral_gaussTailObservable_succ]
    have hc := gaussCylinder_average_of_typical ha [(k : ℕ)]
    change Tendsto (timeAverage (fun j => gaussCylinderObservable [(k : ℕ)]
      (gaussMap^[j] (gaussCode a)))) atTop _ at hc
    change Tendsto (fun N => timeAverage (fun j => gaussTailObservable k (gaussMap^[j] (gaussCode a)) -
      gaussCylinderObservable [(k : ℕ)] (gaussMap^[j] (gaussCode a))) N) atTop _
    simpa only [timeAverage_sub] using ih.sub hc

theorem gauss_digit_tail_frequency (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    (k : ℕ+) :
    Tendsto (timeAverage (fun j => if (k : ℕ) ≤ a j then 1 else 0)) atTop
      (𝓝 (Real.log (1 + 1 / (k : ℝ)) / Real.log 2)) := by
  have h := gauss_tail_average_integral a ha k
  have heq : (fun j => gaussTailObservable k (gaussMap^[j] (gaussCode a))) =
      (fun j => if (k : ℕ) ≤ a j then (1 : ℝ) else 0) := by
    funext j
    rw [gaussMap_iterate_code, gaussTailObservable_code]
    rfl
  rwa [heq, integral_gaussTailObservable] at h

theorem gauss_truncated_digit_average (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    (R : ℕ) :
    Tendsto (timeAverage (fun j => min (a j : ℝ) (R : ℝ))) atTop
      (𝓝 (Real.log ((R : ℝ) + 1) / Real.log 2)) := by
  have heq : (fun j => min (a j : ℝ) (R : ℝ)) =
      (fun j => ∑ i ∈ Finset.range R, if i + 1 ≤ (a j : ℕ) then (1 : ℝ) else 0) :=
    funext (fun j => nat_min_eq_sum_tails (a j) R)
  rw [heq, ← gauss_log_tail_sum R]
  change Tendsto (fun N => timeAverage (fun j => ∑ i ∈ Finset.range R,
    if i + 1 ≤ (a j : ℕ) then (1 : ℝ) else 0) N) atTop _
  simp_rw [timeAverage_finsetSum]
  apply tendsto_finsetSum
  intro i _
  simpa using gauss_digit_tail_frequency a ha ⟨i + 1, by omega⟩

theorem gauss_truncated_integral_tendsto_atTop :
    Tendsto (fun R : ℕ => Real.log ((R : ℝ) + 1) / Real.log 2) atTop atTop := by
  apply Filter.Tendsto.atTop_div_const log_two_pos
  exact Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

theorem gauss_digit_average_tendsto_atTop (a : ℕ → ℕ+)
    (ha : gaussCode a ∈ gaussCylinderTypicalSet) :
    Tendsto (timeAverage (fun j => (a j : ℝ))) atTop atTop :=
  timeAverage_tendsto_atTop_of_truncations (gauss_truncated_digit_average a ha)
    gauss_truncated_integral_tendsto_atTop

namespace InverseBranchTree.BranchEstimates

theorem ae_digit_statistics {T : InverseBranchTree} {d e : ℕ → ℝ}
    (E : T.BranchEstimates d e) (hB : Literature.BirkhoffErgodicInput ℝ) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)),
      (∀ k : ℕ+, Tendsto (timeAverage (fun j => if (T.digits x j : ℕ) = k then 1 else 0)) atTop
        (𝓝 (Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2))) ∧
      (∀ k : ℕ+, Tendsto (timeAverage (fun j => if (k : ℕ) ≤ T.digits x j then 1 else 0)) atTop
        (𝓝 (Real.log (1 + 1 / (k : ℝ)) / Real.log 2))) ∧
      (∀ R : ℕ, Tendsto (timeAverage (fun j => min (T.digits x j : ℝ) (R : ℝ))) atTop
        (𝓝 (Real.log ((R : ℝ) + 1) / Real.log 2))) ∧
      Tendsto (timeAverage (fun j => (T.digits x j : ℝ))) atTop atTop := by
  filter_upwards [E.ae_code_gaussCylinderTypical hB hbudget] with x hx
  exact ⟨gauss_digit_frequency (T.digits x) hx, gauss_digit_tail_frequency (T.digits x) hx,
    gauss_truncated_digit_average (T.digits x) hx, gauss_digit_average_tendsto_atTop (T.digits x) hx⟩

end InverseBranchTree.BranchEstimates
end
end BianchiIX

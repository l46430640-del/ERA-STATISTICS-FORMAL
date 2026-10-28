import BianchiIX.Statistics.GaussDigitStatistics

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- A cylinder-typical code cannot have a finite upper bound on all its digits. -/
theorem not_bounded_digits_of_typical {a : ℕ → ℕ+}
    (ha : gaussCode a ∈ gaussCylinderTypicalSet) : ¬ ∃ N : ℕ, ∀ n, (a n : ℕ) ≤ N := by
  rintro ⟨N, hN⟩
  let k : ℕ+ := ⟨N + 1, by omega⟩
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  have hpos : 0 < Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2 :=
    div_pos (Real.log_pos ((one_lt_div (by positivity)).mpr (by nlinarith))) log_two_pos
  have hzero : (fun j => if (a j : ℕ) = (k : ℕ) then (1 : ℝ) else 0) = fun _ => 0 := by
    funext j
    have hne : (a j : ℕ) ≠ (k : ℕ) := by have := hN j; dsimp [k]; omega
    simp only [if_neg hne]
  have H := gauss_digit_frequency a ha k
  rw [hzero] at H
  have H0 : Tendsto (timeAverage (fun _ : ℕ => (0 : ℝ))) atTop (𝓝 0) := by
    change Tendsto (fun n => timeAverage (fun _ : ℕ => (0 : ℝ)) n) atTop (𝓝 0)
    simp only [timeAverage, Finset.sum_const_zero, mul_zero]
    exact tendsto_const_nhds
  exact (ne_of_gt hpos) (tendsto_nhds_unique H H0)

def gaussBoundedDigits (N : ℕ) : Set ℝ :=
  Ioo 0 1 ∩ {x | ∀ n : ℕ, gaussDigit (gaussMap^[n] x) ≤ N}

theorem measurable_gaussDigit : Measurable gaussDigit :=
  (measurable_const.div measurable_id).nat_floor

theorem measurableSet_gaussBoundedDigits (N : ℕ) : MeasurableSet (gaussBoundedDigits N) := by
  apply measurableSet_Ioo.inter
  rw [ofPred_forall]
  exact MeasurableSet.iInter (fun n => measurableSet_le
    (measurable_gaussDigit.comp (measurable_gaussMap.iterate n)) measurable_const)

theorem gaussCode_mem_boundedDigits_iff (a : ℕ → ℕ+) (N : ℕ) :
    gaussCode a ∈ gaussBoundedDigits N ↔ ∀ n, (a n : ℕ) ≤ N := by
  simp only [gaussBoundedDigits, mem_inter_iff, mem_Ioo, mem_ofPred_eq,
    gaussCode_pos, gaussCode_lt_one, true_and, gaussMap_iterate_code, gaussDigit_code, shiftDigits,
    add_zero]

theorem gaussMeasure_boundedDigits_zero (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) (N : ℕ) :
    gaussMeasure (gaussBoundedDigits N) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_gaussCylinderTypicalSet hBirkhoff, ae_gaussMeasure_irrational] with x hx hi
  intro hbounded
  obtain ⟨a, rfl⟩ := exists_gaussCode_of_irrational hbounded.1 hi
  exact not_bounded_digits_of_typical hx ⟨N, (gaussCode_mem_boundedDigits_iff a N).mp hbounded⟩

theorem volume_gaussBoundedDigits_zero (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) (N : ℕ) :
    volume (gaussBoundedDigits N) = 0 := by
  have H := volume_restrict_absolutelyContinuous_gaussMeasure (gaussMeasure_boundedDigits_zero hBirkhoff N)
  rwa [Measure.restrict_apply (measurableSet_gaussBoundedDigits N),
    inter_eq_left.mpr (fun _ hx => hx.1)] at H

theorem volume_boundedGaussDigits_zero (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    volume (⋃ N : ℕ, gaussBoundedDigits N) = 0 :=
  measure_iUnion_null (fun N => volume_gaussBoundedDigits_zero hBirkhoff N)

/-- Absolute continuity of the coding map excludes bounded digits for any source measure. -/
theorem measure_bounded_digits_zero_of_code_absolutelyContinuous {X : Type*} [MeasurableSpace X]
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) (μ : Measure X) (a : X → ℕ → ℕ+)
    (ha : Measurable a) (hac : Measure.map (fun q => gaussCode (a q)) μ ≪ volume) :
    μ {q | ∃ N : ℕ, ∀ n, (a q n : ℕ) ≤ N} = 0 := by
  have H := hac (volume_boundedGaussDigits_zero hBirkhoff)
  change (Measure.map (gaussCode ∘ a) μ) (⋃ N : ℕ, gaussBoundedDigits N) = 0 at H
  rw [Measure.map_apply (measurable_gaussCode.comp ha)
    (MeasurableSet.iUnion measurableSet_gaussBoundedDigits)] at H
  convert H using 1
  congr 1
  ext q
  simp only [mem_ofPred_eq, mem_preimage, mem_iUnion, Function.comp_apply, gaussCode_mem_boundedDigits_iff]

end BianchiIX

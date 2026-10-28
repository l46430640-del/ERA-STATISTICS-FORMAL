import BianchiIX.Statistics.EraStatistics

open Set Filter MeasureTheory
open scoped Topology

namespace BianchiIX

theorem timeAverage_shift (u : ℕ → ℝ) (k n : ℕ) (hn : 0 < n) :
    timeAverage (fun j => u (k + j)) n =
      (1 + (k : ℝ) * (n : ℝ)⁻¹) * timeAverage u (k + n) -
        (n : ℝ)⁻¹ * ∑ j ∈ Finset.range k, u j := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hkn0 : ((k + n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.add_pos_right k hn).ne'
  simp only [timeAverage, Finset.sum_range_add]
  field_simp
  push_cast
  ring

/-- A finite change of starting index preserves every finite Cesaro limit, without a boundedness hypothesis. -/
theorem timeAverage_shift_tendsto_iff (u : ℕ → ℝ) (k : ℕ) (l : ℝ) :
    Tendsto (timeAverage (fun j => u (k + j))) atTop (𝓝 l) ↔
      Tendsto (timeAverage u) atTop (𝓝 l) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hf : Tendsto (fun n : ℕ => 1 + (k : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hi)
  have hp : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range k, u j) atTop (𝓝 0) := by
    simpa using hi.mul tendsto_const_nhds
  have hindex : Tendsto (fun n : ℕ => k + n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat k
  constructor
  · intro h
    have hlim := (h.add hp).div hf (by norm_num : (1 : ℝ) ≠ 0)
    have heq : (fun n : ℕ =>
        (timeAverage (fun j => u (k + j)) n + (n : ℝ)⁻¹ * ∑ j ∈ Finset.range k, u j) /
          (1 + (k : ℝ) * (n : ℝ)⁻¹)) =ᶠ[atTop] (fun n => timeAverage u (k + n)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hf0 : 1 + (k : ℝ) * (n : ℝ)⁻¹ ≠ 0 := by positivity
      rw [timeAverage_shift u k n hn, sub_add_cancel]
      exact mul_div_cancel_left₀ _ hf0
    have hs : Tendsto (fun n => timeAverage u (n + k)) atTop (𝓝 l) := by
      simpa only [add_zero, div_one, Nat.add_comm] using hlim.congr' heq
    exact (tendsto_add_atTop_iff_nat k).mp hs
  · intro h
    have hlim := (hf.mul (h.comp hindex)).sub hp
    have heq : (fun n : ℕ =>
        (1 + (k : ℝ) * (n : ℝ)⁻¹) * timeAverage u (k + n) -
          (n : ℝ)⁻¹ * ∑ j ∈ Finset.range k, u j) =ᶠ[atTop]
        timeAverage (fun j => u (k + j)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (timeAverage_shift u k n hn).symm
    simpa only [one_mul, sub_zero] using hlim.congr' heq

theorem eraStatistics_shift_iff (a : ℕ → ℕ+) (y : ℕ → ℝ) (k : ℕ) :
    EraStatistics (shiftDigits a k) (fun j => y (k + j)) ↔ EraStatistics a y := by
  constructor
  · intro h
    have ht (R : ℕ) := (timeAverage_shift_tendsto_iff
      (fun j => min (a j : ℝ) (R : ℝ)) k _).mp (h.truncated_average R)
    refine ⟨?_, ?_, ?_, ?_, ht,
      timeAverage_tendsto_atTop_of_truncations ht gauss_truncated_integral_tendsto_atTop⟩
    · intro f hf
      exact (timeAverage_shift_tendsto_iff (fun j => f (y j)) k _).mp (h.continuous_average f hf)
    · intro w hw
      apply (timeAverage_shift_tendsto_iff
        (fun j => if digitPrefix (shiftDigits a j) w.length = w then 1 else 0) k _).mp
      simpa only [shiftDigits_add] using h.block_frequency w hw
    · intro r
      exact (timeAverage_shift_tendsto_iff (fun j => if (a j : ℕ) = (r : ℕ) then 1 else 0) k _).mp
        (h.digit_frequency r)
    · intro r
      exact (timeAverage_shift_tendsto_iff (fun j => if (r : ℕ) ≤ (a j : ℕ) then 1 else 0) k _).mp
        (h.tail_frequency r)
  · intro h
    have ht (R : ℕ) := (timeAverage_shift_tendsto_iff
      (fun j => min (a j : ℝ) (R : ℝ)) k _).mpr (h.truncated_average R)
    refine ⟨?_, ?_, ?_, ?_, ht,
      timeAverage_tendsto_atTop_of_truncations ht gauss_truncated_integral_tendsto_atTop⟩
    · intro f hf
      exact (timeAverage_shift_tendsto_iff (fun j => f (y j)) k _).mpr (h.continuous_average f hf)
    · intro w hw
      simpa only [shiftDigits_add] using (timeAverage_shift_tendsto_iff
        (fun j => if digitPrefix (shiftDigits a j) w.length = w then 1 else 0) k _).mpr
        (h.block_frequency w hw)
    · intro r
      exact (timeAverage_shift_tendsto_iff (fun j => if (a j : ℕ) = (r : ℕ) then 1 else 0) k _).mpr
        (h.digit_frequency r)
    · intro r
      exact (timeAverage_shift_tendsto_iff (fun j => if (r : ℕ) ≤ (a j : ℕ) then 1 else 0) k _).mpr
        (h.tail_frequency r)

end BianchiIX

import BianchiIX.Statistics.PhysicalEraSequence

/-! Adjacent single-epoch eras and the precise long-era tail coefficient. -/

open Set Filter MeasureTheory
open scoped Topology

namespace BianchiIX

noncomputable section

theorem gaussCylinder_one_one :
    gaussCylinder [1, 1] = Ioo (1 / 2 : ℝ) (2 / 3) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [gaussWord, Nat.cast_one, mem_Ioo]
    change 1 / 2 < gaussInv 1 (gaussInv 1 t) ∧
      gaussInv 1 (gaussInv 1 t) < 2 / 3
    rw [gaussInv_pair_eq le_rfl le_rfl ht.1.le]
    have hd : 0 < 1 * (1 + t) + 1 := by linarith [ht.1]
    constructor
    · apply (lt_div_iff₀ hd).mpr
      linarith [ht.1]
    · apply (div_lt_iff₀ hd).mpr
      linarith [ht.2]
  · intro hx
    have hd : 0 < 1 - x := by linarith [hx.2]
    have ht : (2 * x - 1) / (1 - x) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (by linarith [hx.1]) hd
      · apply (div_lt_one hd).mpr
        linarith [hx.2]
    refine ⟨(2 * x - 1) / (1 - x), ht, ?_⟩
    simp only [gaussWord, Nat.cast_one]
    change gaussInv 1 (gaussInv 1 ((2 * x - 1) / (1 - x))) = x
    rw [gaussInv_pair_eq le_rfl le_rfl ht.1.le]
    field_simp
    ring

theorem gaussMeasure_one_one :
    (gaussMeasure (gaussCylinder [1, 1])).toReal =
      Real.log (10 / 9) / Real.log 2 := by
  rw [gaussCylinder_one_one, gaussMeasure_Ioo (by norm_num) (by norm_num) (by norm_num)]
  have heq : (Real.log (1 + 2 / 3) - Real.log (1 + 1 / 2)) / Real.log 2 =
      Real.log (10 / 9) / Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [heq, ENNReal.toReal_ofReal]
  exact div_nonneg (Real.log_nonneg (by norm_num)) log_two_pos.le

theorem EraStatistics.adjacent_single_frequency {a : ℕ → ℕ+} {y : ℕ → ℝ}
    (H : EraStatistics a y) :
    Tendsto (timeAverage (fun j => if (a j : ℕ) = 1 ∧ (a (j + 1) : ℕ) = 1 then 1 else 0))
      atTop (𝓝 (Real.log (10 / 9) / Real.log 2)) := by
  have h := H.block_frequency [1, 1] (by simp)
  rw [gaussMeasure_one_one] at h
  simpa [digitPrefix, shiftDigits, List.range_succ] using h

theorem gauss_tail_coefficient_bounds {k : ℝ} (hk : 0 < k) :
    (1 - 1 / (k + 1)) / Real.log 2 ≤ k * (Real.log (1 + 1 / k) / Real.log 2) ∧
      k * (Real.log (1 + 1 / k) / Real.log 2) ≤ 1 / Real.log 2 := by
  have hp : 0 < 1 + 1 / k := by positivity
  have hlo : 1 / (k + 1) ≤ Real.log (1 + 1 / k) := by
    have h := Real.one_sub_inv_le_log_of_pos hp
    have heq : 1 - (1 + 1 / k)⁻¹ = 1 / (k + 1) := by
      field_simp
      ring
    rwa [heq] at h
  have hhi : Real.log (1 + 1 / k) ≤ 1 / k := by
    linarith [Real.log_le_sub_one_of_pos hp]
  constructor
  · rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right log_two_pos).mpr
    calc
      _ = k * (1 / (k + 1)) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hk.le
  · rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right log_two_pos).mpr
    calc
      _ ≤ k * (1 / k) := mul_le_mul_of_nonneg_left hhi hk.le
      _ = 1 := by field_simp

theorem tendsto_gauss_tail_coefficient :
    Tendsto (fun k : ℝ => k * (Real.log (1 + 1 / k) / Real.log 2))
      atTop (𝓝 (1 / Real.log 2)) := by
  have hinv : Tendsto (fun k : ℝ => 1 / (k + 1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def, id_eq] using
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have hlo : Tendsto (fun k : ℝ => (1 - 1 / (k + 1)) / Real.log 2)
      atTop (𝓝 (1 / Real.log 2)) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hinv).div_const (Real.log 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
    exact (gauss_tail_coefficient_bounds hk).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
    exact (gauss_tail_coefficient_bounds hk).2

/-- The frequency limit is taken first at each fixed threshold; its tail then has coefficient `1 / log 2`. -/
theorem EraStatistics.tail_frequency_with_asymptotic {a : ℕ → ℕ+} {y : ℕ → ℝ}
    (H : EraStatistics a y) :
    ∃ p : ℕ+ → ℝ,
      (∀ k : ℕ+, Tendsto (timeAverage (fun j => if (k : ℕ) ≤ (a j : ℕ) then 1 else 0))
        atTop (𝓝 (p k))) ∧
      Tendsto (fun n : ℕ => ((n : ℝ) + 1) * p ⟨n + 1, by omega⟩)
        atTop (𝓝 (1 / Real.log 2)) := by
  refine ⟨fun k => Real.log (1 + 1 / (k : ℝ)) / Real.log 2, H.tail_frequency, ?_⟩
  simpa [Function.comp_def] using
    tendsto_gauss_tail_coefficient.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

namespace PhysicalEraSequence

variable {η : ℝ} {J : ℕ} {x : NormalizedState} {K : ℕ → ℕ+}
  {Y : ℕ → CoreAngleState} {t : ℕ → ℝ} {a : ℕ → Fin 6}

theorem adjacent_single_frequency (H : PhysicalEraSequence η J x K Y t a) :
    Tendsto (timeAverage (fun j => if (K j : ℕ) = 1 ∧ (K (j + 1) : ℕ) = 1 then 1 else 0))
      atTop (𝓝 (Real.log (10 / 9) / Real.log 2)) :=
  H.statistics.adjacent_single_frequency

theorem tail_frequency_with_asymptotic (H : PhysicalEraSequence η J x K Y t a) :
    ∃ p : ℕ+ → ℝ,
      (∀ k : ℕ+, Tendsto (timeAverage (fun j => if (k : ℕ) ≤ (K j : ℕ) then 1 else 0))
        atTop (𝓝 (p k))) ∧
      Tendsto (fun n : ℕ => ((n : ℝ) + 1) * p ⟨n + 1, by omega⟩)
        atTop (𝓝 (1 / Real.log 2)) :=
  H.statistics.tail_frequency_with_asymptotic

end PhysicalEraSequence
end
end BianchiIX

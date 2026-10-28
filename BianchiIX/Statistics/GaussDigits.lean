import BianchiIX.Statistics.GaussTypical

/-! Digit intervals, tail events, and the exact integral of each truncated digit. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace BianchiIX

noncomputable section

def gaussDigit (x : ℝ) : ℕ := ⌊1 / x⌋₊

def gaussTailObservable (k : ℕ+) : ℝ → ℝ :=
  (Ioo (0 : ℝ) (1 / (k : ℝ))).indicator (fun _ => 1)

def gaussTruncatedDigit (R : ℕ) (x : ℝ) : ℝ := min (gaussDigit x : ℝ) R

theorem gaussDigit_code (a : ℕ → ℕ+) : gaussDigit (gaussCode a) = (a 0 : ℕ) := by
  apply Nat.floor_eq_iff (one_div_pos.mpr (gaussCode_pos a)).le |>.mpr
  rw [gaussCode_reciprocal]
  constructor
  · linarith [gaussCode_pos (shiftDigits a 1)]
  · linarith [gaussCode_lt_one (shiftDigits a 1)]

theorem gaussCode_mem_tail_iff (a : ℕ → ℕ+) (k : ℕ+) :
    gaussCode a ∈ Ioo (0 : ℝ) (1 / (k : ℝ)) ↔ (k : ℕ) ≤ a 0 := by
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  have hrec : gaussCode a < 1 / (k : ℝ) ↔ (k : ℝ) < 1 / gaussCode a := by
    rw [lt_div_iff₀ hk, lt_div_iff₀ (gaussCode_pos a), mul_comm]
  rw [mem_Ioo, and_iff_right (gaussCode_pos a), hrec, gaussCode_reciprocal]
  constructor
  · intro h
    by_contra hn
    have hle : ((a 0 : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge hn)
    linarith [gaussCode_lt_one (shiftDigits a 1)]
  · intro h
    have hle : (k : ℝ) ≤ a 0 := by exact_mod_cast h
    linarith [gaussCode_pos (shiftDigits a 1)]

theorem gaussTailObservable_code (a : ℕ → ℕ+) (k : ℕ+) :
    gaussTailObservable k (gaussCode a) = if (k : ℕ) ≤ a 0 then 1 else 0 := by
  simp only [gaussTailObservable, indicator_apply, gaussCode_mem_tail_iff]

theorem gaussCylinder_singleton (k : ℕ+) :
    gaussCylinder [(k : ℕ)] = Ioo (1 / ((k : ℝ) + 1)) (1 / (k : ℝ)) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    change 1 / ((k : ℝ) + 1) < 1 / ((k : ℝ) + t) ∧ 1 / ((k : ℝ) + t) < 1 / (k : ℝ)
    constructor
    · exact (one_div_lt_one_div (by linarith) (by linarith [ht.1])).mpr (by linarith [ht.2])
    · exact (one_div_lt_one_div (by linarith [ht.1]) hk).mpr (by linarith [ht.1])
  · intro hx
    have hx0 : 0 < x := (by positivity : 0 < 1 / ((k : ℝ) + 1)).trans hx.1
    refine ⟨1 / x - (k : ℝ), ⟨?_, ?_⟩, ?_⟩
    · have h := (lt_div_iff₀ hk).mp hx.2
      apply sub_pos.mpr
      exact (lt_div_iff₀ hx0).mpr (by nlinarith)
    · have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mp hx.1
      have h' : 1 / x < (k : ℝ) + 1 := (div_lt_iff₀ hx0).mpr (by nlinarith)
      linarith
    · simp [gaussWord, gaussInv]

theorem gaussMeasure_singleton_cylinder (k : ℕ+) :
    (gaussMeasure (gaussCylinder [(k : ℕ)])).toReal =
      Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2 := by
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  rw [gaussCylinder_singleton, gaussMeasure_digit_interval, ENNReal.toReal_ofReal]
  apply div_nonneg _ log_two_pos.le
  apply Real.log_nonneg
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem integrable_gaussTailObservable (k : ℕ+) : Integrable (gaussTailObservable k) gaussMeasure :=
  (integrable_const (1 : ℝ)).indicator measurableSet_Ioo

theorem integral_gaussTailObservable (k : ℕ+) :
    (∫ x, gaussTailObservable k x ∂gaussMeasure) = Real.log (1 + 1 / (k : ℝ)) / Real.log 2 := by
  have hi : (∫ x, gaussTailObservable k x ∂gaussMeasure) =
      (gaussMeasure (Ioo (0 : ℝ) (1 / (k : ℝ)))).toReal := integral_indicator_one measurableSet_Ioo
  rw [hi, gaussMeasure_tail_interval, ENNReal.toReal_ofReal]
  exact div_nonneg (Real.log_nonneg (le_add_of_nonneg_right (by positivity))) log_two_pos.le

theorem gaussTailObservable_one_code (a : ℕ → ℕ+) : gaussTailObservable 1 (gaussCode a) = 1 := by
  simp [gaussTailObservable, gaussCode_pos a, gaussCode_lt_one a]

private theorem nat_tail_step (m k : ℕ) :
    (if k + 1 ≤ m then (1 : ℝ) else 0) =
      (if k ≤ m then 1 else 0) - (if m = k then 1 else 0) := by
  by_cases he : m = k
  · subst m
    simp
  · by_cases h : k ≤ m
    · simp [he, h, show k + 1 ≤ m by omega]
    · simp [he, h, show ¬ k + 1 ≤ m by omega]

theorem gaussTailObservable_succ_code (a : ℕ → ℕ+) (k : ℕ+) :
    gaussTailObservable (k + 1) (gaussCode a) =
      gaussTailObservable k (gaussCode a) - gaussCylinderObservable [(k : ℕ)] (gaussCode a) := by
  rw [gaussTailObservable_code, gaussTailObservable_code,
    gaussCylinderObservable_code _ _ (by simpa using Nat.succ_le_of_lt k.pos)]
  simpa [digitPrefix] using nat_tail_step (a 0) k

theorem gaussTailObservable_succ_ae (k : ℕ+) :
    gaussTailObservable (k + 1) =ᵐ[gaussMeasure]
      (fun x => gaussTailObservable k x - gaussCylinderObservable [(k : ℕ)] x) := by
  filter_upwards [ae_gaussMeasure_mem_unit, ae_gaussMeasure_irrational] with x hx hi
  obtain ⟨a, rfl⟩ := exists_gaussCode_of_irrational hx hi
  exact gaussTailObservable_succ_code a k

theorem integral_gaussTailObservable_succ (k : ℕ+) :
    (∫ x, gaussTailObservable (k + 1) x ∂gaussMeasure) =
      (∫ x, gaussTailObservable k x ∂gaussMeasure) -
        (gaussMeasure (gaussCylinder [(k : ℕ)])).toReal := by
  rw [integral_congr_ae (gaussTailObservable_succ_ae k),
    integral_sub (integrable_gaussTailObservable k) (integrable_gaussCylinderObservable _),
    integral_gaussCylinderObservable]

theorem nat_min_eq_sum_tails (m R : ℕ) :
    min (m : ℝ) (R : ℝ) = ∑ j ∈ Finset.range R, if j + 1 ≤ m then (1 : ℝ) else 0 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ← ih]
    by_cases h : R < m
    · have hR : (R : ℝ) ≤ m := by exact_mod_cast h.le
      have hR' : (R : ℝ) + 1 ≤ m := by exact_mod_cast h
      simp [min_eq_right hR, min_eq_right hR', Nat.succ_le_iff.mpr h]
    · have hm : (m : ℝ) ≤ R := by exact_mod_cast le_of_not_gt h
      have hm' : (m : ℝ) ≤ (R : ℝ) + 1 := by linarith
      simp [min_eq_left hm, min_eq_left hm', show ¬ R + 1 ≤ m by omega]

theorem gaussTruncatedDigit_eq_sum_ae (R : ℕ) :
    gaussTruncatedDigit R =ᵐ[gaussMeasure]
      (fun x => ∑ j ∈ Finset.range R, gaussTailObservable ⟨j + 1, by omega⟩ x) := by
  filter_upwards [ae_gaussMeasure_mem_unit, ae_gaussMeasure_irrational] with x hx hi
  obtain ⟨a, rfl⟩ := exists_gaussCode_of_irrational hx hi
  rw [gaussTruncatedDigit, gaussDigit_code, nat_min_eq_sum_tails]
  apply Finset.sum_congr rfl
  intro j _
  exact (gaussTailObservable_code a ⟨j + 1, by omega⟩).symm

theorem integrable_gaussTruncatedDigit (R : ℕ) : Integrable (gaussTruncatedDigit R) gaussMeasure :=
  (integrable_finsetSum (Finset.range R) (fun j _ =>
    integrable_gaussTailObservable ⟨j + 1, by omega⟩)).congr (gaussTruncatedDigit_eq_sum_ae R).symm

theorem integral_gaussTruncatedDigit (R : ℕ) :
    (∫ x, gaussTruncatedDigit R x ∂gaussMeasure) = Real.log ((R : ℝ) + 1) / Real.log 2 := by
  rw [integral_congr_ae (gaussTruncatedDigit_eq_sum_ae R),
    integral_finsetSum _ (fun j _ => integrable_gaussTailObservable ⟨j + 1, by omega⟩)]
  calc
    _ = ∑ j ∈ Finset.range R, Real.log (1 + 1 / ((j : ℝ) + 1)) / Real.log 2 := by
      apply Finset.sum_congr rfl
      intro j _
      simpa using integral_gaussTailObservable ⟨j + 1, by omega⟩
    _ = _ := gauss_log_tail_sum R

end
end BianchiIX

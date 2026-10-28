import BianchiIX.Analysis.ConnectionReturnBounds

noncomputable section

namespace BianchiIX

open Set

/-- A single positive power absorbs the remaining logarithm of the auxiliary scale. -/
theorem scale_log_weight_le_two {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    (1 + |Real.log a|) * a ≤ 2 := by
  have H := mul_neg_log_le_one ha.1
  rw [abs_of_nonpos (Real.log_nonpos ha.1.le ha.2)]
  nlinarith only [H, ha.2]

/-- The fixed long-tail powers retain more than the required twenty-four powers in both cone directions. -/
theorem shear_tail_entrance_cone_powers {a u v w : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1)
    (hu : 0 ≤ u ∧ u ≤ 20 * a ^ 48) (hv : 0 ≤ v ∧ v ≤ 40 * a ^ 8)
    (hw : 0 ≤ w ∧ w ≤ 80 * a ^ 44) :
    (1 + |Real.log a|) * Real.sqrt (u * v) ≤ 60 * a ^ 27 ∧
    (1 + |Real.log a|) * Real.sqrt (w * v) ≤ 120 * a ^ 25 := by
  have HU : Real.sqrt (u * v) ≤ 30 * a ^ 28 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity [ha.1], ?_⟩
    have H := mul_le_mul hu.2 hv.2 hv.1 (by positivity [ha.1] : 0 ≤ 20 * a ^ 48)
    nlinarith only [H, pow_nonneg ha.1.le 56]
  have HW : Real.sqrt (w * v) ≤ 60 * a ^ 26 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity [ha.1], ?_⟩
    have H := mul_le_mul hw.2 hv.2 hv.1 (by positivity [ha.1] : 0 ≤ 80 * a ^ 44)
    nlinarith only [H, pow_nonneg ha.1.le 52]
  have HL := scale_log_weight_le_two ha
  constructor
  · calc
      _ ≤ (1 + |Real.log a|) * (30 * a ^ 28) := mul_le_mul_of_nonneg_left HU (by positivity)
      _ = 30 * ((1 + |Real.log a|) * a) * a ^ 27 := by ring
      _ ≤ 30 * 2 * a ^ 27 := by gcongr; positivity [ha.1]
      _ = _ := by ring
  · calc
      _ ≤ (1 + |Real.log a|) * (60 * a ^ 26) := mul_le_mul_of_nonneg_left HW (by positivity)
      _ = 60 * ((1 + |Real.log a|) * a) * a ^ 25 := by ring
      _ ≤ 60 * 2 * a ^ 25 := by gcongr; positivity [ha.1]
      _ = _ := by ring

/-- Without the long tail the stable wall powers alone give the required entrance cone. -/
theorem shear_fast_entrance_cone_powers {a u v w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 16 * a ^ 48) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 16 * a ^ 548) :
    Real.sqrt (u * v) ≤ 4 * a ^ 24 ∧ Real.sqrt (w * v) ≤ 4 * a ^ 274 := by
  constructor
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have H := (mul_le_of_le_one_right hu.1 hv.2).trans hu.2
    nlinarith only [H]
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have H := (mul_le_of_le_one_right hw.1 hv.2).trans hw.2
    nlinarith only [H]

end BianchiIX

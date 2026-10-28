import BianchiIX.Algebra.CoreAngle

noncomputable section

namespace BianchiIX

def exitTailGap (R v : ℝ) : ℝ := Real.sqrt (R ^ 2 - v ^ 2)

def exitTailSpeed (R u v w : ℝ) : ℝ := exitTailGap R v + coupling u v w

def exitTailRadial (R u v w : ℝ) : ℝ :=
  (-coupling u v w * R - exitTailGap R v * (u - w) ^ 2 / R) / exitTailSpeed R u v w

def exitTailStrongRate (R u v w : ℝ) : ℝ :=
  (2 * exitTailGap R v - R ^ 2 + 2 * v * w - w ^ 2 + u ^ 2) / (2 * exitTailSpeed R u v w)

def exitTailWeakRate (R u v w : ℝ) : ℝ :=
  (exitTailGap R v - 2 - coupling u v w) / exitTailSpeed R u v w

theorem exitTailGap_of_coreRadius {m v : ℝ} (hm : m < 1) :
    exitTailGap (coreRadius m v) v = 1 - m := by
  unfold exitTailGap
  rw [coreRadius_sq]
  dsimp only [coreEnergy]
  rw [add_sub_cancel_right, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hm] : m - 1 < 0)]
  ring

theorem exitTailGap_sq {R v : ℝ} (h : v ^ 2 ≤ R ^ 2) :
    exitTailGap R v ^ 2 = R ^ 2 - v ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

/-- The boundary rates retain both the small gap from R = 2 and the decaying active wall. -/
theorem exitTail_boundary_rates {R v : ℝ} (hR : 0 < R) (hv : v ^ 2 < R ^ 2) :
    exitTailStrongRate R 0 v 0 = -(R - 2) / 2 - R * v ^ 2 / (2 * exitTailGap R v * (R + exitTailGap R v)) ∧
    exitTailWeakRate R 0 v 0 = (R - 2) / R - 2 * v ^ 2 / (R * exitTailGap R v * (R + exitTailGap R v)) := by
  have ht : 0 < exitTailGap R v := Real.sqrt_pos.mpr (sub_pos.mpr hv)
  have hs := exitTailGap_sq hv.le
  have hp : R + exitTailGap R v ≠ 0 := ne_of_gt (add_pos hR ht)
  simp only [exitTailStrongRate, exitTailWeakRate, exitTailSpeed, coupling, zero_mul,
    mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, sub_zero]
  constructor <;> field_simp <;> nlinarith only [hs, congrArg (R * ·) hs]

/-- The pure weak wall changes the radius only quadratically, including at zero weak amplitude. -/
theorem exitTailRadial_zero_strong {R v : ℝ} (w : ℝ) (ht : exitTailGap R v ≠ 0) :
    exitTailRadial R 0 v w = -w ^ 2 / R := by
  dsimp [exitTailRadial, exitTailSpeed, coupling]
  simp only [zero_mul, neg_zero, zero_sub, neg_sq, add_zero]
  rw [neg_div, mul_div_assoc, mul_div_cancel_left₀ _ ht]
  ring

theorem exitTailWeakRate_correction {R u v w : ℝ}
    (ht : exitTailGap R v ≠ 0) (hd : exitTailSpeed R u v w ≠ 0) :
    exitTailWeakRate R u v w - (1 - 2 / exitTailGap R v) =
      -2 * coupling u v w * (exitTailGap R v - 1) / (exitTailGap R v * exitTailSpeed R u v w) := by
  dsimp only [exitTailWeakRate]
  field_simp
  dsimp only [exitTailSpeed]
  ring

end BianchiIX

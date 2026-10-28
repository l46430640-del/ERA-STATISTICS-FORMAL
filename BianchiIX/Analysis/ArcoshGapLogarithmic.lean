import BianchiIX.Analysis.ArcoshGap

noncomputable section

namespace BianchiIX

/-- The excess over the logarithmic height is uniformly bounded, including long entrances. -/
theorem arcoshGap_log_bounds {k v : ℝ} (hk : 1 < k) (hv : 0 < v ∧ v < 1) :
    -Real.log v ≤ arcoshGap k v ∧ arcoshGap k v ≤ 1 - Real.log v := by
  have hk0 : 0 < k := by linarith
  let A := k + Real.sqrt (k ^ 2 - v ^ 2)
  let B := k + Real.sqrt (k ^ 2 - 1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hAB : B ≤ A := by
    have H : Real.sqrt (k ^ 2 - 1) ≤ Real.sqrt (k ^ 2 - v ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith only [hv.1, hv.2])
    dsimp [A, B]
    linarith only [H]
  have hsqrt : Real.sqrt (k ^ 2 - v ^ 2) ≤ k :=
    Real.sqrt_le_iff.mpr ⟨hk0.le, by nlinarith only [sq_nonneg v]⟩
  have hratio : 1 ≤ A / B ∧ A / B ≤ 2 := by
    constructor
    · exact (one_le_div hB).mpr hAB
    · apply (div_le_iff₀ hB).mpr
      dsimp [A, B]
      linarith [Real.sqrt_nonneg (k ^ 2 - 1)]
  have hsplit : Real.arcosh (k / v) = Real.log A - Real.log v := by
    rw [Real.arcosh, sqrt_scaled_gap hk hv, ← add_div, Real.log_div hA.ne' hv.1.ne']
  have hgap : arcoshGap k v = Real.log (A / B) - Real.log v := by
    rw [arcoshGap, hsplit, Real.arcosh, Real.log_div hA.ne' hB.ne']
    dsimp [B]
    ring
  have hlo := Real.log_nonneg hratio.1
  have hhi := Real.log_le_sub_one_of_pos (div_pos hA hB)
  rw [hgap]
  constructor <;> linarith only [hlo, hhi, hratio.2]

end BianchiIX

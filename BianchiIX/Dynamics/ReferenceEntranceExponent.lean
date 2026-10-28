import BianchiIX.Analysis.ArcoshGap
import BianchiIX.Dynamics.ReferenceEntranceResponse

noncomputable section

namespace BianchiIX

def referenceEntranceExponent (k v : ℝ) : ℝ := k / 2 * arcoshGap k v

def referenceEntranceExponentSlope (k v : ℝ) : ℝ := arcoshGap k v / 2 + k / 2 *
  (1 / Real.sqrt (k ^ 2 - v ^ 2) - 1 / Real.sqrt (k ^ 2 - 1))

theorem hasDerivAt_referenceEntranceExponent {k v : ℝ} (hk : 1 < k) (hv : 0 < v ∧ v < 1) :
    HasDerivAt (fun r => referenceEntranceExponent r v) (referenceEntranceExponentSlope k v) k := by
  convert! ((hasDerivAt_id k).div_const 2).mul (hasDerivAt_arcoshGap hk hv) using 1
  dsimp [referenceEntranceExponentSlope]
  ring

theorem referenceEntranceExponent_bounds {k v : ℝ} (hk : 2 ≤ k) (hv : 0 < v ∧ v < 1) :
    (1 - v) / 2 * k ≤ referenceEntranceExponent k v ∧
      |referenceEntranceExponentSlope k v| ≤ (1 / v + 1) * k := by
  have hk0 : 0 < k := by linarith
  have hgap := arcoshGap_bounds (show 1 < k by linarith) hv
  have hg0 : 0 ≤ arcoshGap k v := le_trans (by linarith [hv.2]) hgap.1
  constructor
  · calc
      (1 - v) / 2 * k = k / 2 * (1 - v) := by ring
      _ ≤ k / 2 * arcoshGap k v := mul_le_mul_of_nonneg_left hgap.1 (by positivity)
      _ = referenceEntranceExponent k v := rfl
  · have H := arcoshGap_derivative_bound hk hv
    calc
      _ ≤ |arcoshGap k v / 2| + |k / 2 *
          (1 / Real.sqrt (k ^ 2 - v ^ 2) - 1 / Real.sqrt (k ^ 2 - 1))| := abs_add_le _ _
      _ = arcoshGap k v / 2 + k / 2 *
          |1 / Real.sqrt (k ^ 2 - v ^ 2) - 1 / Real.sqrt (k ^ 2 - 1)| := by
        rw [abs_mul, abs_of_nonneg (div_nonneg hg0 (by norm_num)), abs_of_pos (div_pos hk0 (by norm_num))]
      _ ≤ (2 * k / v) / 2 + k / 2 * (4 / k) :=
        add_le_add (div_le_div_of_nonneg_right hgap.2 (by norm_num))
          (mul_le_mul_of_nonneg_left H (by positivity))
      _ = k / v + 2 := by field_simp; ring
      _ ≤ k / v + k := add_le_add le_rfl hk
      _ = (1 / v + 1) * k := by ring

theorem referenceEntranceStrongResponse_exponent (k v : ℝ) :
    referenceEntranceStrongResponse k v = -2 * v / k * (1 - Real.exp (-referenceEntranceExponent k v)) := by
  by_cases hk : k = 0
  · simp [hk, referenceEntranceStrongResponse]
  rw [referenceEntranceStrongResponse_eq]
  have H : -(k ^ 2 / 2) * ((Real.arcosh (k / v) - Real.arcosh k) / k) =
      -referenceEntranceExponent k v := by
    dsimp [referenceEntranceExponent, arcoshGap]
    field_simp
  rw [H]

theorem hasDerivAt_referenceEntranceStrongResponse {k v : ℝ} (hk : 1 < k) (hv : 0 < v ∧ v < 1) :
    HasDerivAt (fun r => referenceEntranceStrongResponse r v)
      (2 * v / k ^ 2 * (1 - Real.exp (-referenceEntranceExponent k v)) -
        2 * v / k * referenceEntranceExponentSlope k v * Real.exp (-referenceEntranceExponent k v)) k := by
  have hk0 : k ≠ 0 := ne_of_gt (lt_trans zero_lt_one hk)
  have he := (hasDerivAt_referenceEntranceExponent hk hv).neg.exp
  have H := ((hasDerivAt_const k (-2 * v)).div (hasDerivAt_id k) hk0).mul (he.const_sub 1)
  convert! H using 1
  · ext r
    exact referenceEntranceStrongResponse_exponent r v
  · simp only [Pi.neg_apply, Pi.div_apply, id_eq]
    ring

end BianchiIX

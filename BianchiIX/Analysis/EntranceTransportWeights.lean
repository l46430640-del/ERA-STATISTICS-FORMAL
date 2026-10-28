import BianchiIX.Analysis.EntranceOrdinaryWeights

noncomputable section

namespace BianchiIX

theorem entrance_phase_waiting_budget {u v w θ : ℝ}
    (hu : 0 ≤ u) (hv : 0 < v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    0 ≤ u * v + θ * (v * w) ^ 2 ∧
      u * v + θ * (v * w) ^ 2 ≤ u + w ∧
      (-Real.log v) * (u * v + θ * (v * w) ^ 2) ≤ u + w := by
  have hv0 := hv.1.le
  have hw0 := hw.1
  have hθ0 := hθ.1
  have hW2 : w ^ 2 ≤ w := by nlinarith only [mul_le_mul_of_nonneg_left hw.2 hw.1]
  have htail : θ * v * w ^ 2 ≤ w :=
    ((mul_le_of_le_one_left (sq_nonneg w)
      ((mul_le_of_le_one_left hv0 hθ.2).trans hv.2)).trans hW2)
  have hP : 0 ≤ u + θ * v * w ^ 2 := by positivity
  have hPbound : u + θ * v * w ^ 2 ≤ u + w := add_le_add le_rfl htail
  have hLv : (-Real.log v) * v ≤ 1 := by simpa only [mul_comm] using mul_neg_log_le_one hv.1
  refine ⟨by positivity, ?_, ?_⟩
  · calc
      _ = v * (u + θ * v * w ^ 2) := by ring
      _ ≤ u + θ * v * w ^ 2 := mul_le_of_le_one_left hP hv.2
      _ ≤ _ := hPbound
  · calc
      _ = ((-Real.log v) * v) * (u + θ * v * w ^ 2) := by ring
      _ ≤ u + θ * v * w ^ 2 := mul_le_of_le_one_left hP hLv
      _ ≤ _ := hPbound

theorem entrance_transport_initial_weights {u v w θ k βU βW : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w ∧ w ≤ 1) (hθ : 0 ≤ θ)
    (hk : 1 ≤ k) (hU : |βU| ≤ 12 * k) (hW : |βW| ≤ 9) :
    |u * βU| + |w * βW| ≤ 12 * k * u + 9 * w ∧
      (v * |u * βU| + (u * v + θ * v ^ 2 * w) * |w * βW|) / k ≤
        21 * (u * v + θ * (v * w) ^ 2) := by
  have hk0 : 0 < k := by linarith
  let H := u * v + θ * (v * w) ^ 2
  let S := u * v + θ * v ^ 2 * w
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity [hw.1]
  have hU' : |u * βU| ≤ 12 * k * u := by
    rw [abs_mul, abs_of_nonneg hu]
    exact (mul_le_mul_of_nonneg_left hU hu).trans_eq (by ring)
  have hW' : |w * βW| ≤ 9 * w := by
    rw [abs_mul, abs_of_nonneg hw.1]
    exact (mul_le_mul_of_nonneg_left hW hw.1).trans_eq (by ring)
  refine ⟨add_le_add hU' hW', ?_⟩
  have hP : u * v ≤ H := by dsimp [H]; nlinarith only [mul_nonneg hθ (sq_nonneg (v * w))]
  have hSW : S * w ≤ H := by
    have HE := mul_le_of_le_one_right (mul_nonneg hu hv) hw.2
    dsimp [S, H]
    nlinarith only [HE]
  apply (div_le_iff₀ hk0).mpr
  have HE := add_le_add (mul_le_mul_of_nonneg_left hU' hv) (mul_le_mul_of_nonneg_left hW' hS)
  change _ ≤ 21 * H * k
  calc
    _ ≤ v * (12 * k * u) + S * (9 * w) := HE
    _ = 12 * k * (u * v) + 9 * (S * w) := by ring
    _ ≤ 12 * k * H + 9 * H := add_le_add (mul_le_mul_of_nonneg_left hP (by positivity))
      (mul_le_mul_of_nonneg_left hSW (by norm_num))
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hk hH]

end BianchiIX

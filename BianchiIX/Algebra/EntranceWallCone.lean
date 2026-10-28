import BianchiIX.Algebra.ConnectionConeSize

noncomputable section

namespace BianchiIX

theorem entrance_sqrt_waiting_weights {k L : ℝ} (hk : 1 ≤ k) (hL : 0 ≤ L) :
    (1 + L) * Real.exp (-k * L / 6) ≤ 6 ∧
    (k + L) * Real.exp (-L / (2 * k)) ≤ 2 * k := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  constructor
  · have H := affine_mul_exp_neg_le_one (k * L / 6)
    have hscale : 1 + L ≤ 6 * (1 + k * L / 6) := by
      nlinarith only [mul_le_mul_of_nonneg_right hk hL]
    calc
      _ ≤ (6 * (1 + k * L / 6)) * Real.exp (-k * L / 6) :=
        mul_le_mul_of_nonneg_right hscale (Real.exp_pos _).le
      _ = 6 * ((1 + k * L / 6) * Real.exp (-(k * L / 6))) := by
        rw [show -k * L / 6 = -(k * L / 6) by ring]
        ring
      _ ≤ 6 := by linarith only [H]
  · have H := affine_mul_exp_neg_le_one (L / (2 * k))
    have hscale : k + L ≤ (2 * k) * (1 + L / (2 * k)) := by
      field_simp
      nlinarith only [hk0]
    calc
      _ ≤ ((2 * k) * (1 + L / (2 * k))) * Real.exp (-L / (2 * k)) :=
        mul_le_mul_of_nonneg_right hscale (Real.exp_pos _).le
      _ = (2 * k) * ((1 + L / (2 * k)) * Real.exp (-(L / (2 * k)))) := by rw [neg_div]; ring
      _ ≤ 2 * k := by nlinarith only [mul_le_mul_of_nonneg_left H hk0.le]

/-- Square-root weighting absorbs the entrance waiting time without a lower bound on the active wall. -/
theorem entrance_wall_sqrt_response {C D k L U V W X Z dX dZ : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hk : 1 ≤ k) (hL : 0 ≤ L)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hX : 0 ≤ X) (hZ : 0 ≤ Z)
    (hdecayX : X ≤ U * V * Real.exp (-k * L / 3))
    (hdecayZ : Z ≤ W * V * Real.exp (-L / k))
    (hdX : |dX| ≤ C * D * k ^ 2 * (1 + L) * X)
    (hdZ : |dZ| ≤ C * D * (k + L) * Z) :
    |dX| ≤ 6 * C * D * k ^ 2 * Real.sqrt (U * V) * Real.sqrt X ∧
    |dZ| ≤ 2 * C * D * k * Real.sqrt (W * V) * Real.sqrt Z := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have HX : Real.sqrt X ≤ Real.sqrt (U * V) * Real.exp (-k * L / 6) := by
    convert sqrt_le_sqrt_mul_exp_half (mul_nonneg hU hV) hdecayX using 1
    congr 2
    ring
  have HZ : Real.sqrt Z ≤ Real.sqrt (W * V) * Real.exp (-L / (2 * k)) := by
    convert sqrt_le_sqrt_mul_exp_half (mul_nonneg hW hV) hdecayZ using 1
    congr 2
    ring
  obtain ⟨HwaitX, HwaitZ⟩ := entrance_sqrt_waiting_weights hk hL
  constructor
  · calc
      _ ≤ C * D * k ^ 2 * (1 + L) * X := hdX
      _ = C * D * k ^ 2 * (1 + L) * (Real.sqrt X * Real.sqrt X) := by rw [Real.mul_self_sqrt hX]
      _ ≤ C * D * k ^ 2 * (1 + L) * ((Real.sqrt (U * V) * Real.exp (-k * L / 6)) * Real.sqrt X) := by gcongr
      _ = (C * D * k ^ 2 * Real.sqrt (U * V) * Real.sqrt X) * ((1 + L) * Real.exp (-k * L / 6)) := by ring
      _ ≤ (C * D * k ^ 2 * Real.sqrt (U * V) * Real.sqrt X) * 6 := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ C * D * (k + L) * Z := hdZ
      _ = C * D * (k + L) * (Real.sqrt Z * Real.sqrt Z) := by rw [Real.mul_self_sqrt hZ]
      _ ≤ C * D * (k + L) * ((Real.sqrt (W * V) * Real.exp (-L / (2 * k))) * Real.sqrt Z) := by gcongr
      _ = (C * D * Real.sqrt (W * V) * Real.sqrt Z) * ((k + L) * Real.exp (-L / (2 * k))) := by ring
      _ ≤ (C * D * Real.sqrt (W * V) * Real.sqrt Z) * (2 * k) := by gcongr
      _ = _ := by ring

end BianchiIX

import BianchiIX.Analysis.ConnectionReturnBounds

noncomputable section

namespace BianchiIX

theorem affine_mul_exp_neg_le_one (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
  simpa only [add_comm] using H

/-- The endpoint envelopes absorb both the moving-clock denominator and the waiting length. -/
theorem connection_endpoint_envelope_bounds {μ u w U V : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u) (hw : 0 < w ∧ w ≤ 1 / 10000) (hV : 0 ≤ V)
    (hU : U ≤ u * Real.exp (-μ * (-Real.log w) / 2))
    (hdecay : V ≤ w * Real.exp (-2 * (-Real.log w) / μ)) :
    U / w ≤ 8 * u / μ ∧ V ^ 2 ≤ w ^ 2 ∧ (1 - Real.log w) * V ^ 2 ≤ μ * w ^ 2 := by
  let L := -Real.log w
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hL : 1 / 2 ≤ L := by
    have H := Real.log_le_sub_one_of_pos hw.1
    dsimp [L]
    linarith only [H, hw.2]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hwexp : w = Real.exp (-L) := by simp [L, Real.exp_log hw.1]
  have hstrong : Real.exp (-μ * L / 4) ≤ 8 / μ := by
    apply (le_div_iff₀ hμ0).mpr
    have H := affine_mul_exp_neg_le_one (μ * L / 4)
    rw [show -(μ * L / 4) = -μ * L / 4 by ring] at H
    have Hl := mul_le_mul_of_nonneg_right hL (show 0 ≤ μ * Real.exp (-μ * L / 4) by positivity)
    nlinarith only [H, Hl, Real.exp_pos (-μ * L / 4)]
  have hv2 : V ^ 2 ≤ w ^ 2 * Real.exp (-4 * L / μ) := by
    have H := pow_le_pow_left₀ hV hdecay 2
    rw [mul_pow, ← Real.exp_nat_mul] at H
    convert! H using 1
    congr 2
    ring
  have hexp : Real.exp (-4 * L / μ) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by linarith only [hL0]) hμ0.le)
  refine ⟨?_, (hv2.trans (mul_le_mul_of_nonneg_left hexp (sq_nonneg w))).trans_eq (mul_one _), ?_⟩
  · calc
      U / w ≤ (u * Real.exp (-μ * L / 2)) / w := div_le_div_of_nonneg_right hU hw.1.le
      _ = u * Real.exp (-μ * L / 2 - (-L)) := by rw [hwexp, Real.exp_sub]; ring
      _ ≤ u * Real.exp (-μ * L / 4) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith only [hμ, hL0])) hu
      _ ≤ u * (8 / μ) := mul_le_mul_of_nonneg_left hstrong hu
      _ = 8 * u / μ := by ring
  · have H := affine_mul_exp_neg_le_one (4 * L / μ)
    rw [show -(4 * L / μ) = -4 * L / μ by ring] at H
    have hweight : 1 + L ≤ μ * (1 + 4 * L / μ) := by
      have hid : μ * (1 + 4 * L / μ) = μ + 4 * L := by field_simp
      rw [hid]
      linarith only [hμ, hL0]
    have Hb : (1 + L) * Real.exp (-4 * L / μ) ≤ μ := by
      have H1 := mul_le_mul_of_nonneg_right hweight (Real.exp_pos (-4 * L / μ)).le
      have H2 := mul_le_mul_of_nonneg_left H hμ0.le
      nlinarith only [H1, H2]
    change (1 + L) * V ^ 2 ≤ μ * w ^ 2
    calc
      (1 + L) * V ^ 2 ≤ (1 + L) * (w ^ 2 * Real.exp (-4 * L / μ)) :=
        mul_le_mul_of_nonneg_left hv2 (by positivity)
      _ = w ^ 2 * ((1 + L) * Real.exp (-4 * L / μ)) := by ring
      _ ≤ w ^ 2 * μ := mul_le_mul_of_nonneg_left Hb (sq_nonneg w)
      _ = μ * w ^ 2 := mul_comm _ _

end BianchiIX

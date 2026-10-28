import BianchiIX.Analysis.CompactConePowers

noncomputable section

namespace BianchiIX

theorem terminal_strong_log_bound {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    v ^ (19 / 24 : ℝ) * (1 + |Real.log v|) ≤ 24 * v ^ (3 / 4 : ℝ) := by
  have hp := Real.rpow_pos_of_pos hv (1 / 24 : ℝ)
  have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hp.ne', Real.log_rpow hv] at H
  have Hsmall : v ^ (1 / 24 : ℝ) * (1 + |Real.log v|) ≤ 24 := by
    rw [abs_of_nonpos (Real.log_nonpos hv.le hv1)]
    nlinarith only [H, hp.le]
  have Hsplit : v ^ (19 / 24 : ℝ) = v ^ (3 / 4 : ℝ) * v ^ (1 / 24 : ℝ) := by
    rw [← Real.rpow_add hv]
    norm_num
  rw [Hsplit, mul_assoc]
  exact (mul_le_mul_of_nonneg_left Hsmall (Real.rpow_nonneg hv.le _)).trans_eq (by ring)

theorem terminal_scaled_wall_power {α v w A p : ℝ} (hα : 0 < α) (hv : 0 ≤ v)
    (hw : 0 ≤ w) (hA : 1 ≤ A) (hp : 0 ≤ p ∧ p ≤ 1) (hscale : v ≤ A * w / α ^ 2) :
    v ^ p ≤ A * α ^ (-(2 * p)) * w ^ p := by
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hAp : A ^ p ≤ A := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA hp.2
  calc
    _ ≤ (A * w / α ^ 2) ^ p := Real.rpow_le_rpow hv hscale hp.1
    _ = A ^ p * w ^ p / α ^ (2 * p) := by
      rw [Real.div_rpow (mul_nonneg hA0 hw) (sq_nonneg α), Real.mul_rpow hA0 hw,
        ← Real.rpow_natCast α 2, ← Real.rpow_mul hα.le]
      norm_num
    _ ≤ A * w ^ p / α ^ (2 * p) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAp (Real.rpow_nonneg hw _)) (Real.rpow_nonneg hα.le _)
    _ = _ := by rw [Real.rpow_neg hα.le]; ring

/-- The strong row retains the two phase powers in (D.37). -/
theorem terminal_strong_cone_power {α v w A β : ℝ} (hα : 0 < α)
    (hv : 0 < v ∧ v ≤ 1) (hw : 0 < w) (hA : 1 ≤ A) (hscale : v ≤ A * w / α ^ 2) :
    α ^ β * (v ^ (19 / 24 : ℝ) * (1 + |Real.log v|) + α * v ^ (19 / 24 : ℝ) / Real.sqrt w) ≤
      24 * A * (α ^ (β - 3 / 2) * w ^ (3 / 4 : ℝ) + α ^ (β - 7 / 12) * w ^ (7 / 24 : ℝ)) := by
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have H3 := terminal_scaled_wall_power hα hv.1.le hw.le hA (by norm_num : 0 ≤ (3 / 4 : ℝ) ∧ (3 / 4 : ℝ) ≤ 1) hscale
  have H19 := terminal_scaled_wall_power hα hv.1.le hw.le hA (by norm_num : 0 ≤ (19 / 24 : ℝ) ∧ (19 / 24 : ℝ) ≤ 1) hscale
  norm_num at H3 H19
  have Hid1 : α ^ β * (24 * (A * α ^ (-(3 / 2 : ℝ)) * w ^ (3 / 4 : ℝ))) =
      24 * A * α ^ (β - 3 / 2) * w ^ (3 / 4 : ℝ) := by
    rw [show β - 3 / 2 = β + -(3 / 2 : ℝ) by ring, Real.rpow_add hα]
    ring
  have Hid2 : α ^ β * (α * (A * α ^ (-(19 / 12 : ℝ)) * w ^ (19 / 24 : ℝ)) / Real.sqrt w) =
      A * α ^ (β - 7 / 12) * w ^ (7 / 24 : ℝ) := by
    have hαpow : α ^ (β - 7 / 12) = α ^ β * α * α ^ (-(19 / 12 : ℝ)) := by
      rw [show β - 7 / 12 = (β + 1) + -(19 / 12 : ℝ) by ring,
        Real.rpow_add hα, Real.rpow_add hα, Real.rpow_one]
    have hwpow : w ^ (19 / 24 : ℝ) / Real.sqrt w = w ^ (7 / 24 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hw]
      norm_num
    rw [hαpow, show α ^ β * (α * (A * α ^ (-(19 / 12 : ℝ)) * w ^ (19 / 24 : ℝ)) / Real.sqrt w) =
      A * (α ^ β * α * α ^ (-(19 / 12 : ℝ))) * (w ^ (19 / 24 : ℝ) / Real.sqrt w) by ring, hwpow]
  have H1 := mul_le_mul_of_nonneg_left ((terminal_strong_log_bound hv.1 hv.2).trans
    (mul_le_mul_of_nonneg_left H3 (by norm_num : (0 : ℝ) ≤ 24))) (Real.rpow_nonneg hα.le β)
  rw [Hid1] at H1
  have H2 := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left H19 hα.le) (Real.sqrt_nonneg w)) (Real.rpow_nonneg hα.le β)
  rw [Hid2] at H2
  have Hpos : 0 ≤ A * α ^ (β - 7 / 12) * w ^ (7 / 24 : ℝ) := by positivity
  nlinarith only [H1, H2, Hpos]

/-- The weak row loses no phase power and creates no wall-ratio factor. -/
theorem terminal_weak_cone_power {α v w U W A : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hv : 0 < v ∧ v ≤ 1) (hU : 0 < U) (hW : 0 < W) (hA : 1 ≤ A)
    (hwscale : Real.sqrt w ≤ A / α * Real.sqrt U)
    (hvscale : Real.sqrt v ≤ A / α * Real.sqrt W) :
    α ^ 2 * Real.sqrt w * Real.sqrt v *
      (|Real.log v| + 1 / α + 1 / Real.sqrt W + 1 / Real.sqrt U) ≤
        4 * A ^ 2 * (Real.sqrt U + Real.sqrt W) := by
  have hα0 : 0 < α := hα.1
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hAA : A ≤ A ^ 2 := by nlinarith only [hA]
  have hlog : Real.sqrt v * |Real.log v| ≤ 2 := by
    have H := sqrt_log_small_bound hv.1 hv.2
    nlinarith only [H, Real.sqrt_nonneg v]
  have hscaled : α ^ 2 * Real.sqrt w ≤ A * Real.sqrt U := calc
    _ ≤ α ^ 2 * (A / α * Real.sqrt U) := mul_le_mul_of_nonneg_left hwscale (sq_nonneg α)
    _ = α * (A * Real.sqrt U) := by field_simp
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hα.2
  have hprod : α ^ 2 * Real.sqrt w * Real.sqrt v ≤ A ^ 2 * Real.sqrt U * Real.sqrt W := calc
    _ ≤ α ^ 2 * (A / α * Real.sqrt U) * (A / α * Real.sqrt W) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hwscale (sq_nonneg α)) hvscale (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp
  have Hlog : α ^ 2 * Real.sqrt w * Real.sqrt v * |Real.log v| ≤ 2 * A * Real.sqrt U := calc
    _ = (α ^ 2 * Real.sqrt w) * (Real.sqrt v * |Real.log v|) := by ring
    _ ≤ (A * Real.sqrt U) * 2 := mul_le_mul hscaled hlog (by positivity) (by positivity)
    _ = _ := by ring
  have Ha : α ^ 2 * Real.sqrt w * Real.sqrt v * (1 / α) ≤ A * Real.sqrt U := calc
    _ ≤ α ^ 2 * (A / α * Real.sqrt U) * 1 * (1 / α) := by
      gcongr
      exact Real.sqrt_le_one.mpr hv.2
    _ = _ := by field_simp
  have HU : α ^ 2 * Real.sqrt w * Real.sqrt v * (1 / Real.sqrt U) ≤ A ^ 2 * Real.sqrt W :=
    (mul_le_mul_of_nonneg_right hprod (by positivity)).trans_eq (by field_simp [(Real.sqrt_pos.mpr hU).ne'])
  have HW : α ^ 2 * Real.sqrt w * Real.sqrt v * (1 / Real.sqrt W) ≤ A ^ 2 * Real.sqrt U :=
    (mul_le_mul_of_nonneg_right hprod (by positivity)).trans_eq (by field_simp [(Real.sqrt_pos.mpr hW).ne'])
  nlinarith only [Hlog, Ha, HU, HW, mul_le_mul_of_nonneg_right hAA (Real.sqrt_nonneg U),
    mul_nonneg (sq_nonneg A) (Real.sqrt_nonneg W)]

theorem terminal_cone_power_budget {α b U W : ℝ} {J : ℕ} (hJ : 5 ≤ J)
    (hα : 0 < α ∧ α ≤ 1) (hb : 0 < b ∧ b ≤ 1) (hU : 0 ≤ U) (hW : 0 < W)
    (hsum : U + W ≤ b) :
    α ^ (((J : ℝ) - 5) / 2) * W ^ (3 / 4 : ℝ) +
      α ^ ((J : ℝ) / 2 - 19 / 12) * W ^ (7 / 24 : ℝ) ≤ 2 * b ^ (7 / 24 : ℝ) ∧
      Real.sqrt U + Real.sqrt W ≤ 2 * b ^ (7 / 24 : ℝ) := by
  have hJr : (5 : ℝ) ≤ J := by exact_mod_cast hJ
  have hWb : W ≤ b := by linarith only [hsum, hU]
  have hUb : U ≤ b := by linarith only [hsum, hW]
  have h3 : W ^ (3 / 4 : ℝ) ≤ b ^ (7 / 24 : ℝ) :=
    (Real.rpow_le_rpow hW.le hWb (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_ge hb.1 hb.2 (by norm_num))
  have h7 : W ^ (7 / 24 : ℝ) ≤ b ^ (7 / 24 : ℝ) := Real.rpow_le_rpow hW.le hWb (by norm_num)
  have hα1 := Real.rpow_le_one hα.1.le hα.2 (by linarith only [hJr] : 0 ≤ ((J : ℝ) - 5) / 2)
  have hα2 := Real.rpow_le_one hα.1.le hα.2 (by linarith only [hJr] : 0 ≤ (J : ℝ) / 2 - 19 / 12)
  have hs : Real.sqrt b ≤ b ^ (7 / 24 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hb.1 hb.2 (by norm_num)
  constructor
  · have H1 := (mul_le_of_le_one_left (Real.rpow_nonneg hW.le _) hα1).trans h3
    have H2 := (mul_le_of_le_one_left (Real.rpow_nonneg hW.le _) hα2).trans h7
    linarith only [H1, H2]
  · linarith only [(Real.sqrt_le_sqrt hUb).trans hs, (Real.sqrt_le_sqrt hWb).trans hs]

theorem sqrt_wall_ratio_of_scaled_log {x a p α C : ℝ} (hx : 0 < x) (hα : 0 < α)
    (hC : 0 ≤ C) (hp : 3 / (4 * α ^ 2) ≤ |p|)
    (H : α ^ 2 * Real.sqrt x * |a / x| ≤ C) :
    |a| / (Real.sqrt x * |p|) ≤ 2 * C := by
  have hp0 : 0 < |p| := (by positivity : 0 < 3 / (4 * α ^ 2)).trans_le hp
  have hden : 1 / 2 ≤ α ^ 2 * |p| := by
    have H' := (div_le_iff₀ (by positivity : 0 < 4 * α ^ 2)).mp hp
    nlinarith only [H']
  have hcancel : Real.sqrt x * |a / x| = |a| / Real.sqrt x := by
    rw [abs_div, abs_of_pos hx]
    calc
      _ = (Real.sqrt x / x) * |a| := by ring
      _ = (1 / Real.sqrt x) * |a| := by rw [Real.sqrt_div_self']
      _ = _ := by ring
  have Hid : |a| / (Real.sqrt x * |p|) =
      (α ^ 2 * Real.sqrt x * |a / x|) / (α ^ 2 * |p|) := by
    rw [mul_assoc (α ^ 2), hcancel]
    field_simp [hα.ne', hp0.ne', (Real.sqrt_pos.mpr hx).ne']
  rw [Hid]
  exact ((div_le_div_of_nonneg_right H (by positivity)).trans
    (div_le_div_of_nonneg_left hC (by norm_num : (0 : ℝ) < 1 / 2) hden)).trans_eq (by ring)

end BianchiIX

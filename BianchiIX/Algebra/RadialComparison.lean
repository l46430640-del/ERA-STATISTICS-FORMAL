import BianchiIX.Algebra.MatchingPhase

noncomputable section

namespace BianchiIX

/-- Changing the positive axial coordinate changes its Euclidean radius by at most that amount. -/
theorem phaseNorm_sub_le {a b v : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |phaseNorm a v - phaseNorm b v| ≤ |a - b| := by
  have hr := phaseNorm_pos (b := v) ha
  have hR := phaseNorm_pos (b := v) hb
  have hs := add_pos hr hR
  have heq : phaseNorm a v - phaseNorm b v =
      (a - b) * (a + b) / (phaseNorm a v + phaseNorm b v) := by
    apply (eq_div_iff hs.ne').mpr
    nlinarith only [phaseNorm_sq a v, phaseNorm_sq b v]
  have hratio : (a + b) / (phaseNorm a v + phaseNorm b v) ≤ 1 :=
    (div_le_one hs).mpr (add_le_add (phaseNorm_ge ha.le) (phaseNorm_ge hb.le))
  rw [heq, abs_div, abs_mul, abs_of_pos (add_pos ha hb), abs_of_pos hs]
  calc
    _ = |a - b| * ((a + b) / (phaseNorm a v + phaseNorm b v)) := by ring
    _ ≤ |a - b| := mul_le_of_le_one_right (abs_nonneg _) hratio

/-- A coarse radius comparison already preserves the inverse radial derivative scale. -/
theorem radial_ratio_comparison {k q χ r R δ : ℝ}
    (hk : 0 < k) (hq : 0 ≤ q) (hR : 0 < R) (hqR : q ≤ R) (hχ : k / 2 ≤ χ)
    (hδ : 0 ≤ δ) (hr : |r - R| ≤ δ) (hphase : |q - χ| ≤ δ) :
    |q * r / (R * χ) - 1| ≤ 4 * δ / k := by
  have hχ0 : 0 < χ := by linarith
  have hnum : |q * r - R * χ| ≤ 2 * R * δ := by
    calc
      _ = |q * (r - R) + R * (q - χ)| := by congr 1; ring
      _ ≤ |q * (r - R)| + |R * (q - χ)| := abs_add_le _ _
      _ = q * |r - R| + R * |q - χ| := by rw [abs_mul, abs_mul, abs_of_nonneg hq, abs_of_pos hR]
      _ ≤ q * δ + R * δ := add_le_add (mul_le_mul_of_nonneg_left hr hq)
        (mul_le_mul_of_nonneg_left hphase hR.le)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hqR hδ]
  rw [div_sub_one (mul_ne_zero hR.ne' hχ0.ne'), abs_div, abs_of_pos (mul_pos hR hχ0)]
  calc
    _ ≤ (2 * R * δ) / (R * χ) := div_le_div_of_nonneg_right hnum (mul_pos hR hχ0).le
    _ = 2 * δ / χ := by field_simp
    _ ≤ 2 * δ / (k / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hχ
    _ = _ := by ring

theorem radial_correction_derivative_bound {k q χ r R δ σ p : ℝ}
    (hk : 0 < k) (hq : 0 ≤ q) (hR : 0 < R) (hqR : q ≤ R) (hχ : k / 2 ≤ χ)
    (hδ : 0 ≤ δ) (hr : |r - R| ≤ δ) (hphase : |q - χ| ≤ δ)
    (hp : 1 / 2 ≤ p) (hσ : |p - 1| ≤ σ) :
    |1 - q * r / (R * χ * p)| ≤ 2 * σ + 8 * δ / k := by
  have hp0 : 0 < p := by linarith
  have hratio := radial_ratio_comparison hk hq hR hqR hχ hδ hr hphase
  have heq : 1 - q * r / (R * χ * p) =
      ((p - 1) - (q * r / (R * χ) - 1)) / p := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hp0]
  calc
    _ ≤ (|p - 1| + |q * r / (R * χ) - 1|) / p :=
      div_le_div_of_nonneg_right (abs_sub _ _) hp0.le
    _ ≤ 2 * (|p - 1| + |q * r / (R * χ) - 1|) := by
      calc
        _ ≤ (|p - 1| + |q * r / (R * χ) - 1|) / (1 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hp
        _ = _ := by ring
    _ ≤ 2 * (σ + 4 * δ / k) := mul_le_mul_of_nonneg_left (add_le_add hσ hratio) (by norm_num)
    _ = _ := by ring

theorem radial_wall_correction_bound {q R p a : ℝ}
    (hq : 0 ≤ q) (hR : 0 < R) (hqR : q ≤ R) (hp : 1 / 2 ≤ p) :
    |q * a / (R * p)| ≤ 2 * |a| := by
  have hp0 : 0 < p := by linarith
  rw [abs_div, abs_mul, abs_of_nonneg hq, abs_of_pos (mul_pos hR hp0)]
  calc
    _ = (q / R) * (|a| / p) := by ring
    _ ≤ |a| / p := mul_le_of_le_one_left (by positivity) ((div_le_one hR).mpr hqR)
    _ ≤ |a| / (1 / 2) := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hp
    _ = _ := by ring

end BianchiIX

import BianchiIX.Analysis.ConnectionAmplitudeDifferential

noncomputable section

namespace BianchiIX

theorem connection_amplitude_base_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |1 + coupling u v w| ≤ 2 ∧ |connectionStrongClockRate m u v w| ≤ 2 * μ ∧
      |m + connectionStrongClockRate m u v w| ≤ 4 * μ ∧ |v + w - 2 * u| ≤ 3 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hm0 : 0 ≤ m := by linarith only [hμ, (abs_le.mp hm).1]
  have hm1 : m ≤ 9 * μ / 8 := by linarith only [hμ, (abs_le.mp hm).2]
  have hm2 := pow_le_pow_left₀ hm0 hm1 2
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hd : |v - w| ≤ 1 := abs_le.mpr ⟨by linarith only [hv.1, hw.2], by linarith only [hv.2, hw.1]⟩
  have hd2 : (v - w) ^ 2 ≤ 1 := by nlinarith only [sq_abs (v - w), pow_le_pow_left₀ (abs_nonneg _) hd 2]
  have hN : |connectionStrongRate m u v w| ≤ μ ^ 2 := by
    have H := connection_strong_rate_le (v := v) (w := w) hμ hm hu
    rw [abs_le]
    dsimp [connectionStrongRate] at *
    constructor <;> nlinarith only [hm2, hd2, sq_nonneg u, sq_nonneg μ, H]
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have ha : |connectionStrongClockRate m u v w| ≤ 2 * μ := by
    rw [connectionStrongClockRate, abs_div, abs_of_pos hD0]
    apply (div_le_iff₀ hD0).mpr
    have H := mul_le_mul_of_nonneg_left hD hμ0.le
    nlinarith only [hN, H]
  refine ⟨?_, ha, ?_, ?_⟩
  · have hC := connection_coupling_bounds hu.1 hv hw
    apply abs_le.mpr
    constructor <;> nlinarith only [hC.1, hC.2, hu.2, hu2]
  · exact (abs_add_le _ _).trans ((add_le_add (by simpa [abs_of_nonneg hm0] using hm1) ha).trans
      (by linarith only [hμ0]))
  · apply abs_le.mpr
    constructor <;> linarith only [hu.1, hu.2, hv.1, hv.2, hw.1, hw.2]

theorem connectionWeakClockPartials_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionWeakClockPartials m u v w 0| ≤ 64 / μ ^ 2 ∧
    |connectionWeakClockPartials m u v w 1| ≤ 64 * u / μ ∧
    |connectionWeakClockPartials m u v w 2| ≤ 64 * (v ^ 2 / μ ^ 3 + u * v / μ) ∧
    |connectionWeakClockPartials m u v w 3| ≤ 64 * (w ^ 2 / μ ^ 3 + u * w / μ) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hu0 := hu.1
  have hm0 : 0 ≤ m := by linarith only [hμ, (abs_le.mp hm).1]
  have hm1 : |m| ≤ 2 * μ := by rw [abs_of_nonneg hm0]; linarith only [hμ, (abs_le.mp hm).2]
  obtain ⟨hC, _, _, hS⟩ := connection_amplitude_base_bounds hμ hm hu hv hw
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have hD2 : μ ^ 2 / 4 ≤ connectionSpeed m u v w ^ 2 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ μ / 2) hD 2
    nlinarith only [H]
  have hD2pos : 0 < connectionSpeed m u v w ^ 2 := by positivity
  have hf := (matchingPhase_slope_bounds hμ hm hv hw).1
  have hf0 : 0 < matchingPhaseSlope m v w := by linarith only [hf]
  have hvariation := matchingPhase_inverse_weighted_bounds hμ hm hv hw
  have wall_bound (r e : ℝ) (hr : 0 ≤ r) (he : |e| ≤ 3 * r ^ 2 / μ) :
      |(2 * (1 + coupling u v w) * e - 2 * m * u * r) / connectionSpeed m u v w ^ 2| ≤
        64 * (r ^ 2 / μ ^ 3 + u * r / μ) := by
    have H1 : |2 * (1 + coupling u v w) * e| ≤ 12 * r ^ 2 / μ := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hC (by norm_num)) he (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    have H2 : |2 * m * u * r| ≤ 4 * μ * u * r := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hu.1, abs_of_nonneg hr]
      have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm1 (by norm_num : (0 : ℝ) ≤ 2)) hu.1) hr
      nlinarith only [H]
    have H := (abs_sub _ _).trans (add_le_add H1 H2)
    rw [abs_div, abs_of_pos hD2pos]
    calc
      _ ≤ (12 * r ^ 2 / μ + 4 * μ * u * r) / (μ ^ 2 / 4) :=
        div_le_div₀ (by positivity) H (by positivity) hD2
      _ = 48 * (r ^ 2 / μ ^ 3) + 16 * (u * r / μ) := by field_simp; ring
      _ ≤ 64 * (r ^ 2 / μ ^ 3 + u * r / μ) := by
        have H3 : 0 ≤ r ^ 2 / μ ^ 3 := by positivity
        have H4 : 0 ≤ u * r / μ := by positivity
        linarith only [H3, H4]
  refine ⟨?_, ?_, wall_bound v _ hv.1 hvariation.2.1, wall_bound w _ hw.1 hvariation.2.2⟩
  · have H : μ ^ 2 / 8 ≤ connectionSpeed m u v w ^ 2 * matchingPhaseSlope m v w := by
      have H' := mul_le_mul hD2 hf (by norm_num : (0 : ℝ) ≤ 3 / 4) hD2pos.le
      nlinarith only [H', sq_nonneg μ]
    change |2 * (1 + coupling u v w) / (connectionSpeed m u v w ^ 2 * matchingPhaseSlope m v w)| ≤ _
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (mul_pos hD2pos hf0)]
    calc
      _ ≤ 4 / (μ ^ 2 / 8) := div_le_div₀ (by positivity) (by linarith only [hC]) (by positivity) H
      _ = 32 / μ ^ 2 := by ring
      _ ≤ 64 / μ ^ 2 := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg μ)
  · change |-(2 * m * u * (v + w - 2 * u)) / connectionSpeed m u v w ^ 2| ≤ _
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg hu.1, abs_of_pos hD2pos]
    have H := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm1 (by norm_num)) hu.1)
      hS (abs_nonneg _) (by positivity : 0 ≤ 2 * (2 * μ) * u)
    calc
      _ ≤ (2 * (2 * μ) * u * 3) / (μ ^ 2 / 4) := div_le_div₀ (by positivity) H (by positivity) hD2
      _ = 48 * u / μ := by field_simp; ring
      _ ≤ 64 * u / μ := div_le_div_of_nonneg_right (by nlinarith only [hu.1]) hμ0.le

theorem connectionStrongClockPartials_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionStrongClockPartials m u v w 0| ≤ 32 ∧
    |connectionStrongClockPartials m u v w 1| ≤ 32 * u ∧
    |connectionStrongClockPartials m u v w 2| ≤ 32 * ((v ^ 2 + v * w) / μ + u * v) ∧
    |connectionStrongClockPartials m u v w 3| ≤ 32 * ((w ^ 2 + v * w) / μ + u * w) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hu0 := hu.1
  obtain ⟨_, ha, hma, hS⟩ := connection_amplitude_base_bounds hμ hm hu hv hw
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have hf := (matchingPhase_slope_bounds hμ hm hv hw).1
  have hf0 : 0 < matchingPhaseSlope m v w := by linarith only [hf]
  have hvariation := matchingPhase_inverse_weighted_bounds hμ hm hv hw
  have wall_bound (r s e : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (he : |e| ≤ 3 * r ^ 2 / μ) :
      |(-(m + connectionStrongClockRate m u v w) * e + r * (s - r) +
        connectionStrongClockRate m u v w * u * r) / connectionSpeed m u v w| ≤
        32 * ((r ^ 2 + r * s) / μ + u * r) := by
    have H1 : |-(m + connectionStrongClockRate m u v w) * e| ≤ 12 * r ^ 2 := by
      rw [abs_mul, abs_neg]
      exact (mul_le_mul hma he (abs_nonneg _) (by positivity)).trans_eq (by field_simp; ring)
    have H2 : |r * (s - r)| ≤ r * (s + r) := by
      rw [abs_mul, abs_of_nonneg hr]
      apply mul_le_mul_of_nonneg_left _ hr
      simpa only [abs_of_nonneg hr, abs_of_nonneg hs] using abs_sub s r
    have H3 : |connectionStrongClockRate m u v w * u * r| ≤ 2 * μ * u * r := by
      rw [abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_nonneg hr]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hu0) hr
    have H := ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add H1 H2) H3)
    rw [abs_div, abs_of_pos hD0]
    calc
      _ ≤ (12 * r ^ 2 + r * (s + r) + 2 * μ * u * r) / (μ / 2) :=
        div_le_div₀ (by positivity) H (by positivity) hD
      _ = 26 * (r ^ 2 / μ) + 2 * (r * s / μ) + 4 * (u * r) := by field_simp; ring
      _ ≤ 32 * ((r ^ 2 + r * s) / μ + u * r) := by
        rw [add_div]
        have H4 : 0 ≤ r ^ 2 / μ := by positivity
        have H5 : 0 ≤ r * s / μ := by positivity
        have H6 : 0 ≤ u * r := by positivity
        linarith only [H4, H5, H6]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have H : μ / 4 ≤ connectionSpeed m u v w * matchingPhaseSlope m v w := by
      have H' := mul_le_mul hD hf (by norm_num : (0 : ℝ) ≤ 3 / 4) hD0.le
      nlinarith only [H', hμ0]
    change |-(m + connectionStrongClockRate m u v w) / (connectionSpeed m u v w * matchingPhaseSlope m v w)| ≤ _
    rw [abs_div, abs_neg, abs_of_pos (mul_pos hD0 hf0)]
    calc
      _ ≤ (4 * μ) / (μ / 4) := div_le_div₀ (by positivity) hma (by positivity) H
      _ = 16 := by field_simp; ring
      _ ≤ 32 := by norm_num
  · have H1 : u ^ 2 ≤ μ * u := by
      have H := mul_le_mul_of_nonneg_right (show u ≤ μ by linarith only [hu.2, hμ]) hu0
      nlinarith only [H]
    have H2 : |connectionStrongClockRate m u v w * u * (v + w - 2 * u)| ≤ 6 * μ * u := by
      rw [abs_mul, abs_mul, abs_of_nonneg hu0]
      exact (mul_le_mul (mul_le_mul_of_nonneg_right ha hu0) hS (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have H := (abs_add_le (u ^ 2) (connectionStrongClockRate m u v w * u * (v + w - 2 * u))).trans
      (add_le_add (by simpa only [abs_of_nonneg (sq_nonneg u)] using H1) H2)
    change |(u ^ 2 + connectionStrongClockRate m u v w * u * (v + w - 2 * u)) / connectionSpeed m u v w| ≤ _
    rw [abs_div, abs_of_pos hD0]
    calc
      _ ≤ (μ * u + 6 * μ * u) / (μ / 2) := div_le_div₀ (by positivity) H (by positivity) hD
      _ = 14 * u := by field_simp; ring
      _ ≤ 32 * u := by linarith only [hu0]
  · have hid : connectionStrongClockPartials m u v w 2 =
        (-(m + connectionStrongClockRate m u v w) * matchingPhaseVVariation m v w +
          v * (w - v) + connectionStrongClockRate m u v w * u * v) / connectionSpeed m u v w := by
      dsimp [connectionStrongClockPartials]
      ring
    rw [hid]
    exact wall_bound v w _ hv.1 hw.1 hvariation.2.1
  · exact (wall_bound w v _ hw.1 hv.1 hvariation.2.2).trans_eq (by rw [mul_comm w v])

end BianchiIX

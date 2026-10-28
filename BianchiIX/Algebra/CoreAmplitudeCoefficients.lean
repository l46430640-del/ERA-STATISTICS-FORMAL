import BianchiIX.Algebra.CoreCoefficientEstimates

noncomputable section

namespace BianchiIX

/-- Quadratic wall terms retain the strong amplitude and the square of the weak amplitude. -/
theorem core_wall_quadratic_bounds {m u w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m) :
    |u - w| * |u - 2 * w| ≤ 4 * m * u + 2 * w ^ 2 ∧
    |u - w| * |3 * w - u| ≤ 5 * m * u + 3 * w ^ 2 := by
  have hδ : |u - w| ≤ u + w := by
    simpa only [abs_of_nonneg hu.1, abs_of_nonneg hw.1] using abs_sub u w
  have h2 : |u - 2 * w| ≤ u + 2 * w := by
    calc
      _ ≤ |u| + |2 * w| := abs_sub _ _
      _ = u + 2 * w := by rw [abs_of_nonneg hu.1, abs_of_nonneg (mul_nonneg (by norm_num) hw.1)]
  have h3 : |3 * w - u| ≤ u + 3 * w := by
    calc
      _ ≤ |3 * w| + |u| := abs_sub _ _
      _ = u + 3 * w := by rw [abs_of_nonneg hu.1, abs_of_nonneg (mul_nonneg (by norm_num) hw.1)]; ring
  have hu2 := mul_le_mul_of_nonneg_left hu.2 hu.1
  have huw := mul_le_mul_of_nonneg_left hw.2 hu.1
  constructor
  · have H := mul_le_mul hδ h2 (abs_nonneg _) (add_nonneg hu.1 hw.1)
    nlinarith only [H, hu2, huw]
  · have H := mul_le_mul hδ h3 (abs_nonneg _) (add_nonneg hu.1 hw.1)
    nlinarith only [H, hu2, huw]

theorem core_amplitude_clock_products {r m u w g : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hg : |g| ≤ 2 * r * m) :
    |g * (2 * (u - w) * (u - 2 * w) / r ^ 3)| ≤ (u + w ^ 2 / r ^ 2) / 10 ∧
    |g * (-2 * (u - w) / r ^ 2)| ≤ (u + w / r) / 10 := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr0
  have hm0 := hm.1
  have hu0 := hu.1
  have hw0 := hw.1
  have hm2 : m ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := (sq_le_sq₀ hm.1 (by norm_num)).mpr hm.2
  have hδ : |u - w| ≤ u + w := by
    calc
      _ ≤ |u| + |w| := abs_sub _ _
      _ = u + w := by rw [abs_of_nonneg hu.1, abs_of_nonneg hw.1]
  have hucoef : 16 * m ^ 2 / r ^ 2 ≤ 1 / 10 := by
    apply (div_le_iff₀ hr2).mpr
    nlinarith only [hm2, hr, sq_nonneg (r - 5)]
  have hwcoef : 8 * m ≤ 1 / 10 := by linarith only [hm.2]
  have h4m : 4 * m ≤ 1 / 10 := by linarith only [hm.2]
  have h4mr : 4 * m / r ≤ 1 / 10 := by
    apply (div_le_iff₀ hr0).mpr
    linarith only [hr, hm.2]
  constructor
  · calc
      _ = |g| * (2 * (|u - w| * |u - 2 * w|) / r ^ 3) := by
        simp only [abs_mul, abs_div, abs_pow, abs_of_pos hr0, show |(2 : ℝ)| = 2 by norm_num]
        ring
      _ ≤ (2 * r * m) * (2 * (4 * m * u + 2 * w ^ 2) / r ^ 3) := by
        apply mul_le_mul hg ?_ (by positivity) (by positivity)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (core_wall_quadratic_bounds hu hw).1 (by norm_num)) (by positivity)
      _ = (16 * m ^ 2 / r ^ 2) * u + (8 * m) * (w ^ 2 / r ^ 2) := by field_simp; ring
      _ ≤ (1 / 10) * u + (1 / 10) * (w ^ 2 / r ^ 2) := by gcongr
      _ = (u + w ^ 2 / r ^ 2) / 10 := by ring
  · calc
      _ = |g| * (2 * |u - w| / r ^ 2) := by
        simp [abs_mul, abs_div, abs_pow, abs_of_pos hr0]
      _ ≤ (2 * r * m) * (2 * (u + w) / r ^ 2) := by
        apply mul_le_mul hg ?_ (by positivity) (by positivity)
        gcongr
      _ = (4 * m / r) * u + (4 * m) * (w / r) := by field_simp; ring
      _ ≤ (1 / 10) * u + (1 / 10) * (w / r) := by gcongr
      _ = (u + w / r) / 10 := by ring

/-- Radius-row numerators with the weak wall kept at its correct power and scale. -/
theorem core_amplitude_radius_numerators {r m u v w s c : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 1 ≤ v ∧ v ≤ r) (hs : 0 ≤ s ∧ s ≤ 1) (hc : |c| ≤ 1) :
    |-u * (s - w / r) + c * (u - w) * (3 * w - u) / r ^ 2| ≤ 2 * u + 3 * w ^ 2 / r ^ 2 ∧
    |(-(v - 2 * u + w) + 2 * c * (u - w) / r) + v - v * (1 - coreClockFactor r u w)| ≤
      4 * (u + w) ∧
    |v * (-u / v - 2 * c * (u - w) / (r * v))| ≤ 2 * (u + w / r) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hv0 : 0 < v := by linarith only [hv.1]
  have hδ : |u - w| ≤ u + w := by
    calc
      _ ≤ |u| + |w| := abs_sub _ _
      _ = u + w := by rw [abs_of_nonneg hu.1, abs_of_nonneg hw.1]
  have hδm := (core_wall_difference_bounds hu hw).1
  have hδ2 : (u - w) ^ 2 ≤ m * (u + w) := by
    have H := mul_le_mul hδm hδ (abs_nonneg _) hm.1
    simpa only [← sq, sq_abs] using H
  have hcd : |c| * |u - w| ≤ u + w := (mul_le_of_le_one_left (abs_nonneg _) hc).trans hδ
  have hterm : |2 * c * (u - w) / r| ≤ 2 * (u + w) / r := by
    simp only [abs_div, abs_mul, abs_of_pos hr0]
    norm_num
    exact div_le_div_of_nonneg_right (by linarith only [hcd]) hr0.le
  have hterm' : |2 * c * (u - w) / r| ≤ u + w := by
    apply hterm.trans
    apply (div_le_iff₀ hr0).mpr
    nlinarith only [mul_nonneg (add_nonneg hu.1 hw.1) (show 0 ≤ r - 2 by linarith only [hr])]
  have hclock : |v * (1 - coreClockFactor r u w)| ≤ u + w := by
    have hid : 1 - coreClockFactor r u w = (u - w) ^ 2 / r ^ 2 := by unfold coreClockFactor; ring
    rw [hid, abs_of_nonneg (by positivity)]
    calc
      _ ≤ r * (m * (u + w) / r ^ 2) := mul_le_mul hv.2
        (div_le_div_of_nonneg_right hδ2 (sq_nonneg _)) (by positivity) hr0.le
      _ = (m / r) * (u + w) := by field_simp
      _ ≤ u + w := mul_le_of_le_one_left (add_nonneg hu.1 hw.1)
        ((div_le_one hr0).mpr (by linarith only [hm.2, hr]))
  constructor
  · have hcoupling := (core_small_coupling_derivatives hr hm hu hw hv hs).1
    have hsecond : |c * (u - w) * (3 * w - u) / r ^ 2| ≤
        u + 3 * w ^ 2 / r ^ 2 := by
      calc
        _ = |c| * (|u - w| * |3 * w - u|) / r ^ 2 := by
          simp [abs_mul, abs_div, abs_pow, abs_of_pos hr0]
          ring
        _ ≤ (5 * m * u + 3 * w ^ 2) / r ^ 2 := div_le_div_of_nonneg_right
          ((mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hc).trans
            (core_wall_quadratic_bounds hu hw).2) (sq_nonneg _)
        _ ≤ u + 3 * w ^ 2 / r ^ 2 := by
          have hcoeff : 5 * m / r ^ 2 ≤ 1 := by
            apply (div_le_one (sq_pos_of_pos hr0)).mpr
            nlinarith only [hr, hm.2, sq_nonneg (r - 5)]
          calc
            _ = (5 * m / r ^ 2) * u + 3 * w ^ 2 / r ^ 2 := by ring
            _ ≤ u + 3 * w ^ 2 / r ^ 2 := add_le_add (mul_le_of_le_one_left hu.1 hcoeff) (le_refl _)
    have H := abs_add_le (-u * (s - w / r)) (c * (u - w) * (3 * w - u) / r ^ 2)
    have hfirst : |-u * (s - w / r)| ≤ u := by simpa only [neg_mul, abs_neg] using hcoupling
    linarith only [H, hfirst, hsecond]
  constructor
  · rw [show -(v - 2 * u + w) + 2 * c * (u - w) / r + v =
      (2 * u - w) + 2 * c * (u - w) / r by ring]
    have hfirst : |2 * u - w| ≤ 2 * (u + w) := by
      apply abs_le.mpr
      constructor <;> linarith only [hu.1, hw.1]
    have H := abs_sub ((2 * u - w) + 2 * c * (u - w) / r) (v * (1 - coreClockFactor r u w))
    have H' := abs_add_le (2 * u - w) (2 * c * (u - w) / r)
    linarith only [H, H', hfirst, hterm', hclock]
  · rw [show v * (-u / v - 2 * c * (u - w) / (r * v)) = -u - 2 * c * (u - w) / r by field_simp]
    have H := abs_sub (-u) (2 * c * (u - w) / r)
    rw [abs_neg, abs_of_nonneg hu.1] at H
    have hU : 2 * u / r ≤ u := by
      apply (div_le_iff₀ hr0).mpr
      nlinarith only [mul_nonneg hu.1 (show 0 ≤ r - 2 by linarith only [hr])]
    rw [mul_add, add_div] at hterm
    rw [show 2 * w / r = 2 * (w / r) by ring] at hterm
    linarith only [H, hterm, hU]

end BianchiIX

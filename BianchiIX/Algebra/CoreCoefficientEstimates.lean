import BianchiIX.Algebra.CoreBounds

noncomputable section

namespace BianchiIX

theorem coreBootstrap_coefficient_scales {k r : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ r ∧ r ≤ 101 / 100 * k) :
    let m := (1 / 10000) / k
    5 ≤ r ∧ 0 ≤ m ∧ m ≤ 1 / 100 ∧ r * m ≤ 1 / 1000 ∧
    m / r ≤ 1 / 100 ∧ k / r ≤ 3 / 2 ∧ k ^ 2 / r ^ 2 ≤ 3 / 2 ∧
    4 * m ^ 2 / r ≤ m / 10 := by
  let m := (1 / 10000) / k
  have hk0 : 0 < k := by linarith
  have hr5 : 5 ≤ r := by linarith [hr.1]
  have hr0 : 0 < r := by linarith
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hm : m ≤ 1 / 100 := (div_le_iff₀ hk0).mpr (by linarith)
  have hrm : r * m ≤ 1 / 1000 := by
    dsimp [m]
    rw [← mul_div_assoc, div_le_iff₀ hk0]
    linarith [hr.2]
  have hmr : m / r ≤ 1 / 100 := (div_le_iff₀ hr0).mpr (by linarith)
  refine ⟨hr5, hm0, hm, hrm, hmr,
    (div_le_iff₀ hr0).mpr (by linarith [hr.1]),
    (div_le_iff₀ (sq_pos_of_pos hr0)).mpr ?_, ?_⟩
  · have H := (sq_le_sq₀ (show 0 ≤ 99 / 100 * k by positivity) hr0.le).mpr hr.1
    nlinarith
  · have H := mul_le_mul_of_nonneg_left hmr hm0
    calc
      4 * m ^ 2 / r = 4 * (m * (m / r)) := by ring
      _ ≤ m / 10 := by nlinarith

theorem core_wall_difference_bounds {m u w : ℝ} (hu : 0 ≤ u ∧ u ≤ m)
    (hw : 0 ≤ w ∧ w ≤ m) :
    |u - w| ≤ m ∧ |u - 2 * w| ≤ 2 * m ∧ |3 * w - u| ≤ 3 * m ∧ |2 * u - w| ≤ 2 * m := by
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem core_small_coupling {r m u v w : ℝ}
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hrm : r * m ≤ 1 / 1000)
    (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m) (hv : 1 ≤ v ∧ v ≤ r) :
    0 ≤ coupling u v w ∧ coupling u v w ≤ r * m + m ^ 2 ∧ coupling u v w ≤ 1 / 100 := by
  have hC0 : 0 ≤ coupling u v w := mul_nonneg hu.1 (by linarith [hm.2, hv.1])
  have hC : coupling u v w ≤ m * (r + m) := by
    unfold coupling
    apply mul_le_mul hu.2 (by linarith [hv.2]) (by linarith [hm.2, hv.1]) hm.1
  have hm2 : m ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := (sq_le_sq₀ hm.1 (by norm_num)).mpr hm.2
  exact ⟨hC0, by nlinarith, by nlinarith⟩

theorem core_small_numerators {r m u v w s c : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hrm : r * m ≤ 1 / 1000)
    (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m) (hv : 1 ≤ v ∧ v ≤ r)
    (hs : 0 ≤ s ∧ s ≤ 1) (hc : |c| ≤ 1) :
    |-r / 2 - c + s * w + (u ^ 2 - w ^ 2) / (2 * r)| ≤ r ∧
    |-coupling u v w + c * (u - w) ^ 2 / r| ≤ 2 * r * m := by
  have hr0 : 0 < r := by linarith
  have hu2 : u ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ hu.1 (by norm_num)).mpr (hu.2.trans hm.2)
  have hw2 : w ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ hw.1 (by norm_num)).mpr (hw.2.trans hm.2)
  have hsw : 0 ≤ s * w ∧ s * w ≤ m :=
    ⟨mul_nonneg hs.1 hw.1, (mul_le_of_le_one_left hw.1 hs.2).trans hw.2⟩
  have he : |(u ^ 2 - w ^ 2) / (2 * r)| ≤ 1 / 100 := by
    rw [abs_div, abs_of_pos (show 0 < 2 * r by positivity), div_le_iff₀ (by positivity)]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg u, sq_nonneg w]
  constructor
  · have H := abs_add_le (-r / 2 - c + s * w) ((u ^ 2 - w ^ 2) / (2 * r))
    have H' := abs_add_le (-r / 2 - c) (s * w)
    have H'' := abs_sub (-r / 2) c
    have hhalf : |(-r / 2)| = r / 2 := by rw [abs_div, abs_neg, abs_of_pos hr0]; norm_num
    rw [hhalf] at H''
    rw [abs_of_nonneg hsw.1] at H'
    linarith [hm.2]
  · obtain ⟨hC0, hC, _⟩ := core_small_coupling hm hrm hu hw hv
    have hdelta := (core_wall_difference_bounds hu hw).1
    have hdelta2 : (u - w) ^ 2 ≤ m ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hm.1).mpr hdelta
    have he' : |c * (u - w) ^ 2 / r| ≤ m ^ 2 / r := by
      simp only [abs_div, abs_mul, abs_of_pos hr0, abs_of_nonneg (sq_nonneg (u - w))]
      exact div_le_div_of_nonneg_right
        ((mul_le_of_le_one_left (sq_nonneg _) hc).trans hdelta2) hr0.le
    have he'' : m ^ 2 / r ≤ m ^ 2 := div_le_self (sq_nonneg _) (by linarith)
    have H := abs_add_le (-coupling u v w) (c * (u - w) ^ 2 / r)
    rw [abs_neg, abs_of_nonneg hC0] at H
    have hsmall : 2 * m ^ 2 ≤ r * m := by nlinarith [mul_nonneg hm.1 (show 0 ≤ r - 2 * m by linarith [hm.2])]
    linarith

theorem core_small_clock_derivatives {r m u w v : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 0 < v) :
    |2 * (u - w) * (u - 2 * w) / r ^ 3| ≤ m / r ^ 2 ∧
    |-2 * (u - w) / r ^ 2| ≤ 2 * m / r ^ 2 ∧
    |2 * (u - w) / (v * r ^ 2)| ≤ 2 * m / (v * r ^ 2) := by
  have hr0 : 0 < r := by linarith
  obtain ⟨hδ, h2, _, _⟩ := core_wall_difference_bounds hu hw
  have hnum : 2 * |u - w| * |u - 2 * w| ≤ 4 * m ^ 2 := by
    have H := mul_le_mul hδ h2 (abs_nonneg _) hm.1
    nlinarith
  have hfactor : 4 * m / r ≤ 1 := (div_le_one hr0).mpr (by linarith [hm.2])
  constructor
  · calc
      |2 * (u - w) * (u - 2 * w) / r ^ 3| = 2 * |u - w| * |u - 2 * w| / r ^ 3 := by
        simp [abs_mul, abs_div, abs_pow, abs_of_pos hr0]
      _ ≤ 4 * m ^ 2 / r ^ 3 := div_le_div_of_nonneg_right hnum (by positivity)
      _ = (m / r ^ 2) * (4 * m / r) := by ring
      _ ≤ m / r ^ 2 := mul_le_of_le_one_right (div_nonneg hm.1 (sq_nonneg _)) hfactor
  constructor
  · simp only [abs_div, abs_mul, abs_pow, abs_of_pos hr0]
    norm_num
    gcongr
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos hv (sq_pos_of_pos hr0))]
    norm_num
    gcongr

theorem core_small_coupling_derivatives {r m u v w s : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 1 ≤ v ∧ v ≤ r) (hs : 0 ≤ s ∧ s ≤ 1) :
    |u * (s - w / r)| ≤ u ∧ |v - 2 * u + w| ≤ 2 * r := by
  have hr0 : 0 < r := by linarith
  have hwr : 0 ≤ w / r ∧ w / r ≤ 1 :=
    ⟨div_nonneg hw.1 hr0.le, (div_le_one hr0).mpr (by linarith [hw.2, hm.2])⟩
  have hdiff : |s - w / r| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  constructor
  · rw [abs_mul, abs_of_nonneg hu.1]
    exact mul_le_of_le_one_right hu.1 hdiff
  · apply abs_le.mpr
    constructor <;> linarith [hv.1, hv.2, hm.2]

theorem core_small_strong_derivatives {r m u v w s : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 1 ≤ v) (hs : 0 ≤ s ∧ s ≤ 1) :
    |-1 / 2 - s * w / r + (3 * w ^ 2 - u ^ 2) / (2 * r ^ 2)| ≤ 3 / 4 ∧
    |(1 - w / v) / r| ≤ 1 / r := by
  have hr0 : 0 < r := by linarith
  have hv0 : 0 < v := by linarith
  have hu2 : u ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ hu.1 (by norm_num)).mpr (hu.2.trans hm.2)
  have hw2 : w ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ hw.1 (by norm_num)).mpr (hw.2.trans hm.2)
  have hsw : 0 ≤ s * w ∧ s * w ≤ 1 / 100 :=
    ⟨mul_nonneg hs.1 hw.1, ((mul_le_of_le_one_left hw.1 hs.2).trans hw.2).trans hm.2⟩
  have hfirst : |s * w / r| ≤ 1 / 100 := by
    rw [abs_of_nonneg (div_nonneg hsw.1 hr0.le)]
    exact (div_le_self hsw.1 (by linarith)).trans hsw.2
  have hsecond : |(3 * w ^ 2 - u ^ 2) / (2 * r ^ 2)| ≤ 1 / 100 := by
    rw [abs_div, abs_of_pos (show 0 < 2 * r ^ 2 by positivity), div_le_iff₀ (by positivity)]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (r - 5), sq_nonneg u, sq_nonneg w]
  constructor
  · have H := abs_add_le (-1 / 2 - s * w / r) ((3 * w ^ 2 - u ^ 2) / (2 * r ^ 2))
    have H' := abs_sub (-1 / 2 : ℝ) (s * w / r)
    norm_num at H'
    linarith
  · rw [abs_div, abs_of_pos hr0]
    apply div_le_div_of_nonneg_right _ hr0.le
    apply abs_le.mpr
    have hwr : 0 ≤ w / v ∧ w / v ≤ 1 :=
      ⟨div_nonneg hw.1 hv0.le, (div_le_one hv0).mpr (by linarith [hw.2, hm.2])⟩
    constructor <;> linarith

theorem core_small_radius_derivatives {r m u v w s c : ℝ} (hr : 5 ≤ r)
    (hm : 0 ≤ m ∧ m ≤ 1 / 100) (hu : 0 ≤ u ∧ u ≤ m) (hw : 0 ≤ w ∧ w ≤ m)
    (hv : 1 ≤ v ∧ v ≤ r) (hs : 0 ≤ s ∧ s ≤ 1) (hc : |c| ≤ 1) :
    |-u * (s - w / r) + c * (u - w) * (3 * w - u) / r ^ 2| ≤ 2 * m ∧
    |(-(v - 2 * u + w) + 2 * c * (u - w) / r) + v| ≤ 3 * m ∧
    |-u / v - 2 * c * (u - w) / (r * v)| ≤ 2 * m / v := by
  have hr0 : 0 < r := by linarith
  have hv0 : 0 < v := by linarith [hv.1]
  obtain ⟨hδ, _, h3, h2⟩ := core_wall_difference_bounds hu hw
  have hcd : |c| * |u - w| ≤ m := (mul_le_of_le_one_left (abs_nonneg _) hc).trans hδ
  have hnum : |c| * |u - w| * |3 * w - u| ≤ 3 * m ^ 2 := by
    have H := mul_le_mul hcd h3 (abs_nonneg _) hm.1
    nlinarith
  have hCR := (core_small_coupling_derivatives hr hm hu hw hv hs).1
  have he : |c * (u - w) * (3 * w - u) / r ^ 2| ≤ m := by
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_of_pos hr0]
    apply (div_le_iff₀ (sq_pos_of_pos hr0)).mpr
    have H : 3 * m ^ 2 ≤ m * r ^ 2 := by
      have H' : 3 * m ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 5), hm.2]
      nlinarith [mul_nonneg hm.1 (sub_nonneg.mpr H')]
    exact hnum.trans H
  have he' : |2 * c * (u - w) / r| ≤ m := by
    simp only [abs_div, abs_mul, abs_of_pos hr0]
    norm_num
    apply (div_le_iff₀ hr0).mpr
    nlinarith [mul_nonneg hm.1 (show 0 ≤ r - 2 by linarith)]
  have he'' : |2 * c * (u - w) / (r * v)| ≤ m / v := by
    rw [← div_div, abs_div, abs_of_pos hv0]
    exact div_le_div_of_nonneg_right he' hv0.le
  constructor
  · have H := abs_add_le (-u * (s - w / r)) (c * (u - w) * (3 * w - u) / r ^ 2)
    have H' : |-u * (s - w / r)| ≤ u := by simpa only [neg_mul, abs_neg] using hCR
    linarith [hu.2]
  constructor
  · rw [show -(v - 2 * u + w) + 2 * c * (u - w) / r + v =
      (2 * u - w) + 2 * c * (u - w) / r by ring]
    have H := abs_add_le (2 * u - w) (2 * c * (u - w) / r)
    linarith
  · have H := abs_sub (-u / v) (2 * c * (u - w) / (r * v))
    have H' : |(-u / v)| ≤ m / v := by
      rw [abs_div, abs_neg, abs_of_nonneg hu.1, abs_of_pos hv0]
      exact div_le_div_of_nonneg_right hu.2 hv0.le
    calc
      _ ≤ m / v + m / v := H.trans (add_le_add H' he'')
      _ = 2 * m / v := by ring

theorem core_clock_quotient_bound {d x y A B : ℝ} (hd : 999 / 1000 ≤ d)
    (hx : |x| ≤ A) (hy : |y| ≤ B) : |x / d - y / d ^ 2| ≤ 3 / 2 * A + 2 * B := by
  have hd0 : 0 < d := by linarith
  have hA : 0 ≤ A := (abs_nonneg _).trans hx
  have hB : 0 ≤ B := (abs_nonneg _).trans hy
  have hdx : |x / d| ≤ 3 / 2 * A := by
    rw [abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    nlinarith [mul_nonneg hA (show 0 ≤ d - 2 / 3 by linarith)]
  have hdy : |y / d ^ 2| ≤ 2 * B := by
    rw [abs_div, abs_pow, abs_of_pos hd0, div_le_iff₀ (sq_pos_of_pos hd0)]
    have hsq : 1 / 2 ≤ d ^ 2 := by nlinarith
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hsq)]
  exact (abs_sub _ _).trans (add_le_add hdx hdy)

end BianchiIX

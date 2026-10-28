import BianchiIX.Analysis.ConnectionPhaseNumeratorBounds

noncomputable section

namespace BianchiIX

theorem connectionPhaseA_wall_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseA m u v w| ≤ 8 ∧
    |connectionPhaseAPartials m u v w 1| ≤ 16 * u ∧
    |connectionPhaseAPartials m u v w 2| ≤ 16 * v ∧
    |connectionPhaseAPartials m u v w 3| ≤ 16 * w := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hu0 := hu.1
  have hu1 : u ≤ 1 := by linarith only [hu.2]
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hN := connectionPhaseNumerator_bounds hμ hm hu hv hw
  have hvar := matchingPhase_inverse_weighted_bounds hμ hm hv hw
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hD0 : 0 < connectionSpeed m u v w := by linarith only [hD, hμ0]
  have div_bound (x K : ℝ) (hx : |x| ≤ K) : |x / connectionSpeed m u v w| ≤ 2 * K / μ := by
    rw [abs_div, abs_of_pos hD0]
    exact (div_le_div₀ ((abs_nonneg x).trans hx) hx (by positivity) hD).trans_eq (by ring)
  have hA : |connectionPhaseA m u v w| ≤ 8 := by
    change |-connectionPhaseNumerator m u v w / connectionSpeed m u v w| ≤ _
    exact (div_bound _ _ (by simpa only [abs_neg] using hN.1)).trans_eq (by field_simp; norm_num)
  have column (n e K L : ℝ) (hn : |n| ≤ K) (he : |e| ≤ L) :
      |-n / connectionSpeed m u v w - connectionPhaseA m u v w * e / connectionSpeed m u v w| ≤
        2 * (K + 8 * L) / μ := by
    have H : |connectionPhaseA m u v w * e| ≤ 8 * L := by
      rw [abs_mul]
      exact mul_le_mul hA he (abs_nonneg _) (by norm_num)
    exact ((abs_sub _ _).trans (add_le_add (div_bound _ _ (by simpa only [abs_neg] using hn))
      (div_bound _ _ H))).trans_eq (by ring)
  have wall_bound (r n e : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (hn : |n| ≤ 3 * μ * r)
      (he : |e| ≤ 3 * r ^ 2 / μ) :
      |-n / connectionSpeed m u v w - connectionPhaseA m u v w * (e - u * r) / connectionSpeed m u v w| ≤ 16 * r := by
    have he' : |e - u * r| ≤ 3 * r ^ 2 / μ + u * r := by
      simpa only [abs_of_nonneg (mul_nonneg hu0 hr.1)] using (abs_sub e (u * r)).trans (add_le_add he le_rfl)
    have hr2 : r ^ 2 ≤ r := by nlinarith only [mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]
    have H1 : r ^ 2 / μ ^ 2 ≤ r / 16 := div_le_div₀ hr.1 hr2 (by norm_num) hμ2
    have H2 : u * r / μ ≤ r / 4 := div_le_div₀ hr.1
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hu1 hr.1) (by norm_num) hμ
    calc
      _ ≤ 2 * (3 * μ * r + 8 * (3 * r ^ 2 / μ + u * r)) / μ := column _ _ _ _ hn he'
      _ = 6 * r + 48 * (r ^ 2 / μ ^ 2) + 16 * (u * r / μ) := by field_simp; ring
      _ ≤ 16 * r := by linarith only [H1, H2, hr.1]
  refine ⟨hA, ?_, wall_bound v _ _ hv hN.2.2.1 hvar.2.1, wall_bound w _ _ hw hN.2.2.2 hvar.2.2⟩
  · have hS := (connection_amplitude_base_bounds hμ hm hu hv hw).2.2.2
    have he : |-u * (v + w - 2 * u)| ≤ 3 * u := by
      rw [abs_mul, abs_neg, abs_of_nonneg hu0]
      exact (mul_le_mul_of_nonneg_left hS hu0).trans_eq (by ring)
    have H : u / μ ≤ u / 4 := div_le_div_of_nonneg_left hu0 (by norm_num) hμ
    calc
      _ ≤ 2 * (3 * μ / 2 * u + 8 * (3 * u)) / μ := column _ _ _ _ hN.2.1 he
      _ = 3 * u + 48 * (u / μ) := by field_simp; ring
      _ ≤ 16 * u := by linarith only [H, hu0]

end BianchiIX

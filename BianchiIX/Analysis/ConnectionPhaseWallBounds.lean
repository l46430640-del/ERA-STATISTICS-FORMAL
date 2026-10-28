import BianchiIX.Analysis.ConnectionPhaseAWallBounds
import BianchiIX.Analysis.ConnectionPhaseLinearization

noncomputable section

namespace BianchiIX

theorem connectionPhaseGPartials_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseGPartials m u v w 0| ≤ 64 * (u / μ ^ 2 + (v * w) ^ 2 / μ ^ 4) ∧
    |connectionPhaseGPartials m u v w 1| ≤ 32 * u ∧
    |connectionPhaseGPartials m u v w 2| ≤ 32 * (u * v + (v * w) ^ 2 / μ ^ 3) ∧
    |connectionPhaseGPartials m u v w 3| ≤ 32 * (u * w + (v * w) ^ 2 / μ ^ 3) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hu0 := hu.1
  have hu1 : u ≤ 1 := by linarith only [hu.2]
  have hu2 : u ^ 2 ≤ u := by nlinarith only [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hμ4 : 36 ≤ μ ^ 4 := by
    have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hμ 4
    norm_num at H
    linarith only [H]
  have hA := connectionPhaseA_wall_bounds hμ hm hu hv hw
  have hB := connectionPhaseB_bounds hμ hm hu hv hw
  have hP0 : 0 ≤ (v * w) ^ 2 := sq_nonneg _
  have hP : (v * w) ^ 2 ≤ 1 := by
    have H : 0 ≤ v * w ∧ v * w ≤ 1 := ⟨mul_nonneg hv.1 hw.1,
      (mul_le_mul hv.2 hw.2 hw.1 zero_le_one).trans_eq (by norm_num)⟩
    simpa using pow_le_pow_left₀ H.1 H.2 2
  have wall_bound (r a b : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (ha : |a| ≤ 16 * r)
      (hb : |b| ≤ 100 * r ^ 2 / μ ^ 5 + 12 * u * r / μ ^ 4) :
      |u * a + (v * w) ^ 2 * b + 2 * (v * w) ^ 2 * connectionPhaseB m u v w| ≤
        32 * (u * r + (v * w) ^ 2 / μ ^ 3) := by
    have hr2 : r ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hr.1 hr.2 2
    have hur : u * r ≤ 1 := (mul_le_mul hu1 hr.2 hr.1 zero_le_one).trans_eq (by norm_num)
    have H1 : r ^ 2 / μ ^ 2 ≤ 1 / 16 := div_le_div₀ zero_le_one hr2 (by norm_num) hμ2
    have H2 : u * r / μ ≤ 1 / 4 := div_le_div₀ zero_le_one hur (by norm_num) hμ
    have hb' : |b| ≤ 20 / μ ^ 3 := hb.trans (by
      calc
        _ = (100 * (r ^ 2 / μ ^ 2) + 12 * (u * r / μ)) / μ ^ 3 := by field_simp
        _ ≤ 20 / μ ^ 3 := div_le_div_of_nonneg_right (by linarith only [H1, H2]) (by positivity))
    have Ha : |u * a| ≤ 16 * (u * r) := by
      rw [abs_mul, abs_of_nonneg hu0]
      exact (mul_le_mul_of_nonneg_left ha hu0).trans_eq (by ring)
    have Hb : |(v * w) ^ 2 * b| ≤ 20 * ((v * w) ^ 2 / μ ^ 3) := by
      rw [abs_mul, abs_of_nonneg hP0]
      exact (mul_le_mul_of_nonneg_left hb' hP0).trans_eq (by ring)
    have HB : |2 * (v * w) ^ 2 * connectionPhaseB m u v w| ≤ 12 * ((v * w) ^ 2 / μ ^ 3) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (v * w) ^ 2)]
      exact (mul_le_mul_of_nonneg_left hB.1 (by positivity : 0 ≤ 2 * (v * w) ^ 2)).trans_eq (by ring)
    have H := ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add Ha Hb) HB)
    exact H.trans (by nlinarith only [mul_nonneg hu0 hr.1])
  refine ⟨?_, ?_, wall_bound v _ _ hv hA.2.2.1 hB.2.2.2.1,
    wall_bound w _ _ hw hA.2.2.2 hB.2.2.2.2⟩
  · have hD := (connection_speed_bounds hμ hm hu hv hw).1
    rw [connectionPhaseGPartials_phase (by linarith only [hD, hμ])]
    exact connectionPhaseGJ_bound hμ hm hu hv hw
  · have H1 : |u * connectionPhaseAPartials m u v w 1| ≤ 16 * u := by
      rw [abs_mul, abs_of_nonneg hu0]
      have H := mul_le_mul_of_nonneg_left hA.2.1 hu0
      nlinarith only [H, hu2]
    have H2 : |(v * w) ^ 2 * connectionPhaseBPartials m u v w 1| ≤ u := by
      rw [abs_mul, abs_of_nonneg hP0]
      have H : 36 * u / μ ^ 4 ≤ u := by
        calc
          _ = u * (36 / μ ^ 4) := by ring
          _ ≤ u * 1 := mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr hμ4) hu0
          _ = u := mul_one u
      exact (mul_le_mul hP (hB.2.2.1.trans H) (abs_nonneg _) zero_le_one).trans_eq (by ring)
    have H3 : |u * connectionPhaseA m u v w| ≤ 8 * u := by
      rw [abs_mul, abs_of_nonneg hu0]
      exact (mul_le_mul_of_nonneg_left hA.1 hu0).trans_eq (by ring)
    exact (((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add H1 H2) H3)).trans (by linarith only [hu0])

end BianchiIX

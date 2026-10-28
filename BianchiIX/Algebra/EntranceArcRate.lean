import BianchiIX.Algebra.EntranceBounds

noncomputable section

namespace BianchiIX

theorem entrance_strong_arc_identity {m u v w : ℝ} (hm : m - 1 ≠ 0)
    (hD : connectionSpeed m u v w ≠ 0) :
    connectionStrongRate m u v w / connectionSpeed m u v w =
      -1 - coreRadius m v ^ 2 / (2 * (m - 1)) +
        (2 * v * w - w ^ 2 + u ^ 2 - (2 + coreRadius m v ^ 2 / (m - 1)) * coupling u v w) /
          (2 * connectionSpeed m u v w) := by
  rw [coreRadius_sq]
  dsimp [coreEnergy, connectionStrongRate, connectionSpeed] at *
  field_simp
  ring

theorem entrance_arc_square_coefficient {k m v : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100) (hv : 0 ≤ v ∧ v ≤ 1) :
    coreRadius m v ^ 2 / (m - 1) ≤ 32 / 25 * k := by
  have hp := entrance_phase_bounds hk hm hr hv
  have hk0 : 0 ≤ k := by linarith
  have ht : 0 < m - 1 := by linarith [hp.1]
  have hR0 : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  have hRsq := mul_nonneg (show 0 ≤ 101 / 100 * k - coreRadius m v by linarith [(abs_le.mp hr).2])
    (show 0 ≤ 101 / 100 * k + coreRadius m v by positivity)
  have hprod := mul_le_mul_of_nonneg_left hp.1 (show 0 ≤ 32 / 25 * k by positivity)
  apply (div_le_iff₀ ht).mpr
  nlinarith only [hRsq, hprod, sq_nonneg k]

theorem entrance_arc_error_bound {k m u v w : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    (2 * v * w - w ^ 2 + u ^ 2 - (2 + coreRadius m v ^ 2 / (m - 1)) * coupling u v w) /
      (2 * connectionSpeed m u v w) ≤ 2 * w / k + 2 * u ^ 2 := by
  have hk0 : 0 < k := by linarith
  have hp := entrance_phase_bounds hk hm hr hv
  have ht : 0 < m - 1 := by linarith [hp.1]
  have hD := entrance_speed_bounds hk hp hu hv hw
  have hD0 : 0 < connectionSpeed m u v w := by linarith [hD.1]
  have hfrac := entrance_arc_square_coefficient hk hm hr hv
  have hcoef : 3 + coreRadius m v ^ 2 / (m - 1) ≤ 4 * connectionSpeed m u v w := by
    linarith only [hfrac, hD.1, hk]
  have hc0 : 0 ≤ 2 + coreRadius m v ^ 2 / (m - 1) := by positivity
  have hC := (connection_coupling_bounds hu.1 hv ⟨hw.1, by linarith [hw.2]⟩).1
  have hCu := mul_le_mul_of_nonneg_left hC hc0
  have hcoefU := mul_le_mul_of_nonneg_right hcoef (sq_nonneg u)
  have hrem : (2 * v * w - w ^ 2 + u ^ 2 - (2 + coreRadius m v ^ 2 / (m - 1)) * coupling u v w) /
      (2 * connectionSpeed m u v w) ≤ v * w / connectionSpeed m u v w + 2 * u ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * connectionSpeed m u v w)).mpr
    have hid : (v * w / connectionSpeed m u v w + 2 * u ^ 2) * (2 * connectionSpeed m u v w) =
        2 * v * w + 4 * connectionSpeed m u v w * u ^ 2 := by field_simp; ring
    rw [hid]
    nlinarith only [hCu, hcoefU, sq_nonneg w]
  have hvw := mul_le_mul_of_nonneg_right hv.2 hw.1
  have hkw := mul_le_mul_of_nonneg_right (show k ≤ 2 * connectionSpeed m u v w by linarith [hD.1]) hw.1
  have hvwk := mul_le_mul_of_nonneg_right hvw hk0.le
  have hterm : v * w / connectionSpeed m u v w ≤ 2 * w / k :=
    (div_le_div_iff₀ hD0 hk0).mpr (by nlinarith only [hkw, hvwk])
  exact hrem.trans (add_le_add hterm le_rfl)

theorem entrance_arc_damping_lower {k m v : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100) (hv : 0 ≤ v ∧ v ≤ 1) :
    99 * k / 200 ≤ coreRadius m v ^ 2 / (2 * (m - 1)) := by
  have hp := entrance_phase_bounds hk hm hr hv
  have ht : 0 < m - 1 := by linarith [hp.1]
  have hR0 : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  have htR : m - 1 ≤ coreRadius m v := by nlinarith only [he, sq_nonneg v, hR0, hm]
  have hprod := mul_le_mul_of_nonneg_left htR hR0
  have hhalf : coreRadius m v / 2 ≤ coreRadius m v ^ 2 / (2 * (m - 1)) :=
    (le_div_iff₀ (by positivity : 0 < 2 * (m - 1))).mpr (by nlinarith only [hprod])
  exact (show 99 * k / 200 ≤ coreRadius m v / 2 by linarith [(abs_le.mp hr).1]).trans hhalf

theorem entrance_strong_arc_rate {k m u v w : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    connectionStrongRate m u v w / connectionSpeed m u v w ≤
      -(1 + 99 * k / 200) + 2 * w / k + 2 * u ^ 2 := by
  have hp := entrance_phase_bounds hk hm hr hv
  have hD := entrance_speed_bounds hk hp hu hv hw
  have ht : m - 1 ≠ 0 := by linarith [hp.1]
  have hD0 : connectionSpeed m u v w ≠ 0 := by linarith [hD.1]
  rw [entrance_strong_arc_identity ht hD0]
  have hrem := entrance_arc_error_bound hk hm hr hu hv hw
  have hmain := entrance_arc_damping_lower hk hm hr hv
  linarith only [hrem, hmain]

end BianchiIX

import BianchiIX.Algebra.CoreBounds
import BianchiIX.Algebra.Coordinates

noncomputable section

namespace BianchiIX

/-- Completing the active-wall square keeps the projective chart regular even at zero walls. -/
theorem coreBootstrap_denom_lower {k m u v w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    2 ≤ projectiveDenom m u v w := by
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have huw := mul_le_mul hu' hw' hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 60000)
  unfold projectiveDenom curvature
  nlinarith [sq_nonneg m, sq_nonneg (v - u - w)]

theorem coreRadius_component_bounds (m v : ℝ) :
    |m - 1| ≤ coreRadius m v ∧ |v| ≤ coreRadius m v := by
  have hr : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg v]
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (m - 1)]

theorem coreBootstrap_denom_upper {k m u v w : ℝ} (hk : 6 ≤ k)
    (hr : coreRadius m v ≤ 101 / 100 * k) (hv : 0 ≤ v)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    projectiveDenom m u v w ≤ 2 * k ^ 2 := by
  have hm : m - 1 ≤ 101 / 100 * k :=
    (le_abs_self _).trans ((coreRadius_component_bounds m v).1.trans hr)
  have hr2 := (sq_le_sq₀ (Real.sqrt_nonneg (coreEnergy m v)) (by linarith)).mpr hr
  change coreRadius m v ^ 2 ≤ (101 / 100 * k) ^ 2 at hr2
  rw [coreRadius_sq] at hr2
  unfold coreEnergy at hr2
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hdelta : (u - w) ^ 2 ≤ (1 / 60000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 60000 - (u - w) by linarith)
      (show 0 ≤ 1 / 60000 + (u - w) by linarith)]
  have hprod := mul_nonneg hv (add_nonneg hu.1 hw.1)
  unfold projectiveDenom curvature
  nlinarith [sq_nonneg (k - 6)]

theorem coreBootstrap_inverse_scale_bounds {k m u v w : ℝ} (hk : 6 ≤ k)
    (hr : coreRadius m v ≤ 101 / 100 * k)
    (hv : 0 ≤ v) (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k)
    (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    3 / k ^ 2 ≤ 6 / projectiveDenom m u v w ∧ 6 / projectiveDenom m u v w ≤ 3 := by
  have hk0 : 0 < k := by linarith
  have hDlo := coreBootstrap_denom_lower (m := m) (v := v) hk hu hw
  have hDhi := coreBootstrap_denom_upper hk hr hv hu hw
  constructor
  · apply (div_le_div_iff₀ (sq_pos_of_pos hk0) (by linarith)).mpr
    nlinarith
  · apply (div_le_iff₀ (by linarith)).mpr
    nlinarith

/-- A uniform lower bound on the angle speed in the original normalized Einstein time. -/
theorem coreBootstrap_original_clock_lower {k m u v w : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ coreRadius m v ∧ coreRadius m v ≤ 101 / 100 * k)
    (hv : 0 ≤ v) (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k)
    (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    1 / k ≤ (6 / projectiveDenom m u v w) * coreRadius m v * coreClockFactor (coreRadius m v) u w := by
  have hk0 : 0 < k := by linarith
  have hDlo := coreBootstrap_denom_lower (m := m) (v := v) hk hu hw
  have hA := (coreBootstrap_inverse_scale_bounds hk hr.2 hv hu hw).1
  have hd := coreBootstrap_clock_bounds hk hr.1 hu hw
  have hrd : k / 2 ≤ coreRadius m v * coreClockFactor (coreRadius m v) u w := by
    have H := mul_le_mul hr.1 hd.1 (by norm_num : (0 : ℝ) ≤ 999 / 1000) (by linarith)
    nlinarith
  calc
    1 / k ≤ (3 / k ^ 2) * (k / 2) := by
      field_simp
      nlinarith
    _ ≤ (6 / projectiveDenom m u v w) *
        (coreRadius m v * coreClockFactor (coreRadius m v) u w) :=
      mul_le_mul hA hrd (by positivity) (by positivity)
    _ = _ := by ring

theorem coreBootstrap_angle_bound {k m v : ℝ} (hk : 6 ≤ k)
    (hr : coreRadius m v ≤ 101 / 100 * k) (hv : 1 ≤ v) :
    |coreAngle m v| ≤ Real.log (4 * k) := by
  have hv0 : 0 < v := by linarith
  have hc : Real.cosh (coreAngle m v) ≤ 101 / 100 * k := by
    rw [cosh_coreAngle hv0]
    exact (div_le_self (coreRadius_pos hv0).le hv).trans hr
  have he : Real.exp |coreAngle m v| ≤ 2 * Real.cosh (coreAngle m v) := by
    rw [← Real.cosh_abs (coreAngle m v), Real.cosh_eq]
    linarith [Real.exp_pos (-|coreAngle m v|)]
  apply (Real.le_log_iff_exp_le (by linarith : 0 < 4 * k)).mpr
  linarith

end BianchiIX

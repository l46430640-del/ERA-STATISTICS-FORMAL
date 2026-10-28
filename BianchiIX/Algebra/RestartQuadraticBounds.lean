import BianchiIX.Algebra.RestartTransferBounds
import Mathlib.Tactic.GCongr

noncomputable section

namespace BianchiIX

def quadraticFromCoefficients (m : Fin 3 → ℝ) (s v : ℝ) : ℝ :=
  m 0 * s ^ 2 + m 1 * s * v + m 2 * v ^ 2

theorem abs_quadraticFromCoefficients_le (m : Fin 3 → ℝ) (s v : ℝ) :
    |quadraticFromCoefficients m s v| ≤ 2 * ‖m‖ * (s ^ 2 + v ^ 2) := by
  have hm (i : Fin 3) : |m i| ≤ ‖m‖ := norm_le_pi_norm m i
  have hsv : |s| * |v| ≤ s ^ 2 + v ^ 2 := by
    nlinarith only [sq_nonneg (|s| - |v|), sq_abs s, sq_abs v, sq_nonneg s, sq_nonneg v]
  calc
    _ ≤ |m 0 * s ^ 2| + |m 1 * s * v| + |m 2 * v ^ 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ‖m‖ * s ^ 2 + ‖m‖ * (|s| * |v|) + ‖m‖ * v ^ 2 := by
      simp only [abs_mul, abs_sq, mul_assoc]
      gcongr
      · exact hm 0
      · exact hm 1
      · exact hm 2
    _ ≤ 2 * ‖m‖ * (s ^ 2 + v ^ 2) := by
      nlinarith only [mul_le_mul_of_nonneg_left hsv (norm_nonneg m)]

theorem abs_quadraticFromCoefficients_le_radius {r s v : ℝ} (m : Fin 3 → ℝ)
    (_hr : 0 ≤ r) (hs : |s| ≤ r) (hv : |v| ≤ 2 * r) :
    |quadraticFromCoefficients m s v| ≤ 12 * ‖m‖ * r ^ 2 := by
  have hs2 : s ^ 2 ≤ r ^ 2 := by
    have H := mul_self_le_mul_self (abs_nonneg s) hs
    nlinarith only [H, sq_abs s]
  have hv2 : v ^ 2 ≤ 4 * r ^ 2 := by
    have H := mul_self_le_mul_self (abs_nonneg v) hv
    nlinarith only [H, sq_abs v]
  exact (abs_quadraticFromCoefficients_le m s v).trans (by
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hs2 hv2) (norm_nonneg m),
      mul_nonneg (norm_nonneg m) (sq_nonneg r)])

theorem abs_quadratic_tangent_le {r d s v ds dv : ℝ} (m dm : Fin 3 → ℝ)
    (hr : 0 ≤ r) (hd : 0 ≤ d) (hs : |s| ≤ r) (hv : |v| ≤ 2 * r)
    (hds : |ds| ≤ d) (hdv : |dv| ≤ 2 * d) :
    |quadraticFromCoefficients dm s v + (2 * m 0 * s + m 1 * v) * ds +
      (m 1 * s + 2 * m 2 * v) * dv| ≤ 12 * ‖dm‖ * r ^ 2 + 24 * ‖m‖ * r * d := by
  have hm (i : Fin 3) : |m i| ≤ ‖m‖ := norm_le_pi_norm m i
  have Hs : |(2 * m 0 * s + m 1 * v) * ds| ≤ 4 * ‖m‖ * r * d := by
    calc
      _ ≤ (|2 * m 0 * s| + |m 1 * v|) * |ds| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
      _ ≤ (2 * ‖m‖ * r + ‖m‖ * (2 * r)) * d := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
        · exact hm 0
        · exact hm 1
      _ = _ := by ring
  have Hv : |(m 1 * s + 2 * m 2 * v) * dv| ≤ 10 * ‖m‖ * r * d := by
    calc
      _ ≤ (|m 1 * s| + |2 * m 2 * v|) * |dv| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
      _ ≤ (‖m‖ * r + 2 * ‖m‖ * (2 * r)) * (2 * d) := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
        · exact hm 1
        · exact hm 2
      _ = _ := by ring
  have H : |quadraticFromCoefficients dm s v + (2 * m 0 * s + m 1 * v) * ds +
      (m 1 * s + 2 * m 2 * v) * dv| ≤ |quadraticFromCoefficients dm s v| +
        |(2 * m 0 * s + m 1 * v) * ds| + |(m 1 * s + 2 * m 2 * v) * dv| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have HQ := abs_quadraticFromCoefficients_le_radius dm hr hs hv
  nlinarith only [H, HQ, Hs, Hv, mul_nonneg (mul_nonneg (norm_nonneg m) hr) hd]

theorem restartQuadratic_coercive {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) (s v : ℝ) :
    s ^ 2 + v ^ 2 ≤ 2 * restartQuadratic n s v := by
  obtain ⟨ha0, _, hc0, _, hk0, hk1⟩ := restart_coefficients_small hn
  have ha2 : 1 ≤ restartShearFactor n ^ 2 := by nlinarith only [ha0]
  have hc2 : 1 ≤ restartWallFactor n ^ 2 := by nlinarith only [hc0]
  have hk2 : 2 * restartShearCoupling n ^ 2 ≤ 1 := by nlinarith only [hk0, hk1, hn.2]
  have HA := mul_le_mul_of_nonneg_right ha2 (sq_nonneg s)
  have HC := mul_le_mul_of_nonneg_right hc2 (sq_nonneg v)
  have HK := mul_le_mul_of_nonneg_right hk2 (sq_nonneg v)
  dsimp only [restartQuadratic]
  nlinarith only [HA, HC, HK, sq_nonneg (restartShearFactor n * s + 2 * restartShearCoupling n * v)]

end BianchiIX

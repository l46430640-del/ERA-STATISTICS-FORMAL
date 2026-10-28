import BianchiIX.Algebra.CoreRadialBounds

noncomputable section

namespace BianchiIX

theorem partial_core_radius_budget {k u p : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hp : 0 ≤ p ∧ p ≤ (1 / 10000) / k) :
    (14 * u + 4 * u * p / k + 3 * u ^ 2 / k ^ 2 + 4 * p ^ 2 / k) / (999 / 1000) ≤
      16 * (u + p ^ 2 / k) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hu1 : u ≤ 1 := (coreBootstrap_wall_bound hk hu.2).trans (by norm_num)
  have hp1 : p ≤ 1 := (coreBootstrap_wall_bound hk hp.2).trans (by norm_num)
  have huw : 4 * u * p / k ≤ u := by
    apply (div_le_iff₀ hk0).mpr
    have H := mul_le_mul_of_nonneg_left hp1 hu.1
    have Hk := mul_le_mul_of_nonneg_left hk hu.1
    nlinarith only [H, Hk, hu.1]
  have huu : 3 * u ^ 2 / k ^ 2 ≤ u / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hk0)).mpr
    have H := mul_le_mul_of_nonneg_left hu1 hu.1
    have Hk := mul_le_mul_of_nonneg_left (show 36 ≤ k ^ 2 by nlinarith only [hk]) hu.1
    nlinarith only [H, Hk, hu.1]
  have hp2 : 0 ≤ p ^ 2 / k := div_nonneg (sq_nonneg p) hk0.le
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 999 / 1000)).mpr
  rw [show 4 * p ^ 2 / k = 4 * (p ^ 2 / k) by ring]
  linarith only [huw, huu, hu.1, hp2]

theorem partial_core_radius_energy_improvement {k r u p : ℝ} (hk : 6 ≤ k)
    (hr : 0 ≤ r) (hrhi : r ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hp : 0 ≤ p ∧ p ≤ (1 / 10000) / k)
    (hR : |r - k| ≤ 16 * (u + p ^ 2 / k)) : |r ^ 2 - k ^ 2| < 1 / 16 := by
  have hk0 : 0 < k := by linarith only [hk]
  have hku : k * u ≤ 1 / 10000 := by
    have H := (le_div_iff₀ hk0).mp hu.2
    linarith only [H]
  have hp' := coreBootstrap_wall_bound hk hp.2
  have hp2 := (sq_le_sq₀ hp.1 (by norm_num : (0 : ℝ) ≤ 1 / 60000)).mpr hp'
  have hnonneg : 0 ≤ 16 * (u + p ^ 2 / k) :=
    mul_nonneg (by norm_num) (add_nonneg hu.1 (div_nonneg (sq_nonneg p) hk0.le))
  calc
    |r ^ 2 - k ^ 2| = |r - k| * (r + k) := by
      rw [show r ^ 2 - k ^ 2 = (r - k) * (r + k) by ring, abs_mul,
        abs_of_nonneg (by linarith only [hr, hk] : 0 ≤ r + k)]
    _ ≤ (16 * (u + p ^ 2 / k)) * (201 / 100 * k) :=
      mul_le_mul hR (by linarith only [hrhi]) (by linarith only [hr, hk]) hnonneg
    _ = (804 / 25) * (k * u + p ^ 2) := by field_simp; ring
    _ < 1 / 16 := by nlinarith only [hku, hp2]

end BianchiIX

import BianchiIX.Algebra.PartialCoreRadialResponseBounds

noncomputable section

namespace BianchiIX

theorem partial_core_radial_variation_budget {r K k U P dR dU dP dz : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hk : 0 < k)
    (hki : 1 / k ≤ K * r) (hkhi : k ≤ K / r)
    (_hU : 0 ≤ U) (hKU : k * U ≤ 1) (hP : 0 ≤ P ∧ P ≤ 1)
    (hR : |dR| ≤ K / r ^ 2) (hdU : |dU| ≤ K * U / r)
    (hdP : |dP| ≤ K * P / r) (hdz : |dz| ≤ K / r) :
    |dR| + k * |dU| + |dP| + (k ^ 2 * U + P / k) * |dz| ≤ 5 * K ^ 2 / r ^ 2 := by
  have hr0 := hr.1
  have hP0 := hP.1
  have hP1 := hP.2
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hKK : K ≤ K ^ 2 := by nlinarith only [hK]
  have hscale : K / r ≤ K ^ 2 / r ^ 2 := by
    apply (div_le_div_iff₀ hr.1 (sq_pos_of_pos hr.1)).mpr
    have H := mul_le_mul_of_nonneg_left hr.2 hK0
    nlinarith only [mul_le_mul_of_nonneg_right H hr.1.le,
      mul_le_mul_of_nonneg_right hKK hr.1.le]
  have hplain : K ^ 2 ≤ K ^ 2 / r ^ 2 := le_div_self (sq_nonneg K) (sq_pos_of_pos hr.1)
    (by nlinarith only [hr.1, hr.2])
  have HR := hR.trans (div_le_div_of_nonneg_right hKK (sq_nonneg r))
  have HU : k * |dU| ≤ K ^ 2 / r ^ 2 := by
    calc
      _ ≤ k * (K * U / r) := mul_le_mul_of_nonneg_left hdU hk.le
      _ = (K / r) * (k * U) := by ring
      _ ≤ K / r := mul_le_of_le_one_right (by positivity) hKU
      _ ≤ _ := hscale
  have HP : |dP| ≤ K ^ 2 / r ^ 2 := hdP.trans (le_trans
    (div_le_div_of_nonneg_right (mul_le_of_le_one_right hK0 hP.2) hr.1.le) hscale)
  have HZ : k ^ 2 * U * |dz| ≤ K ^ 2 / r ^ 2 := by
    calc
      _ = (k * U) * k * |dz| := by ring
      _ ≤ 1 * (K / r) * (K / r) := by gcongr
      _ = _ := by ring
  have HW : P / k * |dz| ≤ K ^ 2 / r ^ 2 := by
    calc
      _ = P * (1 / k) * |dz| := by ring
      _ ≤ 1 * (K * r) * (K / r) := by gcongr
      _ = K ^ 2 := by field_simp
      _ ≤ _ := hplain
  have heq : (k ^ 2 * U + P / k) * |dz| = k ^ 2 * U * |dz| + P / k * |dz| := by ring
  rw [heq]
  rw [show 5 * K ^ 2 / r ^ 2 = 5 * (K ^ 2 / r ^ 2) by ring]
  linarith only [HR, HU, HP, HZ, HW]

theorem partial_core_radial_log_bounds {r K k B L Q dz lU lP : ℝ}
    (hr : 0 < r) (hK : 1 ≤ K) (hk : 0 < k) (hB : 0 ≤ B) (hL : 1 ≤ L)
    (hki : 1 / k ≤ K * r) (hkhi : k ≤ K / r)
    (hQ : Q ≤ 5 * K ^ 2 / r ^ 2) (hdz : |dz| ≤ K / r)
    (hU : |lU| ≤ 40 * B * L * Q + 2 * k * |dz|)
    (hP : |lP| ≤ 236 * B * L * Q / k ^ 2 + 4 * |dz| / k) :
    |lU| ≤ (200 * B + 2) * K ^ 2 * L / r ^ 2 ∧
      |lP| ≤ (1180 * B * K ^ 4 + 4 * K ^ 2) * L := by
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have HU : 40 * B * L * Q ≤ 200 * B * K ^ 2 * L / r ^ 2 :=
    (mul_le_mul_of_nonneg_left hQ (by positivity)).trans_eq (by ring)
  have HUz : 2 * k * |dz| ≤ 2 * K ^ 2 / r ^ 2 := by
    calc
      _ ≤ 2 * (K / r) * (K / r) := by gcongr
      _ = _ := by ring
  have HP : 236 * B * L * Q / k ^ 2 ≤ 1180 * B * K ^ 4 * L := by
    calc
      _ ≤ 236 * B * L * (5 * K ^ 2 / r ^ 2) / k ^ 2 := by gcongr
      _ = (1180 * B * K ^ 2 * L / r ^ 2) * (1 / k) ^ 2 := by ring
      _ ≤ (1180 * B * K ^ 2 * L / r ^ 2) * (K * r) ^ 2 := by gcongr
      _ = _ := by field_simp
  have HPz : 4 * |dz| / k ≤ 4 * K ^ 2 := by
    calc
      _ = 4 * |dz| * (1 / k) := by ring
      _ ≤ 4 * (K / r) * (K * r) := by gcongr
      _ = _ := by field_simp
  constructor
  · have H := mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * K ^ 2 / r ^ 2 by positivity)
    have HUz' := HUz.trans (by simpa only [mul_one] using H)
    exact hU.trans ((add_le_add HU HUz').trans_eq (by ring))
  · have H := mul_le_mul_of_nonneg_left hL (show 0 ≤ 4 * K ^ 2 by positivity)
    nlinarith only [hP, HP, HPz, H]

end BianchiIX

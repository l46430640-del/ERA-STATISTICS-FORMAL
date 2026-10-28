import BianchiIX.Algebra.PartialCoreRadialCone

noncomputable section

namespace BianchiIX

/-- The strong-wall exponential absorbs the logarithm and the extra inverse radial scale. -/
theorem partial_core_connection_wall_budget {r K k A B U P u w du dw : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hk : 6 ≤ k)
    (hki : 1 / k ≤ K * r) (hkhi : k ≤ K / r)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (_hu : 0 ≤ u) (hw : 0 ≤ w)
    (hdec : u ≤ U * Real.exp (-k / 12)) (hweak : w ≤ P)
    (hdu : |du| ≤ u * (K / r + A * Real.log (4 * k) / r ^ 2))
    (hdw : |dw| ≤ w * (K / r + B * Real.log (4 * k))) :
    u ≤ U ∧ r * |du| ≤ K * (1 + 576 * A) * U ∧
      r * |dw| ≤ K * (1 + B) * P := by
  have hk0 : 0 < k := by linarith only [hk]
  have hP : 0 ≤ P := hw.trans hweak
  have hL : 0 ≤ Real.log (4 * k) := Real.log_nonneg (by linarith only [hk])
  have hE : Real.exp (-k / 12) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hk])
  have hue : u ≤ U := hdec.trans (mul_le_of_le_one_right hU hE)
  have hkinv : 1 / r ≤ K * k := by
    apply (div_le_iff₀ hr).mpr
    nlinarith only [(div_le_iff₀ hk0).mp hki]
  have Hlin : k * Real.exp (-k / 24) ≤ 24 := by
    have H := affine_mul_exp_neg_le_one (k / 24)
    rw [show -(k / 24) = -k / 24 by ring] at H
    nlinarith only [H, Real.exp_pos (-k / 24)]
  have Hlog : Real.exp (-k / 12) * Real.log (4 * k) / r ≤ 576 * K := by
    calc
      _ = (Real.exp (-k / 24) * Real.log (4 * k)) * Real.exp (-k / 24) * (1 / r) := by
        rw [show -k / 12 = -k / 24 + -k / 24 by ring, Real.exp_add]
        ring
      _ ≤ (Real.exp (-k / 24) * Real.log (4 * k)) * Real.exp (-k / 24) * (K * k) := by gcongr
      _ = K * (Real.exp (-k / 24) * Real.log (4 * k)) * (k * Real.exp (-k / 24)) := by ring
      _ ≤ K * 24 * 24 := by gcongr; exact partial_core_strong_log_budget hk
      _ = _ := by ring
  have HU : r * |du| ≤ U * (K * Real.exp (-k / 12) +
      A * (Real.exp (-k / 12) * Real.log (4 * k) / r)) := by
    calc
      _ ≤ r * (u * (K / r + A * Real.log (4 * k) / r ^ 2)) := mul_le_mul_of_nonneg_left hdu hr.le
      _ ≤ r * ((U * Real.exp (-k / 12)) * (K / r + A * Real.log (4 * k) / r ^ 2)) := by gcongr
      _ = _ := by field_simp
  have HW : K / r + B * Real.log (4 * k) ≤ K * (1 + B) / r := by
    calc
      _ ≤ K / r + B * k := add_le_add le_rfl (mul_le_mul_of_nonneg_left (core_log_bound hk) hB)
      _ ≤ K / r + B * (K / r) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hkhi hB)
      _ = _ := by ring
  refine ⟨hue, HU.trans ?_, ?_⟩
  · calc
      _ ≤ U * (K * 1 + A * (576 * K)) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ r * (w * (K / r + B * Real.log (4 * k))) := mul_le_mul_of_nonneg_left hdw hr.le
      _ ≤ r * (P * (K * (1 + B) / r)) := by gcongr
      _ = _ := by field_simp

/-- Ordinary connection columns retain the full strong amplitude and the squared weak amplitude. -/
theorem connection_phase_radial_budget {r K M A B μ U P u w v0 v1 v2 : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hμ : 0 < μ) (hi : 1 / μ ≤ K * r) (hU : 0 ≤ U) (hP : 0 ≤ P ∧ P ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ U) (hw : 0 ≤ w ∧ w ≤ P)
    (hv0 : |v0| ≤ M / r ^ 2) (hv1 : r * |v1| ≤ A * U) (hv2 : r * |v2| ≤ B * P) :
    |v0| * (50000 * (u + w ^ 2) / μ ^ 2) + |v1| * (50000 / μ) +
      |v2| * (50000 * (u + w) / μ) ≤
        50000 * (K ^ 2 * M + K * A + K * B) * (U + P ^ 2) := by
  have hP0 := hP.1
  have hu0 := hu.1
  have huU := hu.2
  have hw0 := hw.1
  have hwP := hw.2
  have hwsq : w ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hw.1 hw.2 2
  have H0 : |v0| * (50000 * (u + w ^ 2) / μ ^ 2) ≤ 50000 * K ^ 2 * M * (U + P ^ 2) := by
    calc
      _ = 50000 * |v0| * (u + w ^ 2) * (1 / μ) ^ 2 := by ring
      _ ≤ 50000 * (M / r ^ 2) * (U + P ^ 2) * (K * r) ^ 2 := by gcongr
      _ = _ := by field_simp
  have H1 : |v1| * (50000 / μ) ≤ 50000 * K * A * U := by
    calc
      _ = 50000 * |v1| * (1 / μ) := by ring
      _ ≤ 50000 * |v1| * (K * r) := by gcongr
      _ = 50000 * K * (r * |v1|) := by ring
      _ ≤ 50000 * K * (A * U) := by gcongr
      _ = _ := by ring
  have H2 : |v2| * (50000 * (u + w) / μ) ≤ 50000 * K * B * (U + P ^ 2) := by
    calc
      _ = 50000 * (u + w) * |v2| * (1 / μ) := by ring
      _ ≤ 50000 * (U + P) * |v2| * (K * r) := by gcongr
      _ = 50000 * K * (U + P) * (r * |v2|) := by ring
      _ ≤ 50000 * K * (U + P) * (B * P) := by gcongr
      _ = 50000 * K * B * (P * U + P ^ 2) := by ring
      _ ≤ 50000 * K * B * (U + P ^ 2) := by gcongr; exact mul_le_of_le_one_left hU hP.2
  have H1' : 50000 * K * A * U ≤ 50000 * K * A * (U + P ^ 2) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg P)) (by positivity)
  exact (add_le_add (add_le_add H0 (H1.trans H1')) H2).trans_eq (by ring)

end BianchiIX

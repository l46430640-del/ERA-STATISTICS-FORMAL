import BianchiIX.Algebra.ConnectionConeSize
import BianchiIX.Analysis.CoreGrowthBudget
import Mathlib.Tactic.GCongr

noncomputable section

namespace BianchiIX

theorem partial_core_strong_log_budget {k : ℝ} (hk : 6 ≤ k) :
    Real.exp (-k / 24) * Real.log (4 * k) ≤ 24 := by
  have hk0 : 0 ≤ k := by linarith only [hk]
  have H := affine_mul_exp_neg_le_one (k / 24)
  rw [show -(k / 24) = -k / 24 by ring] at H
  have HE := Real.exp_pos (-k / 24)
  have Hk : Real.exp (-k / 24) * k ≤ 24 := by nlinarith only [H, HE]
  exact (mul_le_mul_of_nonneg_left (core_log_bound hk) HE.le).trans Hk

/-- Multiplicative square-root cone estimates remain meaningful on either zero wall. -/
theorem partial_core_radial_cone {r K k A B D U P Uout Pout dU dP dR : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 0 ≤ K) (hk : 6 ≤ k) (hkhi : k ≤ K / r)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 < D)
    (hU : 0 ≤ U) (_hP : 0 ≤ P) (hUout : 0 ≤ Uout) (hPout : 0 ≤ Pout)
    (hcontractU : Uout ≤ U * Real.exp (-k / 12)) (hcontractP : Pout ≤ P)
    (hdU : |dU| ≤ Uout * (K / r + A * Real.log (4 * k) / r ^ 2))
    (hdP : |dP| ≤ Pout * (K / r + B * Real.log (4 * k)))
    (hdR : 1 / (D * r ^ 2) ≤ |dR|) :
    |dU| ≤ (D * (K + 24 * A) * Real.sqrt U) * Real.sqrt Uout * |dR| ∧
      |dP| ≤ (D * K * (1 + B) * r * Real.sqrt P) * Real.sqrt Pout * |dR| := by
  have hr0 := hr.1
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hL : 0 ≤ Real.log (4 * k) := Real.log_nonneg (by linarith only [hk])
  have hspeed : 1 ≤ D * r ^ 2 * |dR| := by
    have H := (div_le_iff₀ (mul_pos hD (sq_pos_of_pos hr.1))).mp hdR
    nlinarith only [H]
  have hrootU : Real.sqrt Uout ≤ Real.sqrt U * Real.exp (-k / 24) := by
    simpa only [show (-k / 12) / 2 = -k / 24 by ring] using sqrt_le_sqrt_mul_exp_half hU hcontractU
  have hE : Real.exp (-k / 24) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hk0])
  have hEr : r * Real.exp (-k / 24) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hE hr.1.le).trans (by simpa only [mul_one] using hr.2)
  have HE : Real.exp (-k / 24) * (K / r + A * Real.log (4 * k) / r ^ 2) ≤
      (K + 24 * A) / r ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hr.1)).mp
    have H₁ := mul_le_mul_of_nonneg_left hEr hK
    have H₂ := mul_le_mul_of_nonneg_left (partial_core_strong_log_budget hk) hA
    calc
      _ = K * (r * Real.exp (-k / 24)) + A * (Real.exp (-k / 24) * Real.log (4 * k)) := by
        field_simp
      _ ≤ K * 1 + A * 24 := add_le_add H₁ H₂
      _ = _ := by field_simp
  have HP : K / r + B * Real.log (4 * k) ≤ K * (1 + B) / r := by
    calc
      _ ≤ K / r + B * k := add_le_add le_rfl (mul_le_mul_of_nonneg_left (core_log_bound hk) hB)
      _ ≤ K / r + B * (K / r) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hkhi hB)
      _ = _ := by ring
  have HU' : |dU| ≤ (Real.sqrt Uout * Real.sqrt U) * ((K + 24 * A) / r ^ 2) := by
    calc
      _ ≤ (Real.sqrt Uout * Real.sqrt Uout) * (K / r + A * Real.log (4 * k) / r ^ 2) := by
        rwa [Real.mul_self_sqrt hUout]
      _ ≤ (Real.sqrt Uout * (Real.sqrt U * Real.exp (-k / 24))) *
          (K / r + A * Real.log (4 * k) / r ^ 2) := by gcongr
      _ = (Real.sqrt Uout * Real.sqrt U) *
          (Real.exp (-k / 24) * (K / r + A * Real.log (4 * k) / r ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left HE (by positivity)
  have HP' : |dP| ≤ (Real.sqrt Pout * Real.sqrt P) * (K * (1 + B) / r) := by
    calc
      _ ≤ (Real.sqrt Pout * Real.sqrt Pout) * (K / r + B * Real.log (4 * k)) := by
        rwa [Real.mul_self_sqrt hPout]
      _ ≤ (Real.sqrt Pout * Real.sqrt P) * (K * (1 + B) / r) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcontractP) (Real.sqrt_nonneg _))
          HP (by positivity) (by positivity)
  constructor
  · exact HU'.trans (calc
      _ ≤ ((Real.sqrt Uout * Real.sqrt U) * ((K + 24 * A) / r ^ 2)) *
          (D * r ^ 2 * |dR|) := le_mul_of_one_le_right (by positivity) hspeed
      _ = _ := by field_simp)
  · exact HP'.trans (calc
      _ ≤ ((Real.sqrt Pout * Real.sqrt P) * (K * (1 + B) / r)) *
          (D * r ^ 2 * |dR|) := le_mul_of_one_le_right (by positivity) hspeed
      _ = _ := by field_simp)

theorem partial_core_radial_cone_ratio {r CU CP U P Uout Pout dU dP dR : ℝ}
    (hr : 0 ≤ r) (hCU : 0 ≤ CU) (hCP : 0 ≤ CP)
    (hUout : 0 < Uout) (hPout : 0 < Pout) (hdR : 0 < |dR|)
    (hdu : |dU| ≤ (CU * Real.sqrt U) * Real.sqrt Uout * |dR|)
    (hdp : |dP| ≤ (CP * r * Real.sqrt P) * Real.sqrt Pout * |dR|) :
    |dU| / (Real.sqrt Uout * |dR|) + |dP| / (Real.sqrt Pout * |dR|) ≤
      (CU + CP) * (Real.sqrt U + r * Real.sqrt P) := by
  have HU : |dU| / (Real.sqrt Uout * |dR|) ≤ CU * Real.sqrt U :=
    (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hUout) hdR)).mpr (hdu.trans_eq (by ring))
  have HP : |dP| / (Real.sqrt Pout * |dR|) ≤ CP * r * Real.sqrt P :=
    (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hPout) hdR)).mpr (hdp.trans_eq (by ring))
  apply (add_le_add HU HP).trans
  nlinarith only [mul_nonneg hCU (mul_nonneg hr (Real.sqrt_nonneg P)),
    mul_nonneg hCP (Real.sqrt_nonneg U)]

end BianchiIX

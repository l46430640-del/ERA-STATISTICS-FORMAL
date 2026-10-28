import BianchiIX.Algebra.ExitSinglePhase
import BianchiIX.Algebra.ExitCycleEndpoint

noncomputable section

namespace BianchiIX

theorem exitSingleDefect_bound {b u v w : ℝ} (hv : 0 ≤ v) (hw : |u| + |w| ≤ b) :
    |exitSingleDefect u v w| ≤ 2 * b * (v + b) := by
  have hb : 0 ≤ b := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have Hsub : |u - w| ≤ b := (abs_sub u w).trans hw
  have Hadd : |u + w| ≤ b := (abs_add_le u w).trans hw
  calc
    |exitSingleDefect u v w| ≤ |(u - w) ^ 2| + |2 * v * (u + w)| := abs_sub _ _
    _ = |u - w| ^ 2 + 2 * v * |u + w| := by
      rw [abs_pow, abs_mul, abs_mul, abs_of_nonneg hv]; norm_num
    _ ≤ b ^ 2 + 2 * v * b := by gcongr
    _ ≤ 2 * b * (v + b) := by nlinarith only [sq_nonneg b]

theorem exitSingle_terminal_geometry {α b R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hb : b ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ α / 10000)
    (hw : |u| + |w| ≤ b) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    2 < R ∧ R ≤ 5 ∧ 2 < exitTailGap R v ∧ exitTailGap R v ≤ 5 ∧
      v ^ 2 < R ^ 2 ∧ α ^ 2 ≤ exitSingleBase R v ∧
      |exitSingleDefect u v w| ≤ α ^ 2 / 1000 ∧
      |R ^ 2 - 4 + exitSingleDefect u v w| ≤ 22 * α ∧
      0 < exitSingleBase R v + exitSingleDefect u v w ∧
      0 < R ^ 2 - 4 + exitSingleDefect u v w := by
  have hα0 := hα.1
  have hv0 := hv.1
  have hvhi := hv.2
  have hb0 : 0 ≤ b := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have HR := abs_le.mp hR
  have HRlo : 2 < R := by linarith only [HR.1, hα.1]
  have HRhi : R ≤ 5 := by linarith only [HR.2, hα.2]
  have HG := exitTailGap_terminal_offset hα (le_refl (α / 10000)) hR hv
  have HGlo : 2 < exitTailGap R v := by linarith only [HG.1, hα.1]
  have HGhi : exitTailGap R v ≤ 5 := by linarith only [HG.2, hα.2]
  have HvR : v ^ 2 < R ^ 2 := by
    have Hv : v ≤ 1 / 100 := hv.2.trans (by linarith only [hα.2])
    nlinarith only [Hv, hv.1, HRlo, sq_nonneg (v - 1 / 100)]
  have HH₀ := exitCycleDenom_terminal_bounds (u := 0) (w := 0) hα
    (le_refl (α / 10000)) hR (by simpa using (by positivity : 0 ≤ α / 10000)) hv
  rw [← exitSingleBase_eq] at HH₀
  have HHlo : α ^ 2 ≤ exitSingleBase R v := by nlinarith only [HH₀.1, sq_nonneg α]
  have HT := exitSingleDefect_bound hv.1 hw
  have HTsmall : |exitSingleDefect u v w| ≤ α ^ 2 / 1000 := by
    have HT' : 2 * b * (v + b) ≤ 2 * (α / 10000) * (α / 100 + α / 10000) := by gcongr
    nlinarith only [HT, HT', sq_nonneg α]
  have HN₀lo : 0 ≤ R ^ 2 - 4 := by nlinarith only [HRlo]
  have HN₀hi : R ^ 2 - 4 ≤ 21 * α := by
    have Hdiff : R - 2 ≤ 3 * α := by linarith only [HR.2, hα.1]
    have Hsum : R + 2 ≤ 7 := by linarith only [HRhi]
    nlinarith only [mul_le_mul Hdiff Hsum (by linarith only [HRlo] : 0 ≤ R + 2)
      (by positivity : 0 ≤ 3 * α)]
  have HN : |R ^ 2 - 4 + exitSingleDefect u v w| ≤ 22 * α := by
    have H := abs_add_le (R ^ 2 - 4) (exitSingleDefect u v w)
    rw [abs_of_nonneg HN₀lo] at H
    nlinarith only [H, HN₀hi, HTsmall, hα.1, hα.2]
  have HH := exitCycleDenom_terminal_bounds hα (le_refl (α / 10000)) hR (hw.trans hb) hv
  rw [exitSingleDenom_eq] at HH
  have HHpos : 0 < exitSingleBase R v + exitSingleDefect u v w :=
    lt_trans (by positivity) HH.1
  have HNpos : 0 < R ^ 2 - 4 + exitSingleDefect u v w := by
    have H := exitSingleNumerator_eq HvR.le u w
    linarith only [H, HHpos, HGlo]
  exact ⟨HRlo, HRhi, HGlo, HGhi, HvR, HHlo, HTsmall, HN, HHpos, HNpos⟩

/-- The perturbation retains both small old walls; its radial coefficient has no zeroth-order term. -/
theorem exitSingleError_scalar_bounds {α R H T L K : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hR : 0 ≤ R ∧ R ≤ 5) (hH : α ^ 2 ≤ H) (hT : |T| ≤ α ^ 2 / 1000)
    (hN : |R ^ 2 - 4 + T| ≤ 22 * α) (hL : |L| ≤ 20 * α)
    (hK : |T| ≤ K) :
    |T * (1 + (R ^ 2 - 4 + T) / H)| ≤ 23 * K / α ∧
      |T * (1 + (R ^ 2 - 4 + T) / H)| ≤ 23 * α / 1000 ∧
      |T * (2 * R / H - (R ^ 2 - 4 + T) * L / H ^ 2)| ≤ 450 * K / α ^ 2 ∧
      |1 + (R ^ 2 - 4 + 2 * T) / H| ≤ 24 / α := by
  have hα0 := hα.1
  have hR0 := hR.1
  have hRhi := hR.2
  have hH0 : 0 < H := lt_of_lt_of_le (sq_pos_of_pos hα0) hH
  have hK0 : 0 ≤ K := (abs_nonneg T).trans hK
  have Hfactor : |1 + (R ^ 2 - 4 + T) / H| ≤ 23 / α := by
    calc
      _ ≤ 1 + |R ^ 2 - 4 + T| / H := by
        have Ha : |1 + (R ^ 2 - 4 + T) / H| ≤ |(1 : ℝ)| + |(R ^ 2 - 4 + T) / H| := abs_add_le _ _
        simpa only [abs_one, abs_div, abs_of_pos hH0] using Ha
      _ ≤ 1 + 22 * α / α ^ 2 := by gcongr
      _ ≤ 23 / α := by
        apply (le_div_iff₀ hα0).mpr
        field_simp
        nlinarith only [hα.2]
  have HE : |T * (1 + (R ^ 2 - 4 + T) / H)| ≤ |T| * (23 / α) := by
    rw [abs_mul]; gcongr
  have HRad : |2 * R / H - (R ^ 2 - 4 + T) * L / H ^ 2| ≤ 450 / α ^ 2 := by
    calc
      _ ≤ |2 * R / H| + |(R ^ 2 - 4 + T) * L / H ^ 2| := abs_sub _ _
      _ = 2 * R / H + |R ^ 2 - 4 + T| * |L| / H ^ 2 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2 * R / H), abs_div, abs_mul,
          abs_of_nonneg (sq_nonneg H)]
      _ ≤ 2 * 5 / α ^ 2 + (22 * α) * (20 * α) / (α ^ 2) ^ 2 := by gcongr
      _ = 450 / α ^ 2 := by field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ K * (23 / α) := HE.trans (mul_le_mul_of_nonneg_right hK (by positivity))
      _ = _ := by ring
  · calc
      _ ≤ (α ^ 2 / 1000) * (23 / α) := HE.trans (mul_le_mul_of_nonneg_right hT (by positivity))
      _ = _ := by field_simp
  · calc
      _ ≤ K * (450 / α ^ 2) := by rw [abs_mul]; exact mul_le_mul hK HRad (abs_nonneg _) hK0
      _ = _ := by ring
  · have HN' : |R ^ 2 - 4 + 2 * T| ≤ 23 * α := by
      have H := abs_add_le (R ^ 2 - 4 + T) T
      have Heq : R ^ 2 - 4 + 2 * T = (R ^ 2 - 4 + T) + T := by ring
      rw [Heq]
      nlinarith only [H, hN, hT, hα.1, hα.2]
    calc
      _ ≤ 1 + |R ^ 2 - 4 + 2 * T| / H := by
        have Ha : |1 + (R ^ 2 - 4 + 2 * T) / H| ≤ |(1 : ℝ)| + |(R ^ 2 - 4 + 2 * T) / H| := abs_add_le _ _
        simpa only [abs_one, abs_div, abs_of_pos hH0] using Ha
      _ ≤ 1 + 23 * α / α ^ 2 := by gcongr
      _ ≤ 24 / α := by
        apply (le_div_iff₀ hα0).mpr
        field_simp
        nlinarith only [hα.2]

end BianchiIX

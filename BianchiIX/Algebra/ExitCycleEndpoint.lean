import BianchiIX.Algebra.ExitCycleBounds
import BianchiIX.Algebra.PhaseBoundaryStability

noncomputable section

namespace BianchiIX

theorem exitTailGap_terminal_offset {α B R v : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    199 / 100 * α < exitTailGap R v - 2 ∧ exitTailGap R v - 2 < 201 / 100 * α := by
  have hα0 : 0 < α := hα.1
  have hRc := abs_le.mp hR
  have hRlo : 2 + 19999 / 10000 * α ≤ R := by linarith only [hRc.1, hB]
  have hR0 : 0 ≤ R := by linarith only [hRlo, hα.1]
  have hRsq := (sq_le_sq₀ (by positivity) hR0).mpr hRlo
  have hvsq := (sq_le_sq₀ hv.1 (by positivity)).mpr hv.2
  have hvR : v ^ 2 ≤ R ^ 2 := by nlinarith only [hRsq, hvsq, hα.1, sq_nonneg α]
  have ht := exitTailGap_sq hvR
  have ht0 : 0 ≤ exitTailGap R v := Real.sqrt_nonneg _
  have hs : (2 + 199 / 100 * α) ^ 2 < (exitTailGap R v) ^ 2 := by
    nlinarith only [hRsq, hvsq, ht, hα.1, sq_nonneg α]
  have hlo := (sq_lt_sq₀ (by positivity) ht0).mp hs
  have hhi : exitTailGap R v ≤ R := (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])
  constructor <;> linarith only [hlo, hhi, hRc.2, hB, hα.1]

theorem exitCycle_terminal_phase_bounds {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    19 / (10 * α) < 4 * (exitTailGap R v - 2) / axisCycleDenom (1 - exitTailGap R v) u v w ∧
      4 * (exitTailGap R v - 2) / axisCycleDenom (1 - exitTailGap R v) u v w < 21 / (10 * α) := by
  have hα0 : 0 < α := hα.1
  have HH := exitCycleDenom_terminal_bounds hα hB hR hw hv
  have HG := exitTailGap_terminal_offset hα hB hR hv
  have hH0 : 0 < axisCycleDenom (1 - exitTailGap R v) u v w := lt_trans (by positivity) HH.1
  constructor
  · apply (div_lt_div_iff₀ (by positivity) hH0).mpr
    nlinarith only [HH.2, mul_lt_mul_of_pos_right HG.1 hα.1, sq_pos_of_pos hα.1]
  · apply (div_lt_div_iff₀ hH0 (by positivity)).mpr
    nlinarith only [HH.1, mul_lt_mul_of_pos_right HG.2 hα.1, sq_pos_of_pos hα.1]

theorem exitCycle_terminal_radius_bounds {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α ^ 2 / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    let H := axisCycleDenom (1 - exitTailGap R v) u v w
    let m := 1 - 4 * (2 - exitTailGap R v) / H
    19 / (10 * α) < coreRadius m (4 * w / H) ∧ coreRadius m (4 * w / H) < 11 / (5 * α) := by
  intro H m
  have hα0 : 0 < α := hα.1
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have hBlin : B ≤ α / 10000 := hB.trans (by nlinarith only [hα.1, hα.2])
  have HH := exitCycleDenom_terminal_bounds hα hBlin hR hw hv
  have Hphase := exitCycle_terminal_phase_bounds hα hBlin hR hw hv
  have hm : m - 1 = 4 * (exitTailGap R v - 2) / H := by dsimp only [m]; ring
  change 19 / (10 * α) < 4 * (exitTailGap R v - 2) / H ∧
    4 * (exitTailGap R v - 2) / H < 21 / (10 * α) at Hphase
  rw [← hm] at Hphase
  have hm0 : 0 < m - 1 := lt_trans (by positivity) Hphase.1
  have hH : 39 / 10 * α ^ 2 < H := by nlinarith only [HH.1, sq_pos_of_pos hα.1]
  have hwB : |w| ≤ B := by linarith only [hw, abs_nonneg u]
  have HW := exitCycle_newWall_small hα.1 hB0 hB hH hwB
  have hlo : m - 1 ≤ coreRadius m (4 * w / H) := phaseNorm_ge hm0.le
  have hhi : coreRadius m (4 * w / H) ≤ (m - 1) + 1 / 5000 := by
    have HE := phaseNorm_le_abs_add (m - 1) (4 * w / H)
    rw [abs_of_pos hm0] at HE
    exact HE.trans (add_le_add_right HW (m - 1))
  refine ⟨Hphase.1.trans_le hlo, ?_⟩
  apply (lt_div_iff₀ (by positivity : 0 < 5 * α)).mpr
  have HM := (lt_div_iff₀ (by positivity : 0 < 10 * α)).mp Hphase.2
  nlinarith only [HM, mul_le_mul_of_nonneg_right hhi hα.1.le, hα.2]

theorem exitCycle_positive_wall_scale {α H v : ℝ} (hα : 0 < α) (hv : 0 ≤ v)
    (hH : 399 / 100 * α ^ 2 < H ∧ H < 401 / 100 * α ^ 2) :
    v / (2 * α ^ 2) ≤ 4 * v / H ∧ 4 * v / H ≤ 2 * v / α ^ 2 := by
  have hH0 : 0 < H := lt_trans (by positivity) hH.1
  constructor
  · apply (div_le_div_iff₀ (by positivity) hH0).mpr
    have HH : H ≤ 8 * α ^ 2 := by nlinarith only [hH.2, sq_nonneg α]
    nlinarith only [mul_le_mul_of_nonneg_left HH hv]
  · have HB : |4 * v / H| ≤ 2 * v / α ^ 2 := exitCycle_newWall_bound hα hv
      (by nlinarith only [hH.1, sq_pos_of_pos hα]) (by rw [abs_of_nonneg hv])
    exact (le_abs_self _).trans HB

end BianchiIX

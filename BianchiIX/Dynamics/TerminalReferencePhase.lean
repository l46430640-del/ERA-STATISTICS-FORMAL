import BianchiIX.Algebra.ExitCycleBoundary
import BianchiIX.Dynamics.ProjectiveCycle
import BianchiIX.Dynamics.StableSingleStrongWall
import BianchiIX.Dynamics.CoreTailBoundary
import BianchiIX.Dynamics.EntranceStablePhase

noncomputable section

namespace BianchiIX

theorem exitCycle_boundary_stable_projection {α v : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hv : 0 ≤ v ∧ v ≤ α ^ 2 / 400) :
    let R := 2 + 2 * α
    let H := axisCycleDenom (1 - exitTailGap R v) 0 v 0
    stableBoundaryProjection (1 - 4 * (2 - exitTailGap R v) / H) (4 * v / H) 0 = 1 + 2 / α := by
  intro R H
  have hα0 : 0 < α := hα.1
  have hR : 2 < R := by dsimp only [R]; linarith only [hα.1]
  have hvs : v ≤ α / 100 := by nlinarith only [hv.2, mul_nonneg hα.1.le (sub_nonneg.mpr hα.2)]
  have hvR : v ^ 2 ≤ R ^ 2 := by dsimp only [R]; nlinarith only [hv.1, hvs, hα.1, hα.2]
  have HB : (0 : ℝ) ≤ α / 10000 := by positivity
  have HR : |R - (2 + 2 * α)| ≤ 0 := by dsimp only [R]; simp
  have HW : |(0 : ℝ)| + |(0 : ℝ)| ≤ 0 := by norm_num
  have HH := exitCycleDenom_terminal_bounds hα HB HR HW ⟨hv.1, hvs⟩
  have HP := exitCycle_terminal_phase_bounds hα HB HR HW ⟨hv.1, hvs⟩
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) HH.1.le
  have hlow : (19 / 10 : ℝ) ≤ 19 / (10 * α) := by
    apply (le_div_iff₀ (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.2]
  have hm : 2 ≤ 1 - 4 * (2 - exitTailGap R v) / H := by
    have HE : 1 - 4 * (2 - exitTailGap R v) / H - 1 = 4 * (exitTailGap R v - 2) / H := by ring
    change 19 / (10 * α) < 4 * (exitTailGap R v - 2) / H ∧ _ at HP
    linarith only [HE, HP.1, hlow]
  have hu : |4 * v / H| ≤ 1 / 200 := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hv.1) hH0.le)]
    apply (exitCycle_positive_wall_scale hα.1 hv.1 HH).2.trans
    apply (div_le_iff₀ (sq_pos_of_pos hα.1)).mpr
    linarith only [hv.2]
  rw [stableBoundaryProjection_strong hm (by simp) hu, exitCycle_boundary_upperRoot hR hvR]
  dsimp only [R]
  rw [show 2 + 2 * α - 2 = 2 * α by ring]
  field_simp
  ring

/-- D.21 is an exact identity for the stable projection of the actual zero-wall reference tail. -/
theorem terminal_reference_stable_radius {α η : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hη : 0 < η ∧ η ≤ 1 / 400) {J : ℕ} (hJ : 2 ≤ J) :
    entranceStableRadius (projectiveCycle (coreTailState (η * α ^ J) ![2 + 2 * α, 0, 0])) = 2 / α := by
  let R := 2 + 2 * α
  let h := η * α ^ J
  let H := axisCycleDenom (1 - exitTailGap R h) 0 h 0
  have hα0 : 0 < α := hα.1
  have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
  have hsmall : h ≤ α ^ 2 / 400 := by
    have hp := pow_le_pow_of_le_one hα.1.le hα.2 hJ
    change η * α ^ J ≤ α ^ 2 / 400
    nlinarith only [mul_le_mul_of_nonneg_left hp hη.1.le, mul_le_mul_of_nonneg_right hη.2 (sq_nonneg α)]
  have hh1 : h < 1 := by nlinarith only [hsmall, mul_nonneg hα.1.le (sub_nonneg.mpr hα.2), hα.2]
  have hR : 1 < R := by dsimp only [R]; linarith only [hα.1]
  have HT := (coreTail_reference_regular hR ⟨hh, hh1⟩).2.1
  change coreTailState h ![R, 0, 0] = ![1 - exitTailGap R h, 0, h, 0] at HT
  have HZ : projectiveCycle (coreTailState h ![R, 0, 0]) =
      ![1 - 4 * (2 - exitTailGap R h) / H, 4 * h / H, 0, 0] := by
    rw [HT]
    ext i
    fin_cases i <;> dsimp [projectiveCycle, projectiveCycleDenom, H] <;> ring
  have HP := exitCycle_boundary_stable_projection hα ⟨hh.le, hsmall⟩
  change entranceStableRadius (projectiveCycle (coreTailState h ![R, 0, 0])) = _
  rw [HZ]
  change coreRadius (stableBoundaryProjection (1 - 4 * (2 - exitTailGap R h) / H) (4 * h / H) 0) 0 = _
  rw [HP]
  change Real.sqrt ((1 + 2 / α - 1) ^ 2 + 0 ^ 2) = 2 / α
  rw [show (1 + 2 / α - 1) ^ 2 + 0 ^ 2 = (2 / α) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

end BianchiIX

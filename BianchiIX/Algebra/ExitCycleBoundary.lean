import BianchiIX.Algebra.ExitCycleEndpoint
import BianchiIX.Algebra.SingleStrongWall

noncomputable section

namespace BianchiIX

theorem exitCycle_boundary_phase {R v : ℝ} (hR : 2 < R) (hv : v ^ 2 ≤ R ^ 2) :
    let H := axisCycleDenom (1 - exitTailGap R v) 0 v 0
    0 < H ∧ 1 - 4 * (2 - exitTailGap R v) / H = (R ^ 2 - 4) / H := by
  intro H
  have hR0 : 0 < R := by linarith only [hR]
  have hgap0 := Real.sqrt_nonneg (R ^ 2 - v ^ 2)
  have hden : 0 < R + exitTailGap R v := add_pos_of_pos_of_nonneg hR0 hgap0
  have HH := exitCycle_denom_split hR0 hv (0 : ℝ) 0
  have Hpos : 0 < H := by
    dsimp only [H]
    rw [HH]
    nlinarith only [sq_pos_of_pos (sub_pos.mpr hR), div_nonneg (by positivity : 0 ≤ 4 * v ^ 2) hden.le]
  have hs := exitTailGap_sq hv
  have Hdef : H = R ^ 2 + 4 - 4 * exitTailGap R v := by
    dsimp only [H, axisCycleDenom, curvature]
    nlinarith only [hs]
  refine ⟨Hpos, ?_⟩
  apply (eq_div_iff Hpos.ne').mpr
  field_simp
  linarith only [Hdef]

theorem exitCycle_boundary_invariant {R v : ℝ} (hR : 2 < R) (hv : v ^ 2 ≤ R ^ 2) :
    let H := axisCycleDenom (1 - exitTailGap R v) 0 v 0
    singleStrongInvariant (1 - 4 * (2 - exitTailGap R v) / H) (4 * v / H) = 2 + 16 / (R ^ 2 - 4) := by
  intro H
  obtain ⟨hH, hm⟩ := exitCycle_boundary_phase hR hv
  change 0 < H at hH
  change 1 - 4 * (2 - exitTailGap R v) / H = (R ^ 2 - 4) / H at hm
  have hN : 0 < R ^ 2 - 4 := by nlinarith only [hR]
  have hs := exitTailGap_sq hv
  have Hdef : H = R ^ 2 + 4 - 4 * exitTailGap R v := by
    dsimp only [H, axisCycleDenom, curvature]
    nlinarith only [hs]
  have hpoly : H ^ 2 + (R ^ 2 - 4) ^ 2 + 16 * v ^ 2 = (2 * (R ^ 2 - 4) + 16) * H := by
    rw [Hdef, show v ^ 2 = R ^ 2 - (exitTailGap R v) ^ 2 by linarith only [hs]]
    ring
  rw [hm]
  unfold singleStrongInvariant
  field_simp
  nlinarith only [hpoly]

theorem exitCycle_boundary_upperRoot {R v : ℝ} (hR : 2 < R) (hv : v ^ 2 ≤ R ^ 2) :
    let H := axisCycleDenom (1 - exitTailGap R v) 0 v 0
    singleStrongUpperRoot (singleStrongInvariant (1 - 4 * (2 - exitTailGap R v) / H) (4 * v / H)) =
      (R + 2) / (R - 2) := by
  intro H
  rw [exitCycle_boundary_invariant hR hv]
  have hN : 0 < R ^ 2 - 4 := by nlinarith only [hR]
  have hρ : 0 < R - 2 := sub_pos.mpr hR
  apply Eq.symm
  apply singleStrongUpperRoot_unique (by linarith only [div_pos (by norm_num : (0 : ℝ) < 16) hN])
    ((lt_div_iff₀ hρ).mpr (by linarith))
  field_simp
  ring

end BianchiIX

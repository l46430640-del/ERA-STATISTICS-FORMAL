import BianchiIX.Algebra.ConnectionConeSize

noncomputable section

namespace BianchiIX

/-- The strong radial response gains two inverse radial powers uniformly in waiting length. -/
theorem connection_radial_decay {μ L : ℝ} (hμ : 0 < μ) (hL : 1 ≤ L) :
    L * Real.exp (-μ * L / 4) ≤ 64 / μ ^ 2 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  let E := Real.exp (-μ * L / 8)
  have hE : 0 < E := Real.exp_pos _
  have H := affine_mul_exp_neg_le_one (μ * L / 8)
  rw [show -(μ * L / 8) = -μ * L / 8 by ring] at H
  have H1 : μ * L * E ≤ 8 := by nlinarith only [H, hE]
  have H2 : μ * E ≤ 8 := by
    have Hl := mul_le_mul_of_nonneg_left hL (mul_nonneg hμ.le hE.le)
    nlinarith only [Hl, H1]
  have Hprod := mul_le_mul H2 H1 (by positivity : 0 ≤ μ * L * E) (by norm_num : (0 : ℝ) ≤ 8)
  have heq : E * E = Real.exp (-μ * L / 4) := by
    dsimp only [E]
    rw [← Real.exp_add]
    congr 1
    ring
  apply (le_div_iff₀ (sq_pos_of_pos hμ)).mpr
  calc
    _ = (μ * E) * (μ * L * E) := by rw [← heq]; ring
    _ ≤ 64 := by norm_num at Hprod ⊢; exact Hprod

end BianchiIX

import BianchiIX.Algebra.ConnectionConeSize

noncomputable section

namespace BianchiIX

theorem exists_connection_cone_threshold :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ Real.sqrt ε ≤ 1 / 1000000 ∧ ε ≤ Real.exp (-256) := by
  let ε := min ((1 / 1000000 : ℝ) ^ 2) (Real.exp (-256))
  have hε0 : 0 < ε := lt_min (by norm_num) (Real.exp_pos _)
  have hεd : ε ≤ (1 / 1000000 : ℝ) ^ 2 := min_le_left _ _
  refine ⟨ε, hε0, ?_, ?_, min_le_right _ _⟩
  · exact hεd.trans (by norm_num)
  · exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hεd]⟩

/-- A radial lower bound suffices to compare the weak margin with the phase error. -/
theorem connection_cone_gap {μ L : ℝ} (hμ : 4 ≤ μ) (hL : 4 ≤ L) :
    1 / μ ≤ 1 - Real.exp (-L / (2 * μ)) ∧ 1 - Real.exp (-L / (2 * μ)) ≤ 1 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hx : 0 ≤ 2 / μ := by positivity
  have hx1 : 2 / μ ≤ 1 := (div_le_one hμ0).mpr (by linarith only [hμ])
  have H := exp_neg_le_one_sub_half hx hx1
  have Hexp : Real.exp (-L / (2 * μ)) ≤ Real.exp (-(2 / μ)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ -4 / (2 * μ) := div_le_div_of_nonneg_right (neg_le_neg hL) (by positivity)
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · have heq : 2 / μ / 2 = 1 / μ := by ring
    rw [heq] at H
    linarith only [H, Hexp]
  · linarith only [Real.exp_pos (-L / (2 * μ))]

theorem connection_cone_phase_margin {μ L d : ℝ} (hμ : 4 ≤ μ) (hL : 4 ≤ L)
    (hd : |d - 1| ≤ 1 / (4 * μ)) :
    3 / 4 ≤ d ∧
      1 / 4 ≤ (1 / 3) * d ∧
      Real.exp (-L / (2 * μ)) ≤ (1 - (1 - Real.exp (-L / (2 * μ))) / 2) * d := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  let γ := 1 - Real.exp (-L / (2 * μ))
  have hg := connection_cone_gap hμ hL
  have hg0 : 0 ≤ γ := (by positivity : (0 : ℝ) ≤ 1 / μ).trans hg.1
  have hsmall : 1 / (4 * μ) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * μ)).mpr
    linarith only [hμ]
  have hdlo := (abs_le.mp hd).1
  have hd3 : 3 / 4 ≤ d := by linarith only [hdlo, hsmall]
  have hdγ : 1 - γ / 4 ≤ d := by
    have heq : 1 / (4 * μ) = (1 / μ) / 4 := by ring
    rw [heq] at hdlo
    linarith only [hg.1, hdlo]
  refine ⟨hd3, by linarith only [hd3], ?_⟩
  have hfac : 0 ≤ 1 - γ / 2 := by linarith only [hg.2]
  have H := mul_le_mul_of_nonneg_left hdγ hfac
  have Hfinal : 1 - γ ≤ (1 - γ / 2) * d := by nlinarith only [H, hg0, sq_nonneg γ]
  dsimp only [γ] at Hfinal
  linarith only [Hfinal]

end BianchiIX

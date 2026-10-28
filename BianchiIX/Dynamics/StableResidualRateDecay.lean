import BianchiIX.Dynamics.StableRescaledResidualRate
import BianchiIX.Dynamics.StableResidualFlowWeights
import BianchiIX.Dynamics.StableResidualJetDecay

noncomputable section

namespace BianchiIX

theorem exists_stableRescaledResidualRate_weighted_decay :
    ∃ C > (0 : ℝ), ∀ (c s : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| < 1 / 40 →
      |y 1| < 1 / 200 → |y 2| < 1 / 200 → 0 ≤ s →
      let b := |y 1| + |y 2|
      let q := Real.exp (-(c + 1) / 16 * s)
      ContDiffAt ℝ 2 (stableRescaledResidualRate (c + 1) s) y ∧
        |stableRescaledResidualRate (c + 1) s y| ≤ C / (c + 1) ^ 2 * |y 1| * b ^ 3 * q ∧
        (∀ v, |fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v| ≤
          C / (c + 1) ^ 2 * b ^ 3 * stableFirstInputWeight b v * q) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w| ≤
          C / (c + 1) ^ 2 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q) := by
  obtain ⟨C, hC, HC⟩ := exists_stableRescaledResidualRate_bounds
  let E := Real.exp 6
  let F := 400000000 * E ^ 3
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by norm_num)
  have hE0 : 0 ≤ E := le_trans (by norm_num) hE
  have hF : 0 < F := by dsimp [F, E]; positivity
  have hF1 : 1 ≤ F := by
    have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hE 3
    dsimp [F]
    norm_num only [one_pow] at H
    linarith
  have hF969 : 969 * E ≤ F := by
    have H := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hE 2) hE0
    norm_num only [one_pow, mul_one] at H
    dsimp [F]
    nlinarith only [H, hE0]
  refine ⟨F * C, mul_pos hF hC, ?_⟩
  intro c s y hc hm hu hw hs
  dsimp only
  let b := |y 1| + |y 2|
  let q := Real.exp (-(c + 1) / 16 * s)
  let Q := C / (c + 1) ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hscale : F * C / (c + 1) ^ 2 = F * Q := by dsimp [Q]; ring
  rw [hscale]
  obtain ⟨hreg, h0, h1, h2⟩ := HC c s y hc hm hu hw hs
  have hY := stableRescaledFlow_residual_weights hc hm.le hu.le hw.le hs
  have hU : |stableRescaledFlow (c + 1) y s 1| ≤ b * q :=
    hY.2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg (y 2))) hq)
  have hJ (v : StableState) := stableRescaledDifferential_residual_weights hc hm.le hu.le hw.le hs v
  have hH (v w : StableState) := stableRescaledSecondDifferential_residual_weights hc hm hu hw hs v w
  refine ⟨hreg, ?_, ?_, ?_⟩
  · have h3 := pow_le_pow_left₀
      (by positivity : 0 ≤ |stableRescaledFlow (c + 1) y s 1| + |stableRescaledFlow (c + 1) y s 2|) hY.1 3
    have H0 := mul_le_mul_of_nonneg_left
      (mul_le_mul hY.2 h3 (by positivity) (by positivity)) hQ
    have H1 := mul_le_mul_of_nonneg_right hF1 (show 0 ≤ Q * |y 1| * b ^ 3 * q by positivity)
    dsimp only [Q, b, q] at H0 H1 ⊢
    nlinarith only [h0, H0, H1]
  · intro v
    have H := stableResidualFirstDecay_bound hb hE0 hq hY.1 hU (hJ v).1 (hJ v).2.1 (hJ v).2.2
    have H0 := mul_le_mul_of_nonneg_left H hQ
    have H1 := mul_le_mul_of_nonneg_right hF969
      (show 0 ≤ Q * b ^ 3 * stableFirstInputWeight b v * q by
        have := stableFirstInputWeight_nonneg hb v
        positivity)
    have R := h1 v
    dsimp only [Q, b, q, E] at H0 H1 ⊢
    nlinarith only [R, H0, H1]
  · intro v w
    have H := stableResidualSecondDecay_bound hb hb1 hE hq hY.1 hU
      (hJ v).1 (hJ w).1 (hJ v).2.1 (hJ w).2.1 (hJ v).2.2 (hJ w).2.2 (hH v w).1 (hH v w).2
    have H0 := mul_le_mul_of_nonneg_left H hQ
    have R := h2 v w
    dsimp only [Q, b, q, E, F] at H0 ⊢
    nlinarith only [R, H0]

end BianchiIX

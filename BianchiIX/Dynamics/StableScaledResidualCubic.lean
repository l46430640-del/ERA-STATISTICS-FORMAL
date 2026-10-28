import BianchiIX.Dynamics.StableScaledResidualCoefficients
import BianchiIX.Algebra.StableCubicBounds

noncomputable section

namespace BianchiIX

def stableScaledResidual (K : ℝ) (y : StableState) : ℝ :=
  stableResidualClock K y * stableCorrectedResidual (y 0) (y 1) (y 2)

def stableScaledResidualCubic (K : ℝ) (y : StableState) : ℝ :=
  ∑ i : Fin 4, stableScaledResidualCoefficient K i y * stableCubicMonomial i y

def stableCubicFirstBudget (y v : StableState) : ℝ :=
  (|y 1| + |y 2|) ^ 3 * ‖v‖ + 3 * (|y 1| + |y 2|) ^ 2 * ‖![v 1, v 2]‖

def stableCubicSecondBudget (y v w : StableState) : ℝ :=
  (|y 1| + |y 2|) ^ 3 * ‖v‖ * ‖w‖ +
    3 * (|y 1| + |y 2|) ^ 2 * (‖v‖ * ‖![w 1, w 2]‖ + ‖![v 1, v 2]‖ * ‖w‖) +
    6 * (|y 1| + |y 2|) * ‖![v 1, v 2]‖ * ‖![w 1, w 2]‖

theorem stableCubicFirstBudget_nonneg (y v : StableState) : 0 ≤ stableCubicFirstBudget y v := by
  unfold stableCubicFirstBudget
  positivity

theorem stableCubicSecondBudget_nonneg (y v w : StableState) : 0 ≤ stableCubicSecondBudget y v w := by
  unfold stableCubicSecondBudget
  positivity

theorem stableScaledResidual_factor (K : ℝ) (y : StableState) :
    stableScaledResidual K y = y 1 * stableScaledResidualCubic K y := by
  simp [stableScaledResidual, stableScaledResidualCubic, stableScaledResidualCoefficient,
    stableResidualCoefficient, stableCenterWeakProjection_apply, stableCubicMonomial,
    stableCorrectedResidual, Fin.sum_univ_succ]
  ring

theorem stableScaledResidualCubic_bounds_of_coefficients {K B : ℝ} {y : StableState} (hB : 0 ≤ B)
    (ha : ∀ i : Fin 4, ContDiffAt ℝ 2 (stableScaledResidualCoefficient K i) y ∧
      |stableScaledResidualCoefficient K i y| ≤ B ∧
      ‖fderiv ℝ (stableScaledResidualCoefficient K i) y‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient K i)) y‖ ≤ B) :
    ContDiffAt ℝ 2 (stableScaledResidualCubic K) y ∧
      |stableScaledResidualCubic K y| ≤ 4 * B * (|y 1| + |y 2|) ^ 3 ∧
      (∀ v, |fderiv ℝ (stableScaledResidualCubic K) y v| ≤ 4 * B * stableCubicFirstBudget y v) ∧
      (∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w| ≤ 4 * B * stableCubicSecondBudget y v w) := by
  let f := fun (i : Fin 4) (z : StableState) => stableScaledResidualCoefficient K i z * stableCubicMonomial i z
  have hf (i : Fin 4) : ContDiffAt ℝ 2 (f i) y :=
    (ha i).1.mul (contDiff_stableCubicMonomial 2 i).contDiffAt
  have ha1 (i : Fin 4) (v : StableState) : |fderiv ℝ (stableScaledResidualCoefficient K i) y v| ≤ B * ‖v‖ :=
    ((fderiv ℝ (stableScaledResidualCoefficient K i) y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (ha i).2.2.1 (norm_nonneg v))
  have ha2 (i : Fin 4) (v w : StableState) : |fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient K i)) y v w| ≤ B * ‖v‖ * ‖w‖ :=
    (((fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient K i)) y) v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient K i)) y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (ha i).2.2.2 (norm_nonneg v))) (norm_nonneg w))
  have h0 (i : Fin 4) : |f i y| ≤ B * (|y 1| + |y 2|) ^ 3 := by
    rw [show f i y = stableScaledResidualCoefficient K i y * stableCubicMonomial i y from rfl, abs_mul]
    exact mul_le_mul (ha i).2.1 (stableCubicMonomial_bound i y) (abs_nonneg _) hB
  have h1 (i : Fin 4) (v : StableState) : |fderiv ℝ (f i) y v| ≤ B * stableCubicFirstBudget y v := by
    dsimp only [f]
    rw [fderiv_fun_mul ((ha i).1.differentiableAt (by norm_num))
      ((contDiff_stableCubicMonomial 1 i).differentiable (by norm_num) y)]
    change |stableScaledResidualCoefficient K i y * fderiv ℝ (stableCubicMonomial i) y v +
      stableCubicMonomial i y * fderiv ℝ (stableScaledResidualCoefficient K i) y v| ≤ _
    have H := abs_add_le (stableScaledResidualCoefficient K i y * fderiv ℝ (stableCubicMonomial i) y v)
      (stableCubicMonomial i y * fderiv ℝ (stableScaledResidualCoefficient K i) y v)
    simp only [abs_mul] at H
    have H0 := mul_le_mul (ha i).2.1 (stableCubicMonomial_first_bound i y v) (abs_nonneg _) hB
    have H1 := mul_le_mul (stableCubicMonomial_bound i y) (ha1 i v) (abs_nonneg _) (by positivity : 0 ≤ (|y 1| + |y 2|) ^ 3)
    dsimp [stableCubicFirstBudget]
    nlinarith only [H, H0, H1]
  have h2 (i : Fin 4) (v w : StableState) : |fderiv ℝ (fderiv ℝ (f i)) y v w| ≤ B * stableCubicSecondBudget y v w := by
    dsimp only [f]
    rw [fderiv2_mul_apply (ha i).1 (contDiff_stableCubicMonomial 2 i).contDiffAt]
    have H0 := mul_le_mul (ha i).2.1 (stableCubicMonomial_second_bound i y v w) (abs_nonneg _) hB
    have H1 := mul_le_mul (ha1 i v) (stableCubicMonomial_first_bound i y w) (abs_nonneg _) (mul_nonneg hB (norm_nonneg v))
    have H2 := mul_le_mul (ha1 i w) (stableCubicMonomial_first_bound i y v) (abs_nonneg _) (mul_nonneg hB (norm_nonneg w))
    have H3 := mul_le_mul (ha2 i v w) (stableCubicMonomial_bound i y) (abs_nonneg _)
      (mul_nonneg (mul_nonneg hB (norm_nonneg v)) (norm_nonneg w))
    have htri (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
      linarith only [abs_add_le a b, abs_add_le (a + b) c, abs_add_le (a + b + c) d]
    have H := htri (stableScaledResidualCoefficient K i y * fderiv ℝ (fderiv ℝ (stableCubicMonomial i)) y v w)
      (fderiv ℝ (stableScaledResidualCoefficient K i) y v * fderiv ℝ (stableCubicMonomial i) y w)
      (fderiv ℝ (stableScaledResidualCoefficient K i) y w * fderiv ℝ (stableCubicMonomial i) y v)
      (fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient K i)) y v w * stableCubicMonomial i y)
    simp only [abs_mul] at H
    dsimp [stableCubicSecondBudget]
    nlinarith only [H, H0, H1, H2, H3]
  refine ⟨ContDiffAt.sum (fun i _ => hf i), ?_, ?_, ?_⟩
  · exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ => h0 i)).trans_eq (by simp; ring))
  · intro v
    change |fderiv ℝ (fun z => ∑ i : Fin 4, f i z) y v| ≤ _
    rw [fderiv_fun_sum (fun i _ => (hf i).differentiableAt (by norm_num))]
    simp only [sum_apply]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ => h1 i v)).trans_eq (by simp; ring))
  · intro v w
    change |fderiv ℝ (fderiv ℝ (fun z => ∑ i : Fin 4, f i z)) y v w| ≤ _
    rw [fderiv2_finset_sum_apply Finset.univ (fun i _ => hf i)]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ => h2 i v w)).trans_eq (by simp; ring))

theorem exists_stableScaledResidualCubic_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| ≤ 1 / 10 →
      |y 1| ≤ 1 / 100 → |y 2| ≤ 1 / 100 →
      ContDiffAt ℝ 2 (stableScaledResidualCubic (c + 1)) y ∧
        |stableScaledResidualCubic (c + 1) y| ≤ C / (c + 1) ^ 2 * (|y 1| + |y 2|) ^ 3 ∧
        (∀ v, |fderiv ℝ (stableScaledResidualCubic (c + 1)) y v| ≤ C / (c + 1) ^ 2 * stableCubicFirstBudget y v) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidualCubic (c + 1))) y v w| ≤ C / (c + 1) ^ 2 * stableCubicSecondBudget y v w) := by
  obtain ⟨C, hC, HC⟩ := exists_stableScaledResidualCoefficient_bounds
  refine ⟨4 * C, by positivity, ?_⟩
  intro c y hc hm hu hw
  have H := stableScaledResidualCubic_bounds_of_coefficients (by positivity : 0 ≤ C / (c + 1) ^ 2) (HC c y hc hm hu hw)
  have hscale : 4 * (C / (c + 1) ^ 2) = 4 * C / (c + 1) ^ 2 := by ring
  simpa only [hscale] using H

end BianchiIX

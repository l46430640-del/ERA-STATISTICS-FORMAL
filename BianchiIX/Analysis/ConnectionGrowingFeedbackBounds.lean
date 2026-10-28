import BianchiIX.Analysis.ConnectionFeedbackBounds
import BianchiIX.Analysis.ConnectionGrowingSources

noncomputable section

namespace BianchiIX

theorem connectionPhase_growing_variation_bound {μ w A B : ℝ} {y : ProjectiveState}
    (hμ : 4 ≤ μ) (hw0 : 0 < w)
    (hm : |-y 0 - μ| ≤ 1 / 2) (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000)
    (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1)
    (d : Fin 4 → ℝ) (hζ : d 3 = 1 / w) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : |d 1| ≤ A + B) (hy : |d 2| ≤ B / μ ^ 2) :
    |connectionLogLinearizedRates y d 0| ≤
      64 * (y 1 / μ ^ 2 + (y 2 * y 3) ^ 2 / μ ^ 4) * |d 0| + 32 * y 1 * A +
      64 * (y 1 + (y 2 * y 3) ^ 2 / μ ^ 5) * B + connectionGrowingPhaseSource μ w y := by
  let G := connectionPhaseGPartials (-y 0) (y 1) (y 2) (y 3)
  have hsum : |connectionLogLinearizedRates y d 0| ≤
      |G 0| * |d 0| + |G 1| * |d 1| + |G 2| * |d 2| + |G 3| * |d 3| := by
    change |∑ j : Fin 4, G j * d j| ≤ _
    simpa [Fin.sum_univ_succ, abs_mul, add_assoc] using Finset.abs_sum_le_sum_abs (fun j : Fin 4 => G j * d j) Finset.univ
  have hwall : |G 3| * |d 3| ≤ connectionGrowingPhaseSource μ w y := by
    simpa [G, hζ, abs_div, div_eq_mul_inv] using (connectionGrowingSources_bound hμ hw0 hm hu hv hw).2.2
  have H := hsum.trans (add_le_add (add_le_add (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left hx (abs_nonneg _))) (mul_le_mul_of_nonneg_left hy (abs_nonneg _))) hwall)
  have hG := connectionPhaseGPartials_bounds hμ hm hu hv hw
  have hT := connectionPhase_transverse_row_bound hμ hm hu hv hw
  calc
    _ ≤ |G 0| * |d 0| + |G 1| * A + (|G 1| + |G 2| / μ ^ 2) * B + connectionGrowingPhaseSource μ w y :=
      H.trans_eq (by ring)
    _ ≤ _ := add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right hG.1 (abs_nonneg _)) (mul_le_mul_of_nonneg_right hG.2.1 hA))
      (mul_le_mul_of_nonneg_right hT hB)) (le_refl _)

def connectionGrowingFeedbackSource (μ u w : ℝ) (y : ProjectiveState) : ℝ :=
  1024 * y 1 * (1 + y 3 ^ 2 / (μ * w)) +
    64 * (y 1 + (y 2 * y 3) ^ 2 / μ ^ 5) * (12800 * u + 64 * y 3 ^ 2 / (μ * w)) +
    connectionGrowingPhaseSource μ w y

def connectionGrowingFeedbackBudget (μ u w : ℝ) : ℝ :=
  (u * (7296 + 1638400 * u + 204800 * w ^ 2 / μ ^ 3) + w * (2048 / μ ^ 5 + 8 / μ)) / μ

theorem continuous_connectionGrowingFeedbackSource (μ u w : ℝ) :
    Continuous (connectionGrowingFeedbackSource μ u w) := by
  unfold connectionGrowingFeedbackSource connectionGrowingPhaseSource
  fun_prop

theorem connectionGrowingFeedbackSource_nonneg {μ u w : ℝ} {y : ProjectiveState}
    (hμ : 0 ≤ μ) (hu : 0 ≤ u) (hw : 0 ≤ w) (hU : 0 ≤ y 1) (hW : 0 ≤ y 3) :
    0 ≤ connectionGrowingFeedbackSource μ u w y := by
  unfold connectionGrowingFeedbackSource connectionGrowingPhaseSource
  positivity

/-- The initial phase contribution is included in the ordinary growing-wall source budget. -/
theorem connectionGrowingFeedbackBudget_small {μ u w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    2 * w / μ + connectionGrowingFeedbackBudget μ u w ≤ 7500 * (u + w) / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ3 : 64 ≤ μ ^ 3 := by
    have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hμ 3
    norm_num at H
    exact H
  have hμ5 : 1024 ≤ μ ^ 5 := by
    have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hμ 5
    norm_num at H
    exact H
  have hu' : u ≤ 1 / 40000 := hu.2.trans
    ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 10000) (by norm_num : (0 : ℝ) < 4) hμ).trans_eq (by norm_num))
  have hw2 : w ^ 2 ≤ 1 / 100000000 := by
    have H := pow_le_pow_left₀ hw.1 hw.2 2
    norm_num at H
    exact H
  have Hw : 204800 * w ^ 2 / μ ^ 3 ≤ 1 := (div_le_iff₀ (by positivity : 0 < μ ^ 3)).mpr
    (by linarith only [hw2, hμ3])
  have Hμ5 : 2048 / μ ^ 5 ≤ (2 : ℝ) := (div_le_iff₀ (by positivity : 0 < μ ^ 5)).mpr (by linarith only [hμ5])
  have Hμ : 8 / μ ≤ (2 : ℝ) := (div_le_iff₀ hμ0).mpr (by linarith only [hμ])
  have HU := mul_le_mul_of_nonneg_left
    (show 7296 + 1638400 * u + 204800 * w ^ 2 / μ ^ 3 ≤ 7500 by linarith only [hu', Hw]) hu.1
  have HW := mul_le_mul_of_nonneg_left
    (show 2048 / μ ^ 5 + 8 / μ + 2 ≤ (7500 : ℝ) by linarith only [Hμ5, Hμ]) hw.1
  calc
    _ = (u * (7296 + 1638400 * u + 204800 * w ^ 2 / μ ^ 3) + w * (2048 / μ ^ 5 + 8 / μ + 2)) / μ := by
      unfold connectionGrowingFeedbackBudget
      ring
    _ ≤ (u * 7500 + w * 7500) / μ := div_le_div_of_nonneg_right (add_le_add HU HW) hμ0.le
    _ = _ := by ring

end BianchiIX

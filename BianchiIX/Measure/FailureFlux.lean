import BianchiIX.Measure.ClippedLogIntegral
import BianchiIX.Measure.DyadicFlux
import BianchiIX.Measure.Capture

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def logarithmicFluxConstant (C δ : ℝ) : ℝ :=
  (1 + (Real.log C + 1 + 2 * δ) + (Real.log C + 1 + 2 * δ) ^ 2 / 2) / δ ^ 2

theorem logarithmicFluxConstant_nonneg {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ) :
    0 ≤ logarithmicFluxConstant C δ := by
  have hlog := Real.log_nonneg hC
  unfold logarithmicFluxConstant
  positivity

def logarithmicLayerCost (a C δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1,
    ENNReal.ofReal (min a ((C * a ^ (-2 * δ)) * (x * y) ^ δ) / (x * y))

theorem logarithmicLayerCost_le {a C δ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hC : 1 ≤ C) (hδ : 0 < δ) :
    logarithmicLayerCost a C δ ≤
      ENNReal.ofReal (logarithmicFluxConstant C δ * a * (1 + |Real.log a|) ^ 2) := by
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hB : 0 < C * a ^ (-2 * δ) := mul_pos hC0 (Real.rpow_pos_of_pos ha _)
  unfold logarithmicLayerCost
  rw [lintegral_clipped_log_two ha hB hδ]
  apply ENNReal.ofReal_le_ofReal
  let L : ℝ := 1 + |Real.log a|
  let K : ℝ := Real.log C + 1 + 2 * δ
  let z : ℝ := max (Real.log (C * a ^ (-2 * δ) / a)) 0
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hloga : Real.log a ≤ 0 := Real.log_nonpos ha.le ha1
  have hlogs : Real.log (C * a ^ (-2 * δ) / a) = Real.log C + (1 + 2 * δ) * |Real.log a| := by
    rw [Real.log_div (ne_of_gt hB) (ne_of_gt ha),
      Real.log_mul (ne_of_gt hC0) (ne_of_gt (Real.rpow_pos_of_pos ha _)), Real.log_rpow ha,
      abs_of_nonpos hloga]
    ring
  have hz : z = Real.log C + (1 + 2 * δ) * |Real.log a| := by
    dsimp only [z]
    rw [hlogs, max_eq_left (by positivity)]
  have hL : 1 ≤ L := by dsimp [L]; linarith [abs_nonneg (Real.log a)]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hz0 : 0 ≤ z := le_max_right _ _
  have hzle : z ≤ K * L := by
    rw [hz]
    dsimp [K, L]
    nlinarith [mul_nonneg hlogC (abs_nonneg (Real.log a))]
  have hsq := pow_le_pow_left₀ hz0 hzle 2
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hKLL := mul_le_mul_of_nonneg_left hLL hK
  have hpoly : 1 + z + z ^ 2 / 2 ≤ (1 + K + K ^ 2 / 2) * L ^ 2 := by
    nlinarith
  have hp : 0 ≤ 1 + z + z ^ 2 / 2 := by positivity
  change min a (C * a ^ (-2 * δ)) / δ ^ 2 * (1 + z + z ^ 2 / 2) ≤
    logarithmicFluxConstant C δ * a * L ^ 2
  calc
    _ ≤ a / δ ^ 2 * (1 + z + z ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg δ)) hp
    _ ≤ a / δ ^ 2 * ((1 + K + K ^ 2 / 2) * L ^ 2) :=
      mul_le_mul_of_nonneg_left hpoly (div_nonneg ha.le (sq_nonneg δ))
    _ = _ := by dsimp [logarithmicFluxConstant, K]; ring

theorem finite_flux_of_logarithmic_layers {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E boundary : Set X} {F : ℕ → Set X} {d A C δ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hA : 0 ≤ A) (hC : 1 ≤ C) (hδ : 0 < δ)
    (hcover : E ⊆ boundary ∪ ⋃ j, F j) (hboundary : μ boundary = 0)
    (hF : ∀ j, μ (F j) ≤ ENNReal.ofReal A * logarithmicLayerCost (dyadicScale d j) C δ) :
    μ E ≤ ENNReal.ofReal (11 * (A * logarithmicFluxConstant C δ) * d * (1 + |Real.log d|) ^ 2) ∧
      μ E ≠ ⊤ := by
  apply finite_flux_of_dyadic_bounds hd hd1
    (mul_nonneg hA (logarithmicFluxConstant_nonneg hC hδ)) hcover hboundary
  intro j
  calc
    μ (F j) ≤ ENNReal.ofReal A * logarithmicLayerCost (dyadicScale d j) C δ := hF j
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal
        (logarithmicFluxConstant C δ * dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2) :=
      mul_le_mul le_rfl (logarithmicLayerCost_le (dyadicScale_pos hd j)
        ((dyadicScale_le hd.le j).trans hd1) hC hδ) (by positivity) (by positivity)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      ring

theorem ae_leaves_failure_of_logarithmic_layers {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E boundary D : Set X} {F : ℕ → Set X} {d A C δ : ℝ} {R : X → X} {j : X → ℝ≥0∞}
    (hd : 0 < d) (hd1 : d ≤ 1) (hA : 0 ≤ A) (hC : 1 ≤ C) (hδ : 0 < δ)
    (hcover : E ⊆ boundary ∪ ⋃ n, F n) (hboundary : μ boundary = 0)
    (hF : ∀ n, μ (F n) ≤ ENNReal.ofReal A * logarithmicLayerCost (dyadicScale d n) C δ)
    (hR : Measurable R) (hD : MeasurableSet D) (hE : MeasurableSet E) (hj : Measurable j)
    (hexpand : ∀ x ∈ D, 1 < j x)
    (hchange : ∀ B, MeasurableSet B → B ⊆ D → μ (R '' B) = ∫⁻ x in B, j x ∂μ) :
    ∀ᵐ x ∂μ, (∀ n : ℕ, R^[n] x ∈ D) → ∃ n : ℕ, R^[n] x ∉ E :=
  ae_eventually_leaves_failure hR hD hE
    (finite_flux_of_logarithmic_layers hd hd1 hA hC hδ hcover hboundary hF).2 hj hexpand hchange

end BianchiIX

import BianchiIX.Dynamics.PartialCoreStrongIntegrals
import BianchiIX.Dynamics.CoreRadialVariation

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem coreRegion_radius_variation_row_unweighted {k Q : ℝ} {y : ProjectiveState}
    {v : CoreAngleState} (hk : 6 ≤ k) (hy : coreRegion k y) (hQ : ‖v‖ ≤ Q) :
    let B := coreWeightedJacobian k (projectiveCoreAngle y) (toCoreAngleState y)
    |B.mulVec v 0| ≤
      (16 * y 1 + 8 / k ^ 2 * y 3 ^ 2 + 8 * (y 3 / (k * y 2))) * Q + 3 * |v 1| := by
  have H := coreRegion_radius_variation_row hk hy hQ
  have hs := div_le_self (abs_nonneg (v 1)) (Real.one_le_cosh (projectiveCoreAngle y))
  have hk0 : 0 < k := by linarith only [hk]
  have hi : 1 / k ≤ 1 := (div_le_iff₀ hk0).mpr (by linarith only [hk])
  have hx := mul_le_mul_of_nonneg_right hi (abs_nonneg (v 1))
  dsimp only at H ⊢
  linarith only [H, hs, hx]

private theorem partial_core_radius_integral_constants {k U P Q X : ℝ}
    (hk : 6 ≤ k) (hU : 0 ≤ U) (hP : 0 ≤ P) (hPk : P ≤ k) (hQ : 0 ≤ Q) (hX : 0 ≤ X) :
    (16 * Q) * (4 * U / k) + (8 * Q / k ^ 2) * (2 * (101 / 99 : ℝ) ^ 2 * P ^ 2) +
        (8 * Q) * (2 * (101 / 99 : ℝ) ^ 2 * P / k) + 3 * ((4 * X + 48 * U * Q) / k) ≤
      256 * (X / k + (U + P) * Q / k) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hP2 := mul_le_mul_of_nonneg_right hPk (mul_nonneg hP hQ)
  have hUQk := mul_nonneg (mul_nonneg hU hQ) hk0.le
  have hPQk := mul_nonneg (mul_nonneg hP hQ) hk0.le
  have hXk := mul_nonneg hX hk0.le
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hk0)).mp
  field_simp
  nlinarith only [hP2, hUQk, hPQk, hXk]

/-- The partial-core drift loses only the extra inverse-radius gain of a full entrance. -/
theorem partialCore_projectedFlowVariation_radius_drift {y : ProjectiveState} {t₀ k a b Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (w : ProjectiveState)
    (hQ : ∀ t ∈ Icc a b, ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ t w)‖ ≤ Q) :
    let β := projectiveOriginalFlow y t₀
    let ξ := fun t => coreProjectedFlowVariation y t₀ t w
    |ξ b 0 - ξ a 0| ≤ 256 * (|k * ξ a 1| / k + (β a 1 + β a 2 * β a 3) * Q / k) := by
  intro β ξ
  let θ := fun t => projectiveCoreAngle (β t)
  let rate := fun t => coreOriginalClockRate (β t)
  let x := fun t => k * ξ t 1
  let u := fun t => β t 1 * rate t
  let w₂ := fun t => β t 3 ^ 2 * rate t
  let wv := fun t => (β t 3 / (k * β t 2)) * rate t
  let xa := fun t => |x t| * rate t
  let A := fun t => (16 * Q) * u t + (8 * Q / k ^ 2) * w₂ t + (8 * Q) * wv t + 3 * xa t
  have hk0 : 0 < k := by linarith only [hk]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ a ha)
  have hV (t : ℝ) (ht : t ∈ Icc a b) : 0 < β t 2 :=
    lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hflow (t : ℝ) (ht : t ∈ Icc a b) := hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)
  have hrate : ContinuousOn rate (Icc a b) := by
    intro t ht
    exact ((contDiffAt_coreOriginalClockRate 1 (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).1)).continuousAt.comp
        (hflow t ht).continuousAt).continuousWithinAt
  have hpos (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ rate t :=
    (coreRegion_clock_regular hk (hcore t ht)).2.2.le
  have hc (i : Fin 4) : ContinuousOn (fun t => β t i) (Icc a b) :=
    fun t ht => (hasDerivAt_pi.mp (hflow t ht) i).continuousAt.continuousWithinAt
  have hξ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt ξ
      (rate t • (coreAngleJacobian (θ t) (toCoreAngleState (β t))).mulVec (ξ t)) t :=
    hasDerivAt_coreProjectedFlowVariation hD (hdom ht) (hA t ht) (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).2.1) w
  have hxc : ContinuousOn x (Icc a b) := fun t ht =>
    ((hasDerivAt_pi.mp (hξ t ht) 1).const_mul k).continuousAt.continuousWithinAt
  have hu : ContinuousOn u (Icc a b) := (hc 1).mul hrate
  have hw₂ : ContinuousOn w₂ (Icc a b) := ((hc 3).pow 2).mul hrate
  have hwv : ContinuousOn wv (Icc a b) :=
    ((hc 3).div (continuousOn_const.mul (hc 2)) (fun t ht => ne_of_gt (mul_pos hk0 (hV t ht)))).mul hrate
  have hxa : ContinuousOn xa (Icc a b) := hxc.abs.mul hrate
  have hAc : ContinuousOn A (Icc a b) :=
    (((hu.const_mul _).add (hw₂.const_mul _)).add (hwv.const_mul _)).add (hxa.const_mul _)
  have hbound (t : ℝ) (ht : t ∈ Icc a b) :
      |rate t * (coreAngleJacobian (θ t) (toCoreAngleState (β t))).mulVec (ξ t) 0| ≤ A t := by
    have H := coreRegion_radius_variation_row_unweighted hk (hcore t ht) (hQ t ht)
    dsimp only at H
    rw [coreWeightedJacobian_mulVec (ne_of_gt hk0)] at H
    have H' := mul_le_mul_of_nonneg_left H (hpos t ht)
    rw [abs_mul, abs_of_nonneg (hpos t ht)]
    convert! H' using 1
    dsimp [A, u, w₂, wv, xa, x, scaleCoreVariation, θ]
    ring
  have hdiff := abs_sub_le_integral_bound hab
    (fun t ht => hasDerivAt_pi.mp (hξ t ht) 0) hAc hbound
  have hi₁ := (hu.const_mul (16 * Q)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₂ := (hw₂.const_mul (8 * Q / k ^ 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₃ := (hwv.const_mul (8 * Q)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₄ := (hxa.const_mul 3).intervalIntegrable_of_Icc (μ := volume) hab
  have hlin : (∫ t in a..b, A t) =
      (16 * Q) * (∫ t in a..b, u t) + (8 * Q / k ^ 2) * (∫ t in a..b, w₂ t) +
        (8 * Q) * (∫ t in a..b, wv t) + 3 * (∫ t in a..b, xa t) := by
    dsimp only [A]
    rw [intervalIntegral.integral_add ((hi₁.add hi₂).add hi₃) hi₄,
      intervalIntegral.integral_add (hi₁.add hi₂) hi₃, intervalIntegral.integral_add hi₁ hi₂]
    simp only [intervalIntegral.integral_const_mul]
  obtain ⟨hUint, _, hWVint, hW₂int⟩ := projectiveOriginalFlow_core_weight_integrals hk hab hD hdom hA hcore
  have hXAint := partialCore_projectedFlowVariation_strong_integral hk hab hD hdom hA hcore w hQ
  have hint := add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hUint (by positivity : 0 ≤ 16 * Q))
    (mul_le_mul_of_nonneg_left hW₂int (by positivity : 0 ≤ 8 * Q / k ^ 2)))
    (mul_le_mul_of_nonneg_left hWVint (by positivity : 0 ≤ 8 * Q)))
    (mul_le_mul_of_nonneg_left hXAint (by norm_num : (0 : ℝ) ≤ 3))
  have hPk : β a 2 * β a 3 ≤ k := by
    have H := coreBootstrap_wall_bound hk (hcore a ha).2.2.2.2
    linarith only [H, hk]
  exact hdiff.trans (hlin.le.trans (hint.trans (partial_core_radius_integral_constants hk
    (hcore a ha).2.2.1.1 (hcore a ha).2.2.2.1 hPk hQ0 (abs_nonneg _))))

end BianchiIX
